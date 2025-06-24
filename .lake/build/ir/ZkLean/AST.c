// Lean compiler output
// Module: ZkLean.AST
// Imports: Init Mathlib.Algebra.Field.Defs ZkLean.LookupTable
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
extern lean_object* l_Nat_instOrd__mathlib;
lean_object* l_instBEqOfDecidableEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instAddZKExpr(lean_object*);
LEAN_EXPORT lean_object* l_instHMulZKExpr(lean_object*);
LEAN_EXPORT lean_object* l_instOfNatZKExpr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedRamId;
static lean_object* l_instWitnessIdBEq___closed__2;
LEAN_EXPORT lean_object* l_instNegZKExpr___rarg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedRAM(lean_object*);
LEAN_EXPORT lean_object* l_instHAddZKExpr___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instZeroZKExpr(lean_object*);
LEAN_EXPORT lean_object* l_instWitnessIdOrd;
LEAN_EXPORT lean_object* l_instOfNatZKExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHSubZKExpr___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instZeroZKExpr___rarg(lean_object*);
static lean_object* l_instWitnessIdHashable___closed__1;
LEAN_EXPORT lean_object* l_instAddZKExpr___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instWitnessIdHashable;
LEAN_EXPORT lean_object* l_instWitnessIdLT;
LEAN_EXPORT lean_object* l_instNegZKExpr(lean_object*);
LEAN_EXPORT lean_object* l_instHMulZKExpr___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHSubZKExpr(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedZKExpr___rarg(lean_object*);
extern lean_object* l_instLTNat;
LEAN_EXPORT lean_object* l_instWitnessIdBEq;
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHAddZKExpr(lean_object*);
LEAN_EXPORT lean_object* l_instOfNatZKExpr___rarg(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedZKExpr(lean_object*);
static lean_object* l_instWitnessIdBEq___closed__1;
lean_object* l_instHashableNat___boxed(lean_object*);
static lean_object* _init_l_instWitnessIdBEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instWitnessIdBEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instWitnessIdBEq___closed__1;
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instWitnessIdBEq() {
_start:
{
lean_object* x_1; 
x_1 = l_instWitnessIdBEq___closed__2;
return x_1;
}
}
static lean_object* _init_l_instWitnessIdOrd() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_instOrd__mathlib;
return x_1;
}
}
static lean_object* _init_l_instWitnessIdLT() {
_start:
{
lean_object* x_1; 
x_1 = l_instLTNat;
return x_1;
}
}
static lean_object* _init_l_instWitnessIdHashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instHashableNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instWitnessIdHashable() {
_start:
{
lean_object* x_1; 
x_1 = l_instWitnessIdHashable___closed__1;
return x_1;
}
}
static lean_object* _init_l_instInhabitedRamId() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_instInhabitedRAM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instInhabitedZKExpr___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instInhabitedZKExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instInhabitedZKExpr___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instOfNatZKExpr___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instOfNatZKExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instOfNatZKExpr___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instOfNatZKExpr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instOfNatZKExpr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instZeroZKExpr___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instZeroZKExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instZeroZKExpr___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHAddZKExpr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instHAddZKExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instHAddZKExpr___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instAddZKExpr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instAddZKExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instAddZKExpr___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHSubZKExpr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instHSubZKExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instHSubZKExpr___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instNegZKExpr___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instNegZKExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instNegZKExpr___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instHMulZKExpr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instHMulZKExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instHMulZKExpr___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Field_Defs(uint8_t builtin, lean_object*);
lean_object* initialize_ZkLean_LookupTable(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ZkLean_AST(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Field_Defs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ZkLean_LookupTable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instWitnessIdBEq___closed__1 = _init_l_instWitnessIdBEq___closed__1();
lean_mark_persistent(l_instWitnessIdBEq___closed__1);
l_instWitnessIdBEq___closed__2 = _init_l_instWitnessIdBEq___closed__2();
lean_mark_persistent(l_instWitnessIdBEq___closed__2);
l_instWitnessIdBEq = _init_l_instWitnessIdBEq();
lean_mark_persistent(l_instWitnessIdBEq);
l_instWitnessIdOrd = _init_l_instWitnessIdOrd();
lean_mark_persistent(l_instWitnessIdOrd);
l_instWitnessIdLT = _init_l_instWitnessIdLT();
lean_mark_persistent(l_instWitnessIdLT);
l_instWitnessIdHashable___closed__1 = _init_l_instWitnessIdHashable___closed__1();
lean_mark_persistent(l_instWitnessIdHashable___closed__1);
l_instWitnessIdHashable = _init_l_instWitnessIdHashable();
lean_mark_persistent(l_instWitnessIdHashable);
l_instInhabitedRamId = _init_l_instInhabitedRamId();
lean_mark_persistent(l_instInhabitedRamId);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
