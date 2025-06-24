// Lean compiler output
// Module: ZkLean.Builder
// Imports: Init Std.Data.HashMap.Basic ZkLean.AST ZkLean.LookupTable ZkLean.FreeMonad
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
LEAN_EXPORT lean_object* l_instWitnessableVector_go___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_FreeM_lift___rarg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_instWitnessableVector___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instWitnessableVector_go___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instWitnessableZKExpr(lean_object*);
LEAN_EXPORT lean_object* l_runFold(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_toStateM(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_instWitnessableVector___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ZKOpInterp___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_FreeM_mapM___at_toStateM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ZKBuilder_ramNew___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ZKBuilder_constrainR1CS___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_runFold___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_instWitnessableVector_go___rarg___closed__1;
LEAN_EXPORT lean_object* l_ZKBuilder_lookup(lean_object*);
LEAN_EXPORT lean_object* l_ZKBuilder_witness(lean_object*);
LEAN_EXPORT lean_object* l_FreeM_mapM___at_toStateM___spec__1(lean_object*, lean_object*);
lean_object* l_FreeM_cataFreeM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instWitnessableVector_go___rarg___lambda__1(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedZKBuilderState(lean_object*);
lean_object* l_FreeM_bind___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedRamOp(lean_object*);
LEAN_EXPORT lean_object* l_ZKBuilder_ramNew(lean_object*);
static lean_object* l_instMonadZKBuilder___closed__1;
static lean_object* l_instInhabitedZKBuilderState___closed__1;
LEAN_EXPORT lean_object* l_ZKBuilder_constrainEq(lean_object*);
LEAN_EXPORT lean_object* l_instWitnessableVector_go___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_runFold___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instZeroZKExpr__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ZKBuilder_constrainEq___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ZKOpInterp___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_instWitnessableZKExpr___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ZKOpInterp___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_toStateM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ZKBuilder_ramWrite(lean_object*);
LEAN_EXPORT lean_object* l_FreeM_mapM___at_toStateM___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instWitnessableVector_go___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ZKBuilder_ramRead(lean_object*);
LEAN_EXPORT lean_object* l_ZKBuilder_ramRead___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ZKBuilder_muxLookup___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ZKBuilder_lookup___rarg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instWitnessableVector(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_runFold___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_instInhabitedZKBuilderState___closed__2;
static lean_object* l_ZKBuilder_witness___closed__1;
LEAN_EXPORT lean_object* l_ZKBuilder_ramWrite___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_ZKBuilder_constrainR1CS(lean_object*);
LEAN_EXPORT lean_object* l_ZKOpInterp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ZKOpInterp(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_instMonadZKBuilder(lean_object*);
lean_object* l_FreeM_instMonad(lean_object*);
LEAN_EXPORT lean_object* l_instWitnessableVector_go(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_instZeroZKExpr__1(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_runFold___rarg___closed__1;
LEAN_EXPORT lean_object* l_instInhabitedRamOp___rarg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ZKBuilder_muxLookup(lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedRamOp___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instInhabitedRamOp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instInhabitedRamOp___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_instInhabitedZKBuilderState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_instInhabitedZKBuilderState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_instInhabitedZKBuilderState___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instInhabitedZKBuilderState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instInhabitedZKBuilderState___closed__2;
return x_2;
}
}
static lean_object* _init_l_instMonadZKBuilder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_FreeM_instMonad(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instMonadZKBuilder(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instMonadZKBuilder___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instZeroZKExpr__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instZeroZKExpr__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instZeroZKExpr__1___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_ZKBuilder_witness___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_FreeM_lift___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_witness(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ZKBuilder_witness___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_constrainEq___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = l_FreeM_lift___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_constrainEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ZKBuilder_constrainEq___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_constrainR1CS___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_FreeM_lift___rarg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_constrainR1CS(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ZKBuilder_constrainR1CS___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_lookup___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = l_FreeM_lift___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_lookup(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ZKBuilder_lookup___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_muxLookup___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = l_FreeM_lift___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_muxLookup(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ZKBuilder_muxLookup___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_ramNew___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l_FreeM_lift___rarg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_ramNew(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ZKBuilder_ramNew___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_ramRead___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = l_FreeM_lift___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_ramRead(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ZKBuilder_ramRead___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_ramWrite___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(7, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_FreeM_lift___rarg(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ZKBuilder_ramWrite(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ZKBuilder_ramWrite___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ZKOpInterp___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_fget(x_1, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_array_fget(x_1, x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_array_fget(x_1, x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_array_fget(x_1, x_18);
x_20 = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_13);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_19);
lean_ctor_set_tag(x_7, 5);
lean_ctor_set(x_7, 1, x_20);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_7);
x_3 = x_9;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_fget(x_1, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_array_fget(x_1, x_27);
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_array_fget(x_1, x_29);
x_31 = lean_unsigned_to_nat(3u);
x_32 = lean_array_fget(x_1, x_31);
x_33 = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_34);
x_3 = x_9;
x_5 = x_35;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ZKOpInterp___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_ZKOpInterp___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ZKOpInterp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
lean_inc(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_11);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_11, x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
case 1:
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_4, 1);
lean_ctor_set_tag(x_3, 0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_4, 1, x_23);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
x_28 = lean_ctor_get(x_4, 2);
x_29 = lean_ctor_get(x_4, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
lean_ctor_set_tag(x_3, 0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_3, 0);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_3);
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 3);
lean_inc(x_39);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_40 = x_4;
} else {
 lean_dec_ref(x_4);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 4, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_38);
lean_ctor_set(x_43, 3, x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
case 2:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_1);
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 2);
lean_inc(x_48);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_4);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_4, 1);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_47);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_4, 1, x_53);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_4);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = lean_ctor_get(x_4, 0);
x_57 = lean_ctor_get(x_4, 1);
x_58 = lean_ctor_get(x_4, 2);
x_59 = lean_ctor_get(x_4, 3);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_4);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_46);
lean_ctor_set(x_60, 1, x_47);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_48);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_58);
lean_ctor_set(x_63, 3, x_59);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
case 3:
{
uint8_t x_66; 
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_3, 0);
x_68 = lean_ctor_get(x_3, 1);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_array_fget(x_68, x_69);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_array_fget(x_68, x_71);
x_73 = lean_unsigned_to_nat(2u);
x_74 = lean_array_fget(x_68, x_73);
x_75 = lean_unsigned_to_nat(3u);
x_76 = lean_array_fget(x_68, x_75);
lean_dec(x_68);
x_77 = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_70);
lean_ctor_set(x_77, 2, x_72);
lean_ctor_set(x_77, 3, x_74);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_77);
return x_3;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_78 = lean_ctor_get(x_3, 0);
x_79 = lean_ctor_get(x_3, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_3);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_array_fget(x_79, x_80);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_array_fget(x_79, x_82);
x_84 = lean_unsigned_to_nat(2u);
x_85 = lean_array_fget(x_79, x_84);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_array_fget(x_79, x_86);
lean_dec(x_79);
x_88 = lean_alloc_ctor(6, 5, 0);
lean_ctor_set(x_88, 0, x_78);
lean_ctor_set(x_88, 1, x_81);
lean_ctor_set(x_88, 2, x_83);
lean_ctor_set(x_88, 3, x_85);
lean_ctor_set(x_88, 4, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_4);
return x_89;
}
}
case 4:
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_3);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_91 = lean_ctor_get(x_3, 0);
x_92 = lean_ctor_get(x_3, 1);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_1);
x_94 = lean_array_get_size(x_92);
x_95 = lean_unsigned_to_nat(0u);
x_96 = lean_nat_dec_lt(x_95, x_94);
if (x_96 == 0)
{
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_93);
return x_3;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_le(x_94, x_94);
if (x_97 == 0)
{
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_93);
return x_3;
}
else
{
size_t x_98; size_t x_99; lean_object* x_100; 
x_98 = 0;
x_99 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_100 = l_Array_foldlMUnsafe_fold___at_ZKOpInterp___spec__1___rarg(x_91, x_92, x_98, x_99, x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_100);
return x_3;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = lean_ctor_get(x_3, 0);
x_102 = lean_ctor_get(x_3, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_3);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_1);
x_104 = lean_array_get_size(x_102);
x_105 = lean_unsigned_to_nat(0u);
x_106 = lean_nat_dec_lt(x_105, x_104);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_101);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_4);
return x_107;
}
else
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_104, x_104);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_101);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_4);
return x_109;
}
else
{
size_t x_110; size_t x_111; lean_object* x_112; lean_object* x_113; 
x_110 = 0;
x_111 = lean_usize_of_nat(x_104);
lean_dec(x_104);
x_112 = l_Array_foldlMUnsafe_fold___at_ZKOpInterp___spec__1___rarg(x_101, x_102, x_110, x_111, x_103);
lean_dec(x_102);
lean_dec(x_101);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_4);
return x_113;
}
}
}
}
case 5:
{
lean_object* x_114; uint8_t x_115; 
lean_dec(x_1);
x_114 = lean_ctor_get(x_3, 0);
lean_inc(x_114);
lean_dec(x_3);
x_115 = !lean_is_exclusive(x_4);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_4, 2);
x_117 = lean_array_get_size(x_116);
x_118 = lean_array_push(x_116, x_114);
lean_ctor_set(x_4, 2, x_118);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_4);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = lean_ctor_get(x_4, 0);
x_121 = lean_ctor_get(x_4, 1);
x_122 = lean_ctor_get(x_4, 2);
x_123 = lean_ctor_get(x_4, 3);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_4);
x_124 = lean_array_get_size(x_122);
x_125 = lean_array_push(x_122, x_114);
x_126 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_126, 0, x_120);
lean_ctor_set(x_126, 1, x_121);
lean_ctor_set(x_126, 2, x_125);
lean_ctor_set(x_126, 3, x_123);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
case 6:
{
uint8_t x_128; 
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_3);
if (x_128 == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_4);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_4, 3);
x_131 = lean_array_get_size(x_130);
x_132 = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set_tag(x_3, 0);
x_133 = lean_array_push(x_130, x_3);
lean_ctor_set(x_4, 3, x_133);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_4);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_135 = lean_ctor_get(x_4, 0);
x_136 = lean_ctor_get(x_4, 1);
x_137 = lean_ctor_get(x_4, 2);
x_138 = lean_ctor_get(x_4, 3);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_4);
x_139 = lean_array_get_size(x_138);
x_140 = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set_tag(x_3, 0);
x_141 = lean_array_push(x_138, x_3);
x_142 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_142, 0, x_135);
lean_ctor_set(x_142, 1, x_136);
lean_ctor_set(x_142, 2, x_137);
lean_ctor_set(x_142, 3, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_144 = lean_ctor_get(x_3, 0);
x_145 = lean_ctor_get(x_3, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_3);
x_146 = lean_ctor_get(x_4, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_4, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_4, 2);
lean_inc(x_148);
x_149 = lean_ctor_get(x_4, 3);
lean_inc(x_149);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_150 = x_4;
} else {
 lean_dec_ref(x_4);
 x_150 = lean_box(0);
}
x_151 = lean_array_get_size(x_149);
x_152 = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_145);
x_154 = lean_array_push(x_149, x_153);
if (lean_is_scalar(x_150)) {
 x_155 = lean_alloc_ctor(0, 4, 0);
} else {
 x_155 = x_150;
}
lean_ctor_set(x_155, 0, x_146);
lean_ctor_set(x_155, 1, x_147);
lean_ctor_set(x_155, 2, x_148);
lean_ctor_set(x_155, 3, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
default: 
{
uint8_t x_157; 
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_3);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_4);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_4, 3);
lean_ctor_set_tag(x_3, 1);
x_160 = lean_array_push(x_159, x_3);
lean_ctor_set(x_4, 3, x_160);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_4);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_163 = lean_ctor_get(x_4, 0);
x_164 = lean_ctor_get(x_4, 1);
x_165 = lean_ctor_get(x_4, 2);
x_166 = lean_ctor_get(x_4, 3);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_4);
lean_ctor_set_tag(x_3, 1);
x_167 = lean_array_push(x_166, x_3);
x_168 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_168, 0, x_163);
lean_ctor_set(x_168, 1, x_164);
lean_ctor_set(x_168, 2, x_165);
lean_ctor_set(x_168, 3, x_167);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_171 = lean_ctor_get(x_3, 0);
x_172 = lean_ctor_get(x_3, 1);
x_173 = lean_ctor_get(x_3, 2);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_3);
x_174 = lean_ctor_get(x_4, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_4, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_4, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_4, 3);
lean_inc(x_177);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_178 = x_4;
} else {
 lean_dec_ref(x_4);
 x_178 = lean_box(0);
}
x_179 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_179, 0, x_171);
lean_ctor_set(x_179, 1, x_172);
lean_ctor_set(x_179, 2, x_173);
x_180 = lean_array_push(x_177, x_179);
if (lean_is_scalar(x_178)) {
 x_181 = lean_alloc_ctor(0, 4, 0);
} else {
 x_181 = x_178;
}
lean_ctor_set(x_181, 0, x_174);
lean_ctor_set(x_181, 1, x_175);
lean_ctor_set(x_181, 2, x_176);
lean_ctor_set(x_181, 3, x_180);
x_182 = lean_box(0);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ZKOpInterp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ZKOpInterp___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_ZKOpInterp___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_ZKOpInterp___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_FreeM_mapM___at_toStateM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_FreeM_mapM___at_toStateM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_2);
x_8 = lean_apply_3(x_2, lean_box(0), x_6, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_1(x_7, x_9);
x_12 = lean_alloc_closure((void*)(l_FreeM_mapM___at_toStateM___spec__1___rarg___lambda__1), 4, 1);
lean_closure_set(x_12, 0, x_2);
x_1 = x_11;
x_2 = x_12;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_FreeM_mapM___at_toStateM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_FreeM_mapM___at_toStateM___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_toStateM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_ZKOpInterp___rarg), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_FreeM_mapM___at_toStateM___spec__1___rarg(x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_toStateM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_toStateM___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_runFold___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_runFold___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_ZKOpInterp___rarg(x_1, lean_box(0), x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_runFold___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_runFold___rarg___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_runFold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_runFold___rarg___lambda__2), 5, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_runFold___rarg___closed__1;
x_6 = l_FreeM_cataFreeM___rarg(x_5, x_4, x_2);
x_7 = lean_apply_1(x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_runFold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_runFold___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_instWitnessableZKExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_ZKBuilder_witness(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_instWitnessableZKExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_instWitnessableZKExpr___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_instWitnessableVector_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_push(x_2, x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instWitnessableVector_go___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_instWitnessableVector_go___rarg(x_1, x_2);
x_5 = lean_alloc_closure((void*)(l_instWitnessableVector_go___rarg___lambda__1), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = l_FreeM_bind___rarg(x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_instWitnessableVector_go___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instInhabitedZKBuilderState___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instWitnessableVector_go___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_instWitnessableVector_go___rarg___lambda__2___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
x_8 = l_FreeM_bind___rarg(x_1, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_instWitnessableVector_go___rarg___closed__1;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_instWitnessableVector_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instWitnessableVector_go___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instWitnessableVector_go___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instWitnessableVector_go___rarg___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instWitnessableVector_go___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instWitnessableVector_go___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instWitnessableVector___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instWitnessableVector_go___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instWitnessableVector(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instWitnessableVector___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instWitnessableVector___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instWitnessableVector___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_ZkLean_AST(uint8_t builtin, lean_object*);
lean_object* initialize_ZkLean_LookupTable(uint8_t builtin, lean_object*);
lean_object* initialize_ZkLean_FreeMonad(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ZkLean_Builder(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ZkLean_AST(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ZkLean_LookupTable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ZkLean_FreeMonad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instInhabitedZKBuilderState___closed__1 = _init_l_instInhabitedZKBuilderState___closed__1();
lean_mark_persistent(l_instInhabitedZKBuilderState___closed__1);
l_instInhabitedZKBuilderState___closed__2 = _init_l_instInhabitedZKBuilderState___closed__2();
lean_mark_persistent(l_instInhabitedZKBuilderState___closed__2);
l_instMonadZKBuilder___closed__1 = _init_l_instMonadZKBuilder___closed__1();
lean_mark_persistent(l_instMonadZKBuilder___closed__1);
l_ZKBuilder_witness___closed__1 = _init_l_ZKBuilder_witness___closed__1();
lean_mark_persistent(l_ZKBuilder_witness___closed__1);
l_runFold___rarg___closed__1 = _init_l_runFold___rarg___closed__1();
lean_mark_persistent(l_runFold___rarg___closed__1);
l_instWitnessableZKExpr___closed__1 = _init_l_instWitnessableZKExpr___closed__1();
lean_mark_persistent(l_instWitnessableZKExpr___closed__1);
l_instWitnessableVector_go___rarg___closed__1 = _init_l_instWitnessableVector_go___rarg___closed__1();
lean_mark_persistent(l_instWitnessableVector_go___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
