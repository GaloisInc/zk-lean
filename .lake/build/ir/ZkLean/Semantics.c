// Lean compiler output
// Module: ZkLean.Semantics
// Imports: Init Mathlib.Algebra.Field.Defs ZkLean.AST ZkLean.Builder Init.Prelude Init.Data.Array.Basic Init.Data.Array.Set
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
LEAN_EXPORT lean_object* l_semantics__ram___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_CommRing_toNonUnitalCommRing___rarg(lean_object*);
static lean_object* l_semantics__ram___rarg___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_semantics__constraints___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_semantics___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_semantics__zkexpr___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AddGroupWithOne_toAddGroup___rarg(lean_object*);
lean_object* l_Ring_toAddGroupWithOne___rarg(lean_object*);
LEAN_EXPORT lean_object* l_semantics__zkexpr_eval___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_semantics__ram___rarg___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_semantics__zkexpr_eval___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_semantics__ram(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_semantics__zkexpr_eval___spec__1(lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toDistrib___rarg(lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_GetElem_0__List_get_x3fInternal___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_semantics__zkexpr___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_semantics__ram___spec__1(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_SubNegZeroMonoid_toNegZeroClass___rarg(lean_object*);
lean_object* l_evalComposedLookupTable___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_semantics__constraints___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_semantics__ram___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_semantics__zkexpr_eval___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_semantics___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Field_toDivisionRing___rarg(lean_object*);
LEAN_EXPORT lean_object* l_semantics__ram___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_semantics__ram___rarg___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_semantics__ram___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_semantics__zkexpr_eval___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_semantics__ram___rarg___closed__2;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_semantics__ram___rarg___closed__4;
LEAN_EXPORT lean_object* l_semantics__zkexpr_eval(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_semantics(lean_object*);
LEAN_EXPORT lean_object* l_semantics__constraints(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_semantics__zkexpr(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Ring_toAddCommGroup___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_semantics__zkexpr_eval___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(16u);
x_11 = lean_apply_2(x_9, x_10, x_6);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_array_uset(x_8, x_3, x_11);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_semantics__zkexpr_eval___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_semantics__zkexpr_eval___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_semantics__zkexpr_eval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l___private_Init_GetElem_0__List_get_x3fInternal___rarg(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
lean_inc(x_1);
x_16 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_3, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_1);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_3, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_1);
x_20 = lean_box(0);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_CommRing_toNonUnitalCommRing___rarg(x_24);
x_26 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(x_25);
x_27 = l_NonUnitalNonAssocSemiring_toDistrib___rarg(x_26);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_apply_2(x_28, x_18, x_22);
lean_ctor_set(x_19, 0, x_29);
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_CommRing_toNonUnitalCommRing___rarg(x_32);
x_34 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(x_33);
x_35 = l_NonUnitalNonAssocSemiring_toDistrib___rarg(x_34);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_apply_2(x_36, x_18, x_30);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
case 3:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_4, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
lean_inc(x_1);
x_41 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_3, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
lean_dec(x_40);
lean_dec(x_1);
x_42 = lean_box(0);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_1);
x_44 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_3, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_1);
x_45 = lean_box(0);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = l_Field_toDivisionRing___rarg(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Ring_toAddGroupWithOne___rarg(x_50);
x_52 = l_AddGroupWithOne_toAddGroup___rarg(x_51);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_apply_2(x_53, x_43, x_47);
lean_ctor_set(x_44, 0, x_54);
return x_44;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
lean_dec(x_44);
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
lean_dec(x_1);
x_57 = l_Field_toDivisionRing___rarg(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Ring_toAddGroupWithOne___rarg(x_58);
x_60 = l_AddGroupWithOne_toAddGroup___rarg(x_59);
lean_dec(x_59);
x_61 = lean_ctor_get(x_60, 2);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_apply_2(x_61, x_43, x_55);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
}
case 4:
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_4, 0);
lean_inc(x_64);
lean_dec(x_4);
lean_inc(x_1);
x_65 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_3, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
lean_dec(x_1);
x_66 = lean_box(0);
return x_66;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
lean_dec(x_1);
x_70 = l_Field_toDivisionRing___rarg(x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Ring_toAddCommGroup___rarg(x_71);
lean_dec(x_71);
x_73 = l_SubNegZeroMonoid_toNegZeroClass___rarg(x_72);
lean_dec(x_72);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_apply_1(x_74, x_68);
lean_ctor_set(x_65, 0, x_75);
return x_65;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_76 = lean_ctor_get(x_65, 0);
lean_inc(x_76);
lean_dec(x_65);
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
lean_dec(x_1);
x_78 = l_Field_toDivisionRing___rarg(x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Ring_toAddCommGroup___rarg(x_79);
lean_dec(x_79);
x_81 = l_SubNegZeroMonoid_toNegZeroClass___rarg(x_80);
lean_dec(x_80);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_apply_1(x_82, x_76);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
case 5:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_4, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_4, 1);
lean_inc(x_86);
lean_dec(x_4);
lean_inc(x_1);
x_87 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_3, x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
lean_dec(x_86);
lean_dec(x_1);
x_88 = lean_box(0);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_1);
x_90 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_3, x_86);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
lean_dec(x_89);
lean_dec(x_1);
x_91 = lean_box(0);
return x_91;
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_1, 0);
lean_inc(x_94);
lean_dec(x_1);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_CommRing_toNonUnitalCommRing___rarg(x_95);
x_97 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(x_96);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_apply_2(x_98, x_89, x_93);
lean_ctor_set(x_90, 0, x_99);
return x_90;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_ctor_get(x_90, 0);
lean_inc(x_100);
lean_dec(x_90);
x_101 = lean_ctor_get(x_1, 0);
lean_inc(x_101);
lean_dec(x_1);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_CommRing_toNonUnitalCommRing___rarg(x_102);
x_104 = l_NonUnitalNonAssocCommRing_toNonUnitalNonAssocCommSemiring___rarg(x_103);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_apply_2(x_105, x_89, x_100);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
}
case 6:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_4, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_4, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_4, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_4, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_4, 4);
lean_inc(x_112);
lean_dec(x_4);
lean_inc(x_1);
x_113 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_3, x_109);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_1);
x_114 = lean_box(0);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_1);
x_116 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_3, x_110);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_108);
lean_dec(x_1);
x_117 = lean_box(0);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_1);
x_119 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_3, x_111);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_112);
lean_dec(x_108);
lean_dec(x_1);
x_120 = lean_box(0);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
lean_inc(x_1);
x_122 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_3, x_112);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
lean_dec(x_121);
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_1);
x_123 = lean_box(0);
return x_123;
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; size_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_125 = lean_ctor_get(x_122, 0);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_121);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_118);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_115);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_array_mk(x_130);
x_132 = lean_array_size(x_131);
x_133 = 0;
x_134 = l_Array_mapMUnsafe_map___at_semantics__zkexpr_eval___spec__1___rarg(x_1, x_132, x_133, x_131);
x_135 = lean_unsigned_to_nat(16u);
x_136 = lean_unsigned_to_nat(4u);
x_137 = l_evalComposedLookupTable___rarg(x_135, x_136, x_108, x_134);
lean_dec(x_134);
lean_ctor_set(x_122, 0, x_137);
return x_122;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; size_t x_145; size_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_138 = lean_ctor_get(x_122, 0);
lean_inc(x_138);
lean_dec(x_122);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_121);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_118);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_115);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_array_mk(x_143);
x_145 = lean_array_size(x_144);
x_146 = 0;
x_147 = l_Array_mapMUnsafe_map___at_semantics__zkexpr_eval___spec__1___rarg(x_1, x_145, x_146, x_144);
x_148 = lean_unsigned_to_nat(16u);
x_149 = lean_unsigned_to_nat(4u);
x_150 = l_evalComposedLookupTable___rarg(x_148, x_149, x_108, x_147);
lean_dec(x_147);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
}
}
}
}
default: 
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_dec(x_1);
x_152 = lean_ctor_get(x_4, 0);
lean_inc(x_152);
lean_dec(x_4);
x_153 = lean_array_get_size(x_3);
x_154 = lean_nat_dec_lt(x_152, x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
lean_dec(x_152);
x_155 = lean_box(0);
return x_155;
}
else
{
lean_object* x_156; 
x_156 = lean_array_fget(x_3, x_152);
lean_dec(x_152);
return x_156;
}
}
}
}
}
LEAN_EXPORT lean_object* l_semantics__zkexpr_eval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_semantics__zkexpr_eval___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_semantics__zkexpr_eval___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_semantics__zkexpr_eval___spec__1___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_semantics__zkexpr_eval___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_semantics__zkexpr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_semantics__zkexpr_eval___rarg(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_semantics__zkexpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_semantics__zkexpr___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_semantics__zkexpr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_semantics__zkexpr___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_semantics__ram___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_7, x_8);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_array_uget(x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
lean_inc(x_1);
x_22 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_19, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_free_object(x_9);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_18);
x_26 = lean_nat_dec_lt(x_20, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_20);
lean_free_object(x_9);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_28 = lean_array_fget(x_18, x_20);
lean_dec(x_20);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_array_get_size(x_29);
lean_inc(x_4);
lean_inc(x_24);
x_31 = lean_apply_1(x_4, x_24);
x_32 = lean_unbox_uint64(x_31);
lean_dec(x_31);
x_33 = 32;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = 16;
x_37 = lean_uint64_shift_right(x_35, x_36);
x_38 = lean_uint64_xor(x_35, x_37);
x_39 = lean_uint64_to_usize(x_38);
x_40 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_41 = 1;
x_42 = lean_usize_sub(x_40, x_41);
x_43 = lean_usize_land(x_39, x_42);
x_44 = lean_array_uget(x_29, x_43);
lean_dec(x_29);
lean_inc(x_3);
x_45 = l_Std_DHashMap_Internal_AssocList_get_x3f___rarg(x_3, x_24, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
lean_free_object(x_9);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_46 = lean_box(0);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_array_push(x_19, x_45);
lean_ctor_set(x_9, 1, x_48);
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_array_push(x_19, x_50);
lean_ctor_set(x_9, 1, x_51);
x_10 = x_9;
goto block_14;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_9, 0);
x_53 = lean_ctor_get(x_9, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_9);
x_54 = lean_ctor_get(x_16, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
lean_dec(x_16);
lean_inc(x_1);
x_56 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_53, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_box(0);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_array_get_size(x_52);
x_60 = lean_nat_dec_lt(x_54, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_58);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = lean_box(0);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; 
x_62 = lean_array_fget(x_52, x_54);
lean_dec(x_54);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_array_get_size(x_63);
lean_inc(x_4);
lean_inc(x_58);
x_65 = lean_apply_1(x_4, x_58);
x_66 = lean_unbox_uint64(x_65);
lean_dec(x_65);
x_67 = 32;
x_68 = lean_uint64_shift_right(x_66, x_67);
x_69 = lean_uint64_xor(x_66, x_68);
x_70 = 16;
x_71 = lean_uint64_shift_right(x_69, x_70);
x_72 = lean_uint64_xor(x_69, x_71);
x_73 = lean_uint64_to_usize(x_72);
x_74 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_75 = 1;
x_76 = lean_usize_sub(x_74, x_75);
x_77 = lean_usize_land(x_73, x_76);
x_78 = lean_array_uget(x_63, x_77);
lean_dec(x_63);
lean_inc(x_3);
x_79 = l_Std_DHashMap_Internal_AssocList_get_x3f___rarg(x_3, x_58, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_80 = lean_box(0);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
x_84 = lean_array_push(x_53, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_52);
lean_ctor_set(x_85, 1, x_84);
x_10 = x_85;
goto block_14;
}
}
}
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_9);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_16);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_9, 0);
x_89 = lean_ctor_get(x_9, 1);
x_90 = lean_ctor_get(x_16, 0);
x_91 = lean_ctor_get(x_16, 1);
x_92 = lean_ctor_get(x_16, 2);
lean_inc(x_1);
x_93 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_89, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
lean_free_object(x_16);
lean_dec(x_92);
lean_dec(x_90);
lean_free_object(x_9);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_94 = lean_box(0);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_1);
x_96 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_89, x_92);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
lean_dec(x_95);
lean_free_object(x_16);
lean_dec(x_90);
lean_free_object(x_9);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = lean_box(0);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_array_get_size(x_88);
x_100 = lean_nat_dec_lt(x_90, x_99);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_95);
lean_free_object(x_16);
lean_dec(x_90);
lean_free_object(x_9);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = lean_box(0);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; 
x_102 = lean_array_fget(x_88, x_90);
x_103 = lean_box(0);
x_104 = lean_array_push(x_89, x_103);
x_105 = lean_nat_dec_le(x_99, x_90);
lean_dec(x_99);
x_106 = !lean_is_exclusive(x_102);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; size_t x_118; size_t x_119; size_t x_120; size_t x_121; size_t x_122; lean_object* x_123; uint8_t x_124; 
x_107 = lean_ctor_get(x_102, 0);
x_108 = lean_ctor_get(x_102, 1);
x_109 = lean_array_get_size(x_108);
lean_inc(x_4);
lean_inc(x_95);
x_110 = lean_apply_1(x_4, x_95);
x_111 = lean_unbox_uint64(x_110);
lean_dec(x_110);
x_112 = 32;
x_113 = lean_uint64_shift_right(x_111, x_112);
x_114 = lean_uint64_xor(x_111, x_113);
x_115 = 16;
x_116 = lean_uint64_shift_right(x_114, x_115);
x_117 = lean_uint64_xor(x_114, x_116);
x_118 = lean_uint64_to_usize(x_117);
x_119 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_120 = 1;
x_121 = lean_usize_sub(x_119, x_120);
x_122 = lean_usize_land(x_118, x_121);
x_123 = lean_array_uget(x_108, x_122);
lean_inc(x_123);
lean_inc(x_95);
lean_inc(x_3);
x_124 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_3, x_95, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_107, x_125);
lean_dec(x_107);
lean_ctor_set(x_16, 2, x_123);
lean_ctor_set(x_16, 1, x_98);
lean_ctor_set(x_16, 0, x_95);
x_127 = lean_array_uset(x_108, x_122, x_16);
x_128 = lean_unsigned_to_nat(4u);
x_129 = lean_nat_mul(x_126, x_128);
x_130 = lean_unsigned_to_nat(3u);
x_131 = lean_nat_div(x_129, x_130);
lean_dec(x_129);
x_132 = lean_array_get_size(x_127);
x_133 = lean_nat_dec_le(x_131, x_132);
lean_dec(x_132);
lean_dec(x_131);
if (x_133 == 0)
{
if (x_105 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_inc(x_4);
x_134 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_4, x_127);
lean_ctor_set(x_102, 1, x_134);
lean_ctor_set(x_102, 0, x_126);
x_135 = lean_array_fset(x_88, x_90, x_102);
lean_dec(x_90);
lean_ctor_set(x_9, 1, x_104);
lean_ctor_set(x_9, 0, x_135);
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_136; 
lean_dec(x_127);
lean_dec(x_126);
lean_free_object(x_102);
lean_dec(x_104);
lean_dec(x_90);
lean_free_object(x_9);
lean_dec(x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_136 = lean_box(0);
return x_136;
}
}
else
{
if (x_105 == 0)
{
lean_object* x_137; 
lean_ctor_set(x_102, 1, x_127);
lean_ctor_set(x_102, 0, x_126);
x_137 = lean_array_fset(x_88, x_90, x_102);
lean_dec(x_90);
lean_ctor_set(x_9, 1, x_104);
lean_ctor_set(x_9, 0, x_137);
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_138; 
lean_dec(x_127);
lean_dec(x_126);
lean_free_object(x_102);
lean_dec(x_104);
lean_dec(x_90);
lean_free_object(x_9);
lean_dec(x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_138 = lean_box(0);
return x_138;
}
}
}
else
{
lean_free_object(x_16);
if (x_105 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_inc(x_5);
x_139 = lean_array_uset(x_108, x_122, x_5);
lean_inc(x_3);
x_140 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_3, x_95, x_98, x_123);
x_141 = lean_array_uset(x_139, x_122, x_140);
lean_ctor_set(x_102, 1, x_141);
x_142 = lean_array_fset(x_88, x_90, x_102);
lean_dec(x_90);
lean_ctor_set(x_9, 1, x_104);
lean_ctor_set(x_9, 0, x_142);
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_143; 
lean_dec(x_123);
lean_free_object(x_102);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_90);
lean_free_object(x_9);
lean_dec(x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_143 = lean_box(0);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; uint64_t x_151; uint64_t x_152; uint64_t x_153; uint64_t x_154; size_t x_155; size_t x_156; size_t x_157; size_t x_158; size_t x_159; lean_object* x_160; uint8_t x_161; 
x_144 = lean_ctor_get(x_102, 0);
x_145 = lean_ctor_get(x_102, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_102);
x_146 = lean_array_get_size(x_145);
lean_inc(x_4);
lean_inc(x_95);
x_147 = lean_apply_1(x_4, x_95);
x_148 = lean_unbox_uint64(x_147);
lean_dec(x_147);
x_149 = 32;
x_150 = lean_uint64_shift_right(x_148, x_149);
x_151 = lean_uint64_xor(x_148, x_150);
x_152 = 16;
x_153 = lean_uint64_shift_right(x_151, x_152);
x_154 = lean_uint64_xor(x_151, x_153);
x_155 = lean_uint64_to_usize(x_154);
x_156 = lean_usize_of_nat(x_146);
lean_dec(x_146);
x_157 = 1;
x_158 = lean_usize_sub(x_156, x_157);
x_159 = lean_usize_land(x_155, x_158);
x_160 = lean_array_uget(x_145, x_159);
lean_inc(x_160);
lean_inc(x_95);
lean_inc(x_3);
x_161 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_3, x_95, x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_162 = lean_unsigned_to_nat(1u);
x_163 = lean_nat_add(x_144, x_162);
lean_dec(x_144);
lean_ctor_set(x_16, 2, x_160);
lean_ctor_set(x_16, 1, x_98);
lean_ctor_set(x_16, 0, x_95);
x_164 = lean_array_uset(x_145, x_159, x_16);
x_165 = lean_unsigned_to_nat(4u);
x_166 = lean_nat_mul(x_163, x_165);
x_167 = lean_unsigned_to_nat(3u);
x_168 = lean_nat_div(x_166, x_167);
lean_dec(x_166);
x_169 = lean_array_get_size(x_164);
x_170 = lean_nat_dec_le(x_168, x_169);
lean_dec(x_169);
lean_dec(x_168);
if (x_170 == 0)
{
if (x_105 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_inc(x_4);
x_171 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_4, x_164);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_163);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_array_fset(x_88, x_90, x_172);
lean_dec(x_90);
lean_ctor_set(x_9, 1, x_104);
lean_ctor_set(x_9, 0, x_173);
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_174; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_104);
lean_dec(x_90);
lean_free_object(x_9);
lean_dec(x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_174 = lean_box(0);
return x_174;
}
}
else
{
if (x_105 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_163);
lean_ctor_set(x_175, 1, x_164);
x_176 = lean_array_fset(x_88, x_90, x_175);
lean_dec(x_90);
lean_ctor_set(x_9, 1, x_104);
lean_ctor_set(x_9, 0, x_176);
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_177; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_104);
lean_dec(x_90);
lean_free_object(x_9);
lean_dec(x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_177 = lean_box(0);
return x_177;
}
}
}
else
{
lean_free_object(x_16);
if (x_105 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_inc(x_5);
x_178 = lean_array_uset(x_145, x_159, x_5);
lean_inc(x_3);
x_179 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_3, x_95, x_98, x_160);
x_180 = lean_array_uset(x_178, x_159, x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_144);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_array_fset(x_88, x_90, x_181);
lean_dec(x_90);
lean_ctor_set(x_9, 1, x_104);
lean_ctor_set(x_9, 0, x_182);
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_183; 
lean_dec(x_160);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_104);
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_90);
lean_free_object(x_9);
lean_dec(x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_183 = lean_box(0);
return x_183;
}
}
}
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_184 = lean_ctor_get(x_9, 0);
x_185 = lean_ctor_get(x_9, 1);
x_186 = lean_ctor_get(x_16, 0);
x_187 = lean_ctor_get(x_16, 1);
x_188 = lean_ctor_get(x_16, 2);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_16);
lean_inc(x_1);
x_189 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_185, x_187);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; 
lean_dec(x_188);
lean_dec(x_186);
lean_free_object(x_9);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_190 = lean_box(0);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
lean_dec(x_189);
lean_inc(x_1);
x_192 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_185, x_188);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
lean_dec(x_191);
lean_dec(x_186);
lean_free_object(x_9);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_193 = lean_box(0);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_array_get_size(x_184);
x_196 = lean_nat_dec_lt(x_186, x_195);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_191);
lean_dec(x_186);
lean_free_object(x_9);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_197 = lean_box(0);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; uint64_t x_210; uint64_t x_211; uint64_t x_212; uint64_t x_213; size_t x_214; size_t x_215; size_t x_216; size_t x_217; size_t x_218; lean_object* x_219; uint8_t x_220; 
x_198 = lean_array_fget(x_184, x_186);
x_199 = lean_box(0);
x_200 = lean_array_push(x_185, x_199);
x_201 = lean_nat_dec_le(x_195, x_186);
lean_dec(x_195);
x_202 = lean_ctor_get(x_198, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_198, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_204 = x_198;
} else {
 lean_dec_ref(x_198);
 x_204 = lean_box(0);
}
x_205 = lean_array_get_size(x_203);
lean_inc(x_4);
lean_inc(x_191);
x_206 = lean_apply_1(x_4, x_191);
x_207 = lean_unbox_uint64(x_206);
lean_dec(x_206);
x_208 = 32;
x_209 = lean_uint64_shift_right(x_207, x_208);
x_210 = lean_uint64_xor(x_207, x_209);
x_211 = 16;
x_212 = lean_uint64_shift_right(x_210, x_211);
x_213 = lean_uint64_xor(x_210, x_212);
x_214 = lean_uint64_to_usize(x_213);
x_215 = lean_usize_of_nat(x_205);
lean_dec(x_205);
x_216 = 1;
x_217 = lean_usize_sub(x_215, x_216);
x_218 = lean_usize_land(x_214, x_217);
x_219 = lean_array_uget(x_203, x_218);
lean_inc(x_219);
lean_inc(x_191);
lean_inc(x_3);
x_220 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_3, x_191, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_221 = lean_unsigned_to_nat(1u);
x_222 = lean_nat_add(x_202, x_221);
lean_dec(x_202);
x_223 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_223, 0, x_191);
lean_ctor_set(x_223, 1, x_194);
lean_ctor_set(x_223, 2, x_219);
x_224 = lean_array_uset(x_203, x_218, x_223);
x_225 = lean_unsigned_to_nat(4u);
x_226 = lean_nat_mul(x_222, x_225);
x_227 = lean_unsigned_to_nat(3u);
x_228 = lean_nat_div(x_226, x_227);
lean_dec(x_226);
x_229 = lean_array_get_size(x_224);
x_230 = lean_nat_dec_le(x_228, x_229);
lean_dec(x_229);
lean_dec(x_228);
if (x_230 == 0)
{
if (x_201 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_inc(x_4);
x_231 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_4, x_224);
if (lean_is_scalar(x_204)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_204;
}
lean_ctor_set(x_232, 0, x_222);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_array_fset(x_184, x_186, x_232);
lean_dec(x_186);
lean_ctor_set(x_9, 1, x_200);
lean_ctor_set(x_9, 0, x_233);
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_234; 
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_204);
lean_dec(x_200);
lean_dec(x_186);
lean_free_object(x_9);
lean_dec(x_184);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_234 = lean_box(0);
return x_234;
}
}
else
{
if (x_201 == 0)
{
lean_object* x_235; lean_object* x_236; 
if (lean_is_scalar(x_204)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_204;
}
lean_ctor_set(x_235, 0, x_222);
lean_ctor_set(x_235, 1, x_224);
x_236 = lean_array_fset(x_184, x_186, x_235);
lean_dec(x_186);
lean_ctor_set(x_9, 1, x_200);
lean_ctor_set(x_9, 0, x_236);
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_237; 
lean_dec(x_224);
lean_dec(x_222);
lean_dec(x_204);
lean_dec(x_200);
lean_dec(x_186);
lean_free_object(x_9);
lean_dec(x_184);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_237 = lean_box(0);
return x_237;
}
}
}
else
{
if (x_201 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_inc(x_5);
x_238 = lean_array_uset(x_203, x_218, x_5);
lean_inc(x_3);
x_239 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_3, x_191, x_194, x_219);
x_240 = lean_array_uset(x_238, x_218, x_239);
if (lean_is_scalar(x_204)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_204;
}
lean_ctor_set(x_241, 0, x_202);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_array_fset(x_184, x_186, x_241);
lean_dec(x_186);
lean_ctor_set(x_9, 1, x_200);
lean_ctor_set(x_9, 0, x_242);
x_10 = x_9;
goto block_14;
}
else
{
lean_object* x_243; 
lean_dec(x_219);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_194);
lean_dec(x_191);
lean_dec(x_186);
lean_free_object(x_9);
lean_dec(x_184);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_243 = lean_box(0);
return x_243;
}
}
}
}
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_244 = lean_ctor_get(x_9, 0);
x_245 = lean_ctor_get(x_9, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_9);
x_246 = lean_ctor_get(x_16, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_16, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_16, 2);
lean_inc(x_248);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_249 = x_16;
} else {
 lean_dec_ref(x_16);
 x_249 = lean_box(0);
}
lean_inc(x_1);
x_250 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_245, x_247);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_251 = lean_box(0);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
lean_dec(x_250);
lean_inc(x_1);
x_253 = l_semantics__zkexpr_eval___rarg(x_1, x_2, x_245, x_248);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; 
lean_dec(x_252);
lean_dec(x_249);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_254 = lean_box(0);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_array_get_size(x_244);
x_257 = lean_nat_dec_lt(x_246, x_256);
if (x_257 == 0)
{
lean_object* x_258; 
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_252);
lean_dec(x_249);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_258 = lean_box(0);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint64_t x_268; uint64_t x_269; uint64_t x_270; uint64_t x_271; uint64_t x_272; uint64_t x_273; uint64_t x_274; size_t x_275; size_t x_276; size_t x_277; size_t x_278; size_t x_279; lean_object* x_280; uint8_t x_281; 
x_259 = lean_array_fget(x_244, x_246);
x_260 = lean_box(0);
x_261 = lean_array_push(x_245, x_260);
x_262 = lean_nat_dec_le(x_256, x_246);
lean_dec(x_256);
x_263 = lean_ctor_get(x_259, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_259, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_265 = x_259;
} else {
 lean_dec_ref(x_259);
 x_265 = lean_box(0);
}
x_266 = lean_array_get_size(x_264);
lean_inc(x_4);
lean_inc(x_252);
x_267 = lean_apply_1(x_4, x_252);
x_268 = lean_unbox_uint64(x_267);
lean_dec(x_267);
x_269 = 32;
x_270 = lean_uint64_shift_right(x_268, x_269);
x_271 = lean_uint64_xor(x_268, x_270);
x_272 = 16;
x_273 = lean_uint64_shift_right(x_271, x_272);
x_274 = lean_uint64_xor(x_271, x_273);
x_275 = lean_uint64_to_usize(x_274);
x_276 = lean_usize_of_nat(x_266);
lean_dec(x_266);
x_277 = 1;
x_278 = lean_usize_sub(x_276, x_277);
x_279 = lean_usize_land(x_275, x_278);
x_280 = lean_array_uget(x_264, x_279);
lean_inc(x_280);
lean_inc(x_252);
lean_inc(x_3);
x_281 = l_Std_DHashMap_Internal_AssocList_contains___rarg(x_3, x_252, x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_282 = lean_unsigned_to_nat(1u);
x_283 = lean_nat_add(x_263, x_282);
lean_dec(x_263);
if (lean_is_scalar(x_249)) {
 x_284 = lean_alloc_ctor(1, 3, 0);
} else {
 x_284 = x_249;
}
lean_ctor_set(x_284, 0, x_252);
lean_ctor_set(x_284, 1, x_255);
lean_ctor_set(x_284, 2, x_280);
x_285 = lean_array_uset(x_264, x_279, x_284);
x_286 = lean_unsigned_to_nat(4u);
x_287 = lean_nat_mul(x_283, x_286);
x_288 = lean_unsigned_to_nat(3u);
x_289 = lean_nat_div(x_287, x_288);
lean_dec(x_287);
x_290 = lean_array_get_size(x_285);
x_291 = lean_nat_dec_le(x_289, x_290);
lean_dec(x_290);
lean_dec(x_289);
if (x_291 == 0)
{
if (x_262 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_inc(x_4);
x_292 = l_Std_DHashMap_Internal_Raw_u2080_expand___rarg(x_4, x_285);
if (lean_is_scalar(x_265)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_265;
}
lean_ctor_set(x_293, 0, x_283);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_array_fset(x_244, x_246, x_293);
lean_dec(x_246);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_261);
x_10 = x_295;
goto block_14;
}
else
{
lean_object* x_296; 
lean_dec(x_285);
lean_dec(x_283);
lean_dec(x_265);
lean_dec(x_261);
lean_dec(x_246);
lean_dec(x_244);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_296 = lean_box(0);
return x_296;
}
}
else
{
if (x_262 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
if (lean_is_scalar(x_265)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_265;
}
lean_ctor_set(x_297, 0, x_283);
lean_ctor_set(x_297, 1, x_285);
x_298 = lean_array_fset(x_244, x_246, x_297);
lean_dec(x_246);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_261);
x_10 = x_299;
goto block_14;
}
else
{
lean_object* x_300; 
lean_dec(x_285);
lean_dec(x_283);
lean_dec(x_265);
lean_dec(x_261);
lean_dec(x_246);
lean_dec(x_244);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_300 = lean_box(0);
return x_300;
}
}
}
else
{
lean_dec(x_249);
if (x_262 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_inc(x_5);
x_301 = lean_array_uset(x_264, x_279, x_5);
lean_inc(x_3);
x_302 = l_Std_DHashMap_Internal_AssocList_replace___rarg(x_3, x_252, x_255, x_280);
x_303 = lean_array_uset(x_301, x_279, x_302);
if (lean_is_scalar(x_265)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_265;
}
lean_ctor_set(x_304, 0, x_263);
lean_ctor_set(x_304, 1, x_303);
x_305 = lean_array_fset(x_244, x_246, x_304);
lean_dec(x_246);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_261);
x_10 = x_306;
goto block_14;
}
else
{
lean_object* x_307; 
lean_dec(x_280);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_261);
lean_dec(x_255);
lean_dec(x_252);
lean_dec(x_246);
lean_dec(x_244);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_307 = lean_box(0);
return x_307;
}
}
}
}
}
}
}
}
else
{
lean_object* x_308; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_9);
return x_308;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_7, x_11);
x_7 = x_12;
x_9 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_semantics__ram___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_semantics__ram___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
static lean_object* _init_l_semantics__ram___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_semantics__ram___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_semantics__ram___rarg___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_semantics__ram___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_semantics__ram___rarg___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_semantics__ram___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_semantics__ram___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_semantics__ram___rarg___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_semantics__ram___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l_semantics__ram___rarg___closed__3;
x_10 = lean_mk_array(x_5, x_9);
x_11 = l_semantics__ram___rarg___closed__4;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_get_size(x_4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = l_semantics__ram___rarg___closed__5;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_13, x_13);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_18 = l_semantics__ram___rarg___closed__5;
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_21 = l_Array_foldlMUnsafe_fold___at_semantics__ram___spec__1___rarg(x_1, x_2, x_6, x_7, x_8, x_4, x_19, x_20, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_semantics__ram(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_semantics__ram___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_semantics__ram___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = l_Array_foldlMUnsafe_fold___at_semantics__ram___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_9);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_semantics__ram___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_semantics__ram___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_semantics__constraints___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
lean_inc(x_1);
x_10 = l_semantics__zkexpr_eval___rarg(x_1, x_3, x_4, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_11 = 0;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = l_semantics__zkexpr_eval___rarg(x_1, x_3, x_4, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_14 = 0;
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_apply_2(x_16, x_12, x_15);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_1);
x_19 = 0;
return x_19;
}
else
{
x_2 = x_7;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_semantics__constraints(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_semantics__constraints___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_semantics__constraints___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_semantics__constraints___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_semantics___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_semantics__ram___rarg(x_1, x_2, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_semantics__constraints___rarg(x_1, x_9, x_2, x_8);
lean_dec(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_semantics(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_semantics___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_semantics___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_semantics___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Field_Defs(uint8_t builtin, lean_object*);
lean_object* initialize_ZkLean_AST(uint8_t builtin, lean_object*);
lean_object* initialize_ZkLean_Builder(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Prelude(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Set(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ZkLean_Semantics(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Field_Defs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ZkLean_AST(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ZkLean_Builder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Prelude(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Set(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_semantics__ram___rarg___closed__1 = _init_l_semantics__ram___rarg___closed__1();
lean_mark_persistent(l_semantics__ram___rarg___closed__1);
l_semantics__ram___rarg___closed__2 = _init_l_semantics__ram___rarg___closed__2();
lean_mark_persistent(l_semantics__ram___rarg___closed__2);
l_semantics__ram___rarg___closed__3 = _init_l_semantics__ram___rarg___closed__3();
lean_mark_persistent(l_semantics__ram___rarg___closed__3);
l_semantics__ram___rarg___closed__4 = _init_l_semantics__ram___rarg___closed__4();
lean_mark_persistent(l_semantics__ram___rarg___closed__4);
l_semantics__ram___rarg___closed__5 = _init_l_semantics__ram___rarg___closed__5();
lean_mark_persistent(l_semantics__ram___rarg___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
