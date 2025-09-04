import ZkLean.Formalism
import ZkLean.solve_mle


set_option maxHeartbeats  20000000000000000000

def AND_64 [Field f] : Subtable f 64 :=
  subtableFromMLE (fun x => 0 + 2147483648*x[0]*x[1] + 1073741824*x[2]*x[3] + 536870912*x[4]*x[5] + 268435456*x[6]*x[7] + 134217728*x[8]*x[9] + 67108864*x[10]*x[11] + 33554432*x[12]*x[13] + 16777216*x[14]*x[15] + 8388608*x[16]*x[17] + 4194304*x[18]*x[19] + 2097152*x[20]*x[21] + 1048576*x[22]*x[23] + 524288*x[24]*x[25] + 262144*x[26]*x[27] + 131072*x[28]*x[29] + 65536*x[30]*x[31] + 32768*x[32]*x[33] + 16384*x[34]*x[35] + 8192*x[36]*x[37] + 4096*x[38]*x[39] + 2048*x[40]*x[41] + 1024*x[42]*x[43] + 512*x[44]*x[45] + 256*x[46]*x[47] + 128*x[48]*x[49] + 64*x[50]*x[51] + 32*x[52]*x[53] + 16*x[54]*x[55] + 8*x[56]*x[57] + 4*x[58]*x[59] + 2*x[60]*x[61] + 1*x[62]*x[63])

lemma and_32_mle_one_chunk_[ZKField f] (bv1 bv2 : BitVec 32) (fv1 fv2 : Vector f 32) :
  some bvoutput = map_f_to_bv_32 foutput ->
   some (bool_to_bv_32 bv1[31])  = map_f_to_bv_32 fv1[0]  ->
   some (bool_to_bv_32 bv2[31]) =map_f_to_bv_32 fv1[1]  ->
   some (bool_to_bv_32 bv1[30]) = map_f_to_bv_32 fv1[2]  ->
   some (bool_to_bv_32 bv2[30]) = map_f_to_bv_32 fv1[3]  ->
   some (bool_to_bv_32 bv1[29]) = map_f_to_bv_32 fv1[4]  ->
   some (bool_to_bv_32 bv2[29]) = map_f_to_bv_32 fv1[5]  ->
   some (bool_to_bv_32 bv1[28]) = map_f_to_bv_32 fv1[6]  ->
   some (bool_to_bv_32 bv2[28]) = map_f_to_bv_32 fv1[7]  ->
   some (bool_to_bv_32 bv1[27])  = map_f_to_bv_32 fv1[8]  ->
   some (bool_to_bv_32 bv2[27]) = map_f_to_bv_32 fv1[9]  ->
   some (bool_to_bv_32 bv1[26]) = map_f_to_bv_32 fv1[10]  ->
   some (bool_to_bv_32 bv2[26]) = map_f_to_bv_32 fv1[11]  ->
   some (bool_to_bv_32 bv1[25]) = map_f_to_bv_32 fv1[12]  ->
   some (bool_to_bv_32 bv2[25]) = map_f_to_bv_32 fv1[13]  ->
   some (bool_to_bv_32 bv1[24]) = map_f_to_bv_32 fv1[14]  ->
   some (bool_to_bv_32 bv2[24]) = map_f_to_bv_32 fv1[15]  ->
   some (bool_to_bv_32 bv1[23])  = map_f_to_bv_32 fv1[16]  ->
   some (bool_to_bv_32 bv2[23]) =map_f_to_bv_32 fv1[17]  ->
   some (bool_to_bv_32 bv1[22]) = map_f_to_bv_32 fv1[18]  ->
   some (bool_to_bv_32 bv2[22]) = map_f_to_bv_32 fv1[19]  ->
   some (bool_to_bv_32 bv1[21]) = map_f_to_bv_32 fv1[20]  ->
   some (bool_to_bv_32 bv2[21]) = map_f_to_bv_32 fv1[21]  ->
   some (bool_to_bv_32 bv1[20]) = map_f_to_bv_32 fv1[22]  ->
   some (bool_to_bv_32 bv2[20]) = map_f_to_bv_32 fv1[23]  ->
   some (bool_to_bv_32 bv1[19])  = map_f_to_bv_32 fv1[24]  ->
   some (bool_to_bv_32 bv2[19]) =map_f_to_bv_32 fv1[25]  ->
   some (bool_to_bv_32 bv1[18]) = map_f_to_bv_32 fv1[26]  ->
   some (bool_to_bv_32 bv2[18]) = map_f_to_bv_32 fv1[27]  ->
   some (bool_to_bv_32 bv1[17]) = map_f_to_bv_32 fv1[28]  ->
   some (bool_to_bv_32 bv2[17]) = map_f_to_bv_32 fv1[29]  ->
   some (bool_to_bv_32 bv1[16]) = map_f_to_bv_32 fv1[30]  ->
   some (bool_to_bv_32 bv2[16]) = map_f_to_bv_32 fv1[31]  ->
  some (bool_to_bv_32 bv1[15])  = map_f_to_bv_32 fv2[0]  ->
   some (bool_to_bv_32 bv2[15]) =map_f_to_bv_32 fv2[1]  ->
   some (bool_to_bv_32 bv1[14]) = map_f_to_bv_32 fv2[2]  ->
   some (bool_to_bv_32 bv2[14]) = map_f_to_bv_32 fv2[3]  ->
   some (bool_to_bv_32 bv1[13]) = map_f_to_bv_32 fv2[4]  ->
   some (bool_to_bv_32 bv2[13]) = map_f_to_bv_32 fv2[5]  ->
   some (bool_to_bv_32 bv1[12]) = map_f_to_bv_32 fv2[6]  ->
   some (bool_to_bv_32 bv2[12]) = map_f_to_bv_32 fv2[7]  ->
  some (bool_to_bv_32 bv1[11]) = map_f_to_bv_32 fv2[8]  ->
  some (bool_to_bv_32 bv2[11]) = map_f_to_bv_32 fv2[9]  ->
  some (bool_to_bv_32 bv1[10]) = map_f_to_bv_32  fv2[10]  ->
  some (bool_to_bv_32 bv2[10]) = map_f_to_bv_32 fv2[11]  ->
  some (bool_to_bv_32 bv1[9]) = map_f_to_bv_32 fv2[12]  ->
  some (bool_to_bv_32 bv2[9]) = map_f_to_bv_32 fv2[13]  ->
  some (bool_to_bv_32 bv1[8]) = map_f_to_bv_32 fv2[14]  ->
  some (bool_to_bv_32 bv2[8]) = map_f_to_bv_32 fv2[15]  ->
   some (bool_to_bv_32 bv1[7])  = map_f_to_bv_32 fv2[16]  ->
   some (bool_to_bv_32 bv2[7]) =map_f_to_bv_32 fv2[17]  ->
   some (bool_to_bv_32 bv1[6]) = map_f_to_bv_32 fv2[18]  ->
   some (bool_to_bv_32 bv2[6]) = map_f_to_bv_32 fv2[19]  ->
   some (bool_to_bv_32 bv1[5]) = map_f_to_bv_32 fv2[20]  ->
   some (bool_to_bv_32 bv2[5]) = map_f_to_bv_32 fv2[21]  ->
   some (bool_to_bv_32 bv1[4]) = map_f_to_bv_32 fv2[22]  ->
   some (bool_to_bv_32 bv2[4]) = map_f_to_bv_32 fv2[23]  ->
  some (bool_to_bv_32 bv1[3]) = map_f_to_bv_32 fv2[24]  ->
  some (bool_to_bv_32 bv2[3]) = map_f_to_bv_32 fv2[25]  ->
  some (bool_to_bv_32 bv1[2]) = map_f_to_bv_32  fv2[26]  ->
  some (bool_to_bv_32 bv2[2]) = map_f_to_bv_32 fv2[27]  ->
  some (bool_to_bv_32 bv1[1]) = map_f_to_bv_32 fv2[28]  ->
  some (bool_to_bv_32 bv2[1]) = map_f_to_bv_32 fv2[29]  ->
  some (bool_to_bv_32 bv1[0]) = map_f_to_bv_32 fv2[30]  ->
  some (bool_to_bv_32 bv2[0]) = map_f_to_bv_32 fv2[31]  ->
  (bvoutput = (bv1 &&& bv2))
  =
  (foutput = evalSubtable AND_64 (Vector.append fv1 fv2))
:= by
 solveMLE AND_64 32
