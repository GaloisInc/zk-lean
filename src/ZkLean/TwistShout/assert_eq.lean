import ZkLean.Formalism
import ZkLean.solve_mle


set_option maxHeartbeats  20000000000000000000

def VirtualAssertEQ_32 [Field f] : Subtable f 64 :=
  subtableFromMLE (fun x => (x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[2]*x[3] + (1 - x[2])*(1 - x[3]))*(x[4]*x[5] + (1 - x[4])*(1 - x[5]))*(x[6]*x[7] + (1 - x[6])*(1 - x[7]))*(x[8]*x[9] + (1 - x[8])*(1 - x[9]))*(x[10]*x[11] + (1 - x[10])*(1 - x[11]))*(x[12]*x[13] + (1 - x[12])*(1 - x[13]))*(x[14]*x[15] + (1 - x[14])*(1 - x[15]))*(x[16]*x[17] + (1 - x[16])*(1 - x[17]))*(x[18]*x[19] + (1 - x[18])*(1 - x[19]))*(x[20]*x[21] + (1 - x[20])*(1 - x[21]))*(x[22]*x[23] + (1 - x[22])*(1 - x[23]))*(x[24]*x[25] + (1 - x[24])*(1 - x[25]))*(x[26]*x[27] + (1 - x[26])*(1 - x[27]))*(x[28]*x[29] + (1 - x[28])*(1 - x[29]))*(x[30]*x[31] + (1 - x[30])*(1 - x[31]))*(x[32]*x[33] + (1 - x[32])*(1 - x[33]))*(x[34]*x[35] + (1 - x[34])*(1 - x[35]))*(x[36]*x[37] + (1 - x[36])*(1 - x[37]))*(x[38]*x[39] + (1 - x[38])*(1 - x[39]))*(x[40]*x[41] + (1 - x[40])*(1 - x[41]))*(x[42]*x[43] + (1 - x[42])*(1 - x[43]))*(x[44]*x[45] + (1 - x[44])*(1 - x[45]))*(x[46]*x[47] + (1 - x[46])*(1 - x[47]))*(x[48]*x[49] + (1 - x[48])*(1 - x[49]))*(x[50]*x[51] + (1 - x[50])*(1 - x[51]))*(x[52]*x[53] + (1 - x[52])*(1 - x[53]))*(x[54]*x[55] + (1 - x[54])*(1 - x[55]))*(x[56]*x[57] + (1 - x[56])*(1 - x[57]))*(x[58]*x[59] + (1 - x[58])*(1 - x[59]))*(x[60]*x[61] + (1 - x[60])*(1 - x[61]))*(x[62]*x[63] + (1 - x[62])*(1 - x[63])))


lemma eq_mle_one_chunk_[ZKField f] (bv1 bv2 : BitVec 32) (fv1 fv2 : Vector f 32) :
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
  (bvoutput = bool_to_bv_32 (bv1 = bv2))
  =
  (foutput = evalSubtable VirtualAssertEQ_32 (Vector.append fv1 fv2))
:= by
 --unfold bool_to_bv_32
 solveMLE VirtualAssertEQ_32 32
