import ZkLean.Formalism
import ZkLean.solve_mle


set_option maxHeartbeats  20000000000000000000

def VirtualShiftRightBitmask_32 [Field f] : Subtable f 64 :=
  subtableFromMLE (fun x => 4294967295*1*(1 - x[63])*(1 - x[62])*(1 - x[61])*(1 - x[60])*(1 - x[59]) + 4294967294*1*x[63]*(1 - x[62])*(1 - x[61])*(1 - x[60])*(1 - x[59]) + 4294967292*1*(1 - x[63])*x[62]*(1 - x[61])*(1 - x[60])*(1 - x[59]) + 4294967288*1*x[63]*x[62]*(1 - x[61])*(1 - x[60])*(1 - x[59]) + 4294967280*1*(1 - x[63])*(1 - x[62])*x[61]*(1 - x[60])*(1 - x[59]) + 4294967264*1*x[63]*(1 - x[62])*x[61]*(1 - x[60])*(1 - x[59]) + 4294967232*1*(1 - x[63])*x[62]*x[61]*(1 - x[60])*(1 - x[59]) + 4294967168*1*x[63]*x[62]*x[61]*(1 - x[60])*(1 - x[59]) + 4294967040*1*(1 - x[63])*(1 - x[62])*(1 - x[61])*x[60]*(1 - x[59]) + 4294966784*1*x[63]*(1 - x[62])*(1 - x[61])*x[60]*(1 - x[59]) + 4294966272*1*(1 - x[63])*x[62]*(1 - x[61])*x[60]*(1 - x[59]) + 4294965248*1*x[63]*x[62]*(1 - x[61])*x[60]*(1 - x[59]) + 4294963200*1*(1 - x[63])*(1 - x[62])*x[61]*x[60]*(1 - x[59]) + 4294959104*1*x[63]*(1 - x[62])*x[61]*x[60]*(1 - x[59]) + 4294950912*1*(1 - x[63])*x[62]*x[61]*x[60]*(1 - x[59]) + 4294934528*1*x[63]*x[62]*x[61]*x[60]*(1 - x[59]) + 4294901760*1*(1 - x[63])*(1 - x[62])*(1 - x[61])*(1 - x[60])*x[59] + 4294836224*1*x[63]*(1 - x[62])*(1 - x[61])*(1 - x[60])*x[59] + 4294705152*1*(1 - x[63])*x[62]*(1 - x[61])*(1 - x[60])*x[59] + 4294443008*1*x[63]*x[62]*(1 - x[61])*(1 - x[60])*x[59] + 4293918720*1*(1 - x[63])*(1 - x[62])*x[61]*(1 - x[60])*x[59] + 4292870144*1*x[63]*(1 - x[62])*x[61]*(1 - x[60])*x[59] + 4290772992*1*(1 - x[63])*x[62]*x[61]*(1 - x[60])*x[59] + 4286578688*1*x[63]*x[62]*x[61]*(1 - x[60])*x[59] + 4278190080*1*(1 - x[63])*(1 - x[62])*(1 - x[61])*x[60]*x[59] + 4261412864*1*x[63]*(1 - x[62])*(1 - x[61])*x[60]*x[59] + 4227858432*1*(1 - x[63])*x[62]*(1 - x[61])*x[60]*x[59] + 4160749568*1*x[63]*x[62]*(1 - x[61])*x[60]*x[59] + 4026531840*1*(1 - x[63])*(1 - x[62])*x[61]*x[60]*x[59] + 3758096384*1*x[63]*(1 - x[62])*x[61]*x[60]*x[59] + 3221225472*1*(1 - x[63])*x[62]*x[61]*x[60]*x[59] + 2147483648*1*x[63]*x[62]*x[61]*x[60]*x[59])



lemma shift_right_bit_mask_32_mle_one_chunk_[ZKField f] (bv1 bv2 : BitVec 32) (fv1 fv2 : Vector f 32) :
  some bvoutput = map_f_to_bv_32 foutput ->
    some (bool_to_bv_32 bv1[31])  = map_f_to_bv_32 fv1[0]  ->
   some (bool_to_bv_32 bv1[30]) =map_f_to_bv_32 fv1[1]  ->
   some (bool_to_bv_32 bv1[29]) = map_f_to_bv_32 fv1[2]  ->
   some (bool_to_bv_32 bv1[28]) = map_f_to_bv_32 fv1[3]  ->
   some (bool_to_bv_32 bv1[27]) = map_f_to_bv_32 fv1[4]  ->
   some (bool_to_bv_32 bv1[26]) = map_f_to_bv_32 fv1[5]  ->
   some (bool_to_bv_32 bv1[25]) = map_f_to_bv_32 fv1[6]  ->
   some (bool_to_bv_32 bv1[24]) = map_f_to_bv_32 fv1[7]  ->
   some (bool_to_bv_32 bv1[23])  = map_f_to_bv_32 fv1[8]  ->
   some (bool_to_bv_32 bv1[22]) = map_f_to_bv_32 fv1[9]  ->
   some (bool_to_bv_32 bv1[21]) = map_f_to_bv_32 fv1[10]  ->
   some (bool_to_bv_32 bv1[20]) = map_f_to_bv_32 fv1[11]  ->
   some (bool_to_bv_32 bv1[19]) = map_f_to_bv_32 fv1[12]  ->
   some (bool_to_bv_32 bv1[18]) = map_f_to_bv_32 fv1[13]  ->
   some (bool_to_bv_32 bv1[17]) = map_f_to_bv_32 fv1[14]  ->
   some (bool_to_bv_32 bv1[16]) = map_f_to_bv_32 fv1[15]  ->
   some (bool_to_bv_32 bv1[15])  = map_f_to_bv_32 fv1[16]  ->
   some (bool_to_bv_32 bv1[14]) =map_f_to_bv_32 fv1[17]  ->
   some (bool_to_bv_32 bv1[13]) = map_f_to_bv_32 fv1[18]  ->
   some (bool_to_bv_32 bv1[12]) = map_f_to_bv_32 fv1[19]  ->
   some (bool_to_bv_32 bv1[11]) = map_f_to_bv_32 fv1[20]  ->
   some (bool_to_bv_32 bv1[10]) = map_f_to_bv_32 fv1[21]  ->
   some (bool_to_bv_32 bv1[9]) = map_f_to_bv_32 fv1[22]  ->
   some (bool_to_bv_32 bv1[8]) = map_f_to_bv_32 fv1[23]  ->
   some (bool_to_bv_32 bv1[7])  = map_f_to_bv_32 fv1[24]  ->
   some (bool_to_bv_32 bv1[6]) =map_f_to_bv_32 fv1[25]  ->
   some (bool_to_bv_32 bv1[5]) = map_f_to_bv_32 fv1[26]  ->
   some (bool_to_bv_32 bv1[4]) = map_f_to_bv_32 fv1[27]  ->
   some (bool_to_bv_32 bv1[3]) = map_f_to_bv_32 fv1[28]  ->
   some (bool_to_bv_32 bv1[2]) = map_f_to_bv_32 fv1[29]  ->
   some (bool_to_bv_32 bv1[1]) = map_f_to_bv_32 fv1[30]  ->
   some (bool_to_bv_32 bv1[0]) = map_f_to_bv_32 fv1[31]  ->
  some (bool_to_bv_32 bv2[31])  = map_f_to_bv_32 fv2[0]  ->
   some (bool_to_bv_32 bv2[30]) =map_f_to_bv_32 fv2[1]  ->
   some (bool_to_bv_32 bv2[29]) = map_f_to_bv_32 fv2[2]  ->
   some (bool_to_bv_32 bv2[28]) = map_f_to_bv_32 fv2[3]  ->
   some (bool_to_bv_32 bv2[27]) = map_f_to_bv_32 fv2[4]  ->
   some (bool_to_bv_32 bv2[26]) = map_f_to_bv_32 fv2[5]  ->
   some (bool_to_bv_32 bv2[25]) = map_f_to_bv_32 fv2[6]  ->
   some (bool_to_bv_32 bv2[24]) = map_f_to_bv_32 fv2[7]  ->
  some (bool_to_bv_32 bv2[23]) = map_f_to_bv_32 fv2[8]  ->
  some (bool_to_bv_32 bv2[22]) = map_f_to_bv_32 fv2[9]  ->
  some (bool_to_bv_32 bv2[21]) = map_f_to_bv_32  fv2[10]  ->
  some (bool_to_bv_32 bv2[20]) = map_f_to_bv_32 fv2[11]  ->
  some (bool_to_bv_32 bv2[19]) = map_f_to_bv_32 fv2[12]  ->
  some (bool_to_bv_32 bv2[18]) = map_f_to_bv_32 fv2[13]  ->
  some (bool_to_bv_32 bv2[17]) = map_f_to_bv_32 fv2[14]  ->
  some (bool_to_bv_32 bv2[16]) = map_f_to_bv_32 fv2[15]  ->
   some (bool_to_bv_32 bv2[15])  = map_f_to_bv_32 fv2[16]  ->
   some (bool_to_bv_32 bv2[14]) =map_f_to_bv_32 fv2[17]  ->
   some (bool_to_bv_32 bv2[13]) = map_f_to_bv_32 fv2[18]  ->
   some (bool_to_bv_32 bv2[12]) = map_f_to_bv_32 fv2[19]  ->
   some (bool_to_bv_32 bv2[11]) = map_f_to_bv_32 fv2[20]  ->
   some (bool_to_bv_32 bv2[10]) = map_f_to_bv_32 fv2[21]  ->
   some (bool_to_bv_32 bv2[9]) = map_f_to_bv_32 fv2[22]  ->
   some (bool_to_bv_32 bv2[8]) = map_f_to_bv_32 fv2[23]  ->
  some (bool_to_bv_32 bv2[7]) = map_f_to_bv_32 fv2[24]  ->
  some (bool_to_bv_32 bv2[6]) = map_f_to_bv_32 fv2[25]  ->
  some (bool_to_bv_32 bv2[5]) = map_f_to_bv_32  fv2[26]  ->
  some (bool_to_bv_32 bv2[4]) = map_f_to_bv_32 fv2[27]  ->
  some (bool_to_bv_32 bv2[3]) = map_f_to_bv_32 fv2[28]  ->
  some (bool_to_bv_32 bv2[2]) = map_f_to_bv_32 fv2[29]  ->
  some (bool_to_bv_32 bv2[1]) = map_f_to_bv_32 fv2[30]  ->
  some (bool_to_bv_32 bv2[0]) = map_f_to_bv_32 fv2[31] ->
 ((bvoutput = ~~~ (((((1#32 + (((bv2 >>> 0) &&& 1#32) * 1#32))
       * (1#32 + (((bv2 >>> 1) &&& 1#32) * 3#32)))
       * (1#32 + (((bv2 >>> 2) &&& 1#32) * 15#32)))
       * (1#32 + (((bv2 >>> 3) &&& 1#32) * 255#32)))
       * (1#32 + (((bv2 >>> 4) &&& 1#32) * 65535#32))
     - 1#32))
  =
  (foutput = evalSubtable VirtualShiftRightBitmask_32 (Vector.append fv1 fv2))) := by
    solveMLE VirtualShiftRightBitmask_32  32

    -- rw [ Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
    -- rw [<- Nat.mul_comm_ofNat ]
    -- rw [<- Nat.mul_comm_ofNat]
