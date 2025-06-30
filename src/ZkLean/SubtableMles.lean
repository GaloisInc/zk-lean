import Jolt.R1CS
import ZkLean
import Jolt.Instructions
import Jolt.Subtables


structure JoltR1CSInputs (f : Type) : Type where
  Bytecode_A : ZKExpr f
  Bytecode_ELFAddress : ZKExpr f
  Bytecode_Bitflags : ZKExpr f
  Bytecode_RS1 : ZKExpr f
  Bytecode_RS2 : ZKExpr f
  Bytecode_RD : ZKExpr f
  Bytecode_Imm : ZKExpr f
  RAM_Address : ZKExpr f
  RS1_Read : ZKExpr f
  RS2_Read : ZKExpr f
  RD_Read : ZKExpr f
  RAM_Read : ZKExpr f
  RD_Write : ZKExpr f
  RAM_Write : ZKExpr f
  ChunksQuery_0 : ZKExpr f
  ChunksQuery_1 : ZKExpr f
  ChunksQuery_2 : ZKExpr f
  ChunksQuery_3 : ZKExpr f
  LookupOutput : ZKExpr f
  ChunksX_0 : ZKExpr f
  ChunksX_1 : ZKExpr f
  ChunksX_2 : ZKExpr f
  ChunksX_3 : ZKExpr f
  ChunksY_0 : ZKExpr f
  ChunksY_1 : ZKExpr f
  ChunksY_2 : ZKExpr f
  ChunksY_3 : ZKExpr f
  OpFlags_LeftOperandIsPC : ZKExpr f
  OpFlags_RightOperandIsImm : ZKExpr f
  OpFlags_Load : ZKExpr f
  OpFlags_Store : ZKExpr f
  OpFlags_Jump : ZKExpr f
  OpFlags_Branch : ZKExpr f
  OpFlags_Lui : ZKExpr f
  OpFlags_WriteLookupOutputToRD : ZKExpr f
  OpFlags_ConcatLookupQueryChunks : ZKExpr f
  OpFlags_Virtual : ZKExpr f
  OpFlags_Assert : ZKExpr f
  OpFlags_DoNotUpdatePC : ZKExpr f
  InstructionFlags_ADD_ADDInstruction_0_0 : ZKExpr f
  InstructionFlags_SUB_SUBInstruction_0_0 : ZKExpr f
  InstructionFlags_AND_ANDInstruction_0_0 : ZKExpr f
  InstructionFlags_OR_ORInstruction_0_0 : ZKExpr f
  InstructionFlags_XOR_XORInstruction_0_0 : ZKExpr f
  InstructionFlags_BEQ_BEQInstruction_0_0 : ZKExpr f
  InstructionFlags_BGE_BGEInstruction_0_0 : ZKExpr f
  InstructionFlags_BGEU_BGEUInstruction_0_0 : ZKExpr f
  InstructionFlags_BNE_BNEInstruction_0_0 : ZKExpr f
  InstructionFlags_SLT_SLTInstruction_0_0 : ZKExpr f
  InstructionFlags_SLTU_SLTUInstruction_0_0 : ZKExpr f
  InstructionFlags_SLL_SLLInstruction_0_0 : ZKExpr f
  InstructionFlags_SRA_SRAInstruction_0_0 : ZKExpr f
  InstructionFlags_SRL_SRLInstruction_0_0 : ZKExpr f
  InstructionFlags_MOVSIGN_MOVSIGNInstruction_0 : ZKExpr f
  InstructionFlags_MUL_MULInstruction_0_0 : ZKExpr f
  InstructionFlags_MULU_MULUInstruction_0_0 : ZKExpr f
  InstructionFlags_MULHU_MULHUInstruction_0_0 : ZKExpr f
  InstructionFlags_VIRTUAL_ADVICE_ADVICEInstruction_0 : ZKExpr f
  InstructionFlags_VIRTUAL_MOVE_MOVEInstruction_0 : ZKExpr f
  InstructionFlags_VIRTUAL_ASSERT_LTE_ASSERTLTEInstruction_0_0 : ZKExpr f
  InstructionFlags_VIRTUAL_ASSERT_VALID_SIGNED_REMAINDER_AssertValidSignedRemainderInstruction_0_0 : ZKExpr f
  InstructionFlags_VIRTUAL_ASSERT_VALID_UNSIGNED_REMAINDER_AssertValidUnsignedRemainderInstruction_0_0 : ZKExpr f
  InstructionFlags_VIRTUAL_ASSERT_VALID_DIV0_AssertValidDiv0Instruction_0_0 : ZKExpr f
  InstructionFlags_VIRTUAL_ASSERT_HALFWORD_ALIGNMENT_AssertHalfwordAlignmentInstruction_0_0 : ZKExpr f
  InstructionFlags_VIRTUAL_POW2_POW2Instruction_0 : ZKExpr f
  InstructionFlags_VIRTUAL_SRA_PADDING_RightShiftPaddingInstruction_0 : ZKExpr f
  Aux_LeftLookupOperand : ZKExpr f
  Aux_RightLookupOperand : ZKExpr f
  Aux_Product : ZKExpr f
  Aux_RelevantYChunk_0 : ZKExpr f
  Aux_RelevantYChunk_1 : ZKExpr f
  Aux_RelevantYChunk_2 : ZKExpr f
  Aux_RelevantYChunk_3 : ZKExpr f
  Aux_WriteLookupOutputToRD : ZKExpr f
  Aux_WritePCtoRD : ZKExpr f
  Aux_NextPCJump : ZKExpr f
  Aux_ShouldBranch : ZKExpr f
  Aux_NextPC : ZKExpr f

instance: Witnessable f (JoltR1CSInputs f) where
  witness := do
    let Bytecode_A <- Witnessable.witness
    let Bytecode_ELFAddress <- Witnessable.witness
    let Bytecode_Bitflags <- Witnessable.witness
    let Bytecode_RS1 <- Witnessable.witness
    let Bytecode_RS2 <- Witnessable.witness
    let Bytecode_RD <- Witnessable.witness
    let Bytecode_Imm <- Witnessable.witness
    let RAM_Address <- Witnessable.witness
    let RS1_Read <- Witnessable.witness
    let RS2_Read <- Witnessable.witness
    let RD_Read <- Witnessable.witness
    let RAM_Read <- Witnessable.witness
    let RD_Write <- Witnessable.witness
    let RAM_Write <- Witnessable.witness
    let ChunksQuery_0 <- Witnessable.witness
    let ChunksQuery_1 <- Witnessable.witness
    let ChunksQuery_2 <- Witnessable.witness
    let ChunksQuery_3 <- Witnessable.witness
    let LookupOutput <- Witnessable.witness
    let ChunksX_0 <- Witnessable.witness
    let ChunksX_1 <- Witnessable.witness
    let ChunksX_2 <- Witnessable.witness
    let ChunksX_3 <- Witnessable.witness
    let ChunksY_0 <- Witnessable.witness
    let ChunksY_1 <- Witnessable.witness
    let ChunksY_2 <- Witnessable.witness
    let ChunksY_3 <- Witnessable.witness
    let OpFlags_LeftOperandIsPC <- Witnessable.witness
    let OpFlags_RightOperandIsImm <- Witnessable.witness
    let OpFlags_Load <- Witnessable.witness
    let OpFlags_Store <- Witnessable.witness
    let OpFlags_Jump <- Witnessable.witness
    let OpFlags_Branch <- Witnessable.witness
    let OpFlags_Lui <- Witnessable.witness
    let OpFlags_WriteLookupOutputToRD <- Witnessable.witness
    let OpFlags_ConcatLookupQueryChunks <- Witnessable.witness
    let OpFlags_Virtual <- Witnessable.witness
    let OpFlags_Assert <- Witnessable.witness
    let OpFlags_DoNotUpdatePC <- Witnessable.witness
    let InstructionFlags_ADD_ADDInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_SUB_SUBInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_AND_ANDInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_OR_ORInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_XOR_XORInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_BEQ_BEQInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_BGE_BGEInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_BGEU_BGEUInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_BNE_BNEInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_SLT_SLTInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_SLTU_SLTUInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_SLL_SLLInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_SRA_SRAInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_SRL_SRLInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_MOVSIGN_MOVSIGNInstruction_0 <- Witnessable.witness
    let InstructionFlags_MUL_MULInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_MULU_MULUInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_MULHU_MULHUInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_VIRTUAL_ADVICE_ADVICEInstruction_0 <- Witnessable.witness
    let InstructionFlags_VIRTUAL_MOVE_MOVEInstruction_0 <- Witnessable.witness
    let InstructionFlags_VIRTUAL_ASSERT_LTE_ASSERTLTEInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_VIRTUAL_ASSERT_VALID_SIGNED_REMAINDER_AssertValidSignedRemainderInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_VIRTUAL_ASSERT_VALID_UNSIGNED_REMAINDER_AssertValidUnsignedRemainderInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_VIRTUAL_ASSERT_VALID_DIV0_AssertValidDiv0Instruction_0_0 <- Witnessable.witness
    let InstructionFlags_VIRTUAL_ASSERT_HALFWORD_ALIGNMENT_AssertHalfwordAlignmentInstruction_0_0 <- Witnessable.witness
    let InstructionFlags_VIRTUAL_POW2_POW2Instruction_0 <- Witnessable.witness
    let InstructionFlags_VIRTUAL_SRA_PADDING_RightShiftPaddingInstruction_0 <- Witnessable.witness
    let Aux_LeftLookupOperand <- Witnessable.witness
    let Aux_RightLookupOperand <- Witnessable.witness
    let Aux_Product <- Witnessable.witness
    let Aux_RelevantYChunk_0 <- Witnessable.witness
    let Aux_RelevantYChunk_1 <- Witnessable.witness
    let Aux_RelevantYChunk_2 <- Witnessable.witness
    let Aux_RelevantYChunk_3 <- Witnessable.witness
    let Aux_WriteLookupOutputToRD <- Witnessable.witness
    let Aux_WritePCtoRD <- Witnessable.witness
    let Aux_NextPCJump <- Witnessable.witness
    let Aux_ShouldBranch <- Witnessable.witness
    let Aux_NextPC <- Witnessable.witness

    pure {
      Bytecode_A := Bytecode_A
      Bytecode_ELFAddress := Bytecode_ELFAddress
      Bytecode_Bitflags := Bytecode_Bitflags
      Bytecode_RS1 := Bytecode_RS1
      Bytecode_RS2 := Bytecode_RS2
      Bytecode_RD := Bytecode_RD
      Bytecode_Imm := Bytecode_Imm
      RAM_Address := RAM_Address
      RS1_Read := RS1_Read
      RS2_Read := RS2_Read
      RD_Read := RD_Read
      RAM_Read := RAM_Read
      RD_Write := RD_Write
      RAM_Write := RAM_Write
      ChunksQuery_0 := ChunksQuery_0
      ChunksQuery_1 := ChunksQuery_1
      ChunksQuery_2 := ChunksQuery_2
      ChunksQuery_3 := ChunksQuery_3
      LookupOutput := LookupOutput
      ChunksX_0 := ChunksX_0
      ChunksX_1 := ChunksX_1
      ChunksX_2 := ChunksX_2
      ChunksX_3 := ChunksX_3
      ChunksY_0 := ChunksY_0
      ChunksY_1 := ChunksY_1
      ChunksY_2 := ChunksY_2
      ChunksY_3 := ChunksY_3
      OpFlags_LeftOperandIsPC := OpFlags_LeftOperandIsPC
      OpFlags_RightOperandIsImm := OpFlags_RightOperandIsImm
      OpFlags_Load := OpFlags_Load
      OpFlags_Store := OpFlags_Store
      OpFlags_Jump := OpFlags_Jump
      OpFlags_Branch := OpFlags_Branch
      OpFlags_Lui := OpFlags_Lui
      OpFlags_WriteLookupOutputToRD := OpFlags_WriteLookupOutputToRD
      OpFlags_ConcatLookupQueryChunks := OpFlags_ConcatLookupQueryChunks
      OpFlags_Virtual := OpFlags_Virtual
      OpFlags_Assert := OpFlags_Assert
      OpFlags_DoNotUpdatePC := OpFlags_DoNotUpdatePC
      InstructionFlags_ADD_ADDInstruction_0_0 := InstructionFlags_ADD_ADDInstruction_0_0
      InstructionFlags_SUB_SUBInstruction_0_0 := InstructionFlags_SUB_SUBInstruction_0_0
      InstructionFlags_AND_ANDInstruction_0_0 := InstructionFlags_AND_ANDInstruction_0_0
      InstructionFlags_OR_ORInstruction_0_0 := InstructionFlags_OR_ORInstruction_0_0
      InstructionFlags_XOR_XORInstruction_0_0 := InstructionFlags_XOR_XORInstruction_0_0
      InstructionFlags_BEQ_BEQInstruction_0_0 := InstructionFlags_BEQ_BEQInstruction_0_0
      InstructionFlags_BGE_BGEInstruction_0_0 := InstructionFlags_BGE_BGEInstruction_0_0
      InstructionFlags_BGEU_BGEUInstruction_0_0 := InstructionFlags_BGEU_BGEUInstruction_0_0
      InstructionFlags_BNE_BNEInstruction_0_0 := InstructionFlags_BNE_BNEInstruction_0_0
      InstructionFlags_SLT_SLTInstruction_0_0 := InstructionFlags_SLT_SLTInstruction_0_0
      InstructionFlags_SLTU_SLTUInstruction_0_0 := InstructionFlags_SLTU_SLTUInstruction_0_0
      InstructionFlags_SLL_SLLInstruction_0_0 := InstructionFlags_SLL_SLLInstruction_0_0
      InstructionFlags_SRA_SRAInstruction_0_0 := InstructionFlags_SRA_SRAInstruction_0_0
      InstructionFlags_SRL_SRLInstruction_0_0 := InstructionFlags_SRL_SRLInstruction_0_0
      InstructionFlags_MOVSIGN_MOVSIGNInstruction_0 := InstructionFlags_MOVSIGN_MOVSIGNInstruction_0
      InstructionFlags_MUL_MULInstruction_0_0 := InstructionFlags_MUL_MULInstruction_0_0
      InstructionFlags_MULU_MULUInstruction_0_0 := InstructionFlags_MULU_MULUInstruction_0_0
      InstructionFlags_MULHU_MULHUInstruction_0_0 := InstructionFlags_MULHU_MULHUInstruction_0_0
      InstructionFlags_VIRTUAL_ADVICE_ADVICEInstruction_0 := InstructionFlags_VIRTUAL_ADVICE_ADVICEInstruction_0
      InstructionFlags_VIRTUAL_MOVE_MOVEInstruction_0 := InstructionFlags_VIRTUAL_MOVE_MOVEInstruction_0
      InstructionFlags_VIRTUAL_ASSERT_LTE_ASSERTLTEInstruction_0_0 := InstructionFlags_VIRTUAL_ASSERT_LTE_ASSERTLTEInstruction_0_0
      InstructionFlags_VIRTUAL_ASSERT_VALID_SIGNED_REMAINDER_AssertValidSignedRemainderInstruction_0_0 := InstructionFlags_VIRTUAL_ASSERT_VALID_SIGNED_REMAINDER_AssertValidSignedRemainderInstruction_0_0
      InstructionFlags_VIRTUAL_ASSERT_VALID_UNSIGNED_REMAINDER_AssertValidUnsignedRemainderInstruction_0_0 := InstructionFlags_VIRTUAL_ASSERT_VALID_UNSIGNED_REMAINDER_AssertValidUnsignedRemainderInstruction_0_0
      InstructionFlags_VIRTUAL_ASSERT_VALID_DIV0_AssertValidDiv0Instruction_0_0 := InstructionFlags_VIRTUAL_ASSERT_VALID_DIV0_AssertValidDiv0Instruction_0_0
      InstructionFlags_VIRTUAL_ASSERT_HALFWORD_ALIGNMENT_AssertHalfwordAlignmentInstruction_0_0 := InstructionFlags_VIRTUAL_ASSERT_HALFWORD_ALIGNMENT_AssertHalfwordAlignmentInstruction_0_0
      InstructionFlags_VIRTUAL_POW2_POW2Instruction_0 := InstructionFlags_VIRTUAL_POW2_POW2Instruction_0
      InstructionFlags_VIRTUAL_SRA_PADDING_RightShiftPaddingInstruction_0 := InstructionFlags_VIRTUAL_SRA_PADDING_RightShiftPaddingInstruction_0
      Aux_LeftLookupOperand := Aux_LeftLookupOperand
      Aux_RightLookupOperand := Aux_RightLookupOperand
      Aux_Product := Aux_Product
      Aux_RelevantYChunk_0 := Aux_RelevantYChunk_0
      Aux_RelevantYChunk_1 := Aux_RelevantYChunk_1
      Aux_RelevantYChunk_2 := Aux_RelevantYChunk_2
      Aux_RelevantYChunk_3 := Aux_RelevantYChunk_3
      Aux_WriteLookupOutputToRD := Aux_WriteLookupOutputToRD
      Aux_WritePCtoRD := Aux_WritePCtoRD
      Aux_NextPCJump := Aux_NextPCJump
      Aux_ShouldBranch := Aux_ShouldBranch
      Aux_NextPC := Aux_NextPC
    }

def uniform_jolt_constraints [ZKField f] (jolt_inputs : JoltR1CSInputs f) : ZKBuilder f PUnit := do
  constrainR1CS
    jolt_inputs.InstructionFlags_ADD_ADDInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_ADD_ADDInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_SUB_SUBInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_SUB_SUBInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_AND_ANDInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_AND_ANDInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_OR_ORInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_OR_ORInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_XOR_XORInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_XOR_XORInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_BEQ_BEQInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_BEQ_BEQInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_BGE_BGEInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_BGE_BGEInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_BGEU_BGEUInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_BGEU_BGEUInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_BNE_BNEInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_BNE_BNEInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_SLT_SLTInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_SLT_SLTInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_SLTU_SLTUInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_SLTU_SLTUInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_SLL_SLLInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_SLL_SLLInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_SRA_SRAInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_SRA_SRAInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_SRL_SRLInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_SRL_SRLInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_MOVSIGN_MOVSIGNInstruction_0
    (-1*jolt_inputs.InstructionFlags_MOVSIGN_MOVSIGNInstruction_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_MUL_MULInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_MUL_MULInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_MULU_MULUInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_MULU_MULUInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_MULHU_MULHUInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_MULHU_MULHUInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_VIRTUAL_ADVICE_ADVICEInstruction_0
    (-1*jolt_inputs.InstructionFlags_VIRTUAL_ADVICE_ADVICEInstruction_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_VIRTUAL_MOVE_MOVEInstruction_0
    (-1*jolt_inputs.InstructionFlags_VIRTUAL_MOVE_MOVEInstruction_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_LTE_ASSERTLTEInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_LTE_ASSERTLTEInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_VALID_SIGNED_REMAINDER_AssertValidSignedRemainderInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_VALID_SIGNED_REMAINDER_AssertValidSignedRemainderInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_VALID_UNSIGNED_REMAINDER_AssertValidUnsignedRemainderInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_VALID_UNSIGNED_REMAINDER_AssertValidUnsignedRemainderInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_VALID_DIV0_AssertValidDiv0Instruction_0_0
    (-1*jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_VALID_DIV0_AssertValidDiv0Instruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_HALFWORD_ALIGNMENT_AssertHalfwordAlignmentInstruction_0_0
    (-1*jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_HALFWORD_ALIGNMENT_AssertHalfwordAlignmentInstruction_0_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_VIRTUAL_POW2_POW2Instruction_0
    (-1*jolt_inputs.InstructionFlags_VIRTUAL_POW2_POW2Instruction_0 + 1)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_VIRTUAL_SRA_PADDING_RightShiftPaddingInstruction_0
    (-1*jolt_inputs.InstructionFlags_VIRTUAL_SRA_PADDING_RightShiftPaddingInstruction_0 + 1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_LeftOperandIsPC
    (-1*jolt_inputs.OpFlags_LeftOperandIsPC + 1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_RightOperandIsImm
    (-1*jolt_inputs.OpFlags_RightOperandIsImm + 1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Load
    (-1*jolt_inputs.OpFlags_Load + 1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Store
    (-1*jolt_inputs.OpFlags_Store + 1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Jump
    (-1*jolt_inputs.OpFlags_Jump + 1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Branch
    (-1*jolt_inputs.OpFlags_Branch + 1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Lui
    (-1*jolt_inputs.OpFlags_Lui + 1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_WriteLookupOutputToRD
    (-1*jolt_inputs.OpFlags_WriteLookupOutputToRD + 1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_ConcatLookupQueryChunks
    (-1*jolt_inputs.OpFlags_ConcatLookupQueryChunks + 1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Virtual
    (-1*jolt_inputs.OpFlags_Virtual + 1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Assert
    (-1*jolt_inputs.OpFlags_Assert + 1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_DoNotUpdatePC
    (-1*jolt_inputs.OpFlags_DoNotUpdatePC + 1)
    0
  constrainR1CS
    (-1*jolt_inputs.Bytecode_Bitflags + 274877906944*jolt_inputs.OpFlags_LeftOperandIsPC + 137438953472*jolt_inputs.OpFlags_RightOperandIsImm + 68719476736*jolt_inputs.OpFlags_Load + 34359738368*jolt_inputs.OpFlags_Store + 17179869184*jolt_inputs.OpFlags_Jump + 8589934592*jolt_inputs.OpFlags_Branch + 4294967296*jolt_inputs.OpFlags_Lui + 2147483648*jolt_inputs.OpFlags_WriteLookupOutputToRD + 1073741824*jolt_inputs.OpFlags_ConcatLookupQueryChunks + 536870912*jolt_inputs.OpFlags_Virtual + 268435456*jolt_inputs.OpFlags_Assert + 134217728*jolt_inputs.OpFlags_DoNotUpdatePC + 67108864*jolt_inputs.InstructionFlags_ADD_ADDInstruction_0_0 + 33554432*jolt_inputs.InstructionFlags_SUB_SUBInstruction_0_0 + 16777216*jolt_inputs.InstructionFlags_AND_ANDInstruction_0_0 + 8388608*jolt_inputs.InstructionFlags_OR_ORInstruction_0_0 + 4194304*jolt_inputs.InstructionFlags_XOR_XORInstruction_0_0 + 2097152*jolt_inputs.InstructionFlags_BEQ_BEQInstruction_0_0 + 1048576*jolt_inputs.InstructionFlags_BGE_BGEInstruction_0_0 + 524288*jolt_inputs.InstructionFlags_BGEU_BGEUInstruction_0_0 + 262144*jolt_inputs.InstructionFlags_BNE_BNEInstruction_0_0 + 131072*jolt_inputs.InstructionFlags_SLT_SLTInstruction_0_0 + 65536*jolt_inputs.InstructionFlags_SLTU_SLTUInstruction_0_0 + 32768*jolt_inputs.InstructionFlags_SLL_SLLInstruction_0_0 + 16384*jolt_inputs.InstructionFlags_SRA_SRAInstruction_0_0 + 8192*jolt_inputs.InstructionFlags_SRL_SRLInstruction_0_0 + 4096*jolt_inputs.InstructionFlags_MOVSIGN_MOVSIGNInstruction_0 + 2048*jolt_inputs.InstructionFlags_MUL_MULInstruction_0_0 + 1024*jolt_inputs.InstructionFlags_MULU_MULUInstruction_0_0 + 512*jolt_inputs.InstructionFlags_MULHU_MULHUInstruction_0_0 + 256*jolt_inputs.InstructionFlags_VIRTUAL_ADVICE_ADVICEInstruction_0 + 128*jolt_inputs.InstructionFlags_VIRTUAL_MOVE_MOVEInstruction_0 + 64*jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_LTE_ASSERTLTEInstruction_0_0 + 32*jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_VALID_SIGNED_REMAINDER_AssertValidSignedRemainderInstruction_0_0 + 16*jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_VALID_UNSIGNED_REMAINDER_AssertValidUnsignedRemainderInstruction_0_0 + 8*jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_VALID_DIV0_AssertValidDiv0Instruction_0_0 + 4*jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_HALFWORD_ALIGNMENT_AssertHalfwordAlignmentInstruction_0_0 + 2*jolt_inputs.InstructionFlags_VIRTUAL_POW2_POW2Instruction_0 + jolt_inputs.InstructionFlags_VIRTUAL_SRA_PADDING_RightShiftPaddingInstruction_0)
    1
    0
  constrainR1CS
    jolt_inputs.OpFlags_LeftOperandIsPC
    (4*jolt_inputs.Bytecode_ELFAddress + -1*jolt_inputs.RS1_Read + 2147483644)
    (-1*jolt_inputs.RS1_Read + jolt_inputs.Aux_LeftLookupOperand)
  constrainR1CS
    jolt_inputs.OpFlags_RightOperandIsImm
    (jolt_inputs.Bytecode_Imm + -1*jolt_inputs.RS2_Read)
    (-1*jolt_inputs.RS2_Read + jolt_inputs.Aux_RightLookupOperand)
  constrainR1CS
    (jolt_inputs.OpFlags_Load + jolt_inputs.OpFlags_Store)
    (jolt_inputs.Bytecode_Imm + -4*jolt_inputs.RAM_Address + jolt_inputs.RS1_Read + -2147467264)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Load
    (jolt_inputs.RAM_Read + -1*jolt_inputs.RAM_Write)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Load
    (jolt_inputs.RAM_Read + -1*jolt_inputs.RD_Write)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Store
    (jolt_inputs.RS2_Read + -1*jolt_inputs.RAM_Write)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Lui
    (-1*jolt_inputs.Bytecode_Imm + jolt_inputs.RD_Write)
    0
  constrainR1CS
    (jolt_inputs.InstructionFlags_ADD_ADDInstruction_0_0 + jolt_inputs.InstructionFlags_VIRTUAL_ASSERT_HALFWORD_ALIGNMENT_AssertHalfwordAlignmentInstruction_0_0)
    (281474976710656*jolt_inputs.ChunksQuery_0 + 4294967296*jolt_inputs.ChunksQuery_1 + 65536*jolt_inputs.ChunksQuery_2 + jolt_inputs.ChunksQuery_3 + -1*jolt_inputs.Aux_LeftLookupOperand + -1*jolt_inputs.Aux_RightLookupOperand)
    0
  constrainR1CS
    jolt_inputs.InstructionFlags_SUB_SUBInstruction_0_0
    (281474976710656*jolt_inputs.ChunksQuery_0 + 4294967296*jolt_inputs.ChunksQuery_1 + 65536*jolt_inputs.ChunksQuery_2 + jolt_inputs.ChunksQuery_3 + -1*jolt_inputs.Aux_LeftLookupOperand + jolt_inputs.Aux_RightLookupOperand + -4294967296)
    0
  constrainR1CS
    jolt_inputs.RS1_Read
    jolt_inputs.RS2_Read
    jolt_inputs.Aux_Product
  constrainR1CS
    (jolt_inputs.InstructionFlags_MUL_MULInstruction_0_0 + jolt_inputs.InstructionFlags_MULU_MULUInstruction_0_0 + jolt_inputs.InstructionFlags_MULHU_MULHUInstruction_0_0)
    (281474976710656*jolt_inputs.ChunksQuery_0 + 4294967296*jolt_inputs.ChunksQuery_1 + 65536*jolt_inputs.ChunksQuery_2 + jolt_inputs.ChunksQuery_3 + -1*jolt_inputs.Aux_Product)
    0
  constrainR1CS
    (jolt_inputs.InstructionFlags_MOVSIGN_MOVSIGNInstruction_0 + jolt_inputs.InstructionFlags_VIRTUAL_MOVE_MOVEInstruction_0)
    (281474976710656*jolt_inputs.ChunksQuery_0 + 4294967296*jolt_inputs.ChunksQuery_1 + 65536*jolt_inputs.ChunksQuery_2 + jolt_inputs.ChunksQuery_3 + -1*jolt_inputs.Aux_LeftLookupOperand)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Assert
    (jolt_inputs.LookupOutput + -1)
    0
  constrainR1CS
    jolt_inputs.OpFlags_ConcatLookupQueryChunks
    (16777216*jolt_inputs.ChunksX_0 + 65536*jolt_inputs.ChunksX_1 + 256*jolt_inputs.ChunksX_2 + jolt_inputs.ChunksX_3 + -1*jolt_inputs.Aux_LeftLookupOperand)
    0
  constrainR1CS
    jolt_inputs.OpFlags_ConcatLookupQueryChunks
    (16777216*jolt_inputs.ChunksY_0 + 65536*jolt_inputs.ChunksY_1 + 256*jolt_inputs.ChunksY_2 + jolt_inputs.ChunksY_3 + -1*jolt_inputs.Aux_RightLookupOperand)
    0
  constrainR1CS
    (jolt_inputs.InstructionFlags_SLL_SLLInstruction_0_0 + jolt_inputs.InstructionFlags_SRA_SRAInstruction_0_0 + jolt_inputs.InstructionFlags_SRL_SRLInstruction_0_0)
    (-1*jolt_inputs.ChunksY_0 + jolt_inputs.ChunksY_3)
    (-1*jolt_inputs.ChunksY_0 + jolt_inputs.Aux_RelevantYChunk_0)
  constrainR1CS
    jolt_inputs.OpFlags_ConcatLookupQueryChunks
    (jolt_inputs.ChunksQuery_0 + -256*jolt_inputs.ChunksX_0 + -1*jolt_inputs.Aux_RelevantYChunk_0)
    0
  constrainR1CS
    (jolt_inputs.InstructionFlags_SLL_SLLInstruction_0_0 + jolt_inputs.InstructionFlags_SRA_SRAInstruction_0_0 + jolt_inputs.InstructionFlags_SRL_SRLInstruction_0_0)
    (-1*jolt_inputs.ChunksY_1 + jolt_inputs.ChunksY_3)
    (-1*jolt_inputs.ChunksY_1 + jolt_inputs.Aux_RelevantYChunk_1)
  constrainR1CS
    jolt_inputs.OpFlags_ConcatLookupQueryChunks
    (jolt_inputs.ChunksQuery_1 + -256*jolt_inputs.ChunksX_1 + -1*jolt_inputs.Aux_RelevantYChunk_1)
    0
  constrainR1CS
    (jolt_inputs.InstructionFlags_SLL_SLLInstruction_0_0 + jolt_inputs.InstructionFlags_SRA_SRAInstruction_0_0 + jolt_inputs.InstructionFlags_SRL_SRLInstruction_0_0)
    (-1*jolt_inputs.ChunksY_2 + jolt_inputs.ChunksY_3)
    (-1*jolt_inputs.ChunksY_2 + jolt_inputs.Aux_RelevantYChunk_2)
  constrainR1CS
    jolt_inputs.OpFlags_ConcatLookupQueryChunks
    (jolt_inputs.ChunksQuery_2 + -256*jolt_inputs.ChunksX_2 + -1*jolt_inputs.Aux_RelevantYChunk_2)
    0
  constrainR1CS
    (jolt_inputs.InstructionFlags_SLL_SLLInstruction_0_0 + jolt_inputs.InstructionFlags_SRA_SRAInstruction_0_0 + jolt_inputs.InstructionFlags_SRL_SRLInstruction_0_0)
    0
    (-1*jolt_inputs.ChunksY_3 + jolt_inputs.Aux_RelevantYChunk_3)
  constrainR1CS
    jolt_inputs.OpFlags_ConcatLookupQueryChunks
    (jolt_inputs.ChunksQuery_3 + -256*jolt_inputs.ChunksX_3 + -1*jolt_inputs.Aux_RelevantYChunk_3)
    0
  constrainR1CS
    jolt_inputs.Bytecode_RD
    jolt_inputs.OpFlags_WriteLookupOutputToRD
    jolt_inputs.Aux_WriteLookupOutputToRD
  constrainR1CS
    jolt_inputs.Aux_WriteLookupOutputToRD
    (jolt_inputs.RD_Write + -1*jolt_inputs.LookupOutput)
    0
  constrainR1CS
    jolt_inputs.Bytecode_RD
    jolt_inputs.OpFlags_Jump
    jolt_inputs.Aux_WritePCtoRD
  constrainR1CS
    jolt_inputs.Aux_WritePCtoRD
    (4*jolt_inputs.Bytecode_ELFAddress + -1*jolt_inputs.RD_Write + 2147483648)
    0
  constrainR1CS
    jolt_inputs.OpFlags_Jump
    (-4*jolt_inputs.Bytecode_ELFAddress + jolt_inputs.LookupOutput + 4*jolt_inputs.OpFlags_DoNotUpdatePC + -2147483648)
    (-4*jolt_inputs.Bytecode_ELFAddress + 4*jolt_inputs.OpFlags_DoNotUpdatePC + jolt_inputs.Aux_NextPCJump + -2147483652)
  constrainR1CS
    jolt_inputs.OpFlags_Branch
    jolt_inputs.LookupOutput
    jolt_inputs.Aux_ShouldBranch
  constrainR1CS
    jolt_inputs.Aux_ShouldBranch
    (4*jolt_inputs.Bytecode_ELFAddress + jolt_inputs.Bytecode_Imm + -1*jolt_inputs.Aux_NextPCJump + 2147483648)
    (-1*jolt_inputs.Aux_NextPCJump + jolt_inputs.Aux_NextPC)

def non_uniform_jolt_constraints [ZKField f] (jolt_inputs : JoltR1CSInputs f) (jolt_offset_inputs : JoltR1CSInputs f) : ZKBuilder f PUnit := do
  constrainR1CS
    (jolt_inputs.Aux_NextPC - (4*jolt_offset_inputs.Bytecode_ELFAddress + 2147483648))
    jolt_offset_inputs.Bytecode_ELFAddress
    0
  constrainR1CS
    (jolt_offset_inputs.Bytecode_A - (jolt_inputs.Bytecode_A + 1))
    jolt_inputs.OpFlags_Virtual
    0


def AND_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*x[7]*x[15] + 2*x[6]*x[14] + 4*x[5]*x[13] + 8*x[4]*x[12] + 16*x[3]*x[11] + 32*x[2]*x[10] + 64*x[1]*x[9] + 128*x[0]*x[8])
def EQ_ABS_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 1*(x[1]*x[9] + (1 - x[1])*(1 - x[9]))*(x[2]*x[10] + (1 - x[2])*(1 - x[10]))*(x[3]*x[11] + (1 - x[3])*(1 - x[11]))*(x[4]*x[12] + (1 - x[4])*(1 - x[12]))*(x[5]*x[13] + (1 - x[5])*(1 - x[13]))*(x[6]*x[14] + (1 - x[6])*(1 - x[14]))*(x[7]*x[15] + (1 - x[7])*(1 - x[15])))
def EQ_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 1*(x[0]*x[8] + (1 - x[0])*(1 - x[8]))*(x[1]*x[9] + (1 - x[1])*(1 - x[9]))*(x[2]*x[10] + (1 - x[2])*(1 - x[10]))*(x[3]*x[11] + (1 - x[3])*(1 - x[11]))*(x[4]*x[12] + (1 - x[4])*(1 - x[12]))*(x[5]*x[13] + (1 - x[5])*(1 - x[13]))*(x[6]*x[14] + (1 - x[6])*(1 - x[14]))*(x[7]*x[15] + (1 - x[7])*(1 - x[15])))
def LEFT_MSB_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => x[0])
def RIGHT_MSB_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => x[8])
def IDENTITY_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*x[15] + 2*x[14] + 4*x[13] + 8*x[12] + 16*x[11] + 32*x[10] + 64*x[9] + 128*x[8] + 256*x[7] + 512*x[6] + 1024*x[5] + 2048*x[4] + 4096*x[3] + 8192*x[2] + 16384*x[1] + 32768*x[0])
def LT_ABS_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + (1 - x[1])*x[9]*1 + (1 - x[2])*x[10]*1*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9]) + (1 - x[3])*x[11]*1*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10]) + (1 - x[4])*x[12]*1*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10])*(1 - x[3] - x[11] + x[3]*x[11] + x[3]*x[11]) + (1 - x[5])*x[13]*1*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10])*(1 - x[3] - x[11] + x[3]*x[11] + x[3]*x[11])*(1 - x[4] - x[12] + x[4]*x[12] + x[4]*x[12]) + (1 - x[6])*x[14]*1*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10])*(1 - x[3] - x[11] + x[3]*x[11] + x[3]*x[11])*(1 - x[4] - x[12] + x[4]*x[12] + x[4]*x[12])*(1 - x[5] - x[13] + x[5]*x[13] + x[5]*x[13]) + (1 - x[7])*x[15]*1*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10])*(1 - x[3] - x[11] + x[3]*x[11] + x[3]*x[11])*(1 - x[4] - x[12] + x[4]*x[12] + x[4]*x[12])*(1 - x[5] - x[13] + x[5]*x[13] + x[5]*x[13])*(1 - x[6] - x[14] + x[6]*x[14] + x[6]*x[14]))
def LTU_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + (1 - x[0])*x[8]*1 + (1 - x[1])*x[9]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8]) + (1 - x[2])*x[10]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8])*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9]) + (1 - x[3])*x[11]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8])*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10]) + (1 - x[4])*x[12]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8])*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10])*(1 - x[3] - x[11] + x[3]*x[11] + x[3]*x[11]) + (1 - x[5])*x[13]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8])*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10])*(1 - x[3] - x[11] + x[3]*x[11] + x[3]*x[11])*(1 - x[4] - x[12] + x[4]*x[12] + x[4]*x[12]) + (1 - x[6])*x[14]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8])*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10])*(1 - x[3] - x[11] + x[3]*x[11] + x[3]*x[11])*(1 - x[4] - x[12] + x[4]*x[12] + x[4]*x[12])*(1 - x[5] - x[13] + x[5]*x[13] + x[5]*x[13]) + (1 - x[7])*x[15]*1*(1 - x[0] - x[8] + x[0]*x[8] + x[0]*x[8])*(1 - x[1] - x[9] + x[1]*x[9] + x[1]*x[9])*(1 - x[2] - x[10] + x[2]*x[10] + x[2]*x[10])*(1 - x[3] - x[11] + x[3]*x[11] + x[3]*x[11])*(1 - x[4] - x[12] + x[4]*x[12] + x[4]*x[12])*(1 - x[5] - x[13] + x[5]*x[13] + x[5]*x[13])*(1 - x[6] - x[14] + x[6]*x[14] + x[6]*x[14]))
def OR_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*(x[7] + x[15] - x[7]*x[15]) + 2*(x[6] + x[14] - x[6]*x[14]) + 4*(x[5] + x[13] - x[5]*x[13]) + 8*(x[4] + x[12] - x[4]*x[12]) + 16*(x[3] + x[11] - x[3]*x[11]) + 32*(x[2] + x[10] - x[2]*x[10]) + 64*(x[1] + x[9] - x[1]*x[9]) + 128*(x[0] + x[8] - x[0]*x[8]))
def SIGN_EXTEND_16_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => x[0]*65535)
def SLL0_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[7] + 2*x[6] + 4*x[5] + 8*x[4] + 16*x[3] + 32*x[2] + 64*x[1] + 128*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2*x[7] + 4*x[6] + 8*x[5] + 16*x[4] + 32*x[3] + 64*x[2] + 128*x[1] + 256*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 4*x[7] + 8*x[6] + 16*x[5] + 32*x[4] + 64*x[3] + 128*x[2] + 256*x[1] + 512*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 8*x[7] + 16*x[6] + 32*x[5] + 64*x[4] + 128*x[3] + 256*x[2] + 512*x[1] + 1024*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 16*x[7] + 32*x[6] + 64*x[5] + 128*x[4] + 256*x[3] + 512*x[2] + 1024*x[1] + 2048*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 32*x[7] + 64*x[6] + 128*x[5] + 256*x[4] + 512*x[3] + 1024*x[2] + 2048*x[1] + 4096*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 64*x[7] + 128*x[6] + 256*x[5] + 512*x[4] + 1024*x[3] + 2048*x[2] + 4096*x[1] + 8192*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 128*x[7] + 256*x[6] + 512*x[5] + 1024*x[4] + 2048*x[3] + 4096*x[2] + 8192*x[1] + 16384*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 256*x[7] + 512*x[6] + 1024*x[5] + 2048*x[4] + 4096*x[3] + 8192*x[2] + 16384*x[1] + 32768*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 512*x[7] + 1024*x[6] + 2048*x[5] + 4096*x[4] + 8192*x[3] + 16384*x[2] + 32768*x[1] + 65536*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1024*x[7] + 2048*x[6] + 4096*x[5] + 8192*x[4] + 16384*x[3] + 32768*x[2] + 65536*x[1] + 131072*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2048*x[7] + 4096*x[6] + 8192*x[5] + 16384*x[4] + 32768*x[3] + 65536*x[2] + 131072*x[1] + 262144*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 4096*x[7] + 8192*x[6] + 16384*x[5] + 32768*x[4] + 65536*x[3] + 131072*x[2] + 262144*x[1] + 524288*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 8192*x[7] + 16384*x[6] + 32768*x[5] + 65536*x[4] + 131072*x[3] + 262144*x[2] + 524288*x[1] + 1048576*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 16384*x[7] + 32768*x[6] + 65536*x[5] + 131072*x[4] + 262144*x[3] + 524288*x[2] + 1048576*x[1] + 2097152*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 32768*x[7] + 65536*x[6] + 131072*x[5] + 262144*x[4] + 524288*x[3] + 1048576*x[2] + 2097152*x[1] + 4194304*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 65536*x[7] + 131072*x[6] + 262144*x[5] + 524288*x[4] + 1048576*x[3] + 2097152*x[2] + 4194304*x[1] + 8388608*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 131072*x[7] + 262144*x[6] + 524288*x[5] + 1048576*x[4] + 2097152*x[3] + 4194304*x[2] + 8388608*x[1] + 16777216*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 262144*x[7] + 524288*x[6] + 1048576*x[5] + 2097152*x[4] + 4194304*x[3] + 8388608*x[2] + 16777216*x[1] + 33554432*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 524288*x[7] + 1048576*x[6] + 2097152*x[5] + 4194304*x[4] + 8388608*x[3] + 16777216*x[2] + 33554432*x[1] + 67108864*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1048576*x[7] + 2097152*x[6] + 4194304*x[5] + 8388608*x[4] + 16777216*x[3] + 33554432*x[2] + 67108864*x[1] + 134217728*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2097152*x[7] + 4194304*x[6] + 8388608*x[5] + 16777216*x[4] + 33554432*x[3] + 67108864*x[2] + 134217728*x[1] + 268435456*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 4194304*x[7] + 8388608*x[6] + 16777216*x[5] + 33554432*x[4] + 67108864*x[3] + 134217728*x[2] + 268435456*x[1] + 536870912*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 8388608*x[7] + 16777216*x[6] + 33554432*x[5] + 67108864*x[4] + 134217728*x[3] + 268435456*x[2] + 536870912*x[1] + 1073741824*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 16777216*x[7] + 33554432*x[6] + 67108864*x[5] + 134217728*x[4] + 268435456*x[3] + 536870912*x[2] + 1073741824*x[1] + 2147483648*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 33554432*x[7] + 67108864*x[6] + 134217728*x[5] + 268435456*x[4] + 536870912*x[3] + 1073741824*x[2] + 2147483648*x[1]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 67108864*x[7] + 134217728*x[6] + 268435456*x[5] + 536870912*x[4] + 1073741824*x[3] + 2147483648*x[2]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 134217728*x[7] + 268435456*x[6] + 536870912*x[5] + 1073741824*x[4] + 2147483648*x[3]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 268435456*x[7] + 536870912*x[6] + 1073741824*x[5] + 2147483648*x[4]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 536870912*x[7] + 1073741824*x[6] + 2147483648*x[5]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1073741824*x[7] + 2147483648*x[6]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[7]))
def SLL1_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[7] + 2*x[6] + 4*x[5] + 8*x[4] + 16*x[3] + 32*x[2] + 64*x[1] + 128*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2*x[7] + 4*x[6] + 8*x[5] + 16*x[4] + 32*x[3] + 64*x[2] + 128*x[1] + 256*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 4*x[7] + 8*x[6] + 16*x[5] + 32*x[4] + 64*x[3] + 128*x[2] + 256*x[1] + 512*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 8*x[7] + 16*x[6] + 32*x[5] + 64*x[4] + 128*x[3] + 256*x[2] + 512*x[1] + 1024*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 16*x[7] + 32*x[6] + 64*x[5] + 128*x[4] + 256*x[3] + 512*x[2] + 1024*x[1] + 2048*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 32*x[7] + 64*x[6] + 128*x[5] + 256*x[4] + 512*x[3] + 1024*x[2] + 2048*x[1] + 4096*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 64*x[7] + 128*x[6] + 256*x[5] + 512*x[4] + 1024*x[3] + 2048*x[2] + 4096*x[1] + 8192*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 128*x[7] + 256*x[6] + 512*x[5] + 1024*x[4] + 2048*x[3] + 4096*x[2] + 8192*x[1] + 16384*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 256*x[7] + 512*x[6] + 1024*x[5] + 2048*x[4] + 4096*x[3] + 8192*x[2] + 16384*x[1] + 32768*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 512*x[7] + 1024*x[6] + 2048*x[5] + 4096*x[4] + 8192*x[3] + 16384*x[2] + 32768*x[1] + 65536*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1024*x[7] + 2048*x[6] + 4096*x[5] + 8192*x[4] + 16384*x[3] + 32768*x[2] + 65536*x[1] + 131072*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2048*x[7] + 4096*x[6] + 8192*x[5] + 16384*x[4] + 32768*x[3] + 65536*x[2] + 131072*x[1] + 262144*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 4096*x[7] + 8192*x[6] + 16384*x[5] + 32768*x[4] + 65536*x[3] + 131072*x[2] + 262144*x[1] + 524288*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 8192*x[7] + 16384*x[6] + 32768*x[5] + 65536*x[4] + 131072*x[3] + 262144*x[2] + 524288*x[1] + 1048576*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 16384*x[7] + 32768*x[6] + 65536*x[5] + 131072*x[4] + 262144*x[3] + 524288*x[2] + 1048576*x[1] + 2097152*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 32768*x[7] + 65536*x[6] + 131072*x[5] + 262144*x[4] + 524288*x[3] + 1048576*x[2] + 2097152*x[1] + 4194304*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 65536*x[7] + 131072*x[6] + 262144*x[5] + 524288*x[4] + 1048576*x[3] + 2097152*x[2] + 4194304*x[1] + 8388608*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 131072*x[7] + 262144*x[6] + 524288*x[5] + 1048576*x[4] + 2097152*x[3] + 4194304*x[2] + 8388608*x[1]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 262144*x[7] + 524288*x[6] + 1048576*x[5] + 2097152*x[4] + 4194304*x[3] + 8388608*x[2]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 524288*x[7] + 1048576*x[6] + 2097152*x[5] + 4194304*x[4] + 8388608*x[3]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1048576*x[7] + 2097152*x[6] + 4194304*x[5] + 8388608*x[4]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2097152*x[7] + 4194304*x[6] + 8388608*x[5]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 4194304*x[7] + 8388608*x[6]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 8388608*x[7]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0)
def SLL2_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[7] + 2*x[6] + 4*x[5] + 8*x[4] + 16*x[3] + 32*x[2] + 64*x[1] + 128*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2*x[7] + 4*x[6] + 8*x[5] + 16*x[4] + 32*x[3] + 64*x[2] + 128*x[1] + 256*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 4*x[7] + 8*x[6] + 16*x[5] + 32*x[4] + 64*x[3] + 128*x[2] + 256*x[1] + 512*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 8*x[7] + 16*x[6] + 32*x[5] + 64*x[4] + 128*x[3] + 256*x[2] + 512*x[1] + 1024*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 16*x[7] + 32*x[6] + 64*x[5] + 128*x[4] + 256*x[3] + 512*x[2] + 1024*x[1] + 2048*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 32*x[7] + 64*x[6] + 128*x[5] + 256*x[4] + 512*x[3] + 1024*x[2] + 2048*x[1] + 4096*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 64*x[7] + 128*x[6] + 256*x[5] + 512*x[4] + 1024*x[3] + 2048*x[2] + 4096*x[1] + 8192*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 128*x[7] + 256*x[6] + 512*x[5] + 1024*x[4] + 2048*x[3] + 4096*x[2] + 8192*x[1] + 16384*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 256*x[7] + 512*x[6] + 1024*x[5] + 2048*x[4] + 4096*x[3] + 8192*x[2] + 16384*x[1] + 32768*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 512*x[7] + 1024*x[6] + 2048*x[5] + 4096*x[4] + 8192*x[3] + 16384*x[2] + 32768*x[1]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1024*x[7] + 2048*x[6] + 4096*x[5] + 8192*x[4] + 16384*x[3] + 32768*x[2]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2048*x[7] + 4096*x[6] + 8192*x[5] + 16384*x[4] + 32768*x[3]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 4096*x[7] + 8192*x[6] + 16384*x[5] + 32768*x[4]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 8192*x[7] + 16384*x[6] + 32768*x[5]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 16384*x[7] + 32768*x[6]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 32768*x[7]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0)
def SLL3_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[7] + 2*x[6] + 4*x[5] + 8*x[4] + 16*x[3] + 32*x[2] + 64*x[1] + 128*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2*x[7] + 4*x[6] + 8*x[5] + 16*x[4] + 32*x[3] + 64*x[2] + 128*x[1]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 4*x[7] + 8*x[6] + 16*x[5] + 32*x[4] + 64*x[3] + 128*x[2]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 8*x[7] + 16*x[6] + 32*x[5] + 64*x[4] + 128*x[3]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 16*x[7] + 32*x[6] + 64*x[5] + 128*x[4]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 32*x[7] + 64*x[6] + 128*x[5]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 64*x[7] + 128*x[6]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 128*x[7]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0)
def SRA_SIGN_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0] + 64*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0] + 64*x[0] + 32*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0] + 64*x[0] + 32*x[0] + 16*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0] + 64*x[0] + 32*x[0] + 16*x[0] + 8*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0] + 64*x[0] + 32*x[0] + 16*x[0] + 8*x[0] + 4*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2147483648*x[0] + 1073741824*x[0] + 536870912*x[0] + 268435456*x[0] + 134217728*x[0] + 67108864*x[0] + 33554432*x[0] + 16777216*x[0] + 8388608*x[0] + 4194304*x[0] + 2097152*x[0] + 1048576*x[0] + 524288*x[0] + 262144*x[0] + 131072*x[0] + 65536*x[0] + 32768*x[0] + 16384*x[0] + 8192*x[0] + 4096*x[0] + 2048*x[0] + 1024*x[0] + 512*x[0] + 256*x[0] + 128*x[0] + 64*x[0] + 32*x[0] + 16*x[0] + 8*x[0] + 4*x[0] + 2*x[0]))
def SRL0_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[7] + 2*x[6] + 4*x[5] + 8*x[4] + 16*x[3] + 32*x[2] + 64*x[1] + 128*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[6] + 2*x[5] + 4*x[4] + 8*x[3] + 16*x[2] + 32*x[1] + 64*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[5] + 2*x[4] + 4*x[3] + 8*x[2] + 16*x[1] + 32*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[4] + 2*x[3] + 4*x[2] + 8*x[1] + 16*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[3] + 2*x[2] + 4*x[1] + 8*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[2] + 2*x[1] + 4*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[1] + 2*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0)
def SRL1_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 256*x[7] + 512*x[6] + 1024*x[5] + 2048*x[4] + 4096*x[3] + 8192*x[2] + 16384*x[1] + 32768*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 128*x[7] + 256*x[6] + 512*x[5] + 1024*x[4] + 2048*x[3] + 4096*x[2] + 8192*x[1] + 16384*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 64*x[7] + 128*x[6] + 256*x[5] + 512*x[4] + 1024*x[3] + 2048*x[2] + 4096*x[1] + 8192*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 32*x[7] + 64*x[6] + 128*x[5] + 256*x[4] + 512*x[3] + 1024*x[2] + 2048*x[1] + 4096*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 16*x[7] + 32*x[6] + 64*x[5] + 128*x[4] + 256*x[3] + 512*x[2] + 1024*x[1] + 2048*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 8*x[7] + 16*x[6] + 32*x[5] + 64*x[4] + 128*x[3] + 256*x[2] + 512*x[1] + 1024*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 4*x[7] + 8*x[6] + 16*x[5] + 32*x[4] + 64*x[3] + 128*x[2] + 256*x[1] + 512*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2*x[7] + 4*x[6] + 8*x[5] + 16*x[4] + 32*x[3] + 64*x[2] + 128*x[1] + 256*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[7] + 2*x[6] + 4*x[5] + 8*x[4] + 16*x[3] + 32*x[2] + 64*x[1] + 128*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[6] + 2*x[5] + 4*x[4] + 8*x[3] + 16*x[2] + 32*x[1] + 64*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[5] + 2*x[4] + 4*x[3] + 8*x[2] + 16*x[1] + 32*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[4] + 2*x[3] + 4*x[2] + 8*x[1] + 16*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[3] + 2*x[2] + 4*x[1] + 8*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[2] + 2*x[1] + 4*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[1] + 2*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0)
def SRL2_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 65536*x[7] + 131072*x[6] + 262144*x[5] + 524288*x[4] + 1048576*x[3] + 2097152*x[2] + 4194304*x[1] + 8388608*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 32768*x[7] + 65536*x[6] + 131072*x[5] + 262144*x[4] + 524288*x[3] + 1048576*x[2] + 2097152*x[1] + 4194304*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 16384*x[7] + 32768*x[6] + 65536*x[5] + 131072*x[4] + 262144*x[3] + 524288*x[2] + 1048576*x[1] + 2097152*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 8192*x[7] + 16384*x[6] + 32768*x[5] + 65536*x[4] + 131072*x[3] + 262144*x[2] + 524288*x[1] + 1048576*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 4096*x[7] + 8192*x[6] + 16384*x[5] + 32768*x[4] + 65536*x[3] + 131072*x[2] + 262144*x[1] + 524288*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2048*x[7] + 4096*x[6] + 8192*x[5] + 16384*x[4] + 32768*x[3] + 65536*x[2] + 131072*x[1] + 262144*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1024*x[7] + 2048*x[6] + 4096*x[5] + 8192*x[4] + 16384*x[3] + 32768*x[2] + 65536*x[1] + 131072*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 512*x[7] + 1024*x[6] + 2048*x[5] + 4096*x[4] + 8192*x[3] + 16384*x[2] + 32768*x[1] + 65536*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 256*x[7] + 512*x[6] + 1024*x[5] + 2048*x[4] + 4096*x[3] + 8192*x[2] + 16384*x[1] + 32768*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 128*x[7] + 256*x[6] + 512*x[5] + 1024*x[4] + 2048*x[3] + 4096*x[2] + 8192*x[1] + 16384*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 64*x[7] + 128*x[6] + 256*x[5] + 512*x[4] + 1024*x[3] + 2048*x[2] + 4096*x[1] + 8192*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 32*x[7] + 64*x[6] + 128*x[5] + 256*x[4] + 512*x[3] + 1024*x[2] + 2048*x[1] + 4096*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 16*x[7] + 32*x[6] + 64*x[5] + 128*x[4] + 256*x[3] + 512*x[2] + 1024*x[1] + 2048*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 8*x[7] + 16*x[6] + 32*x[5] + 64*x[4] + 128*x[3] + 256*x[2] + 512*x[1] + 1024*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 4*x[7] + 8*x[6] + 16*x[5] + 32*x[4] + 64*x[3] + 128*x[2] + 256*x[1] + 512*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2*x[7] + 4*x[6] + 8*x[5] + 16*x[4] + 32*x[3] + 64*x[2] + 128*x[1] + 256*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[7] + 2*x[6] + 4*x[5] + 8*x[4] + 16*x[3] + 32*x[2] + 64*x[1] + 128*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[6] + 2*x[5] + 4*x[4] + 8*x[3] + 16*x[2] + 32*x[1] + 64*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[5] + 2*x[4] + 4*x[3] + 8*x[2] + 16*x[1] + 32*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[4] + 2*x[3] + 4*x[2] + 8*x[1] + 16*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[3] + 2*x[2] + 4*x[1] + 8*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[2] + 2*x[1] + 4*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[1] + 2*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0 + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*0)
def SRL3_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 16777216*x[7] + 33554432*x[6] + 67108864*x[5] + 134217728*x[4] + 268435456*x[3] + 536870912*x[2] + 1073741824*x[1] + 2147483648*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 8388608*x[7] + 16777216*x[6] + 33554432*x[5] + 67108864*x[4] + 134217728*x[3] + 268435456*x[2] + 536870912*x[1] + 1073741824*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 4194304*x[7] + 8388608*x[6] + 16777216*x[5] + 33554432*x[4] + 67108864*x[3] + 134217728*x[2] + 268435456*x[1] + 536870912*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2097152*x[7] + 4194304*x[6] + 8388608*x[5] + 16777216*x[4] + 33554432*x[3] + 67108864*x[2] + 134217728*x[1] + 268435456*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1048576*x[7] + 2097152*x[6] + 4194304*x[5] + 8388608*x[4] + 16777216*x[3] + 33554432*x[2] + 67108864*x[1] + 134217728*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 524288*x[7] + 1048576*x[6] + 2097152*x[5] + 4194304*x[4] + 8388608*x[3] + 16777216*x[2] + 33554432*x[1] + 67108864*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 262144*x[7] + 524288*x[6] + 1048576*x[5] + 2097152*x[4] + 4194304*x[3] + 8388608*x[2] + 16777216*x[1] + 33554432*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 131072*x[7] + 262144*x[6] + 524288*x[5] + 1048576*x[4] + 2097152*x[3] + 4194304*x[2] + 8388608*x[1] + 16777216*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 65536*x[7] + 131072*x[6] + 262144*x[5] + 524288*x[4] + 1048576*x[3] + 2097152*x[2] + 4194304*x[1] + 8388608*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 32768*x[7] + 65536*x[6] + 131072*x[5] + 262144*x[4] + 524288*x[3] + 1048576*x[2] + 2097152*x[1] + 4194304*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 16384*x[7] + 32768*x[6] + 65536*x[5] + 131072*x[4] + 262144*x[3] + 524288*x[2] + 1048576*x[1] + 2097152*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 8192*x[7] + 16384*x[6] + 32768*x[5] + 65536*x[4] + 131072*x[3] + 262144*x[2] + 524288*x[1] + 1048576*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 4096*x[7] + 8192*x[6] + 16384*x[5] + 32768*x[4] + 65536*x[3] + 131072*x[2] + 262144*x[1] + 524288*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 2048*x[7] + 4096*x[6] + 8192*x[5] + 16384*x[4] + 32768*x[3] + 65536*x[2] + 131072*x[1] + 262144*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 1024*x[7] + 2048*x[6] + 4096*x[5] + 8192*x[4] + 16384*x[3] + 32768*x[2] + 65536*x[1] + 131072*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(0*x[11] + (1 - 0)*(1 - x[11]))*(0 + 512*x[7] + 1024*x[6] + 2048*x[5] + 4096*x[4] + 8192*x[3] + 16384*x[2] + 32768*x[1] + 65536*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 256*x[7] + 512*x[6] + 1024*x[5] + 2048*x[4] + 4096*x[3] + 8192*x[2] + 16384*x[1] + 32768*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 128*x[7] + 256*x[6] + 512*x[5] + 1024*x[4] + 2048*x[3] + 4096*x[2] + 8192*x[1] + 16384*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 64*x[7] + 128*x[6] + 256*x[5] + 512*x[4] + 1024*x[3] + 2048*x[2] + 4096*x[1] + 8192*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 32*x[7] + 64*x[6] + 128*x[5] + 256*x[4] + 512*x[3] + 1024*x[2] + 2048*x[1] + 4096*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 16*x[7] + 32*x[6] + 64*x[5] + 128*x[4] + 256*x[3] + 512*x[2] + 1024*x[1] + 2048*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 8*x[7] + 16*x[6] + 32*x[5] + 64*x[4] + 128*x[3] + 256*x[2] + 512*x[1] + 1024*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 4*x[7] + 8*x[6] + 16*x[5] + 32*x[4] + 64*x[3] + 128*x[2] + 256*x[1] + 512*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(0*x[12] + (1 - 0)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 2*x[7] + 4*x[6] + 8*x[5] + 16*x[4] + 32*x[3] + 64*x[2] + 128*x[1] + 256*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[7] + 2*x[6] + 4*x[5] + 8*x[4] + 16*x[3] + 32*x[2] + 64*x[1] + 128*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[6] + 2*x[5] + 4*x[4] + 8*x[3] + 16*x[2] + 32*x[1] + 64*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[5] + 2*x[4] + 4*x[3] + 8*x[2] + 16*x[1] + 32*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(0*x[13] + (1 - 0)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[4] + 2*x[3] + 4*x[2] + 8*x[1] + 16*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[3] + 2*x[2] + 4*x[1] + 8*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(0*x[14] + (1 - 0)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[2] + 2*x[1] + 4*x[0]) + 1*(0*x[15] + (1 - 0)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[1] + 2*x[0]) + 1*(1*x[15] + (1 - 1)*(1 - x[15]))*(1*x[14] + (1 - 1)*(1 - x[14]))*(1*x[13] + (1 - 1)*(1 - x[13]))*(1*x[12] + (1 - 1)*(1 - x[12]))*(1*x[11] + (1 - 1)*(1 - x[11]))*(0 + 1*x[0]))
def XOR_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 0 + 1*((1 - x[7])*x[15] + x[7]*(1 - x[15])) + 2*((1 - x[6])*x[14] + x[6]*(1 - x[14])) + 4*((1 - x[5])*x[13] + x[5]*(1 - x[13])) + 8*((1 - x[4])*x[12] + x[4]*(1 - x[12])) + 16*((1 - x[3])*x[11] + x[3]*(1 - x[11])) + 32*((1 - x[2])*x[10] + x[2]*(1 - x[10])) + 64*((1 - x[1])*x[9] + x[1]*(1 - x[9])) + 128*((1 - x[0])*x[8] + x[0]*(1 - x[8])))
def LEFT_IS_ZERO_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 1*(1 - x[0])*(1 - x[1])*(1 - x[2])*(1 - x[3])*(1 - x[4])*(1 - x[5])*(1 - x[6])*(1 - x[7]))
def RIGHT_IS_ZERO_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 1*(1 - x[8])*(1 - x[9])*(1 - x[10])*(1 - x[11])*(1 - x[12])*(1 - x[13])*(1 - x[14])*(1 - x[15]))
def DIV_BY_ZERO_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => 1*(1 - x[0])*x[8]*(1 - x[1])*x[9]*(1 - x[2])*x[10]*(1 - x[3])*x[11]*(1 - x[4])*x[12]*(1 - x[5])*x[13]*(1 - x[6])*x[14]*(1 - x[7])*x[15])
def LSB_16 [Field f] : Subtable f 16 :=
  subtableFromMLE (fun x => x[15])


def ADD_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (IDENTITY_16, 2), (IDENTITY_16, 3) ].toVector (fun x => 0 + 1*x[1] + 1*65536*x[0])
def SUB_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (IDENTITY_16, 2), (IDENTITY_16, 3) ].toVector (fun x => 0 + 1*x[1] + 1*65536*x[0])
def AND_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (AND_16, 0), (AND_16, 1), (AND_16, 2), (AND_16, 3) ].toVector (fun x => 0 + 1*x[3] + 1*256*x[2] + 1*256*256*x[1] + 1*256*256*256*x[0])
def OR_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (OR_16, 0), (OR_16, 1), (OR_16, 2), (OR_16, 3) ].toVector (fun x => 0 + 1*x[3] + 1*256*x[2] + 1*256*256*x[1] + 1*256*256*256*x[0])
def XOR_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (XOR_16, 0), (XOR_16, 1), (XOR_16, 2), (XOR_16, 3) ].toVector (fun x => 0 + 1*x[3] + 1*256*x[2] + 1*256*256*x[1] + 1*256*256*256*x[0])
def BEQ_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (EQ_16, 0), (EQ_16, 1), (EQ_16, 2), (EQ_16, 3) ].toVector (fun x => x[0]*x[1]*x[2]*x[3])
def BGE_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (LEFT_MSB_16, 0), (RIGHT_MSB_16, 0), (LTU_16, 1), (LTU_16, 2), (LTU_16, 3), (EQ_16, 1), (EQ_16, 2), (LT_ABS_16, 0), (EQ_ABS_16, 0) ].toVector (fun x => 1 - x[0]*(1 - x[1]) + (x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[7] + x[2]*x[8] + x[3]*x[8]*x[5] + x[4]*x[8]*x[5]*x[6]))
def BGEU_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (LTU_16, 0), (LTU_16, 1), (LTU_16, 2), (LTU_16, 3), (EQ_16, 0), (EQ_16, 1), (EQ_16, 2) ].toVector (fun x => 1 - 0 + x[0]*1 + x[1]*1*x[4] + x[2]*1*x[4]*x[5] + x[3]*1*x[4]*x[5]*x[6])
def BNE_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (EQ_16, 0), (EQ_16, 1), (EQ_16, 2), (EQ_16, 3) ].toVector (fun x => 1 - x[0]*x[1]*x[2]*x[3])
def SLT_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (LEFT_MSB_16, 0), (RIGHT_MSB_16, 0), (LTU_16, 1), (LTU_16, 2), (LTU_16, 3), (EQ_16, 1), (EQ_16, 2), (LT_ABS_16, 0), (EQ_ABS_16, 0) ].toVector (fun x => x[0]*(1 - x[1]) + (x[0]*x[1] + (1 - x[0])*(1 - x[1]))*(x[7] + x[2]*x[8] + x[3]*x[8]*x[5] + x[4]*x[8]*x[5]*x[6]))
def SLTU_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (LTU_16, 0), (LTU_16, 1), (LTU_16, 2), (LTU_16, 3), (EQ_16, 0), (EQ_16, 1), (EQ_16, 2) ].toVector (fun x => 0 + x[0]*1 + x[1]*1*x[4] + x[2]*1*x[4]*x[5] + x[3]*1*x[4]*x[5]*x[6])
def SLL_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (SLL3_16, 0), (SLL2_16, 1), (SLL1_16, 2), (SLL0_16, 3) ].toVector (fun x => 0 + 1*x[3] + 1*256*x[2] + 1*256*256*x[1] + 1*256*256*256*x[0])
def SRA_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (SRL3_16, 0), (SRL2_16, 1), (SRL1_16, 2), (SRL0_16, 3), (SRA_SIGN_16, 0) ].toVector (fun x => x[0] + x[1] + x[2] + x[3] + x[4])
def SRL_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (SRL3_16, 0), (SRL2_16, 1), (SRL1_16, 2), (SRL0_16, 3) ].toVector (fun x => x[0] + x[1] + x[2] + x[3])
def MOVSIGN_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (SIGN_EXTEND_16_16, 2), (IDENTITY_16, 0), (IDENTITY_16, 1), (IDENTITY_16, 2), (IDENTITY_16, 3) ].toVector (fun x => 0 + 1*x[0] + 1*65536*x[0])
def MUL_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (IDENTITY_16, 2), (IDENTITY_16, 3) ].toVector (fun x => 0 + 1*x[1] + 1*65536*x[0])
def MULU_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (IDENTITY_16, 2), (IDENTITY_16, 3) ].toVector (fun x => 0 + 1*x[1] + 1*65536*x[0])
def MULHU_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (IDENTITY_16, 0), (IDENTITY_16, 1) ].toVector (fun x => 0 + 1*x[1] + 1*65536*x[0])
def VIRTUAL_ADVICE_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (IDENTITY_16, 2), (IDENTITY_16, 3) ].toVector (fun x => 0 + 1*x[1] + 1*65536*x[0])
def VIRTUAL_MOVE_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (IDENTITY_16, 0), (IDENTITY_16, 1), (IDENTITY_16, 2), (IDENTITY_16, 3) ].toVector (fun x => 0 + 1*x[3] + 1*65536*x[2] + 1*65536*65536*x[1] + 1*65536*65536*65536*x[0])
def VIRTUAL_ASSERT_LTE_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (LTU_16, 0), (LTU_16, 1), (LTU_16, 2), (LTU_16, 3), (EQ_16, 0), (EQ_16, 1), (EQ_16, 2), (EQ_16, 3) ].toVector (fun x => 0 + x[0]*1 + x[1]*1*x[4] + x[2]*1*x[4]*x[5] + x[3]*1*x[4]*x[5]*x[6] + 1*x[4]*x[5]*x[6]*x[7])
def VIRTUAL_ASSERT_VALID_SIGNED_REMAINDER_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (LEFT_MSB_16, 0), (RIGHT_MSB_16, 0), (EQ_16, 1), (EQ_16, 2), (EQ_16, 3), (LTU_16, 1), (LTU_16, 2), (LTU_16, 3), (EQ_ABS_16, 0), (LT_ABS_16, 0), (LEFT_IS_ZERO_16, 0), (LEFT_IS_ZERO_16, 1), (LEFT_IS_ZERO_16, 2), (LEFT_IS_ZERO_16, 3), (RIGHT_IS_ZERO_16, 0), (RIGHT_IS_ZERO_16, 1), (RIGHT_IS_ZERO_16, 2), (RIGHT_IS_ZERO_16, 3) ].toVector (fun x => (1 - x[0] - x[1])*(x[9] + x[5]*x[8] + x[6]*x[8]*x[2] + x[7]*x[8]*x[2]*x[3]) + x[0]*x[1]*(1 - x[8]*x[2]*x[3]*x[4]) + (1 - x[0])*x[1]*x[10]*x[11]*x[12]*x[13] + x[14]*x[15]*x[16]*x[17])
def VIRTUAL_ASSERT_VALID_UNSIGNED_REMAINDER_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (LTU_16, 0), (LTU_16, 1), (LTU_16, 2), (LTU_16, 3), (EQ_16, 0), (EQ_16, 1), (EQ_16, 2), (RIGHT_IS_ZERO_16, 0), (RIGHT_IS_ZERO_16, 1), (RIGHT_IS_ZERO_16, 2), (RIGHT_IS_ZERO_16, 3) ].toVector (fun x => 0 + x[0]*1 + x[1]*1*x[4] + x[2]*1*x[4]*x[5] + x[3]*1*x[4]*x[5]*x[6] + x[7]*x[8]*x[9]*x[10])
def VIRTUAL_ASSERT_VALID_DIV0_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (LEFT_IS_ZERO_16, 0), (LEFT_IS_ZERO_16, 1), (LEFT_IS_ZERO_16, 2), (LEFT_IS_ZERO_16, 3), (DIV_BY_ZERO_16, 0), (DIV_BY_ZERO_16, 1), (DIV_BY_ZERO_16, 2), (DIV_BY_ZERO_16, 3) ].toVector (fun x => 1 - x[0]*x[1]*x[2]*x[3] + x[4]*x[5]*x[6]*x[7])
def VIRTUAL_ASSERT_HALFWORD_ALIGNMENT_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[ (LSB_16, 3) ].toVector (fun x => 1 - x[0])
def VIRTUAL_POW2_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[  ].toVector (fun x => 0)
def VIRTUAL_SRA_PADDING_32_4_16 [Field f] : ComposedLookupTable f 16 4
  := mkComposedLookupTable #[  ].toVector (fun x => 0)


def lookup_step [ZKField f] (inputs: JoltR1CSInputs f): ZKBuilder f PUnit := do
  let res <- mux_lookup
    (#v[inputs.ChunksQuery_0, inputs.ChunksQuery_1, inputs.ChunksQuery_2, inputs.ChunksQuery_3])
    (#[
      (inputs.InstructionFlags_ADD_ADDInstruction_0_0, ADD_32_4_16),
      (inputs.InstructionFlags_SUB_SUBInstruction_0_0, SUB_32_4_16),
      (inputs.InstructionFlags_AND_ANDInstruction_0_0, AND_32_4_16),
      (inputs.InstructionFlags_OR_ORInstruction_0_0, OR_32_4_16),
      (inputs.InstructionFlags_XOR_XORInstruction_0_0, XOR_32_4_16),
      (inputs.InstructionFlags_BEQ_BEQInstruction_0_0, BEQ_32_4_16),
      (inputs.InstructionFlags_BGE_BGEInstruction_0_0, BGE_32_4_16),
      (inputs.InstructionFlags_BGEU_BGEUInstruction_0_0, BGEU_32_4_16),
      (inputs.InstructionFlags_BNE_BNEInstruction_0_0, BNE_32_4_16),
      (inputs.InstructionFlags_SLT_SLTInstruction_0_0, SLT_32_4_16),
      (inputs.InstructionFlags_SLTU_SLTUInstruction_0_0, SLTU_32_4_16),
      (inputs.InstructionFlags_SLL_SLLInstruction_0_0, SLL_32_4_16),
      (inputs.InstructionFlags_SRA_SRAInstruction_0_0, SRA_32_4_16),
      (inputs.InstructionFlags_SRL_SRLInstruction_0_0, SRL_32_4_16),
      (inputs.InstructionFlags_MOVSIGN_MOVSIGNInstruction_0, MOVSIGN_32_4_16),
      (inputs.InstructionFlags_MUL_MULInstruction_0_0, MUL_32_4_16),
      (inputs.InstructionFlags_MULU_MULUInstruction_0_0, MULU_32_4_16),
      (inputs.InstructionFlags_MULHU_MULHUInstruction_0_0, MULHU_32_4_16),
      (inputs.InstructionFlags_VIRTUAL_ADVICE_ADVICEInstruction_0, VIRTUAL_ADVICE_32_4_16),
      (inputs.InstructionFlags_VIRTUAL_MOVE_MOVEInstruction_0, VIRTUAL_MOVE_32_4_16),
      (inputs.InstructionFlags_VIRTUAL_ASSERT_LTE_ASSERTLTEInstruction_0_0, VIRTUAL_ASSERT_LTE_32_4_16),
      (inputs.InstructionFlags_VIRTUAL_ASSERT_VALID_SIGNED_REMAINDER_AssertValidSignedRemainderInstruction_0_0, VIRTUAL_ASSERT_VALID_SIGNED_REMAINDER_32_4_16),
      (inputs.InstructionFlags_VIRTUAL_ASSERT_VALID_UNSIGNED_REMAINDER_AssertValidUnsignedRemainderInstruction_0_0, VIRTUAL_ASSERT_VALID_UNSIGNED_REMAINDER_32_4_16),
      (inputs.InstructionFlags_VIRTUAL_ASSERT_VALID_DIV0_AssertValidDiv0Instruction_0_0, VIRTUAL_ASSERT_VALID_DIV0_32_4_16),
      (inputs.InstructionFlags_VIRTUAL_ASSERT_HALFWORD_ALIGNMENT_AssertHalfwordAlignmentInstruction_0_0, VIRTUAL_ASSERT_HALFWORD_ALIGNMENT_32_4_16),
      (inputs.InstructionFlags_VIRTUAL_POW2_POW2Instruction_0, VIRTUAL_POW2_32_4_16),
      (inputs.InstructionFlags_VIRTUAL_SRA_PADDING_RightShiftPaddingInstruction_0, VIRTUAL_SRA_PADDING_32_4_16)
    ])
  constrainEq res inputs.LookupOutput
