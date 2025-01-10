import Mathlib.Algebra.Field.Defs
import ZkLean

def main : IO Unit :=
  IO.println s!"Hello!"






def example1 [Field f] : ZKBuilder (ZKVar f) := do
  let x: ZKVar f <- witness
  let one: ZKVar f := 1
  constrain (x * (x - one) === 0)
  return x




def eq32 [Field f] : LookupTable f := {}



structure RISCVState (f: Type) where
  pc: ZKVar f
  registers: Vector (ZKVar f) 32

def example2 [Field f] (prev_st : RISCVState f) : ZKBuilder (RISCVState f) := do
  let new_st <- witness

  let r1 := prev_st.registers[1]
  let r2 := prev_st.registers[2]

  let isEq <- lookup eq32 r1 r2
  constrain (new_st.registers[0] === isEq)

  pure new_st

-- structure RISCVState (backend : Type) where
--   pc: ZKRepr backend Unit
--   -- registers: List (zkrepr UInt32)

-- #check RISCVState.mk 32

-- structure [ZKRepr zkrepr] RISCVState (zkrepr : Type) where
--   pc: repr zkrepr UInt32
--   -- registers: List (zkrepr UInt32)

-- def example2 {zkrepr:Type} [ZKRepr1 zkrepr Unit Unit] : ZKBuilder (RISCVState (ZKRepr1 zkrepr Unit)) := do
-- def example2 {zkrepr:Type} : ZKBuilder (RISCVState zkrepr) := do
--   let new_st <- witness
-- 
--   pure new_st
  

-- #eval example1
