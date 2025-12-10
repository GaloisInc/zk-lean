import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Nat.Prime.Defs

-- Eq polynomial (from 2.4 of Justin's notes).
def eq [Field f] (x y : Vector f size) : f :=
  let v := Vector.zipWith (λ xi yi => (1 - xi) * (1 - yi) + xi * yi) x y
  Vector.foldr (λ a b => a * b) (1 : f) v

instance : Fact (Nat.Prime 127) := by decide


def one : ZMod 127 := 1
#eval eq #v[one] #v[one]

def enumerate_eq := do
  let bit0 ← [0, one]
  let bit1 ← [0, one]
  let bit2 ← [0, one]
  let bit3 ← [0, one]
  pure (bit0, bit1, bit2, bit3, eq #v[bit0, bit1] #v[bit2, bit3])

#eval enumerate_eq


-- Lagrange poly
def χ [Field f] [BEq f] (H: f) (h x : f) : f :=
  let helper i := if i == h then 1 else (i - x) / (i - h)
  let rec go i :=
    if i == 0 then
      helper i
    else
      helper i * go (i - 1)
  termination_by i
  decreasing_by
    sorry
    
  go (H - 1)

def enumerate := do
  let input0 ← [0, one, 2, 3]
  let input1 ← [0, one, 2, 3]
  pure (input0, input1, χ 4 input0 input1)

#eval! enumerate




-- Example 1

def W₁_claim [Field f] [BEq f] (w : f) : f :=
  if w == 0 then
    sorry
  else if w == 1 then
    sorry
  else if w == 2 then
    sorry
  else if w == 3 then
    sorry
  else
    sorry

def sum [Field f] [BEq f] (H: f) (g : f → f) : f :=
  let rec go i :=
    if i == 0 then
      g i
    else
      g i * go (i - 1)
  termination_by i
  decreasing_by
    sorry

  go (H - 1)
  

-- Layer 2’s MLE
def W₂ [Field f] [BEq f] (z : f) : f :=
  let mul₂ (z w1 w2 : f) : f := χ 4 0 z * χ 4 0 w1 * χ 4 1 w2

  sum 4 (λ w1 => sum 4 (λ w2 => (mul₂ z w1 w2) * W₁_claim w1 * W₁_claim w2))


