import ZKLeanExamples.Keccak.Circuit.Chi
import ZKLeanExamples.Keccak.Circuit.Iota
import ZKLeanExamples.Keccak.Circuit.Not
import ZKLeanExamples.Keccak.Circuit.RhoPi
import ZKLeanExamples.Keccak.Circuit.Shift
import ZKLeanExamples.Keccak.Circuit.State
import ZKLeanExamples.Keccak.Circuit.Theta
import ZKLeanExamples.Keccak.Circuit.Xor

def keccakRound (s : State) (round : Fin 24) : ZKBuilder f State := do
  theta s >>= rho_pi >>= chi >>= (iota · round)

/-- Full Keccak-f[1600] permutation (24 rounds) --/
def keccakF (s : State) : ZKBuilder f State :=
  (Array.finRange 24).foldlM (fun acc i => keccakRound acc i) s

