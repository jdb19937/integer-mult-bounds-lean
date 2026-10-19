module

public import IntegerMultBounds.Machine.RecursiveChildSetupRoleBank
public import IntegerMultBounds.Machine.RecursiveCrossPrepare
public import IntegerMultBounds.Machine.RecursiveChildReturnRoleBank

/-! Recursive call entry after the parent row split. Supplied headers already
describe one role array: save those headers and the return PC, then construct
the cross-group child with divisor one. No second row division occurs. -/

@[expose] public section

namespace IntegerMultBounds.Machine.RecursiveRoleChildCallSetup
noncomputable section
open RecursiveInterchangeLayout (Descriptor child volume)
open RecursiveChildCallSetup (bank fields words descriptorStack pcStack savedStacks)
open Networks
open Shared50ModularControl (prime)
variable {q k t u : ℕ}

def program (hq : 2 ≤ q) {m : ℕ} (i j : Fin m) (code : FiniteReturnStack.Code k) :=
  seq (RecursiveFrameControl.callProgram (a := q) descriptorStack fields pcStack code)
    (extend (RecursiveCrossPrepare.program hq i j) 2)

def constant (m k : ℕ) := RecursiveCrossPrepare.constant m+k+74

/-- Physical role-header/PC saving and same-row child construction. The
runtime volume is that of the role, not the unsplit network's parent array. -/
theorem prepares (hq : 2 ≤ q) (b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hw : v.width = m*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (st : Tapes 2 q) (code : FiniteReturnStack.Code k) :
    ∃ ch : Fin 6 → List Bool, RecursiveDimensionBank.Headers (child q 1 b v i j) ch ∧
      HoareTime (program hq i j code) (fun w => w = bank hs st)
        (fun w => w = bank ch (savedStacks hs st code)) (constant m k*volume q v) := by
  obtain ⟨ch,hch,hcross⟩ := RecursiveCrossPrepare.prepares hq b v i j hw hp hs hv
  have hsave := RecursiveChildCallSetup.save_hoare hs st code
  have hprepare := hoare_extend_eq hcross (savedStacks hs st code)
  have hjoin := hsave.seq hprepare
  have hV := RecursiveAffinePrepare.volume_positive hq v hp
  have hlen (z : Fin 6) : (hs z).length ≤ 2*volume q v := by
    have hl := RecursiveAffinePrepare.header_log hq v hp hs hv z
    have hl' := Nat.log2_le_self (volume q v)
    omega
  have hcost := BinaryDescriptorFrames.six_field_cost fields (by simp [fields]) (words hs)
    (2*volume q v) (by
      intro op hop
      obtain ⟨z,rfl⟩ := List.mem_ofFn.mp hop
      rw [RecursiveChildCallSetup.words_header]
      exact hlen z)
  refine ⟨ch,hch,hjoin.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  unfold constant
  nlinarith

/-- The permanent bank is exactly the one used by physical header return.
All role arrays, shared scratch, and auxiliary tapes are literal spectators. -/
def placedProgram {m : ℕ} (i j : Fin m) (code : FiniteReturnStack.Code k) :=
  Placement.placed (program Shared50ModularControl.prime_prime.two_le i j code)
    (CleanSubbank.placement RecursiveChildSetupRoleBank.ports
      (RecursiveChildSetupRoleBank.commonPorts (t := t) (u := u)) RecursiveChildSetupRoleBank.commonPorts_injective)

theorem placed_prepares (b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m)
    (hw : v.width = m*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (roles : Tapes t prime) (aux : Tapes u prime)
    (st : Tapes 2 prime) (code : FiniteReturnStack.Code k) :
    ∃ ch : Fin 6 → List Bool, RecursiveDimensionBank.Headers (child prime 1 b v i j) ch ∧
      HoareTime (placedProgram (t := t) (u := u) i j code)
        (fun w => w = CleanSubbank.bank (RecursiveShiftRoleBank.common roles hs (aux.append st)))
        (fun w => w = CleanSubbank.bank
          (RecursiveShiftRoleBank.common roles ch (aux.append (savedStacks hs st code))))
        (constant m k*volume prime v) := by
  obtain ⟨ch,hch,h⟩ := prepares Shared50ModularControl.prime_prime.two_le b v i j hw hp hs hv st code
  exact ⟨ch,hch,RecursiveChildSetupRoleBank.placed_hoare _ roles hs ch aux st _ h⟩


end
end IntegerMultBounds.Machine.RecursiveRoleChildCallSetup
