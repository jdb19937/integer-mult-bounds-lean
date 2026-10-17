module

public import IntegerMultBounds.MathlibTM2.Fast.CompactTopConfigDivisor
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopConfigPadding
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopRows
import IntegerMultBounds.MathlibTM2.Fast.SynRecB
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Exact padded rows computed from original axis count, outside row count and
high spectator axes. The only output is s7; inputs and other scratch are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

def compactTopConfigRowsWires : Fin 9 → SynW :=
  ![.s 8,.s 7,.s 11,.s 12,.s 13,.s 14,.s 2,.s 3,.s 4]

def compactTopConfigRowsAfter : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.s 29)) (sreg (.s 8)) (sreg (.s 2))) <|
  .seq (upow2 (sreg (.s 30)) (sreg (.s 8)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (compactTopConfigPadding compactTopConfigRowsWires) <|
  .seq (uclear (sreg (.s 7))) <|
  .seq (uclear (sreg (.s 8))) (moveR (sreg (.s 11)) (sreg (.s 7)) id)

def compactTopConfigRowsAfterCost (a Rv c : ℕ) : ℕ :=
  (4*Rv+4)+((4*(2^a*Rv)+9*a+4)+
    (compactTopConfigPaddingCost (2^a*Rv) c+
      ((2*c+2)+((2*(2^a*Rv)+2)+(2*Compact.Layout.paddedRows (2^a*Rv) c+2)))))

theorem sg_compactTopConfigRowsAfter (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (a Rv c : ℕ) (hc : 1≤c) (ha : (v (.s 30)).length=a)
    (hRows : (v (.s 29)).length=Rv) (hdiv : (v (.s 7)).length=c)
    (hz : ∀ i : Fin 32, i∈[2,3,4,8,11,12,13,14] → v (.s i)=[]) :
    LayRuns body compactTopConfigRowsAfter (synG R v)
      (synG R (Function.update v (.s 7)
        (List.replicate (Compact.Layout.paddedRows (2^a*Rv) c) tick)))
      (compactTopConfigRowsAfterCost a Rv c) := by
  have h2 := hz 2 (by simp); have h3 := hz 3 (by simp); have h4 := hz 4 (by simp)
  have h8 := hz 8 (by simp); have h11 := hz 11 (by simp); have h12 := hz 12 (by simp)
  have h13 := hz 13 (by simp); have h14 := hz 14 (by simp)
  have he : Function.Injective compactTopConfigRowsWires := by decide
  refine lr_weaken body
    ((sgU_copy body (R := R) (v := v) (a := .s 29) (b := .s 8) (t := .s 2)
      (x := Rv) (y := 0) (by decide) (by decide) (by decide) h2 hRows (by simp [h8])).seq <|
    (sgU_pow2 body (a := .s 30) (b := .s 8) (t₁ := .s 2) (t₂ := .s 3)
      (x := a) (y := Rv) (by decide) (by simp [h2]) (by simp [h3])
      (by simp [ha]) (by simp)).seq <|
    (sg_compactTopConfigPadding body compactTopConfigRowsWires he R _ (2^a*Rv) c hc
      (by simp [compactTopConfigRowsWires]) (by simp [compactTopConfigRowsWires,hdiv])
      (by intro i hi; fin_cases i <;> simp_all [compactTopConfigRowsWires])).seq <|
    (sgU_clear body (a := .s 7) (x := c) (by simp [compactTopConfigRowsWires,hdiv])).seq <|
    (sgU_clear body (a := .s 8) (x := 2^a*Rv) (by simp [compactTopConfigRowsWires])).seq <|
    sgU_move body (a := .s 11) (b := .s 7) (x := Compact.Layout.paddedRows (2^a*Rv) c)
      (by decide) (by simp [compactTopConfigRowsWires]) (by simp)) ?_ (Nat.le_refl _)
  apply congrArg (synG R)
  funext z
  simp only [compactTopConfigRowsWires,
    Function.update_apply]
  split_ifs <;> simp_all

def compactTopConfigRows : Pr P (nT SXReg) Q A U :=
  .seq compactTopConfigDivisor compactTopConfigRowsAfter

def compactTopConfigRowsCost (d a Rv : ℕ) : ℕ :=
  compactTopConfigDivisorCost d+
    compactTopConfigRowsAfterCost a Rv (NW^CompactGlobalRowPadding.depth m d)

theorem sg_compactTopConfigRows (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (d a Rv : ℕ) (hd : 0<d) (hdv : (v (.s 0)).length=d)
    (ha : (v (.s 30)).length=a) (hRows : (v (.s 29)).length=Rv)
    (hz : ∀ i : Fin 32, i∈[2,3,4,7,8,9,10,11,12,13,14,17,22,23] → v (.s i)=[]) :
    LayRuns body compactTopConfigRows (synG R v)
      (synG R (Function.update v (.s 7) (List.replicate (compactTopRows d Rv a) tick)))
      (compactTopConfigRowsCost d a Rv) := by
  have hsub : ∀ i : Fin 32, i∈[2,3,7,9,10,17,22,23] →
      i∈[2,3,4,7,8,9,10,11,12,13,14,17,22,23] := by decide
  have hsub' : ∀ i : Fin 32, i∈[2,3,4,8,11,12,13,14] →
      i∈[2,3,4,7,8,9,10,11,12,13,14,17,22,23] := by decide
  have hne : ∀ i : Fin 32, i∈[2,3,4,8,11,12,13,14] → i≠7 := by decide
  have hh := sg_compactTopConfigDivisor body R v d hd hdv
    (fun i hi => hz i (hsub i hi))
  have hn : 1≤NW^CompactGlobalRowPadding.depth m d := Nat.one_le_pow _ _ NW_pos
  have ht := sg_compactTopConfigRowsAfter body R
    (Function.update v (.s 7) (List.replicate (NW^CompactGlobalRowPadding.depth m d) tick))
    a Rv _ hn (by simp [ha]) (by simp [hRows]) (by simp)
    (by intro i hi; have hh := hz i (hsub' i hi); have hi7 := hne i hi; simp [hi7,hh])
  refine lr_weaken body (hh.seq ht) ?_ (Nat.le_refl _)
  simp only [Function.update_idem,compactTopRows,Nat.mul_comm]

end
end IntegerMultBounds.MathlibTM2.Fast
