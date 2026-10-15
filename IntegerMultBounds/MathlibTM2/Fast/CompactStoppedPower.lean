module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedPiece

/-! Charged unary powers used by runtime cutoff record construction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}
variable (body : P → Pr P (nT SXReg) Q A U) {R : Fin (nT SXReg) → List (Fin (A+4))}

def compactStoppedLeafPow : Pr P (nT SXReg) Q A U :=
  scanP (sreg (.s 12)) (sreg (.s 23)) (synMulIn m (sreg (.s 18)) (sreg (.s 2)) (sreg (.s 3)))

theorem sg_compactStoppedLeafPow (v : SynW → List (Fin (A + 4))) (n y : ℕ) (h22 : (v (.s 12)).length = n)
    (h23 : v (.s 23) = []) (h7 : v (.s 18) = List.replicate y tick) (h2 : v (.s 2) = [])
    (h3 : v (.s 3) = []) :
    LayRuns body compactStoppedLeafPow (synG R v)
      (synG R (Function.update v (.s 18) (List.replicate (m ^ n * y) tick)))
      (∑ j ∈ Finset.range n, (8 * (m ^ j * y) + 8 + 3) + 2 * n + 4) := by
  set cs := v (.s 12) with hcs
  let Φ : ℕ → SynW → List (Fin (A + 4)) := fun j =>
    Function.update v (.s 18) (List.replicate (m ^ j * y) tick)
  have hstep : ∀ j < cs.length, LayRuns body (synMulIn m (sreg (.s 18)) (sreg (.s 2)) (sreg (.s 3)))
      (synG R (Function.update (Function.update (Φ j) (.s 12) (cs.drop (j + 1))) (.s 23)
        (cs.take (j + 1)).reverse))
      (synG R (Function.update (Function.update (Φ (j + 1)) (.s 12) (cs.drop (j + 1))) (.s 23)
        (cs.take (j + 1)).reverse)) (8 * (m ^ j * y) + 8) := by
    intro j _
    refine lr_weaken body (sgU_mulIn body m (a := .s 18) (t := .s 2) (t₁ := .s 3)
      (x := m ^ j * y) (by decide) (by simp [Φ, h2]) (by simp [Φ, h3]) (by simp [Φ])) ?_ le_rfl
    refine congrArg (synG R) ?_
    funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all [pow_succ]; ring
  have h := sg_scan body (R := R) (a := .s 12) (t := .s 23) (by decide) Φ cs
    (fun j => 8 * (m ^ j * y) + 8) hstep
  rw [h22] at h
  refine lr_weaken body (lr_congr_left body h ?_) ?_ le_rfl
  · refine congrArg (synG R) ?_
    funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all
  · refine congrArg (synG R) ?_
    funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all

def compactStoppedDepthPow : Pr P (nT SXReg) Q A U :=
  scanP (sreg (.s 14)) (sreg (.s 23)) (synMulIn m (sreg (.s 13)) (sreg (.s 2)) (sreg (.s 3)))

theorem sg_compactStoppedDepthPow (v : SynW → List (Fin (A + 4))) (n y : ℕ) (h22 : (v (.s 14)).length = n)
    (h23 : v (.s 23) = []) (h7 : v (.s 13) = List.replicate y tick) (h2 : v (.s 2) = [])
    (h3 : v (.s 3) = []) :
    LayRuns body compactStoppedDepthPow (synG R v)
      (synG R (Function.update v (.s 13) (List.replicate (m ^ n * y) tick)))
      (∑ j ∈ Finset.range n, (8 * (m ^ j * y) + 8 + 3) + 2 * n + 4) := by
  set cs := v (.s 14) with hcs
  let Φ : ℕ → SynW → List (Fin (A + 4)) := fun j =>
    Function.update v (.s 13) (List.replicate (m ^ j * y) tick)
  have hstep : ∀ j < cs.length, LayRuns body (synMulIn m (sreg (.s 13)) (sreg (.s 2)) (sreg (.s 3)))
      (synG R (Function.update (Function.update (Φ j) (.s 14) (cs.drop (j + 1))) (.s 23)
        (cs.take (j + 1)).reverse))
      (synG R (Function.update (Function.update (Φ (j + 1)) (.s 14) (cs.drop (j + 1))) (.s 23)
        (cs.take (j + 1)).reverse)) (8 * (m ^ j * y) + 8) := by
    intro j _
    refine lr_weaken body (sgU_mulIn body m (a := .s 13) (t := .s 2) (t₁ := .s 3)
      (x := m ^ j * y) (by decide) (by simp [Φ, h2]) (by simp [Φ, h3]) (by simp [Φ])) ?_ le_rfl
    refine congrArg (synG R) ?_
    funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all [pow_succ]; ring
  have h := sg_scan body (R := R) (a := .s 14) (t := .s 23) (by decide) Φ cs
    (fun j => 8 * (m ^ j * y) + 8) hstep
  rw [h22] at h
  refine lr_weaken body (lr_congr_left body h ?_) ?_ le_rfl
  · refine congrArg (synG R) ?_
    funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all
  · refine congrArg (synG R) ?_
    funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all

end
end IntegerMultBounds.MathlibTM2.Fast
