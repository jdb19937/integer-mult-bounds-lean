module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedPipeline

/-!
# Selected stopping cutoff from the caller's global dimension

The pinned assembler selects beta = 1 / 10^24. Global dimension remains on
p.D after synChunkQ; s26 instead contains the remaining chunk dimension.
Compute floor(log_m(globalD) / 10^24) - 1, reserving one radix digit of slack.
The leaf budget theorem requires the explicit large-dimension threshold;
for smaller dimensions the executable cutoff saturates at zero.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
variable {Q A : ℕ} {U P : Type}
variable (body : P → Pr P (nT SXReg) Q A U) {R : Fin (nT SXReg) → List (Fin (A+4))}

def selectedStopDen : ℕ := 10^24

def compactGlobalCutoff (D : ℕ) : ℕ := Nat.log m D / selectedStopDen - 1

noncomputable def compactStoppedGlobalCutoff : Pr P (nT SXReg) Q A U :=
  .seq (compactStoppedCutoff (.p .D)) <|
  .seq (udiv selectedStopDen (sreg (.s 22)) (sreg (.s 29)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.s 22))) <|
  .seq (moveR (sreg (.s 29)) (sreg (.s 22)) id) (synPop (sreg (.s 22)))

def compactStoppedGlobalCutoffCost (D : ℕ) : ℕ :=
  compactStoppedCutoffCost D + (4*Nat.log m D+4) + (2*Nat.log m D+2) +
    (2*(Nat.log m D / selectedStopDen)+2) + 1

theorem sg_compactStoppedGlobalCutoff (v : SynW → List (Fin (A+4)))
    (D : ℕ) (hDpos : 0 < D) (hD : (v (.p .D)).length=D)
    (h2 : v (.s 2)=[]) (h17 : v (.s 17)=[]) (h22 : v (.s 22)=[])
    (h23 : v (.s 23)=[]) (h29 : v (.s 29)=[]) :
    LayRuns body compactStoppedGlobalCutoff (synG R v)
      (synG R (Function.update v (.s 22) (List.replicate (compactGlobalCutoff D) tick)))
      (compactStoppedGlobalCutoffCost D) := by
  refine lr_weaken body
    ((sg_compactStoppedCutoff body (.p .D) v D hDpos hD
      (by decide) (by decide) (by decide) (by decide) (by decide) h2 h17 h22 h23 h29).seq <|
    (sgU_div body (k:=selectedStopDen) (a:=.s 22) (b:=.s 29) (t:=.s 2)
      (x:=Nat.log m D) (y:=0) (by norm_num [selectedStopDen])
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [h29])).seq <|
    (sgU_clear body (a:=.s 22) (x:=Nat.log m D) (by simp)).seq <|
    (sgU_move body (a:=.s 29) (b:=.s 22) (x:=Nat.log m D / selectedStopDen)
      (by decide) (by simp) (by simp)).seq <|
    sgU_pop body (a:=.s 22) (y:=Nat.log m D / selectedStopDen) (by simp)) ?_ ?_
  · apply congrArg (synG R)
    funext z
    by_cases hz22 : z = .s 22
    · subst z; simp [compactGlobalCutoff]
    by_cases hz29 : z = .s 29
    · subst z; simp [h29]
    simp [hz22, hz29]
  · simp only [compactStoppedGlobalCutoffCost]
    omega

/-- Below the selected asymptotic threshold, the computed cutoff is zero. -/
theorem compactGlobalCutoff_small (D : ℕ) (h : Nat.log m D < selectedStopDen) :
    compactGlobalCutoff D = 0 := by
  unfold compactGlobalCutoff
  rw [Nat.div_eq_of_lt h]

/-- The extra radix digit absorbs every possible nonzero base-m digit. This is
an integer-power formulation of the selected beta leaf budget. -/
theorem compactGlobalCutoff_leaf_bound (D d j : ℕ) (hD : 0 < D)
    (hlarge : selectedStopDen ≤ Nat.log m D) (hd : d < m) :
    (d * m^(min j (compactGlobalCutoff D)))^selectedStopDen ≤ D := by
  have hq : 0 < Nat.log m D / selectedStopDen :=
    Nat.div_pos hlarge (by norm_num [selectedStopDen])
  have hc : (compactGlobalCutoff D + 1)*selectedStopDen ≤ Nat.log m D := by
    rw [compactGlobalCutoff, Nat.sub_add_cancel hq]
    exact Nat.div_mul_le_self _ _
  have hm : 1 ≤ m := by norm_num [m]
  have hdigit : d * m^(min j (compactGlobalCutoff D)) ≤ m^(compactGlobalCutoff D+1) := by
    calc
      _ ≤ m * m^(compactGlobalCutoff D) := Nat.mul_le_mul (Nat.le_of_lt hd)
        (Nat.pow_le_pow_right hm (min_le_right _ _))
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  calc
    _ ≤ (m^(compactGlobalCutoff D+1))^selectedStopDen := Nat.pow_le_pow_left hdigit _
    _ = m^((compactGlobalCutoff D+1)*selectedStopDen) := (pow_mul _ _ _).symm
    _ ≤ m^(Nat.log m D) := Nat.pow_le_pow_right hm hc
    _ ≤ D := Nat.pow_log_le_self m (Nat.ne_of_gt hD)

end IntegerMultBounds.MathlibTM2.Fast
