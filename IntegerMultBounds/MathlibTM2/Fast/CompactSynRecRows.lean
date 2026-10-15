module

public import IntegerMultBounds.MathlibTM2.Fast.SynRec
public import IntegerMultBounds.Machine.CompactGlobalRowPadding

/-! # Runtime computation of the original row reservation

The fixed division scanner computes ceil log base m of twice the global axis
count, then multiplies by ceil log base two of the fixed number of roles.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

lemma compactRowLog (d : ℕ) (hd : 0<d) :
    synJ (2*d-1) (2*d-1) = Nat.clog m (2*d) := by
  rw [synJ_self_eq (by omega)]
  apply eq_of_forall_lt_iff
  intro t
  rw [Nat.lt_clog_iff_pow_lt one_lt_m]
  have hh := Nat.le_log_iff_pow_le (b := m) (x := t) (y := 2*d-1) one_lt_m (by omega)
  omega

/-- Original d on s0; exact row reservation on s8; every other register restored. -/
def compactRowReserve : Pr P (nT SXReg) Q A U :=
  .seq (umul 2 (sreg (.s 0)) (sreg (.s 9)) (sreg (.s 2))) <|
  .seq (synPop (sreg (.s 9))) <|
  .seq (ucopy (sreg (.s 9)) (sreg (.s 10)) (sreg (.s 2))) <|
  .seq (synCntLoop m (.s 10) (.s 11) (.s 9)) <|
  .seq (umul (Nat.clog 2 NW) (sreg (.s 11)) (sreg (.s 8)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.s 9))) <|
  .seq (uclear (sreg (.s 10))) (uclear (sreg (.s 11)))

def compactRowReserveCost (d : ℕ) : ℕ :=
  (4*d+4)+1+(4*(2*d-1)+4)+synCntCost m (2*d-1) (2*d-1)+
    (4*synJ (2*d-1) (2*d-1)+4)+(2*(2*d-1)+2)+2+(2*synJ (2*d-1) (2*d-1)+2)

theorem sg_compactRowReserve (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (d : ℕ) (hd : 0<d) (h0 : (v (.s 0)).length=d)
    (hz : ∀ i : Fin 32, i∈[2,8,9,10,11,17,23] → v (.s i)=[]) :
    LayRuns body compactRowReserve (synG R v)
      (synG R (Function.update v (.s 8)
        (List.replicate (CompactGlobalRowPadding.rowAxes NW m d) tick)))
      (compactRowReserveCost d) := by
  have h2 := hz 2 (by simp); have h8 := hz 8 (by simp)
  have h9 := hz 9 (by simp); have h10 := hz 10 (by simp)
  have h11 := hz 11 (by simp); have h17 := hz 17 (by simp); have h23 := hz 23 (by simp)
  have hj : synJk m (2*d-1) (2*d-1) = Nat.clog m (2*d) := compactRowLog d hd
  refine lr_weaken body
    ((sgU_umul body 2 (R := R) (v := v) (a := .s 0) (b := .s 9) (t := .s 2)
      (x := d) (y := 0) (by decide) (by decide) (by decide) h2 h0 (by simpa using h9)).seq <|
    (sgU_pop body (a := .s 9) (y := 2*d) (by simp)).seq <|
    (sgU_copy body (a := .s 9) (b := .s 10) (t := .s 2) (x := 2*d-1) (y := 0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [h10])).seq <|
    (sg_synCntLoop body m (by have := m_pos; omega) (x := .s 10) (cnt := .s 11) (ctr := .s 9)
      _ (2*d-1) (2*d-1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp) (by simp [h11]) (by simp) (by simp [h17]) (by simp [h2]) (by simp [h23])).seq <|
    (sgU_umul body (Nat.clog 2 NW) (a := .s 11) (b := .s 8) (t := .s 2)
      (x := synJ (2*d-1) (2*d-1)) (y := 0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [synJ]) (by simp [h8])).seq <|
    (sgU_clear body (a := .s 9) (x := 2*d-1) (by simp)).seq <|
    (sgU_clear body (a := .s 10) (x := 0) (by simp [div_pow_self])).seq <|
    sgU_clear body (a := .s 11) (x := synJ (2*d-1) (2*d-1)) (by simp [synJ])) ?_ ?_
  · apply congrArg (synG R)
    funext z
    simp only [Function.update_apply]
    split_ifs <;> simp_all [CompactGlobalRowPadding.rowAxes,compactRowLog d hd]
  · simp only [compactRowReserveCost]
    omega

end
end IntegerMultBounds.MathlibTM2.Fast
