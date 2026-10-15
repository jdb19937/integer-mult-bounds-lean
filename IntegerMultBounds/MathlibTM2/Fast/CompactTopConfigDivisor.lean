module

public import IntegerMultBounds.MathlibTM2.Fast.SynRec
public import IntegerMultBounds.Machine.CompactGlobalRowPadding

/-! Runtime construction of the global divisor from the original axis count.
No depth or row-reservation oracle is supplied to the machine. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

lemma compactTopConfigDepth (d : ℕ) (hd : 0<d) :
    synJ (d-1) (d-1) = CompactGlobalRowPadding.depth m d := by
  by_cases h1 : d=1
  · subst d; simp [synJ,synJk,CompactGlobalRowPadding.depth]
  rw [synJ_self_eq (by omega)]
  unfold CompactGlobalRowPadding.depth
  apply eq_of_forall_lt_iff
  intro t
  rw [Nat.lt_clog_iff_pow_lt one_lt_m]
  have hh := Nat.le_log_iff_pow_le (b := m) (x := t) (y := d-1) one_lt_m (by omega)
  omega

/-- Original d on s0; exact global divisor on s7; every other register restored. -/
def compactTopConfigDivisor : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.s 0)) (sreg (.s 9)) (sreg (.s 2))) <|
  .seq (synPop (sreg (.s 9))) <|
  .seq (ucopy (sreg (.s 9)) (sreg (.s 10)) (sreg (.s 2))) <|
  .seq (synCntLoop m (.s 10) (.s 22) (.s 9)) <|
  .seq (synPush (sreg (.s 7)) tick) <|
  .seq synNWLoop <|
  .seq (uclear (sreg (.s 9))) <|
  .seq (uclear (sreg (.s 10))) (uclear (sreg (.s 22)))

def compactTopConfigDivisorCost (d : ℕ) : ℕ :=
  (4*d+4)+1+(4*(d-1)+4)+synCntCost m (d-1) (d-1)+
    (1+(∑ j ∈ Finset.range (synJ (d-1) (d-1)), (8*(NW^j*1)+8+3))+2*synJ (d-1) (d-1)+4)+(2*(d-1)+2)+2+(2*synJ (d-1) (d-1)+2)

theorem sg_compactTopConfigDivisor (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (d : ℕ) (hd : 0<d) (h0 : (v (.s 0)).length=d)
    (hz : ∀ i : Fin 32, i∈[2,3,7,9,10,17,22,23] → v (.s i)=[]) :
    LayRuns body compactTopConfigDivisor (synG R v)
      (synG R (Function.update v (.s 7)
        (List.replicate (NW^CompactGlobalRowPadding.depth m d) tick)))
      (compactTopConfigDivisorCost d) := by
  have h2 := hz 2 (by simp); have h3 := hz 3 (by simp); have h7 := hz 7 (by simp)
  have h9 := hz 9 (by simp); have h10 := hz 10 (by simp)
  have h22 := hz 22 (by simp); have h17 := hz 17 (by simp); have h23 := hz 23 (by simp)
  have hj : synJk m (d-1) (d-1) = CompactGlobalRowPadding.depth m d := compactTopConfigDepth d hd
  refine lr_weaken body
    ((sgU_copy body (R := R) (v := v) (a := .s 0) (b := .s 9) (t := .s 2)
      (x := d) (y := 0) (by decide) (by decide) (by decide) h2 h0 (by simpa using h9)).seq <|
    (sgU_pop body (a := .s 9) (y := d) (by simp)).seq <|
    (sgU_copy body (a := .s 9) (b := .s 10) (t := .s 2) (x := d-1) (y := 0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [h10])).seq <|
    (sg_synCntLoop body m (by have := m_pos; omega) (x := .s 10) (cnt := .s 22) (ctr := .s 9)
      _ (d-1) (d-1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp) (by simp [h22]) (by simp) (by simp [h17]) (by simp [h2]) (by simp [h23])).seq <|
    (sgU_push body (a := .s 7) (y := 0) (by simp [h7])).seq <|
    (sg_synNWLoop body _ (synJ (d-1) (d-1)) 1
      (by simp [synJ]) (by simp [h23]) (by simp) (by simp [h2]) (by simp [h3])).seq <|
    (sgU_clear body (a := .s 9) (x := d-1) (by simp)).seq <|
    (sgU_clear body (a := .s 10) (x := 0) (by simp [div_pow_self])).seq <|
    sgU_clear body (a := .s 22) (x := synJ (d-1) (d-1)) (by simp [synJ])) ?_ ?_
  · apply congrArg (synG R)
    funext z
    simp only [Function.update_apply]
    split_ifs <;> simp_all [compactTopConfigDepth d hd]
  · simp only [compactTopConfigDivisorCost]
    omega

end
end IntegerMultBounds.MathlibTM2.Fast
