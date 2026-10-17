module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedScannerRecord

/-! Actual stopped digit-body execution with a supplied cutoff on s22.
The tail clears the rebased leaf count, not the original base-m digit.
The scanner prefix on s23 and live registers s27/s28 are preserved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
variable {Q A : ℕ} {U P : Type}
variable (body : P → Pr P (nT SXReg) Q A U) {R : Fin (nT SXReg) → List (Fin (A+4))}

noncomputable def compactStoppedDigBody (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (udiv m (sreg (.s 12)) (sreg (.s 17)) (sreg (.s 2))) <|
  .seq (umul m (sreg (.s 17)) (sreg (.s 24)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.s 12)) (sreg (.s 18)) (sreg (.s 2))) <|
  .seq (usub (sreg (.s 24)) (sreg (.s 18)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.s 24))) <|
  .seq (synIfNE (sreg (.s 18)) (compactStoppedScannerRecord G F) synSkip) <|
  .seq (uclear (sreg (.s 18))) <|
  .seq (uclear (sreg (.s 12))) <|
  .seq (moveR (sreg (.s 17)) (sreg (.s 12)) id) <|
  .seq (synMulIn m (sreg (.s 13)) (sreg (.s 2)) (sreg (.s 3))) (synPush (sreg (.s 14)) tick)

/-- The step bound of one pass of the digit loop on `x`. -/
def compactStoppedDigBodyCost (G F Kv cutoff x t A0 prefixLen : ℕ) : ℕ :=
  (4 * x + 4) + (4 * (x / m) + 4) + (4 * x + 4) + (4 * (m * (x / m)) + 4) +
    (2 * (m * (x / m)) + 2) +
    ((if x - m * (x / m) = 0 then 1 else compactStoppedScannerRecordCost G F Kv cutoff t (x - m * (x / m)) A0 x prefixLen) + 2) +
    (2 * ((x - m * (x / m)) * m^(min t cutoff)) + 2) + (2 * x + 2) + (2 * (x / m) + 2) + (8 * m ^ t + 8) + 1

theorem sg_compactStoppedDigBody (G F : ℕ) (v : SynW → List (Fin (A + 4))) (cutoff Kv x t A0 E : ℕ)
    (Prl : List (Fin (A + 4))) (hx : v (.s 12) = List.replicate x tick)
    (hP : v (.s 13) = List.replicate (m ^ t) tick) (hJ : v (.s 14) = List.replicate t tick)
    (hA0 : v (.s 15) = List.replicate A0 tick) (hE : v (.s 16) = List.replicate E tick)
    (hpr : v (.p .pr) = Prl) (hK : (v (.p .K)).length = Kv) (h2 : v (.s 2) = [])
    (h3 : v (.s 3) = []) (h4 : v (.s 4) = []) (h17 : v (.s 17) = []) (h18 : v (.s 18) = [])
    (h19 : v (.s 19) = []) (h20 : v (.s 20) = []) (h21 : v (.s 21) = [])
    (h24 : v (.s 24) = []) (hc : (v (.s 22)).length = cutoff)
    (h29 : v (.s 29) = []) (h30 : v (.s 30) = []) (h31 : v (.s 31) = []) :
    LayRuns body (compactStoppedDigBody G F) (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update v (.s 12) (List.replicate (x / m) tick)) (.s 13)
          (List.replicate (m * m ^ t) tick)) (.s 14) (List.replicate (t + 1) tick)) (.s 15)
          (List.replicate (if x - m * (x / m) = 0 then A0
            else Kv * ((x - m * (x / m)) * m ^ t) + A0) tick)) (.s 16)
          (List.replicate (if x - m * (x / m) = 0 then E
            else expSeq G F ((x - m * (x / m))*m^(min t cutoff)) (t-cutoff) + E) tick)) (.p .pr)
          (if x - m * (x / m) = 0 then Prl
            else topRec [t-cutoff, (x - m * (x / m))*m^(min t cutoff), A0, Kv * ((x - m * (x / m)) * m ^ t)] ++ Prl)))
      (compactStoppedDigBodyCost G F Kv cutoff x t A0 (v (.s 23)).length) := by
  have hm1 : 1 ≤ m := m_pos
  have s1 := sgU_div body (R := R) (v := v) (k := m) (a := .s 12) (b := .s 17) (t := .s 2) (x := x)
    (y := 0) hm1 (by decide) (by decide) (by decide) h2 (by simp [hx]) (by simp [h17])
  have s2 := sgU_umul body (R := R) m (a := .s 17) (b := .s 24) (t := .s 2) (x := x / m) (y := 0)
    (v := Function.update v (.s 17) (List.replicate (x / m + 0) tick)) (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [h24])
  have s3 := sgU_copy body (R := R) (a := .s 12) (b := .s 18) (t := .s 2) (x := x) (y := 0)
    (v := Function.update (Function.update v (.s 17) (List.replicate (x / m + 0) tick)) (.s 24)
      (List.replicate (m * (x / m) + 0) tick))
    (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hx]) (by simp [h18])
  have s4 := sgU_sub body (R := R) (a := .s 24) (b := .s 18) (t := .s 2) (x := m * (x / m))
    (y := x + 0)
    (v := Function.update (Function.update (Function.update v (.s 17)
      (List.replicate (x / m + 0) tick)) (.s 24) (List.replicate (m * (x / m) + 0) tick)) (.s 18)
      (List.replicate (x + 0) tick))
    (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp)
  have s5 := sgU_clear body (R := R) (a := .s 24) (x := m * (x / m))
    (v := Function.update (Function.update (Function.update (Function.update v (.s 17)
      (List.replicate (x / m + 0) tick)) (.s 24) (List.replicate (m * (x / m) + 0) tick)) (.s 18)
      (List.replicate (x + 0) tick)) (.s 18) (List.replicate (x + 0 - m * (x / m)) tick))
    (by simp)
  set d := x - m * (x / m) with hd
  set v₅ := Function.update (Function.update (Function.update (Function.update (Function.update v
    (.s 17) (List.replicate (x / m + 0) tick)) (.s 24) (List.replicate (m * (x / m) + 0) tick))
    (.s 18) (List.replicate (x + 0) tick)) (.s 18) (List.replicate (x + 0 - m * (x / m)) tick))
    (.s 24) [] with hv₅
  have e18 : v₅ (.s 18) = List.replicate d tick := by simp [hv₅, hd]
  -- the tail after the branch
  have tail : ∀ (leaf A0' E' : ℕ) (Prl' : List (Fin (A + 4))) (w : SynW → List (Fin (A + 4))),
      w (.s 18) = List.replicate leaf tick → w (.s 12) = List.replicate x tick →
      w (.s 17) = List.replicate (x / m) tick → w (.s 13) = List.replicate (m ^ t) tick →
      w (.s 14) = List.replicate t tick → w (.s 2) = [] → w (.s 3) = [] →
      LayRuns body (.seq (uclear (sreg (.s 18))) <| .seq (uclear (sreg (.s 12))) <|
          .seq (moveR (sreg (.s 17)) (sreg (.s 12)) id) <|
          .seq (synMulIn m (sreg (.s 13)) (sreg (.s 2)) (sreg (.s 3)))
            (synPush (sreg (.s 14)) tick)) (synG R w)
        (synG R (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update w (.s 18) []) (.s 12) []) (.s 17) []) (.s 12)
            (List.replicate (x / m) tick)) (.s 13) (List.replicate (m * m ^ t) tick)) (.s 14)
            (List.replicate (t + 1) tick)))
        (2 * leaf + 2 + (2 * x + 2 + (2 * (x / m) + 2 + (8 * m ^ t + 8 + 1)))) := by
    intro leaf A0' E' Prl' w w18 w12 w17 w13 w14 w2 w3
    exact lr_weaken body
      ((sgU_clear body (a := .s 18) (x := leaf) (by simp [w18])).seq <|
      (sgU_clear body (a := .s 12) (x := x) (by simp [w12])).seq <|
      (sgU_move body (a := .s 17) (b := .s 12) (x := x / m) (by decide) (by simp [w17])
        (by simp)).seq <|
      (sgU_mulIn body m (a := .s 13) (t := .s 2) (t₁ := .s 3) (x := m ^ t) (by decide)
        (by simp [w2]) (by simp [w3]) (by simp [w13])).seq <|
      sgU_push body (a := .s 14) (y := t) (by simp [w14])) rfl le_rfl
  by_cases hd0 : d = 0
  · have s6 := sg_ifNE_neg body (p := compactStoppedScannerRecord G F) (x := .s 18) (R := R) (v := v₅)
      (by rw [e18, hd0]; rfl) (sg_skip body)
    have s7 := tail (d*m^(min t cutoff)) A0 E Prl v₅ (by simp [e18, hd0]) (by simp [hv₅, hx]) (by simp [hv₅]) (by simp [hv₅, hP])
      (by simp [hv₅, hJ]) (by simp [hv₅, h2]) (by simp [hv₅, h3])
    refine lr_weaken body (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))) ?_ ?_
    · simp only [hd0, ite_true]
      refine congrArg (synG R) ?_
      funext y
      by_cases hy12 : y = .s 12
      · subst y
        simp [hv₅]
      by_cases hy13 : y = .s 13
      · subst y
        simp [hv₅]
      by_cases hy14 : y = .s 14
      · subst y
        simp [hv₅]
      by_cases hy15 : y = .s 15
      · subst y
        simp [hv₅, hA0]
      by_cases hy16 : y = .s 16
      · subst y
        simp [hv₅, hE]
      by_cases hy17 : y = .s 17
      · subst y
        simp [hv₅, h17]
      by_cases hy18 : y = .s 18
      · subst y
        simp [hv₅, h18]
      by_cases hy24 : y = .s 24
      · subst y
        simp [hv₅, h24]
      by_cases hypr : y = .p .pr
      · subst y
        simp [hv₅, hpr]
      simp [hv₅, hy12, hy13, hy14, hy15, hy16, hy17, hy18, hy24, hypr]
    · simp only [compactStoppedDigBodyCost, ← hd, hd0, ite_true]
      omega
  · have s6 := sg_ifNE_pos body (p := compactStoppedScannerRecord G F) (q := synSkip) (x := .s 18) (R := R)
      (v := v₅) (by rw [e18]; simpa using hd0)
      (sg_compactStoppedScannerRecord body G F v₅ cutoff Kv t d A0 E Prl
        (by simp [hv₅,hJ]) e18 (by simp [hv₅,hP]) (by simp [hv₅,hc])
        (by simp [hv₅,hA0]) (by simp [hv₅,hE]) (by simp [hv₅,hpr]) (by simp [hv₅,hK])
        (by simp [hv₅,h2]) (by simp [hv₅,h3]) (by simp [hv₅,h4])
        (by simp [hv₅,h19]) (by simp [hv₅,h20]) (by simp [hv₅,h21])
        (by simp [hv₅]) (by simp [hv₅,h29]) (by simp [hv₅,h30]) (by simp [hv₅,h31]))
    have s7 := tail (d*m^(min t cutoff)) (Kv * bits d t + A0)
      (expSeq G F (d*m^(min t cutoff)) (t-cutoff) + E)
      (topRec [t-cutoff,d*m^(min t cutoff),A0,Kv*bits d t] ++ Prl)
      (Function.update (Function.update (Function.update (Function.update v₅
        (.s 18) (List.replicate (d*m^(min t cutoff)) tick)) (.s 15)
        (List.replicate (Kv*bits d t+A0) tick)) (.s 16)
        (List.replicate (expSeq G F (d*m^(min t cutoff)) (t-cutoff)+E) tick)) (.p .pr)
        (topRec [t-cutoff,d*m^(min t cutoff),A0,Kv*bits d t] ++ Prl))
      (by simp) (by simp [hv₅,hx]) (by simp [hv₅]) (by simp [hv₅,hP])
      (by simp [hv₅,hJ]) (by simp [hv₅,h2]) (by simp [hv₅,h3])
    refine lr_weaken body (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))) ?_ ?_
    · simp only [hd0, ite_false]
      refine congrArg (synG R) ?_
      funext y
      by_cases hy12 : y = .s 12
      · subst y
        simp [hv₅, hd, bits_eq_mul]
      by_cases hy13 : y = .s 13
      · subst y
        simp [hv₅, hd, bits_eq_mul]
      by_cases hy14 : y = .s 14
      · subst y
        simp [hv₅, hd, bits_eq_mul]
      by_cases hy15 : y = .s 15
      · subst y
        simp [hv₅, hd, bits_eq_mul]
      by_cases hy16 : y = .s 16
      · subst y
        simp [hv₅, hd, bits_eq_mul]
      by_cases hy17 : y = .s 17
      · subst y
        simp [hv₅, hd, bits_eq_mul, h17]
      by_cases hy18 : y = .s 18
      · subst y
        simp [hv₅, hd, bits_eq_mul, h18]
      by_cases hy24 : y = .s 24
      · subst y
        simp [hv₅, hd, bits_eq_mul, h24]
      by_cases hypr : y = .p .pr
      · subst y
        simp [hv₅, hd, bits_eq_mul]
      simp [hv₅, hy12, hy13, hy14, hy15, hy16, hy17, hy18, hy24, hypr]
    · simp [compactStoppedDigBodyCost, ← hd, hd0, hv₅, hx]
      omega


end IntegerMultBounds.MathlibTM2.Fast
