module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedDigBody

/-! Actual supplied-cutoff digit scanner. The scan records the stopped exponent
and rebased fields at every nonzero digit, retaining cutoff22 and all remaining
live wires. Cutoff computation, precision analysis and layer-cost absorption
remain separate obligations. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
variable {Q A : ℕ} {U P : Type}
variable (body : P → Pr P (nT SXReg) Q A U) {R : Fin (nT SXReg) → List (Fin (A+4))}

/-- Accumulated exponent of the actually emitted stopped records. -/
noncomputable def compactStoppedE (G F cutoff D : ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => if synDg D t = 0 then compactStoppedE G F cutoff D t else
      expSeq G F (synDg D t*m^(min t cutoff)) (t-cutoff)+compactStoppedE G F cutoff D t

/-- Literal stopped fields in the same prepend order as the executed scanner. -/
noncomputable def compactStoppedFields (cutoff Kv oS D : ℕ) : ℕ → List ℕ
  | 0 => []
  | t+1 => if synDg D t = 0 then compactStoppedFields cutoff Kv oS D t else
      [t-cutoff,synDg D t*m^(min t cutoff),oS+Kv*(D%m^t),Kv*(synDg D t*m^t)] ++
        compactStoppedFields cutoff Kv oS D t

noncomputable def compactStoppedDigits (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.s 26)) (sreg (.s 12)) (sreg (.s 2))) <|
  .seq (synPush (sreg (.s 13)) tick) <|
  .seq (ucopy (sreg (.s 6)) (sreg (.s 15)) (sreg (.s 2))) <|
  .seq (scanP (sreg (.s 26)) (sreg (.s 23)) (synIfNE (sreg (.s 12)) (compactStoppedDigBody G F) synSkip)) <|
  .seq (uclear (sreg (.s 12))) <| .seq (uclear (sreg (.s 13))) (uclear (sreg (.s 15)))

/-- The wire file after `t` passes of the digit loop. -/
noncomputable def compactStoppedDigSt (G F cutoff Kv oS D : ℕ) (v : SynW → List (Fin (A + 4))) (t : ℕ) :
    SynW → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update v (.s 12) (List.replicate (D / m ^ t) tick)) (.s 13)
      (List.replicate (m ^ synJ D t) tick)) (.s 14) (List.replicate (synJ D t) tick)) (.s 15)
      (List.replicate (oS + Kv * (D % m ^ t)) tick)) (.s 16)
      (List.replicate (compactStoppedE G F cutoff D t) tick)) (.p .pr)
      (topRec (compactStoppedFields cutoff Kv oS D t))

/-- The step bound of pass `t` of the digit loop. -/
def compactStoppedDigPassCost (G F cutoff Kv oS D t : ℕ) : ℕ :=
  if D / m ^ t = 0 then 3
  else compactStoppedDigBodyCost G F Kv cutoff (D / m ^ t) t (oS + Kv * (D % m ^ t)) (t+1) + 2

/-- The step bound of the digit loop. -/
def compactStoppedDigitsCost (G F cutoff Kv oS D : ℕ) : ℕ :=
  (4 * D + 4) + 1 + (4 * oS + 4) +
    ((∑ t ∈ Finset.range D, (compactStoppedDigPassCost G F cutoff Kv oS D t + 3)) + 2 * D + 4) +
    2 + (2 * m ^ synJ D D + 2) + (2 * (oS + Kv * D) + 2)

theorem compactStoppedDigSt_zero_pass {G F cutoff Kv oS D : ℕ} (v : SynW → List (Fin (A + 4))) {t : ℕ}
    (h : D / m ^ t = 0) : compactStoppedDigSt G F cutoff Kv oS D v (t + 1) = compactStoppedDigSt G F cutoff Kv oS D v t := by
  have h1 : D / m ^ (t + 1) = 0 := by rw [div_pow_succ', h]; simp
  simp only [compactStoppedDigSt, h1, h, synJ_eq_of_zero h, mod_pow_of_zero h, compactStoppedE, compactStoppedFields,
    synDg_of_zero h, ite_true]

theorem sg_compactStoppedDigits (G F : ℕ) (v : SynW → List (Fin (A + 4))) (cutoff Kv oS D : ℕ)
    (hoS : v (.s 6) = List.replicate oS tick) (hK : (v (.p .K)).length = Kv)
    (hD : (v (.s 26)).length = D) (hpr : v (.p .pr) = [])
    (hs : ∀ i, 12 ≤ i → i ≤ 24 → i ≠ 22 → v (.s i) = [])
    (hc : (v (.s 22)).length = cutoff)
    (h29 : v (.s 29) = []) (h30 : v (.s 30) = []) (h31 : v (.s 31) = []) (h2 : v (.s 2) = []) (h3 : v (.s 3) = [])
    (h4 : v (.s 4) = []) :
    LayRuns body (compactStoppedDigits G F) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.s 14)
        (List.replicate (synJ D D) tick)) (.s 16) (List.replicate (compactStoppedE G F cutoff D D) tick)) (.p .pr)
        (topRec (compactStoppedFields cutoff Kv oS D D))))
      (compactStoppedDigitsCost G F cutoff Kv oS D) := by
  have hz : ∀ i : Fin 32, 12 ≤ (i : ℕ) → (i : ℕ) ≤ 24 → i ≠ 22 → v (.s i) = [] := fun i h1 h2 h3 => hs i h1 h2 h3
  have h12 := hz 12 (by decide) (by decide) (by decide)
  have h13 := hz 13 (by decide) (by decide) (by decide)
  have h14 := hz 14 (by decide) (by decide) (by decide)
  have h15 := hz 15 (by decide) (by decide) (by decide)
  have h16 := hz 16 (by decide) (by decide) (by decide)
  have h17 := hz 17 (by decide) (by decide) (by decide)
  have h18 := hz 18 (by decide) (by decide) (by decide)
  have h19 := hz 19 (by decide) (by decide) (by decide)
  have h20 := hz 20 (by decide) (by decide) (by decide)
  have h21 := hz 21 (by decide) (by decide) (by decide)
  have h23 := hz 23 (by decide) (by decide) (by decide)
  have h24 := hz 24 (by decide) (by decide) (by decide)
  set cs := v (.s 26) with hcs
  set Φ := compactStoppedDigSt G F cutoff Kv oS D v with hΦ
  have hstep : ∀ t < cs.length, LayRuns body (synIfNE (sreg (.s 12)) (compactStoppedDigBody G F) synSkip)
      (synG R (Function.update (Function.update (Φ t) (.s 26) (cs.drop (t + 1))) (.s 23)
        (cs.take (t + 1)).reverse))
      (synG R (Function.update (Function.update (Φ (t + 1)) (.s 26) (cs.drop (t + 1))) (.s 23)
        (cs.take (t + 1)).reverse)) (compactStoppedDigPassCost G F cutoff Kv oS D t) := by
    intro t ht
    set w := Function.update (Function.update (Φ t) (.s 26) (cs.drop (t + 1))) (.s 23)
      (cs.take (t + 1)).reverse with hw
    by_cases hx : D / m ^ t = 0
    · rw [hΦ, compactStoppedDigSt_zero_pass v hx]
      refine lr_weaken body (sg_ifNE_neg body (by simp [hw, hΦ, compactStoppedDigSt, hx]) (sg_skip body))
        rfl (by simp [compactStoppedDigPassCost, hx])
    · have hJt : synJ D t = t := synJ_eq_of_pos (Nat.pos_of_ne_zero hx)
      have hb := sg_compactStoppedDigBody body (R := R) G F w cutoff Kv (D / m ^ t) t (oS + Kv * (D % m ^ t))
        (compactStoppedE G F cutoff D t) (topRec (compactStoppedFields cutoff Kv oS D t))
        (by simp [hw, hΦ, compactStoppedDigSt]) (by simp [hw, hΦ, compactStoppedDigSt, hJt])
        (by simp [hw, hΦ, compactStoppedDigSt, hJt]) (by simp [hw, hΦ, compactStoppedDigSt])
        (by simp [hw, hΦ, compactStoppedDigSt]) (by simp [hw, hΦ, compactStoppedDigSt]) (by simp [hw, hΦ, compactStoppedDigSt, hK])
        (by simp [hw, hΦ, compactStoppedDigSt, h2]) (by simp [hw, hΦ, compactStoppedDigSt, h3])
        (by simp [hw, hΦ, compactStoppedDigSt, h4]) (by simp [hw, hΦ, compactStoppedDigSt, h17])
        (by simp [hw, hΦ, compactStoppedDigSt, h18]) (by simp [hw, hΦ, compactStoppedDigSt, h19])
        (by simp [hw, hΦ, compactStoppedDigSt, h20]) (by simp [hw, hΦ, compactStoppedDigSt, h21])
        (by simp [hw, hΦ, compactStoppedDigSt, h24])
        (by simp [hw, hΦ, compactStoppedDigSt, hc])
        (by simp [hw, hΦ, compactStoppedDigSt, h29])
        (by simp [hw, hΦ, compactStoppedDigSt, h30])
        (by simp [hw, hΦ, compactStoppedDigSt, h31])
      refine lr_weaken body (sg_ifNE_pos body (q := synSkip)
        (by
          rw [show w (.s 12) = List.replicate (D / m ^ t) tick by simp [hw, hΦ, compactStoppedDigSt]]
          intro h; exact hx (by simpa using congrArg List.length h)) hb) ?_
        (by simp [compactStoppedDigPassCost, hx, hw, hΦ, compactStoppedDigSt, Nat.min_eq_left (by omega : t+1 ≤ cs.length)])
      have hJ1 : synJ D (t + 1) = t + 1 := by rw [synJ_succ, hJt]; simp [Nat.pos_of_ne_zero hx]
      have hdg := synDg_eq D t
      rw [hdg]
      refine congrArg (synG R) ?_
      have e12 : D / m ^ t / m = D / m ^ (t + 1) := (div_pow_succ' D t).symm
      have e13 : m * m ^ t = m ^ (t + 1) := (pow_succ' m t).symm
      have e15 : (if synDg D t = 0 then oS + Kv * (D % m ^ t)
          else Kv * (synDg D t * m ^ t) + (oS + Kv * (D % m ^ t))) =
          oS + Kv * (D % m ^ (t + 1)) := by
        rw [mod_pow_succ_dg]
        split_ifs with h0
        · rw [h0]; ring
        · ring
      have e16 : (if synDg D t = 0 then compactStoppedE G F cutoff D t
          else expSeq G F (synDg D t*m^(min t cutoff)) (t-cutoff) + compactStoppedE G F cutoff D t) = compactStoppedE G F cutoff D (t + 1) := by
        rw [compactStoppedE]
      have epr : (if synDg D t = 0 then topRec (compactStoppedFields cutoff Kv oS D t)
          else topRec [t-cutoff, synDg D t*m^(min t cutoff), oS + Kv * (D % m ^ t), Kv * (synDg D t * m ^ t)] ++
            topRec (compactStoppedFields cutoff Kv oS D t)) =
          (topRec (compactStoppedFields cutoff Kv oS D (t+1)) : List (Fin (A + 4))) := by
        rw [compactStoppedFields]
        split_ifs
        · rfl
        · exact (topRec_append _ _).symm
      rw [e12, e13, e15, e16, epr]
      funext y
      by_cases hy12 : y = .s 12
      · subst y
        simp [hw, hΦ, compactStoppedDigSt, hJ1]
      by_cases hy13 : y = .s 13
      · subst y
        simp [hw, hΦ, compactStoppedDigSt, hJ1]
      by_cases hy14 : y = .s 14
      · subst y
        simp [hw, hΦ, compactStoppedDigSt, hJ1]
      by_cases hy15 : y = .s 15
      · subst y
        simp [hw, hΦ, compactStoppedDigSt, hJ1]
      by_cases hy16 : y = .s 16
      · subst y
        simp [hw, hΦ, compactStoppedDigSt, hJ1]
      by_cases hy23 : y = .s 23
      · subst y
        simp [hw, hΦ, compactStoppedDigSt, hJ1]
      by_cases hy26 : y = .s 26
      · subst y
        simp [hw, hΦ, compactStoppedDigSt, hJ1]
      by_cases hypr : y = .p .pr
      · subst y
        simp [hw, hΦ, compactStoppedDigSt, hJ1]
      simp [hw, hΦ, compactStoppedDigSt, hy12, hy13, hy14, hy15, hy16, hy23, hy26, hypr]
  have hscan := sg_scan body (R := R) (a := .s 26) (t := .s 23) (by decide) Φ cs
    (fun t => compactStoppedDigPassCost G F cutoff Kv oS D t) hstep
  have hcsl : cs.length = D := hD
  rw [hcsl] at hscan
  have hfin : Φ D (.s 12) = [] := by simp [hΦ, compactStoppedDigSt, div_pow_self]
  refine lr_weaken body
    ((sgU_copy body (a := .s 26) (b := .s 12) (t := .s 2) (x := D) (y := 0) (by decide)
      (by decide) (by decide) h2 hD (by simp [h12])).seq <|
    (sgU_push body (a := .s 13) (y := 0) (by simp [h13])).seq <|
    (sgU_copy body (a := .s 6) (b := .s 15) (t := .s 2) (x := oS) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hoS]) (by simp [h15])).seq <|
    (lr_congr_left body hscan ?_).seq <|
    (sgU_clear body (a := .s 12) (x := 0) (by simp [hΦ, compactStoppedDigSt, div_pow_self])).seq <|
    (sgU_clear body (a := .s 13) (x := m ^ synJ D D) (by simp [hΦ, compactStoppedDigSt])).seq <|
    sgU_clear body (a := .s 15) (x := oS + Kv * D) (by simp [hΦ, compactStoppedDigSt, mod_pow_self])) ?_ ?_
  · refine congrArg (synG R) ?_
    funext y
    by_cases hy12 : y = .s 12
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, compactStoppedE, compactStoppedFields, hcs]
    by_cases hy13 : y = .s 13
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, compactStoppedE, compactStoppedFields, hcs]
    by_cases hy14 : y = .s 14
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, compactStoppedE, compactStoppedFields, h14, hcs]
    by_cases hy15 : y = .s 15
    · subst y
      simp [Nat.mod_one, hΦ, compactStoppedDigSt, synJ, synJk, compactStoppedE, compactStoppedFields, hcs]
    by_cases hy16 : y = .s 16
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, compactStoppedE, compactStoppedFields, h16, hcs]
    by_cases hy23 : y = .s 23
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, compactStoppedE, compactStoppedFields, h23, hcs]
    by_cases hy26 : y = .s 26
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, compactStoppedE, compactStoppedFields, hcs]
    by_cases hypr : y = .p .pr
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, compactStoppedE, compactStoppedFields, hpr, hcs]
    simp [hΦ, compactStoppedDigSt, hy12, hy13, hy14, hy15, hy16, hy23, hy26, hypr]
  · refine congrArg (synG R) ?_
    funext y
    by_cases hy12 : y = .s 12
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, h12, hcs, div_pow_self]
    by_cases hy13 : y = .s 13
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, h13, hcs, div_pow_self]
    by_cases hy14 : y = .s 14
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, hcs, div_pow_self]
    by_cases hy15 : y = .s 15
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, h15, hcs, div_pow_self]
    by_cases hy16 : y = .s 16
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, hcs, div_pow_self]
    by_cases hy23 : y = .s 23
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, h23, hcs, div_pow_self]
    by_cases hy26 : y = .s 26
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, hcs, div_pow_self]
    by_cases hypr : y = .p .pr
    · subst y
      simp [hΦ, compactStoppedDigSt, synJ, synJk, hcs, div_pow_self]
    simp [hΦ, compactStoppedDigSt, hy12, hy13, hy14, hy15, hy16, hy23, hy26, hypr]
  · simp only [compactStoppedDigitsCost]
    omega


end IntegerMultBounds.MathlibTM2.Fast
