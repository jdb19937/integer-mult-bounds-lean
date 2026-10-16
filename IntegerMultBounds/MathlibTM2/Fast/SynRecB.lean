module

public import IntegerMultBounds.MathlibTM2.Fast.SynRec

/-!
# The chunk branch of the record builder, and `synRec`

Paper §6, proof of `lem:synthetic-transform-cost`. The chunk branch `synChunkB` of the record
builder (`Fast/SynRec.lean`): `synChunkA` (stride, offset `ρ_h`, `oS`), `synChunkQ` (the kernel
bits `q₀`, `D'`, `a'`, `aT`), `synDigits` (the pieces of the base-`m` digits of `D'`),
`synChunkR2` (the rows `R₂ = 2^X NW^J'`), `synChunkCfg` (the configuration record) and
`synChunkEnd` (`w'`, scratch cleared). `sg_synRec` is the contract of the whole builder.

**Rows.** `synR2c_ge`, `synR2c_lt`: `2^a' ≤ R₂ < 2^(a' + 1)` for `K ≥ 1`, since
`NW^J' ≤ 2^a'` (`NW_pow_synJp_le`: `a' ≥ K q₀ ≥ 46 J ≥ 46 J'` when `46 J ≤ D`, and `J' = 0`
otherwise) and `X = a' - ⌊log₂ NW^J'⌋`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Node hiding LReg

set_option maxHeartbeats 4000000

/-! ### The rows of a chunk round -/

section Rows

variable (es : List ℕ) (ℓ K : ℕ)

theorem synQK_le : synQK es ≤ es.length := Nat.sub_le _ _

theorem synQK_eq_min : synQK es = min (synCW * synJt es) es.length := by
  unfold synQK synQKn; omega

theorem synDpp_add_synQK : synDpp es + synQK es = es.length := Nat.sub_add_cancel (synQK_le es)

theorem synJp_le_synJt : synJp es ≤ synJt es := by
  unfold synJp synJt
  have := synJ_self_mono (D := es.length) (D' := synDpp es) (Nat.sub_le _ _)
  omega

theorem NW_le_pow_synCW : NW ≤ 2 ^ synCW := by
  rw [Cost.br_NW_eq]; norm_num [synCW]

theorem NW_pos : 0 < NW := Nat.pos_of_ne_zero (NeZero.ne _)

/-- `NW^J' ≤ 2^a'` for `K ≥ 1`. -/
theorem NW_pow_synJp_le (hK : 1 ≤ K) : NW ^ synJp es ≤ 2 ^ synAc es ℓ K := by
  by_cases h : synCW * synJt es ≤ es.length
  · have hq : synQK es = synCW * synJt es := by rw [synQK_eq_min, min_eq_left h]
    have hJ := synJp_le_synJt es
    calc NW ^ synJp es ≤ (2 ^ synCW) ^ synJp es := Nat.pow_le_pow_left NW_le_pow_synCW _
      _ = 2 ^ (synCW * synJp es) := by rw [← pow_mul]
      _ ≤ 2 ^ synAc es ℓ K := by
          apply Nat.pow_le_pow_right (by norm_num)
          unfold synAc
          rw [hq]
          have h1 : synCW * synJp es ≤ synCW * synJt es := Nat.mul_le_mul_left _ hJ
          have h2 : 1 * (synCW * synJt es) ≤ K * (synCW * synJt es) :=
            Nat.mul_le_mul_right _ hK
          omega
  · have hq : synQK es = es.length := by rw [synQK_eq_min, min_eq_right (by omega)]
    have hD' : synDpp es = 0 := by unfold synDpp; omega
    have hJ : synJp es = 0 := by unfold synJp; rw [hD']; simp [synJ, synJk_zero_left]
    rw [hJ, pow_zero]
    exact Nat.one_le_two_pow

theorem synLb_eq (hK : 1 ≤ K) : synLb es ℓ K = Nat.log 2 (NW ^ synJp es) := by
  unfold synLb
  have hB : NW ^ synJp es ≠ 0 := (pow_pos NW_pos _).ne'
  have hlt : NW ^ synJp es < 2 ^ (synAc es ℓ K + 1) :=
    lt_of_le_of_lt (NW_pow_synJp_le es ℓ K hK) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have := Nat.log_lt_of_lt_pow hB hlt
  rw [synJk_eq_min (by norm_num) hB]
  omega

theorem synLb_le (hK : 1 ≤ K) : synLb es ℓ K ≤ synAc es ℓ K := by
  rw [synLb_eq es ℓ K hK]
  have hB : NW ^ synJp es ≠ 0 := (pow_pos NW_pos _).ne'
  exact (Nat.log_mono_right (NW_pow_synJp_le es ℓ K hK)).trans (by rw [Nat.log_pow (by norm_num)])

/-- `2^a' ≤ R₂`. -/
theorem synR2c_ge (hK : 1 ≤ K) : 2 ^ synAc es ℓ K ≤ synR2c es ℓ K := by
  unfold synR2c synX
  have hB : NW ^ synJp es ≠ 0 := (pow_pos NW_pos _).ne'
  have hL := synLb_le es ℓ K hK
  calc 2 ^ synAc es ℓ K = 2 ^ (synAc es ℓ K - synLb es ℓ K) * 2 ^ synLb es ℓ K := by
        rw [← pow_add, Nat.sub_add_cancel hL]
    _ ≤ 2 ^ (synAc es ℓ K - synLb es ℓ K) * NW ^ synJp es := by
        apply Nat.mul_le_mul_left
        rw [synLb_eq es ℓ K hK]
        exact Nat.pow_log_le_self 2 hB

/-- `R₂ < 2^(a' + 1)`: the padding at most doubles the rows. -/
theorem synR2c_lt (hK : 1 ≤ K) : synR2c es ℓ K < 2 * 2 ^ synAc es ℓ K := by
  unfold synR2c synX
  have hL := synLb_le es ℓ K hK
  calc 2 ^ (synAc es ℓ K - synLb es ℓ K) * NW ^ synJp es
      < 2 ^ (synAc es ℓ K - synLb es ℓ K) * 2 ^ (synLb es ℓ K + 1) := by
        apply Nat.mul_lt_mul_of_pos_left _ (pow_pos (by norm_num) _)
        rw [synLb_eq es ℓ K hK]
        exact Nat.lt_pow_succ_log_self (by norm_num) _
    _ = 2 * 2 ^ synAc es ℓ K := by
        rw [← pow_add, show synAc es ℓ K - synLb es ℓ K + (synLb es ℓ K + 1) =
          synAc es ℓ K + 1 by omega, pow_succ]
        ring

/-- The pieces' rows: `R₂ = rowsAt (2^X) J'`. -/
theorem synR2_chunk {h : ℕ} (hc : synChunk ℓ K h) :
    synR2 es ℓ K h = rowsAt (2 ^ synX es ℓ K) (synJ (synDpp es) (synDpp es) - 1) := by
  simp [synR2, hc, synR2c, synJp, rowsAt_eq, Nat.mul_comm]

end Rows

/-! ### The chunk branch -/

section ChunkBr

variable {Q A : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q A U)
  {R : Fin (nT SXReg) → List (Fin (A + 4))}

/-- The step bound of `synChunkA`. -/
def synChunkACost (hv bv Kv Dv : ℕ) : ℕ :=
  (4 * Kv + 4) + (4 * hv + 4) + (4 * bv + 4) + synDivModCost (hv - bv) Kv +
    (4 * ((hv - bv) % Kv) + 4) + (2 * ((hv - bv) % Kv) + 2) + (2 * (hv - bv) + 2) +
    synMulRCost ((hv - bv) / Kv) Dv + synMulRCost Kv ((hv - bv) / Kv * Dv) +
    (2 * ((hv - bv) / Kv * Dv) + 2) + (2 * ((hv - bv) / Kv) + 2)

theorem sg_synChunkA (v : SynW → List (Fin (A + 4))) (hv bv Kv Dv : ℕ) (hk : 1 ≤ Kv)
    (h2 : v (.s 2) = []) (h3 : v (.s 3) = []) (h4 : v (.s 4) = []) (h6 : v (.s 6) = [])
    (h8 : v (.s 8) = []) (h9 : v (.s 9) = []) (h10 : v (.s 10) = []) (h11 : v (.s 11) = [])
    (hkh : v (.p .kh) = []) (hrh : v (.p .rh) = [])
    (hh : (v (.p .h)).length = hv) (hb : (v (.p .b)).length = bv) (hK : (v (.p .K)).length = Kv)
    (hD : (v (.p .D)).length = Dv) :
    LayRuns body synChunkA (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.p .kh)
        (List.replicate Kv tick)) (.p .rh) (List.replicate ((hv - bv) % Kv) tick)) (.s 6)
        (List.replicate (Kv * ((hv - bv) / Kv * Dv)) tick)))
      (synChunkACost hv bv Kv Dv) := by
  refine lr_weaken body
    ((sgU_copy body (a := .p .K) (b := .p .kh) (t := .s 2) (x := Kv) (y := 0) (by decide)
      (by decide) (by decide) h2 hK (by simp [hkh])).seq <|
    (sgU_copy body (a := .p .h) (b := .s 9) (t := .s 2) (x := hv) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hh]) (by simp [h9])).seq <|
    (sgU_sub body (a := .p .b) (b := .s 9) (t := .s 2) (x := bv) (y := hv) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hb]) (by simp)).seq <|
    (sgU_divMod body (x := .s 9) (k := .p .K) (q := .s 10) (r := .s 11) (t₁ := .s 2)
      (t₂ := .s 3) (t₃ := .s 4) (X := hv - bv) (Kv := Kv) (z := 0) (by decide) hk
      (by simp [hK]) (by simp) (by simp [h11]) (by simp [h10]) (by simp [h2]) (by simp [h3])
      (by simp [h4])).seq <|
    (sgU_copy body (a := .s 11) (b := .p .rh) (t := .s 2) (x := (hv - bv) % Kv) (y := 0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [hrh])).seq <|
    (sgU_clear body (a := .s 11) (x := (hv - bv) % Kv) (by simp)).seq <|
    (sgU_clear body (a := .s 9) (x := hv - bv) (by simp)).seq <|
    (sgU_mulR body (a := .s 10) (b := .p .D) (c := .s 8) (t₁ := .s 2) (t₂ := .s 3)
      (x := (hv - bv) / Kv) (y := Dv) (z := 0) (by decide) (by simp [h2]) (by simp [h3])
      (by simp) (by simp [hD]) (by simp [h8])).seq <|
    (sgU_mulR body (a := .p .K) (b := .s 8) (c := .s 6) (t₁ := .s 2) (t₂ := .s 3) (x := Kv)
      (y := (hv - bv) / Kv * Dv) (z := 0) (by decide) (by simp [h2]) (by simp [h3])
      (by simp [hK]) (by simp) (by simp [h6])).seq <|
    (sgU_clear body (a := .s 8) (x := (hv - bv) / Kv * Dv) (by simp)).seq <|
    sgU_clear body (a := .s 10) (x := (hv - bv) / Kv) (by simp)) ?_ ?_
  · refine congrArg (synG R) ?_
    funext y
    simp only [Function.update_apply]
    split_ifs <;> (try simp_all) <;> omega
  · simp only [synChunkACost]
    omega

/-- The step bound of `synChunkQ`. -/
def synChunkQCost (oS Kv Dv : ℕ) : ℕ :=
  let Jn := synJ Dv Dv
  let J := Jn - 1
  let q := Dv - (Dv - synCW * J)
  (4 * Dv + 4) + synCntCost m Dv Dv + (4 * Jn + 4) + 1 + (4 * J + 4) + (4 * Dv + 4) +
    (4 * (synCW * J) + 4) + (4 * Dv + 4) + (4 * (Dv - synCW * J) + 4) + (4 * Dv + 4) +
    (4 * q + 4) + synMulRCost Kv q + (4 * (Kv * q) + 4) + synMulRCost Kv (Dv - q) +
    (4 * oS + 4) + (2 * Jn + 2) + (2 * J + 2) + (2 * (synCW * J) + 2) +
    (2 * (Dv - synCW * J) + 2)

theorem sg_synChunkQ (v : SynW → List (Fin (A + 4))) (a oS Kv Dv : ℕ)
    (ha : v (.s 0) = List.replicate a tick) (hoS : v (.s 6) = List.replicate oS tick)
    (hK : (v (.p .K)).length = Kv) (hD : (v (.p .D)).length = Dv)
    (h2 : v (.s 2) = []) (h3 : v (.s 3) = []) (h9 : v (.s 9) = []) (h10 : v (.s 10) = [])
    (h12 : v (.s 12) = []) (h14 : v (.s 14) = []) (h17 : v (.s 17) = []) (h22 : v (.s 22) = [])
    (h23 : v (.s 23) = []) (h25 : v (.s 25) = []) (h26 : v (.s 26) = []) (h27 : v (.s 27) = [])
    (h28 : v (.s 28) = []) :
    LayRuns body synChunkQ (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update
        (Function.update v (.s 0) (List.replicate (Kv * synQKn Dv (synJ Dv Dv - 1) + a) tick))
        (.s 25) (List.replicate (synQKn Dv (synJ Dv Dv - 1)) tick))
        (.s 26) (List.replicate (Dv - synQKn Dv (synJ Dv Dv - 1)) tick))
        (.s 27) (List.replicate (Kv * synQKn Dv (synJ Dv Dv - 1)) tick))
        (.s 28) (List.replicate (oS + Kv * (Dv - synQKn Dv (synJ Dv Dv - 1))) tick)))
      (synChunkQCost oS Kv Dv) := by
  set Jn := synJ Dv Dv with hJn
  set q := synQKn Dv (Jn - 1) with hq
  have hq' : q = Dv - (Dv - synCW * (Jn - 1)) := by rw [hq, synQKn]
  refine lr_weaken body
    ((sgU_copy body (a := .p .D) (b := .s 12) (t := .s 2) (x := Dv) (y := 0) (by decide)
      (by decide) (by decide) h2 hD (by simp [h12])).seq <|
    (sg_synCntLoop body m m_pos (x := .s 12) (cnt := .s 14) (ctr := .p .D) _ Dv Dv
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp) (by simp [h14]) (by simp [hD]) (by simp [h17]) (by simp [h2])
      (by simp [h23])).seq <|
    (sgU_copy body (a := .s 14) (b := .s 22) (t := .s 2) (x := Jn) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hJn, synJ]) (by simp [h22])).seq <|
    (sgU_pop body (a := .s 22) (y := Jn) (by simp)).seq <|
    (sgU_umul body synCW (a := .s 22) (b := .s 9) (t := .s 2) (x := Jn - 1) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp) (by simp [h9])).seq <|
    (sgU_copy body (a := .p .D) (b := .s 10) (t := .s 2) (x := Dv) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hD]) (by simp [h10])).seq <|
    (sgU_sub body (a := .s 9) (b := .s 10) (t := .s 2) (x := synCW * (Jn - 1)) (y := Dv)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp)).seq <|
    (sgU_copy body (a := .p .D) (b := .s 25) (t := .s 2) (x := Dv) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hD]) (by simp [h25])).seq <|
    (sgU_sub body (a := .s 10) (b := .s 25) (t := .s 2) (x := Dv - synCW * (Jn - 1)) (y := Dv)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp)).seq <|
    (sgU_copy body (a := .p .D) (b := .s 26) (t := .s 2) (x := Dv) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hD]) (by simp [h26])).seq <|
    (sgU_sub body (a := .s 25) (b := .s 26) (t := .s 2) (x := q) (y := Dv)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hq']) (by simp)).seq <|
    (sgU_mulR body (a := .p .K) (b := .s 25) (c := .s 27) (t₁ := .s 2) (t₂ := .s 3) (x := Kv)
      (y := q) (z := 0) (by decide) (by simp [h2]) (by simp [h3]) (by simp [hK])
      (by simp [hq']) (by simp [h27])).seq <|
    (sgU_copy body (a := .s 27) (b := .s 0) (t := .s 2) (x := Kv * q) (y := a) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp) (by simp [ha])).seq <|
    (sgU_mulR body (a := .p .K) (b := .s 26) (c := .s 28) (t₁ := .s 2) (t₂ := .s 3) (x := Kv)
      (y := Dv - q) (z := 0) (by decide) (by simp [h2]) (by simp [h3]) (by simp [hK])
      (by simp [hq']) (by simp [h28])).seq <|
    (sgU_copy body (a := .s 6) (b := .s 28) (t := .s 2) (x := oS) (y := Kv * (Dv - q))
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hoS]) (by simp)).seq <|
    (sgU_clear body (a := .s 14) (x := Jn) (by simp [hJn, synJ])).seq <|
    (sgU_clear body (a := .s 22) (x := Jn - 1) (by simp)).seq <|
    (sgU_clear body (a := .s 9) (x := synCW * (Jn - 1)) (by simp)).seq <|
    sgU_clear body (a := .s 10) (x := Dv - synCW * (Jn - 1)) (by simp)) ?_ ?_
  · refine congrArg (synG R) ?_
    funext y
    simp only [Function.update_apply]
    split_ifs <;> (try simp_all [div_pow_self]) <;> omega
  · simp only [synChunkQCost, ← hJn, ← hq']
    omega

/-- The step bound of `synChunkR2`. -/
noncomputable def synChunkR2Cost (a' Jn : ℕ) : ℕ :=
  let J := Jn - 1
  let B := NW ^ J
  let L := synJk 2 B (a' + 1) - 1
  let X := a' - L
  1 + (4 * Jn + 4) + 1 + ((∑ j ∈ Finset.range J, (8 * (NW ^ j * 1) + 8 + 3)) + 2 * J + 4) +
    (2 * J + 2) + (4 * B + 4) + (4 * a' + 4) + 1 + synCntCost 2 B (a' + 1) +
    (2 * (a' + 1) + 2) + (2 * (B / 2 ^ (a' + 1)) + 2) + 1 + (4 * a' + 4) + (4 * L + 4) +
    (4 * (2 ^ X * B) + 9 * X + 4) + (2 * X + 2) + (2 * L + 2)

theorem sg_synChunkR2 (v : SynW → List (Fin (A + 4))) (a' Jn : ℕ)
    (ha : v (.s 0) = List.replicate a' tick) (hJ : v (.s 14) = List.replicate Jn tick)
    (h2 : v (.s 2) = []) (h3 : v (.s 3) = []) (h7 : v (.s 7) = []) (h8 : v (.s 8) = [])
    (h17 : v (.s 17) = []) (h22 : v (.s 22) = []) (h23 : v (.s 23) = []) (h29 : v (.s 29) = [])
    (h30 : v (.s 30) = []) (h31 : v (.s 31) = []) :
    LayRuns body synChunkR2 (synG R v)
      (synG R (Function.update v (.s 7) (List.replicate
        (2 ^ (a' - (synJk 2 (NW ^ (Jn - 1)) (a' + 1) - 1)) * NW ^ (Jn - 1)) tick)))
      (synChunkR2Cost a' Jn) := by
  set B := NW ^ (Jn - 1) with hB
  set L := synJk 2 B (a' + 1) - 1 with hL
  refine lr_weaken body
    ((sgU_push body (a := .s 7) (y := 0) (by simp [h7])).seq <|
    (sgU_copy body (a := .s 14) (b := .s 22) (t := .s 2) (x := Jn) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hJ]) (by simp [h22])).seq <|
    (sgU_pop body (a := .s 22) (y := Jn) (by simp)).seq <|
    (sg_synNWLoop body _ (Jn - 1) 1 (by simp) (by simp [h23]) (by simp) (by simp [h2])
      (by simp [h3])).seq <|
    (sgU_clear body (a := .s 22) (x := Jn - 1) (by simp)).seq <|
    (sgU_copy body (a := .s 7) (b := .s 29) (t := .s 2) (x := B) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hB]) (by simp [h29])).seq <|
    (sgU_copy body (a := .s 0) (b := .s 31) (t := .s 2) (x := a') (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [ha]) (by simp [h31])).seq <|
    (sgU_push body (a := .s 31) (y := a') (by simp)).seq <|
    (sg_synCntLoop body 2 (by norm_num) (x := .s 29) (cnt := .s 30) (ctr := .s 31) _ B (a' + 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by simp) (by simp [h30]) (by simp) (by simp [h17]) (by simp [h2])
      (by simp [h23])).seq <|
    (sgU_clear body (a := .s 31) (x := a' + 1) (by simp)).seq <|
    (sgU_clear body (a := .s 29) (x := B / 2 ^ (a' + 1)) (by simp)).seq <|
    (sgU_pop body (a := .s 30) (y := synJk 2 B (a' + 1)) (by simp)).seq <|
    (sgU_copy body (a := .s 0) (b := .s 8) (t := .s 2) (x := a') (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [ha]) (by simp [h8])).seq <|
    (sgU_sub body (a := .s 30) (b := .s 8) (t := .s 2) (x := L) (y := a') (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hL]) (by simp)).seq <|
    (sgU_pow2 body (a := .s 8) (b := .s 7) (t₁ := .s 2) (t₂ := .s 3) (x := a' - L) (y := B)
      (by decide) (by simp [h2]) (by simp [h3]) (by simp) (by simp [hB])).seq <|
    (sgU_clear body (a := .s 8) (x := a' - L) (by simp)).seq <|
    sgU_clear body (a := .s 30) (x := L) (by simp [hL])) ?_ ?_
  · refine congrArg (synG R) ?_
    funext y
    simp only [Function.update_apply]
    split_ifs <;> (try simp_all) <;> omega
  · simp only [synChunkR2Cost, ← hB, ← hL]
    omega

/-- The step bound of `synChunkCfg`. -/
def synChunkCfgCost (W a' Dv q E R2 aT Kq oS : ℕ) : ℕ :=
  (4 * Dv + 4 + (1 + (4 * (Dv + 1) + 4 + (2 * (Dv + 1) + 2 + (4 * q + 4))))) +
    (4 * ((Dv + 1) / 2 + q) + 4) +
    (4 * W + 5) + (4 * ((Dv + 1) / 2 + q + E) + 5) + (4 * a' + 5) + 2 + (4 * R2 + 5) +
    (4 * q + 5) + (4 * aT + 5) + (4 * Kq + 5) + (4 * oS + 5) + (4 * Dv + 5)

theorem sg_synChunkCfg (v : SynW → List (Fin (A + 4))) (W a' Dv q E R2 aT Kq oS : ℕ)
    (ha : v (.s 0) = List.replicate a' tick) (hE : v (.s 16) = List.replicate E tick)
    (hR : v (.s 7) = List.replicate R2 tick) (hoS : v (.s 6) = List.replicate oS tick)
    (hq : v (.s 25) = List.replicate q tick) (haT : v (.s 28) = List.replicate aT tick)
    (hKq : v (.s 27) = List.replicate Kq tick)
    (h1 : v (.s 1) = []) (h2 : v (.s 2) = []) (h5 : v (.s 5) = []) (hcf : v (.p .cf) = [])
    (hW : (v (.p .w)).length = W) (hD : (v (.p .D)).length = Dv) :
    LayRuns body synChunkCfg (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.s 5)
        (List.replicate ((Dv + 1) / 2 + q) tick)) (.s 16)
        (List.replicate ((Dv + 1) / 2 + q + E) tick)) (.p .cf)
        (topRec [W, (Dv + 1) / 2 + q + E, a', 1, R2, q, aT, Kq, oS, Dv]).reverse))
      (synChunkCfgCost W a' Dv q E R2 aT Kq oS) := by
  refine lr_weaken body
    ((sg_synHalfAdd body (x := .p .D) (y := .s 25) (by decide) (by decide) (by decide)
      (by decide) (by decide) _ Dv q hD (by simp [hq]) h1 h2 h5).seq <|
    (sgU_copy body (a := .s 5) (b := .s 16) (t := .s 2) (x := (Dv + 1) / 2 + q) (y := E)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [hE])).seq <|
    (sg_synCF body (x := .p .w) (by decide) (by decide) _ [] W (by simp [h2]) (by simp [hW])
      (by simp [hcf])).seq <|
    (sg_synCF body (x := .s 16) (by decide) (by decide) _ [W] ((Dv + 1) / 2 + q + E)
      (by simp [h2]) (by simp) (by simp)).seq <|
    (sg_synCF body (x := .s 0) (by decide) (by decide) _ [W, (Dv + 1) / 2 + q + E] a'
      (by simp [h2]) (by simp [ha]) (by simp)).seq <|
    (sg_synCF1 body _ [W, (Dv + 1) / 2 + q + E, a'] (by simp)).seq <|
    (sg_synCF body (x := .s 7) (by decide) (by decide) _ [W, (Dv + 1) / 2 + q + E, a', 1] R2
      (by simp [h2]) (by simp [hR]) (by simp)).seq <|
    (sg_synCF body (x := .s 25) (by decide) (by decide) _ [W, (Dv + 1) / 2 + q + E, a', 1, R2]
      q (by simp [h2]) (by simp [hq]) (by simp)).seq <|
    (sg_synCF body (x := .s 28) (by decide) (by decide) _
      [W, (Dv + 1) / 2 + q + E, a', 1, R2, q] aT (by simp [h2]) (by simp [haT]) (by simp)).seq <|
    (sg_synCF body (x := .s 27) (by decide) (by decide) _
      [W, (Dv + 1) / 2 + q + E, a', 1, R2, q, aT] Kq (by simp [h2]) (by simp [hKq])
      (by simp)).seq <|
    (sg_synCF body (x := .s 6) (by decide) (by decide) _
      [W, (Dv + 1) / 2 + q + E, a', 1, R2, q, aT, Kq] oS (by simp [h2]) (by simp [hoS])
      (by simp)).seq <|
    sg_synCF body (x := .p .D) (by decide) (by decide) _
      [W, (Dv + 1) / 2 + q + E, a', 1, R2, q, aT, Kq, oS] Dv (by simp [h2]) (by simp [hD])
      (by simp)) ?_ ?_
  · refine congrArg (synG R) ?_
    funext y
    simp only [Function.update_apply]
    split_ifs <;> (try simp_all) <;> omega
  · simp only [synChunkCfgCost]
    omega

/-- The step bound of `synChunkEnd`. -/
def synChunkEndCost (W S Dv S5 oS R2 Jn q Dp Kq aT a' : ℕ) : ℕ :=
  (4 * W + 4 + (4 * S + 4 + (4 * Dv + 4))) + (2 * S5 + 2) + (2 * oS + 2) + (2 * R2 + 2) +
    (2 * Jn + 2) + (2 * S + 2) + (2 * q + 2) + (2 * Dp + 2) + (2 * Kq + 2) + (2 * aT + 2) +
    (2 * a' + 2)

theorem sg_synChunkEnd (v : SynW → List (Fin (A + 4))) (W S Dv S5 oS R2 Jn q Dp Kq aT a' : ℕ)
    (h5 : v (.s 5) = List.replicate S5 tick) (h6 : v (.s 6) = List.replicate oS tick)
    (h7 : v (.s 7) = List.replicate R2 tick) (h14 : v (.s 14) = List.replicate Jn tick)
    (h16 : v (.s 16) = List.replicate S tick) (h25 : v (.s 25) = List.replicate q tick)
    (h26 : v (.s 26) = List.replicate Dp tick) (h27 : v (.s 27) = List.replicate Kq tick)
    (h28 : v (.s 28) = List.replicate aT tick) (h0 : v (.s 0) = List.replicate a' tick)
    (h2 : v (.s 2) = []) (hw2 : v (.p .w2) = [])
    (hW : (v (.p .w)).length = W) (hD : (v (.p .D)).length = Dv) :
    LayRuns body synChunkEnd (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update v (.p .w2)
          (List.replicate (W + S + Dv) tick)) (.s 5) []) (.s 6) []) (.s 7) []) (.s 14) [])
          (.s 16) []) (.s 25) []) (.s 26) []) (.s 27) []) (.s 28) []) (.s 0) []))
      (synChunkEndCost W S Dv S5 oS R2 Jn q Dp Kq aT a') := by
  refine lr_weaken body
    ((sg_synW2P body (x := .s 16) (by decide) (by decide) _ W S Dv h2 hw2 hW (by simp [h16])
      hD).seq <|
    (sgU_clear body (a := .s 5) (x := S5) (by simp [h5])).seq <|
    (sgU_clear body (a := .s 6) (x := oS) (by simp [h6])).seq <|
    (sgU_clear body (a := .s 7) (x := R2) (by simp [h7])).seq <|
    (sgU_clear body (a := .s 14) (x := Jn) (by simp [h14])).seq <|
    (sgU_clear body (a := .s 16) (x := S) (by simp [h16])).seq <|
    (sgU_clear body (a := .s 25) (x := q) (by simp [h25])).seq <|
    (sgU_clear body (a := .s 26) (x := Dp) (by simp [h26])).seq <|
    (sgU_clear body (a := .s 27) (x := Kq) (by simp [h27])).seq <|
    (sgU_clear body (a := .s 28) (x := aT) (by simp [h28])).seq <|
    sgU_clear body (a := .s 0) (x := a') (by simp [h0])) rfl ?_
  simp only [synChunkEndCost]
  omega

/-- The step bound of `synChunkB`. -/
noncomputable def synChunkCost (G F a hv bv Kv Dv W : ℕ) : ℕ :=
  let oS := Kv * ((hv - bv) / Kv * Dv)
  let q := synQKn Dv (synJ Dv Dv - 1)
  let Dp := Dv - q
  let a' := Kv * q + a
  let E := synE G F Dp Dp
  let Jn := synJ Dp Dp
  let R2 := 2 ^ (a' - (synJk 2 (NW ^ (Jn - 1)) (a' + 1) - 1)) * NW ^ (Jn - 1)
  synChunkACost hv bv Kv Dv + (synChunkQCost oS Kv Dv + (synDigitsCost G F Kv oS Dp +
    (synChunkR2Cost a' Jn + (synChunkCfgCost W a' Dv q E R2 (oS + Kv * Dp) (Kv * q) oS +
      synChunkEndCost W ((Dv + 1) / 2 + q + E) Dv ((Dv + 1) / 2 + q) oS R2 Jn q Dp (Kv * q)
        (oS + Kv * Dp) a'))))

theorem sg_synChunkB (G F : ℕ) (v : SynW → List (Fin (A + 4))) (a hv bv Kv Dv W Xp Jp : ℕ)
    (hk : 1 ≤ Kv) (hs : ∀ i, i ≠ 0 → v (.s i) = []) (ha : v (.s 0) = List.replicate a tick)
    (hcf : v (.p .cf) = []) (hkh : v (.p .kh) = []) (hrh : v (.p .rh) = [])
    (hpr : v (.p .pr) = []) (hw2 : v (.p .w2) = [])
    (hh : (v (.p .h)).length = hv) (hb : (v (.p .b)).length = bv) (hK : (v (.p .K)).length = Kv)
    (hD : (v (.p .D)).length = Dv) (hW : (v (.p .w)).length = W) :
    LayRuns body (synChunkB G F) (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update v (.s 0) []) (.p .kh) (List.replicate Kv tick))
          (.p .rh) (List.replicate ((hv - bv) % Kv) tick)) (.p .pr)
          (topRec (topPcRec Kv (synPcs Kv Xp (Dv - synQKn Dv (synJ Dv Dv - 1))
            (Kv * ((hv - bv) / Kv * Dv)) Jp (Dv - synQKn Dv (synJ Dv Dv - 1))))))
        (.p .cf) (topRec [W,
          (Dv + 1) / 2 + synQKn Dv (synJ Dv Dv - 1) +
            synE G F (Dv - synQKn Dv (synJ Dv Dv - 1)) (Dv - synQKn Dv (synJ Dv Dv - 1)),
          Kv * synQKn Dv (synJ Dv Dv - 1) + a, 1,
          2 ^ (Kv * synQKn Dv (synJ Dv Dv - 1) + a -
            (synJk 2 (NW ^ (synJ (Dv - synQKn Dv (synJ Dv Dv - 1))
              (Dv - synQKn Dv (synJ Dv Dv - 1)) - 1))
              (Kv * synQKn Dv (synJ Dv Dv - 1) + a + 1) - 1)) *
            NW ^ (synJ (Dv - synQKn Dv (synJ Dv Dv - 1)) (Dv - synQKn Dv (synJ Dv Dv - 1)) - 1),
          synQKn Dv (synJ Dv Dv - 1),
          Kv * ((hv - bv) / Kv * Dv) + Kv * (Dv - synQKn Dv (synJ Dv Dv - 1)),
          Kv * synQKn Dv (synJ Dv Dv - 1), Kv * ((hv - bv) / Kv * Dv), Dv]).reverse)
        (.p .w2) (List.replicate (W + ((Dv + 1) / 2 + synQKn Dv (synJ Dv Dv - 1) +
          synE G F (Dv - synQKn Dv (synJ Dv Dv - 1)) (Dv - synQKn Dv (synJ Dv Dv - 1))) + Dv)
          tick)))
      (synChunkCost G F a hv bv Kv Dv W) := by
  have hz : ∀ i : Fin 32, i ≠ 0 → v (.s i) = [] := hs
  set oS := Kv * ((hv - bv) / Kv * Dv) with hoS
  set q := synQKn Dv (synJ Dv Dv - 1) with hq
  set Dp := Dv - q with hDp
  set a' := Kv * q + a with ha'
  set E := synE G F Dp Dp with hE
  set Jn := synJ Dp Dp with hJn
  set R2 := 2 ^ (a' - (synJk 2 (NW ^ (Jn - 1)) (a' + 1) - 1)) * NW ^ (Jn - 1) with hR2
  have sA := sg_synChunkA body (R := R) v hv bv Kv Dv hk (hz 2 (by decide)) (hz 3 (by decide))
    (hz 4 (by decide)) (hz 6 (by decide)) (hz 8 (by decide)) (hz 9 (by decide))
    (hz 10 (by decide)) (hz 11 (by decide)) hkh hrh hh hb hK hD
  set vA := Function.update (Function.update (Function.update v (.p .kh)
    (List.replicate Kv tick)) (.p .rh) (List.replicate ((hv - bv) % Kv) tick)) (.s 6)
    (List.replicate oS tick) with hvA
  have sQ := sg_synChunkQ body (R := R) vA a oS Kv Dv (by simp [hvA, ha]) (by simp [hvA])
    (by simp [hvA, hK]) (by simp [hvA, hD]) (by simp [hvA, hz 2 (by decide)])
    (by simp [hvA, hz 3 (by decide)]) (by simp [hvA, hz 9 (by decide)])
    (by simp [hvA, hz 10 (by decide)]) (by simp [hvA, hz 12 (by decide)])
    (by simp [hvA, hz 14 (by decide)]) (by simp [hvA, hz 17 (by decide)])
    (by simp [hvA, hz 22 (by decide)]) (by simp [hvA, hz 23 (by decide)])
    (by simp [hvA, hz 25 (by decide)]) (by simp [hvA, hz 26 (by decide)])
    (by simp [hvA, hz 27 (by decide)]) (by simp [hvA, hz 28 (by decide)])
  set vQ := Function.update (Function.update (Function.update (Function.update
    (Function.update vA (.s 0) (List.replicate a' tick)) (.s 25) (List.replicate q tick))
    (.s 26) (List.replicate Dp tick)) (.s 27) (List.replicate (Kv * q) tick))
    (.s 28) (List.replicate (oS + Kv * Dp) tick) with hvQ
  have sD := sg_synDigits body (R := R) G F vQ Kv Xp oS Jp Dp (by simp [hvQ, hvA])
    (by simp [hvQ, hvA, hK]) (by simp [hvQ]) (by simp [hvQ, hvA, hpr]) (fun i hi1 hi2 => by
      have hi0 : i ≠ 0 := by intro h; subst h; simp at hi1
      have hi6 : i ≠ 6 := by intro h; subst h; simp at hi1
      have hi25 : i ≠ 25 := by intro h; subst h; simp at hi2
      have hi26 : i ≠ 26 := by intro h; subst h; simp at hi2
      have hi27 : i ≠ 27 := by intro h; subst h; simp at hi2
      have hi28 : i ≠ 28 := by intro h; subst h; simp at hi2
      simp [hvQ, hvA, hi0, hi6, hi25, hi26, hi27, hi28, hz i hi0])
    (by simp [hvQ, hvA, hz 2 (by decide)]) (by simp [hvQ, hvA, hz 3 (by decide)])
    (by simp [hvQ, hvA, hz 4 (by decide)])
  set vD := Function.update (Function.update (Function.update vQ (.s 14)
    (List.replicate Jn tick)) (.s 16) (List.replicate E tick)) (.p .pr)
    (topRec (topPcRec Kv (synPcs Kv Xp Dp oS Jp Dp))) with hvD
  have sR := sg_synChunkR2 body (R := R) vD a' Jn (by simp [hvD, hvQ]) (by simp [hvD])
    (by simp [hvD, hvQ, hvA, hz 2 (by decide)]) (by simp [hvD, hvQ, hvA, hz 3 (by decide)])
    (by simp [hvD, hvQ, hvA, hz 7 (by decide)]) (by simp [hvD, hvQ, hvA, hz 8 (by decide)])
    (by simp [hvD, hvQ, hvA, hz 17 (by decide)]) (by simp [hvD, hvQ, hvA, hz 22 (by decide)])
    (by simp [hvD, hvQ, hvA, hz 23 (by decide)]) (by simp [hvD, hvQ, hvA, hz 29 (by decide)])
    (by simp [hvD, hvQ, hvA, hz 30 (by decide)]) (by simp [hvD, hvQ, hvA, hz 31 (by decide)])
  set vR := Function.update vD (.s 7) (List.replicate R2 tick) with hvR
  have sC := sg_synChunkCfg body (R := R) vR W a' Dv q E R2 (oS + Kv * Dp) (Kv * q) oS
    (by simp [hvR, hvD, hvQ]) (by simp [hvR, hvD]) (by simp [hvR])
    (by simp [hvR, hvD, hvQ, hvA]) (by simp [hvR, hvD, hvQ]) (by simp [hvR, hvD, hvQ])
    (by simp [hvR, hvD, hvQ]) (by simp [hvR, hvD, hvQ, hvA, hz 1 (by decide)])
    (by simp [hvR, hvD, hvQ, hvA, hz 2 (by decide)])
    (by simp [hvR, hvD, hvQ, hvA, hz 5 (by decide)]) (by simp [hvR, hvD, hvQ, hvA, hcf])
    (by simp [hvR, hvD, hvQ, hvA, hW]) (by simp [hvR, hvD, hvQ, hvA, hD])
  set S := (Dv + 1) / 2 + q + E with hS
  set vC := Function.update (Function.update (Function.update vR (.s 5)
    (List.replicate ((Dv + 1) / 2 + q) tick)) (.s 16) (List.replicate S tick)) (.p .cf)
    (topRec [W, S, a', 1, R2, q, oS + Kv * Dp, Kv * q, oS, Dv]).reverse with hvC
  have sE := sg_synChunkEnd body (R := R) vC W S Dv ((Dv + 1) / 2 + q) oS R2 Jn q Dp (Kv * q)
    (oS + Kv * Dp) a'
    (by simp [hvC]) (by simp [hvC, hvR, hvD, hvQ, hvA]) (by simp [hvC, hvR])
    (by simp [hvC, hvR, hvD]) (by simp [hvC]) (by simp [hvC, hvR, hvD, hvQ])
    (by simp [hvC, hvR, hvD, hvQ]) (by simp [hvC, hvR, hvD, hvQ])
    (by simp [hvC, hvR, hvD, hvQ]) (by simp [hvC, hvR, hvD, hvQ])
    (by simp [hvC, hvR, hvD, hvQ, hvA, hz 2 (by decide)])
    (by simp [hvC, hvR, hvD, hvQ, hvA, hw2]) (by simp [hvC, hvR, hvD, hvQ, hvA, hW])
    (by simp [hvC, hvR, hvD, hvQ, hvA, hD])
  refine lr_weaken body (sA.seq (sQ.seq (sD.seq (sR.seq (sC.seq sE))))) ?_ le_rfl
  refine congrArg (synG R) ?_
  clear sA sQ sD sR sC sE
  clear_value oS q Dp a' E Jn R2 S
  clear hoS hq hDp ha' hE hJn hR2 hS
  funext y
  simp only [hvC, hvR, hvD, hvQ, hvA]
  clear hvC hvR hvD hvQ hvA
  clear_value vC vR vD vQ vA
  clear vC vR vD vQ vA
  rcases y with x | i | x | i
  · cases x <;> simp
  · fin_cases i <;> simp
  · cases x <;> simp
  · fin_cases i <;> simp [hz]

end ChunkBr

/-! ### The record builder -/

section Rec

variable {Q A : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q A U)
  {R : Fin (nT SXReg) → List (Fin (A + 4))}

/-- The wire file after `synRec`: the outputs of round `h`. -/
noncomputable def synRecOut (G F : ℕ) (es : List ℕ) (ℓ K w h : ℕ)
    (v : SynW → List (Fin (A + 4))) : SynW → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update v (.p .kh)
    (List.replicate (synKh ℓ K h) tick)) (.p .rh) (List.replicate (synRh ℓ K h) tick)) (.p .pr)
    (topRec (topPcRec (synKh ℓ K h) (synPcsR es ℓ K h)))) (.p .cf)
    (topRec (synCfg es ℓ K G F w h)).reverse) (.p .w2)
    (List.replicate (synW2 es ℓ K G F w h) tick)

/-- The step bound of `synRec`. -/
noncomputable def synRecCost (G F : ℕ) (es : List ℕ) (ℓ K w h : ℕ) : ℕ :=
  let D := es.length
  let b := layB ℓ K
  let Lg := synLg es ℓ
  let a := synA es ℓ K
  synMulRCost b D + (4 * Lg + 4) + (4 * ℓ + 4) + (4 * h + 4) + 1 + 2 +
    (2 * (ℓ - h - 1) + 2) +
    (if h + 1 < ℓ then
      (4 * b + 4) + (4 * h + 4) + 2 +
        (if h < b then
          4 * es.sum + 4 + (4 * Lg + 4 + (synMulRCost (b - h) D + (4 * ((b - h) * D) + 4 +
            (2 * ((b - h) * D) + 2 + (2 * (b - h) + 2 +
              synPreBrCost w a D (es.sum - Lg - (b - h) * D) D)))))
        else 2 * (b - h) + 2 + synChunkCost G F a h b K D w)
    else 4 * es.sum + 4 + (4 * Lg + 4 + synPreBrCost w a Lg (es.sum - Lg) D))

/-- **The record builder of round `h`.** From unary `h, K ≥ 1, ℓ, b = (ℓ - 1) mod K, D = |es|,
Lg, N = Σ es, w` on the parameter wires, empty outputs and empty scratch, `synRec G F` writes
the configuration record `synCfg` (reversed) on `p .cf`, the piece record
`topPcRec K_h (synPcsR es ℓ K h)` on `p .pr`, `K_h`, `ρ_h` and `w'` on `p .kh`, `p .rh`,
`p .w2`, and restores the scratch, within `synRecCost` steps. -/
theorem sg_synRec (G F : ℕ) (es : List ℕ) (ℓ K w h : ℕ) (hK1 : 1 ≤ K)
    (v : SynW → List (Fin (A + 4))) (hs : ∀ i, v (.s i) = [])
    (hcf : v (.p .cf) = []) (hkh : v (.p .kh) = []) (hrh : v (.p .rh) = [])
    (hpr : v (.p .pr) = []) (hw2 : v (.p .w2) = [])
    (hh : (v (.p .h)).length = h) (hKv : (v (.p .K)).length = K)
    (hℓ : (v (.p .ℓ)).length = ℓ) (hb : (v (.p .b)).length = layB ℓ K)
    (hD : (v (.p .D)).length = es.length) (hLg : (v (.p .Lg)).length = synLg es ℓ)
    (hN : (v (.p .N)).length = es.sum) (hW : (v (.p .w)).length = w) :
    LayRuns body (synRec G F) (synG R v) (synG R (synRecOut G F es ℓ K w h v))
      (synRecCost G F es ℓ K w h) := by
  have hz : ∀ i : Fin 32, v (.s i) = [] := hs
  set a := synA es ℓ K with ha
  -- the prelude
  have sP : LayRuns body (synPreA (Q := Q) (U := U) (P := P)) (synG R v)
      (synG R (Function.update v (.s 0) (List.replicate a tick)))
      (synMulRCost (layB ℓ K) es.length + (4 * synLg es ℓ + 4)) := by
    refine lr_weaken body
      ((sgU_mulR body (a := .p .b) (b := .p .D) (c := .s 0) (t₁ := .s 2) (t₂ := .s 3)
        (x := layB ℓ K) (y := es.length) (z := 0) (by decide) (hz 2) (hz 3) hb hD
        (by simp [hz 0])).seq <|
      sgU_copy body (a := .p .Lg) (b := .s 0) (t := .s 2) (x := synLg es ℓ)
        (y := layB ℓ K * es.length + 0) (by decide) (by decide) (by decide) (by simp [hz 2])
        (by simp [hLg]) (by simp)) ?_ le_rfl
    simp [ha, synA]
  set v₀ := Function.update v (.s 0) (List.replicate a tick) with hv₀
  have sT := (sgU_copy body (R := R) (v := v₀) (a := .p .ℓ) (b := .s 1) (t := .s 2) (x := ℓ)
    (y := 0) (by decide) (by decide) (by decide) (by simp [hv₀, hz 2]) (by simp [hv₀, hℓ])
    (by simp [hv₀, hz 1])).seq <|
    (sgU_sub body (a := .p .h) (b := .s 1) (t := .s 2) (x := h) (y := ℓ) (by decide)
      (by decide) (by decide) (by simp [hv₀, hz 2]) (by simp [hv₀, hh]) (by simp)).seq <|
    sgU_pop body (a := .s 1) (y := ℓ - h) (by simp)
  set v₁ := Function.update (Function.update (Function.update v₀ (.s 1)
    (List.replicate (ℓ + 0) tick)) (.s 1) (List.replicate (ℓ - h) tick)) (.s 1)
    (List.replicate (ℓ - h - 1) tick) with hv₁
  have e1 : v₁ (.s 1) = List.replicate (ℓ - h - 1) tick := by simp [hv₁]
  have hzero : ∀ i : Fin 32, i ≠ 0 → i ≠ 1 → v₁ (.s i) = [] := by
    intro i h0 h1; simp [hv₁, hv₀, h0, h1, hz i]
  by_cases htop : h + 1 < ℓ
  · have hne : v₁ (.s 1) ≠ [] := by rw [e1]; simp; omega
    have hnc : ¬ (synChunk ℓ K h) ∨ synChunk ℓ K h := by tauto
    -- not the top round
    set v₂ := Function.update v₁ (.s 1) [] with hv₂
    have sB := (sgU_clear body (R := R) (v := v₁) (a := .s 1) (x := ℓ - h - 1) (by simp [e1])).seq <|
      (sgU_copy body (a := .p .b) (b := .s 1) (t := .s 2) (x := layB ℓ K) (y := 0) (by decide)
        (by decide) (by decide) (by simp [hv₁, hv₀, hz 2]) (by simp [hv₁, hv₀, hb])
        (by simp)).seq <|
      sgU_sub body (a := .p .h) (b := .s 1) (t := .s 2) (x := h) (y := layB ℓ K + 0) (by decide)
        (by decide) (by decide) (by simp [hv₁, hv₀, hz 2]) (by simp [hv₁, hv₀, hh]) (by simp)
    set v₃ := Function.update (Function.update (Function.update v₁ (.s 1) []) (.s 1)
      (List.replicate (layB ℓ K + 0) tick)) (.s 1) (List.replicate (layB ℓ K + 0 - h) tick)
      with hv₃
    have e3 : v₃ (.s 1) = List.replicate (layB ℓ K - h) tick := by simp [hv₃]
    by_cases hlow : h < layB ℓ K
    · have hne3 : v₃ (.s 1) ≠ [] := by rw [e3]; simp; omega
      have sL := sg_synLowB body (R := R) v₃ a es.sum (synLg es ℓ) w es.length (layB ℓ K - h)
        (fun i h0 h1 => by simp [hv₃, hv₁, hv₀, h0, h1, hz i]) (by simp [hv₃, hv₁, hv₀]) e3
        (by simp [hv₃, hv₁, hv₀, hcf]) (by simp [hv₃, hv₁, hv₀, hkh])
        (by simp [hv₃, hv₁, hv₀, hw2]) (by simp [hv₃, hv₁, hv₀, hN])
        (by simp [hv₃, hv₁, hv₀, hLg]) (by simp [hv₃, hv₁, hv₀, hW]) (by simp [hv₃, hv₁, hv₀, hD])
      have sIf := sg_ifNE_pos body (q := .seq (uclear (sreg (.s 1))) (synChunkB G F)) hne3 sL
      have sIf0 := sg_ifNE_pos body (q := .seq (uclear (sreg (.s 1))) synTopB) hne (sB.seq sIf)
      refine lr_weaken body (sP.seq (sT.seq sIf0)) ?_ ?_
      · have hc : ¬ synChunk ℓ K h := by unfold synChunk; omega
        refine congrArg (synG R) ?_
        funext y
        simp only [synRecOut, synKh, synRh, synPcsR, synCfg, topCfg, synS, synDp, synQ, synOS,
          synAT, synER, synR2, synW2, synAR, hc, ite_false, htop, hlow, ite_true, hv₃, hv₁, hv₀,
          Function.update_apply, topPcRec, List.flatMap_nil, topRec_nil]
        split_ifs <;> simp_all [synA]
      · simp only [synRecCost, htop, hlow, ite_true, ← ha]
        omega
    · have hc : synChunk ℓ K h := ⟨htop, by omega⟩
      have he3 : v₃ (.s 1) = [] := by rw [e3]; simp; omega
      set v₄ := Function.update v₃ (.s 1) [] with hv₄
      have sC := sg_synChunkB body (R := R) G F v₄ a h (layB ℓ K) K es.length w (synX es ℓ K)
        (synJp es) hK1
        (fun i h0 => by
          by_cases h1 : i = 1
          · subst h1; simp [hv₄]
          simp [hv₄, hv₃, hv₁, hv₀, h0, h1, hz i]) (by simp [hv₄, hv₃, hv₁, hv₀])
        (by simp [hv₄, hv₃, hv₁, hv₀, hcf]) (by simp [hv₄, hv₃, hv₁, hv₀, hkh])
        (by simp [hv₄, hv₃, hv₁, hv₀, hrh]) (by simp [hv₄, hv₃, hv₁, hv₀, hpr])
        (by simp [hv₄, hv₃, hv₁, hv₀, hw2]) (by simp [hv₄, hv₃, hv₁, hv₀, hh])
        (by simp [hv₄, hv₃, hv₁, hv₀, hb]) (by simp [hv₄, hv₃, hv₁, hv₀, hKv])
        (by simp [hv₄, hv₃, hv₁, hv₀, hD]) (by simp [hv₄, hv₃, hv₁, hv₀, hW])
      have sIf := sg_ifNE_neg body (p := synLowB) he3
        ((sgU_clear body (a := .s 1) (x := 0) (by simp [he3])).seq sC)
      have sIf0 := sg_ifNE_pos body (q := .seq (uclear (sreg (.s 1))) synTopB) hne (sB.seq sIf)
      refine lr_weaken body (sP.seq (sT.seq sIf0)) ?_ ?_
      · refine congrArg (synG R) ?_
        funext y
        simp only [synRecOut, synKh, synRh, synPcsR, synCfg, topCfg, synS, synDp, synQ, synOS,
          synAT, synER, synR2, synW2, synAR, synR2c, synX, synLb, synAc, synJp, synDpp, synQK,
          synJt, hc, htop, hlow, ite_false, ite_true, hv₄, hv₃, hv₁, hv₀, Function.update_apply]
        split_ifs <;> simp_all [synA]
      · simp only [synRecCost, htop, hlow, ite_true, ite_false, ← ha]
        have : layB ℓ K - h = 0 := by omega
        simp only [this]
        omega
  · have he : v₁ (.s 1) = [] := by rw [e1]; simp; omega
    have hc : ¬ synChunk ℓ K h := by unfold synChunk; omega
    have sTop := sg_synTopB body (R := R) (Function.update v₁ (.s 1) []) a es.sum (synLg es ℓ) w
      es.length (fun i h0 => by
        by_cases h1 : i = 1
        · subst h1; simp
        simp [hv₁, hv₀, h0, h1, hz i]) (by simp [hv₁, hv₀])
      (by simp [hv₁, hv₀, hcf]) (by simp [hv₁, hv₀, hkh]) (by simp [hv₁, hv₀, hw2])
      (by simp [hv₁, hv₀, hN]) (by simp [hv₁, hv₀, hLg]) (by simp [hv₁, hv₀, hW])
      (by simp [hv₁, hv₀, hD])
    have sIf0 := sg_ifNE_neg body (p := .seq (.seq (uclear (sreg (.s 1)))
      (.seq (ucopy (sreg (.p .b)) (sreg (.s 1)) (sreg (.s 2)))
        (usub (sreg (.p .h)) (sreg (.s 1)) (sreg (.s 2)))))
      (synIfNE (sreg (.s 1)) synLowB (.seq (uclear (sreg (.s 1))) (synChunkB G F)))) he
      ((sgU_clear body (a := .s 1) (x := ℓ - h - 1) (by simp [e1])).seq sTop)
    refine lr_weaken body (sP.seq (sT.seq sIf0)) ?_ ?_
    · refine congrArg (synG R) ?_
      funext y
      simp only [synRecOut, synKh, synRh, synPcsR, synCfg, topCfg, synS, synDp, synQ, synOS,
        synAT, synER, synR2, synW2, synAR, hc, htop, ite_false, hv₁, hv₀, Function.update_apply,
        topPcRec, List.flatMap_nil, topRec_nil]
      split_ifs <;> simp_all [synA]
    · simp only [synRecCost, htop, ite_false, ← ha]
      omega

end Rec

end IntegerMultBounds.MathlibTM2.Fast
