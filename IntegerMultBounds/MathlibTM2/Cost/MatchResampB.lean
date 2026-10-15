module

public import IntegerMultBounds.MathlibTM2.Cost.MatchBase
public import IntegerMultBounds.MathlibTM2.Fast.PrepB

/-!
# Cost matching: the `B̃₀` stage with its loader

`mt_rsb_stage_le`: the step bound of `rsbStage_exec` (`Fast/PrepB.lean`),
`rsbAllCost Tm t₀ w (fastWindow p α) α² d t … (preCpB σ₀ …) T`, is eventually at most
`C (totResamp + totCRT + T p)`, for fixed host stack count `Tm`, bank `t₀`, alphabet
`prime + Ka` and width ratios `w ≤ cw p`, `W ≤ cW p`, with the cleared registers of the base
file `σ₀` of at most `T w` symbols.

Per axis (`mt_rsb_all_le`):
* **Lines** (`mt_rsb_axisCost_le`, `mt_rsb_X_le`): `T/t` lines of `α²` Horner steps over windows
  of `m = fastWindow p α ≤ √p/(2α) + 1` records, `T · mtRsbX ≤ mtRsbCX · T α √p M(p)`; over the
  `d` axes this is `mtRsbCX · totResamp` (`mt_rsb_resamp_eq`).
* **Interchanges** of a non-last axis with the last one (`mt_rsb_swap_le`): `swapConst · 3 T w ·
  ℓ^τ + 1` each, times the simulation factor `Tm + 12 swapT t₀ + 5`; with the banks, headers and
  stream copies, `mtRsbCL · T p (ℓ^τ + 1)` per axis (`mt_rsb_stepAx_le`). Over the `d` axes this
  is `d T p (1 + ℓ^τ) ≤ totCRT` (`mt_rsb_dV_le`); it does not fit `totResamp`.
* **Loader** (`mt_rsb_cp_succ_le`, `mt_rsb_cp_zero_le`): `100 (P + G) ≤ 200 T` per record and
  per cleared file (record fields `P`, `G` in unary, headers), and `O((t + 1) Q^4)` for the four
  table runs at `tblC W w` steps per atom, the counters and the cleared tables
  (`mt_rsb_loader_body_le`, `mt_rsb_clear_le`, `Q` the small parameters); with `t ≤ r`,
  `Q ≤ (cW + cw + 6) p` this is at most `mtRsbU = 2 r ((cW + cw + 6) p)^4` per axis, and
  `(d + 1) mtRsbU ≤ A b^5 r` is eventually below `T p` (`mt_small_le`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds
  IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- The per-record factor of one line of `B̃₀`. -/
def mtRsbX (Tm w m Kn : ℕ) : ℕ :=
  Kn * (2 * m * (rmulCost Tm w + 64 * w + 64) + 64 * w + 198) + 2 * rmulCost Tm w + 66 * w + 114

theorem mt_rsb_lineCost_le {Tm w s t m Kn : ℕ} (hst : s ≤ t) (ht : 1 ≤ t) :
    rsbLineCost Tm w s t m Kn + 2 + 2 * (t * w) ≤ t * mtRsbX Tm w m Kn := by
  unfold rsbLineCost rsbStepCost mtRsbX
  set R := rmulCost Tm w
  have h1 : 2 * m * s * (R + 64 * w + 64) ≤ t * (2 * m * (R + 64 * w + 64)) := by
    calc 2 * m * s * (R + 64 * w + 64) = s * (2 * m * (R + 64 * w + 64)) := by ring
      _ ≤ t * (2 * m * (R + 64 * w + 64)) := Nat.mul_le_mul_right _ hst
  have h2 : 64 * s * w + 64 * s + 128 + 6 ≤ t * (64 * w + 198) := by nlinarith
  have h3 : 2 * m * s * (R + 64 * w + 64) + 64 * s * w + 64 * s + 128 + 6 ≤
      t * (2 * m * (R + 64 * w + 64) + 64 * w + 198) := by nlinarith
  have h4 : Kn * (2 * m * s * (R + 64 * w + 64) + 64 * s * w + 64 * s + 128 + 6) ≤
      Kn * (t * (2 * m * (R + 64 * w + 64) + 64 * w + 198)) := Nat.mul_le_mul_left _ h3
  have h5 : 2 * s * (R + 16 * w + 16) ≤ t * (2 * R + 32 * w + 32) := by nlinarith
  have h6 : 32 * t * w + 16 * t + 64 + 2 + 2 * (t * w) ≤ t * (34 * w + 82) := by nlinarith
  have e : Kn * (2 * m * s * (R + 64 * w + 64) + 64 * s * w + 64 * s + 128 + 6) =
      Kn * (2 * m * s * (R + 64 * w + 64) + 64 * s * w + 64 * s + 128 + 6) := rfl
  nlinarith

theorem mt_rsb_axisCost_le {Tm w s t m Kn : ℕ} (N : ℕ) (hst : s ≤ t) (ht : 1 ≤ t) :
    rsbAxisCost Tm w s t m Kn (N / t) ≤ N * mtRsbX Tm w m Kn + 4 := by
  unfold rsbAxisCost
  have h1 := mt_rsb_lineCost_le (Tm := Tm) (w := w) (m := m) (Kn := Kn) hst ht
  have h2 : N / t * t ≤ N := Nat.div_mul_le_self N t
  set X := mtRsbX Tm w m Kn
  set B := N / t
  have h3 : B * (rsbLineCost Tm w s t m Kn + 2) + 2 * (B * t * w) ≤ B * (t * X) := by
    have : B * (rsbLineCost Tm w s t m Kn + 2 + 2 * (t * w)) ≤ B * (t * X) :=
      Nat.mul_le_mul_left _ h1
    have e : B * (rsbLineCost Tm w s t m Kn + 2 + 2 * (t * w)) =
        B * (rsbLineCost Tm w s t m Kn + 2) + 2 * (B * t * w) := by ring
    omega
  have h4 : B * (t * X) ≤ N * X := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h2
  omega

/-! ### The loader -/

theorem mt_rsb_tblC_le {W w Q : ℕ} (hW : W ≤ Q) (hw : w ≤ Q) (hQ : 1 ≤ Q) :
    tblC W w ≤ 808 * Q ^ 2 := by
  unfold tblC
  have : W + 4 ≤ 5 * Q := by omega
  have h2 : (W + 4) ^ 2 ≤ (5 * Q) ^ 2 := Nat.pow_le_pow_left this 2
  nlinarith

theorem mt_rsb_vm_le {W w Q X K E : ℕ} (lens : List ℕ) (hW : W ≤ Q) (hw : w ≤ Q)
    (hl : ∀ k ∈ lens, k ≤ X) :
    preVMCost 48 W w lens K E ≤
      K * tblC W w + 2 * E + lens.length * (X * (4 * Q + 10) + 6 * Q + 10) + 300 * Q + 331 := by
  unfold preVMCost
  have h1 : (lens.map fun k => k * (4 * W + 10) + 6 * W + 10).sum ≤
      lens.length * (X * (4 * Q + 10) + 6 * Q + 10) := by
    have := List.sum_le_card_nsmul (lens.map fun k => k * (4 * W + 10) + 6 * W + 10)
      (X * (4 * Q + 10) + 6 * Q + 10) (by
        intro x hx
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
        have := hl k hk
        have : k * (4 * W + 10) ≤ X * (4 * Q + 10) := Nat.mul_le_mul this (by omega)
        omega)
    simpa using this
  omega

/-- The bound `U = (t + 1) Q^4` of the small loader terms dominates its monomials. -/
theorem mt_rsb_U_facts {t Q : ℕ} (hQ : 1 ≤ Q) :
    t + 1 ≤ (t + 1) * Q ^ 4 ∧ Q ≤ (t + 1) * Q ^ 4 ∧ Q ^ 2 ≤ (t + 1) * Q ^ 4 ∧
      (t + 1) * Q ≤ (t + 1) * Q ^ 4 ∧ (t + 1) * Q ^ 2 ≤ (t + 1) * Q ^ 4 ∧
      (t + 1) * Q ^ 3 ≤ (t + 1) * Q ^ 4 ∧ Q ^ 4 ≤ (t + 1) * Q ^ 4 := by
  have q1 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQ
  have q2 : Q ≤ Q ^ 4 := by
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ 4 := Nat.pow_le_pow_right hQ (by norm_num)
  have q3 : Q ^ 2 ≤ Q ^ 4 := Nat.pow_le_pow_right hQ (by norm_num)
  have q4 : Q ^ 3 ≤ Q ^ 4 := Nat.pow_le_pow_right hQ (by norm_num)
  have ht : Q ^ 4 ≤ (t + 1) * Q ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ht⟩
  · calc t + 1 = (t + 1) * 1 := by ring
      _ ≤ (t + 1) * Q ^ 4 := Nat.mul_le_mul_left _ q1
  · omega
  · omega
  · exact Nat.mul_le_mul_left _ q2
  · exact Nat.mul_le_mul_left _ q3
  · exact Nat.mul_le_mul_left _ q4

/-- The small parameters of a loader record. -/
def mtRsbQ (D : PreAxB) (w : ℕ) : ℕ := D.m + D.α + D.p + D.W + w + D.L + D.Ld + 1

/-- **The loader of one axis apart from the clearing**: `100 (P + G)` for the record fields and
the headers, and `O((t + 1) Q^4)` for the counters and the four table runs. -/
theorem mt_rsb_loader_body_le (D : PreAxB) (w : ℕ) (hst : D.s ≤ D.t) :
    (3 * D.fields.sum + 3 * 10 + 1) + preNumCostB D w + preHdrCostB D w + preTabCostB D w +
        (2 * (D.t + D.m + D.L + D.Ld + D.P + D.G + D.α + D.W) + 17) ≤
      100 * (D.P + D.G) + 10 ^ 8 * ((D.t + 1) * mtRsbQ D w ^ 4) := by
  obtain ⟨t, s, m, L, Ld, P, G, α, p, W⟩ := D
  simp only at hst ⊢
  set Q := mtRsbQ ⟨t, s, m, L, Ld, P, G, α, p, W⟩ w with hQdef
  have hQ : Q = m + α + p + W + w + L + Ld + 1 := rfl
  have hQ1 : 1 ≤ Q := by omega
  have hmQ : m ≤ Q := by omega
  have hαQ : α ≤ Q := by omega
  have hpQ : p ≤ Q := by omega
  have hWQ : W ≤ Q := by omega
  have hwQ : w ≤ Q := by omega
  have h1Q : (1 : ℕ) ≤ Q := hQ1
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := mt_rsb_U_facts (t := t) hQ1
  set U := (t + 1) * Q ^ 4
  have hC := mt_rsb_tblC_le hWQ hwQ hQ1
  have hC1 := mt_rsb_tblC_le hWQ (show 1 ≤ Q from hQ1) hQ1
  -- the fields
  have hf : (PreAxB.fields ⟨t, s, m, L, Ld, P, G, α, p, W⟩).sum ≤ 2 * t + P + G + Q := by
    simp only [PreAxB.fields, List.sum_cons, List.sum_nil]; omega
  -- the counters
  have hn : preNumCostB ⟨t, s, m, L, Ld, P, G, α, p, W⟩ w ≤ 100 * U := by
    unfold preNumCostB
    simp only
    have a1 : (s - m) * (4 * w + 7) ≤ t * (4 * Q + 7) := Nat.mul_le_mul (by omega) (by omega)
    have a2 : (t - s) * (4 * w + 7) ≤ t * (4 * Q + 7) := Nat.mul_le_mul (by omega) (by omega)
    have a3 : m * (4 * w + 7) ≤ Q * (4 * Q + 7) := Nat.mul_le_mul hmQ (by omega)
    have a4 : α * (4 * α + 7) ≤ Q * (4 * Q + 7) := Nat.mul_le_mul hαQ (by omega)
    have a5 : m * w ≤ Q * Q := Nat.mul_le_mul hmQ hwQ
    have a6 : t * Q ≤ (t + 1) * Q := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  -- the headers
  have hh : preHdrCostB ⟨t, s, m, L, Ld, P, G, α, p, W⟩ w ≤ 16 * (P + G) + 100 * U := by
    unfold preHdrCostB
    simp only
    omega
  -- the tables
  have hKE : preKE ⟨t, s, m, L, Ld, P, G, α, p, W⟩ ≤ 1456 * ((t + 1) * Q ^ 2) := by
    unfold preKE
    simp only
    have a1 : s * (2 * m) * (310 * p + 126) ≤ t * (2 * Q) * (436 * Q) :=
      Nat.mul_le_mul (Nat.mul_le_mul hst (by omega)) (by omega)
    have e : t * (2 * Q) * (436 * Q) = 872 * (t * Q ^ 2) := by ring
    have a2 : t * Q ^ 2 ≤ (t + 1) * Q ^ 2 := Nat.mul_le_mul_right _ (by omega)
    have a3 : Q ≤ Q ^ 2 := by nlinarith
    have a4 : (t + 1) ≤ (t + 1) * Q ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    have a5 : Q ^ 2 ≤ (t + 1) * Q ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hKD : preKD ⟨t, s, m, L, Ld, P, G, α, p, W⟩ ≤ 1043 * ((t + 1) * Q) := by
    unfold preKD
    simp only
    have a1 : s * (310 * p + 123) ≤ t * (433 * Q) := Nat.mul_le_mul hst (by omega)
    have a2 : t * (433 * Q) = 433 * (t * Q) := by ring
    have a3 : t * Q ≤ (t + 1) * Q := Nat.mul_le_mul_right _ (by omega)
    have a4 : Q ≤ (t + 1) * Q := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hKH : preKH ⟨t, s, m, L, Ld, P, G, α, p, W⟩ ≤ 14 * Q := by
    unfold preKH; simp only; omega
  have hKM : preKM ⟨t, s, m, L, Ld, P, G, α, p, W⟩ ≤ 10 * (t + 1) := by
    unfold preKM; simp only; omega
  have hT1 := mt_rsb_vm_le (W := W) (w := w) (Q := Q) (X := t + Q)
    (K := preKE ⟨t, s, m, L, Ld, P, G, α, p, W⟩) (E := s * (2 * m) * w) [s, t, α, m, p] hWQ hwQ
    (by intro k hk; simp at hk; omega)
  have hT2 := mt_rsb_vm_le (W := W) (w := w) (Q := Q) (X := t + Q)
    (K := preKD ⟨t, s, m, L, Ld, P, G, α, p, W⟩) (E := s * w) [s, t, α, p] hWQ hwQ
    (by intro k hk; simp at hk; omega)
  have hT3 := mt_rsb_vm_le (W := W) (w := w) (Q := Q) (X := t + Q)
    (K := preKH ⟨t, s, m, L, Ld, P, G, α, p, W⟩) (E := w) [p] hWQ hwQ
    (by intro k hk; simp at hk; omega)
  have hT4 := mt_rsb_vm_le (W := W) (w := 1) (Q := Q) (X := t + Q)
    (K := preKM ⟨t, s, m, L, Ld, P, G, α, p, W⟩) (E := t) [s, t] hWQ hQ1
    (by intro k hk; simp at hk; omega)
  simp only [List.length_cons, List.length_nil] at hT1 hT2 hT3 hT4
  have b1 : preKE ⟨t, s, m, L, Ld, P, G, α, p, W⟩ * tblC W w ≤ 1456 * 808 * U := by
    calc _ ≤ (1456 * ((t + 1) * Q ^ 2)) * (808 * Q ^ 2) := Nat.mul_le_mul hKE hC
      _ = 1456 * 808 * U := by ring
  have b2 : preKD ⟨t, s, m, L, Ld, P, G, α, p, W⟩ * tblC W w ≤ 1043 * 808 * U := by
    calc _ ≤ (1043 * ((t + 1) * Q)) * (808 * Q ^ 2) := Nat.mul_le_mul hKD hC
      _ = 1043 * 808 * ((t + 1) * Q ^ 3) := by ring
      _ ≤ 1043 * 808 * U := Nat.mul_le_mul_left _ u6
  have b3 : preKH ⟨t, s, m, L, Ld, P, G, α, p, W⟩ * tblC W w ≤ 14 * 808 * U := by
    calc _ ≤ (14 * Q) * (808 * Q ^ 2) := Nat.mul_le_mul hKH hC
      _ = 14 * 808 * Q ^ 3 := by ring
      _ ≤ 14 * 808 * U := Nat.mul_le_mul_left _ (by
          have : Q ^ 3 ≤ Q ^ 4 := Nat.pow_le_pow_right hQ1 (by norm_num); omega)
  have b4 : preKM ⟨t, s, m, L, Ld, P, G, α, p, W⟩ * tblC W 1 ≤ 10 * 808 * U := by
    calc _ ≤ (10 * (t + 1)) * (808 * Q ^ 2) := Nat.mul_le_mul hKM hC1
      _ = 10 * 808 * ((t + 1) * Q ^ 2) := by ring
      _ ≤ 10 * 808 * U := Nat.mul_le_mul_left _ u5
  have e1 : s * (2 * m) * w ≤ 2 * U := by
    have : s * (2 * m) * w ≤ t * (2 * Q) * Q := Nat.mul_le_mul (Nat.mul_le_mul hst (by omega)) hwQ
    have e : t * (2 * Q) * Q = 2 * (t * Q ^ 2) := by ring
    have : t * Q ^ 2 ≤ (t + 1) * Q ^ 2 := Nat.mul_le_mul_right _ (by omega)
    omega
  have e2 : s * w ≤ U := by
    have : s * w ≤ t * Q := Nat.mul_le_mul hst hwQ
    have : t * Q ≤ (t + 1) * Q := Nat.mul_le_mul_right _ (by omega)
    omega
  have l1 : (t + Q) * (4 * Q + 10) + 6 * Q + 10 ≤ 50 * U := by
    have e : (t + Q) * (4 * Q + 10) + 6 * Q + 10 = 4 * (t * Q) + 10 * t + 4 * Q ^ 2 + 16 * Q + 10 :=
      by ring
    have : t * Q ≤ (t + 1) * Q := Nat.mul_le_mul_right _ (by omega)
    omega
  have hT : preTabCostB ⟨t, s, m, L, Ld, P, G, α, p, W⟩ w ≤ 3 * 10 ^ 6 * U := by
    unfold preTabCostB
    simp only
    omega
  omega

/-- A bank register holds at most one header and a separator. -/
theorem mt_rsb_bank_length_le {t₀ A : ℕ} (hd : Fin 5 → Fin t₀) (hs : Fin 5 → List Bool)
    (j : Fin (swapT t₀)) :
    (rsbBank (A := A) hd hs j).length ≤ 1 + ∑ k, (hs k).length := by
  unfold rsbBank
  split_ifs with h
  · simp only [List.length_cons, List.length_map]
    have := Finset.single_le_sum (f := fun k => (hs k).length) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (Classical.choose h))
    omega
  · simp

/-- The bank of an interchange: at most `swapT t₀ (1 + Σ |hs k|)` symbols. -/
theorem mt_rsb_bank_sum_le {t₀ A : ℕ} (hd : Fin 5 → Fin t₀) (hs : Fin 5 → List Bool) :
    ∑ j, (rsbBank (A := A) hd hs j).length ≤ swapT t₀ * (1 + ∑ k, (hs k).length) := by
  have := Finset.sum_le_card_nsmul Finset.univ (fun j => (rsbBank (A := A) hd hs j).length)
    (1 + ∑ k, (hs k).length) (fun j _ => mt_rsb_bank_length_le hd hs j)
  simpa using this

/-- The headers of an interchange of `[P] × [2^h] × [G] × [2^d] × [B]`. -/
theorem mt_rsb_hs_sum_le (P G B h e : ℕ) :
    ∑ k, (sxBits (BinaryInterchangeRun.values P G B h e k)).length ≤ 5 * (P + G + B + h + e) := by
  have : ∀ k, (sxBits (BinaryInterchangeRun.values P G B h e k)).length ≤ P + G + B + h + e := by
    intro k
    refine (mt_length_sxBits_le _).trans ?_
    fin_cases k <;> simp [BinaryInterchangeRun.values] <;> omega
  have := Finset.sum_le_card_nsmul Finset.univ
    (fun k => (sxBits (BinaryInterchangeRun.values P G B h e k)).length) (P + G + B + h + e)
    (fun k _ => this k)
  simpa using this

/-- **Clearing a configured file**: the registers loaded for the axis `D` hold at most
`50 (P + G) + O((t + 1) Q^4)` symbols, counted twice, plus two per register. -/
theorem mt_rsb_clear_le {t₀ A : ℕ} (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)))
    (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxB) (rest : List (Fin (A + 4))) (hst : D.s ≤ D.t) :
    ((preClrB hd).map fun r => 2 * (preLoadB σ hd w D rest r).length + 2).sum ≤
      100 * (D.P + D.G) + 1000 * ((D.t + 1) * mtRsbQ D w ^ 4) := by
  have hb : ∀ k, (rsbBank (A := A) hd (D.hs w) (reg (hd k))).length ≤
      1 + 5 * (D.P + D.G + 3 * w + D.L + D.Ld) := by
    intro k
    have h1 := mt_rsb_bank_length_le (A := A) hd (D.hs w) (reg (hd k))
    have h2 := mt_rsb_hs_sum_le D.P D.G (3 * w) D.L D.Ld
    have e : (∑ k, (D.hs w k).length) =
        ∑ k, (sxBits (BinaryInterchangeRun.values D.P D.G (3 * w) D.L D.Ld k)).length := rfl
    omega
  simp [preClrB, preLoadB, Function.update_apply, preHB, preBankB, preMaskE, tblStreamE,
    tblStreamD, tblPairs, tblWinE, List.length_flatMap, Function.comp_def, List.map_const',
    List.sum_replicate]
  generalize hQ : mtRsbQ D w = Q
  have hQ' : Q = D.m + D.α + D.p + D.W + w + D.L + D.Ld + 1 := by rw [← hQ]; rfl
  have hQ1 : 1 ≤ Q := by omega
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := mt_rsb_U_facts (t := D.t) hQ1
  generalize hU : (D.t + 1) * Q ^ 4 = U at u1 u2 u3 u4 u5 u6 u7 ⊢
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  have hb3 := hb 3
  have hb4 := hb 4
  have hmQ : D.m ≤ Q := by omega
  have hwQ : w ≤ Q := by omega
  have hαQ : D.α ≤ Q := by omega
  have q2 : Q * Q = Q ^ 2 := by ring
  have tq : D.t * Q ≤ (D.t + 1) * Q := Nat.mul_le_mul_right _ (by omega)
  have tq2 : D.t * Q ^ 2 ≤ (D.t + 1) * Q ^ 2 := Nat.mul_le_mul_right _ (by omega)
  have a1 : D.s * (D.m * w + D.m * w) ≤ 2 * U := by
    have h1 : D.m * w ≤ Q * Q := Nat.mul_le_mul hmQ hwQ
    have : D.s * (D.m * w + D.m * w) ≤ D.t * (2 * (Q * Q)) := Nat.mul_le_mul hst (by omega)
    have e : D.t * (2 * (Q * Q)) = 2 * (D.t * Q ^ 2) := by ring
    omega
  have a2 : D.s * w ≤ U := by
    have : D.s * w ≤ D.t * Q := Nat.mul_le_mul hst hwQ
    omega
  have a3 : D.m * w ≤ U := by
    have : D.m * w ≤ Q * Q := Nat.mul_le_mul hmQ hwQ
    omega
  have a4 : (D.s - D.m) * w ≤ U := by
    have : (D.s - D.m) * w ≤ D.s * w := Nat.mul_le_mul_right _ (by omega)
    omega
  have a5 : (D.t - D.s) * w ≤ U := by
    have : (D.t - D.s) * w ≤ D.t * Q := Nat.mul_le_mul (by omega) hwQ
    omega
  have a6 : D.α * D.α ≤ U := by
    have : D.α * D.α ≤ Q * Q := Nat.mul_le_mul hαQ hαQ
    omega
  generalize (rsbBank (A := A) hd (D.hs w) (reg (hd 0))).length = x0 at hb0 ⊢
  generalize (rsbBank (A := A) hd (D.hs w) (reg (hd 1))).length = x1 at hb1 ⊢
  generalize (rsbBank (A := A) hd (D.hs w) (reg (hd 2))).length = x2 at hb2 ⊢
  generalize (rsbBank (A := A) hd (D.hs w) (reg (hd 3))).length = x3 at hb3 ⊢
  generalize (rsbBank (A := A) hd (D.hs w) (reg (hd 4))).length = x4 at hb4 ⊢
  clear hb hQ hU u3 u4 u5 u6 u7 q2 tq tq2
  linarith

/-! ### The lines against `M(p)` -/

/-- `α² m ≤ (3/2) α √p` for the window `m = fastWindow p α`. -/
theorem mt_rsb_window_le {n : ℕ} (h : Big n) :
    (alpha n : ℝ) ^ 2 * (Mult.FastB0.fastWindow (p n) (alpha n) : ℝ) ≤
      3 / 2 * ((alpha n : ℝ) * Real.sqrt (p n)) := by
  have hα2 : (2 : ℝ) ≤ alpha n := by exact_mod_cast two_le_alpha h.1
  have hα0 : (0 : ℝ) < alpha n := by linarith
  have hsp : (alpha n : ℝ) ≤ Real.sqrt (p n) := by
    rw [Real.le_sqrt hα0.le (Nat.cast_nonneg _)]
    exact_mod_cast h.alpha_sq_le_p
  have hm : (Mult.FastB0.fastWindow (p n) (alpha n) : ℝ) ≤
      Real.sqrt (p n) / (2 * alpha n) + 1 := by
    unfold Mult.FastB0.fastWindow
    push_cast
    have h1 : ((Nat.sqrt (p n) / (2 * alpha n) : ℕ) : ℝ) ≤
        ((Nat.sqrt (p n) : ℕ) : ℝ) / ((2 * alpha n : ℕ) : ℝ) := Nat.cast_div_le
    have h2 : ((Nat.sqrt (p n) : ℕ) : ℝ) ≤ Real.sqrt (p n) := Real.nat_sqrt_le_real_sqrt
    have h3 : ((Nat.sqrt (p n) : ℕ) : ℝ) / ((2 * alpha n : ℕ) : ℝ) ≤
        Real.sqrt (p n) / (2 * alpha n) := by
      push_cast
      exact div_le_div_of_nonneg_right h2 (by positivity)
    linarith
  have e : (alpha n : ℝ) ^ 2 * (Real.sqrt (p n) / (2 * alpha n) + 1) =
      (alpha n : ℝ) * Real.sqrt (p n) / 2 + (alpha n : ℝ) ^ 2 := by
    field_simp
  have h4 : (alpha n : ℝ) ^ 2 ≤ (alpha n : ℝ) * Real.sqrt (p n) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hsp hα0.le
  calc (alpha n : ℝ) ^ 2 * (Mult.FastB0.fastWindow (p n) (alpha n) : ℝ) ≤
      (alpha n : ℝ) ^ 2 * (Real.sqrt (p n) / (2 * alpha n) + 1) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ ≤ _ := by rw [e]; linarith

/-- `1 ≤ α √p` and `α² ≤ α √p`. -/
theorem mt_rsb_alpha_facts {n : ℕ} (h : Big n) :
    1 ≤ (alpha n : ℝ) * Real.sqrt (p n) ∧
      (alpha n : ℝ) ^ 2 ≤ (alpha n : ℝ) * Real.sqrt (p n) := by
  have hα2 : (2 : ℝ) ≤ alpha n := by exact_mod_cast two_le_alpha h.1
  have hα0 : (0 : ℝ) < alpha n := by linarith
  have hsp : (alpha n : ℝ) ≤ Real.sqrt (p n) := by
    rw [Real.le_sqrt hα0.le (Nat.cast_nonneg _)]
    exact_mod_cast h.alpha_sq_le_p
  have hs1 : (1 : ℝ) ≤ Real.sqrt (p n) := Real.one_le_sqrt.2 (mt_one_le_p h)
  refine ⟨by nlinarith, ?_⟩
  rw [sq]; exact mul_le_mul_of_nonneg_left hsp hα0.le

/-- The constant of one line of `B̃₀` against `α √p M(p)` per record. -/
noncomputable def mtRsbCX (Tm cw : ℕ) : ℝ := 5 * mtCM Tm cw + 322 * cw + 504

/-- **One line of `B̃₀` per record**: `mtRsbX ≤ mtRsbCX · α √p M(p)`. -/
theorem mt_rsb_X_le {n w cw : ℕ} (Tm : ℕ) (h : Big n) (hw : 1 ≤ w) (hwc : w ≤ cw * p n) :
    (mtRsbX Tm w (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2) : ℝ) ≤
      mtRsbCX Tm cw * ((alpha n : ℝ) * Real.sqrt (p n) * totMp n) := by
  have hR := mt_rmul_le Tm h hw hwc
  have hc := mt_CM_nonneg Tm cw
  have hM1 := mt_one_le_mp h
  have hpM := mt_p_le_mp h
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hwc
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hwM : (w : ℝ) ≤ cw * totMp n := hw'.trans (mul_le_mul_of_nonneg_left hpM hcw)
  have hwin := mt_rsb_window_le h
  obtain ⟨hy1, hy2⟩ := mt_rsb_alpha_facts h
  set a2 : ℝ := (alpha n : ℝ) ^ 2
  set mf : ℝ := (Mult.FastB0.fastWindow (p n) (alpha n) : ℝ)
  set y : ℝ := (alpha n : ℝ) * Real.sqrt (p n)
  set M := totMp n
  set R : ℝ := (rmulCost Tm w : ℝ)
  set c := mtCM Tm cw
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hmf0 : (0 : ℝ) ≤ mf := Nat.cast_nonneg _
  have ha20 : (0 : ℝ) ≤ a2 := by positivity
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have e : (mtRsbX Tm w (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2) : ℝ) =
      a2 * (2 * mf * (R + 64 * w + 64) + 64 * w + 198) + 2 * R + 66 * w + 114 := by
    simp only [mtRsbX, a2, mf, R]; push_cast; ring
  rw [e]
  -- `R + 64 w + 64 ≤ (c + 64 cw + 64) M`
  have k1 : R + 64 * w + 64 ≤ (c + 64 * cw + 64) * M := by nlinarith
  have k1' : 0 ≤ R + 64 * w + 64 := by positivity
  -- `a2 · 2 mf · (R + 64 w + 64) ≤ 3 y (c + 64 cw + 64) M`
  have k2 : a2 * (2 * mf * (R + 64 * w + 64)) ≤ 3 * y * ((c + 64 * cw + 64) * M) := by
    have : a2 * (2 * mf * (R + 64 * w + 64)) = 2 * (a2 * mf) * (R + 64 * w + 64) := by ring
    rw [this]
    calc 2 * (a2 * mf) * (R + 64 * w + 64) ≤ 2 * (3 / 2 * y) * (R + 64 * w + 64) := by
          gcongr
      _ ≤ 2 * (3 / 2 * y) * ((c + 64 * cw + 64) * M) := by
          gcongr
      _ = 3 * y * ((c + 64 * cw + 64) * M) := by ring
  have k3 : a2 * (64 * w + 198) ≤ y * ((64 * cw + 198) * M) := by
    have : (64 * (w : ℝ) + 198) ≤ (64 * cw + 198) * M := by nlinarith
    calc a2 * (64 * w + 198) ≤ y * (64 * w + 198) := by gcongr
      _ ≤ y * ((64 * cw + 198) * M) := by gcongr
  have k4 : 2 * R + 66 * w + 114 ≤ y * ((2 * c + 66 * cw + 114) * M) := by
    have h1 : 2 * R + 66 * w + 114 ≤ (2 * c + 66 * cw + 114) * M := by nlinarith
    have h2 : 0 ≤ (2 * c + 66 * cw + 114) * M := by positivity
    nlinarith
  have e2 : a2 * (2 * mf * (R + 64 * w + 64) + 64 * w + 198) =
      a2 * (2 * mf * (R + 64 * w + 64)) + a2 * (64 * w + 198) := by ring
  rw [e2]
  have : mtRsbCX Tm cw * (y * M) = 3 * y * ((c + 64 * cw + 64) * M) +
      y * ((64 * cw + 198) * M) + y * ((2 * c + 66 * cw + 114) * M) := by
    simp only [mtRsbCX, c]; ring
  rw [this]
  linarith

/-! ### The axes of the pipeline -/

section Axes

variable {n : ℕ}

theorem mt_rsb_last (hd0 : 0 < d n) : rsbAx hd0 0 = ⟨d n - 1, by omega⟩ :=
  Fin.ext (by simp [rsbAx])

/-- Before, along, between and the last axis: the whole box. -/
theorem mt_rsb_prod_eq (h : Big n) (hd0 : 0 < d n) (i : Fin (d n)) (hi : (i : ℕ) + 1 < d n) :
    rsbPre (t n) i * (t n i * (rsbMid (t n) i * t n (rsbAx hd0 0))) = T n := by
  have h1 := rsbPre_mul (t n) i
  rw [rsb_suf_last (t n) i hi, mt_prod_t h] at h1
  rw [mt_rsb_last hd0]
  exact h1

/-- `rsbPre t i ≤ T` and `rsbMid t i ≤ T`. -/
theorem mt_rsb_PG_le (h : Big n) (i : Fin (d n)) :
    rsbPre (t n) i ≤ T n ∧ rsbMid (t n) i ≤ T n := by
  have h1 := rsbPre_mul (t n) i
  rw [mt_prod_t h] at h1
  have hT : 0 < T n := Nat.two_pow_pos _
  have hP : 0 < rsbPre (t n) i := Nat.pos_of_ne_zero (fun e => by rw [e] at h1; omega)
  have hS : 0 < t n i * rsbSuf (t n) i := Nat.pos_of_ne_zero (fun e => by rw [e] at h1; omega)
  have hS' : 0 < rsbSuf (t n) i := Nat.pos_of_mul_pos_left hS
  have hti : 0 < t n i := mt_t_pos n i
  refine ⟨?_, ?_⟩
  · calc rsbPre (t n) i = rsbPre (t n) i * 1 := (mul_one _).symm
      _ ≤ rsbPre (t n) i * (t n i * rsbSuf (t n) i) := Nat.mul_le_mul_left _ hS
      _ = T n := h1
  · have hdvd : rsbMid (t n) i ∣ rsbSuf (t n) i :=
      (List.dropLast_sublist _).prod_dvd_prod
    have hMS := Nat.le_of_dvd hS' hdvd
    have hST : rsbSuf (t n) i ≤ T n := by
      calc rsbSuf (t n) i ≤ rsbPre (t n) i * (t n i * rsbSuf (t n) i) := by
            have : rsbSuf (t n) i ≤ t n i * rsbSuf (t n) i := Nat.le_mul_of_pos_left _ hti
            exact this.trans (Nat.le_mul_of_pos_left _ hP)
        _ = T n := h1
    omega

/-- The volume of the interchange of axis `i` with the last axis: `3 T w`. -/
theorem mt_rsb_vol (h : Big n) (hd0 : 0 < d n) (i : Fin (d n)) (hi : (i : ℕ) + 1 < d n) (E : ℕ) :
    rsbPre (t n) i * 2 ^ Nat.log 2 (t n i) * rsbMid (t n) i *
        2 ^ Nat.log 2 (t n (rsbAx hd0 0)) * E = T n * E ∧
      rsbPre (t n) i * 2 ^ Nat.log 2 (t n (rsbAx hd0 0)) * rsbMid (t n) i *
        2 ^ Nat.log 2 (t n i) * E = T n * E := by
  rw [← IntegerMultBounds.MathlibTM2.Mult.Pipeline.t_pow_log n i, ← IntegerMultBounds.MathlibTM2.Mult.Pipeline.t_pow_log n (rsbAx hd0 0)]
  have := mt_rsb_prod_eq h hd0 i hi
  constructor
  · rw [← this]; ring
  · rw [← this]; ring

theorem mt_rsb_P_pos (h : Big n) (hd0 : 0 < d n) (i : Fin (d n)) (hi : (i : ℕ) + 1 < d n) :
    0 < rsbPre (t n) i ∧ 0 < rsbMid (t n) i := by
  have h1 := mt_rsb_prod_eq h hd0 i hi
  have hT : 0 < T n := Nat.two_pow_pos _
  refine ⟨Nat.pos_of_ne_zero (fun e => by rw [e] at h1; omega),
    Nat.pos_of_ne_zero (fun e => by rw [e] at h1; simp at h1; omega)⟩

/-- The widths of the axes: `ℓ - 1` or `ℓ`, and `ℓ` for the last one. -/
theorem mt_rsb_logs (h : Big n) (hd0 : 0 < d n) (i : Fin (d n)) :
    (Nat.log 2 (t n i) = ℓ n - 1 ∨ Nat.log 2 (t n i) = ℓ n) ∧
      Nat.log 2 (t n (rsbAx hd0 0)) = ℓ n :=
  ⟨pre_log_t i, pre_log_last h hd0⟩

/-- **The interchanges of axis `i` with the last axis**, both directions: at most
`swapConst · 3 T w · ℓ^τ + 1` steps each. -/
theorem mt_rsb_swap_le (h : Big n) (hd0 : 0 < d n) (i : Fin (d n)) (hi : (i : ℕ) + 1 < d n)
    {w : ℕ} (hw : 1 ≤ w) :
    (BinaryInterchangeRun.cost (rsbPre (t n) i) (rsbMid (t n) i) (3 * w) (Nat.log 2 (t n i))
        (Nat.log 2 (t n (rsbAx hd0 0))) (preHsB n w hd0 i) : ℝ) ≤
        swapConst * (T n * (3 * w) : ℕ) * (ℓ n : ℝ) ^ Parameters.tau + 1 ∧
      (BinaryInterchangeRun.cost (rsbPre (t n) i) (rsbMid (t n) i) (3 * w)
        (Nat.log 2 (t n (rsbAx hd0 0))) (Nat.log 2 (t n i))
        (fun k => preHsB n w hd0 i (Equiv.swap 3 4 k)) : ℝ) ≤
        swapConst * (T n * (3 * w) : ℕ) * (ℓ n : ℝ) ^ Parameters.tau + 1 := by
  obtain ⟨hP, hG⟩ := mt_rsb_P_pos h hd0 i hi
  obtain ⟨hl, hlast⟩ := mt_rsb_logs h hd0 i
  have h2 := h.two_le_ℓ
  have hlt := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n i
  obtain ⟨v1, v2⟩ := mt_rsb_vol h hd0 i hi (3 * w)
  constructor
  · have := mt_swap_le (E := 3 * w) (h := Nat.log 2 (t n i)) (w := Nat.log 2 (t n (rsbAx hd0 0)))
      (L := ℓ n) (preHsB n w hd0 i) hP hG (by omega)
      (by rcases hl with e | e <;> omega) (by rcases hl with e | e <;> omega)
      (fun k => by simp only [preHsB]; exact value_sxBits _)
      (fun k => canonical_sxBits _) hlt (by omega) (by omega)
    rwa [v1] at this
  · have := mt_swap_le (E := 3 * w) (h := Nat.log 2 (t n (rsbAx hd0 0))) (w := Nat.log 2 (t n i))
      (L := ℓ n) (fun k => preHsB n w hd0 i (Equiv.swap 3 4 k)) hP hG (by omega)
      (by rcases hl with e | e <;> omega) (by rcases hl with e | e <;> omega)
      (fun k => by simp only [preHsB]; rw [value_sxBits, ResampA.rsa_values_swap34])
      (fun k => canonical_sxBits _) (by omega) hlt (by omega)
    rwa [v2] at this

/-- The headers of axis `i`: at most `5 (2 T + 3 w + 2 ℓ)` bits, either order. -/
theorem mt_rsb_hs_le (h : Big n) (hd0 : 0 < d n) (i : Fin (d n)) (w : ℕ) :
    ∑ k, (preHsB n w hd0 i k).length ≤ 5 * (2 * T n + 3 * w + 2 * ℓ n) ∧
      ∑ k, (preHsB n w hd0 i (Equiv.swap 3 4 k)).length ≤ 5 * (2 * T n + 3 * w + 2 * ℓ n) := by
  obtain ⟨hP, hG⟩ := mt_rsb_PG_le h i
  have hl1 := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n i
  have hl2 := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n (rsbAx hd0 0)
  constructor
  · have := mt_rsb_hs_sum_le (rsbPre (t n) i) (rsbMid (t n) i) (3 * w) (Nat.log 2 (t n i))
      (Nat.log 2 (t n (rsbAx hd0 0)))
    simp only [preHsB]
    omega
  · have := mt_rsb_hs_sum_le (rsbPre (t n) i) (rsbMid (t n) i) (3 * w)
      (Nat.log 2 (t n (rsbAx hd0 0))) (Nat.log 2 (t n i))
    simp only [preHsB, ResampA.rsa_values_swap34]
    omega

end Axes

/-! ### The loader at the pipeline records -/

/-- The loader of one axis: the clearing of the previous file, plus the body. -/
theorem mt_rsb_preCost_le {t₀ A : ℕ} (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)))
    (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxB) (hst : D.s ≤ D.t) :
    preCostB σ hd w D ≤ ((preClrB hd).map fun r => 2 * (σ r).length + 2).sum + 1 +
      100 * (D.P + D.G) + 10 ^ 8 * ((D.t + 1) * mtRsbQ D w ^ 4) := by
  have := mt_rsb_loader_body_le D w hst
  unfold preCostB
  omega

/-- The bound of the small loader terms of every axis at length `n`. -/
def mtRsbU (n cw cW : ℕ) : ℕ := 2 * r n * ((cW + cw + 6) * p n) ^ 4

section Records

variable {n : ℕ}

theorem mt_rsb_preDB_facts (h : Big n) (hd0 : 0 < d n) {w W cw cW : ℕ} (hwc : w ≤ cw * p n)
    (hWc : W ≤ cW * p n) (k : ℕ) :
    (preDB n W hd0 k).s ≤ (preDB n W hd0 k).t ∧ (preDB n W hd0 k).P ≤ T n ∧
      (preDB n W hd0 k).G ≤ T n ∧
      ((preDB n W hd0 k).t + 1) * mtRsbQ (preDB n W hd0 k) w ^ 4 ≤ mtRsbU n cw cW := by
  obtain ⟨hP, hG⟩ := mt_rsb_PG_le h (rsbAx hd0 k)
  have hst := (mt_s_lt_t h (rsbAx hd0 k)).le
  have htr := mt_t_le_r n (rsbAx hd0 k)
  have hr1 : 1 ≤ r n := Nat.one_le_two_pow
  refine ⟨hst, hP, hG, ?_⟩
  have hp13 := h.thirteen_le_p
  have hfw := Mult.FastB0.fastWindow_le_third (two_le_alpha h.1) hp13
  have hα := mt_alpha_le_p h
  have hl1 := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n (rsbAx hd0 k)
  have hl2 := IntegerMultBounds.MathlibTM2.Mult.Pipeline.log_t_le n (rsbAx hd0 0)
  have hlp := mt_ℓ_le_p h
  have hQ : mtRsbQ (preDB n W hd0 k) w ≤ (cW + cw + 6) * p n := by
    simp only [mtRsbQ, preDB]
    nlinarith
  have h1 : (preDB n W hd0 k).t + 1 ≤ 2 * r n := by simp only [preDB]; omega
  calc ((preDB n W hd0 k).t + 1) * mtRsbQ (preDB n W hd0 k) w ^ 4 ≤
      (2 * r n) * ((cW + cw + 6) * p n) ^ 4 :=
        Nat.mul_le_mul h1 (Nat.pow_le_pow_left hQ 4)
    _ = mtRsbU n cw cW := rfl

/-- The loader of step `j + 1`: clearing the file of step `j`, loading the axis of step
`j + 1`. -/
theorem mt_rsb_cp_succ_le {t₀ A : ℕ} (h : Big n) (hd0 : 0 < d n) {w W cw cW : ℕ}
    (hwc : w ≤ cw * p n) (hWc : W ≤ cW * p n) (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)))
    (hd : Fin 5 → Fin t₀) (rest : List (Fin (A + 4))) (j : ℕ) :
    preCpB σ₀ hd n w W hd0 rest (j + 1) ≤ 400 * T n + 1 + (10 ^ 8 + 1000) * mtRsbU n cw cW := by
  obtain ⟨s1, P1, G1, U1⟩ := mt_rsb_preDB_facts h hd0 hwc hWc (w := w) (j + 1)
  obtain ⟨s0, P0, G0, U0⟩ := mt_rsb_preDB_facts h hd0 hwc hWc (w := w) j
  have h1 := mt_rsb_preCost_le (preCfgB σ₀ hd n w W hd0 rest j) hd w (preDB n W hd0 (j + 1)) s1
  have h2 := mt_rsb_clear_le σ₀ hd w (preDB n W hd0 j) (preRecsB n W hd0 (j + 1) ++ rest) s0
  simp only [preCpB, preCfgB] at h1 ⊢
  nlinarith

/-- The loader of step `0`: clearing the base file (registers of at most `T w` symbols). -/
theorem mt_rsb_cp_zero_le {t₀ A : ℕ} (h : Big n) (hd0 : 0 < d n) {w W cw cW : ℕ}
    (hwc : w ≤ cw * p n) (hWc : W ≤ cW * p n) (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)))
    (hd : Fin 5 → Fin t₀) (rest : List (Fin (A + 4)))
    (hσ₀ : ∀ r ∈ preClrB hd, (σ₀ r).length ≤ T n * w) :
    preCpB σ₀ hd n w W hd0 rest 0 ≤ 17 * (2 * (T n * w) + 2) + 1 + 200 * T n +
      10 ^ 8 * mtRsbU n cw cW := by
  obtain ⟨s0, P0, G0, U0⟩ := mt_rsb_preDB_facts h hd0 hwc hWc (w := w) 0
  have h1 := mt_rsb_preCost_le σ₀ hd w (preDB n W hd0 0) s0
  have h2 : ((preClrB hd).map fun r => 2 * (σ₀ r).length + 2).sum ≤ 17 * (2 * (T n * w) + 2) := by
    have := List.sum_le_card_nsmul ((preClrB hd).map fun r => 2 * (σ₀ r).length + 2)
      (2 * (T n * w) + 2) (by
        intro x hx
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
        have := hσ₀ r hr
        omega)
    simpa [preClrB] using this
  simp only [preCpB]
  nlinarith

end Records

/-! ### One step of `B̃₀` along a non-last axis -/

/-- The arithmetic of `rsbStepAxCost`. -/
theorem mt_rsb_stepAx_arith {Tm t₀ w s ti m Kn N c₁ c₂ b₁ b₂ e X B E : ℕ} {C : ℝ}
    (hax : rsbAxisCost Tm w s ti m Kn (N / ti) ≤ N * X + 4) (hc₁ : (c₁ : ℝ) ≤ C)
    (hc₂ : (c₂ : ℝ) ≤ C) (hb₁ : b₁ ≤ B) (hb₂ : b₂ ≤ B) (he : e ≤ E) :
    (rsbStepAxCost Tm t₀ w s ti m Kn N c₁ c₂ b₁ b₂ e : ℝ) ≤
      (N * X + 4 : ℕ) + 2 * ((Tm + 12 * swapT t₀ + 5 : ℕ) * C) +
        (12 * B + 68 * (N * w) + 4 * Tm + 12 * swapT t₀ + 8 * E + 62 : ℕ) := by
  unfold rsbStepAxCost rsbSwapCost
  have hK : (0 : ℝ) ≤ (Tm + 12 * swapT t₀ + 5 : ℕ) := Nat.cast_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hc₁ hK
  have h2 := mul_le_mul_of_nonneg_left hc₂ hK
  have h3 : (rsbAxisCost Tm w s ti m Kn (N / ti) : ℝ) ≤ (N * X + 4 : ℕ) := by exact_mod_cast hax
  have h4 : ((6 * b₁ + 34 * (N * w) + 2 * Tm + 6 * swapT t₀ + 23 + (4 * e + 8) + 6 * b₂ +
      34 * (N * w) + 2 * Tm + 6 * swapT t₀ + 23 + (4 * e + 8) : ℕ) : ℝ) ≤
      (12 * B + 68 * (N * w) + 4 * Tm + 12 * swapT t₀ + 8 * E + 62 : ℕ) := by
    exact_mod_cast (by omega)
  push_cast at h1 h2 h3 h4 ⊢
  linarith

/-- The constant of the linear part of one step: the two interchanges, the bank, the
headers. -/
noncomputable def mtRsbCL (Tm t₀ cw : ℕ) : ℝ :=
  6 * (Tm + 12 * swapT t₀ + 5 : ℕ) * swapConst * cw + 2 * (Tm + 12 * swapT t₀ + 5 : ℕ) +
    12 * swapT t₀ * (21 + 15 * cw) + 200 * cw + 4 * Tm + 12 * swapT t₀ + 300

theorem mt_rsb_CL_nonneg (Tm t₀ cw : ℕ) : 0 ≤ mtRsbCL Tm t₀ cw := by
  unfold mtRsbCL
  have := mt_swapConst_nonneg
  positivity

/-- The unit of the linear terms of one axis: `T p (ℓ^τ + 1)`. -/
noncomputable def mtRsbV (n : ℕ) : ℝ := (T n : ℝ) * p n * ((ℓ n : ℝ) ^ Parameters.tau + 1)

theorem mt_rsb_V_facts {n w cw : ℕ} (h : Big n) (hwc : w ≤ cw * p n) :
    1 ≤ mtRsbV n ∧ (T n : ℝ) ≤ mtRsbV n ∧ (p n : ℝ) ≤ mtRsbV n ∧ (ℓ n : ℝ) ≤ mtRsbV n ∧
      (T n : ℝ) * w ≤ cw * mtRsbV n ∧ (w : ℝ) ≤ cw * mtRsbV n ∧
      (T n : ℝ) * w * (ℓ n : ℝ) ^ Parameters.tau ≤ cw * mtRsbV n := by
  have hT1 := mt_one_le_T n
  have hp1 := mt_one_le_p h
  have hΛ : 0 ≤ (ℓ n : ℝ) ^ Parameters.tau := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hwc
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hlp : (ℓ n : ℝ) ≤ p n := by exact_mod_cast mt_ℓ_le_p h
  have hTp : (T n : ℝ) ≤ T n * p n := le_mul_of_one_le_right (by linarith) hp1
  have hpT : (p n : ℝ) ≤ T n * p n := le_mul_of_one_le_left (by linarith) hT1
  have hV : (T n : ℝ) * p n ≤ mtRsbV n := by
    unfold mtRsbV
    have : (0 : ℝ) ≤ T n * p n := by positivity
    nlinarith
  have hTw : (T n : ℝ) * w ≤ cw * (T n * p n) := by
    have := mul_le_mul_of_nonneg_left hw' (show (0 : ℝ) ≤ T n by linarith)
    linarith
  refine ⟨by nlinarith, by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
  · nlinarith
  · have : (w : ℝ) ≤ cw * (T n * p n) := by nlinarith
    nlinarith
  · have h1 : (T n : ℝ) * w * (ℓ n : ℝ) ^ Parameters.tau ≤
        cw * (T n * p n) * (ℓ n : ℝ) ^ Parameters.tau := mul_le_mul_of_nonneg_right hTw hΛ
    have h2 : cw * (T n * p n) * (ℓ n : ℝ) ^ Parameters.tau ≤ cw * mtRsbV n := by
      unfold mtRsbV
      have : (0 : ℝ) ≤ cw * (T n * p n) := by positivity
      nlinarith
    linarith

/-- **One step of `B̃₀` along the non-last axis `i`**: the lines `T · mtRsbX` and the linear
part `mtRsbCL · T p (ℓ^τ + 1)` (interchanges, banks, headers, stream copies). -/
theorem mt_rsb_stepAx_le {n : ℕ} (Tm t₀ A : ℕ) (h : Big n) (hd0 : 0 < d n) (i : Fin (d n))
    (hi : (i : ℕ) + 1 < d n) {w cw : ℕ} (hw : 1 ≤ w) (hwc : w ≤ cw * p n)
    (hd : Fin 5 → Fin t₀) :
    (rsbStepAxCost Tm t₀ w (s n i) (t n i) (Mult.FastB0.fastWindow (p n) (alpha n))
        (alpha n ^ 2) (∏ i, t n i)
        (BinaryInterchangeRun.cost (rsbPre (t n) i) (rsbMid (t n) i) (3 * w) (Nat.log 2 (t n i))
          (Nat.log 2 (t n (rsbAx hd0 0))) (preHsB n w hd0 i))
        (BinaryInterchangeRun.cost (rsbPre (t n) i) (rsbMid (t n) i) (3 * w)
          (Nat.log 2 (t n (rsbAx hd0 0))) (Nat.log 2 (t n i))
          (fun k => preHsB n w hd0 i (Equiv.swap 3 4 k)))
        (∑ j, (rsbBank (A := A) hd (preHsB n w hd0 i) j).length)
        (∑ j, (rsbBank (A := A) hd (fun k => preHsB n w hd0 i (Equiv.swap 3 4 k)) j).length)
        ((preHsB n w hd0 i 3).length + (preHsB n w hd0 i 4).length + 2) : ℝ) ≤
      (T n : ℝ) * mtRsbX Tm w (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2) + 4 +
        mtRsbCL Tm t₀ cw * mtRsbV n := by
  obtain ⟨c1, c2⟩ := mt_rsb_swap_le h hd0 i hi hw
  obtain ⟨hs1, hs2⟩ := mt_rsb_hs_le h hd0 i w
  have hax := mt_rsb_axisCost_le (Tm := Tm) (w := w) (m := Mult.FastB0.fastWindow (p n) (alpha n))
    (Kn := alpha n ^ 2) (∏ i, t n i) (mt_s_lt_t h i).le (mt_t_pos n i)
  have hb1 := mt_rsb_bank_sum_le (A := A) hd (preHsB n w hd0 i)
  have hb2 := mt_rsb_bank_sum_le (A := A) hd (fun k => preHsB n w hd0 i (Equiv.swap 3 4 k))
  have he : (preHsB n w hd0 i 3).length + (preHsB n w hd0 i 4).length + 2 ≤
      5 * (2 * T n + 3 * w + 2 * ℓ n) + 2 := by
    have : (preHsB n w hd0 i 3).length + (preHsB n w hd0 i 4).length ≤
        ∑ k, (preHsB n w hd0 i k).length := by
      rw [Fin.sum_univ_five]; omega
    omega
  have hb1' : ∑ j, (rsbBank (A := A) hd (preHsB n w hd0 i) j).length ≤
      swapT t₀ * (1 + 5 * (2 * T n + 3 * w + 2 * ℓ n)) :=
    hb1.trans (Nat.mul_le_mul_left _ (by omega))
  have hb2' : ∑ j, (rsbBank (A := A) hd (fun k => preHsB n w hd0 i (Equiv.swap 3 4 k)) j).length ≤
      swapT t₀ * (1 + 5 * (2 * T n + 3 * w + 2 * ℓ n)) :=
    hb2.trans (Nat.mul_le_mul_left _ (by omega))
  have key := mt_rsb_stepAx_arith (t₀ := t₀) hax c1 c2 hb1' hb2' he
  rw [mt_prod_t h] at key ⊢
  refine key.trans ?_
  obtain ⟨v1, vT, vp, vl, vTw, vw, vTwl⟩ := mt_rsb_V_facts h hwc
  have hCL0 : mtRsbCL Tm t₀ cw = 6 * (Tm + 12 * swapT t₀ + 5 : ℕ) * swapConst * cw +
      2 * (Tm + 12 * swapT t₀ + 5 : ℕ) + 12 * swapT t₀ * (21 + 15 * cw) + 200 * cw + 4 * Tm +
      12 * swapT t₀ + 300 := rfl
  rw [hCL0]
  generalize swapT t₀ = S
  set V := mtRsbV n
  set X := mtRsbX Tm w (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2)
  have hK1 : (0 : ℝ) ≤ ((Tm + 12 * S + 5 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsT : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg _
  have hsc := mt_swapConst_nonneg
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hTm : (0 : ℝ) ≤ (Tm : ℝ) := Nat.cast_nonneg _
  push_cast
  push_cast at hK1
  -- the interchange term
  have i1 : 2 * ((Tm + 12 * S + 5) * (swapConst * ((T n : ℝ) * (3 * w)) *
      (ℓ n : ℝ) ^ Parameters.tau + 1)) ≤
      6 * (Tm + 12 * S + 5) * swapConst * cw * V + 2 * (Tm + 12 * S + 5) * V := by
    have a : swapConst * ((T n : ℝ) * (3 * w)) * (ℓ n : ℝ) ^ Parameters.tau =
        3 * swapConst * ((T n : ℝ) * w * (ℓ n : ℝ) ^ Parameters.tau) := by ring
    have b : 3 * swapConst * ((T n : ℝ) * w * (ℓ n : ℝ) ^ Parameters.tau) ≤
        3 * swapConst * (cw * V) := by
      have : (0 : ℝ) ≤ 3 * swapConst := by linarith
      exact mul_le_mul_of_nonneg_left vTwl this
    have c : ((Tm : ℝ) + 12 * S + 5) * (swapConst * ((T n : ℝ) * (3 * w)) *
        (ℓ n : ℝ) ^ Parameters.tau + 1) ≤ ((Tm : ℝ) + 12 * S + 5) * (3 * swapConst * (cw * V) + V) := by
      apply mul_le_mul_of_nonneg_left _ hK1
      rw [a]; linarith
    have e : ((Tm : ℝ) + 12 * S + 5) * (3 * swapConst * (cw * V) + V) =
        3 * ((Tm + 12 * S + 5) * swapConst * cw * V) + (Tm + 12 * S + 5) * V := by ring
    linarith
  -- the bank and header terms
  have i2 : 12 * ((S : ℝ) * (1 + 5 * (2 * (T n : ℝ) + 3 * w + 2 * ℓ n))) ≤
      12 * S * (21 + 15 * cw) * V := by
    have h1 : (1 + 5 * (2 * (T n : ℝ) + 3 * w + 2 * ℓ n)) ≤ (21 + 15 * cw) * V := by linarith
    have := mul_le_mul_of_nonneg_left h1 hsT
    linarith
  have i3 : 68 * ((T n : ℝ) * w) + 8 * (5 * (2 * (T n : ℝ) + 3 * w + 2 * ℓ n) + 2) ≤
      (200 * cw + 300) * V := by linarith
  have i4 : 4 * (Tm : ℝ) + 12 * S + 62 ≤ (4 * Tm + 12 * S + 62) * V := by
    have : (0 : ℝ) ≤ 4 * Tm + 12 * S + 62 := by linarith
    exact le_mul_of_one_le_right this v1
  clear_value V X
  clear key hax c1 c2 hb1 hb2 hb1' hb2' he hs1 hs2
  nlinarith

/-! ### All axes -/

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- **`B̃₀` along all axes with its loader**, at one length `n`: per axis the lines
`T · mtRsbX`, the linear part `mtRsbCL · T p (ℓ^τ + 1)`, `400 T + 1` for the record fields and
headers of the loader and `O(mtRsbU)` for its tables and counters. -/
theorem mt_rsb_all_le {n : ℕ} (Tm t₀ A : ℕ) (h : Big n) (hd0 : 0 < d n) {w W cw cW : ℕ}
    (hw : 1 ≤ w) (hwc : w ≤ cw * p n) (hWc : W ≤ cW * p n)
    (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (rest : List (Fin (A + 4)))
    (hσ₀ : ∀ r ∈ preClrB hd, (σ₀ r).length ≤ T n * w) :
    (rsbAllCost Tm t₀ w (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2) (d n) (t n) hd0
        (rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)) A hd
        (preCpB σ₀ hd n w W hd0 rest) (∏ i, t n i) : ℝ) ≤
      (d n : ℝ) * ((T n : ℝ) * mtRsbX Tm w (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2) +
          mtRsbCL Tm t₀ cw * mtRsbV n + 400 * T n + 9 + (10 ^ 8 + 1000) * mtRsbU n cw cW) +
        ((T n : ℝ) * mtRsbX Tm w (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2) +
          17 * (2 * (T n * w) + 2) + 200 * T n + 10 ^ 8 * mtRsbU n cw cW + 2 * d n + 9) := by
  set X := mtRsbX Tm w (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2)
  set Bs : ℝ := (T n : ℝ) * X + mtRsbCL Tm t₀ cw * mtRsbV n + 400 * T n + 9 +
    (10 ^ 8 + 1000) * mtRsbU n cw cW
  let F : ℕ → ℕ := fun j =>
      preCpB σ₀ hd n w W hd0 rest (j + 1) +
        rsbStepAxCost Tm t₀ w
          ((rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)) (rsbAx hd0 (j + 1))).s
          (t n (rsbAx hd0 (j + 1))) (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2)
          (∏ i, t n i)
          (BinaryInterchangeRun.cost (rsbPre (t n) (rsbAx hd0 (j + 1)))
            (rsbMid (t n) (rsbAx hd0 (j + 1))) (3 * w)
            ((rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)) (rsbAx hd0 (j + 1))).Lb
            ((rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)) (rsbAx hd0 0)).Lb
            ((rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)) (rsbAx hd0 (j + 1))).hs)
          (BinaryInterchangeRun.cost (rsbPre (t n) (rsbAx hd0 (j + 1)))
            (rsbMid (t n) (rsbAx hd0 (j + 1))) (3 * w)
            ((rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)) (rsbAx hd0 0)).Lb
            ((rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)) (rsbAx hd0 (j + 1))).Lb
            (fun k => ((rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0))
              (rsbAx hd0 (j + 1))).hs (Equiv.swap 3 4 k)))
          (∑ i, (rsbBank hd ((rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0))
            (rsbAx hd0 (j + 1))).hs i : List (Fin (A + 4))).length)
          (∑ i, (rsbBank hd (fun k => ((rsbLineBData n (fun i => Nat.log 2 (t n i))
            (preHsB n w hd0)) (rsbAx hd0 (j + 1))).hs (Equiv.swap 3 4 k)) i :
              List (Fin (A + 4))).length)
          ((((rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0))
            (rsbAx hd0 (j + 1))).hs 3).length + (((rsbLineBData n (fun i => Nat.log 2 (t n i))
              (preHsB n w hd0)) (rsbAx hd0 (j + 1))).hs 4).length + 2) + 4
  have hstep : ∀ j ∈ Finset.range (d n - 1), ((F j : ℕ) : ℝ) ≤ Bs := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have hi : ((rsbAx hd0 (j + 1) : Fin (d n)) : ℕ) + 1 < d n := by simp [rsbAx]; omega
    have h1 := mt_rsb_stepAx_le Tm t₀ A h hd0 (rsbAx hd0 (j + 1)) hi hw hwc hd
    have h2 : (preCpB σ₀ hd n w W hd0 rest (j + 1) : ℝ) ≤
        400 * T n + 1 + (10 ^ 8 + 1000) * mtRsbU n cw cW := by
      exact_mod_cast mt_rsb_cp_succ_le h hd0 hwc hWc σ₀ hd rest j
    simp only [F]
    push_cast
    simp only [rsbLineBData]
    linarith
  have hall : rsbAllCost Tm t₀ w (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2) (d n)
      (t n) hd0 (rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)) A hd
      (preCpB σ₀ hd n w W hd0 rest) (∏ i, t n i) =
      preCpB σ₀ hd n w W hd0 rest 0 +
        rsbAxisCost Tm w (s n (rsbAx hd0 0)) (t n (rsbAx hd0 0))
          (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2)
          ((∏ i, t n i) / t n (rsbAx hd0 0)) +
        ((∑ j ∈ Finset.range (d n - 1), F j) + 2 * (d n - 1) + 4) := rfl
  have hS : (∑ j ∈ Finset.range (d n - 1), ((F j : ℕ) : ℝ)) ≤ (d n - 1 : ℕ) * Bs := by
    have := Finset.sum_le_card_nsmul (Finset.range (d n - 1)) (fun j => ((F j : ℕ) : ℝ)) Bs hstep
    simpa using this
  have hax : rsbAxisCost Tm w (s n (rsbAx hd0 0)) (t n (rsbAx hd0 0))
      (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2)
      ((∏ i, t n i) / t n (rsbAx hd0 0)) ≤ T n * X + 4 := by
    have := mt_rsb_axisCost_le (Tm := Tm) (w := w) (m := Mult.FastB0.fastWindow (p n) (alpha n))
      (Kn := alpha n ^ 2) (∏ i, t n i) (mt_s_lt_t h (rsbAx hd0 0)).le (mt_t_pos n (rsbAx hd0 0))
    rwa [mt_prod_t h] at this ⊢
  have h0 := mt_rsb_cp_zero_le h hd0 hwc hWc σ₀ hd rest hσ₀ (W := W)
  have hBs : 0 ≤ Bs := by
    have := mt_rsb_CL_nonneg Tm t₀ cw
    have hV : 0 ≤ mtRsbV n := by
      unfold mtRsbV
      have := Real.rpow_nonneg (Nat.cast_nonneg (ℓ n)) Parameters.tau
      positivity
    have : (0 : ℝ) ≤ (T n : ℝ) * X := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have : (0 : ℝ) ≤ (mtRsbU n cw cW : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ mtRsbCL Tm t₀ cw * mtRsbV n := mul_nonneg (by assumption) hV
    have : (0 : ℝ) ≤ (T n : ℝ) := Nat.cast_nonneg _
    simp only [Bs]
    linarith
  have hd1 : ((d n - 1 : ℕ) : ℝ) ≤ d n := by
    have : d n - 1 ≤ d n := Nat.sub_le _ _
    exact_mod_cast this
  have hdB : ((d n - 1 : ℕ) : ℝ) * Bs ≤ d n * Bs := mul_le_mul_of_nonneg_right hd1 hBs
  have h0' : (preCpB σ₀ hd n w W hd0 rest 0 : ℝ) ≤
      17 * (2 * (T n * w) + 2) + 1 + 200 * T n + 10 ^ 8 * mtRsbU n cw cW := by exact_mod_cast h0
  have hax' : (rsbAxisCost Tm w (s n (rsbAx hd0 0)) (t n (rsbAx hd0 0))
      (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2)
      ((∏ i, t n i) / t n (rsbAx hd0 0)) : ℝ) ≤ T n * X + 4 := by exact_mod_cast hax
  have hd2 : ((2 * (d n - 1) : ℕ) : ℝ) ≤ 2 * d n := by
    have : 2 * (d n - 1) ≤ 2 * d n := by omega
    exact_mod_cast this
  rw [hall]
  push_cast [Nat.cast_sum] at hS ⊢
  linarith

/-! ### Against the terms of `totBound` -/

/-- The small terms of all axes: `(10^8 + 1000)(d + 1) mtRsbU ≤ A b^5 r`. -/
theorem mt_rsb_small_le {n : ℕ} (h : Big n) (cw cW : ℕ) :
    (10 ^ 8 + 1000) * (d n + 1) * mtRsbU n cw cW ≤
      (10 ^ 8 + 1000) * 4 * 6 ^ 4 * (cW + cw + 6) ^ 4 * b n ^ 5 * r n := by
  have hdb : d n + 1 ≤ 2 * b n := by have := d_le_b n; have := h.sixteen_le_b; omega
  unfold mtRsbU p
  calc (10 ^ 8 + 1000) * (d n + 1) * (2 * r n * ((cW + cw + 6) * (6 * b n)) ^ 4) ≤
      (10 ^ 8 + 1000) * (2 * b n) * (2 * r n * ((cW + cw + 6) * (6 * b n)) ^ 4) := by gcongr
    _ = (10 ^ 8 + 1000) * 4 * 6 ^ 4 * (cW + cw + 6) ^ 4 * b n ^ 5 * r n := by ring

/-- `d T α √p M(p) = totResamp`. -/
theorem mt_rsb_resamp_eq (n : ℕ) :
    (d n : ℝ) * ((T n : ℝ) * ((alpha n : ℝ) * Real.sqrt (p n) * totMp n)) = totResamp n := by
  rw [totResamp, Real.sqrt_eq_rpow]; ring

/-- `d T p (ℓ^τ + 1) ≤ totCRT`. -/
theorem mt_rsb_dV_le {n : ℕ} (h : Big n) : (d n : ℝ) * mtRsbV n ≤ totCRT n := by
  unfold mtRsbV totCRT
  have hd1 : (1 : ℝ) ≤ d n := by exact_mod_cast h.one_le_d
  have hΛ : 0 ≤ (ℓ n : ℝ) ^ Parameters.tau := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hTp := mt_Tp_nonneg n
  have hdd : (d n : ℝ) ≤ (d n : ℝ) ^ 2 := by nlinarith
  have h0 : 0 ≤ (T n : ℝ) * p n * ((ℓ n : ℝ) ^ Parameters.tau + 1) := by positivity
  calc (d n : ℝ) * ((T n : ℝ) * p n * ((ℓ n : ℝ) ^ Parameters.tau + 1)) ≤
      (d n : ℝ) ^ 2 * ((T n : ℝ) * p n * ((ℓ n : ℝ) ^ Parameters.tau + 1)) :=
        mul_le_mul_of_nonneg_right hdd h0
    _ = _ := by ring

/-- `d T ≤ totCRT`. -/
theorem mt_rsb_dT_le {n : ℕ} (h : Big n) : (d n : ℝ) * T n ≤ totCRT n := by
  have h1 := mt_rsb_dV_le h
  have hp1 := mt_one_le_p h
  have hΛ : 0 ≤ (ℓ n : ℝ) ^ Parameters.tau := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hT : (0 : ℝ) ≤ T n := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d n := Nat.cast_nonneg _
  have : (d n : ℝ) * T n ≤ (d n : ℝ) * mtRsbV n := by
    apply mul_le_mul_of_nonneg_left _ hd
    unfold mtRsbV
    have : (T n : ℝ) ≤ T n * p n := le_mul_of_one_le_right hT hp1
    have : (T n : ℝ) * p n ≤ T n * p n * ((ℓ n : ℝ) ^ Parameters.tau + 1) :=
      le_mul_of_one_le_right (mt_Tp_nonneg n) (by linarith)
    linarith
  linarith

/-- **The cost of the `B̃₀` stage with its loader** (`rsbStage_exec`) against `totBound`: for
fixed host stack count `Tm`, interchange bank `t₀`, alphabet `prime + Ka` and width ratios
`cw`, `cW`, eventually in `n`, for every configuration with `1 ≤ w ≤ cw p`, table word size
`W ≤ cW p` and the cleared registers of the base file `σ₀` of at most `T w` symbols, the
stage costs at most `C (totResamp + totCRT + T p)`. The lines (`α²` Horner steps over windows
of `fastWindow p α ≈ √p / (2α)` records, Schönhage–Strassen products at width `w`) give
`totResamp`; the interchanges of each axis with the last one (`O(T w ℓ^τ)` per axis), the
banks, headers and record fields (`O(T)` per axis) give `d T p (1 + ℓ^τ) ≤ totCRT`; the tables
and counters of the loader (`O(r p^4)` per axis) are below `T p`. -/
theorem mt_rsb_stage_le (Tm t₀ Ka cw cW : ℕ) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∀ (hd0 : 0 < d n) (w W : ℕ)
      (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + Ka + 4))) (hd : Fin 5 → Fin t₀)
      (rest : List (Fin (prime + Ka + 4))),
      1 ≤ w → w ≤ cw * p n → W ≤ cW * p n →
      (∀ r ∈ preClrB hd, (σ₀ r).length ≤ T n * w) →
      (rsbAllCost Tm t₀ w (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2) (d n) (t n) hd0
          (rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)) (prime + Ka) hd
          (preCpB σ₀ hd n w W hd0 rest) (∏ i, t n i) : ℝ) ≤
        C * (totResamp n + totCRT n + T n * p n) := by
  refine ⟨2 * mtRsbCX Tm cw + mtRsbCL Tm t₀ cw + 409 + 34 * cw + 246, ?_⟩
  filter_upwards [eventually_big,
    mt_small_le ((10 ^ 8 + 1000) * 4 * 6 ^ 4 * (cW + cw + 6) ^ 4) 5] with n h hsm
    hd0 w W σ₀ hd rest hw hwc hWc hσ₀
  have hall := mt_rsb_all_le Tm t₀ (prime + Ka) h hd0 hw hwc hWc σ₀ hd rest hσ₀
  have hX := mt_rsb_X_le Tm h hw hwc
  have hres := mt_rsb_resamp_eq n
  have hY0 : 0 ≤ (alpha n : ℝ) * Real.sqrt (p n) * totMp n := by
    have := tot_mp_nonneg n
    have := Real.sqrt_nonneg (p n : ℝ)
    have : (0 : ℝ) ≤ alpha n := Nat.cast_nonneg _
    positivity
  set X := mtRsbX Tm w (Mult.FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2)
  set Y : ℝ := (alpha n : ℝ) * Real.sqrt (p n) * totMp n
  clear_value X Y
  have hdV := mt_rsb_dV_le h
  have hdT := mt_rsb_dT_le h
  have hU := hsm _ (mt_rsb_small_le h cw cW)
  push_cast at hU
  have hd1 : (1 : ℝ) ≤ d n := by exact_mod_cast h.one_le_d
  have hT0 : (0 : ℝ) ≤ T n := Nat.cast_nonneg _
  have hT1 := mt_one_le_T n
  have hp1 := mt_one_le_p h
  have hTp := mt_Tp_nonneg n
  have hcw : (0 : ℝ) ≤ cw := Nat.cast_nonneg _
  have hw' : (w : ℝ) ≤ cw * p n := by exact_mod_cast hwc
  have hCX : 0 ≤ mtRsbCX Tm cw := by
    unfold mtRsbCX; have := mt_CM_nonneg Tm cw; positivity
  have hCL := mt_rsb_CL_nonneg Tm t₀ cw
  have hRes0 := mt_resamp_nonneg n
  have hCrt0 := mt_crt_nonneg n
  -- the lines
  have l1 : (T n : ℝ) * X ≤ mtRsbCX Tm cw * ((T n : ℝ) * Y) := by
    have := mul_le_mul_of_nonneg_left hX hT0
    linarith
  have l2 : (d n : ℝ) * ((T n : ℝ) * X) ≤ mtRsbCX Tm cw * totResamp n := by
    rw [← hres]
    have := mul_le_mul_of_nonneg_left l1 (show (0 : ℝ) ≤ d n by linarith)
    linarith
  have l3 : (T n : ℝ) * X ≤ mtRsbCX Tm cw * totResamp n := by
    have : (T n : ℝ) * Y ≤ (d n : ℝ) * ((T n : ℝ) * Y) :=
      le_mul_of_one_le_left (mul_nonneg hT0 hY0) hd1
    rw [← hres]
    nlinarith
  -- the linear terms
  have l4 : (d n : ℝ) * (mtRsbCL Tm t₀ cw * mtRsbV n) ≤ mtRsbCL Tm t₀ cw * totCRT n := by
    have := mul_le_mul_of_nonneg_left hdV hCL
    linarith
  have l5 : (d n : ℝ) * (400 * T n + 9) ≤ 409 * totCRT n := by
    have : (d n : ℝ) * 9 ≤ 9 * ((d n : ℝ) * T n) := by nlinarith
    nlinarith
  have l6 : 17 * (2 * ((T n : ℝ) * w) + 2) + 200 * T n + 2 * d n + 9 ≤
      (34 * cw + 245) * ((T n : ℝ) * p n) := by
    have a1 : (T n : ℝ) * w ≤ cw * ((T n : ℝ) * p n) := by
      have := mul_le_mul_of_nonneg_left hw' hT0; linarith
    have a2 : (T n : ℝ) ≤ T n * p n := le_mul_of_one_le_right hT0 hp1
    have a3 : (d n : ℝ) ≤ T n * p n := by
      have : (d n : ℝ) ≤ p n := by
        have := d_le_b n
        have : d n ≤ p n := by unfold p; omega
        exact_mod_cast this
      have : (p n : ℝ) ≤ T n * p n := le_mul_of_one_le_left (by linarith) hT1
      linarith
    have a4 : (1 : ℝ) ≤ T n * p n := by nlinarith
    nlinarith
  -- the small terms
  have l7 : (d n : ℝ) * ((10 ^ 8 + 1000) * (mtRsbU n cw cW : ℝ)) + 10 ^ 8 * (mtRsbU n cw cW : ℝ) ≤
      (T n : ℝ) * p n := by
    have hU0 : (0 : ℝ) ≤ (mtRsbU n cw cW : ℝ) := Nat.cast_nonneg _
    nlinarith
  have e : (d n : ℝ) * ((T n : ℝ) * X + mtRsbCL Tm t₀ cw * mtRsbV n + 400 * T n + 9 +
      (10 ^ 8 + 1000) * (mtRsbU n cw cW : ℝ)) =
      (d n : ℝ) * ((T n : ℝ) * X) + (d n : ℝ) * (mtRsbCL Tm t₀ cw * mtRsbV n) +
        (d n : ℝ) * (400 * T n + 9) + (d n : ℝ) * ((10 ^ 8 + 1000) * (mtRsbU n cw cW : ℝ)) := by
    ring
  rw [e] at hall
  have hfin : mtRsbCX Tm cw * totResamp n + mtRsbCX Tm cw * totResamp n +
      mtRsbCL Tm t₀ cw * totCRT n + 409 * totCRT n + (34 * cw + 245) * ((T n : ℝ) * p n) +
      (T n : ℝ) * p n ≤
      (2 * mtRsbCX Tm cw + mtRsbCL Tm t₀ cw + 409 + 34 * cw + 246) *
        (totResamp n + totCRT n + T n * p n) := by
    have hc0 : (0 : ℝ) ≤ 34 * cw + 246 := by linarith
    have p1 := mul_nonneg hCX hCrt0
    have p2 := mul_nonneg hCX hTp
    have p3 := mul_nonneg hCL hRes0
    have p4 := mul_nonneg hCL hTp
    have p5 := mul_nonneg hc0 hRes0
    have p6 := mul_nonneg hc0 hCrt0
    have p7 : (0 : ℝ) ≤ 409 * totResamp n := by linarith
    have p8 : (0 : ℝ) ≤ 409 * ((T n : ℝ) * p n) := by linarith
    linarith
  clear e hX hres hdV hdT hU
  linarith

end IntegerMultBounds.MathlibTM2.Cost
