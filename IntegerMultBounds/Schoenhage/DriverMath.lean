module

public import IntegerMultBounds.Schoenhage.ChunkRound
public import IntegerMultBounds.Schoenhage.AlphaLift
public import IntegerMultBounds.Spec.SyntheticConvolutionFacts

/-! The transform drivers' bookkeeping (§6 task 6). Rounds that contract and
commute with differences only see an array's first `2^n` records
(`agree_of_contracts`); so if each round's output records agree there with the
computed round of their input records, the records after all rounds agree with
the computed schedule (`roundRun_agree`). Records on the `2^(-p)` grid whose
coefficients lie in the unit disk are disk records (`diskGrid_of_norm`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

variable {r : ℕ}

theorem agree_of_contracts {n : ℕ} {G : (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ} (hG : Contracts n G ∧ Additive G)
    {w₁ w₂ : ℕ → Fin r → ℂ} (h : Agree n w₁ w₂) : Agree n (G w₁) (G w₂) := by
  intro y hy
  have hz : ∀ y < 2 ^ n, ∀ k, ‖(w₁ - w₂) y k‖ ≤ 0 := fun y hy k => by simp [h y hy]
  have := hG.1 (w₁ - w₂) 0 hz y hy
  rw [hG.2] at this
  funext k
  have hk := this k
  simp only [Pi.sub_apply, norm_le_zero_iff, sub_eq_zero] at hk
  exact hk

theorem agree_roundArr {n p : ℕ} {w₁ w₂ : ℕ → Fin r → ℂ} (h : Agree n w₁ w₂) :
    Agree n (roundArr p w₁) (roundArr p w₂) := by
  intro y hy; funext k; simp only [roundArr, h y hy]

theorem Agree.trans' {n : ℕ} {u v w : ℕ → Fin r → ℂ} (h₁ : Agree n u v) (h₂ : Agree n v w) : Agree n u w :=
  fun y hy => (h₁ y hy).trans (h₂ y hy)

/-- One round on records: the output's values agree with the computed round of the input's. -/
def RoundStep (n p : ℕ) (G : (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ) (R R' : List (Rec r)) : Prop :=
  Agree n (arrayVec p R') (roundArr p (G (arrayVec p R)))

/-- Records produced round by round. -/
inductive Chain (n p : ℕ) : List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ) → List (Rec r) → List (Rec r) → Prop
  | nil (R : List (Rec r)) : Chain n p [] R R
  | cons {G : (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ} {Gs : List _} {R R' R'' : List (Rec r)} :
      RoundStep n p G R R' → Chain n p Gs R' R'' → Chain n p (G :: Gs) R R''

theorem roundRun_agree {n p : ℕ} : ∀ {Gs : List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ)} {R R' : List (Rec r)},
    (∀ G ∈ Gs, Contracts n G ∧ Additive G) → Chain n p Gs R R' →
    ∀ w, Agree n (arrayVec p R) w → Agree n (arrayVec p R') (roundRun p Gs w)
  | [], R, R', _, hc, w, hw => by cases hc; exact hw
  | G :: Gs, R, R', hG, hc, w, hw => by
    cases hc with
    | cons hs hc' =>
      refine roundRun_agree (fun G' hG' => hG G' (by simp [hG'])) hc' _ ?_
      exact hs.trans' (agree_roundArr (agree_of_contracts (hG G (by simp)) hw))

/-- Grid records whose coefficients lie in the unit disk are disk records. -/
theorem diskGrid_of_norm {p : ℕ} {f : Rec r} (h : ∀ k, ‖gridPoly p f.1 f.2 k‖ ≤ 1) : DiskGrid p f.1 f.2 := by
  intro j
  have hj := h j
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  rw [Complex.norm_def, Real.sqrt_le_one, Complex.normSq_apply] at hj
  simp only [gridPoly] at hj
  have key : ((f.1 j : ℝ)) ^ 2 + (f.2 j : ℝ) ^ 2 ≤ (2 ^ p) ^ 2 := by
    have e : (f.1 j : ℝ) / 2 ^ p * ((f.1 j : ℝ) / 2 ^ p) + (f.2 j : ℝ) / 2 ^ p * ((f.2 j : ℝ) / 2 ^ p) =
        ((f.1 j : ℝ) ^ 2 + (f.2 j : ℝ) ^ 2) / (2 ^ p) ^ 2 := by field_simp
    rw [e, div_le_one (by positivity)] at hj
    exact hj
  have e2 : (2 : ℤ) ^ (2 * p) = (2 ^ p) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [e2]
  exact_mod_cast key

theorem arrayVec_mem {p : ℕ} {R : List (Rec r)} {f : Rec r} (hf : f ∈ R) :
    ∃ y < R.length, arrayVec p R y = gridPoly p f.1 f.2 := by
  obtain ⟨y, hy, rfl⟩ := List.getElem_of_mem hf
  exact ⟨y, hy, by simp [arrayVec, List.getElem?_eq_getElem hy]⟩

/-- Records whose values agree on `[0, 2^n)` with a unit-disk array are disk records. -/
theorem diskGrid_of_agree {n p : ℕ} {R : List (Rec r)} (hl : R.length = 2 ^ n) {w : ℕ → Fin r → ℂ}
    (ha : Agree n (arrayVec p R) w) (hw : ∀ y < 2 ^ n, ∀ k, ‖w y k‖ ≤ 1) : ∀ f ∈ R, DiskGrid p f.1 f.2 := by
  intro f hf
  obtain ⟨y, hy, e⟩ := arrayVec_mem (p := p) hf
  apply diskGrid_of_norm
  intro k
  rw [← e, ha y (by omega)]
  exact hw y (by omega) k

/-! ### The transforms' outputs -/

/-- The forward driver's output: records obtained by the computed forward rounds from the input in
the layout `π` are within `√2 H 2^(-p)` of `L B F⁻ z` and are disk records. -/
theorem forward_close [NeZero r] {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) {H : ℕ} (hH : ∀ i < ts.length, axLen ts i ≤ H) (hH0 : 0 < H) (p : ℕ)
    (fs R0 R : List (Rec r)) (hfs : ∀ f ∈ fs, DiskGrid p f.1 f.2) (hRl : R.length = 2 ^ n)
    (h0 : Agree n (arrayVec p R0) fun y => arrayVec p fs (π.logi y))
    (hc : Chain n p (slotRounds π ts H) R0 R) :
    Close ts.prod (arrayVec p R) (fwdExact ts (π.toPerm hn) (arrayVec p fs)) (Real.sqrt 2 * H / 2 ^ p) ∧
      ∀ f ∈ R, DiskGrid p f.1 f.2 := by
  have hG : ∀ G ∈ slotRounds (r := r) π ts H, Contracts n G ∧ Additive G := by
    intro G hG
    simp only [slotRounds, List.mem_map] at hG
    obtain ⟨h, -, rfl⟩ := hG
    exact slotRound_contracts hts hn π h
  have ha := roundRun_agree hG hc _ (fun y hy => rfl)
  obtain ⟨hcl, hdisk⟩ := compSchedule_close hts hn π hH hH0 p (arrayVec p fs) (arrayVec p R0) h0
  have hw : ∀ y < 2 ^ n, ∀ k, ‖arrayVec p R0 y k‖ ≤ 1 := by
    intro y hy k
    rw [h0 y hy]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mp (norm_arrayVec_le hfs _) k
  refine ⟨fun y hy k => ?_, diskGrid_of_agree hRl ha (hdisk hw)⟩
  rw [hn] at hy
  rw [ha y hy]
  exact hcl y hy k

/-- The opposite driver's output: records obtained by the computed opposite rounds from `us`, then
moved to natural order, are within `√2 H 2^(-p)` of `F⁺ B⁻¹ L⁻¹ u` and are disk records. -/
theorem opposite_close [NeZero r] {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) {H : ℕ} (hH : ∀ i < ts.length, axLen ts i ≤ H) (hH0 : 0 < H) (p : ℕ)
    (us R G : List (Rec r)) (hus : ∀ u ∈ us, DiskGrid p u.1 u.2) (hGl : G.length = 2 ^ n)
    (hc : Chain n p (oppSlotRounds π ts H) us R)
    (hG : Agree n (arrayVec p G) fun x => arrayVec p R (π.phys x)) :
    Close ts.prod (arrayVec p G) (oppExact ts (π.toPerm hn) (arrayVec p us)) (Real.sqrt 2 * H / 2 ^ p) ∧
      ∀ g ∈ G, DiskGrid p g.1 g.2 := by
  have hGs : ∀ G ∈ oppSlotRounds (r := r) π ts H, Contracts n G ∧ Additive G := by
    intro G hG
    simp only [oppSlotRounds, List.mem_map] at hG
    obtain ⟨h, -, rfl⟩ := hG
    exact oppSlotRound_contracts hts hn π h
  have ha := roundRun_agree hGs hc _ (fun y hy => rfl)
  obtain ⟨hcl, hdisk⟩ := compOppSchedule_close hts hn π hH hH0 p (arrayVec p us)
  have hw : ∀ y < 2 ^ n, ∀ k, ‖arrayVec p us y k‖ ≤ 1 := fun y _ k =>
    (pi_norm_le_iff_of_nonneg zero_le_one).mp (norm_arrayVec_le hus _) k
  have hd := hdisk hw
  refine ⟨fun x hx k => ?_, diskGrid_of_agree hGl (w := fun x => compOppSchedule p π ts H (arrayVec p us) (π.phys x))
    (fun x hx => by rw [hG x hx]; exact ha _ (π.phys_lt x)) (fun x hx k => hd _ (π.phys_lt x) k)⟩
  rw [hn] at hx
  rw [hG x hx]
  dsimp only
  rw [ha _ (π.phys_lt x)]
  have := hcl (π.phys x) (π.phys_lt x) k
  rwa [π.logi_phys hx] at this

end IntegerMultBounds.Schoenhage
