module

public import IntegerMultBounds.Schoenhage.PrefixRounds
public import IntegerMultBounds.Schoenhage.PaperRounds
public import IntegerMultBounds.Schoenhage.ConvScale

/-! The prefix-slot round on numerators. A butterfly on address bit `P` of an
array on the `2^(-m)` grid is, on numerators, the exact sum and difference of
the paired records, on the `2^(-(m+1))` grid (`arrayVec_bflyRecs`); after
`s` of them one truncation toward zero by `2^s` is the grid rounding at `p`
(`arrayVec_truncRecs`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

variable {r : ℕ}

/-- Componentwise sum of records. -/
def addRec (f g : Rec r) : Rec r := (fun j => f.1 j + g.1 j, fun j => f.2 j + g.2 j)

/-- Componentwise difference of records. -/
def subRec (f g : Rec r) : Rec r := (fun j => f.1 j - g.1 j, fun j => f.2 j - g.2 j)

/-- One exact butterfly on address bit `P`, on numerators. -/
def bflyRecs (P : ℕ) (fs : List (Rec r)) : List (Rec r) :=
  List.ofFn fun y : Fin fs.length =>
    if bitAt y P = 0 then addRec (fs.getD y 0) (fs.getD (y + 2 ^ P) 0)
    else subRec (fs.getD (y - 2 ^ P) 0) (fs.getD y 0)

@[simp] theorem length_bflyRecs (P : ℕ) (fs : List (Rec r)) : (bflyRecs P fs).length = fs.length := by
  simp [bflyRecs]

theorem gridPoly_add (m : ℕ) (f g : Rec r) :
    gridPoly (m + 1) (addRec f g).1 (addRec f g).2 = (1 / 2 : ℂ) • (gridPoly m f.1 f.2 + gridPoly m g.1 g.2) := by
  funext j
  apply Complex.ext <;> simp [gridPoly, addRec, pow_succ] <;> ring

theorem gridPoly_sub (m : ℕ) (f g : Rec r) :
    gridPoly (m + 1) (subRec f g).1 (subRec f g).2 = (1 / 2 : ℂ) • (gridPoly m f.1 f.2 - gridPoly m g.1 g.2) := by
  funext j
  apply Complex.ext <;> simp [gridPoly, subRec, pow_succ] <;> ring

theorem arrayVec_getD (m : ℕ) (fs : List (Rec r)) (y : ℕ) :
    arrayVec m fs y = gridPoly m (fs.getD y 0).1 (fs.getD y 0).2 := by
  unfold arrayVec
  rw [List.getD_eq_getElem?_getD]
  cases fs[y]? with
  | none => funext j; simp [gridPoly]; rfl
  | some f => rfl

/-- On numerators, a butterfly on bit `P` of an array whose length is a multiple of `2^(P+1)`. -/
theorem arrayVec_bflyRecs (m P : ℕ) (fs : List (Rec r)) (hlen : 2 ^ (P + 1) ∣ fs.length) :
    arrayVec (m + 1) (bflyRecs P fs) = bfly P (arrayVec m fs) := by
  funext y
  rw [arrayVec_getD]
  by_cases hy : y < fs.length
  · have hgd : (bflyRecs P fs).getD y 0 = if bitAt y P = 0 then addRec (fs.getD y 0) (fs.getD (y + 2 ^ P) 0)
        else subRec (fs.getD (y - 2 ^ P) 0) (fs.getD y 0) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hy)]
      simp [bflyRecs, List.getElem?_eq_getElem hy]
    rw [hgd]
    unfold bfly
    split_ifs
    · rw [gridPoly_add, arrayVec_getD, arrayVec_getD]
    · rw [gridPoly_sub, arrayVec_getD, arrayVec_getD]
  · -- outside the array both sides vanish
    have hgd : (bflyRecs P fs).getD y 0 = 0 := by
      rw [List.getD_eq_default _ _ (by simpa using hy)]
    rw [hgd]
    obtain ⟨c, hc⟩ := hlen
    have hout : ∀ z, fs.length ≤ z → arrayVec m fs z = 0 := fun z hz => by
      rw [arrayVec_getD, List.getD_eq_default _ _ hz]; funext j; simp [gridPoly]; rfl
    have hz0 : gridPoly (m + 1) (0 : Rec r).1 (0 : Rec r).2 = 0 := by funext j; simp [gridPoly]; rfl
    rw [hz0]
    unfold bfly
    split_ifs with hb
    · rw [hout y (not_lt.mp hy), hout (y + 2 ^ P) (le_trans (not_lt.mp hy) (Nat.le_add_right _ _))]; simp
    · have hP : 2 ^ P ≤ y - fs.length := by
        -- bit `P` of `y` is that of `y - fs.length`, a multiple of `2^(P+1)` being removed
        have hy' : y = (y - fs.length) + 2 ^ (P + 1) * c := by omega
        have hb' : bitAt (y - fs.length) P ≠ 0 := by
          intro h0; apply hb
          rw [hy']; unfold bitAt at h0 ⊢
          rw [pow_succ, Nat.mul_assoc, Nat.add_mul_div_left _ _ (by positivity)]
          omega
        unfold bitAt at hb'
        by_contra hlt
        rw [Nat.div_eq_of_lt (by omega)] at hb'
        simp at hb'
      rw [hout (y - 2 ^ P) (by omega), hout y (by omega)]; simp

/-- Exact butterflies on a list of bits. -/
def bflysRecs : List ℕ → List (Rec r) → List (Rec r)
  | [], fs => fs
  | P :: Ps, fs => bflysRecs Ps (bflyRecs P fs)

@[simp] theorem length_bflysRecs : ∀ (Ps : List ℕ) (fs : List (Rec r)), (bflysRecs Ps fs).length = fs.length
  | [], _ => rfl
  | P :: Ps, fs => by rw [bflysRecs, length_bflysRecs, length_bflyRecs]

theorem arrayVec_bflysRecs : ∀ (Ps : List ℕ) (m : ℕ) (fs : List (Rec r)),
    (∀ P ∈ Ps, 2 ^ (P + 1) ∣ fs.length) →
    arrayVec (m + Ps.length) (bflysRecs Ps fs) = bflys Ps (arrayVec m fs)
  | [], m, fs, _ => by simp [bflysRecs, bflys, run]
  | P :: Ps, m, fs, h => by
    rw [bflysRecs, List.length_cons, show m + (Ps.length + 1) = (m + 1) + Ps.length by ring,
      arrayVec_bflysRecs Ps (m + 1) _ (fun Q hQ => by rw [length_bflyRecs]; exact h Q (by simp [hQ])),
      arrayVec_bflyRecs m P fs (h P (by simp))]
    rfl

/-! ### One truncation -/

/-- Truncation toward zero of the numerators by `2^s`. -/
noncomputable def truncRec (s : ℕ) (f : Rec r) : Rec r :=
  (fun j => rho0 ((f.1 j : ℝ) / 2 ^ s), fun j => rho0 ((f.2 j : ℝ) / 2 ^ s))

theorem arrayVec_truncRecs (p s : ℕ) (gs : List (Rec r)) :
    arrayVec p (gs.map (truncRec s)) = roundArr p (arrayVec (p + s) gs) := by
  funext y k
  simp only [roundArr]
  rw [arrayVec_getD, arrayVec_getD]
  by_cases hy : y < gs.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hy), List.getD_eq_getElem _ _ hy]
    simp only [List.getElem_map, truncRec, gridPoly]
    apply Complex.ext <;> simp [rhoC_re, rhoC_im, pow_add] <;> congr 2 <;> field_simp
  · rw [List.getD_eq_default _ _ (by simpa using hy), List.getD_eq_default _ _ (by omega)]
    apply Complex.ext <;> simp [gridPoly, rhoC_re, rhoC_im, rho0]

/-! ### The prefix slots in the paper's layout -/

/-- In the paper's layout, prefix slot `h < (ℓ-1) mod K` of axis `i` sits at physical bit
`DqK + hD + (D-1-i)`, `q = (ℓ-1)/K`. -/
theorem paperPerm_σ_prefix {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {h i : ℕ}
    (hh : h < (ℓ - 1) % K) (hi : i < ts.length) :
    (paperPerm hL).σ (axOff ts i + h) =
      ts.length * ((ℓ - 1) / K) * K + h * ts.length + (ts.length - 1 - i) := by
  set D := ts.length
  set B := D * ((ℓ - 1) / K) * K
  set Q := B + h * D + (D - 1 - i) with hQdef
  have hD : 0 < D := by omega
  have hsub : Q - B = (D - 1 - i) + D * h := by rw [hQdef]; ring_nf; omega
  have hmod : (Q - B) % D = D - 1 - i := by
    rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (Q - B) / D = h := by
    rw [hsub, Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt (by omega), zero_add]
  have hlt1 : ¬ Q < B := by omega
  have hlt2 : Q < B + D * ((ℓ - 1) % K) := by
    have hb1 : (h + 1) * D ≤ ((ℓ - 1) % K) * D := Nat.mul_le_mul_right _ (by omega)
    have e1 : (h + 1) * D = h * D + D := by ring
    have e2 : D * ((ℓ - 1) % K) = ((ℓ - 1) % K) * D := Nat.mul_comm _ _
    omega
  have hslot : paperSlot ts ℓ K Q = (i, h) := by
    unfold paperSlot
    rw [if_neg hlt1, if_pos hlt2, hmod, hdiv]
    simp only [Prod.mk.injEq, and_true]
    omega
  have htau : paperTau ts ℓ K Q = axOff ts i + h := by unfold paperTau; rw [hslot]
  have hn : Q < Nat.log 2 ts.prod := by
    rw [log_prod_layout hL]
    change Q < B + D * ((ℓ - 1) % K) + (longs ts ℓ).length
    omega
  rw [← htau]
  exact BitPerm.ofTau_σ hn

/-- The bits of a prefix round: all `D` bits from `DqK + hD`, last axis first. -/
theorem paper_slotBits_prefix {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {h : ℕ}
    (hh : h < (ℓ - 1) % K) :
    slotBits (paperPerm hL) ts (slotAxes ts h) h =
      (List.range ts.length).map fun i => ts.length * ((ℓ - 1) / K) * K + h * ts.length + (ts.length - 1 - i) := by
  have hb : (ℓ - 1) % K ≤ ℓ - 1 := Nat.mod_le _ _
  rw [slotAxes_below_top hL (by omega)]
  unfold slotBits
  apply List.map_congr_left
  intro i hi
  exact paperPerm_σ_prefix hL hh (List.mem_range.mp hi)

theorem bflys_cons (P : ℕ) (Ps : List ℕ) (z : ℕ → Fin r → ℂ) : bflys (P :: Ps) z = bflys Ps (bfly P z) := rfl

/-- Butterflies on distinct bits may be applied in any order. -/
theorem bflys_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) (hnd : l₁.Nodup) (z : ℕ → Fin r → ℂ) :
    bflys l₁ z = bflys l₂ z := by
  induction h generalizing z with
  | nil => rfl
  | cons x _ ih => rw [bflys_cons, bflys_cons, ih (List.nodup_cons.mp hnd).2]
  | swap x y l =>
    rw [bflys_cons, bflys_cons, bflys_cons, bflys_cons, bfly_comm]
    intro e; subst e; simp at hnd
  | trans h₁ _ ih₁ ih₂ => rw [ih₁ hnd, ih₂ (h₁.nodup_iff.mp hnd)]

theorem range_map_rev (s D : ℕ) :
    ((List.range D).map fun i => s + (D - 1 - i)).Perm ((List.range D).map (s + ·)) := by
  have : (List.range D).map (fun i => s + (D - 1 - i)) = ((List.range D).map (s + ·)).reverse := by
    apply List.ext_getElem (by simp)
    intro n h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_map, List.length_range]
  rw [this]; exact List.reverse_perm _

/-- The first physical bit of prefix slot `h`. -/
def prefixBase (D ℓ K h : ℕ) : ℕ := D * ((ℓ - 1) / K) * K + h * D

/-- `prefix_round_eq`: in the paper's layout the computed round of prefix slot `h` (exact round,
then rounding at `p`) is: exact butterflies on the numerators of the `D` bits from `prefixBase`,
one truncation by `2^D`, then the round's twist. -/
theorem prefix_round_eq [NeZero r] {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {h : ℕ}
    (hh : h < (ℓ - 1) % K) (p : ℕ) (fs : List (Rec r)) (hlen : fs.length = ts.prod) :
    roundArr p (slotRound (paperPerm hL) ts h (arrayVec p fs)) =
      twist (slotExp (paperPerm hL) r ts (slotAxes ts h) h)
        (arrayVec p ((bflysRecs ((List.range ts.length).map (prefixBase ts.length ℓ K h + ·)) fs).map
          (truncRec ts.length))) := by
  set D := ts.length
  set s := prefixBase D ℓ K h
  unfold slotRound
  rw [roundArr_twist]
  congr 1
  rw [arrayVec_truncRecs]
  congr 1
  have hbits := paper_slotBits_prefix hL hh
  rw [hbits]
  have hfun : (fun i => ts.length * ((ℓ - 1) / K) * K + h * ts.length + (ts.length - 1 - i)) =
      fun i => s + (D - 1 - i) := by
    funext i; simp only [s, prefixBase, D]
  rw [hfun]
  have hnd : ((List.range D).map fun i => s + (D - 1 - i)).Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro x hx y hy e
    simp only [List.mem_range] at hx hy
    omega
  rw [bflys_perm (range_map_rev s D) hnd]
  rw [show p + D = p + ((List.range D).map (s + ·)).length by simp]
  refine (arrayVec_bflysRecs _ p fs ?_).symm
  -- every bit lies below `log₂ M`
  intro P hP
  simp only [List.mem_map, List.mem_range] at hP
  obtain ⟨j, hj, rfl⟩ := hP
  obtain ⟨-, hM⟩ := axes_zeros (ts := ts) (fun t ht => by obtain ⟨a, ha, -⟩ := hL.1 t ht; exact ⟨a, ha⟩)
  rw [hlen, hM]
  apply Nat.pow_dvd_pow
  have hlog : Nat.log 2 ts.prod = D * ((ℓ - 1) / K) * K + D * ((ℓ - 1) % K) + (longs ts ℓ).length :=
    log_prod_layout hL
  have : s + j + 1 ≤ D * ((ℓ - 1) / K) * K + D * ((ℓ - 1) % K) := by
    have hb1 : (h + 1) * D ≤ ((ℓ - 1) % K) * D := Nat.mul_le_mul_right _ (by omega)
    have e1 : (h + 1) * D = h * D + D := by ring
    have e2 : D * ((ℓ - 1) % K) = ((ℓ - 1) % K) * D := Nat.mul_comm _ _
    simp only [s, prefixBase]
    omega
  omega

end IntegerMultBounds.Schoenhage
