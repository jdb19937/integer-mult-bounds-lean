module

public import IntegerMultBounds.MathlibTM2.Node.OffPrep
public import IntegerMultBounds.MathlibTM2.Node.RepairPass

/-!
# The exceptional set of the compact slot XOR, by automata

An index of the compact slot XOR (`IntegerMultBounds.MathlibTM2.Layer.CompactXor.GoodE`,
`GoodL`) is exceptional when a used radix-`2^G` digit of a temporary field is `2^G - 1` or the
guard of a used segment of the target slot leaves `[2^{G+1}, 2^{K-1} - 1 - 2^{G+1}]`. Both are
checked by two-input code automata (`Host.CAuto`) reading a field beside a constant mask:

* `onesAuto` reads `(F, M)` where the runs of equal bits of `M` delimit the digits of `F`
  (`M` alternates every `G` bits); it outputs `1` when some run of `F` is all ones
  (`onesAuto_eval`).
* `guardAuto` reads `(Y, M)` where the runs of ones of `M` are the high guard bits
  `[ρ + cK + G + 2, ρ + cK + K)` of the used segments; it outputs `1` when some run of `Y` is
  all zeros or all ones (`guardAuto_eval`), that is when a guard leaves the range.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.PackedXor
  IntegerMultBounds.MathlibTM2.Layer.CompactXor

/-! ### Runs of all ones -/

section Ones

/-- The state: whether a column was read, the current mask bit, whether the current run of the
field is all ones so far, and whether a closed run was all ones. -/
structure OSt where
  started : Bool
  cur : Bool
  allOnes : Bool
  bad : Bool
  deriving DecidableEq

/-- One column `(f, m)`. -/
def oStep (s : OSt) (col : Fin 2 → Bool) : OSt :=
  if !s.started then ⟨true, col 1, col 0, false⟩
  else if col 1 = s.cur then { s with allOnes := s.allOnes && col 0 }
  else ⟨true, col 1, col 0, s.bad || s.allOnes⟩

/-- The output: a closed run was all ones, or the current run is. -/
def oOut (s : OSt) : Fin 2 := if s.bad || (s.started && s.allOnes) then 1 else 0

def OSt.code (s : OSt) : ℕ :=
  s.started.toNat + 2 * s.cur.toNat + 4 * s.allOnes.toNat + 8 * s.bad.toNat

lemma OSt.code_lt (s : OSt) : s.code < 16 := by
  obtain ⟨a, b, c, d⟩ := s
  cases a <;> cases b <;> cases c <;> cases d <;> decide

def oEnc {A : ℕ} (s : OSt) : Fin (A + 4) := ⟨s.code % (A + 4), Nat.mod_lt _ (by omega)⟩

def oDec {A : ℕ} (x : Fin (A + 4)) : OSt :=
  ⟨x.val.testBit 0, x.val.testBit 1, x.val.testBit 2, x.val.testBit 3⟩

lemma oDec_oEnc {A : ℕ} (hA : 12 ≤ A) (s : OSt) : oDec (oEnc (A := A) s) = s := by
  have h := s.code_lt
  simp only [oDec, oEnc, Nat.mod_eq_of_lt (show s.code < A + 4 by omega)]
  obtain ⟨a, b, c, d⟩ := s
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- The automaton of runs of all ones. -/
def onesAuto (A : ℕ) : CAuto A 2 2 := absAuto oEnc oDec ⟨false, false, false, false⟩ oStep oOut

/-- The fold of `oStep` over the positions `0, …, t - 1`. -/
def oFold (F M : ℕ) (t : ℕ) : OSt :=
  (List.range t).foldl (fun s u => oStep s ![F.testBit u, M.testBit u]) ⟨false, false, false, false⟩

lemma oFold_succ (F M t : ℕ) :
    oFold F M (t + 1) = oStep (oFold F M t) ![F.testBit t, M.testBit t] := by
  unfold oFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- All positions `u < t` of run `r` carry a one. -/
def RunOnes (F : ℕ) (rid : ℕ → ℕ) (r t : ℕ) : Prop := ∀ u < t, rid u = r → F.testBit u = true

variable {rid : ℕ → ℕ} (hrid0 : rid 0 = 0) (hrid : ∀ t, rid (t + 1) = rid t ∨ rid (t + 1) = rid t + 1)
include hrid0 hrid

lemma rid_mono (u v : ℕ) (huv : u ≤ v) : rid u ≤ rid v := by
  induction v with
  | zero => rw [Nat.le_zero.mp huv]
  | succ v ih =>
      rcases Nat.lt_or_ge u (v + 1) with h | h
      · have := ih (by omega)
        rcases hrid v with h' | h' <;> omega
      · rw [Nat.le_antisymm huv h]

lemma rid_le (t : ℕ) : rid t ≤ t := by
  induction t with
  | zero => omega
  | succ t ih => rcases hrid t with h | h <;> omega

/-- Every run index up to `rid t` is attained at a position `≤ t`. -/
lemma rid_surj (t r : ℕ) (hr : r ≤ rid t) : ∃ u ≤ t, rid u = r := by
  induction t with
  | zero => exact ⟨0, le_rfl, by rw [hrid0] at hr ⊢; omega⟩
  | succ t ih =>
      rcases hrid t with h | h
      · obtain ⟨u, hu, hu'⟩ := ih (by omega)
        exact ⟨u, by omega, hu'⟩
      · rcases Nat.lt_or_ge r (rid (t + 1)) with h' | h'
        · obtain ⟨u, hu, hu'⟩ := ih (by omega)
          exact ⟨u, by omega, hu'⟩
        · exact ⟨t + 1, le_rfl, by omega⟩

/-- Positions of a run `r < rid t` lie below `t`. -/
lemma rid_lt_of_lt (t u : ℕ) (hu : rid u < rid t) : u < t := by
  by_contra h
  have := rid_mono hrid0 hrid t u (by omega)
  omega

omit hrid0 in
/-- Adjacent mask bits agree exactly when the run index does not change. -/
lemma mask_flip (M L : ℕ) (hM : ∀ t < L, M.testBit t = decide (rid t % 2 = 1)) (t : ℕ)
    (ht : t + 1 < L) :
    (M.testBit (t + 1) = M.testBit t) ↔ rid (t + 1) = rid t := by
  rw [hM _ ht, hM _ (by omega)]
  rcases hrid t with h | h
  · simp [h]
  · rw [h]
    constructor
    · intro e
      exfalso
      rcases Nat.mod_two_eq_zero_or_one (rid t) with h0 | h1
      · rw [Nat.add_mod, h0] at e; simp at e
      · rw [Nat.add_mod, h1] at e; simp at e
    · omega

/-- The invariant of the fold after `t ≥ 1` columns. -/
lemma oFold_inv (F M L : ℕ) (hM : ∀ t < L, M.testBit t = decide (rid t % 2 = 1)) :
    ∀ t, 1 ≤ t → t ≤ L →
      (oFold F M t).started = true ∧
      (oFold F M t).cur = M.testBit (t - 1) ∧
      ((oFold F M t).allOnes = true ↔ RunOnes F rid (rid (t - 1)) t) ∧
      ((oFold F M t).bad = true ↔ ∃ r < rid (t - 1), RunOnes F rid r t) := by
  intro t ht htL
  induction t with
  | zero => omega
  | succ t ih =>
      rcases Nat.eq_zero_or_pos t with rfl | hpos
      · -- the first column
        rw [oFold_succ]
        simp only [oFold, List.range_zero, List.foldl_nil, oStep, Bool.not_false, ↓reduceIte,
          Nat.add_sub_cancel, hrid0, RunOnes, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        refine ⟨by first | trivial | rfl, by first | trivial | rfl, ?_, ?_⟩
        · constructor
          · intro h u hu _
            have : u = 0 := by omega
            subst this; exact h
          · intro h; exact h 0 (by omega) hrid0
        · simp
      · obtain ⟨hs, hc, ha, hb⟩ := ih hpos (by omega)
        rw [oFold_succ]
        have ht' : t - 1 + 1 = t := by omega
        simp only [Nat.add_sub_cancel]
        by_cases hflip : M.testBit t = M.testBit (t - 1)
        · -- same run
          have hsame : rid t = rid (t - 1) := by
            have := (mask_flip hrid M L hM (t - 1) (by omega)).1 (by rw [ht']; exact hflip)
            rwa [ht'] at this
          simp only [oStep, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_one,
            Matrix.cons_val_fin_one, hc, hflip, Matrix.cons_val_zero, Bool.and_eq_true]
          refine ⟨by first | trivial | rfl, by first | trivial | rfl, ?_, ?_⟩
          · rw [ha, hsame]
            constructor
            · rintro ⟨h1, h2⟩ u hu hr
              rcases Nat.lt_or_ge u t with h | h
              · exact h1 u h hr
              · have : u = t := by omega
                subst this; exact h2
            · intro h
              exact ⟨fun u hu hr => h u (by omega) hr, h t (by omega) hsame⟩
          · rw [hb, hsame]
            constructor
            · rintro ⟨r, hr, h⟩
              refine ⟨r, hr, fun u hu hr' => ?_⟩
              rcases Nat.lt_or_ge u t with h' | h'
              · exact h u h' hr'
              · have : u = t := by omega
                subst this; omega
            · rintro ⟨r, hr, h⟩
              exact ⟨r, hr, fun u hu hr' => h u (by omega) hr'⟩
        · -- a new run
          have hnew : rid t = rid (t - 1) + 1 := by
            have h1 := (mask_flip hrid M L hM (t - 1) (by omega))
            rw [ht'] at h1
            rcases hrid (t - 1) with h | h
            · rw [ht'] at h; exact absurd (h1.2 h) hflip
            · rwa [ht'] at h
          simp only [oStep, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Matrix.cons_val_one,
            Matrix.cons_val_fin_one, hc, hflip, Matrix.cons_val_zero, Bool.or_eq_true]
          refine ⟨by first | trivial | rfl, by first | trivial | rfl, ?_, ?_⟩
          · constructor
            · intro h u hu hr
              rcases Nat.lt_or_ge u t with h' | h'
              · exfalso
                have := rid_mono hrid0 hrid u (t - 1) (by omega)
                omega
              · have : u = t := by omega
                subst this; exact h
            · intro h; exact h t (by omega) rfl
          · rw [hb, ha, hnew]
            constructor
            · rintro (⟨r, hr, h⟩ | h)
              · refine ⟨r, by omega, fun u hu hr' => ?_⟩
                rcases Nat.lt_or_ge u t with h' | h'
                · exact h u h' hr'
                · have : u = t := by omega
                  subst this; omega
              · refine ⟨rid (t - 1), by omega, fun u hu hr' => ?_⟩
                rcases Nat.lt_or_ge u t with h' | h'
                · exact h u h' hr'
                · have : u = t := by omega
                  subst this; omega
            · rintro ⟨r, hr, h⟩
              rcases Nat.lt_or_ge r (rid (t - 1)) with h' | h'
              · exact Or.inl ⟨r, h', fun u hu hr' => h u (by omega) hr'⟩
              · have : r = rid (t - 1) := by omega
                subst this
                exact Or.inr fun u hu hr' => h u (by omega) hr'

open Classical in
/-- **The runs-of-ones automaton** on a field `F` and a mask `M` alternating with the run index
`rid`: it outputs `1` exactly when some run attained below `L` is all ones. -/
theorem onesAuto_eval {A : ℕ} (hA : 12 ≤ A) (F M L : ℕ)
    (hM : ∀ t < L, M.testBit t = decide (rid t % 2 = 1)) (hL : 1 ≤ L) :
    (onesAuto A).eval L ![F, M] =
      if ∃ r ≤ rid (L - 1), RunOnes F rid r L then 1 else 0 := by
  unfold onesAuto
  rw [absAuto_eval _ _ (oDec_oEnc hA)]
  have hfold : (List.range L).foldl (fun s t => oStep s fun r => (![F, M] r).testBit t)
      ⟨false, false, false, false⟩ = oFold F M L := by
    unfold oFold
    congr 1
  rw [hfold]
  clear hfold
  obtain ⟨hs, -, ha, hb⟩ := oFold_inv hrid0 hrid F M L hM L hL le_rfl
  unfold oOut
  rw [hs, Bool.true_and]
  by_cases h : ∃ r ≤ rid (L - 1), RunOnes F rid r L
  · rw [if_pos h, if_pos]
    obtain ⟨r, hr, hrun⟩ := h
    rcases Nat.lt_or_ge r (rid (L - 1)) with h' | h'
    · rw [Bool.or_eq_true, hb]; exact Or.inl ⟨r, h', hrun⟩
    · rw [Bool.or_eq_true, ha]; right
      have : r = rid (L - 1) := by omega
      subst this; exact hrun
  · rw [if_neg h, if_neg]
    rw [Bool.or_eq_true, hb, ha]
    rintro (⟨r, hr, hrun⟩ | hrun)
    · exact h ⟨r, by omega, hrun⟩
    · exact h ⟨_, le_rfl, hrun⟩

end Ones

section Digits

/-- Bit `u` of `F < 2^m` with `m ≤ u` is `0`. -/
lemma testBit_of_lt_pow {F m u : ℕ} (hF : F < 2 ^ m) (hu : m ≤ u) : F.testBit u = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hF (Nat.pow_le_pow_right (by norm_num) hu))

open Classical in
/-- **Digits all ones.** On a field `F < 2^{nG}` and the mask alternating every `G` bits, the
automaton outputs `1` exactly when a used digit of `F` is `2^G - 1`. -/
theorem onesAuto_eval_digits {A : ℕ} (hA : 12 ≤ A) {G : ℕ} (hG : 1 ≤ G) (F M L n : ℕ)
    (hM : ∀ t < L, M.testBit t = decide (t / G % 2 = 1)) (hL : n * G ≤ L) (hL1 : 1 ≤ L)
    (hF : F < 2 ^ (n * G)) :
    (onesAuto A).eval L ![F, M] =
      if ∃ c < n, F / 2 ^ (c * G) % 2 ^ G = 2 ^ G - 1 then 1 else 0 := by
  have hrid0 : (0 : ℕ) / G = 0 := Nat.zero_div G
  have hrid : ∀ t, (t + 1) / G = t / G ∨ (t + 1) / G = t / G + 1 := by
    intro t
    rw [Nat.succ_div]
    split_ifs <;> simp
  rw [onesAuto_eval hrid0 hrid hA F M L hM hL1]
  congr 1
  apply propext
  constructor
  · rintro ⟨r, hr, hrun⟩
    have hrG : r * G ≤ L - 1 := (Nat.le_div_iff_mul_le (by omega)).1 hr
    rcases Nat.lt_or_ge r n with hrn | hrn
    · refine ⟨r, hrn, (mod_eq_max_iff_bits F (r * G) G).2 ?_⟩
      rw [List.all_eq_true]
      intro u hu
      rw [List.mem_range] at hu
      apply hrun (r * G + u)
      · have : (r + 1) * G ≤ n * G := Nat.mul_le_mul_right G hrn
        rw [Nat.add_mul, one_mul] at this
        omega
      · show (r * G + u) / G = r
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hu, Nat.zero_add]
    · exfalso
      have h1 := hrun (r * G) (by omega) (Nat.mul_div_cancel _ (by omega))
      have h2 : F.testBit (r * G) = false :=
        testBit_of_lt_pow hF (Nat.mul_le_mul_right G hrn)
      rw [h1] at h2
      exact Bool.noConfusion h2
  · rintro ⟨c, hc, hdig⟩
    have hall := (mod_eq_max_iff_bits F (c * G) G).1 hdig
    rw [List.all_eq_true] at hall
    have hcG : (c + 1) * G ≤ n * G := Nat.mul_le_mul_right G hc
    rw [Nat.add_mul, one_mul] at hcG
    refine ⟨c, (Nat.le_div_iff_mul_le (by omega)).2 (by omega), fun u hu hr => ?_⟩
    have hu' : u = c * G + u % G := by
      have := Nat.div_add_mod u G
      have hr' : u / G = c := hr
      rw [hr', Nat.mul_comm] at this
      omega
    rw [hu']
    exact hall (u % G) (List.mem_range.2 (Nat.mod_lt _ (by omega)))

end Digits

/-! ### Runs of all zeros or all ones -/

section Guards

/-- The state: whether the previous mask bit was one (a run is open), whether the open run of
the field is all zeros so far, all ones so far, and whether a closed run was all zeros or all
ones. -/
structure GSt where
  inRun : Bool
  allZ : Bool
  allO : Bool
  bad : Bool
  deriving DecidableEq

/-- One column `(y, m)`. -/
def gStep (s : GSt) (col : Fin 2 → Bool) : GSt :=
  if col 1 then
    (if s.inRun then { s with allZ := s.allZ && !col 0, allO := s.allO && col 0 }
      else ⟨true, !col 0, col 0, s.bad⟩)
  else if s.inRun then ⟨false, false, false, s.bad || s.allZ || s.allO⟩ else s

/-- The output: a closed run was all zeros or all ones, or the open run is. -/
def gOut (s : GSt) : Fin 2 := if s.bad || (s.inRun && (s.allZ || s.allO)) then 1 else 0

def GSt.code (s : GSt) : ℕ :=
  s.inRun.toNat + 2 * s.allZ.toNat + 4 * s.allO.toNat + 8 * s.bad.toNat

lemma GSt.code_lt (s : GSt) : s.code < 16 := by
  obtain ⟨a, b, c, d⟩ := s
  cases a <;> cases b <;> cases c <;> cases d <;> decide

def gEnc {A : ℕ} (s : GSt) : Fin (A + 4) := ⟨s.code % (A + 4), Nat.mod_lt _ (by omega)⟩

def gDec {A : ℕ} (x : Fin (A + 4)) : GSt :=
  ⟨x.val.testBit 0, x.val.testBit 1, x.val.testBit 2, x.val.testBit 3⟩

lemma gDec_gEnc {A : ℕ} (hA : 12 ≤ A) (s : GSt) : gDec (gEnc (A := A) s) = s := by
  have h := s.code_lt
  simp only [gDec, gEnc, Nat.mod_eq_of_lt (show s.code < A + 4 by omega)]
  obtain ⟨a, b, c, d⟩ := s
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- The automaton of runs of all zeros or all ones. -/
def guardAuto (A : ℕ) : CAuto A 2 2 := absAuto gEnc gDec ⟨false, false, false, false⟩ gStep gOut

/-- The fold of `gStep` over the positions `0, …, t - 1`. -/
def gFold (Y M : ℕ) (t : ℕ) : GSt :=
  (List.range t).foldl (fun s u => gStep s ![Y.testBit u, M.testBit u]) ⟨false, false, false, false⟩

lemma gFold_succ (Y M t : ℕ) :
    gFold Y M (t + 1) = gStep (gFold Y M t) ![Y.testBit t, M.testBit t] := by
  unfold gFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

variable (K ρ G n : ℕ)

/-- Position `t` is a high guard bit of a used segment: `ρ + cK + G + 2 ≤ t < ρ + cK + K`. -/
def InHigh (t : ℕ) : Prop := ∃ c < n, ρ + c * K + G + 2 ≤ t ∧ t < ρ + c * K + K

instance (t : ℕ) : Decidable (InHigh K ρ G n t) := by unfold InHigh; infer_instance

/-- The high guard bits of segment `c` below `t` are all `b`. -/
def HighAll (Y : ℕ) (c t : ℕ) (b : Bool) : Prop :=
  ∀ u, ρ + c * K + G + 2 ≤ u → u < ρ + c * K + K → u < t → Y.testBit u = b

variable {K ρ G n}

lemma inHigh_unique (hK : G + 3 ≤ K) {t c c' : ℕ} (hc : c < n) (hc' : c' < n)
    (h1 : ρ + c * K + G + 2 ≤ t) (h2 : t < ρ + c * K + K) (h1' : ρ + c' * K + G + 2 ≤ t)
    (h2' : t < ρ + c' * K + K) : c = c' := by
  rcases Nat.lt_trichotomy c c' with h | h | h
  · have := Nat.mul_le_mul_right K (show c + 1 ≤ c' by omega)
    rw [Nat.add_mul, one_mul] at this
    omega
  · exact h
  · have := Nat.mul_le_mul_right K (show c' + 1 ≤ c by omega)
    rw [Nat.add_mul, one_mul] at this
    omega

/-- The position just below the high run of segment `c` is in no high run. -/
lemma notInHigh_below (hK : G + 3 ≤ K) {c : ℕ} (hc : c < n) :
    ¬ InHigh K ρ G n (ρ + c * K + G + 1) := by
  rintro ⟨c', hc', h1, h2⟩
  rcases Nat.lt_trichotomy c c' with h | h | h
  · have := Nat.mul_le_mul_right K (show c + 1 ≤ c' by omega)
    rw [Nat.add_mul, one_mul] at this
    omega
  · subst h; omega
  · have := Nat.mul_le_mul_right K (show c' + 1 ≤ c by omega)
    rw [Nat.add_mul, one_mul] at this
    omega

/-- The position just above the high run of segment `c` is in no high run. -/
lemma notInHigh_above (hK : G + 3 ≤ K) {c : ℕ} (hc : c < n) :
    ¬ InHigh K ρ G n (ρ + c * K + K) := by
  rintro ⟨c', hc', h1, h2⟩
  rcases Nat.lt_trichotomy c c' with h | h | h
  · have := Nat.mul_le_mul_right K (show c + 1 ≤ c' by omega)
    rw [Nat.add_mul, one_mul] at this
    omega
  · subst h; omega
  · have := Nat.mul_le_mul_right K (show c' + 1 ≤ c by omega)
    rw [Nat.add_mul, one_mul] at this
    omega

/-- A closed run is not closing again at the next column. -/
lemma run_end_ne (hK : G + 3 ≤ K) {c t : ℕ} (hc : c < n) (hhigh : ¬ InHigh K ρ G n t) :
    ρ + c * K + K ≠ t + 1 := fun e => hhigh ⟨c, hc, by omega, by omega⟩

/-- The invariant of the fold after `t` columns. -/
lemma gFold_inv (hK : G + 3 ≤ K) (Y M L : ℕ)
    (hM : ∀ t < L, M.testBit t = decide (InHigh K ρ G n t)) :
    ∀ t ≤ L,
      ((gFold Y M t).inRun = true ↔ 0 < t ∧ InHigh K ρ G n (t - 1)) ∧
      (∀ c < n, ρ + c * K + G + 2 ≤ t - 1 → t - 1 < ρ + c * K + K → 0 < t →
        ((gFold Y M t).allZ = true ↔ HighAll K ρ G Y c t false) ∧
        ((gFold Y M t).allO = true ↔ HighAll K ρ G Y c t true)) ∧
      ((gFold Y M t).bad = true ↔
        ∃ c < n, ρ + c * K + K < t ∧ (HighAll K ρ G Y c t false ∨ HighAll K ρ G Y c t true)) := by
  intro t htL
  induction t with
  | zero =>
      refine ⟨⟨fun h => Bool.noConfusion h, fun h => absurd h.1 (Nat.lt_irrefl 0)⟩,
        fun c hc h1 h2 h0 => absurd h0 (Nat.lt_irrefl 0), ⟨fun h => Bool.noConfusion h, ?_⟩⟩
      rintro ⟨c, hc, h, -⟩
      omega
  | succ t ih =>
      obtain ⟨hin, hrun, hbad⟩ := ih (by omega)
      rw [gFold_succ]
      simp only [Nat.add_sub_cancel]
      have hMt := hM t (by omega)
      set s := gFold Y M t with hs
      -- extending a run
      have hext : ∀ {c : ℕ}, c < n → ρ + c * K + G + 2 ≤ t → t < ρ + c * K + K → ∀ b : Bool,
          (HighAll K ρ G Y c t b ∧ Y.testBit t = b) ↔ HighAll K ρ G Y c (t + 1) b := by
        intro c hc hc1 hc2 b
        constructor
        · rintro ⟨h, h'⟩ u hu1 hu2 hu3
          rcases Nat.lt_or_ge u t with hut | hut
          · exact h u hu1 hu2 hut
          · have : u = t := by omega
            subst this; exact h'
        · intro h
          exact ⟨fun u h1 h2 h3 => h u h1 h2 (by omega), h t hc1 hc2 (by omega)⟩
      -- a full run below `t` is a full run below `t + 1` and back
      have hfull : ∀ {c : ℕ}, c < n → ρ + c * K + K ≤ t → ∀ b : Bool,
          HighAll K ρ G Y c t b ↔ HighAll K ρ G Y c (t + 1) b := by
        intro c hc hct b
        constructor
        · intro h u a b' d
          exact h u a b' (by omega)
        · intro h u a b' d
          exact h u a b' (by omega)
      by_cases hhigh : InHigh K ρ G n t
      · -- inside a high run
        obtain ⟨c, hc, hc1, hc2⟩ := hhigh
        have hm : M.testBit t = true := by rw [hMt]; exact decide_eq_true ⟨c, hc, hc1, hc2⟩
        by_cases hpre : InHigh K ρ G n (t - 1) ∧ 0 < t
        · -- the run continues
          obtain ⟨⟨c', hc', hc1', hc2'⟩, hpos⟩ := hpre
          have hnot : t ≠ ρ + c * K + G + 2 := by
            intro e
            apply notInHigh_below hK hc
            rw [show ρ + c * K + G + 1 = t - 1 by omega]
            exact ⟨c', hc', hc1', hc2'⟩
          have hcc : c' = c :=
            inHigh_unique hK hc' hc hc1' hc2' (by omega) (by omega)
          subst hcc
          have hin' : s.inRun = true := hin.2 ⟨hpos, c', hc', hc1', hc2'⟩
          obtain ⟨hz, ho⟩ := hrun c' hc' hc1' hc2' hpos
          have hst : gStep s ![Y.testBit t, M.testBit t] =
              ⟨true, s.allZ && !Y.testBit t, s.allO && Y.testBit t, s.bad⟩ := by
            simp [gStep, hm, hin']
          rw [hst]
          refine ⟨⟨fun _ => ⟨by omega, c', hc', hc1, hc2⟩, fun _ => rfl⟩, ?_, ?_⟩
          · intro c'' hc'' h1 h2 _
            have : c'' = c' := inHigh_unique hK hc'' hc' h1 h2 hc1 hc2
            subst this
            constructor
            · show (s.allZ && !Y.testBit t) = true ↔ _
              rw [Bool.and_eq_true, hz, Bool.not_eq_eq_eq_not, Bool.not_true]
              exact hext hc'' hc1 hc2 false
            · show (s.allO && Y.testBit t) = true ↔ _
              rw [Bool.and_eq_true, ho]
              exact hext hc'' hc1 hc2 true
          · show s.bad = true ↔ _
            rw [hbad]
            constructor
            · rintro ⟨c'', hc'', h1, h2⟩
              refine ⟨c'', hc'', by omega, ?_⟩
              rcases h2 with h2 | h2
              · exact Or.inl ((hfull hc'' h1.le false).1 h2)
              · exact Or.inr ((hfull hc'' h1.le true).1 h2)
            · rintro ⟨c'', hc'', h1, h2⟩
              have hne : ρ + c'' * K + K ≠ t := by
                intro e
                exact notInHigh_above hK hc'' (by rw [e]; exact ⟨c', hc', hc1, hc2⟩)
              refine ⟨c'', hc'', by omega, ?_⟩
              rcases h2 with h2 | h2
              · exact Or.inl ((hfull hc'' (by omega) false).2 h2)
              · exact Or.inr ((hfull hc'' (by omega) true).2 h2)
        · -- the run starts at `t`
          have hin' : s.inRun = false := by
            rw [← Bool.not_eq_true, hin]; tauto
          have hstart : t = ρ + c * K + G + 2 := by
            by_contra hne
            exact hpre ⟨⟨c, hc, by omega, by omega⟩, by omega⟩
          have hst : gStep s ![Y.testBit t, M.testBit t] =
              ⟨true, !Y.testBit t, Y.testBit t, s.bad⟩ := by
            simp [gStep, hm, hin']
          rw [hst]
          refine ⟨⟨fun _ => ⟨by omega, c, hc, hc1, hc2⟩, fun _ => rfl⟩, ?_, ?_⟩
          · intro c'' hc'' h1 h2 _
            have : c'' = c := inHigh_unique hK hc'' hc h1 h2 hc1 hc2
            subst this
            constructor
            · show (!Y.testBit t) = true ↔ _
              rw [Bool.not_eq_eq_eq_not, Bool.not_true]
              constructor
              · intro h u hu1 hu2 hu3
                have : u = t := by omega
                subst this; exact h
              · intro h; exact h t hc1 hc2 (by omega)
            · show Y.testBit t = true ↔ _
              constructor
              · intro h u hu1 hu2 hu3
                have : u = t := by omega
                subst this; exact h
              · intro h; exact h t hc1 hc2 (by omega)
          · show s.bad = true ↔ _
            rw [hbad]
            constructor
            · rintro ⟨c'', hc'', h1, h2⟩
              refine ⟨c'', hc'', by omega, ?_⟩
              rcases h2 with h2 | h2
              · exact Or.inl ((hfull hc'' h1.le false).1 h2)
              · exact Or.inr ((hfull hc'' h1.le true).1 h2)
            · rintro ⟨c'', hc'', h1, h2⟩
              have hne : ρ + c'' * K + K ≠ t := by
                intro e
                exact notInHigh_above hK hc'' (by rw [e]; exact ⟨c, hc, hc1, hc2⟩)
              refine ⟨c'', hc'', by omega, ?_⟩
              rcases h2 with h2 | h2
              · exact Or.inl ((hfull hc'' (by omega) false).2 h2)
              · exact Or.inr ((hfull hc'' (by omega) true).2 h2)
      · -- outside every high run
        have hm : M.testBit t = false := by rw [hMt]; exact decide_eq_false hhigh
        by_cases hpre : InHigh K ρ G n (t - 1) ∧ 0 < t
        · -- a run closes
          obtain ⟨⟨c, hc, hc1, hc2⟩, hpos⟩ := hpre
          have hend : t = ρ + c * K + K := by
            by_contra hne
            exact hhigh ⟨c, hc, by omega, by omega⟩
          have hin' : s.inRun = true := hin.2 ⟨hpos, c, hc, hc1, hc2⟩
          obtain ⟨hz, ho⟩ := hrun c hc hc1 hc2 hpos
          have hst : gStep s ![Y.testBit t, M.testBit t] =
              ⟨false, false, false, s.bad || s.allZ || s.allO⟩ := by
            simp [gStep, hm, hin']
          rw [hst]
          refine ⟨⟨fun h => Bool.noConfusion h, fun h => absurd h.2 hhigh⟩, ?_, ?_⟩
          · intro c'' hc'' h1 h2 _
            exact absurd ⟨c'', hc'', h1, h2⟩ hhigh
          · show (s.bad || s.allZ || s.allO) = true ↔ _
            rw [Bool.or_eq_true, Bool.or_eq_true, hbad, hz, ho]
            constructor
            · rintro ((⟨c'', hc'', h1, h2⟩ | h) | h)
              · refine ⟨c'', hc'', by omega, ?_⟩
                rcases h2 with h2 | h2
                · exact Or.inl ((hfull hc'' h1.le false).1 h2)
                · exact Or.inr ((hfull hc'' h1.le true).1 h2)
              · exact ⟨c, hc, by omega, Or.inl ((hfull hc (by omega) false).1 h)⟩
              · exact ⟨c, hc, by omega, Or.inr ((hfull hc (by omega) true).1 h)⟩
            · rintro ⟨c'', hc'', h1, h2⟩
              by_cases hcc : c'' = c
              · subst hcc
                rcases h2 with h2 | h2
                · exact Or.inl (Or.inr ((hfull hc (by omega) false).2 h2))
                · exact Or.inr ((hfull hc (by omega) true).2 h2)
              · have hne : ρ + c'' * K + K ≠ t := by
                  intro e
                  rw [hend] at e
                  have hmul : c'' * K = c * K := by omega
                  exact hcc (Nat.eq_of_mul_eq_mul_right (by omega) hmul)
                refine Or.inl (Or.inl ⟨c'', hc'', by omega, ?_⟩)
                rcases h2 with h2 | h2
                · exact Or.inl ((hfull hc'' (by omega) false).2 h2)
                · exact Or.inr ((hfull hc'' (by omega) true).2 h2)
        · -- nothing changes
          have hin' : s.inRun = false := by
            rw [← Bool.not_eq_true, hin]; tauto
          have hst : gStep s ![Y.testBit t, M.testBit t] = s := by
            simp [gStep, hm, hin']
          rw [hst]
          refine ⟨⟨fun h => absurd (hin.1 h) (fun h' => hpre ⟨h'.2, h'.1⟩),
            fun h => absurd h.2 hhigh⟩, ?_, ?_⟩
          · intro c'' hc'' h1 h2 _
            exact absurd ⟨c'', hc'', h1, h2⟩ hhigh
          · rw [hbad]
            constructor
            · rintro ⟨c'', hc'', h1, h2⟩
              refine ⟨c'', hc'', by omega, ?_⟩
              rcases h2 with h2 | h2
              · exact Or.inl ((hfull hc'' h1.le false).1 h2)
              · exact Or.inr ((hfull hc'' h1.le true).1 h2)
            · rintro ⟨c'', hc'', h1, h2⟩
              have hne : ρ + c'' * K + K ≠ t := by
                intro e
                exact hpre ⟨⟨c'', hc'', by omega, by omega⟩, by omega⟩
              refine ⟨c'', hc'', by omega, ?_⟩
              rcases h2 with h2 | h2
              · exact Or.inl ((hfull hc'' (by omega) false).2 h2)
              · exact Or.inr ((hfull hc'' (by omega) true).2 h2)

open Classical in
/-- **The guard automaton** on the slot `Y` and the mask of the high guard bits, over `L ≥ ρ + nK`
columns: it outputs `1` exactly when the high guard bits of some used segment are all zeros or
all ones. -/
theorem guardAuto_eval {A : ℕ} (hA : 12 ≤ A) (hK : G + 3 ≤ K) (Y M L : ℕ)
    (hM : ∀ t < L, M.testBit t = decide (InHigh K ρ G n t)) (hL : ρ + n * K ≤ L) :
    (guardAuto A).eval L ![Y, M] =
      if ∃ c < n, HighAll K ρ G Y c L false ∨ HighAll K ρ G Y c L true then 1 else 0 := by
  unfold guardAuto
  rw [absAuto_eval _ _ (gDec_gEnc hA)]
  have hfold : (List.range L).foldl (fun s t => gStep s fun r => (![Y, M] r).testBit t)
      ⟨false, false, false, false⟩ = gFold Y M L := by
    unfold gFold
    congr 1
  rw [hfold]
  clear hfold
  obtain ⟨hin, hrun, hbad⟩ := gFold_inv hK Y M L hM L le_rfl
  unfold gOut
  have hcomplete : ∀ c < n, ρ + c * K + K ≤ L := fun c hc => by
    have := Nat.mul_le_mul_right K (show c + 1 ≤ n by omega)
    rw [Nat.add_mul, one_mul] at this
    omega
  by_cases h : ∃ c < n, HighAll K ρ G Y c L false ∨ HighAll K ρ G Y c L true
  · rw [if_pos h, if_pos]
    obtain ⟨c, hc, hor⟩ := h
    rw [Bool.or_eq_true, hbad]
    rcases Nat.lt_or_ge (ρ + c * K + K) L with hlt | hge
    · exact Or.inl ⟨c, hc, hlt, hor⟩
    · have heq : ρ + c * K + K = L := le_antisymm (hcomplete c hc) hge
      right
      rw [Bool.and_eq_true, hin]
      have hpos : 0 < L := by omega
      obtain ⟨hz, ho⟩ := hrun c hc (by omega) (by omega) hpos
      refine ⟨⟨hpos, c, hc, by omega, by omega⟩, ?_⟩
      rw [Bool.or_eq_true, hz, ho]
      exact hor
  · rw [if_neg h, if_neg]
    rw [Bool.or_eq_true, hbad, Bool.and_eq_true, hin]
    rintro (⟨c, hc, -, hor⟩ | ⟨⟨hpos, c, hc, hc1, hc2⟩, hor⟩)
    · exact h ⟨c, hc, hor⟩
    · obtain ⟨hz, ho⟩ := hrun c hc hc1 hc2 hpos
      rw [Bool.or_eq_true, hz, ho] at hor
      exact h ⟨c, hc, hor⟩

end Guards


/-! ### The guard range -/

section GuardRange

variable {K ρ G : ℕ}

/-- Shifting a bit field: the high part of `a / 2^p % 2^w`. -/
lemma div_mod_pow_div (a p w v : ℕ) (hv : v ≤ w) :
    a / 2 ^ p % 2 ^ w / 2 ^ v = a / 2 ^ (p + v) % 2 ^ (w - v) := by
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  have e : t + v + p = t + (p + v) := by ring
  by_cases ht : t < w - v
  · have h1 : t + v < w := by omega
    simp only [ht, h1, decide_true, Bool.true_and, e]
  · have h1 : ¬ t + v < w := by omega
    simp only [ht, h1, decide_false, Bool.false_and]

/-- The high guard bits of segment `c` are all zeros or all ones exactly when the guard leaves
`[2^{G+1}, 2^{K-1} - 1 - 2^{G+1}]`. -/
lemma highAll_iff_not_guardOK (hK : G + 3 ≤ K) (Y c L : ℕ) (hc : ρ + c * K + K ≤ L) :
    (HighAll K ρ G Y c L false ∨ HighAll K ρ G Y c L true) ↔
      ¬ GuardOK K ρ (2 ^ (G + 1)) Y c := by
  set g := guard K ρ Y c with hg
  have hglt : g < 2 ^ (K - 1) := Nat.mod_lt _ (by positivity)
  have hsplit : 2 ^ (K - 1) = 2 ^ (K - G - 2) * 2 ^ (G + 1) := by
    rw [← pow_add]; congr 1; omega
  have e1 : ρ + c * K + 1 + (G + 1) = ρ + c * K + G + 2 := by ring
  have e2 : K - 1 - (G + 1) = K - G - 2 := by omega
  have hhigh : g / 2 ^ (G + 1) = Y / 2 ^ (ρ + c * K + G + 2) % 2 ^ (K - G - 2) := by
    rw [hg, IntegerMultBounds.MathlibTM2.Layer.PackedXor.guard,
      div_mod_pow_div Y (ρ + c * K + 1) (K - 1) (G + 1) (by omega), e1, e2]
  have hz : HighAll K ρ G Y c L false ↔ Y / 2 ^ (ρ + c * K + G + 2) % 2 ^ (K - G - 2) = 0 := by
    rw [mod_eq_zero_iff_bits, List.all_eq_true]
    constructor
    · intro h u hu
      rw [List.mem_range] at hu
      simpa using h (ρ + c * K + G + 2 + u) (by omega) (by omega) (by omega)
    · intro h u h1 h2 h3
      have := h (u - (ρ + c * K + G + 2)) (List.mem_range.2 (by omega))
      rw [show ρ + c * K + G + 2 + (u - (ρ + c * K + G + 2)) = u by omega] at this
      simpa using this
  have ho : HighAll K ρ G Y c L true ↔
      Y / 2 ^ (ρ + c * K + G + 2) % 2 ^ (K - G - 2) = 2 ^ (K - G - 2) - 1 := by
    rw [mod_eq_max_iff_bits, List.all_eq_true]
    constructor
    · intro h u hu
      rw [List.mem_range] at hu
      exact h (ρ + c * K + G + 2 + u) (by omega) (by omega) (by omega)
    · intro h u h1 h2 h3
      have := h (u - (ρ + c * K + G + 2)) (List.mem_range.2 (by omega))
      rwa [show ρ + c * K + G + 2 + (u - (ρ + c * K + G + 2)) = u by omega] at this
  rw [hz, ho, ← hhigh]
  unfold GuardOK
  rw [← hg]
  set W := 2 ^ (K - G - 2) with hW
  set e := 2 ^ (G + 1) with he
  have hWpos : 0 < W := by positivity
  have hepos : 0 < e := by positivity
  have hq := Nat.div_add_mod g e
  have hmod := Nat.mod_lt g hepos
  have hqlt : g / e < W := by
    rw [Nat.div_lt_iff_lt_mul hepos]; rw [hsplit] at hglt; exact hglt
  rw [hsplit]
  constructor
  · rintro (h | h)
    · rw [Nat.div_eq_zero_iff] at h
      rcases h with h | h
      · omega
      · intro ⟨h1, _⟩; omega
    · intro ⟨_, h2⟩
      have : (W - 1) * e ≤ g := by
        rw [← h]; exact Nat.div_mul_le_self g e
      have hW1 : W = (W - 1) + 1 := by omega
      rw [hW1, Nat.add_mul, one_mul] at h2
      omega
  · intro h
    rw [not_and_or, not_le, not_lt] at h
    rcases h with h | h
    · left
      rw [Nat.div_eq_zero_iff]
      exact Or.inr h
    · right
      have hW1 : W = (W - 1) + 1 := by omega
      have h' : (W - 1) * e ≤ g := by
        rw [hW1, Nat.add_mul, one_mul] at h; omega
      have h1 : W - 1 ≤ g / e := (Nat.le_div_iff_mul_le hepos).2 h'
      omega

end GuardRange

/-! ### The mask constants -/

section MaskValues

/-- The mask alternating every `G` bits, truncated to `L` bits. -/
def altMask (G L : ℕ) : ℕ := bitsMask (fun t => decide (t / G % 2 = 1)) L

lemma testBit_altMask (G L t : ℕ) (ht : t < L) :
    (altMask G L).testBit t = decide (t / G % 2 = 1) := by
  rw [altMask, testBit_bitsMask]; simp [ht]

/-- The mask of the high guard bits of the `n` used segments, truncated to `L` bits. -/
def highMask (K ρ G n L : ℕ) : ℕ := bitsMask (fun t => decide (InHigh K ρ G n t)) L

lemma testBit_highMask (K ρ G n L t : ℕ) (ht : t < L) :
    (highMask K ρ G n L).testBit t = decide (InHigh K ρ G n t) := by
  rw [highMask, testBit_bitsMask]; simp [ht]

lemma bitsMask_lt (p : ℕ → Bool) (n : ℕ) : bitsMask p n < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro t ht
  rw [testBit_bitsMask]
  simp [show ¬ t < n by omega]

lemma altMask_lt (G L : ℕ) : altMask G L < 2 ^ L := bitsMask_lt _ _

lemma highMask_lt (K ρ G n L : ℕ) : highMask K ρ G n L < 2 ^ L := bitsMask_lt _ _

end MaskValues

/-! ### Building the masks -/

section MaskBuild

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- One item: `|aR|` zeros then `|bR|` ones. -/
def segItem (aR bR cnt w t₂ : Fin T) : Pr P T Q A U :=
  .seq (scanR aR t₂ (emit cnt w false)) (scanR bR t₂ (emit cnt w true))

/-- `|kR|` items, scanning `kR` through the empty `t₁`. -/
theorem segItems_exec {kR aR bR cnt w t₁ t₂ : Fin T} (hreg : [kR, aR, bR, cnt, w, t₁, t₂].Nodup)
    {n X p₀ a b : ℕ} (R₀ : Regs T A) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = maskRegs cnt w n X R₀ p₀) (hal : (R₀ aR).length = a) (hbl : (R₀ bR).length = b)
    (ht₁ : R₀ t₁ = []) (ht₂ : R₀ t₂ = [])
    (hz : ∀ j < (R₀ kR).length, ∀ s < a, p₀ + (a + b) * j + s < n →
      X.testBit (p₀ + (a + b) * j + s) = false)
    (ho : ∀ j < (R₀ kR).length, ∀ s, a ≤ s → s < a + b → p₀ + (a + b) * j + s < n →
      X.testBit (p₀ + (a + b) * j + s) = true) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (R₀ kR).length * (4 * (a + b) + 13) + 4 ∧
      Exec body (scanP kR t₁ (segItem aR bR cnt w t₂)) (mk v S) m
        (mk v' { S with R := maskRegs cnt w n X R₀ (p₀ + (a + b) * (R₀ kR).length) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hka, hkb, hkc, hkw, hk1, hk2⟩, ⟨hab, hac, haw, ha1, ha2⟩, ⟨hbc, hbw, hb1, hb2⟩,
    ⟨hcw, hc1, hc2⟩, ⟨hw1, hw2⟩, h12⟩ := hreg'
  let Ψ : ℕ → Regs T A := fun j => maskRegs cnt w n X R₀ (p₀ + (a + b) * j)
  have hp : IterSpec body (segItem aR bR cnt w t₂) kR t₁ Ψ (fun _ => 4 * (a + b) + 8)
      (R₀ kR).length := by
    intro j hj v' S' hS'
    have hc' : S'.R cnt = List.replicate (n - (p₀ + (a + b) * j)) tick :=
      (hS' cnt hkc.symm hc1).trans (maskRegs_cnt hcw _ _)
    have hw' : S'.R w = (binSyms (min (p₀ + (a + b) * j) n) X).reverse :=
      (hS' w hkw.symm hw1).trans (maskRegs_w _ _)
    have haR : S'.R aR = R₀ aR := (hS' aR hka.symm ha1).trans (maskRegs_of_ne hac haw _ _)
    have hbR : S'.R bR = R₀ bR := (hS' bR hkb.symm hb1).trans (maskRegs_of_ne hbc hbw _ _)
    have ht₂' : S'.R t₂ = [] :=
      (hS' t₂ hk2.symm h12.symm).trans ((maskRegs_of_ne hc2.symm hw2.symm _ _).trans ht₂)
    have hself : S'.R = maskRegs cnt w n X S'.R (p₀ + (a + b) * j) :=
      (maskRegs_self hc' hw').symm
    obtain ⟨v₁, hu₁, he₁⟩ := scanEmit_exec body (a := aR) (t := t₂) (cnt := cnt) (w := w)
      (by simp [ha2, hac, haw, hc2.symm, hw2.symm, hcw]) false S'.R v' S' hself ht₂'
      (fun q h1 h2 h3 => by
        rw [haR, hal] at h2
        have := hz j hj (q - (p₀ + (a + b) * j)) (by omega) (by omega)
        rwa [show p₀ + (a + b) * j + (q - (p₀ + (a + b) * j)) = q by omega] at this)
    rw [haR, hal] at he₁
    obtain ⟨v₂, hu₂, he₂⟩ := scanEmit_exec body (a := bR) (t := t₂) (cnt := cnt) (w := w)
      (by simp [hb2, hbc, hbw, hc2.symm, hw2.symm, hcw]) true S'.R v₁
      { S' with R := maskRegs cnt w n X S'.R (p₀ + (a + b) * j + a) } rfl ht₂'
      (fun q h1 h2 h3 => by
        rw [hbR, hbl] at h2
        have := ho j hj (q - (p₀ + (a + b) * j)) (by omega) (by omega) (by omega)
        rwa [show p₀ + (a + b) * j + (q - (p₀ + (a + b) * j)) = q by omega] at this)
    rw [hbR, hbl] at he₂
    have hpos : p₀ + (a + b) * j + a + b = p₀ + (a + b) * (j + 1) := by ring
    rw [hpos] at he₂
    refine ⟨v₂, _, _, by rw [hu₂, hu₁], le_of_eq (by beta_reduce; ring),
      Exec.seq he₁ he₂, maskRegs_of_ne hkc hkw _ _, maskRegs_of_ne hc1.symm hw1.symm _ _,
      fun k hka' hkt => ?_⟩
    exact maskRegs_congr _ fun h1 h2 => by
      rw [hS' k hka' hkt]; exact maskRegs_of_ne h1 h2 _ _
  obtain ⟨v', R', m, hu, hm, he, ha', ht', hΨ'⟩ := scanP_exec body hk1 hp 0 v S
    (by rw [hS, maskRegs_of_ne hkc hkw]; simp)
    (fun k hka' hkt => by rw [hS]; simp [Ψ])
  have hSk : S.R kR = R₀ kR := by rw [hS, maskRegs_of_ne hkc hkw]
  have hSt : S.R t₁ = [] := by rw [hS, maskRegs_of_ne hc1.symm hw1.symm, ht₁]
  refine ⟨v', m, hu, ?_, Exec.cast he rfl ?_⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.zero_add, hSk, hSt,
      List.length_nil, Nat.mul_zero, Nat.add_zero] at hm
    nlinarith
  · congr 2
    funext k
    by_cases hka' : k = kR
    · subst hka'; rw [ha', hSt, maskRegs_of_ne hkc hkw, hSk]; rfl
    · by_cases hkt : k = t₁
      · subst hkt; rw [ht', maskRegs_of_ne hc1.symm hw1.symm, ht₁]
      · rw [hΨ' k hka' hkt, hSk]; simp [Ψ]

/-- The segment-mask builder: `o` zeros, `N` items of `a` zeros and `b` ones, zeros up to `n`
positions; the result moved onto `z`. -/
def segMask (nR oR aR bR kR z cnt w t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (ucopy nR cnt t₁)
    (.seq (scanR oR t₁ (emit cnt w false))
      (.seq (scanP kR t₁ (segItem aR bR cnt w t₂))
        (.seq (scanR nR t₁ (emit cnt w false)) (moveR w z id))))

/-- `segMask`: `z` gains `binSyms n X` on top for every `X` whose low `n` bits follow the item
pattern; every other register ends as it started. -/
theorem segMask_exec {nR oR aR bR kR z cnt w t₁ t₂ : Fin T}
    (hreg : [nR, oR, aR, bR, kR, z, cnt, w, t₁, t₂].Nodup)
    {n o a b N X : ℕ} (v : HS T Q A U) (S : Stacks T A) (hn : (S.R nR).length = n)
    (ho : (S.R oR).length = o) (hal : (S.R aR).length = a) (hbl : (S.R bR).length = b)
    (hkl : (S.R kR).length = N) (hc : S.R cnt = []) (hw : S.R w = []) (ht₁ : S.R t₁ = [])
    (ht₂ : S.R t₂ = [])
    (hX₁ : ∀ q < o, q < n → X.testBit q = false)
    (hX₂ : ∀ j < N, ∀ s < a, o + (a + b) * j + s < n → X.testBit (o + (a + b) * j + s) = false)
    (hX₃ : ∀ j < N, ∀ s, a ≤ s → s < a + b → o + (a + b) * j + s < n →
      X.testBit (o + (a + b) * j + s) = true)
    (hX₄ : ∀ q, o + (a + b) * N ≤ q → q < n → X.testBit q = false) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 10 * n + 4 * o + N * (4 * (a + b) + 13) + 18 ∧
      Exec body (segMask nR oR aR bR kR z cnt w t₁ t₂) (mk v S) m
        (mk v' { S with R := Function.update S.R z (binSyms n X ++ S.R z) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hno, hna, hnb, hnk, hnz, hnc, hnw, hn1, hn2⟩, ⟨hoa, hob, hok, hoz, hoc, how, ho1, ho2⟩,
    ⟨hab, hak, haz, hac, haw, ha1, ha2⟩, ⟨hbk, hbz, hbc, hbw, hb1, hb2⟩,
    ⟨hkz, hkc, hkw, hk1, hk2⟩, ⟨hzc, hzw, hz1, hz2⟩, ⟨hcw, hc1, hc2⟩, ⟨hw1, hw2⟩, h12⟩ := hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body hnc hn1 hc1 v S ht₁
  rw [maskRegs_start (X := X) hcw S.R hc hw, hn] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := scanEmit_exec body (a := oR) (t := t₁) (cnt := cnt) (w := w)
    (by simp [ho1, hoc, how, hc1.symm, hw1.symm, hcw])
    false S.R v₁ { S with R := maskRegs cnt w n X S.R 0 } rfl ht₁
    (fun q _ h2 h3 => hX₁ q (by rw [ho] at h2; omega) h3)
  rw [ho, Nat.zero_add] at he₂
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := segItems_exec body (kR := kR) (aR := aR) (bR := bR)
    (cnt := cnt) (w := w) (t₁ := t₁) (t₂ := t₂)
    (by simp [hak.symm, hbk.symm, hkc, hkw, hk1, hk2, hab, hac, haw, ha1, ha2, hbc, hbw, hb1, hb2,
      hcw, hc1, hc2, hw1, hw2, h12])
    S.R v₂ { S with R := maskRegs cnt w n X S.R o } rfl hal hbl ht₁ ht₂
    (fun j hj s hs hlt => hX₂ j (by rw [← hkl]; exact hj) s hs hlt)
    (fun j hj s hs1 hs2 hlt => hX₃ j (by rw [← hkl]; exact hj) s hs1 hs2 hlt)
  rw [hkl] at he₃ hm₃
  obtain ⟨v₄, hu₄, he₄⟩ := scanEmit_exec body (a := nR) (t := t₁) (cnt := cnt) (w := w)
    (by simp [hn1, hnc, hnw, hc1.symm, hw1.symm, hcw])
    false S.R v₃ { S with R := maskRegs cnt w n X S.R (o + (a + b) * N) } rfl ht₁
    (fun q h1 _ h3 => hX₄ q h1 h3)
  rw [hn] at he₄
  obtain ⟨v₅, hu₅, he₅⟩ := maskFinish_exec body hzc hzw hcw (p := o + (a + b) * N + n)
    (by omega) S.R hc hw v₄ { S with R := maskRegs cnt w n X S.R (o + (a + b) * N + n) } rfl
  refine ⟨v₅, _, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))⟩
  rw [hn, ho] at *
  omega

end MaskBuild

end IntegerMultBounds.MathlibTM2.Node
