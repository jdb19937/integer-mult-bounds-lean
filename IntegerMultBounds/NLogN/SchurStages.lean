module

public import IntegerMultBounds.NLogN.SchurCongr

/-! Rounded factors in explicit form. Relabelling the vertices by an injection
relabels the factors. For the order `k₀, k₀+1, …` on natural positions the
multipliers and pivot rows are read off the stage matrices `stg`: pivot `j`
sees the matrix after the earlier pivots. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open Finset
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

section Relabel
variable (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (f : ι → κ) (hf : Function.Injective f)
include hf

theorem lur_map (ks : List ι) : ∀ (A : Matrix ι ι ℝ) (A' : Matrix κ κ ℝ) (S : Finset ι),
    (∀ a b, A' (f a) (f b)=A a b) → ∀ i j,
      luLr rd mul A' (S.image f) (ks.map f) (f i) (f j)=luLr rd mul A S ks i j ∧
      luUr rd mul A' (S.image f) (ks.map f) (f i) (f j)=luUr rd mul A S ks i j := by
  induction ks with
  | nil =>
    intro A A' S hA i j
    simp [luLr, luUr, hf.eq_iff, hA, hf.mem_finset_image]
  | cons k ks ih =>
    intro A A' S hA i j
    have hmem : ∀ x, f x∈S.image f ↔ x∈S := fun x => hf.mem_finset_image
    have herase : (S.image f).erase (f k)=(S.erase k).image f := (image_erase hf S k).symm
    have hrel : ∀ a b, relim rd mul A' (f k) (f a) (f b)=relim rd mul A k a b := by
      intro a b; simp only [relim, hA]
    have hih := ih (relim rd mul A k) (relim rd mul A' (f k)) (S.erase k) hrel i j
    by_cases hk : k∈S
    · simp only [List.map_cons, luLr, luUr, hmem, hk, ite_true, hf.eq_iff, herase, hA]
      exact ⟨by split <;> [rfl; exact hih.1], by split <;> [rfl; exact hih.2]⟩
    · simp only [List.map_cons, luLr, luUr, hmem, hk, ite_false]
      exact ih A A' S hA i j

theorem fwdM_map (L : Matrix ι ι ℝ) (L' : Matrix κ κ ℝ) (hL : ∀ a c, L' (f a) (f c)=L a c)
    (b : ι → ℝ) (b' : κ → ℝ) (hb : ∀ a, b' (f a)=b a) (ks : List ι) :
    ∀ (done : Finset ι) (y : ι → ℝ) (y' : κ → ℝ), (∀ a, y' (f a)=y a) →
      ∀ a, fwdM rd L' b' (done.image f) y' (ks.map f) (f a)=fwdM rd L b done y ks a := by
  induction ks with
  | nil => intro _ _ _ hy a; exact hy a
  | cons k ks ih =>
    intro done y y' hy a
    simp only [List.map_cons, fwdM]
    rw [← image_insert]
    refine ih _ _ _ (fun c => ?_) a
    by_cases hc : c=k
    · subst hc
      simp only [Function.update_self, hb]
      rw [sum_image (fun x _ z _ h => hf h)]
      simp only [hL, hy]
    · simp only [Function.update_of_ne (hf.ne hc), Function.update_of_ne hc, hy]

theorem bwdM_map (U : Matrix ι ι ℝ) (U' : Matrix κ κ ℝ) (hU : ∀ a c, U' (f a) (f c)=U a c)
    (r y : ι → ℝ) (r' y' : κ → ℝ) (hr : ∀ a, r' (f a)=r a) (hy : ∀ a, y' (f a)=y a) (ks : List ι) :
    ∀ (done : Finset ι) (x : ι → ℝ) (x' : κ → ℝ), (∀ a, x' (f a)=x a) →
      ∀ a, bwdM rd U' r' y' (done.image f) x' (ks.map f) (f a)=bwdM rd U r y done x ks a := by
  induction ks with
  | nil => intro _ _ _ hx a; exact hx a
  | cons k ks ih =>
    intro done x x' hx a
    simp only [List.map_cons, bwdM]
    rw [← image_insert]
    refine ih _ _ _ (fun c => ?_) a
    by_cases hc : c=k
    · subst hc
      simp only [Function.update_self, hy, hr]
      rw [sum_image (fun x _ z _ h => hf h)]
      simp only [hU, hx]
    · simp only [Function.update_of_ne (hf.ne hc), Function.update_of_ne hc, hx]

/-- Relabelling the vertices relabels the solve. -/
theorem bandSolveG_map (rec : ℝ → ℝ) (A : Matrix ι ι ℝ) (A' : Matrix κ κ ℝ)
    (hA : ∀ a c, A' (f a) (f c)=A a c) (S : Finset ι) (ks : List ι) (b : ι → ℝ) (b' : κ → ℝ)
    (hb : ∀ a, b' (f a)=b a) (a : ι) :
    bandSolveG rd mul rec A' (S.image f) (ks.map f) b' (f a)=bandSolveG rd mul rec A S ks b a := by
  have hlu := lur_map rd mul f hf ks A A' S hA
  unfold bandSolveG
  rw [← List.map_reverse]
  have h0 := image_empty (f := f)
  rw [← h0]
  refine bwdM_map rd f hf _ _ (fun a c => (hlu a c).2) _ _ _ _ (fun c => by simp only [(hlu c c).2])
    (fun c => ?_) _ _ _ _ (fun _ => rfl) a
  exact fwdM_map rd f hf _ _ (fun a c => (hlu a c).1) b b' hb ks _ _ _ (fun _ => rfl) c

end Relabel

section Stages
variable (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ)

/-- Stage matrices from pivot `k₀` on: `n` pivots `k₀, …, k₀+n-1` eliminated. -/
noncomputable def stg (A : Matrix ℕ ℕ ℝ) (k₀ : ℕ) : ℕ → Matrix ℕ ℕ ℝ
  | 0 => A
  | n+1 => relim rd mul (stg A k₀ n) (k₀+n)

theorem stg_succ (A : Matrix ℕ ℕ ℝ) (k₀ : ℕ) : ∀ n,
    stg rd mul (relim rd mul A k₀) (k₀+1) n=stg rd mul A k₀ (n+1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stg] at ih ⊢
    rw [ih]
    congr 1
    omega

/-- Factors of the natural order: the multiplier of row `i` at pivot `j` and the
pivot row of `i` are entries of the stage matrices. -/
theorem lur_range (n : ℕ) : ∀ (A : Matrix ℕ ℕ ℝ) (k₀ i j : ℕ),
    luLr rd mul A (Ico k₀ (k₀+n)) (List.range' k₀ n) i j=
      (if k₀ ≤ j ∧ j ≤ i ∧ i < k₀+n then
        (if i=j then 1 else mul (stg rd mul A k₀ (j-k₀) i j) (stg rd mul A k₀ (j-k₀) j j)) else 0) ∧
    luUr rd mul A (Ico k₀ (k₀+n)) (List.range' k₀ n) i j=
      (if k₀ ≤ i ∧ i ≤ j ∧ j < k₀+n then stg rd mul A k₀ (i-k₀) i j else 0) := by
  induction n with
  | zero =>
    intro A k₀ i j
    simp only [add_zero, Ico_self, List.range'_zero, luLr, luUr, notMem_empty, false_and,
      ite_false]
    constructor <;> (split <;> [omega; rfl])
  | succ n ih =>
    intro A k₀ i j
    have hk : k₀∈Ico k₀ (k₀+(n+1)) := mem_Ico.mpr ⟨le_rfl, by omega⟩
    have herase : (Ico k₀ (k₀+(n+1))).erase k₀=Ico (k₀+1) (k₀+1+n) := by
      ext x; simp only [mem_erase, mem_Ico]; omega
    have hih := ih (relim rd mul A k₀) (k₀+1) i j
    rw [stg_succ, stg_succ] at hih
    simp only [List.range'_succ, luLr, luUr, hk, ite_true, herase, mem_Ico]
    refine ⟨?_, ?_⟩
    · rw [hih.1]
      by_cases hjk : j=k₀
      · subst hjk
        simp only [ite_true, Nat.sub_self, stg]
        by_cases hik : i=j
        · simp [hik]
        · simp only [hik, ite_false]
          split <;> split <;> first | rfl | omega
      · simp only [hjk, ite_false]
        by_cases hc : k₀+1 ≤ j ∧ j ≤ i ∧ i < k₀+1+n
        · have e : j-(k₀+1)+1=j-k₀ := by omega
          have hc' : k₀ ≤ j ∧ j ≤ i ∧ i < k₀+(n+1) := by omega
          rw [e]; simp only [hc, hc', and_self, ite_true]
        · have hc' : ¬(k₀ ≤ j ∧ j ≤ i ∧ i < k₀+(n+1)) := by omega
          simp only [hc, hc', ite_false]
    · rw [hih.2]
      by_cases hik : i=k₀
      · subst hik
        simp only [ite_true, Nat.sub_self, stg]
        split <;> split <;> first | rfl | omega
      · simp only [hik, ite_false]
        by_cases hc : k₀+1 ≤ i ∧ i ≤ j ∧ j < k₀+1+n
        · have e : i-(k₀+1)+1=i-k₀ := by omega
          have hc' : k₀ ≤ i ∧ i ≤ j ∧ j < k₀+(n+1) := by omega
          rw [e]; simp only [hc, hc', and_self, ite_true]
        · have hc' : ¬(k₀ ≤ i ∧ i ≤ j ∧ j < k₀+(n+1)) := by omega
          simp only [hc, hc', ite_false]

end Stages

end IntegerMultBounds.NLogN.SchurDominance
