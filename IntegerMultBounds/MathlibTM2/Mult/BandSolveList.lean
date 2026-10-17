module

public import IntegerMultBounds.MathlibTM2.Mult.BandFactor
public import IntegerMultBounds.MathlibTM2.Mult.BandList
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! The banded line solve on integer numerators from the window factorization.
A banded grid matrix `AZ` (half width `B`, zero outside `s × s`) is factored by
the window run; its multiplier columns drive the forward pass, the transposed
pivot rows and the Newton reciprocals of the pivots drive the backward pass.
This file identifies the window outputs with the integer stage matrices
`stgZ`, whose grid values are the real stage matrices of the machine rules. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.BandFactor

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
open IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.BandList

variable (P K : ℕ)

theorem gv_injective : Function.Injective (gv P) := by
  intro a b h
  simp only [gv] at h
  have h2 : (2 : ℝ)^P≠0 := by positivity
  exact_mod_cast (div_left_inj' h2).mp h

theorem gv_zero : gv P 0=0 := by simp [gv]

/-- One integer elimination step with the machine rules. -/
def relimZ (AZ : ℕ → ℕ → ℤ) (k : ℕ) : ℕ → ℕ → ℤ :=
  fun i j => AZ i j-(mulZ P K (AZ i k) (AZ k k)*AZ k j).tdiv (2^P)

/-- Integer stage matrices: pivots `0, …, n-1` eliminated. -/
def stgZ (AZ : ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ
  | 0 => AZ
  | n+1 => relimZ P K (stgZ AZ n) n

/-- Grid values of a numerator matrix. -/
noncomputable def gvM (AZ : ℕ → ℕ → ℤ) : Matrix ℕ ℕ ℝ := fun a c => gv P (AZ a c)

theorem relimZ_map (hP : 2 ≤ P) (AZ : ℕ → ℕ → ℤ) (k : ℕ) :
    gvM P (relimZ P K AZ k)=relim (rdP P) (PhaseCellMatrix.machMul (rdP P) K) (gvM P AZ) k := by
  funext i j
  simp only [gvM, relimZ, relim]
  rw [mulZ_eq P K hP]
  have h := rdP_mul_grid P (mulZ P K (AZ i k) (AZ k k)) (AZ k j)
  simp only [gv] at h ⊢
  rw [h]; push_cast; ring

theorem stgZ_map (hP : 2 ≤ P) (AZ : ℕ → ℕ → ℤ) : ∀ n,
    gvM P (stgZ P K AZ n)=stg (rdP P) (PhaseCellMatrix.machMul (rdP P) K) (gvM P AZ) 0 n
  | 0 => rfl
  | n+1 => by
    simp only [stgZ, stg, zero_add]
    rw [relimZ_map P K hP, stgZ_map hP AZ n]

variable (B : ℕ)

/-- Row `i` of `AZ` on columns `k, …, k+2B`. -/
def winRowZ (AZ : ℕ → ℕ → ℤ) (k i : ℕ) : List ℤ := (List.range' k (2*B+1)).map (AZ i)

/-- The initial window: rows `0, …, B` on columns `0, …, 2B`. -/
def windowZ (AZ : ℕ → ℕ → ℤ) : List (List ℤ) := (List.range' 0 (B+1)).map (winRowZ B AZ 0)

/-- The input rows fed to the `n` steps: row `m+B+1` on columns `m+1, …, m+2B+1`. -/
def inputsZ (AZ : ℕ → ℕ → ℤ) (n : ℕ) : List (List ℤ) :=
  (List.range' 0 n).map fun m => winRowZ B AZ (m+1) (m+B+1)

theorem machMul_zero (c : ℝ) : PhaseCellMatrix.machMul (rdP P) K 0 c=0 := by
  simp [PhaseCellMatrix.machMul, rdP_zero]

theorem winRowZ_map (AZ : ℕ → ℕ → ℤ) (k i : ℕ) :
    (winRowZ B AZ k i).map (gv P)=winRow B (gvM P AZ) k i := by
  simp only [winRowZ, winRow, List.map_map]; rfl

/-- The integer window run emits, for each pivot `m`, the multipliers of rows
`m+1, …, m+B` and the pivot row of the integer stage matrix. -/
theorem factorRowsZ_run (hP : 2 ≤ P) (AZ : ℕ → ℕ → ℤ) (hA : BandFrom B (gvM P AZ) 0) (n : ℕ) :
    factorRowsZ P K (windowZ B AZ) (inputsZ B AZ n)=
      (List.range' 0 n).map fun m => ((List.range' (m+1) B).map fun i =>
        mulZ P K (stgZ P K AZ m i m) (stgZ P K AZ m m m), winRowZ B (stgZ P K AZ m) m m) := by
  have hinj : Function.Injective (List.map fun x : List ℤ × List ℤ => (x.1.map (gv P), x.2.map (gv P))) := by
    refine List.map_injective_iff.mpr fun x y h => ?_
    simp only [Prod.mk.injEq] at h
    exact Prod.ext ((List.map_injective_iff.mpr (gv_injective P)) h.1)
      ((List.map_injective_iff.mpr (gv_injective P)) h.2)
  apply hinj
  rw [factorRowsZ_map P K hP]
  have hw : (windowZ B AZ).map (List.map (gv P))=
      window B (stg (rdP P) (PhaseCellMatrix.machMul (rdP P) K) (gvM P AZ) 0 0) 0 := by
    simp only [windowZ, window, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    exact winRowZ_map P B AZ 0 i
  have hi : (inputsZ B AZ n).map (List.map (gv P))=
      (List.range' 0 n).map fun m => winRow B (gvM P AZ) (m+1) (m+B+1) := by
    simp only [inputsZ, List.map_map]
    refine List.map_congr_left fun m _ => ?_
    exact winRowZ_map P B AZ _ _
  rw [hw, hi, factorRows_run (rdP P) _ B (rdP_zero P) (machMul_zero P K) _ hA n 0, List.map_map]
  refine List.map_congr_left fun m _ => ?_
  simp only [Function.comp, List.map_map]
  congr 1
  · refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, ← mulZ_eq P K hP]
    rw [← stgZ_map P K hP]
    rfl
  · rw [winRowZ_map, stgZ_map P K hP]

theorem padCol_map (f : ℕ → ℤ) : ∀ (B a L : ℕ),
    padCol B ((List.range' a L).map f)=(List.range' a B).map fun i => if i<a+L then f i else 0
  | 0, a, L => by simp [padCol]
  | B+1, a, 0 => by
    simp only [padCol, List.range'_zero, List.map_nil, List.take_nil, List.length_nil, Nat.sub_zero,
      add_zero]
    rw [List.map_congr_left (g := fun _ => (0 : ℤ)) fun i hi => by
      have := List.mem_range'_1.mp hi; simp only [ite_eq_right_iff]; omega]
    simp
  | B+1, a, L+1 => by
    have ih := padCol_map f B (a+1) L
    simp only [padCol] at ih ⊢
    rw [List.range'_succ, List.map_cons, List.take_succ_cons, List.length_cons, List.cons_append,
      List.range'_succ, List.map_cons, ite_eq_left (by omega), Nat.add_sub_add_right, ih]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range'_1.mp hi
    congr 1
    simp only [eq_iff_iff]; omega

theorem cols_range' (Lz : ℕ → ℕ → ℤ) : ∀ a n,
    cols Lz (List.range' a n)=(List.range' a n).map fun m => (List.range' (m+1) (a+n-(m+1))).map (Lz · m)
  | _, 0 => rfl
  | a, n+1 => by
    rw [List.range'_succ, cols, List.map_cons, cols_range' Lz (a+1) n]
    congr 1
    · congr 2; omega
    · refine List.map_congr_left fun m _ => ?_
      congr 2; omega

/-- Zero rows and columns outside `s` stay zero through elimination. -/
theorem stgZ_out (s : ℕ) (AZ : ℕ → ℕ → ℤ) (hout : ∀ i j, (s ≤ i ∨ s ≤ j) → AZ i j=0) :
    ∀ n i j, (s ≤ i ∨ s ≤ j) → stgZ P K AZ n i j=0
  | 0, i, j, h => hout i j h
  | n+1, i, j, h => by
    simp only [stgZ, relimZ]
    rcases h with h | h
    · rw [stgZ_out s AZ hout n i j (Or.inl h), stgZ_out s AZ hout n i n (Or.inl h)]
      simp [mulZ]
    · rw [stgZ_out s AZ hout n i j (Or.inr h), stgZ_out s AZ hout n n j (Or.inr h)]
      simp

/-- The integer stage matrices are banded on the active part. -/
theorem stgZ_band (hP : 2 ≤ P) (AZ : ℕ → ℕ → ℤ) (hA : BandFrom B (gvM P AZ) 0) (n i j : ℕ)
    (hi : n ≤ i) (hj : n ≤ j) (h : stgZ P K AZ n i j≠0) : i ≤ j+B ∧ j ≤ i+B := by
  have hb := bandFrom_stg (rdP P) _ B (rdP_zero P) (machMul_zero P K) _ hA n i j hi hj
  rw [← stgZ_map P K hP] at hb
  refine hb fun h0 => h ?_
  have : gv P (stgZ P K AZ n i j)=gv P 0 := by rw [gv_zero]; exact h0
  exact gv_injective P this

variable (s : ℕ)

/-- Unit-lower factor numerators of the natural order. -/
def LzN (AZ : ℕ → ℕ → ℤ) (i k : ℕ) : ℤ :=
  if k ≤ i ∧ i<s then (if i=k then 2^P else mulZ P K (stgZ P K AZ k i k) (stgZ P K AZ k k k)) else 0

/-- Pivot-row factor numerators of the natural order. -/
def UzN (AZ : ℕ → ℕ → ℤ) (k j : ℕ) : ℤ := if k ≤ j ∧ j<s then stgZ P K AZ k k j else 0

/-- Machine rules on the grid. -/
noncomputable abbrev mRule : ℝ → ℝ → ℝ := PhaseCellMatrix.machMul (rdP P) K

theorem luLr_natural (hP : 2 ≤ P) (AZ : ℕ → ℕ → ℤ) (i k : ℕ) :
    luLr (rdP P) (mRule P K) (gvM P AZ) (Finset.Ico 0 s) (List.range' 0 s) i k=gv P (LzN P K s AZ i k) := by
  have h := (lur_range (rdP P) (mRule P K) s (gvM P AZ) 0 i k).1
  rw [zero_add] at h
  rw [h, LzN]
  by_cases hc : k ≤ i ∧ i<s
  · rw [ite_eq_left ⟨Nat.zero_le _, hc⟩, ite_eq_left hc]
    by_cases hik : i=k
    · simp only [hik, ite_true, gv]; push_cast; field_simp
    · simp only [hik, ite_false, Nat.sub_zero, mRule]
      rw [← stgZ_map P K hP]; exact mulZ_eq P K hP _ _
  · rw [ite_eq_right (fun h' => hc h'.2), ite_eq_right hc, gv_zero]

theorem luUr_natural (hP : 2 ≤ P) (AZ : ℕ → ℕ → ℤ) (k j : ℕ) :
    luUr (rdP P) (mRule P K) (gvM P AZ) (Finset.Ico 0 s) (List.range' 0 s) k j=gv P (UzN P K s AZ k j) := by
  have h := (lur_range (rdP P) (mRule P K) s (gvM P AZ) 0 k j).2
  rw [zero_add] at h
  rw [h, UzN]
  by_cases hc : k ≤ j ∧ j<s
  · rw [ite_eq_left ⟨Nat.zero_le _, hc⟩, ite_eq_left hc, Nat.sub_zero, ← stgZ_map P K hP]; rfl
  · rw [ite_eq_right (fun h' => hc h'.2), ite_eq_right hc, gv_zero]

variable (hP : 2 ≤ P) (AZ : ℕ → ℕ → ℤ) (hA : BandFrom B (gvM P AZ) 0)
  (hout : ∀ i j, (s ≤ i ∨ s ≤ j) → AZ i j=0)
include hout

/-- The padded forward table is the window's multiplier output. -/
theorem lcols_eq : (cols (LzN P K s AZ) (List.range' 0 s)).map (padCol B)=
    (List.range' 0 s).map fun m => (List.range' (m+1) B).map fun i =>
      mulZ P K (stgZ P K AZ m i m) (stgZ P K AZ m m m) := by
  rw [cols_range', List.map_map]
  refine List.map_congr_left fun m hm => ?_
  have hm' := List.mem_range'_1.mp hm
  simp only [Function.comp, padCol_map]
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range'_1.mp hi
  by_cases his : i<s
  · rw [ite_eq_left (by omega), LzN, ite_eq_left ⟨by omega, his⟩, ite_eq_right (by omega)]
  · rw [ite_eq_right (by omega), stgZ_out P K s AZ hout m i m (Or.inl (by omega))]
    simp [mulZ]

include hP hA in
omit hout in
/-- Multiplier columns vanish beyond the band. -/
theorem banded_LzN : Banded B (LzN P K s AZ) (List.range' 0 s) := by
  suffices h : ∀ a n, Banded B (LzN P K s AZ) (List.range' a n) from h 0 s
  intro a n
  induction n generalizing a with
  | zero => trivial
  | succ n ih =>
    rw [List.range'_succ]
    refine ⟨fun x hx => ?_, ih (a+1)⟩
    rw [List.drop_range', Nat.mul_one] at hx
    have hx' := List.mem_range'_1.mp hx
    unfold LzN
    split
    · rw [ite_eq_right (by omega)]
      by_contra hne
      have h0 : stgZ P K AZ a x a≠0 := by
        intro h0; apply hne; simp [h0, mulZ]
      have := stgZ_band P K B hP AZ hA a x a (by omega) le_rfl h0
      omega
    · rfl

omit hout in
theorem cols_range'_reverse (Uz : ℕ → ℕ → ℤ) : ∀ n,
    cols Uz (List.range' 0 n).reverse=(List.range' 0 n).reverse.map fun m => (List.range' 0 m).reverse.map (Uz · m)
  | 0 => rfl
  | n+1 => by
    rw [range'_snoc, List.reverse_append, List.reverse_singleton, List.singleton_append, cols,
      cols_range'_reverse Uz n, List.map_cons, zero_add]

omit hout in
theorem padCol_rev (f : ℕ → ℤ) (m : ℕ) :
    padCol B ((List.range' 0 m).reverse.map f)=(List.range' 1 B).map fun d => if d ≤ m then f (m-d) else 0 := by
  have e : (List.range' 0 m).reverse.map f=(List.range' 1 m).map fun d => f (m-d) := by
    rw [List.reverse_range', List.map_map, List.range_eq_range', List.range'_eq_map_range,
      List.range'_eq_map_range, List.map_map, List.map_map]
    refine List.map_congr_left fun d hd => ?_
    have := List.mem_range.mp hd
    simp only [Function.comp]; congr 1; omega
  rw [e, padCol_map]
  refine List.map_congr_left fun d hd => ?_
  have := List.mem_range'_1.mp hd
  congr 1; simp only [eq_iff_iff]; omega

/-- Transposed pivot-row entries for the backward pass: column `m` above the
diagonal, nearest first, from the stored pivot rows. -/
def ucolZ (urows : List (List ℤ)) (m : ℕ) : List ℤ :=
  (List.range' 1 B).map fun d => if d ≤ m then (urows.getD (m-d) []).getD d 0 else 0

omit hout in
theorem getD_range'_map {α : Type*} (f : ℕ → α) (a n i : ℕ) (d : α) (hi : i<n) :
    ((List.range' a n).map f).getD i d=f (a+i) := by
  simp [List.getD_eq_getElem?_getD, hi]

omit hout in
/-- The padded backward table is the transpose of the window's pivot rows. -/
theorem ucols_eq : (cols (UzN P K s AZ) (List.range' 0 s).reverse).map (padCol B)=
    (List.range' 0 s).reverse.map (ucolZ B ((List.range' 0 s).map fun m => winRowZ B (stgZ P K AZ m) m m)) := by
  rw [cols_range'_reverse, List.map_map]
  refine List.map_congr_left fun m hm => ?_
  have hm' := List.mem_range'_1.mp (List.mem_reverse.mp hm)
  simp only [Function.comp, padCol_rev, ucolZ]
  refine List.map_congr_left fun d hd => ?_
  have hd' := List.mem_range'_1.mp hd
  by_cases hdm : d ≤ m
  · rw [ite_eq_left hdm, ite_eq_left hdm, getD_range'_map _ _ _ _ _ (by omega), winRowZ,
      getD_range'_map _ _ _ _ _ (by omega), UzN, ite_eq_left ⟨by omega, by omega⟩]
    congr 1 <;> omega
  · rw [ite_eq_right hdm, ite_eq_right hdm]

include hP hA in
omit hout in
/-- Transposed pivot rows vanish beyond the band. -/
theorem banded_UzN : Banded B (UzN P K s AZ) (List.range' 0 s).reverse := by
  suffices h : ∀ n, n ≤ s → Banded B (UzN P K s AZ) (List.range' 0 n).reverse from h s le_rfl
  intro n
  induction n with
  | zero => intro _; trivial
  | succ n ih =>
    intro hn
    rw [range'_snoc, List.reverse_append, List.reverse_singleton, List.singleton_append, zero_add]
    refine ⟨fun x hx => ?_, ih (by omega)⟩
    rw [List.reverse_range', ← List.map_drop, List.range_eq_range', List.drop_range',
      Nat.mul_one] at hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hj' := List.mem_range'_1.mp hj
    unfold UzN
    split
    · by_contra hne
      have := stgZ_band P K B hP AZ hA (0+n-1-j) (0+n-1-j) n le_rfl (by omega) hne
      omega
    · rfl

omit hP hA hout in
theorem bwdM_congr_y {ι : Type*} [DecidableEq ι] (rd : ℝ → ℝ) (U : Matrix ι ι ℝ) (r y y' : ι → ℝ)
    (ks : List ι) (hy : ∀ k∈ks, y' k=y k) : ∀ (done : Finset ι) (x : ι → ℝ),
      bwdM rd U r y' done x ks=bwdM rd U r y done x ks := by
  induction ks with
  | nil => intro _ _; rfl
  | cons k ks ih =>
    intro done x
    simp only [bwdM, hy k List.mem_cons_self]
    exact ih (fun z hz => hy z (List.mem_cons_of_mem _ hz)) _ _

omit hP hA hout in
theorem range'_getD (l : List ℤ) : (List.range' 0 l.length).map (fun i => l.getD i 0)=l := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  simp [List.getD_eq_getElem?_getD, h2]

omit hout in
/-- The banded line solve on numerators: window factorization, forward pass on
the padded multiplier columns, backward pass on the transposed pivot rows with
Newton reciprocals. -/
def lineSolveZ (bZ : List ℤ) : List ℤ :=
  let fac := factorRowsZ P K (windowZ B AZ) (inputsZ B AZ s)
  let Ur := fac.map Prod.snd
  let y := fwdZ P (fac.map Prod.fst) (bZ++List.replicate B 0)
  (bwdZ P ((List.range' 0 s).reverse.map (ucolZ B Ur))
    (Ur.map fun r => newtonZ P (r.headD 0) K).reverse (y.reverse++List.replicate B 0)).reverse

include hP hA in
/-- On the grid the numerator line solve is the machine-rule band solve of the
natural order. -/
theorem lineSolveZ_eq (bZ : List ℤ) (hlen : bZ.length=s) :
    (lineSolveZ P K B s AZ bZ).map (gv P)=(List.range' 0 s).map
      (bandSolveG (rdP P) (mRule P K) (fun c => NewtonRecip.newtonR (rdP P) c K) (gvM P AZ)
        (Finset.Ico 0 s) (List.range' 0 s) (fun i => gv P (bZ.getD i 0))) := by
  set ks := List.range' 0 s with hks
  have hnd : ks.Nodup := List.nodup_range'
  set L := luLr (rdP P) (mRule P K) (gvM P AZ) (Finset.Ico 0 s) ks
  set U := luUr (rdP P) (mRule P K) (gvM P AZ) (Finset.Ico 0 s) ks
  have hfac := factorRowsZ_run P K B hP AZ hA s
  have hLc : (factorRowsZ P K (windowZ B AZ) (inputsZ B AZ s)).map Prod.fst=(cols (LzN P K s AZ) ks).map (padCol B) := by
    rw [hfac, List.map_map, lcols_eq P K B s AZ hout]; rfl
  have hUr : (factorRowsZ P K (windowZ B AZ) (inputsZ B AZ s)).map Prod.snd=
      ks.map fun m => winRowZ B (stgZ P K AZ m) m m := by
    rw [hfac, List.map_map]; rfl
  set rzF : ℕ → ℤ := fun m => newtonZ P (UzN P K s AZ m m) K
  have hrz : ((ks.map fun m => winRowZ B (stgZ P K AZ m) m m).map fun r => newtonZ P (r.headD 0) K)=ks.map rzF := by
    rw [List.map_map]
    refine List.map_congr_left fun m hm => ?_
    have hm' := List.mem_range'_1.mp hm
    simp only [Function.comp, winRowZ, List.range'_succ, List.map_cons, List.headD_cons, rzF, UzN,
      ite_eq_left (show m ≤ m ∧ m<s from ⟨le_refl m, by omega⟩)]
  have hbZ : bZ=ks.map fun i => bZ.getD i 0 := by rw [hks, ← hlen, range'_getD]
  have hlenk : bZ.length=ks.length := by rw [hlen, hks, List.length_range']
  -- forward pass
  set b : ℕ → ℝ := fun i => gv P (bZ.getD i 0)
  set F := fwdM (rdP P) L b ∅ (fun _ => 0) ks
  have hy : (fwdZ P (cols (LzN P K s AZ) ks) bZ).map (gv P)=ks.map F := by
    have h1 := fwdZ_eq P L (LzN P K s AZ) (fun i k => luLr_natural P K s hP AZ i k) ks hnd
      (fun _ => 0) (fun i => bZ.getD i 0)
    rw [← hbZ] at h1
    have h2 := colFwd_eq (rdP P) L b ks hnd ∅ (fun _ => 0) (fun i => ((bZ.getD i 0 : ℤ) : ℝ)/2^P)
      (fun k _ => Finset.notMem_empty k) (fun k _ => by simp [b, gv])
    exact h1.trans (by rw [h2])
  set y := fwdZ P (cols (LzN P K s AZ) ks) bZ
  have hylen : y.length=s := by
    have := congrArg List.length hy
    simp only [List.length_map, hks, List.length_range'] at this
    exact this
  set yZ : ℕ → ℤ := fun k => y.getD k 0
  have hyZ : y=ks.map yZ := by rw [hks, ← hylen, range'_getD]
  have hyF : ∀ k∈ks, gv P (yZ k)=F k := by
    have h := hy
    rw [hyZ, List.map_map] at h
    exact fun k hk => List.map_inj_left.mp h k hk
  -- backward pass
  have hUz : ∀ i k, U i k=((UzN P K s AZ i k : ℤ) : ℝ)/2^P := fun i k => luUr_natural P K s hP AZ i k
  have hr : (fun k => ((rzF k : ℤ) : ℝ)/2^P)=fun k => NewtonRecip.newtonR (rdP P) (U k k) K := by
    funext k
    rw [hUz k k]
    exact (newtonZ_eq P hP _ K).symm
  have hndr : ks.reverse.Nodup := List.nodup_reverse.mpr hnd
  have hb := bwdZ_eq P U (UzN P K s AZ) hUz rzF ks.reverse hndr (fun _ => 0) yZ
  have hc := colBwd_eq (rdP P) U (fun k => ((rzF k : ℤ) : ℝ)/2^P) (fun i => ((yZ i : ℤ) : ℝ)/2^P)
    ks.reverse hndr ∅ (fun _ => 0) (fun i => ((yZ i : ℤ) : ℝ)/2^P)
    (fun k _ => Finset.notMem_empty k) (fun k _ => by simp)
  have hcy := bwdM_congr_y (rdP P) U (fun k => ((rzF k : ℤ) : ℝ)/2^P) F
    (fun i => ((yZ i : ℤ) : ℝ)/2^P) ks.reverse (fun k hk => hyF k (List.mem_reverse.mp hk)) ∅ (fun _ => 0)
  rw [hc, hcy, hr] at hb
  have hpadU := bwdZ_pad P B (UzN P K s AZ) ks.reverse (banded_UzN P K B s hP AZ hA)
    (ks.reverse.map rzF) (ks.reverse.map yZ) (by simp)
  have hpadL := fwdZ_pad P B (LzN P K s AZ) ks (banded_LzN P K B s hP AZ hA) bZ hlenk
  have e : (bwdZ P (cols (UzN P K s AZ) ks.reverse) (ks.reverse.map rzF) (ks.reverse.map yZ)).map (gv P)=
      ks.reverse.map (bandSolveG (rdP P) (mRule P K) (fun c => NewtonRecip.newtonR (rdP P) c K) (gvM P AZ)
        (Finset.Ico 0 s) ks b) := hb
  simp only [lineSolveZ, hLc, hUr, hrz, hpadL]
  rw [← ucols_eq P K B s AZ, ← hks, show fwdZ P (cols (LzN P K s AZ) ks) bZ=ks.map yZ from hyZ,
    show (ks.map yZ).reverse=ks.reverse.map yZ from List.map_reverse.symm]
  simp only [← List.map_reverse]
  rw [hpadU, List.map_reverse]
  rw [e, List.map_reverse, List.reverse_reverse]

end IntegerMultBounds.MathlibTM2.Mult.BandFactor
