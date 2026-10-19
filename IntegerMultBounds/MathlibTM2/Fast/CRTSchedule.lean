module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControl
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Linear CRT axis routing

Keep the full reversed layout between triangular rotations. Expose each target
by exchanging it with axis zero, rotate with all other axes as prefix, then
undo the exchange. Finally reverse the layout by paired distant exchanges.
This is a pure routing specification, not a finite-host machine integration.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

/-- Relabel the two exchanged axes. On duplicate-free layouts this exchanges
exactly their physical positions. -/
def crtAxisExchange {α : Type*} [DecidableEq α] (j k : α) (o : List α) : List α :=
  o.map (Equiv.swap j k)

@[simp] theorem crtAxisExchange_twice {α : Type*} [DecidableEq α]
    (j k : α) (o : List α) :
    crtAxisExchange j k (crtAxisExchange j k o) = o := by
  simp [crtAxisExchange, List.map_map, Function.comp_def]

@[simp] theorem crtAxisExchange_self {α : Type*} [DecidableEq α]
    (j : α) (o : List α) : crtAxisExchange j j o = o := by
  simp [crtAxisExchange]

/-- The exact arbitrary-gap shape consumed by `crtSwapGapBox`. -/
theorem crtAxisExchange_gap {α : Type*} [DecidableEq α]
    (pre gap post : List α) (j k : α)
    (hnd : (pre ++ j :: gap ++ k :: post).Nodup) :
    crtAxisExchange j k (pre ++ j :: gap ++ k :: post) =
      pre ++ k :: gap ++ j :: post := by
  have hfix : ∀ x ∈ pre ++ gap ++ post, Equiv.swap j k x = x := by
    intro x hx
    have hj : x ≠ j := by
      intro h; subst x
      simp only [List.append_assoc, List.cons_append, List.nodup_append, List.nodup_cons, List.mem_append, List.mem_cons] at hnd
      simp only [List.mem_append] at hx
      grind
    have hk : x ≠ k := by
      intro h; subst x
      simp only [List.append_assoc, List.cons_append, List.nodup_append, List.nodup_cons, List.mem_append, List.mem_cons] at hnd
      simp only [List.mem_append] at hx
      grind
    exact Equiv.swap_apply_of_ne_of_ne hj hk
  have hp : pre.map (Equiv.swap j k) = pre := by
    calc
      _ = pre.map id := List.map_congr_left (fun x hx => hfix x (by simp [hx]))
      _ = pre := List.map_id _
  have hg : gap.map (Equiv.swap j k) = gap := by
    calc
      _ = gap.map id := List.map_congr_left (fun x hx => hfix x (by simp [hx]))
      _ = gap := List.map_id _
  have ht : post.map (Equiv.swap j k) = post := by
    calc
      _ = post.map id := List.map_congr_left (fun x hx => hfix x (by simp [hx]))
      _ = post := List.map_id _
  simp [crtAxisExchange, hp, hg, ht]

/-- All axes except the innermost zero, in full reverse order. -/
def crtOuterAxes (d : ℕ) : List (Fin (d + 1)) :=
  ((List.finRange d).map Fin.succ).reverse

/-- The controls for target `i`: all remaining axes, in their physical order. -/
def crtExposePrefix {d : ℕ} (i : Fin (d + 1)) : List (Fin (d + 1)) :=
  crtAxisExchange i 0 (crtOuterAxes d)

theorem crtRevAx_eq_outer (d : ℕ) :
    crtRevAx (d := d + 1) (d + 1) = crtOuterAxes d ++ [0] := by
  simp [crtRevAx, List.finRange_succ, crtOuterAxes]

/-- Exposure puts the target last; every other axis is a control or spectator. -/
theorem crtExpose_layout {d : ℕ} (i : Fin (d + 1)) :
    crtAxisExchange i 0 (crtRevAx (d := d + 1) (d + 1)) =
      crtExposePrefix i ++ [i] := by
  rw [crtRevAx_eq_outer]
  simp [crtAxisExchange, crtExposePrefix]

theorem crtExpose_nodup {d : ℕ} (i : Fin (d + 1)) :
    (crtExposePrefix i ++ [i]).Nodup := by
  rw [← crtExpose_layout]
  exact (crtRevAx_nodup _).map (Equiv.swap i 0).injective

theorem crtExposePrefix_nodup {d : ℕ} (i : Fin (d + 1)) :
    (crtExposePrefix i).Nodup := (List.nodup_append.mp (crtExpose_nodup i)).1

theorem crtExposePrefix_controls {d : ℕ} (i : Fin (d + 1)) :
    ∀ j : Fin (d + 1), j.val < i.val → j ∈ crtExposePrefix i := by
  intro j hj
  have hmem : j ∈ crtExposePrefix i ++ [i] := by
    rw [← crtExpose_layout]
    apply List.mem_map.mpr
    refine ⟨Equiv.swap i 0 j, ?_, by simp⟩
    exact (crt_mem_revAx _).mpr (Equiv.swap i 0 j).isLt
  have hne : j ≠ i := by intro h; subst j; omega
  simpa [hne] using hmem

/-- The exposed prefix directly satisfies the arbitrary-order arithmetic
control evaluator's semantic contract. -/
theorem crtExpose_controlValue {d : ℕ} (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (F : ℕ) (x : Fin (d + 1) → ℕ) :
    crtControlValue (crtControlFields a s i.val (crtExposePrefix i)) F =
      crtKI s i.val (crtDec a (crtExposePrefix i) F x) :=
  crtControlValue_eq_crtKI a s i.val (crtExposePrefix i)
    (crtExposePrefix_nodup i) (crtExposePrefix_controls i) F x

/-- A concrete route made solely of arbitrary-gap exchanges, counting swaps.
Each `swap` constructor supplies the five lists/axes needed by the box lemma. -/
inductive CrtAxisRoute {α : Type*} : List α → List α → ℕ → Prop
  | refl (o) : CrtAxisRoute o o 0
  | swap (pre gap post : List α) (j k : α) :
      CrtAxisRoute (pre ++ j :: gap ++ k :: post)
        (pre ++ k :: gap ++ j :: post) 1
  | trans {o p q n m} : CrtAxisRoute o p n → CrtAxisRoute p q m →
      CrtAxisRoute o q (n + m)

/-- Routes preserve the complete axis permutation. -/
theorem CrtAxisRoute.perm {α : Type*} {o p : List α} {n : ℕ}
    (h : CrtAxisRoute o p n) : o.Perm p := by
  classical
  induction h with
  | refl => exact List.Perm.refl _
  | swap pre gap post j k =>
      apply List.perm_iff_count.mpr
      intro x
      simp only [List.count_append, List.count_cons]
      omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Every route can be traversed backward for the inverse transform. -/
theorem CrtAxisRoute.symm {α : Type*} {o p : List α} {n : ℕ}
    (h : CrtAxisRoute o p n) : CrtAxisRoute p o n := by
  induction h with
  | refl => exact .refl _
  | swap pre gap post j k => exact .swap pre gap post k j
  | trans _ _ ih₁ ih₂ => simpa [Nat.add_comm] using ih₂.trans ih₁

/-- Every nonzero target is exposed by exactly one arbitrary-gap exchange. -/
theorem crtExpose_route {d : ℕ} (i : Fin (d + 1)) (hi : i ≠ 0) :
    CrtAxisRoute (crtRevAx (d := d + 1) (d + 1))
      (crtExposePrefix i ++ [i]) 1 := by
  have hm : i ∈ crtOuterAxes d := by
    have h := (crt_mem_revAx (m := d + 1) i).mpr i.isLt
    rw [crtRevAx_eq_outer] at h
    simpa [hi] using h
  obtain ⟨pre, gap, he⟩ := List.mem_iff_append.mp hm
  have hlay : crtRevAx (d := d + 1) (d + 1) = pre ++ i :: gap ++ 0 :: [] := by
    rw [crtRevAx_eq_outer, he]
  have hnd : (pre ++ i :: gap ++ (0 : Fin (d + 1)) :: []).Nodup := by
    rw [← hlay]; exact crtRevAx_nodup _
  rw [← crtExpose_layout, hlay, crtAxisExchange_gap pre gap [] i 0 hnd]
  exact .swap pre gap [] i 0

/-- A target rotation leaves the physical layout restored after two swaps. -/
theorem crtExpose_roundTrip {d : ℕ} (i : Fin (d + 1)) (hi : i ≠ 0) :
    CrtAxisRoute (crtRevAx (d := d + 1) (d + 1))
      (crtRevAx (d := d + 1) (d + 1)) 2 :=
  (crtExpose_route i hi).trans (crtExpose_route i hi).symm

/-- A list of targets can be processed in either triangular order, restoring
full reverse layout after each rotation. Zero contributes no swaps. -/
theorem crtTriangular_route {d : ℕ} (targets : List (Fin (d + 1))) :
    CrtAxisRoute (crtRevAx (d := d + 1) (d + 1))
      (crtRevAx (d := d + 1) (d + 1))
      ((targets.map fun i => if i.val = 0 then 0 else 2).sum) := by
  induction targets with
  | nil => simpa using CrtAxisRoute.refl (crtRevAx (d := d + 1) (d + 1))
  | cons i targets ih =>
      by_cases hi : i.val = 0
      · simpa only [List.map_cons, List.sum_cons, hi, ite_true, Nat.zero_add] using ih
      · have hne : i ≠ 0 := by intro h; subst i; simp at hi
        simpa only [List.map_cons, List.sum_cons, hi, ite_false] using (crtExpose_roundTrip i hne).trans ih

/-- Paired outer exchanges reverse any contiguous layout in floor(length/2)
passes, including the empty and singleton cases. -/
theorem crtAxisRoute_reverse {α : Type*} (o pre post : List α) :
    CrtAxisRoute (pre ++ o ++ post) (pre ++ o.reverse ++ post) (o.length / 2) := by
  induction o using List.bidirectionalRecOn generalizing pre post with
  | H0 => simpa using CrtAxisRoute.refl (pre ++ post)
  | H1 j => simpa using CrtAxisRoute.refl (pre ++ [j] ++ post)
  | Hn j gap k ih =>
      have hs := CrtAxisRoute.swap pre gap post j k
      have hr := ih (pre ++ [k]) (j :: post)
      have h := hs.trans (by simpa only [List.append_assoc, List.singleton_append] using hr)
      have hc : 1 + gap.length / 2 = (j :: (gap ++ [k])).length / 2 := by
        simp only [List.length_cons, List.length_append, List.length_nil]
        omega
      simpa only [List.reverse_cons, List.reverse_append, List.reverse_singleton,
        List.append_assoc, List.cons_append, List.singleton_append, List.reverse_nil,
        List.nil_append, hc] using h

/-- Forward terminal reversal: full reversed axes become ascending axes. -/
theorem crtAxisRoute_toFinRange (d : ℕ) :
    CrtAxisRoute (crtRevAx (d := d) d) (List.finRange d) (d / 2) := by
  simpa [crtRevAx, List.take_of_length_le (show d ≥ (List.finRange d).length by simp)] using crtAxisRoute_reverse (List.finRange d).reverse [] []

/-- Exposure and restoration for each nonzero target, then paired reversal. -/
def crtLinearSwapCount (d : ℕ) : ℕ := 2 * (d - 1) + d / 2

/-- Sum the actual exposure/restore cost, skipping the already-inner zero. -/
theorem crtExposure_swap_sum (d : ℕ) :
    ((List.finRange d).map fun i => if i.val = 0 then 0 else 2).sum = 2 * (d - 1) := by
  cases d with
  | zero => simp
  | succ d =>
      simp [List.finRange_succ, List.map_map, Function.comp_def, Nat.mul_comm]

/-- Exposure and restoration costs plus the verified paired-reversal count. -/
theorem crtSchedule_swap_count (d : ℕ) :
    ((List.finRange d).map fun i => if i.val = 0 then 0 else 2).sum + d / 2 =
      crtLinearSwapCount d := by
  rw [crtExposure_swap_sum, crtLinearSwapCount]

/-- The complete forward layout route has the stated linear swap count. -/
theorem crtLinear_route (d : ℕ) :
    CrtAxisRoute (crtRevAx (d := d) d) (List.finRange d) (crtLinearSwapCount d) := by
  cases d with
  | zero => simpa [crtRevAx, crtLinearSwapCount] using CrtAxisRoute.refl ([] : List (Fin 0))
  | succ d =>
      have h := (crtTriangular_route (List.finRange (d + 1))).trans
        (crtAxisRoute_toFinRange (d + 1))
      simpa only [crtSchedule_swap_count] using h

/-- Reversing that route supplies the inverse layout schedule with the same bound. -/
theorem crtLinear_inverse_route (d : ℕ) :
    CrtAxisRoute (List.finRange d) (crtRevAx (d := d) d) (crtLinearSwapCount d) :=
  (crtLinear_route d).symm

end IntegerMultBounds.MathlibTM2.Fast
