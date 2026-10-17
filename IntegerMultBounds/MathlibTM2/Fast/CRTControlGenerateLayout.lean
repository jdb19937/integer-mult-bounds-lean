module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerate
public import IntegerMultBounds.MathlibTM2.Fast.CRTSchedule
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Descriptor generation in the exposed physical order -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.MathlibTM2.Mult

/-- Completed physical prefix after visiting original nonzero axes below `m`.
The target's position emits the deferred axis-zero descriptor. -/
def crtControlGeneratedAxes {d : ℕ} (i : Fin (d + 1)) (m : ℕ) : List (Fin (d + 1)) :=
  ((crtRevAx m).filter fun j => j ≠ 0).map (Equiv.swap i 0)

@[simp] theorem crtControlGeneratedAxes_zero {d : ℕ} (i : Fin (d + 1)) :
    crtControlGeneratedAxes i 0 = [] := by simp [crtControlGeneratedAxes]

theorem crtControlGeneratedAxes_succ {d : ℕ} (i : Fin (d + 1)) {m : ℕ}
    (hm : m < d + 1) (hpos : 0 < m) :
    crtControlGeneratedAxes i (m + 1) =
      Equiv.swap i 0 ⟨m, hm⟩ :: crtControlGeneratedAxes i m := by
  have hn : (⟨m, hm⟩ : Fin (d + 1)) ≠ 0 := by intro h; have := congrArg Fin.val h; simp at this; omega
  simp [crtControlGeneratedAxes, crtRevAx_succ hm, hn]

@[simp] theorem crtControlGeneratedAxes_one {d : ℕ} (i : Fin (d + 1)) :
    crtControlGeneratedAxes i 1 = [] := by
  simp [crtControlGeneratedAxes, crtRevAx_succ (show 0 < d + 1 by omega)]

/-- The ascending traversal with packet prepending gives the true physical
prefix, including zero at the exchanged target position. -/
theorem crtControlGeneratedAxes_full {d : ℕ} (i : Fin (d + 1)) :
    crtControlGeneratedAxes i (d + 1) = crtExposePrefix i := by
  rw [crtControlGeneratedAxes, crtRevAx_eq_outer]
  have hz : ∀ j ∈ crtOuterAxes d, j ≠ 0 := by
    intro j hj
    simp only [crtOuterAxes, List.mem_reverse, List.mem_map] at hj
    obtain ⟨k, _, rfl⟩ := hj
    exact Fin.succ_ne_zero k
  have hf : (crtOuterAxes d).filter (fun j => j ≠ 0) = crtOuterAxes d := by
    apply List.filter_eq_self.mpr
    intro j hj
    simpa using hz j hj
  rw [List.filter_append, hf]
  simp [crtExposePrefix, crtAxisExchange]

/-- Width of the already emitted lower physical axes. -/
theorem crtControlGeneratedAxes_width {d : ℕ} (a : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) : ∀ m ≤ d + 1,
    crtW a (crtControlGeneratedAxes i m) =
      crtPre a m - (if m ≤ i.val then a 0 else a i) := by
  intro m
  induction m with
  | zero => intro hm; simp
  | succ m ih =>
    intro hm
    have hm' : m < d + 1 := by omega
    by_cases hm0 : m = 0
    · subst m
      by_cases hi : 0 < i.val
      · simp [crtPre_succ a (show 0 < d + 1 by omega), show 1 ≤ i.val by omega]
      · have hi0 : i = 0 := Fin.ext (by simpa using (show i.val = 0 by omega))
        subst i
        simp [crtPre_succ a (show 0 < d + 1 by omega)]
    · have hpos : 0 < m := by omega
      rw [crtControlGeneratedAxes_succ i hm' hpos, crtW_cons, ih (by omega), crtPre_succ a hm']
      have ha0 : a 0 ≤ crtPre a m := by
        have h := crtPre_add_le a (0 : Fin (d + 1)) hpos
        simpa using h
      by_cases hmi : m < i.val
      · have hn : (⟨m, hm'⟩ : Fin (d + 1)) ≠ i := by intro h; have := congrArg Fin.val h; simp at this; omega
        have hz : (⟨m, hm'⟩ : Fin (d + 1)) ≠ 0 := by intro h; have := congrArg Fin.val h; simp at this; omega
        rw [Equiv.swap_apply_of_ne_of_ne hn hz]
        simp only [show m + 1 ≤ i.val by omega, show m ≤ i.val by omega, ite_true]
        omega
      · by_cases heq : m = i.val
        · have hj : (⟨m, hm'⟩ : Fin (d + 1)) = i := Fin.ext heq
          rw [hj, Equiv.swap_apply_left]
          simp only [show ¬m + 1 ≤ i.val by omega, show m ≤ i.val by omega, ite_false, ite_true]
          omega
        · have hgt : i.val < m := by omega
          have hai : a i ≤ crtPre a m := by have := crtPre_add_le a i hgt; omega
          have hn : (⟨m, hm'⟩ : Fin (d + 1)) ≠ i := by intro h; have := congrArg Fin.val h; simp at this; omega
          have hz : (⟨m, hm'⟩ : Fin (d + 1)) ≠ 0 := by intro h; have := congrArg Fin.val h; simp at this; omega
          rw [Equiv.swap_apply_of_ne_of_ne hn hz]
          simp only [show ¬m + 1 ≤ i.val by omega, show ¬m ≤ i.val by omega, ite_false]
          omega

/-- Closed arithmetic field produced for original axis `j`; its weight
always remains the original mixed-radix prefix product. -/
def crtControlAxisField {d : ℕ} (a s : Fin (d + 1) → ℕ)
    (i j : Fin (d + 1)) : CrtControlField :=
  ⟨2 ^ (if j.val < i.val then
      (if j.val = 0 then crtPre a i.val else crtPre a j.val) - a 0
    else crtPre a j.val - a i), s j, prefixProd s j, decide (j.val < i.val)⟩

/-- Connect the executable arithmetic kernel to the layout field. The
omitted target is excluded; axis zero uses the target's original prefix width. -/
theorem crtControlGeneratedField_eq_axisField {d A : ℕ} (a s : Fin (d + 1) → ℕ)
    (i j : Fin (d + 1)) (hji : j ≠ i) (st : TableVM.TblSt 10 A)
    (h0 : st.val 0 = j.val) (h1 : st.val 1 = i.val)
    (h2 : st.val 2 = 2 ^ crtPre a j.val) (h3 : st.val 3 = 2 ^ a i)
    (h4 : st.val 4 = 2 ^ a 0) (h5 : st.val 5 = s j)
    (h6 : st.val 6 = prefixProd s j) (h9 : st.val 9 = 2 ^ crtPre a i.val) :
    crtControlGeneratedField st = crtControlAxisField a s i j := by
  apply crtControlGeneratedField_spec s j i (crtPre a j.val) (crtPre a i.val) (a i) (a 0)
    st h0 h1 h2 h3 h4 h5 h6 h9
  · intro hlt
    by_cases hz : j.val = 0
    · rw [ite_eq_left hz]
      have h := crtPre_add_le a (0 : Fin (d + 1)) (show 0 < i.val by omega)
      simpa using h
    · rw [ite_eq_right hz]
      have h := crtPre_add_le a (0 : Fin (d + 1)) (show 0 < j.val by omega)
      simpa using h
  · intro hlt
    have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
    have h := crtPre_add_le a i (show i.val < j.val by omega)
    omega

/-- At an ascending emission slot, the arithmetic place is exactly the
width of the physical prefix already generated. -/
theorem crtControlAxisField_emit {d : ℕ} (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) {m : ℕ} (hm : m < d + 1) (hpos : 0 < m) :
    crtControlAxisField a s i (Equiv.swap i 0 ⟨m, hm⟩) =
      ⟨2 ^ crtW a (crtControlGeneratedAxes i m),
        s (Equiv.swap i 0 ⟨m, hm⟩), prefixProd s (Equiv.swap i 0 ⟨m, hm⟩),
        decide ((Equiv.swap i 0 ⟨m, hm⟩).val < i.val)⟩ := by
  rw [crtControlGeneratedAxes_width a i m hm.le]
  by_cases heq : m = i.val
  · have hj : (⟨m, hm⟩ : Fin (d + 1)) = i := Fin.ext heq
    rw [hj, Equiv.swap_apply_left]
    simp [crtControlAxisField, show 0 < i.val by omega, heq]
  · have hn : (⟨m, hm⟩ : Fin (d + 1)) ≠ i := by intro h; exact heq (congrArg Fin.val h)
    have hz : (⟨m, hm⟩ : Fin (d + 1)) ≠ 0 := by intro h; have := congrArg Fin.val h; simp at this; omega
    rw [Equiv.swap_apply_of_ne_of_ne hn hz]
    by_cases hlt : m < i.val
    · simp [crtControlAxisField, hlt, show m ≠ 0 by omega, show m ≤ i.val by omega]
    · simp [crtControlAxisField, hlt, show ¬m ≤ i.val by omega]

/-- Ascending original-axis traversal with packet prepending. Original zero
is parked, and its descriptor is emitted at the target's positive slot;
target zero instead omits zero and emits all the positive spectators. -/
def crtControlGeneratedFields {d : ℕ} (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) : ℕ → List CrtControlField
  | 0 => []
  | m + 1 => if hm : m < d + 1 then
      if m = 0 then crtControlGeneratedFields a s i m
      else crtControlAxisField a s i (Equiv.swap i 0 ⟨m, hm⟩) ::
        crtControlGeneratedFields a s i m
    else crtControlGeneratedFields a s i m

/-- Every intermediate generated tape has exactly the descriptors for its
physical prefix, including the correct suffix place values. -/
theorem crtControlGeneratedFields_eq {d : ℕ} (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) : ∀ m ≤ d + 1,
    crtControlGeneratedFields a s i m =
      crtControlFields a s i.val (crtControlGeneratedAxes i m) := by
  intro m
  induction m with
  | zero => intro hm; simp [crtControlGeneratedFields, crtControlFields]
  | succ m ih =>
    intro hm
    have hm' : m < d + 1 := by omega
    by_cases hz : m = 0
    · subst m; simp [crtControlGeneratedFields, crtControlFields]
    · rw [crtControlGeneratedFields, dite_eq_left hm', ite_eq_right hz,
        crtControlGeneratedAxes_succ i hm' (by omega), crtControlFields,
        ih (by omega), crtControlAxisField_emit a s i hm' (by omega)]

/-- The final prepended descriptor tape is exactly the exposed-layout tape. -/
theorem crtControlGeneratedFields_full {d : ℕ} (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) :
    crtControlGeneratedFields a s i (d + 1) =
      crtControlFields a s i.val (crtExposePrefix i) := by
  rw [crtControlGeneratedFields_eq a s i (d + 1) le_rfl, crtControlGeneratedAxes_full]

/-- Target zero has no deferred packet: all positive axes are spectators. -/
theorem crtControlGeneratedFields_zero_target {d : ℕ} (a s : Fin (d + 1) → ℕ) :
    crtControlGeneratedFields a s 0 (d + 1) = crtControlFields a s 0 (crtOuterAxes d) := by
  rw [crtControlGeneratedFields_full]
  simp [crtExposePrefix]

end IntegerMultBounds.MathlibTM2.Fast
