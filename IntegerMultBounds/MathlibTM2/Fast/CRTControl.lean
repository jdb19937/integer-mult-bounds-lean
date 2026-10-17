module

import IntegerMultBounds.MathlibTM2.Fast.CRTSpec
public import IntegerMultBounds.MathlibTM2.Fast.CRTRot
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# CRT controls independent of the physical axis order

The old rotation scanner obtains its control value by counting valid preceding
fibers. That requires the controls in reverse axis order. Here a runtime list
of descriptors instead decodes an address and sums the original mixed-radix
weights. The semantic contract works in any duplicate-free layout containing
all the lower axes, including layouts produced by distant swaps.

These are arithmetic specifications for the replacement scanner, not yet its
finite-machine implementation or a changed multiplication time bound.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.MathlibTM2.Mult

/-- One physical address field: place value, validity bound, mixed-radix weight,
and whether this axis controls the current rotation. -/
structure CrtControlField where
  place : ℕ
  bound : ℕ
  weight : ℕ
  active : Bool

/-- Descriptors follow physical order; weights retain the original arithmetic order. -/
def crtControlFields {d : ℕ} (a s : Fin d → ℕ) (i : ℕ) :
    List (Fin d) → List CrtControlField
  | [] => []
  | j :: o => ⟨2 ^ crtW a o, s j, prefixProd s j, decide (j.val < i)⟩ ::
      crtControlFields a s i o

/-- Decode each field and accumulate its original mixed-radix contribution. -/
def crtControlValue : List CrtControlField → ℕ → ℕ
  | [], _ => 0
  | f :: fs, F => (if f.active then F / f.place * f.weight else 0) +
      crtControlValue fs (F % f.place)

/-- Only lower axes constrain the validity of this rotation's controls. -/
def crtControlValid : List CrtControlField → ℕ → Bool
  | [], _ => true
  | f :: fs, F => (!f.active || decide (F / f.place < f.bound)) &&
      crtControlValid fs (F % f.place)

lemma crtControlValue_eq {d : ℕ} (a s : Fin d → ℕ) (i : ℕ)
    (o : List (Fin d)) (ho : o.Nodup) (F : ℕ) (x : Fin d → ℕ) :
    crtControlValue (crtControlFields a s i o) F =
      (o.map fun j => if j.val < i then crtDec a o F x j * prefixProd s j else 0).sum := by
  induction o generalizing F x with
  | nil => rfl
  | cons j o ih =>
      have hj := (List.nodup_cons.mp ho).1
      have ht := (List.nodup_cons.mp ho).2
      simp only [crtControlFields, crtControlValue, decide_eq_true_eq,
        List.map_cons, List.sum_cons, crtDec_cons]
      rw [ih ht (F % 2 ^ crtW a o) (Function.update x j (F / 2 ^ crtW a o)),
        crtDec_apply_of_not_mem a o _ _ j hj, Function.update_self]

lemma crtControlValid_eq {d : ℕ} (a s : Fin d → ℕ) (i : ℕ)
    (o : List (Fin d)) (ho : o.Nodup) (F : ℕ) (x : Fin d → ℕ) :
    crtControlValid (crtControlFields a s i o) F = true ↔
      ∀ j ∈ o, j.val < i → crtDec a o F x j < s j := by
  induction o generalizing F x with
  | nil => simp [crtControlFields, crtControlValid]
  | cons j o ih =>
      have hj := (List.nodup_cons.mp ho).1
      have ht := (List.nodup_cons.mp ho).2
      simp only [crtControlFields, crtControlValid, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq, List.forall_mem_cons,
        crtDec_cons]
      rw [ih ht (F % 2 ^ crtW a o) (Function.update x j (F / 2 ^ crtW a o)),
        crtDec_apply_of_not_mem a o _ _ j hj, Function.update_self]
      by_cases hji : j.val < i <;> simp [hji]

/-- Summing the original weights in any layout containing all controls gives `crtKI`. -/
lemma crtControl_sum_eq {d : ℕ} (s : Fin d → ℕ) (i : ℕ)
    (o : List (Fin d)) (ho : o.Nodup) (hctrl : ∀ j : Fin d, j.val < i → j ∈ o)
    (y : Fin d → ℕ) :
    (o.map fun j => if j.val < i then y j * prefixProd s j else 0).sum = crtKI s i y := by
  classical
  rw [← List.sum_toFinset _ ho]
  rw [crtKI, Finset.sum_filter]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  have hji : ¬j.val < i := fun h => hj (List.mem_toFinset.mpr (hctrl j h))
  simp [hji]

/-- The control evaluator computes the original CRT offset in an arbitrary layout. -/
theorem crtControlValue_eq_crtKI {d : ℕ} (a s : Fin d → ℕ) (i : ℕ)
    (o : List (Fin d)) (ho : o.Nodup) (hctrl : ∀ j : Fin d, j.val < i → j ∈ o)
    (F : ℕ) (x : Fin d → ℕ) :
    crtControlValue (crtControlFields a s i o) F = crtKI s i (crtDec a o F x) := by
  rw [crtControlValue_eq a s i o ho F x]
  exact crtControl_sum_eq s i o ho hctrl _

/-- Spectator axes are ignored; validity agrees with the original triangular map. -/
theorem crtControlValid_eq_controls {d : ℕ} (a s : Fin d → ℕ) (i : ℕ)
    (o : List (Fin d)) (ho : o.Nodup) (hctrl : ∀ j : Fin d, j.val < i → j ∈ o)
    (F : ℕ) (x : Fin d → ℕ) :
    crtControlValid (crtControlFields a s i o) F = true ↔
      ∀ j : Fin d, j.val < i → crtDec a o F x j < s j := by
  rw [crtControlValid_eq a s i o ho F x]
  exact ⟨fun h j hj => h j (hctrl j hj) hj, fun h j _ hj => h j hj⟩

/-- The same cyclic shift computed by one multiplication and remainder,
rather than by iterating once per earlier valid fiber. -/
def crtControlShift (fwd : Bool) (S μ K : ℕ) : ℕ :=
  if fwd then S - (μ * K) % S else (μ * K) % S

lemma crtControlShift_mod (fwd : Bool) (S μ K : ℕ) (hS : 0 < S) (hμ : μ ≤ S) :
    crtControlShift fwd S μ K % S = crtShift fwd S μ K % S := by
  rw [← ZMod.natCast_eq_natCast_iff']
  cases fwd
  · change ((μ * K % S : ℕ) : ZMod S) = (crtLo S μ K : ZMod S)
    rw [ZMod.natCast_mod, Nat.cast_mul]
    exact (crtLo_cast S μ K).symm
  · change ((S - (μ * K) % S : ℕ) : ZMod S) = ((S - crtLo S μ K : ℕ) : ZMod S)
    rw [Nat.cast_sub (Nat.mod_lt _ hS).le, Nat.cast_sub (crtLo_le hμ K),
      ZMod.natCast_mod, Nat.cast_mul, crtLo_cast]

lemma crtControlShift_rotate {α : Type*} (l : List α) (fwd : Bool) (S μ K : ℕ)
    (hlen : l.length = S) (hS : 0 < S) (hμ : μ ≤ S) :
    l.rotate (crtControlShift fwd S μ K) = l.rotate (crtShift fwd S μ K) := by
  rw [← List.rotate_mod l (crtControlShift fwd S μ K),
    ← List.rotate_mod l (crtShift fwd S μ K), hlen, crtControlShift_mod fwd S μ K hS hμ]

/-- Slots of a target fiber in an arbitrary physical prefix layout. -/
def crtControlSlots {d : ℕ} {α : Type*} (a : Fin d → ℕ)
    (pre : List (Fin d)) (i : Fin d) (post : List (Fin d))
    (C : (Fin d → ℕ) → List α) (F : ℕ) : List (List α) :=
  (List.range (2 ^ a i)).map fun z =>
    (crtBox a post C (Function.update (crtDec a pre F 0) i z)).flatten

/-- The descriptor evaluator gives exactly the original rotation, including
invalid controls and the padding beyond the target modulus. -/
theorem crtControlRot_fiber {d : ℕ} {α : Type*} (a s : Fin d → ℕ)
    {i : ℕ} (hi : i < d) (pre post : List (Fin d))
    (hnd : (pre ++ (⟨i, hi⟩ : Fin d) :: post).Nodup)
    (hctrl : ∀ j : Fin d, j.val < i → j ∈ pre)
    (hs : s ⟨i, hi⟩ ≤ 2 ^ a ⟨i, hi⟩)
    (μ : ℕ) (fwd : Bool) (C : (Fin d → ℕ) → List α) (F : ℕ) :
    (crtBox a ((⟨i, hi⟩ : Fin d) :: post) (crtRotC s i hi μ fwd C)
      (crtDec a pre F 0)).flatten =
      if crtControlValid (crtControlFields a s i pre) F then
        (((crtControlSlots a pre ⟨i, hi⟩ post C F).take (s ⟨i, hi⟩)).rotate
          (crtShift fwd (s ⟨i, hi⟩) μ
            (crtControlValue (crtControlFields a s i pre) F)) ++
          (crtControlSlots a pre ⟨i, hi⟩ post C F).drop (s ⟨i, hi⟩)).flatten
      else (crtControlSlots a pre ⟨i, hi⟩ post C F).flatten := by
  have hparts := List.nodup_append.mp hnd
  have hIp := (List.nodup_cons.mp hparts.2.1).1
  have hjp : ∀ j : Fin d, j.val < i → j ∉ post := by
    intro j hj hjpost
    exact hparts.2.2 j (hctrl j hj) j (List.mem_cons_of_mem _ hjpost) rfl
  set I : Fin d := ⟨i, hi⟩ with hI
  set y₀ := crtDec a pre F 0 with hy₀
  have hval : crtControlValid (crtControlFields a s i pre) F = true ↔
      ∀ j : Fin d, j.val < i → y₀ j < s j :=
    crtControlValid_eq_controls a s i pre hparts.1 hctrl F 0
  have hw : ∀ e z, ∀ j : Fin d, j.val < i → crtDec a post e (Function.update y₀ I z) j = y₀ j := by
    intro e z j hj
    rw [crtDec_apply_of_not_mem a post e _ j (hjp j hj), Function.update_of_ne]
    intro h; rw [h] at hj; simp [hI] at hj
  have hwI : ∀ e z, crtDec a post e (Function.update y₀ I z) I = z := by
    intro e z; rw [crtDec_apply_of_not_mem a post e _ I hIp, Function.update_self]
  have hK : ∀ e z, crtKI s i (crtDec a post e (Function.update y₀ I z)) =
      crtControlValue (crtControlFields a s i pre) F := by
    intro e z
    rw [crtKI_congr s (hw e z), crtControlValue_eq_crtKI a s i pre hparts.1 hctrl F 0]
  have hupd : ∀ e z v, Function.update (crtDec a post e (Function.update y₀ I z)) I v =
      crtDec a post e (Function.update y₀ I v) := by
    intro e z v
    rw [← crtDec_update_of_not_mem a post e _ I v hIp, Function.update_idem]
  rw [crtBox_cons, crt_flatten_flatMap]
  by_cases hv : crtControlValid (crtControlFields a s i pre) F = true
  · rw [ite_eq_left hv, crt_rot_getElem _ (2 ^ a I) _ _ (by simp [crtControlSlots, hI]) hs,
      List.flatMap_def]
    congr 1
    refine List.map_congr_left fun z hz => ?_
    have hz' := List.mem_range.1 hz
    have hσ : (if z < s I then (z + crtShift fwd (s I) μ
        (crtControlValue (crtControlFields a s i pre) F)) % s I else z) < 2 ^ a I := by
      split_ifs with h
      · exact lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hs
      · exact hz'
    rw [List.getD_eq_getElem _ _ (by simp [crtControlSlots]; exact hσ)]
    simp only [crtControlSlots, List.getElem_map, List.getElem_range]
    congr 1
    rw [crtBox, crtBox]
    refine List.map_congr_left fun e _ => ?_
    rw [crtRotC]
    have hvalw : (∀ j : Fin d, j.val < i → crtDec a post e (Function.update y₀ I z) j < s j) := by
      intro j hj; rw [hw e z j hj]; exact (hval.1 hv) j hj
    by_cases hzs : z < s I
    · rw [ite_eq_left ⟨hvalw, by rw [hwI]; exact hzs⟩, ite_eq_left hzs, hwI, hK, hupd]
    · rw [ite_eq_right (fun h => hzs (by have := h.2; rwa [hwI] at this)), ite_eq_right hzs]
  · rw [ite_eq_right hv, crtControlSlots, List.flatMap_def]
    congr 1
    refine List.map_congr_left fun z _ => ?_
    congr 1
    rw [crtBox, crtBox]
    refine List.map_congr_left fun e _ => ?_
    rw [crtRotC, ite_eq_right]
    rintro ⟨h, _⟩
    exact hv (hval.2 fun j hj => by rw [← hw e z j hj]; exact h j hj)

/-- Output of one fiber using a directly computed modular control. -/
def crtControlRotOut {d : ℕ} {α : Type*} (a s : Fin d → ℕ)
    (pre : List (Fin d)) (i : Fin d) (post : List (Fin d)) (μ : ℕ) (fwd : Bool)
    (C : (Fin d → ℕ) → List α) (F : ℕ) : List α :=
  let slots := crtControlSlots a pre i post C F
  if crtControlValid (crtControlFields a s i.val pre) F then
    ((slots.take (s i)).rotate (crtControlShift fwd (s i) μ
      (crtControlValue (crtControlFields a s i.val pre) F)) ++ slots.drop (s i)).flatten
  else slots.flatten

/-- Recomputing controls for each physical fiber preserves the complete CRT
rotation, including invalid addresses and padding, in either direction. -/
theorem crtControlRotOut_top {d : ℕ} {α : Type*} (a s : Fin d → ℕ)
    (pre : List (Fin d)) (i : Fin d) (post : List (Fin d))
    (hnd : (pre ++ i :: post).Nodup) (hctrl : ∀ j : Fin d, j.val < i.val → j ∈ pre)
    (hs : 0 < s i ∧ s i ≤ 2 ^ a i) (μ : ℕ) (hμ : μ ≤ s i) (fwd : Bool)
    (C : (Fin d → ℕ) → List α) :
    (List.range (2 ^ crtW a pre)).flatMap (crtControlRotOut a s pre i post μ fwd C) =
      (crtBox a (pre ++ i :: post) (crtRotC s i.val i.isLt μ fwd C) 0).flatten := by
  rw [crtBox_append, crt_flatten_flatMap]
  refine List.flatMap_congr fun F _ => ?_
  rw [crtControlRot_fiber a s i.isLt pre post hnd hctrl hs.2 μ fwd C F]
  unfold crtControlRotOut
  dsimp only
  split_ifs
  · rw [crtControlShift_rotate ((crtControlSlots a pre i post C F).take (s i)) fwd (s i) μ _ (by simp [crtControlSlots, Nat.min_eq_left hs.2])
      hs.1 hμ]
  · rfl

end IntegerMultBounds.MathlibTM2.Fast
