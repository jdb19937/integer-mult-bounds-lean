module

public import IntegerMultBounds.MathlibTM2.M8.Global.CovarianceDataB
public import IntegerMultBounds.MathlibTM2.M8.Global.UseSlotsB
public import IntegerMultBounds.MathlibTM2.M8.Local.CovarianceRecurrenceB

/-! The checked mask tables give the actual design-B compiler readout coefficients. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Global.DesignB
noncomputable section
open IntegerMultBounds.MathlibTM2.M8.Local
open Classical
open CovarianceB MaskWeightsB AdjointB

def useCoefficient (t : Nat) (u : Use) : ZMod 2 := coeff (coefficientMasks.use u) t

def slotWeights (r : Nat) (f : Nat → ZMod 2) : Reg →₀ ZMod 2 :=
  ∑ s ∈ Finset.range r, Finsupp.single (.aux s) (f s)

theorem slotWeights_aux (r : Nat) (f : Nat → ZMod 2) (s : Nat) :
    slotWeights r f (.aux s) = if s < r then f s else 0 := by
  simp [slotWeights, Finsupp.finsetSum_apply, Finsupp.single_apply]

def garbageWeights (t : Nat) : Reg →₀ ZMod 2 :=
  slotWeights 28866 (fun s => coeff (slotMask s) t)

theorem garbageWeights_aux (t s : Nat) :
    garbageWeights t (.aux s) = coeff (slotMask s) t := by
  rw [garbageWeights, slotWeights_aux]
  by_cases hs : s < 28866
  · simp [hs]
  · simp [hs, slotMask]

/-- A newly allocated use has the same slot at its birth and in the final compiler state. -/
theorem allocated_step_slot (n : Nat) (hn : n < nodeCount) (i : Nat)
    (hi : i < (dagB.freeUses n).length) (hnew : n < leafCount ∨ i ≠ 0) :
    (dagB.step (dagB.compileTo n) n).pend (dagB.freeUses n)[i] =
      slotsBefore n + if n < leafCount then i else i - 1 := by
  have h := compiled_allocated_use_slot n hn i hi hnew
  have hu : (dagB.freeUses n)[i] ∈ dagB.freeUses n := List.getElem_mem hi
  have hs := dagB.srcNode_free hu
  rw [Dag.compile, FrameFlow.compileTo_pend_after_source dagB dagB_valid _
    (n + 1) dagB.N (by rw [hs]; omega) (Nat.succ_le_of_lt hn) le_rfl, compile_step] at h
  exact h

/-- Instantiate every allocation and argument equation from the kernel-checked masks. -/
theorem covariance_useRecurrence (t : Nat) :
    UseRecurrence dagB (useCoefficient t) (garbageWeights t) := by
  constructor
  · intro n hn u hu
    change n < leafCount at hn
    have hnN : n < nodeCount := hn.trans leafCount_lt
    have hm := (nodeOk_parts coefficientMasks n (bAt n) (covariance_node_checked n hnN)).1
    rw [ite_eq_left hn, ← dagB_freeUses_eq n hnN] at hm
    let i := (dagB.freeUses n).idxOf u
    have hi : i < (dagB.freeUses n).length := List.idxOf_lt_length_iff.mpr hu
    have he : (dagB.freeUses n)[i] = u := List.getElem_idxOf hi
    have hs := allocationOk_get coefficientMasks (slotsBefore n) (dagB.freeUses n) hm i hi
    rw [he] at hs
    rw [garbageWeights_aux]
    unfold useCoefficient
    rw [← hs, ← he, allocated_step_slot n hnN i hi (Or.inl hn), ite_eq_left hn]
    rfl
  · intro n hn hnN u hu
    change leafCount ≤ n at hn
    change n < nodeCount at hnN
    have hm := (nodeOk_parts coefficientMasks n (bAt n) (covariance_node_checked n hnN)).1
    rw [ite_eq_right (Nat.not_lt.mpr hn), ← dagB_freeUses_eq n hnN] at hm
    cases he : dagB.freeUses n with
    | nil => simp [he] at hu
    | cons v us =>
      simp only [he, List.tail_cons] at hu hm
      let i := us.idxOf u
      have hi : i < us.length := List.idxOf_lt_length_iff.mpr hu
      have hi' : i + 1 < (dagB.freeUses n).length := by simp [he]; omega
      have hue : (dagB.freeUses n)[i + 1] = u := by
        simpa only [he, List.getElem_cons_succ] using List.getElem_idxOf hi
      have hs := allocationOk_get coefficientMasks (slotsBefore n) us hm i hi
      rw [List.getElem_idxOf hi] at hs
      rw [garbageWeights_aux]
      unfold useCoefficient
      rw [← hs, ← hue, allocated_step_slot n hnN (i + 1) hi' (Or.inr (by omega)),
        ite_eq_right (Nat.not_lt.mpr hn)]
      simp only [Nat.add_sub_cancel]
      rfl
  · intro n hn hnN pos
    change leafCount ≤ n at hn
    change n < nodeCount at hnN
    have hm := (nodeOk_parts coefficientMasks n (bAt n) (covariance_node_checked n hnN)).2
    have ha := hm.resolve_left (Nat.not_lt.mpr hn)
    have hp : argumentOk coefficientMasks n (bAt n).2 pos = true := by cases pos; exact ha.1; exact ha.2
    have hf := argumentOk_coeff coefficientMasks n (bAt n).2 pos hp t
    rw [← dagB_freeUses_eq n hnN] at hf
    change coeff (coefficientMasks.argument n pos) t = _
    simp only [useCoefficient]
    change coeff (coefficientMasks.argument n pos) t =
      ((dagB.freeUses n).map fun u => coeff (coefficientMasks.use u) t).sum + _
    cases hl : (records.get width n).link with
    | none => simpa only [hl, dagB, dag, recAt, Option.map_none] using hf
    | some L => simpa only [hl, dagB, dag, recAt, Option.map_some, CovarianceB.Masks.use] using hf

/-- Every actual compiler covariance is the corresponding bit of the checked slot mask. -/
theorem covariance_eq_slotMask (s t : Nat) :
    dagB.cov targets s t = coeff (slotMask s) t := by
  have hslots : dagB.compile.next = 28866 := by
    change (dagB.compileTo nodeCount).next = 28866
    rw [dagB_compileTo_next nodeCount le_rfl]
    decide +kernel
  have h := UseRecurrence.cov_eq dagB dagB_valid targets t
    (useCoefficient t) (garbageWeights t) (covariance_useRecurrence t)
    (fun j hj => covariance_root_coefficient j hj t) (by
      intro s hs
      rw [hslots] at hs
      rw [garbageWeights_aux]
      simp [slotMask, Nat.not_lt.mpr hs]) s
  rw [garbageWeights_aux] at h
  exact h

end
end IntegerMultBounds.MathlibTM2.M8.Global.DesignB
