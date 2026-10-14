module

public import IntegerMultBounds.Schoenhage.DriverTwist
public import IntegerMultBounds.Schoenhage.RingPointwise

/-! The twist block at rest between rounds (§6 task 6): the constant words of the twist machine,
the counter at `bits n 0` and the `2^n` ticks, all else empty (`twRest`). From rest, with the array
words on tape 0 and the round's table on tape 16, the clean twist and untwist meet the hypothesis of
`runs_twistStep` (`runs_twistRest`, `runs_untwistRest`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct TwistDescriptors

/-- The twist block between rounds, for records of ring degree `r` and `M` records. -/
def twRest (r n M : ℕ) : Fin 29 → WTape := fun j =>
  if j = 3 then reg (ones (2 * r)) else if j = 15 then reg (bits n 0)
  else if j = 17 then ⟨[], List.replicate M []⟩ else if j = 22 then reg (ones (4 * r - 1))
  else if j = 23 then reg (ones (4 * r)) else if j = 24 then reg (ones (2 * r - 1))
  else if j = 25 then reg (ones (2 * r)) else emp

theorem cut_array_arrWords {r w : ℕ} (hw : 1 ≤ w) (fs : List (Rec r)) :
    cut w (array w fs) = TwistArray.arrWords w fs := by
  rw [array_words, cut_flatten_words hw]
  · simp [TwistArray.arrWords, List.flatMap]
  · intro c hc
    simp only [List.mem_flatten, List.mem_map] at hc
    obtain ⟨l, ⟨f, -, rfl⟩, hl⟩ := hc
    exact recordWords_lengths w f.1 f.2 c hl

variable {r : ℕ} [NeZero r]

/-- The rest state with the array words and a table loaded. -/
def twLoad (n w : ℕ) (fs : List (Rec r)) (tab : List (List Bool)) : Fin 29 → WTape :=
  Function.update (Function.update (twRest r n (2 ^ n)) 0 ⟨[], cut w (array w fs)⟩) 16 ⟨[], tab⟩

theorem genPre_twLoad {n : ℕ} (π : BitPerm n) (ts Is : List ℕ) (h w : ℕ) (fs : List (Rec r))
    (hM : fs.length = 2 ^ n) :
    GenPre π r ts Is h fs.length (twLoad n w fs (tableWords (slotTable π r ts Is h)) ∘ φ) := by
  rw [hM]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) [twLoad, twRest, φ, Function.update_apply]

theorem idle_twLoad (n w : ℕ) (fs : List (Rec r)) (tab : List (List Bool)) :
    TwistArray.Idle r (twLoad n w fs tab ∘ ψ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := {decide := true}) [twLoad, twRest, ψ, Function.update_apply]

/-- The forward round's clean twist from rest. -/
theorem runs_twistRest {n : ℕ} (π : BitPerm n) (ts : List ℕ) (h : ℕ)
    (hpos : ∀ i ∈ slotAxes ts h, axOff ts i + h < n) (w : ℕ) (hw : 1 ≤ w) (fs : List (Rec r))
    (hM : fs.length = 2 ^ n) :
    Runs slotTwistClean (twLoad n w fs (tableWords (slotTable π r ts (slotAxes ts h) h)))
      (· = Function.update (Function.update (twLoad n w fs (tableWords (slotTable π r ts (slotAxes ts h) h)))
        0 ⟨(cut w (array w fs)).reverse, []⟩)
        1 ⟨(cut w (array w (TwistRound.twistRecs (slotExp π r ts (slotAxes ts h) h) fs))).reverse, []⟩)
      (cleanCost n r w fs.length (slotTable π r ts (slotAxes ts h) h)) := by
  obtain ⟨-, hrun⟩ := runs_slotTwistClean π ts (slotAxes ts h) h hpos 0 w fs _
    (genPre_twLoad π ts (slotAxes ts h) h w fs hM) (idle_twLoad n w fs _) (Lx := []) (R := []) (D := [])
    (by simp [twLoad, cut_array_arrWords hw]) (by simp (config := {decide := true}) [twLoad, twRest, emp])
  refine hrun.mono (fun τ e => ?_) le_rfl
  rw [e, hM, bits_pow_self, cut_array_arrWords hw, cut_array_arrWords hw]
  funext j
  simp only [Function.update_apply, List.append_nil]
  split_ifs <;> (try subst_vars) <;> simp_all (config := {decide := true}) [twLoad, twRest]

/-- The opposite round's clean untwist from rest. -/
theorem runs_untwistRest {n : ℕ} (π : BitPerm n) (ts : List ℕ) (h : ℕ)
    (hpos : ∀ i ∈ slotAxes ts h, axOff ts i + h < n) (w : ℕ) (hw : 1 ≤ w) (fs : List (Rec r))
    (hM : fs.length = 2 ^ n) :
    Runs slotUntwistClean (twLoad n w fs (tableWords (slotTable π r ts (slotAxes ts h) h)))
      (· = Function.update (Function.update (twLoad n w fs (tableWords (slotTable π r ts (slotAxes ts h) h)))
        0 ⟨(cut w (array w fs)).reverse, []⟩)
        1 ⟨(cut w (array w (TwistRound.untwistRecs (slotExp π r ts (slotAxes ts h) h) fs))).reverse, []⟩)
      (cleanCost n r w fs.length (slotTable π r ts (slotAxes ts h) h)) := by
  obtain ⟨-, hrun⟩ := runs_slotUntwistClean π ts (slotAxes ts h) h hpos 0 w fs _
    (genPre_twLoad π ts (slotAxes ts h) h w fs hM) (idle_twLoad n w fs _) (Lx := []) (R := []) (D := [])
    (by simp [twLoad, cut_array_arrWords hw]) (by simp (config := {decide := true}) [twLoad, twRest, emp])
  refine hrun.mono (fun τ e => ?_) le_rfl
  rw [e, hM, bits_pow_self, cut_array_arrWords hw, cut_array_arrWords hw]
  funext j
  simp only [Function.update_apply, List.append_nil]
  split_ifs <;> (try subst_vars) <;> simp_all (config := {decide := true}) [twLoad, twRest]

end IntegerMultBounds.Schoenhage
