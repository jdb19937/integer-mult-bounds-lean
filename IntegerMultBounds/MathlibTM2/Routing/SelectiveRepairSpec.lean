module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveIdeal
public import IntegerMultBounds.MathlibTM2.Routing.SelectivePasses
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveDensity
public import IntegerMultBounds.MathlibTM2.Node.RepairPass
public import IntegerMultBounds.Compact.Repair

/-!
# Exact selective repair: permutation and record specification

The actual schedule and the all-address ideal agree off the physical bad set.
The ideal preserves that set, hence so does the actual schedule. The existing
stable-sort repair mathematics then supplies the two record partition identities
required by the concrete scan/sort/merge program. Classifier and key execution
remain separate obligations; no code oracle is used as an executed program here.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
  (hs : ∀ c, (s c).Allowed active) (R : ℕ)

theorem selectivePerm_agrees (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X)))
    (hi : Good p (selectiveView p X i)) :
    listPerm (selectivePerm p X hG hK hGK active s R) progW i =
      selectiveIdealPerm hK active s R hs i := by
  apply Fin.ext
  exact selectiveProgramPerm_good p X hG hK hGK active s R hs i hi

include hs in
/-- The packed schedule does not move exceptional records into good holes. -/
theorem selectivePerm_bad (i : Fin (R * 2 ^ fieldsLen (selectiveLen p X))) :
    (¬ Good p (selectiveView p X
      (listPerm (selectivePerm p X hG hK hGK active s R) progW i))) ↔
      ¬ Good p (selectiveView p X i) := by
  apply IntegerMultBounds.Compact.actual_preserves_bad
    (listPerm (selectivePerm p X hG hK hGK active s R) progW)
    (selectiveIdealPerm hK active s R hs)
    (fun i => ¬ Good p (selectiveView p X i))
  · intro j
    exact not_congr (selectiveIdeal_good hK active s j)
  · intro j hj
    exact selectivePerm_agrees p X hG hK hGK active s hs R j (not_not.mp hj)

noncomputable def selectiveBadCode (p : Par) (X i : ℕ) : Fin 2 := by
  classical
  exact if ¬ Good p (selectiveView p X i) then 1 else 0

include hG in
/-- One extra zero column flushes the final segment, including zero-width suffixes.
The automaton values and phase mask do not depend on the suffix width. -/
theorem selectiveBadCode_padded {A : ℕ} (hA : 4 ≤ A) (hguard : p.G + 1 < p.K) (i : ℕ) :
    (badC A hA).eval (p.wy + 1) (badVals p (selectiveView p X i)) =
      selectiveBadCode p X i := by
  classical
  have he := badC_eval (p := { p with m := p.m + 1 }) hA hG hguard
    (show 0 < p.m + 1 from Nat.succ_pos _) (selectiveView p X i)
  have hvals : badVals { p with m := p.m + 1 } (selectiveView p X i) =
      badVals p (selectiveView p X i) := rfl
  have hgood : Good { p with m := p.m + 1 } (selectiveView p X i) =
      Good p (selectiveView p X i) := rfl
  rw [hvals, hgood] at he
  have hv : (badC A hA).eval (p.wy + 1) (badVals p (selectiveView p X i)) =
      if Good p (selectiveView p X i) then 0 else 1 := by
    simpa only [Par.wy, Nat.add_assoc] using he
  by_cases hg : Good p (selectiveView p X i) <;> simpa [selectiveBadCode, hg] using hv

/-- Good records already match; sorting exceptional destination keys supplies the
remaining records in the exact order needed by the executed merge. -/
theorem selectiveRepair_partition {A : ℕ} (k : ℕ)
    (hk : R * 2 ^ fieldsLen (selectiveLen p X) ≤ 2 ^ k)
    (l : List (List (Fin (A + 4)))) :
    let actual := listPerm (selectivePerm p X hG hK hGK active s R) progW
    let ideal := selectiveIdealPerm hK active s R hs
    let keyed := keyRecs k ideal l
    codeRecs (moveRecs actual keyed) (selectiveBadCode p X) 0 =
        codeRecs (moveRecs ideal keyed) (selectiveBadCode p X) 0 ∧
      RadixSort.sort (fun rec j => symBit (rec.getD j 0)) k
        (codeRecs (moveRecs actual keyed) (selectiveBadCode p X) 1) =
        codeRecs (moveRecs ideal keyed) (selectiveBadCode p X) 1 := by
  classical
  let actual := listPerm (selectivePerm p X hG hK hGK active s R) progW
  let ideal := selectiveIdealPerm hK active s R hs
  let bad := fun i : Fin (R * 2 ^ fieldsLen (selectiveLen p X)) =>
    ¬ Good p (selectiveView p X i)
  have hp : ∀ i, bad (ideal i) ↔ bad i := fun i =>
    not_congr (selectiveIdeal_good hK active s i)
  have ha : ∀ i, ¬ bad i → actual i = ideal i := fun i hi =>
    selectivePerm_agrees p X hG hK hGK active s hs R i (not_not.mp hi)
  have hc : ∀ i : Fin (R * 2 ^ fieldsLen (selectiveLen p X)), selectiveBadCode p X i = if bad i then 1 else 0 := fun _ => rfl
  exact ⟨repair_good_of (Equiv.refl _) (πS := actual) (πT := ideal)
      (code := selectiveBadCode p X) hp ha hc (fun _ => rfl) (fun _ => rfl) k l,
    repair_bad_of (Equiv.refl _) (πS := actual) (πT := ideal)
      (code := selectiveBadCode p X) hp ha hc (fun _ => rfl) (fun _ => rfl) k hk l⟩

open Classical in
/-- Extraction counts precisely the physical bad ranks, regardless of payloads. -/
theorem selectiveBad_records {α : Type} (records : List (List α))
    (hlen : records.length = R * 2 ^ fieldsLen (selectiveLen p X)) :
    (codeRecs records (selectiveBadCode p X) 1).length =
      ((Finset.range (R * 2 ^ fieldsLen (selectiveLen p X))).filter
        fun i => ¬ Good p (selectiveView p X i)).card := by
  unfold codeRecs
  rw [List.length_map, hlen]
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1
  ext i
  simp [selectiveBadCode]

end IntegerMultBounds.MathlibTM2.Routing
