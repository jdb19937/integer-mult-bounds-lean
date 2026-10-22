module

public import IntegerMultBounds.MathlibTM2.Routing.PatternGate

/-!
# Sparse source-pattern descriptors

A structural list search compiles an injective placement into optional source
selectors. The resulting gate word is the sparse `placeVal` expression used by
the packed gadget. Gaps are explicit zero selectors; repeated source wires are
allowed. This is descriptor correctness, not a free descriptor-generation call.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks

/-- Find the placed input for an output position, or request zero in a gap. -/
def sparsePattern {W m L : ℕ} (pos : ℕ → ℕ) (src : Fin m → Option (Fin W))
    (q : Fin L) : Option (Fin W) :=
  ((List.finRange m).find? (fun j => decide (pos j.val = q.val))).bind src

private theorem find_position {m : ℕ} {pos : ℕ → ℕ} (hpos : StrictMono pos) (j : Fin m) :
    (List.finRange m).find? (fun k => decide (pos k.val = pos j.val)) = some j := by
  cases hf : (List.finRange m).find? (fun k => decide (pos k.val = pos j.val)) with
  | none =>
    have hn := List.find?_eq_none.mp hf j (List.mem_finRange j)
    simp at hn
  | some k =>
    have hk : pos k.val = pos j.val := by simpa using List.find?_some hf
    have hkj : k = j := Fin.ext (hpos.injective hk)
    simp [hkj]

theorem sparsePattern_at {W m L : ℕ} {pos : ℕ → ℕ} (hpos : StrictMono pos)
    (src : Fin m → Option (Fin W)) (hbound : ∀ j < m, pos j < L) (j : Fin m) :
    sparsePattern pos src ⟨pos j.val, hbound _ j.isLt⟩ = src j := by
  simp only [sparsePattern, find_position hpos, Option.bind_some]

theorem sparsePattern_off {W m L : ℕ} (pos : ℕ → ℕ) (src : Fin m → Option (Fin W))
    (q : Fin L) (hq : ¬ ∃ j : Fin m, pos j.val = q.val) : sparsePattern pos src q = none := by
  have hf : (List.finRange m).find? (fun j => decide (pos j.val = q.val)) = none := by
    rw [List.find?_eq_none]
    intro j _ hj
    exact hq ⟨j, by simpa using hj⟩
  simp [sparsePattern, hf]

/-- Decode an optional source selector at the current word. -/
def selectorBit {W : ℕ} (src : Option (Fin W)) (x : ℕ) : Bool :=
  src.elim false (fun q => x.testBit q.val)

private theorem patternValue_bit {W L : ℕ} (s : Fin L → Option (Fin W)) (x q : ℕ)
    (hq : q < L) : (patternValue s x).testBit q = selectorBit (s ⟨q, hq⟩) x := by
  simp [patternValue, testBit_placeVal strictMono_id, patternBitNat, hq, patternBit, selectorBit]

/-- Two sparse patterns with the same placement implement the gadget's sparse gate
sum, with all gaps and out-of-range positions accounted for. -/
theorem patternGate_sparse {W m L : ℕ} {pos : ℕ → ℕ} (hpos : StrictMono pos)
    (hbound : ∀ j < m, pos j < L) (src : Fin 2 → Fin m → Option (Fin W))
    (gate : Bool → Bool → Bool) (hzero : gate false false = false) (x : ℕ) :
    patternGateValue gate (fun k => sparsePattern (L := L) pos (src k)) x =
      placeVal m pos (fun j => if hj : j < m then
        gate (selectorBit (src 0 ⟨j, hj⟩) x) (selectorBit (src 1 ⟨j, hj⟩) x) else false) := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [patternGateValue, gateWord_bit, testBit_placeVal hpos]
  by_cases hq : ∃ j : Fin m, pos j.val = q
  · obtain ⟨j, rfl⟩ := hq
    have hjL := hbound j.val j.isLt
    rw [patternValue_bit _ _ _ hjL, patternValue_bit _ _ _ hjL,
      sparsePattern_at hpos _ hbound, sparsePattern_at hpos _ hbound]
    simp [hjL, hpos.injective.eq_iff, j.isLt]
  · have hnone : ¬ ∃ j < m, pos j = q := by
      rintro ⟨j, hj, he⟩
      exact hq ⟨⟨j, hj⟩, he⟩
    have hrhs : decide (∃ j < m, pos j = q ∧
        (if hj : j < m then gate (selectorBit (src 0 ⟨j, hj⟩) x)
          (selectorBit (src 1 ⟨j, hj⟩) x) else false) = true) = false := by
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro j hj he _
      exact hnone ⟨j, hj, he⟩
    rw [hrhs]
    by_cases hqL : q < L
    · rw [patternValue_bit _ _ _ hqL, patternValue_bit _ _ _ hqL,
        sparsePattern_off _ _ ⟨q, hqL⟩ hq, sparsePattern_off _ _ ⟨q, hqL⟩ hq]
      simp [selectorBit, hzero]
    · simp [hqL]

end IntegerMultBounds.MathlibTM2.Routing
