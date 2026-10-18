module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallCheckDefs
public import IntegerMultBounds.Networks.Certificates.T16.Impl.HelperRank
public import IntegerMultBounds.Networks.Certificates.T16.Impl.HelperBits

/-! The checks of a local invocation and their soundness: a successful `callCheck s r`, together
with the global hosting check, gives every fact of `CallFacts s r`. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open Streams Geometry

/-! ### Hosting completeness -/

/-- The helper bitmask of a slot, from the role list. -/
def helperBits (s r : ℕ) : ℕ := (rolesList s r).foldl (fun m f => m ||| 2 ^ f) 0

theorem testBit_foldl (l : List ℕ) (m f : ℕ) :
    (l.foldl (fun m f => m ||| 2 ^ f) m).testBit f = (m.testBit f || decide (f ∈ l)) := by
  induction l generalizing m with
  | nil => simp
  | cons g l ih =>
    rw [List.foldl_cons, ih, testBit_or_pow]
    by_cases h : f = g <;> simp [h, Bool.or_assoc]

theorem mem_of_helperBits {s r f : ℕ} (h : (helperBits s r).testBit f = true) : f ∈ rolesList s r := by
  rw [helperBits, testBit_foldl] at h
  simpa using h

/-- Every hosted slice of every slot lies on a helper of that slot. -/
def hostedCovered : Bool :=
  (List.range 16).all fun r' => (List.range 112).all fun a' =>
    (groupData r' a').hosted.all fun e =>
      decide (e.1 < 144) && (helperBitsLit e.1).testBit (famIdx r' a' (toStream e.2.1))

/-- The literal bitmasks are the bitmasks of the role lists. -/
def bitsAgree : Bool := (List.range 144).all fun slot => helperBitsLit slot == helperBits (slot / 16) (slot % 16)

theorem hostAcc_ne_zero {G : GroupData} {slot : ℕ} {i : Fin 8} (h : hostAcc G slot i ≠ Vec.zero) :
    ∃ e ∈ G.hosted, e.1 = slot ∧ toStream e.2.1 = i := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  apply h
  rw [hostAcc, List.filter_eq_nil_iff.mpr]
  · rfl
  · intro e he hp
    simp only [decide_eq_true_eq] at hp
    exact hne e he hp.1 hp.2

theorem complete_of_covered (hc : hostedCovered = true) (ha : bitsAgree = true) {s r : ℕ}
    (hs : s < 9) (hr : r < 16) (hl : (rolesList s r).length = 480) :
    ∀ r' < 16, ∀ a' < 112, ∀ i : Fin 8, hostAcc (groupData r' a') (slotOf s r) i ≠ Vec.zero →
      ∃ h < 480, helperFamily s r h = famIdx r' a' i := by
  intro r' hr' a' ha' i hacc
  obtain ⟨e, he, hslot, hstr⟩ := hostAcc_ne_zero hacc
  have h1 := List.all_eq_true.mp hc r' (List.mem_range.mpr hr')
  have h2 := List.all_eq_true.mp h1 a' (List.mem_range.mpr ha')
  have h3 := List.all_eq_true.mp h2 e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
  have hagree := List.all_eq_true.mp ha (slotOf s r) (List.mem_range.mpr (by simp [slotOf]; omega))
  simp only [beq_iff_eq] at hagree
  rw [hslot, hagree, hstr, show slotOf s r / 16 = s by simp [slotOf]; omega,
    show slotOf s r % 16 = r by simp [slotOf]; omega] at h3
  have hmem := mem_of_helperBits h3.2
  obtain ⟨h, hh, he'⟩ := List.getElem_of_mem hmem
  refine ⟨h, hl ▸ hh, ?_⟩
  rw [helperFamily_eq hh, he']

/-! ### The checks of one invocation -/

theorem helperCheck_of {s r : ℕ} (hc : callCheck s r = true) {h : ℕ} (hh : h < 480) :
    helperCheck s r h (helperFamily s r h) = true := by
  simp only [callCheck, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hl, -⟩, hhelp⟩, -⟩ := hc
  have hh' : h < (rolesList s r).length := by rw [hl]; exact hh
  have hz : h < ((List.range 480).zip (rolesList s r)).length := by
    rw [List.length_zip, List.length_range, hl, min_self]; exact hh
  have hmem : (h, helperFamily s r h) ∈ (List.range 480).zip (rolesList s r) := by
    rw [helperFamily_eq hh']
    have := List.getElem_mem hz
    rw [List.getElem_zip, List.getElem_range] at this
    exact this
  exact List.all_eq_true.mp hhelp _ hmem

/-- **Soundness of the checks.** -/
theorem callFacts_of_check (hc : hostedCovered = true) (ha : bitsAgree = true) {s r : ℕ}
    (hs : s < 9) (hr : r < 16) (h : callCheck s r = true) : CallFacts s r := by
  have hl : (rolesList s r).length = 480 := by
    simp only [callCheck, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1.1
  have hd : insertAll 0 (callFamilies s r) ≠ none := by
    simp only [callCheck, Bool.and_eq_true, Option.isSome_iff_ne_none] at h
    exact h.1.1.2
  have hext : ∀ a < 112, extCheck s a = true := by
    simp only [callCheck, Bool.and_eq_true] at h
    exact fun a ha => List.all_eq_true.mp h.2 a (List.mem_range.mpr ha)
  have hh := fun {h' : ℕ} (hh : h' < 480) => helperCheck_of h hh
  have hlt : ∀ h < 480, helperFamily s r h < 14336 := fun h' hh' => by
    have := hh hh'
    simp only [helperCheck, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1
  refine ⟨callReg_inj hr hl hlt hd, hlt, fun h' hh' => ?_, fun h' hh' => ?_, fun h' hh' => ?_,
    complete_of_covered hc ha hs hr hl, fun a ha' => ?_⟩
  · have := hh hh'
    simp only [helperCheck, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.1.1.2
  · have := hh hh'
    simp only [helperCheck, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.2
  · have := hh hh'
    simp only [helperCheck, Bool.and_eq_true, beq_iff_eq] at this
    rw [helper_rank this.1.2, this.2]
  · have he := hext a ha'
    simp only [extCheck, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
      decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at he
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rcases he k with h1 | ⟨⟨h1, -⟩, -⟩
      · exact absurd h1 hk
      · exact h1
    · rcases he k with h1 | ⟨⟨-, h2⟩, -⟩
      · exact absurd h1 hk
      · exact h2
    · rcases he k with h1 | ⟨-, h3⟩
      · exact absurd h1 hk
      · exact h3
    · rcases he k with h1 | ⟨⟨h1, h2⟩, h3⟩
      · exact absurd h1 hk
      · rw [h2, ← h3, h1]

end IntegerMultBounds.Networks.Certificates.T16.Impl
