module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallCorrect

/-! Checkable forms of the facts of a local invocation. Distinct register families are checked
by inserting them into a bitmask; every hosted slice of a slot is checked to lie on a helper by
membership in the slot's helper bitmask; the remaining facts are direct computations. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open Streams

/-! ### Distinctness by a bitmask -/

/-- Insert naturals into a bitmask, failing on a repeat. -/
def insertAll : ℕ → List ℕ → Option ℕ
  | m, [] => some m
  | m, f :: fs => if m.testBit f then none else insertAll (m ||| 2 ^ f) fs

theorem testBit_or_pow (m f g : ℕ) : (m ||| 2 ^ f).testBit g = (m.testBit g || decide (g = f)) := by
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases h : g = f
  · subst h; simp
  · simp [h, Ne.symm h]

theorem insertAll_spec : ∀ (fs : List ℕ) (m : ℕ), insertAll m fs ≠ none →
    fs.Nodup ∧ ∀ f ∈ fs, m.testBit f = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | f :: fs, m, h => by
    simp only [insertAll] at h
    split_ifs at h with hf
    · exact absurd rfl h
    · obtain ⟨hnd, hmem⟩ := insertAll_spec fs _ h
      refine ⟨List.nodup_cons.mpr ⟨fun hin => ?_, hnd⟩, fun g hg => ?_⟩
      · have := hmem f hin
        rw [testBit_or_pow] at this
        simp at this
      · rcases List.mem_cons.mp hg with rfl | hg
        · simpa using hf
        · have := hmem g hg
          rw [testBit_or_pow] at this
          simp only [Bool.or_eq_false_iff] at this
          exact this.1

theorem nodup_of_insertAll {fs : List ℕ} (h : insertAll 0 fs ≠ none) : fs.Nodup :=
  (insertAll_spec fs 0 h).1

/-! ### Register families -/

/-- The families of the 704 non-private registers of an invocation. -/
def callFamilies (s r : ℕ) : List ℕ :=
  (List.range 112).map (fun a => famIdx r a (toStream (2 * localPair s))) ++
    (List.range 112).map (fun a => famIdx r a (toStream (2 * localPair s + 1))) ++
      (List.range 480).map (helperFamily s r)

theorem callFamilies_length (s r : ℕ) : (callFamilies s r).length = 704 := by
  simp [callFamilies]

theorem callReg_family {s r : ℕ} (hr : r < 16) (hlt : ∀ h < 480, helperFamily s r h < 14336)
    (w : ℕ) (hw : w < 704) :
    ∃ hf : (callFamilies s r)[w]'(by rw [callFamilies_length]; exact hw) < 14336,
      callReg s r w = .inl ⟨(callFamilies s r)[w]'(by rw [callFamilies_length]; exact hw), hf⟩ := by
  by_cases h1 : w < 112
  · have e : (callFamilies s r)[w]'(by rw [callFamilies_length]; exact hw) =
        famIdx r w (toStream (2 * localPair s)) := by
      simp [callFamilies, List.getElem_append_left, h1]
    refine ⟨e ▸ famIdx_lt hr h1 _, ?_⟩
    rw [callReg_X h1, streamUnit_val hr h1]
    simp [e]
  · by_cases h2 : w < 224
    · have e : (callFamilies s r)[w]'(by rw [callFamilies_length]; exact hw) =
          famIdx r (w - 112) (toStream (2 * localPair s + 1)) := by
        simp only [callFamilies]
        rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp
      refine ⟨e ▸ famIdx_lt hr (by omega) _, ?_⟩
      have := callReg_Y (s := s) (r := r) (a := w - 112) (by omega)
      rw [show w - 112 + 112 = w by omega] at this
      rw [this, streamUnit_val hr (by omega)]
      simp [e]
    · have e : (callFamilies s r)[w]'(by rw [callFamilies_length]; exact hw) =
          helperFamily s r (w - 224) := by
        simp only [callFamilies]
        rw [List.getElem_append_right (by simp; omega)]
        simp
      refine ⟨e ▸ hlt _ (by omega), ?_⟩
      have := callReg_helper (s := s) (r := r) (h := w - 224) (by omega)
      rw [show 224 + (w - 224) = w by omega] at this
      rw [this, famUnit_inl (hlt _ (by omega))]
      simp [e]

/-- **Distinct registers.** -/
theorem callReg_inj {s r : ℕ} (hr : r < 16) (hlt : ∀ h < 480, helperFamily s r h < 14336)
    (hd : insertAll 0 (callFamilies s r) ≠ none) :
    ∀ w < 712, ∀ w' < 712, callReg s r w = callReg s r w' → w = w' := by
  have hnd := nodup_of_insertAll hd
  intro w hw w' hw' e
  by_cases h1 : w < 704 <;> by_cases h2 : w' < 704
  · obtain ⟨hf, ef⟩ := callReg_family hr hlt w h1
    obtain ⟨hf', ef'⟩ := callReg_family hr hlt w' h2
    rw [ef, ef'] at e
    have := congrArg Fin.val (Sum.inl_injective e)
    exact (List.Nodup.getElem_inj_iff hnd).mp this
  · obtain ⟨hf, ef⟩ := callReg_family hr hlt w h1
    rw [ef] at e
    simp [callReg, show ¬ w' < 112 by omega, show ¬ w' < 224 by omega, h2] at e
  · obtain ⟨hf', ef'⟩ := callReg_family hr hlt w' h2
    rw [ef'] at e
    simp [callReg, show ¬ w < 112 by omega, show ¬ w < 224 by omega, h1] at e
  · simp only [callReg, show ¬ w < 112 by omega, show ¬ w < 224 by omega, h1,
      show ¬ w' < 112 by omega, show ¬ w' < 224 by omega, h2, ite_false, Sum.inr.injEq,
      Fin.mk.injEq] at e
    omega

end IntegerMultBounds.Networks.Certificates.T16.Impl
