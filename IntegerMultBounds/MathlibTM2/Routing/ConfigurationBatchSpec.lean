module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationBatch

/-! # Exact installed metadata and rewind archive of a configuration batch -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {T A : ℕ}

theorem configurationWords_count_le (words : List (List (Fin (A + 4)))) :
    words.length ≤ (configurationWords words).length := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [configurationWords, List.length_cons, List.length_append]
    omega

theorem configurationBatchCost_eq (words : List (List (Fin (A + 4)))) :
    configurationBatchCost words = 4 * (configurationWords words).length + 2 * words.length + 1 := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [configurationBatchCost, configurationWords, List.length_cons, List.length_append]
    omega

/-- Bank installation is linear in the full framed configuration input. -/
theorem configurationBatchCost_le (words : List (List (Fin (A + 4)))) :
    configurationBatchCost words ≤ 6 * (configurationWords words).length + 1 := by
  rw [configurationBatchCost_eq]
  have h := configurationWords_count_le words
  omega

/-- No unrelated register changes while loading a bank. -/
theorem configurationBatchLoaded_keep (R : Fin T → List (Fin (A + 4))) (src tmp saved : Fin T)
    (slots : List (ConfigurationSlot T)) (words : List (List (Fin (A + 4))))
    (rest : List (Fin (A + 4))) (j : Fin T) (hs : j ≠ src) (ht : j ≠ tmp) (ha : j ≠ saved)
    (hd : j ∉ slots.map ConfigurationSlot.dst) :
    configurationBatchLoaded R src tmp saved slots words rest j = R j := by
  induction slots generalizing R words with
  | nil => rfl
  | cons slot slots ih =>
    cases words with
    | nil => rfl
    | cons word words =>
      have hhead : j ≠ slot.dst := by intro he; exact hd (by simp [he])
      have htail : j ∉ slots.map ConfigurationSlot.dst := fun hm => hd (by simp [hm])
      rw [configurationBatchLoaded, ih _ words htail]
      simp [configurationLoaded, Function.update_of_ne hhead,
        Function.update_of_ne hs, Function.update_of_ne ht, Function.update_of_ne ha]

/-- The entire framed prefix, including all separators, is saved in reverse. -/
theorem configurationBatchLoaded_saved (R : Fin T → List (Fin (A + 4))) (src tmp saved : Fin T)
    (slots : List (ConfigurationSlot T)) (words : List (List (Fin (A + 4))))
    (hlen : words.length = slots.length)
    (hslots : ∀ slot ∈ slots, saved ≠ slot.dst) (rest : List (Fin (A + 4))) :
    configurationBatchLoaded R src tmp saved slots words rest saved =
      (configurationWords words).reverse ++ R saved := by
  induction slots generalizing R words with
  | nil =>
    have hw : words = [] := List.length_eq_zero_iff.mp hlen
    subst words
    rfl
  | cons slot slots ih =>
    cases words with
    | nil => simp at hlen
    | cons word words =>
      rw [configurationBatchLoaded, ih _ words (by simpa using hlen)
        (fun j hj => hslots j (by simp [hj]))]
      have hd := hslots slot (by simp)
      simp [configurationLoaded, Function.update_of_ne hd, configurationWords,
        List.reverse_append, List.reverse_cons, List.append_assoc]

/-- The raw input head is exactly after the complete loaded frame. -/
theorem configurationBatchLoaded_src (R : Fin T → List (Fin (A + 4))) (src tmp saved : Fin T)
    (hst : src ≠ tmp) (hss : src ≠ saved)
    (slots : List (ConfigurationSlot T)) (words : List (List (Fin (A + 4))))
    (hlen : words.length = slots.length)
    (hslots : ∀ slot ∈ slots, src ≠ slot.dst) (rest : List (Fin (A + 4)))
    (hsrc : R src = configurationWords words ++ rest) :
    configurationBatchLoaded R src tmp saved slots words rest src = rest := by
  induction slots generalizing R words with
  | nil =>
    have hw : words = [] := List.length_eq_zero_iff.mp hlen
    subst words
    simpa only [configurationBatchLoaded, configurationWords, List.nil_append] using hsrc
  | cons slot slots ih =>
    cases words with
    | nil => simp at hlen
    | cons word words =>
      rw [configurationBatchLoaded]
      apply ih _ words (by simpa using hlen) (fun j hj => hslots j (by simp [hj]))
      have hd := hslots slot (by simp)
      simp [configurationLoaded, Function.update_of_ne hd, Function.update_of_ne hss,
        Function.update_of_ne hst]

/-- Scratch is empty again after every completed batch. -/
theorem configurationBatchLoaded_tmp (R : Fin T → List (Fin (A + 4))) (src tmp saved : Fin T)
    (hts : tmp ≠ saved) (slots : List (ConfigurationSlot T))
    (words : List (List (Fin (A + 4)))) (hlen : words.length = slots.length)
    (hslots : ∀ slot ∈ slots, tmp ≠ slot.dst) (rest : List (Fin (A + 4))) (htmp : R tmp = []) :
    configurationBatchLoaded R src tmp saved slots words rest tmp = [] := by
  induction slots generalizing R words with
  | nil =>
    have hw : words = [] := List.length_eq_zero_iff.mp hlen
    subst words
    exact htmp
  | cons slot slots ih =>
    cases words with
    | nil => simp at hlen
    | cons word words =>
      rw [configurationBatchLoaded]
      apply ih _ words (by simpa using hlen) (fun j hj => hslots j (by simp [hj]))
      have hd := hslots slot (by simp)
      simp [configurationLoaded, Function.update_of_ne hd, Function.update_of_ne hts]

/-- Each distinct destination receives exactly its own word and header marker. -/
theorem configurationBatchLoaded_data (R : Fin T → List (Fin (A + 4))) (src tmp saved : Fin T)
    (slots : List (ConfigurationSlot T)) (hn : (slots.map ConfigurationSlot.dst).Nodup)
    (hslots : ∀ slot ∈ slots, src ≠ slot.dst ∧ tmp ≠ slot.dst ∧ saved ≠ slot.dst)
    (words : List (List (Fin (A + 4)))) (hlen : words.length = slots.length)
    (rest : List (Fin (A + 4))) :
    List.Forall₂ (fun slot word =>
      configurationBatchLoaded R src tmp saved slots words rest slot.dst =
        (if slot.header then [separator] else []) ++ word) slots words := by
  induction slots generalizing R words with
  | nil =>
    have hw : words = [] := List.length_eq_zero_iff.mp hlen
    subst words
    exact .nil
  | cons slot slots ih =>
    cases words with
    | nil => simp at hlen
    | cons word words =>
      have hn' := List.nodup_cons.mp hn
      obtain ⟨hs, ht, ha⟩ := hslots slot (by simp)
      refine List.Forall₂.cons ?_ ?_
      · rw [configurationBatchLoaded, configurationBatchLoaded_keep _ src tmp saved slots words rest
          slot.dst hs.symm ht.symm ha.symm hn'.1]
        simp [configurationLoaded]
      · exact ih _ hn'.2 (fun j hj => hslots j (by simp [hj])) words (by simpa using hlen)

end IntegerMultBounds.MathlibTM2.Routing
