module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationLoad

/-!
# Load a fixed metadata bank from a framed configuration stream

The destination list fixes the program; word lengths and values are read from
the input tape. The same source, scratch and rewind archive are reused for every
word, with every left stack unchanged and every scanned symbol charged.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

structure ConfigurationSlot (T : ℕ) where
  dst : Fin T
  header : Bool

def configurationWords : List (List (Fin (A + 4))) → List (Fin (A + 4))
  | [] => []
  | word :: words => word ++ separator :: configurationWords words

def configurationBatch (src tmp saved : Fin T) (p : Fin (A + 4) → Bool) :
    List (ConfigurationSlot T) → Pr P T Q A U
  | [] => .act .done
  | slot :: slots => .seq (configurationLoad src slot.dst tmp saved p slot.header)
      (configurationBatch src tmp saved p slots)

def configurationBatchLoaded (R : Fin T → List (Fin (A + 4))) (src tmp saved : Fin T) :
    List (ConfigurationSlot T) → List (List (Fin (A + 4))) → List (Fin (A + 4)) →
      Fin T → List (Fin (A + 4))
  | slot :: slots, word :: words, rest =>
    configurationBatchLoaded
      (configurationLoaded R src slot.dst tmp saved word (configurationWords words ++ rest) slot.header)
      src tmp saved slots words rest
  | _, _, _ => R

def configurationBatchCost : List (List (Fin (A + 4))) → ℕ
  | [] => 1
  | word :: words => 4 * word.length + 6 + configurationBatchCost words

/-- Execute the complete fixed bank load with a concrete source, scratch and
archive. Distinct destinations prevent later loads overwriting earlier metadata. -/
theorem configurationBatch_exec (body : P → Pr P T Q A U) (src tmp saved : Fin T)
    (hst : src ≠ tmp) (hss : src ≠ saved) (hts : tmp ≠ saved)
    (p : Fin (A + 4) → Bool) (hsep : p separator = false)
    (slots : List (ConfigurationSlot T)) (hn : (slots.map ConfigurationSlot.dst).Nodup)
    (hslots : ∀ slot ∈ slots, src ≠ slot.dst ∧ tmp ≠ slot.dst ∧ saved ≠ slot.dst)
    (words : List (List (Fin (A + 4)))) (hlen : words.length = slots.length)
    (hwords : ∀ word ∈ words, ∀ x ∈ word, p x = true) (rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = configurationWords words ++ rest) (htmp : S.R tmp = [])
    (hempty : ∀ slot ∈ slots, S.R slot.dst = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (configurationBatch src tmp saved p slots) (mk v S) (configurationBatchCost words)
        (mk v' { S with R := configurationBatchLoaded S.R src tmp saved slots words rest }) := by
  induction slots generalizing words v S with
  | nil =>
    have hw : words = [] := List.length_eq_zero_iff.mp hlen
    subst words
    exact ⟨v, rfl, Exec.act (body := body) .done (mk v S)⟩
  | cons slot slots ih =>
    cases words with
    | nil => simp at hlen
    | cons word words =>
      have hn' := List.nodup_cons.mp hn
      have htail (j : ConfigurationSlot T) (hj : j ∈ slots) : j ∈ slot :: slots := by simp [hj]
      obtain ⟨hsd, htd, had⟩ := hslots slot (by simp)
      obtain ⟨v₁, hu₁, he₁⟩ := configurationLoad_exec body src slot.dst tmp saved hst hss hts
        hsd htd had p hsep slot.header word (configurationWords words ++ rest)
        (hwords word (by simp)) v S (by simpa only [configurationWords, List.append_assoc, List.cons_append] using hsrc)
        htmp (hempty slot (by simp))
      let R₁ := configurationLoaded S.R src slot.dst tmp saved word (configurationWords words ++ rest) slot.header
      let S₁ : Stacks T A := { S with R := R₁ }
      have hsrc₁ : S₁.R src = configurationWords words ++ rest := by
        simp [S₁, R₁, configurationLoaded, Function.update_of_ne hsd,
          Function.update_of_ne hss, Function.update_of_ne hst]
      have htmp₁ : S₁.R tmp = [] := by
        simp [S₁, R₁, configurationLoaded, Function.update_of_ne htd, Function.update_of_ne hts]
      have hempty₁ : ∀ j ∈ slots, S₁.R j.dst = [] := by
        intro j hj
        obtain ⟨hjs, hjt, hja⟩ := hslots j (htail j hj)
        have hne : j.dst ≠ slot.dst := by
          intro he
          exact hn'.1 (List.mem_map.mpr ⟨j, hj, he⟩)
        simpa only [S₁, R₁, configurationLoaded, Function.update_of_ne hne,
          Function.update_of_ne hja.symm, Function.update_of_ne hjt.symm,
          Function.update_of_ne hjs.symm] using hempty j (htail j hj)
      obtain ⟨v₂, hu₂, he₂⟩ := ih hn'.2 (fun j hj => hslots j (htail j hj)) words
        (by simpa using hlen) (fun w hw => hwords w (by simp [hw])) v₁ S₁ hsrc₁ htmp₁ hempty₁
      exact ⟨v₂, hu₂.trans hu₁, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
