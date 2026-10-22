module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationBatchSpec
public import IntegerMultBounds.MathlibTM2.Routing.LowBitXorExec
public import Mathlib.Data.List.Forall2

/-!
# Six raw configuration words for one elementary routing call

Five canonical interchange headers and the renamed source mask are loaded from
one framed stream, reusing one scratch register and one archive. Shared counters
and the target-bit mask are separate persistent setup. Word generation is not
claimed by this input format.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast

variable {t₀ T A : ℕ}

def configurationIsBit (x : Fin (A + 4)) : Bool :=
  decide (x = bitSymbol false ∨ x = bitSymbol true)

@[simp] theorem configurationIsBit_bit (b : Bool) :
    configurationIsBit (bitSymbol (a := A) b) = true := by cases b <;> rfl

@[simp] theorem configurationIsBit_separator :
    configurationIsBit (separator : Fin (A + 4)) = false := by rfl

noncomputable def elementaryConfigTarget (rg : LayReg t₀ → Fin T) (hd : Fin 5 → Fin t₀) (key : Fin 6) : Fin T :=
  if h : key.val < 5 then rg (.sw (reg (hd ⟨key.val, h⟩))) else rg .mB

noncomputable def elementaryConfigSlot (rg : LayReg t₀ → Fin T) (hd : Fin 5 → Fin t₀)
    (key : Fin 6) : ConfigurationSlot T :=
  ⟨elementaryConfigTarget rg hd key, decide (key.val < 5)⟩

def elementaryConfigWord (n source : ℕ) (headers : Fin 5 → List Bool) (key : Fin 6) :
    List (Fin (A + 4)) :=
  if h : key.val < 5 then (headers ⟨key.val, h⟩).map bitSymbol else binSyms n (2 ^ source)

theorem elementaryConfigWord_bits (n source : ℕ) (headers : Fin 5 → List Bool) (key : Fin 6) :
    ∀ x ∈ (elementaryConfigWord n source headers key : List (Fin (A + 4))),
      configurationIsBit x = true := by
  unfold elementaryConfigWord
  split_ifs
  · intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    exact configurationIsBit_bit b
  · rw [binSyms_eq]
    intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    exact configurationIsBit_bit b

theorem elementaryConfigTarget_injective (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (hd : Fin 5 → Fin t₀) (hhd : Function.Injective hd) :
    Function.Injective (elementaryConfigTarget rg hd) := by
  intro i j he
  unfold elementaryConfigTarget at he
  split_ifs at he with hi hj hj
  · have h := hhd (swapReg_injective (LayReg.sw.inj (hrg he)))
    exact Fin.ext (congrArg (fun k : Fin 5 => k.val) h)
  · have h := hrg he
    cases h
  · have h := hrg he
    cases h
  · apply Fin.ext
    have h₁ := i.isLt
    have h₂ := j.isLt
    omega

theorem elementaryConfigSlots_nodup (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (hd : Fin 5 → Fin t₀) (hhd : Function.Injective hd) :
    ((List.ofFn (elementaryConfigSlot rg hd)).map ConfigurationSlot.dst).Nodup := by
  simp only [List.map_ofFn]
  exact List.nodup_ofFn.mpr (elementaryConfigTarget_injective rg hrg hd hhd)

theorem elementaryConfigTarget_role (rg : LayReg t₀ → Fin T) (hd : Fin 5 → Fin t₀)
    (key : Fin 6) :
    (∃ j, elementaryConfigTarget rg hd key = rg (.sw j)) ∨
      elementaryConfigTarget rg hd key = rg .mB := by
  unfold elementaryConfigTarget
  split_ifs
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr rfl

/-- The shared scan scratch never aliases a metadata destination. -/
theorem elementaryConfigTarget_tmp (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (hd : Fin 5 → Fin t₀) (key : Fin 6) :
    rg .tmp ≠ elementaryConfigTarget rg hd key := by
  rcases elementaryConfigTarget_role rg hd key with ⟨j, hj⟩ | hj <;>
    rw [hj] <;> simp [hrg.eq_iff]

noncomputable def elementaryLoaded (R : Fin T → List (Fin (A + 4))) (rg : LayReg t₀ → Fin T)
    (hd : Fin 5 → Fin t₀) (src saved : Fin T) (n source : ℕ)
    (headers : Fin 5 → List Bool) (rest : List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  configurationBatchLoaded R src (rg .tmp) saved (List.ofFn (elementaryConfigSlot rg hd))
    (List.ofFn (elementaryConfigWord n source headers)) rest

theorem elementaryConfigSlots_separate (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (hd : Fin 5 → Fin t₀) (src saved : Fin T)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r) :
∀ slot ∈ List.ofFn (elementaryConfigSlot rg hd),
      src ≠ slot.dst ∧ rg .tmp ≠ slot.dst ∧ saved ≠ slot.dst := by
    intro slot hs
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
    rcases elementaryConfigTarget_role rg hd j with ⟨i, hi⟩ | hi
    · exact ⟨by simpa only [elementaryConfigSlot, hi] using hsrc (.sw i),
        elementaryConfigTarget_tmp rg hrg hd j,
        by simpa only [elementaryConfigSlot, hi] using hsaved (.sw i)⟩
    · exact ⟨by simpa only [elementaryConfigSlot, hi] using hsrc .mB,
        elementaryConfigTarget_tmp rg hrg hd j,
        by simpa only [elementaryConfigSlot, hi] using hsaved .mB⟩

/-- The batch-loader postcondition gives each exact prepared metadata word. -/
theorem elementaryLoaded_at (R : Fin T → List (Fin (A + 4))) (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg) (hd : Fin 5 → Fin t₀) (hhd : Function.Injective hd)
    (src saved : Fin T) (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (n source : ℕ) (headers : Fin 5 → List Bool) (rest : List (Fin (A + 4))) (key : Fin 6) :
    elementaryLoaded R rg hd src saved n source headers rest (elementaryConfigTarget rg hd key) =
      (if key.val < 5 then [separator] else []) ++ elementaryConfigWord n source headers key := by
  have hslots := elementaryConfigSlots_separate rg hrg hd src saved hsrc hsaved
  have h := configurationBatchLoaded_data R src (rg .tmp) saved
    (List.ofFn (elementaryConfigSlot rg hd)) (elementaryConfigSlots_nodup rg hrg hd hhd) hslots
    (List.ofFn (elementaryConfigWord n source headers)) (by simp) rest
  have hk := h.get (i := key.val) (by simp) (by simp)
  simp only [List.get_eq_getElem, List.getElem_ofFn] at hk
  simpa only [elementaryLoaded, elementaryConfigSlot, decide_eq_true_eq] using hk

end IntegerMultBounds.MathlibTM2.Routing
