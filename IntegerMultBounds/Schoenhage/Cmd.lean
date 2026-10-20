module

public import IntegerMultBounds.Schoenhage.Words
public import IntegerMultBounds.MathlibTM2.Host.WordTape

/-! Word programs: a small language over banks of word tapes. A primitive has an abstract effect
on the word zippers of a few tapes and a verified host implementation (`Host/WordTape`);
programs place primitives on chosen tapes, sequence them, loop while a tape has a word under its
head, and branch on whether the current word starts with a one bit. `Exec` is their big-step
semantics with costs; `Host/WordCmd` runs them on host stacks. The alphabet parameter `a` is a
leftover of the multitape backend (restore from 3ce5bd58) and is unused. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine

variable {a t : ℕ}

/-- A verified primitive on `s` word tapes: an abstract effect on their word zippers and its
host implementation. -/
structure Prim (a : ℕ) where
  s : ℕ
  pre : (Fin s → WTape) → Prop
  sem : (Fin s → WTape) → (Fin s → WTape)
  cost : (Fin s → WTape) → ℕ
  /-- The control states its host implementation needs. -/
  nQ : ℕ
  /-- The host implementation on host stacks. -/
  prog : MathlibTM2.Host.WordCmd.HProg s
  hspec : MathlibTM2.Host.WordCmd.HostSpec 3 nQ s pre sem cost prog
  hcalls : MathlibTM2.Host.WordCmd.HNoCalls prog

/-- Word programs over `t` tapes. -/
inductive Cmd (a t : ℕ) : Type 1 where
  | prim (P : Prim a) (slot : Fin P.s → Fin t) (hinj : Function.Injective slot)
  | seq (c d : Cmd a t)
  | loop (i : Fin t) (body : Cmd a t)
  | cond (i : Fin t) (c d : Cmd a t)

/-- Replace the slotted tapes. -/
noncomputable def upd {s : ℕ} (σ : Fin t → WTape) (slot : Fin s → Fin t) (τ : Fin s → WTape) :
    Fin t → WTape :=
  fun x => if h : ∃ i, slot i = x then τ h.choose else σ x

theorem upd_slot {s : ℕ} (σ : Fin t → WTape) {slot : Fin s → Fin t} (hinj : Function.Injective slot)
    (τ : Fin s → WTape) (i : Fin s) : upd σ slot τ (slot i) = τ i := by
  have h : ∃ j, slot j = slot i := ⟨i, rfl⟩
  simp only [upd, h, ↓reduceDIte]
  rw [hinj h.choose_spec]

theorem upd_other {s : ℕ} (σ : Fin t → WTape) (slot : Fin s → Fin t) (τ : Fin s → WTape) (x : Fin t)
    (hx : ∀ i, slot i ≠ x) : upd σ slot τ x = σ x := by
  have h : ¬ ∃ i, slot i = x := fun ⟨i, hi⟩ => hx i hi
  simp [upd, h]

/-- The branch condition on word tapes. -/
def StartsOne (T : WTape) : Prop := ∃ w R, T.right = (true :: w) :: R

/-- Big-step executions with their costs. -/
inductive Exec : Cmd a t → (Fin t → WTape) → (Fin t → WTape) → ℕ → Prop where
  | prim {P : Prim a} {slot : Fin P.s → Fin t} {hinj : Function.Injective slot} {σ : Fin t → WTape}
      (h : P.pre (σ ∘ slot)) :
      Exec (.prim P slot hinj) σ (upd σ slot (P.sem (σ ∘ slot))) (P.cost (σ ∘ slot))
  | seq {c d : Cmd a t} {σ σ₁ σ₂ : Fin t → WTape} {k₁ k₂ : ℕ}
      (h₁ : Exec c σ σ₁ k₁) (h₂ : Exec d σ₁ σ₂ k₂) : Exec (.seq c d) σ σ₂ (k₁ + 1 + k₂)
  | loop_done {i : Fin t} {b : Cmd a t} {σ : Fin t → WTape} (h : (σ i).right = []) :
      Exec (.loop i b) σ σ 0
  | loop_step {i : Fin t} {b : Cmd a t} {σ σ₁ σ₂ : Fin t → WTape} {k₁ k₂ : ℕ}
      (h : (σ i).right ≠ []) (h₁ : Exec b σ σ₁ k₁) (h₂ : Exec (.loop i b) σ₁ σ₂ k₂) :
      Exec (.loop i b) σ σ₂ (k₁ + 2 + k₂)
  | cond_true {i : Fin t} {c d : Cmd a t} {σ σ' : Fin t → WTape} {k : ℕ}
      (h : StartsOne (σ i)) (h₁ : Exec c σ σ' k) : Exec (.cond i c d) σ σ' (k + 1)
  | cond_false {i : Fin t} {c d : Cmd a t} {σ σ' : Fin t → WTape} {k : ℕ}
      (h : ¬ StartsOne (σ i)) (h₁ : Exec d σ σ' k) : Exec (.cond i c d) σ σ' (k + 1)

end IntegerMultBounds.Schoenhage
