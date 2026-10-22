module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCall

/-!
# Data and explicit cost ledger for a fixed elementary routing loop

Instructions are proof-side descriptions of the raw configuration stream. The
machine program will not depend on their number, coordinates or header values.
The ledger follows the exact banks produced by the executed call, rather than
assuming independent prepared states at successive iterations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

structure ElementaryInstruction (n : ℕ) where
  target : Fin n
  source : Fin n
  source_ne : source ≠ target
  headers : Fin 5 → List Bool

def ElementaryInstruction.rank {n : ℕ} (d : ElementaryInstruction n) (R : ℕ) :=
  elementaryXorRank d.target d.source d.source_ne R

def ElementaryInstruction.Valid {n : ℕ} (d : ElementaryInstruction n) (R B : ℕ) : Prop :=
  (∀ k, Counter.value (d.headers k) = swapValues
    (blockExchangeDimensions n (elementarySwapSpec d.target).a (elementarySwapSpec d.target).b
      (elementarySwapSpec d.target).w R B).1
    (blockExchangeDimensions n (elementarySwapSpec d.target).a (elementarySwapSpec d.target).b
      (elementarySwapSpec d.target).w R B).2.1
    (blockExchangeDimensions n (elementarySwapSpec d.target).a (elementarySwapSpec d.target).b
      (elementarySwapSpec d.target).w R B).2.2
    (elementarySwapSpec d.target).w (elementarySwapSpec d.target).w k) ∧
    ∀ k, GrowingCounterData.Canonical (d.headers k)

noncomputable def ElementaryInstruction.words {n A : ℕ} (d : ElementaryInstruction n) :
    List (List (Fin (A + 4))) :=
  List.ofFn (elementaryConfigWord n ((elementarySwapSpec d.target).coordinate d.source).val d.headers)

noncomputable def ElementaryInstruction.frame {n A : ℕ} (d : ElementaryInstruction n) :
    List (Fin (A + 4)) := configurationWords d.words

theorem ElementaryInstruction.frame_ne_nil {n A : ℕ} (d : ElementaryInstruction n) :
    (d.frame : List (Fin (A + 4))) ≠ [] := by
  have h := configurationWords_count_le (d.words : List (List (Fin (A + 4))))
  have hw : (d.words : List (List (Fin (A + 4)))).length = 6 := by simp [words]
  intro he
  change configurationWords d.words = [] at he
  rw [he, List.length_nil, hw] at h
  omega

noncomputable def elementaryFrames {n A : ℕ} : List (ElementaryInstruction n) → List (Fin (A + 4))
  | [] => []
  | d :: ds => d.frame ++ elementaryFrames ds

noncomputable def elementaryStepBank {t₀ T n A : ℕ}
    (R : Fin T → List (Fin (A + 4))) (rg : LayReg t₀ → Fin T) (config saved : Fin T)
    (d : ElementaryInstruction n) (rows : ℕ) (rest : List (Fin (A + 4)))
    (l : List (List (Fin (A + 4)))) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update R config rest) saved (d.frame.reverse ++ R saved))
    (rg .str) (moveRecs (d.rank rows) l).flatten

noncomputable def elementaryLoopBank {t₀ T n A : ℕ}
    (R : Fin T → List (Fin (A + 4))) (rg : LayReg t₀ → Fin T) (config saved : Fin T) (rows : ℕ) :
    List (ElementaryInstruction n) → List (List (Fin (A + 4))) → Fin T → List (Fin (A + 4))
  | [], _ => R
  | d :: ds, l => elementaryLoopBank
      (elementaryStepBank R rg config saved d rows (elementaryFrames ds) l) rg config saved rows ds
      (moveRecs (d.rank rows) l)

noncomputable def elementaryStepPrice {t₀ T n K : ℕ} (rg : LayReg t₀ → Fin T)
    (hd : Fin 5 → Fin t₀) (config saved : Fin T) (rows B : ℕ)
    (S : Stacks T (prime + K)) (d : ElementaryInstruction n) (rest : List (Fin (prime + K + 4))) : ℝ :=
  let installed := elementaryLoaded S.R rg hd config saved n
    ((elementarySwapSpec d.target).coordinate d.source).val d.headers rest
  configurationBatchCost (d.words (A := prime + K)) + elementaryXorCost rg d.target rows B { S with R := installed } +
    metadataCleanCost installed (elementaryConfigKeys rg hd)

noncomputable def elementaryLoopCost {t₀ T n K : ℕ} (rg : LayReg t₀ → Fin T)
    (hd : Fin 5 → Fin t₀) (config saved : Fin T) (rows B : ℕ)
    (S : Stacks T (prime + K)) : List (ElementaryInstruction n) → List (List (Fin (prime + K + 4))) → ℝ
  | [], _ => 1
  | d :: ds, l => elementaryStepPrice rg hd config saved rows B S d (elementaryFrames ds) + 2 +
      elementaryLoopCost rg hd config saved rows B
        { S with R := elementaryStepBank S.R rg config saved d rows (elementaryFrames ds) l }
        ds (moveRecs (d.rank rows) l)

/-- All reusable registers other than the record stream survive one whole call. -/
theorem elementaryStepBank_keep {t₀ T n A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg) (config saved : Fin T)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (d : ElementaryInstruction n) (rows : ℕ) (rest : List (Fin (A + 4)))
    (l : List (List (Fin (A + 4)))) (r : LayReg t₀) (hr : r ≠ .str) :
    elementaryStepBank R rg config saved d rows rest l (rg r) = R (rg r) := by
  simp only [elementaryStepBank, Function.update_of_ne (fun he => hr (hrg he)),
    Function.update_of_ne (hsaved r).symm, Function.update_of_ne (hconfig r).symm]

end IntegerMultBounds.MathlibTM2.Routing
