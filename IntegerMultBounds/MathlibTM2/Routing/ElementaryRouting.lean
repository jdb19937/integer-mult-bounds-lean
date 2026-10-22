module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryLoop
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryLoopFrame

/-!
# Uniform elementary routing with raw configuration restored

One fixed loop reads all per-call metadata, executes and clears each elementary
XOR, then rewinds the configuration archive. The whole register bank is restored
except for the requested record permutation. Shared-counter setup and uniform
raw-word generation remain explicit later obligations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {t₀ T Q K : ℕ} {U P : Type}

noncomputable def elementaryRoutingProgram (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T) (config saved : Fin T) :
    Pr P T Q (prime + K) U :=
  .seq (elementaryLoopProgram rg hrg hd pay hhd hQ hT config saved) (moveR saved config id)

/-- Actual routing of the complete instruction stream, with every configuration
symbol and machine call charged and only the output stream changed. -/
theorem elementaryRouting_exec {n rows B : ℕ}
    (body : P → Pr P T Q (prime + K) U) (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ j, hd j ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (config saved : Fin T) (hcs : config ≠ saved)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (hrows : 0 < rows) (hB : 1 ≤ B) (ds : List (ElementaryInstruction n))
    (hvalid : ∀ d ∈ ds, d.Valid rows B)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = []) (hready : ElementaryLoopReady rg hd pay S.R n rows B)
    (harchive : S.R saved = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rows * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8)
    (hstream : S.R (rg .str) = l.flatten) (hinput : S.R config = elementaryFrames ds) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ 1 + elementaryLoopCost rg hd config saved rows B S ds l +
        (2 * (elementaryFrames (A := prime + K) ds).length + 2 : ℕ) ∧
      Exec body (elementaryRoutingProgram rg hrg hd pay hhd hQ hT config saved) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .str) (moveRecs (elementaryInstructionsRank rows ds) l).flatten }) := by
  let v₀ := { v with flag := (elementaryFrames (A := prime + K) ds).head?.isSome }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := elementaryLoop_loop_exec body rg hrg hd pay hhd hpay hQ hT
    config saved hcs hconfig hsaved hrows hB ds hvalid v₀ S hL hready l hl hlB h8 hstream hinput rfl
  have hp : (peekR config : Act T Q (prime + K) U).run (mk v S) = mk v₀ S := by
    simp only [peekR_run, hinput]
    rfl
  have heloop := Exec.seq (hp ▸ Exec.act (body := body) (peekR config) (mk v S)) he₁
  let finalBank := elementaryLoopBank S.R rg config saved rows ds l
  let S₁ : Stacks T (prime + K) := { S with R := finalBank }
  have hbank : finalBank = Function.update (Function.update (Function.update S.R config [])
      saved ((elementaryFrames ds).reverse ++ S.R saved)) (rg .str) (elementaryLoopRecords rows ds l).flatten :=
    elementaryLoopBank_eq S.R rg config saved hcs (hconfig .str) (hsaved .str) rows ds l hinput hstream
  have hsrc₁ : S₁.R config = [] := by
    simp [S₁, hbank, Function.update_of_ne (hconfig .str), Function.update_of_ne hcs]
  have hsaved₁ : S₁.R saved = (elementaryFrames ds).reverse := by
    simp [S₁, hbank, Function.update_of_ne (hsaved .str), harchive]
  obtain ⟨v₂, hu₂, he₂⟩ := configurationRestore_exec body config saved hcs.symm
    (elementaryFrames ds) [] v₁ S₁ hsaved₁ hsrc₁
  have hrestore : Function.update (Function.update finalBank saved []) config (elementaryFrames ds ++ []) =
      Function.update S.R (rg .str) (moveRecs (elementaryInstructionsRank rows ds) l).flatten := by
    rw [hbank, elementaryLoopRecords_eq rows ds l hl]
    funext j
    by_cases hj : j = config
    · subst j
      simp only [Function.update_self, List.append_nil, Function.update_of_ne (hconfig .str), hinput]
    · by_cases ha : j = saved
      · subst j
        simp only [Function.update_of_ne hcs.symm, Function.update_self,
          Function.update_of_ne (hsaved .str), harchive]
      · by_cases ht : j = rg .str
        · subst j
          simp only [Function.update_of_ne (hconfig .str).symm,
            Function.update_of_ne (hsaved .str).symm, Function.update_self]
        · simp only [Function.update_of_ne hj, Function.update_of_ne ha, Function.update_of_ne ht]
  have he₂' : Exec body (moveR saved config id) (mk v₁ S₁)
      (2 * (elementaryFrames (A := prime + K) ds).length + 2)
      (mk v₂ { S with R := Function.update S.R (rg .str) (moveRecs (elementaryInstructionsRank rows ds) l).flatten }) := by
    simpa only [S₁, hrestore] using he₂
  refine ⟨v₂, (1 + m₁) + (2 * (elementaryFrames (A := prime + K) ds).length + 2),
    hu₂.trans hu₁, ?_, Exec.seq heloop he₂'⟩
  rw [Nat.cast_add, Nat.cast_add]
  norm_num only [Nat.cast_one]
  linarith only [hm₁]

end IntegerMultBounds.MathlibTM2.Routing
