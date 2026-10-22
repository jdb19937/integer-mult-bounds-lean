module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompileLoop

/-!
# Uniform compilation with complete coordinate-table restoration

A fixed loop compiles every coordinate pair, emits valid instruction frames and
rewinds its input archive. Only the output stream differs from the initial bank.
The coordinate table itself remains input data; generating it is separate work.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def elementaryCompileTableProgram (rg : ElementaryCompilerReg → Fin T) (src saved : Fin T) : Pr P T Q A U :=
  .seq (elementaryCompileLoopProgram rg src saved) (moveR saved src id)

/-- Compile any finite coordinate table, restore its raw input and every private
register, and charge initial setup, all iterations, guards and final rewind. -/
theorem elementaryCompileTable_exec {n : ℕ} (body : P → Pr P T Q A U)
    (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg)
    (src saved : Fin T) (hss : src ≠ saved) (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (L Lb rows B : ℕ) (hn : n < 2 ^ L) (hB : B < 2 ^ Lb)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = rows) (cs : List (ElementaryCoordinate n))
    (v : HS T Q A U) (S : Stacks T A) (hready : ElementaryCompileReady rg S.R n L Lb B rowBits)
    (hinput : S.R src = elementaryCoordinateFrames L cs) (harchive : S.R saved = []) :
    ∃ (ds : List (ElementaryInstruction n)) (v' : HS T Q A U) (m : ℕ),
      (∀ d ∈ ds, d.Valid rows B) ∧
      (∀ d ∈ ds, (d.frame : List (Fin (A + 4))).length ≤ rowBits.length + 3 * n + Lb + 11) ∧ ds.map (fun d => (d.target, d.source)) = cs.reverse.map ElementaryCoordinate.key ∧
      v'.user = v.user ∧
      m ≤ cs.length * (elementaryCompileBase n L Lb rowBits.length + 2) +
        7 * (elementaryFrames (A := A) ds).length + 2 * (elementaryCoordinateFrames (A := A) L cs).length + 4 ∧
      Exec body (elementaryCompileTableProgram rg src saved) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .output) (elementaryFrames ds ++ S.R (rg .output)) }) := by
  let v₀ := { v with flag := (elementaryCoordinateFrames (A := A) L cs).head?.isSome }
  obtain ⟨ds, v₁, m₁, hv, hsize, hk, hu₁, hm₁, he₁⟩ := elementaryCompileLoop_loop_exec body rg hrg src saved
    hss hsrc hsaved L Lb rows B hn hB rowBits hrow hrowNe hrowValue cs v₀ S hready hinput rfl
  have hp : (peekR src : Act T Q A U).run (mk v S) = mk v₀ S := by
    simp only [peekR_run, hinput]
    rfl
  have heloop := Exec.seq (hp ▸ Exec.act (body := body) (peekR src) (mk v S)) he₁
  let finalBank := elementaryCompileLoopBank S.R rg src saved (elementaryCoordinateFrames L cs) (elementaryFrames ds)
  let S₁ : Stacks T A := { S with R := finalBank }
  have hsrc₁ : S₁.R src = [] := by simp [S₁, finalBank, elementaryCompileLoopBank, hsrc .output, hss]
  have hsaved₁ : S₁.R saved = (elementaryCoordinateFrames (A := A) L cs).reverse := by
    simp [S₁, finalBank, elementaryCompileLoopBank, hsaved .output, harchive]
  obtain ⟨v₂, hu₂, he₂⟩ := configurationRestore_exec body src saved hss.symm
    (elementaryCoordinateFrames L cs) [] v₁ S₁ hsaved₁ hsrc₁
  have hfinal : Function.update (Function.update finalBank saved []) src (elementaryCoordinateFrames L cs ++ []) =
      Function.update S.R (rg .output) (elementaryFrames ds ++ S.R (rg .output)) := by
    funext j
    by_cases hj : j = src
    · subst j
      simp [Function.update_of_ne (hsrc .output), hinput]
    · by_cases ha : j = saved
      · subst j
        simp [hss.symm, hsaved .output, harchive]
      · by_cases ho : j = rg .output
        · subst j
          simp [finalBank, elementaryCompileLoopBank, (hsrc .output).symm, (hsaved .output).symm]
        · simp [finalBank, elementaryCompileLoopBank, hj, ha, ho]
  have he₂' : Exec body (moveR saved src id) (mk v₁ S₁)
      (2 * (elementaryCoordinateFrames (A := A) L cs).length + 2)
      (mk v₂ { S with R := Function.update S.R (rg .output) (elementaryFrames ds ++ S.R (rg .output)) }) := by
    simpa only [S₁, hfinal] using he₂
  exact ⟨ds, v₂, (1 + m₁) + (2 * (elementaryCoordinateFrames (A := A) L cs).length + 2), hv, hsize, hk,
    hu₂.trans hu₁, by omega, Exec.seq heloop he₂'⟩

end IntegerMultBounds.MathlibTM2.Routing
