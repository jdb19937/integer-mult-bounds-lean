module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompilerMask
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompilerFrame

/-!
# Executed compilation of one elementary routing instruction

From five binary inputs, generate coordinates, canonical headers and source mask,
serialize the exact loader frame, then clear all private words. Only the output
configuration stream changes. Every phase, including final cleanup, is charged.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def elementaryCompilerPrepareBound (n L Lb rowLength : ℕ) : ℕ :=
  (5 * (L * (4 * n + 33) + 2 * n + 31) + 6 * n + 6 * L + 15) +
    (6 * rowLength + 12 * n + 44 * Lb + 190) + (10 * n + 9)

/-- One uniform compiler call emits a valid instruction and restores its bank. -/
theorem elementaryCompiler_exec {T Q A n : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg)
    (L Lb rows B : ℕ) (hn : n < 2 ^ L) (hB : B < 2 ^ Lb) (target source : Fin n) (hne : source ≠ target)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = rows)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg (.coordinate .width)) = binSyms L n)
    (htarget : S.R (rg (.coordinate .target)) = binSyms L target.val)
    (hsource : S.R (rg (.coordinate .source)) = binSyms L source.val)
    (hrows : S.R (rg .rows) = rowBits.map bitSymbol) (hblock : S.R (rg .block) = binSyms Lb B)
    (hblank : ∀ r, r ∉ elementaryCompilerInputs → S.R (rg r) = []) :
    ∃ (triple : List Bool) (v' : HS T Q A U) (m : ℕ),
      let d := ElementaryInstruction.mk target source hne (elementaryCompilerWords rowBits triple target)
      triple.length ≤ Lb + 2 ∧ d.Valid rows B ∧ v'.user = v.user ∧
      m ≤ elementaryCompilerPrepareBound n L Lb rowBits.length + 7 * (d.frame : List (Fin (A + 4))).length + 1 +
        metadataCleanCost (elementaryCompilerReady S.R rg L target source rowBits triple) (elementaryCompilerPrivate.map rg) ∧
      Exec body (elementaryCompilerProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .output) (d.frame ++ S.R (rg .output)) }) := by
  obtain ⟨triple, v₁, m₁, hc, hv, hl, hu₁, hm₁, he₁⟩ := elementaryCompilerPrepare_exec body rg hrg
    L Lb B hn hB target source hne rowBits v S hwidth htarget hsource hrows hblock hblank
  let d := ElementaryInstruction.mk target source hne (elementaryCompilerWords rowBits triple target)
  let bank := elementaryCompilerReady S.R rg L target source rowBits triple
  let S₁ : Stacks T A := { S with R := bank }
  let keys := elementaryCompilerPrivate.map rg
  have hout : rg .output ∉ keys := by simp [keys, elementaryCompilerPrivate, hrg.eq_iff]
  have houtput : bank (rg .output) = S.R (rg .output) :=
    elementaryCompilerReady_keep S.R rg L target source rowBits triple _ hout
  have hscratch (i : Fin 7) : S₁.R (rg (.coordinate (.scratch i))) = [] := by
    change elementaryCompilerReady S.R rg L target source rowBits triple (rg (.coordinate (.scratch i))) = []
    rw [elementaryCompilerReady_keep]
    · exact hblank _ (by simp [elementaryCompilerInputs])
    · simp [elementaryCompilerPrivate, hrg.eq_iff]
  obtain ⟨v₂, hu₂, hwrite, he₂⟩ := elementaryInstructionWrite_exec body
    (fun key => rg (elementaryCompilerWord key)) (rg .output)
    (rg (.coordinate (.scratch 3))) (rg (.coordinate (.scratch 4)))
    (by simp [List.nodup_cons, hrg.eq_iff])
    (by intro key; fin_cases key <;> simp [elementaryCompilerWord, hrg.eq_iff]) d v₁ S₁
    (fun key => elementaryCompilerReady_word S.R rg hrg L target source rowBits triple key)
    (hscratch 3) (hscratch 4)
  let S₂ : Stacks T A := { S with R := Function.update bank (rg .output) (d.frame ++ S.R (rg .output)) }
  have he₂' : Exec body (elementaryInstructionWrite (fun key => rg (elementaryCompilerWord key)) (rg .output)
      (rg (.coordinate (.scratch 3))) (rg (.coordinate (.scratch 4)))) (mk v₁ S₁)
      (configurationWriteCost S₁.R (List.ofFn fun key => rg (elementaryCompilerWord key))) (mk v₂ S₂) := by
    simpa only [S₁, houtput] using he₂
  have hkeys : keys.Nodup := by simp [keys, elementaryCompilerPrivate, List.nodup_cons, hrg.eq_iff]
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body keys hkeys v₂ S₂
  have hcost : metadataCleanCost S₂.R keys = metadataCleanCost bank keys := by
    apply metadataCleanCost_congr
    intro j hj
    apply Function.update_of_ne
    intro he
    subst j
    exact hout hj
  have hfinal : metadataCleared S₂.R keys = Function.update S.R (rg .output) (d.frame ++ S.R (rg .output)) :=
    elementaryCompiler_restore S.R rg hrg L target source rowBits triple _ hblank
  have he₃' : Exec body (metadataClean keys) (mk v₂ S₂) (metadataCleanCost bank keys)
      (mk v₃ { S with R := Function.update S.R (rg .output) (d.frame ++ S.R (rg .output)) }) := by
    simpa only [hcost, hfinal] using he₃
  refine ⟨triple, v₃, m₁ + (configurationWriteCost S₁.R
    (List.ofFn fun key => rg (elementaryCompilerWord key)) + metadataCleanCost bank keys),
    hl, elementaryCompilerWords_valid target source hne rowBits triple rows B hrow hrowNe hrowValue hc hv,
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂' he₃')⟩
  change m₁ + (configurationWriteCost S₁.R _ + metadataCleanCost bank keys) ≤
    elementaryCompilerPrepareBound n L Lb rowBits.length + 7 * (d.frame : List (Fin (A + 4))).length + 1 +
      metadataCleanCost bank keys
  change m₁ ≤ elementaryCompilerPrepareBound n L Lb rowBits.length at hm₁
  omega

end IntegerMultBounds.MathlibTM2.Routing
