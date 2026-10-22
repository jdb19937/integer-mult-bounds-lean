module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCoordinatePair
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompilerCost

/-! One executed iteration of the uniform elementary instruction-stream compiler. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def elementaryCompileCallProgram (rg : ElementaryCompilerReg → Fin T) (src saved : Fin T) : Pr P T Q A U :=
  .seq (elementaryPairLoad rg src saved)
    (.seq (elementaryCompilerProgram rg) (metadataClean ((elementaryPairSlots rg).map ConfigurationSlot.dst)))

def elementaryCompileStepBank (R : Fin T → List (Fin (A + 4))) (rg : ElementaryCompilerReg → Fin T)
    (src saved : Fin T) (pair frame rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src rest) saved (pair.reverse ++ R saved))
    (rg .output) (frame ++ R (rg .output))

/-- Load a coordinate pair, compile and emit its instruction, and restore the
reusable bank. Every phase is charged; the consumed pair is archived for rewind. -/
theorem elementaryCompileCall_exec {n : ℕ} (body : P → Pr P T Q A U)
    (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg)
    (src saved : Fin T) (hss : src ≠ saved) (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (L Lb rows B : ℕ) (hn : n < 2 ^ L) (hB : B < 2 ^ Lb) (target source : Fin n) (hne : source ≠ target)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = rows) (rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg (.coordinate .width)) = binSyms L n)
    (hrows : S.R (rg .rows) = rowBits.map bitSymbol) (hblock : S.R (rg .block) = binSyms Lb B)
    (hblank : ∀ r, r ∉ elementaryCompilerInputs → S.R (rg r) = [])
    (htarget0 : S.R (rg (.coordinate .target)) = []) (hsource0 : S.R (rg (.coordinate .source)) = [])
    (hinput : S.R src = configurationWords (elementaryPairWords L target.val source.val) ++ rest) :
    ∃ (triple : List Bool) (v' : HS T Q A U) (m : ℕ),
      let d := ElementaryInstruction.mk target source hne (elementaryCompilerWords rowBits triple target)
      d.Valid rows B ∧ (d.frame : List (Fin (A + 4))).length ≤ rowBits.length + 3 * n + Lb + 11 ∧ v'.user = v.user ∧
      m ≤ (8 * L + 13) +
        (elementaryCompilerPrepareBound n L Lb rowBits.length + 7 * (d.frame : List (Fin (A + 4))).length + 1 +
          (26 * (n + rowBits.length + Lb + L + 3) + 1)) + (4 * L + 5) ∧
      Exec body (elementaryCompileCallProgram rg src saved) (mk v S) m
        (mk v' { S with R := elementaryCompileStepBank S.R rg src saved (configurationWords (elementaryPairWords L target.val source.val)) d.frame rest }) := by
  have htmp : S.R (rg (.coordinate (.scratch 3))) = [] := hblank _ (by simp [elementaryCompilerInputs])
  obtain ⟨v₁, hu₁, he₁⟩ := elementaryPairLoad_exec body rg hrg src saved hss hsrc hsaved
    L target.val source.val rest v S hinput htmp htarget0 hsource0
  let S₁ : Stacks T A := { S with R := elementaryPairLoaded S.R rg src saved L target.val source.val rest }
  have hdata := elementaryPairLoaded_data S.R rg hrg src saved hsrc hsaved L target.val source.val rest
  have hkeep (r : ElementaryCompilerReg) (ht : r ≠ .coordinate .target) (hs : r ≠ .coordinate .source)
      (hw : r ≠ .coordinate (.scratch 3)) : S₁.R (rg r) = S.R (rg r) :=
    elementaryPairLoaded_keep S.R rg hrg src saved hsrc hsaved L target.val source.val rest r ht hs hw
  obtain ⟨triple, v₂, m₂, hl, hvalid, hu₂, hm₂, he₂⟩ := elementaryCompiler_exec_le body rg hrg
    L Lb rows B hn hB target source hne rowBits hrow hrowNe hrowValue v₁ S₁
    (by rw [hkeep _ (by simp) (by simp) (by simp)]; exact hwidth) hdata.1 hdata.2
    (by rw [hkeep _ (by simp) (by simp) (by simp)]; exact hrows)
    (by rw [hkeep _ (by simp) (by simp) (by simp)]; exact hblock)
    (elementaryPairLoaded_blank S.R rg hrg src saved hsrc hsaved L target.val source.val rest hblank)
  let d := ElementaryInstruction.mk target source hne (elementaryCompilerWords rowBits triple target)
  have hout : S₁.R (rg .output) = S.R (rg .output) := hkeep _ (by simp) (by simp) (by simp)
  have hout' : elementaryPairLoaded S.R rg src saved L target.val source.val rest (rg .output) = S.R (rg .output) := hout
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .output) (d.frame ++ S₁.R (rg .output)) }
  let keys := (elementaryPairSlots rg).map ConfigurationSlot.dst
  have hkeys : keys.Nodup := by simp [keys, elementaryPairSlots, List.nodup_cons, hrg.eq_iff]
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body keys hkeys v₂ S₂
  have ht₁ : S₁.R (rg (.coordinate .target)) = binSyms L target.val := hdata.1
  have hs₁ : S₁.R (rg (.coordinate .source)) = binSyms L source.val := hdata.2
  have hcost : metadataCleanCost S₂.R keys = 4 * L + 5 := by
    simp [keys, elementaryPairSlots, metadataCleanCost, S₂, hrg.eq_iff, ht₁, hs₁]
    omega
  have hfinal : metadataCleared S₂.R keys = elementaryCompileStepBank S.R rg src saved
      (configurationWords (elementaryPairWords L target.val source.val)) d.frame rest := by
    have h := elementaryPairLoaded_restore S.R rg hrg src saved hss hsrc hsaved L target.val source.val rest
      (d.frame ++ S₁.R (rg .output)) hinput htmp htarget0 hsource0
    simpa only [S₂, S₁, keys, hout', elementaryCompileStepBank] using h
  have he₃' : Exec body (metadataClean keys) (mk v₂ S₂) (4 * L + 5)
      (mk v₃ { S with R := elementaryCompileStepBank S.R rg src saved (configurationWords (elementaryPairWords L target.val source.val)) d.frame rest }) := by
    simpa only [hcost, hfinal] using he₃
  exact ⟨triple, v₃, (8 * L + 13) + (m₂ + (4 * L + 5)), hvalid,
    elementaryCompiled_frame_length_le target source hne rowBits triple Lb hl, hu₃.trans (hu₂.trans hu₁), by omega, Exec.seq he₁ (Exec.seq he₂ he₃')⟩

end IntegerMultBounds.MathlibTM2.Routing
