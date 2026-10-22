module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompiler
public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationSize

/-! Closed private-bank cleanup bound for elementary instruction compilation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

theorem elementaryCompilerReady_length {T A n : ℕ}
    (R : Fin T → List (Fin (A + 4))) (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg)
    (L Lb : ℕ) (target source : Fin n) (rowBits triple : List Bool) (hl : triple.length ≤ Lb + 2)
    (j : Fin T) (hj : j ∈ elementaryCompilerPrivate.map rg) :
    (elementaryCompilerReady R rg L target source rowBits triple j).length ≤
      n + rowBits.length + Lb + L + 2 := by
  have ht := target.isLt
  have hs := source.isLt
  have hq := ((elementarySwapSpec target).coordinate source).isLt
  have hr := Nat.sub_le n (target.val + (elementarySwapSpec target).w)
  have hh := Nat.sub_le n (((elementarySwapSpec target).coordinate source).val + 1)
  obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hj
  simp only [elementaryCompilerPrivate, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [elementaryCompilerReady, elementaryCompilerHeaders, elementaryHeaderBank,
    elementaryCompilerHeader, elementaryCompilerCoordinates, elementaryCoordinateFinalBank,
    elementaryCoordinateInitialBank, elementaryCompilerWords, elementaryHeaderWords,
    binaryPowerBits, binaryNonemptyBits, hrg.eq_iff]
  all_goals first | omega | (split_ifs <;> simp_all only [List.length_nil, List.length_cons] <;> omega)

theorem elementaryCompilerCleanCost_le {T A n : ℕ}
    (R : Fin T → List (Fin (A + 4))) (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg)
    (L Lb : ℕ) (target source : Fin n) (rowBits triple : List Bool) (hl : triple.length ≤ Lb + 2) :
    metadataCleanCost (elementaryCompilerReady R rg L target source rowBits triple)
      (elementaryCompilerPrivate.map rg) ≤ 26 * (n + rowBits.length + Lb + L + 3) + 1 := by
  have h := metadataCleanCost_le (elementaryCompilerReady R rg L target source rowBits triple)
    (elementaryCompilerPrivate.map rg) (n + rowBits.length + Lb + L + 2)
    (elementaryCompilerReady_length R rg hrg L Lb target source rowBits triple hl)
  have hlen : (elementaryCompilerPrivate.map rg).length = 13 := by rfl
  rw [hlen] at h
  omega

/-- Each emitted instruction has a linear-size framed encoding. -/
theorem elementaryCompiled_frame_length_le {n A : ℕ} (target source : Fin n) (hne : source ≠ target)
    (rowBits triple : List Bool) (Lb : ℕ) (hl : triple.length ≤ Lb + 2) :
    ((ElementaryInstruction.mk target source hne (elementaryCompilerWords rowBits triple target)).frame :
      List (Fin (A + 4))).length ≤ rowBits.length + 3 * n + Lb + 11 := by
  have ht := target.isLt
  have hr := Nat.sub_le n (target.val + (elementarySwapSpec target).w)
  simp [ElementaryInstruction.frame, ElementaryInstruction.words, elementaryConfigWord,
    elementaryCompilerWords, elementaryHeaderWords, List.ofFn_succ, configurationWords,
    binaryPowerBits, binaryNonemptyBits]
  split_ifs <;> simp_all only [List.length_nil, List.length_cons] <;> omega

/-- The actual compiler with a closed bound for private cleanup. -/
theorem elementaryCompiler_exec_le {T Q A n : ℕ} {P U : Type}
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
        (26 * (n + rowBits.length + Lb + L + 3) + 1) ∧
      Exec body (elementaryCompilerProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .output) (d.frame ++ S.R (rg .output)) }) := by
  obtain ⟨triple, v', m, hl, hv, hu, hm, he⟩ := elementaryCompiler_exec body rg hrg L Lb rows B hn hB
    target source hne rowBits hrow hrowNe hrowValue v S hwidth htarget hsource hrows hblock hblank
  have hc := elementaryCompilerCleanCost_le S.R rg hrg L Lb target source rowBits triple hl
  exact ⟨triple, v', m, hl, hv, hu, by omega, he⟩

end IntegerMultBounds.MathlibTM2.Routing
