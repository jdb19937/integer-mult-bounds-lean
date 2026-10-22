module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompileTable

/-! Closed input-size cost bounds for uniform coordinate-table compilation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

theorem elementaryCoordinateFrames_length {A n : ℕ} (L : ℕ) (cs : List (ElementaryCoordinate n)) :
    (elementaryCoordinateFrames (A := A) L cs).length = cs.length * (2 * L + 2) := by
  induction cs with
  | nil => simp [elementaryCoordinateFrames]
  | cons c cs ih =>
    simp [elementaryCoordinateFrames, elementaryPairWords, configurationWords, ih, Nat.add_mul]
    omega

theorem elementaryFrames_length_le {A n : ℕ} (ds : List (ElementaryInstruction n)) (F : ℕ)
    (hsize : ∀ d ∈ ds, (d.frame : List (Fin (A + 4))).length ≤ F) :
    (elementaryFrames (A := A) ds).length ≤ ds.length * F := by
  induction ds with
  | nil => simp [elementaryFrames]
  | cons d ds ih =>
    have hd := hsize d (by simp)
    have hi := ih (fun e he => hsize e (by simp [he]))
    simp only [elementaryFrames, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem elementaryCompileTable_cost (k C F L x out : ℕ)
    (hx : x ≤ k * (C + 2) + 7 * out + 2 * (k * (2 * L + 2)) + 4)
    (ho : out ≤ k * F) : x ≤ k * (C + 7 * F + 4 * L + 6) + 4 := by
  have he : k * (C + 7 * F + 4 * L + 6) =
      k * (C + 2) + 7 * (k * F) + 2 * (k * (2 * L + 2)) := by ring
  rw [he]
  omega

/-- Actual table compilation with a bound depending only on input dimensions
and the number of coordinate pairs, including complete input restoration. -/
theorem elementaryCompileTable_exec_le {n : ℕ} (body : P → Pr P T Q A U)
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
      m ≤ cs.length * (elementaryCompileBase n L Lb rowBits.length +
        7 * (rowBits.length + 3 * n + Lb + 11) + 4 * L + 6) + 4 ∧
      Exec body (elementaryCompileTableProgram rg src saved) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .output) (elementaryFrames ds ++ S.R (rg .output)) }) := by
  obtain ⟨ds, v', m, hv, hsize, hk, hu, hm, he⟩ := elementaryCompileTable_exec body rg hrg src saved hss hsrc hsaved
    L Lb rows B hn hB rowBits hrow hrowNe hrowValue cs v S hready hinput harchive
  have hlength := congrArg List.length hk
  simp only [List.length_map, List.length_reverse] at hlength
  have hf := elementaryFrames_length_le (A := A) ds (rowBits.length + 3 * n + Lb + 11) hsize
  rw [hlength] at hf
  rw [elementaryCoordinateFrames_length] at hm
  exact ⟨ds, v', m, hv, hsize, hk, hu, elementaryCompileTable_cost _ _ _ _ _ _ hm hf, he⟩

end IntegerMultBounds.MathlibTM2.Routing
