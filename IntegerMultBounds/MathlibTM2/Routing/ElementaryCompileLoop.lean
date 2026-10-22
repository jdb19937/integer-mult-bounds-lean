module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompileLoopData

/-! One fixed program compiles any finite table of target/source coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def elementaryCompileLoopBody (rg : ElementaryCompilerReg → Fin T) (src saved : Fin T) : Pr P T Q A U :=
  .seq (elementaryCompileCallProgram rg src saved) (.act (peekR src))

def elementaryCompileLoopProgram (rg : ElementaryCompilerReg → Fin T) (src saved : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR src)) (.loop (·.flag) (elementaryCompileLoopBody rg src saved))

private theorem elementaryCompileLoop_cost (C k F O x y : ℕ)
    (hx : x ≤ C + 7 * F) (hy : y ≤ k * (C + 2) + 7 * O + 1) :
    x + y + 2 ≤ (k + 1) * (C + 2) + 7 * (O + F) + 1 := by
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- All generated instructions are valid and match the reversed coordinate table.
Prepending frames explains this order. The entire reusable bank is restored. -/
theorem elementaryCompileLoop_loop_exec {n : ℕ} (body : P → Pr P T Q A U)
    (rg : ElementaryCompilerReg → Fin T) (hrg : Function.Injective rg)
    (src saved : Fin T) (hss : src ≠ saved) (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (L Lb rows B : ℕ) (hn : n < 2 ^ L) (hB : B < 2 ^ Lb)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = rows) (cs : List (ElementaryCoordinate n))
    (v : HS T Q A U) (S : Stacks T A) (hready : ElementaryCompileReady rg S.R n L Lb B rowBits)
    (hinput : S.R src = elementaryCoordinateFrames L cs)
    (hflag : v.flag = (elementaryCoordinateFrames (A := A) L cs).head?.isSome) :
    ∃ (ds : List (ElementaryInstruction n)) (v' : HS T Q A U) (m : ℕ),
      (∀ d ∈ ds, d.Valid rows B) ∧
      (∀ d ∈ ds, (d.frame : List (Fin (A + 4))).length ≤ rowBits.length + 3 * n + Lb + 11) ∧ ds.map (fun d => (d.target, d.source)) = cs.reverse.map ElementaryCoordinate.key ∧
      v'.user = v.user ∧
      m ≤ cs.length * (elementaryCompileBase n L Lb rowBits.length + 2) +
        7 * (elementaryFrames (A := A) ds).length + 1 ∧
      Exec body (.loop (·.flag) (elementaryCompileLoopBody rg src saved)) (mk v S) m
        (mk v' { S with R := elementaryCompileLoopBank S.R rg src saved (elementaryCoordinateFrames L cs) (elementaryFrames ds) }) := by
  induction cs generalizing v S with
  | nil =>
    refine ⟨[], v, 1, by simp, by simp, rfl, rfl, by simp [elementaryFrames], ?_⟩
    rw [elementaryCoordinateFrames, elementaryFrames, elementaryCompileLoopBank_nil S.R rg src saved hss
      (hsrc .output) (hsaved .output) (by simpa only [elementaryCoordinateFrames] using hinput)]
    exact Exec.loop_false (by simpa only [elementaryCoordinateFrames, List.head?_nil, Option.isSome_none, mk_var] using hflag)
  | cons c cs ih =>
    obtain ⟨triple, v₁, m₁, hdvalid, hdsize, hu₁, hm₁, he₁⟩ := elementaryCompileCall_exec body rg hrg src saved hss hsrc hsaved
      L Lb rows B hn hB c.target c.source c.source_ne rowBits hrow hrowNe hrowValue
      (elementaryCoordinateFrames L cs) v S hready.width hready.rows hready.block hready.blank hready.target0 hready.source0 hinput
    let d := ElementaryInstruction.mk c.target c.source c.source_ne (elementaryCompilerWords rowBits triple c.target)
    let pair : List (Fin (A + 4)) := configurationWords (elementaryPairWords L c.target.val c.source.val)
    let S₁ : Stacks T A := { S with R := elementaryCompileStepBank S.R rg src saved pair d.frame (elementaryCoordinateFrames L cs) }
    have hi₁ : S₁.R src = elementaryCoordinateFrames L cs := by
      simp [S₁, elementaryCompileStepBank, hsrc .output, hss]
    let v₂ := { v₁ with flag := (elementaryCoordinateFrames (A := A) L cs).head?.isSome }
    have hp : (peekR src : Act T Q A U).run (mk v₁ S₁) = mk v₂ S₁ := by
      simp only [peekR_run, hi₁]
      rfl
    have hr₁ : ElementaryCompileReady rg S₁.R n L Lb B rowBits :=
      hready.congr (elementaryCompileStepBank_keep S.R rg hrg src saved hsrc hsaved pair d.frame _)
    obtain ⟨ds, v₃, m₃, hv, hsize, hk, hu₃, hm₃, he₃⟩ := ih v₂ S₁ hr₁ hi₁ rfl
    have hf : v.flag = true := by
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (elementaryCoordinateFrames_cons_ne_nil (A := A) L c cs)
      simpa only [hx, List.head?_cons, Option.isSome_some] using hflag
    have hbank := elementaryCompileLoopBank_step S.R rg src saved hss (hsrc .output) (hsaved .output)
      pair (d.frame : List (Fin (A + 4))) (elementaryCoordinateFrames L cs) (elementaryCoordinateFrames L cs) (elementaryFrames ds)
    change elementaryCompileLoopBank S₁.R rg src saved (elementaryCoordinateFrames L cs) (elementaryFrames ds) = _ at hbank
    rw [hbank] at he₃
    have he₃' : Exec body (.loop (·.flag) (elementaryCompileLoopBody rg src saved)) (mk v₂ S₁) m₃
        (mk v₃ { S with R := elementaryCompileLoopBank S.R rg src saved (elementaryCoordinateFrames L (c :: cs)) (elementaryFrames (ds ++ [d])) }) := by
      simpa only [S₁, elementaryFrames_append, elementaryFrames, List.append_nil, elementaryCoordinateFrames] using he₃
    have hex := Exec.loop_true (body := body) (f := (·.flag)) (by simpa only [mk_var] using hf)
      (Exec.seq he₁ (hp ▸ Exec.act (body := body) (peekR src) (mk v₁ S₁))) he₃'
    refine ⟨ds ++ [d], v₃, m₁ + m₃ + 2, ?_, ?_, ?_, hu₃.trans hu₁, ?_, Exec.cast hex (by omega) rfl⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hv e he
      · have he' : e = d := by simpa using he
        subst e
        exact hdvalid
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hsize e he
      · have he' : e = d := by simpa using he
        subst e
        exact hdsize
    · simp only [List.map_append, List.map_singleton, List.reverse_cons, List.map_append, hk]
      rfl
    · have hc : m₁ ≤ elementaryCompileBase n L Lb rowBits.length + 7 * (d.frame : List (Fin (A + 4))).length := by
        change m₁ ≤ (8 * L + 13) +
          (elementaryCompilerPrepareBound n L Lb rowBits.length + 7 * (d.frame : List (Fin (A + 4))).length + 1 +
            (26 * (n + rowBits.length + Lb + L + 3) + 1)) + (4 * L + 5) at hm₁
        unfold elementaryCompileBase
        omega
      simp only [List.length_cons, elementaryFrames_append, elementaryFrames, List.append_nil, List.length_append]
      exact elementaryCompileLoop_cost _ _ _ _ _ _ hc hm₃

end IntegerMultBounds.MathlibTM2.Routing
