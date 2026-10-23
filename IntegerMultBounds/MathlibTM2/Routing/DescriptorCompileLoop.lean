module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorCompileData

/-! One fixed descriptor compiler loop for arbitrary finite selector tables. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def descriptorCompileLoopBody {T Q A : ℕ} {P U : Type}
    (rg : BinaryMaskReg → Fin T) (src saved out : Fin T) : Pr P T Q A U :=
  .seq (descriptorCompileCallProgram rg src saved out) (.act (peekR src))

theorem descriptorCompileLoop_exec {T Q A M : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : BinaryMaskReg → Fin T) (hrg : Function.Injective rg)
    (src saved out : Fin T) (hss : src ≠ saved) (hso : src ≠ out) (hao : saved ≠ out)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r) (hout : ∀ r, out ≠ rg r)
    (L : ℕ) (hM : M < 2 ^ L) (qs : List (Fin M))
    (v : HS T Q A U) (S : Stacks T A) (hready : DescriptorCompileReady rg S.R L M)
    (hinput : S.R src = descriptorSelectorFrames L qs)
    (hflag : v.flag = (descriptorSelectorFrames (A := A) L qs).head?.isSome) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ qs.length * (descriptorCompileCallCost L M + 2) + 1 ∧
      Exec body (.loop (·.flag) (descriptorCompileLoopBody rg src saved out)) (mk v S) m
        (mk v' { S with R := descriptorCompileLoopBank S.R src saved out (descriptorSelectorFrames L qs) (descriptorRows qs.reverse) }) := by
  induction qs generalizing v S with
  | nil =>
    refine ⟨v, 1, rfl, by simp, ?_⟩
    rw [show descriptorRows (A := A) ([] : List (Fin M)).reverse = [] by rfl,
      descriptorSelectorFrames, descriptorCompileLoopBank_nil S.R src saved out hss hso hao hinput]
    exact Exec.loop_false (by simpa only [descriptorSelectorFrames, List.head?_nil, Option.isSome_none, mk_var] using hflag)
  | cons q qs ih =>
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := descriptorCompileCall_exec body rg hrg src saved out hss hso hao
      hsrc hsaved hout L M hM q (descriptorSelectorFrames L qs) v S hready hinput
    let frame : List (Fin (A + 4)) := binSyms L q.val ++ [separator]
    let row : List (Fin (A + 4)) := binSyms M (2 ^ q.val)
    let S₁ : Stacks T A := { S with R := descriptorCompileStepBank S.R src saved out frame row (descriptorSelectorFrames L qs) }
    have hi₁ : S₁.R src = descriptorSelectorFrames L qs := by simp [S₁, descriptorCompileStepBank, hso, hss]
    let v₂ := { v₁ with flag := (descriptorSelectorFrames (A := A) L qs).head?.isSome }
    have hp : (peekR src : Act T Q A U).run (mk v₁ S₁) = mk v₂ S₁ := by
      simp only [peekR_run, hi₁]
      rfl
    have hr₁ := descriptorCompileStep_ready S.R rg src saved out hsrc hsaved hout frame row
      (descriptorSelectorFrames (A := A) L qs) L M hready
    obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := ih v₂ S₁ hr₁ hi₁ rfl
    have hf : v.flag = true := by
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (descriptorSelectorFrames_cons_ne_nil (A := A) L q qs)
      simpa only [hx, List.head?_cons, Option.isSome_some] using hflag
    have hbank := descriptorCompileLoopBank_step S.R src saved out hss hso hao frame row
      (descriptorSelectorFrames L qs) (descriptorSelectorFrames L qs) (descriptorRows (A := A) qs.reverse)
    change descriptorCompileLoopBank S₁.R src saved out (descriptorSelectorFrames L qs) (descriptorRows qs.reverse) = _ at hbank
    rw [hbank] at he₃
    have he₃' : Exec body (.loop (·.flag) (descriptorCompileLoopBody rg src saved out)) (mk v₂ S₁) m₃
        (mk v₃ { S with R := descriptorCompileLoopBank S.R src saved out (descriptorSelectorFrames L (q :: qs)) (descriptorRows (q :: qs).reverse) }) := by
      simp only [List.reverse_cons, descriptorRows_append]
      simpa only [descriptorSelectorFrames, descriptorRows,
        List.map_singleton, List.flatten_singleton, frame, row, List.singleton_append, List.append_assoc] using he₃
    have hex := Exec.loop_true (body := body) (f := (·.flag)) (by simpa only [mk_var] using hf)
      (Exec.seq he₁ (hp ▸ Exec.act (body := body) (peekR src) (mk v₁ S₁))) he₃'
    refine ⟨v₃, m₁ + m₃ + 2, hu₃.trans hu₁, ?_, Exec.cast hex (by omega) rfl⟩
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

end IntegerMultBounds.MathlibTM2.Routing
