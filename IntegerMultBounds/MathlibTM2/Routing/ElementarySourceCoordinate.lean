module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationChoose
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCoordinateData

/-! Executed source renaming from live binary target and source coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

/-- The zero-source branch copies the target; all other sources remain unchanged.
The unary gate and both binary coordinate inputs are restored. -/
theorem elementarySourceCoordinate_exec {T Q A n : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (target source : Fin n) (hne : source ≠ target)
    (gate sourceBin targetBin dst tmp work : Fin T)
    (hsource : [sourceBin, dst, tmp, work].Nodup) (htarget : [targetBin, dst, tmp, work].Nodup)
    (L : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hgate : (S.R gate).length = source.val)
    (hsourceBin : S.R sourceBin = binSyms L source.val)
    (htargetBin : S.R targetBin = binSyms L target.val)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (configurationChooseProgram gate sourceBin targetBin dst tmp work) (mk v S) (6 * L + 8)
        (mk v' { S with R := Function.update S.R dst (binSyms L ((elementarySwapSpec target).coordinate source).val) }) := by
  have hselect := elementarySwap_source_gate target source hne (S.R gate) hgate
  have hword : S.R (if (S.R gate).head?.isSome then sourceBin else targetBin) =
      binSyms L ((elementarySwapSpec target).coordinate source).val := by
    cases hg : (S.R gate).head?.isSome with
    | false =>
      simp only [hg, Bool.false_eq_true, reduceIte] at hselect ⊢
      rw [← hselect]
      exact htargetBin
    | true =>
      simp only [hg, reduceIte] at hselect ⊢
      rw [← hselect]
      exact hsourceBin
  obtain ⟨v', hu, he⟩ := configurationChoose_exec body gate sourceBin targetBin dst tmp work
    hsource htarget v S hdst htmp hwork
  refine ⟨v', hu, ?_⟩
  simpa only [hword, length_binSyms] using he

end IntegerMultBounds.MathlibTM2.Routing
