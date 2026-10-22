module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationWrite
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryLoopData

/-! Serialize an actual six-word instruction frame for the elementary loop. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

/-- The code depends on six fixed source registers, never on the instruction's
coordinates, header values, or the accumulated instruction-stream length. -/
def elementaryInstructionWrite (words : Fin 6 → Fin T) (dst tmp work : Fin T) : Pr P T Q A U :=
  configurationWrite dst tmp work (List.ofFn words)

/-- Produce precisely the frame consumed by the executed instruction loader. -/
theorem elementaryInstructionWrite_exec {n : ℕ} (body : P → Pr P T Q A U)
    (words : Fin 6 → Fin T) (dst tmp work : Fin T) (hreg : [dst, tmp, work].Nodup)
    (hwords : ∀ key, words key ≠ dst ∧ words key ≠ tmp ∧ words key ≠ work)
    (d : ElementaryInstruction n) (v : HS T Q A U) (S : Stacks T A)
    (hbank : ∀ key, S.R (words key) = elementaryConfigWord n
      ((elementarySwapSpec d.target).coordinate d.source).val d.headers key)
    (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      configurationWriteCost S.R (List.ofFn words) ≤ 7 * (d.frame : List (Fin (A + 4))).length + 1 ∧
      Exec body (elementaryInstructionWrite words dst tmp work) (mk v S)
        (configurationWriteCost S.R (List.ofFn words))
        (mk v' { S with R := Function.update S.R dst (d.frame ++ S.R dst) }) := by
  have hdata : (List.ofFn words).map S.R = (d.words : List (List (Fin (A + 4)))) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext key
    exact hbank key
  have hframe : configurationWords ((List.ofFn words).map S.R) = (d.frame : List (Fin (A + 4))) := by
    rw [hdata]
    rfl
  obtain ⟨v', hu, he⟩ := configurationWrite_exec body dst tmp work hreg (List.ofFn words)
    (by intro src hs; obtain ⟨key, rfl⟩ := List.mem_ofFn.mp hs; exact hwords key) v S htmp hwork
  refine ⟨v', hu, ?_, ?_⟩
  · simpa only [hframe] using configurationWriteCost_le S.R (List.ofFn words)
  · simpa only [elementaryInstructionWrite, hframe] using he

end IntegerMultBounds.MathlibTM2.Routing
