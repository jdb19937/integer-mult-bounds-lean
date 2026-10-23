module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorCompile
public import IntegerMultBounds.MathlibTM2.Routing.DescriptorRows

/-! Compile interpreter tables in their required order from reversed binary
selector frames. The selector input is restored, rather than consumed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

theorem descriptorSelectorFrames_length {A M : ℕ} (L : ℕ) (qs : List (Fin M)) :
    (descriptorSelectorFrames (A := A) L qs).length = qs.length * (L + 1) := by
  induction qs with
  | nil => simp [descriptorSelectorFrames]
  | cons q qs ih =>
    simp only [descriptorSelectorFrames, List.length_append, length_binSyms,
      List.length_cons, ih, Nat.add_mul, Nat.one_mul]
    omega

theorem sourceTableCompile_exec {T Q A W : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : BinaryMaskReg → Fin T) (hrg : Function.Injective rg)
    (src saved out : Fin T) (hss : src ≠ saved) (hso : src ≠ out) (hao : saved ≠ out)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r) (hout : ∀ r, out ≠ rg r)
    (L : ℕ) (hW : W < 2 ^ L) (qs : List (Fin W))
    (v : HS T Q A U) (S : Stacks T A) (hready : DescriptorCompileReady rg S.R L W)
    (hinput : S.R src = descriptorSelectorFrames L qs.reverse) (hsave : S.R saved = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ qs.length * (descriptorCompileCallCost L W + 2) +
        2 * (qs.length * (L + 1)) + 4 ∧
      Exec body (descriptorCompileProgram rg src saved out) (mk v S) m
        (mk v' { S with R := Function.update S.R out ((sourceTable qs).flatten.map (bitSymbol (a := A)) ++ S.R out) }) := by
  obtain ⟨v', m, hu, hm, he⟩ := descriptorCompile_exec body rg hrg src saved out hss hso hao
    hsrc hsaved hout L hW qs.reverse v S hready hinput hsave
  refine ⟨v', m, hu, ?_, ?_⟩
  · simpa only [descriptorSelectorFrames_length, List.length_reverse] using hm
  · simpa only [List.reverse_reverse, sourceTable_binSyms, descriptorRows] using he

theorem patternTableCompile_exec {T Q A W N : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : BinaryMaskReg → Fin T) (hrg : Function.Injective rg)
    (src saved out : Fin T) (hss : src ≠ saved) (hso : src ≠ out) (hao : saved ≠ out)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r) (hout : ∀ r, out ≠ rg r)
    (L : ℕ) (hW : W + 1 < 2 ^ L) (s : Fin N → Option (Fin W))
    (v : HS T Q A U) (S : Stacks T A) (hready : DescriptorCompileReady rg S.R L (W + 1))
    (hinput : S.R src = descriptorSelectorFrames L (List.ofFn (patternIndex s)).reverse)
    (hsave : S.R saved = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ N * (descriptorCompileCallCost L (W + 1) + 2) + 2 * (N * (L + 1)) + 4 ∧
      Exec body (descriptorCompileProgram rg src saved out) (mk v S) m
        (mk v' { S with R := Function.update S.R out ((patternTable s).flatten.map (bitSymbol (a := A)) ++ S.R out) }) := by
  obtain ⟨v', m, hu, hm, he⟩ := sourceTableCompile_exec body rg hrg src saved out hss hso hao
    hsrc hsaved hout L hW (List.ofFn (patternIndex s)) v S hready hinput hsave
  exact ⟨v', m, hu, by simpa only [List.length_ofFn] using hm, he⟩

end IntegerMultBounds.MathlibTM2.Routing
