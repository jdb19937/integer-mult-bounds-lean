module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalData
public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationTrim

/-!
# Executed canonicalization of computed binary headers

One fixed program converts a padded arithmetic register into canonical header
bits, preserving its numeric value. Every other stack, including scratch, is
restored. No numeric value or width is compiled into the program.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def binaryCanonicalProgram (src tmp : Fin T) : Pr P T Q A U :=
  configurationTrim src tmp (fun x => x == bitSymbol false)

/-- Normalize an arithmetic result in linear time, with exact frame restoration. -/
theorem binaryCanonical_exec (body : P → Pr P T Q A U) (src tmp : Fin T) (hst : src ≠ tmp)
    (L x : ℕ) (hx : x < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms L x) (htmp : S.R tmp = []) :
    ∃ (cs : List Bool) (v' : HS T Q A U), GrowingCounterData.Canonical cs ∧
      Counter.value cs = x ∧ cs.length ≤ L ∧ v'.user = v.user ∧
      Exec body (binaryCanonicalProgram src tmp) (mk v S) (4 * L + 6)
        (mk v' { S with R := Function.update S.R src (cs.map bitSymbol) }) := by
  obtain ⟨cs, k, hsplit, hcanonical⟩ := binaryCanonical_split (binBits L x)
  have hvalue : Counter.value cs = x := by
    have hv := binaryCanonical_value_binBits L x hx
    rw [hsplit, binaryCanonical_value_padding] at hv
    exact hv
  have hlength : cs.length ≤ L := by
    have hl := congrArg List.length hsplit
    simp only [length_binBits, List.length_append, List.length_replicate] at hl
    omega
  have hstop : (((cs.map (bitSymbol (a := A))).reverse.head?.map
      (fun x => x == bitSymbol false)).getD false) = false := by
    rcases hcanonical with he | he
    · subst cs
      rfl
    · simp only [List.head?_reverse, List.getLast?_map, he]
      rfl
  have hinput : S.R src = cs.map bitSymbol ++ (List.replicate k false).map bitSymbol := by
    rw [hsrc, binSyms_eq, hsplit, List.map_append]
  obtain ⟨v', hu, he⟩ := configurationTrim_exec body src tmp hst (fun x => x == bitSymbol false)
    (cs.map bitSymbol) ((List.replicate k false).map bitSymbol)
    (by simp) hstop v S hinput htmp
  refine ⟨cs, v', hcanonical, hvalue, hlength, hu, ?_⟩
  have hl : (cs.map (bitSymbol (a := A)) ++ (List.replicate k false).map bitSymbol).length = L := by
    rw [← List.map_append, ← hsplit, List.length_map, length_binBits]
  simpa only [binaryCanonicalProgram, hl] using he

end IntegerMultBounds.MathlibTM2.Routing
