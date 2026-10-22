module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-!
# Priced live source headers

Copy a fixed list of live field counters into one metadata header, in
least-significant-field order. The copies run from the end of the list because
`bcopy` prepends. Every source and both temporary registers are restored.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

/-- The field list is fixed program structure, rather than address data. -/
def sourceHeader (fields : List (Fin T)) (header t₁ t₂ : Fin T) : Pr P T Q A U :=
  match fields with
  | [] => .act .done
  | f :: fs => .seq (sourceHeader fs header t₁ t₂) (bcopy f header t₁ t₂)

/-- Exact copying cost, including the terminal no-op. -/
def sourceHeaderCost (R : Fin T → List (Fin (A + 4))) (fields : List (Fin T)) : ℕ :=
  match fields with
  | [] => 1
  | f :: fs => sourceHeaderCost R fs + (6 * (R f).length + 6)

variable (body : P → Pr P T Q A U)

/-- Build the actual header from live counters, preserving arbitrary initial
header contents as a suffix and restoring every other register. -/
theorem sourceHeader_exec (fields : List (Fin T)) (header t₁ t₂ : Fin T)
    (hfields : ∀ f ∈ fields, f ≠ header ∧ f ≠ t₁ ∧ f ≠ t₂)
    (htemps : [header, t₁, t₂].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (sourceHeader fields header t₁ t₂) (mk v S)
        (sourceHeaderCost S.R fields)
        (mk v' { S with
          R := Function.update S.R header ((fields.flatMap S.R) ++ S.R header) }) := by
  induction fields generalizing v S with
  | nil =>
    refine ⟨v, rfl, ?_⟩
    simpa [sourceHeader, sourceHeaderCost] using
      (Exec.act (body := body) .done (mk v S))
  | cons f fs ih =>
    have hf := hfields f (by simp)
    obtain ⟨v₁, hu₁, he₁⟩ := ih (fun f hf => hfields f (by simp [hf])) v S ht₁ ht₂
    let R₁ := Function.update S.R header (fs.flatMap S.R ++ S.R header)
    have hreg : [f, header, t₁, t₂].Nodup := by
      simpa using List.nodup_cons.mpr ⟨by simpa using hf, htemps⟩
    have ht₁h : t₁ ≠ header := by
      have := htemps; regs_ne this; exact Ne.symm (by assumption)
    have ht₂h : t₂ ≠ header := by
      have := htemps; regs_ne this; exact Ne.symm (by assumption)
    obtain ⟨v₂, hu₂, he₂⟩ := bcopy_exec body hreg v₁ { S with R := R₁ }
      (by simpa [R₁, ht₁h] using ht₁) (by simpa [R₁, ht₂h] using ht₂)
    refine ⟨v₂, hu₂.trans hu₁, Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
    · simp [sourceHeaderCost, R₁, hf.1]
    · congr 2
      funext k
      simp [R₁, Function.update_apply, List.flatMap_cons, List.append_assoc]
      split_ifs <;> simp_all

end IntegerMultBounds.MathlibTM2.Routing
