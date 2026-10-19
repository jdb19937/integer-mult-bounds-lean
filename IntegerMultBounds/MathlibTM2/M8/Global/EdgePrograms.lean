module

public import IntegerMultBounds.MathlibTM2.M8.ExchangeBound
public import IntegerMultBounds.MathlibTM2.M8.Machine.Network

/-!
# Exchange edge programs meet the machine's requirements

`ExchangeEdges control`: every edge program of `control` is the exchange program
`Exchange.program U` of a rational matrix `U` whose entries have numerators and denominators at
most `10 ^ 10000`. For widths up to `529`, such a control has bounded coefficients
(`ExchangeEdges.coeff_bound`), legal programs over `ℚ` (`ExchangeEdges.legal`) and legal
reductions mod every power of the machine prime (`ExchangeEdges.legal_mod`). A bit network with
such a control, the machine prime and at least as many contract roles as coordinates runs on the
machine (`ExchangeEdges.runs`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

open IntegerMultBounds IntegerMultBounds.Networks

variable {ι : Type} {d : ℕ}

/-- Every edge program is the exchange program of a matrix with entries at most `10 ^ 10000`. -/
def ExchangeEdges (control : List (Step ι (FieldProgram d))) : Prop :=
  ∀ i p, Step.edge i p ∈ control → ∃ U : Matrix (Fin d) (Fin d) ℚ, p = Exchange.program U ∧
    ∀ a b, (U a b).num.natAbs ≤ 10 ^ 10000 ∧ (U a b).den ≤ 10 ^ 10000

variable {control : List (Step ι (FieldProgram d))}

theorem ExchangeEdges.coeff_bound (h : ExchangeEdges control) (hd1 : 1 ≤ d) (hd : d ≤ 529) :
    ∀ i p, Step.edge i p ∈ control → ∀ op ∈ p, Machine.Coordinates.CoeffBounded op := by
  intro i p hp op hop
  obtain ⟨U, rfl, hU⟩ := h i p hp
  exact Exchange.program_coeffs_le_coefficientBound U (by simpa using hd1) (by simpa using hd) hU
    op hop

theorem ExchangeEdges.legal (h : ExchangeEdges control) :
    ∀ i p, Step.edge i p ∈ control → ∀ op ∈ p, AffineFieldProgram.Legal op := by
  intro i p hp op hop
  obtain ⟨U, rfl, -⟩ := h i p hp
  exact Exchange.program_legal U op hop

theorem ExchangeEdges.legal_mod (h : ExchangeEdges control) (hd1 : 1 ≤ d) (hd : d ≤ 529) (b : ℕ) :
    ∀ i p, Step.edge i p ∈ control →
      ∀ op ∈ specialize (Shared50ModularControl.prime ^ b) p, AffineFieldProgram.Legal op := by
  intro i p hp op hop
  obtain ⟨U, rfl, hU⟩ := h i p hp
  exact Exchange.specialize_legal_of_bound U (by simpa using hd1) (by simpa using hd) hU
    Shared50ModularControl.prime_prime Shared50ModularControl.coefficientBound_lt_prime b op hop

/-- A bit network with exchange edges, the machine prime and at least as many contract roles as
address coordinates runs on the machine. -/
theorem ExchangeEdges.runs {N : BitNetwork} (h : ExchangeEdges N.control) (hd : N.width ≤ 529)
    (hp : N.prime = Shared50ModularControl.prime) (hr : N.width ≤ N.roleCount) :
    Machine.Runs N where
  prime_eq := hp
  coeff_bound := h.coeff_bound (by have := N.two_le_width; omega) hd
  width_le_roleCount := hr

end IntegerMultBounds.MathlibTM2.M8.Global
