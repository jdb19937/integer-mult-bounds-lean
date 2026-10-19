module

public import IntegerMultBounds.MathlibTM2.M8.BitNetwork
public import IntegerMultBounds.MathlibTM2.M8.Machine.Segments
public import IntegerMultBounds.Networks.AffineFieldSegments

/-!
# Networks the recursive interchange machine runs

The recursive interchange machine works over the alphabet of `Shared50ModularControl.prime`, and
its coefficient stages accept the coefficients of Shared50's schedules and every coefficient
within `Networks.coefficientBound`. `Supports N` collects what the machine needs of a
`BitNetwork` beyond its own certificates: the network's prime is the machine's, every operation
of every edge program has supported coefficients (`Coordinates.CoeffSupported`), and there are at
least as many contract roles as address coordinates per field (the row divisor `roleCount^k` of
the arbitrary-width wrapper then dominates the width `width^k`). `Runs N` is the same with every
coefficient within the bound; it gives `Supports N` (`Runs.supports`).

Under `Supports N`, every nonrecursive run of an edge program (`AffineFieldSegments.runs`) is a
good segment (`segment_good`), so it compiles to one fixed clean machine (`Segments.realizes`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks

/-- What the machine needs of a bit network. -/
structure Runs (N : BitNetwork) : Prop where
  prime_eq : N.prime = Shared50ModularControl.prime
  coeff_bound : ∀ (i : N.World ⊕ N.Temp) (p : FieldProgram N.width), Step.edge i p ∈ N.control →
    ∀ op ∈ p, Coordinates.CoeffBounded op
  width_le_roleCount : N.width ≤ N.roleCount

/-- What the machine needs of a bit network, with supported coefficients. -/
structure Supports (N : BitNetwork) : Prop where
  prime_eq : N.prime = Shared50ModularControl.prime
  coeff_supported : ∀ (i : N.World ⊕ N.Temp) (p : FieldProgram N.width), Step.edge i p ∈ N.control →
    ∀ op ∈ p, Coordinates.CoeffSupported op
  width_le_roleCount : N.width ≤ N.roleCount

variable {N : BitNetwork}

/-- Bounded coefficients are supported. -/
theorem Runs.supports (hN : Runs N) : Supports N where
  prime_eq := hN.prime_eq
  coeff_supported i p hp op hop := (hN.coeff_bound i p hp op hop).supported (N.legal i p hp op hop)
  width_le_roleCount := hN.width_le_roleCount

/-- Every nonrecursive run of an edge program is a good segment. -/
theorem segment_good (hN : Supports N) {i : N.World ⊕ N.Temp} {p : FieldProgram N.width}
    (hp : Step.edge i p ∈ N.control) {ops : FieldProgram N.width}
    (hops : ops ∈ AffineFieldSegments.runs (AffineFieldSegments.split p)) : Segments.Good ops := by
  obtain ⟨hmem, hn⟩ := AffineFieldSegments.split_run_spec _ _ hops
  exact ⟨fun op hop => N.legal i p hp op (hmem op hop),
    fun op hop => hN.coeff_supported i p hp op (hmem op hop), hn⟩

end
end IntegerMultBounds.MathlibTM2.M8.Machine
