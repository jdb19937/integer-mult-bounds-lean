module

public import IntegerMultBounds.MathlibTM2.M8.Machine.Net
public import IntegerMultBounds.Networks.Shared50FixedControl
public import IntegerMultBounds.Networks.CircuitRouting
public import IntegerMultBounds.Machine.Shared50OrderedPieces
public import IntegerMultBounds.Machine.Shared50RecursiveNodeLayout
public import IntegerMultBounds.Shared50Parameters

/-!
# Shared50 as a bit network

Shared50's fixed control (`Shared50FixedControl.control`) is a bit network on its World roles
with no temporaries (`network`): its edges keep their roles and rational field programs, and its
gates are renamed along `World ≃ Role ⊕ Empty` (`step`). Its run on every stream bank is
Shared50's run (`run_step`), so it is the routed transpose (`run_identity`). Its certificates are
Shared50's: the interchange count `s` (`calls_exact`), legal programs over `ℚ` and mod every power
of the prime, XOR gates, and the branching bound at `Shared50Parameters.tau`.

Its coefficients are those of Shared50's schedules, which the machine's coefficient stages accept
(`supported`), so it runs on the machine (`supports`, `net`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.Shared50Network

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks
open Shared50ModularControl (prime)

/-- Shared50's roles. -/
abbrev Role : Type := Shared50GlobalBudget.World

/-- The wires of the network: Shared50's roles, no temporaries. -/
def inl : Role ≃ Role ⊕ Empty := (Equiv.sumEmpty Role Empty).symm

/-- One step of Shared50's control on the network's wires. -/
def step : Shared50OrderedControl.Control → Step (Role ⊕ Empty) (M8.FieldProgram 125000)
  | .edge i p => .edge (.inl i) p
  | .gate g => .gate (g.rename inl)

/-- Shared50's control on the network's wires. -/
def control : List (Step (Role ⊕ Empty) (M8.FieldProgram 125000)) :=
  Shared50FixedControl.control.map step

theorem moduleGate_rename {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (g : Circuit.Gate Role (ZMod 2)) (x : Role ⊕ Empty → E) :
    FramedCircuit.moduleGate (g.rename inl) x ∘ inl = FramedCircuit.moduleGate g (x ∘ inl) := by
  funext k
  simp only [Function.comp_apply, FramedCircuit.moduleGate, Circuit.Gate.rename, List.map_map]
  by_cases hk : k = g.target
  · subst hk
    simp only [Function.update_self, Function.comp_def]
  · rw [Function.update_of_ne (inl.injective.ne hk), Function.update_of_ne hk]
    rfl

/-- The network runs as Shared50's control on the contract roles. -/
theorem run_step {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (edge : M8.FieldProgram 125000 → E → E) (s : List Shared50OrderedControl.Control)
    (x : Role ⊕ Empty → E) :
    Step.run edge (s.map step) x ∘ inl = FramedControlSchedule.run edge s (x ∘ inl) := by
  induction s generalizing x with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map_cons, Step.run, FramedControlSchedule.run]
    rw [ih]
    congr 1
    cases c with
    | edge i p =>
      simp only [step, Step.execute, FramedControlSchedule.execute]
      exact Function.update_comp_eq_of_injective x inl.injective i _
    | gate g =>
      simp only [step, Step.execute, FramedControlSchedule.execute]
      exact moduleGate_rename g x

theorem programs_step (s : List Shared50OrderedControl.Control) :
    Step.programs (s.map step) = FramedControlSchedule.programs s := by
  induction s with
  | nil => rfl
  | cons c rest ih =>
    cases c <;> simp [Step.programs, FramedControlSchedule.programs, step] at ih ⊢ <;> exact ih

theorem edge_mem {w : Role ⊕ Empty} {p : M8.FieldProgram 125000} (h : Step.edge w p ∈ control) :
    ∃ i, w = .inl i ∧ FramedControlSchedule.Step.edge i p ∈ Shared50FixedControl.control := by
  obtain ⟨c, hc, he⟩ := List.mem_map.mp h
  cases c with
  | edge i q =>
    simp only [step, Step.edge.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨i, rfl, hc⟩
  | gate g => simp [step] at he

theorem gate_mem {g' : Circuit.Gate (Role ⊕ Empty) (ZMod 2)} (h : Step.gate g' ∈ control) :
    ∃ g, g' = g.rename inl ∧ FramedControlSchedule.Step.gate g ∈ Shared50FixedControl.control := by
  obtain ⟨c, hc, he⟩ := List.mem_map.mp h
  cases c with
  | edge i q => simp [step] at he
  | gate g =>
    simp only [step, Step.gate.injEq] at he
    exact ⟨g, he.symm, hc⟩

theorem program_rational {w : Role ⊕ Empty} {p : M8.FieldProgram 125000} (h : Step.edge w p ∈ control) :
    p ∈ Shared50AffineControl.rationalSchedules := by
  obtain ⟨i, -, hi⟩ := edge_mem h
  rw [← Shared50FixedControl.programs_exact]
  exact List.mem_filterMap.mpr ⟨.edge i p, hi, rfl⟩

theorem specialize_eq (b : ℕ) (p : M8.FieldProgram 125000) :
    specialize (prime ^ b) p = Shared50OrderedControl.specializes b p := rfl

theorem edgeAction_eq (b : ℕ) : edgeAction 125000 (prime ^ b) = Shared50OrderedControl.edgeAction b := rfl

theorem coefficient_of_mem {op : AffineFieldProgram.Op (Fin 125000) ℚ} {r : ℚ}
    (hr : r ∈ M8.Exchange.opCoeffs op) : Shared50AffineCoefficients.Coefficient r op := by
  cases op with
  | affineH o =>
    cases o <;> simpa [M8.Exchange.opCoeffs, Shared50AffineCoefficients.Coefficient,
      Shared50AffineCoefficients.ScalarCoefficient] using hr
  | affineD o =>
    cases o <;> simpa [M8.Exchange.opCoeffs, Shared50AffineCoefficients.Coefficient,
      Shared50AffineCoefficients.ScalarCoefficient] using hr
  | addToD i j => simpa [M8.Exchange.opCoeffs, Shared50AffineCoefficients.Coefficient] using hr
  | subFromD i j => simpa [M8.Exchange.opCoeffs, Shared50AffineCoefficients.Coefficient] using hr
  | interchange i j => simp [M8.Exchange.opCoeffs] at hr

/-- Every operation of a Shared50 schedule has supported coefficients. -/
theorem supported {p : M8.FieldProgram 125000} (hp : p ∈ Shared50AffineControl.rationalSchedules)
    {op : AffineFieldProgram.Op (Fin 125000) ℚ} (hop : op ∈ p) : Coordinates.CoeffSupported op where
  occurs _ hr := Or.inl ⟨p, hp, op, hop, coefficient_of_mem hr⟩
  scaleH i _ he := Or.inl ⟨p, hp, i, Or.inl (he ▸ hop)⟩
  scaleD i _ he := Or.inl ⟨p, hp, i, Or.inr (he ▸ hop)⟩

/-- Shared50 as a bit network. -/
def network₀ : BitNetwork where
  World := Role
  Temp := Empty
  roleCount := IntegerMultBounds.Machine.Shared50TapeGlobal.roleCount
  roleEquiv := IntegerMultBounds.Machine.Shared50TapeGlobal.roleEquiv
  tempCount := 0
  tempEquiv := Equiv.equivOfIsEmpty (Fin 0) Empty
  width := 125000
  two_le_width := by norm_num
  prime := prime
  prime_prime := Shared50ModularControl.prime_prime
  prime_odd := Shared50ModularControl.prime_odd.ne'
  control := control
  route := Shared50ShearEndpoints.route
  route_involutive := Shared50ShearEndpoints.route_involutive
  rankSum := Shared50Parameters.s
  calls_exact := by
    have h := Shared50FixedControl.calls_exact
    simp only [Shared50OrderedControl.calls, AffineFieldSegments.split_recursiveCalls] at h
    rw [calls, control, programs_step]
    exact h
  legal i p hp op hop := Shared50AffineControl.rational_schedules_legal p (program_rational hp) op hop
  legal_mod b i p hp op hop := by
    apply Shared50AffineControl.schedules_legal b (specialize (prime ^ b) p) _ op hop
    rw [Shared50AffineControl.schedules_eq_map]
    exact List.mem_map.mpr ⟨p, program_rational hp, rfl⟩
  xor_gate g hg := by
    obtain ⟨g, rfl, hm⟩ := gate_mem hg
    obtain ⟨dst, src, hne, rfl⟩ := IntegerMultBounds.Machine.Shared50OrderedPieces.gate_xor ⟨g, hm⟩ g List.mem_cons_self
    exact ⟨inl dst, inl src, inl.injective.ne hne, rfl⟩
  run_identity b stored _ i a := by
    have h := congrFun (congrFun (run_step (edgeAction 125000 (prime ^ b))
      Shared50FixedControl.control stored) i) a
    rw [edgeAction_eq, Shared50FixedControl.run_identity] at h
    exact h
  tau := Shared50Parameters.tau
  tau_pos := by norm_num [Shared50Parameters.tau]
  tau_lt_one := by norm_num [Shared50Parameters.tau]
  branching := by
    have h := Shared50Parameters.branching_bound
    rw [← IntegerMultBounds.Machine.Shared50RecursiveNodeLayout.roleCount_eq_W] at h
    exact h

theorem supports₀ : Supports network₀ where
  prime_eq := rfl
  coeff_supported _ p hp op hop := supported (program_rational hp) hop
  width_le_roleCount := by
    change 125000 ≤ IntegerMultBounds.Machine.Shared50TapeGlobal.roleCount
    norm_num [IntegerMultBounds.Machine.Shared50TapeGlobal.roleCount]

/-- Shared50 as a bit network, sealed: nothing unfolds its control. -/
irreducible_def network : BitNetwork := network₀

theorem supports : Supports network := network_def ▸ supports₀

theorem network_tau : network.tau = Shared50Parameters.tau := by
  rw [network_def]
  rfl

/-- Shared50 on the machine. -/
@[reducible] def net : Net := ⟨network, supports⟩

end
end IntegerMultBounds.MathlibTM2.M8.Machine.Shared50Network
