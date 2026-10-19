module

public import IntegerMultBounds.MathlibTM2.M8.Global.NodeCost
public import IntegerMultBounds.MathlibTM2.M8.Global.EdgePrograms
public import IntegerMultBounds.MathlibTM2.M8.Global.Branching97

/-!
# The PR97 bit network

`pr97` is the PR97 node as a `BitNetwork`, sealed by `irreducible_def`: `108516254` contract roles, `3217908` temporaries,
`529` address coordinates, the machine prime, the framed node's physical steps as control, the
routed transpose as node theorem (`node_run`) and at most `57403754177` recursive children
(`calls_node_le`), so the branching certificate of `Branching97` applies. Every edge program of
the control is the exchange program of a nested frame difference (`exchangeEdges_node`), so the
machine runs it (`runs_pr97`). Its exponent is `Branching97.tau` (`pr97_tau`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local
open Classical

/-! ### What valid framed lists give the machine -/

section Phys
variable {ι : Type} [DecidableEq ι] {d : ℕ}

theorem frames_step (s : FStep ι d) (fr : ι → Mat d) (z : ι → Prop) (hfr : ∀ w, IsFrame (fr w))
    (hok : s.Ok fr z) : ∀ w, IsFrame (s.frames fr w) := by
  intro w
  cases s with
  | up i A B =>
    by_cases h : w = i
    · subst h; rw [FStep.frames, Function.update_self]; exact hok.2.1
    · rw [FStep.frames, Function.update_of_ne h]; exact hfr w
  | down i A B =>
    by_cases h : w = i
    · subst h; rw [FStep.frames, Function.update_self]; exact hok.2.1
    · rw [FStep.frames, Function.update_of_ne h]; exact hfr w
  | gate g F => exact hfr w
  | reset i => exact hfr w
  | relabel i F =>
    by_cases h : w = i
    · subst h; rw [FStep.frames, Function.update_self]; exact hok.2
    · rw [FStep.frames, Function.update_of_ne h]; exact hfr w

/-- Every edge of a valid framed list is the exchange program of an edge matrix. -/
theorem valid_edges : ∀ (L : List (FStep ι d)) (fr : ι → Mat d) (z : ι → Prop),
    (∀ w, IsFrame (fr w)) → Valid L fr z → ∀ i p, Step.edge i p ∈ physOf L →
      ∃ U, p = Exchange.program U ∧ EdgeMat U
  | [], _, _, _, _, _, _, h => by simp [physOf] at h
  | s :: rest, fr, z, hfr, hv, i, p, h => by
    rw [physOf, List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · cases s with
      | up j A B =>
        obtain ⟨hj, hB, hAB, hBA⟩ := hv.1
        simp only [FStep.phys, List.mem_singleton, Step.edge.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨_, rfl, edgeMat_sub (hj ▸ hfr j) hB hAB hBA⟩
      | down j A B =>
        obtain ⟨hj, hB, hAB, hBA⟩ := hv.1
        simp only [FStep.phys, List.mem_singleton, Step.edge.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ⟨_, rfl, edgeMat_sub hB (hj ▸ hfr j) hBA hAB⟩
      | gate g F => simp [FStep.phys] at h
      | reset j => simp [FStep.phys] at h
      | relabel j F => simp [FStep.phys] at h
    · exact valid_edges rest _ _ (frames_step s fr z hfr hv.1) hv.2 i p h

/-- Every gate of a valid framed list is an XOR of two distinct wires. -/
theorem valid_gates : ∀ (L : List (FStep ι d)) (fr : ι → Mat d) (z : ι → Prop), Valid L fr z →
    ∀ g, Step.gate g ∈ physOf L → ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src
  | [], _, _, _, _, h => by simp [physOf] at h
  | s :: rest, fr, z, hv, g, h => by
    rw [physOf, List.flatMap_cons, List.mem_append] at h
    rcases h with h | h
    · cases s with
      | gate g' F =>
        simp only [FStep.phys, List.mem_singleton, Step.gate.injEq] at h
        subst h
        exact hv.1.2
      | up j A B => simp [FStep.phys] at h
      | down j A B => simp [FStep.phys] at h
      | reset j => simp [FStep.phys] at h
      | relabel j F => simp [FStep.phys] at h
    · exact valid_gates rest _ _ hv.2 g h

omit [DecidableEq ι] in
/-- The run does not depend on the decidable-equality instance. -/
theorem run_inst {P E : Type} [AddCommGroup E] [Module (ZMod 2) E] (i1 i2 : DecidableEq ι)
    (edge : P → E → E) (L : List (Step ι P)) (x : ι → E) :
    @Step.run ι P E _ _ i1 edge L x = @Step.run ι P E _ _ i2 edge L x := by
  rw [Subsingleton.elim i1 i2]

end Phys

theorem exchangeEdges_node : ExchangeEdges (physOf framedNode) := by
  intro i p h
  obtain ⟨U, rfl, hU⟩ := valid_edges framedNode gInit tempZero isFrame_gInit valid_node i p h
  exact ⟨U, rfl, hU.bound⟩

theorem card_world : Fintype.card World = 108516254 := by
  rw [Fintype.card_sum (α := V × V) (β := (V × V) ⊕ (Bool × V × Slot)),
    Fintype.card_sum (α := V × V) (β := Bool × V × Slot), card_pairs, card_sides]

theorem card_temp : Fintype.card Temp = 3217908 := by
  rw [Fintype.card_sum (α := Bool × V × Fin 23) (β := (V × V) ⊕ Unit),
    Fintype.card_sum (α := V × V) (β := Unit), card_centres, card_pairs, Fintype.card_unit]

/-- The PR97 node as a bit network, unsealed. -/
def pr97₀ : BitNetwork where
  World := World
  Temp := Temp
  roleCount := 108516254
  roleEquiv := (Fintype.equivFinOfCardEq card_world).symm
  tempCount := 3217908
  tempEquiv := (Fintype.equivFinOfCardEq card_temp).symm
  width := 529
  two_le_width := by norm_num
  prime := Shared50ModularControl.prime
  prime_prime := Shared50ModularControl.prime_prime
  prime_odd := (ne_of_lt Shared50ModularControl.prime_odd).symm
  control := physOf framedNode
  route := route
  route_involutive := route_involutive
  rankSum := calls (physOf framedNode)
  calls_exact := rfl
  legal := exchangeEdges_node.legal
  legal_mod := fun b => exchangeEdges_node.legal_mod (by norm_num) le_rfl b
  xor_gate := fun g hg => valid_gates framedNode gInit tempZero valid_node g hg
  run_identity := fun b stored hz i a => by
    rw [run_inst _ (fun x y : Wire => propDecidable (x = y))]
    exact node_run Shared50ModularControl.prime_prime Shared50ModularControl.coefficientBound_lt_prime
      b stored hz i a
  tau := Branching97.tau
  tau_pos := Branching97.tau_pos
  tau_lt_one := Branching97.tau_lt_one
  branching := Branching97.branching _ calls_node_le

/-- **The PR97 bit network**, sealed so that elaboration never unfolds its control. -/
irreducible_def pr97 : BitNetwork := pr97₀

theorem runs_pr97₀ : Machine.Runs pr97₀ :=
  ExchangeEdges.runs exchangeEdges_node le_rfl rfl (by show 529 ≤ 108516254; norm_num)

/-- **The machine runs the PR97 node.** -/
theorem runs_pr97 : Machine.Runs pr97 := pr97_def ▸ runs_pr97₀

theorem pr97_tau : pr97.tau = Branching97.tau := by
  rw [pr97_def]
  rfl

end

end IntegerMultBounds.MathlibTM2.M8.Global
