module

public import IntegerMultBounds.MathlibTM2.M8.Rev.Node

/-!
# The reversed-network interface and the stage-2 PR97 node

A `RevNetwork` is the stage-2 analogue of `BitNetwork`: a fixed list of steps on named role
streams whose edge programs run twisted on atom fields, coordinates in `Fin f → ℤ/q^b` with the
head read in reversed atom order (`Rev.twEdgeAction` at `σ = atomRev f`). Its node theorem is the
routed **reversed** interchange `(h, d) ↦ (σ(C d), σ(C h))` (`run_identity`), and the
interchanges of every edge program form one block child: they are the reversed pivots
`revPivots m r` with `r` the program's interchange count (`block`). `calls` counts the children
by rank, so the stage-2 rank histogram is the list of these counts.

`rev97` is the PR97 node in this form. Its control replaces every frame change `D_U` of the
framed node by the stage-2 edge program of `G U G⁻¹` (`Rev.revPhysOf`), for one basis `G` with
natural entries that makes every frame change generic (`GenericBasis`), and a prime beyond all
denominators of the node (`prime97`). Each edge program has `rank U` children
(`edge_interchanges`), so the total equals the stage-1 count (`calls_rev97`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Global
open IntegerMultBounds.Swap.Modular (ratMod reduce Admissible denominators admissible_of_lt)
open ReversedExchange (rev revPivots)
open TwistedExchange (twist atomRev)

/-- The scalars of the atom ring over `ℤ/q^b`. -/
abbrev atomScalar (q b f : ℕ) : ZMod (q ^ b) →+* (Fin f → ZMod (q ^ b)) := algebraMap _ _

/-- A fixed reversed interchange node with its certificates. -/
structure RevNetwork where
  World : Type
  Temp : Type
  [worldFintype : Fintype World]
  [worldDecidableEq : DecidableEq World]
  [tempFintype : Fintype Temp]
  [tempDecidableEq : DecidableEq Temp]
  roleCount : ℕ
  roleEquiv : Fin roleCount ≃ World
  tempCount : ℕ
  tempEquiv : Fin tempCount ≃ Temp
  /-- Address coordinates per field; each coordinate carries the atoms of one sub-field. -/
  width : ℕ
  two_le_width : 2 ≤ width
  prime : ℕ
  prime_prime : prime.Prime
  prime_odd : prime ≠ 2
  control : List (Step (World ⊕ Temp) (FieldProgram width))
  route : World → World
  route_involutive : Function.Involutive route
  /-- The total rank of the children. -/
  rankSum : ℕ
  calls_exact : calls control = rankSum
  /-- The reductions mod every `q^b` are legal. -/
  legal_mod : ∀ (b : ℕ) (i : World ⊕ Temp) (p : FieldProgram width), Step.edge i p ∈ control →
    ∀ op ∈ specialize (prime ^ b) p, AffineFieldProgram.Legal op
  xor_gate : ∀ g, Step.gate g ∈ control → ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src
  /-- The interchanges of every edge program form one reversed block child. -/
  block : ∀ (i : World ⊕ Temp) (p : FieldProgram width), Step.edge i p ∈ control →
    ∀ j k, AffineFieldProgram.Op.interchange j k ∈ p ↔
      (j, k) ∈ revPivots width (AffineFieldProgram.interchanges p)
  /-- **The node theorem**: at every width `b` and atom count `f`, on arbitrary stored streams of
  the contract roles and zero temporaries, contract role `i` ends with the stream of `route i`
  read at the reversed interchange of its address. -/
  run_identity : ∀ (b f : ℕ) (stored : World ⊕ Temp → Rev.Streams width (Fin f → ZMod (prime ^ b))),
    (∀ t, stored (.inr t) = 0) → ∀ (i : World) (a : Rev.Addr width (Fin f → ZMod (prime ^ b))),
      Step.run (Rev.twEdgeAction (atomScalar prime b f) (atomRev f)) control stored (.inl i) a =
        stored (.inl (route i))
          (twist (atomRev f) (Rev.revS (d := width) (atomScalar prime b f) *ᵥ a.2),
            twist (atomRev f) (Rev.revS (d := width) (atomScalar prime b f) *ᵥ a.1))

attribute [instance] RevNetwork.worldFintype RevNetwork.worldDecidableEq RevNetwork.tempFintype
  RevNetwork.tempDecidableEq

namespace Rev

variable {ι : Type} [DecidableEq ι] {d : ℕ}

omit [DecidableEq ι] in
theorem mem_revPhysOf_edge (G G' : Mat d) : ∀ (L : List (FStep ι d)) (i : ι) (p : FieldProgram d),
    Step.edge i p ∈ revPhysOf G G' L → ∃ U ∈ edgeMats L, p = revProgram (G * U * G')
  | [], _, _, h => by simp [revPhysOf] at h
  | s :: rest, i, p, h => by
    rw [revPhysOf, List.flatMap_cons, List.mem_append, ← revPhysOf] at h
    rcases h with h | h
    · cases s with
      | up j A B =>
        simp only [revStep, List.mem_singleton, Step.edge.injEq] at h
        exact ⟨B - A, by simp [edgeMats], h.2⟩
      | down j A B =>
        simp only [revStep, List.mem_singleton, Step.edge.injEq] at h
        exact ⟨A - B, by simp [edgeMats], h.2⟩
      | gate g F => simp [revStep] at h
      | reset j => simp [revStep] at h
      | relabel j F => simp [revStep] at h
    · obtain ⟨U, hU, rfl⟩ := mem_revPhysOf_edge G G' rest i p h
      refine ⟨U, ?_, rfl⟩
      cases s <;> simp only [edgeMats, List.mem_cons] <;> tauto

omit [DecidableEq ι] in
theorem mem_revPhysOf_gate (G G' : Mat d) : ∀ (L : List (FStep ι d)) (g : Circuit.Gate ι (ZMod 2)),
    Step.gate g ∈ revPhysOf G G' L → Step.gate g ∈ physOf L
  | [], _, h => by simp [revPhysOf] at h
  | s :: rest, g, h => by
    rw [revPhysOf, List.flatMap_cons, List.mem_append, ← revPhysOf] at h
    rw [physOf, List.flatMap_cons, List.mem_append, ← physOf]
    rcases h with h | h
    · left
      cases s <;> simp_all [revStep, FStep.phys]
    · exact Or.inr (mem_revPhysOf_gate G G' rest g h)

theorem rank_conj {G G' U : Mat d} (h : G * G' = 1) (h' : G' * G = 1) :
    (G * U * G').rank = U.rank := by
  have hG : IsUnit G.det := IsUnit.of_mul_eq_one _ (by rw [← det_mul, h, det_one])
  have hG' : IsUnit G'.det := IsUnit.of_mul_eq_one _ (by rw [← det_mul, h', det_one])
  rw [rank_mul_eq_left_of_isUnit_det _ _ hG', rank_mul_eq_right_of_isUnit_det _ _ hG]

omit [DecidableEq ι] in
/-- The stage-2 list has the stage-1 count of children. -/
theorem calls_revPhysOf {G G' : Mat d} (h : G * G' = 1) (h' : G' * G = 1) [DecidableEq ι] :
    ∀ L : List (FStep ι d), calls (revPhysOf G G' L) = edgeRanks L
  | [] => rfl
  | s :: rest => by
    have ih := calls_revPhysOf h h' rest
    cases s <;>
      simp [revPhysOf, calls, Step.programs, edgeRanks, revStep, revProgram_interchanges,
        rank_conj h h'] at ih ⊢ <;>
      try exact ih

end Rev

/-! ### The stage-2 PR97 node -/

open Classical

open Rev (revNumbers revProgram revProgram_interchanges revProgram_specialize_legal
  mem_revProgram_interchange)

/-- The height bound of the frame changes. -/
irreducible_def edgeBound : ℕ := 10 ^ 10000

/-- The frame changes of the PR97 framed node. -/
irreducible_def edges97 : List (Mat 529) := Rev.edgeMats framedNode

theorem edgeMat_edges97 : ∀ U ∈ edges97, EdgeMat U := by
  rw [edges97_def]
  exact Rev.edgeMat_of_valid framedNode gInit tempZero isFrame_gInit valid_node

theorem exists_basis97 :
    ∃ g : Matrix (Fin 529) (Fin 529) ℕ,
      (∀ a b, g a b ≤ GenericBasis.degreeBound 529 fun j : Fin edges97.length => (edges97.get j).rank) ∧
      (g.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ j : Fin edges97.length, GenericBasis.Generic
        (g.map (Nat.cast : ℕ → ℚ) * edges97.get j * (g.map (Nat.cast : ℕ → ℚ))⁻¹) (edges97.get j).rank := by
  obtain ⟨g, hg, hdet, hgen⟩ := GenericBasis.exists_generic_basis_of_idempotent (fun j => edges97.get j)
    (fun j => (edgeMat_edges97 _ (List.get_mem _ _)).idem)
  exact ⟨g, hg, hdet, hgen⟩

/-- The basis of the stage-2 node: every frame change generic. -/
irreducible_def basis97 : Mat 529 := (Classical.choose exists_basis97).map (Nat.cast : ℕ → ℚ)

/-- Its inverse. -/
irreducible_def basis97' : Mat 529 := basis97⁻¹

theorem basis97_det : IsUnit basis97.det := by
  rw [basis97_def]
  exact isUnit_iff_ne_zero.mpr (Classical.choose_spec exists_basis97).2.1

theorem basis97_inv : basis97 * basis97' = 1 := by
  rw [basis97'_def]; exact Matrix.mul_nonsing_inv _ basis97_det

theorem basis97_inv' : basis97' * basis97 = 1 := by
  rw [basis97'_def]; exact Matrix.nonsing_inv_mul _ basis97_det

theorem generic97 {U : Mat 529} (hU : U ∈ edges97) :
    GenericBasis.Generic (basis97 * U * basis97') (basis97 * U * basis97').rank := by
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hU
  rw [Rev.rank_conj basis97_inv basis97_inv']
  have := (Classical.choose_spec exists_basis97).2.2 j
  rwa [← basis97_def, ← basis97'_def] at this

section Generic

variable {m : ℕ}

/-- The denominators a prime must avoid for a list of frame changes in the basis `G`. -/
def nums (edges : List (Mat m)) (G G' : Mat m) : Finset ℕ :=
  ((Finset.univ : Finset (Fin edges.length)).biUnion fun j => revNumbers (G * edges.get j * G')) ∪
    denominators G' ∪ {edgeBound}

theorem edge_nums {edges : List (Mat m)} {G G' : Mat m} {q : ℕ} (hp : ∀ e ∈ nums edges G G', e < q)
    {U : Mat m} (hU : U ∈ edges) : ∀ e ∈ revNumbers (G * U * G'), e < q := by
  intro e he
  apply hp
  unfold nums
  rw [Finset.mem_union, Finset.mem_union]
  left; left
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hU
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, he⟩

theorem basis_of_nums {edges : List (Mat m)} {G G' : Mat m} {q : ℕ} (hq : q.Prime)
    (hp : ∀ e ∈ nums edges G G', e < q) (hG : ∀ i j, (G i j).den = 1) (h : G * G' = 1)
    (h' : G' * G = 1) (b : ℕ) : Rev.Basis G G' q b where
  prime := hq
  large := by
    have hb : edgeBound < q := by
      apply hp
      unfold nums
      rw [Finset.mem_union]
      exact Or.inr (Finset.mem_singleton_self _)
    rwa [edgeBound_def] at hb
  admissible := fun i j => by
    rw [hG i j]
    exact Nat.coprime_one_left _
  admissible' := admissible_of_lt hq (fun e he => hp e (by
    unfold nums
    rw [Finset.mem_union, Finset.mem_union]
    exact Or.inl (Or.inr he))) b
  inv := h
  inv' := h'

end Generic

theorem exists_prime97 : ∃ q : ℕ, q.Prime ∧ 2 < q ∧ ∀ e ∈ nums edges97 basis97 basis97', e < q :=
  Swap.Modular.exists_prime_gt _

/-- The prime of the stage-2 node. -/
def prime97 : ℕ := Classical.choose exists_prime97

theorem prime97_prime : prime97.Prime := (Classical.choose_spec exists_prime97).1

theorem basis97_den (i j : Fin 529) : (basis97 i j).den = 1 := by
  rw [basis97_def, Matrix.map_apply, Rat.den_natCast]

theorem basis97_basis (b : ℕ) : Rev.Basis basis97 basis97' prime97 b :=
  basis_of_nums prime97_prime (Classical.choose_spec exists_prime97).2.2 basis97_den basis97_inv
    basis97_inv' b

theorem edges97_numbers {U : Mat 529} (hU : U ∈ edges97) :
    ∀ e ∈ revNumbers (basis97 * U * basis97'), e < prime97 :=
  edge_nums (Classical.choose_spec exists_prime97).2.2 hU

theorem rev_admissible (b : ℕ) : Admissible (prime97 ^ b) (rev 529 : Mat 529) := fun i j => by
  have : ((rev 529 : Mat 529) i j).den = 1 := by
    simp only [rev, Matrix.of_apply]
    split_ifs <;> rfl
  rw [this]
  exact Nat.coprime_one_left _

/-- The control of the stage-2 node. -/
def control97 : List (Step Wire (FieldProgram 529)) := Rev.revPhysOf basis97 basis97' framedNode

theorem edge_interchanges {i : Wire} {p : FieldProgram 529} (h : Step.edge i p ∈ control97) :
    ∃ U ∈ edges97, p = revProgram (basis97 * U * basis97') ∧
      AffineFieldProgram.interchanges p = U.rank := by
  obtain ⟨U, hU, rfl⟩ := Rev.mem_revPhysOf_edge basis97 basis97' framedNode i p h
  exact ⟨U, by rw [edges97_def]; exact hU, rfl,
    by rw [revProgram_interchanges, Rev.rank_conj basis97_inv basis97_inv']⟩

theorem calls_rev97 : calls control97 = calls (physOf framedNode) := by
  rw [control97, Rev.calls_revPhysOf basis97_inv basis97_inv', calls_physOf]

/-- **The stage-2 PR97 node** as a reversed network. -/
def rev97 : RevNetwork where
  World := World
  Temp := Temp
  roleCount := 108516254
  roleEquiv := (Fintype.equivFinOfCardEq card_world).symm
  tempCount := 3217908
  tempEquiv := (Fintype.equivFinOfCardEq card_temp).symm
  width := 529
  two_le_width := by norm_num
  prime := prime97
  prime_prime := prime97_prime
  prime_odd := fun h => by
    have := (Classical.choose_spec exists_prime97).2.1
    rw [← prime97] at this
    omega
  control := control97
  route := route
  route_involutive := route_involutive
  rankSum := calls (physOf framedNode)
  calls_exact := calls_rev97
  legal_mod := fun b i p h => by
    obtain ⟨U, hU, rfl, -⟩ := edge_interchanges h
    exact revProgram_specialize_legal prime97_prime (edges97_numbers hU) b
  xor_gate := fun g hg =>
    valid_gates framedNode gInit tempZero valid_node g (Rev.mem_revPhysOf_gate _ _ _ g hg)
  block := fun i p h j k => by
    obtain ⟨U, hU, rfl, -⟩ := edge_interchanges h
    rw [revProgram_interchanges]
    exact mem_revProgram_interchange _ (generic97 hU) j k
  run_identity := fun b f stored hz i a => by
    rw [run_inst _ (fun x y : Wire => propDecidable (x = y))]
    exact Rev.rev_node_run (TwistedExchange.atomRev_atomRev f)
      (fun c => funext fun x => by simp) (basis97_basis b) (rev_admissible b)
      (fun U hU => edges97_numbers (by rw [edges97_def]; exact hU)) stored hz i a

end

end IntegerMultBounds.MathlibTM2.M8
