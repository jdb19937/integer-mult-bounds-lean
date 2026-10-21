module

public import IntegerMultBounds.MathlibTM2.M8.Rev.Edge
public import IntegerMultBounds.MathlibTM2.M8.Rev.FramedRing
public import IntegerMultBounds.MathlibTM2.M8.Global.Instance

/-!
# The stage-2 node

The stage-2 node replaces every frame change `D_U` of the PR97 node by the stage-2 edge program
of `G U G⁻¹` (`revStep`, `revPhysOf`), for one basis change `G` of the whole node, and runs its
edge programs twisted on atom fields (`twEdgeAction`): coefficients reduced mod `q^b`, mapped by
`φ` into a ring `S`, the head read through an involution `σ` of `S`.

With `C` the reversal of the coordinates and `Φ (h, d) = (h, σ(C d))`, every stage-2 edge acts
on addresses as `Φ ∘ D_{G U G⁻¹} ∘ Φ` (`edge_map`). Conjugation by `Φ` on every wire commutes
with gates and resets, so the stage-2 run is the conjugate of the framed run over `S` in the
reading `U ↦ G U G⁻¹` (`rev_run`, with `Interp` `conjInterp`). The framed node over any ring is
the routed transpose (`Rev.node_run_ring`), so the stage-2 node is the routed **reversed**
interchange: role `i` ends with the stream of `route i` at `(σ(C d), σ(C h))`
(`rev_node_run`). Gates and resets are those of the stage-1 node, unchanged.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Rev

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Global
open IntegerMultBounds.Swap.Modular (ratMod reduce Admissible)
open ReversedExchange (rev revExchangeOf)
open TwistedExchange (twist)

variable {ι : Type} [DecidableEq ι] {d : ℕ}

/-- The stage-2 physical steps of a framed step, for a basis change `G` with inverse `G'`. -/
def revStep (G G' : Mat d) : FStep ι d → List (Step ι (FieldProgram d))
  | .up i A B => [.edge i (revProgram (G * (B - A) * G'))]
  | .down i A B => [.edge i (revProgram (G * (A - B) * G'))]
  | .gate g _ => [.gate g]
  | .reset i => [.reset i]
  | .relabel _ _ => []

/-- The stage-2 physical list. -/
def revPhysOf (G G' : Mat d) (L : List (FStep ι d)) : List (Step ι (FieldProgram d)) :=
  L.flatMap (revStep G G')

/-- The frame changes of a framed list. -/
def edgeMats : List (FStep ι d) → List (Mat d)
  | [] => []
  | .up _ A B :: rest => (B - A) :: edgeMats rest
  | .down _ A B :: rest => (A - B) :: edgeMats rest
  | _ :: rest => edgeMats rest

/-- The frame changes of a valid list are edge matrices. -/
theorem edgeMat_of_valid : ∀ (L : List (FStep ι d)) (fr : ι → Mat d) (z : ι → Prop),
    (∀ w, IsFrame (fr w)) → Valid L fr z → ∀ U ∈ edgeMats L, EdgeMat U
  | [], _, _, _, _ => by simp [edgeMats]
  | s :: rest, fr, z, hfr, hv => by
    have ih := edgeMat_of_valid rest (s.frames fr) (s.zeros z) (frames_step s fr z hfr hv.1) hv.2
    cases s with
    | up i A B =>
      obtain ⟨hi, hB, hAB, hBA⟩ := hv.1
      intro U hU
      simp only [edgeMats, List.mem_cons] at hU
      rcases hU with rfl | hU
      · exact edgeMat_sub (hi ▸ hfr i) hB hAB hBA
      · exact ih U hU
    | down i A B =>
      obtain ⟨hi, hB, hAB, hBA⟩ := hv.1
      intro U hU
      simp only [edgeMats, List.mem_cons] at hU
      rcases hU with rfl | hU
      · exact edgeMat_sub hB (hi ▸ hfr i) hBA hAB
      · exact ih U hU
    | gate g F => exact ih
    | reset i => exact ih
    | relabel i F => exact ih

section Ring

variable {q b : ℕ} {S : Type} [CommRing S] (φ : ZMod (q ^ b) →+* S) (σ : S →+* S)

/-- The address map of an edge program, reduced, mapped to `S` and run twisted. -/
def twMap (p : FieldProgram d) : Addr d S → Addr d S :=
  TwistedProgram.twRun σ ((p.map (AffineFieldProgram.mapOp (ratMod (q ^ b)))).map
    (AffineFieldProgram.mapOp φ))

/-- The twisted edge action on streams: the entry at `a` moves to `twMap p a`. -/
def twEdgeAction (p : FieldProgram d) (x : Streams d S) : Streams d S :=
  fun a => x (Function.invFun (twMap φ σ p) a)

/-- The reversal of the coordinates over `S`. -/
def revS : Matrix (Fin d) (Fin d) S := (reduce (q ^ b) (rev d)).map φ

/-- The conjugation: the tail field reversed in coordinates and atoms. -/
def Φ (a : Addr d S) : Addr d S := (a.1, twist σ (revS φ *ᵥ a.2))

theorem revS_def : (reduce (q ^ b) (rev d)).map φ = revS φ := rfl

theorem revS_fixed {φ : ZMod (q ^ b) →+* S} {σ : S →+* S} (hφ : ∀ c, σ (φ c) = φ c) :
    TwistedExchange.Fixed σ (revS (d := d) φ) := by
  ext i j
  simp only [Matrix.map_apply, revS, hφ]

variable {φ σ} (hσ : ∀ x, σ (σ x) = x) (hφ : ∀ c, σ (φ c) = φ c)

theorem revS_mul (hrev : Admissible (q ^ b) (rev d : Mat d)) :
    revS (d := d) φ * revS φ = 1 := by
  rw [revS, ← Matrix.map_mul, ← Swap.Modular.reduce_mul _ hrev hrev, ReversedExchange.rev_mul_rev,
    Swap.Modular.reduce_one, Matrix.map_one φ (map_zero φ) (map_one φ)]

include hσ hφ

theorem Φ_involutive (hrev : Admissible (q ^ b) (rev d : Mat d)) :
    Function.Involutive (Φ (d := d) φ σ) := by
  intro a
  simp only [Φ]
  rw [← TwistedExchange.twist_mulVec (revS_fixed hφ), TwistedExchange.twist_twist hσ,
    mulVec_mulVec, revS_mul hrev, one_mulVec]

/-- **The edge map.** The twisted map of the stage-2 edge program of an idempotent `P` is
`Φ ∘ D_P ∘ Φ`, with `P` reduced and mapped to `S`. -/
theorem edge_map {P : Mat d} (hP : P * P = P) (hq : q.Prime) (hd : ∀ d ∈ revNumbers P, d < q)
    (a : Addr d S) :
    twMap φ σ (revProgram P) a = Φ φ σ (Exchange.exchange ((reduce (q ^ b) P).map φ) (Φ φ σ a)) := by
  rw [twMap, revProgram_twRun φ hP hq hd hσ hφ, revS_def]
  simp only [revExchangeOf, Exchange.transform, TwistedExchange.conj, one_mulVec, Φ,
    TwistedExchange.twist_mulVec (revS_fixed (d := d) hφ)]

omit hσ hφ in
theorem edgeMat_admissible {U : Mat d} (hU : EdgeMat U) (hq : q.Prime) (h : 10 ^ 10000 < q) :
    Admissible (q ^ b) U := fun i j =>
  Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hq).mpr
    (Nat.not_dvd_of_pos_of_lt (U i j).den_pos (lt_of_le_of_lt (hU.bound i j).2 h))))

omit hσ hφ in
theorem frame_admissible' {U : Mat d} (hU : IsFrame U) (hq : q.Prime) (h : 10 ^ 10000 < q) :
    Admissible (q ^ b) U :=
  admissible_of_bounded hU.bound hq (lt_of_le_of_lt (pow_le_pow_right₀ (by norm_num) (by norm_num)) h) b

/-- The hypotheses on the basis change `G` with inverse `G'` and the prime. -/
structure Basis (G G' : Mat d) (q b : ℕ) : Prop where
  prime : q.Prime
  large : 10 ^ 10000 < q
  admissible : Admissible (q ^ b) G
  admissible' : Admissible (q ^ b) G'
  inv : G * G' = 1
  inv' : G' * G = 1

omit hσ hφ in
theorem Basis.mapInv {G G' : Mat d} (hB : Basis G G' q b) :
    (reduce (q ^ b) G).map φ * (reduce (q ^ b) G').map φ = 1 := by
  rw [← Matrix.map_mul, ← Swap.Modular.reduce_mul _ hB.admissible hB.admissible', hB.inv,
    Swap.Modular.reduce_one, Matrix.map_one φ (map_zero φ) (map_one φ)]

omit hσ hφ in
theorem Basis.mapInv' {G G' : Mat d} (hB : Basis G G' q b) :
    (reduce (q ^ b) G').map φ * (reduce (q ^ b) G).map φ = 1 := by
  rw [← Matrix.map_mul, ← Swap.Modular.reduce_mul _ hB.admissible' hB.admissible, hB.inv',
    Swap.Modular.reduce_one, Matrix.map_one φ (map_zero φ) (map_one φ)]

omit hσ hφ in
/-- The frames read in the basis `G`, reduced and mapped to `S`. -/
def conjInterp {G G' : Mat d} (hB : Basis G G' q b) : Interp d S where
  ρ U := (reduce (q ^ b) G).map φ * (reduce (q ^ b) U).map φ * (reduce (q ^ b) G').map φ
  mul {A B} hA hB' := by
    rw [Swap.Modular.reduce_mul _ (frame_admissible' hA hB.prime hB.large)
      (frame_admissible' hB' hB.prime hB.large), Matrix.map_mul]
    calc (reduce (q ^ b) G).map φ * ((reduce (q ^ b) A).map φ * (reduce (q ^ b) B).map φ) *
          (reduce (q ^ b) G').map φ =
        (reduce (q ^ b) G).map φ * (reduce (q ^ b) A).map φ *
          ((reduce (q ^ b) G').map φ * (reduce (q ^ b) G).map φ) * (reduce (q ^ b) B).map φ *
          (reduce (q ^ b) G').map φ := by rw [hB.mapInv']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  sub {A B} hA hB' := by
    rw [Global.reduce_sub _ (frame_admissible' hB' hB.prime hB.large)
      (frame_admissible' hA hB.prime hB.large), Matrix.map_sub _ (map_sub φ), Matrix.mul_sub,
      Matrix.sub_mul]
  one := by
    rw [Swap.Modular.reduce_one, Matrix.map_one φ (map_zero φ) (map_one φ), Matrix.mul_one,
      hB.mapInv]
  zero := by
    rw [show reduce (q ^ b) (0 : Mat d) = 0 by ext i j; simp [reduce, Swap.Modular.ratMod_zero],
      Matrix.map_zero φ (map_zero φ), Matrix.mul_zero, Matrix.zero_mul]

omit hσ hφ in
theorem conjInterp_reduce {G G' : Mat d} (hB : Basis G G' q b) {U : Mat d} (hU : EdgeMat U) :
    (reduce (q ^ b) (G * U * G')).map φ = (conjInterp (φ := φ) hB).ρ U := by
  have hUa := edgeMat_admissible hU hB.prime hB.large (b := b)
  rw [Swap.Modular.reduce_mul _ (Swap.Modular.admissible_mul _ hB.admissible hUa) hB.admissible',
    Swap.Modular.reduce_mul _ hB.admissible hUa, Matrix.map_mul, Matrix.map_mul]
  rfl

omit hσ hφ in
theorem conj_idem {G G' : Mat d} (hB : Basis G G' q b) {U : Mat d} (hU : U * U = U) :
    G * U * G' * (G * U * G') = G * U * G' := by
  calc G * U * G' * (G * U * G') = G * U * (G' * G) * U * G' := by simp only [Matrix.mul_assoc]
    _ = G * U * G' := by rw [hB.inv', Matrix.mul_one, Matrix.mul_assoc G U U, hU]

/-- Every wire read through `Φ`. -/
def cΦ (φ : ZMod (q ^ b) →+* S) (σ : S →+* S) {ι : Type} (x : ι → Streams d S) : ι → Streams d S :=
  fun w a => x w (Φ φ σ a)

/-- **One stage-2 edge.** The twisted edge action of the stage-2 program of `G U G'`, read through
`Φ`, is the frame change `D_U` over `S` in the reading `conjInterp`. -/
theorem twEdgeAction_edge {G G' : Mat d} (hB : Basis G G' q b) (hrev : Admissible (q ^ b) (rev d : Mat d))
    {U : Mat d} (hU : EdgeMat U) (hd : ∀ d ∈ revNumbers (G * U * G'), d < q) (x : Streams d S)
    (a : Addr d S) :
    twEdgeAction φ σ (revProgram (G * U * G')) x (Φ φ σ a) = x (Φ φ σ ((conjInterp (φ := φ) hB).swap U a)) := by
  have hP := conj_idem hB hU.idem
  have hE : Function.Involutive (Exchange.exchange ((reduce (q ^ b) (G * U * G')).map φ)) := by
    have hPa : Admissible (q ^ b) (G * U * G') := Swap.Modular.admissible_mul _
      (Swap.Modular.admissible_mul _ hB.admissible (edgeMat_admissible hU hB.prime hB.large)) hB.admissible'
    refine exchange_involutive ?_
    rw [← Matrix.map_mul, ← Swap.Modular.reduce_mul _ hPa hPa, hP]
  have hM : Function.Involutive (twMap φ σ (revProgram (G * U * G'))) := by
    intro c
    rw [edge_map hσ hφ hP hB.prime hd, edge_map hσ hφ hP hB.prime hd,
      Φ_involutive hσ hφ hrev, hE, Φ_involutive hσ hφ hrev]
  have hinv : Function.invFun (twMap φ σ (revProgram (G * U * G'))) (Φ φ σ a) =
      twMap φ σ (revProgram (G * U * G')) (Φ φ σ a) := by
    have := Function.leftInverse_invFun hM.injective (twMap φ σ (revProgram (G * U * G')) (Φ φ σ a))
    rwa [hM] at this
  rw [twEdgeAction, hinv, edge_map hσ hφ hP hB.prime hd, Φ_involutive hσ hφ hrev,
    conjInterp_reduce hB hU]
  rfl

omit hσ hφ in
theorem cΦ_gate {ι : Type} [DecidableEq ι] (g : Circuit.Gate ι (ZMod 2)) (x : ι → Streams d S) :
    cΦ φ σ (FramedCircuit.moduleGate g x) = FramedCircuit.moduleGate g (cΦ φ σ x) := by
  funext w a
  simp only [cΦ, FramedCircuit.moduleGate]
  by_cases hw : w = g.target
  · subst hw
    simp only [Function.update_self, Pi.add_apply, Pi.list_sum_apply, List.map_map,
      Function.comp_def, Pi.smul_apply]
    rfl
  · simp only [Function.update_of_ne hw]; rfl

/-- **The conjugated run.** Read through `Φ`, the stage-2 run of a framed list is its framed run
over `S` in the reading `conjInterp`. -/
theorem rev_run {G G' : Mat d} (hB : Basis G G' q b) (hrev : Admissible (q ^ b) (rev d : Mat d)) :
    ∀ (L : List (FStep ι d)), (∀ U ∈ edgeMats L, EdgeMat U ∧ ∀ e ∈ revNumbers (G * U * G'), e < q) →
    ∀ x : ι → Streams d S,
      cΦ φ σ (Step.run (twEdgeAction φ σ) (revPhysOf G G' L) x) = frun (conjInterp (φ := φ) hB) L (cΦ φ σ x)
  | [], _, _ => rfl
  | s :: rest, hL, x => by
    have hrest : ∀ U ∈ edgeMats rest, EdgeMat U ∧ ∀ e ∈ revNumbers (G * U * G'), e < q := by
      intro U hU
      apply hL
      cases s <;> simp only [edgeMats, List.mem_cons] <;> tauto
    rw [revPhysOf, List.flatMap_cons, Global.Step.run_append, ← revPhysOf, rev_run hB hrev rest hrest]
    change frun _ rest _ = frun _ rest _
    congr 1
    cases s with
    | up i A B =>
      have h := hL (B - A) (by simp [edgeMats])
      funext w a
      simp only [revStep, Step.run, Step.execute, cΦ, fstep]
      by_cases hw : w = i
      · subst hw
        simp only [Function.update_self]
        exact twEdgeAction_edge hσ hφ hB hrev h.1 h.2 (x w) a
      · simp only [Function.update_of_ne hw]; rfl
    | down i A B =>
      have h := hL (A - B) (by simp [edgeMats])
      funext w a
      simp only [revStep, Step.run, Step.execute, cΦ, fstep]
      by_cases hw : w = i
      · subst hw
        simp only [Function.update_self]
        exact twEdgeAction_edge hσ hφ hB hrev h.1 h.2 (x w) a
      · simp only [Function.update_of_ne hw]; rfl
    | gate g F =>
      simp only [revStep, Step.run, Step.execute, fstep]
      exact cΦ_gate g x
    | reset i =>
      funext w a
      simp only [revStep, Step.run, Step.execute, cΦ, fstep]
      by_cases hw : w = i
      · subst hw; simp
      · simp only [Function.update_of_ne hw]; rfl
    | relabel i F => rfl

open Classical in
/-- **The stage-2 node.** On arbitrary stored streams of the contract roles and zero
temporaries, every contract role ends with the stream of its route, read at the reversed
interchange of its address: `(h, d) ↦ (σ(C d), σ(C h))`. -/
theorem rev_node_run {G G' : Mat 529} (hB : Basis G G' q b)
    (hrev : Admissible (q ^ b) (rev 529 : Mat 529))
    (hedge : ∀ U ∈ edgeMats framedNode, ∀ e ∈ revNumbers (G * U * G'), e < q)
    (stored : Wire → Streams 529 S) (hz : ∀ t, stored (.inr t) = 0) (i : World) (a : Addr 529 S) :
    Step.run (twEdgeAction φ σ) (revPhysOf G G' framedNode) stored (.inl i) a =
      stored (.inl (route i)) (twist σ (revS φ *ᵥ a.2), twist σ (revS φ *ᵥ a.1)) := by
  have hL : ∀ U ∈ edgeMats framedNode, EdgeMat U ∧ ∀ e ∈ revNumbers (G * U * G'), e < q :=
    fun U hU => ⟨edgeMat_of_valid framedNode gInit tempZero isFrame_gInit valid_node U hU, hedge U hU⟩
  have h := congrFun (congrFun (rev_run hσ hφ hB hrev framedNode hL stored) (.inl i)) (Φ φ σ a)
  simp only [cΦ, Φ_involutive hσ hφ hrev a] at h
  rw [h, node_run_ring (conjInterp (φ := φ) hB) _ (fun t => by funext c; simp [cΦ, hz t])]
  simp only [cΦ, Φ]

end Ring

end

end IntegerMultBounds.MathlibTM2.M8.Rev
