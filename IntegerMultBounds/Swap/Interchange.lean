module

public import IntegerMultBounds.Swap.Modular
public import IntegerMultBounds.Swap.Recurrence
public import IntegerMultBounds.Networks.ShearFrame
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The mathematics of the power-width interchange (§4, Proposition 4.3). Two
address chunks `H`, `D` are interchanged by `D ← D - H`, `H ← H + D`,
`D ← H - D`, where only the middle shear uses the circuit. On every role stream
an edge between frame labels `M_tail`, `M_head` applies the address shear by
`M_head - M_tail`, which the field programs of `Shear` realize modulo `q^b`
with exactly `rank (M_head - M_tail)` recursive interchanges; the finite shear
contract makes the routed output of the framed circuit the full shear on every
wire. The recursion `time (k+1) V ≤ s · time k (V / W) + C V` with
`s / W ≤ m^τ` gives time `O(V (m^k)^τ)`. The role-stream split, the
depth-first tape schedule, and descriptor processing are tape obligations. -/

@[expose] public section

namespace IntegerMultBounds.Swap.Interchange

open Matrix
open IntegerMultBounds.Swap.Shear (Op State run interchanges shearProgram)
open IntegerMultBounds.Swap.Modular (reduce)
open IntegerMultBounds.Networks.ShearFrame (address frame frame_change full_shear)
open IntegerMultBounds.Networks.FramedCircuit

section ThreeSteps
variable {ι R : Type*} [CommRing R]

/-- `D ← D - H`: the later group updated by the earlier one. -/
def subH (s : State ι R) : State ι R := (s.1, s.2 - s.1)

/-- `H ← H + D`: the shear by the identity matrix, realized by the circuit. -/
def addD (s : State ι R) : State ι R := (s.1 + s.2, s.2)

/-- `D ← H - D`. -/
def subD (s : State ι R) : State ι R := (s.1, s.1 - s.2)

/-- The three steps interchange the two groups. -/
theorem full_interchange (s : State ι R) : subD (addD (subH s)) = (s.2, s.1) := by
  simp only [subH, addD, subD, Prod.mk.injEq]
  constructor <;> abel

end ThreeSteps

section AddressShear
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The field programs realize the address permutation `address` of the
manuscript's `Φ_M`, with `M` the reduction of the rational matrix. -/
theorem run_eq_address {m : ℕ} (A : Matrix ι ι ℚ) (E₁ E₁' E₂ E₂' : Matrix ι ι (ZMod m))
    (L : List (ι × ι)) (hrun : ∀ s, run (shearProgram E₁ E₁' E₂ E₂' L) s =
      (s.1 + reduce m A *ᵥ s.2, s.2)) (s : State ι (ZMod m)) :
    run (shearProgram E₁ E₁' E₂ E₂' L) s = address (Matrix.toLin' (reduce m A)) s := by
  rw [hrun]
  simp [address, Matrix.toLin'_apply]

/-- Lemma 4.2 as an address permutation: modulo every power of a suitable prime,
every matrix of a finite collection has a field program realizing its address
shear with exactly `rank A` interchanges. -/
theorem exists_prime_address (𝒜 : Finset (Matrix ι ι ℚ)) :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ ∀ A ∈ 𝒜, ∀ b : ℕ, ∃ p : List (Op ι (ZMod (q ^ b))),
      interchanges p = A.rank ∧
      ∀ s, run p s = address (Matrix.toLin' (reduce (q ^ b) A)) s := by
  obtain ⟨q, hq, h2, h⟩ := Modular.exists_prime_shear 𝒜
  refine ⟨q, hq, h2, ?_⟩
  intro A hA b
  obtain ⟨E₁, E₁', E₂, E₂', L, -, -, -, -, hcount, hrun⟩ := h A hA b
  exact ⟨shearProgram E₁ E₁' E₂ E₂' L, hcount, run_eq_address A E₁ E₁' E₂ E₂' L hrun⟩

/-- A schedule of edges, each labeled by its tail and head matrices, is realized
edge by edge with total interchange count the sum of the edge ranks. -/
theorem exists_prime_schedule (es : List (Matrix ι ι ℚ × Matrix ι ι ℚ)) :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ ∀ b : ℕ, ∃ ps : List (List (Op ι (ZMod (q ^ b)))),
      List.Forall₂ (fun e p => interchanges p = (e.2 - e.1).rank ∧
        ∀ s, run p s = address (Matrix.toLin' (reduce (q ^ b) (e.2 - e.1))) s) es ps ∧
      (ps.map interchanges).sum = (es.map fun e => (e.2 - e.1).rank).sum := by
  obtain ⟨q, hq, h2, h⟩ := exists_prime_address (es.map fun e => e.2 - e.1).toFinset
  refine ⟨q, hq, h2, ?_⟩
  intro b
  have hmem : ∀ e ∈ es, e.2 - e.1 ∈ (es.map fun e => e.2 - e.1).toFinset := by
    intro e he
    rw [List.mem_toFinset]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have key : ∀ es' : List (Matrix ι ι ℚ × Matrix ι ι ℚ), (∀ e ∈ es', e ∈ es) →
      ∃ ps : List (List (Op ι (ZMod (q ^ b)))),
        List.Forall₂ (fun e p => interchanges p = (e.2 - e.1).rank ∧
          ∀ s, run p s = address (Matrix.toLin' (reduce (q ^ b) (e.2 - e.1))) s) es' ps := by
    intro es'
    induction es' with
    | nil => intro _; exact ⟨[], List.Forall₂.nil⟩
    | cons e rest ih =>
      intro hsub
      obtain ⟨ps, hps⟩ := ih fun e' he' => hsub e' (List.mem_cons_of_mem _ he')
      obtain ⟨p, hp⟩ := h _ (hmem e (hsub e (List.mem_cons_self))) b
      exact ⟨p :: ps, List.Forall₂.cons hp hps⟩
  obtain ⟨ps, hps⟩ := key es fun _ he => he
  refine ⟨ps, hps, ?_⟩
  clear key hmem h
  induction hps with
  | nil => rfl
  | cons hp _ ih =>
    simp only [List.map_cons, List.sum_cons, ih, hp.1]

end AddressShear

section Frames
variable {ι K E R : Type*} [DecidableEq ι] [CommRing K] [AddCommGroup E] [Module K E]
  [CommRing R]

/-- Each edge between frame labels applies the address shear by the matrix
difference, on every wire it touches. -/
theorem edge_apply (Mold Mnew : E →ₗ[K] E) (f : (E × E) → R) :
    frame Mnew ((frame Mold).symm f) = frame (Mnew - Mold) f := frame_change Mold Mnew f

end Frames

section Cost

end Cost

end IntegerMultBounds.Swap.Interchange
