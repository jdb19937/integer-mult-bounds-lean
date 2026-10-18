module

public import IntegerMultBounds.Networks.Certificates.T16.Streams.Lift
public import IntegerMultBounds.Networks.Certificates.T16.PauliLowering

/-! Primitive operations on 73-bit arrays and the lowering of nine-bit Clifford realizations to
them. A primitive is a two-term translation kernel `kernel q v` (a child for odd `q`, a
translation for `q = 2`), an address permutation, a diagonal phase `i^φ` or a scalar. The lift of
a nine-bit permutation, diagonal gate, C gate, translation or character multiplication is the
corresponding primitive on the local coordinates, so every exact nine-bit realization lifts to a
word of primitives whose odd kernels number exactly its X-block rank. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams

/-- One primitive operation on a 73-bit array. -/
inductive Prim where
  | kernel (q : ZMod 4) (v : Addr)
  | perm (G : Addr ≃ₗ[ZMod 2] Addr)
  | diag (φ : Addr → ZMod 4)
  | scale (c : ℂ)

/-- The operator of a primitive. -/
noncomputable def Prim.op : Prim → Arrays 73 → Arrays 73
  | .kernel q v, f => BinaryWalsh.kernel q v f
  | .perm G, f => permOp G f
  | .diag φ, f => phaseDiagonal φ f
  | .scale c, f => c • f

/-- A `Z/4`-quadratic exponent on 73 bits. -/
def Quadratic (φ : Addr → ZMod 4) : Prop :=
  ∃ (k : ZMod 4) (c : Fin 73 → ZMod 4) (d : Fin 73 → Fin 73 → ZMod 4), ∀ x,
    φ x = k + ∑ i, c i * bitLift (x i) + ∑ i, ∑ j, 2 * d i j * (bitLift (x i) * bitLift (x j))

/-- A primitive the machine runs: a kernel, a permutation, a quadratic phase or a fourth-root
scalar. -/
def Prim.Ready : Prim → Prop
  | .kernel _ _ => True
  | .perm _ => True
  | .diag φ => Quadratic φ
  | .scale c => ∃ j : ZMod 4, c = phase j

/-- Whether a primitive is a child call: a kernel with an odd phase. -/
def Prim.isChild : Prim → Bool
  | .kernel q _ => q.val % 2 == 1
  | _ => false

/-- A word of primitives, applied head first. -/
noncomputable def wordOp : List Prim → Arrays 73 → Arrays 73
  | [], f => f
  | p :: ps, f => wordOp ps (p.op f)

theorem wordOp_append (ps qs : List Prim) (f : Arrays 73) :
    wordOp (ps ++ qs) f = wordOp qs (wordOp ps f) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih => exact ih _

/-- The number of child calls of a word. -/
def childCount (ps : List Prim) : ℕ := (ps.filter Prim.isChild).length

theorem childCount_append (ps qs : List Prim) :
    childCount (ps ++ qs) = childCount ps + childCount qs := by
  simp [childCount, List.filter_append]

/-! ### Lifting nine-bit operators -/

theorem joinAddr_add_add (l l' : Address 9) (h h' : Address 64) :
    joinAddr (l + l') (h + h') = joinAddr l h + joinAddr l' h' := by
  funext i
  simp only [joinAddr, Pi.add_apply]
  refine Fin.addCases (m := 9) (n := 64) (fun i => ?_) (fun j => ?_) i <;> simp

theorem joinAddr_smul (c : ZMod 2) (l : Address 9) (h : Address 64) :
    joinAddr (c • l) (c • h) = c • joinAddr l h := by
  funext i
  simp only [joinAddr, Pi.smul_apply]
  refine Fin.addCases (m := 9) (n := 64) (fun i => ?_) (fun j => ?_) i <;> simp

/-- A nine-bit address map acting on the local coordinates. -/
def liftGL (G : Address 9 ≃ₗ[ZMod 2] Address 9) : Addr ≃ₗ[ZMod 2] Addr where
  toFun x := joinAddr (G (lowPart x)) (highPart x)
  invFun x := joinAddr (G.symm (lowPart x)) (highPart x)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by
    rw [show lowPart (x + y) = lowPart x + lowPart y from rfl,
      show highPart (x + y) = highPart x + highPart y from rfl, map_add, joinAddr_add_add]
  map_smul' c x := by
    rw [show lowPart (c • x) = c • lowPart x from rfl,
      show highPart (c • x) = c • highPart x from rfl, map_smul, RingHom.id_apply, joinAddr_smul]

theorem lift9_permutation (G : Address 9 ≃ₗ[ZMod 2] Address 9) (f : Arrays 73) :
    lift9 (Pauli.permutation G).toLinearMap f = permOp (liftGL G) f := by
  funext x
  rfl

theorem lift9_phaseDiagonal (φ : Address 9 → ZMod 4) (f : Arrays 73) :
    lift9 (phaseDiagonal φ).toLinearMap f = phaseDiagonal (fun x => φ (lowPart x)) f := by
  funext x
  change phase (φ (lowPart x)) * f (joinAddr (lowPart x) (highPart x)) = _
  rw [join_parts]
  rfl

theorem lift9_smul (c : ℂ) (T : Arrays 9 →ₗ[ℂ] Arrays 9) (f : Arrays 73) :
    lift9 (c • T) f = c • lift9 T f := rfl

theorem kernel_two (v : Address 73) (f : Arrays 73) : BinaryWalsh.kernel 2 v f = translation v f := by
  funext x
  rw [kernel_apply]
  have h2 : phase 2 = -1 := by
    change Complex.I ^ 2 = -1
    rw [Complex.I_sq]
  change _ = f (x + v)
  rw [h2]
  ring

theorem lift9_translation (v : Address 9) (f : Arrays 73) :
    lift9 (translation v) f = BinaryWalsh.kernel 2 (padLow v) f := by
  rw [kernel_two]
  funext x
  change f (joinAddr (lowPart x + v) (highPart x)) = f (x + padLow v)
  conv_rhs => rw [← join_parts x]
  rw [joinAddr_add]

end IntegerMultBounds.Networks.Certificates.T16.Impl
