module

public import IntegerMultBounds.Networks.Certificates.T16.Streams.Model
public import IntegerMultBounds.Networks.BinaryWalsh
public import Mathlib.GroupTheory.NoncommPiCoprod

/-! The T16 operator interpretation of coefficient vectors. Translation kernels
`kernel q v = ((1+i^q)/2) I + ((1-i^q)/2) X_v` satisfy `kernel (a+b) v = kernel a v ∘ kernel b v`
and all commute, so a basis `B : Fin 73 → F₂^73` gives the homomorphism
`basisOp B c = ∏_k kernel (c k) (B k)` from coefficient vectors to operators on 73-bit arrays.
At coefficient one it is the source C gate `C_{B k}`. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Streams

open BinaryWalsh BinaryPhase Multiplicative

variable {h : ℕ}

theorem translation_comp (v w : Address h) :
    (translation v).comp (translation w) = translation (v + w) := by
  apply LinearMap.ext
  intro f
  funext x
  change f (x + v + w) = f (x + (v + w))
  rw [add_assoc]

theorem translation_self (v : Address h) : (translation v).comp (translation v) = LinearMap.id := by
  rw [translation_comp]
  have : v + v = 0 := by funext i; exact CharTwo.add_self_eq_zero (v i)
  rw [this]
  apply LinearMap.ext
  intro f
  funext x
  change f (x + 0) = f x
  rw [add_zero]

theorem kernel_eq (q : ZMod 4) (v : Address h) :
    kernel q v = ((1 + phase q) / 2) • (1 : Module.End ℂ (Arrays h)) +
      ((1 - phase q) / 2) • (translation v : Module.End ℂ (Arrays h)) := rfl

theorem translation_commute (v w : Address h) :
    Commute (translation v : Module.End ℂ (Arrays h)) (translation w) := by
  change (translation v).comp (translation w) = (translation w).comp (translation v)
  rw [translation_comp, translation_comp, add_comm]

theorem kernel_commute (a b : ZMod 4) (v w : Address h) : Commute (kernel a v) (kernel b w) := by
  rw [kernel_eq, kernel_eq]
  apply Commute.add_left <;> apply Commute.add_right <;>
    first
    | exact (Commute.one_left _).smul_left _ |>.smul_right _
    | exact (Commute.one_right _).smul_left _ |>.smul_right _
    | exact ((translation_commute v w).smul_left _).smul_right _

theorem kernel_add (a b : ZMod 4) (v : Address h) :
    kernel (a + b) v = kernel a v * kernel b v := by
  have hX : (translation v : Module.End ℂ (Arrays h)) * translation v = 1 := translation_self v
  rw [kernel_eq, kernel_eq, kernel_eq, phase_add]
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hX]
  rw [← sub_eq_zero]
  have e : ((1 + phase a * phase b) / 2 : ℂ) =
      (1 + phase a) / 2 * ((1 + phase b) / 2) + (1 - phase a) / 2 * ((1 - phase b) / 2) := by ring
  have e' : ((1 - phase a * phase b) / 2 : ℂ) =
      (1 + phase a) / 2 * ((1 - phase b) / 2) + (1 - phase a) / 2 * ((1 + phase b) / 2) := by ring
  rw [e, e', add_smul, add_smul]
  abel

theorem kernel_zero (v : Address h) : kernel 0 v = 1 := by
  rw [kernel_eq, phase_zero]
  norm_num

/-- One translation direction as a homomorphism from `ZMod 4`. -/
noncomputable def kernelHom (v : Address h) : Multiplicative (ZMod 4) →* Module.End ℂ (Arrays h) where
  toFun n := kernel (toAdd n) v
  map_one' := kernel_zero v
  map_mul' a b := kernel_add (toAdd a) (toAdd b) v

def splitHom : Multiplicative (Fin 73 → ZMod 4) →* (Fin 73 → Multiplicative (ZMod 4)) where
  toFun c k := ofAdd (toAdd c k)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem kernelHom_commute (B : Fin 73 → Address 73) :
    Pairwise fun i j => ∀ x y : Multiplicative (ZMod 4),
      Commute (kernelHom (B i) x) (kernelHom (B j) y) :=
  fun _ _ _ _ _ => kernel_commute _ _ _ _

/-- The operator of a coefficient vector over the basis `B`. -/
@[irreducible] noncomputable def basisOp (B : Fin 73 → Address 73) : Op (Arrays 73) :=
  (MonoidHom.noncommPiCoprod (fun k => kernelHom (B k)) (kernelHom_commute B)).comp splitHom

theorem basisOp_single (B : Fin 73 → Address 73) (k : Fin 73) (q : ZMod 4) :
    basisOp B (ofAdd (Pi.single k q)) = kernel q (B k) := by
  have e : splitHom (ofAdd (Pi.single k q) : Multiplicative (Fin 73 → ZMod 4)) =
      Pi.mulSingle k (ofAdd q) := by
    funext j
    by_cases hj : j = k
    · subst hj; simp [splitHom]
    · simp [splitHom, hj]
  rw [basisOp, MonoidHom.comp_apply, e, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

end IntegerMultBounds.Networks.Certificates.T16.Streams
