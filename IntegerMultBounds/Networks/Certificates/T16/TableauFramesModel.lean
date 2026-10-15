module

public import IntegerMultBounds.Networks.Certificates.T16.TableauCertificate

/-! Small checked binary matrix witnesses for source basis extensions. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Tableau
open Geometry

structure MatrixWitness where
  columns : Fin 9 → Mask
  dual : Fin 9 → Mask

def MatrixWitness.DualCheck (m : MatrixWitness) : Prop :=
  ∀ i j, dot (decode (m.dual i)) (decode (m.columns j)) = if i = j then 1 else 0

instance (m : MatrixWitness) : Decidable m.DualCheck := inferInstanceAs
  (Decidable (∀ i j, dot (decode (m.dual i)) (decode (m.columns j)) = if i = j then 1 else 0))

noncomputable def MatrixWitness.forward (m : MatrixWitness) : Address →ₗ[F] Address :=
  (Pi.basisFun F (Fin 9)).constr F (fun i => decode (m.columns i))

def MatrixWitness.backward (m : MatrixWitness) : Address →ₗ[F] Address :=
  LinearMap.pi (fun i => dot (decode (m.dual i)))

theorem MatrixWitness.left_inverse (m : MatrixWitness) (h : m.DualCheck) :
    m.backward.comp m.forward = LinearMap.id := by
  apply (Pi.basisFun F (Fin 9)).ext
  intro j
  ext i
  change dot (decode (m.dual i)) (m.forward ((Pi.basisFun F (Fin 9)) j)) =
    ((Pi.basisFun F (Fin 9)) j) i
  rw [MatrixWitness.forward, Module.Basis.constr_basis, h i j, Pi.basisFun_apply]
  simp [Pi.single_apply, eq_comm]

theorem MatrixWitness.injective (m : MatrixWitness) (h : m.DualCheck) :
    Function.Injective m.forward := by
  apply Function.LeftInverse.injective (g := m.backward)
  intro x
  exact LinearMap.congr_fun (m.left_inverse h) x

noncomputable def MatrixWitness.equiv (m : MatrixWitness) (h : m.DualCheck) :
    Address ≃ₗ[F] Address := LinearEquiv.ofInjectiveEndo m.forward (m.injective h)

theorem MatrixWitness.equiv_column (m : MatrixWitness) (h : m.DualCheck) (i : Fin 9) :
    m.equiv h (Pi.single i 1) = decode (m.columns i) := by
  change m.forward (Pi.single i 1) = _
  rw [← Pi.basisFun_apply F (Fin 9) i]
  exact (Pi.basisFun F (Fin 9)).constr_basis F _ i

def MatrixWitness.Retains (m : MatrixWitness) (f : Frame) (hr : f.rank ≤ 9) : Prop :=
  ∀ i, m.columns (Fin.castLE hr i) = f.masks i

instance (m : MatrixWitness) (f : Frame) (hr : f.rank ≤ 9) : Decidable (m.Retains f hr) :=
  inferInstanceAs (Decidable (∀ i, m.columns (Fin.castLE hr i) = f.masks i))

noncomputable def MatrixWitness.extension (m : MatrixWitness) (h : m.DualCheck)
    (f : Frame) (hr : f.rank ≤ 9) (hc : m.Retains f hr) : FrameExtension f where
  rank_le := hr
  matrix := m.equiv h
  columns i := by rw [m.equiv_column h, hc i]; rfl

end IntegerMultBounds.Networks.Certificates.T16.Tableau
