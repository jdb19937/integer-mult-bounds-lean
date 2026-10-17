module

public import IntegerMultBounds.Networks.Certificates.T16.PauliSchur

/-! Realizations with the same binary tableau differ by a Pauli operator and a global scalar.
Label maps of realizations are multiplicative because Pauli operators determine their labels;
generator squares then force equal phases modulo two, and conjugation by a suitable Pauli
operator repairs the remaining signs. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Pauli
open Geometry BinaryPhase BinaryWalsh

theorem Label.ext' {p q : Label} (hx : p.x = q.x) (hz : p.z = q.z) (hp : p.phase = q.phase) :
    p = q := by
  cases p; cases q
  simp only at hx hz hp
  subst hx hz hp
  rfl

theorem address_add_eq_zero {y x : Geometry.Address} : y + x = 0 ↔ y = x := by
  constructor
  · intro h
    calc y = y + x + x := by rw [add_assoc, Tableau.address_add_self, add_zero]
      _ = x := by rw [h, zero_add]
  · intro h
    rw [h, Tableau.address_add_self]

theorem phase_ne_zero (q : ZMod 4) : BinaryPhase.phase q ≠ 0 := by
  intro h
  have := phase_neg_mul q
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem phase_injective : Function.Injective BinaryPhase.phase := by
  intro a b h
  have h1 : BinaryPhase.phase (a - b) = 1 := by
    have e : BinaryPhase.phase (a - b) * BinaryPhase.phase b = BinaryPhase.phase a := by
      rw [← phase_add, sub_add_cancel]
    rw [h] at e
    have hb := phase_ne_zero b
    calc BinaryPhase.phase (a - b) = BinaryPhase.phase (a - b) * BinaryPhase.phase b /
          BinaryPhase.phase b := by field_simp
      _ = 1 := by rw [e, div_self hb]
  have key : ∀ d : ZMod 4, BinaryPhase.phase d = 1 → d = 0 := by
    intro d hd
    fin_cases d
    · rfl
    · exfalso
      change Complex.I ^ 1 = 1 at hd
      rw [pow_one] at hd
      have := congrArg Complex.im hd
      simp at this
    · exfalso
      change Complex.I ^ 2 = 1 at hd
      rw [Complex.I_sq] at hd
      norm_num at hd
    · exfalso
      change Complex.I ^ 3 = 1 at hd
      rw [pow_succ, Complex.I_sq] at hd
      have := congrArg Complex.im hd
      simp at this
  exact sub_eq_zero.mp (key _ h1)

theorem operator_basisState (p : Label) (a : Geometry.Address) :
    operator p (basisState a) (a + p.x) = BinaryPhase.phase p.phase * chi p.z a := by
  rw [operator_apply, add_assoc, Tableau.address_add_self, add_zero]
  simp [basisState]

theorem operator_basisState_of_ne (p : Label) {a y : Geometry.Address} (h : y ≠ a + p.x) :
    operator p (basisState a) y = 0 := by
  rw [operator_apply]
  have : y + p.x ≠ a := by
    intro e
    apply h
    rw [← e, add_assoc, Tableau.address_add_self, add_zero]
  simp [basisState, this]

theorem chi_single (z : Geometry.Address) (i : Fin 9) : chi z (Pi.single i 1) = sign (z i) := by
  rw [chi, show Labels.binary 9 = Tableau.dot from rfl, Tableau.dot_symm, dot_single]

/-- A Pauli operator determines its label, including the phase. -/
theorem operator_injective {p q : Label} (h : operator p = operator q) : p = q := by
  have hval : ∀ a y, operator p (basisState a) y = operator q (basisState a) y :=
    fun a y => by rw [h]
  have hx : p.x = q.x := by
    by_contra hne
    have h1 := hval 0 (0 + p.x)
    rw [operator_basisState, operator_basisState_of_ne q (by simpa using hne), chi_zero_right,
      mul_one] at h1
    exact phase_ne_zero _ h1
  have hpz : ∀ a, BinaryPhase.phase p.phase * chi p.z a =
      BinaryPhase.phase q.phase * chi q.z a := by
    intro a
    have h1 := hval a (a + p.x)
    rw [operator_basisState, hx, operator_basisState] at h1
    exact h1
  have hph : p.phase = q.phase := by
    have h0 := hpz 0
    simp only [chi_zero_right, mul_one] at h0
    exact phase_injective h0
  have hz : p.z = q.z := by
    funext i
    have h1 := hpz (Pi.single i 1)
    rw [hph, chi_single, chi_single] at h1
    exact sign_injective _ _ (mul_left_cancel₀ (phase_ne_zero _) h1)
  exact Label.ext' hx hz hph

/-- The identity label. -/
def Label.one : Label := ⟨0, 0, 0⟩

theorem operator_one (f : State) : operator Label.one f = f := by
  funext y
  rw [operator_apply]
  simp [Label.one]

/-! ### Label maps are multiplicative -/

theorem Realization.label_multiply (A : Realization) (p q : Label) :
    A.label (multiply p q) = multiply (A.label p) (A.label q) := by
  apply operator_injective
  apply LinearMap.ext
  intro f
  rw [← A.conjugates, ← operator_multiply, ← operator_multiply, ← A.conjugates q, ← A.conjugates p,
    LinearEquiv.symm_apply_apply]

theorem Realization.label_one (A : Realization) : A.label Label.one = Label.one := by
  apply operator_injective
  apply LinearMap.ext
  intro f
  rw [← A.conjugates, operator_one, operator_one, LinearEquiv.apply_symm_apply]

theorem multiply_xGenerator_self (i : Fin 9) :
    multiply (xGenerator i) (xGenerator i) = Label.one := by
  apply Label.ext'
  · exact Tableau.address_add_self _
  · simp [multiply, xGenerator, Label.one]
  · simp [multiply, xGenerator, Label.one]

theorem multiply_zGenerator_self (i : Fin 9) :
    multiply (zGenerator i) (zGenerator i) = Label.one := by
  apply Label.ext'
  · simp [multiply, zGenerator, Label.one]
  · exact Tableau.address_add_self _
  · simp [multiply, zGenerator, Label.one]

/-- An involutive label has phase determined modulo two by its binary part. -/
theorem two_phase_of_square {l : Label} (h : multiply l l = Label.one) :
    2 * l.phase + doubleLift (Tableau.dot l.z l.x) = 0 := by
  have := congrArg Label.phase h
  simp only [multiply, Label.one] at this
  rw [two_mul]
  exact this

theorem eq_add_doubleLift_of_two_mul {a b : ZMod 4} (h : 2 * a = 2 * b) :
    ∃ s : F, a = b + doubleLift s := by
  revert a b
  decide

/-! ### Conjugation by a Pauli operator -/

/-- Conjugation by `c` adds twice the symplectic pairing to the phase. -/
def pauliLabel (c p : Label) : Label :=
  ⟨p.x, p.z, p.phase + doubleLift (Tableau.dot c.z p.x + Tableau.dot p.z c.x)⟩

/-- The inverse label of `c`. -/
def Label.inv (c : Label) : Label := ⟨c.x, c.z, -c.phase - doubleLift (Tableau.dot c.z c.x)⟩

theorem multiply_inv_self (c : Label) : multiply c.inv c = Label.one := by
  apply Label.ext'
  · exact Tableau.address_add_self _
  · exact Tableau.address_add_self _
  · simp only [multiply, Label.inv, Label.one]
    ring

theorem multiply_self_inv (c : Label) : multiply c c.inv = Label.one := by
  apply Label.ext'
  · exact Tableau.address_add_self _
  · exact Tableau.address_add_self _
  · simp only [multiply, Label.inv, Label.one]
    ring

/-- The Pauli operator of `c` as an equivalence. -/
noncomputable def pauliEquiv (c : Label) : State ≃ₗ[ℂ] State :=
  { operator c with
    invFun := operator c.inv
    left_inv := fun f => by
      change operator c.inv (operator c f) = f
      rw [operator_multiply, multiply_inv_self, operator_one]
    right_inv := fun f => by
      change operator c (operator c.inv f) = f
      rw [operator_multiply, multiply_self_inv, operator_one] }

theorem pauliEquiv_apply (c : Label) (f : State) : pauliEquiv c f = operator c f := rfl

theorem multiply_conjugate (c p : Label) :
    multiply (multiply c p) c.inv = pauliLabel c p := by
  apply Label.ext'
  · change c.x + p.x + c.x = p.x
    rw [add_comm c.x, add_assoc, Tableau.address_add_self, add_zero]
  · change c.z + p.z + c.z = p.z
    rw [add_comm c.z, add_assoc, Tableau.address_add_self, add_zero]
  · simp only [multiply, Label.inv, pauliLabel, map_add, LinearMap.add_apply]
    ring

noncomputable def pauliRealization (c : Label) : Realization where
  scalar := pauliEquiv c
  label := pauliLabel c
  binary := LinearEquiv.refl F PhaseAddress
  projects _ := rfl
  conjugates p f := by
    change operator c (operator p (operator c.inv f)) = _
    rw [operator_multiply, operator_multiply, multiply_conjugate]

/-! ### The correction theorem -/

/-- The symplectic pairing against a fixed Pauli, as a linear functional. -/
def pairing (c : Label) : PhaseAddress →ₗ[F] F :=
  (Tableau.dot c.z).comp (LinearMap.fst F _ _) +
    (Tableau.dot c.x).comp (LinearMap.snd F _ _)

theorem pairing_apply (c : Label) (v : PhaseAddress) :
    pairing c v = Tableau.dot c.z v.1 + Tableau.dot v.2 c.x := by
  simp [pairing, Tableau.dot_symm c.x]

/-- Every linear functional is a symplectic pairing. -/
theorem exists_pairing (φ : PhaseAddress →ₗ[F] F) : ∃ c : Label, ∀ v, pairing c v = φ v := by
  refine ⟨⟨fun i => φ (0, Pi.single i 1), fun i => φ (Pi.single i 1, 0), 0⟩, fun v => ?_⟩
  have hx : ∀ x : Geometry.Address, φ (x, 0) =
      Tableau.dot (fun i => φ (Pi.single i 1, 0)) x := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [show ((∑ i, Pi.single i (x i), (0 : Geometry.Address)) : PhaseAddress) =
      ∑ i, x i • ((Pi.single i 1, 0) : PhaseAddress) by
        ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Pi.single_apply]]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    simp [Tableau.dot, Labels.binary, Labels.form_apply, mul_comm]
  have hz : ∀ z : Geometry.Address, φ (0, z) =
      Tableau.dot (fun i => φ (0, Pi.single i 1)) z := by
    intro z
    conv_lhs => rw [← Finset.univ_sum_single z]
    rw [show (((0 : Geometry.Address), ∑ i, Pi.single i (z i)) : PhaseAddress) =
      ∑ i, z i • (((0 : Geometry.Address), Pi.single i 1) : PhaseAddress) by
        ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Pi.single_apply]]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    simp [Tableau.dot, Labels.binary, Labels.form_apply, mul_comm]
  have hv : φ v = φ (v.1, 0) + φ (0, v.2) := by
    rw [← map_add]
    simp
  rw [pairing_apply, hv, hx, hz, Tableau.dot_symm v.2]

/-- **Pauli correction.** Realizations with the same binary tableau differ by a Pauli operator
followed by a global scalar. -/
theorem Realization.eq_pauli_smul (A B : Realization) (h : ∀ p, A.binary p = B.binary p) :
    ∃ c : Label, ∃ κ : ℂ, ∀ f, A.scalar f = κ • operator c (B.scalar f) := by
  -- generator labels share their binary part
  have hbin : ∀ g, (A.label g).binary = (B.label g).binary := by
    intro g
    rw [A.projects, B.projects, h]
  have hxz : ∀ g, (A.label g).x = (B.label g).x ∧ (A.label g).z = (B.label g).z := by
    intro g
    have := hbin g
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  -- their phases agree modulo two
  have hsq : ∀ g, multiply g g = Label.one → ∃ s : F,
      (A.label g).phase = (B.label g).phase + doubleLift s := by
    intro g hg
    have hA := two_phase_of_square (by rw [← A.label_multiply, hg, A.label_one])
    have hB := two_phase_of_square (by rw [← B.label_multiply, hg, B.label_one])
    rw [(hxz g).1, (hxz g).2] at hA
    apply eq_add_doubleLift_of_two_mul
    exact add_right_cancel (hA.trans hB.symm)
  choose sx hsx using fun i => hsq (xGenerator i) (multiply_xGenerator_self i)
  choose sz hsz using fun i => hsq (zGenerator i) (multiply_zGenerator_self i)
  -- the sign pattern is a functional of the binary images
  let φ : PhaseAddress →ₗ[F] F :=
    ((Tableau.dot sx).comp (LinearMap.fst F _ _) +
      (Tableau.dot sz).comp (LinearMap.snd F _ _)).comp B.binary.symm.toLinearMap
  obtain ⟨c, hc⟩ := exists_pairing φ
  have hlabel : ∀ g s, (A.label g).phase = (B.label g).phase + doubleLift s →
      φ ((B.label g).binary) = s → (B.then (pauliRealization c)).label g = A.label g := by
    intro g s hs hφ
    change pauliLabel c (B.label g) = A.label g
    refine Label.ext' (p := pauliLabel c (B.label g)) (q := A.label g)
      (hxz g).1.symm (hxz g).2.symm ?_
    change (B.label g).phase + doubleLift (Tableau.dot c.z (B.label g).x +
      Tableau.dot (B.label g).z c.x) = _
    have hp := hc (B.label g).binary
    rw [pairing_apply, hφ] at hp
    change (B.label g).phase + doubleLift (Tableau.dot c.z (B.label g).x +
      Tableau.dot (B.label g).z c.x) = _
    rw [hs]
    exact congrArg (fun t => (B.label g).phase + doubleLift t) hp
  have hφx : ∀ i, φ ((B.label (xGenerator i)).binary) = sx i := by
    intro i
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, B.projects,
      LinearEquiv.symm_apply_apply, LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply]
    simp [xGenerator, Label.binary, Tableau.dot_symm sx, dot_single]
  have hφz : ∀ i, φ ((B.label (zGenerator i)).binary) = sz i := by
    intro i
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, B.projects,
      LinearEquiv.symm_apply_apply, LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply]
    simp [zGenerator, Label.binary, Tableau.dot_symm sz, dot_single]
  obtain ⟨κ, hκ⟩ := Realization.scalar_eq_smul (A := A) (B := B.then (pauliRealization c))
    (fun i => (hlabel _ _ (hsx i) (hφx i)).symm) (fun i => (hlabel _ _ (hsz i) (hφz i)).symm)
  exact ⟨c, κ, fun f => hκ f⟩

end IntegerMultBounds.Networks.Certificates.T16.Pauli
