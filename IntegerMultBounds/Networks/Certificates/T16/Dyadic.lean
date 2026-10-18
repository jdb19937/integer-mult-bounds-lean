module

public import IntegerMultBounds.Networks.Certificates.T16.PauliLowering
public import IntegerMultBounds.Networks.GaussianDyadic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Basic.Complex.BigOperators

/-! **Dyadic unitary realizations.** An operator on nine-bit arrays is *good* when it keeps
Gaussian dyadic values Gaussian dyadic and preserves the sum of squared moduli. Kernels, diagonal
phases, permutations and Pauli operators are good, so are their inverses, and so is every native
realization and every transition between native realizations. A scalar relating two good
operators is a Gaussian dyadic number of modulus one, hence a fourth root of unity. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Pauli

open Geometry BinaryPhase BinaryWalsh GaussianDyadic ComplexConjugate

/-! ### Gaussian dyadic numbers -/

/-- A Gaussian integer divided by a power of two. -/
def Dy (z : ℂ) : Prop := ∃ n, Grid n z

theorem grid_lift {n : ℕ} {z : ℂ} (h : Grid n z) (k : ℕ) : Grid (n + k) z := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨a * 2 ^ k, b * 2 ^ k, ?_⟩
  rw [pow_add, ← mul_assoc, hab]
  push_cast
  ring

theorem Dy.add {z w : ℂ} (hz : Dy z) (hw : Dy w) : Dy (z + w) := by
  obtain ⟨n, hn⟩ := hz
  obtain ⟨m, hm⟩ := hw
  exact ⟨n + m, grid_add (grid_lift hn m) (by rw [Nat.add_comm]; exact grid_lift hm n)⟩

theorem Dy.mul {z w : ℂ} (hz : Dy z) (hw : Dy w) : Dy (z * w) := by
  obtain ⟨n, hn⟩ := hz
  obtain ⟨m, hm⟩ := hw
  exact ⟨n + m, grid_mul hn hm⟩

theorem Dy.neg {z : ℂ} (hz : Dy z) : Dy (-z) := by
  obtain ⟨n, hn⟩ := hz
  exact ⟨n, grid_neg hn⟩

theorem Dy.half {z : ℂ} (hz : Dy z) : Dy (z / 2) := by
  obtain ⟨n, hn⟩ := hz
  exact ⟨n + 1, grid_half hn⟩

theorem Dy.conj {z : ℂ} (hz : Dy z) : Dy (conj z) := by
  obtain ⟨n, a, b, hab⟩ := hz
  refine ⟨n, a, -b, ?_⟩
  have h := congrArg conj hab
  simp only [map_mul, map_pow, map_ofNat, map_add, map_intCast, Complex.conj_I] at h
  rw [h]
  push_cast
  ring

theorem dy_int (a : ℤ) : Dy a := ⟨0, grid_int a⟩

theorem dy_one : Dy 1 := by simpa using dy_int 1

theorem dy_zero : Dy 0 := ⟨0, grid_zero 0⟩

theorem dy_I : Dy Complex.I := ⟨0, grid_I⟩

theorem dy_phase (q : ZMod 4) : Dy (phase q) := by
  unfold phase
  induction q.val with
  | zero => simpa using dy_one
  | succ k ih => rw [pow_succ]; exact ih.mul dy_I

theorem dy_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ) (h : ∀ i ∈ s, Dy (g i)) : Dy (∑ i ∈ s, g i) :=
  Finset.sum_induction _ Dy (fun _ _ => Dy.add) dy_zero h

theorem normSq_phase (q : ZMod 4) : Complex.normSq (phase q) = 1 := by
  unfold phase
  rw [map_pow, Complex.normSq_I, one_pow]

theorem sq_mod_four (a : ℤ) : a ^ 2 % 4 = if a % 2 = 0 then 0 else 1 := by
  rcases Int.even_or_odd' a with ⟨k, rfl | rfl⟩
  · rw [show (2 * k) ^ 2 = 4 * k ^ 2 by ring, Int.mul_emod_right]
    simp
  · rw [show (2 * k + 1) ^ 2 = 1 + 4 * (k ^ 2 + k) by ring, Int.add_mul_emod_self_left]
    have : (2 * k + 1) % 2 = 1 := by omega
    simp [this]

theorem phase_two : phase 2 = -1 := by
  simp [phase, show (2 : ZMod 4).val = 2 from rfl]

theorem phase_three : phase 3 = -Complex.I := by
  simp [phase, show (3 : ZMod 4).val = 3 from rfl, pow_succ]

/-- Integer points on the circle of radius `2^n`. -/
theorem int_circle (n : ℕ) (a b : ℤ) (h : a ^ 2 + b ^ 2 = 4 ^ n) :
    (a = 2 ^ n ∧ b = 0) ∨ (a = -2 ^ n ∧ b = 0) ∨ (a = 0 ∧ b = 2 ^ n) ∨ (a = 0 ∧ b = -2 ^ n) := by
  induction n generalizing a b with
  | zero =>
    have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
    have hb : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
    have ha' : -1 ≤ a ∧ a ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    have hb' : -1 ≤ b ∧ b ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    simp only [pow_zero] at h ⊢
    obtain ⟨ha1, ha2⟩ := ha'
    obtain ⟨hb1, hb2⟩ := hb'
    interval_cases a <;> interval_cases b <;> simp_all
  | succ n ih =>
    have hpar : 2 ∣ a ∧ 2 ∣ b := by
      have h4 : (a ^ 2 + b ^ 2) % 4 = 0 := by rw [h, pow_succ]; simp
      have ha := sq_mod_four a
      have hb := sq_mod_four b
      rw [Int.add_emod] at h4
      generalize a ^ 2 = A at h4 ha
      generalize b ^ 2 = B at h4 hb
      constructor <;> apply Int.dvd_of_emod_eq_zero <;> split_ifs at ha hb <;> omega
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := hpar
    have h' : a' ^ 2 + b' ^ 2 = 4 ^ n := by
      have : 4 * (a' ^ 2 + b' ^ 2) = 4 * 4 ^ n := by rw [← pow_succ']; linarith
      omega
    rcases ih a' b' h' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;>
      simp [pow_succ] <;> ring_nf <;> simp

/-- **A Gaussian dyadic number of modulus one is a fourth root of unity.** -/
theorem eq_phase_of_dy {z : ℂ} (hz : Dy z) (h1 : Complex.normSq z = 1) : ∃ j : ZMod 4, z = phase j := by
  obtain ⟨n, a, b, hab⟩ := hz
  have hc : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 = 4 ^ n := by
    have e := congrArg Complex.normSq hab
    rw [map_mul, h1, one_mul, map_pow, Complex.normSq_ofNat] at e
    rw [show ((a : ℂ) + b * Complex.I) = ((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I by push_cast; rfl,
      Complex.normSq_add_mul_I] at e
    rw [← e]
    norm_num
  have hc' : a ^ 2 + b ^ 2 = 4 ^ n := by exact_mod_cast hc
  have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  have hz' : z = ((a : ℂ) + b * Complex.I) / 2 ^ n := by rw [← hab]; field_simp
  rcases int_circle n a b hc' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨0, by rw [hz', phase_zero]; push_cast; field_simp; ring⟩
  · exact ⟨2, by rw [hz', phase_two]; push_cast; field_simp; ring⟩
  · exact ⟨1, by rw [hz', phase_one]; push_cast; field_simp; ring⟩
  · exact ⟨3, by rw [hz', phase_three]; push_cast; field_simp; ring⟩

/-! ### Good operators -/

/-- An array with Gaussian dyadic values. -/
def DVal (f : State) : Prop := ∀ x, Dy (f x)

/-- The sum of squared moduli. -/
noncomputable def nsq (f : State) : ℝ := ∑ x, Complex.normSq (f x)

/-- An operator keeping Gaussian dyadic arrays Gaussian dyadic and preserving `nsq`. -/
structure Good (L : State →ₗ[ℂ] State) : Prop where
  dy : ∀ f, DVal f → DVal (L f)
  norm : ∀ f, nsq (L f) = nsq f

theorem Good.comp {A B : State →ₗ[ℂ] State} (hA : Good A) (hB : Good B) : Good (B ∘ₗ A) :=
  ⟨fun f hf => hB.dy _ (hA.dy f hf), fun f => (hB.norm _).trans (hA.norm f)⟩

theorem good_id : Good LinearMap.id := ⟨fun _ hf => hf, fun _ => rfl⟩

/-- Reindexing by a bijection of addresses. -/
theorem good_reindex (L : State →ₗ[ℂ] State) (e : Geometry.Address ≃ Geometry.Address)
    (h : ∀ f x, L f x = f (e x)) : Good L := by
  refine ⟨fun f hf x => by rw [h]; exact hf _, fun f => ?_⟩
  unfold nsq
  simp only [h]
  exact Equiv.sum_comp e (fun x => Complex.normSq (f x))

/-- Multiplication by unimodular Gaussian dyadic weights. -/
theorem good_weight (L : State →ₗ[ℂ] State) (ψ : Geometry.Address → ℂ) (hψ : ∀ x, Dy (ψ x))
    (h1 : ∀ x, Complex.normSq (ψ x) = 1) (h : ∀ f x, L f x = ψ x * f x) : Good L := by
  refine ⟨fun f hf x => by rw [h]; exact (hψ x).mul (hf x), fun f => ?_⟩
  unfold nsq
  simp only [h, map_mul, h1, one_mul]

theorem dy_sign (b : ZMod 2) : Dy (sign b) := by
  unfold sign; split_ifs
  · exact dy_one
  · exact dy_one.neg

theorem normSq_sign (b : ZMod 2) : Complex.normSq (sign b) = 1 := by
  unfold sign; split_ifs <;> simp

theorem kernel_coeffs (q : ZMod 4) :
    Complex.normSq ((1 + phase q) / 2) + Complex.normSq ((1 - phase q) / 2) = 1 ∧
      ((1 + phase q) / 2 * conj ((1 - phase q) / 2)).re = 0 := by
  obtain rfl | rfl | rfl | rfl : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by revert q; decide
  all_goals
    simp only [phase_zero, phase_one, phase_two, phase_three]
    constructor <;>
      simp [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.mul_re] <;> norm_num

theorem good_kernel (q : ZMod 4) (v : Geometry.Address) : Good (BinaryWalsh.kernel q v) := by
  obtain ⟨hab, hre⟩ := kernel_coeffs q
  have hda : Dy ((1 + phase q) / 2) := (dy_one.add (dy_phase q)).half
  have hdb : Dy ((1 - phase q) / 2) := by
    have := (dy_one.add (dy_phase q).neg).half
    simpa [sub_eq_add_neg] using this
  refine ⟨fun f hf x => ?_, fun f => ?_⟩
  · rw [BinaryWalsh.kernel_apply]
    exact (hda.mul (hf x)).add (hdb.mul (hf _))
  unfold nsq
  simp only [BinaryWalsh.kernel_apply, Complex.normSq_add, map_mul]
  set S := ∑ x, f x * conj (f (x + v))
  have hS : conj S = S := by
    simp only [S, map_sum, map_mul, Complex.conj_conj]
    exact Fintype.sum_equiv (Equiv.addRight v) _ _ fun x => by
      simp [add_assoc, mul_comm]
  have hSim : S.im = 0 := Complex.conj_eq_iff_im.mp hS
  have hshift : ∑ x, Complex.normSq (f (x + v)) = ∑ x, Complex.normSq (f x) :=
    Fintype.sum_equiv (Equiv.addRight v) _ _ fun x => rfl
  have hcross : ∑ x, ((1 + phase q) / 2 * f x * (conj ((1 - phase q) / 2) * conj (f (x + v)))).re =
      ((1 + phase q) / 2 * conj ((1 - phase q) / 2) * S).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring_nf
  have hzero : ((1 + phase q) / 2 * conj ((1 - phase q) / 2) * S).re = 0 := by
    rw [Complex.mul_re, hre, hSim]
    ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hshift,
    ← Finset.mul_sum, hcross, hzero]
  linear_combination (∑ x, Complex.normSq (f x)) * hab

theorem good_operator (c : Label) : Good (operator c) := by
  have ht : Good (translation c.x) := good_reindex _ (Equiv.addRight c.x) fun _ _ => rfl
  have hc : Good (characterMultiply c.z) := good_weight _ (chi c.z) (fun _ => dy_sign _)
    (fun _ => normSq_sign _) fun _ _ => rfl
  have hp : Good (phase c.phase • (LinearMap.id : State →ₗ[ℂ] State)) :=
    good_weight _ (fun _ => phase c.phase) (fun _ => dy_phase _) (fun _ => normSq_phase _)
      fun _ _ => rfl
  have e : operator c = (phase c.phase • (LinearMap.id : State →ₗ[ℂ] State)) ∘ₗ
      ((translation c.x).comp (characterMultiply c.z)) := by
    apply LinearMap.ext; intro f; rfl
  rw [e]
  exact (hc.comp ht).comp hp

/-! ### Good equivalences and realizations -/

/-- An equivalence that is good in both directions. -/
def GoodE (L : State ≃ₗ[ℂ] State) : Prop := Good L.toLinearMap ∧ Good L.symm.toLinearMap

theorem GoodE.trans {A B : State ≃ₗ[ℂ] State} (hA : GoodE A) (hB : GoodE B) : GoodE (A.trans B) :=
  ⟨hA.1.comp hB.1, hB.2.comp hA.2⟩

theorem GoodE.symm {A : State ≃ₗ[ℂ] State} (hA : GoodE A) : GoodE A.symm := ⟨hA.2, hA.1⟩

theorem goodE_refl : GoodE (LinearEquiv.refl ℂ State) := ⟨good_id, good_id⟩

theorem goodE_kernelEquiv (s : ZMod 4) (q : Geometry.Address) : GoodE (kernelEquiv s q) :=
  ⟨good_kernel s q, good_kernel (-s) q⟩

theorem goodE_phaseDiagonal (ψ : Geometry.Address → ZMod 4) : GoodE (phaseDiagonal ψ) :=
  ⟨good_weight _ (fun x => phase (ψ x)) (fun _ => dy_phase _) (fun _ => normSq_phase _)
      fun _ _ => rfl,
    good_weight _ (fun x => phase (-ψ x)) (fun _ => dy_phase _) (fun _ => normSq_phase _)
      fun _ _ => rfl⟩

theorem goodE_permutation (G : Geometry.Address ≃ₗ[F] Geometry.Address) : GoodE (permutation G) :=
  ⟨good_reindex _ G.symm.toEquiv fun _ _ => rfl, good_reindex _ G.toEquiv fun _ _ => rfl⟩

/-- A realization whose operator is good in both directions. -/
def Realization.Dyadic (K : Realization) : Prop := GoodE K.scalar

theorem Realization.Dyadic.then {A B : Realization} (hA : A.Dyadic) (hB : B.Dyadic) :
    (A.then B).Dyadic := GoodE.trans hA hB

theorem Realization.Dyadic.symm {A : Realization} (hA : A.Dyadic) : A.symm.Dyadic := GoodE.symm hA

theorem dyadic_identity : Realization.identity.Dyadic := goodE_refl

theorem dyadic_realizeWord (gs : List Realization) (h : ∀ g ∈ gs, g.Dyadic) :
    (realizeWord gs).Dyadic := by
  induction gs with
  | nil => exact dyadic_identity
  | cons g gs ih =>
    exact (h g List.mem_cons_self).then (ih fun g' h' => h g' (List.mem_cons_of_mem _ h'))

theorem dyadic_permutation (G : Geometry.Address ≃ₗ[F] Geometry.Address) :
    (permutationRealization G).Dyadic := goodE_permutation G

theorem dyadic_permutationInverse (G : Geometry.Address ≃ₗ[F] Geometry.Address) :
    (permutationInverseRealization G).Dyadic := (goodE_permutation G).symm

theorem dyadic_c (q : Geometry.Address) : (cRealization q).Dyadic := goodE_kernelEquiv 1 q

theorem dyadic_diagonal (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4) (hQ : ∀ i j, Q i j = Q j i)
    (ha : ∀ i, 2 * alpha i = doubleLift (Q i i)) : (diagonalRealization Q alpha hQ ha).Dyadic :=
  goodE_phaseDiagonal _

theorem dyadic_diagonalInverse (Q : BinaryMatrix) (alpha : Fin 9 → ZMod 4)
    (hQ : ∀ i j, Q i j = Q j i) (ha : ∀ i, 2 * alpha i = doubleLift (Q i i)) :
    (diagonalInverseRealization Q alpha hQ ha).Dyadic :=
  (goodE_phaseDiagonal _).symm

theorem dyadic_cWord (r : ℕ) : ∀ g ∈ cWord r, g.Dyadic := by
  induction r with
  | zero => simp [cWord]
  | succ k ih =>
    intro g hg
    rw [cWord, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih g hg
    · split_ifs at hg
      · rw [List.mem_singleton] at hg; subst hg; exact dyadic_c _
      · simp at hg

theorem dyadic_partialC (r : ℕ) : (partialCRealization r).Dyadic :=
  dyadic_realizeWord _ (dyadic_cWord r)

theorem dyadic_canonical (G : Geometry.Address ≃ₗ[F] Geometry.Address) (r : ℕ) :
    (canonicalRealization G r).Dyadic := by
  apply dyadic_realizeWord
  intro g hg
  simp only [canonicalWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ((rfl | rfl) | hg) | rfl | rfl
  · exact dyadic_diagonalInverse _ _ _ _
  · exact dyadic_permutationInverse _
  · exact dyadic_cWord r g hg
  · exact dyadic_permutation _
  · exact dyadic_diagonal _ _ _ _

theorem dyadic_native (i : ℕ) : (nativeRealization i).Dyadic := by
  unfold nativeRealization sourceCanonicalRealization
  split_ifs
  · exact dyadic_identity
  · exact dyadic_partialC 9
  · exact dyadic_canonical _ _

theorem dyadic_edge (a b : ℕ) : (edgeRealization a b).Dyadic :=
  (dyadic_native a).symm.then (dyadic_native b)

theorem dyadic_shear (S : Geometry.Address →ₗ[F] Geometry.Address) (hS : Tableau.DotSymmetric S) :
    (shearRealization S hS).Dyadic := dyadic_diagonal _ _ _ _

theorem dyadic_monomial (G : Geometry.Address ≃ₗ[F] Geometry.Address)
    (S : Geometry.Address →ₗ[F] Geometry.Address) (hS : Tableau.DotSymmetric S) :
    (monomialRealization G S hS).Dyadic := (dyadic_permutation G).then (dyadic_shear S hS)

theorem dyadic_hadamard (r : ℕ) : (hadamardRealization r).Dyadic :=
  (dyadic_shear _ _).then ((dyadic_partialC r).then (dyadic_shear _ _))

/-! ### Scalars between good operators -/

theorem nsq_single : nsq (Pi.single 0 1) = 1 := by
  unfold nsq
  rw [Finset.sum_eq_single 0 (fun x _ hx => by simp [hx]) (by simp)]
  simp

/-- **A scalar relating two good operators is a fourth root of unity.** -/
theorem phase_of_good {U W : State →ₗ[ℂ] State} (hU : Good U) (hW : Good W) {κ : ℂ}
    (h : ∀ f, U f = κ • W f) : ∃ j : ZMod 4, κ = phase j := by
  set δ : State := Pi.single 0 1
  have hδ : DVal δ := fun x => by
    by_cases hx : x = 0
    · subst hx; simpa [δ] using dy_one
    · simpa [δ, Pi.single_apply, hx] using dy_zero
  set g := W δ
  have hg : nsq g = 1 := (hW.norm δ).trans nsq_single
  have hu : nsq (κ • g) = 1 := by rw [← h]; exact (hU.norm δ).trans nsq_single
  have hκ : Complex.normSq κ = 1 := by
    unfold nsq at hu hg
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← Finset.mul_sum] at hu
    rw [hg, mul_one] at hu
    exact hu
  have he : κ = ∑ x, conj (g x) * (κ • g) x := by
    have hgc : (∑ x, conj (g x) * g x) = 1 := by
      have : ((nsq g : ℝ) : ℂ) = ∑ x, conj (g x) * g x := by
        unfold nsq
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun x _ => Complex.normSq_eq_conj_mul_self
      rw [← this, hg]; simp
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (∑ x, conj (g x) * (κ * g x)) = κ * ∑ x, conj (g x) * g x by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring, hgc, mul_one]
  have hdg : DVal g := hW.dy δ hδ
  have hdu : DVal (κ • g) := by rw [← h]; exact hU.dy δ hδ
  refine eq_phase_of_dy ?_ hκ
  rw [he]
  exact dy_sum _ _ fun x _ => (hdg x).conj.mul (hdu x)

end IntegerMultBounds.Networks.Certificates.T16.Pauli
