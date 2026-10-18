module

public import IntegerMultBounds.Networks.Certificates.T16.Streams.Characters
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Schedule
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The full frame of every port is `C_all`. For an orthonormal basis `B`, weight modulo four is
additive over orthogonal sums, so `Σ_k wt(B_k) [u·B_k] ≡ wt(u)`, and the coefficient vector of
basis weights gives the product of the coordinate kernels. Each port basis is checked to be
orthonormal: its high vectors are the coordinate vectors and its nine low vectors have the
identity Gram matrix. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Streams

open BinaryWalsh BinaryPhase Multiplicative

/-! ### Weight modulo four over orthonormal bases -/

theorem weightPhase_smul {h : ℕ} (c : ZMod 2) (b : Address h) :
    weightPhase (c • b) = bitLift c * weightPhase b := by
  simp only [weightPhase, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  generalize b i = x
  revert c x
  decide

theorem weightPhase_zero {h : ℕ} : weightPhase (0 : Address h) = 0 := by
  simp [weightPhase]

theorem weightPhase_sum_orth {h : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ZMod 2)
    (B : ι → Address h) (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Labels.binary h (B i) (B j) = 0) :
    weightPhase (∑ i ∈ s, c i • B i) = ∑ i ∈ s, bitLift (c i) * weightPhase (B i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, weightPhase_add, weightPhase_smul,
      ih (fun i hi j hj hij => horth i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij)]
    have hd : Labels.binary h (c a • B a) (∑ i ∈ s, c i • B i) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i hi
      rw [map_smul, LinearMap.map_smul₂,
        horth a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun e => ha (e ▸ hi)), smul_zero, smul_zero]
    rw [hd, map_zero, sub_zero]

/-- Orthonormal families. -/
def Orthonormal73 (B : Fin 73 → Address 73) : Prop :=
  ∀ i j, Labels.binary 73 (B i) (B j) = if i = j then 1 else 0

theorem Orthonormal73.expand {B : Fin 73 → Address 73} (hB : Orthonormal73 B) (u : Address 73) :
    u = ∑ k, Labels.binary 73 u (B k) • B k := by
  have hB' : ∀ i j, Labels.binary 73 (B i) (B j) = if i = j then 1 else 0 := hB
  have hli : LinearIndependent (ZMod 2) B := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun v => Labels.binary 73 v (B j)) hg
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul₂, hB', smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_zero,
      LinearMap.zero_apply] at this
    exact this
  have hcard : Fintype.card (Fin 73) = Module.finrank (ZMod 2) (Address 73) := by
    rw [Module.finrank_fin_fun, Fintype.card_fin]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ∀ k, b k = B k := fun k => by simp [b]
  have hrepr := b.sum_repr u
  have hcoef : ∀ j, b.repr u j = Labels.binary 73 u (B j) := by
    intro j
    have := congrArg (fun v => Labels.binary 73 v (B j)) hrepr
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul₂, hb, hB', smul_eq_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    exact this
  conv_lhs => rw [← hrepr]
  simp only [hb, hcoef]

theorem Orthonormal73.weight {B : Fin 73 → Address 73} (hB : Orthonormal73 B) (u : Address 73) :
    ∑ k, weightPhase (B k) * bitLift (Labels.binary 73 u (B k)) = weightPhase u := by
  conv_rhs => rw [hB.expand u]
  rw [weightPhase_sum_orth Finset.univ _ B (fun i _ j _ hij => by simpa [hij] using hB i j)]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-! ### The coordinate kernels -/

/-- The standard basis. -/
def stdBasis (k : Fin 73) : Address 73 := Pi.single k 1

/-- `C_all`, the product of the coordinate kernels. -/
noncomputable def cAll := basisOp stdBasis (ofAdd fun _ => 1)

theorem binary_single (u : Address 73) (k : Fin 73) : Labels.binary 73 u (Pi.single k 1) = u k := by
  simp [Labels.binary, Labels.form_single]

/-- Over an orthonormal basis, the basis weights give `C_all`. -/
theorem basisOp_weights {B : Fin 73 → Address 73} (hB : Orthonormal73 B) :
    basisOp B (ofAdd fun k => weightPhase (B k)) = cAll := by
  apply basisOp_eq_of_phase
  intro u
  rw [phaseExp, hB.weight]
  simp [phaseExp, stdBasis, binary_single, weightPhase]

/-! ### Port bases -/

def decodeMask (n : ℕ) : Address 73 := fun i => if n.testBit i then 1 else 0

/-- The basis of a port: its nine stored low vectors, then the coordinate vectors. -/
def portBasis (P : PortData) (k : Fin 73) : Address 73 :=
  if k.val < 9 then decodeMask (P.basis.getD k.val 0) else Pi.single k 1

/-- Parity of the common low bits of two masks. -/
def dotNat (a b : ℕ) : ZMod 2 := ∑ i : Fin 9, if (a &&& b).testBit i then 1 else 0

/-- Weight modulo four of the low bits of a mask. -/
def weightNat (a : ℕ) : ZMod 4 := ∑ i : Fin 9, if a.testBit i then 1 else 0

/-- Checkable conditions on a port, in bit operations: low masks below `2^9`, identity low Gram
matrix, low full-frame coefficients equal to the low weights, and high coefficients one. -/
def portCheck (P : PortData) : Bool :=
  (List.finRange 9).all (fun i =>
    decide (P.basis.getD i.val 0 < 512) &&
    (List.finRange 9).all (fun j =>
      decide (dotNat (P.basis.getD i.val 0) (P.basis.getD j.val 0) = if i = j then 1 else 0)) &&
    decide ((fullFrame P).coeff i.val = weightNat (P.basis.getD i.val 0))) &&
  (List.finRange 73).all fun k => decide (9 ≤ k.val → (fullFrame P).coeff k.val = 1)

theorem testBit_low {n : ℕ} (hn : n < 512) {i : ℕ} (hi : 9 ≤ i) : n.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hn
    (by calc 512 = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi))

theorem decodeMask_high {n : ℕ} (hn : n < 512) {i : Fin 73} (hi : 9 ≤ i.val) :
    decodeMask n i = 0 := by
  simp [decodeMask, testBit_low hn hi]

theorem sum_fin73_low {M : Type*} [AddCommMonoid M] (f : ℕ → M) (hf : ∀ i, 9 ≤ i → f i = 0) :
    ∑ i : Fin 73, f i = ∑ i : Fin 9, f i := by
  rw [Fin.sum_univ_eq_sum_range f 73, Fin.sum_univ_eq_sum_range f 9,
    ← Finset.sum_range_add_sum_Ico f (show 9 ≤ 73 by norm_num)]
  rw [Finset.sum_eq_zero (fun i hi => hf i (Finset.mem_Ico.mp hi).1), add_zero]

theorem binary_decodeMask {a b : ℕ} (ha : a < 512) :
    Labels.binary 73 (decodeMask a) (decodeMask b) = dotNat a b := by
  simp only [Labels.binary, Labels.form_apply, zero_mul, sub_zero, dotNat, decodeMask]
  rw [sum_fin73_low (fun i => (if a.testBit i then (1 : ZMod 2) else 0) *
    (if b.testBit i then 1 else 0))]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.testBit_land]
    cases a.testBit i <;> cases b.testBit i <;> rfl
  · intro i hi
    simp [testBit_low ha hi]

theorem weightPhase_decodeMask {a : ℕ} (ha : a < 512) :
    weightPhase (decodeMask a) = weightNat a := by
  simp only [weightPhase, weightNat, decodeMask]
  rw [sum_fin73_low (fun i => bitLift (if a.testBit i then (1 : ZMod 2) else 0))]
  · apply Finset.sum_congr rfl
    intro i _
    cases a.testBit i <;> rfl
  · intro i hi
    simp [testBit_low ha hi]

theorem weightPhase_single (k : Fin 73) : weightPhase (Pi.single k (1 : ZMod 2)) = 1 := by
  simp only [weightPhase]
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [hx]) (by simp)]
  simp

structure PortFacts (P : PortData) : Prop where
  low : ∀ i : Fin 73, i.val < 9 → P.basis.getD i.val 0 < 512
  gram : ∀ i j : Fin 73, i.val < 9 → j.val < 9 →
    dotNat (P.basis.getD i.val 0) (P.basis.getD j.val 0) = if i = j then 1 else 0
  weight : ∀ i : Fin 73, i.val < 9 → (fullFrame P).coeff i.val = weightNat (P.basis.getD i.val 0)
  high : ∀ k : Fin 73, 9 ≤ k.val → (fullFrame P).coeff k.val = 1

theorem portFacts {P : PortData} (h : portCheck P = true) : PortFacts P := by
  simp only [portCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlow, hhigh⟩ := h
  have get : ∀ i : Fin 73, (hi : i.val < 9) →
      (P.basis.getD i.val 0 < 512 ∧ ∀ x ∈ List.finRange 9,
        dotNat (P.basis.getD i.val 0) (P.basis.getD x.val 0) =
          if (⟨i.val, hi⟩ : Fin 9) = x then 1 else 0) ∧
      (fullFrame P).coeff i.val = weightNat (P.basis.getD i.val 0) :=
    fun i hi => hlow ⟨i.val, hi⟩ (List.mem_finRange _)
  refine ⟨fun i hi => (get i hi).1.1, fun i j hi hj => ?_, fun i hi => (get i hi).2,
    fun k hk => hhigh k (List.mem_finRange k) hk⟩
  have := (get i hi).1.2 ⟨j.val, hj⟩ (List.mem_finRange _)
  rw [this]
  by_cases e : i = j
  · subst e; simp
  · have hne : (⟨i.val, hi⟩ : Fin 9) ≠ ⟨j.val, hj⟩ := fun h' => e (Fin.ext (Fin.mk.inj h'))
    simp [e, hne]

theorem portBasis_orthonormal {P : PortData} (h : portCheck P = true) :
    Orthonormal73 (portBasis P) := by
  have F := portFacts h
  have hsupp : ∀ i : Fin 73, i.val < 9 → ∀ k : Fin 73, 9 ≤ k.val → portBasis P i k = 0 := by
    intro i hi k hk
    simp only [portBasis, hi, ite_true]
    exact decodeMask_high (F.low i hi) hk
  intro i j
  by_cases hi : i.val < 9 <;> by_cases hj : j.val < 9
  · simp only [portBasis, hi, hj, ite_true]
    rw [binary_decodeMask (F.low i hi)]
    exact F.gram i j hi hj
  · have hj' : portBasis P j = Pi.single j 1 := by simp [portBasis, hj]
    rw [hj', binary_single, hsupp i hi j (by omega)]
    simp only [show i ≠ j from fun e => by subst e; omega, ite_false]
  · have hi' : portBasis P i = Pi.single i 1 := by simp [portBasis, hi]
    rw [hi', Labels.binary, Labels.form_symm, ← Labels.binary, binary_single,
      hsupp j hj i (by omega)]
    simp only [show i ≠ j from fun e => by subst e; omega, ite_false]
  · have hi' : portBasis P i = Pi.single i 1 := by simp [portBasis, hi]
    have hj' : portBasis P j = Pi.single j 1 := by simp [portBasis, hj]
    rw [hi', hj', binary_single]
    by_cases e : i = j
    · subst e; simp
    · simp [Ne.symm e, e]

/-- **The full frame of a checked port is `C_all`.** -/
theorem fullFrame_cAll {P : PortData} (h : portCheck P = true) :
    basisOp (portBasis P) (ofAdd (fullFrame P).toFun) = cAll := by
  have F := portFacts h
  have hw : (fullFrame P).toFun = fun k => weightPhase (portBasis P k) := by
    funext k
    change (fullFrame P).coeff k.val = _
    by_cases hk : k.val < 9
    · simp only [portBasis, hk, ite_true]
      rw [weightPhase_decodeMask (F.low k hk), F.weight k hk]
    · simp only [portBasis, hk, ite_false]
      rw [weightPhase_single, F.high k (by omega)]
  rw [hw]
  exact basisOp_weights (portBasis_orthonormal h)

end IntegerMultBounds.Networks.Certificates.T16.Streams
