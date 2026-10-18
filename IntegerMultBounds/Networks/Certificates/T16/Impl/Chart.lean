module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Factor
public import IntegerMultBounds.Networks.Certificates.T16.Streams.PortsCheck

/-! Register charts. A register array is its family array read through an orthogonal chart.
`basisChart B σ` sends coordinate `j` to the basis vector `B (σ j)`; it pulls the basis back to
coordinate vectors. `swapChart w` adds `[x·w_i] w_i` for pairwise orthogonal isotropic vectors
`w_i`: with `w_i = b + e` for orthonormal `b` and `e` orthogonal to each other, it exchanges `b`
and `e` and fixes everything orthogonal to both. Through a chart, a kernel product over a basis
becomes a kernel product over the pulled-back basis, which splits into its local and exterior
parts whenever every pulled-back vector is local or exterior. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams Multiplicative

/-! ### The binary form on sums -/

@[simp] theorem binary_sum_left {ι : Type*} (s : Finset ι) (f : ι → Addr) (y : Addr) :
    Labels.binary 73 (∑ i ∈ s, f i) y = ∑ i ∈ s, Labels.binary 73 (f i) y := by
  rw [map_sum, LinearMap.sum_apply]

@[simp] theorem binary_sum_right {ι : Type*} (s : Finset ι) (f : ι → Addr) (x : Addr) :
    Labels.binary 73 x (∑ i ∈ s, f i) = ∑ i ∈ s, Labels.binary 73 x (f i) := map_sum _ _ _

@[simp] theorem binary_smul_left (c : ZMod 2) (x y : Addr) :
    Labels.binary 73 (c • x) y = c * Labels.binary 73 x y := by
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

@[simp] theorem binary_smul_right (c : ZMod 2) (x y : Addr) :
    Labels.binary 73 x (c • y) = c * Labels.binary 73 x y := by
  rw [map_smul, smul_eq_mul]

/-! ### Basis charts -/

/-- The chart sending coordinate `j` to `B (σ j)`. -/
noncomputable def basisChart (B : Fin 73 → Addr) (hB : Orthonormal73 B) (σ : Equiv.Perm (Fin 73)) :
    Addr ≃ₗ[ZMod 2] Addr where
  toFun x := ∑ j, x j • B (σ j)
  invFun y j := Labels.binary 73 y (B (σ j))
  left_inv x := by
    funext j
    have hB' : ∀ i j, Labels.binary 73 (B i) (B j) = if i = j then 1 else 0 := hB
    simp only [binary_sum_left, binary_smul_left, hB', σ.injective.eq_iff, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  right_inv y := by
    conv_rhs => rw [hB.expand y]
    exact (Equiv.sum_comp σ (fun k => Labels.binary 73 y (B k) • B k))
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

theorem basisChart_symm_apply (B : Fin 73 → Addr) (hB : Orthonormal73 B) (σ : Equiv.Perm (Fin 73))
    (y : Addr) (j : Fin 73) : (basisChart B hB σ).symm y j = Labels.binary 73 y (B (σ j)) := by
  rfl

theorem basisChart_symm_basis (B : Fin 73 → Addr) (hB : Orthonormal73 B) (σ : Equiv.Perm (Fin 73))
    (k : Fin 73) : (basisChart B hB σ).symm (B k) = Pi.single (σ.symm k) 1 := by
  funext j
  rw [basisChart_symm_apply, hB, Pi.single_apply]
  by_cases h : σ j = k
  · subst h; simp
  · have h' : j ≠ σ.symm k := fun e => h (by rw [e, Equiv.apply_symm_apply])
    simp [Ne.symm h, h']

theorem basisChart_orth (B : Fin 73 → Addr) (hB : Orthonormal73 B) (σ : Equiv.Perm (Fin 73)) :
    IsOrth (basisChart B hB σ) := by
  intro x y
  change Labels.binary 73 (∑ j, x j • B (σ j)) (∑ j, y j • B (σ j)) = _
  have hB' : ∀ i j, Labels.binary 73 (B i) (B j) = if i = j then 1 else 0 := hB
  simp only [binary_sum_left, binary_sum_right, binary_smul_left, binary_smul_right, hB',
    σ.injective.eq_iff, mul_ite, mul_one, mul_zero]
  simp [Labels.binary, Labels.form_apply, mul_comm]

/-! ### Swap charts -/

/-- `x ↦ x + Σ_i [x·w_i] w_i`. -/
def swapMap {n : ℕ} (w : Fin n → Addr) (x : Addr) : Addr := x + ∑ i, Labels.binary 73 x (w i) • w i

theorem swapMap_add {n : ℕ} (w : Fin n → Addr) (x y : Addr) :
    swapMap w (x + y) = swapMap w x + swapMap w y := by
  simp only [swapMap, map_add, LinearMap.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem binary_swapMap {n : ℕ} (w : Fin n → Addr) (hw : ∀ i j, Labels.binary 73 (w i) (w j) = 0)
    (x : Addr) (j : Fin n) : Labels.binary 73 (swapMap w x) (w j) = Labels.binary 73 x (w j) := by
  simp [swapMap, hw]

theorem swapMap_swapMap {n : ℕ} (w : Fin n → Addr) (hw : ∀ i j, Labels.binary 73 (w i) (w j) = 0)
    (x : Addr) : swapMap w (swapMap w x) = x := by
  conv_lhs => rw [swapMap]
  simp only [binary_swapMap w hw]
  rw [swapMap, add_assoc, ← Finset.sum_add_distrib]
  simp [ZModModule.add_self]

/-- The swap chart: an orthogonal involution. -/
def swapChart {n : ℕ} (w : Fin n → Addr) (hw : ∀ i j, Labels.binary 73 (w i) (w j) = 0) :
    Addr ≃ₗ[ZMod 2] Addr where
  toFun := swapMap w
  invFun := swapMap w
  left_inv := swapMap_swapMap w hw
  right_inv := swapMap_swapMap w hw
  map_add' := swapMap_add w
  map_smul' c x := by
    simp only [swapMap, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum,
      smul_smul, RingHom.id_apply]

theorem swapChart_apply {n : ℕ} (w : Fin n → Addr) (hw : ∀ i j, Labels.binary 73 (w i) (w j) = 0)
    (x : Addr) : swapChart w hw x = swapMap w x := rfl

theorem swapChart_symm {n : ℕ} (w : Fin n → Addr) (hw : ∀ i j, Labels.binary 73 (w i) (w j) = 0) :
    (swapChart w hw).symm = swapChart w hw := rfl

theorem swapChart_orth {n : ℕ} (w : Fin n → Addr) (hw : ∀ i j, Labels.binary 73 (w i) (w j) = 0) :
    IsOrth (swapChart w hw) := by
  intro x y
  change Labels.binary 73 (swapMap w x) (swapMap w y) = _
  have hxy : ∀ z, Labels.binary 73 (∑ i, Labels.binary 73 z (w i) • w i)
      (∑ i, Labels.binary 73 y (w i) • w i) = 0 := by
    intro z
    simp [hw]
  simp only [swapMap, map_add, LinearMap.add_apply, hxy, add_zero]
  have h1 : Labels.binary 73 x (∑ i, Labels.binary 73 y (w i) • w i) =
      ∑ i, Labels.binary 73 y (w i) * Labels.binary 73 x (w i) := by
    simp
  have h2 : Labels.binary 73 (∑ i, Labels.binary 73 x (w i) • w i) y =
      ∑ i, Labels.binary 73 y (w i) * Labels.binary 73 x (w i) := by
    simp only [binary_sum_left, binary_smul_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [Labels.binary, Labels.form_symm 0 (w i) y]
    ring
  rw [h1, h2, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-! ### Splitting through a chart -/

/-- Splitting a phase over local and exterior pulled-back vectors. -/
theorem phaseExp_split (V : Fin 73 → Addr) (c : Fin 73 → ZMod 4) (L : List (Fin 73))
    (hL : L.Nodup) (b : Fin 73 → Address 9) (hloc : ∀ k ∈ L, V k = padLow (b k)) (u : Addr) :
    phaseExp V c u = kernelListPhase (L.map fun k => (c k, b k)) (lowPart u) +
      phaseExp V (fun k => if k ∈ L then 0 else c k) u := by
  have hterm : ∀ k ∈ L, c k * bitLift (Labels.binary 73 u (V k)) =
      c k * bitLift (Labels.binary 9 (lowPart u) (b k)) := by
    intro k hk
    rw [hloc k hk, padLow, ← join_parts u, binary_join]
    simp
  unfold phaseExp
  have hpt : ∀ k, c k * bitLift (Labels.binary 73 u (V k)) =
      (if k ∈ L then c k * bitLift (Labels.binary 73 u (V k)) else 0) +
        (if k ∈ L then 0 else c k) * bitLift (Labels.binary 73 u (V k)) := by
    intro k
    split_ifs <;> simp
  have hfilter : (Finset.univ.filter fun k => k ∈ L) = L.toFinset := by
    ext k
    simp
  have hA : (∑ k, if k ∈ L then c k * bitLift (Labels.binary 73 u (V k)) else 0) =
      kernelListPhase (L.map fun k => (c k, b k)) (lowPart u) := by
    rw [← Finset.sum_filter, hfilter, List.sum_toFinset _ hL, kernelListPhase, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    exact hterm k hk
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, hA]

end IntegerMultBounds.Networks.Certificates.T16.Impl
