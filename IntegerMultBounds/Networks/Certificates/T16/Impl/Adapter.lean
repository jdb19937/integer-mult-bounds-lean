module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Factor
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Word

/-! Rank-zero adapters between nine-bit kernel lists and native labels. A kernel list is
realized exactly by C gates, their inverses and Pauli translations; its binary tableau adds the
orthogonal projection onto the span of its odd vectors. When the odd vectors are orthonormal,
its inverse-Z subspace is the frame Lagrangian of that span, so against a native label with the
same span the relative tableau has no X block, and the adapter lowers to a word of primitives
without child calls. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams Pauli Tableau

/-! ### Kernel realizations -/

/-- The exact realization of a nine-bit kernel. -/
noncomputable def kernelRealization (q : ZMod 4) (v : Geometry.Address) : Realization :=
  if q = 1 then cRealization v
  else if q = 3 then (cRealization v).symm
  else if q = 2 then pauliRealization ⟨v, 0, 0⟩
  else Realization.identity

theorem kernel_zero_apply {h : ℕ} (v : BinaryWalsh.Address h) (f : Arrays h) :
    BinaryWalsh.kernel 0 v f = f := by
  funext x
  simp [kernel_apply]

theorem kernelRealization_scalar (q : ZMod 4) (v : Geometry.Address) (f : State) :
    (kernelRealization q v).scalar f = BinaryWalsh.kernel q v f := by
  unfold kernelRealization
  split_ifs with h1 h3 h2
  · subst h1; rfl
  · subst h3
    change BinaryWalsh.kernel (-1) v f = _
    rfl
  · subst h2
    funext x
    change operator ⟨v, 0, 0⟩ f x = _
    rw [operator_apply, kernel_apply]
    have hp : phase 2 = -1 := by
      change Complex.I ^ 2 = -1
      rw [Complex.I_sq]
    simp [hp]
  · have h0 : q = 0 := by
      revert h1 h3 h2
      generalize q = q
      revert q
      decide
    subst h0
    exact (kernel_zero_apply v f).symm

/-- Odd phases are C gates or their inverses. -/
def isOdd (q : ZMod 4) : Bool := q = 1 || q = 3

theorem kernelRealization_binary (q : ZMod 4) (v : Geometry.Address) (p : Geometry.PhaseAddress) :
    (kernelRealization q v).binary p =
      if isOdd q then (p.1 + dot v p.2 • v, p.2) else p := by
  unfold kernelRealization isOdd
  split_ifs with h1 h3 h2 <;> simp_all
  · rfl
  · change (p.1 - dot v p.2 • v, p.2) = _
    rw [sub_eq_add_neg, ZModModule.neg_eq_self]
  · rfl
  · rfl

/-! ### Kernel lists -/

/-- The exact realization of a nine-bit kernel list. -/
noncomputable def kernelListRealization (gs : List (ZMod 4 × Geometry.Address)) : Realization :=
  realizeWord (gs.map fun g => kernelRealization g.1 g.2)

theorem kernelListRealization_scalar (gs : List (ZMod 4 × Geometry.Address)) (f : State) :
    (kernelListRealization gs).scalar f = kernelList gs f := by
  induction gs generalizing f with
  | nil => rfl
  | cons g gs ih =>
    change (kernelListRealization gs).scalar ((kernelRealization g.1 g.2).scalar f) = _
    rw [ih, kernelRealization_scalar]
    rfl

/-- The projection added by the odd vectors of a kernel list. -/
def oddSum (gs : List (ZMod 4 × Geometry.Address)) (b : Geometry.Address) : Geometry.Address :=
  ((gs.filter fun g => isOdd g.1).map fun g => dot g.2 b • g.2).sum

theorem oddSum_cons (g : ZMod 4 × Geometry.Address) (gs : List (ZMod 4 × Geometry.Address))
    (b : Geometry.Address) :
    oddSum (g :: gs) b = (if isOdd g.1 then dot g.2 b • g.2 else 0) + oddSum gs b := by
  unfold oddSum
  rw [List.filter_cons]
  split_ifs <;> simp

theorem kernelListRealization_binary (gs : List (ZMod 4 × Geometry.Address)) (p : Geometry.PhaseAddress) :
    (kernelListRealization gs).binary p = (p.1 + oddSum gs p.2, p.2) := by
  induction gs generalizing p with
  | nil => simp [kernelListRealization, realizeWord, Realization.identity, oddSum]
  | cons g gs ih =>
    change (kernelListRealization gs).binary ((kernelRealization g.1 g.2).binary p) = _
    rw [kernelRealization_binary, oddSum_cons]
    split_ifs
    · rw [ih, add_assoc]
    · rw [ih]
      simp

theorem oddSum_add (gs : List (ZMod 4 × Geometry.Address)) (a b : Geometry.Address) :
    oddSum gs (a + b) = oddSum gs a + oddSum gs b := by
  induction gs with
  | nil => simp [oddSum]
  | cons g gs ih =>
    rw [oddSum_cons, oddSum_cons, oddSum_cons, ih]
    split_ifs
    · rw [map_add, add_smul]; abel
    · simp

theorem oddSum_smul (gs : List (ZMod 4 × Geometry.Address)) (c : Geometry.F)
    (a : Geometry.Address) : oddSum gs (c • a) = c • oddSum gs a := by
  induction gs with
  | nil => simp [oddSum]
  | cons g gs ih =>
    rw [oddSum_cons, oddSum_cons, ih]
    split_ifs
    · rw [map_smul, smul_eq_mul, mul_smul, smul_add]
    · simp

/-- The odd vectors of a kernel list. -/
def oddVecs (gs : List (ZMod 4 × Geometry.Address)) : List Geometry.Address :=
  (gs.filter fun g => isOdd g.1).map Prod.snd

theorem oddSum_mem (gs : List (ZMod 4 × Geometry.Address)) (b : Geometry.Address) :
    oddSum gs b ∈ Submodule.span Geometry.F {v | v ∈ oddVecs gs} := by
  induction gs with
  | nil => exact Submodule.zero_mem _
  | cons g gs ih =>
    rw [oddSum_cons]
    apply Submodule.add_mem
    · split_ifs with h
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [oddVecs, h]))
      · exact Submodule.zero_mem _
    · refine Submodule.span_mono ?_ ih
      intro v hv
      simp only [oddVecs, List.filter_cons] at hv ⊢
      split_ifs <;> simp_all

/-- `oddSum` is symmetric for the binary form. -/
theorem dot_oddSum (gs : List (ZMod 4 × Geometry.Address)) (x b : Geometry.Address) :
    dot x (oddSum gs b) = dot (oddSum gs x) b := by
  induction gs with
  | nil => simp [oddSum]
  | cons g gs ih =>
    rw [oddSum_cons, oddSum_cons, map_add, map_add, LinearMap.add_apply, ih]
    split_ifs
    · rw [map_smul, smul_eq_mul, map_smul, LinearMap.smul_apply, smul_eq_mul, dot_symm g.2 x,
        mul_comm]
    · simp

theorem dot_oddSum_zero (gs : List (ZMod 4 × Geometry.Address)) {w : Geometry.Address}
    (hw : ∀ v ∈ oddVecs gs, dot v w = 0) : oddSum gs w = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [oddSum_cons, ih (fun v hv => hw v (by
      simp only [oddVecs, List.filter_cons] at hv ⊢
      split_ifs <;> simp_all))]
    split_ifs with h
    · rw [hw g.2 (by simp [oddVecs, h]), zero_smul, add_zero]
    · simp

/-- **Projection.** If `oddSum` fixes every odd vector, the inverse-Z subspace of the kernel list
is the frame Lagrangian of their span. -/
theorem kernelList_inverseZ (gs : List (ZMod 4 × Geometry.Address))
    (hproj : ∀ v ∈ oddVecs gs, oddSum gs v = v) :
    inverseZ (kernelListRealization gs).binary =
      Geometry.frameLagrangian (Submodule.span Geometry.F {v | v ∈ oddVecs gs}) := by
  set U := Submodule.span Geometry.F {v | v ∈ oddVecs gs}
  have hfix : ∀ u ∈ U, oddSum gs u = u := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem v hv => exact hproj v hv
    | zero => simpa using oddSum_smul gs 0 0
    | add a b _ _ ha hb => rw [oddSum_add, ha, hb]
    | smul c a _ ha => rw [oddSum_smul, ha]
  have horth : ∀ w, (∀ v ∈ oddVecs gs, dot v w = 0) → w ∈ Geometry.binaryOrthogonal U := by
    intro w hw
    rw [Geometry.binaryOrthogonal, LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    change dot u w = 0
    induction hu using Submodule.span_induction with
    | mem v hv => exact hw v hv
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, LinearMap.smul_apply, ha, smul_zero]
  have hdot : ∀ v ∈ oddVecs gs, ∀ b, dot v (oddSum gs b) = dot v b := fun v hv b => by
    rw [dot_oddSum, hproj v hv]
  ext p
  rw [mem_inverseZ, kernelListRealization_binary, Geometry.mem_frameLagrangian]
  constructor
  · intro h
    have hp1 : p.1 = oddSum gs p.2 := by
      have := congrArg (· + oddSum gs p.2) h
      simpa [add_assoc, ZModModule.add_self] using this
    refine ⟨oddSum gs p.2, oddSum_mem gs p.2, oddSum gs p.2 + p.2, horth _ (fun v hv => ?_), ?_⟩
    · rw [map_add, hdot v hv, CharTwo.add_self_eq_zero]
    · refine Prod.ext hp1 ?_
      change p.2 = oddSum gs p.2 + (oddSum gs p.2 + p.2)
      rw [← add_assoc, ZModModule.add_self, zero_add]
  · rintro ⟨u, hu, w, hw, rfl⟩
    change u + oddSum gs (u + w) = 0
    have hw' : ∀ v ∈ oddVecs gs, dot v w = 0 := by
      intro v hv
      rw [Geometry.binaryOrthogonal, LinearMap.BilinForm.mem_orthogonal_iff] at hw
      exact hw v (Submodule.subset_span hv)
    rw [oddSum_add, hfix u hu, dot_oddSum_zero gs hw', add_zero, ZModModule.add_self]

/-- Equal inverse-Z subspaces leave the relative tableau without an X block. -/
theorem xRange_eq_bot {A B : Geometry.PhaseAddress ≃ₗ[Geometry.F] Geometry.PhaseAddress} (h : inverseZ A = inverseZ B) :
    xRange (A.symm.trans B) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨z, rfl⟩
  rw [Submodule.mem_bot]
  have hz : A.symm (0, z) ∈ inverseZ B := by
    rw [← h, mem_inverseZ, LinearEquiv.apply_symm_apply]
  rw [mem_inverseZ] at hz
  exact hz

theorem finrank_xRange_eq_zero {A B : Geometry.PhaseAddress ≃ₗ[Geometry.F] Geometry.PhaseAddress}
    (h : inverseZ A = inverseZ B) : Module.finrank Geometry.F (xRange (A.symm.trans B)) = 0 := by
  rw [xRange_eq_bot h, finrank_bot]

/-! ### Adapters -/

/-- The adapter from a kernel list into a native label: undo the list, apply the label. -/
noncomputable def preAdapter (gs : List (ZMod 4 × Geometry.Address)) (i : ℕ) : Realization :=
  (kernelListRealization gs).symm.then (nativeRealization i)

/-- The adapter from a native label to a kernel list: undo the label, apply the list. -/
noncomputable def postAdapter (gs : List (ZMod 4 × Geometry.Address)) (i : ℕ) : Realization :=
  (nativeRealization i).symm.then (kernelListRealization gs)

/-- A kernel list whose odd vectors are fixed by its projection and span a native label's
space. -/
structure Matches (gs : List (ZMod 4 × Geometry.Address)) (i : ℕ) : Prop where
  proj : ∀ v ∈ oddVecs gs, oddSum gs v = v
  span : Submodule.span Geometry.F {v | v ∈ oddVecs gs} = (Geometry.catalog i).space

theorem Matches.inverseZ {gs : List (ZMod 4 × Geometry.Address)} {i : ℕ} (h : Matches gs i) :
    inverseZ (kernelListRealization gs).binary = inverseZ (nativeRealization i).binary := by
  rw [kernelList_inverseZ gs h.proj, h.span, nativeRealization_binary, nativeTableau_inverse_Z]

end IntegerMultBounds.Networks.Certificates.T16.Impl
