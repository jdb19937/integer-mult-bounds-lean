module

public import IntegerMultBounds.MathlibTM2.M6.T16Node
public import IntegerMultBounds.MathlibTM2.Layer.NodeZ
public import IntegerMultBounds.MathlibTM2.Node.Phase

/-!
# The T16 node at the decoded-array level

The layer machine views a stored wire on its active bits `e : Fin (h * k) → Fin n` as an array
`view e (toC u) : Arr (Y × (Fin n → ZMod 2)) (h * k)`, and a column operator `T` acts on such
an array slice by slice through `lift T`. This file proves, for any width `h`, that the tape
passes of the T16 primitives are `lift (colRep k ·)` of their operators after decoding, and that
the fitted T16 program applies `Cfull` (the kernel `C` on every active bit) to every data family.

* Column operators. `tensorColumns_pullOp`: a pull-back `f ↦ f ∘ L` in every column is
  `pullCols L`; translations and the slot XORs are pull-backs (`translation_eq_pullOp`,
  `kernel_two`). `tensorColumns_diag`: a diagonal phase in every column multiplies by the
  product of the column phases; `tensorColumns_unit`: the unit `i^c` in every column is
  `i^(c k)`.
* Tape passes. `view_pullMH`: the tape's change of basis along `L` (`pullMH`, Kenny's
  `NodeZ.pullM` at `h = m`) decodes to `lift (pullCols L)`. `view_phaseZ_slot`: the slot-phase
  pass `phaseZ (signMask e e_x) c` decodes to `lift` of the slot phase in every column.
  `view_unitZ`: multiplying the tape by `i^s` multiplies the decoded array by `i^s`.
* `liftRep`: `T ↦ lift (colRep k T)` as a representation on decoded arrays.
* `fittedArr_cfull`: with every primitive acting through `liftRep`, the fitted program sends
  every data family to `Cfull` of its input, for any contents of the eight private centres.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.T16Arr

open IntegerMultBounds.Networks BinaryPhase IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Certificates.T16 Streams
open IntegerMultBounds.MathlibTM2.M6.T16Node

/-! ### Column operators -/

section Columns

variable {h k : ℕ}

/-- The pull-back of an array along an address map. -/
def pullOp (L : BinaryWalsh.Address h → BinaryWalsh.Address h) :
    Module.End ℂ (BinaryWalsh.Arrays h) where
  toFun f a := f (L a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem translation_eq_pullOp (v : BinaryWalsh.Address h) :
    BinaryWalsh.translation v = pullOp (· + v) := rfl

theorem phase_two : phase (2 : ZMod 4) = -1 := by
  rw [phase, show (2 : ZMod 4).val = 2 from rfl, Complex.I_sq]

/-- The kernel at phase `2` is the translation. -/
theorem kernel_two (v : BinaryWalsh.Address h) :
    BinaryWalsh.kernel 2 v = BinaryWalsh.translation v := by
  apply LinearMap.ext
  intro f
  funext x
  rw [BinaryWalsh.kernel_apply, phase_two]
  change _ = f (x + v)
  ring

theorem liftColumn_pullOp (j : Fin k) (L : BinaryWalsh.Address h → BinaryWalsh.Address h)
    (f : BinaryColumns.Arrays h k) (x : BinaryColumns.Address h k) :
    BinaryColumns.liftColumn j (pullOp L) f x = f (Function.update x j (L (x j))) := rfl

theorem prod_liftColumn_pullOp (L : BinaryWalsh.Address h → BinaryWalsh.Address h)
    (l : List (Fin k)) (hl : l.Nodup) (f : BinaryColumns.Arrays h k)
    (x : BinaryColumns.Address h k) :
    (l.map fun j => BinaryColumns.liftColumn j (pullOp L)).prod f x =
      f (fun c => if c ∈ l then L (x c) else x c) := by
  induction l generalizing x with
  | nil => simp
  | cons j l ih =>
    have hj : j ∉ l := (List.nodup_cons.1 hl).1
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, liftColumn_pullOp,
      ih (List.nodup_cons.1 hl).2]
    congr 1
    funext c
    by_cases hc : c = j
    · subst hc
      simp [hj]
    · by_cases hcl : c ∈ l <;> simp [hc, hcl, Function.update_of_ne hc]

/-- **A pull-back in every column** is `pullCols`. -/
theorem tensorColumns_pullOp (L : BinaryWalsh.Address h → BinaryWalsh.Address h)
    (f : BinaryColumns.Arrays h k) :
    BinaryColumns.tensorColumns k (pullOp L) f = pullCols L f := by
  funext x
  rw [BinaryColumns.tensorColumns, List.ofFn_eq_map,
    prod_liftColumn_pullOp L _ (List.nodup_finRange k)]
  simp [pullCols]

theorem liftColumn_diag (j : Fin k) (ψ : BinaryWalsh.Address h → ZMod 4)
    (f : BinaryColumns.Arrays h k) (x : BinaryColumns.Address h k) :
    BinaryColumns.liftColumn j (phaseDiagonal ψ).toLinearMap f x = phase (ψ (x j)) * f x := by
  change phase (ψ (x j)) * f (Function.update x j (x j)) = _
  rw [Function.update_eq_self]

theorem prod_liftColumn_diag (ψ : BinaryWalsh.Address h → ZMod 4) (l : List (Fin k))
    (f : BinaryColumns.Arrays h k) (x : BinaryColumns.Address h k) :
    (l.map fun j => BinaryColumns.liftColumn j (phaseDiagonal ψ).toLinearMap).prod f x =
      (l.map fun c => phase (ψ (x c))).prod * f x := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, liftColumn_diag, ih,
      List.map_cons, List.prod_cons, mul_assoc]

/-- **A diagonal phase in every column** multiplies by the product of the column phases. -/
theorem tensorColumns_diag (ψ : BinaryWalsh.Address h → ZMod 4) (f : BinaryColumns.Arrays h k)
    (x : BinaryColumns.Address h k) :
    BinaryColumns.tensorColumns k (phaseDiagonal ψ).toLinearMap f x =
      (∏ c, phase (ψ (x c))) * f x := by
  rw [BinaryColumns.tensorColumns, List.ofFn_eq_map, prod_liftColumn_diag, ← List.ofFn_eq_map,
    List.prod_ofFn]

theorem phase_smul_eq_diag (c : ZMod 4) :
    (phase c • LinearMap.id : Module.End ℂ (BinaryWalsh.Arrays h)) =
      (phaseDiagonal fun _ => c).toLinearMap := by
  apply LinearMap.ext
  intro f
  funext x
  rfl

/-- **A unit scalar in every column** is its `k`-th power. -/
theorem tensorColumns_unit (c : ZMod 4) (f : BinaryColumns.Arrays h k)
    (x : BinaryColumns.Address h k) :
    BinaryColumns.tensorColumns k (phase c • LinearMap.id) f x = phase c ^ k * f x := by
  rw [phase_smul_eq_diag, tensorColumns_diag, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

end Columns

/-! ### Tape passes after decoding -/

section Tape

variable {Y : Type} {h k n : ℕ} (e : Fin (h * k) → Fin n)

/-- Column `c` of the active bits. -/
def colBitsH (c : Fin k) (b : Fin n → ZMod 2) : BinaryWalsh.Address h :=
  fun j => b (e (bitIdx j c))

/-- The tape's change of basis along `L` on the active bits (`NodeZ.pullM` at `h = m`). -/
noncomputable def pullMH (L : BinaryWalsh.Address h → BinaryWalsh.Address h) (f : ZArr Y n) :
    ZArr Y n :=
  fun p => f (p.1, merge e p.2 (ofCols fun c => L (colBitsH e c p.2)))

/-- Multiplication of every cell by `i^s`. -/
def unitZ (s : ℕ) (f : ZArr Y n) : ZArr Y n := fun p => (⟨0, 1⟩ : GaussianInt) ^ s * f p

variable {e}

theorem colBitsH_merge (he : Function.Injective e) (r : Fin n → ZMod 2) (a : Fin (h * k) → ZMod 2)
    (c : Fin k) : colBitsH e c (merge e r a) = toCols a c := by
  funext j
  exact merge_apply_of_inj he r a _

/-- **The change of basis** decodes to `lift (pullCols L)`. -/
theorem view_pullMH (he : Function.Injective e) (L : BinaryWalsh.Address h → BinaryWalsh.Address h)
    (g : ZArr Y n) : view e (toC (pullMH e L g)) = lift (pullCols L) (view e (toC g)) := by
  funext ⟨⟨y, r⟩, a⟩
  simp only [view, toC, pullMH, lift, pullCols, colBitsH_merge he, merge_merge]

theorem toComplex_I_pow (s : ℕ) : GaussianInt.toComplex ((⟨0, 1⟩ : GaussianInt) ^ s) = Complex.I ^ s := by
  rw [map_pow]
  congr 1
  apply Complex.ext <;> simp [GaussianInt.toComplex_def]

/-- **The unit pass** multiplies the decoded array by `i^s`. -/
theorem view_unitZ (s : ℕ) (g : ZArr Y n) :
    view e (toC (unitZ s g)) = Complex.I ^ s • view e (toC g) := by
  funext p
  simp only [view, toC, unitZ, map_mul, toComplex_I_pow, Pi.smul_apply, smul_eq_mul]

/-- The `ZMod 4` count of the masked set bits is the sum over the columns. -/
theorem sum_val_signMask (he : Function.Injective e) (u : Fin h → ZMod 2) (x : Fin n → ZMod 2) :
    ∑ t, (((Node.signMask e u t * x t).val : ℕ) : ZMod 4) =
      ∑ c : Fin k, ∑ j : Fin h, (((u j * x (e (bitIdx j c))).val : ℕ) : ZMod 4) := by
  have h1 : ∑ t, (((Node.signMask e u t * x t).val : ℕ) : ZMod 4) =
      ∑ t ∈ Finset.univ.image e, (((Node.signMask e u t * x t).val : ℕ) : ZMod 4) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ ht
    have : Node.signMask e u t = 0 := by
      unfold Node.signMask
      split_ifs with hex
      · obtain ⟨j, c, hjc, _⟩ := hex
        exact absurd (Finset.mem_image.2 ⟨_, Finset.mem_univ _, hjc⟩) ht
      · rfl
    rw [this, zero_mul, ZMod.val_zero, Nat.cast_zero]
  rw [h1, Finset.sum_image (fun a _ b _ hab => he hab), ← Equiv.sum_comp finProdFinEquiv,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show finProdFinEquiv (j, c) = bitIdx j c from rfl, Node.signMask_bitIdx he]

/-- **The slot-phase pass** decodes to the slot phase `i^(c x_x)` in every column. -/
theorem view_phaseZ_slot (he : Function.Injective e) (x : Fin h) (c : ZMod 4) (g : ZArr Y n) :
    view e (toC (Node.phaseZ (Node.signMask e (Pi.single x 1)) c g)) =
      lift (BinaryColumns.tensorColumns k (phaseDiagonal fun a => c * bitLift (a x)).toLinearMap)
        (view e (toC g)) := by
  funext ⟨⟨y, r⟩, a⟩
  simp only [lift]
  rw [tensorColumns_diag]
  simp only [view, toC, Node.phaseZ, map_mul, toComplex_I_pow, ofCols_toCols]
  congr 1
  rw [← phase, Node.phaseExp, sum_val_signMask he, Finset.mul_sum, phase_sum]
  refine Finset.prod_congr rfl fun col _ => ?_
  congr 1
  rw [Finset.sum_eq_single x]
  · simp [bitLift, toCols, merge_apply_of_inj he]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

end Tape

/-! ### The node on decoded arrays -/

section Node

variable {Y : Type} {h k : ℕ}

/-- `lift T` as a linear map on decoded arrays. -/
noncomputable def liftL (T : BinaryColumns.Arrays h k →ₗ[ℂ] BinaryColumns.Arrays h k) :
    Module.End ℂ (Arr Y (h * k)) where
  toFun := lift T
  map_add' f g := by
    funext p
    change T ((fun z => f (p.1, ofCols z)) + (fun z => g (p.1, ofCols z))) (toCols p.2) = _
    rw [map_add]
    rfl
  map_smul' c f := by
    funext p
    change T (c • fun z => f (p.1, ofCols z)) (toCols p.2) = _
    rw [map_smul]
    rfl

variable (Y k)

/-- The decoded-array representation of the 73-bit operators: each acts in every column of every
slice. -/
noncomputable def liftRep : Module.End ℂ (BinaryWalsh.Arrays 73) →* Module.End ℂ (Arr Y (73 * k)) where
  toFun T := liftL (colRep k T)
  map_one' := by
    apply LinearMap.ext
    intro f
    funext p
    change (colRep k 1) (fun z => f (p.1, ofCols z)) (toCols p.2) = f p
    rw [map_one]
    change f (p.1, ofCols (toCols p.2)) = f p
    rw [ofCols_toCols]
  map_mul' T S := by
    apply LinearMap.ext
    intro f
    change lift (colRep k (T * S)) f = lift (colRep k T) (lift (colRep k S) f)
    rw [map_mul, Module.End.coe_mul]
    exact lift_comp (colRep k T) (colRep k S) f

variable {Y k}

/-- **The T16 node on decoded arrays.** With every primitive acting through `liftRep`, the fitted
program sends every data family to `Cfull` of its input, whatever the private centres hold. -/
theorem fittedArr_cfull (y : NodeUnit → Arr Y (73 * k)) (j : Fin 14336) :
    Impl.runM (liftRep Y k) Impl.fittedProgram y (.inl j) = Cfull Y (73 * k) (y (.inl j)) := by
  obtain ⟨r, a, i, hr, ha, hj⟩ := family_streamUnit j
  rw [← hj, Impl.fittedProgram_cAll (liftRep Y k) y hr ha i, cAll_eq_frame]
  exact lift_fullFrame (y (streamUnit r a i))

end Node

/-! ### The primitives without child calls -/

section Prims

variable {Y : Type} {k n : ℕ} (e : Fin (73 * k) → Fin n)

/-- The tape pass of a primitive that makes no child call: the identity for `factor 0`, a
change of basis for translations (`factor 2`, `trans`) and slot XORs, the slot-phase pass, and
`i^(c k)` for the unit `i^c`. -/
noncomputable def tapeZ : Impl.MPrim → ZArr Y n → ZArr Y n
  | .factor q v => if q = 0 then id else pullMH e (· + v)
  | .trans v => pullMH e (· + v)
  | .xor i j => pullMH e fun a => (Impl.xorEquiv i j).symm a
  | .phase i c => Node.phaseZ (Node.signMask e (Pi.single i 1)) c
  | .unit c => unitZ (c.val * k)

variable {e}

theorem liftRep_apply (T : Module.End ℂ (BinaryWalsh.Arrays 73)) (f : Arr Y (73 * k)) :
    liftRep Y k T f = lift (colRep k T) f := rfl

theorem lift_congr {T T' : BinaryColumns.Arrays 73 k → BinaryColumns.Arrays 73 k}
    (hT : ∀ g, T g = T' g) (f : Arr Y (73 * k)) : lift T f = lift T' f := by
  funext p
  simp only [lift, hT]

theorem liftRep_pullOp (L : BinaryWalsh.Address 73 → BinaryWalsh.Address 73) (f : Arr Y (73 * k)) :
    liftRep Y k (pullOp L) f = lift (pullCols L) f := by
  rw [liftRep_apply]
  exact lift_congr (fun g => tensorColumns_pullOp L g) f

/-- **Every primitive without a child call** is, after decoding, its operator acting through
`liftRep`. -/
theorem view_tapeZ (he : Function.Injective e) (p : Impl.MPrim) (hp : p.isChild = false)
    (g : ZArr Y n) :
    view e (toC (tapeZ e p g)) = liftRep (Y × (Fin n → ZMod 2)) k p.lin (view e (toC g)) := by
  cases p with
  | factor q v =>
    have key : ∀ q : ZMod 4, (q.val % 2 == 1) = false → q = 0 ∨ q = 2 := by decide
    have hq : q = 0 ∨ q = 2 := key q (by simpa only [Impl.MPrim.isChild] using hp)
    rcases hq with rfl | rfl
    · rw [tapeZ, if_pos rfl, Impl.MPrim.lin, Impl.kernel_zero_eq, map_one]
      rfl
    · rw [tapeZ, if_neg (by decide), Impl.MPrim.lin, kernel_two, translation_eq_pullOp,
        liftRep_pullOp, view_pullMH he]
  | trans v =>
    rw [tapeZ, Impl.MPrim.lin, kernel_two, translation_eq_pullOp, liftRep_pullOp, view_pullMH he]
  | xor i j =>
    rw [tapeZ, Impl.MPrim.lin, show permOp (Impl.xorEquiv i j) =
      pullOp (fun a => (Impl.xorEquiv i j).symm a) from rfl, liftRep_pullOp, view_pullMH he]
  | phase i c =>
    rw [tapeZ, Impl.MPrim.lin, view_phaseZ_slot he, liftRep_apply]
    rfl
  | unit c =>
    rw [tapeZ, Impl.MPrim.lin, view_unitZ, liftRep_apply]
    funext q
    simp only [lift, Pi.smul_apply, smul_eq_mul]
    change _ = BinaryColumns.tensorColumns k (phase c • LinearMap.id) _ (toCols q.2)
    rw [tensorColumns_unit, phase, ← pow_mul, ofCols_toCols]

end Prims

end IntegerMultBounds.MathlibTM2.M6.T16Arr
