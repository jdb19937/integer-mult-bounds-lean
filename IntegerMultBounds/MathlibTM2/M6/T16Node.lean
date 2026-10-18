module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.MachineFit
public import IntegerMultBounds.Networks.BinaryColumnFrame

/-!
# The T16 node on the layer machine's column banks

`Impl.fittedProgram` applies `C_all` to every data family, for every representation of the
73-bit operators (`Impl.fittedProgram_cAll`). The layer machine stores a wire as `k` columns of
73-bit arrays, `BinaryColumns.Arrays 73 k`, and its node contract is the full frame
`BinaryColumnFrame.frameEquiv k weightPhase` on every data wire. This file connects the two.

* `frame_charVec`: a Walsh frame scales every character by its phase.
* `cAll_eq_frame`: `C_all` is the full frame `frame weightPhase` at `h = 73`.
* `colRep`: applying a 73-bit operator in every column is a monoid homomorphism.
* `colRep_kernel`: in every column, `kernel q v` is the layer machine's factor
  `vectorFactor k (q, v)`.
* `family_streamUnit`: each of the 14,336 data families is a stream unit.
* `fitted_fullFrame`: the fitted program applies the full frame to every data family of a
  `k`-column bank, whatever the eight private centres hold.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.T16Node

open IntegerMultBounds.Networks BinaryWalsh BinaryPhase
open IntegerMultBounds.Networks.Certificates.T16 Streams Impl

/-! ### The full frame on characters -/

theorem walsh_single {h : ℕ} (u : BinaryWalsh.Address h) :
    walshEquiv h (Pi.single u 1) = charVec u := by
  funext x
  change walsh h (Pi.single u 1) x = chi u x
  rw [walsh_apply, chi_symm]
  simp [Pi.single_apply]

/-- A Walsh frame scales every character by its phase. -/
theorem frame_charVec {h : ℕ} (q : BinaryWalsh.Address h → ZMod 4) (u : BinaryWalsh.Address h) :
    frame q (charVec u) = phase (q u) • charVec u := by
  have hd : phaseDiagonal q (Pi.single u 1 : BinaryWalsh.Arrays h) =
      phase (q u) • (Pi.single u 1 : BinaryWalsh.Arrays h) := by
    funext y
    change phase (q y) * (Pi.single u 1 : BinaryWalsh.Arrays h) y =
      phase (q u) * (Pi.single u 1 : BinaryWalsh.Arrays h) y
    by_cases hy : y = u
    · subst hy
      rfl
    · simp [Pi.single_apply, hy]
  rw [← walsh_single, frame, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, hd, map_smul]

/-- **`C_all` is the full frame** `i^{weight}` at `h = 73`. -/
theorem cAll_eq_frame : cAll = (frame (weightPhase (h := 73))).toLinearMap := by
  apply eq_of_chars
  intro u
  have he : phaseExp stdBasis (fun _ => (1 : ZMod 4)) u = weightPhase u := by
    simp [phaseExp, stdBasis, binary_single, weightPhase]
  rw [cAll, basisOp_char, LinearEquiv.coe_toLinearMap, frame_charVec, he]

/-! ### The column representation -/

/-- A 73-bit operator applied in every column of a `k`-column array. -/
noncomputable def colRep (k : ℕ) :
    Module.End ℂ (BinaryWalsh.Arrays 73) →* Module.End ℂ (BinaryColumns.Arrays 73 k) where
  toFun := BinaryColumns.tensorColumns k
  map_one' := BinaryColumns.tensorColumns_one
  map_mul' := BinaryColumns.tensorColumns_mul

/-- In every column, the kernel `kernel q v` is the layer machine's factor `vectorFactor k (q, v)`. -/
theorem colRep_kernel (k : ℕ) (q : ZMod 4) (v : BinaryWalsh.Address 73) :
    colRep k (kernel q v) = BinaryColumns.vectorFactor k (q, v) := by
  change BinaryColumns.tensorColumns k (kernel q v) = _
  simpa using BinaryColumns.tensorColumns_kernel_prod (k := k) [(q, v)]

/-! ### Families -/

/-- Each of the 14,336 data families is a stream unit. -/
theorem family_streamUnit (j : Fin 14336) :
    ∃ r a : ℕ, ∃ i : Fin 8, r < 16 ∧ a < 112 ∧ streamUnit r a i = .inl j := by
  refine ⟨j.val / 896, j.val % 896 % 112, ⟨j.val % 896 / 112, by omega⟩, by omega, by omega, ?_⟩
  simp only [streamUnit, famIdx, Sum.inl.injEq]
  apply Fin.ext
  simp only
  omega

/-! ### The node -/

/-- **The T16 node on the layer machine's banks.** On a bank of `k`-column arrays, the fitted
program applies the full frame to every data family, whatever the private centres hold. -/
theorem fitted_fullFrame (k : ℕ) (y : NodeUnit → BinaryColumns.Arrays 73 k) (j : Fin 14336) :
    runM (colRep k) fittedProgram y (.inl j) =
      BinaryColumnFrame.frameEquiv k weightPhase (y (.inl j)) := by
  obtain ⟨r, a, i, hr, ha, hj⟩ := family_streamUnit j
  rw [← hj, fittedProgram_cAll (colRep k) y hr ha i, cAll_eq_frame]
  rfl

/-- The fitted program makes `1,041,408` child calls on `14,336` data families. -/
theorem fitted_children : mprogramChildren fittedProgram = 1041408 := fittedProgram_children

end IntegerMultBounds.MathlibTM2.M6.T16Node
