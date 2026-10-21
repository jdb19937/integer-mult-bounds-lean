module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSegment

/-!
# Atom segments move bits

A segment's chain moves the record of every address `x` of the selected wire to the address
`chainAddr x` (`AtomRoleSegment.chain_entry`). Every operation of the chain is invertible: a
shift adds a multiple of another coordinate, and a scaling multiplies by a unit, since its
coefficient occurs (`levelOp_invertible`). So every address is reached (`chainAddr_surjective`),
every cell of the new array is a cell of the old one, and an array of encoded bits stays an array
of encoded bits (`chain_bits`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.SegmentBits

open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveScalarCoordinates (Address index field)
open AtomRolePlan (Fits)
noncomputable section

/-! ### Invertible operations -/

section Ops

variable {ι R : Type*} [LinearOrder ι] [CommRing R]

/-- An ordered-affine operation that is a bijection: a scaling by a unit, or a shift from another
coordinate. -/
def Invertible : OrderedAffine.Op ι R → Prop
  | .scale _ a => IsUnit a
  | .shift i j _ => i ≠ j

theorem execute_surjective {op : OrderedAffine.Op ι R} (h : Invertible op) :
    Function.Surjective (OrderedAffine.execute op) := by
  cases op with
  | scale i a =>
    obtain ⟨u, rfl⟩ := h
    intro y
    refine ⟨Function.update y i (↑u⁻¹ * y i), ?_⟩
    funext k
    by_cases hk : k = i
    · subst hk; simp [OrderedAffine.execute]
    · simp [OrderedAffine.execute, hk]
  | shift i j a =>
    have hij : i ≠ j := h
    intro y
    refine ⟨Function.update y i (y i - a * y j), ?_⟩
    funext k
    by_cases hk : k = i
    · subst hk; simp [OrderedAffine.execute, Function.update_of_ne hij.symm]
    · simp [OrderedAffine.execute, hk]

theorem reidx_invertible {A B : ℕ} (σ : Fin A ≃ Fin B) {op : OrderedAffine.Op (Fin A) R}
    (h : Invertible op) : Invertible (AtomRoleSem.reidx σ op) := by
  cases op with
  | scale i a => exact h
  | shift i j a => exact fun he => h (σ.injective he)

end Ops

/-! ### Addresses -/

section Addresses

variable {N b : ℕ} {v : Descriptor}
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

/-- An address with the spectators of `y` and the field `u`. -/
def withField (y : Address N b v) (u : Fin (N+N) → ZMod (modulus b)) : Address N b v :=
  { y with h := fun i => u (AffineFieldCoordinates.hIndex i), d := fun i => u (AffineFieldCoordinates.dIndex i) }

theorem field_withField (y : Address N b v) (u : Fin (N+N) → ZMod (modulus b)) :
    field (withField y u) = u := by
  funext k
  induction k using Fin.addCases with
  | left k => simp only [field]; rw [Fin.addCases_left]; rfl
  | right k => simp only [field]; rw [Fin.addCases_right]; rfl

/-- Addresses with the same spectators and fields are equal. -/
theorem addr_ext {x y : Address N b v} (h₁ : x.beforeRows = y.beforeRows) (h₂ : x.row = y.row)
    (h₃ : x.before = y.before) (h₄ : x.middle = y.middle) (h₅ : x.after = y.after)
    (hf : field x = field y) : x = y := by
  cases x; cases y
  have hh : ∀ i, field ⟨_, _, _, _, _, _, _⟩ (AffineFieldCoordinates.hIndex i) = _ := fun i => congrFun hf _
  have hd : ∀ i, field ⟨_, _, _, _, _, _, _⟩ (AffineFieldCoordinates.dIndex i) = _ := fun i => congrFun hf _
  simp only [RecursiveScalarCoordinates.field_h, RecursiveScalarCoordinates.field_d] at hh hd
  simp only at h₁ h₂ h₃ h₄ h₅
  subst h₁ h₂ h₃ h₄ h₅
  rw [funext hh, funext hd]

theorem execute_spect (op : OrderedAffine.Op (Fin (N+N)) (ZMod (modulus b))) (x : Address N b v) :
    (RecursiveScalarTransport.execute op x).beforeRows = x.beforeRows ∧
      (RecursiveScalarTransport.execute op x).row = x.row ∧
      (RecursiveScalarTransport.execute op x).before = x.before ∧
      (RecursiveScalarTransport.execute op x).middle = x.middle ∧
      (RecursiveScalarTransport.execute op x).after = x.after := by
  cases op <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem execute_onto {op : OrderedAffine.Op (Fin (N+N)) (ZMod (modulus b))} (h : Invertible op)
    (y : Address N b v) : ∃ x, RecursiveScalarTransport.execute op x = y := by
  obtain ⟨u, hu⟩ := execute_surjective h (field y)
  refine ⟨withField y u, ?_⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := execute_spect op (withField y u)
  exact addr_ext h₁ h₂ h₃ h₄ h₅
    (by rw [RecursiveScalarTransport.field_execute, field_withField, hu])

theorem execs_onto (e : ℕ → OrderedAffine.Op (Fin (N+N)) (ZMod (modulus b))) :
    ∀ L, (∀ l < L, Invertible (e l)) → ∀ y : Address N b v, ∃ x, AtomRoleOp.execs e L x = y
  | 0, _, y => ⟨y, rfl⟩
  | L+1, h, y => by
    obtain ⟨z, hz⟩ := execute_onto (h L (by omega)) y
    obtain ⟨x, hx⟩ := execs_onto e L (fun l hl => h l (by omega)) z
    exact ⟨x, by rw [AtomRoleOp.execs, hx, hz]⟩

/-- Every array index is an address. -/
theorem index_surjective (hw : v.width = N*b) : Function.Surjective (index (m := N) (b := b) (v := v) hw) := by
  intro y
  have hM : (modulus b)^N = prime ^ v.width := by
    rw [RecursiveScalarCoordinates.power, hw, Nat.mul_comm]
  have hy : y.val < v.beforeRows * v.rows * v.beforeH * prime ^ v.width * v.between * prime ^ v.width *
      v.afterD := y.isLt
  have hpos : 0 < v.beforeRows * v.rows * v.beforeH * prime ^ v.width * v.between * prime ^ v.width *
      v.afterD := by omega
  have hE := Nat.pos_of_mul_pos_left hpos
  have h6 := Nat.pos_of_mul_pos_right hpos
  have hD := Nat.pos_of_mul_pos_left h6
  have h5 := Nat.pos_of_mul_pos_right h6
  have hC := Nat.pos_of_mul_pos_left h5
  have h4 := Nat.pos_of_mul_pos_right h5
  have hH := Nat.pos_of_mul_pos_left h4
  have h3 := Nat.pos_of_mul_pos_right h4
  have hB := Nat.pos_of_mul_pos_left h3
  have h2 := Nat.pos_of_mul_pos_right h3
  have hR := Nat.pos_of_mul_pos_left h2
  have y1 := (Nat.div_lt_iff_lt_mul hE).mpr hy
  have y2 := (Nat.div_lt_iff_lt_mul hD).mpr y1
  have y3 := (Nat.div_lt_iff_lt_mul hC).mpr y2
  have y4 := (Nat.div_lt_iff_lt_mul hH).mpr y3
  have y5 := (Nat.div_lt_iff_lt_mul hB).mpr y4
  have y6 := (Nat.div_lt_iff_lt_mul hR).mpr y5
  refine ⟨⟨⟨y.val / v.afterD / prime ^ v.width / v.between / prime ^ v.width / v.beforeH / v.rows, y6⟩,
    ⟨y.val / v.afterD / prime ^ v.width / v.between / prime ^ v.width / v.beforeH % v.rows, Nat.mod_lt _ hR⟩,
    ⟨y.val / v.afterD / prime ^ v.width / v.between / prime ^ v.width % v.beforeH, Nat.mod_lt _ hB⟩,
    FlatCoordinateLayout.coordinates
      ⟨y.val / v.afterD / prime ^ v.width / v.between % prime ^ v.width, by rw [hM]; exact Nat.mod_lt _ hH⟩,
    ⟨y.val / v.afterD / prime ^ v.width % v.between, Nat.mod_lt _ hC⟩,
    FlatCoordinateLayout.coordinates ⟨y.val / v.afterD % prime ^ v.width, by rw [hM]; exact Nat.mod_lt _ hD⟩,
    ⟨y.val % v.afterD, Nat.mod_lt _ hE⟩⟩, ?_⟩
  apply Fin.ext
  rw [RecursiveScalarCoordinates.index_val]
  simp only [FlatCoordinateLayout.rank_coordinates, RecursiveInterchangeLayout.index]
  simp only [Nat.div_add_mod']

end Addresses

/-! ### The chain -/

section Chain

variable {m f : ℕ}

theorem at_ne {n : ℕ} {x y : Fin n} {l l' : Fin f} (h : x ≠ y) : AtomOps.«at» x l ≠ AtomOps.«at» y l' := by
  intro he
  have := congrArg finProdFinEquiv.symm he
  simp only [AtomOps.«at», Equiv.symm_apply_apply, Prod.mk.injEq] at this
  exact h this.1

/-- An occurring scale is a unit at every prime power. -/
theorem scale_unit {c : ℚ} (hc : Shared50AffineCoefficients.ScaleOccurs c) (b : ℕ) :
    IsUnit (Swap.Modular.ratMod (modulus b) c) := by
  obtain ⟨-, -, hn, hd, he⟩ := Shared50AffineCoefficients.unit_recipe hc b
  have h1 := he 1
  rw [mul_one, mul_one] at h1
  change IsUnit (Swap.Modular.ratMod (prime ^ b) c)
  rw [h1]
  have hdu : IsUnit (c.den : ZMod (prime ^ b)) := (ZMod.isUnit_iff_coprime _ _).mpr hd
  refine IsUnit.mul ?_ (IsUnit.mul ((ZMod.isUnit_iff_coprime _ _).mpr hn)
    (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans (ZMod.mul_inv_of_unit _ hdu))))
  split_ifs
  · exact isUnit_one
  · exact isUnit_one.neg

theorem levelOp_invertible (b : ℕ) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) (l : Fin f) :
    Invertible (AtomRolePlan.levelOp b op l) := by
  cases op with
  | scale tt c => exact scale_unit hop b
  | shift tt k c => exact at_ne (show tt ≠ k from fun h => by have := hop.1; rw [h] at this; exact lt_irrefl _ this)
  | revShift tt k c => exact at_ne (show tt ≠ k from fun h => by have := hop.1; have := hop.2.1; rw [h] at *; omega)

theorem coord_invertible {b : ℕ} (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) (l : ℕ)
    (hl : l < f) : Invertible (AtomRolePlan.coord b hf op hop l) := by
  rw [AtomRolePlan.coord_reidx hf op hop l hl]
  exact reidx_invertible _ (levelOp_invertible b op hop _)

theorem chainAddr_surjective {b : ℕ} {v : Descriptor} (hf : 0 < f) :
    ∀ (l : List (AtomRoleSegment.SOp m)) (y : Address (m*f) b v), ∃ x, AtomRoleSegment.chainAddr hf l x = y
  | [], y => ⟨y, rfl⟩
  | s :: l, y => by
    obtain ⟨z, hz⟩ := chainAddr_surjective hf l y
    obtain ⟨x, hx⟩ := execs_onto (AtomRolePlan.coord b hf s.1 s.2) f
      (fun l hl => coord_invertible hf s.1 s.2 l hl) z
    exact ⟨x, by rw [AtomRoleSegment.chainAddr, hx, hz]⟩

/-- An array of encoded bits. -/
def Bits {n : ℕ} (a : Fin n → Fin 4) : Prop := ∀ i, ∃ z : ZMod 2, a i = SparseRoleCircuit.encode z

/-- **The chain moves bits.** -/
theorem chain_bits {t b : ℕ} (hf : 0 < f) (wire : Fin t) (v : Descriptor) (hw : v.width = (m*f)*b)
    (l : List (AtomRoleSegment.SOp m)) (data : RecursiveViewedAction.Data t v) (hb : Bits (data wire)) :
    Bits (AtomRoleSegment.chainData hf wire v hw l data wire) := by
  intro i
  obtain ⟨y, rfl⟩ := index_surjective hw i
  obtain ⟨x, rfl⟩ := chainAddr_surjective (b := b) (v := v) hf l y
  rw [AtomRoleSegment.chain_entry hf wire v hw l data x]
  exact hb _

end Chain

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.SegmentBits
