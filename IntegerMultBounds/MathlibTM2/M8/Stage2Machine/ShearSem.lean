module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SegmentBits
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Transpose

/-!
# The plain atomwise shears as atom segments

The core's shears `d ← d - h`, `d ← d + h` and `d ← h - d` are atom segments on one coordinate
of `n` atoms per field (`ops₁`, `ops₂`, `ops₃`): a plain cross shift from H into D, and for the
third a scaling of D by `-1` after it. Each changes the tail atoms to `α h + β d`, atom by atom,
for integers `α, β` (`Lin`). On array addresses (`chain_rank`): the chain keeps the head field and
sends the tail field to the code of the atomwise combination (`Stage2Wrapper.enc`), so its address
move is the atomwise shear of `Stage2Wrapper`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.ShearSem

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveScalarCoordinates (Address field)
open FlatCoordinateLayout (rank)
open RevMachine
open RevMachine.AtomRolePlan (Fits)
open RevMachine.AtomRoleSegment (SOp chainAddr)
open RevMachine.AtomRoleSem (castE)
open Stage2Wrapper (enc dec)

/-! ### Digits of a rank -/

section Digits

variable {Q : ℕ} [NeZero Q]

theorem digit_rank {N : ℕ} (y : Fin N → ZMod Q) {j : ℕ} (hj : j < N) :
    (rank y).val / Q ^ j % Q = (y ⟨N - 1 - j, by omega⟩).val := by
  have := FlatCoordinateLayout.coordinate_value y ⟨N - 1 - j, by omega⟩
  simp only [FlatCoordinateLayout.suffixFields] at this
  rwa [show N - 1 - (N - 1 - j) = j by omega] at this

theorem symm_digit {N : ℕ} (y : Fin N → ZMod Q) {j : ℕ} (hj : j < N) :
    (ZMod.finEquiv Q).symm (y ⟨N - 1 - j, by omega⟩) = dec Q N (rank y).val ⟨j, hj⟩ := by
  apply Fin.ext
  rw [FlatCoordinateLayout.finEquiv_symm_val, ← digit_rank y hj]
  unfold dec
  rw [finFunctionFinEquiv_symm_apply_val]
  change (rank y).val / Q ^ j % Q = (rank y).val % Q ^ N / Q ^ j % Q
  rw [Nat.mod_eq_of_lt (rank y).isLt]

/-- The atomwise image of two codes under an operation of `ZMod Q`. -/
def lift (g : ZMod Q → ZMod Q → ZMod Q) (n h d : ℕ) : Fin n → Fin Q :=
  fun j => (ZMod.finEquiv Q).symm (g (ZMod.finEquiv Q (dec Q n h j)) (ZMod.finEquiv Q (dec Q n d j)))

/-- **An atomwise operation of two ranks.** -/
theorem rank_op {N : ℕ} (g : ZMod Q → ZMod Q → ZMod Q) (H D : Fin N → ZMod Q) :
    (rank (fun k => g (H k) (D k))).val = enc Q N (lift g N (rank H).val (rank D).val) := by
  have hQ : 0 < Q := NeZero.pos Q
  apply eq_of_digits hQ N _ _ (rank _).isLt (Stage2Wrapper.enc_lt _)
  intro j hj
  rw [digit_rank _ hj, Stage2Wrapper.enc_digit _ ⟨j, hj⟩, lift, FlatCoordinateLayout.finEquiv_symm_val,
    ← symm_digit H hj, ← symm_digit D hj, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem rank_op' {N n : ℕ} (hN : N = n) (g : ZMod Q → ZMod Q → ZMod Q) (H D : Fin N → ZMod Q) :
    (rank (fun k => g (H k) (D k))).val = enc Q n (lift g n (rank H).val (rank D).val) := by
  subst hN; exact rank_op g H D

/-- The lift of a difference, a sum and a reversed difference. -/
theorem lift_sub (n h d : ℕ) : lift (Q := Q) (fun h d => d - h) n h d = dec Q n d - dec Q n h := by
  funext j
  simp only [lift, Pi.sub_apply]
  rw [show (ZMod.finEquiv Q (dec Q n d j) - ZMod.finEquiv Q (dec Q n h j)) =
    (ZMod.finEquiv Q).toAddEquiv (dec Q n d j - dec Q n h j) from (map_sub _ _ _).symm]
  exact (ZMod.finEquiv Q).symm_apply_apply _

theorem lift_add (n h d : ℕ) : lift (Q := Q) (fun h d => d + h) n h d = dec Q n d + dec Q n h := by
  funext j
  simp only [lift, Pi.add_apply]
  rw [show (ZMod.finEquiv Q (dec Q n d j) + ZMod.finEquiv Q (dec Q n h j)) =
    ZMod.finEquiv Q (dec Q n d j + dec Q n h j) from (RingEquiv.map_add _ _ _).symm]
  exact (ZMod.finEquiv Q).symm_apply_apply _

theorem lift_rsub (n h d : ℕ) : lift (Q := Q) (fun h d => h - d) n h d = dec Q n h - dec Q n d := by
  funext j
  simp only [lift, Pi.sub_apply]
  rw [show (ZMod.finEquiv Q (dec Q n h j) - ZMod.finEquiv Q (dec Q n d j)) =
    (ZMod.finEquiv Q).toAddEquiv (dec Q n h j - dec Q n d j) from (map_sub _ _ _).symm]
  exact (ZMod.finEquiv Q).symm_apply_apply _

end Digits

/-! ### The three segments -/

theorem one_lt : 1 < prime := Networks.Shared50ModularControl.prime_prime.one_lt

theorem neg_one_occurs : Networks.Shared50AffineCoefficients.ScaleOccurs (-1) :=
  Or.inr ⟨by norm_num, by simp [Nat.one_le_two_pow, Networks.coefficientBound],
    by simp [Nat.one_le_two_pow, Networks.coefficientBound]⟩

/-- `d ← d - h`. -/
def ops₁ : List (SOp 1) := [⟨.shift 1 0 (-1), ⟨by decide, by simpa using one_lt⟩⟩]

/-- `d ← d + h`. -/
def ops₂ : List (SOp 1) := [⟨.shift 1 0 1, ⟨by decide, by simpa using one_lt⟩⟩]

/-- `d ← h - d`. -/
def ops₃ : List (SOp 1) :=
  [⟨.shift 1 0 (-1), ⟨by decide, by simpa using one_lt⟩⟩, ⟨.scale 1 (-1), neg_one_occurs⟩]

variable {f b : ℕ}

/-- The segment changes the tail atoms to `g h d`. -/
def Lin (l : List (SOp 1)) (g : ZMod (modulus b) → ZMod (modulus b) → ZMod (modulus b)) : Prop :=
  ∀ X : Fin (1+1) → Fin f → ZMod (modulus b),
    AtomOps.atomRun (l.map fun s => AtomSegment.mapOp (Swap.Modular.ratMod (modulus b)) s.1) X =
      ![X 0, fun k => g (X 0 k) (X 1 k)]

theorem lin₁ : Lin (f := f) (b := b) ops₁ (fun h d => d - h) := by
  intro X
  funext i k
  fin_cases i
  · simp [ops₁, AtomOps.atomRun, AtomOps.atomExecute, AtomSegment.mapOp]
  · simp [ops₁, AtomOps.atomRun, AtomOps.atomExecute, AtomSegment.mapOp, AtomSegment.ratMod_neg_one]; ring

theorem lin₂ : Lin (f := f) (b := b) ops₂ (fun h d => d + h) := by
  intro X
  funext i k
  fin_cases i <;> simp [ops₂, AtomOps.atomRun, AtomOps.atomExecute, AtomSegment.mapOp,
    Swap.Modular.ratMod_one]

theorem lin₃ : Lin (f := f) (b := b) ops₃ (fun h d => h - d) := by
  intro X
  funext i k
  fin_cases i
  · simp [ops₃, AtomOps.atomRun, AtomOps.atomExecute, AtomSegment.mapOp]
  · simp [ops₃, AtomOps.atomRun, AtomOps.atomExecute, AtomSegment.mapOp, AtomSegment.ratMod_neg_one]; ring

/-! ### Addresses -/

local instance (w : ℕ) : NeZero (modulus w) :=
  ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

variable {n w : ℕ} {u : Descriptor}

/-- The atoms of the two fields of an address of one coordinate. -/
def atoms (x : RecursiveScalarCoordinates.Address (1*n) w u) : Fin (1+1) → Fin n → ZMod (modulus w) :=
  ![fun l => x.h (Fin.cast (one_mul n).symm l), fun l => x.d (Fin.cast (one_mul n).symm l)]

theorem field_atoms (x : RecursiveScalarCoordinates.Address (1*n) w u) : field x ∘ castE = AtomOps.refine (atoms x) := by
  funext k
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective k
  change field x (castE (AtomOps.«at» i l)) = AtomOps.refine (atoms x) (AtomOps.«at» i l)
  rw [AtomOps.refine_at]
  fin_cases i
  · rw [AtomRoleSem.castE_h _ _ (by decide), RecursiveScalarCoordinates.field_h]
    simp only [atoms]
    congr 1; apply Fin.ext; simp
  · rw [AtomRoleSem.castE_d _ _ (by decide), RecursiveScalarCoordinates.field_d]
    simp only [atoms]
    congr 1; apply Fin.ext; simp

theorem fields_of {x : RecursiveScalarCoordinates.Address (1*n) w u} {Z : Fin (1+1) → Fin n → ZMod (modulus w)}
    (h : field x ∘ castE = AtomOps.refine Z) :
    x.h = (fun j => Z 0 (Fin.cast (one_mul n) j)) ∧ x.d = (fun j => Z 1 (Fin.cast (one_mul n) j)) := by
  have he := h.symm.trans (field_atoms x)
  have hr : Z = atoms x := by
    funext i l
    have := congrFun he (AtomOps.«at» i l)
    simpa only [AtomOps.refine_at] using this
  subst hr
  constructor <;> funext j <;> simp [atoms]

/-- **The chain on addresses.** A segment changing the tail atoms to `α h + β d` keeps the head
field and sends the tail field to the code of `α h + β d`, atom by atom. -/
theorem chain_rank {l : List (SOp 1)}
    {g : ZMod (modulus w) → ZMod (modulus w) → ZMod (modulus w)} (hl : Lin (f := n) (b := w) l g)
    (hf : 0 < n) (hw : u.width = (1*n)*w) (x : RecursiveScalarCoordinates.Address (1*n) w u) :
    (rank (chainAddr hf l x).h).val = (rank x.h).val ∧
      (rank (chainAddr hf l x).d).val = enc (modulus w) n (lift g n (rank x.h).val (rank x.d).val) := by
  have hc := AtomRoleSegment.chain_field hf hw l x (atoms x) (field_atoms x)
  rw [hl] at hc
  obtain ⟨hh, hd⟩ := fields_of hc
  refine ⟨?_, ?_⟩
  · rw [hh]
    congr 2
  · rw [hd]
    have : (fun j => (![atoms x 0, fun k => g (atoms x 0 k) (atoms x 1 k)]
        : Fin (1+1) → Fin n → ZMod (modulus w)) 1 (Fin.cast (one_mul n) j)) =
        fun j => g (x.h j) (x.d j) := by
      funext j
      simp [atoms]
    rw [this]
    exact rank_op' (one_mul n) g x.h x.d

/-! ### Array moves -/

local instance (w : ℕ) : NeZero (prime ^ w) :=
  ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

theorem encode_injective : Function.Injective (SparseRoleCircuit.encode (a := 0)) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> first | rfl | exact absurd h (by decide)

/-- **The chain's array move.** If the segment changes the tail atoms to `g h d` and `g` lifts to
the atomwise `s`, the chain moves the record of the selected wire at fields `(h, d)` to the fields of
the atomwise shear `d ← s h d`. -/
theorem chain_moves {t : ℕ} {l : List (SOp 1)}
    {g : ZMod (modulus w) → ZMod (modulus w) → ZMod (modulus w)} (hl : Lin (f := n) (b := w) l g)
    {s : Stage2Wrapper.Atoms (prime ^ w) n → Stage2Wrapper.Atoms (prime ^ w) n → Stage2Wrapper.Atoms (prime ^ w) n}
    (hs : ∀ h d, lift g n h d = s (dec (prime ^ w) n h) (dec (prime ^ w) n d))
    (hf : 0 < n) (hw : u.width = (1*n)*w) (wire : Fin t) (data : RecursiveViewedAction.Data t u)
    (X : ℕ → ZMod 2) (hX : ∀ i : Fin (volume prime u), data wire i = SparseRoleCircuit.encode (X i))
    (y : Fin (volume prime u) → ZMod 2)
    (hy : ∀ i, AtomRoleSegment.chainData hf wire u hw l data wire i = SparseRoleCircuit.encode (y i)) :
    Stage2Wrapper.Moves prime u (Stage2Wrapper.shear (prime ^ w) n s) X (FamilyRoot.ext y) := by
  intro a ha row hrow before hb h hh mid hm d hd after haf
  have hQ : prime ^ u.width = (modulus w) ^ (1*n) := by
    rw [hw, mul_comm, pow_mul]; rfl
  let x' : RecursiveScalarCoordinates.Address (1*n) w u :=
    ⟨⟨a, ha⟩, ⟨row, hrow⟩, ⟨before, hb⟩, FlatCoordinateLayout.coordinates ⟨h, hQ ▸ hh⟩, ⟨mid, hm⟩,
      FlatCoordinateLayout.coordinates ⟨d, hQ ▸ hd⟩, ⟨after, haf⟩⟩
  have e1 := AtomRoleSegment.chain_entry hf wire u hw l data x'
  obtain ⟨rh, rd⟩ := chain_rank hl hf hw x'
  have hsp := AtomRoleSegment.spect_chain (b := w) (v := u) hf l x'
  simp only [AtomRoleSegment.spect, Prod.mk.injEq] at hsp
  obtain ⟨s1, s2, s3, s4, s5⟩ := hsp
  have i0 : (RecursiveScalarCoordinates.index hw x').val =
      RecursiveInterchangeLayout.index prime u a row before h mid d after := by
    rw [RecursiveScalarCoordinates.index_val]
    simp [x', FlatCoordinateLayout.rank_coordinates]
  have i1 : (RecursiveScalarCoordinates.index hw (chainAddr hf l x')).val =
      RecursiveInterchangeLayout.index prime u a row before (Stage2Wrapper.shear (prime ^ w) n s (h, d)).1 mid
        (Stage2Wrapper.shear (prime ^ w) n s (h, d)).2 after := by
    rw [RecursiveScalarCoordinates.index_val, rh, rd, s1, s2, s3, s4, s5]
    simp only [x', FlatCoordinateLayout.rank_coordinates, hs]
    rfl
  rw [← i1, Transpose.ext_lt, ← i0]
  apply encode_injective
  rw [← hy, e1, hX]

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.ShearSem
