module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSem
public import IntegerMultBounds.MathlibTM2.M8.AtomSegment

/-!
# The plans of atom operations on the role bank

An atom operation of a field segment on fields of `m` coordinates of `f` atoms (`AtomOps.AtomOp`)
runs as one of the three level families of `AtomRoleOp`: a scaling as a cross family on its own
atoms, a shift within a field as a within family, a shift from H into D as a cross family, and a
reversed shift from H into D as a reversed family (`kind`). Each level moves the selected wire's
records by stage 1's transport (`coord_entry`), and the levels' coordinate operations are the
refined operations of the atom operation, reindexed (`coord_reidx`), so the family moves the
records of every atom vector by the atom operation (`plan_field`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRolePlan

open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewRoleBank (Selection)
open RecursiveScalarCoordinates (Address index field)
open RecursiveScalarSelection (first second)
open AffineFieldCoordinates (hIndex dIndex)
open AtomRoleOp (crossFamily withinFamily revFamily execs)
open AtomRoleLoop (datas)
open AtomRoleSem (castE reidx)
variable {t : ℕ}
noncomputable section

/-! ### Level families -/

/-- A level family: its first positions and their bounds. -/
inductive Kind (f N : ℕ) where
  | cross (i₀ j₀ : ℕ) (hi : i₀ + (f-1) < N) (hj : j₀ + (f-1) < N)
  | within (g : RecursiveAffineDimensions.Group) (j₀ i₀ : ℕ) (hji : j₀ < i₀) (hi : i₀ + (f-1) < N)
  | rev (i₀ j₀ : ℕ) (hi0 : f-1 ≤ i₀) (hi : i₀ < N) (hj : j₀ + (f-1) < N)

/-- The selections of a level family. -/
def Kind.sel {f N : ℕ} : Kind f N → ℕ → Selection N
  | .cross i₀ j₀ hi hj => crossFamily f i₀ j₀ hi hj
  | .within g j₀ i₀ hji hi => withinFamily f g j₀ i₀ hji hi
  | .rev i₀ j₀ hi0 hi hj => revFamily f i₀ j₀ hi0 hi hj

section Values

variable {f N : ℕ} (l : ℕ)

theorem cross_first (i₀ j₀ : ℕ) (hi : i₀ + (f-1) < N) (hj : j₀ + (f-1) < N) :
    (first (crossFamily f i₀ j₀ hi hj l)).val = i₀ + min l (f-1) := rfl
theorem cross_second (i₀ j₀ : ℕ) (hi : i₀ + (f-1) < N) (hj : j₀ + (f-1) < N) :
    (second (crossFamily f i₀ j₀ hi hj l)).val = N + (j₀ + min l (f-1)) := rfl
theorem within_first_h (j₀ i₀ : ℕ) (hji : j₀ < i₀) (hi : i₀ + (f-1) < N) :
    (first (withinFamily f .h j₀ i₀ hji hi l)).val = j₀ + min l (f-1) := rfl
theorem within_second_h (j₀ i₀ : ℕ) (hji : j₀ < i₀) (hi : i₀ + (f-1) < N) :
    (second (withinFamily f .h j₀ i₀ hji hi l)).val = i₀ + min l (f-1) := rfl
theorem within_first_d (j₀ i₀ : ℕ) (hji : j₀ < i₀) (hi : i₀ + (f-1) < N) :
    (first (withinFamily f .d j₀ i₀ hji hi l)).val = N + (j₀ + min l (f-1)) := rfl
theorem within_second_d (j₀ i₀ : ℕ) (hji : j₀ < i₀) (hi : i₀ + (f-1) < N) :
    (second (withinFamily f .d j₀ i₀ hji hi l)).val = N + (i₀ + min l (f-1)) := rfl
theorem rev_first (i₀ j₀ : ℕ) (hi0 : f-1 ≤ i₀) (hi : i₀ < N) (hj : j₀ + (f-1) < N) :
    (first (revFamily f i₀ j₀ hi0 hi hj l)).val = i₀ - min l (f-1) := rfl
theorem rev_second (i₀ j₀ : ℕ) (hi0 : f-1 ≤ i₀) (hi : i₀ < N) (hj : j₀ + (f-1) < N) :
    (second (revFamily f i₀ j₀ hi0 hi hj l)).val = N + (j₀ + min l (f-1)) := rfl

end Values

/-! ### The plan of an atom operation -/

variable {m f : ℕ}

/-- Atom operations the role bank runs: scalings with occurring coefficients, ordered shifts, and
reversed shifts from H into D. -/
def Fits (m : ℕ) : AtomOps.AtomOp (m+m) ℚ → Prop
  | .scale _ c => Shared50AffineCoefficients.ScaleOccurs c
  | .shift t k c => k < t ∧ c.den < prime
  | .revShift t k c => k.val < m ∧ m ≤ t.val ∧ c.den < prime

theorem pos_lt {x : ℕ} (hx : x < m) (hf : 0 < f) : x*f + (f-1) < m*f := by
  have := Nat.mul_le_mul_right f (show x + 1 ≤ m from hx)
  rw [Nat.succ_mul] at this
  omega

theorem pos_lt_d (x : Fin (m+m)) (hx : m ≤ x.val) (hf : 0 < f) : (x.val-m)*f + (f-1) < m*f :=
  pos_lt (by omega) hf

/-- The level family of an atom operation. -/
def kind (hf : 0 < f) : (op : AtomOps.AtomOp (m+m) ℚ) → Fits m op → Kind f (m*f)
  | .scale t _, _ =>
    if h : t.val < m then .cross (t.val*f) (t.val*f) (pos_lt h hf) (pos_lt h hf)
    else .cross ((t.val-m)*f) ((t.val-m)*f) (pos_lt_d t (by omega) hf) (pos_lt_d t (by omega) hf)
  | .shift t k _, hop =>
    if ht : t.val < m then
      .within .h (k.val*f) (t.val*f) (Nat.mul_lt_mul_of_pos_right hop.1 hf) (pos_lt ht hf)
    else if hk : k.val < m then .cross (k.val*f) ((t.val-m)*f) (pos_lt hk hf) (pos_lt_d t (by omega) hf)
    else .within .d ((k.val-m)*f) ((t.val-m)*f)
      (Nat.mul_lt_mul_of_pos_right (by have : k.val < t.val := hop.1; omega) hf) (pos_lt_d t (by omega) hf)
  | .revShift t k _, hop =>
    .rev (k.val*f + (f-1)) ((t.val-m)*f) (by omega) (by have := pos_lt hop.1 hf; omega)
      (pos_lt_d t hop.2.1 hf)

/-- The viewed action of an atom operation on `wire`. -/
def act (wire : Fin t) : (op : AtomOps.AtomOp (m+m) ℚ) → Fits m op → RecursiveViewedAction.Action t
  | .scale tt c, hop => .scale wire c hop (if tt.val < m then .h else .d)
  | .shift _ _ c, hop => .shift wire c hop.2
  | .revShift _ _ c, hop => .shift wire c hop.2.2

/-- The coordinate operation of a level. -/
def coord (b : ℕ) (hf : 0 < f) : (op : AtomOps.AtomOp (m+m) ℚ) → Fits m op → ℕ →
    OrderedAffine.Op (Fin (m*f+m*f)) (ZMod (modulus b))
  | .scale tt c, hop, l =>
    if tt.val < m then .scale (first ((kind hf (.scale tt c) hop).sel l)) (Swap.Modular.ratMod (modulus b) c)
    else .scale (second ((kind hf (.scale tt c) hop).sel l)) (Swap.Modular.ratMod (modulus b) c)
  | op, hop, l => .shift (second ((kind hf op hop).sel l)) (first ((kind hf op hop).sel l))
      (Swap.Modular.ratMod (modulus b) (match op with | .scale _ c => c | .shift _ _ c => c | .revShift _ _ c => c))

/-- **One level's transport.** -/
theorem coord_entry {b : ℕ} (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) (wire : Fin t)
    (v : Descriptor) (hw : v.width = (m*f)*b) (l : ℕ) (data : RecursiveViewedAction.Data t v)
    (x : Address (m*f) b v) :
    RecursiveViewedAction.array ((kind hf op hop).sel l) (act wire op hop) b v hw data wire
      (index hw (RecursiveScalarTransport.execute (coord b hf op hop l) x)) = data wire (index hw x) := by
  cases op with
  | scale tt c =>
    by_cases h : tt.val < m
    · simp only [coord, kind, act, h, ite_true, Kind.sel]
      exact RecursiveScalarTransport.scale_first_entry wire _ _ c hop hw data x
    · simp only [coord, kind, act, h, ite_false, Kind.sel]
      exact RecursiveScalarTransport.scale_second_entry _ wire c hop hw data x
  | shift tt k c => exact RecursiveScalarTransport.shift_entry _ wire c hop.2 hw data x
  | revShift tt k c => exact RecursiveScalarTransport.shift_entry _ wire c hop.2.2 hw data x

/-! ### The levels are the refined operations -/

theorem castE_val (x : Fin (m+m)) (l : Fin f) : (castE (AtomOps.«at» x l)).val = x.val*f + l.val := by
  simp [castE, AtomOps.«at», finProdFinEquiv_apply_val]; ring

theorem d_val (x : Fin (m+m)) (hx : m ≤ x.val) : m*f + (x.val-m)*f = x.val*f := by
  rw [← Nat.add_mul]; congr 1; omega

/-- The coordinates of the levels' refined operations. -/
def levelOp (b : ℕ) : AtomOps.AtomOp (m+m) ℚ → Fin f → OrderedAffine.Op (Fin ((m+m)*f)) (ZMod (modulus b))
  | .scale tt c, l => .scale (AtomOps.«at» tt l) (Swap.Modular.ratMod (modulus b) c)
  | .shift tt k c, l => .shift (AtomOps.«at» tt l) (AtomOps.«at» k l) (Swap.Modular.ratMod (modulus b) c)
  | .revShift tt k c, l => .shift (AtomOps.«at» tt l) (AtomOps.«at» k l.rev) (Swap.Modular.ratMod (modulus b) c)

theorem refined_levels (b : ℕ) (op : AtomOps.AtomOp (m+m) ℚ) :
    AtomOps.refined (f := f) (AtomSegment.mapOp (Swap.Modular.ratMod (modulus b)) op) =
      AtomOps.levels (levelOp b op) := by
  cases op <;> rfl

theorem coord_reidx {b : ℕ} (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) (l : ℕ)
    (hl : l < f) : coord b hf op hop l = reidx castE (levelOp b op ⟨l, hl⟩) := by
  have e0 : min l (f-1) = l := by omega
  have hv : (⟨l, hl⟩ : Fin f).rev.val = f - 1 - l := by simp [Fin.val_rev]; omega
  cases op with
  | scale tt c =>
    by_cases h : tt.val < m
    · simp only [coord, kind, h, ite_true, dite_true, Kind.sel, levelOp, reidx]
      congr 1; apply Fin.ext; rw [castE_val, cross_first]; simp only [e0]
    · have hd := d_val (f := f) tt (by omega)
      simp only [coord, kind, h, ite_false, dite_false, Kind.sel, levelOp, reidx]
      congr 1; apply Fin.ext; rw [castE_val, cross_second]; simp only [e0]; omega
  | shift tt k c =>
    have hk : k.val < tt.val := hop.1
    by_cases ht : tt.val < m
    · simp only [coord, kind, ht, dite_true, Kind.sel, levelOp, reidx]
      congr 1 <;> apply Fin.ext
      · rw [castE_val, within_second_h]; simp only [e0]
      · rw [castE_val, within_first_h]; simp only [e0]
    · have hd := d_val (f := f) tt (by omega)
      by_cases hkm : k.val < m
      · simp only [coord, kind, ht, hkm, dite_true, dite_false, Kind.sel, levelOp, reidx]
        congr 1 <;> apply Fin.ext
        · rw [castE_val, cross_second]; simp only [e0]; omega
        · rw [castE_val, cross_first]; simp only [e0]
      · have hd' := d_val (f := f) k (by omega)
        simp only [coord, kind, ht, hkm, dite_false, Kind.sel, levelOp, reidx]
        congr 1 <;> apply Fin.ext
        · rw [castE_val, within_second_d]; simp only [e0]; omega
        · rw [castE_val, within_first_d]; simp only [e0]; omega
  | revShift tt k c =>
    have hd := d_val (f := f) tt hop.2.1
    simp only [coord, kind, Kind.sel, levelOp, reidx]
    congr 1 <;> apply Fin.ext
    · rw [castE_val, rev_second]; simp only [e0]; omega
    · rw [castE_val, rev_first, hv]; simp only [e0]; omega

theorem fits_distinct (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) {S : Type*} (g : ℚ → S) :
    AtomOps.Distinct (AtomSegment.mapOp g op) := by
  cases op with
  | scale => trivial
  | shift tt k c => exact (show k < tt from hop.1).ne
  | revShift tt k c =>
    intro h; have := congrArg Fin.val h; have := hop.1; have := hop.2.1; omega

/-- **The plan's semantics.** The level family of an atom operation moves the selected wire's
records of every atom vector by the atom operation. -/
theorem plan_field {b : ℕ} (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) (wire : Fin t)
    (v : Descriptor) (hw : v.width = (m*f)*b) (data : RecursiveViewedAction.Data t v)
    (x : Address (m*f) b v) (X : Fin (m+m) → Fin f → ZMod (modulus b))
    (hx : field x ∘ castE = AtomOps.refine X) :
    datas (kind hf op hop).sel (act wire op hop) v hw data f wire (index hw (execs (coord b hf op hop) f x)) =
        data wire (index hw x) ∧
      field (execs (coord b hf op hop) f x) ∘ castE =
        AtomOps.refine (AtomOps.atomExecute (AtomSegment.mapOp (Swap.Modular.ratMod (modulus b)) op) X) :=
  AtomRoleSem.family_field _ _ v hw wire _ (coord_entry hf op hop wire v hw) _ (fits_distinct op hop _)
    (levelOp b op) (refined_levels b op) (coord_reidx hf op hop) data x X hx

/-- The plan changes no other wire. -/
theorem plan_other {b : ℕ} (hf : 0 < f) (op : AtomOps.AtomOp (m+m) ℚ) (hop : Fits m op) (wire : Fin t)
    (v : Descriptor) (hw : v.width = (m*f)*b) (data : RecursiveViewedAction.Data t v) (other : Fin t)
    (hne : other ≠ wire) :
    datas (kind hf op hop).sel (act wire op hop) v hw data f other = data other :=
  AtomRoleOp.datas_other _ _ v hw wire
    (fun l d o ho => AtomRoleOp.array_other _ _ v hw wire (by cases op <;> rfl) d o ho) data other hne f

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRolePlan
