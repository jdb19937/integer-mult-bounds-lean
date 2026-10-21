module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleOp
public import IntegerMultBounds.MathlibTM2.M8.AtomOps

/-!
# The semantics of atom operations on the role bank

The refined coordinates of `AtomOps` number the atoms of `m + m` coordinates of `f` atoms
coordinate-major, `t f + l`; stage 1's field addresses number the `N + N` atoms of the two fields,
H then D, `N = m f`. The two numberings agree (`castE`), so the refined operations of an atom
operation, reindexed (`reidx`), give the levels' coordinate operations of its family loop, and
the loop moves the records of every atom vector by the atom operation (`family_field`, through
`AtomOps.refined_run`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSem

open IntegerMultBounds.Machine
open Networks
open AffineFieldCoordinates (hIndex dIndex)
variable {R : Type*} [CommRing R]
noncomputable section

/-! ### Reindexing -/

/-- An ordered-affine operation with its coordinates renamed. -/
def reidx {A B : ℕ} (σ : Fin A ≃ Fin B) : OrderedAffine.Op (Fin A) R → OrderedAffine.Op (Fin B) R
  | .scale i c => .scale (σ i) c
  | .shift i j c => .shift (σ i) (σ j) c

theorem execute_reidx {A B : ℕ} (σ : Fin A ≃ Fin B) (op : OrderedAffine.Op (Fin A) R) (y : Fin B → R) :
    OrderedAffine.execute (reidx σ op) y = OrderedAffine.execute op (y ∘ σ) ∘ σ.symm := by
  funext z
  obtain ⟨z, rfl⟩ := σ.surjective z
  cases op with
  | scale i c =>
    by_cases h : z = i
    · subst h; simp [reidx, OrderedAffine.execute]
    · have h' : σ z ≠ σ i := fun e => h (σ.injective e)
      simp [reidx, OrderedAffine.execute, Function.update_of_ne h, Function.update_of_ne h']
  | shift i j c =>
    by_cases h : z = i
    · subst h; simp [reidx, OrderedAffine.execute]
    · have h' : σ z ≠ σ i := fun e => h (σ.injective e)
      simp [reidx, OrderedAffine.execute, Function.update_of_ne h, Function.update_of_ne h']

theorem run_reidx {A B : ℕ} (σ : Fin A ≃ Fin B) :
    ∀ (ops : List (OrderedAffine.Op (Fin A) R)) (y : Fin B → R),
      OrderedAffine.run (ops.map (reidx σ)) y = OrderedAffine.run ops (y ∘ σ) ∘ σ.symm
  | [], y => by funext z; simp [OrderedAffine.run]
  | op :: ops, y => by
    change OrderedAffine.run (ops.map (reidx σ)) (OrderedAffine.execute (reidx σ op) y) =
      OrderedAffine.run ops (OrderedAffine.execute op (y ∘ σ)) ∘ σ.symm
    rw [execute_reidx, run_reidx σ ops]
    congr 2
    funext z; simp

/-! ### The two numberings -/

variable {m f : ℕ}

/-- The refined numbering as the two-field numbering. -/
def castE : Fin ((m+m)*f) ≃ Fin (m*f + m*f) := finCongr (by ring)

theorem castE_h (x : Fin (m+m)) (l : Fin f) (hx : x.val < m) :
    castE (AtomOps.«at» x l) = hIndex (⟨x.val*f + l.val, by
      have := l.isLt; nlinarith⟩ : Fin (m*f)) := by
  apply Fin.ext
  simp [castE, AtomOps.«at», finProdFinEquiv_apply_val]; ring

theorem castE_d (x : Fin (m+m)) (l : Fin f) (hx : m ≤ x.val) :
    castE (AtomOps.«at» x l) = dIndex (⟨(x.val-m)*f + l.val, by
      have := l.isLt; have := x.isLt
      have h1 : x.val - m + 1 ≤ m := by omega
      nlinarith⟩ : Fin (m*f)) := by
  apply Fin.ext
  simp only [castE, AtomOps.«at», finCongr_apply, Fin.val_cast, finProdFinEquiv_apply_val, Fin.val_natAdd]
  have : x.val = m + (x.val - m) := by omega
  conv_lhs => rw [this]
  ring

/-! ### A family loop moves atom vectors by its atom operation -/

open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor)
open RecursiveViewRoleBank (Selection)
open RecursiveScalarCoordinates (Address index field)
open AtomRoleOp (execs)

theorem map_range_eq {α : Type*} (f : ℕ) (e : ℕ → α) (g : Fin f → α)
    (h : ∀ l (hl : l < f), e l = g ⟨l, hl⟩) : (List.range f).map e = (List.finRange f).map g := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
  exact h n (by simpa using h1)

/-- **The family's semantics.** If the levels' coordinate operations are the refined operations of
an atom operation, reindexed, the loop moves the records of every atom vector by the atom
operation. -/
theorem family_field {b : ℕ} {t : ℕ} (s : ℕ → Selection (m*f)) (act : RecursiveViewedAction.Action t)
    (v : Descriptor) (hw : v.width = (m*f)*b) (wire : Fin t)
    (e : ℕ → OrderedAffine.Op (Fin (m*f+m*f)) (ZMod (modulus b)))
    (he : ∀ l (data : RecursiveViewedAction.Data t v) (x : Address (m*f) b v),
      RecursiveViewedAction.array (s l) act b v hw data wire (index hw (RecursiveScalarTransport.execute (e l) x)) =
        data wire (index hw x))
    (op : AtomOps.AtomOp (m+m) (ZMod (modulus b))) (hdist : AtomOps.Distinct op)
    (g : Fin f → OrderedAffine.Op (Fin ((m+m)*f)) (ZMod (modulus b)))
    (hop : AtomOps.refined (f := f) op = AtomOps.levels g)
    (heq : ∀ l (hl : l < f), e l = reidx castE (g ⟨l, hl⟩))
    (data : RecursiveViewedAction.Data t v) (x : Address (m*f) b v)
    (X : Fin (m+m) → Fin f → ZMod (modulus b)) (hx : field x ∘ castE = AtomOps.refine X) :
    AtomRoleLoop.datas s act v hw data f wire (index hw (execs e f x)) = data wire (index hw x) ∧
      field (execs e f x) ∘ castE = AtomOps.refine (AtomOps.atomExecute op X) := by
  refine ⟨AtomRoleOp.datas_entry s act v hw wire e he data f x, ?_⟩
  have hmap : (List.finRange f).map (fun i => reidx castE (g i)) = (AtomOps.levels g).map (reidx castE) := by
    simp [AtomOps.levels]
  rw [AtomRoleOp.field_execs, map_range_eq f e (fun i => reidx castE (g i)) heq, hmap, run_reidx, hx, ← hop,
    AtomOps.refined_run op hdist X]
  funext z
  simp

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSem
