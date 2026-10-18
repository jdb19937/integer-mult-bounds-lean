module

public import IntegerMultBounds.MathlibTM2.Layer.Enc
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

/-!
# The recursive layer on Gaussian-integer arrays

`layerZ u ds R₀ j e` is the function the layer machine computes on an array with `W ^ j R₀` rows: at
level `0` it applies the doubled kernel `k2` to each of the `u` active bits `e`; at level `j + 1`
the `m · bits u j` active bits are split into `m` slots, the rows into the `W = 14336` data roles
`u = W g + i`, and the scaled node `nodeM` runs with the level-`j` layer as the child on every slot.

`layerZ_correct`: on `rowsAt R₀ j = W ^ j R₀` rows the layer is `2 ^ expZ` times `C` on every
active bit.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks ComplexFramedExecution

/-- The number of data roles: the families of the node. -/
@[irreducible] def NW : ℕ := 14336

theorem NW_eq : NW = 14336 := by unfold NW; rfl

instance : NeZero NW := ⟨by rw [NW_eq]; decide⟩

/-- The number of bank wires: the families and the private centres. -/
@[irreducible] def NB : ℕ := Fintype.card NWire

theorem NB_card : NB = Fintype.card NWire := by unfold NB; rfl

theorem NB_eq : NB = 14344 := by
  rw [NB_card]; simp [NWire, Networks.Certificates.T16.Streams.NodeUnit]

/-- Data family of a role index. -/
def wireOf : Fin NW ≃ DWire := finCongr NW_eq

/-- Active bits at level `j` with `u` bits per leaf. -/
def bits (u : ℕ) : ℕ → ℕ
  | 0 => u
  | j + 1 => m * bits u j

/-- The exponent of the level-`j` layer. -/
noncomputable def expZ (u : ℕ) (ds : Directions) : ℕ → ℕ
  | 0 => u
  | j + 1 => nodeExp ds (expZ u ds j)

variable {R r n : ℕ}

/-- Doubled kernels on a list of bits, the first bit first. -/
def k2s : List (Fin n) → ZArr (Fin R × Fin r) n → ZArr (Fin R × Fin r) n
  | [], f => f
  | t :: ts, f => k2s ts (k2 t f)

/-- An array with `W R'` rows as a bank-indexed array: row `W g + i` is row `g` of wire
`wireOf i`. -/
noncomputable def toBank (R' : ℕ) (Z : ZArr (Fin (NW * R') × Fin r) n) : ZArr ((Fin R' × Fin r) × DWire) n :=
  fun p => roleArr NW R' (wireOf.symm p.1.2) Z (p.1.1, p.2)

/-- The inverse of `toBank`. -/
noncomputable def ofBank (R' : ℕ) (f : ZArr ((Fin R' × Fin r) × DWire) n) : ZArr (Fin (NW * R') × Fin r) n :=
  unroles NW R' (fun i p => f ((p.1, wireOf i), p.2))

/-- Rows at level `j`: `NW ^ j * R₀`, split definitionally into `NW` roles. -/
noncomputable def rowsAt (R₀ : ℕ) : ℕ → ℕ
  | 0 => R₀
  | j + 1 => NW * rowsAt R₀ j

theorem rowsAt_eq (R₀ j : ℕ) : rowsAt R₀ j = NW ^ j * R₀ := by
  induction j with
  | zero => simp [rowsAt]
  | succ j ih => rw [rowsAt, ih, pow_succ]; ring

/-- The layer at level `j` on an array with `rowsAt R₀ j` rows. -/
noncomputable def layerZ (u : ℕ) (ds : Directions) (R₀ : ℕ) :
    (j : ℕ) → (Fin (bits u j) → Fin n) → ZArr (Fin (rowsAt R₀ j) × Fin r) n →
      ZArr (Fin (rowsAt R₀ j) × Fin r) n
  | 0, e, f => k2s ((List.finRange u).map e) f
  | j + 1, e, f =>
      ofBank (rowsAt R₀ j) (nodeM (k := bits u j) e
        (fun s => layerZ u ds R₀ j (fun c => e (bitIdx s c))) (expZ u ds j) ds (toBank (rowsAt R₀ j) f))

/-- The doubled kernels on a list are `2 ^ length` times the kernels, the last bit outermost. -/
lemma toC_k2s (l : List (Fin n)) (f : ZArr (Fin R × Fin r) n) :
    toC (k2s l f) = (2 : ℂ) ^ l.length • (l.reverse.map (kBit 1)).prod (toC f) := by
  induction l generalizing f with
  | nil => simp [k2s]
  | cons t ts ih =>
    rw [k2s, ih, toC_k2, map_smul, smul_smul, List.reverse_cons, List.map_append, List.prod_append]
    simp [pow_succ]

/-- Kernels commute, so the order of a product of kernels does not matter. -/
lemma prod_reverse_kBit {X : Type} (l : List (Fin n)) :
    (l.reverse.map (kBit (X := X) 1)).prod = (l.map (kBit 1)).prod :=
  ((List.reverse_perm l).map _).prod_eq' (pairwise_commute_kBit 1 l.reverse)

/-- A product of kernels passes through the bank reindexing: if `g` is `c` times the kernels on
the bank form of `f`, then `ofBank g` is `c` times the kernels on `f`. -/
lemma toC_ofBank (R' k : ℕ) (e : Fin k → Fin n) (c : ℂ) (f : ZArr (Fin (NW * R') × Fin r) n)
    (g : ZArr ((Fin R' × Fin r) × DWire) n)
    (hg : toC g = c • ((List.finRange k).map fun i => kBit 1 (e i)).prod (toC (toBank R' f))) :
    toC (ofBank R' g) = c • ((List.finRange k).map fun i => kBit 1 (e i)).prod (toC f) := by
  have hl : ((List.finRange k).map fun i => kBit 1 (e i)) =
      ((List.finRange k).map e).map (kBit (X := (Fin R' × Fin r) × DWire) 1) := by
    rw [List.map_map]; rfl
  have hl' : ((List.finRange k).map fun i => kBit 1 (e i)) =
      ((List.finRange k).map e).map (kBit (X := Fin (NW * R') × Fin r) 1) := by
    rw [List.map_map]; rfl
  rw [hl] at hg
  rw [hl']
  let φ : Fin (NW * R') × Fin r → (Fin R' × Fin r) × DWire := fun z =>
    ((⟨z.1 / NW, Nat.div_lt_of_lt_mul z.1.2⟩, z.2), wireOf (roleSel NW z.1))
  have h2 : (fun q : (Fin (NW * R') × Fin r) × (Fin n → ZMod 2) => toC (toBank R' f) (φ q.1, q.2)) =
      toC f := by
    funext ⟨⟨u, a⟩, b⟩
    simp only [toC, toBank, roleArr, φ, Equiv.symm_apply_apply, roleSel]
    congr
    exact Nat.div_add_mod _ _
  funext p
  have h1 : toC (ofBank R' g) p = toC g (φ p.1, p.2) := rfl
  rw [h1, hg, Pi.smul_apply, Pi.smul_apply, ← h2]
  exact congrArg (c • ·) (congrFun (prod_respec φ 1 _ (toC (toBank R' f))) p)

/-- The layer computes `2 ^ expZ` times `C` on every active bit. -/
theorem layerZ_correct (u : ℕ) (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) (R₀ j : ℕ)
    (e : Fin (bits u j) → Fin n) (he : Function.Injective e) (f : ZArr (Fin (rowsAt R₀ j) × Fin r) n) :
    toC (layerZ u ds R₀ j e f) =
      (2 : ℂ) ^ expZ u ds j • ((List.finRange (bits u j)).map fun i => kBit 1 (e i)).prod (toC f) := by
  induction j with
  | zero =>
    have key : ∀ e' : Fin u → Fin n, toC (k2s ((List.finRange u).map e') f) =
        (2 : ℂ) ^ u • ((List.finRange u).map fun i => kBit 1 (e' i)).prod (toC f) := by
      intro e'
      rw [toC_k2s, prod_reverse_kBit, List.length_map, List.length_finRange, List.map_map]
      rfl
    exact key e
  | succ j ih =>
    refine toC_ofBank (rowsAt R₀ j) (m * bits u j) e _ f _ ?_
    refine nodeM_correct (k := bits u j) e he ds hd _ (expZ u ds j) (fun s g => ?_) _
    exact ih (fun c => e (bitIdx s c))
      (he.comp fun c c' h => (bitIdx_inj.1 h).2) g

end IntegerMultBounds.MathlibTM2.Layer
