module

public import IntegerMultBounds.MathlibTM2.Layer.NodeRSharp
public import IntegerMultBounds.MathlibTM2.Layer.TopZ

/-!
# The recursive layer with rounded children

`layerR` is `layerZ` with every child's result divided by the child's scale (truncating toward
zero) before the node uses it, and nodes with `Tc = 0`. The scale of level `j + 1` is the gate
count `nodeExp ds 0` at every level (`scaleR`), instead of the compounding `expZ`.

`layerR_err`: in the `ℓ²` norm, the layer at level `j` is within `errL j` of `2^(scaleR j)` times
`C` on its active bits. Each level adds the truncation of its children (at most `√2` per entry)
and the child errors divided by their scale, propagated through the node by `errRun`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks ComplexFramedExecution

variable {r n : ℕ}

/-- The scale of the rounded layer at level `j`. -/
noncomputable def scaleR (u : ℕ) (ds : Directions) : ℕ → ℕ
  | 0 => u
  | _ + 1 => nodeExp ds 0

/-- Truncate every entry of an array by `2^s`. -/
def tdivArr {Y : Type} (s : ℕ) (f : ZArr Y n) : ZArr Y n := fun p => tdivZ s (f p)

/-- The layer at level `j` with rounded children. -/
noncomputable def layerR (u : ℕ) (ds : Directions) (R₀ : ℕ) :
    (j : ℕ) → (Fin (bits u j) → Fin n) → ZArr (Fin (rowsAt R₀ j) × Fin r) n →
      ZArr (Fin (rowsAt R₀ j) × Fin r) n
  | 0, e, f => k2s ((List.finRange u).map e) f
  | j + 1, e, f =>
      ofBank (rowsAt R₀ j) (nodeM (k := bits u j) e
        (fun s g => tdivArr (scaleR u ds j) (layerR u ds R₀ j (fun c => e (bitIdx s c)) g)) 0 ds
        (toBank (rowsAt R₀ j) f))

/-- The error bound of the rounded layer. -/
noncomputable def errL (u : ℕ) (ds : Directions) (R₀ r n : ℕ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => errRun (√2 * √(rowsAt R₀ j * r * 2 ^ n) + errL u ds R₀ r n j / 2 ^ scaleR u ds j)
      (program ds) 0

lemma errRun_nonneg {δ : ℝ} (hδ : 0 ≤ δ) (l : List Instr) {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ errRun δ l E := by
  induction l generalizing E with
  | nil => exact hE
  | cons i rest ih =>
    cases i with
    | factor w g => exact ih (by linarith)
    | gate g => exact ih (mul_nonneg (by have := one_le_gateLip g; linarith) hE)

lemma errL_nonneg (u : ℕ) (ds : Directions) (R₀ r n : ℕ) : ∀ j, 0 ≤ errL u ds R₀ r n j
  | 0 => le_rfl
  | j + 1 => errRun_nonneg (add_nonneg (by positivity)
      (div_nonneg (errL_nonneg u ds R₀ r n j) (by positivity))) _ le_rfl

/-- The step of the error bound in closed form. -/
lemma errL_succ_le (u : ℕ) (ds : Directions) (R₀ r n j : ℕ) :
    errL u ds R₀ r n (j + 1) ≤ lipProd (program ds) * facCount (program ds) *
      (√2 * √(rowsAt R₀ j * r * 2 ^ n) + errL u ds R₀ r n j / 2 ^ scaleR u ds j) := by
  have hδ : 0 ≤ √2 * √(rowsAt R₀ j * r * 2 ^ n) + errL u ds R₀ r n j / 2 ^ scaleR u ds j :=
    add_nonneg (by positivity) (div_nonneg (errL_nonneg u ds R₀ r n j) (by positivity))
  have h := errRun_le hδ (program ds) (le_refl (0 : ℝ))
  simp only [errL]
  linarith

/-! ### Truncation -/

lemma abs_truncR_sub_le_one (x : ℝ) : |(truncR x : ℝ) - x| ≤ 1 := by
  unfold truncR
  split_ifs with h
  · have h1 := Int.floor_le x
    have h2 := Int.lt_floor_add_one x
    rw [abs_le]; constructor <;> linarith
  · have h1 := Int.le_ceil x
    have h2 := Int.ceil_lt_add_one x
    rw [abs_le]; constructor <;> linarith

lemma norm_tdivZ_sub_le (s : ℕ) (z : GaussianInt) :
    ‖GaussianInt.toComplex (tdivZ s z) - GaussianInt.toComplex z / 2 ^ s‖ ≤ √2 := by
  have hre : ((tdivZ s z).re : ℝ) = truncR ((z.re : ℝ) / 2 ^ s) := by
    simp only [tdivZ]; exact_mod_cast tdiv_truncR z.re s
  have him : ((tdivZ s z).im : ℝ) = truncR ((z.im : ℝ) / 2 ^ s) := by
    simp only [tdivZ]; exact_mod_cast tdiv_truncR z.im s
  have h1 := abs_truncR_sub_le_one ((z.re : ℝ) / 2 ^ s)
  have h2 := abs_truncR_sub_le_one ((z.im : ℝ) / 2 ^ s)
  set w := GaussianInt.toComplex (tdivZ s z) - GaussianInt.toComplex z / 2 ^ s
  have hc : (2 : ℂ) ^ s = ((2 ^ s : ℝ) : ℂ) := by push_cast; rfl
  have hwre : w.re = ((tdivZ s z).re : ℝ) - (z.re : ℝ) / 2 ^ s := by
    simp only [w, Complex.sub_re, hc, Complex.div_ofReal_re]
    simp
  have hwim : w.im = ((tdivZ s z).im : ℝ) - (z.im : ℝ) / 2 ^ s := by
    simp only [w, Complex.sub_im, hc, Complex.div_ofReal_im]
    simp
  rw [← hre] at h1; rw [← him] at h2
  rw [← hwre] at h1; rw [← hwim] at h2
  rw [← Real.sqrt_sq (norm_nonneg w), Complex.sq_norm, Complex.normSq_apply]
  apply Real.sqrt_le_sqrt
  have a1 : w.re * w.re ≤ 1 := by nlinarith [abs_le.1 h1]
  have a2 : w.im * w.im ≤ 1 := by nlinarith [abs_le.1 h2]
  linarith

lemma l2_tdivArr_sub_le {Y : Type} [Fintype Y] (s : ℕ) (f : ZArr Y n) :
    l2 (toC (tdivArr s f) - ((2 : ℂ) ^ s)⁻¹ • toC f) ≤
      √2 * √(Fintype.card (Y × (Fin n → ZMod 2))) := by
  have := l2_le_of_norm_le (Real.sqrt_nonneg 2) (toC (tdivArr s f) - ((2 : ℂ) ^ s)⁻¹ • toC f)
    (fun p => by
      have h := norm_tdivZ_sub_le s (f p)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, toC, tdivArr]
      rwa [inv_mul_eq_div])
  linarith [mul_comm (√2) (√(Fintype.card (Y × (Fin n → ZMod 2)) : ℝ))]

/-! ### The bank reindexing -/

lemma l2_ofBank_sub_le (R' k : ℕ) (e : Fin k → Fin n) (c : ℂ) (f : ZArr (Fin (NW * R') × Fin r) n)
    (g : ZArr ((Fin R' × Fin r) × NWire) n) :
    l2 (toC (ofBank R' g) - c • ((List.finRange k).map fun i => kBit 1 (e i)).prod (toC f)) ≤
      l2 (toC g - c • ((List.finRange k).map fun i => kBit 1 (e i)).prod (toC (toBank R' f))) := by
  let φ : Fin (NW * R') × Fin r → (Fin R' × Fin r) × NWire := fun z =>
    ((⟨z.1 / NW, Nat.div_lt_of_lt_mul z.1.2⟩, z.2), wireOf (roleSel NW z.1))
  have hφ : Function.Injective φ := by
    intro a b h
    simp only [φ, Prod.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have h3' := wireOf.injective h3
    simp only [roleSel, Fin.mk.injEq] at h3'
    refine Prod.ext (Fin.ext ?_) h2
    rw [← Nat.div_add_mod a.1 NW, ← Nat.div_add_mod b.1 NW, h1, h3']
  let ψ : (Fin (NW * R') × Fin r) × (Fin n → ZMod 2) → ((Fin R' × Fin r) × NWire) × (Fin n → ZMod 2) :=
    fun q => (φ q.1, q.2)
  have hψ : Function.Injective ψ := fun a b h => by
    simp only [ψ, Prod.mk.injEq] at h
    exact Prod.ext (hφ h.1) h.2
  have h2 : (fun q : (Fin (NW * R') × Fin r) × (Fin n → ZMod 2) => toC (toBank R' f) (φ q.1, q.2)) =
      toC f := by
    funext ⟨⟨u, a⟩, b⟩
    simp only [toC, toBank, roleArr, φ, Equiv.symm_apply_apply, roleSel]
    congr
    exact Nat.div_add_mod _ _
  have heq : toC (ofBank R' g) - c • ((List.finRange k).map fun i => kBit 1 (e i)).prod (toC f) =
      (toC g - c • ((List.finRange k).map fun i => kBit 1 (e i)).prod (toC (toBank R' f))) ∘ ψ := by
    funext p
    have h1 : toC (ofBank R' g) p = toC g (φ p.1, p.2) := rfl
    simp only [Pi.sub_apply, Pi.smul_apply, Function.comp_apply, ψ, h1]
    congr 2
    rw [← h2]
    have hl : ((List.finRange k).map fun i => kBit 1 (e i)) =
        ((List.finRange k).map e).map (kBit (X := (Fin R' × Fin r) × NWire) 1) := by
      rw [List.map_map]; rfl
    have hl' : ((List.finRange k).map fun i => kBit 1 (e i)) =
        ((List.finRange k).map e).map (kBit (X := Fin (NW * R') × Fin r) 1) := by
      rw [List.map_map]; rfl
    rw [hl, hl']
    exact (congrFun (prod_respec φ 1 _ (toC (toBank R' f))) p).symm
  rw [heq]
  exact l2_le_of_injective _ ψ hψ

/-! ### The error of the layer -/

/-- **The rounded layer.** On `rowsAt R₀ j` rows the rounded layer is within `errL j` of
`2 ^ scaleR j` times `C` on every active bit, in the `ℓ²` norm. -/
theorem layerR_err (u : ℕ) (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) (R₀ j : ℕ)
    (e : Fin (bits u j) → Fin n) (he : Function.Injective e)
    (f : ZArr (Fin (rowsAt R₀ j) × Fin r) n) :
    l2 (toC (layerR u ds R₀ j e f) - (2 : ℂ) ^ scaleR u ds j •
      ((List.finRange (bits u j)).map fun i => kBit 1 (e i)).prod (toC f)) ≤ errL u ds R₀ r n j := by
  induction j with
  | zero =>
    have key : ∀ e' : Fin u → Fin n, toC (k2s ((List.finRange u).map e') f) =
        (2 : ℂ) ^ u • ((List.finRange u).map fun i => kBit 1 (e' i)).prod (toC f) := by
      intro e'
      rw [toC_k2s, prod_reverse_kBit, List.length_map, List.length_finRange, List.map_map]
      rfl
    have h0 : toC (layerR u ds R₀ 0 e f) = (2 : ℂ) ^ scaleR u ds 0 •
        ((List.finRange (bits u 0)).map fun i => kBit 1 (e i)).prod (toC f) := key e
    rw [h0, sub_self]
    unfold l2; simp [errL]
  | succ j ih =>
    rw [show scaleR u ds (j + 1) = nodeExp ds 0 from rfl]
    simp only [layerR, errL]
    refine (l2_ofBank_sub_le (rowsAt R₀ j) (m * bits u j) e _ f _).trans ?_
    have hN : Fintype.card ((Fin (rowsAt R₀ j) × Fin r) × (Fin n → ZMod 2)) =
        rowsAt R₀ j * r * 2 ^ n := by simp
    refine nodeM_err_sharp (k := bits u j) (e := e) he ds hd _
      (add_nonneg (by positivity) (div_nonneg (errL_nonneg u ds R₀ r n j) (by positivity)))
      (fun s g => ?_) _
    -- the rounded child against the kernels on its slot
    set X := layerR u ds R₀ j (fun c => e (bitIdx s c)) g
    have hX := ih (fun c => e (bitIdx s c)) (he.comp fun c c' h => (bitIdx_inj.1 h).2) g
    set P := ((List.finRange (bits u j)).map fun c => kBit 1 (e (bitIdx s c))).prod (toC g)
    have hT := l2_tdivArr_sub_le (Y := Fin (rowsAt R₀ j) × Fin r) (scaleR u ds j) X
    rw [hN] at hT
    have hsplit : toC (tdivArr (scaleR u ds j) X) - P =
        (toC (tdivArr (scaleR u ds j) X) - ((2 : ℂ) ^ scaleR u ds j)⁻¹ • toC X) +
          ((2 : ℂ) ^ scaleR u ds j)⁻¹ • (toC X - (2 : ℂ) ^ scaleR u ds j • P) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]; abel
    rw [hsplit]
    refine (l2_add_le _ _).trans ?_
    rw [l2_smul]
    have hn : ‖((2 : ℂ) ^ scaleR u ds j)⁻¹‖ = 1 / 2 ^ scaleR u ds j := by
      rw [norm_inv, norm_pow, RCLike.norm_two, one_div]
    rw [hn]
    have hpos : (0 : ℝ) < 2 ^ scaleR u ds j := by positivity
    have : 1 / 2 ^ scaleR u ds j * l2 (toC X - (2 : ℂ) ^ scaleR u ds j • P) ≤
        errL u ds R₀ r n j / 2 ^ scaleR u ds j := by
      rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hX hpos.le
    push_cast at hT ⊢
    linarith

end IntegerMultBounds.MathlibTM2.Layer
