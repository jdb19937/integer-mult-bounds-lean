module

public import IntegerMultBounds.MathlibTM2.Layer.LayerZ
public import IntegerMultBounds.MathlibTM2.Layer.H0
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

/-!
# The normalized layer on Gaussian-integer arrays

The function the layer machine computes on an array of grid numerators. With `sel` the list of
selected address bits (one per chunk, all distinct) and `H = Hl sel` the normalized butterflies,
`Hl_eq` gives `H = ((1 - i)/2)^D • S C S`. The machine applies the phase `S` exactly, applies
the doubled kernels (individually on the top bits `top`, and by the recursive layer on each
piece of the remaining bits after turning the top bits into rows and padding the rows), applies
`S` again, multiplies by the unit `(-i)^⌊D/2⌋ (1 - i)^(D mod 2)`, and truncates toward zero by
a right shift of `⌈D/2⌉ + E`, where `E` is the total kernel exponent.

`topZ_correct`: the output is the componentwise truncation toward zero of `H` applied to the input.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks ComplexFramedExecution

variable {R r n : ℕ}

/-! ### Exact operations -/

/-- The phase `i ^ (number of set bits among l)`. -/
def sZ (l : List (Fin n)) (Z : ZArr (Fin R × Fin r) n) : ZArr (Fin R × Fin r) n :=
  fun p => (⟨0, 1⟩ : GaussianInt) ^ (l.countP fun t => p.2 t = 1) * Z p

/-- Truncation toward zero of a real number. -/
noncomputable def truncR (x : ℝ) : ℤ := if 0 ≤ x then ⌊x⌋ else ⌈x⌉

/-- Division by `2^s` with truncation toward zero, componentwise. -/
def tdivZ (s : ℕ) (z : GaussianInt) : GaussianInt := ⟨z.re.tdiv (2 ^ s), z.im.tdiv (2 ^ s)⟩

/-- The number with bits `v`, least significant first. -/
def bitsVal {a : ℕ} (v : Fin a → ZMod 2) : ℕ := ∑ t : Fin a, if v t = 1 then 2 ^ (t : ℕ) else 0

theorem bitsVal_lt {a : ℕ} (v : Fin a → ZMod 2) : bitsVal v < 2 ^ a := bitsNum_lt v

lemma row_lt {R a u c : ℕ} (hu : u < R) (hc : c < 2 ^ a) : 2 ^ a * u + c < R * 2 ^ a := by
  have : 2 ^ a * (u + 1) ≤ 2 ^ a * R := Nat.mul_le_mul_left _ hu
  rw [Nat.mul_succ] at this
  rw [Nat.mul_comm R]
  omega

/-- Rows from the top `a` address bits: row `u` and address `b ++ c` (`c` the top `a` bits)
become row `2^a u + c` and address `b`. -/
def toRows (a : ℕ) (Z : ZArr (Fin R × Fin r) (n + a)) : ZArr (Fin (R * 2 ^ a) × Fin r) n :=
  fun p => Z ((⟨p.1.1 / 2 ^ a, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq p.1.1.2 (Nat.mul_comm _ _))⟩, p.1.2),
    Fin.append p.2 (addrBits a (p.1.1 % 2 ^ a)))

/-- The inverse of `toRows`. -/
def ofRows (a : ℕ) (Z : ZArr (Fin (R * 2 ^ a) × Fin r) n) : ZArr (Fin R × Fin r) (n + a) :=
  fun p => Z ((⟨2 ^ a * p.1.1 + bitsVal (fun t => p.2 (Fin.natAdd n t)),
      row_lt p.1.1.2 (bitsVal_lt _)⟩, p.1.2), fun t => p.2 (Fin.castAdd a t))

/-- Zero rows appended: `R₁ ≤ R₂`. -/
def padRows (R₂ : ℕ) (Z : ZArr (Fin R × Fin r) n) : ZArr (Fin R₂ × Fin r) n :=
  fun p => if h : (p.1.1 : ℕ) < R then Z ((⟨p.1.1, h⟩, p.1.2), p.2) else 0

/-- The first `R` rows. -/
def unpadRows {R₂ : ℕ} (h : R ≤ R₂) (Z : ZArr (Fin R₂ × Fin r) n) : ZArr (Fin R × Fin r) n :=
  fun p => Z ((Fin.castLE h p.1.1, p.1.2), p.2)

/-- One piece of the remaining chunks: the level-`j` layer with leaf size `u` on the bits
`e`, on an array whose row count is `rowsAt R₀ j`. -/
noncomputable def pieceZ (u : ℕ) (ds : Directions) (R₀ j : ℕ) {R₂ : ℕ} (hR : R₂ = rowsAt R₀ j)
    (e : Fin (bits u j) → Fin n) (Z : ZArr (Fin R₂ × Fin r) n) : ZArr (Fin R₂ × Fin r) n :=
  fun p => layerZ u ds R₀ j e (fun q => Z ((Fin.cast hR.symm q.1.1, q.1.2), q.2))
    ((Fin.cast hR p.1.1, p.1.2), p.2)

/-- A piece descriptor: leaf size, level, base rows and active bits. -/
structure Piece (n R₂ : ℕ) where
  u : ℕ
  j : ℕ
  R₀ : ℕ
  hR : R₂ = rowsAt R₀ j
  e : Fin (bits u j) → Fin n

/-- Run the pieces in order. -/
noncomputable def piecesZ (ds : Directions) {R₂ : ℕ} :
    List (Piece n R₂) → ZArr (Fin R₂ × Fin r) n → ZArr (Fin R₂ × Fin r) n
  | [], Z => Z
  | P :: Ps, Z => piecesZ ds Ps (pieceZ P.u ds P.R₀ P.j P.hR P.e Z)

/-- The active bits of a piece, as bits of the full address. -/
def Piece.bitsList {R₂ : ℕ} (P : Piece n R₂) : List (Fin n) := (List.finRange (bits P.u P.j)).map P.e

/-- The exponent of a piece. -/
noncomputable def Piece.exp {R₂ : ℕ} (ds : Directions) (P : Piece n R₂) : ℕ := expZ P.u ds P.j

/-- The unit `(-i)^⌊D/2⌋ (1 - i)^(D mod 2)`, so that `(1 - i)^D = 2^⌊D/2⌋ · unitD D`. -/
def unitD (D : ℕ) : GaussianInt := (⟨0, -1⟩ : GaussianInt) ^ (D / 2) * (⟨1, -1⟩ : GaussianInt) ^ (D % 2)

/-- The layer on an array with `R` rows, `n + a` address bits, selected bits `sel = low ++ top`
(`top` among the top `a` bits, `low` the bits of the pieces), pieces on `R₂ ≥ R 2^a` rows. -/
noncomputable def topZ (ds : Directions) (a : ℕ) (low : List (Fin n)) (top : List (Fin (n + a)))
    {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂) (Ps : List (Piece n R₂)) (s : ℕ)
    (Z : ZArr (Fin R × Fin r) (n + a)) : ZArr (Fin R × Fin r) (n + a) :=
  let sel : List (Fin (n + a)) := low.map (Fin.castAdd a) ++ top
  let Z₁ := sZ sel Z
  let Z₂ := k2s top Z₁
  let Z₃ := ofRows a (unpadRows hR₂ (piecesZ ds Ps (padRows R₂ (toRows a Z₂))))
  let Z₄ := sZ sel Z₃
  fun p => tdivZ s (unitD sel.length * Z₄ p)


/-! ### Helper lemmas -/

lemma addrBits_bitsVal {a : ℕ} (v : Fin a → ZMod 2) : addrBits a (bitsVal v) = v :=
  addrBits_bitsNum v

lemma toComplex_i : GaussianInt.toComplex ⟨0, 1⟩ = Complex.I := by
  simp [GaussianInt.toComplex_def']

/-- The phase is `Sl`. -/
lemma toC_sZ (l : List (Fin n)) (Z : ZArr (Fin R × Fin r) n) :
    toC (sZ l Z) = Sl _ l (toC Z) := by
  induction l with
  | nil => funext p; simp [sZ, Sl, toC]
  | cons t l ih =>
    funext p
    change toC (sZ (t :: l) Z) p = sBit t (Sl _ l (toC Z)) p
    rw [← ih]
    simp only [sBit, LinearMap.coe_mk, AddHom.coe_mk, toC, sZ, map_mul, map_pow, List.countP_cons,
      toComplex_i, pow_add]
    rcases zmod2_cases (p.2 t) with h | h
    · simp [h]
    · simp [h]; ring

lemma Cl_perm {X : Type} {l l' : List (Fin n)} (h : l.Perm l') : Cl X l = Cl X l' :=
  (h.map _).prod_eq' (pairwise_commute_kBit 1 l)

lemma Cl_append {X : Type} (l l' : List (Fin n)) (f : Arr X n) :
    Cl X (l ++ l') f = Cl X l (Cl X l' f) := by
  simp only [Cl, List.map_append, List.prod_append, Module.End.mul_apply]

/-- One piece is `2 ^ exp` times the kernels on its bits. -/
lemma toC_pieceZ (u : ℕ) (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) (R₀ j : ℕ)
    {R₂ : ℕ} (hR : R₂ = rowsAt R₀ j) (e : Fin (bits u j) → Fin n) (he : Function.Injective e)
    (W : ZArr (Fin R₂ × Fin r) n) :
    toC (pieceZ u ds R₀ j hR e W) =
      (2 : ℂ) ^ expZ u ds j • Cl _ ((List.finRange (bits u j)).map e) (toC W) := by
  subst hR
  rw [Cl, List.map_map]
  exact layerZ_correct u ds hd R₀ j e he W

/-- The pieces are `2 ^ (Σ exp)` times the kernels on all their bits. -/
lemma toC_piecesZ (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) {R₂ : ℕ}
    (Ps : List (Piece n R₂)) (hinj : ∀ P ∈ Ps, Function.Injective P.e)
    (W : ZArr (Fin R₂ × Fin r) n) :
    toC (piecesZ ds Ps W) =
      (2 : ℂ) ^ (Ps.map (Piece.exp ds)).sum • Cl _ (Ps.flatMap Piece.bitsList) (toC W) := by
  induction Ps generalizing W with
  | nil => simp [piecesZ, Cl]
  | cons P Ps ih =>
    rw [piecesZ, ih (fun Q hQ => hinj Q (List.mem_cons_of_mem _ hQ)),
      toC_pieceZ P.u ds hd P.R₀ P.j P.hR P.e (hinj P List.mem_cons_self), map_smul, smul_smul,
      List.flatMap_cons, Cl_perm List.perm_append_comm, Cl_append, List.map_cons, List.sum_cons,
      pow_add, mul_comm]
    rfl

/-- Kernels pass through padding and unpadding rows. -/
lemma toC_unpad_pad {R₂ : ℕ} (h : R ≤ R₂) (l : List (Fin n)) (c : ℂ) (W : ZArr (Fin R × Fin r) n)
    (G : ZArr (Fin R₂ × Fin r) n) (hG : toC G = c • Cl _ l (toC (padRows R₂ W))) :
    toC (unpadRows h G) = c • Cl _ l (toC W) := by
  let φ : Fin R × Fin r → Fin R₂ × Fin r := fun z => (Fin.castLE h z.1, z.2)
  have h2 : (fun q : (Fin R × Fin r) × (Fin n → ZMod 2) => toC (padRows R₂ W) (φ q.1, q.2)) =
      toC W := by
    funext q
    simp [toC, padRows, φ]
  funext p
  have h1 : toC (unpadRows h G) p = toC G (φ p.1, p.2) := rfl
  rw [h1, hG, Pi.smul_apply, Pi.smul_apply, ← h2]
  exact congrArg (c • ·) (congrFun (prod_respec φ 1 l _) p)

/-- The source cell of `ofRows`. -/
def ofRowsIdx (a : ℕ) (p : (Fin R × Fin r) × (Fin (n + a) → ZMod 2)) :
    (Fin (R * 2 ^ a) × Fin r) × (Fin n → ZMod 2) :=
  ((⟨2 ^ a * p.1.1 + bitsVal (fun t => p.2 (Fin.natAdd n t)), row_lt p.1.1.2 (bitsVal_lt _)⟩,
    p.1.2), fun t => p.2 (Fin.castAdd a t))

lemma ofRows_apply (a : ℕ) (Z : ZArr (Fin (R * 2 ^ a) × Fin r) n)
    (p : (Fin R × Fin r) × (Fin (n + a) → ZMod 2)) : ofRows a Z p = Z (ofRowsIdx a p) := rfl

lemma ofRows_toRows (a : ℕ) (Z : ZArr (Fin R × Fin r) (n + a)) : ofRows a (toRows a Z) = Z := by
  funext p
  obtain ⟨⟨u, c⟩, b⟩ := p
  have hv := bitsVal_lt (fun t => b (Fin.natAdd n t))
  have h1 : (2 ^ a * u.1 + bitsVal (fun t => b (Fin.natAdd n t))) / 2 ^ a = u.1 := by
    rw [Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hv, add_zero]
  have h2 : (2 ^ a * u.1 + bitsVal (fun t => b (Fin.natAdd n t))) % 2 ^ a =
      bitsVal (fun t => b (Fin.natAdd n t)) := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
  simp only [ofRows, toRows]
  congr 1
  refine Prod.ext (Prod.ext (Fin.ext h1) rfl) ?_
  simp only [h2, addrBits_bitsVal]
  exact Fin.append_castAdd_natAdd

lemma flip_castAdd (a : ℕ) (t s : Fin n) (b : Fin (n + a) → ZMod 2) :
    flip (Fin.castAdd a t) b (Fin.castAdd a s) = flip t (fun s => b (Fin.castAdd a s)) s := by
  by_cases h : s = t
  · subst h; rw [flip_self, flip_self]
  · rw [flip_other h, flip_other (fun h' => h (Fin.castAdd_inj.1 h'))]

lemma flip_castAdd_natAdd (a : ℕ) (t : Fin n) (s : Fin a) (b : Fin (n + a) → ZMod 2) :
    flip (Fin.castAdd a t) b (Fin.natAdd n s) = b (Fin.natAdd n s) := by
  refine flip_other (fun h => ?_) b
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  omega

lemma ofRowsIdx_flip (a : ℕ) (t : Fin n) (p : (Fin R × Fin r) × (Fin (n + a) → ZMod 2)) :
    ofRowsIdx a (p.1, flip (Fin.castAdd a t) p.2) = ((ofRowsIdx a p).1, flip t (ofRowsIdx a p).2) := by
  simp only [ofRowsIdx, flip_castAdd_natAdd, flip_castAdd]

/-- Kernels on low bits pass through the `ofRows` reindexing. -/
lemma prod_ofRows (a : ℕ) (l : List (Fin n)) (F : Arr (Fin (R * 2 ^ a) × Fin r) n) :
    (fun p => Cl _ l F (ofRowsIdx a p)) = Cl _ (l.map (Fin.castAdd a)) (fun p => F (ofRowsIdx a p)) := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    funext p
    simp only [Cl, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    rw [← ih, kBit_apply, kBit_apply, ofRowsIdx_flip]

lemma toC_ofRows (a : ℕ) (l : List (Fin n)) (c : ℂ) (Z : ZArr (Fin R × Fin r) (n + a))
    (G : ZArr (Fin (R * 2 ^ a) × Fin r) n) (hG : toC G = c • Cl _ l (toC (toRows a Z))) :
    toC (ofRows a G) = c • Cl _ (l.map (Fin.castAdd a)) (toC Z) := by
  have hZ : (fun p => toC (toRows a Z) (ofRowsIdx a p)) = toC Z := by
    change toC (ofRows a (toRows a Z)) = toC Z
    rw [ofRows_toRows]
  funext p
  change toC G (ofRowsIdx a p) = _
  rw [hG, Pi.smul_apply, Pi.smul_apply, ← hZ, ← prod_ofRows]

/-- `(1 - i)^D = 2^⌊D/2⌋ · unitD D`. -/
lemma one_sub_I_pow (D : ℕ) :
    (1 - Complex.I) ^ D = 2 ^ (D / 2) * GaussianInt.toComplex (unitD D) := by
  have h2 : (1 - Complex.I) ^ 2 = 2 * (-Complex.I) := by
    ring_nf; rw [Complex.I_sq]; ring
  have hu : GaussianInt.toComplex (unitD D) = (-Complex.I) ^ (D / 2) * (1 - Complex.I) ^ (D % 2) := by
    simp [unitD, GaussianInt.toComplex_def']
    ring
  rw [hu, ← mul_assoc, ← mul_pow, ← h2, ← pow_mul, ← pow_add, Nat.div_add_mod]

lemma tdiv_truncR (x : ℤ) (s : ℕ) : x.tdiv (2 ^ s) = truncR ((x : ℝ) / 2 ^ s) := by
  have h : ((x : ℝ) / 2 ^ s) = (((x : ℚ) / ((2 ^ s : ℕ) : ℚ) : ℚ) : ℝ) := by push_cast; ring
  have hpos : (0 : ℝ) < 2 ^ s := by positivity
  unfold truncR
  rw [h, Rat.floor_cast, Rat.ceil_cast]
  split_ifs with hx
  · have : 0 ≤ x := by
      rw [← h] at hx
      have := (div_nonneg_iff.1 hx)
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact_mod_cast h1
      · linarith
    rw [Int.tdiv_eq_ediv_of_nonneg this, Rat.floor_intCast_div_natCast]
    push_cast; rfl
  · have : x < 0 := by
      rw [← h] at hx
      by_contra hc
      exact hx (div_nonneg (by exact_mod_cast not_lt.1 hc) hpos.le)
    rw [Rat.ceil_intCast_div_natCast, ← neg_neg x, Int.neg_tdiv, neg_neg,
      Int.tdiv_eq_ediv_of_nonneg (by omega)]
    push_cast; rfl

lemma tdivZ_eq (s : ℕ) (w : GaussianInt) (h : ℂ) (hw : GaussianInt.toComplex w = 2 ^ s * h) :
    tdivZ s w = ⟨truncR h.re, truncR h.im⟩ := by
  have hc : (2 : ℂ) ^ s = ((2 ^ s : ℝ) : ℂ) := by push_cast; rfl
  have hpos : (0 : ℝ) < 2 ^ s := by positivity
  have hre : h.re = (w.re : ℝ) / 2 ^ s := by
    rw [GaussianInt.intCast_re, hw, hc, Complex.re_ofReal_mul]; field_simp
  have him : h.im = (w.im : ℝ) / 2 ^ s := by
    rw [GaussianInt.intCast_im, hw, hc, Complex.im_ofReal_mul]; field_simp
  simp only [tdivZ, hre, him, tdiv_truncR]

/-- The layer computes the truncation toward zero of the normalized butterflies on the selected
bits, provided the pieces cover `low` exactly, the selected bits are distinct, the shift is
`⌈D/2⌉ + E` and every output is small. -/
theorem topZ_correct (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds) (a : ℕ)
    (low : List (Fin n)) (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂)
    (Ps : List (Piece n R₂)) (hinj : ∀ P ∈ Ps, Function.Injective P.e)
    (hcover : (Ps.flatMap Piece.bitsList).Perm low)
    (hsel : (low.map (Fin.castAdd a) ++ top).Nodup)
    (s : ℕ) (hs : s = (low.length + top.length + 1) / 2 + top.length + (Ps.map (Piece.exp ds)).sum)
    (Z : ZArr (Fin R × Fin r) (n + a)) (p : (Fin R × Fin r) × (Fin (n + a) → ZMod 2)) :
    topZ ds a low top hR₂ Ps s Z p =
      ⟨truncR (Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) p).re,
        truncR (Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) p).im⟩ := by
  set sel : List (Fin (n + a)) := low.map (Fin.castAdd a) ++ top with hsel_def
  set L := Ps.flatMap Piece.bitsList
  set E := (Ps.map (Piece.exp ds)).sum
  set Z₂ := k2s top (sZ sel Z)
  set Z₃ := ofRows a (unpadRows hR₂ (piecesZ ds Ps (padRows R₂ (toRows a Z₂))))
  set D := sel.length with hD
  set F := Sl _ sel (Cl _ sel (Sl _ sel (toC Z)))
  have hZ₂ : toC Z₂ = (2 : ℂ) ^ top.length • Cl _ top (Sl _ sel (toC Z)) := by
    rw [toC_k2s, prod_reverse_kBit, toC_sZ]; rfl
  have hZ₃ : toC Z₃ = (2 : ℂ) ^ (E + top.length) • Cl _ sel (Sl _ sel (toC Z)) := by
    rw [toC_ofRows a L _ Z₂ _ (toC_unpad_pad hR₂ L _ _ _ (toC_piecesZ ds hd Ps hinj _)),
      Cl_perm (hcover.map _), hZ₂, map_smul, smul_smul, ← pow_add, hsel_def, Cl_append]
  have hZ₄ : toC (sZ sel Z₃) = (2 : ℂ) ^ (E + top.length) • F := by
    rw [toC_sZ, hZ₃, map_smul]
  have hH : Hl _ sel (toC Z) p = ((1 - Complex.I) / 2) ^ D * F p := by
    rw [Hl_eq sel hsel]; rfl
  have hDlen : D = low.length + top.length := by
    rw [hD, hsel_def, List.length_append, List.length_map]
  apply tdivZ_eq
  rw [map_mul]
  change GaussianInt.toComplex (unitD D) * toC (sZ sel Z₃) p = _
  rw [hZ₄, Pi.smul_apply, smul_eq_mul, hH, div_pow, one_sub_I_pow, hs, ← hDlen]
  have h2D : (2 : ℂ) ^ ((D + 1) / 2) * 2 ^ (D / 2) = 2 ^ D := by
    rw [← pow_add]; congr 1; omega
  have h2 : (2 : ℂ) ^ D ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [pow_add, pow_add]
  field_simp
  linear_combination (-(GaussianInt.toComplex (unitD D) * F p * 2 ^ top.length)) * h2D

end IntegerMultBounds.MathlibTM2.Layer
