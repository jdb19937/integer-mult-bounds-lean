import IntegerMultBounds.Spec.PointwiseProducts
import IntegerMultBounds.NLogN.SynthFFT

/-! The statement of the paper's synthetic transforms (`lem:synthetic-transform-cost`,
§6) on the literal machine model and in the paper's formats. An array holds
`M = ∏ tᵢ` polynomial records of `ℛ_r = ℂ[y]/(y^r + 1)` in lexicographic order
of their axis addresses (first axis most significant). With `ω_t = y^(2r/t)`,

  `(F⁻z)_j = M⁻¹ Σ_k y^(-Σᵢ (2r/tᵢ) jᵢ kᵢ) z_k`,  `(F⁺z)_j = M⁻¹ Σ_k y^(Σᵢ (2r/tᵢ) jᵢ kᵢ) z_k`,

`B` reverses the bits of every axis address, and `L` is a record permutation
fixed by the parameters. The forward procedure approximates `L B F⁻` and the
opposite procedure `F⁺ B⁻¹ L⁻¹`, each within `√2 ℓ 2^(-p)` per coefficient,
returning disk grid arrays in the same component format, within
`O(T p [d K + p K^(τ-1) + ℓ d^λ'])` steps. The layout is stated
existentially, shared by both procedures: the paper constructs one explicit
`L`, and the convolution only uses that the two procedures agree on it.
Definitions only. -/

namespace IntegerMultBounds.Spec.SignedRingProduct

open Machine NLogN

/-! ### Addresses -/

/-- Digit `i` of the mixed-radix address `n` (first axis most significant). -/
def digit (ts : List ℕ) (i : ℕ) (n : ℕ) : ℕ := n / (ts.drop (i + 1)).prod % ts.getD i 1

/-- The address with digits `ds`. -/
def undigits (ts : List ℕ) (ds : ℕ → ℕ) : ℕ :=
  ((List.range ts.length).map fun i => ds i * (ts.drop (i + 1)).prod).sum

/-- Reverse the low `a` bits of `j`. -/
def bitrev (a j : ℕ) : ℕ := ((List.range a).map fun h => (j / 2 ^ h % 2) * 2 ^ (a - 1 - h)).sum

/-- `B`: reverse the bits of every axis address (axis lengths are powers of two). -/
def bitrevAddr (ts : List ℕ) (n : ℕ) : ℕ :=
  undigits ts fun i => bitrev (Nat.log 2 (ts.getD i 1)) (digit ts i n)

/-- The synthetic exponent `Σᵢ (2r/tᵢ) jᵢ kᵢ`. -/
def synthExpL (r : ℕ) (ts : List ℕ) (j k : ℕ) : ℕ :=
  ((List.range ts.length).map fun i => (2 * r / ts.getD i 1) * digit ts i j * digit ts i k).sum

/-! ### Arrays and transforms -/

/-- The coefficient array of a list of records. -/
noncomputable def arrayVec {r : ℕ} (p : ℕ) (fs : List (Rec r)) : ℕ → Fin r → ℂ :=
  fun n => match fs[n]? with
    | some f => gridPoly p f.1 f.2
    | none => 0

/-- Multiplication by `y^(-e)` in `ℛ_r`. -/
noncomputable def shiftInv {r : ℕ} [NeZero r] (e : ℕ) (a : Fin r → ℂ) : Fin r → ℂ :=
  shiftNegZ ((2 * r - e % (2 * r)) % (2 * r)) a

/-- `F⁻` on an array of `M = ∏ tᵢ` records. -/
noncomputable def fwdT {r : ℕ} [NeZero r] (ts : List ℕ) (z : ℕ → Fin r → ℂ) : ℕ → Fin r → ℂ :=
  fun j => (1 / (ts.prod : ℂ)) • ∑ k ∈ Finset.range ts.prod, shiftInv (synthExpL r ts j k) (z k)

/-- `F⁺` on an array of `M = ∏ tᵢ` records. -/
noncomputable def oppT {r : ℕ} [NeZero r] (ts : List ℕ) (z : ℕ → Fin r → ℂ) : ℕ → Fin r → ℂ :=
  fun j => (1 / (ts.prod : ℂ)) • ∑ k ∈ Finset.range ts.prod, shiftNegZ (synthExpL r ts j k) (z k)

/-- A layout: a permutation of the record addresses, for each parameter choice. -/
abbrev Layout := (p d ℓ K w : ℕ) → (ts : List ℕ) → Equiv.Perm (Fin ts.prod)

/-- The exact forward counterpart `L B F⁻`: the record at `y` is entry `B⁻¹ L⁻¹ y` of `F⁻z`. -/
noncomputable def fwdExact {r : ℕ} [NeZero r] (ts : List ℕ) (Lp : Equiv.Perm (Fin ts.prod))
    (z : ℕ → Fin r → ℂ) : ℕ → Fin r → ℂ :=
  fun y => if h : y < ts.prod then fwdT ts z (bitrevAddr ts (Lp.symm ⟨y, h⟩)) else 0

/-- The exact opposite counterpart `F⁺ B⁻¹ L⁻¹`: `F⁺` of the array whose entry `j` is `u (L (B j))`. -/
noncomputable def oppExact {r : ℕ} [NeZero r] (ts : List ℕ) (Lp : Equiv.Perm (Fin ts.prod))
    (u : ℕ → Fin r → ℂ) : ℕ → Fin r → ℂ :=
  oppT ts fun j => if h : bitrevAddr ts j % ts.prod < ts.prod then
    u (Lp ⟨bitrevAddr ts j % ts.prod, h⟩) else 0

/-- Coefficientwise closeness of two arrays on the first `M` records. -/
def Close {r : ℕ} (M : ℕ) (u v : ℕ → Fin r → ℂ) (ε : ℝ) : Prop := ∀ n < M, ∀ k, ‖u n k - v n k‖ < ε

/-! ### Fixed parameters and admissible instances -/

/-- The fixed parameters of `prop:simultaneous-layer` and `lem:synthetic-transform-cost`. -/
structure TransformParams where
  c : ℝ
  ε : ℝ
  lam' : ℝ
  τ : ℝ
  ad : ℝ
  bd : ℝ
  ar : ℝ
  br : ℝ
  Cl : ℝ
  Cw : ℕ

/-- An admissible instance (the per-call hypotheses of `lem:synthetic-transform-cost`). -/
def Admissible (P : TransformParams) (p d ℓ K w : ℕ) (ts : List ℕ) : Prop :=
  P.ad * (p : ℝ) ^ P.ε ≤ d ∧ (d : ℝ) ≤ P.bd * (p : ℝ) ^ P.ε ∧
    (2 : ℝ) ^ (P.ar * p / d) ≤ (2 : ℝ) ^ ℓ ∧ (2 : ℝ) ^ ℓ ≤ (2 : ℝ) ^ (P.br * p / d) ∧
    2 ≤ d ∧ 2 ≤ ℓ ∧ ℓ < p ∧ ((d * ℓ : ℕ) : ℝ) ≤ P.Cl * p ∧ K = ⌊(d : ℝ) ^ P.c⌋₊ ∧ 1 ≤ K ∧ K ≤ ℓ - 1 ∧
    AxisLengths d ℓ ts ∧ p + 2 ≤ w ∧ w ≤ P.Cw * p

/-- The paper's step bound `T p [d K + p K^(τ-1) + ℓ d^λ']`, without the constant. -/
noncomputable def transformCost (P : TransformParams) (p d ℓ K : ℕ) (ts : List ℕ) : ℝ :=
  ((2 ^ ℓ * ts.prod : ℕ) : ℝ) * p * (d * K + p * (K : ℝ) ^ (P.τ - 1) + ℓ * (d : ℝ) ^ P.lam')

/-- The forward procedure meets the lemma for an admissible instance with layout `L`. -/
def MeetsForward {t q a : ℕ} (P : TransformParams) (M : Program t q a) (L : Layout) (C : ℝ)
    (p d ℓ K w : ℕ) (ts : List ℕ) : Prop :=
  ∀ fs : List (Rec (2 ^ ℓ)), fs.length = ts.prod → (∀ f ∈ fs, DiskGrid p f.1 f.2) →
    ∃ (gs : List (Rec (2 ^ ℓ))) (k : ℕ), gs.length = ts.prod ∧ (∀ g ∈ gs, DiskGrid p g.1 g.2) ∧
      Close ts.prod (arrayVec p gs) (fwdExact ts (L p d ℓ K w ts) (arrayVec p fs))
        (Real.sqrt 2 * ℓ / 2 ^ p) ∧
      (k : ℝ) ≤ C * transformCost P p d ℓ K ts ∧
      HoareTime M (· = bank (transformHeader p d (2 ^ ℓ) K w ts) (array w fs) [] [])
        (· = bank (transformHeader p d (2 ^ ℓ) K w ts) (array w fs) [] (array w gs)) k

/-- The opposite procedure meets the lemma for an admissible instance with layout `L`. -/
def MeetsOpposite {t q a : ℕ} (P : TransformParams) (M : Program t q a) (L : Layout) (C : ℝ)
    (p d ℓ K w : ℕ) (ts : List ℕ) : Prop :=
  ∀ us : List (Rec (2 ^ ℓ)), us.length = ts.prod → (∀ u ∈ us, DiskGrid p u.1 u.2) →
    ∃ (gs : List (Rec (2 ^ ℓ))) (k : ℕ), gs.length = ts.prod ∧ (∀ g ∈ gs, DiskGrid p g.1 g.2) ∧
      Close ts.prod (arrayVec p gs) (oppExact ts (L p d ℓ K w ts) (arrayVec p us))
        (Real.sqrt 2 * ℓ / 2 ^ p) ∧
      (k : ℝ) ≤ C * transformCost P p d ℓ K ts ∧
      HoareTime M (· = bank (transformHeader p d (2 ^ ℓ) K w ts) (array w us) [] [])
        (· = bank (transformHeader p d (2 ^ ℓ) K w ts) (array w us) [] (array w gs)) k

/-- `lem:synthetic-transform-cost`: for fixed parameters there are a cutoff, a layout, two fixed
programs and a time constant meeting both procedures on every admissible instance. -/
def transformTarget (P : TransformParams) : Prop :=
  ∃ (p₁ : ℕ) (L : Layout) (t q₁ q₂ a : ℕ) (Mf : Program t q₁ a) (Mo : Program t q₂ a) (C : ℝ), 4 ≤ t ∧
    ∀ p d ℓ K w ts, p₁ ≤ p → Admissible P p d ℓ K w ts →
      MeetsForward P Mf L C p d ℓ K w ts ∧ MeetsOpposite P Mo L C p d ℓ K w ts

end IntegerMultBounds.Spec.SignedRingProduct
