module

public import IntegerMultBounds.Spec.SyntheticTransform

/-! The statement of the paper's simultaneous normalized butterfly layer
(`prop:simultaneous-layer`, §5) on the literal machine model and in the
paper's formats. The descriptor tape holds the header

  `ℰ = Γ(p)Γ(d)Γ(r)Γ(D)Γ(P)Γ(S)Γ(K)Γ(ρ+1)Γ(w)`,

and the array tape holds `M = P S 2^(K D)` records of `ℛ_r` in lexicographic
order on `[P] × [2^K]^D × [S]`, each `r` coefficients with the real then the
imaginary numerator as a signed `w`-bit two's-complement word, most
significant bit first. On each of the `D` address chunks bit `ρ` (from the
least significant) is selected, and `ℋ` is the tensor product of
`H₀ = ½ [[1, 1], [1, -1]]` on the selected bits. The procedure replaces the
array by `Q_p(ℋ z)` in the same format within `O(V d^λ')` steps,
`V = 2 M r w`, uniformly over the bands for `d` and `r`. The two numerical
consequences (unit disk, error `< √2 2^(-p)`) are proved from the
definitions in `SimultaneousLayerFacts`. Definitions only. -/

@[expose] public section

namespace IntegerMultBounds.Spec.SignedRingProduct

open Machine NLogN

/-- The layer header `Γ(p)Γ(d)Γ(r)Γ(D)Γ(P)Γ(S)Γ(K)Γ(ρ+1)Γ(w)`. -/
def layerHeader (p d r D P S K ρ w : ℕ) : List Bool :=
  gamma p ++ gamma d ++ gamma r ++ gamma D ++ gamma P ++ gamma S ++ gamma K ++ gamma (ρ + 1) ++ gamma w

/-- The bit position of the selected bit of chunk `j` (counted from the last chunk) in `x / S`. -/
def selPos (K ρ j : ℕ) : ℕ := j * K + ρ

/-- The selected bit of chunk `j` of address `x`. -/
def selBit {D : ℕ} (K ρ S : ℕ) (x : ℕ) (j : Fin D) : Bool := (x / S).testBit (selPos K ρ j)

/-- Address `x` with its selected bits replaced by `b`. -/
def setSel {D : ℕ} (K ρ S : ℕ) (x : ℕ) (b : Fin D → Bool) : ℕ :=
  x - S * ∑ j : Fin D, (if selBit K ρ S x j then 2 ^ selPos K ρ j else 0) +
    S * ∑ j : Fin D, (if b j then 2 ^ selPos K ρ j else 0)

/-- `ℋ z`: at `x`, `2^(-D) Σ_b (-1)^(Σⱼ xⱼ bⱼ) z(x with selected bits b)`. -/
noncomputable def hadamard {r : ℕ} (D K ρ S : ℕ) (z : ℕ → Fin r → ℂ) : ℕ → Fin r → ℂ :=
  fun x k => (1 / (2 ^ D : ℂ)) * ∑ b : Fin D → Bool,
    (-1) ^ (Finset.univ.filter fun j => selBit K ρ S x j && b j).card * z (setSel K ρ S x b) k

/-- The returned array `Q_p(ℋ z)` as records. -/
noncomputable def layerOut {r : ℕ} (p D K ρ S M : ℕ) (zs : List (Rec r)) : List (Rec r) :=
  (List.range M).map fun x =>
    (fun k => rho0 (2 ^ p * (hadamard D K ρ S (arrayVec p zs) x k).re),
      fun k => rho0 (2 ^ p * (hadamard D K ρ S (arrayVec p zs) x k).im))

/-- The fixed parameters of the proposition. -/
structure LayerParams where
  c : ℚ
  ε : ℚ
  lam : ℚ
  lam' : ℚ
  ad : ℝ
  bd : ℝ
  ar : ℝ
  br : ℝ
  CM : ℝ
  Cdesc : ℝ
  Cw : ℝ

/-- The paper's fixed `τ = σ = 1 - 2^(-50)`, `β = 1/2`, `C₁ = 20`. -/
def layerTau : ℚ := 1 - 1 / 2 ^ 50

/-- The constraints on the fixed parameters. -/
def LayerParams.Valid (P : LayerParams) : Prop :=
  0 < P.c ∧ 0 < P.ε ∧ 0 < P.lam ∧ 0 < P.lam' ∧
    layerTau < P.lam ∧ P.lam < 1 ∧ layerTau * (1 + P.c / (1 / 2)) < P.lam ∧
    max P.lam (layerTau + 1 / 2 * (1 - layerTau)) < P.lam' ∧ P.lam' < 1 ∧ P.ε * 20 < 1 ∧
    0 < P.ad ∧ P.ad ≤ P.bd ∧ 0 < P.ar ∧ P.ar ≤ P.br ∧
    0 < P.CM ∧ 0 < P.Cdesc ∧ 1 < P.Cw

/-- An admissible call (the hypotheses of the proposition beyond the cutoff). -/
def LayerAdmissible (P : LayerParams) (p d r D Pa S K ρ w : ℕ) : Prop :=
  P.ad * (p : ℝ) ^ (P.ε : ℝ) ≤ d ∧ (d : ℝ) ≤ P.bd * (p : ℝ) ^ (P.ε : ℝ) ∧
    (2 : ℝ) ^ (P.ar * p / d) ≤ r ∧ (r : ℝ) ≤ (2 : ℝ) ^ (P.br * p / d) ∧
    K = ⌊(d : ℝ) ^ (P.c : ℝ)⌋₊ ∧ 1 ≤ D ∧ D ≤ d ∧ 1 ≤ Pa ∧ 1 ≤ S ∧ ρ < K ∧
    ((2 * (Pa * S * 2 ^ (K * D)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (P.CM * p) ∧
    ((layerHeader p d r D Pa S K ρ w).length : ℝ) ≤ P.Cdesc * p ∧
    p + 2 ≤ w ∧ (w : ℝ) ≤ P.Cw * p

/-- The paper's step bound `V d^λ'` with `V = 2 M r w`, without the constant. -/
noncomputable def layerCost (P : LayerParams) (d r M w : ℕ) : ℝ :=
  ((2 * M * r * w : ℕ) : ℝ) * (d : ℝ) ^ (P.lam' : ℝ)

/-- The layer procedure meets the proposition for an admissible call: the array on tape 1 is
replaced in place by `Q_p(ℋ z)`, and every other tape is unchanged. -/
def MeetsLayer {t q a : ℕ} (P : LayerParams) (M : Program t q a) (C : ℝ)
    (p d r D Pa S K ρ w : ℕ) : Prop :=
  ∀ zs : List (Rec r), zs.length = Pa * S * 2 ^ (K * D) → (∀ z ∈ zs, DiskGrid p z.1 z.2) →
    ∃ k : ℕ, (k : ℝ) ≤ C * layerCost P d r (Pa * S * 2 ^ (K * D)) w ∧
      HoareTime M (· = bank (layerHeader p d r D Pa S K ρ w) (array w zs) [] [])
        (· = bank (layerHeader p d r D Pa S K ρ w)
          (array w (layerOut p D K ρ S (Pa * S * 2 ^ (K * D)) zs)) [] []) k

/-- `prop:simultaneous-layer`: for valid fixed parameters there are a cutoff, one fixed program
and a time constant meeting the layer on every admissible call. -/
def layerTarget (P : LayerParams) : Prop :=
  ∃ (p₀ t q a : ℕ) (M : Program t q a) (C : ℝ), 2 ≤ t ∧
    ∀ p d r D Pa S K ρ w, p₀ ≤ p → LayerAdmissible P p d r D Pa S K ρ w →
      MeetsLayer P M C p d r D Pa S K ρ w

end IntegerMultBounds.Spec.SignedRingProduct
