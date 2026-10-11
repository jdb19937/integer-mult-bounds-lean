module

public import IntegerMultBounds.Spec.SyntheticTransform

/-! The statement of the paper's synthetic convolution
(`prop:synthetic-convolution`, §6) on the literal machine model and in the
paper's formats. For arrays `f, g` of `M = ∏ tᵢ` records of `ℛ_r`, the
normalized convolution is

  `ℳ_r(f, g)_x = (r M)⁻¹ Σ_y f_y g_(x - y)`,

with cyclic address subtraction on every axis and the product of `ℛ_r`
(`NLogN.negacyclicMul`). The procedure reads the transform header and the two
operand arrays (component width `w`) and returns an approximation within
`√2 M (3ℓ + 1) 2^(-p)` per coefficient, as a grid array in the original order
with component width `w_M = w + log₂ M`, and writes `Γ(w_M)` on an output
descriptor tape, within `O(T p [d K + p K^(τ-1) + ℓ d^λ' + log (r p)])` steps.
Definitions only. -/

@[expose] public section

namespace IntegerMultBounds.Spec.SignedRingProduct

open Machine NLogN

/-- Cyclic address subtraction `x - y`, axis by axis. -/
def subAddr (ts : List ℕ) (x y : ℕ) : ℕ :=
  undigits ts fun i => (digit ts i x + (ts.getD i 1 - digit ts i y)) % ts.getD i 1

/-- The normalized convolution `ℳ_r(f, g) = (f * g) / (r M)`. -/
noncomputable def convM {r : ℕ} (ts : List ℕ) (f g : ℕ → Fin r → ℂ) : ℕ → Fin r → ℂ :=
  fun x => (1 / ((r * ts.prod : ℕ) : ℂ)) • ∑ y ∈ Finset.range ts.prod, negacyclicMul (f y) (g (subAddr ts x y))

/-- The output component width `w_M = w + log₂ M`. -/
def outWidth (w : ℕ) (ts : List ℕ) : ℕ := w + Nat.log 2 ts.prod

/-- The banks of the convolution: header, operands, output, and the output descriptor on tape 4. -/
def bank5 {t a : ℕ} (hdr f g out desc : List Bool) : Tapes t a :=
  ⟨fun _ => 0, fun i => if i.val = 0 then wordAt hdr else if i.val = 1 then wordAt f
    else if i.val = 2 then wordAt g else if i.val = 3 then wordAt out else if i.val = 4 then wordAt desc
    else fun _ => blank⟩

/-- The paper's step bound for the convolution, without the constant. -/
noncomputable def convolutionCost (P : TransformParams) (p d ℓ K : ℕ) (ts : List ℕ) : ℝ :=
  transformCost P p d ℓ K ts +
    ((2 ^ ℓ * ts.prod : ℕ) : ℝ) * p * (Nat.log 2 (2 ^ ℓ * p) + 1)

/-- The convolution procedure meets the proposition for an admissible instance. -/
def MeetsConvolution {t q a : ℕ} (P : TransformParams) (M : Program t q a) (C : ℝ)
    (p d ℓ K w : ℕ) (ts : List ℕ) : Prop :=
  ∀ fs gs : List (Rec (2 ^ ℓ)), fs.length = ts.prod → gs.length = ts.prod →
    (∀ f ∈ fs, DiskGrid p f.1 f.2) → (∀ g ∈ gs, DiskGrid p g.1 g.2) →
    ∃ (hs : List (Rec (2 ^ ℓ))) (k : ℕ), hs.length = ts.prod ∧
      Close ts.prod (arrayVec p hs) (convM ts (arrayVec p fs) (arrayVec p gs))
        (Real.sqrt 2 * ts.prod * (3 * ℓ + 1) / 2 ^ p) ∧
      (k : ℝ) ≤ C * convolutionCost P p d ℓ K ts ∧
      HoareTime M (· = bank5 (transformHeader p d (2 ^ ℓ) K w ts) (array w fs) (array w gs) [] [])
        (· = bank5 (transformHeader p d (2 ^ ℓ) K w ts) (array w fs) (array w gs)
          (array (outWidth w ts) hs) (gamma (outWidth w ts))) k

/-- `prop:synthetic-convolution`: for fixed parameters there are a cutoff, one fixed program and
a time constant meeting the convolution on every admissible instance. -/
def convolutionTarget (P : TransformParams) : Prop :=
  ∃ (p₁ : ℕ) (t q a : ℕ) (M : Program t q a) (C : ℝ), 5 ≤ t ∧
    ∀ p d ℓ K w ts, p₁ ≤ p → Admissible P p d ℓ K w ts → MeetsConvolution P M C p d ℓ K w ts

end IntegerMultBounds.Spec.SignedRingProduct
