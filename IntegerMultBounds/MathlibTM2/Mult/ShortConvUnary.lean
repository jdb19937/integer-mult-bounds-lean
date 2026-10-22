module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvHeader
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPadding

/-! # Shared short convolution from raw blocks and unary dimensions

This is the complete single-block entry point. Both padding counters and the ring header
are generated, used, and cleared. Only the full output coefficient stream changes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.Spec.SignedRingProduct

/-- Cost of generating the symbol-padding count for `a` coefficients. -/
def paddingCost (l w a : ℕ) : ℕ := 4 * w + 4 * (2 ^ l * w) + 9 * l + 4 * (a * w) + 12

/-- Every setup, conversion, product and cleanup phase of one block pair. -/
def unaryCost (p l w a b : ℕ) : ℕ :=
  paddingCost l w a + paddingCost l w b + ldrHeaderCost p l w +
    (4 * ((2 ^ l - a) * w) + 6 * (a * w) +
     4 * ((2 ^ l - b) * w) + 6 * (b * w) +
     rpRecCost p l w + rpFixCost p l w + 4 * (2 ^ l * w) + 24) +
    2 * (header p (2 ^ l) w).length + 2 +
    (2 * ((2 ^ l - a) * w) + 2) + (2 * ((2 ^ l - b) * w) + 2)

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

noncomputable def fromUnary (rg : RpReg → Fin T) (ι : Fin 91 → Fin T)
    (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q)
    (pR lR wR srcX padX srcY padY : Fin T) : Pr P T Q A U :=
  .seq (padding lR wR srcX padX (rg .ta) (rg .tb)) <|
  .seq (padding lR wR srcY padY (rg .ta) (rg .tb)) <|
  .seq (withHeader rg ι h hT hQ pR lR wR srcX padX srcY padY) <|
  .seq (uclear padX) (uclear padY)

/-- The complete shared block primitive, with no prepared padding or header inputs. -/
theorem fromUnary_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w) (x y : List GaussianInt)
    (hx : x.length ≤ 2 ^ l) (hy : y.length ≤ 2 ^ l)
    (hxy : x.length + y.length ≤ 2 ^ l + 1)
    (hX : ∀ z ∈ x, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ z ∈ y, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (pR lR wR srcX padX srcY padY : Fin T)
    (hin : [pR, lR, wR, rg .d0, rg .ta, rg .tb, rg .acc, rg .sv, rg .tmp].Nodup)
    (hreg : [srcX, padX, srcY, padY, rg .xs, rg .ys, rg .ta, rg .tb, rg .d0].Nodup)
    (haux : [pR, lR, wR, srcX, srcY, padX, padY].Nodup)
    (hoff : ∀ r, padX ≠ rg r ∧ padY ≠ rg r)
    (hpriv : ∀ j, padX ≠ ι j ∧ padY ≠ ι j)
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hsrcX : S.R srcX = cstream A w x) (hsrcY : S.R srcY = cstream A w y)
    (hpadX : S.R padX = []) (hpadY : S.R padY = [])
    (hwn : (S.R (rg .wn)).length = w)
    (hempty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d0, .d1, .d2, .d3], S.R (rg r) = [])
    (hpR : (S.R pR).length = p) (hlR : (S.R lR).length = l) (hwR : (S.R wR).length = w) :
    ∃ v' n, v'.user = v.user ∧ n ≤ unaryCost p l w x.length y.length ∧
      Exec body (fromUnary rg ι h hT hQ pR lR wR srcX padX srcY padY) (mk v S) n
        (mk v' { S with R := (Function.update S.R (rg .out)
          (cstream A w (List.ofFn (coeff p l x y)) ++ S.R (rg .out))) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have haux' := haux
  regs_ne haux'
  have hin' := hin
  regs_ne hin'
  set PX := List.replicate ((2 ^ l - x.length) * w) (tick : Fin (A + 4))
  set PY := List.replicate ((2 ^ l - y.length) * w) (tick : Fin (A + 4))
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := padding_coeffs_exec (body := body)
    (show [lR, wR, srcX, padX, rg .ta, rg .tb].Nodup by simp_all)
    v S x l w hlR hwR hsrcX hpadX (hempty .ta (by simp)) (hempty .tb (by simp))
  set S₁ : Stacks T A := { S with R := Function.update S.R padX PX }
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := padding_coeffs_exec (body := body)
    (show [lR, wR, srcY, padY, rg .ta, rg .tb].Nodup by simp_all)
    v₁ S₁ y l w (by simpa [S₁, ‹lR ≠ padX›] using hlR)
    (by simpa [S₁, ‹wR ≠ padX›] using hwR)
    (by simpa [S₁, ‹srcY ≠ padX›] using hsrcY)
    (by simp [S₁, ‹padX ≠ padY›.symm, hpadY])
    (by simp [S₁, (hoff .ta).1.symm, hempty .ta (by simp)])
    (by simp [S₁, (hoff .tb).1.symm, hempty .tb (by simp)])
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R padY PY }
  have e (r : RpReg) : S₂.R (rg r) = S.R (rg r) := by
    simp [S₂, S₁, (hoff r).1.symm, (hoff r).2.symm]
  have hc₂ : RpClean ι S₂ := by
    refine ⟨hc.1, fun j hj => ?_⟩
    simp [S₂, S₁, (hpriv j).1.symm, (hpriv j).2.symm, hc.2 j hj]
  obtain ⟨v₃, n₃, hu₃, hn₃, he₃⟩ := withHeader_exec (body := body) h hT hQ hA hp hw x y hx hy hxy
    hX hY pR lR wR srcX padX srcY padY hin hreg v₂ S₂ hc₂
    (by simpa [S₂, S₁, ‹srcX ≠ padX›, ‹srcX ≠ padY›] using hsrcX)
    (by simpa [S₂, S₁, ‹srcY ≠ padX›, ‹srcY ≠ padY›] using hsrcY)
    (by simp [S₂, S₁, ‹padX ≠ padY›, PX]) (by simp [S₂, PY])
    (by rw [e]; exact hwn) (fun r hr => by rw [e]; exact hempty r hr)
    (by simpa [S₂, S₁, ‹pR ≠ padX›, ‹pR ≠ padY›] using hpR)
    (by simpa [S₂, S₁, ‹lR ≠ padX›, ‹lR ≠ padY›] using hlR)
    (by simpa [S₂, S₁, ‹wR ≠ padX›, ‹wR ≠ padY›] using hwR)
  set S₃ : Stacks T A := { S₂ with R := (Function.update S₂.R (rg .out)
    (cstream A w (List.ofFn (coeff p l x y)) ++ S₂.R (rg .out))) }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body padX v₃ S₃
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R padX [] }
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body padY v₄ S₄
  refine ⟨v₅, _, hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast rfl ?_⟩
  · have hlenX : (S₃.R padX).length = (2 ^ l - x.length) * w := by
      simp [S₃, S₂, S₁, (hoff .out).1, ‹padX ≠ padY›, PX]
    have hlenY : (S₄.R padY).length = (2 ^ l - y.length) * w := by
      simp [S₄, S₃, S₂, ‹padX ≠ padY›.symm, (hoff .out).2, PY]
    rw [hlenX, hlenY]
    unfold unaryCost paddingCost
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hkX : k = padX
    · subst k
      simp [S₄, S₃, S₂, S₁, ‹padX ≠ padY›, (hoff .out).1, hpadX]
    by_cases hkY : k = padY
    · subst k
      simp [S₄, S₃, S₂, S₁, (hoff .out).2, hpadY]
    simp [S₄, S₃, S₂, S₁, Function.update_apply, hkX, hkY,
      (hoff .out).1.symm, (hoff .out).2.symm]

/-- The entire wrapper adds only linear stream work, dimension work and header work to
one proved packed-product bound. -/
theorem unaryCost_le (p l w a b : ℕ) (ha : a ≤ 2 ^ l) (hb : b ≤ 2 ^ l) :
    unaryCost p l w a b ≤ rpRecBound p l w + rpFixCost p l w + ldrHeaderCost p l w +
      32 * (2 ^ l * w) + 18 * l + 8 * w + 2 * (header p (2 ^ l) w).length + 54 := by
  have hA : (2 ^ l - a) * w + a * w = 2 ^ l * w := by
    rw [← Nat.add_mul, Nat.sub_add_cancel ha]
  have hB : (2 ^ l - b) * w + b * w = 2 ^ l * w := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hb]
  have hrp := rpRecCost_le p l w
  unfold unaryCost paddingCost
  omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
