module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvExec

/-! # Pack, multiply, and restore the short-convolution workspace

One uniform program starts with two raw coefficient blocks and unary symbol-padding counts.
It packs both blocks, invokes the existing ring-product stage, and clears the packed copies.
Only the output register changes. Header and padding-counter generation are caller setup;
their words are explicitly specified, never hidden behind an execution hypothesis.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.Spec.SignedRingProduct

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

noncomputable def program (rg : RpReg → Fin T) (ι : Fin 91 → Fin T)
    (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q)
    (srcX padX srcY padY : Fin T) : Pr P T Q A U :=
  .seq (packBlock srcX padX (rg .xs) (rg .ta) (rg .tb)) <|
  .seq (packBlock srcY padY (rg .ys) (rg .ta) (rg .tb)) <|
  .seq (rpProg rg ι h.ι_inj hT hQ) <|
  .seq (uclear (rg .xs)) (uclear (rg .ys))

/-- Both raw blocks and all scratch are restored; only the output stream grows. -/
theorem program_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w) (x y : List GaussianInt)
    (hx : x.length ≤ 2 ^ l) (hy : y.length ≤ 2 ^ l)
    (hxy : x.length + y.length ≤ 2 ^ l + 1)
    (hX : ∀ z ∈ x, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ z ∈ y, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (srcX padX srcY padY : Fin T)
    (hreg : [srcX, padX, srcY, padY, rg .xs, rg .ys, rg .ta, rg .tb].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hsrcX : S.R srcX = cstream A w x) (hsrcY : S.R srcY = cstream A w y)
    (hpadX : (S.R padX).length = (2 ^ l - x.length) * w)
    (hpadY : (S.R padY).length = (2 ^ l - y.length) * w)
    (hwn : (S.R (rg .wn)).length = w)
    (hempty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3], S.R (rg r) = [])
    (hd0 : S.R (rg .d0) = (header p (2 ^ l) w).map bitSymbol) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 4 * ((2 ^ l - x.length) * w) + 6 * (x.length * w) +
        4 * ((2 ^ l - y.length) * w) + 6 * (y.length * w) +
        rpRecCost p l w + rpFixCost p l w + 4 * (2 ^ l * w) + 24 ∧
      Exec body (program rg ι h hT hQ srcX padX srcY padY) (mk v S) n
        (mk v' { S with R := (Function.update S.R (rg .out)
          (cstream A w (List.ofFn (coeff p l x y)) ++ S.R (rg .out))) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have ne (r s : RpReg) (hrs : r ≠ s) : rg r ≠ rg s := h.rg_inj.ne hrs
  have empty (r : RpReg) (hr : r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d1, .d2, .d3]) :=
    hempty r hr
  set X := cstream A w (List.ofFn (recOf (2 ^ l) (block x)))
  set Y := cstream A w (List.ofFn (recOf (2 ^ l) (block y)))
  obtain ⟨v₁, hu₁, he₁⟩ := packBlock_coeffs_exec (body := body)
    (show [srcX, padX, rg .xs, rg .ta, rg .tb].Nodup by simp_all) v S x (2 ^ l) w hx
    hsrcX hpadX (empty _ (by simp)) (empty _ (by simp)) (empty _ (by simp))
  set S₁ : Stacks T A := { S with R := Function.update S.R (rg .xs) X }
  obtain ⟨v₂, hu₂, he₂⟩ := packBlock_coeffs_exec (body := body)
    (show [srcY, padY, rg .ys, rg .ta, rg .tb].Nodup by simp_all) v₁ S₁ y (2 ^ l) w hy
    (by simpa [S₁, ‹srcY ≠ rg .xs›] using hsrcY)
    (by simpa [S₁, ‹padY ≠ rg .xs›] using hpadY)
    (by simp [S₁, ne .ys .xs (by decide), empty .ys (by simp)])
    (by simp [S₁, ne .ta .xs (by decide), empty .ta (by simp)])
    (by simp [S₁, ne .tb .xs (by decide), empty .tb (by simp)])
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .ys) Y }
  have e (r : RpReg) (hx : r ≠ .xs) (hy : r ≠ .ys) : S₂.R (rg r) = S.R (rg r) := by
    simp [S₂, S₁, ne r .xs hx, ne r .ys hy]
  have hc₂ : RpClean ι S₂ := by
    refine ⟨hc.1, fun j hj => ?_⟩
    simp [S₂, S₁, (h.priv .xs j hj).symm, (h.priv .ys j hj).symm, hc.2 j hj]
  obtain ⟨v₃, n₃, hu₃, hn₃, he₃⟩ := shortConv_exec (body := body) h hT hQ hA hp hw x y hxy
    (diskGrid_block p (2 ^ l) x hX) (diskGrid_block p (2 ^ l) y hY) v₂ S₂ hc₂
    (by simp [S₂, S₁, ne .xs .ys (by decide), X]) (by simp [S₂, Y])
    (by rw [e .wn (by decide) (by decide)]; exact hwn)
    (by rw [e .sv (by decide) (by decide)]; exact empty _ (by simp))
    (by rw [e .ta (by decide) (by decide)]; exact empty _ (by simp))
    (by rw [e .tb (by decide) (by decide)]; exact empty _ (by simp))
    (by rw [e .acc (by decide) (by decide)]; exact empty _ (by simp))
    (by rw [e .tmp (by decide) (by decide)]; exact empty _ (by simp))
    (by rw [e .d0 (by decide) (by decide)]; exact hd0)
    (by rw [e .d1 (by decide) (by decide)]; exact empty _ (by simp))
    (by rw [e .d2 (by decide) (by decide)]; exact empty _ (by simp))
    (by rw [e .d3 (by decide) (by decide)]; exact empty _ (by simp))
  set S₃ : Stacks T A := { S₂ with R := (Function.update S₂.R (rg .out)
    (cstream A w (List.ofFn (coeff p l x y)) ++ S₂.R (rg .out))) }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body (rg .xs) v₃ S₃
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R (rg .xs) [] }
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body (rg .ys) v₄ S₄
  refine ⟨v₅, _, hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast rfl ?_⟩
  · have hlenX : (S₃.R (rg .xs)).length = 2 ^ l * w := by
      simp [S₃, S₂, S₁, ne .xs .out (by decide), ne .xs .ys (by decide), X]
    have hlenY : (S₄.R (rg .ys)).length = 2 ^ l * w := by
      simp [S₄, S₃, S₂, ne .ys .xs (by decide), ne .ys .out (by decide), Y]
    rw [hlenX, hlenY]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hxs : k = rg .xs
    · subst k
      simp [S₄, S₃, S₂, S₁, ne .xs .ys (by decide), ne .xs .out (by decide), empty .xs (by simp)]
    by_cases hys : k = rg .ys
    · subst k
      simp [S₄, S₃, S₂, S₁, ne .ys .out (by decide), empty .ys (by simp)]
    simp [S₄, S₃, S₂, S₁, Function.update_apply, hxs, hys,
      ne .out .xs (by decide), ne .out .ys (by decide)]

/-- Packing both operands and clearing their copies is linear in the padded stream size. -/
theorem overhead_le (r w a b : ℕ) (ha : a ≤ r) (hb : b ≤ r) :
    4 * ((r - a) * w) + 6 * (a * w) +
      4 * ((r - b) * w) + 6 * (b * w) + 4 * (r * w) + 24 ≤ 16 * (r * w) + 24 := by
  have hA : (r - a) * w + a * w = r * w := by
    rw [← Nat.add_mul, Nat.sub_add_cancel ha]
  have hB : (r - b) * w + b * w = r * w := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hb]
  omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
