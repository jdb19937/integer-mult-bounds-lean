module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvProgram
public import IntegerMultBounds.MathlibTM2.Fast.LoadRing

/-! # Generated headers for the shared short-convolution program

Generate the ring header from unary parameters, execute the complete block program, and
clear the header. The complete final bank differs only at the output register.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.Spec.SignedRingProduct

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

noncomputable def withHeader (rg : RpReg → Fin T) (ι : Fin 91 → Fin T)
    (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q)
    (pR lR wR srcX padX srcY padY : Fin T) : Pr P T Q A U :=
  .seq (ldrHeader pR lR wR (rg .d0) (rg .ta) (rg .tb) (rg .acc) (rg .sv) (rg .tmp))
    (.seq (program rg ι h hT hQ srcX padX srcY padY) (uclear (rg .d0)))

/-- Actual header generation and cleanup are both charged. -/
theorem withHeader_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w) (x y : List GaussianInt)
    (hx : x.length ≤ 2 ^ l) (hy : y.length ≤ 2 ^ l)
    (hxy : x.length + y.length ≤ 2 ^ l + 1)
    (hX : ∀ z ∈ x, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ z ∈ y, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (pR lR wR srcX padX srcY padY : Fin T)
    (hin : [pR, lR, wR, rg .d0, rg .ta, rg .tb, rg .acc, rg .sv, rg .tmp].Nodup)
    (hreg : [srcX, padX, srcY, padY, rg .xs, rg .ys, rg .ta, rg .tb, rg .d0].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hsrcX : S.R srcX = cstream A w x) (hsrcY : S.R srcY = cstream A w y)
    (hpadX : (S.R padX).length = (2 ^ l - x.length) * w)
    (hpadY : (S.R padY).length = (2 ^ l - y.length) * w)
    (hwn : (S.R (rg .wn)).length = w)
    (hempty : ∀ r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d0, .d1, .d2, .d3], S.R (rg r) = [])
    (hpR : (S.R pR).length = p) (hlR : (S.R lR).length = l) (hwR : (S.R wR).length = w) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ ldrHeaderCost p l w +
        (4 * ((2 ^ l - x.length) * w) + 6 * (x.length * w) +
         4 * ((2 ^ l - y.length) * w) + 6 * (y.length * w) +
         rpRecCost p l w + rpFixCost p l w + 4 * (2 ^ l * w) + 24) +
        2 * (header p (2 ^ l) w).length + 2 ∧
      Exec body (withHeader rg ι h hT hQ pR lR wR srcX padX srcY padY) (mk v S) n
        (mk v' { S with R := (Function.update S.R (rg .out)
          (cstream A w (List.ofFn (coeff p l x y)) ++ S.R (rg .out))) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have ne (r s : RpReg) (hrs : r ≠ s) : rg r ≠ rg s := h.rg_inj.ne hrs
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := ldrHeader_exec body hin v S
    (hempty .ta (by simp)) (hempty .tb (by simp)) (hempty .acc (by simp))
    (hempty .sv (by simp)) (hempty .tmp (by simp))
  rw [hpR, hlR, hwR, hempty .d0 (by simp), List.append_nil] at he₁
  rw [hpR, hlR, hwR] at hn₁
  set S₁ : Stacks T A := { S with R := (Function.update S.R (rg .d0)
    ((header p (2 ^ l) w).map bitSymbol)) }
  have hc₁ : RpClean ι S₁ := by
    refine ⟨hc.1, fun j hj => ?_⟩
    simp [S₁, (h.priv .d0 j hj).symm, hc.2 j hj]
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := program_exec (body := body) h hT hQ hA hp hw x y hx hy hxy
    hX hY srcX padX srcY padY (by simp_all) v₁ S₁ hc₁
    (by simpa [S₁, ‹srcX ≠ rg .d0›] using hsrcX)
    (by simpa [S₁, ‹srcY ≠ rg .d0›] using hsrcY)
    (by simpa [S₁, ‹padX ≠ rg .d0›] using hpadX)
    (by simpa [S₁, ‹padY ≠ rg .d0›] using hpadY)
    (by simpa [S₁, ne .wn .d0 (by decide)] using hwn)
    (fun r hr => by
      have hr0 : r ≠ .d0 := by intro he; subst r; simp at hr
      have hr' : r ∈ [RpReg.xs, .ys, .sv, .ta, .tb, .acc, .tmp, .d0, .d1, .d2, .d3] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h | h | h | h | h | h <;> simp_all
      simpa [S₁, ne r .d0 hr0] using hempty r hr')
    (by simp [S₁])
  set S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R (rg .out)
    (cstream A w (List.ofFn (coeff p l x y)) ++ S₁.R (rg .out))) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (rg .d0) v₂ S₂
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · have hlen : (S₂.R (rg .d0)).length = (header p (2 ^ l) w).length := by
      simp [S₂, S₁, ne .d0 .out (by decide)]
    rw [hlen]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = rg .d0
    · subst k
      simp [S₂, S₁, ne .d0 .out (by decide), hempty .d0 (by simp)]
    · simp [S₂, S₁, Function.update_apply, hk, ne .out .d0 (by decide)]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
