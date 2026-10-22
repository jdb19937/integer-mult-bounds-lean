module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConv
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! # Packing finite blocks for a short convolution

The finite input block is followed by zeros. `packBlock` constructs its actual pair-symbol
stream, preserving the raw input and the unary padding counter and restoring both work tapes.
The counter counts pair symbols (not bits or coefficients); its construction belongs to the
caller. The program is independent of every block length and coefficient width.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer

/-- Extend a finite block by zero coefficients. -/
def block (x : List GaussianInt) (i : ℕ) : GaussianInt := x[i]?.getD 0

@[simp] theorem block_eq_zero (x : List GaussianInt) {i : ℕ} (hi : x.length ≤ i) :
    block x i = 0 := by simp [block, List.getElem?_eq_none hi]

/-- The padded record, in coefficient order. -/
theorem ofFn_recOf_block (x : List GaussianInt) {r : ℕ} (hx : x.length ≤ r) :
    List.ofFn (recOf r (block x)) = x ++ List.replicate (r - x.length) 0 := by
  apply List.ext_getElem (by simp ; omega)
  intro i h₁ h₂
  simp only [List.length_ofFn] at h₁
  simp only [List.getElem_ofFn, recOf, block]
  by_cases hi : i < x.length
  · rw [List.getElem?_eq_getElem hi, Option.getD_some, List.getElem_append_left hi]
  · rw [List.getElem?_eq_none (by omega), Option.getD_none,
      List.getElem_append_right (by omega), List.getElem_replicate]

/-- A zero numerator is represented by `w` zero pair symbols. -/
theorem csyms_zero (A w : ℕ) :
    csyms A w 0 = List.replicate w (pairSym A false false) := by
  simp [csyms, coeffSyms, red, List.ofFn_const]

/-- Symbol-level packing agrees with the ring-product record format. -/
theorem cstream_recOf_block (A w : ℕ) (x : List GaussianInt) {r : ℕ}
    (hx : x.length ≤ r) :
    cstream A w (List.ofFn (recOf r (block x))) =
      cstream A w x ++ List.replicate ((r - x.length) * w) (pairSym A false false) := by
  rw [ofFn_recOf_block x hx, cstream_append]
  congr 1
  induction r - x.length with
  | zero => simp [cstream]
  | succ n ih =>
      rw [List.replicate_succ, cstream_cons, ih, csyms_zero,
        List.replicate_append_replicate]
      congr 1
      ring

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Pad first, then copy the original block onto the padding. -/
def packBlock (src pad dst t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (umulSym 1 (pairSym A false false) pad dst t₁) (bcopy src dst t₁ t₂)

/-- Exact packing cost, with restored inputs and scratch and arbitrary left stacks. -/
theorem packBlock_exec {src pad dst t₁ t₂ : Fin T}
    (hreg : [src, pad, dst, t₁, t₂].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (packBlock src pad dst t₁ t₂) (mk v S)
        (4 * (S.R pad).length + 6 * (S.R src).length + 10)
        (mk v' { S with R := (Function.update S.R dst
          (S.R src ++ List.replicate (S.R pad).length (pairSym A false false) ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := umulSym_exec body 1 (pairSym A false false)
    ‹pad ≠ dst› ‹pad ≠ t₁› ‹dst ≠ t₁› v S ht₁
  obtain ⟨v₂, hu₂, he₂⟩ := bcopy_exec body
    (show [src, dst, t₁, t₂].Nodup by simp_all) v₁
    { S with R := (Function.update S.R dst
      (List.replicate (1 * (S.R pad).length) (pairSym A false false) ++ S.R dst)) }
    (by simp [ht₁, Ne.symm ‹dst ≠ t₁›]) (by simp [ht₂, Ne.symm ‹dst ≠ t₂›])
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by simp [‹src ≠ dst›]; omega) ?_⟩
  congr 1
  simp [‹src ≠ dst›, List.append_assoc]

/-- Packing a raw coefficient block produces exactly one padded ring record. -/
theorem packBlock_coeffs_exec {src pad dst t₁ t₂ : Fin T}
    (hreg : [src, pad, dst, t₁, t₂].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (x : List GaussianInt) (r w : ℕ) (hx : x.length ≤ r)
    (hsrc : S.R src = cstream A w x) (hpad : (S.R pad).length = (r - x.length) * w)
    (hdst : S.R dst = []) (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (packBlock src pad dst t₁ t₂) (mk v S)
        (4 * ((r - x.length) * w) + 6 * (x.length * w) + 10)
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (List.ofFn (recOf r (block x))))) }) := by
  obtain ⟨v', hu, he⟩ := packBlock_exec hreg v S ht₁ ht₂
  refine ⟨v', hu, he.cast ?_ ?_⟩
  · simp [hsrc, hpad, cstream]
  · rw [hsrc, hpad, hdst, List.append_nil, cstream_recOf_block A w x hx]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
