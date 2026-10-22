module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPacking

/-! # Generate padding counters from dimensions and raw blocks

Copy the unary word width, double it once per unary exponent symbol, then subtract the raw
block's symbol length. The inputs and both scratch tapes are restored. No padded-size word
is supplied for free.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Generate the symbol-padding count for a raw coefficient block. -/
def padding (lR wR src pad t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (ucopy wR pad t₁) (.seq (upow2 lR pad t₁ t₂) (usub src pad t₁))

/-- Padding generation costs linear time in the padded stream, raw stream and exponent. -/
theorem padding_exec {lR wR src pad t₁ t₂ : Fin T}
    (hreg : [lR, wR, src, pad, t₁, t₂].Nodup)
    (v : HS T Q A U) (S : Stacks T A)
    (hpad : S.R pad = []) (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 4 * (S.R wR).length + 4 * (2 ^ (S.R lR).length * (S.R wR).length) +
        9 * (S.R lR).length + 4 * (S.R src).length + 12 ∧
      Exec body (padding lR wR src pad t₁ t₂) (mk v S) n
        (mk v' { S with R := (Function.update S.R pad
          (List.replicate (2 ^ (S.R lR).length * (S.R wR).length - (S.R src).length) tick)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body ‹wR ≠ pad› ‹wR ≠ t₁› ‹pad ≠ t₁› v S ht₁
  rw [hpad, List.append_nil] at he₁
  set S₁ : Stacks T A := { S with R := Function.update S.R pad (List.replicate (S.R wR).length tick) }
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := upow2_exec body
    (show [lR, pad, t₁, t₂].Nodup by simp_all) v₁ S₁
    (by simp [S₁, ‹pad ≠ t₁›.symm, ht₁]) (by simp [S₁, ‹pad ≠ t₂›.symm, ht₂])
  have hflat : (S₁.R pad).flatMap (List.replicate (2 ^ (S₁.R lR).length)) =
      List.replicate (2 ^ (S.R lR).length * (S.R wR).length) tick := by
    simp [S₁, ‹lR ≠ pad›, List.flatMap_replicate,
      Nat.mul_comm]
  rw [hflat] at he₂
  set S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R pad
    (List.replicate (2 ^ (S.R lR).length * (S.R wR).length) tick)) }
  obtain ⟨v₃, hu₃, he₃⟩ := usub_exec body ‹src ≠ pad› ‹src ≠ t₁› ‹pad ≠ t₁› v₂ S₂
    (by simp [S₂, S₁, ‹pad ≠ t₁›.symm, ht₁])
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · simp only [S₁, Function.update_self, List.length_replicate,
      Function.update_of_ne ‹lR ≠ pad›] at hn₂
    simp only [S₂, S₁, Function.update_of_ne ‹src ≠ pad›]
    omega
  · congr 1
    simp [S₂, S₁, ‹src ≠ pad›, List.drop_replicate]

/-- On a raw block, the generated counter is precisely the missing coefficients
 times the pair-symbol width, including empty blocks and zero padding. -/
theorem padding_coeffs_exec {lR wR src pad t₁ t₂ : Fin T}
    (hreg : [lR, wR, src, pad, t₁, t₂].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (x : List GaussianInt) (l w : ℕ)
    (hl : (S.R lR).length = l) (hw : (S.R wR).length = w)
    (hsrc : S.R src = cstream A w x)
    (hpad : S.R pad = []) (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 4 * w + 4 * (2 ^ l * w) + 9 * l + 4 * (x.length * w) + 12 ∧
      Exec body (padding lR wR src pad t₁ t₂) (mk v S) n
        (mk v' { S with R := (Function.update S.R pad
          (List.replicate ((2 ^ l - x.length) * w) tick)) }) := by
  obtain ⟨v', n, hu, hn, he⟩ := padding_exec hreg v S hpad ht₁ ht₂
  rw [hl, hw, hsrc, length_cstream] at hn he
  rw [← Nat.sub_mul] at he
  exact ⟨v', n, hu, hn, he⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
