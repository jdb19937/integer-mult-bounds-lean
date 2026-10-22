module

public import IntegerMultBounds.MathlibTM2.Node.CompactRotCodes

/-! Spread compact borrowed digits with a final classifier-flush column. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par) (hG : 0 < p.G) (hGK : p.G < p.K)

include hG hGK in
/-- The old spread identity with an additional high zero column. -/
theorem spread_mAV_padded (value : ℕ) :
    spreadL (binBits p.wc value) (binBits (p.wy + 1) (mAV p)) =
      binBits (p.wy + 1) (placeVal (p.n * p.G) (posA p) value.testBit) := by
  have he := spread_mAV (p := { p with m := p.m + 1 }) hG hGK value
  have hp : posA { p with m := p.m + 1 } = posA p := rfl
  simp only [Par.wy, Par.wc, mAV, Nat.add_assoc] at he
  rw [hp] at he
  simpa only [Par.wy, Par.wc, mAV, Nat.add_assoc] using he

variable {T Q A : ℕ} {P U : Type}

include hG hGK in
/-- Actual padded spreading, with all mask/source and scan scratch restored. -/
theorem spreadPadded_exec (body : P → Pr P T Q A U)
    {src mask ts tm dst out : Fin T} (hregs : GSRegs src mask ts tm dst out)
    (value : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hmask : S.R mask = binSyms (p.wy + 1) (mAV p))
    (hsrc : S.R src = binSyms p.wc value)
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ 8 * (p.wy + 1) + 8 ∧
      Exec body (spread src mask ts tm dst out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (binSyms (p.wy + 1) (placeVal (p.n * p.G) (posA p) value.testBit) ++ S.R out) }) := by
  have hcount : (binBits (p.wy + 1) (mAV p)).count true = (binBits p.wc value).length := by
    rw [mAV, count_maskVal (posA_mono hG hGK)
      (fun j hj => Nat.lt_succ_of_lt (posA_lt hG hGK hj))]
    simp [Par.wc, binBits]
  obtain ⟨v', steps, hu, hm, he⟩ := spread_exec body hregs
    (binBits (p.wy + 1) (mAV p)) (binBits p.wc value) hcount v S
    (by simpa only [binSyms_eq] using hmask) (by simpa only [binSyms_eq] using hsrc)
    hts htm hdst
  rw [spread_mAV_padded p hG hGK value, ← binSyms_eq] at he
  exact ⟨v', steps, hu, by simpa [binBits] using hm, he⟩

end IntegerMultBounds.MathlibTM2.Routing
