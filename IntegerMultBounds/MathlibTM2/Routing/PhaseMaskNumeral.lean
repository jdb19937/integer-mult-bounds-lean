module

public import IntegerMultBounds.MathlibTM2.Routing.LowPadNumeral
public import IntegerMultBounds.MathlibTM2.Routing.RepeatedPhaseMask

/-! The phase classifier consists of repeated three-mark blocks followed by
one final boundary mark. Low padding then places the complete classifier. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem phaseBlockValue_lt (K G : ℕ) (hG : 0 < G) (hGK : G + 1 < K) :
    phaseBlockValue G < 2 ^ K := by
  have hlow : 3 < 2 ^ (G + 1) := by
    have h := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ G + 1 by omega)
    norm_num at h ⊢
    omega
  have hhigh := Nat.pow_le_pow_right (n := 2) (by decide) (show G + 2 ≤ K by omega)
  have hp : 2 ^ (G + 2) = 2 * 2 ^ (G + 1) := by rw [show G + 2 = (G + 1) + 1 by omega, pow_succ]; omega
  unfold phaseBlockValue
  omega

theorem binSyms_final_one {A : ℕ} (W x : ℕ) (hx : x < 2 ^ W) :
    binSyms (A := A) W x ++ [bitSymbol true] = binSyms (W + 1) (x + 2 ^ W) := by
  have hb := binaryBits_value_repr (binBits W x ++ [true])
  rw [List.length_append, length_binBits, List.length_singleton, counterValue_append,
    binaryCanonical_value_binBits W x hx, length_binBits] at hb
  simp only [Counter.value] at hb
  simp only [ite_true, Nat.mul_one, Nat.mul_zero, Nat.add_zero] at hb
  rw [binSyms_eq, binSyms_eq, hb, List.map_append]
  rfl

theorem phaseMask_repeatedWord {A : ℕ} (p : Par) (hG : 0 < p.G) (hGK : p.G + 1 < p.K) :
    wordCopies (binSyms (A := A) p.K (phaseBlockValue p.G)) p.n ++ [bitSymbol true] =
      binSyms (p.n * p.K + 1)
        (repeatBlockValue p.n p.K (phaseBlockValue p.G) + 2 ^ (p.n * p.K)) := by
  rw [wordCopies_binSyms_eq _ _ _ (phaseBlockValue_lt _ _ hG hGK)]
  exact binSyms_final_one _ _ (repeatBlockValue_lt _ _ _ (phaseBlockValue_lt _ _ hG hGK))

theorem phaseMask_shiftedWord {A : ℕ} (p : Par) (hG : 0 < p.G) (hGK : p.G + 1 < p.K) :
    binSyms (A := A) p.ρ 0 ++
      (wordCopies (binSyms p.K (phaseBlockValue p.G)) p.n ++ [bitSymbol true]) =
      binSyms (p.ρ + (p.n * p.K + 1)) (mkV p) := by
  rw [phaseMask_repeatedWord p hG hGK]
  have hfit := repeatBlockValue_lt p.K (phaseBlockValue p.G) p.n (phaseBlockValue_lt _ _ hG hGK)
  have hfull : repeatBlockValue p.n p.K (phaseBlockValue p.G) + 2 ^ (p.n * p.K) <
      2 ^ (p.n * p.K + 1) := by rw [pow_succ]; omega
  rw [binSyms_lowPad _ _ _ hfull, phaseMask_repeatBlocks p]

end IntegerMultBounds.MathlibTM2.Routing
