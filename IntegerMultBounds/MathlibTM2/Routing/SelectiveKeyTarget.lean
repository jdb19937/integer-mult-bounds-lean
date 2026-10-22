module

public import IntegerMultBounds.MathlibTM2.Routing.PatternKey
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveKeyPattern

/-! The executed target digit of the full selective destination key. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T Q A : ℕ} {P U : Type}

def selectiveKeyTargetCost (p : Par) (X : ℕ) : ℕ :=
  p.wy * (6 * (p.wy + 2 * p.wc + X) + 25) + 8 * (p.wy + 2 * p.wc + X) + 45

/-- Actual source descriptor interpretation, target XOR emission and cleanup,
from the unchanged physical five-field bank. No precomputed source word enters. -/
theorem selectiveKeyTarget_exec (p : Par) (X : ℕ) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (body : P → Pr P T Q A U) (cf : Fin 5 → Fin T)
    {header desc ts tm dst word mask t0 t1 t2 acc st : Fin T}
    (hregs : [header, desc, ts, tm, dst, word, cf 1, mask, t0, t1, t2, acc].Nodup)
    (hst : st ∉ [cf 1, word, mask])
    (hfields : ∀ f ∈ higherFields (0 : Fin 5), cf f ≠ header ∧ cf f ≠ ts ∧ cf f ≠ tm)
    (i : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hcf : ∀ f, S.R (cf f) = binSyms (selectiveLen p X f) (digit (selectiveLen p X) f i))
    (hheader : S.R header = []) (hword : S.R word = [])
    (hdesc : S.R desc = (patternTable (selectiveKeyPattern p X active s)).flatten.map bitSymbol)
    (hmask : S.R mask = binSyms p.wy (maskVal p.wy id))
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = [])
    (ht0 : S.R t0 = []) (ht1 : S.R t1 = []) (ht2 : S.R t2 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (patternKey ((higherFields (0 : Fin 5)).map cf)
        header desc ts tm dst word (cf 1) mask t0 t1 t2 acc st) (mk v S)
        (selectiveKeyTargetCost p X)
        (mk v' { S with R := Function.update S.R acc ((binSyms p.wy
          ((selectiveView p X i).y ^^^ targetWord p active s
            (selectiveView p X i).y (selectiveView p X i).x)).reverse ++ S.R acc) }) := by
  have hchain : HeaderChain (selectiveLen p X) p.wc (higherFields (0 : Fin 5)) := by
    have hc := higherFields_chain (selectiveLen p X) 0
    rw [selectiveFieldOff] at hc
    simpa [selectiveLen] using hc
  have hv := headerValue (A := A) (selectiveLen p X) (higherFields (0 : Fin 5)) p.wc i hchain
  rw [selectiveHeader_b] at hv
  have hsource : (((higherFields (0 : Fin 5)).map cf).flatMap S.R) =
      binSyms (p.wy + 2 * p.wc + X) ((i / 2 ^ p.wc) % 2 ^ (p.wy + 2 * p.wc + X)) := by
    simp only [List.flatMap_map]
    simp_rw [hcf]
    exact hv.trans (binSyms_mod _ _).symm
  obtain ⟨v', hu, he⟩ := patternKey_exec body ((higherFields (0 : Fin 5)).map cf)
    hregs hst (fun f hf => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hf
      exact hfields j hj)
    (selectiveKeyPattern p X active s)
    ((i / 2 ^ p.wc) % 2 ^ (p.wy + 2 * p.wc + X)) (selectiveView p X i).y v S
    hheader hword hsource hdesc (hcf 1) hmask hts htm hdst ht0 ht1 ht2
  rw [selectiveKeyPattern_value p X active s hK i] at he
  have hc : sourceHeaderCost S.R ((higherFields (0 : Fin 5)).map cf) =
      6 * (p.wy + 2 * p.wc + X) + 25 := by
    simp [higherFields, fieldRun, sourceHeaderCost, hcf, selectiveLen]
    omega
  rw [hc] at he
  refine ⟨v', hu, Exec.cast he ?_ rfl⟩
  unfold selectiveKeyTargetCost
  ring

end IntegerMultBounds.MathlibTM2.Routing
