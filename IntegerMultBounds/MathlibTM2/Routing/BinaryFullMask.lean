module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob
public import IntegerMultBounds.MathlibTM2.Layer.CompactMasks

/-! The unary converter also generates the full one mask used by R2.
No separate raw mask input or bit-by-bit certificate is needed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Node (tick)

theorem binSyms_fullMask {A n : ℕ} :
    binSyms (A := A) n (maskVal n id) = List.replicate n tick := by
  rw [binSyms_eq]
  have hb : binBits n (maskVal n id) = List.replicate n true := by
    unfold binBits
    rw [← List.ofFn_const]
    congr 1
    funext j
    rw [testBit_maskVal strictMono_id]
    simp [j.isLt]
  rw [hb, List.map_replicate]
  rfl

/-- Generate R2's full key mask from its binary width. The input and every
scratch tape are restored; the output may already contain an arbitrary suffix. -/
theorem binaryFullMask_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src dst work tmp ctmp : Fin T)
    (hreg : [src, dst, work, tmp, ctmp].Nodup) (L n : ℕ) (hn : n < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = binSyms L n)
    (hw : S.R work = []) (ht : S.R tmp = []) (hct : S.R ctmp = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ L * (4 * n + 11) + 2 * n + 6 ∧
      Exec body (toUnary src dst work tmp ctmp) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (binSyms n (maskVal n id) ++ S.R dst) }) := by
  obtain ⟨v', m, hu, hm, he⟩ := toUnary_exec body hreg hn v S hsrc hw ht hct
  exact ⟨v', m, hu, hm, by simpa only [binSyms_fullMask] using he⟩

end IntegerMultBounds.MathlibTM2.Routing
