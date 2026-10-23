module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFullMask

/-! Construct a repeated temporary-mask block from a binary run length and a
padding tape. All inputs and scratch are restored; only the block output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks

def paddedOnesBlockProgram {T Q A : ℕ} {P U : Type} (src high dst work tmp ctmp : Fin T) : Pr P T Q A U :=
  .seq (toUnary src dst work tmp ctmp) (bpad dst high tmp ctmp)

theorem paddedOnesBlock_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src high dst work tmp ctmp : Fin T)
    (hreg : [src, high, dst, work, tmp, ctmp].Nodup) (L G : ℕ) (hG : G < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = binSyms L G)
    (hdst : S.R dst = []) (hwork : S.R work = []) (htmp : S.R tmp = []) (hctmp : S.R ctmp = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ L * (4 * G + 11) + 6 * G + 6 * (S.R high).length + 14 ∧
      Exec body (paddedOnesBlockProgram src high dst work tmp ctmp) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (binSyms (G + (S.R high).length) (maskVal G id)) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryFullMask_exec body src dst work tmp ctmp
    (by regs_nodup) L G hG v S hsrc hwork htmp hctmp
  rw [hdst, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R dst (binSyms G (maskVal G id)) }
  have hfit : maskVal G id < 2 ^ G := by
    rw [maskVal_eq_placeVal]
    exact placeVal_lt strictMono_id _ G
  obtain ⟨v₂, hu₂, he₂⟩ := bpad_exec body (a := dst) (eR := high) (t₁ := tmp) (t₂ := ctmp)
    (by regs_nodup) hfit v₁ S₁ (by simp [S₁])
    (by simp [S₁, Ne.symm ‹dst ≠ tmp›, htmp]) (by simp [S₁, Ne.symm ‹dst ≠ ctmp›, hctmp])
  have hh₁ : S₁.R high = S.R high := by simp [S₁, ‹high ≠ dst›]
  rw [hh₁] at he₂
  have hf : Function.update S₁.R dst (binSyms (G + (S.R high).length) (maskVal G id)) =
      Function.update S.R dst (binSyms (G + (S.R high).length) (maskVal G id)) := by
    simp only [S₁, Function.update_idem]
  rw [hf] at he₂
  exact ⟨v₂, m₁ + (4 * G + 6 * (S.R high).length + 8), hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
