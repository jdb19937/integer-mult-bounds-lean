module

public import IntegerMultBounds.MathlibTM2.Routing.MetadataJob

/-! Append high zeros from a binary padding length. The unary length and all
scratch are generated and erased, leaving only the extended output register. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

def binaryHighPadProgram {T Q A : ℕ} {P U : Type} (src unary dst work tmp ctmp : Fin T) : Pr P T Q A U :=
  .seq (toUnary src unary work tmp ctmp) (.seq (bpad dst unary tmp ctmp) (bclear unary))

theorem binaryHighPad_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src unary dst work tmp ctmp : Fin T)
    (hreg : [src, unary, dst, work, tmp, ctmp].Nodup) (L e W x : ℕ) (he : e < 2 ^ L) (hx : x < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = binSyms L e) (hdst : S.R dst = binSyms W x)
    (hunary : S.R unary = []) (hwork : S.R work = []) (htmp : S.R tmp = []) (hctmp : S.R ctmp = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ L * (4 * e + 11) + 10 * e + 4 * W + 16 ∧
      Exec body (binaryHighPadProgram src unary dst work tmp ctmp) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (binSyms (W + e) x) }) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := toUnary_exec body (a := src) (z := unary) (w := work)
    (t := tmp) (t₂ := ctmp) (by regs_nodup) he v S hsrc hwork htmp hctmp
  rw [hunary, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R unary (List.replicate e tick) }
  obtain ⟨v₂, hu₂, he₂⟩ := bpad_exec body (a := dst) (eR := unary) (t₁ := tmp) (t₂ := ctmp)
    (by regs_nodup) hx v₁ S₁ (by simp [S₁, Ne.symm ‹unary ≠ dst›, hdst])
    (by simp [S₁, Ne.symm ‹unary ≠ tmp›, htmp]) (by simp [S₁, Ne.symm ‹unary ≠ ctmp›, hctmp])
  have hu₁' : S₁.R unary = List.replicate e tick := by simp [S₁]
  rw [hu₁', List.length_replicate] at he₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (binSyms (W + e) x) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body unary v₂ S₂
  have hu₂' : S₂.R unary = List.replicate e tick := by simp [S₂, S₁, ‹unary ≠ dst›]
  have hf : Function.update S₂.R unary [] = Function.update S.R dst (binSyms (W + e) x) := by
    funext j
    by_cases hj : j = unary
    · subst j; simp [‹unary ≠ dst›, hunary]
    · by_cases hd : j = dst
      · subst j; simp [S₂, hj]
      · simp [S₂, S₁, hj, hd]
  rw [hf, hu₂', List.length_replicate] at he₃
  exact ⟨v₃, m₁ + ((4 * W + 6 * e + 8) + (2 * e + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
