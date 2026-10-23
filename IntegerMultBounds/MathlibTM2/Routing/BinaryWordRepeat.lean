module

public import IntegerMultBounds.MathlibTM2.Routing.WordRepeat

/-! Repeat a supplied block a binary-specified number of times. The unary count
is generated, archived/restored by the loop, then erased; every input survives. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

def binaryWordRepeatProgram {T Q A : ℕ} {P U : Type}
    (src count saved block dst work tmp ctmp : Fin T) : Pr P T Q A U :=
  .seq (toUnary src count work tmp ctmp)
    (.seq (wordRepeatProgram count saved block dst tmp ctmp) (bclear count))

def binaryWordRepeatCost (L n blockWidth : ℕ) :=
  (L * (4 * n + 11) + 2 * n + 6) + (n * (6 * blockWidth + 11) + 4) + (2 * n + 2)

theorem binaryWordRepeat_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src count saved block dst work tmp ctmp : Fin T)
    (hreg : [src, count, saved, block, dst, work, tmp, ctmp].Nodup)
    (L n : ℕ) (hn : n < 2 ^ L) (word : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = binSyms L n) (hblock : S.R block = word)
    (hcount : S.R count = []) (hsaved : S.R saved = []) (hwork : S.R work = [])
    (htmp : S.R tmp = []) (hctmp : S.R ctmp = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ binaryWordRepeatCost L n word.length ∧
      Exec body (binaryWordRepeatProgram src count saved block dst work tmp ctmp) (mk v S) m
        (mk v' { S with R := Function.update S.R dst (wordCopies word n ++ S.R dst) }) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := toUnary_exec body (a := src) (z := count) (w := work)
    (t := tmp) (t₂ := ctmp) (by regs_nodup) hn v S hsrc hwork htmp hctmp
  rw [hcount, List.append_nil] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R count (List.replicate n tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := wordRepeat_exec body count saved block dst tmp ctmp
    (by regs_nodup) (List.replicate n tick) word v₁ S₁ (by simp [S₁])
    (by simp [S₁, Ne.symm ‹count ≠ block›, hblock])
    (by simp [S₁, Ne.symm ‹count ≠ saved›, hsaved])
    (by simp [S₁, Ne.symm ‹count ≠ tmp›, htmp]) (by simp [S₁, Ne.symm ‹count ≠ ctmp›, hctmp])
  simp only [List.length_replicate] at hm₂ he₂
  have hd₁ : S₁.R dst = S.R dst := by simp [S₁, Ne.symm ‹count ≠ dst›]
  rw [hd₁] at he₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (wordCopies word n ++ S.R dst) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body count v₂ S₂
  have hc₂ : S₂.R count = List.replicate n tick := by simp [S₂, S₁, ‹count ≠ dst›]
  have hf : Function.update S₂.R count [] = Function.update S.R dst (wordCopies word n ++ S.R dst) := by
    funext j
    by_cases hj : j = count
    · subst j; simp [‹count ≠ dst›, hcount]
    · by_cases hk : j = dst
      · subst j; simp [S₂, hj]
      · simp [S₂, S₁, hj, hk]
  rw [hf, hc₂, List.length_replicate] at he₃
  exact ⟨v₃, m₁ + (m₂ + (2 * n + 2)), hu₃.trans (hu₂.trans hu₁),
    by unfold binaryWordRepeatCost; omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
