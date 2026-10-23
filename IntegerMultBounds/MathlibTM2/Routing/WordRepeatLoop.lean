module

public import IntegerMultBounds.MathlibTM2.Routing.WordRepeatStep

/-! One fixed loop repeats a supplied block once per count-tape symbol.
The complete count is archived in reverse order for subsequent restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

def wordCopies {α : Type} (word : List α) : ℕ → List α
  | 0 => []
  | n + 1 => wordCopies word n ++ word

def wordRepeatBank {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (src saved dst : Fin T) (input word : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src []) saved (input.reverse ++ R saved))
    dst (wordCopies word input.length ++ R dst)

theorem wordRepeatLoop_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (src saved block dst tmp work : Fin T)
    (hreg : [src, saved, block, dst, tmp, work].Nodup)
    (input word : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = input) (hblock : S.R block = word)
    (htmp : S.R tmp = []) (hwork : S.R work = []) (hflag : v.flag = input.head?.isSome) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ input.length * (6 * word.length + 9) + 1 ∧
      Exec body (.loop (·.flag) (wordRepeatStepProgram src saved block dst tmp work)) (mk v S) m
        (mk v' { S with R := wordRepeatBank S.R src saved dst input word }) := by
  have hn := hreg
  regs_ne hn
  induction input generalizing v S with
  | nil =>
    have hb : wordRepeatBank S.R src saved dst [] word = S.R := by
      funext j
      by_cases hj : j = dst
      · subst j; simp [wordRepeatBank, wordCopies]
      · by_cases hk : j = saved
        · subst j; simp [wordRepeatBank, hj]
        · by_cases hs : j = src
          · subst j; simp [wordRepeatBank, wordCopies, hj, hk, hsrc]
          · simp [wordRepeatBank, wordCopies, hj, hk, hs]
    refine ⟨v, 1, rfl, by simp, ?_⟩
    rw [hb]
    exact Exec.loop_false (by simpa only [List.head?_nil, Option.isSome_none, mk_var] using hflag)
  | cons x input ih =>
    obtain ⟨v₁, hu₁, hf₁, he₁⟩ := wordRepeatStep_exec body src saved block dst tmp work hreg x input word
      v S hsrc hblock htmp hwork
    let S₁ : Stacks T A := { S with R := wordRepeatStepBank S.R src saved dst x input word }
    have hs₁ : S₁.R src = input := by simp [S₁, wordRepeatStepBank, ‹src ≠ dst›, ‹src ≠ saved›]
    have hb₁ : S₁.R block = word := by
      simp [S₁, wordRepeatStepBank, (Ne.symm ‹src ≠ block›), (Ne.symm ‹saved ≠ block›), ‹block ≠ dst›, hblock]
    have ht₁ : S₁.R tmp = [] := by
      simp [S₁, wordRepeatStepBank, (Ne.symm ‹src ≠ tmp›), (Ne.symm ‹saved ≠ tmp›), (Ne.symm ‹dst ≠ tmp›), htmp]
    have hw₁ : S₁.R work = [] := by
      simp [S₁, wordRepeatStepBank, (Ne.symm ‹src ≠ work›), (Ne.symm ‹saved ≠ work›), (Ne.symm ‹dst ≠ work›), hwork]
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ih v₁ S₁ hs₁ hb₁ ht₁ hw₁ hf₁
    have hb : wordRepeatBank S₁.R src saved dst input word = wordRepeatBank S.R src saved dst (x :: input) word := by
      funext j
      by_cases hj : j = dst
      · subst j; simp [wordRepeatBank, wordRepeatStepBank, S₁, wordCopies, List.append_assoc]
      · by_cases hk : j = saved
        · subst j; simp [wordRepeatBank, wordRepeatStepBank, S₁, ‹saved ≠ dst›, List.append_assoc]
        · by_cases hs : j = src
          · subst j; simp [wordRepeatBank, wordRepeatStepBank, S₁, ‹src ≠ dst›, ‹src ≠ saved›]
          · simp [wordRepeatBank, wordRepeatStepBank, S₁, hj, hk, hs]
    rw [hb] at he₂
    refine ⟨v₂, (6 * word.length + 8) + m₂ + 1, hu₂.trans hu₁, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    · exact Exec.cast (Exec.loop_true (by simpa only [List.head?_cons, Option.isSome_some, mk_var] using hflag) he₁ he₂)
        (by omega) rfl

end IntegerMultBounds.MathlibTM2.Routing
