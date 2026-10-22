module

public import IntegerMultBounds.MathlibTM2.Host.WordTape

/-!
# Uniform removal of a metadata prefix

After reversing a computed binary word, this scanner removes its high zero
padding. The stopping predicate, rather than a supplied count, controls code.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def configurationDropStep (src : Fin T) (p : Fin (A + 4) → Bool) : Act T Q A U :=
  .pop (.rt src) (fun v _ => v) (WordCmd.peekRp src p)

def configurationDrop (src : Fin T) (p : Fin (A + 4) → Bool) : Pr P T Q A U :=
  .seq (.act (WordCmd.peekRp src p)) (.loop (·.flag) (.act (configurationDropStep src p)))

theorem configurationDrop_loop (body : P → Pr P T Q A U) (src : Fin T)
    (p : Fin (A + 4) → Bool) (rest : List (Fin (A + 4)))
    (hrest : (rest.head?.map p).getD false = false) :
    ∀ (word : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      (∀ x ∈ word, p x = true) → S.R src = word ++ rest →
      v.flag = ((word ++ rest).head?.map p).getD false →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (configurationDropStep src p))) (mk v S)
          (2 * word.length + 1) (mk v' { S with R := Function.update S.R src rest }) := by
  intro word
  induction word with
  | nil =>
    intro v S _ hsrc hflag
    have he : Function.update S.R src rest = S.R := by
      have hs : S.R src = rest := by simpa using hsrc
      rw [← hs]
      simp
    refine ⟨v, rfl, ?_⟩
    rw [he]
    exact Exec.loop_false (by simpa only [List.nil_append, hrest, mk_var] using hflag)
  | cons x word ih =>
    intro v S hword hsrc hflag
    have hx := hword x (by simp)
    let v₁ := { v with flag := ((word ++ rest).head?.map p).getD false }
    let S₁ : Stacks T A := { S with R := Function.update S.R src (word ++ rest) }
    obtain ⟨v₂, hu, he⟩ := ih v₁ S₁ (fun y hy => hword y (by simp [hy])) (by simp [S₁]) rfl
    have hrun : (configurationDropStep src p : Act T Q A U).run (mk v S) = mk v₁ S₁ := by
      simp [configurationDropStep, WordCmd.peekRp, Action.run, hsrc, update_rt, v₁, S₁]
    refine ⟨v₂, hu, ?_⟩
    refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag))
      (by simpa [hx] using hflag)
      (hrun ▸ Exec.act (body := body) (configurationDropStep src p) (mk v S)) he) (by simp; ring) ?_
    congr 2
    simp [S₁]

theorem configurationDrop_exec (body : P → Pr P T Q A U) (src : Fin T)
    (p : Fin (A + 4) → Bool) (word rest : List (Fin (A + 4)))
    (hword : ∀ x ∈ word, p x = true) (hrest : (rest.head?.map p).getD false = false)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = word ++ rest) :
    ∃ v', v'.user = v.user ∧
      Exec body (configurationDrop src p) (mk v S) (2 * word.length + 2)
        (mk v' { S with R := Function.update S.R src rest }) := by
  let v₀ := { v with flag := ((word ++ rest).head?.map p).getD false }
  obtain ⟨v', hu, he⟩ := configurationDrop_loop body src p rest hrest word v₀ S hword hsrc rfl
  have hp : (WordCmd.peekRp src p : Act T Q A U).run (mk v S) = mk v₀ S := by
    simp [WordCmd.peekRp, Action.run, hsrc, v₀]
  exact ⟨v', hu, Exec.cast (Exec.seq
    (hp ▸ Exec.act (body := body) (WordCmd.peekRp src p) (mk v S)) he) (by omega) rfl⟩

/-- Reverse, discard the matching high suffix, then restore low-bit-first order. -/
def configurationTrim (src tmp : Fin T) (p : Fin (A + 4) → Bool) : Pr P T Q A U :=
  .seq (moveR src tmp id) (.seq (configurationDrop tmp p) (moveR tmp src id))

/-- The suffix length is proof data only. All unrelated stacks and scratch are
restored, and the exact cost is linear in the original word length. -/
theorem configurationTrim_exec (body : P → Pr P T Q A U) (src tmp : Fin T) (hst : src ≠ tmp)
    (p : Fin (A + 4) → Bool) (word padding : List (Fin (A + 4)))
    (hpadding : ∀ x ∈ padding, p x = true)
    (hword : (word.reverse.head?.map p).getD false = false)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = word ++ padding) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (configurationTrim src tmp p) (mk v S) (4 * (word ++ padding).length + 6)
        (mk v' { S with R := Function.update S.R src word }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body src tmp hst id v S
  let S₁ : Stacks T A := { S with R := movedR S.R src tmp id (S.R src) }
  have hs₁ : S₁.R src = [] := by simp [S₁, movedR, hst]
  have ht₁ : S₁.R tmp = padding.reverse ++ word.reverse := by
    simp [S₁, movedR, hsrc, htmp]
  obtain ⟨v₂, hu₂, he₂⟩ := configurationDrop_exec body tmp p padding.reverse word.reverse
    (by simpa only [List.mem_reverse] using hpadding) hword v₁ S₁ ht₁
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R tmp word.reverse }
  have hs₂ : S₂.R src = [] := by simp [S₂, hst, hs₁]
  have ht₂ : S₂.R tmp = word.reverse := by simp [S₂]
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body tmp src hst.symm id v₂ S₂
  have hfinal : movedR S₂.R tmp src id (S₂.R tmp) = Function.update S.R src word := by
    funext j
    by_cases hj : j = src
    · subst j
      simp [movedR, ht₂, hs₂]
    · by_cases hk : j = tmp
      · subst j
        simp [movedR, hst.symm, htmp]
      · simp [movedR, S₂, S₁, hj, hk]
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), ?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  refine Exec.cast he ?_ ?_
  · rw [hsrc, ht₂]
    simp only [List.length_reverse, List.length_append]
    omega
  · simp only [hfinal]
    rfl

end IntegerMultBounds.MathlibTM2.Routing
