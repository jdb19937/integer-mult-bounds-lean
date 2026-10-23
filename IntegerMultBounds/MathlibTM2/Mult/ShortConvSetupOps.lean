module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPadding
public import IntegerMultBounds.MathlibTM2.Fast.LoadRing

/-! # Unary products and cleanup for shared convolution setup

The product loop is structural in the unary input. Cleanup is structural in the register
list and charges the actual total word length, restoring all left stacks and user state.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Multiply two unary dimensions, preserving their actual symbols. -/
def unaryProduct (a b dst t₁ t₂ : Fin T) : Pr P T Q A U := scanP a t₁ (ucopy b dst t₂)

theorem unaryProduct_exec {a b dst t₁ t₂ : Fin T} (hreg : [a, b, dst, t₁, t₂].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (S.R a).length * (4 * (S.R b).length + 9) + 4 ∧
      Exec body (unaryProduct a b dst t₁ t₂) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (List.replicate ((S.R a).length * (S.R b).length) tick ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  let Ψ : ℕ → Regs T A := fun j => Function.update S.R dst
    (List.replicate (j * (S.R b).length) tick ++ S.R dst)
  have hp : IterSpec body (ucopy b dst t₂) a t₁ Ψ
      (fun _ => 4 * (S.R b).length + 4) (S.R a).length := by
    intro j _ v₀ S₀ hS
    have hb : S₀.R b = S.R b := by
      rw [hS b ‹a ≠ b›.symm ‹b ≠ t₁›]
      simp [Ψ, ‹b ≠ dst›]
    have hd : S₀.R dst = Ψ j dst := hS dst ‹a ≠ dst›.symm ‹dst ≠ t₁›
    have ht : S₀.R t₂ = [] := by
      rw [hS t₂ ‹a ≠ t₂›.symm ‹t₁ ≠ t₂›.symm]
      simp [Ψ, ‹dst ≠ t₂›.symm, ht₂]
    obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body ‹b ≠ dst› ‹b ≠ t₂› ‹dst ≠ t₂› v₀ S₀ ht
    refine ⟨v₁, Function.update S₀.R dst (List.replicate (S₀.R b).length tick ++ S₀.R dst),
      _, hu₁, by simp [hb], he₁, by simp [‹a ≠ dst›], by simp [‹dst ≠ t₁›.symm], ?_⟩
    intro k hka hkt
    by_cases hk : k = dst
    · subst k
      simp only [Function.update_self, Ψ] at hd ⊢
      rw [hb, hd, ← List.append_assoc, List.replicate_append_replicate]
      congr 2
      ring
    · rw [Function.update_of_ne hk, hS k hka hkt]
      simp [Ψ, hk]
  obtain ⟨v', R', n, hu, hn, he, ha, ht, hrest⟩ := scanP_exec body ‹a ≠ t₁› hp 0 v S (by simp)
    (fun k _ _ => by simp [Ψ])
  refine ⟨v', n, hu, ?_, he.cast rfl ?_⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, ht₁,
      List.length_nil, Nat.mul_zero, Nat.add_zero] at hn
    nlinarith
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    change R' k = Function.update S.R dst
      (List.replicate ((S.R a).length * (S.R b).length) tick ++ S.R dst) k
    by_cases hka : k = a
    · subst k
      simp [ha, ht₁, ‹a ≠ dst›]
    by_cases hkt : k = t₁
    · subst k
      simp [ht, ht₁, ‹dst ≠ t₁›.symm]
    · rw [hrest k hka hkt]
      simp [Ψ]

/-- Clear a finite list of owned registers. -/
def clearWords : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | r :: rs => .seq (uclear r) (clearWords rs)

/-- Cleanup charges each actual word once. Only the listed right stacks change. -/
theorem clearWords_exec (rs : List (Fin T)) (hnd : rs.Nodup)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (clearWords rs) (mk v S)
        (2 * (rs.map fun r => (S.R r).length).sum + 2 * rs.length + 1)
        (mk v' { S with R := fun k => if k ∈ rs then [] else S.R k }) := by
  induction rs generalizing v S with
  | nil =>
      refine ⟨v, rfl, ?_⟩
      simpa [clearWords] using Exec.act (body := body) (.done : Act T Q A U) (mk v S)
  | cons r rs ih =>
      obtain ⟨hr, hrs⟩ := List.nodup_cons.mp hnd
      obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body r v S
      set S₁ : Stacks T A := { S with R := Function.update S.R r [] }
      obtain ⟨v₂, hu₂, he₂⟩ := ih hrs v₁ S₁
      have hsum : (rs.map fun k => (S₁.R k).length).sum = (rs.map fun k => (S.R k).length).sum := by
        congr 1
        apply List.map_congr_left
        intro k hk
        have hkr : k ≠ r := by intro e; subst k; exact hr hk
        simp [S₁, hkr]
      refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast ?_ ?_⟩
      · simp [hsum]
        ring
      · congr 1
        ext1
        · rfl
        · rfl
        · rfl
        funext k
        by_cases hk : k = r
        · subst k
          simp [S₁]
        · simp [S₁, hk]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
