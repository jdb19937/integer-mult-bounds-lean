module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryMaskEmit
public import IntegerMultBounds.MathlibTM2.Routing.ElementarySetupBank

/-! One actual descriptor-compiler iteration: load a binary selector, generate
and emit its row, clear the operand, and archive its input frame for rewind. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

structure DescriptorCompileReady {T A : ℕ} (rg : BinaryMaskReg → Fin T)
    (R : Fin T → List (Fin (A + 4))) (L M : ℕ) : Prop where
  width : R (rg .width) = binSyms L M
  blank : ∀ r, r ≠ .width → R (rg r) = []

def descriptorCompileCallCost (L M : ℕ) :=
  6 * L + 8 + (2 * (L * (4 * M + 33) + 2 * M + 31) + 16 * M + 28)

def descriptorCompileCallProgram {T Q A : ℕ} {P U : Type}
    (rg : BinaryMaskReg → Fin T) (src saved out : Fin T) : Pr P T Q A U :=
  .seq (configurationLoad src (rg .source) (rg (.scratch 3)) saved configurationIsBit false)
    (.seq (binaryMaskEmitProgram rg out) (bclear (rg .source)))

def descriptorCompileStepBank {T A : ℕ} (R : Fin T → List (Fin (A + 4)))
    (src saved out : Fin T) (frame row rest : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update R src rest) saved (frame.reverse ++ R saved))
    out (row ++ R out)

theorem descriptorCompileCall_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : BinaryMaskReg → Fin T) (hrg : Function.Injective rg)
    (src saved out : Fin T) (hss : src ≠ saved) (hso : src ≠ out) (hao : saved ≠ out)
    (hsrc : ∀ r, src ≠ rg r) (hsaved : ∀ r, saved ≠ rg r) (hout : ∀ r, out ≠ rg r)
    (L M : ℕ) (hM : M < 2 ^ L) (q : Fin M) (rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A) (hready : DescriptorCompileReady rg S.R L M)
    (hinput : S.R src = binSyms L q.val ++ separator :: rest) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ descriptorCompileCallCost L M ∧
      Exec body (descriptorCompileCallProgram rg src saved out) (mk v S) m
        (mk v' { S with R := descriptorCompileStepBank S.R src saved out (binSyms L q.val ++ [separator]) (binSyms M (2 ^ q.val)) rest }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := configurationLoad_exec body src (rg .source) (rg (.scratch 3)) saved
    (hsrc _) hss (hsaved _).symm (hsrc _) (by simp [hrg.eq_iff]) (hsaved _)
    configurationIsBit configurationIsBit_separator false (binSyms L q.val) rest
    (by
      intro x hx
      rw [binSyms_eq] at hx
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
      exact configurationIsBit_bit b)
    v S hinput (hready.blank _ (by simp)) (hready.blank _ (by simp))
  let S₁ : Stacks T A := { S with R := configurationLoaded S.R src (rg .source) (rg (.scratch 3)) saved (binSyms L q.val) rest false }
  have hkeep (r : BinaryMaskReg) (hr : r ≠ .source) : S₁.R (rg r) = S.R (rg r) := by
    by_cases ht : r = .scratch 3
    · subst r
      simp [S₁, configurationLoaded, hrg.eq_iff, (hsaved _).symm, hready.blank (.scratch 3) (by simp)]
    · simp [S₁, configurationLoaded, hrg.eq_iff, hr, ht, (hsrc _).symm, (hsaved _).symm]
  have hsource₁ : S₁.R (rg .source) = binSyms L q.val := by simp [S₁, configurationLoaded]
  have hout₁ : S₁.R out = S.R out := by simp [S₁, configurationLoaded, hout, hso.symm, hao.symm]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := binaryMaskEmit_exec body rg hrg out hout L M hM q v₁ S₁
    ((hkeep .width (by simp)).trans hready.width) hsource₁
    ((hkeep .low (by simp)).trans (hready.blank _ (by simp)))
    ((hkeep .high (by simp)).trans (hready.blank _ (by simp)))
    ((hkeep .dst (by simp)).trans (hready.blank _ (by simp)))
    (fun i => (hkeep (.scratch i) (by simp)).trans (hready.blank _ (by simp)))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R out (binSyms M (2 ^ q.val) ++ S₁.R out) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg .source) v₂ S₂
  have hsource₂ : S₂.R (rg .source) = binSyms L q.val := by simp [S₂, (hout _).symm, hsource₁]
  have hfinal : Function.update S₂.R (rg .source) [] = descriptorCompileStepBank S.R src saved out
      (binSyms L q.val ++ [separator]) (binSyms M (2 ^ q.val)) rest := by
    funext j
    by_cases hj : j = out
    · subst j; simp [S₂, descriptorCompileStepBank, hout, hout₁]
    · by_cases hs : j = src
      · subst j; simp [S₂, S₁, configurationLoaded, descriptorCompileStepBank, hsrc, hso, hss]
      · by_cases ha : j = saved
        · subst j; simp [S₂, S₁, configurationLoaded, descriptorCompileStepBank, hsaved, hao]
        · by_cases hd : j = rg .source
          · subst j; simp [descriptorCompileStepBank, (hsrc _).symm, (hsaved _).symm, (hout _).symm, hready.blank .source (by simp)]
          · by_cases ht : j = rg (.scratch 3)
            · subst j; simp [S₂, S₁, configurationLoaded, descriptorCompileStepBank, (hsrc _).symm,
                (hsaved _).symm, (hout _).symm, hrg.eq_iff, hready.blank (.scratch 3) (by simp)]
            · simp [S₂, S₁, configurationLoaded, descriptorCompileStepBank, hj, hs, ha, hd, ht]
  rw [hfinal, hsource₂, length_binSyms] at he₃
  have he₁' : Exec body (configurationLoad src (rg .source) (rg (.scratch 3)) saved configurationIsBit false)
      (mk v S) (4 * L + 6) (mk v₁ S₁) := by simpa only [length_binSyms] using he₁
  refine ⟨v₃, (4 * L + 6) + (m₂ + (2 * L + 2)), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁' (Exec.seq he₂ he₃)⟩
  unfold descriptorCompileCallCost
  omega

end IntegerMultBounds.MathlibTM2.Routing
