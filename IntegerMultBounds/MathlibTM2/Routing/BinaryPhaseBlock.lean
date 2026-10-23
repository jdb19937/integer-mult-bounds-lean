module

public import IntegerMultBounds.MathlibTM2.Routing.PhaseBlockCounts
public import IntegerMultBounds.MathlibTM2.Routing.UnaryDifference

/-! Generate a three-mark phase block from binary segment/run widths.
Both unary dimensions are generated and erased; only the block output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

inductive PhaseBlockReg where
  | width | run | bin | low | high | dst | work | scratch (i : Fin 3)
  deriving DecidableEq

def binaryPhaseBlockProgram {T Q A : ℕ} {P U : Type} (rg : PhaseBlockReg → Fin T) : Pr P T Q A U :=
  .seq (unaryDifferenceProgram (rg .width) (rg .run) (rg .bin) (rg .high) (rg .work)
    (rg (.scratch 0)) (rg (.scratch 1)) (rg (.scratch 2)) (rg (.scratch 2)))
    (.seq (toUnary (rg .run) (rg .low) (rg .work) (rg (.scratch 0)) (rg (.scratch 1)))
      (.seq (phaseBlockCountsProgram (rg .low) (rg .high) (rg .dst) (rg (.scratch 0)) (rg .work))
        (.seq (bclear (rg .low)) (bclear (rg .high)))))

def binaryPhaseBlockCost (L K G : ℕ) :=
  (L * (4 * (K - G) + 21) + 2 * (K - G) + 16) +
    (L * (4 * G + 11) + 2 * G + 6) +
    (10 * (G - 1) + 6 * (K - G - 2) + 22) + (2 * G + 2) + (2 * (K - G) + 2)

theorem binaryPhaseBlock_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : PhaseBlockReg → Fin T) (hrg : Function.Injective rg)
    (L K G : ℕ) (hK : K < 2 ^ L) (hG : 0 < G) (hGK : G + 1 < K)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .width) = binSyms L K) (hrun : S.R (rg .run) = binSyms L G)
    (hblank : ∀ r, r ≠ .width → r ≠ .run → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ binaryPhaseBlockCost L K G ∧
      Exec body (binaryPhaseBlockProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .dst) (binSyms K (phaseBlockValue G)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryDifference_exec body (rg .width) (rg .run) (rg .bin)
    (rg .high) (rg .work) (rg (.scratch 0)) (rg (.scratch 1)) (rg (.scratch 2)) (rg (.scratch 2))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    L K G hK (by omega) v S hwidth hrun
    (hblank .bin (by simp) (by simp)) (hblank .high (by simp) (by simp))
    (hblank .work (by simp) (by simp)) (hblank (.scratch 0) (by simp) (by simp))
    (hblank (.scratch 1) (by simp) (by simp)) (hblank (.scratch 2) (by simp) (by simp))
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .high) (List.replicate (K - G) tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := toUnary_exec body
    (show [rg .run, rg .low, rg .work, rg (.scratch 0), rg (.scratch 1)].Nodup by
      simp [List.nodup_cons, hrg.eq_iff]) (show G < 2 ^ L by omega) v₁ S₁
    (by simp [S₁, hrg.eq_iff, hrun])
    (by simp [S₁, hrg.eq_iff, hblank .work (by simp) (by simp)])
    (by simp [S₁, hrg.eq_iff, hblank (.scratch 0) (by simp) (by simp)])
    (by simp [S₁, hrg.eq_iff, hblank (.scratch 1) (by simp) (by simp)])
  have hl₁ : S₁.R (rg .low) = [] := by simp [S₁, hrg.eq_iff, hblank .low (by simp) (by simp)]
  rw [hl₁, List.append_nil] at he₂
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg .low) (List.replicate G tick) }
  obtain ⟨v₃, hu₃, he₃⟩ := phaseBlockCounts_exec body (rg .low) (rg .high) (rg .dst)
    (rg (.scratch 0)) (rg .work) (by simp [List.nodup_cons, hrg.eq_iff]) G (K - G) hG (by omega) v₂ S₂
    (by simp [S₂]) (by simp [S₂, S₁, hrg.eq_iff])
    (by simp [S₂, S₁, hrg.eq_iff, hblank .dst (by simp) (by simp)])
    (by simp [S₂, S₁, hrg.eq_iff, hblank (.scratch 0) (by simp) (by simp)])
    (by simp [S₂, S₁, hrg.eq_iff, hblank .work (by simp) (by simp)])
  rw [show G + (K - G) = K by omega] at he₃
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R (rg .dst) (binSyms K (phaseBlockValue G)) }
  obtain ⟨v₄, hu₄, _, he₄⟩ := bclear_exec body (rg .low) v₃ S₃
  have hl₃ : S₃.R (rg .low) = List.replicate G tick := by simp [S₃, S₂, hrg.eq_iff]
  rw [hl₃, List.length_replicate] at he₄
  let S₄ : Stacks T A := { S₃ with R := Function.update S₃.R (rg .low) [] }
  obtain ⟨v₅, hu₅, _, he₅⟩ := bclear_exec body (rg .high) v₄ S₄
  have hh₄ : S₄.R (rg .high) = List.replicate (K - G) tick := by simp [S₄, S₃, S₂, S₁, hrg.eq_iff]
  have hf : Function.update S₄.R (rg .high) [] = Function.update S.R (rg .dst) (binSyms K (phaseBlockValue G)) := by
    funext j
    by_cases hh : j = rg .high
    · subst j; simp [hrg.eq_iff, hblank .high (by simp) (by simp)]
    · by_cases hl : j = rg .low
      · subst j; simp [S₄, hrg.eq_iff, hblank .low (by simp) (by simp)]
      · by_cases hd : j = rg .dst
        · subst j; simp [S₄, S₃, hrg.eq_iff]
        · simp [S₄, S₃, S₂, S₁, hh, hl, hd]
  rw [hf, hh₄, List.length_replicate] at he₅
  exact ⟨v₅, m₁ + (m₂ + ((10 * (G - 1) + 6 * (K - G - 2) + 22) +
    ((2 * G + 2) + (2 * (K - G) + 2)))), hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    by unfold binaryPhaseBlockCost; omega,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))⟩

end IntegerMultBounds.MathlibTM2.Routing
