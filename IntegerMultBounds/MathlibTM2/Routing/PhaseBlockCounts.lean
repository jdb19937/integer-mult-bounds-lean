module

public import IntegerMultBounds.MathlibTM2.Routing.PhaseBlock

/-! Construct a phase block directly from unary run and complementary widths.
Three fixed pops expose the source-mask counts; three pushes restore them. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

def phaseBlockTrim {T Q A : ℕ} {U : Type} (low high : Fin T) : Act T Q A U :=
  .pop (.rt low) (fun v _ => v)
    (.pop (.rt high) (fun v _ => v) (.pop (.rt high) (fun v _ => v) .done))

def phaseBlockRestore {T Q A : ℕ} {U : Type} (low high : Fin T) : Act T Q A U :=
  .push (.rt low) (fun _ => tick)
    (.push (.rt high) (fun _ => tick) (.push (.rt high) (fun _ => tick) .done))

def phaseBlockCountsProgram {T Q A : ℕ} {P U : Type} (low high dst tmp work : Fin T) : Pr P T Q A U :=
  .seq (.act (phaseBlockTrim low high))
    (.seq (phaseBlockProgram low high dst tmp work) (.act (phaseBlockRestore low high)))

theorem phaseBlockCounts_exec {T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (low high dst tmp work : Fin T)
    (hreg : [low, high, dst, tmp, work].Nodup) (G H : ℕ) (hG : 0 < G) (hH : 2 ≤ H)
    (v : HS T Q A U) (S : Stacks T A)
    (hlow : S.R low = List.replicate G tick) (hhigh : S.R high = List.replicate H tick)
    (hdst : S.R dst = []) (htmp : S.R tmp = []) (hwork : S.R work = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (phaseBlockCountsProgram low high dst tmp work) (mk v S)
        (10 * (G - 1) + 6 * (H - 2) + 22)
        (mk v' { S with R := Function.update S.R dst (binSyms (G + H) (phaseBlockValue G)) }) := by
  have hn := hreg
  regs_ne hn
  let S₁ : Stacks T A := { S with R := Function.update (Function.update S.R low (List.replicate (G - 1) tick)) high (List.replicate (H - 2) tick) }
  have htrim : (phaseBlockTrim low high : Act T Q A U).run (mk v S) = mk v S₁ := by
    simp [phaseBlockTrim, Action.run, update_rt, S₁, hlow, hhigh,
      Ne.symm ‹low ≠ high›, List.tail_replicate, Nat.sub_sub, Function.update_comm ‹low ≠ high›]
  obtain ⟨v₁, hu₁, he₁⟩ := phaseBlock_exec body low high dst tmp work hreg v S₁
    (by simp [S₁, Ne.symm ‹high ≠ dst›, Ne.symm ‹low ≠ dst›, hdst])
    (by simp [S₁, Ne.symm ‹high ≠ tmp›, Ne.symm ‹low ≠ tmp›, htmp])
    (by simp [S₁, Ne.symm ‹high ≠ work›, Ne.symm ‹low ≠ work›, hwork])
  have hl₁ : S₁.R low = List.replicate (G - 1) tick := by simp [S₁, ‹low ≠ high›]
  have hh₁ : S₁.R high = List.replicate (H - 2) tick := by simp [S₁]
  rw [hl₁, hh₁, List.length_replicate, List.length_replicate,
    show G - 1 + 1 = G by omega, show G - 1 + (H - 2) + 3 = G + H by omega] at he₁
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (binSyms (G + H) (phaseBlockValue G)) }
  have hrestore : (phaseBlockRestore low high : Act T Q A U).run (mk v₁ S₂) =
      mk v₁ { S with R := Function.update S.R dst (binSyms (G + H) (phaseBlockValue G)) } := by
    have hgl : tick :: List.replicate (G - 1) (tick (A := A)) = List.replicate G tick := by
      rw [← List.replicate_succ]; congr 1; omega
    have hhl : tick :: tick :: List.replicate (H - 2) (tick (A := A)) = List.replicate H tick := by
      rw [← List.replicate_succ, ← List.replicate_succ]; congr 1; omega
    simp [phaseBlockRestore, Action.run, update_rt, S₂, S₁,
      ‹low ≠ high›, Ne.symm ‹low ≠ high›, ‹low ≠ dst›, ‹high ≠ dst›, hgl, hhl]
    congr 1
    congr 1
    funext j
    by_cases hj : j = low
    · subst j; simp [hlow, ‹low ≠ high›, ‹low ≠ dst›]
    · by_cases hk : j = high
      · subst j; simp [hhigh, ‹high ≠ dst›]
      · by_cases hd : j = dst
        · subst j; simp [Ne.symm ‹low ≠ dst›, Ne.symm ‹high ≠ dst›]
        · simp [hj, hk, hd]
  exact ⟨v₁, hu₁, Exec.cast (Exec.seq (htrim ▸ Exec.act (body := body) _ (mk v S))
    (Exec.seq he₁ (hrestore ▸ Exec.act (body := body) _ (mk v₁ S₂)))) (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
