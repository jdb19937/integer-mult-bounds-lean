module

public import IntegerMultBounds.MathlibTM2.Routing.ElementarySharedFrame

/-!
# Executed shared setup and cleanup around a routing program

This structural composition charges actual counter construction and clearing.
A routing body must restore its entire installed bank except for the stream.
The resulting program restores the original bank except for that same stream.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast

/-- A fixed setup/body/cleanup composition. -/
def elementarySharedProgram {t₀ T Q A : ℕ} {P U : Type}
    (rg : LayReg t₀ → Fin T) (cfg : Fin 4 → Fin T) (work tmp ctmp : Fin T)
    (wb wm B M : ℕ) (core : Pr P T Q A U) : Pr P T Q A U :=
  .seq (metadataInstall work tmp ctmp (elementarySharedJobs rg cfg wb wm B M))
    (.seq core (metadataClean ((elementarySharedJobs rg cfg wb wm B M).map MetadataJob.dst)))

/-- Compose any restored routing body with executed shared-counter setup and
cleanup. The continuation premise is discharged by the elementary router. -/
theorem elementarySharedProgram_exec {t₀ T Q A : ℕ} {P U : Type}
    (body : P → Pr P T Q A U) (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (cfg : Fin 4 → Fin T) (work tmp ctmp : Fin T) (wb wm n B M : ℕ)
    (hregs : ∀ key, [(elementarySharedJob rg cfg wb wm B M key).src,
      elementarySharedTarget rg key, work, tmp, ctmp].Nodup)
    (hsources : ∀ key other, (elementarySharedJob rg cfg wb wm B M key).src ≠
      elementarySharedTarget rg other)
    (v : HS T Q A U) (S : Stacks T A) (data : ElementarySharedData cfg wb wm n B M S.R)
    (hempty : ∀ key, S.R (elementarySharedTarget rg key) = [])
    (hw : S.R work = []) (ht : S.R tmp = []) (hc : S.R ctmp = [])
    (core : Pr P T Q A U) (out : List (Fin (A + 4))) (C : ℝ)
    (hcore : ∀ v₁ : HS T Q A U, ∃ (v₂ : HS T Q A U) (m : ℕ),
      v₂.user = v₁.user ∧ (m : ℝ) ≤ C ∧
      Exec body core (mk v₁ { S with R := metadataInstalled S.R (elementarySharedJobs rg cfg wb wm B M) }) m
        (mk v₂ { S with R := Function.update (metadataInstalled S.R (elementarySharedJobs rg cfg wb wm B M)) (rg .str) out })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ (metadataInstallCost S.R (elementarySharedJobs rg cfg wb wm B M) : ℕ) + C +
        (metadataCleanCost (metadataInstalled S.R (elementarySharedJobs rg cfg wb wm B M))
          ((elementarySharedJobs rg cfg wb wm B M).map MetadataJob.dst) : ℕ) ∧
      Exec body (elementarySharedProgram rg cfg work tmp ctmp wb wm B M core) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .str) out }) := by
  let jobs := elementarySharedJobs rg cfg wb wm B M
  let bank := metadataInstalled S.R jobs
  let keys := jobs.map MetadataJob.dst
  have hkeys : keys.Nodup := by
    simpa only [keys, jobs, elementarySharedJobs, List.map_map, Function.comp_def,
      elementarySharedJob_dst] using
      (List.nodup_finRange 4).map (elementarySharedTarget_injective rg hrg)
  have hstr : rg .str ∉ keys := by
    intro hx
    obtain ⟨job, hj, he⟩ := List.mem_map.mp hx
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    rw [elementarySharedJob_dst] at he
    fin_cases key <;> simp_all [elementarySharedTarget, hrg.eq_iff]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := elementarySharedSetup_exec body rg hrg cfg work tmp ctmp
    wb wm n B M hregs hsources v S data hempty hw ht hc
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hcore v₁
  let S₂ : Stacks T A := { S with R := Function.update bank (rg .str) out }
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body keys hkeys v₂ S₂
  have hcost : metadataCleanCost S₂.R keys = metadataCleanCost bank keys := by
    apply metadataCleanCost_congr
    intro k hk
    have hne : k ≠ rg .str := by
      intro he
      subst k
      exact hstr hk
    exact Function.update_of_ne hne _ _
  have hfinal : metadataCleared S₂.R keys = Function.update S.R (rg .str) out :=
    elementarySharedSetup_restore rg hrg cfg wb wm B M S.R out hempty
  have he₃' : Exec body (metadataClean keys) (mk v₂ S₂) (metadataCleanCost bank keys)
      (mk v₃ { S with R := Function.update S.R (rg .str) out }) := by
    simpa only [hcost, hfinal] using he₃
  refine ⟨v₃, m₁ + (m₂ + metadataCleanCost bank keys), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃')⟩
  have hm₁' : (m₁ : ℝ) ≤ (metadataInstallCost S.R jobs : ℕ) := by exact_mod_cast hm₁
  simp only [Nat.cast_add]
  dsimp only [bank, keys, jobs] at hm₁' ⊢
  linarith only [hm₁', hm₂]

end IntegerMultBounds.MathlibTM2.Routing
