module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveSetup

/-!
# Selective routing with executed setup and cleanup

The fixed configuration installer surrounds the complete routing schedule. Its
metadata destinations are cleared afterward, restoring the original register
file except for the routed stream. All three phases contribute to the bound.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {T Q K : ℕ} {P U : Type}

noncomputable def setupTargets (H : SelectiveHost T) : List (Fin T) :=
  setupKeys.map (SetupKey.target H)

theorem setupJobs_targets (H : SelectiveHost T) (cfg : SetupKey → Fin T) (wb wm B M : ℕ) :
    (setupJobs H cfg wb wm B M).map MetadataJob.dst = setupTargets H := by
  simp only [setupJobs, List.map_map, Function.comp_def, setupJob_dst, setupTargets]

theorem setupTargets_src (H : SelectiveHost T) (hH : H.Valid) : H.src ∉ setupTargets H := by
  intro hm
  obtain ⟨key, _, he⟩ := List.mem_map.mp hm
  cases key with
  | field f => exact SelectiveHost.Valid.cf_src H hH f he
  | desc off k => exact SelectiveHost.Valid.cb_src H hH off (.desc k) he
  | block =>
    have hn := (List.nodup_cons.mp (hH.move .A).regs).1
    exact hn (by simp [SetupKey.target] at he; simp [he])
  | records =>
    have hn := (List.nodup_cons.mp (hH.move .A).regs).1
    exact hn (by simp [SetupKey.target] at he; simp [he])
  | header c k => exact hH.swap_src c _ he

noncomputable def selectiveProgram (H : SelectiveHost T) (hH : H.Valid)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hT : swapT 6 ≤ T) (cfg : SetupKey → Fin T) : Pr P T Q (prime + K) U :=
  .seq (selectiveSetup H cfg)
    (.seq (Prog.seqList (progW.map (fun o => selectivePass H hH hQ hT o.1)))
      (metadataClean (setupTargets H)))

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

/-- Full execution restores every installed metadata tape and every configuration
input. The bound includes installation, all rotations and swaps, and cleanup. -/
theorem selectiveProgram_exec (body : P → Pr P T Q (prime + K) U)
    (H : SelectiveHost T) (hH : H.Valid)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hT : swapT 6 ≤ T) (cfg : SetupKey → Fin T) (layout : SetupLayout H cfg)
    (hallowed : ∀ c, (s c).Allowed active)
    {wb wm R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B)
    (hs : Fin 2 → Fin 5 → List Bool)
    (hv : ∀ c k, Counter.value (hs c k) = selectiveSwapValues p X R B c k)
    (hc : ∀ c k, GrowingCounterData.Canonical (hs c k))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (data : SetupData p X hG hK active s cfg wb wm B
      (R * 2 ^ fieldsLen (selectiveLen p X)) hs S.R)
    (hempty : ∀ key : SetupKey, S.R (key.target H) = [])
    (hL : ∀ j, S.L j = []) (hblank : ∀ k, H.Blank k → S.R k = [])
    (l : List (List (Fin (prime + K + 4))))
    (hstream : S.R H.src = l.flatten)
    (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlB : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) :
    let jobs := setupJobs H cfg wb wm B (R * 2 ^ fieldsLen (selectiveLen p X))
    let installed := metadataInstalled S.R jobs
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ metadataInstallCost S.R jobs +
        ((progW.map (fun o => selectiveOpCost p X T R B
          (fun c => ∑ j, (installed (H.swaps c j)).length) o.1)).sum + 1) +
        metadataCleanCost installed (setupTargets H) ∧
      Exec body (selectiveProgram H hH hQ hT cfg) (mk v S) m
        (mk v' { S with R := Function.update S.R H.src (moveRecs (listPerm (selectivePerm p X hG hK hGK active s R) progW) l).flatten }) ∧
      ∀ i : Fin (R * 2 ^ fieldsLen (selectiveLen p X)),
        Good p (selectiveView p X i) →
        (listPerm (selectivePerm p X hG hK hGK active s R) progW i : ℕ) =
          setDigit (selectiveLen p X) 1
            ((selectiveView p X i).y ^^^ targetWord p active s
              (selectiveView p X i).y (selectiveView p X i).x) i := by
  dsimp only
  have hsrc := setupTargets_src H hH
  let jobs := setupJobs H cfg wb wm B (R * 2 ^ fieldsLen (selectiveLen p X))
  let installed := metadataInstalled S.R jobs
  have htargets : jobs.map MetadataJob.dst = setupTargets H := setupJobs_targets _ _ _ _ _ _
  have hn : (setupTargets H).Nodup := htargets ▸ setupJobs_nodup H cfg layout _ _ _ _
  have hkeep : installed H.src = l.flatten := by
    exact (metadataInstalled_keep S.R jobs H.src (by rwa [htargets])).trans hstream
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, hp⟩ :=
    selectiveSetup_exec p X hG hK active s body H cfg layout v S data hempty hL hblank
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ :=
    selectivePrepared_exec p X hG hK hGK active s body H hH hQ hT hR hB hs hv hc
      { S with R := installed } hp l hl hlB v₁
  have hi : Function.update installed H.src l.flatten = installed := by
    rw [← hkeep, Function.update_eq_self]
  simp only [hi] at he₂
  let routed := (moveRecs (listPerm (selectivePerm p X hG hK hGK active s R) progW) l).flatten
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body (setupTargets H) hn v₂
    { S with R := Function.update installed H.src routed }
  have hrestore : metadataCleared installed (setupTargets H) = S.R := by
    rw [← htargets]
    apply metadataClean_restore
    intro job hj
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    simpa only [setupJob_dst] using hempty key
  have hfinal : metadataCleared (Function.update installed H.src routed) (setupTargets H) =
      Function.update S.R H.src routed := by
    rw [metadataCleared_update _ _ _ _ hsrc, hrestore]
  have hcost : metadataCleanCost (Function.update installed H.src routed) (setupTargets H) =
      metadataCleanCost installed (setupTargets H) := by
    apply metadataCleanCost_congr
    intro k hk
    have hne : k ≠ H.src := by
      intro he
      exact hsrc (he ▸ hk)
    exact Function.update_of_ne hne _ _
  rw [hfinal] at he₃
  refine ⟨v₃, m₁ + (m₂ + metadataCleanCost installed (setupTargets H)),
    hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · have hm₁' : (m₁ : ℝ) ≤ metadataInstallCost S.R jobs := by exact_mod_cast hm₁
    push_cast
    dsimp only at hm₂
    linarith
  · have he₃' := he₃
    rw [hcost] at he₃'
    exact ⟨Exec.seq he₁ (Exec.seq he₂ he₃'),
      selectiveProgramPerm_good p X hG hK hGK active s R hallowed⟩

end IntegerMultBounds.MathlibTM2.Routing
