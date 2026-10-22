module

public import IntegerMultBounds.MathlibTM2.Routing.SelectiveSetupData

/-!
# Executed setup of the complete selective host program

The input configuration remains on its tapes. All 27 destinations start empty;
all other host scratch stays empty. Actual copying, zero-counter construction,
binary-to-unary construction and header-prefix installation establish every
hypothesis of the complete prepared host execution, with an explicit total cost.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {T Q K : ℕ} {P U : Type}

/-- Scratch that must stay blank, rather than receive an installed word. -/
def SelectiveHost.Blank (H : SelectiveHost T) (k : Fin T) : Prop :=
  k ∈ [H.out, H.tmp, H.ctmp] ∨ (∃ d, H.dst d = k) ∨ (∃ d, H.aux d = k) ∨
  (∃ off r, r ≠ PatternReg.fld 1 ∧ (∀ j, r ≠ .desc j) ∧ H.cb off r = k) ∨
  (∃ c j, (j = reg selectiveSwapPay ∨ 6 ≤ j.val) ∧ H.swaps c j = k)

/-- Separation of configuration sources, installed words and other host scratch. -/
structure SetupLayout (H : SelectiveHost T) (cfg : SetupKey → Fin T) : Prop where
  targets : Function.Injective (SetupKey.target H)
  regs : ∀ key, [cfg key, key.target H, H.out, H.tmp, H.ctmp].Nodup
  sources : ∀ (key other : SetupKey), cfg key ≠ other.target H
  blanks : ∀ (key : SetupKey) (k : Fin T), H.Blank k → key.target H ≠ k
  stream : ∀ key, cfg key ≠ H.src

theorem setupJobs_nodup (H : SelectiveHost T) (cfg : SetupKey → Fin T) (layout : SetupLayout H cfg)
    (wb wm B M : ℕ) : ((setupJobs H cfg wb wm B M).map MetadataJob.dst).Nodup := by
  simpa only [setupJobs, List.map_map, Function.comp_def, setupJob_dst] using
    setupKeys_nodup.map layout.targets

variable (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

/-- Every installed word is established from its raw configuration input. -/
theorem selectiveSetup_at (H : SelectiveHost T) (cfg : SetupKey → Fin T) (layout : SetupLayout H cfg)
    {wb wm B M : ℕ} {hs : Fin 2 → Fin 5 → List Bool} {R : Fin T → List (Fin (prime + K + 4))}
    (data : SetupData p X hG hK active s cfg wb wm B M hs R) (key : SetupKey) :
    metadataInstalled R (setupJobs H cfg wb wm B M) (key.target H) =
      setupPayload p X hG hK active s B M hs key := by
  have he := metadataInstalled_at R (setupJobs H cfg wb wm B M)
    (setupJobs_nodup H cfg layout wb wm B M) (setupJob H cfg wb wm B M key)
    (List.mem_map.mpr ⟨key, setupKeys_mem key, rfl⟩)
  rw [setupJob_dst, SetupData.contents p X hG hK active s H data key] at he
  exact he

theorem selectiveSetup_blank (H : SelectiveHost T) (cfg : SetupKey → Fin T) (layout : SetupLayout H cfg)
    (wb wm B M : ℕ) (R : Fin T → List (Fin (prime + K + 4))) (k : Fin T) (hk : H.Blank k) :
    metadataInstalled R (setupJobs H cfg wb wm B M) k = R k := by
  apply metadataInstalled_keep
  intro hm
  obtain ⟨job, hj, he⟩ := List.mem_map.mp hm
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
  rw [setupJob_dst] at he
  exact layout.blanks key k hk he

/-- The host invariant depends only on its installed words and blank scratch. -/
theorem selectivePrepared_of_words (H : SelectiveHost T) {B M : ℕ}
    {hs : Fin 2 → Fin 5 → List Bool} (S : Stacks T (prime + K))
    (hat : ∀ key : SetupKey, S.R (key.target H) = setupPayload p X hG hK active s B M hs key)
    (hL : ∀ j, S.L j = []) (hb : ∀ k, H.Blank k → S.R k = []) :
    SelectivePrepared p X H hG hK active s B M hs S := by
  refine ⟨hL, ?_, ?_, ?_, ?_, ?_, fun d => ?_, fun d => ?_, fun off => ?_,
    fun c => ?_, fun c j hj => ?_, fun c k => ?_⟩
  · simpa [SetupKey.target, setupPayload] using congrArg List.length (hat .block)
  · simpa [SetupKey.target, setupPayload] using congrArg List.length (hat .records)
  · exact hb H.tmp (Or.inl (by simp))
  · exact hb H.ctmp (Or.inl (by simp))
  · exact hb H.out (Or.inl (by simp))
  · exact hb (H.dst d) (Or.inr (Or.inl ⟨d, rfl⟩))
  · exact hb (H.aux d) (Or.inr (Or.inr (Or.inl ⟨d, rfl⟩)))
  · refine ⟨fun f => ?_, ?_, fun r hr hst => ?_⟩
    · simpa [SetupKey.target, setupPayload, digit] using hat (.field f)
    · exact hb (H.cb off (.fld 0)) (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨off, .fld 0, by simp, by simp, rfl⟩))))
    · by_cases hd : ∃ j, r = PatternReg.desc j
      · obtain ⟨j, rfl⟩ := hd
        exact hat (.desc off j)
      · have hempty := hb (H.cb off r) (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨off, r, hr 1, fun j he => hd ⟨j, he⟩, rfl⟩))))
        have hz : patternStatic (prime + K) (selectivePatterns p X hG hK active s off) r = [] := by
          cases r <;> first | rfl | exact (hd ⟨_, rfl⟩).elim
        exact hempty.trans hz.symm
  · exact hb _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, reg selectiveSwapPay, Or.inl rfl, rfl⟩))))
  · exact hb _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, j, Or.inr hj, rfl⟩))))
  · exact hat (.header c k)

/-- Installed metadata satisfies the full prepared host invariant. -/
theorem selectiveSetup_prepared (H : SelectiveHost T) (cfg : SetupKey → Fin T)
    (layout : SetupLayout H cfg) {wb wm B M : ℕ} {hs : Fin 2 → Fin 5 → List Bool}
    (S : Stacks T (prime + K)) (data : SetupData p X hG hK active s cfg wb wm B M hs S.R)
    (hL : ∀ j, S.L j = []) (hblank : ∀ k, H.Blank k → S.R k = []) :
    SelectivePrepared p X H hG hK active s B M hs
      { S with R := metadataInstalled S.R (setupJobs H cfg wb wm B M) } := by
  have hat := selectiveSetup_at p X hG hK active s H cfg layout data
  have hb (k : Fin T) (hk : H.Blank k) :
      metadataInstalled S.R (setupJobs H cfg wb wm B M) k = [] := by
    rw [selectiveSetup_blank H cfg layout wb wm B M S.R k hk, hblank k hk]
  exact selectivePrepared_of_words p X hG hK active s H _ hat hL hb

/-- Fixed-program setup executes all copies and counter constructions, with all
configuration inputs restored and the exact prepared invariant established. -/
theorem selectiveSetup_exec (body : P → Pr P T Q (prime + K) U)
    (H : SelectiveHost T) (cfg : SetupKey → Fin T) (layout : SetupLayout H cfg)
    {wb wm B M : ℕ} {hs : Fin 2 → Fin 5 → List Bool}
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (data : SetupData p X hG hK active s cfg wb wm B M hs S.R)
    (hempty : ∀ key : SetupKey, S.R (key.target H) = [])
    (hL : ∀ j, S.L j = []) (hblank : ∀ k, H.Blank k → S.R k = []) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      m ≤ metadataInstallCost S.R (setupJobs H cfg wb wm B M) ∧
      Exec body (selectiveSetup H cfg) (mk v S) m
        (mk v' { S with R := metadataInstalled S.R (setupJobs H cfg wb wm B M) }) ∧
      SelectivePrepared p X H hG hK active s B M hs
        { S with R := metadataInstalled S.R (setupJobs H cfg wb wm B M) } := by
  have hregs : ∀ job ∈ setupJobs H cfg wb wm B M,
      [job.src, job.dst, H.out, H.tmp, H.ctmp].Nodup := by
    intro job hj
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    simpa only [setupJob_src, setupJob_dst] using layout.regs key
  have hsource : ∀ job ∈ setupJobs H cfg wb wm B M,
      ∀ other ∈ setupJobs H cfg wb wm B M, job.src ≠ other.dst := by
    intro job hj other ho
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    obtain ⟨key', _, rfl⟩ := List.mem_map.mp ho
    simpa only [setupJob_src, setupJob_dst] using layout.sources key key'
  obtain ⟨v', m, hu, hm, he⟩ := metadataInstall_exec body (setupJobs H cfg wb wm B M)
    H.out H.tmp H.ctmp (setupJobs_nodup H cfg layout wb wm B M) hregs hsource v S
    (fun job hj => by
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
      exact SetupData.jobData p X hG hK active s H data key)
    (fun job hj => by
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
      simpa only [setupJob_dst] using hempty key)
    (hblank H.out (Or.inl (by simp))) (hblank H.tmp (Or.inl (by simp)))
    (hblank H.ctmp (Or.inl (by simp)))
  rw [← selectiveSetup_eq H cfg wb wm B M] at he
  exact ⟨v', m, hu, hm, he, selectiveSetup_prepared p X hG hK active s H cfg layout S data hL hblank⟩

end IntegerMultBounds.MathlibTM2.Routing
