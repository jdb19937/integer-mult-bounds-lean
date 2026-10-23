module

public import IntegerMultBounds.MathlibTM2.Routing.RepairCompactData
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorInstall
public import IntegerMultBounds.MathlibTM2.Routing.RepairSetup
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Compile all eleven raw descriptors and execute the complete R2 installer.
Every intermediate input and scratch condition follows from the initial bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

private theorem repairCompactSource_work (key : RepairSetupKey) (j : Fin repairT)
    (hj : j ∈ [repairHost.out, repairHost.tmp, repairHost.ctmp]) : repairSetupSource key ≠ j := by
  have hn := (List.nodup_cons.mp (repairSetup_regs key)).1
  intro he
  apply hn
  rw [he]
  exact List.mem_cons_of_mem _ hj

variable {Q A : ℕ} {P U : Type}

variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

theorem repairCompactInstall_exec
    (body : P → Pr P repairT Q A U) (body' : P → Pr P repairCompactT Q A U)
    (hbody : ∀ f, body' f = embProg compactDescriptorCore id (body f))
    (Lw Lg L : Fin 11 → ℕ)
    {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    (v : HS repairCompactT Q A U) (S : Stacks repairCompactT A)
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B headers
      (fun i => S.R (compactDescriptorCore i)))
    (hL : ∀ j, L j < 2 ^ Lw j) (hW : ∀ j, repairCompactSourceWidth p X (repairDescriptorKey j) + 1 < 2 ^ L j)
    (hsize : ∀ j, repairCompactRows p (repairDescriptorKey j) < 2 ^ Lg j)
    (hwidth : ∀ j, S.R (compactDescriptorAux (.width j)) = binSyms (Lw j) (L j))
    (hsourceWidth : ∀ j, S.R (compactDescriptorAux (.sourceWidth j)) = binSyms (L j) (repairCompactSourceWidth p X (repairDescriptorKey j) + 1))
    (hinput : ∀ j, S.R (compactDescriptorAux (.input j)) = selectorRunFrames (Lg j) (L j) (SparseSelectorRun.compress (repairCompactIndices p X hG hK active s j).reverse).reverse)
    (hscratch : ∀ r : CompactDescriptorRole 11,
      (∀ k, r ≠ .input k) → (∀ k, r ≠ .width k) → (∀ k, r ≠ .sourceWidth k) → S.R (compactDescriptorAux r) = [])
    (hblank : ∀ d, S.R (compactDescriptorCore (repairDescriptorSource d)) = [])
    (hempty : ∀ key, S.R (compactDescriptorCore (repairSetupTarget key)) = [])
    (hwork : ∀ j ∈ [repairHost.out, repairHost.tmp, repairHost.ctmp], S.R (compactDescriptorCore j) = []) :
    let S₁ : Stacks repairCompactT A := { S with R := compactDescriptorBankGenerated S.R (repairCompactJobs p X hG hK active s Lw Lg L) }
    let jobs := repairJobs p X rb wb wm wp wk R B
    let C := embStk compactDescriptorCore S₁
    ∃ (v' : HS repairCompactT Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ compactDescriptorBatchCost (repairCompactJobs p X hG hK active s Lw Lg L) + metadataInstallCost C.R jobs ∧
      Exec body' (.seq (compactDescriptorBatch (repairCompactJobs p X hG hK active s Lw Lg L))
        (embProg compactDescriptorCore id (metadataInstall repairHost.out repairHost.tmp repairHost.ctmp jobs)))
        (mk v S) m (mk v' (embOvr compactDescriptorCore { C with R := metadataInstalled C.R jobs }.get S₁)) := by
  dsimp only
  let S₁ : Stacks repairCompactT A := { S with R := compactDescriptorBankGenerated S.R (repairCompactJobs p X hG hK active s Lw Lg L) }
  let C := embStk compactDescriptorCore S₁
  let jobs := repairJobs p X rb wb wm wp wk R B
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := repairCompactBank_exec p X hG hK active s body' Lw Lg L v S
    hL hW hsize hwidth hsourceWidth hinput hscratch
  have hd : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers C.R :=
    data.compactGenerated p X rb hG hK active s Lw Lg L hblank
  have hkeep (j : Fin repairT) (hj : ∀ d, repairDescriptorSource d ≠ j) :
      C.R j = S.R (compactDescriptorCore j) := by
    apply compactDescriptorBankGenerated_keep
    intro job hjob
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hjob
    exact compactDescriptorCore_injective.ne (hj (repairDescriptorKey k)).symm
  have hregs : ∀ job ∈ jobs, [job.src, job.dst, repairHost.out, repairHost.tmp, repairHost.ctmp].Nodup := by
    intro job hj
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    simpa only [repairSetupJob_src, repairSetupJob_dst] using repairSetup_regs key
  have hsource : ∀ job ∈ jobs, ∀ other ∈ jobs, job.src ≠ other.dst := by
    intro job hj other ho
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    obtain ⟨other, _, rfl⟩ := List.mem_map.mp ho
    simpa only [repairSetupJob_src, repairSetupJob_dst] using repairSetup_sources key other
  have ht : ∀ job ∈ jobs, C.R job.dst = [] := by
    intro job hj
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
    rw [repairSetupJob_dst, hkeep _ (fun d => by rw [repairDescriptorSource_eq]; exact repairSetup_sources _ _)]
    exact hempty key
  have hw (j : Fin repairT) (hj : j ∈ [repairHost.out, repairHost.tmp, repairHost.ctmp]) : C.R j = [] := by
    rw [hkeep j (fun d => by rw [repairDescriptorSource_eq]; exact repairCompactSource_work _ j hj)]
    exact hwork j hj
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := metadataInstall_exec body jobs repairHost.out repairHost.tmp repairHost.ctmp
    (repairJobs_nodup p X rb wb wm wp wk R B) hregs hsource (embDn compactDescriptorCore v₁) C
    (by
      intro job hj
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
      exact hd.jobData p X rb hG hK active s key) ht
    (hw _ (by simp)) (hw _ (by simp)) (hw _ (by simp))
  obtain ⟨v₃, _, hu₃, he₃⟩ := exec_emb_ovr compactDescriptorCore_injective hbody he₂ v₁ rfl S₁ rfl
  change v₂.user = v₁.user at hu₂
  have hu : v₃.user = v.user := hu₃.trans (hu₂.trans hu₁)
  refine ⟨v₃, m₁ + m₂, hu, ?_, ?_⟩
  · exact Nat.add_le_add hm₁ hm₂
  · exact Exec.seq he₁ he₃

end
end IntegerMultBounds.MathlibTM2.Routing
