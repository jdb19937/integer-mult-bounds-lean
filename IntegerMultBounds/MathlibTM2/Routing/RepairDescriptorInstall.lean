module

public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorData
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

private theorem repairSource_work (key : RepairSetupKey) (j : Fin repairT)
    (hj : j ∈ [repairHost.out, repairHost.tmp, repairHost.ctmp]) : repairSetupSource key ≠ j := by
  have hn := (List.nodup_cons.mp (repairSetup_regs key)).1
  intro he
  apply hn
  rw [he]
  exact List.mem_cons_of_mem _ hj

variable {Q A : ℕ} {P U : Type}

variable (p : Par) (X rb : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
  (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)

def repairDescriptorSetupKey : RepairDescriptorKey → RepairSetupKey
  | none => .inr .keyDescriptor
  | some (off, k) => .inl (.desc off k)

theorem repairDescriptorSource_eq (d : RepairDescriptorKey) :
    repairDescriptorSource d = repairSetupSource (repairDescriptorSetupKey d) := by
  cases d with
  | none => rfl
  | some d => rcases d with ⟨off, k⟩; rfl

theorem repairDescriptorInstall_exec
    (body : P → Pr P repairT Q A U) (body' : P → Pr P (repairT + (2 * 11 + 12)) Q A U)
    (hbody : ∀ f, body' f = embProg descriptorCore id (body f))
    (L : Fin 11 → ℕ)
    {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    (v : HS (repairT + (2 * 11 + 12)) Q A U) (S : Stacks (repairT + (2 * 11 + 12)) A)
    (data : RepairPendingDescriptorData p X rb wb wm wp wk R B headers
      (fun i => S.R (descriptorCore i)))
    (hfit : ∀ j, repairDescriptorWidth p X (repairDescriptorKey j) < 2 ^ L j)
    (hwidth : ∀ j, S.R (descriptorBankReg j .width) = binSyms (L j) (repairDescriptorWidth p X (repairDescriptorKey j)))
    (hinput : ∀ j, S.R (descriptorBankSelectors j) = descriptorSelectorFrames (L j)
      (repairDescriptorIndices p X hG hK active s (repairDescriptorKey j)).reverse)
    (hscratch : ∀ i : Fin (2 * 11 + 12), 2 * 11 ≤ i.val → S.R (descriptorAux i) = [])
    (hblank : ∀ d, S.R (descriptorCore (repairDescriptorSource d)) = [])
    (hempty : ∀ key, S.R (descriptorCore (repairSetupTarget key)) = [])
    (hwork : ∀ j ∈ [repairHost.out, repairHost.tmp, repairHost.ctmp], S.R (descriptorCore j) = []) :
    let S₁ : Stacks (repairT + (2 * 11 + 12)) A := { S with R := descriptorBankGenerated S.R (repairDescriptorJobs p X hG hK active s L) }
    let jobs := repairJobs p X rb wb wm wp wk R B
    let C := embStk descriptorCore S₁
    ∃ (v' : HS (repairT + (2 * 11 + 12)) Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ descriptorBatchCost (repairDescriptorJobs p X hG hK active s L) + metadataInstallCost C.R jobs ∧
      Exec body' (.seq (descriptorBatch (repairDescriptorJobs p X hG hK active s L))
        (embProg descriptorCore id (metadataInstall repairHost.out repairHost.tmp repairHost.ctmp jobs)))
        (mk v S) m (mk v' (embOvr descriptorCore { C with R := metadataInstalled C.R jobs }.get S₁)) := by
  dsimp only
  let S₁ : Stacks (repairT + (2 * 11 + 12)) A := { S with R := descriptorBankGenerated S.R (repairDescriptorJobs p X hG hK active s L) }
  let C := embStk descriptorCore S₁
  let jobs := repairJobs p X rb wb wm wp wk R B
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := repairDescriptorBank_exec p X hG hK active s body' L v S
    hfit hwidth hinput hscratch
  have hd : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers C.R :=
    data.generated p X rb hG hK active s L hblank
  have hkeep (j : Fin repairT) (hj : ∀ d, repairDescriptorSource d ≠ j) :
      C.R j = S.R (descriptorCore j) := by
    apply descriptorBankGenerated_keep
    intro job hjob
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hjob
    exact descriptorCore_injective.ne (hj (repairDescriptorKey k)).symm
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
    rw [hkeep j (fun d => by rw [repairDescriptorSource_eq]; exact repairSource_work _ j hj)]
    exact hwork j hj
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := metadataInstall_exec body jobs repairHost.out repairHost.tmp repairHost.ctmp
    (repairJobs_nodup p X rb wb wm wp wk R B) hregs hsource (embDn descriptorCore v₁) C
    (by
      intro job hj
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
      exact hd.jobData p X rb hG hK active s key) ht
    (hw _ (by simp)) (hw _ (by simp)) (hw _ (by simp))
  obtain ⟨v₃, _, hu₃, he₃⟩ := exec_emb_ovr descriptorCore_injective hbody he₂ v₁ rfl S₁ rfl
  exact ⟨v₃, m₁ + m₂, hu₃.trans (hu₂.trans hu₁), Nat.add_le_add hm₁ hm₂, Exec.seq he₁ he₃⟩

end
end IntegerMultBounds.MathlibTM2.Routing
