module

public import IntegerMultBounds.MathlibTM2.Routing.RepairWidthData
public import IntegerMultBounds.MathlibTM2.Routing.RepairSetup
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Execute binary row/mask generation followed by the complete R2 installer.
The remaining configuration is input data; neither generated word is assumed. -/

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

/-- Only the literal generated words are added before installation. -/
def repairWidthGenerated (bank : Fin (repairT + 6) → List (Fin (A + 4))) :=
  Function.update (Function.update bank (fieldCore (repairSetupSource (.inr .row))) (binSyms rb 0))
    (fieldCore (repairSetupSource (.inr .keyMask))) (binSyms p.wy (Layer.CompactMasks.maskVal p.wy id))

theorem repairWidthInstall_exec
    (body : P → Pr P repairT Q A U) (body' : P → Pr P (repairT + 6) Q A U)
    (hbody : ∀ f, body' f = embProg fieldCore id (body f))
    (Lr Lm : ℕ) (hr : rb < 2 ^ Lr) (hm : p.wy < 2 ^ Lm)
    {wb wm wp wk R B : ℕ} {headers : Fin 2 → Fin 5 → List Bool}
    (v : HS (repairT + 6) Q A U) (S : Stacks (repairT + 6) A)
    (data : RepairPendingWidthData p X rb hG hK active s wb wm wp wk R B headers
      (fun i => S.R (fieldCore i)))
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr rb)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm p.wy)
    (hscratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R (fieldCore (repairSetupSource (.inr .row))) = [])
    (hmask : S.R (fieldCore (repairSetupSource (.inr .keyMask))) = [])
    (hempty : ∀ key, S.R (fieldCore (repairSetupTarget key)) = [])
    (hwork : ∀ j ∈ [repairHost.out, repairHost.tmp, repairHost.ctmp], S.R (fieldCore j) = []) :
    let S₁ : Stacks (repairT + 6) A := { S with R := repairWidthGenerated p rb S.R }
    let jobs := repairJobs p X rb wb wm wp wk R B
    let C := embStk fieldCore S₁
    ∃ (v' : HS (repairT + 6) Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (Lr * (4 * rb + 11) + 8 * rb + 12) +
        (Lm * (4 * p.wy + 11) + 2 * p.wy + 6) + 1 + metadataInstallCost C.R jobs ∧
      Exec body' (.seq (binaryFieldBatch (repairWidthFields Lr Lm rb p.wy))
        (embProg fieldCore id (metadataInstall repairHost.out repairHost.tmp repairHost.ctmp jobs)))
        (mk v S) m (mk v' (embOvr fieldCore { C with R := metadataInstalled C.R jobs }.get S₁)) := by
  dsimp only
  let S₁ : Stacks (repairT + 6) A := { S with R := repairWidthGenerated p rb S.R }
  let C := embStk fieldCore S₁
  let jobs := repairJobs p X rb wb wm wp wk R B
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := repairWidthFields_exec body' Lr Lm rb p.wy hr hm v S
    hrowWidth hmaskWidth hscratch hrow hmask
  have hd : RepairSetupData p X rb hG hK active s wb wm wp wk R B headers C.R :=
    data.generated p X rb hG hK active s
  have hkeep (j : Fin repairT)
      (hrj : repairSetupSource (.inr .row) ≠ j) (hmj : repairSetupSource (.inr .keyMask) ≠ j) :
      C.R j = S.R (fieldCore j) := by
    simp [C, S₁, embStk, repairWidthGenerated, fieldCore_injective.eq_iff, hrj.symm, hmj.symm]
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
    rw [repairSetupJob_dst, hkeep _ (repairSetup_sources _ _) (repairSetup_sources _ _)]
    exact hempty key
  have hw (j : Fin repairT) (hj : j ∈ [repairHost.out, repairHost.tmp, repairHost.ctmp]) : C.R j = [] := by
    rw [hkeep j (repairSource_work _ j hj) (repairSource_work _ j hj)]
    exact hwork j hj
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := metadataInstall_exec body jobs repairHost.out repairHost.tmp repairHost.ctmp
    (repairJobs_nodup p X rb wb wm wp wk R B) hregs hsource (embDn fieldCore v₁) C
    (by
      intro job hj
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hj
      exact hd.jobData p X rb hG hK active s key) ht
    (hw _ (by simp)) (hw _ (by simp)) (hw _ (by simp))
  obtain ⟨v₃, _, hu₃, he₃⟩ := exec_emb_ovr fieldCore_injective hbody he₂ v₁ rfl S₁ rfl
  exact ⟨v₃, m₁ + m₂, hu₃.trans (hu₂.trans hu₁), Nat.add_le_add hm₁ hm₂, Exec.seq he₁ he₃⟩

end
end IntegerMultBounds.MathlibTM2.Routing
