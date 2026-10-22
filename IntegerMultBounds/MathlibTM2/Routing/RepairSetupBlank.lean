module

public import IntegerMultBounds.MathlibTM2.Routing.RepairSetupBank

/-! Installed words are disjoint from every required blank key/repair register. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

noncomputable section

def RepairBlank (j : Fin repairT) : Prop :=
  repairHost.Blank j ∨ j = repairReg .acc ∨
    (∃ r : PatternReg 6, (∀ f, r ≠ .fld f) ∧ (∀ k, r ≠ .desc k) ∧ r ≠ .st ∧ repairKey r = j) ∨
    (∃ r : BadReg, (∀ f, r ≠ .fld f) ∧ r ≠ .mask ∧ r ≠ .phase ∧ r ≠ .st ∧ repairBad r = j)

private theorem repairBlank_image (j : Fin repairT) (hj : repairHost.Blank j) :
    ∃ k : Fin selectiveT, repairRoutingEmbed k = j := by
  rcases hj with hm | ⟨d, he⟩ | ⟨d, he⟩ | ⟨off, r, _, _, he⟩ | ⟨c, r, _, he⟩
  · simp only [repairHost, SelectiveHost.map, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · exact ⟨_, he⟩
  · exact ⟨_, he⟩
  · exact ⟨_, he⟩
  · exact ⟨_, he⟩

private theorem repairExtra_not_image (key : RepairExtra) (k : Fin selectiveT) :
    repairExtraTarget key ≠ repairRoutingEmbed k := by
  obtain ⟨r, rfl⟩ := (Fintype.equivFin SelectiveReg).surjective k
  change repairExtraTarget key ≠ repairRoutingEmbed (selectiveReg r)
  rw [repairRoutingEmbed_reg]
  intro he
  cases key <;> cases r <;> simp [repairExtraTarget, repairRoutingRole, repairKey, repairBad] at he
  rename_i f
  have hv := congrArg Fin.val he
  have hf := f.isLt
  change 5 = f.val at hv
  omega

private theorem repairAcc_not_image (k : Fin selectiveT) :
    repairReg .acc ≠ repairRoutingEmbed k := by
  obtain ⟨r, rfl⟩ := (Fintype.equivFin SelectiveReg).surjective k
  change repairReg .acc ≠ repairRoutingEmbed (selectiveReg r)
  rw [repairRoutingEmbed_reg]
  cases r <;> simp [repairRoutingRole]

private theorem repairKey_not_image (r : PatternReg 6) (hf : ∀ f, r ≠ .fld f) (k : Fin selectiveT) :
    repairKey r ≠ repairRoutingEmbed k := by
  obtain ⟨old, rfl⟩ := (Fintype.equivFin SelectiveReg).surjective k
  change repairKey r ≠ repairRoutingEmbed (selectiveReg old)
  rw [repairRoutingEmbed_reg]
  cases r with
  | fld f => exact (hf f rfl).elim
  | _ => cases old <;> simp [repairKey, repairRoutingRole]

private theorem repairBad_not_image (r : BadReg) (hf : ∀ f, r ≠ .fld f) (k : Fin selectiveT) :
    repairBad r ≠ repairRoutingEmbed k := by
  obtain ⟨old, rfl⟩ := (Fintype.equivFin SelectiveReg).surjective k
  change repairBad r ≠ repairRoutingEmbed (selectiveReg old)
  rw [repairRoutingEmbed_reg]
  cases r with
  | fld f => exact (hf f rfl).elim
  | _ => cases old <;> simp [repairBad, repairRoutingRole]

theorem repairSetupTarget_inl (key : SetupKey) : repairSetupTarget (.inl key) =
    repairRoutingEmbed (key.target placedSelectiveHost) := SetupKey.target_map key _ _

/-- No installed metadata word replaces required blank scratch. -/
theorem repairSetup_target_blank (key : RepairSetupKey) (j : Fin repairT) (hj : RepairBlank j) :
    repairSetupTarget key ≠ j := by
  rcases hj with hj | rfl | ⟨r, hf, hd, hst, rfl⟩ | ⟨r, hf, hm, hp, hst, rfl⟩
  · cases key with
    | inl key => exact repairHost_setup.blanks key j hj
    | inr key =>
      intro he
      obtain ⟨k, hk⟩ := repairBlank_image j hj
      exact repairExtra_not_image key k (he.trans hk.symm)
  · cases key with
    | inl key => rw [repairSetupTarget_inl]; exact (repairAcc_not_image _).symm
    | inr key => cases key <;> simp [repairSetupTarget, repairExtraTarget, repairKey, repairBad]
  · cases key with
    | inl key => rw [repairSetupTarget_inl]; exact (repairKey_not_image r hf _).symm
    | inr key =>
      intro he
      cases r <;> first
        | exact (hf _ rfl).elim
        | exact (hd _ rfl).elim
        | exact (hst rfl).elim
        | (cases key <;> simp [repairSetupTarget, repairExtraTarget, repairKey, repairBad] at he)
  · cases key with
    | inl key => rw [repairSetupTarget_inl]; exact (repairBad_not_image r hf _).symm
    | inr key =>
      intro he
      cases r <;> first
        | exact (hf _ rfl).elim
        | exact (hm rfl).elim
        | exact (hp rfl).elim
        | exact (hst rfl).elim
        | (cases key <;> simp [repairSetupTarget, repairExtraTarget, repairKey, repairBad] at he)

end
end IntegerMultBounds.MathlibTM2.Routing
