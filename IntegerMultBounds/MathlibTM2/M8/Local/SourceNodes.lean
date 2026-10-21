module

public import IntegerMultBounds.MathlibTM2.M8.Local.Schedule
public import IntegerMultBounds.MathlibTM2.M8.Local.Witness

/-! Identify actual compiler sources with the checked donor table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local
noncomputable section
open Classical

theorem donorOk_some {k : ℕ} {pos : Bool} {m : ℕ} (h : donorOk records k pos (some m) = true) :
    m < nodeCount ∧ ∃ L, (recAt m).link = some L ∧ L.user = k ∧ L.pos = pos := by
  simp only [donorOk, Bool.and_eq_true, blt_iff] at h
  obtain ⟨hm, hl⟩ := h
  refine ⟨hm, ?_⟩
  split at hl
  · next L hL =>
    simp only [Bool.and_eq_true, beq_iff, beq_iff_eq] at hl
    exact ⟨L, hL, hl.1, hl.2⟩
  · cases hl

theorem donor_ok_at {k : ℕ} (hk : k < nodeCount) (pos : Bool) :
    donorOk records k pos ((recAt k).donor pos) = true := by
  have := allOk_parts (allOk_at k hk)
  cases pos
  · exact this.2.2.1
  · exact this.2.2.2.1

/-- The source of an argument is its donor, if any, and the argument is a free use exactly when
it has none. -/
theorem src_eq {k : ℕ} (hk : leafCount ≤ k) (hkN : k < nodeCount) (pos : Bool) :
    dag.srcNode (.gate k pos) = ((recAt k).donor pos).getD ((recAt k).arg pos) ∧
      (dag.linkedB (.gate k pos) = false ↔ (recAt k).donor pos = none) := by
  cases hd : (recAt k).donor pos with
  | some m =>
    have hok := donor_ok_at hkN pos
    rw [hd] at hok
    obtain ⟨hm, L, hL, hu, hp⟩ := donorOk_some hok
    have hlink : dag.link m = some (L.operand, k, pos) := by simp [dag, hL, hu, hp]
    have hlu : dag.linkUse m = some (.gate k pos) := dag.linkUse_eq.mpr ⟨_, _, _, hlink, rfl⟩
    refine ⟨dag.srcNode_linked dag_valid hm hlu, ?_⟩
    rw [(dag.linkedB_iff _).mpr ⟨m, hm, hlu⟩]
    simp
  | none =>
    have hl : dag.linkedB (.gate k pos) = false := by
      rcases h : dag.linkedB (.gate k pos) with _ | _
      · rfl
      · obtain ⟨n, hn, hlu⟩ := (dag.linkedB_iff _).mp h
        obtain ⟨o, t, p, hlink, he⟩ := dag.linkUse_eq.mp hlu
        cases he
        obtain ⟨L, hL, -, hu, hp⟩ := dag_link hlink
        have := (linkOk_donor hL).2.2.2.2.2.1
        rw [hu, hp, hd] at this
        cases this
    refine ⟨?_, by simp [hl]⟩
    rw [dag.srcNode_free (y := dag.arg k pos)
      (dag.mem_freeUses.mpr ⟨(dag.mem_uses_gate _ k pos).mpr ⟨hkN, hk, rfl⟩, hl⟩)]
    rfl

end
end IntegerMultBounds.MathlibTM2.M8.Local
