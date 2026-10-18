module

public import IntegerMultBounds.MathlibTM2.M6.BitStagePiece

/-!
# Hosted residuals over the five class runs

For a role `ρ` of an inactive pair, the stage piece applies, run by run, the exchanges on the
slots its family hosts in that run (`stagePiece_inactive_prod`). Here:
* `hostSpan_orthogonal`: two different runs host orthogonal slots on `ρ`, because the same slot
  would need the same class shift, and distinct slots of one family and stage lie in one idle at
  distinct offsets;
* `hostSpan_sum`: over all runs, each stage-`n` residual of `ρ`'s family arrives on `ρ` exactly
  once, from the one class run whose shift lands on `ρ`'s class;
* `stagePiece_inactive`: so the piece changes `ρ` by the exchange on `familySum n ρ`, the sum of
  those residuals' slot projectors.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.MathlibTM2.M6.BitHosting
open Matrix

variable (n : Fin 9)

/-- The copy position of a role: `side · 111 + port`. -/
def roleCopy (ρ : Role) : ℕ := (ρ.bank.val % 2) * 111 + ρ.port.val

/-- Helper `h` of stage `n` is hosted by `ρ`'s family. -/
def FamilyHosts (ρ : Role) (h : ℕ) : Prop :=
  pairOf (slotOf n h).idle = ρ.bank.val / 2 ∧ (slotOf n h).copy = roleCopy ρ

instance (ρ : Role) (h : ℕ) : Decidable (FamilyHosts n ρ h) := by
  unfold FamilyHosts; infer_instance

/-- The sum of the slot projectors of the stage-`n` residuals of `ρ`'s family. -/
noncomputable def familySum (ρ : Role) : Matrix Axis Axis ℚ :=
  ((List.range 439).map fun h => if FamilyHosts n ρ h then helperSpan n h else 0).sum

theorem role_ext {ρ σ : Role} (hr : ρ.replica = σ.replica) (hb : ρ.bank = σ.bank)
    (hp : ρ.port = σ.port) (hc : ρ.cls = σ.cls) : ρ = σ := by
  cases ρ
  cases σ
  simp_all

theorem hostRole_eq_iff (r : Fin 32) (d : Fin 5) (h : ℕ) (hh : h < 439) (ρ : Role) :
    hostRole n r d h = ρ ↔
      r = ρ.replica ∧ FamilyHosts n ρ h ∧ hostClass (slotOf n h) d.val = ρ.cls.val := by
  obtain ⟨hσ, -, -⟩ := slotOf_spec n.val n.isLt h hh
  have hf := slot_fits _ hσ
  have hq := pairOf_lt _ (by omega : (slotOf n h).idle < 10)
  have hb := ρ.bank.isLt
  have hp := ρ.port.isLt
  constructor
  · rintro rfl
    obtain ⟨h1, h2, h3⟩ := hostRole_pair n r d h hh
    refine ⟨rfl, ⟨h1.symm, ?_⟩, rfl⟩
    simp only [roleCopy]
    omega
  · rintro ⟨rfl, ⟨h1, h2⟩, h3⟩
    simp only [roleCopy] at h2
    refine role_ext (σ := ρ) (ρ := hostRole n ρ.replica d h) rfl ?_ ?_ ?_
    · apply Fin.ext
      show (2 * pairOf (slotOf n h).idle + (slotOf n h).copy / 111) % 8 = ρ.bank.val
      omega
    · apply Fin.ext
      show (slotOf n h).copy % 111 = ρ.port.val
      omega
    · exact Fin.ext h3

theorem interval_mul_disjoint_rev {x y x' y' : ℕ} (hy : y' ≤ x) :
    interval x y * interval x' y' = 0 := by
  rw [interval, interval, diagonal_mul_diagonal, ← diagonal_zero]
  congr 1
  funext p
  by_cases h : x ≤ pendingIndex p
  · simp [h, show ¬pendingIndex p < y' by omega]
  · simp [h]

theorem span_mul_disjoint_rev {c : PortCertificate} (hc : c.Checked) {x y x' y' : ℕ}
    (hy : y' ≤ x) : c.span x y * c.span x' y' = 0 := by
  rw [PortCertificate.span_mul hc, interval_mul_disjoint_rev hy, Matrix.mul_zero, Matrix.zero_mul]

/-- Distinct slots of one family and stage are orthogonal. -/
theorem helperSpan_mul (h h' : ℕ) (hh : h < 439) (hh' : h' < 439)
    (hpair : pairOf (slotOf n h).idle = pairOf (slotOf n h').idle)
    (hcopy : (slotOf n h).copy = (slotOf n h').copy) (hne : slotOf n h ≠ slotOf n h') :
    helperSpan n h * helperSpan n h' = 0 := by
  obtain ⟨hσ, hst, -⟩ := slotOf_spec n.val n.isLt h hh
  obtain ⟨hσ', hst', -⟩ := slotOf_spec n.val n.isLt h' hh'
  have hf := slot_fits _ hσ
  have hf' := slot_fits _ hσ'
  have hidle : (slotOf n h).idle = (slotOf n h').idle := by
    by_contra hij
    exact same_pair_windows _ (by omega) _ (by omega) hij hpair _ (slot_in_window _ hσ)
      (hst.trans hst'.symm ▸ slot_in_window _ hσ')
  have hoff : (slotOf n h).offset ≠ (slotOf n h').offset := by
    intro ho
    exact hne (slot_key_injective _ hσ _ hσ' (by simp only [slotKey, hidle, hcopy, ho]))
  have hc := port_checked ((slotOf n h).copy % 111) (Nat.mod_lt _ (by norm_num))
  simp only [helperSpan, slotPos, hcopy, hidle] at hc ⊢
  rcases Nat.lt_or_gt_of_ne hoff with hlt | hlt
  · exact PortCertificate.span_mul_disjoint hc (by omega)
  · exact span_mul_disjoint_rev hc (by omega)

/-- Two different runs host orthogonal slots on a role. -/
theorem hostSpan_orthogonal (k k' : Fin 32 × Fin 5) (hkk : k ≠ k') (ρ : Role) :
    hostSpan n k.1 k.2 ρ * hostSpan n k'.1 k'.2 ρ = 0 := by
  rw [hostSpan, ← List.sum_map_mul_right]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
  rw [hostSpan, ← List.sum_map_mul_left]
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hy
  have hh1 := List.mem_range.mp hh
  have hh2 := List.mem_range.mp hh'
  by_cases e1 : hostRole n k.1 k.2 h = ρ
  · by_cases e2 : hostRole n k'.1 k'.2 h' = ρ
    · rw [if_pos e1, if_pos e2]
      obtain ⟨hr, ⟨hp1, hc1⟩, hcl⟩ := (hostRole_eq_iff n _ _ h hh1 ρ).mp e1
      obtain ⟨hr', ⟨hp2, hc2⟩, hcl'⟩ := (hostRole_eq_iff n _ _ h' hh2 ρ).mp e2
      have hd : k.2 ≠ k'.2 := fun hd => hkk (Prod.ext (hr.trans hr'.symm) hd)
      have hne : slotOf n h ≠ slotOf n h' := by
        intro hs
        rw [hs] at hcl
        apply hd
        apply Fin.ext
        have := k.2.isLt
        have := k'.2.isLt
        simp only [hostClass] at hcl hcl'
        omega
      exact helperSpan_mul n h h' hh1 hh2 (hp1.trans hp2.symm) (hc1.trans hc2.symm) hne
    · rw [if_neg e2, Matrix.mul_zero]
  · rw [if_neg e1, Matrix.zero_mul]

theorem stageRuns_toFinset : stageRuns.toFinset = Finset.univ := by
  ext k
  simp [mem_stageRuns]

/-- Over all runs, each stage-`n` residual of the family arrives on the role once. -/
theorem hostSpan_sum (ρ : Role) :
    (stageRuns.map fun k => hostSpan n k.1 k.2 ρ).sum = familySum n ρ := by
  rw [← List.sum_toFinset _ stageRuns_nodup, stageRuns_toFinset, familySum,
    ← List.sum_toFinset _ List.nodup_range]
  simp only [hostSpan]
  conv_lhs => arg 2; ext k; rw [← List.sum_toFinset _ List.nodup_range]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [List.mem_toFinset, List.mem_range] at hh
  by_cases hfam : FamilyHosts n ρ h
  · rw [if_pos hfam]
    let j := (slotOf n h).offset / 8
    let d₀ : Fin 5 := ⟨(ρ.cls.val + 5 - j % 5) % 5, Nat.mod_lt _ (by norm_num)⟩
    rw [Finset.sum_eq_single (ρ.replica, d₀)]
    · rw [if_pos ((hostRole_eq_iff n _ _ h hh ρ).mpr ⟨rfl, hfam, by
        simp only [hostClass, d₀, j]; have := ρ.cls.isLt; omega⟩)]
    · intro k _ hk
      rw [if_neg]
      intro e
      obtain ⟨hr, -, hcl⟩ := (hostRole_eq_iff n _ _ h hh ρ).mp e
      apply hk
      refine Prod.ext hr ?_
      apply Fin.ext
      have := k.2.isLt
      simp only [hostClass] at hcl
      simp only [d₀, j]
      omega
    · intro hno
      exact absurd (Finset.mem_univ _) hno
  · rw [if_neg hfam]
    apply Finset.sum_eq_zero
    intro k _
    rw [if_neg]
    intro e
    exact hfam ((hostRole_eq_iff n _ _ h hh ρ).mp e).2.1

/-- A role of another pair changes by the exchange on its family's residuals of the stage. -/
theorem stagePiece_inactive (X : State) (ρ : Role) (hρ : ρ.bank.val / 2 ≠ activePair n.val) :
    stagePiece n X ρ = along (exchange (familySum n ρ)) (X ρ) := by
  have hmap : stageRuns.map (fun k => exchange (hostSpan n k.1 k.2 ρ)) =
      (stageRuns.map fun k => hostSpan n k.1 k.2 ρ).map exchange := by
    rw [List.map_map]
    rfl
  rw [stagePiece_inactive_prod n X ρ hρ, hmap]
  rw [prod_exchange _ (List.pairwise_map.mpr
    (stageRuns_nodup.imp fun hkk => hostSpan_orthogonal n _ _ hkk ρ)), hostSpan_sum]

end IntegerMultBounds.MathlibTM2.M6.BitNode
