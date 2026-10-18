module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeFrames

/-!
# The node's pieces keep the frame bookkeeping

Each kind of piece takes the invariant `Inv τ` to `Inv (τ + 1)` with the logical streams updated
by the same schedule entry. This file has the stage pieces, `sweep_step`: the active pair's sides
move to the next level and the receiving side receives the other, while every other role gains
the slots its family hosts at this stage. `BitNodeIdle` has the remainder pieces and bridges.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.MathlibTM2.M6.BitHosting
open Matrix

/-! ### Frame changes on streams -/

theorem along_frame_change (F G : Matrix Axis Axis ℚ) (hF : F * F = F) (f : Stream) :
    along (exchange F * exchange G) (along (exchange F) f) = along (exchange G) f := by
  rw [← along_mul, ← Matrix.mul_assoc, exchange_mul_self hF, Matrix.one_mul]

theorem along_frame_add (F A : Matrix Axis Axis ℚ) (h : F * A = 0) (f : Stream) :
    along (exchange A) (along (exchange F) f) = along (exchange (F + A)) f := by
  rw [← along_mul, exchange_mul_of_orthogonal h]

theorem sourceFrame_idem (c : PortCertificate) (hc : c.Checked) (k : ℕ) :
    c.sourceFrame k * c.sourceFrame k = c.sourceFrame k := by
  cases k with
  | zero =>
    rw [PortCertificate.sourceFrame, fromBlocks_multiply, PortCertificate.lineProj_mul_self hc]
    simp
  | succ k =>
    rw [PortCertificate.sourceFrame, fromBlocks_multiply, lower_mul_self]
    simp

theorem targetFrame_idem (c : PortCertificate) (hc : c.Checked) (k : ℕ) :
    c.targetFrame k * c.targetFrame k = c.targetFrame k := by
  cases k with
  | zero => simp [PortCertificate.targetFrame]
  | succ k =>
    rw [PortCertificate.targetFrame, fromBlocks_multiply, lower_mul_self,
      PortCertificate.orth_mul_self hc]
    simp

/-! ### Roles of a pair -/

theorem role_side (n : Fin 9) (ρ : Role) (hρ : ρ.bank.val / 2 = activePair n.val) :
    ρ = sideRole n ρ.replica ρ.cls (ρ.bank.val % 2) ρ.port := by
  rcases ρ with ⟨r, ⟨b, hb⟩, t, d⟩
  simp only [sideRole, Role.mk.injEq, Fin.mk.injEq, true_and, and_true] at hρ ⊢
  omega

theorem withBank_side (n : Fin 9) (r : Fin 32) (d : Fin 5) (t : Fin 111) (e : ℕ) (b : ℕ)
    (hb : b = 2 * activePair n.val + e) :
    withBank (sideRole n r d e t) b = sideRole n r d e t := by
  simp [withBank, sideRole, hb]

theorem withBank_sideRole (n : Fin 9) (r : Fin 32) (d : Fin 5) (t : Fin 111) (e e' b : ℕ)
    (hb : b = 2 * activePair n.val + e') :
    withBank (sideRole n r d e t) b = sideRole n r d e' t := by
  subst hb
  simp [withBank, sideRole]

theorem withBank_other (ρ : Role) (b : ℕ) (hb : b < 8) :
    (withBank ρ b).bank.val = b ∧ (withBank ρ b).port = ρ.port ∧
      (withBank ρ b).replica = ρ.replica ∧ (withBank ρ b).cls = ρ.cls := by
  simp [withBank, Nat.mod_eq_of_lt hb]

/-! ### Frames at the pieces -/

theorem pendingSum_none (τ : ℕ) (ρ : Role) (h : ∀ σ ∈ slots, OfFamily ρ σ → ¬Pending τ σ) :
    pendingSum τ ρ = 0 :=
  sum_ite_none _ _ _ fun σ hσ hp => h σ hσ hp.1 hp.2

theorem frameAt_level (τ : ℕ) (ρ : Role) (h : ∀ σ ∈ slots, OfFamily ρ σ → ¬Pending τ σ) :
    frameAt τ ρ = if ρ.bank.val % 2 = 0 then
        (port ρ.port.val).sourceFrame (levelAt τ (ρ.bank.val / 2))
      else (port ρ.port.val).targetFrame (levelAt τ (ρ.bank.val / 2)) := by
  rw [frameAt, pendingSum_none τ ρ h, add_zero, sidePart]
  split_ifs
  · rw [PortCertificate.sourceFrame_eq (port_ok ρ)]
  · rw [PortCertificate.targetFrame_eq (port_ok ρ), zero_add]

theorem not_pending_of_pair (τ : ℕ) (ρ : Role) (q : ℕ) (hq : ρ.bank.val / 2 = q)
    (h : ∀ σ ∈ slots, pairOf σ.idle = q → ¬Pending τ σ) :
    ∀ σ ∈ slots, OfFamily ρ σ → ¬Pending τ σ :=
  fun σ hσ hf => h σ hσ (hf.1.trans hq)

/-! ### Sweeps -/

theorem stagePos_le : ∀ s < 9, stagePos s + 1 ≤ 29 ∧ stagePos s ≤ 29 := by
  decide +kernel

theorem curIdle_sweep : ∀ s < 9, ∀ q < 4, curIdle (stagePos s) q = curIdle (stagePos s + 1) q := by
  decide +kernel

theorem sF_idem (t : ℕ) (ht : t < 111) (k : ℕ) : sF t k * sF t k = sF t k :=
  sourceFrame_idem _ (port_checked t ht) k

theorem tF_idem (t : ℕ) (ht : t < 111) (k : ℕ) : tF t k * tF t k = tF t k :=
  targetFrame_idem _ (port_checked t ht) k

theorem sweep_active_side (s : Fin 9) (X L : State) (h : Inv (stagePos s.val) X L) (ρ : Role)
    (hρ : ρ.bank.val / 2 = activePair s.val) :
    stagePiece s X ρ = along (exchange (frameAt (stagePos s.val + 1) ρ))
      (logicalStep (.sweep s.val (activePair s.val)) L ρ) := by
  have hsf := sweep_facts s.val s.isLt
  have hap := activePair_lt s
  have hnone : ∀ τ, (τ = stagePos s.val ∨ τ = stagePos s.val + 1) → ∀ ρ' : Role,
      ρ'.bank.val / 2 = activePair s.val → ∀ σ ∈ slots, OfFamily ρ' σ → ¬Pending τ σ := by
    intro τ hτ ρ' hρ' σ hσ hf
    have := (sweep_pending σ hσ s.val s.isLt).1 (hf.1.trans hρ')
    rcases hτ with rfl | rfl
    · exact this.1
    · exact this.2
  have hF : ∀ τ, (τ = stagePos s.val ∨ τ = stagePos s.val + 1) → ∀ e < 2,
      frameAt τ (sideRole s ρ.replica ρ.cls e ρ.port) =
        if e = 0 then sF ρ.port.val (levelAt τ (activePair s.val))
        else tF ρ.port.val (levelAt τ (activePair s.val)) := by
    intro τ hτ e he
    rw [frameAt_level τ _ (hnone τ hτ _ (side_pair s _ _ e he _)), side_pair s _ _ e he _,
      sideRole_bank s _ _ e he _]
    interval_cases e
    · simp [sF, sideRole]
    · simp [tF, sideRole, show (2 * activePair s.val + 1) % 2 = 1 by omega]
  have hl0 : levelAt (stagePos s.val) (activePair s.val) = s.val := hsf.1
  have hl1 : levelAt (stagePos s.val + 1) (activePair s.val) = s.val + 1 := by
    rw [hsf.2 _ hap, ite_eq_left rfl]
  have ht := ρ.port.isLt
  have hρ' := role_side s ρ hρ
  have hb := ρ.bank.isLt
  rcases Nat.lt_or_ge (ρ.bank.val % 2) 1 with hside | hside
  · have he : ρ.bank.val % 2 = 0 := by omega
    rw [he] at hρ'
    rw [hρ', stagePiece_side_zero, h, h, hF _ (Or.inl rfl) 0 (by norm_num),
      hF _ (Or.inl rfl) 1 (by norm_num), hF _ (Or.inr rfl) 0 (by norm_num), ite_eq_left rfl,
      ite_eq_right one_ne_zero, ite_eq_left rfl, hl0, hl1, along_frame_change _ _ (sF_idem _ ht _)]
    have hbank : (sideRole s ρ.replica ρ.cls 0 ρ.port).bank.val = 2 * activePair s.val := by
      rw [sideRole_bank s _ _ 0 (by norm_num)]
      rfl
    simp only [logicalStep, hbank]
    by_cases hodd : s.val % 2 = 1
    · rw [ite_eq_left hodd, ite_eq_left hodd, ite_true, along_frame_change _ _ (tF_idem _ ht _), map_add,
        withBank_sideRole s _ _ ρ.port 0 1 _ rfl]
    · rw [ite_eq_right hodd, ite_eq_right hodd, add_zero, ite_eq_right (by omega)]
  · have he : ρ.bank.val % 2 = 1 := by omega
    rw [he] at hρ'
    rw [hρ', stagePiece_side_one, h, h, hF _ (Or.inl rfl) 1 (by norm_num),
      hF _ (Or.inl rfl) 0 (by norm_num), hF _ (Or.inr rfl) 1 (by norm_num), ite_eq_right one_ne_zero,
      ite_eq_left rfl, ite_eq_right one_ne_zero, hl0, hl1, along_frame_change _ _ (tF_idem _ ht _)]
    have hbank : (sideRole s ρ.replica ρ.cls 1 ρ.port).bank.val = 2 * activePair s.val + 1 := by
      rw [sideRole_bank s _ _ 1 (by norm_num)]
    simp only [logicalStep, hbank]
    by_cases hodd : s.val % 2 = 1
    · rw [ite_eq_left hodd, ite_eq_left hodd, add_zero, ite_eq_right (by omega)]
    · rw [ite_eq_right hodd, ite_eq_right hodd, ite_true, along_frame_change _ _ (sF_idem _ ht _), map_add,
        withBank_sideRole s _ _ ρ.port 1 0 _ (by omega)]

theorem sidePart_mul_slot (ρ : Role) (σ : Slot) : sidePart ρ * slotSpan ρ σ = 0 :=
  sidePart_mul_span ρ _ _

theorem sweep_inactive (s : Fin 9) (X L : State) (h : Inv (stagePos s.val) X L) (ρ : Role)
    (hρ : ρ.bank.val / 2 ≠ activePair s.val) :
    stagePiece s X ρ = along (exchange (frameAt (stagePos s.val + 1) ρ))
      (logicalStep (.sweep s.val (activePair s.val)) L ρ) := by
  have hsf := sweep_facts s.val s.isLt
  have hq : ρ.bank.val / 2 < 4 := by have := ρ.bank.isLt; omega
  have hlogical : logicalStep (.sweep s.val (activePair s.val)) L ρ = L ρ := by
    simp only [logicalStep]
    split_ifs with h1 h2 h3 <;> first | rfl | omega
  have hlev : levelAt (stagePos s.val + 1) (ρ.bank.val / 2) = levelAt (stagePos s.val) (ρ.bank.val / 2) := by
    rw [hsf.2 _ hq, ite_eq_right hρ]
  have hpend : pendingSum (stagePos s.val + 1) ρ = pendingSum (stagePos s.val) ρ + familySum s ρ := by
    rw [familySum_slots, pendingSum, pendingSum]
    apply sum_ite_split
    · intro σ hσ
      rw [(sweep_pending σ hσ s.val s.isLt).2.1]
      tauto
    · intro σ hσ ⟨⟨_, hp⟩, ⟨_, hst⟩⟩
      exact (sweep_pending σ hσ s.val s.isLt).2.2 hst hp
  have horth : frameAt (stagePos s.val) ρ * familySum s ρ = 0 := by
    rw [familySum_slots]
    apply mul_sum_ite
    intro σ hσ ⟨hfam, hst⟩
    have hpend1 : Pending (stagePos s.val + 1) σ :=
      (sweep_pending σ hσ s.val s.isLt).2.1.mpr (Or.inr hst)
    have hlv := pending_level σ hσ _ (stagePos_le s.val s.isLt).1 hpend1
    rw [hfam.1, hlev] at hlv
    rw [frameAt, Matrix.add_mul, Matrix.add_mul, sidePart_mul_slot, zero_add,
      prefix_mul_slot ρ σ _ (by rw [hlv]; simp only [slotPos]; omega), zero_add]
    apply sum_ite_mul
    intro π hπ ⟨hfam', hp⟩
    have hne : π ≠ σ := fun e => (sweep_pending σ hσ s.val s.isLt).2.2 hst (e ▸ hp)
    have hi1 := pending_curIdle π hπ _ (stagePos_le s.val s.isLt).2 hp
    have hi2 := pending_curIdle σ hσ _ (stagePos_le s.val s.isLt).1 hpend1
    rw [hfam'.1] at hi1
    rw [hfam.1, ← curIdle_sweep s.val s.isLt _ hq] at hi2
    exact slotSpan_mul ρ π σ hπ hσ (hi1.trans hi2.symm) (hfam'.2.trans hfam.2.symm) hne
  rw [stagePiece_inactive s X ρ hρ, h, along_frame_add _ _ horth, hlogical]
  congr 2
  simp only [frameAt, hlev, hpend]
  abel

/-- A stage piece keeps the frame bookkeeping. -/
theorem sweep_step (s : Fin 9) (X L : State) (h : Inv (stagePos s.val) X L) :
    Inv (stagePos s.val + 1) (stagePiece s X) (logicalStep (.sweep s.val (activePair s.val)) L) := by
  intro ρ
  by_cases hρ : ρ.bank.val / 2 = activePair s.val
  · exact sweep_active_side s X L h ρ hρ
  · exact sweep_inactive s X L h ρ hρ

end IntegerMultBounds.MathlibTM2.M6.BitNode
