module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeProgram

/-!
# Frame bookkeeping of the five-class node

After `τ` schedule entries, the role `ρ` of pair `q`, side `e`, port `t` is stored in the exchange
frame `frameAt τ ρ`: the line on side zero, the flag prefix of `7 · levelAt τ q` positions, and the
slots of the hosted residuals still pending on its family (`pendingSum`). `Inv τ X L` says every
role is its logical stream in that frame.

This file holds the algebra of these frames: sums over slots, the orthogonality of the line, the
level prefix and distinct slots (`prefix_mul_slot`, `slotSpan_mul`), the slot sums an idle completes
(`idle_slot_sum`), and the stage-`n` residuals as a slot sum (`familySum_slots`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.MathlibTM2.M6.BitHosting
open Matrix

/-! ### Sums of guarded terms -/

section Sums

variable {α M : Type*} [AddCommMonoid M]

theorem sum_ite_congr (l : List α) (f : α → M) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x ∈ l, (P x ↔ Q x)) :
    (l.map fun x => if P x then f x else 0).sum = (l.map fun x => if Q x then f x else 0).sum := by
  congr 1
  apply List.map_congr_left
  intro x hx
  simp [h x hx]

theorem sum_ite_split (l : List α) (f : α → M) (P Q R : α → Prop) [DecidablePred P]
    [DecidablePred Q] [DecidablePred R] (h : ∀ x ∈ l, (P x ↔ Q x ∨ R x))
    (hd : ∀ x ∈ l, ¬(Q x ∧ R x)) :
    (l.map fun x => if P x then f x else 0).sum =
      (l.map fun x => if Q x then f x else 0).sum + (l.map fun x => if R x then f x else 0).sum := by
  rw [← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro x hx
  by_cases hq : Q x
  · have hr : ¬R x := fun hr => hd x hx ⟨hq, hr⟩
    simp [(h x hx).mpr (Or.inl hq), hq, hr]
  · by_cases hr : R x
    · simp [(h x hx).mpr (Or.inr hr), hq, hr]
    · have hp : ¬P x := fun hp => ((h x hx).mp hp).elim hq hr
      simp [hp, hq, hr]

theorem sum_ite_none (l : List α) (f : α → M) (P : α → Prop) [DecidablePred P]
    (h : ∀ x ∈ l, ¬P x) : (l.map fun x => if P x then f x else 0).sum = 0 := by
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simp [h x hx]

end Sums

theorem mul_sum_ite {α : Type*} (l : List α) (A : Matrix Axis Axis ℚ) (f : α → Matrix Axis Axis ℚ)
    (P : α → Prop) [DecidablePred P] (h : ∀ x ∈ l, P x → A * f x = 0) :
    A * (l.map fun x => if P x then f x else 0).sum = 0 := by
  rw [← List.sum_map_mul_left]
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  by_cases hp : P x
  · simp [hp, h x hx hp]
  · simp [hp]

theorem sum_ite_mul {α : Type*} (l : List α) (A : Matrix Axis Axis ℚ) (f : α → Matrix Axis Axis ℚ)
    (P : α → Prop) [DecidablePred P] (h : ∀ x ∈ l, P x → f x * A = 0) :
    (l.map fun x => if P x then f x else 0).sum * A = 0 := by
  rw [← List.sum_map_mul_right]
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  by_cases hp : P x
  · simp [hp, h x hx hp]
  · simp [hp]

/-! ### Frames -/

/-- A slot belongs to `ρ`'s family. -/
def OfFamily (ρ : Role) (σ : Slot) : Prop := pairOf σ.idle = ρ.bank.val / 2 ∧ σ.copy = roleCopy ρ

instance (ρ : Role) (σ : Slot) : Decidable (OfFamily ρ σ) := by unfold OfFamily; infer_instance

/-- The slot projector of `σ` on `ρ`'s port. -/
noncomputable def slotSpan (ρ : Role) (σ : Slot) : Matrix Axis Axis ℚ :=
  (port ρ.port.val).span (slotPos σ) (slotPos σ + 8)

/-- The slots of `ρ`'s family pending at `τ`. -/
noncomputable def pendingSum (τ : ℕ) (ρ : Role) : Matrix Axis Axis ℚ :=
  (slots.map fun σ => if OfFamily ρ σ ∧ Pending τ σ then slotSpan ρ σ else 0).sum

/-- The line on side zero. -/
noncomputable def sidePart (ρ : Role) : Matrix Axis Axis ℚ :=
  if ρ.bank.val % 2 = 0 then (port ρ.port.val).linePart else 0

/-- The frame of `ρ` after `τ` entries. -/
noncomputable def frameAt (τ : ℕ) (ρ : Role) : Matrix Axis Axis ℚ :=
  sidePart ρ + (port ρ.port.val).span 0 (7 * levelAt τ (ρ.bank.val / 2)) + pendingSum τ ρ

/-- Every role is its logical stream in its frame. -/
def Inv (τ : ℕ) (X L : State) : Prop := ∀ ρ, X ρ = along (exchange (frameAt τ ρ)) (L ρ)

theorem port_ok (ρ : Role) : (port ρ.port.val).Checked := port_checked _ ρ.port.isLt

theorem linePart_mul_span {c : PortCertificate} (hc : c.Checked) (x y : ℕ) :
    c.linePart * c.span x y = 0 := by
  have h : c.linePart * c.flag = 0 := by
    rw [PortCertificate.linePart, PortCertificate.flag, fromBlocks_multiply,
      PortCertificate.lineProj_mul_complement hc]
    simp [← fromBlocks_zero]
  rw [PortCertificate.span, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.zero_mul,
    Matrix.zero_mul]

theorem span_mul_linePart {c : PortCertificate} (hc : c.Checked) (x y : ℕ) :
    c.span x y * c.linePart = 0 := by
  have h := congrArg transpose (linePart_mul_span hc x y)
  have hl : c.linePartᵀ = c.linePart := by
    rw [PortCertificate.linePart, fromBlocks_transpose, PortCertificate.lineProj_transpose]
    simp
  have hs : (c.span x y)ᵀ = c.span x y := by
    rw [PortCertificate.span, transpose_mul, transpose_mul, transpose_transpose, interval,
      diagonal_transpose, Matrix.mul_assoc]
  rwa [transpose_mul, hl, hs, transpose_zero] at h

theorem sidePart_mul_span (ρ : Role) (x y : ℕ) : sidePart ρ * (port ρ.port.val).span x y = 0 := by
  unfold sidePart
  split_ifs
  · exact linePart_mul_span (port_ok ρ) x y
  · exact Matrix.zero_mul _

theorem span_mul_sidePart (ρ : Role) (x y : ℕ) : (port ρ.port.val).span x y * sidePart ρ = 0 := by
  unfold sidePart
  split_ifs
  · exact span_mul_linePart (port_ok ρ) x y
  · exact Matrix.mul_zero _

/-- Distinct slots of one idle and copy are orthogonal. -/
theorem slotSpan_mul (ρ : Role) (σ π : Slot) (hσ : σ ∈ slots) (hπ : π ∈ slots)
    (hidle : σ.idle = π.idle) (hcopy : σ.copy = π.copy) (hne : σ ≠ π) :
    slotSpan ρ σ * slotSpan ρ π = 0 := by
  have hf := slot_fits _ hσ
  have hf' := slot_fits _ hπ
  have hoff : σ.offset ≠ π.offset := fun ho =>
    hne (slot_key_injective _ hσ _ hπ (by simp only [slotKey, hidle, hcopy, ho]))
  simp only [slotSpan, slotPos, hidle]
  rcases Nat.lt_or_gt_of_ne hoff with hlt | hlt
  · exact PortCertificate.span_mul_disjoint (port_ok ρ) (by omega)
  · exact span_mul_disjoint_rev (port_ok ρ) (by omega)

theorem prefix_mul_slot (ρ : Role) (σ : Slot) (e : ℕ) (he : e ≤ slotPos σ) :
    (port ρ.port.val).span 0 e * slotSpan ρ σ = 0 :=
  PortCertificate.span_mul_disjoint (port_ok ρ) he

theorem slot_mul_prefix (ρ : Role) (σ : Slot) (e : ℕ) (he : e ≤ slotPos σ) :
    slotSpan ρ σ * (port ρ.port.val).span 0 e = 0 :=
  span_mul_disjoint_rev (port_ok ρ) he

/-! ### Stage-`n` residuals as a slot sum -/

theorem filter_stage_eq (n : Fin 9) :
    slots.filter (·.stage = n.val) = (List.range 439).map (slotOf n) := by
  have hL := slot_helpers n.val n.isLt
  have hlen : (slots.filter (·.stage = n.val)).length = 439 := by
    have := congrArg List.length hL
    simpa using this
  apply List.ext_getElem
  · simp [hlen]
  · intro h h1 h2
    simp only [List.getElem_map, List.getElem_range, slotOf]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

theorem sum_filter_ite {α M : Type*} [AddCommMonoid M] (l : List α) (p : α → Bool) (f : α → M)
    (P : α → Prop) [DecidablePred P] :
    ((l.filter p).map fun x => if P x then f x else 0).sum =
      (l.map fun x => if p x = true ∧ P x then f x else 0).sum := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    by_cases ha : p a = true
    · simp [ha, ih]
    · simp [ha, ih]

/-- The stage-`n` residuals of `ρ`'s family, as a sum over slots. -/
theorem familySum_slots (n : Fin 9) (ρ : Role) :
    familySum n ρ =
      (slots.map fun σ => if OfFamily ρ σ ∧ σ.stage = n.val then slotSpan ρ σ else 0).sum := by
  have h1 : familySum n ρ = ((List.range 439).map fun h =>
      if OfFamily ρ (slotOf n h) then slotSpan ρ (slotOf n h) else 0).sum := by
    rw [familySum]
    congr 1
    apply List.map_congr_left
    intro h _
    by_cases hf : FamilyHosts n ρ h
    · have hf' : OfFamily ρ (slotOf n h) := hf
      rw [ite_eq_left hf, ite_eq_left hf', helperSpan, slotSpan]
      congr 2
      have := hf.2
      simp only [roleCopy] at this
      rw [this]
      have := ρ.port.isLt
      omega
    · have hf' : ¬OfFamily ρ (slotOf n h) := hf
      rw [ite_eq_right hf, ite_eq_right hf']
  have h2 : ((List.range 439).map fun h =>
      if OfFamily ρ (slotOf n h) then slotSpan ρ (slotOf n h) else 0) =
      ((List.range 439).map (slotOf n)).map fun σ => if OfFamily ρ σ then slotSpan ρ σ else 0 := by
    rw [List.map_map]
    rfl
  rw [h1, h2, ← filter_stage_eq, sum_filter_ite]
  apply sum_ite_congr
  intro σ _
  simp only [decide_eq_true_eq]
  tauto

/-! ### The slots an idle completes -/

theorem filter_zipIdx_flatMap (f : ℕ → ℕ) (c : ℕ) : ∀ (l : List ℕ) (n : ℕ),
    ((((l.zipIdx n).flatMap fun x => (List.range x.1).map fun j => (x.2, f j)).filter
      fun y => decide (y.1 = c)).map Prod.snd) =
      if n ≤ c ∧ c < n + l.length then (List.range (l.getD (c - n) 0)).map f else []
  | [], n => by
    rw [ite_eq_right (by simp only [List.length_nil]; omega)]
    rfl
  | a :: rest, n => by
    have h1 : (((List.range a).map fun j => (n, f j)).filter fun y => decide (y.1 = c)) =
        if c = n then (List.range a).map (fun j => (n, f j)) else [] := by
      split_ifs with hc
      · rw [List.filter_eq_self]
        intro y hy
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
        simp [hc]
      · rw [List.filter_eq_nil_iff]
        intro y hy
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
        simp only [decide_eq_true_eq]
        exact fun e => hc e.symm
    rw [List.zipIdx_cons, List.flatMap_cons, List.filter_append, List.map_append, h1,
      filter_zipIdx_flatMap f c rest (n + 1), List.length_cons]
    by_cases hc : c = n
    · subst hc
      simp [List.map_map, Function.comp_def]
    · rw [ite_eq_right hc]
      simp only [List.map_nil, List.nil_append]
      by_cases hr : n + 1 ≤ c ∧ c < n + 1 + rest.length
      · rw [ite_eq_left hr, ite_eq_left ⟨by omega, by omega⟩, show c - n = (c - (n + 1)) + 1 by omega]
        rfl
      · rw [ite_eq_right hr, ite_eq_right (fun h => hr ⟨by omega, by omega⟩)]

theorem copyCounts_length : ∀ i < 9, (copyCounts i).length = 222 := by
  decide +kernel

/-- The slots of each idle and copy, by offset. -/
theorem idle_copy_offsets (i : ℕ) (hi : i < 9) (c : ℕ) (hc : c < 222) :
    ((idlePositions i).filter (·.1 = c)).map (·.2) = (List.range (copyCount i c)).map (8 * ·) := by
  have h := filter_zipIdx_flatMap (fun j => 8 * j) c (copyCounts i) 0
  rw [ite_eq_left ⟨Nat.zero_le _, by rw [copyCounts_length i hi]; omega⟩, Nat.sub_zero] at h
  exact h

theorem span_self (c : PortCertificate) (x : ℕ) : c.span x x = 0 := by
  have : interval x x = 0 := by
    rw [interval, ← diagonal_zero]
    congr 1
    funext p
    split_ifs with h
    · omega
    · rfl
  rw [PortCertificate.span, this, Matrix.mul_zero, Matrix.zero_mul]

theorem span_telescope (c : PortCertificate) (x : ℕ) :
    ∀ k, ((List.range k).map fun j => c.span (x + 8 * j) (x + 8 * j + 8)).sum = c.span x (x + 8 * k)
  | 0 => by
    simp only [List.range_zero, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero]
    exact (span_self c x).symm
  | k + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, span_telescope c x k, List.map_singleton,
      List.sum_singleton, show x + 8 * (k + 1) = x + 8 * k + 8 by ring,
      PortCertificate.span_add (by omega) (by omega)]

theorem sum_ite_eq_filter {α M : Type*} [AddCommMonoid M] (l : List α) (P : α → Prop)
    [DecidablePred P] (f : α → M) :
    (l.map fun x => if P x then f x else 0).sum = ((l.filter fun x => decide (P x)).map f).sum := by
  induction l with
  | nil => rfl
  | cons a rest ih => by_cases ha : P a <;> simp [ha, ih]

theorem sum_flatMap_gen {α β M : Type*} [AddCommMonoid M] (l : List α) (f : α → List β)
    (g : β → M) : ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a rest ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem roleCopy_lt (ρ : Role) : roleCopy ρ < 222 := by
  unfold roleCopy
  have := ρ.bank.isLt
  have := ρ.port.isLt
  omega

/-- The slots of idle `i` and `ρ`'s copy fill the hosted part of the idle's pending interval. -/
theorem idle_slot_sum (ρ : Role) (i : ℕ) (hi : i < 9) :
    (slots.map fun σ => if σ.idle = i ∧ σ.copy = roleCopy ρ then slotSpan ρ σ else 0).sum =
      (port ρ.port.val).span (7 * idleSource i) (7 * idleSource i + 8 * copyCount i (roleCopy ρ)) := by
  let c := roleCopy ρ
  let F : ℕ × ℕ × ℕ → Matrix Axis Axis ℚ := fun k => if k.1 = i ∧ k.2.1 = c then
      (port ρ.port.val).span (7 * idleSource k.1 + k.2.2) (7 * idleSource k.1 + k.2.2 + 8) else 0
  have h1 : (slots.map fun σ => if σ.idle = i ∧ σ.copy = roleCopy ρ then slotSpan ρ σ else 0) =
      (slots.map fun σ => (σ.idle, σ.copy, σ.offset)).map F := by
    rw [List.map_map]
    rfl
  rw [h1, slot_positions, sum_flatMap_gen, ← List.sum_toFinset _ List.nodup_range,
    Finset.sum_eq_single i]
  · rw [List.map_map]
    have h2 : ((idlePositions i).map (F ∘ fun x => (i, x.1, x.2))) = (idlePositions i).map
        (fun x => if x.1 = c then (port ρ.port.val).span (7 * idleSource i + x.2)
          (7 * idleSource i + x.2 + 8) else 0) := by
      apply List.map_congr_left
      intro x _
      simp [F]
    rw [h2, sum_ite_eq_filter]
    let g : ℕ → Matrix Axis Axis ℚ := fun o =>
      (port ρ.port.val).span (7 * idleSource i + o) (7 * idleSource i + o + 8)
    show (((idlePositions i).filter fun x => decide (x.1 = c)).map (g ∘ Prod.snd)).sum = _
    rw [← List.map_map, idle_copy_offsets i hi c (roleCopy_lt ρ), List.map_map]
    exact span_telescope _ _ _
  · intro i' _ hi'
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    simp [F, hi']
  · intro hno
    exact absurd (List.mem_toFinset.mpr (List.mem_range.mpr hi)) hno

end IntegerMultBounds.MathlibTM2.M6.BitNode
