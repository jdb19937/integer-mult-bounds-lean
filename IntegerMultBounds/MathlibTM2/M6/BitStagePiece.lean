module

public import IntegerMultBounds.MathlibTM2.M6.BitInvocationFrames

/-!
# The stage piece: every replica and class run of one invocation

`stagePiece n` runs the class-`d` run of the stage-`n` invocation for every replica `r < 32` and
class `d < 5`, in the order of `stageRuns`. Its effect on arbitrary dirty roles:
* `stagePiece_side_zero`, `stagePiece_side_one`: the two sides of the active pair, in every
  replica, port and class, change as in their own class run, from the piece's input;
* `stagePiece_inactive`: every role of another pair changes by the exchange on `familySum n ρ`,
  the sum of the slot projectors of the stage-`n` helpers its family hosts. In each class every
  hosted residual of the family arrives once (`hostSpan_sum`), from five different runs whose
  slots are orthogonal (`hostSpan_orthogonal`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.MathlibTM2.M6.BitHosting
open Matrix

/-! ### Folds of role maps -/

section Folds

variable {α : Type*} (run : α → State → State)

theorem foldl_fix (ρ : Role) :
    ∀ (runs : List α) (X : State), (∀ k ∈ runs, ∀ Y, run k Y ρ = Y ρ) →
      (runs.foldl (fun Y k => run k Y) X) ρ = X ρ
  | [], _, _ => rfl
  | k :: rest, X, h => by
    rw [List.foldl_cons, foldl_fix ρ rest _ (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')),
      h k List.mem_cons_self]

/-- A role read and written by a single run of the fold. -/
theorem foldl_one [DecidableEq α] (S : Role → Prop) (F : State → Stream)
    (hF : ∀ X Y, (∀ σ, S σ → X σ = Y σ) → F X = F Y) (k0 : α) (ρ : Role) (hρ : S ρ)
    (hrun : ∀ X, run k0 X ρ = F X) :
    ∀ (runs : List α), runs.Nodup → k0 ∈ runs →
      (∀ k ∈ runs, k ≠ k0 → ∀ Y σ, S σ → run k Y σ = Y σ) →
      ∀ X, (runs.foldl (fun Y k => run k Y) X) ρ = F X
  | [], _, h, _, _ => absurd h List.not_mem_nil
  | k :: rest, hnd, hk0, hother, X => by
    rw [List.foldl_cons]
    by_cases hk : k = k0
    · subst hk
      rw [foldl_fix run ρ rest _ (fun k' hk' Y => hother k' (List.mem_cons_of_mem _ hk')
        (fun e => (List.nodup_cons.mp hnd).1 (e ▸ hk')) Y ρ hρ), hrun]
    · have hk0' : k0 ∈ rest := (List.mem_cons.mp hk0).resolve_left (Ne.symm hk)
      rw [foldl_one S F hF k0 ρ hρ hrun rest (List.nodup_cons.mp hnd).2 hk0'
        (fun k' hk' => hother k' (List.mem_cons_of_mem _ hk')) (run k X)]
      exact hF _ _ fun σ hσ => hother k List.mem_cons_self hk X σ hσ

/-- A role on which every run acts by a frame change. -/
theorem foldl_along (ρ : Role) (E : α → Matrix (Axis ⊕ Axis) (Axis ⊕ Axis) ℚ)
    (hrun : ∀ k Y, run k Y ρ = along (E k) (Y ρ)) :
    ∀ (runs : List α) (X : State),
      (runs.foldl (fun Y k => run k Y) X) ρ = along ((runs.map E).prod) (X ρ)
  | [], X => by simp [along_one]
  | k :: rest, X => by
    rw [List.foldl_cons, foldl_along ρ E hrun rest, hrun, List.map_cons, List.prod_cons, along_mul]

end Folds

theorem mul_list_sum (a : Matrix Axis Axis ℚ) :
    ∀ (l : List (Matrix Axis Axis ℚ)), (∀ b ∈ l, a * b = 0) → a * l.sum = 0
  | [], _ => by simp
  | b :: rest, h => by
    rw [List.sum_cons, Matrix.mul_add, h b List.mem_cons_self, zero_add]
    exact mul_list_sum a rest fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- Exchanges on pairwise orthogonal projectors multiply to the exchange on their sum. -/
theorem prod_exchange (l : List (Matrix Axis Axis ℚ)) (h : l.Pairwise fun A B => A * B = 0) :
    (l.map exchange).prod = exchange l.sum := by
  induction l with
  | nil => simp [exchange_zero]
  | cons a rest ih =>
    rw [List.pairwise_cons] at h
    rw [List.map_cons, List.prod_cons, ih h.2, exchange_mul_of_orthogonal (mul_list_sum a rest h.1),
      List.sum_cons]

/-! ### The runs -/

@[irreducible] def stageRuns : List (Fin 32 × Fin 5) :=
  (List.finRange 32).flatMap fun r => (List.finRange 5).map fun d => (r, d)

theorem stageRuns_nodup : stageRuns.Nodup := by
  decide +kernel

theorem mem_stageRuns (k : Fin 32 × Fin 5) : k ∈ stageRuns := by
  unfold stageRuns
  simp

/-- One class run of the stage piece. -/
noncomputable def stageRun (n : Fin 9) (k : Fin 32 × Fin 5) (X : State) : State := invoke n k.1 k.2 X

/-- The stage piece. -/
noncomputable def stagePiece (n : Fin 9) (X : State) : State :=
  stageRuns.foldl (fun Y k => stageRun n k Y) X

variable (n : Fin 9)

/-! ### The active pair -/

theorem sideRole_bank (r : Fin 32) (d : Fin 5) (side : ℕ) (hs : side < 2) (t : Fin 111) :
    (sideRole n r d side t).bank.val = 2 * activePair n.val + side := by
  have := activePair_lt n
  simp only [sideRole]
  omega

theorem hostRole_pair (r : Fin 32) (d : Fin 5) (h : ℕ) (hh : h < 439) :
    (hostRole n r d h).bank.val / 2 = pairOf (slotOf n h).idle ∧
      (hostRole n r d h).bank.val % 2 = (slotOf n h).copy / 111 ∧
      (hostRole n r d h).port.val = (slotOf n h).copy % 111 := by
  obtain ⟨hσ, -, -⟩ := slotOf_spec n.val n.isLt h hh
  have hf := slot_fits _ hσ
  have hq := pairOf_lt _ (by omega : (slotOf n h).idle < 10)
  refine ⟨?_, ?_, rfl⟩
  · show (2 * pairOf (slotOf n h).idle + (slotOf n h).copy / 111) % 8 / 2 = _
    omega
  · show (2 * pairOf (slotOf n h).idle + (slotOf n h).copy / 111) % 8 % 2 = _
    omega

theorem host_inactive (r : Fin 32) (d : Fin 5) (h : ℕ) (hh : h < 439) :
    (hostRole n r d h).bank.val / 2 ≠ activePair n.val := by
  obtain ⟨hσ, hst, -⟩ := slotOf_spec n.val n.isLt h hh
  have hoff := slot_off_active _ hσ
  rw [hst] at hoff
  rw [(hostRole_pair n r d h hh).1]
  exact hoff

/-- Roles of the active pair own registers only in their own replica and class. -/
theorem owner_eq_side (r : Fin 32) (d : Fin 5) (j : ℕ) (hj : j < 661) (ρ : Role)
    (hρ : ρ.bank.val / 2 = activePair n.val) (hown : owner n r d j = ρ) :
    ρ.replica = r ∧ ρ.cls = d := by
  by_cases hj2 : j < 222
  · simp only [owner, hj2, ite_true, sideRole] at hown
    rw [← hown]
    exact ⟨rfl, rfl⟩
  · simp only [owner, hj2, ite_false] at hown
    exact absurd (hown ▸ hρ) (host_inactive n r d (j - 222) (by omega))

theorem side_pair (r : Fin 32) (d : Fin 5) (side : ℕ) (hs : side < 2) (t : Fin 111) :
    (sideRole n r d side t).bank.val / 2 = activePair n.val := by
  rw [sideRole_bank n r d side hs t]
  omega

theorem stagePiece_side (X : State) (r : Fin 32) (d : Fin 5) (t : Fin 111) (side : ℕ)
    (hs : side < 2) :
    stagePiece n X (sideRole n r d side t) = invoke n r d X (sideRole n r d side t) := by
  refine foldl_one (stageRun n)
    (fun σ => σ = sideRole n r d 0 t ∨ σ = sideRole n r d 1 t)
    (fun Y => invoke n r d Y (sideRole n r d side t)) ?_ (r, d) _ ?_ (fun _ => rfl) stageRuns
    stageRuns_nodup (mem_stageRuns _) ?_ X
  · intro Y Z hYZ
    have h0 := hYZ _ (Or.inl rfl)
    have h1 := hYZ _ (Or.inr rfl)
    interval_cases side
    · rw [invoke_side_zero, invoke_side_zero, h0, h1]
    · rw [invoke_side_one, invoke_side_one, h0, h1]
  · interval_cases side
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro k _ hk Y σ hσ
    apply invoke_other
    intro j hj hown
    have hp : σ.bank.val / 2 = activePair n.val := by
      rcases hσ with rfl | rfl
      · exact side_pair n r d 0 (by norm_num) t
      · exact side_pair n r d 1 (by norm_num) t
    obtain ⟨hr, hd⟩ := owner_eq_side n k.1 k.2 j hj σ hp hown
    apply hk
    rcases hσ with rfl | rfl <;> exact Prod.ext hr.symm hd.symm

/-- Side zero of the active pair after the stage piece. -/
theorem stagePiece_side_zero (X : State) (r : Fin 32) (d : Fin 5) (t : Fin 111) :
    stagePiece n X (sideRole n r d 0 t) =
      along (exchange (sF t.val n.val) * exchange (sF t.val (n.val + 1))) (X (sideRole n r d 0 t)) +
        (if n.val % 2 = 1 then
          along (exchange (tF t.val n.val) * exchange (sF t.val (n.val + 1))) (X (sideRole n r d 1 t))
        else 0) := by
  rw [stagePiece_side n X r d t 0 (by norm_num), invoke_side_zero]

/-- Side one of the active pair after the stage piece. -/
theorem stagePiece_side_one (X : State) (r : Fin 32) (d : Fin 5) (t : Fin 111) :
    stagePiece n X (sideRole n r d 1 t) =
      along (exchange (tF t.val n.val) * exchange (tF t.val (n.val + 1))) (X (sideRole n r d 1 t)) +
        (if n.val % 2 = 1 then 0 else
          along (exchange (sF t.val n.val) * exchange (tF t.val (n.val + 1))) (X (sideRole n r d 0 t))) := by
  rw [stagePiece_side n X r d t 1 (by norm_num), invoke_side_one]

/-! ### The other pairs -/

/-- The slot projector of helper `h` at stage `n`. -/
noncomputable def helperSpan (h : ℕ) : Matrix Axis Axis ℚ :=
  (port ((slotOf n h).copy % 111)).span (slotPos (slotOf n h)) (slotPos (slotOf n h) + 8)

/-- The slot projectors that the class-`d` run hosts on `ρ`. -/
noncomputable def hostSpan (r : Fin 32) (d : Fin 5) (ρ : Role) : Matrix Axis Axis ℚ :=
  ((List.range 439).map fun h => if hostRole n r d h = ρ then helperSpan n h else 0).sum

theorem sum_single {M : Type*} [AddCommMonoid M] (l : List ℕ) (hl : l.Nodup) (f : ℕ → M)
    (P : ℕ → Prop) [DecidablePred P] (h₀ : ℕ) (hm : h₀ ∈ l) (hP : P h₀)
    (huniq : ∀ h ∈ l, P h → h = h₀) :
    (l.map fun h => if P h then f h else 0).sum = f h₀ := by
  induction l with
  | nil => exact absurd hm List.not_mem_nil
  | cons a rest ih =>
    rw [List.map_cons, List.sum_cons]
    by_cases ha : a = h₀
    · subst ha
      have hzero : (rest.map fun h => if P h then f h else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
        have : ¬P h := fun hPh => (List.nodup_cons.mp hl).1
          (huniq h (List.mem_cons_of_mem _ hh) hPh ▸ hh)
        simp [this]
      simp [hP, hzero]
    · have hPa : ¬P a := fun hPa => ha (huniq a List.mem_cons_self hPa)
      rw [if_neg hPa, zero_add]
      exact ih (List.nodup_cons.mp hl).2 ((List.mem_cons.mp hm).resolve_left (Ne.symm ha))
        (fun h hh => huniq h (List.mem_cons_of_mem _ hh))

theorem sum_none {M : Type*} [AddCommMonoid M] (l : List ℕ) (f : ℕ → M) (P : ℕ → Prop)
    [DecidablePred P] (hP : ∀ h ∈ l, ¬P h) : (l.map fun h => if P h then f h else 0).sum = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
  simp [hP h hh]

/-- A role of another pair changes by the exchange on what its run hosts. -/
theorem invoke_inactive (r : Fin 32) (d : Fin 5) (X : State) (ρ : Role)
    (hρ : ρ.bank.val / 2 ≠ activePair n.val) :
    invoke n r d X ρ = along (exchange (hostSpan n r d ρ)) (X ρ) := by
  by_cases hex : ∃ h < 439, hostRole n r d h = ρ
  · obtain ⟨h, hh, rfl⟩ := hex
    have huniq : ∀ h' ∈ List.range 439, hostRole n r d h' = hostRole n r d h → h' = h := by
      intro h' hh' he
      have := owner_injective n r d (222 + h') (by simp at hh'; omega) (222 + h) (by omega)
        (by simp [owner, show (222 + h') - 222 = h' by omega, show (222 + h) - 222 = h by omega, he])
      omega
    rw [hostSpan, sum_single _ List.nodup_range _ (fun h' => hostRole n r d h' = hostRole n r d h) h
      (List.mem_range.mpr hh) rfl huniq,
      invoke_host n r d X h hh, helperSpan]
  · push_neg at hex
    rw [hostSpan, sum_none _ _ _ (fun h hh => hex h (List.mem_range.mp hh)), exchange_zero,
      along_one]
    apply invoke_other
    intro j hj hown
    by_cases hj2 : j < 222
    · simp only [owner, hj2, ite_true] at hown
      exact hρ (hown ▸ side_pair n r d (regSide n j) (by unfold regSide; split_ifs <;> omega) _)
    · simp only [owner, hj2, ite_false] at hown
      exact hex (j - 222) (by omega) hown

/-- A role of another pair after the stage piece. -/
theorem stagePiece_inactive_prod (X : State) (ρ : Role) (hρ : ρ.bank.val / 2 ≠ activePair n.val) :
    stagePiece n X ρ =
      along ((stageRuns.map fun k => exchange (hostSpan n k.1 k.2 ρ)).prod) (X ρ) :=
  foldl_along (stageRun n) ρ (fun k => exchange (hostSpan n k.1 k.2 ρ))
    (fun k Y => invoke_inactive n k.1 k.2 Y ρ hρ) stageRuns X

end IntegerMultBounds.MathlibTM2.M6.BitNode
