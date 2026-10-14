module

public import IntegerMultBounds.Schoenhage.DriverRound

/-! The round loops of the transform drivers (§6 task 6): loop over the round script on named tape 6,
one slot round per pass. From the array `R₀` and the whole script, the forward loop ends with records
reached from `R₀` by the computed forward schedule (`Chain … (slotRounds …)`) and the script consumed
(`runs_fwdRounds`); the opposite loop likewise for the opposite schedule (`runs_oppRounds`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct TwistDescriptors

variable {A tL nL : ℕ}

/-- A loop whose body consumes one item of the loop tape, with a cost bound per pass. -/
theorem Runs.loop_sum {a t : ℕ} {i : Fin t} {b : Cmd a t} (I : ℕ → (Fin t → WTape) → Prop) (C : ℕ → ℕ)
    (hdone : ∀ σ, I 0 σ → (σ i).right = [])
    (hstep : ∀ k σ, I (k + 1) σ → (σ i).right ≠ [] ∧ Runs b σ (I k) (C k)) :
    ∀ k σ, I k σ → Runs (.loop i b) σ (I 0) (((List.range k).map fun j => C j + 2).sum) := by
  intro k
  induction k with
  | zero => intro σ h; exact (Runs.loop_done (b := b) (hdone σ h) h).mono (fun _ h => h) (by simp)
  | succ k ih =>
    intro σ h
    obtain ⟨hne, hb⟩ := hstep k σ h
    have := Runs.loop_step (B₂ := ((List.range k).map fun j => C j + 2).sum) hne (hb.mono (fun σ₁ h₁ => ih σ₁ h₁) le_rfl)
    refine this.mono (fun _ h => h) ?_
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem Chain.snoc {r n p : ℕ} {G : (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ} :
    ∀ {Gs : List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ)} {R R' R'' : List (Rec r)},
    Chain n p Gs R R' → RoundStep n p G R' R'' → Chain n p (Gs ++ [G]) R R''
  | _, _, _, _, .nil _, hs => .cons hs (.nil _)
  | _, _, _, _, .cons h hc, hs => .cons h (Chain.snoc hc hs)

/-- The forward round loop. -/
noncomputable def fwdRounds {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A) : Cmd A (DB tL nL) :=
  .loop (nm tL nL 6) (fwdRoundCmd M ht haA)

/-- The opposite round loop. -/
noncomputable def oppRounds {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A) : Cmd A (DB tL nL) :=
  .loop (nm tL nL 6) (oppRoundCmd M ht haA)

variable {r : ℕ} [NeZero r]

/-- The forward loop's cost bound: every slot's round and the loop's tests. -/
noncomputable def fwdRoundsCost {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (p d w CL : ℕ) : ℕ :=
  ((List.range ℓ).map fun h => hadCost p d r w ts ℓ K CL h + 1 + twCost (paperPerm hL) r w ts h + 2).sum

/-- The opposite loop's cost bound. -/
noncomputable def oppRoundsCost {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (p d w CL : ℕ) : ℕ :=
  ((List.range ℓ).map fun k => twCost (paperPerm hL) r w ts (ℓ - 1 - k) + 1 +
    hadCost p d r w ts ℓ K CL (ℓ - 1 - k) + 2).sum

theorem hadWords_ne_nil (p d r w n : ℕ) (ts : List ℕ) (ℓ K h : ℕ) : hadWords p d r w n ts ℓ K h ≠ [] := by
  unfold hadWords; split_ifs <;> simp

set_option maxHeartbeats 4000000 in
theorem runs_fwdRounds {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A)
    {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {p d w CL : ℕ} (hpw : p + 2 ≤ w)
    (hLayer : LayerCalls M ht r p d w ts ℓ K CL) (R₀ : List (Rec r))
    (hRl : R₀.length = ts.prod) (hRd : ∀ f ∈ R₀, DiskGrid p f.1 f.2) (T7 : WTape) :
    Runs (fwdRounds (nL := nL) M ht haA)
      (dstate tL nL (rnamed w (array w R₀) ⟨[], fwdScript p d r w (paperPerm hL) ts ℓ K⟩ T7) (rest r ts))
      (fun σ => ∃ R, Chain (Nat.log 2 ts.prod) p (slotRounds (paperPerm hL) ts ℓ) R₀ R ∧
        R.length = ts.prod ∧ (∀ f ∈ R, DiskGrid p f.1 f.2) ∧
        σ = dstate tL nL (rnamed w (array w R) ⟨(fwdScript p d r w (paperPerm hL) ts ℓ K).reverse, []⟩ T7)
          (rest r ts))
      (fwdRoundsCost hL p d w CL) := by
  set n := Nat.log 2 ts.prod
  set π := paperPerm hL
  set W : ℕ → List (List Bool) := fun h => hadWords p d r w n ts ℓ K h ++ twistWords π r ts h
  set rem : ℕ → List (List Bool) := fun k => (List.range k).reverse.flatMap W
  set Gk : ℕ → List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ) := fun k => (List.range k).reverse.map (slotRound π ts)
  have hrem : ∀ k, rem (k + 1) = W k ++ rem k := fun k => by
    simp [rem, List.range_succ, List.reverse_append]
  have hGk : ∀ k, Gk (k + 1) = slotRound π ts k :: Gk k := fun k => by
    simp [Gk, List.range_succ, List.reverse_append]
  let I : ℕ → (Fin (DB tL nL) → WTape) → Prop := fun k σ => k ≤ ℓ ∧ ∃ R L Gs,
    Chain n p Gs R₀ R ∧ Gs ++ Gk k = slotRounds π ts ℓ ∧ L.reverse ++ rem k = fwdScript p d r w π ts ℓ K ∧
      R.length = ts.prod ∧ (∀ f ∈ R, DiskGrid p f.1 f.2) ∧ σ = dstate tL nL (rnamed w (array w R) ⟨L, rem k⟩ T7) (rest r ts)
  have hloop := Runs.loop_sum (b := fwdRoundCmd (nL := nL) M ht haA) (i := nm tL nL 6) I
    (fun h => hadCost p d r w ts ℓ K CL h + 1 + twCost π r w ts h)
    (fun σ ⟨_, R, L, Gs, _, _, _, _, _, e⟩ => by rw [e, dstate_nm]; simp [rnamed, rem])
    (fun k σ ⟨hk, R, L, Gs, hc, hG, hS, hl, hd, e⟩ => by
      refine ⟨by rw [e, dstate_nm, hrem]; simp [rnamed, W, hadWords_ne_nil], ?_⟩
      rw [e, hrem]
      refine (runs_fwdRoundCmd (nL := nL) M ht haA hL hpw hLayer (by omega : k < ℓ) R hl hd L (rem k) T7).mono
        (fun σ' ⟨R', hst, hl', hd', e'⟩ => ⟨by omega, R', (W k).reverse ++ L, Gs ++ [slotRound π ts k],
          Chain.snoc hc hst, ?_, ?_, hl', hd', e'⟩) le_rfl
      · rw [List.append_assoc, List.singleton_append, ← hGk, hG]
      · rw [List.reverse_append, List.reverse_reverse, List.append_assoc, ← hrem, hS])
    ℓ _ ⟨le_rfl, R₀, [], [], .nil _, by simp [Gk, slotRounds], by simp [rem, fwdScript, W]; rfl, hRl, hRd, rfl⟩
  refine hloop.mono (fun σ ⟨_, R, L, Gs, hc, hG, hS, hl, hd, e⟩ => ⟨R, ?_, hl, hd, ?_⟩) ?_
  · simp only [Gk, List.range_zero, List.reverse_nil, List.map_nil, List.append_nil] at hG
    rw [← hG]; exact hc
  · simp only [rem, List.range_zero, List.reverse_nil, List.flatMap_nil, List.append_nil] at hS e
    rw [e, ← hS, List.reverse_reverse]
  · rfl

set_option maxHeartbeats 4000000 in
theorem runs_oppRounds {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A)
    {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {p d w CL : ℕ} (hpw : p + 2 ≤ w)
    (hLayer : LayerCalls M ht r p d w ts ℓ K CL) (R₀ : List (Rec r))
    (hRl : R₀.length = ts.prod) (hRd : ∀ f ∈ R₀, DiskGrid p f.1 f.2) (T7 : WTape) :
    Runs (oppRounds (nL := nL) M ht haA)
      (dstate tL nL (rnamed w (array w R₀) ⟨[], oppScript p d r w (paperPerm hL) ts ℓ K⟩ T7) (rest r ts))
      (fun σ => ∃ R, Chain (Nat.log 2 ts.prod) p (oppSlotRounds (paperPerm hL) ts ℓ) R₀ R ∧
        R.length = ts.prod ∧ (∀ f ∈ R, DiskGrid p f.1 f.2) ∧
        σ = dstate tL nL (rnamed w (array w R) ⟨(oppScript p d r w (paperPerm hL) ts ℓ K).reverse, []⟩ T7)
          (rest r ts))
      (oppRoundsCost hL p d w CL) := by
  set n := Nat.log 2 ts.prod
  set π := paperPerm hL
  set W : ℕ → List (List Bool) := fun h => twistWords π r ts h ++ hadWords p d r w n ts ℓ K h
  set rem : ℕ → List (List Bool) := fun k => (List.range' (ℓ - k) k).flatMap W
  set Gk : ℕ → List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ) := fun k => (List.range' (ℓ - k) k).map (oppSlotRound π ts)
  have hrem : ∀ k, k + 1 ≤ ℓ → rem (k + 1) = W (ℓ - 1 - k) ++ rem k := fun k hk => by
    simp only [rem, List.range'_succ, List.flatMap_cons]
    rw [show ℓ - (k + 1) + 1 = ℓ - k by omega, show ℓ - (k + 1) = ℓ - 1 - k by omega]
  have hGk : ∀ k, k + 1 ≤ ℓ → Gk (k + 1) = oppSlotRound π ts (ℓ - 1 - k) :: Gk k := fun k hk => by
    simp only [Gk, List.range'_succ, List.map_cons]
    rw [show ℓ - (k + 1) + 1 = ℓ - k by omega, show ℓ - (k + 1) = ℓ - 1 - k by omega]
  let I : ℕ → (Fin (DB tL nL) → WTape) → Prop := fun k σ => k ≤ ℓ ∧ ∃ R L Gs,
    Chain n p Gs R₀ R ∧ Gs ++ Gk k = oppSlotRounds π ts ℓ ∧ L.reverse ++ rem k = oppScript p d r w π ts ℓ K ∧
      R.length = ts.prod ∧ (∀ f ∈ R, DiskGrid p f.1 f.2) ∧ σ = dstate tL nL (rnamed w (array w R) ⟨L, rem k⟩ T7) (rest r ts)
  have hloop := Runs.loop_sum (b := oppRoundCmd (nL := nL) M ht haA) (i := nm tL nL 6) I
    (fun k => twCost π r w ts (ℓ - 1 - k) + 1 + hadCost p d r w ts ℓ K CL (ℓ - 1 - k))
    (fun σ ⟨_, R, L, Gs, _, _, _, _, _, e⟩ => by rw [e, dstate_nm]; simp [rnamed, rem])
    (fun k σ ⟨hk, R, L, Gs, hc, hG, hS, hl, hd, e⟩ => by
      refine ⟨by rw [e, dstate_nm, hrem k hk]; simp [rnamed, W, twistWords], ?_⟩
      rw [e, hrem k hk]
      refine (runs_oppRoundCmd (nL := nL) M ht haA hL hpw hLayer (by omega : ℓ - 1 - k < ℓ) R hl hd L (rem k)
        T7).mono (fun σ' ⟨R', hst, hl', hd', e'⟩ => ⟨by omega, R', (W (ℓ - 1 - k)).reverse ++ L,
          Gs ++ [oppSlotRound π ts (ℓ - 1 - k)], Chain.snoc hc hst, ?_, ?_, hl', hd', e'⟩) le_rfl
      · rw [List.append_assoc, List.singleton_append, ← hGk k hk, hG]
      · rw [List.reverse_append, List.reverse_reverse, List.append_assoc, ← hrem k hk, hS])
    ℓ (dstate tL nL (rnamed w (array w R₀) ⟨[], rem ℓ⟩ T7) (rest r ts))
    ⟨le_rfl, R₀, [], [], .nil _, by simp [Gk, oppSlotRounds, List.range_eq_range'],
      by simp [rem, oppScript, W, List.range_eq_range']; rfl, hRl, hRd, rfl⟩
  have e0 : rem ℓ = oppScript p d r w π ts ℓ K := by simp [rem, oppScript, W, List.range_eq_range']; rfl
  rw [e0] at hloop
  refine hloop.mono (fun σ ⟨_, R, L, Gs, hc, hG, hS, hl, hd, e⟩ => ⟨R, ?_, hl, hd, ?_⟩) ?_
  · simp only [Gk, List.range'_zero, List.map_nil, List.append_nil] at hG
    rw [← hG]; exact hc
  · simp only [rem, List.range'_zero, List.flatMap_nil, List.append_nil] at hS e
    rw [e, ← hS, List.reverse_reverse]
  · rfl

end IntegerMultBounds.Schoenhage
