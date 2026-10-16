module

public import IntegerMultBounds.Schoenhage.DriverHad

/-! One slot's round on the drivers' bank (§6 task 6), between rest states: the named tapes as
`rnamed`, the twist block at rest. A forward round runs the Hadamard part, then the twist
(`runs_fwdRoundCmd`); an opposite round untwists, then runs the Hadamard part (`runs_oppRoundCmd`). Each
consumes the slot's script words and makes one `RoundStep` of the computed schedule. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct TwistDescriptors

variable {A tL nL : ℕ}

/-- A forward round: the Hadamard part, then the slot's twist. -/
noncomputable def fwdRoundCmd {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A) : Cmd A (DB tL nL) :=
  .seq (hadStep M ht haA) (twistStep A tL nL slotTwistClean)

/-- An opposite round: the slot's untwist, then the Hadamard part. -/
noncomputable def oppRoundCmd {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A) : Cmd A (DB tL nL) :=
  .seq (twistStep A tL nL slotUntwistClean) (hadStep M ht haA)

/-- The cost bound of slot `h`'s twist or untwist. -/
noncomputable def twCost {n : ℕ} (π : BitPerm n) (r w : ℕ) (ts : List ℕ) (h : ℕ) : ℕ :=
  cleanCost n r w ts.prod (slotTable π r ts (slotAxes ts h) h) +
    (tableWords (slotTable π r ts (slotAxes ts h) h)).length *
      (5 * clen (tableWords (slotTable π r ts (slotAxes ts h) h)) + 40) + 80 * (2 * r * w * ts.prod) + 400

/-- The twist block at rest for transforms over `ts`. -/
abbrev rest (r : ℕ) (ts : List ℕ) : Fin 29 → WTape := twRest r (Nat.log 2 ts.prod) (2 ^ Nat.log 2 ts.prod)

theorem length_le_clen : ∀ {L : List (List Bool)} {x : List Bool}, x ∈ L → x.length ≤ clen L
  | y :: L, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [clen_cons]; omega
    · have := length_le_clen hx
      simp only [clen_cons]
      omega

variable {r : ℕ} [NeZero r]

theorem hpos_slot {ts : List ℕ} (hts : PowAxes r ts) (h : ℕ) :
    ∀ i ∈ slotAxes ts h, axOff ts i + h < Nat.log 2 ts.prod := by
  intro i hi
  simp only [slotAxes, List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
  have := axOff_add_len_le hts hi.1
  omega

set_option maxHeartbeats 8000000 in
/-- The twist (`tc = slotTwistClean`) or untwist (`tc = slotUntwistClean`) of slot `h` between rest states. -/
theorem runs_twistPart {ts : List ℕ} (hts : PowAxes r ts) (π : BitPerm (Nat.log 2 ts.prod)) {w : ℕ}
    (hw : 1 ≤ w) (h : ℕ) (tc : Cmd 0 29) (g : List (Rec r) → List (Rec r))
    (htc : ∀ fs : List (Rec r), fs.length = 2 ^ Nat.log 2 ts.prod →
      Runs tc (twLoad (Nat.log 2 ts.prod) w fs (tableWords (slotTable π r ts (slotAxes ts h) h)))
        (· = Function.update (Function.update
          (twLoad (Nat.log 2 ts.prod) w fs (tableWords (slotTable π r ts (slotAxes ts h) h)))
          0 ⟨(cut w (array w fs)).reverse, []⟩) 1 ⟨(cut w (array w (g fs))).reverse, []⟩)
        (cleanCost (Nat.log 2 ts.prod) r w fs.length (slotTable π r ts (slotAxes ts h) h)))
    (hg : ∀ fs : List (Rec r), (g fs).length = fs.length)
    (zs : List (Rec r)) (hzl : zs.length = ts.prod) (Lr Rs : List (List Bool)) (T7 : WTape) :
    Runs (twistStep A tL nL tc)
      (dstate tL nL (rnamed w (array w zs) ⟨Lr, twistWords π r ts h ++ Rs⟩ T7)
        (rest r ts))
      (· = dstate tL nL (rnamed w (array w (g zs)) ⟨(twistWords π r ts h).reverse ++ Lr, Rs⟩ T7)
        (rest r ts))
      (twCost π r w ts h) := by
  set tab := tableWords (slotTable π r ts (slotAxes ts h) h)
  set v := rnamed w (array w zs) ⟨Lr, twistWords π r ts h ++ Rs⟩ T7
  have hpow := powAxes_prod_pow hts
  have s := runs_twistStep (A := A) (tL := tL) (nL := nL) tc v (twRest r (Nat.log 2 ts.prod) (2 ^ Nat.log 2 ts.prod))
    (Lr := Lr) (R := Rs) (tab := tab) (nT := tab.length) (Wt := clen tab) (fs := zs) (gs := g zs) hw
    (by simp (config := {decide := true}) [v, rnamed, twistWords, tab]) rfl (fun x hx => length_le_clen hx)
    (by simp [v, rnamed]) (by simp (config := {decide := true}) [v, rnamed])
    (by simp (config := {decide := true}) [v, rnamed]) (by simp (config := {decide := true}) [v, rnamed])
    (by simp (config := {decide := true}) [v, rnamed])
    (by simp (config := {decide := true}) [twRest]) (by simp (config := {decide := true}) [twRest])
    (by simp (config := {decide := true}) [twRest]) (htc zs (by rw [hzl, ← hpow]))
  refine s.mono (fun σ e => ?_) ?_
  · rw [e]
    congr 1
    funext i
    fin_cases i <;> simp (config := {decide := true}) [v, rnamed, twistWords, tab]
  · have h1 : (array w (g zs)).length = 2 * r * w * ts.prod := by rw [length_array, hg, hzl]
    have h2 : (array w zs).length = 2 * r * w * ts.prod := by rw [length_array, hzl]
    simp only [twCost, h1, h2, hzl, tab]
    omega

/-- Slot `h`'s forward round on records: the Hadamard output, twisted. -/
theorem fwd_step {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (p : ℕ) {h : ℕ} (hh : h < ℓ)
    (R : List (Rec r)) (hRl : R.length = ts.prod) :
    RoundStep (Nat.log 2 ts.prod) p (slotRound (paperPerm hL) ts h) R
      (TwistRound.twistRecs (slotExp (paperPerm hL) r ts (slotAxes ts h) h) (hadOut p ts ℓ K h R)) := by
  have hK : 0 < K := hL.2.2.1
  unfold hadOut
  split_ifs with h1 h2
  · exact step_prefix hL p h1 R hRl
  · have hdm := Nat.div_add_mod (h - (ℓ - 1) % K) K
    have hlm := Nat.div_add_mod (ℓ - 1) K
    have e : h = (ℓ - 1) % K + chunkOf ℓ K h * K + rhoOf ℓ K h := by
      unfold chunkOf rhoOf; rw [Nat.mul_comm (_ / K) K]; omega
    have hc : chunkOf ℓ K h < (ℓ - 1) / K := by
      unfold chunkOf; rw [Nat.div_lt_iff_lt_mul hK]
      have := Nat.mul_comm K ((ℓ - 1) / K); omega
    have := step_chunk hL p hc (ρ := rhoOf ℓ K h) (Nat.mod_lt _ hK) R
    rw [← e] at this
    exact this
  · obtain rfl : h = ℓ - 1 := by omega
    exact step_top hL p R hRl

/-- Slot `h`'s opposite round on records: the Hadamard output of the untwisted records. -/
theorem opp_step {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (p : ℕ) {h : ℕ} (hh : h < ℓ)
    (R : List (Rec r)) (hRl : R.length = ts.prod) :
    RoundStep (Nat.log 2 ts.prod) p (oppSlotRound (paperPerm hL) ts h) R
      (hadOut p ts ℓ K h (TwistRound.untwistRecs (slotExp (paperPerm hL) r ts (slotAxes ts h) h) R)) := by
  have hK : 0 < K := hL.2.2.1
  unfold hadOut
  split_ifs with h1 h2
  · exact step_opp_prefix hL p h1 R hRl
  · have hdm := Nat.div_add_mod (h - (ℓ - 1) % K) K
    have hlm := Nat.div_add_mod (ℓ - 1) K
    have e : h = (ℓ - 1) % K + chunkOf ℓ K h * K + rhoOf ℓ K h := by
      unfold chunkOf rhoOf; rw [Nat.mul_comm (_ / K) K]; omega
    have hc : chunkOf ℓ K h < (ℓ - 1) / K := by
      unfold chunkOf; rw [Nat.div_lt_iff_lt_mul hK]
      have := Nat.mul_comm K ((ℓ - 1) / K); omega
    have := step_opp_chunk hL p hc (ρ := rhoOf ℓ K h) (Nat.mod_lt _ hK) R
    rw [← e] at this
    exact this
  · obtain rfl : h = ℓ - 1 := by omega
    exact step_opp_top hL p R hRl

theorem runs_fwdRoundCmd {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A)
    {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {p d w CL : ℕ} (hpw : p + 2 ≤ w)
    (hLayer : LayerCalls M ht r p d w ts ℓ K CL) {h : ℕ} (hh : h < ℓ) (R : List (Rec r))
    (hRl : R.length = ts.prod) (hRd : ∀ f ∈ R, DiskGrid p f.1 f.2) (Lr Rs : List (List Bool)) (T7 : WTape) :
    Runs (fwdRoundCmd (nL := nL) M ht haA)
      (dstate tL nL (rnamed w (array w R) ⟨Lr, (hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h ++
        twistWords (paperPerm hL) r ts h) ++ Rs⟩ T7) (rest r ts))
      (fun σ => ∃ R', RoundStep (Nat.log 2 ts.prod) p (slotRound (paperPerm hL) ts h) R R' ∧
        R'.length = ts.prod ∧ (∀ f ∈ R', DiskGrid p f.1 f.2) ∧
        σ = dstate tL nL (rnamed w (array w R') ⟨(hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h ++
          twistWords (paperPerm hL) r ts h).reverse ++ Lr, Rs⟩ T7) (rest r ts))
      (hadCost p d r w ts ℓ K CL h + 1 + twCost (paperPerm hL) r w ts h) := by
  have hpow := powAxes_prod_pow hL.1
  have s1 := runs_hadStep (nL := nL) M ht haA hL hpw hLayer hh R hRl hRd Lr
    (twistWords (paperPerm hL) r ts h ++ Rs) T7 (rest r ts)
  rw [← List.append_assoc] at s1
  have hO := length_hadOut p hL h R hRl
  have s2 := runs_twistPart (A := A) (tL := tL) (nL := nL) hL.1 (paperPerm hL) (by omega : 1 ≤ w) h slotTwistClean
    (TwistRound.twistRecs (slotExp (paperPerm hL) r ts (slotAxes ts h) h))
    (fun fs hfs => runs_twistRest (paperPerm hL) ts h (hpos_slot hL.1 h) w (by omega) fs hfs)
    (fun fs => by simp [TwistRound.twistRecs]) (hadOut p ts ℓ K h R) hO
    ((hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h).reverse ++ Lr) Rs T7
  refine (Runs.then s1 s2).mono (fun σ e => ?_) le_rfl
  have hst := fwd_step hL p hh R hRl
  have hl' : (TwistRound.twistRecs (slotExp (paperPerm hL) r ts (slotAxes ts h) h) (hadOut p ts ℓ K h R)).length =
      ts.prod := by simp [TwistRound.twistRecs, hO]
  refine ⟨_, hst, hl', disk_of_step (slotRound_contracts hL.1 hpow (paperPerm hL) h).1 (by rw [hl']; exact hpow) hRd hst,
    ?_⟩
  rw [e, List.reverse_append, List.append_assoc]

theorem runs_oppRoundCmd {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A)
    {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {p d w CL : ℕ} (hpw : p + 2 ≤ w)
    (hLayer : LayerCalls M ht r p d w ts ℓ K CL) {h : ℕ} (hh : h < ℓ) (R : List (Rec r))
    (hRl : R.length = ts.prod) (hRd : ∀ f ∈ R, DiskGrid p f.1 f.2) (Lr Rs : List (List Bool)) (T7 : WTape) :
    Runs (oppRoundCmd (nL := nL) M ht haA)
      (dstate tL nL (rnamed w (array w R) ⟨Lr, (twistWords (paperPerm hL) r ts h ++
        hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h) ++ Rs⟩ T7) (rest r ts))
      (fun σ => ∃ R', RoundStep (Nat.log 2 ts.prod) p (oppSlotRound (paperPerm hL) ts h) R R' ∧
        R'.length = ts.prod ∧ (∀ f ∈ R', DiskGrid p f.1 f.2) ∧
        σ = dstate tL nL (rnamed w (array w R') ⟨(twistWords (paperPerm hL) r ts h ++
          hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h).reverse ++ Lr, Rs⟩ T7) (rest r ts))
      (twCost (paperPerm hL) r w ts h + 1 + hadCost p d r w ts ℓ K CL h) := by
  have hpow := powAxes_prod_pow hL.1
  set U := TwistRound.untwistRecs (slotExp (paperPerm hL) r ts (slotAxes ts h) h) R
  have s1 := runs_twistPart (A := A) (tL := tL) (nL := nL) hL.1 (paperPerm hL) (by omega : 1 ≤ w) h
    slotUntwistClean (TwistRound.untwistRecs (slotExp (paperPerm hL) r ts (slotAxes ts h) h))
    (fun fs hfs => runs_untwistRest (paperPerm hL) ts h (hpos_slot hL.1 h) w (by omega) fs hfs)
    (fun fs => by simp [TwistRound.untwistRecs]) R hRl Lr
    (hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h ++ Rs) T7
  rw [← List.append_assoc] at s1
  have hUl : U.length = ts.prod := by simp [U, TwistRound.untwistRecs, hRl]
  have s2 := runs_hadStep (nL := nL) M ht haA hL hpw hLayer hh U hUl (disk_untwistRecs _ hRd)
    ((twistWords (paperPerm hL) r ts h).reverse ++ Lr) Rs T7 (rest r ts)
  refine (Runs.then s1 s2).mono (fun σ e => ?_) le_rfl
  have hst := opp_step hL p hh R hRl
  have hl' := length_hadOut p hL h U hUl
  refine ⟨_, hst, hl', disk_of_step (oppSlotRound_contracts hL.1 hpow (paperPerm hL) h).1 (by rw [hl']; exact hpow) hRd hst,
    ?_⟩
  rw [e, List.reverse_append, List.append_assoc]

end IntegerMultBounds.Schoenhage
