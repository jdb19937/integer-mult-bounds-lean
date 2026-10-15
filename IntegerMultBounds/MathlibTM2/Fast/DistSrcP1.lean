module

public import IntegerMultBounds.MathlibTM2.Fast.DistSrcCode
public import IntegerMultBounds.MathlibTM2.Fast.Dist

/-!
# Phase 1 of the converter: the records and the axis lists

`dsP1 rg g`: `Wt` into variable `38`, `d` ticks onto the loop counter `o .uD`, the axis loop
(`dsAxes`) with the pushes `dsL₁`: the `Ã` record onto `a (.c .out)`, the `B̃₀` record onto
`b (.inl .bo)`, the reversed chirp blocks onto the spares `o .xT`, `o .xS`, the CRT entries of
`aᵢ = log₂ tᵢ` and `sᵢ` onto `c .wT`, `c .sT`; the loop variables cleared; the chirp blocks moved
onto `x .tSp`, `x .sSp`; the records copied twice more (`preRecsA` three times, for the runs
`srcP`, `srcP`, `oppP'`).

`ds_P1`: the contract (`∃` final family file with the stated values, every other register of the
family as it started).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA
  IntegerMultBounds.MathlibTM2.Fast.ChirpSt

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section P1

variable {T Q A t₀ : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {g : DsY t₀ → Fin T}

/-- The record register of `Ã`. -/
abbrev dsyA : DsY t₀ := .s (.a (.c .out))
/-- The record register of `B̃₀`. -/
abbrev dsyB : DsY t₀ := .s (.b (.inl .bo))
/-- The CRT width list. -/
abbrev dsyWT : DsY t₀ := .s (.c .wT)
/-- The CRT length list. -/
abbrev dsySTc : DsY t₀ := .s (.c .sT)

/-- The pushes of phase 1. -/
def dsL₁ (g : DsY t₀ → Fin T) : List (Fin T × Fin pmNV × DsMode) :=
  dsL₀ (g dsyA) (g dsyB) (g (.o .xT)) (g (.o .xS)) ++ [(g dsyWT, 34, .ent), (g dsySTc, 35, .ent)]

/-- Phase 1. -/
def dsP1 (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) : Pr P T Q A U :=
  .seq (dsLoad rg (g (.o .uW)) 38) <| .seq (dsUn rg 3 (g (.o .uD))) <|
  .seq (tblCompile rg dsInitC) <| .seq (dsAxes rg (g (.o .uD)) (g (.o .tm)) (dsL₁ g)) <|
  .seq (tblCompile rg dsEndC) <| .seq (tblCompile rg dsZ38) <|
  .seq (moveR (g (.o .xT)) (g (.s (.x .tSp))) id) <| .seq (moveR (g (.o .xS)) (g (.s (.x .sSp))) id) <|
  .seq (bcopy (g dsyA) (g (.o .tR)) (rg (.z 0)) (rg (.z 1))) <|
  .seq (bcopy (g (.o .tR)) (g dsyA) (rg (.z 0)) (rg (.z 1))) <|
  .seq (bcopy (g (.o .tR)) (g dsyA) (rg (.z 0)) (rg (.z 1))) <| .seq (bclear (g (.o .tR))) <|
  .seq (bcopy (g dsyB) (g (.o .tR)) (rg (.z 0)) (rg (.z 1))) <|
  .seq (bcopy (g (.o .tR)) (g dsyB) (rg (.z 0)) (rg (.z 1))) <|
  .seq (bcopy (g (.o .tR)) (g dsyB) (rg (.z 0)) (rg (.z 1))) (bclear (g (.o .tR)))

/-- The CRT entries of the values `f j`, `j < m`, axis `m - 1` first. -/
theorem ds_acc_ent (n Wt : ℕ) (L : List (Fin T × Fin pmNV × DsMode)) (o : Fin T) (x : Fin pmNV)
    (f : Fin (d n) → ℕ)
    (hL : ∀ i, dsOut (A := A) (dsAV n Wt i) L o = bitSymbol false :: dsFld (dsAV n Wt i x))
    (hf : ∀ i : Fin (d n), dsAV n Wt i x = f i) :
    ∀ j, j ≤ d n → dsAcc (A := A) n Wt L j o = crtEnts ((crtRevAx j).map f)
  | 0, _ => by simp [dsAcc]
  | j + 1, hj => by
    rw [dsAcc_succ, ds_acc_ent n Wt L o x f hL hf j (by omega),
      crtRevAx_succ (show j < d n by omega), List.map_cons, crtEnts_cons, hL,
      hf ⟨j, by omega⟩]
    rfl

/-- The variables pushed in one iteration of phase 1. -/
def dsVarsL₁ : List (Fin pmNV) := dsVarsL ++ [34, 35]

/-- The step bound of the axis loop of phase 1. -/
def dsLoopCost₁ (n Wt : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d n), (28 * tblC (pmW n) (pmW n) +
    ((dsVarsL₁.map fun x => pmW n * (4 * dsAV n Wt i x + 11) + 2 * dsAV n Wt i x + 8).sum + 1)
      + 3) + 2 * d n + 4

theorem dsAxesCost_eq₁ (n Wt : ℕ) (g : DsY t₀ → Fin T) :
    dsAxesCost n Wt (dsL₁ g) = dsLoopCost₁ n Wt := by
  unfold dsAxesCost dsLoopCost₁ dsAxCost
  have e : (dsL₁ g).map (·.2.1) = dsVarsL₁ := by
    rw [dsL₁, List.map_append, dsL₀_vars]; rfl
  simp only [dsPushCost_eq, e]

/-- The length of the `Ã` records. -/
def dsRecLenA (n Wt : ℕ) : ℕ := ∑ i ∈ Finset.range (d n), ((dsFA.map (dsAV n Wt i)).sum + 11)

/-- The length of the `B̃₀` records. -/
def dsRecLenB (n Wt : ℕ) : ℕ := ∑ i ∈ Finset.range (d n), ((dsFB.map (dsAV n Wt i)).sum + 10)

theorem ds_preRec_length (l : List ℕ) : (preRec (A := A) l).length = l.sum + l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [preRec, List.flatMap_cons, List.length_append, preFld, List.length_replicate,
      List.length_singleton, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih]; simp; ring

theorem ds_flatMap_rev_length (m : ℕ) (f : ℕ → List (Fin (A + 4))) :
    ((List.range m).reverse.flatMap f).length = ∑ i ∈ Finset.range m, (f i).length := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.flatMap_cons, List.length_append, ih, Finset.sum_range_succ, Nat.add_comm]

/-- The step bound of phase 1. -/
def dsP1Cost (n Wt : ℕ) : ℕ :=
  (2 * pmW n + 2 + (Wt * (4 * pmW n + 10) + 4 * pmW n + 8)) +
    (pmW n * (4 * d n + 11) + 2 * d n + 6) + 4 * tblC (pmW n) (pmW n) + dsLoopCost₁ n Wt +
    (2 * ((List.ofFn (t n)).sum + d n) + 2) + (2 * ((List.ofFn (s n)).sum + d n) + 2) +
    (3 * (6 * dsRecLenA n Wt + 6) + (2 * dsRecLenA n Wt + 2)) +
    (3 * (6 * dsRecLenB n Wt + 6) + (2 * dsRecLenB n Wt + 2))

/-- The registers of the family that phase 1 needs empty. -/
def dsP1Pre : List (DsY t₀) :=
  [.o .uD, .o .tm, .o .xT, .o .xS, .o .tR, dsyA, dsyB, dsyWT, dsySTc, .s (.x .tSp), .s (.x .sSp)]

/-- The registers of the family that phase 1 writes. -/
def dsP1Out : List (DsY t₀) :=
  [.o .uD, dsyA, dsyB, dsyWT, dsySTc, .s (.x .tSp), .s (.x .sSp)]

/-- The targets of the pushes of phase 1. -/
theorem dsL₁_targets (g : DsY t₀ → Fin T) :
    ∀ e ∈ dsL₁ g, e.1 = g dsyA ∨ e.1 = g dsyB ∨ e.1 = g (.o .xT) ∨ e.1 = g (.o .xS) ∨
      e.1 = g dsyWT ∨ e.1 = g dsySTc := by
  intro e he
  simp [dsL₁, dsL₀, dsRecPush] at he
  rcases he with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ | rfl | rfl | rfl | rfl <;> simp

variable (h : DsLay rg g)
include h

theorem dsOut_L₁ (val : Fin pmNV → ℕ) (y : DsY t₀) :
    dsOut (A := A) val (dsL₁ g) (g y) =
      (if y = dsySTc then bitSymbol false :: dsFld (val 35) else []) ++
      (if y = dsyWT then bitSymbol false :: dsFld (val 34) else []) ++
      dsOut val (dsL₀ (g dsyA) (g dsyB) (g (.o .xT)) (g (.o .xS))) (g y) := by
  rw [dsL₁, dsOut_append]
  simp only [dsOut_cons, dsOut_nil, List.nil_append, h.ig.eq_iff]
  by_cases h1 : y = dsySTc <;> by_cases h2 : y = dsyWT <;> simp_all [dsBlk, eq_comm]

theorem ds_acc₁ (n Wt : ℕ) (hn : 2 ≤ n) (hd0 : 0 < d n) :
    dsAcc (A := A) n Wt (dsL₁ g) (d n) (g dsyA) = preRecsA n Wt hd0 0 ∧
    dsAcc (A := A) n Wt (dsL₁ g) (d n) (g dsyB) = preRecsB n Wt hd0 0 ∧
    dsAcc (A := A) n Wt (dsL₁ g) (d n) (g (.o .xT)) = (ldcBlocks (List.ofFn (t n))).reverse ∧
    dsAcc (A := A) n Wt (dsL₁ g) (d n) (g (.o .xS)) = (ldcBlocks (List.ofFn (s n))).reverse ∧
    dsAcc (A := A) n Wt (dsL₁ g) (d n) (g dsyWT) = crtEnts ((crtRevAx (d n)).map (srcAx n)) ∧
    dsAcc (A := A) n Wt (dsL₁ g) (d n) (g dsySTc) = crtEnts ((crtRevAx (d n)).map (s n)) := by
  have ne : ∀ {x y : DsY t₀}, x ≠ y → g x ≠ g y := fun hxy => h.ig.ne hxy
  have eA : ∀ k, dsAcc (A := A) n Wt (dsL₁ g) k (g dsyA) =
      dsAcc n Wt (dsL₀ (g dsyA) (g dsyB) (g (.o .xT)) (g (.o .xS))) k (g dsyA) := by
    intro k; unfold dsAcc; simp only [dsOut_L₁ h]; simp
  have eB : ∀ k, dsAcc (A := A) n Wt (dsL₁ g) k (g dsyB) =
      dsAcc n Wt (dsL₀ (g dsyA) (g dsyB) (g (.o .xT)) (g (.o .xS))) k (g dsyB) := by
    intro k; unfold dsAcc; simp only [dsOut_L₁ h]; simp
  have eT : ∀ k, dsAcc (A := A) n Wt (dsL₁ g) k (g (.o .xT)) =
      dsAcc n Wt (dsL₀ (g dsyA) (g dsyB) (g (.o .xT)) (g (.o .xS))) k (g (.o .xT)) := by
    intro k; unfold dsAcc; simp only [dsOut_L₁ h]; simp
  have eS : ∀ k, dsAcc (A := A) n Wt (dsL₁ g) k (g (.o .xS)) =
      dsAcc n Wt (dsL₀ (g dsyA) (g dsyB) (g (.o .xT)) (g (.o .xS))) k (g (.o .xS)) := by
    intro k; unfold dsAcc; simp only [dsOut_L₁ h]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eA]; exact ds_acc_A (ne (fun e => by cases e)) (ne (fun e => by cases e)) (ne (fun e => by cases e)) hn hd0 Wt
  · rw [eB]; exact ds_acc_B (ne (fun e => by cases e)) (ne (fun e => by cases e)) (ne (fun e => by cases e)) hn hd0 Wt
  · rw [eT]; exact ds_acc_T (ne (fun e => by cases e)) (ne (fun e => by cases e)) (ne (fun e => by cases e)) Wt
  · rw [eS]; exact ds_acc_S (ne (fun e => by cases e)) (ne (fun e => by cases e)) (ne (fun e => by cases e)) Wt
  · refine ds_acc_ent n Wt (dsL₁ g) (g dsyWT) 34 (srcAx n) (fun i => ?_) (fun i => ?_) (d n) le_rfl
    · rw [dsOut_L₁ h, dsOut_none _ _ (by
        intro e he; simp [dsL₀, dsRecPush] at he
        rcases he with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ | rfl | rfl <;> exact ne (fun e => by cases e))]
      simp
    · simp [dsAV, srcAx, ds_log_t, pmNV]
  · refine ds_acc_ent n Wt (dsL₁ g) (g dsySTc) 35 (s n) (fun i => ?_) (fun i => ?_) (d n) le_rfl
    · rw [dsOut_L₁ h, dsOut_none _ _ (by
        intro e he; simp [dsL₀, dsRecPush] at he
        rcases he with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ | rfl | rfl <;> exact ne (fun e => by cases e))]
      simp
    · simp [dsAV, dsS_eq, pmNV]

/-- The axis loop in the family form. -/
theorem dsF_axes (R : Regs T A) {n Wt : ℕ} (hn : 2 ≤ n) (hWt : Wt < 2 ^ pmW n)
    (wl : List (Fin (A + 4))) (hwl : wl.length = pmW n) (X : DsY t₀ → List (Fin (A + 4)))
    (hu : (X (.o .uD)).length = d n) (ht : X (.o .tm) = []) :
    dsRuns body (dsAxes rg (g (.o .uD)) (g (.o .tm)) (dsL₁ g))
      (dsF rg g R X (pmW n) wl (dsLV n Wt 0))
      (dsF rg g R (fun y => dsAcc n Wt (dsL₁ g) (d n) (g y) ++ X y) (pmW n) wl
        (dsLV n Wt (d n))) (dsLoopCost₁ n Wt) := by
  have ne : ∀ {x y : DsY t₀}, x ≠ y → g x ≠ g y := fun hxy => h.ig.ne hxy
  have hT := dsL₁_targets g
  have hL1 : ∀ e ∈ dsL₁ g, ∀ r, rg r ≠ e.1 := by
    intro e he r
    rcases hT e he with h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> exact h.disj _ _
  have hL2 : ∀ e ∈ dsL₁ g, e.1 ≠ g (.o .uD) := by
    intro e he
    rcases hT e he with h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> exact ne (fun e => by cases e)
  have hL3 : ∀ e ∈ dsL₁ g, e.1 ≠ g (.o .tm) := by
    intro e he
    rcases hT e he with h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> exact ne (fun e => by cases e)
  have s := ds_axes (body := body) h.irg (fun r => h.disj r (.o .uD)) (fun r => h.disj r (.o .tm))
    (ne (fun e => by cases e)) hn hWt wl hwl (dsL₁ g) hL1 hL2 hL3
    (dsOv g R X) (by rw [dsOv_rg h.ig, hu]) (by rw [dsOv_rg h.ig, ht])
  rw [dsAxesCost_eq₁] at s
  refine s.congr ?_
  unfold dsPsi dsF
  congr 1
  refine dsOv_eq_of h.ig (fun y => by rw [dsOv_rg h.ig]) (fun k hk => ?_)
  have hk' : ∀ e ∈ dsL₁ g, e.1 ≠ k := by
    intro e he
    rcases hT e he with h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> exact hk _
  rw [dsOv_off _ _ hk, dsAcc_none n Wt _ hk', List.nil_append]

set_option maxHeartbeats 1000000 in
/-- **Phase 1.** -/
theorem ds_P1 (R : Regs T A) {n Wt : ℕ} (hn : 2 ≤ n) (hd0 : 0 < d n) (hWt : Wt < 2 ^ pmW n)
    (wl : List (Fin (A + 4))) (hwl : wl.length = pmW n) (X : DsY t₀ → List (Fin (A + 4)))
    (hW : (X (.o .uW)).length = Wt) (h0 : ∀ y ∈ (dsP1Pre : List (DsY t₀)), X y = []) :
    ∃ X' : DsY t₀ → List (Fin (A + 4)),
      (∀ y, y ∉ (dsP1Out : List (DsY t₀)) → X' y = X y) ∧
      X' (.o .uD) = List.replicate (d n) tick ∧
      X' dsyA = preRecsA n Wt hd0 0 ++ (preRecsA n Wt hd0 0 ++ preRecsA n Wt hd0 0) ∧
      X' dsyB = preRecsB n Wt hd0 0 ++ (preRecsB n Wt hd0 0 ++ preRecsB n Wt hd0 0) ∧
      X' (.s (.x .tSp)) = ldcBlocks (List.ofFn (t n)) ∧
      X' (.s (.x .sSp)) = ldcBlocks (List.ofFn (s n)) ∧
      X' dsyWT = crtEnts ((crtRevAx (d n)).map (srcAx n)) ∧
      X' dsySTc = crtEnts ((crtRevAx (d n)).map (s n)) ∧
      dsRuns body (dsP1 rg g) (dsF rg g R X (pmW n) wl (pmVals n))
        (dsF rg g R X' (pmW n) wl (pmVals n)) (dsP1Cost n Wt) := by
  have hpre : ∀ y ∈ (dsP1Pre : List (DsY t₀)), X y = [] := h0
  simp only [dsP1Pre, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h0
  obtain ⟨eD, eTm, eXT, eXS, eTR, eA, eB, eWT, eST, eTSp, eSSp⟩ := h0
  obtain ⟨aA, aB, aT, aS, aW, aSt⟩ := ds_acc₁ (A := A) h n Wt hn hd0
  -- `Wt`
  have s1 := dsF_load (body := body) h R wl X (pmVals n) (.o .uW) 38 hwl
  rw [hW, ← dsV1_pm, dsV1_upd38] at s1
  -- `d` ticks
  have hσ0 := dsV1_lt hn hWt (Nat.two_pow_pos _)
  have s2 := dsF_un (body := body) h R wl X (dsV1 n Wt 0) 3 (.o .uD) (hσ0 3) eD
  have hd3 : dsV1 n Wt 0 3 = d n := by simp [dsV1, pmNV, pmVal]
  rw [hd3, List.append_nil] at s2
  set X₁ := Function.update X (.o .uD) (List.replicate (d n) tick) with hX₁
  -- the loop
  have s3 := dsF_code (body := body) h R wl X₁ (dsV1 n Wt 0) (dsInitC_do (n := n) (Wt := Wt))
    hσ0 hwl
  have s4 := dsF_axes (body := body) h R hn hWt wl hwl X₁ (by simp [hX₁]) (by simp [hX₁, eTm])
  set X₂ := fun y => dsAcc n Wt (dsL₁ g) (d n) (g y) ++ X₁ y with hX₂
  have s5 := dsF_code (body := body) h R wl X₂ (dsLV n Wt (d n)) (dsEndC_do (n := n) (Wt := Wt))
    (dsLV_lt hn hWt le_rfl) hwl
  have s6 := dsF_code (body := body) h R wl X₂ (dsV1 n Wt 0) (dsZ38_do (n := n) Wt) hσ0 hwl
  -- the chirp blocks
  have x2T : X₂ (.o .xT) = (ldcBlocks (List.ofFn (t n))).reverse := by
    simp [hX₂, aT, hX₁, eXT]
  have x2S : X₂ (.o .xS) = (ldcBlocks (List.ofFn (s n))).reverse := by
    simp [hX₂, aS, hX₁, eXS]
  have x2TS : X₂ (.s (.x .tSp)) = [] := by
    simp only [hX₂, hX₁]
    rw [dsAcc_none n Wt _ (by
      intro e he; rcases dsL₁_targets g e he with h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;>
        exact h.ig.ne (fun e => by cases e))]
    simp [eTSp]
  have hoff : ∀ y : DsY t₀, y ≠ dsyA → y ≠ dsyB → y ≠ .o .xT → y ≠ .o .xS → y ≠ dsyWT →
      y ≠ dsySTc → X₂ y = X₁ y := by
    intro y h1 h2 h3 h4 h5 h6
    simp only [hX₂]
    rw [dsAcc_none n Wt _ (by
      intro e he; rcases dsL₁_targets g e he with h' | h' | h' | h' | h' | h' <;> rw [h'] <;>
        exact h.ig.ne (Ne.symm ‹_›)), List.nil_append]
  have x2SS : X₂ (.s (.x .sSp)) = [] := by
    rw [hoff _ (fun e => by cases e) (fun e => by cases e) (fun e => by cases e)
      (fun e => by cases e) (fun e => by cases e) (fun e => by cases e)]
    simp [hX₁, eSSp]
  have x2tR : X₂ (.o .tR) = [] := by
    rw [hoff _ (fun e => by cases e) (fun e => by cases e) (fun e => by cases e)
      (fun e => by cases e) (fun e => by cases e) (fun e => by cases e)]
    simp [hX₁, eTR]
  have x2A : X₂ dsyA = preRecsA n Wt hd0 0 := by simp [hX₂, aA, hX₁, eA]
  have x2B : X₂ dsyB = preRecsB n Wt hd0 0 := by simp [hX₂, aB, hX₁, eB]
  have x2W : X₂ dsyWT = crtEnts ((crtRevAx (d n)).map (srcAx n)) := by simp [hX₂, aW, hX₁, eWT]
  have x2St : X₂ dsySTc = crtEnts ((crtRevAx (d n)).map (s n)) := by simp [hX₂, aSt, hX₁, eST]
  have hpm := ds_pmVals_lt (n := n) hn
  have s7 := dsF_moveR (body := body) (W := pmW n) h R wl X₂ (pmVals n) (.o .xT) (.s (.x .tSp))
    (fun e => by cases e) x2T x2TS
  rw [List.reverse_reverse, List.append_nil] at s7
  set X₃ := Function.update (Function.update X₂ (.o .xT) []) (.s (.x .tSp))
    (ldcBlocks (List.ofFn (t n))) with hX₃
  have s8 := dsF_moveR (body := body) (W := pmW n) h R wl X₃ (pmVals n) (.o .xS) (.s (.x .sSp))
    (fun e => by cases e) (l₁ := (ldcBlocks (List.ofFn (s n))).reverse) (l₂ := [])
    (by simp [hX₃, x2S]) (by simp [hX₃, x2SS])
  rw [List.reverse_reverse, List.append_nil] at s8
  set X₄ := Function.update (Function.update X₃ (.o .xS) []) (.s (.x .sSp))
    (ldcBlocks (List.ofFn (s n))) with hX₄
  -- the records
  have s9 := dsF_bcopy (body := body) (W := pmW n) h R wl X₄ (pmVals n) dsyA (.o .tR) (fun e => by cases e)
    (l₁ := preRecsA n Wt hd0 0) (l₂ := []) (by simp [hX₄, hX₃, x2A]) (by simp [hX₄, hX₃, x2tR])
  rw [List.append_nil] at s9
  set X₅ := Function.update X₄ (.o .tR) (preRecsA n Wt hd0 0) with hX₅
  have s10 := dsF_bcopy (body := body) (W := pmW n) h R wl X₅ (pmVals n) (.o .tR) dsyA (fun e => by cases e)
    (l₁ := preRecsA n Wt hd0 0) (l₂ := preRecsA n Wt hd0 0) (by simp [hX₅]) (by simp [hX₅, hX₄, hX₃, x2A])
  set X₆ := Function.update X₅ dsyA (preRecsA n Wt hd0 0 ++ preRecsA n Wt hd0 0) with hX₆
  have s11 := dsF_bcopy (body := body) (W := pmW n) h R wl X₆ (pmVals n) (.o .tR) dsyA (fun e => by cases e)
    (l₁ := preRecsA n Wt hd0 0) (l₂ := preRecsA n Wt hd0 0 ++ preRecsA n Wt hd0 0) (by simp [hX₆, hX₅]) (by simp [hX₆])
  set X₇ := Function.update X₆ dsyA (preRecsA n Wt hd0 0 ++ (preRecsA n Wt hd0 0 ++
    preRecsA n Wt hd0 0)) with hX₇
  have s12 := dsF_bclear (body := body) (W := pmW n) h R wl X₇ (pmVals n) (.o .tR) (c := (preRecsA (A := A) n Wt hd0 0).length)
    (by simp [hX₇, hX₆, hX₅])
  set X₈ := Function.update X₇ (.o .tR) [] with hX₈
  have s13 := dsF_bcopy (body := body) (W := pmW n) h R wl X₈ (pmVals n) dsyB (.o .tR) (fun e => by cases e)
    (l₁ := preRecsB n Wt hd0 0) (l₂ := []) (by simp [hX₈, hX₇, hX₆, hX₅, hX₄, hX₃, x2B]) (by simp [hX₈])
  rw [List.append_nil] at s13
  set X₉ := Function.update X₈ (.o .tR) (preRecsB n Wt hd0 0) with hX₉
  have s14 := dsF_bcopy (body := body) (W := pmW n) h R wl X₉ (pmVals n) (.o .tR) dsyB (fun e => by cases e)
    (l₁ := preRecsB n Wt hd0 0) (l₂ := preRecsB n Wt hd0 0) (by simp [hX₉]) (by simp [hX₉, hX₈, hX₇, hX₆, hX₅, hX₄, hX₃, x2B])
  set X₁₀ := Function.update X₉ dsyB (preRecsB n Wt hd0 0 ++ preRecsB n Wt hd0 0) with hX₁₀
  have s15 := dsF_bcopy (body := body) (W := pmW n) h R wl X₁₀ (pmVals n) (.o .tR) dsyB (fun e => by cases e)
    (l₁ := preRecsB n Wt hd0 0) (l₂ := preRecsB n Wt hd0 0 ++ preRecsB n Wt hd0 0) (by simp [hX₁₀, hX₉]) (by simp [hX₁₀])
  set X₁₁ := Function.update X₁₀ dsyB (preRecsB n Wt hd0 0 ++ (preRecsB n Wt hd0 0 ++
    preRecsB n Wt hd0 0)) with hX₁₁
  have s16 := dsF_bclear (body := body) (W := pmW n) h R wl X₁₁ (pmVals n) (.o .tR)
    (c := (preRecsB (A := A) n Wt hd0 0).length) (by simp [hX₁₁, hX₁₀, hX₉])
  set X₁₂ := Function.update X₁₁ (.o .tR) [] with hX₁₂
  have lA : (preRecsA (A := A) n Wt hd0 0).length = dsRecLenA n Wt := by
    rw [← ds_recsA hn hd0 Wt, ds_flatMap_rev_length, dsRecLenA]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ds_preRec_length, List.length_map]; rfl
  have lB : (preRecsB (A := A) n Wt hd0 0).length = dsRecLenB n Wt := by
    rw [← ds_recsB hn hd0 Wt, ds_flatMap_rev_length, dsRecLenB]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ds_preRec_length, List.length_map]; rfl
  have hX₂X : ∀ y : DsY t₀, y ≠ dsyA → y ≠ dsyB → y ≠ .o .xT → y ≠ .o .xS → y ≠ dsyWT →
      y ≠ dsySTc → y ≠ .o .uD → X₂ y = X y := by
    intro y h1 h2 h3 h4 h5 h6 h7
    rw [hoff y h1 h2 h3 h4 h5 h6, hX₁, Function.update_of_ne h7]
  refine ⟨X₁₂, fun y hy => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [dsP1Out, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hy
    by_cases hR : y = .o .tR
    · subst hR; simp [hX₁₂, eTR]
    by_cases hT : y = .o .xT
    · subst hT; simp [hX₁₂, hX₁₁, hX₁₀, hX₉, hX₈, hX₇, hX₆, hX₅, hX₄, hX₃, eXT]
    by_cases hS : y = .o .xS
    · subst hS; simp [hX₁₂, hX₁₁, hX₁₀, hX₉, hX₈, hX₇, hX₆, hX₅, hX₄, hX₃, eXS]
    simp only [hX₁₂, hX₁₁, hX₁₀, hX₉, hX₈, hX₇, hX₆, hX₅, hX₄, hX₃, Function.update_apply, hR,
      hT, hS, h1, h2, h3, h4, h5, h6, h7, if_false]
    exact hX₂X y h2 h3 hT hS h4 h5 h1
  · simp [hX₁₂, hX₁₁, hX₁₀, hX₉, hX₈, hX₇, hX₆, hX₅, hX₄, hX₃]
    rw [hoff _ (fun e => by cases e) (fun e => by cases e) (fun e => by cases e)
      (fun e => by cases e) (fun e => by cases e) (fun e => by cases e)]
    simp [hX₁]
  · simp [hX₁₂, hX₁₁, hX₁₀, hX₉, hX₈, hX₇]
  · simp [hX₁₂, hX₁₁]
  · simp [hX₁₂, hX₁₁, hX₁₀, hX₉, hX₈, hX₇, hX₆, hX₅, hX₄, hX₃]
  · simp [hX₁₂, hX₁₁, hX₁₀, hX₉, hX₈, hX₇, hX₆, hX₅, hX₄]
  · simp [hX₁₂, hX₁₁, hX₁₀, hX₉, hX₈, hX₇, hX₆, hX₅, hX₄, hX₃, x2W]
  · simp [hX₁₂, hX₁₁, hX₁₀, hX₉, hX₈, hX₇, hX₆, hX₅, hX₄, hX₃, x2St]
  · refine (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
      (s11.seq (s12.seq (s13.seq (s14.seq (s15.seq s16))))))))))))))).congr_left
      (by rw [dsV1_pm]) |>.mono ?_
    simp only [List.length_reverse, ds_ldcBlocks_length, List.length_ofFn, lA, lB,
      List.length_append]
    unfold dsP1Cost
    omega

end P1

end IntegerMultBounds.MathlibTM2.Fast.TableVM
