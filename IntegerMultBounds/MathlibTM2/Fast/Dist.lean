module

public import IntegerMultBounds.MathlibTM2.Fast.DistRec
public import IntegerMultBounds.MathlibTM2.Fast.DistGlob

/-!
# The parameter distribution machine

`dsIoAll rg io` is one fixed program running after the parameter machine
(`Fast/ParamMachine.lean`, `pmParams_exec`) on its table layout `rg : TblR pmNV → Fin T` and on
the registers `io : DsR → Fin T`. It reads the parameters `pmVals n` from the layout, the table
word size `Wt` (`Wt` symbols on `io .uW`) and the coefficient width `w` (`w` symbols on
`io .uw`), and writes the record and stream formats read by the stage loaders onto empty
registers (`dsVal`):

| register | contents | reader |
|---|---|---|
| `recA` | `preRecsA n Wt hd0 0` | `Fast/PrepA.lean`, `rsaStage_exec` |
| `recB` | `preRecsB n Wt hd0 0` | `Fast/PrepB.lean`, `bandStage_exec` |
| `tS`, `sS` | `ldcBlocks (List.ofFn t)`, `ldcBlocks (List.ofFn s)` | `Fast/LoadChirp.lean` (`tS`, `sS`) |
| `pU`, `gU` | `p`, `g = chirpGuard d` ticks | chirp loader (`pU`, `gU`); ring header (`pR`) |
| `lN`, `lL`, `lK`, `lD`, `lB` | `N = Σ aᵢ = logT - ℓ`, `ℓ`, `K`, `D = d - 1`, `B = r w` ticks | `LdgPre` (`uN`, `uL`, `uK`, `uD`, `uB`); `lL` is the ring header's `lR` |
| `lW`, `lE` | `W_L = r w + N² + N + 4` ticks, `binSyms W_L E` | the layout table width `wr`, `LdgPre.eW` |
| `rR` | `r` ticks | the per-round `r w'` of `TopRegs` |
| `nn` | `topN w` ticks | `PreBaseA.nn`, `BandBase.nn` |

`E = 2^(d-1) - 2^numHalf` has bit `i` set iff axis `i` of the synthetic transform is long
(`numHalf ≤ i < d - 1`). The per-transform constants of the layer machine (`TopRegs`) are
`n + a = N` (`lN`) and `K` (`lK`); `r` (`rR`) gives `r w'` for the per-round width `w'`.

## Program

1. Phase 1 (`dsPhase1`): `Wt` into variable `38`, `d` ticks onto the loop counter `uD`, the axis
   loop (`dsAxes`, `Fast/DistAxis.lean`) pushing the `Ã` and `B̃₀` records and the reversed chirp
   blocks (`dsL₀`), `uD` cleared, the chirp blocks moved into place.
2. Phase 2 (`dsPhase2`): `w` into variable `39`; `p, g, ℓ, K, r` (`toUnary`); `N`, `D` (table
   steps); `B = w · r` by a unary product; `W_L = B + (N² + N + 4)`; `E` widened to `W_L` bits;
   `topN w`; variables `38`, `39` cleared.

The layout ends as it started (`pmVals n`), the inputs and the work registers too.

## Results

* `dsIoAll_runs`: the contract, within `dsIoAllCost n Wt w` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Moduli
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt


/-- The registers of the distribution machine off the parameter layout: the inputs `uW`, `uw`,
the outputs, and the work registers `uD`, `tm`, `xT`, `xS`. -/
inductive DsR
  | uW | uw | recA | recB | tS | sS | pU | gU | lN | lL | lK | lD | lB | lW | lE | rR | nn
  | uD | tm | xT | xS
  deriving DecidableEq

/-! ### Programs -/

section Prog

variable {T Q A : ℕ} {U P : Type}

/-- `P := 1`. -/
def dsInitC : TblCode pmNV := .ins (.inc 32)

/-- `i := 0`, `P := 0`. -/
def dsEndC : TblCode pmNV := tblBlock pmNV [.zero 31] (.zero 32)

/-- `Wt := 0`, `w := 0`. -/
def dsFinC : TblCode pmNV := tblBlock pmNV [.zero 38] (.zero 39)

/-- Phase 1: `Wt`, the axis loop, the chirp streams. -/
def dsPhase1 (rg : TblR pmNV → Fin T) (io : DsR → Fin T) : Pr P T Q A U :=
  .seq (dsLoad rg (io .uW) 38) <| .seq (dsUn rg 3 (io .uD)) <| .seq (tblCompile rg dsInitC) <|
  .seq (dsAxes rg (io .uD) (io .tm) (dsL₀ (io .recA) (io .recB) (io .xT) (io .xS))) <|
  .seq (uclear (io .uD)) <| .seq (tblCompile rg dsEndC) <|
  .seq (moveR (io .xT) (io .tS) id) (moveR (io .xS) (io .sS) id)

/-- Phase 2: `w` and the single values. -/
def dsPhase2 (rg : TblR pmNV → Fin T) (io : DsR → Fin T) : Pr P T Q A U :=
  .seq (dsLoad rg (io .uw) 39) <|
  .seq (dsUn rg 2 (io .pU)) <| .seq (dsUn rg 21 (io .gU)) <| .seq (dsUn rg 7 (io .lL)) <|
  .seq (dsUn rg 4 (io .lK)) <| .seq (dsUn rg 8 (io .rR)) <|
  .seq (dsStep rg dsCN (io .lN)) <| .seq (dsStep rg dsCD (io .lD)) <|
  .seq (dsUMul (io .uw) (io .rR) (io .lB) (io .tm) (io .xT)) <|
  .seq (ucopy (io .lB) (io .lW) (io .tm)) <|
  .seq (dsStep rg dsCWL (io .lW)) <|
  .seq (dsStepB rg dsCE (io .lE) (io .lW)) <|
  .seq (dsStep rg dsCTop (io .nn)) (tblCompile rg dsFinC)

/-- **The parameter distribution machine.** -/
def dsIoAll (rg : TblR pmNV → Fin T) (io : DsR → Fin T) : Pr P T Q A U :=
  .seq (dsPhase1 rg io) (dsPhase2 rg io)

end Prog

/-! ### The table codes of the glue -/

section Glue

variable {A w' : ℕ} {n Wt w : ℕ}

theorem dsInitC_do :
    TblDo A (pmW n) w' dsInitC ⟨dsV1 n Wt 0, []⟩ (· = ⟨dsLV n Wt 0, []⟩) 1 := by
  refine TblDo.insX _ ?_ ?_
  · simp [TblIns.fits, dsV1, pmNV]; have := pmW_ge n; omega
  · rw [dsLV_zero]; simp [TblIns.exact, dsV1, pmNV]

theorem dsEndC_do :
    TblDo A (pmW n) w' dsEndC ⟨dsLV n Wt (d n), []⟩ (· = ⟨dsV1 n Wt 0, []⟩) 2 := by
  refine TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) ?_
  rw [← dsLV_end]; rfl

theorem dsFinC_do :
    TblDo A (pmW n) w' dsFinC ⟨dsV1 n Wt w, []⟩ (· = ⟨pmVals n, []⟩) 2 := by
  refine TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) ?_
  rw [← dsV1_fin n Wt w]; rfl

end Glue

/-! ### The loop pushes and their outputs -/

section Out

variable {T A : ℕ} {n : ℕ}

/-- The variables pushed in one iteration. -/
def dsVarsL : List (Fin pmNV) := dsFA.reverse ++ dsFB.reverse ++ [33, 35]

theorem dsL₀_vars {T : ℕ} (oA oB xT xS : Fin T) :
    (dsL₀ oA oB xT xS).map (·.2.1) = dsVarsL := by
  simp [dsL₀, dsRecPush, dsVarsL, List.map_reverse, Function.comp_def]

theorem dsPushCost_eq (W : ℕ) (val : Fin pmNV → ℕ) (ps : List (Fin T × Fin pmNV × DsMode)) :
    dsPushCost W val ps = ((ps.map (·.2.1)).map fun x => W * (4 * val x + 11) + 2 * val x + 8).sum
      + 1 := by
  simp [dsPushCost, List.map_map, Function.comp_def]

/-- The step bound of the axis loop. -/
def dsLoopCost (n Wt : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d n), (28 * tblC (pmW n) (pmW n) +
    ((dsVarsL.map fun x => pmW n * (4 * dsAV n Wt i x + 11) + 2 * dsAV n Wt i x + 8).sum + 1)
      + 3) + 2 * d n + 4

theorem dsAxesCost_eq (n Wt : ℕ) (oA oB xT xS : Fin T) :
    dsAxesCost n Wt (dsL₀ oA oB xT xS) = dsLoopCost n Wt := by
  unfold dsAxesCost dsLoopCost dsAxCost
  simp only [dsPushCost_eq, dsL₀_vars]

theorem ds_acc_A {oA oB xT xS : Fin T} (h1 : oB ≠ oA) (h2 : xT ≠ oA) (h3 : xS ≠ oA)
    (hn : 2 ≤ n) (hd0 : 0 < d n) (Wt : ℕ) :
    dsAcc (A := A) n Wt (dsL₀ oA oB xT xS) (d n) oA = preRecsA n Wt hd0 0 := by
  unfold dsAcc
  simp only [dsOut_L₀_A h1 h2 h3]
  exact ds_recsA hn hd0 Wt

theorem ds_acc_B {oA oB xT xS : Fin T} (h1 : oA ≠ oB) (h2 : xT ≠ oB) (h3 : xS ≠ oB)
    (hn : 2 ≤ n) (hd0 : 0 < d n) (Wt : ℕ) :
    dsAcc (A := A) n Wt (dsL₀ oA oB xT xS) (d n) oB = preRecsB n Wt hd0 0 := by
  unfold dsAcc
  simp only [dsOut_L₀_B h1 h2 h3]
  exact ds_recsB hn hd0 Wt

theorem ds_acc_T {oA oB xT xS : Fin T} (h1 : oA ≠ xT) (h2 : oB ≠ xT) (h3 : xS ≠ xT) (Wt : ℕ) :
    dsAcc (A := A) n Wt (dsL₀ oA oB xT xS) (d n) xT = (ldcBlocks (List.ofFn (t n))).reverse := by
  unfold dsAcc
  simp only [dsOut_L₀_T h1 h2 h3]
  exact ds_blocksT Wt

theorem ds_acc_S {oA oB xT xS : Fin T} (h1 : oA ≠ xS) (h2 : oB ≠ xS) (h3 : xT ≠ xS) (Wt : ℕ) :
    dsAcc (A := A) n Wt (dsL₀ oA oB xT xS) (d n) xS = (ldcBlocks (List.ofFn (s n))).reverse := by
  unfold dsAcc
  simp only [dsOut_L₀_S h1 h2 h3]
  exact ds_blocksS Wt

end Out

theorem ds_ldcBlocks_length (l : List ℕ) : (ldcBlocks (A := A) l).length = l.sum + l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [ldcBlocks, List.flatMap_cons, ← ldcBlocks, List.length_append, ih]
    simp; ring

/-! ### Phase 1 -/

section Phase1

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {io : DsR → Fin T}

/-- The registers off the layout after phase 1. -/
noncomputable def dsR1 (io : DsR → Fin T) (n Wt : ℕ) (hd0 : 0 < d n) (R : Regs T A) :
    Regs T A :=
  Function.update (Function.update (Function.update (Function.update R
    (io .recA) (preRecsA n Wt hd0 0)) (io .recB) (preRecsB n Wt hd0 0))
    (io .tS) (ldcBlocks (List.ofFn (t n)))) (io .sS) (ldcBlocks (List.ofFn (s n)))

/-- The step bound of phase 1. -/
def dsPhase1Cost (n Wt : ℕ) : ℕ :=
  (2 * pmW n + 2 + (Wt * (4 * pmW n + 10) + 4 * pmW n + 8)) +
    (pmW n * (4 * d n + 11) + 2 * d n + 6) + 3 * tblC (pmW n) (pmW n) + dsLoopCost n Wt +
    (2 * d n + 2) + (2 * ((List.ofFn (t n)).sum + d n) + 2) +
    (2 * ((List.ofFn (s n)).sum + d n) + 2)

/-- **Phase 1.** From the parameter layout and `Wt` symbols on `uW`, with the records, streams
and work registers empty: the records and the chirp streams in place, `Wt` in variable `38`. -/
theorem ds_phase1 (hrg : Function.Injective rg) (hio : Function.Injective io)
    (hdisj : ∀ r x, rg r ≠ io x) {n Wt : ℕ} (hB : Big n) (hd0 : 0 < d n)
    (hWt : Wt < 2 ^ pmW n) (wl : List (Fin (A + 4))) (hwl : wl.length = pmW n) (R : Regs T A)
    (huW : (R (io .uW)).length = Wt)
    (hR0 : ∀ x ∈ [DsR.recA, .recB, .tS, .sS, .uD, .tm, .xT, .xS], R (io x) = []) :
    dsRuns body (dsPhase1 rg io) (dsOv rg R (tblRho (pmW n) wl wl ⟨pmVals n, []⟩))
      (dsOv rg (dsR1 io n Wt hd0 R) (tblRho (pmW n) wl wl ⟨dsV1 n Wt 0, []⟩))
      (dsPhase1Cost n Wt) := by
  have hn : 2 ≤ n := hB.1
  have ho : ∀ x r, rg r ≠ io x := fun x r => hdisj r x
  have hne : ∀ {x y : DsR}, x ≠ y → io x ≠ io y := fun h => hio.ne h
  have h0 : ∀ j, dsV1 n Wt 0 j < 2 ^ pmW n := dsV1_lt hB hWt (Nat.two_pow_pos _)
  set L := dsL₀ (io .recA) (io .recB) (io .xT) (io .xS) with hL
  -- 1. `Wt` into `38`
  have s1 := ds_load (body := body) hrg (ho .uW) wl hwl (pmVals n) 38 R
  rw [huW, ← dsV1_pm, dsV1_upd38] at s1
  -- 2. `d` ticks onto `uD`
  have s2 := ds_un (body := body) hrg (ho .uD) wl wl ⟨dsV1 n Wt 0, []⟩ 3 (h0 3) R
  have hd3 : dsV1 n Wt 0 3 = d n := by simp [dsV1, pmNV, pmVal]
  simp only [hd3, hR0 .uD (by simp), List.append_nil] at s2
  set R₁ := Function.update R (io .uD) (List.replicate (d n) tick) with hR₁
  -- 3. `P := 1`
  have s3 := ds_code (body := body) hrg wl wl hwl hwl le_rfl (dsInitC_do (A := A) (w' := pmW n)
    (n := n) (Wt := Wt)) h0 R₁
  -- 4. the axis loop
  have hLt : ∀ e ∈ L, ∀ r, rg r ≠ e.1 := by
    intro e he r; simp [hL, dsL₀, dsRecPush] at he
    rcases he with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ | rfl | rfl <;> exact ho _ r
  have hLu : ∀ e ∈ L, e.1 ≠ io .uD := by
    intro e he; simp [hL, dsL₀, dsRecPush] at he
    rcases he with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ | rfl | rfl <;> exact hne (by decide)
  have hLm : ∀ e ∈ L, e.1 ≠ io .tm := by
    intro e he; simp [hL, dsL₀, dsRecPush] at he
    rcases he with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ | rfl | rfl <;> exact hne (by decide)
  have s4 := ds_axes (body := body) hrg (ho .uD) (ho .tm) (hne (by decide)) hB hWt wl hwl L hLt hLu
    hLm R₁ (by simp [hR₁]) (by rw [hR₁, Function.update_of_ne (hne (by decide))]; exact hR0 .tm (by simp))
  rw [dsAxesCost_eq] at s4
  unfold dsPsi at s4
  set X := fun k => dsAcc n Wt L (d n) k ++ R₁ k with hX
  -- 5. clear `uD`
  have s5 := ds_uclear (body := body) (io .uD)
    (dsOv rg X (tblRho (pmW n) wl wl ⟨dsLV n Wt (d n), []⟩))
  rw [dsOv_off _ _ (ho .uD), dsOv_update _ _ (ho .uD)] at s5
  have hXu : (X (io .uD)).length = d n := by
    simp [hX, hR₁, dsAcc_none n Wt L hLu]
  rw [hXu] at s5
  set X₂ := Function.update X (io .uD) [] with hX₂
  -- 6. `i, P := 0`
  have s6 := ds_code (body := body) hrg wl wl hwl hwl le_rfl (dsEndC_do (A := A) (w' := pmW n)
    (n := n) (Wt := Wt)) (dsLV_lt hB hWt le_rfl) X₂
  -- 7, 8. the chirp streams
  have s7 := ds_moveR (body := body) (hne (by decide) : io .xT ≠ io .tS)
    (dsOv rg X₂ (tblRho (pmW n) wl wl ⟨dsV1 n Wt 0, []⟩))
  rw [dsOv_off _ _ (ho .xT), dsOv_off _ _ (ho .tS), dsOv_update _ _ (ho .xT),
    dsOv_update _ _ (ho .tS)] at s7
  set X₃ := Function.update (Function.update X₂ (io .xT) []) (io .tS)
    ((X₂ (io .xT)).reverse ++ X₂ (io .tS)) with hX₃
  have s8 := ds_moveR (body := body) (hne (by decide) : io .xS ≠ io .sS)
    (dsOv rg X₃ (tblRho (pmW n) wl wl ⟨dsV1 n Wt 0, []⟩))
  rw [dsOv_off _ _ (ho .xS), dsOv_off _ _ (ho .sS), dsOv_update _ _ (ho .xS),
    dsOv_update _ _ (ho .sS)] at s8
  have hX2T : X₂ (io .xT) = (ldcBlocks (List.ofFn (t n))).reverse := by
    rw [hX₂, Function.update_of_ne (hne (by decide)), hX]
    simp only
    rw [ds_acc_T (hne (by decide)) (hne (by decide)) (hne (by decide)), hR₁,
      Function.update_of_ne (hne (by decide)), hR0 .xT (by simp), List.append_nil]
  have hX3S : X₃ (io .xS) = (ldcBlocks (List.ofFn (s n))).reverse := by
    rw [hX₃, Function.update_of_ne (hne (by decide)), Function.update_of_ne (hne (by decide)),
      hX₂, Function.update_of_ne (hne (by decide)), hX]
    simp only
    rw [ds_acc_S (hne (by decide)) (hne (by decide)) (hne (by decide)), hR₁,
      Function.update_of_ne (hne (by decide)), hR0 .xS (by simp), List.append_nil]
  have hacc0 : ∀ x : DsR, x ≠ .recA → x ≠ .recB → x ≠ .xT → x ≠ .xS →
      dsAcc (A := A) n Wt L (d n) (io x) = [] := by
    intro x h1 h2 h3 h4
    refine dsAcc_none n Wt L (fun e he => ?_) (d n)
    simp [hL, dsL₀, dsRecPush] at he
    rcases he with ⟨y, -, rfl⟩ | ⟨y, -, rfl⟩ | rfl | rfl
    exacts [hne (Ne.symm h1), hne (Ne.symm h2), hne (Ne.symm h3), hne (Ne.symm h4)]
  have hA := ds_acc_A (A := A) (oA := io .recA) (oB := io .recB) (xT := io .xT) (xS := io .xS)
    (hne (by decide) : io .recB ≠ io .recA) (hne (by decide))
    (hne (by decide)) hn hd0 Wt
  have hBloc := ds_acc_B (A := A) (oA := io .recA) (oB := io .recB) (xT := io .xT) (xS := io .xS)
    (hne (by decide) : io .recA ≠ io .recB) (hne (by decide))
    (hne (by decide)) hn hd0 Wt
  have hT := ds_acc_T (A := A) (oA := io .recA) (oB := io .recB) (xT := io .xT) (xS := io .xS)
    (n := n) (hne (by decide) : io .recA ≠ io .xT) (hne (by decide))
    (hne (by decide)) Wt
  have hS := ds_acc_S (A := A) (oA := io .recA) (oB := io .recB) (xT := io .xT) (xS := io .xS)
    (n := n) (hne (by decide) : io .recA ≠ io .xS) (hne (by decide))
    (hne (by decide)) Wt
  rw [← hL] at hA hBloc hT hS
  have e : Function.update (Function.update X₃ (io .xS) []) (io .sS)
      ((X₃ (io .xS)).reverse ++ X₃ (io .sS)) = dsR1 io n Wt hd0 R := by
    funext k
    by_cases hk : ∃ x, io x = k
    · obtain ⟨x, rfl⟩ := hk
      cases x <;> simp [Function.update_apply, hio.eq_iff, hX₃, hX₂, hX, hR₁, hA, hBloc, hT, hS,
        hacc0, hR0, dsR1]
    · push Not at hk
      have hk' : ∀ x, k ≠ io x := fun x h => hk x h.symm
      have hoff : dsAcc (A := A) n Wt L (d n) k = [] := by
        refine dsAcc_none n Wt L (fun e he => ?_) (d n)
        simp [hL, dsL₀, dsRecPush] at he
        rcases he with ⟨y, -, rfl⟩ | ⟨y, -, rfl⟩ | rfl | rfl <;> exact hk _
      simp [Function.update_apply, hk', hX₃, hX₂, hX, hR₁, hoff, dsR1]
  rw [e] at s8
  refine ((s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq s8)))))))).congr_left
    (by rw [dsV1_pm]) |>.mono ?_
  have l1 : (X₂ (io .xT)).length = (List.ofFn (t n)).sum + d n := by
    rw [hX2T, List.length_reverse, ds_ldcBlocks_length, List.length_ofFn]
  have l2 : (X₃ (io .xS)).length = (List.ofFn (s n)).sum + d n := by
    rw [hX3S, List.length_reverse, ds_ldcBlocks_length, List.length_ofFn]
  rw [l1, l2]
  unfold dsPhase1Cost
  omega

end Phase1

/-! ### Phase 2 -/

section Phase2

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {io : DsR → Fin T}

/-- The registers off the layout after phase 2. -/
noncomputable def dsR2 (io : DsR → Fin T) (n w : ℕ) (R : Regs T A) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update R
    (io .pU) (List.replicate (p n) tick))
    (io .gU) (List.replicate (Chirp.chirpGuard (d n)) tick))
    (io .lL) (List.replicate (ℓ n) tick))
    (io .lK) (List.replicate (K n) tick))
    (io .rR) (List.replicate (r n) tick))
    (io .lN) (List.replicate (logT n - ℓ n) tick))
    (io .lD) (List.replicate (d n - 1) tick))
    (io .lB) (List.replicate (r n * w) tick))
    (io .lW) (List.replicate (dsWL n w) tick))
    (io .lE) (binSyms (dsWL n w) (dsE n)))
    (io .nn) (List.replicate (dsTopN w) tick)

/-- The step bound of `toUnary` of the value `x` in words of `W` bits. -/
def dsUnCost (W x : ℕ) : ℕ := W * (4 * x + 11) + 2 * x + 6

/-- The step bound of phase 2. -/
def dsPhase2Cost (n w : ℕ) : ℕ :=
  (2 * pmW n + 2 + (w * (4 * pmW n + 10) + 4 * pmW n + 8)) +
    (dsUnCost (pmW n) (p n) + dsUnCost (pmW n) (Chirp.chirpGuard (d n)) + dsUnCost (pmW n) (ℓ n) +
      dsUnCost (pmW n) (K n) + dsUnCost (pmW n) (r n)) +
    dsStepCost (pmW n) 1 (logT n - ℓ n) + dsStepCost (pmW n) 3 (d n - 1) +
    (w * (4 * r n + 7) + 2 * w + 4) + (4 * (w * r n) + 4) +
    dsStepCost (pmW n) 7 ((logT n - ℓ n) ^ 2 + (logT n - ℓ n) + 4) +
    dsStepBCost (pmW n) (dsEK n) (dsWL n w) + dsStepCost (pmW n) (dsTopK w) (dsTopN w) +
    2 * tblC (pmW n) (pmW n)

/-- **Phase 2.** From `Wt` in variable `38` and `w` symbols on `uw`, with the outputs of the
phase and the work registers `tm`, `xT` empty: the single values in place, the layout back to
the parameters. -/
theorem ds_phase2 (hrg : Function.Injective rg) (hio : Function.Injective io)
    (hdisj : ∀ r x, rg r ≠ io x) {n Wt w : ℕ} (hB : Big n) (hWt : Wt < 2 ^ pmW n)
    (hw : 4 * w + 2 < 2 ^ pmW n) (hWL : pmW n ≤ dsWL n w) (wl : List (Fin (A + 4)))
    (hwl : wl.length = pmW n) (R : Regs T A) (huw : (R (io .uw)).length = w)
    (hR0 : ∀ x ∈ [DsR.pU, .gU, .lL, .lK, .rR, .lN, .lD, .lB, .lW, .lE, .nn, .tm, .xT],
      R (io x) = []) :
    dsRuns body (dsPhase2 rg io) (dsOv rg R (tblRho (pmW n) wl wl ⟨dsV1 n Wt 0, []⟩))
      (dsOv rg (dsR2 io n w R) (tblRho (pmW n) wl wl ⟨pmVals n, []⟩)) (dsPhase2Cost n w) := by
  have hn : 2 ≤ n := hB.1
  have ho : ∀ x r, rg r ≠ io x := fun x r => hdisj r x
  have hne : ∀ {x y : DsR}, x ≠ y → io x ≠ io y := fun h => hio.ne h
  have hw' : w < 2 ^ pmW n := by omega
  have h1 : ∀ j, dsV1 n Wt w j < 2 ^ pmW n := dsV1_lt hB hWt hw'
  have hσ0 : ∀ j : Fin pmNV, 31 ≤ j.val → j.val < 38 → dsV1 n Wt w j = 0 := dsV1_scr n Wt w
  set ρ := tblRho (pmW n) wl wl (⟨dsV1 n Wt w, []⟩ : TblSt pmNV A) with hρ
  -- `w` into `39`
  have s1 := ds_load (body := body) hrg (ho .uw) wl hwl (dsV1 n Wt 0) 39 R
  rw [huw, dsV1_upd39] at s1
  -- `p, g, ℓ, K, r`
  have u1 := ds_un (body := body) hrg (ho .pU) wl wl ⟨dsV1 n Wt w, []⟩ 2 (h1 2) R
  set R₁ := Function.update R (io .pU) (List.replicate (dsV1 n Wt w 2) tick ++ R (io .pU))
  have u2 := ds_un (body := body) hrg (ho .gU) wl wl ⟨dsV1 n Wt w, []⟩ 21 (h1 21) R₁
  set R₂ := Function.update R₁ (io .gU) (List.replicate (dsV1 n Wt w 21) tick ++ R₁ (io .gU))
  have u3 := ds_un (body := body) hrg (ho .lL) wl wl ⟨dsV1 n Wt w, []⟩ 7 (h1 7) R₂
  set R₃ := Function.update R₂ (io .lL) (List.replicate (dsV1 n Wt w 7) tick ++ R₂ (io .lL))
  have u4 := ds_un (body := body) hrg (ho .lK) wl wl ⟨dsV1 n Wt w, []⟩ 4 (h1 4) R₃
  set R₄ := Function.update R₃ (io .lK) (List.replicate (dsV1 n Wt w 4) tick ++ R₃ (io .lK))
  have u5 := ds_un (body := body) hrg (ho .rR) wl wl ⟨dsV1 n Wt w, []⟩ 8 (h1 8) R₄
  set R₅ := Function.update R₄ (io .rR) (List.replicate (dsV1 n Wt w 8) tick ++ R₄ (io .rR))
  -- `N`, `D`
  have t1 := ds_step (body := body) hrg (ho .lN) wl hwl (dsCN_do (A := A) (w' := pmW n)
    (n := n) (Wt := Wt) (w := w) hB) hσ0 h1 R₅
  set R₆ := Function.update R₅ (io .lN) (List.replicate (logT n - ℓ n) tick ++ R₅ (io .lN))
  have t2 := ds_step (body := body) hrg (ho .lD) wl hwl (dsCD_do (A := A) (w' := pmW n)
    (n := n) (Wt := Wt) (w := w) hB) hσ0 h1 R₆
  set R₇ := Function.update R₆ (io .lD) (List.replicate (d n - 1) tick ++ R₆ (io .lD))
  -- `B = w r`, `W_L`
  have v1 := ds_umul (body := body) (a := io .uw) (b := io .rR) (c := io .lB) (t₁ := io .tm)
    (t₂ := io .xT) (by simp [List.nodup_cons, hio.eq_iff]) (dsOv rg R₇ ρ)
    (by rw [dsOv_off _ _ (ho .tm)]; simp [R₇, R₆, R₅, R₄, R₃, R₂, R₁, 
      hio.eq_iff, hR0])
    (by rw [dsOv_off _ _ (ho .xT)]; simp [R₇, R₆, R₅, R₄, R₃, R₂, R₁, 
      hio.eq_iff, hR0])
  have euw : (dsOv rg R₇ ρ (io .uw)).length = w := by
    rw [dsOv_off _ _ (ho .uw)]; simp [R₇, R₆, R₅, R₄, R₃, R₂, R₁, 
      hio.eq_iff, huw]
  have erR : (dsOv rg R₇ ρ (io .rR)).length = r n := by
    rw [dsOv_off _ _ (ho .rR)]; simp [R₇, R₆, R₅, R₄, R₃, R₂, R₁, 
      hio.eq_iff, hR0, dsV1, pmNV, pmVal]
  rw [euw, erR, dsOv_off _ _ (ho .lB), dsOv_update _ _ (ho .lB)] at v1
  set R₈ := Function.update R₇ (io .lB) (List.replicate (w * r n) tick ++ R₇ (io .lB))
  have v2 := ds_ucopy (body := body) (a := io .lB) (b := io .lW) (t := io .tm) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (dsOv rg R₈ ρ)
    (by rw [dsOv_off _ _ (ho .tm)]; simp [R₈, R₇, R₆, R₅, R₄, R₃, R₂, R₁, 
      hio.eq_iff, hR0])
  have elB : (dsOv rg R₈ ρ (io .lB)).length = w * r n := by
    rw [dsOv_off _ _ (ho .lB)]; simp [R₈, R₇, R₆, R₅, R₄, R₃, R₂, R₁, 
      hio.eq_iff, hR0]
  rw [elB, dsOv_off _ _ (ho .lW), dsOv_update _ _ (ho .lW)] at v2
  set R₉ := Function.update R₈ (io .lW) (List.replicate (w * r n) tick ++ R₈ (io .lW))
  have t3 := ds_step (body := body) hrg (ho .lW) wl hwl (dsCWL_do (A := A) (w' := pmW n)
    (n := n) (Wt := Wt) (w := w) hB) hσ0 h1 R₉
  set R₁₀ := Function.update R₉ (io .lW) (List.replicate ((logT n - ℓ n) ^ 2 + (logT n - ℓ n) + 4)
    tick ++ R₉ (io .lW))
  -- `E`
  have elW : (R₁₀ (io .lW)).length = dsWL n w := by
    simp [R₁₀, R₉, R₈, R₇, R₆, R₅, R₄, R₃, R₂, R₁, hio.eq_iff, hR0, dsWL]
    ring
  have t4 := ds_stepB (body := body) hrg (ho .lE) (ho .lW) (hne (by decide)) wl hwl
    (dsCE_do (A := A) (w' := pmW n) (n := n) (Wt := Wt) (w := w) hB) hσ0 h1 hWL R₁₀
    (by simp [R₁₀, R₉, R₈, R₇, R₆, R₅, R₄, R₃, R₂, R₁, hio.eq_iff, hR0])
    elW
  set R₁₁ := Function.update R₁₀ (io .lE) (binSyms (dsWL n w) (dsE n))
  -- `topN w`
  have t5 := ds_step (body := body) hrg (ho .nn) wl hwl (dsCTop_do (A := A) (w' := pmW n)
    (n := n) (Wt := Wt) (w := w) hw) hσ0 h1 R₁₁
  set R₁₂ := Function.update R₁₁ (io .nn) (List.replicate (dsTopN w) tick ++ R₁₁ (io .nn))
  -- clear `38`, `39`
  have t6 := ds_code (body := body) hrg wl wl hwl hwl le_rfl (dsFinC_do (A := A) (w' := pmW n)
    (n := n) (Wt := Wt) (w := w)) h1 R₁₂
  have e : R₁₂ = dsR2 io n w R := by
    funext k
    by_cases hk : ∃ x, io x = k
    · obtain ⟨x, rfl⟩ := hk
      cases x <;> simp [R₁₂, R₁₁, R₁₀, R₉, R₈, R₇, R₆, R₅, R₄, R₃, R₂, R₁, 
        hio.eq_iff, hR0, dsR2, dsV1, pmNV, pmVal, dsWL] <;> ring
    · push Not at hk
      have hk' : ∀ x, k ≠ io x := fun x h => hk x h.symm
      simp [R₁₂, R₁₁, R₁₀, R₉, R₈, R₇, R₆, R₅, R₄, R₃, R₂, R₁, Function.update_apply, hk', dsR2]
  have hv2 : dsV1 n Wt w 2 = p n := by simp [dsV1, pmNV, pmVal]
  have hv21 : dsV1 n Wt w 21 = Chirp.chirpGuard (d n) := by simp [dsV1, pmNV, pmVal]
  have hv7 : dsV1 n Wt w 7 = ℓ n := by simp [dsV1, pmNV, pmVal]
  have hv4 : dsV1 n Wt w 4 = K n := by simp [dsV1, pmNV, pmVal]
  have hv8 : dsV1 n Wt w 8 = r n := by simp [dsV1, pmNV, pmVal]
  refine (s1.seq (u1.seq (u2.seq (u3.seq (u4.seq (u5.seq (t1.seq (t2.seq (v1.seq (v2.seq
    (t3.seq (t4.seq (t5.seq (t6.congr (by rw [e]))))))))))))))).mono ?_
  simp only [hv2, hv21, hv7, hv4, hv8]
  unfold dsPhase2Cost dsUnCost
  omega

end Phase2

/-! ### The machine -/

section All

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {io : DsR → Fin T}

/-- The final contents of the registers `io`: the inputs `uW`, `uw` as they started, the outputs,
the work registers empty. -/
noncomputable def dsVal (n Wt w : ℕ) (hd0 : 0 < d n) (vW vw : List (Fin (A + 4))) :
    DsR → List (Fin (A + 4))
  | .uW => vW
  | .uw => vw
  | .recA => preRecsA n Wt hd0 0
  | .recB => preRecsB n Wt hd0 0
  | .tS => ldcBlocks (List.ofFn (t n))
  | .sS => ldcBlocks (List.ofFn (s n))
  | .pU => List.replicate (p n) tick
  | .gU => List.replicate (Chirp.chirpGuard (d n)) tick
  | .lN => List.replicate (logT n - ℓ n) tick
  | .lL => List.replicate (ℓ n) tick
  | .lK => List.replicate (K n) tick
  | .lD => List.replicate (d n - 1) tick
  | .lB => List.replicate (r n * w) tick
  | .lW => List.replicate (dsWL n w) tick
  | .lE => binSyms (dsWL n w) (dsE n)
  | .rR => List.replicate (r n) tick
  | .nn => List.replicate (dsTopN w) tick
  | .uD => []
  | .tm => []
  | .xT => []
  | .xS => []

/-- The step bound of `dsIoAll`. -/
def dsIoAllCost (n Wt w : ℕ) : ℕ := dsPhase1Cost n Wt + dsPhase2Cost n w

/-- **The parameter distribution machine** (register-file form). From the parameter layout
carrying `pmVals n`, `Wt` symbols on `uW`, `w` symbols on `uw` and every other register of `io`
empty, `dsIoAll` ends with the registers `io` holding `dsVal` and the layout and every other
register as they started, within `dsIoAllCost n Wt w` steps. -/
theorem dsIoAll_runs (hrg : Function.Injective rg) (hio : Function.Injective io)
    (hdisj : ∀ r x, rg r ≠ io x) {n Wt w : ℕ} (hB : Big n) (hd0 : 0 < d n)
    (hWt : Wt < 2 ^ pmW n) (hw : 4 * w + 2 < 2 ^ pmW n) (hWL : pmW n ≤ dsWL n w)
    (wl : List (Fin (A + 4))) (hwl : wl.length = pmW n) (R : Regs T A)
    (huW : (R (io .uW)).length = Wt) (huw : (R (io .uw)).length = w)
    (hR0 : ∀ x, x ≠ .uW → x ≠ .uw → R (io x) = []) :
    dsRuns body (dsIoAll rg io) (dsOv rg R (tblRho (pmW n) wl wl ⟨pmVals n, []⟩))
      (dsOv rg (dsOv io R (dsVal n Wt w hd0 (R (io .uW)) (R (io .uw))))
        (tblRho (pmW n) wl wl ⟨pmVals n, []⟩)) (dsIoAllCost n Wt w) := by
  have hn : 2 ≤ n := hB.1
  have h1 := ds_phase1 (body := body) hrg hio hdisj hB hd0 hWt wl hwl R huW
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hR0 _ (by decide) (by decide))
  have h2 := ds_phase2 (body := body) (Wt := Wt) hrg hio hdisj hB hWt hw hWL wl hwl
    (dsR1 io n Wt hd0 R)
    (by simp [dsR1, hio.eq_iff, huw])
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [dsR1, hio.eq_iff, hR0])
  refine (h1.seq (h2.congr ?_))
  congr 1
  funext k
  by_cases hk : ∃ x, io x = k
  · obtain ⟨x, rfl⟩ := hk
    rw [dsOv_rg hio]
    cases x <;> simp [dsR2, dsR1, hio.eq_iff, dsVal, hR0]
  · push Not at hk
    rw [dsOv_off _ _ hk]
    have hk' : ∀ x, k ≠ io x := fun x h => hk x h.symm
    simp [dsR2, dsR1, hk']

end All

end IntegerMultBounds.MathlibTM2.Fast.TableVM
