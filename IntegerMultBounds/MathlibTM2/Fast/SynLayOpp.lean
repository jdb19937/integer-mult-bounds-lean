module

public import IntegerMultBounds.MathlibTM2.Fast.SynLayFwd
public import IntegerMultBounds.MathlibTM2.Fast.SynLayUnapply

/-!
# The opposite layout program of the synthetic transforms

Paper §6, proof of `lem:synthetic-transform-cost`. The program `slyOpp` discharges the layout
hypothesis `hLay` of `synOpp_spec` (`Fast/SynFwd.lean`): the setup (`slySetup`), the writer of
the forward description streams (`ldgWriter … ldxCode`), the reversal of the records of both
streams (`slyRevStreams`: the single-bit moves reversed with source and target exchanged, the
exchanges reversed), the restoring machine `layUnapply` with the loaders, and the cleanup
(`slyClean`). It is one fixed text; the sizes come from the wires and from `park` as for
`slyFwd`.

* `sg_slyRevStreams`: the reversal pass on the file after the writer.
* `sly_post_opp`: the file after the restoring machine in the canonical form of the cleanup.
* `slyUnstageCost`: the cost of the writer, the reversal and the restoring machine on the file
  `R` (bank registers only, `slyUnstageCost_congr`); `slyOppCost`: the cost of `slyOpp`.
* `slyOpp_lay`: the hypothesis `hLay` of `synOpp_spec` for `slyOpp`, `Pk := slyPk W E`,
  `cL := slyOppCost …`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.Rounds
  IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-! ### The reversal of the description streams -/

section Rev

variable {Q Ka : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q (prime + Ka) U)

/-- Reverse the records of the single-bit move stream `dM` (counter `cM`, records of `|cN|`
symbols, real and imaginary bits exchanged) and of the exchange stream `dX` (counter `cX`,
records of `5 |cW|` symbols), through the spare wires `s 5`, `s 6`, `s 7`. -/
noncomputable def slyRevStreams : Pr P (nT SXReg) Q (prime + Ka) U :=
  .seq (slyRevStream (slyRg .cM) (slyRg .tM) (slyLr .cN) (slyLr .tS) (slyLr .dM) (sreg (.s 6))
    (sreg (.s 5)) (slyPairSw (prime + Ka))) <|
  .seq (umul 5 (slyLr .cW) (sreg (.s 7)) (slyLr .tB)) <|
  .seq (slyRevStream (slyRg .cX) (slyRg .tX) (sreg (.s 7)) (slyLr .tS) (slyLr .dX) (sreg (.s 6))
    (sreg (.s 5)) id)
    (uclear (sreg (.s 7)))

/-- The step bound of the reversal: `m` single-bit moves of `n` symbols, `x` exchanges of
`5 wX` symbols. -/
def slyRevStreamsCost (m n x wX : ℕ) : ℕ :=
  slyRevStreamCost m n + (4 * wX + 4) + slyRevStreamCost x (5 * wX) + (2 * (5 * wX) + 2)

/-- The file after the writer with the streams of the inverse layout. -/
noncomputable def slyRw' (R : Fin (nT SXReg) → List (Fin (prime + Ka + 4))) (es : List ℕ)
    (ℓ K B : ℕ) : Fin (nT SXReg) → List (Fin (prime + Ka + 4)) :=
  Function.update (Function.update (ldgPost slyRg slyLr R es ℓ K B (layXcs es ℓ K B)) (slyLr .dM)
    (ldlBitStream (prime + Ka) es.sum ((layBits es ℓ K).map Prod.swap).reverse)) (slyLr .dX)
    (ldlXcStream (prime + Ka) (es.sum + B + 2) (layXcs es ℓ K B).reverse)

theorem slyRw'_eq (R : Fin (nT SXReg) → List (Fin (prime + Ka + 4))) (es : List ℕ) (ℓ K B : ℕ) :
    slyRw' R es ℓ K B = Function.update (Function.update
      (ldgPost slyRg slyLr R es ℓ K B (layXcs es ℓ K B)) (slyLr .dM)
      (ldlBitStream (prime + Ka) es.sum ((layBits es ℓ K).map Prod.swap).reverse)) (slyLr .dX)
      (ldlXcStream (prime + Ka) (es.sum + B + 2) (layXcs es ℓ K B).reverse) := rfl

/-- **The reversal pass.** On the file after the writer (idle wires apart from the parameters),
the description streams become those of the inverse layout; every other register is restored. -/
theorem sg_slyRevStreams (hA : 4 ≤ prime + Ka) {es : List ℕ} {ℓ K w l : ℕ}
    {L : Equiv.Perm (Fin es.sum)} {v₀ : SynW → List (Fin (prime + Ka + 4))}
    (hv₀ : SynV v₀ es ℓ K w l 0 L) (io P' : List (Fin (prime + Ka + 4))) (W E B : ℕ) :
    LayRuns body slyRevStreams
      (ldgPost slyRg slyLr (synG (synIdle io P') (slyV₂ W E es.sum B v₀)) es ℓ K B (layXcs es ℓ K B))
      (slyRw' (synG (synIdle io P') (slyV₂ W E es.sum B v₀)) es ℓ K B)
      (slyRevStreamsCost (layBits es ℓ K).length es.sum (layXcs es ℓ K B).length (es.sum + B + 2)) := by
  have hs := hv₀.hs
  have hly := hv₀.hly
  set Rw := ldgPost slyRg slyLr (synG (synIdle io P') (slyV₂ W E es.sum B v₀)) es ℓ K B
    (layXcs es ℓ K B) with hRw
  have hwire : ∀ i : Fin 32, 3 ≤ i.val → Rw (sreg (.s i)) = [] := by
    intro i hi
    rw [hRw]
    simp only [ldgPost, Function.update_apply, slyLr, slyRg, slyT_eq_sreg_iff, sreg_eq_slyT_iff,
      sreg_injective.eq_iff, ite_false, synG_sreg, slyV₂, slyPV, SynW.s.injEq, reduceCtorEq]
    split_ifs <;> first | exact hs i |
      (exfalso; rename_i h; have := congrArg Fin.val h; simp at this; omega)
  have hM := lr_slyRevStream (body := body) (cnt := slyRg .cM) (sp1 := slyRg .tM) (cn := slyLr .cN)
    (sp2 := slyLr .tS) (src := slyLr .dM) (tmp := sreg (.s 6)) (dst := sreg (.s 5))
    (by simp [slyRg, slyLr, slyT_inj, sreg_injective.eq_iff]) (slyPairSw (prime + Ka)) Rw
    ((layBits es ℓ K).map (ldlBitRec (prime + Ka) es.sum)) es.sum (sly_mem_bitRec_length _ _)
    (by simp [hRw, ldgPost, Function.update_apply, slyLr, slyRg, slyT_inj, slyBitStream_eq_flatten])
    (by simp [hRw, ldgPost, Function.update_apply, slyLr, slyRg, slyT_inj, sreg_injective.eq_iff,
      length_ldlBitStream_one])
    (by simp [hRw, ldgPost, Function.update_apply, slyLr, slyRg, slyT_inj])
    (by rw [hRw, ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp), slyRg_tM, synG_sreg]
        simp [slyV₂, slyPV, hly])
    (by rw [hRw, ldgPost_lr sly_regs _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp), slyLr_tS,
          synG_of_ne (slyT_out _), synIdle_slyT])
    (hwire 6 (by norm_num)) (hwire 5 (by norm_num))
  rw [slyBitStream_rev hA] at hM
  set R1 := Function.update Rw (slyLr .dM)
    (ldlBitStream (prime + Ka) es.sum ((layBits es ℓ K).map Prod.swap).reverse) with hR1
  have hR1lr : ∀ y, y ≠ .dM → R1 (slyLr y) = Rw (slyLr y) := fun y hy => by
    rw [hR1, Function.update_of_ne (sly_regs.l.lr_inj.ne hy)]
  have hR1rg : ∀ y, R1 (slyRg y) = Rw (slyRg y) := fun y => by
    rw [hR1, Function.update_of_ne (sly_regs.l.disj _ _)]
  have hR1w : ∀ x : SynW, R1 (sreg x) = Rw (sreg x) := fun x => by
    rw [hR1, slyLr_dM, Function.update_of_ne (slyT_ne_sreg _ _)]
  have hU := lr_umul (body := body) (R := R1) 5 (a := slyLr .cW) (b := sreg (.s 7)) (t := slyLr .tB)
    (by simp [slyLr]) (by simp [slyLr, slyT_inj]) (by simp [slyLr])
    (by rw [hR1lr _ (by simp), hRw, ldgPost_lr sly_regs _ _ _ _ _ _ (by simp) (by simp) (by simp)
          (by simp), slyLr_tB, synG_of_ne (slyT_out _), synIdle_slyT])
  have hcW : R1 (slyLr .cW) = List.replicate (es.sum + B + 2) tick := by
    rw [hR1lr _ (by simp), hRw]
    simp [ldgPost, Function.update_apply, slyLr, slyRg, slyT_inj]
  have hs7 : R1 (sreg (.s 7)) = [] := by rw [hR1w, hwire 7 (by norm_num)]
  rw [hcW, hs7, List.length_replicate, List.append_nil] at hU
  set R2 := Function.update R1 (sreg (.s 7)) (List.replicate (5 * (es.sum + B + 2)) tick) with hR2
  have hlr7 : ∀ y, slyLr y ≠ sreg (.s 7) := fun y => by cases y <;> simp [slyLr]
  have hR2lr : ∀ y, R2 (slyLr y) = R1 (slyLr y) := fun y => by
    rw [hR2, Function.update_of_ne (hlr7 y)]
  have hR2rg : ∀ y, (∀ i, y ≠ .sw i) → y ≠ .str → R2 (slyRg y) = Rw (slyRg y) := by
    intro y h1 h2
    rw [hR2, ← hR1rg]
    cases y <;> first | exact absurd rfl (h2) | exact absurd rfl (h1 _) |
      (rw [Function.update_of_ne]; simp [slyRg, sreg_injective.eq_iff])
  have hX := lr_slyRevStream (body := body) (cnt := slyRg .cX) (sp1 := slyRg .tX)
    (cn := sreg (.s 7)) (sp2 := slyLr .tS) (src := slyLr .dX) (tmp := sreg (.s 6))
    (dst := sreg (.s 5)) (by simp [slyRg, slyLr, slyT_inj, sreg_injective.eq_iff]) id R2
    ((layXcs es ℓ K B).map fun d => ldlXcRec (prime + Ka) (es.sum + B + 2) d.hs)
    (5 * (es.sum + B + 2))
    (sly_mem_xcRec_length _ _)
    (by rw [hR2lr, hR1lr _ (by simp), hRw]
        simp [ldgPost, Function.update_apply, slyLr, slyRg, slyT_inj, slyXcStream_eq_flatten])
    (by rw [hR2rg _ (by simp) (by simp), hRw]
        simp [ldgPost, Function.update_apply, slyLr, slyRg, slyT_inj, sreg_injective.eq_iff])
    (by rw [hR2, Function.update_self, List.length_replicate])
    (by rw [hR2rg _ (by simp) (by simp), hRw, ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp),
          slyRg_tX, synG_sreg]
        simp [slyV₂, slyPV, hly])
    (by rw [hR2lr, hR1lr _ (by simp), hRw,
          ldgPost_lr sly_regs _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp), slyLr_tS,
          synG_of_ne (slyT_out _), synIdle_slyT])
    (by rw [hR2, Function.update_of_ne (by simp [sreg_injective.eq_iff]), hR1w, hwire 6 (by norm_num)])
    (by rw [hR2, Function.update_of_ne (by simp [sreg_injective.eq_iff]), hR1w, hwire 5 (by norm_num)])
  rw [slyXcStream_rev] at hX
  set R3 := Function.update R2 (slyLr .dX)
    (ldlXcStream (prime + Ka) (es.sum + B + 2) (layXcs es ℓ K B).reverse) with hR3
  have hC := lr_uclear (body := body) (R := R3) (sreg (.s 7))
  have hR3s7 : R3 (sreg (.s 7)) = List.replicate (5 * (es.sum + B + 2)) tick := by
    rw [hR3, slyLr_dX, Function.update_of_ne (slyT_ne_sreg _ _), hR2, Function.update_self]
  rw [hR3s7, List.length_replicate] at hC
  refine lr_weaken body (hM.seq (hU.seq (hX.seq hC))) ?_ ?_
  · rw [hR3, hR2, hR1, slyRw'_eq, ← hRw]
    funext z
    simp only [Function.update_apply]
    split_ifs <;> simp_all [hwire 7 (by norm_num)]
  · simp only [slyRevStreamsCost, List.length_map]
    omega

end Rev

/-! ### The file after the restoring machine -/

section Post

variable {Ka : ℕ}

/-- The registers outside the wires after the restoring machine. -/
theorem sly_post_opp_R (io P' str' : List (Fin (prime + Ka + 4))) (N wX : ℕ)
    (hs : Fin 5 → List (Fin (prime + Ka + 4))) (sM sX sM' sX' : List (Fin (prime + Ka + 4))) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (synIdle io P') (slyT 0) sM)
        (slyT 1) sX) (slyT 2) (List.replicate N tick)) (slyT 3) (List.replicate wX tick)) (slyT 0) sM')
        (slyT 1) sX') (ldlH slyRg sxHd 0) (hs 0)) (ldlH slyRg sxHd 1) (hs 1))
        (ldlH slyRg sxHd 2) (hs 2)) (ldlH slyRg sxHd 3) (hs 3)) (ldlH slyRg sxHd 4) (hs 4))
        (slyT 1) []) (slyT 0) []) (reg (BReg := SXReg) .io) str' = slyRo str' P' N wX hs := by
  funext z
  by_cases h0 : z = reg (BReg := SXReg) .io
  · subst h0; simp [slyRo, ldlSetH, synIdle]
  by_cases h1 : z = slyT 0
  · subst h1; simp [slyRo, ldlSetH, synIdle]
  by_cases h2 : z = slyT 1
  · subst h2; simp [slyRo, ldlSetH, synIdle]
  by_cases h3 : z = slyT 2
  · subst h3; simp [slyRo, ldlSetH, synIdle]
  by_cases h4 : z = slyT 3
  · subst h4; simp [slyRo, ldlSetH, synIdle]
  by_cases h5 : z = ldlH slyRg sxHd 0
  · subst h5; simp [slyRo, ldlSetH, synIdle]
  by_cases h6 : z = ldlH slyRg sxHd 1
  · subst h6; simp [slyRo, ldlSetH, synIdle]
  by_cases h7 : z = ldlH slyRg sxHd 2
  · subst h7; simp [slyRo, ldlSetH, synIdle]
  by_cases h8 : z = ldlH slyRg sxHd 3
  · subst h8; simp [slyRo, ldlSetH, synIdle]
  by_cases h9 : z = ldlH slyRg sxHd 4
  · subst h9; simp [slyRo, ldlSetH, synIdle]
  simp [slyRo, ldlSetH, synIdle, Function.update_apply, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- The file after the restoring machine, in canonical form. -/
theorem sly_post_opp {es : List ℕ} {ℓ K w l : ℕ} {L : Equiv.Perm (Fin es.sum)}
    {v₀ : SynW → List (Fin (prime + Ka + 4))} (hv₀ : SynV v₀ es ℓ K w l 0 L)
    (io P' str' : List (Fin (prime + Ka + 4))) (W E N B : ℕ)
    (hs : Fin 5 → List (Fin (prime + Ka + 4))) (mA mB csM csX : List (Fin (prime + Ka + 4))) :
    layDyn slyRg (Function.update (Function.update (Function.update (Function.update (ldlSetH slyRg
      sxHd (slyRw' (synG (synIdle io P') (slyV₂ W E N B v₀)) es ℓ K B) hs) (slyLr .dX) [])
        (slyRg .mA) mA) (slyRg .mB) mB) (slyLr .dM) []) str' csM [] csX [] =
      synG (slyRo str' P' es.sum (es.sum + B + 2) hs) (slyV₃ W E N B v₀ csM csX mA mB) := by
  simp only [layDyn, ldlSetH, ldgPost, slyRw'_eq, slyRg_str, slyRg_cM, slyRg_tM, slyRg_cX, slyRg_tX,
    slyRg_mA, slyRg_mB, slyLr_dM, slyLr_dX, slyLr_cN, slyLr_cW]
  simp only [synG_update, synG_update_out (slyT_out 0), synG_update_out (slyT_out 1),
    synG_update_out (slyT_out 2), synG_update_out (slyT_out 3), synG_update_out (slyH_out 0),
    synG_update_out (slyH_out 1), synG_update_out (slyH_out 2), synG_update_out (slyH_out 3),
    synG_update_out (slyH_out 4), synG_update_out sreg_io_out]
  rw [sly_post_opp_R, sly_post_fwd_v hv₀]

end Post

/-! ### The program and its cost -/

section Prog

variable {Q Ka : ℕ} {U : Type}

/-- **The opposite layout program**: the setup, the writer, the reversal of the streams, the
restoring machine, the cleanup. -/
noncomputable def slyOpp (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) :
    Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq slySetup <|
  .seq (ldgWriter slyRg slyLr slyGr ldxCode) <|
  .seq slyRevStreams <|
  .seq (layUnapply sxHd sxPay sxHd_inj hQ slyRg sly_sw_injective sly_swapT (ldlPrepM slyRg slyLr)
    (ldlPrepX sxHd slyRg slyLr))
    slyClean

/-- The step bound of the writer, the reversal and the restoring machine on the file `R`. -/
noncomputable def slyUnstageCost (Ka : ℕ) (es : List ℕ) (ℓ K B W : ℕ)
    (R : Fin (nT SXReg) → List (Fin (prime + Ka + 4))) : ℕ :=
  ldgWriterCost W es.sum ℓ K es.length B (layB ℓ K) (layBits es ℓ K).length
      (layXcs es ℓ K B).length (ldxAtoms es.sum es.length (layQ ℓ K)) +
    slyRevStreamsCost (layBits es ℓ K).length es.sum (layXcs es ℓ K B).length (es.sum + B + 2) +
    (layXcLoopCost (nT SXReg) 6 es.sum K B slyRg
        (ldlWU slyRg slyLr sxHd (prime + Ka) es.sum (es.sum + B + 2) (slyRw' R es ℓ K B)
          (layXcs es ℓ K B).reverse ((layBits es ℓ K).map Prod.swap).reverse)
        (fun _ => 60 * (es.sum + B + 2) + 75) (layXcs es ℓ K B).reverse +
      layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es ℓ K).length)

/-- The step bound of `slyOpp`. -/
noncomputable def slyOppCost (Ka : ℕ) (es : List ℕ) (ℓ K l w W E : ℕ)
    (v₀ : SynW → List (Fin (prime + Ka + 4))) : ℕ :=
  slySetupCost W es.sum (2 ^ l * w) (2 ^ l) w +
    slyUnstageCost Ka es ℓ K (2 ^ l * w) W (slyR₂ Ka W E es.sum (2 ^ l * w) v₀) +
    slyCleanCost (layBits es ℓ K).length (layXcs es ℓ K (2 ^ l * w)).length es.sum
      (es.sum + 2 ^ l * w + 2) (2 ^ l * w) W

/-- The bank registers of the files of the restoring machine depend on the bank of the base
file only. -/
theorem sly_ldlWU_sw_congr {T t₀ A : ℕ} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}
    (h : LdlRegs rg lr) {hd : Fin 5 → Fin t₀} (hi : Function.Injective hd) (n w : ℕ)
    (R R' : Fin T → List (Fin (A + 4))) (xs : List LayXcD) (bs : List (ℕ × ℕ))
    (hR : ∀ i, R (rg (.sw i)) = R' (rg (.sw i))) (j : ℕ) (i : Fin (swapT t₀)) :
    ldlWU rg lr hd A n w R xs bs j (rg (.sw i)) = ldlWU rg lr hd A n w R' xs bs j (rg (.sw i)) := by
  have hX : ∀ (S S' : Fin T → List (Fin (A + 4))), S (rg (.sw i)) = S' (rg (.sw i)) → ∀ j,
      ldlWX rg lr hd A w S xs j (rg (.sw i)) = ldlWX rg lr hd A w S' xs j (rg (.sw i)) := by
    intro S S' hS j
    cases j with
    | zero => exact hS
    | succ j' =>
        by_cases hk : ∃ k, ldlH rg hd k = rg (.sw i)
        · obtain ⟨k, hk⟩ := hk
          rw [← hk, ldlWX_H hd hi w _ xs j' h k, ldlWX_H hd hi w _ xs j' h k]
        · simp only [not_exists] at hk
          rw [ldlWX_rg hd hi w _ xs _ h hk, ldlWX_rg hd hi w _ xs _ h hk, hS]
  simp only [ldlWU]
  split_ifs with hj
  · exact hX R R' (hR i) j
  · rw [ldlWM_rg n _ bs _ h (by simp) (by simp), ldlWM_rg n _ bs _ h (by simp) (by simp)]
    exact hX R R' (hR i) _

theorem slyRw'_sw (R R' : Fin (nT SXReg) → List (Fin (prime + Ka + 4))) (es : List ℕ) (ℓ K B : ℕ)
    (hR : ∀ i, R (slyRg (.sw i)) = R' (slyRg (.sw i))) (i : Fin (swapT 6)) :
    slyRw' R es ℓ K B (slyRg (.sw i)) = slyRw' R' es ℓ K B (slyRg (.sw i)) := by
  rw [slyRw'_eq, slyRw'_eq, Function.update_of_ne (sly_regs.l.disj _ _),
    Function.update_of_ne (sly_regs.l.disj _ _), Function.update_of_ne (sly_regs.l.disj _ _),
    Function.update_of_ne (sly_regs.l.disj _ _), ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp),
    ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp), hR]

/-- The cost of the restoring stage depends on the bank registers of the file only. -/
theorem slyUnstageCost_congr (es : List ℕ) (ℓ K B W : ℕ)
    (R R' : Fin (nT SXReg) → List (Fin (prime + Ka + 4)))
    (hR : ∀ i, R (slyRg (.sw i)) = R' (slyRg (.sw i))) :
    slyUnstageCost Ka es ℓ K B W R = slyUnstageCost Ka es ℓ K B W R' := by
  have e := sly_layXcLoopCost_congr (T := nT SXReg) (t₀ := 6) (Ka := Ka) es.sum K B slyRg
    (ldlWU slyRg slyLr sxHd (prime + Ka) es.sum (es.sum + B + 2) (slyRw' R es ℓ K B)
      (layXcs es ℓ K B).reverse ((layBits es ℓ K).map Prod.swap).reverse)
    (ldlWU slyRg slyLr sxHd (prime + Ka) es.sum (es.sum + B + 2) (slyRw' R' es ℓ K B)
      (layXcs es ℓ K B).reverse ((layBits es ℓ K).map Prod.swap).reverse)
    (fun j i => sly_ldlWU_sw_congr sly_regs.l sxHd_inj _ _ _ _ _ _ (slyRw'_sw R R' es ℓ K B hR) _ _)
    (fun _ => 60 * (es.sum + B + 2) + 75) (layXcs es ℓ K B).reverse
  unfold slyUnstageCost
  rw [e]

end Prog

/-! ### The layout hypothesis -/

section Lay

variable {Q Ka : ℕ} {U : Type} (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
  (ds : ComplexFramedExecution.Directions)

/-- **The opposite layout.** From the idle file with the records of `Y` on `io` in the physical
order of the layout and `W`, `E` parked, `slyOpp` leaves the records in the natural order (the
hypothesis `hLay` of `synOpp_spec` with `Pk := slyPk W E`), within `slyOppCost`. Word width as
for `slyFwd_lay`. -/
theorem slyOpp_lay {d : ℕ} (a : Fin d → ℕ) {ℓ K l w : ℕ} (H : LayHyp (List.ofFn a) ℓ K)
    (v₀ : SynW → List (Fin (prime + Ka + 4)))
    (hv₀ : SynV v₀ (List.ofFn a) ℓ K w l 0 (layPerm (List.ofFn a) ℓ K)) (hA : 4 ≤ prime + Ka)
    (hw : 1 ≤ w) (W E : ℕ)
    (hE : ∀ i < (List.ofFn a).length, ax (List.ofFn a) i = ℓ - 1 + E / 2 ^ i % 2) (hEW : E < 2 ^ W)
    (hW : ((List.ofFn a).sum + 1) ^ (List.ofFn a).sum < 2 ^ W)
    (hWB : (List.ofFn a).sum + 2 ^ l * w + 4 ≤ W) (hℓW : ℓ < 2 ^ W) :
    ∀ (P₀ : List (Fin (prime + Ka + 4))), slyPk W E P₀ → ∀ (Y : ℕ → Fin (2 ^ l) → GaussianInt),
      LayRuns (layerTable (Ka := Ka) (U := U) hQ ds) (slyOpp hQ)
        (synG (synIdle (cstream (prime + Ka) w (rpStream (cvM a) Y)) P₀) v₀)
        (synG (synIdle (cstream (prime + Ka) w (rpStream (cvM a)
          (fun x => Y ((layRec (layPerm (List.ofFn a) ℓ K)) ⟨x % 2 ^ (List.ofFn a).sum,
            Nat.mod_lt _ (by positivity)⟩)))) P₀) v₀)
        (slyOppCost Ka (List.ofFn a) ℓ K l w W E v₀) := by
  rintro P₀ ⟨P', rfl⟩ Y
  set es := List.ofFn a with hes
  set B := 2 ^ l * w with hB
  set rl := slyRecs (prime + Ka) w (2 ^ es.sum) Y with hrl
  have hB1 : 1 ≤ B := by
    rw [hB]; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by omega))
  have hio : cstream (prime + Ka) w (rpStream (cvM a) Y) = rl.flatten := sly_cstream_rpStream _ _
  rw [hio]
  set R₂ := synG (synIdle rl.flatten P') (slyV₂ W E es.sum B v₀) with hR₂
  have h1 := sg_slySetup (layerTable (Ka := Ka) (U := U) hQ ds) hv₀ rl.flatten P' W E
  have hpre := sly_ldgPre hv₀ P' W E rl
  have hNW : es.sum < W := by omega
  have h2W : 2 ≤ W := by omega
  have h2 := ldg_writer_runs (body := layerTable (Ka := Ka) (U := U) hQ ds) sly_regs H hE hEW hW hNW
    h2W hℓW (by omega) (layXcs es ℓ K B)
    (fun w' st h0 h1 h2 h3 h4 hacc => (ldx_do (A := prime + Ka) (W := W) (w := w') H st h0 h1 h2 h3
      h4 hW hWB hℓW).mono (fun s hs => by rw [hs, hacc, List.append_nil, List.reverse_reverse])
      le_rfl)
    (List.replicate W tick) (by simp) R₂ hpre.tbl hpre.uN hpre.uL hpre.uK hpre.uD hpre.uB hpre.eW
    hpre.dM hpre.dX hpre.cN hpre.cW hpre.cM hpre.cX hpre.tc
  rw [show Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update R₂ (slyLr .dM) (ldlBitStream (prime + Ka) es.sum (layBits es ℓ K)))
        (slyRg .cM) (ldlBitStream (prime + Ka) 1 (layBits es ℓ K))) (slyLr .dX)
        (ldlXcStream (prime + Ka) (es.sum + B + 2) (layXcs es ℓ K B))) (slyRg .cX)
        (List.replicate (layXcs es ℓ K B).length tick)) (slyLr .cN) (List.replicate es.sum tick))
        (slyLr .cW) (List.replicate (es.sum + B + 2) tick) =
      ldgPost slyRg slyLr R₂ es ℓ K B (layXcs es ℓ K B) from rfl] at h2
  have h3 := sg_slyRevStreams (layerTable (Ka := Ka) (U := U) hQ ds) hA hv₀ rl.flatten P' W E B
  set Rw' := slyRw' R₂ es ℓ K B with hRw'
  have hbase : LdlBase slyRg slyLr sxHd sxPay Rw' es.sum B (es.sum + B + 2)
      ((layBits es ℓ K).map Prod.swap).reverse (layXcs es ℓ K B).reverse :=
    (ldgPre_base sly_regs hpre (layXcs es ℓ K B)).slySet sly_regs.l _ _
  have h4 := sly_unstage_exec H (layerTable (Ka := Ka) (U := U) hQ ds) sxHd sxPay sxHd_inj hQ
    sly_regs.l sly_swapT hA sly_hd_pay hB1 le_rfl Rw' hbase rl (by simp [hrl])
    (by simpa [hrl, hB] using slyRecs_mem_length (A := prime + Ka) (w := w) (2 ^ es.sum) Y)
    (slyRecs_lt8 hA _ _) (ldlBitStream (prime + Ka) 1 (layBits es ℓ K))
    (List.replicate (layXcs es ℓ K B).length tick) (length_ldlBitStream_one _) (by simp)
  have e : layDyn slyRg Rw' rl.flatten (ldlBitStream (prime + Ka) 1 (layBits es ℓ K)) []
      (List.replicate (layXcs es ℓ K B).length tick) [] = Rw' := by
    have e1 : Rw' (slyRg .str) = rl.flatten := by
      rw [hRw', slyRw'_eq, Function.update_of_ne (sly_regs.l.disj _ _),
        Function.update_of_ne (sly_regs.l.disj _ _), ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp)]
      exact hpre.str
    have e2 : Rw' (slyRg .cM) = ldlBitStream (prime + Ka) 1 (layBits es ℓ K) := by
      rw [hRw', slyRw'_eq, Function.update_of_ne (sly_regs.l.disj _ _),
        Function.update_of_ne (sly_regs.l.disj _ _)]
      simp [ldgPost, Function.update_apply, sly_regs.l.rl, sly_regs.l.rg_inj.eq_iff]
    have e3 : Rw' (slyRg .tM) = [] := by
      rw [hRw', slyRw'_eq, Function.update_of_ne (sly_regs.l.disj _ _),
        Function.update_of_ne (sly_regs.l.disj _ _), ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp)]
      exact hpre.tM
    have e4 : Rw' (slyRg .cX) = List.replicate (layXcs es ℓ K B).length tick := by
      rw [hRw', slyRw'_eq, Function.update_of_ne (sly_regs.l.disj _ _),
        Function.update_of_ne (sly_regs.l.disj _ _)]
      simp [ldgPost, Function.update_apply, sly_regs.l.rl, sly_regs.l.rg_inj.eq_iff]
    have e5 : Rw' (slyRg .tX) = [] := by
      rw [hRw', slyRw'_eq, Function.update_of_ne (sly_regs.l.disj _ _),
        Function.update_of_ne (sly_regs.l.disj _ _), ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp)]
      exact hpre.tX
    calc layDyn slyRg Rw' rl.flatten (ldlBitStream (prime + Ka) 1 (layBits es ℓ K)) []
          (List.replicate (layXcs es ℓ K B).length tick) [] =
        layDyn slyRg Rw' (Rw' (slyRg .str)) (Rw' (slyRg .cM)) (Rw' (slyRg .tM)) (Rw' (slyRg .cX))
          (Rw' (slyRg .tX)) := by rw [e1, e2, e3, e4, e5]
      _ = Rw' := ldg_layDyn_self Rw'
  rw [e] at h4
  obtain ⟨hs, hhs, eX⟩ := sly_ldlWX_full sly_regs.l sxHd_inj (w := es.sum + B + 2) Rw'
    (layXcs es ℓ K B).reverse (by rw [hRw', slyRw'_eq, Function.update_self])
    (fun k => by
      rw [hRw', slyRw'_eq, Function.update_of_ne (slyH_ne_lr k _),
        Function.update_of_ne (slyH_ne_lr k _)]
      simp only [ldlH]
      rw [ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp)]
      exact hpre.hdr k)
    (fun d hd => ldl_layXcs_hs_le H B _ le_rfl d (List.mem_reverse.1 hd))
  set Rx := Function.update (ldlSetH slyRg sxHd Rw' hs) (slyLr .dX) [] with hRx
  have hRxH : ∀ y : LayReg 6, (∀ j, y ≠ .sw j) → Rx (slyRg y) = Rw' (slyRg y) := fun y hy => by
    rw [hRx, Function.update_of_ne (sly_regs.l.disj _ _),
      ldlSetH_of_ne slyRg_injective sxHd_inj _ _ (fun k => slyH_ne_rg k hy)]
  obtain ⟨mA, mB, hmA, hmB, eM⟩ := sly_ldlWM_full sly_regs.l (n := es.sum) Rx
    ((layBits es ℓ K).map Prod.swap).reverse
    (by rw [hRx, Function.update_of_ne (sly_regs.l.lr_inj.ne (by simp)),
          ldlSetH_of_ne slyRg_injective sxHd_inj _ _ (fun k => slyH_ne_lr k _), hRw', slyRw'_eq,
          Function.update_of_ne (sly_regs.l.lr_inj.ne (by simp)), Function.update_self])
    (by rw [hRxH _ (by simp), hRw', slyRw'_eq, Function.update_of_ne (sly_regs.l.disj _ _),
          Function.update_of_ne (sly_regs.l.disj _ _), ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp)]
        exact hpre.mA)
    (by rw [hRxH _ (by simp), hRw', slyRw'_eq, Function.update_of_ne (sly_regs.l.disj _ _),
          Function.update_of_ne (sly_regs.l.disj _ _), ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp)]
        exact hpre.mB)
  have hlen : (layXcs es ℓ K B).length + (layBits es ℓ K).length =
      (layXcs es ℓ K B).reverse.length + ((layBits es ℓ K).map Prod.swap).reverse.length := by simp
  rw [hlen, ldlWU_M, eX, eM, hRx, hRw', hR₂, sly_post_opp hv₀] at h4
  have h5 := sg_slyClean (layerTable (Ka := Ka) (U := U) hQ ds) hv₀
    (moveRecs (layRec (layPerm es ℓ K)).symm rl).flatten P' W E es.sum (es.sum + B + 2) B
    (layBits es ℓ K).length (layXcs es ℓ K B).length hs hhs
    (ldlBitStream (prime + Ka) 1 (layBits es ℓ K)) (List.replicate (layXcs es ℓ K B).length tick)
    mA mB (le_of_eq (length_ldlBitStream_one _)) (by simp) hmA hmB
  refine lr_weaken _ (h1.seq (h2.seq (h3.seq (h4.seq h5)))) ?_ ?_
  · rw [hrl, sly_moveRecs_opp]
  · have e := slyUnstageCost_congr (Ka := Ka) es ℓ K B W R₂ (slyR₂ Ka W E es.sum B v₀)
      (fun i => by rw [hR₂, slyR₂, synG_synIdle_sw, synG_synIdle_sw])
    simp only [slyOppCost, ← hB]
    rw [← e]
    simp only [slyUnstageCost, hRw', hR₂, ← hes]
    omega

end Lay

end IntegerMultBounds.MathlibTM2.Fast
