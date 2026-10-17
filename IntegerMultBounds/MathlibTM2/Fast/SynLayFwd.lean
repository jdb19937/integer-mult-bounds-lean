module

public import IntegerMultBounds.MathlibTM2.Fast.SynLayPre
import IntegerMultBounds.MathlibTM2.Fast.SynLayKit
public import IntegerMultBounds.MathlibTM2.Fast.ConvSpec
public import IntegerMultBounds.MathlibTM2.Fast.SynMath
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The forward layout program of the synthetic transforms

Paper §6, proof of `lem:synthetic-transform-cost`. The program `slyFwd` discharges the layout
hypothesis `hLay` of `synFwd_spec` (`Fast/SynFwd.lean`): the setup (`slySetup`), the layout
stage `ldgStage … ldxCode` (`Fast/LoadLayoutGen.lean`: the writer of the description streams,
then `layApply`), and the cleanup (`slyClean`). It is one fixed text; the sizes `N, ℓ, K, D`
come from the persistent wires, `W` and `E` from `park` (`slyPk W E`), `B = 2^l w` from the
wires `p .r`, `p .w`.

* `sly_post_fwd`: the file after the layout stage in the canonical form `synG (slyRo …)
  (slyV₃ …)` of the cleanup.
* `slyStageCost`: the cost of the layout stage on the file `R` (the bank registers of `R`
  only matter, `slyStageCost_congr`); `slyFwdCost`: the cost of `slyFwd`, on the canonical
  file `slyR₂`.
* `slyFwd_lay`: the hypothesis `hLay` of `synFwd_spec` for `slyFwd`, `Pk := slyPk W E`,
  `cL := slyFwdCost …`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.Rounds
  IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


/-! ### The file after the layout stage -/

section Post

variable {Ka : ℕ}

/-- The registers outside the wires after the forward layout stage. -/
theorem sly_post_fwd_R (io P' str' : List (Fin (prime + Ka + 4))) (N wX : ℕ)
    (hs : Fin 5 → List (Fin (prime + Ka + 4))) (sM sX : List (Fin (prime + Ka + 4))) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (synIdle io P') (slyT 0) sM) (slyT 1) sX) (slyT 2)
        (List.replicate N tick)) (slyT 3) (List.replicate wX tick)) (slyT 0) [])
        (ldlH slyRg sxHd 0) (hs 0)) (ldlH slyRg sxHd 1) (hs 1)) (ldlH slyRg sxHd 2) (hs 2))
        (ldlH slyRg sxHd 3) (hs 3)) (ldlH slyRg sxHd 4) (hs 4)) (slyT 1) [])
        (reg (BReg := SXReg) .io) str' = slyRo str' P' N wX hs := by
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

/-- The wires after the forward layout stage. -/
theorem sly_post_fwd_v {es : List ℕ} {ℓ K w l : ℕ} {L : Equiv.Perm (Fin es.sum)}
    {v₀ : SynW → List (Fin (prime + Ka + 4))} (hv₀ : SynV v₀ es ℓ K w l 0 L) (W E N B : ℕ)
    (mA mB csM csX sM sX : List (Fin (prime + Ka + 4))) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (slyV₂ W E N B v₀) (.ly 19) sM)
        (.ly 21) sX) (.ly 14) mA) (.ly 15) mB) (.ly 19) csM) (.ly 20) []) (.ly 21) csX) (.ly 22) [] =
      slyV₃ W E N B v₀ csM csX mA mB := by
  have hly := hv₀.hly
  funext x
  rcases x with a | i | a | i
  · simp [slyV₃, slyV₂, slyPV]
  · simp only [slyV₃, Function.update_apply, SynW.ly.injEq]
    split_ifs <;> simp_all [slyV₂, slyPV]
  · simp [slyV₃, slyV₂, slyPV]
  · simp [slyV₃, slyV₂, slyPV]

/-- The file after the forward layout stage, in canonical form. -/
theorem sly_post_fwd {es : List ℕ} {ℓ K w l : ℕ} {L : Equiv.Perm (Fin es.sum)}
    {v₀ : SynW → List (Fin (prime + Ka + 4))} (hv₀ : SynV v₀ es ℓ K w l 0 L)
    (io P' str' : List (Fin (prime + Ka + 4))) (W E N B : ℕ) (xs : List LayXcD)
    (hs : Fin 5 → List (Fin (prime + Ka + 4))) (mA mB csM csX : List (Fin (prime + Ka + 4))) :
    layDyn slyRg (Function.update (ldlSetH slyRg sxHd (Function.update (Function.update
      (Function.update (ldgPost slyRg slyLr (synG (synIdle io P') (slyV₂ W E N B v₀)) es ℓ K B xs)
        (slyRg .mA) mA) (slyRg .mB) mB) (slyLr .dM) []) hs) (slyLr .dX) []) str' csM [] csX [] =
      synG (slyRo str' P' es.sum (es.sum + B + 2) hs) (slyV₃ W E N B v₀ csM csX mA mB) := by
  simp only [layDyn, ldlSetH, ldgPost, slyRg_str, slyRg_cM, slyRg_tM, slyRg_cX, slyRg_tX, slyRg_mA,
    slyRg_mB, slyLr_dM, slyLr_dX, slyLr_cN, slyLr_cW]
  simp only [synG_update, synG_update_out (slyT_out 0), synG_update_out (slyT_out 1),
    synG_update_out (slyT_out 2), synG_update_out (slyT_out 3), synG_update_out (slyH_out 0),
    synG_update_out (slyH_out 1), synG_update_out (slyH_out 2), synG_update_out (slyH_out 3),
    synG_update_out (slyH_out 4), synG_update_out sreg_io_out]
  rw [sly_post_fwd_R, sly_post_fwd_v hv₀]

end Post

/-! ### The program and its cost -/

section Prog

variable {Q Ka : ℕ} {U : Type}

/-- **The forward layout program**: the setup, the layout stage (writer and `layApply`), the
cleanup. -/
noncomputable def slyFwd (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) :
    Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq slySetup (.seq (ldgStage sxHd sxPay sxHd_inj hQ slyRg sly_sw_injective sly_swapT slyLr slyGr
    ldxCode) slyClean)

/-- The step bound of the layout stage on the file `R` (`ldLayGenStage_exec`). -/
noncomputable def slyStageCost (Ka : ℕ) (es : List ℕ) (ℓ K B W : ℕ)
    (R : Fin (nT SXReg) → List (Fin (prime + Ka + 4))) : ℕ :=
  ldgWriterCost W es.sum ℓ K es.length B (layB ℓ K) (layBits es ℓ K).length
      (layXcs es ℓ K B).length (ldxAtoms es.sum es.length (layQ ℓ K)) +
    (layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es ℓ K).length +
      layXcLoopCost (nT SXReg) 6 es.sum K B slyRg
        (fun j => ldlW slyRg slyLr sxHd (prime + Ka) es.sum (es.sum + B + 2)
          (ldgPost slyRg slyLr R es ℓ K B (layXcs es ℓ K B)) (layBits es ℓ K) (layXcs es ℓ K B)
          ((layBits es ℓ K).length + j)) (fun _ => 60 * (es.sum + B + 2) + 75)
        (layXcs es ℓ K B))

/-- The canonical file of the layout stage: empty `io` and `park`, the wires `slyV₂`. -/
noncomputable def slyR₂ (Ka : ℕ) (W E N B : ℕ) (v₀ : SynW → List (Fin (prime + Ka + 4))) :
    Fin (nT SXReg) → List (Fin (prime + Ka + 4)) :=
  synG (synIdle [] []) (slyV₂ W E N B v₀)

/-- The step bound of `slyFwd`. -/
noncomputable def slyFwdCost (Ka : ℕ) (es : List ℕ) (ℓ K l w W E : ℕ)
    (v₀ : SynW → List (Fin (prime + Ka + 4))) : ℕ :=
  slySetupCost W es.sum (2 ^ l * w) (2 ^ l) w +
    slyStageCost Ka es ℓ K (2 ^ l * w) W (slyR₂ Ka W E es.sum (2 ^ l * w) v₀) +
    slyCleanCost (layBits es ℓ K).length (layXcs es ℓ K (2 ^ l * w)).length es.sum
      (es.sum + 2 ^ l * w + 2) (2 ^ l * w) W

/-- The cost of the layout stage depends on the bank registers of the file only. -/
theorem slyStageCost_congr (es : List ℕ) (ℓ K B W : ℕ)
    (R R' : Fin (nT SXReg) → List (Fin (prime + Ka + 4)))
    (hR : ∀ i, R (slyRg (.sw i)) = R' (slyRg (.sw i))) :
    slyStageCost Ka es ℓ K B W R = slyStageCost Ka es ℓ K B W R' := by
  have e := sly_layXcLoopCost_congr (T := nT SXReg) (t₀ := 6) (Ka := Ka) es.sum K B slyRg
    (fun j => ldlW slyRg slyLr sxHd (prime + Ka) es.sum (es.sum + B + 2)
      (ldgPost slyRg slyLr R es ℓ K B (layXcs es ℓ K B)) (layBits es ℓ K) (layXcs es ℓ K B)
      ((layBits es ℓ K).length + j))
    (fun j => ldlW slyRg slyLr sxHd (prime + Ka) es.sum (es.sum + B + 2)
      (ldgPost slyRg slyLr R' es ℓ K B (layXcs es ℓ K B)) (layBits es ℓ K) (layXcs es ℓ K B)
      ((layBits es ℓ K).length + j))
    (fun j i => sly_ldlW_sw_congr sly_regs.l sxHd_inj _ _ _ _ _ _ (fun i => by
      rw [ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp),
        ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp), hR]) _ _)
    (fun _ => 60 * (es.sum + B + 2) + 75) (layXcs es ℓ K B)
  unfold slyStageCost
  rw [e]

theorem synG_synIdle_sw (io P₀ : List (Fin (prime + Ka + 4))) (v : SynW → List (Fin (prime + Ka + 4)))
    (i : Fin (swapT 6)) : synG (synIdle io P₀) v (slyRg (.sw i)) = [] := by
  rw [synG_of_ne (slyRg_sw_out i), synIdle_sw]

end Prog

/-! ### The layout hypothesis -/

section Lay

variable {Q Ka : ℕ} {U : Type} (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
  (ds : ComplexFramedExecution.Directions)

/-- **The forward layout.** From the idle file with the records of `Z` on `io` and `W`, `E`
parked, `slyFwd` leaves the records in the physical order of the layout `L = layPerm es ℓ K`
(the hypothesis `hLay` of `synFwd_spec` with `Pk := slyPk W E`), within `slyFwdCost`. Word
width: `(N + 1)^N < 2^W`, `N + 2^l w + 4 ≤ W`, `ℓ < 2^W`, `E < 2^W`; the axis word `E` has bit
`i` set exactly on the long axes. -/
theorem slyFwd_lay {d : ℕ} (a : Fin d → ℕ) {ℓ K l w : ℕ} (H : LayHyp (List.ofFn a) ℓ K)
    (v₀ : SynW → List (Fin (prime + Ka + 4)))
    (hv₀ : SynV v₀ (List.ofFn a) ℓ K w l 0 (layPerm (List.ofFn a) ℓ K)) (hA : 4 ≤ prime + Ka)
    (hw : 1 ≤ w) (W E : ℕ)
    (hE : ∀ i < (List.ofFn a).length, ax (List.ofFn a) i = ℓ - 1 + E / 2 ^ i % 2) (hEW : E < 2 ^ W)
    (hW : ((List.ofFn a).sum + 1) ^ (List.ofFn a).sum < 2 ^ W)
    (hWB : (List.ofFn a).sum + 2 ^ l * w + 4 ≤ W) (hℓW : ℓ < 2 ^ W) :
    ∀ (P₀ : List (Fin (prime + Ka + 4))), slyPk W E P₀ → ∀ (Z : ℕ → Fin (2 ^ l) → GaussianInt),
      LayRuns (layerTable (Ka := Ka) (U := U) hQ ds) (slyFwd hQ)
        (synG (synIdle (cstream (prime + Ka) w (rpStream (cvM a) Z)) P₀) v₀)
        (synG (synIdle (cstream (prime + Ka) w (rpStream (cvM a)
          (fun m => Z (synPi (layPerm (List.ofFn a) ℓ K) m)))) P₀) v₀)
        (slyFwdCost Ka (List.ofFn a) ℓ K l w W E v₀) := by
  rintro P₀ ⟨P', rfl⟩ Z
  set es := List.ofFn a with hes
  set B := 2 ^ l * w with hB
  set rl := slyRecs (prime + Ka) w (2 ^ es.sum) Z with hrl
  have hB1 : 1 ≤ B := by
    rw [hB]; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by omega))
  have hio : cstream (prime + Ka) w (rpStream (cvM a) Z) = rl.flatten := sly_cstream_rpStream _ _
  rw [hio]
  have h1 := sg_slySetup (layerTable (Ka := Ka) (U := U) hQ ds) hv₀ rl.flatten P' W E
  have hpre := sly_ldgPre hv₀ P' W E rl
  have h2 := ldLayGenStage_exec H (layerTable (Ka := Ka) (U := U) hQ ds) sxHd sxPay sxHd_inj hQ
    sly_regs sly_swapT hA sly_hd_pay hB1 hE hEW hW hWB hℓW _ _ rl hpre (by simp [hrl])
    (by simpa [hrl, hB] using slyRecs_mem_length (A := prime + Ka) (w := w) (2 ^ es.sum) Z)
    (slyRecs_lt8 hA _ _)
  set R₂ := synG (synIdle rl.flatten P') (slyV₂ W E es.sum B v₀) with hR₂
  set Rw := ldgPost slyRg slyLr R₂ es ℓ K B (layXcs es ℓ K B) with hRw
  obtain ⟨mA, mB, hmA, hmB, eM⟩ := sly_ldlWM_full sly_regs.l (n := es.sum) Rw (layBits es ℓ K)
    (by simp [hRw, ldgPost, sly_regs.l.lr',
      sly_regs.l.lr_inj.eq_iff])
    (by rw [hRw, ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp)]; exact hpre.mA)
    (by rw [hRw, ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp)]; exact hpre.mB)
  set Rm := Function.update (Function.update (Function.update Rw (slyRg .mA) mA) (slyRg .mB) mB)
    (slyLr .dM) [] with hRm
  obtain ⟨hs, hhs, eX⟩ := sly_ldlWX_full sly_regs.l sxHd_inj (w := es.sum + B + 2) Rm
    (layXcs es ℓ K B)
    (by rw [hRm, slyLr_dX, slyLr_dM, slyRg_mB, slyRg_mA,
          Function.update_of_ne (by simp : slyT 1 ≠ slyT 0),
          Function.update_of_ne (Ne.symm (slyT_ne_sreg (.ly 15) 1)),
          Function.update_of_ne (Ne.symm (slyT_ne_sreg (.ly 14) 1)), hRw]
        simp [ldgPost, slyLr, slyRg])
    (fun k => by
      rw [hRm, Function.update_of_ne (slyH_ne_lr k _), Function.update_of_ne (slyH_ne_rg k (by simp)),
        Function.update_of_ne (slyH_ne_rg k (by simp)), hRw]
      simp only [ldlH]
      rw [ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp)]
      exact hpre.hdr k)
    (ldl_layXcs_hs_le H B _ le_rfl)
  rw [ldlW_X, eM, eX, hRm, hRw, hR₂, sly_post_fwd hv₀] at h2
  have h3 := sg_slyClean (layerTable (Ka := Ka) (U := U) hQ ds) hv₀
    (moveRecs (layRec (layPerm es ℓ K)) rl).flatten P' W E es.sum (es.sum + B + 2) B
    (layBits es ℓ K).length (layXcs es ℓ K B).length hs hhs
    (ldlBitStream (prime + Ka) 1 (layBits es ℓ K)) (List.replicate (layXcs es ℓ K B).length tick)
    mA mB (le_of_eq (length_ldlBitStream_one _)) (by simp) hmA hmB
  refine lr_weaken _ (h1.seq (h2.seq h3)) ?_ ?_
  · rw [hrl, sly_moveRecs_fwd]
  · have e := slyStageCost_congr (Ka := Ka) es ℓ K B W
      (synG (synIdle rl.flatten P') (slyV₂ W E es.sum B v₀)) (slyR₂ Ka W E es.sum B v₀)
      (fun i => by rw [slyR₂, synG_synIdle_sw, synG_synIdle_sw])
    simp only [slyFwdCost, ← hB]
    rw [← e]
    simp only [slyStageCost]
    omega

end Lay

end IntegerMultBounds.MathlibTM2.Fast
