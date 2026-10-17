module

import IntegerMultBounds.MathlibTM2.Fast.SynLayKit
public import IntegerMultBounds.MathlibTM2.Fast.SynLayRegs
import IntegerMultBounds.MathlibTM2.Fast.SynFwd
public import IntegerMultBounds.MathlibTM2.Fast.SynRound
public import IntegerMultBounds.MathlibTM2.Fast.LoadLayoutGen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Setup and cleanup of the layout programs of the synthetic transforms

Paper §6, proof of `lem:synthetic-transform-cost`. The parts shared by the forward and the
opposite layout programs (`Fast/SynLayFwd.lean`, `Fast/SynLayOpp.lean`), on the register maps
of `Fast/SynLayRegs.lean`.

## Parameters

The writer of the description streams needs the word width `W` and the axis word `E` of the
long axes, which the transform wires do not hold (`SynV`): they are parked on `park`
(`slyPark W E P'`, the park predicate `slyPk W E`) and restored onto the wires `s 1`, `s 2`
(`slyPV`). The record length `B = 2^l w` is computed from the wires `p .r`, `p .w`.

* `slySetup`: unpark `W`, `E`; `s 0 := B`; `cnt := 2^N` ticks; `fld := 0` of `N` bits;
  `ctrB := B` (`sg_slySetup`, the wires `slyV₂`); `sly_ldgPre`: the file is then a `LdgPre`
  file of the layout stage.
* `slyRo`, `slyV₃`: the file after the layout machine (headers `hs`, word counters, masks,
  loop counters); `slyClean`: clear them and park `W`, `E` again (`sg_slyClean`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


/-! ### Registers -/

section Regs

variable {A : ℕ}

theorem slyT_eq (c : Fin 64) : slyT c = reg (BReg := SXReg) (.wtmp (wireOf (Fin.castLE sly_NW c))) :=
  rfl

@[simp] theorem synIdle_slyT (io P₀ : List (Fin (A + 4))) (c : Fin 64) :
    synIdle io P₀ (slyT c) = [] := by
  simp [synIdle, slyT_eq]

@[simp] theorem synIdle_sw (io P₀ : List (Fin (A + 4))) (j : Fin (swapT 6)) :
    synIdle io P₀ (slyRg (.sw j)) = [] := by
  simp [synIdle, slyRg]

theorem slyRg_sw_out (j : Fin (swapT 6)) : ∀ x, sreg x ≠ slyRg (.sw j) := fun x => by
  simp [slyRg, sreg_eq]

theorem slyH_out (k : Fin 5) : ∀ x, sreg x ≠ ldlH slyRg sxHd k := slyRg_sw_out _

@[simp] theorem sreg_eq_io_iff (x : SynW) : sreg x = reg (BReg := SXReg) .io ↔ False :=
  ⟨fun h => sreg_ne_reg (by simp) h, False.elim⟩

@[simp] theorem sreg_eq_park_iff (x : SynW) : sreg x = reg (BReg := SXReg) .park ↔ False :=
  ⟨fun h => sreg_ne_reg (by simp) h, False.elim⟩

@[simp] theorem sreg_eq_bc_iff (x : SynW) (b : SXReg) : sreg x = reg (BReg := SXReg) (.bc b) ↔ False :=
  ⟨fun h => sreg_ne_reg (by simp) h, False.elim⟩

@[simp] theorem sreg_eq_sw_iff (x : SynW) (j : Fin (swapT 6)) : sreg x = slyRg (.sw j) ↔ False :=
  ⟨slyRg_sw_out j x, False.elim⟩

@[simp] theorem sreg_eq_slyH_iff (x : SynW) (k : Fin 5) : sreg x = ldlH slyRg sxHd k ↔ False :=
  ⟨slyH_out k x, False.elim⟩

theorem slyH_ne_slyT (k : Fin 5) (c : Fin 64) : ldlH slyRg sxHd k ≠ slyT c := by
  simp [ldlH, slyRg, slyT_eq]

theorem slyH_ne_io (k : Fin 5) : ldlH slyRg sxHd k ≠ reg (BReg := SXReg) .io := by
  simp [ldlH, slyRg]

theorem slyH_ne_park (k : Fin 5) : ldlH slyRg sxHd k ≠ reg (BReg := SXReg) .park := by
  simp [ldlH, slyRg]

theorem slyT_ne_io (c : Fin 64) : slyT c ≠ reg (BReg := SXReg) .io := by simp [slyT_eq]

theorem slyT_ne_park (c : Fin 64) : slyT c ≠ reg (BReg := SXReg) .park := by simp [slyT_eq]

theorem slyH_injective : Function.Injective (ldlH slyRg sxHd) :=
  ldlH_injective slyRg_injective sxHd_inj

@[simp] theorem slyH_eq_slyH_iff (k k' : Fin 5) : ldlH slyRg sxHd k = ldlH slyRg sxHd k' ↔ k = k' :=
  slyH_injective.eq_iff

@[simp] theorem slyT_eq_slyH_iff (c : Fin 64) (k : Fin 5) : slyT c = ldlH slyRg sxHd k ↔ False :=
  ⟨fun h => slyH_ne_slyT k c h.symm, False.elim⟩

@[simp] theorem slyH_eq_slyT_iff (k : Fin 5) (c : Fin 64) : ldlH slyRg sxHd k = slyT c ↔ False :=
  ⟨slyH_ne_slyT k c, False.elim⟩

@[simp] theorem slyT_eq_io_iff (c : Fin 64) : slyT c = reg (BReg := SXReg) .io ↔ False :=
  ⟨slyT_ne_io c, False.elim⟩

@[simp] theorem io_eq_slyT_iff (c : Fin 64) : reg (BReg := SXReg) .io = slyT c ↔ False :=
  ⟨fun h => slyT_ne_io c h.symm, False.elim⟩

@[simp] theorem slyT_eq_park_iff (c : Fin 64) : slyT c = reg (BReg := SXReg) .park ↔ False :=
  ⟨slyT_ne_park c, False.elim⟩

@[simp] theorem park_eq_slyT_iff (c : Fin 64) : reg (BReg := SXReg) .park = slyT c ↔ False :=
  ⟨fun h => slyT_ne_park c h.symm, False.elim⟩

@[simp] theorem slyH_eq_io_iff (k : Fin 5) : ldlH slyRg sxHd k = reg (BReg := SXReg) .io ↔ False :=
  ⟨slyH_ne_io k, False.elim⟩

@[simp] theorem io_eq_slyH_iff (k : Fin 5) : reg (BReg := SXReg) .io = ldlH slyRg sxHd k ↔ False :=
  ⟨fun h => slyH_ne_io k h.symm, False.elim⟩

@[simp] theorem slyH_eq_park_iff (k : Fin 5) : ldlH slyRg sxHd k = reg (BReg := SXReg) .park ↔ False :=
  ⟨slyH_ne_park k, False.elim⟩

@[simp] theorem park_eq_slyH_iff (k : Fin 5) : reg (BReg := SXReg) .park = ldlH slyRg sxHd k ↔ False :=
  ⟨fun h => slyH_ne_park k h.symm, False.elim⟩

theorem slyH_ne_rg (k : Fin 5) {y : LayReg 6} (hy : ∀ j, y ≠ .sw j) : ldlH slyRg sxHd k ≠ slyRg y :=
  fun e => hy _ (slyRg_injective e).symm

theorem slyH_ne_lr (k : Fin 5) (y : LdlReg) : ldlH slyRg sxHd k ≠ slyLr y := sly_regs.l.disj _ _

theorem sreg_io_out : ∀ z, sreg z ≠ reg (BReg := SXReg) .io := fun z => sreg_ne_reg (by simp)

theorem slyRg_str : slyRg .str = reg (BReg := SXReg) .io := rfl
theorem slyRg_mA : slyRg .mA = sreg (.ly 14) := rfl
theorem slyRg_mB : slyRg .mB = sreg (.ly 15) := rfl
theorem slyRg_cM : slyRg .cM = sreg (.ly 19) := rfl
theorem slyRg_tM : slyRg .tM = sreg (.ly 20) := rfl
theorem slyRg_cX : slyRg .cX = sreg (.ly 21) := rfl
theorem slyRg_tX : slyRg .tX = sreg (.ly 22) := rfl
theorem slyRg_tmp : slyRg .tmp = sreg (.ly 11) := rfl
theorem slyLr_dM : slyLr .dM = slyT 0 := rfl
theorem slyLr_dX : slyLr .dX = slyT 1 := rfl
theorem slyLr_cN : slyLr .cN = slyT 2 := rfl
theorem slyLr_cW : slyLr .cW = slyT 3 := rfl
theorem slyLr_tA : slyLr .tA = slyT 4 := rfl
theorem slyLr_tB : slyLr .tB = slyT 5 := rfl
theorem slyLr_tS : slyLr .tS = slyT 6 := rfl

theorem sly_hd_pay : ∀ k, sxHd k ≠ sxPay := fun k h => by
  have := congrArg Fin.val h
  simp [sxHd, sxPay] at this
  omega

end Regs

/-! ### The parked parameters -/

section Park

variable {A : ℕ}

/-- The wires with the word width `W` on `s 1` and the axis word `E` on `s 2`. -/
def slyPV (W E : ℕ) (v₀ : SynW → List (Fin (A + 4))) : SynW → List (Fin (A + 4)) :=
  Function.update (Function.update v₀ (.s 1) (List.replicate W tick)) (.s 2) (binSyms W E)

/-- The parked parameters: the axis word `E` and the word width `W` under markers, above `P'`. -/
def slyPark (W E : ℕ) (P' : List (Fin (A + 4))) : List (Fin (A + 4)) :=
  blank :: (binSyms W E).reverse ++ blank :: List.replicate W tick ++ blank :: P'

/-- The park predicate of the layout programs: `park` holds `W` and `E` above anything. -/
def slyPk (W E : ℕ) (P₀ : List (Fin (A + 4))) : Prop := ∃ P', P₀ = slyPark W E P'

theorem slyPark_eq (W E : ℕ) (v₀ : SynW → List (Fin (A + 4))) (P' : List (Fin (A + 4))) :
    slyPark W E P' = synStkW (slyPV W E v₀) blank [.s 1, .s 2] ++ blank :: P' := by
  simp [slyPark, synStkW, slyPV]

theorem slyPV_clr (v₀ : SynW → List (Fin (A + 4))) (hs : ∀ i, v₀ (.s i) = []) (W E : ℕ) :
    synClrW (slyPV W E v₀) [.s 1, .s 2] = v₀ := by
  funext x
  simp only [synClrW, List.mem_cons, List.not_mem_nil, or_false]
  split_ifs with h
  · rcases h with rfl | rfl <;> exact (hs _).symm
  · simp only [slyPV, Function.update_apply]
    split_ifs <;> simp_all

theorem slyPV_blank (v₀ : SynW → List (Fin (A + 4))) (W E : ℕ) :
    ∀ x ∈ [SynW.s 1, .s 2], blank ∉ slyPV W E v₀ x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · simp only [slyPV, Function.update_apply, Fin.reduceEq, 
      SynW.s.injEq, ↓reduceIte, List.mem_replicate, not_and]
    intro _ h
    exact tick_ne_blank h.symm
  · simp only [slyPV, Function.update_self, binSyms, List.mem_ofFn, not_exists]
    intro t h
    exact rp_bitSymbol_ne_blank _ h

end Park

/-! ### The setup -/

section Setup

variable {Q A : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q A U)

/-- Unpark `W`, `E`; `s 0 := |p .r| |p .w|`; `cnt := 2^N` ticks (`N = |p .N|`); `fld := binSyms
N 0`; `ctrB := |s 0|`. -/
noncomputable def slySetup : Pr P (nT SXReg) Q A U :=
  .seq (synUnstash (lreg .park) blank ([SynW.s 1, .s 2].map sreg)) <|
  .seq (synMulR (sreg (.p .r)) (sreg (.p .w)) (sreg (.s 0)) (sreg (.s 3)) (sreg (.s 4))) <|
  .seq (synPush (sreg (.ly 10)) tick) <|
  .seq (upow2 (sreg (.p .N)) (sreg (.ly 10)) (sreg (.s 3)) (sreg (.s 4))) <|
  .seq (zeroBits (sreg (.p .N)) (sreg (.ly 13)) (sreg (.s 3)))
    (ucopy (sreg (.s 0)) (sreg (.ly 9)) (sreg (.s 3)))

/-- The wires after the setup. -/
def slyV₂ (W E N B : ℕ) (v₀ : SynW → List (Fin (A + 4))) : SynW → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (slyPV W E v₀) (.s 0)
    (List.replicate B tick)) (.ly 10) (List.replicate (2 ^ N) tick)) (.ly 13) (binSyms N 0))
    (.ly 9) (List.replicate B tick)

/-- The step bound of the setup. -/
def slySetupCost (W N B r w : ℕ) : ℕ :=
  (4 * W + 8) + synMulRCost r w + 1 + (4 * 2 ^ N + 9 * N + 4) + (4 * N + 4) + (4 * B + 4)

/-- **The setup.** From the idle file with `W`, `E` parked, to the idle file with the parameters
of the layout stage on the wires. -/
theorem sg_slySetup {es : List ℕ} {ℓ K w l : ℕ} {L : Equiv.Perm (Fin es.sum)}
    {v₀ : SynW → List (Fin (A + 4))} (hv₀ : SynV v₀ es ℓ K w l 0 L) (io P' : List (Fin (A + 4)))
    (W E : ℕ) :
    LayRuns body slySetup (synG (synIdle io (slyPark W E P')) v₀)
      (synG (synIdle io P') (slyV₂ W E es.sum (2 ^ l * w) v₀))
      (slySetupCost W es.sum (2 ^ l * w) (2 ^ l) w) := by
  have hs := hv₀.hs
  have hly := hv₀.hly
  have h1 := sg_synUnstash body (R := synIdle io P') (v := slyPV W E v₀) (pk := lreg .park)
    (lreg_out (by simp)) blank [.s 1, .s 2] P' (by decide) (slyPV_blank v₀ W E)
  rw [synIdle_update_park, synIdle_update_park, slyPV_clr v₀ hs, ← slyPark_eq] at h1
  have h2 := sgU_mulR body (R := synIdle io P') (v := slyPV W E v₀) (a := .p .r) (b := .p .w)
    (c := .s 0) (t₁ := .s 3) (t₂ := .s 4) (x := 2 ^ l) (y := w) (z := 0) (by decide) (by simp [slyPV, hs])
    (by simp [slyPV, hs]) (by simp [slyPV, hv₀.hr]) (by simp [slyPV, hv₀.hw])
    (by simp [slyPV, hs])
  have h3 := sgU_push body (R := synIdle io P') (a := .ly 10) (y := 0)
    (v := Function.update (slyPV W E v₀) (.s 0) (List.replicate (2 ^ l * w + 0) tick))
    (by simp [slyPV, hly])
  have h4 := sgU_pow2 body (R := synIdle io P') (a := .p .N) (b := .ly 10) (t₁ := .s 3)
    (t₂ := .s 4) (x := es.sum) (y := 1)
    (v := Function.update (Function.update (slyPV W E v₀) (.s 0)
      (List.replicate (2 ^ l * w + 0) tick)) (.ly 10) (List.replicate (0 + 1) tick))
    (by decide) (by simp [slyPV, hs]) (by simp [slyPV, hs]) (by simp [slyPV, hv₀.hN]) (by simp)
  have h5 := sgR_zeroBits body (R := synIdle io P') (a := .p .N) (b := .ly 13) (t := .s 3)
    (x := es.sum) (l := [])
    (v := Function.update (Function.update (Function.update (slyPV W E v₀) (.s 0)
      (List.replicate (2 ^ l * w + 0) tick)) (.ly 10) (List.replicate (0 + 1) tick)) (.ly 10)
      (List.replicate (2 ^ es.sum * 1) tick))
    (by decide) (by decide) (by decide) (by simp [slyPV, hs]) (by simp [slyPV, hv₀.hN])
    (by simp [slyPV, hly])
  have h6 := sgU_copy body (R := synIdle io P') (a := .s 0) (b := .ly 9) (t := .s 3)
    (x := 2 ^ l * w) (y := 0)
    (v := Function.update (Function.update (Function.update (Function.update (slyPV W E v₀)
      (.s 0) (List.replicate (2 ^ l * w + 0) tick)) (.ly 10) (List.replicate (0 + 1) tick))
      (.ly 10) (List.replicate (2 ^ es.sum * 1) tick)) (.ly 13) (binSyms es.sum 0 ++ []))
    (by decide) (by decide) (by decide) (by simp [slyPV, hs]) (by simp) (by simp [slyPV, hly])
  refine lr_weaken body (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))) ?_ ?_
  · refine congrArg (synG _) ?_
    funext y
    simp only [slyV₂, Function.update_apply, Nat.add_zero, Nat.mul_one, List.append_nil]
    split_ifs <;> simp_all
  · simp only [slySetupCost, synStashCostW, slyPV, Function.update_apply, ite_true]
    simp
    omega

end Setup

/-! ### The file of the layout stage -/

section Pre

variable {Ka : ℕ}

/-- The file after the setup is a `LdgPre` file of the layout stage. -/
theorem sly_ldgPre {es : List ℕ} {ℓ K w l : ℕ} {L : Equiv.Perm (Fin es.sum)}
    {v₀ : SynW → List (Fin (prime + Ka + 4))} (hv₀ : SynV v₀ es ℓ K w l 0 L)
    (P' : List (Fin (prime + Ka + 4))) (W E : ℕ) (rl : List (List (Fin (prime + Ka + 4)))) :
    LdgPre slyRg slyLr slyGr sxHd sxPay (synG (synIdle rl.flatten P') (slyV₂ W E es.sum (2 ^ l * w) v₀))
      es ℓ K (2 ^ l * w) E W (List.replicate W tick) rl := by
  have hs := hv₀.hs
  have hly := hv₀.hly
  have hw : ∀ x : SynW, synG (synIdle rl.flatten P') (slyV₂ W E es.sum (2 ^ l * w) v₀) (sreg x) =
      slyV₂ W E es.sum (2 ^ l * w) v₀ x := fun x => synG_sreg x
  have ht : ∀ c, synG (synIdle rl.flatten P') (slyV₂ W E es.sum (2 ^ l * w) v₀) (slyT c) = [] :=
    fun c => by rw [synG_of_ne (slyT_out c), synIdle_slyT]
  have hb : ∀ j, synG (synIdle rl.flatten P') (slyV₂ W E es.sum (2 ^ l * w) v₀) (slyRg (.sw j)) =
      [] := fun j => by rw [synG_of_ne (slyRg_sw_out j), synIdle_sw]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hw (.ly 1)).trans (by simp [slyV₂, slyPV, hly])
  · exact (hw (.ly 2)).trans (by simp [slyV₂, slyPV, hly])
  · exact (hw (.ly 3)).trans (by simp [slyV₂, slyPV, hly])
  · exact (hw (.ly 4)).trans (by simp [slyV₂, slyPV, hly])
  · exact (hw (.ly 5)).trans (by simp [slyV₂, slyPV, hly])
  · exact (hw (.ly 6)).trans (by simp [slyV₂, slyPV, hly])
  · exact (hw (.ly 7)).trans (by simp [slyV₂, slyPV, hly])
  · exact (hw (.ly 8)).trans (by simp [slyV₂, slyPV, hly])
  · exact (hw (.ly 11)).trans (by simp [slyV₂, slyPV, hly])
  · rw [show slyRg .ctrB = sreg (.ly 9) from rfl, hw]; simp [slyV₂]
  · rw [show slyRg .cnt = sreg (.ly 10) from rfl, hw]; simp [slyV₂]
  · exact (hw (.ly 13)).trans (by simp [slyV₂])
  · intro r
    rw [show slyRg (.us r) = sreg (.ly ⟨16 + r.val, by omega⟩) from rfl, hw]
    simp only [slyV₂, slyPV, Function.update_apply, SynW.ly.injEq, reduceCtorEq, ite_false]
    split_ifs <;> first | exact hly _ | (exfalso; simp [Fin.ext_iff] at *; omega)
  · exact le_of_eq_of_le ((congrArg List.length (hw (.ly 14))).trans
      (by simp [slyV₂, slyPV, hly])) (Nat.zero_le _)
  · exact le_of_eq_of_le ((congrArg List.length (hw (.ly 15))).trans
      (by simp [slyV₂, slyPV, hly])) (Nat.zero_le _)
  · exact hb _
  · intro j _; exact hb j
  · intro i _ _ s hs'; rw [hb] at hs'; simp at hs'
  · intro k; simp only [ldlH]; rw [hb]; simp
  · rw [show slyRg .str = lreg .io from rfl, synG_of_ne (lreg_out (by simp))]
    simp [synIdle, lreg]
  · exact (hw (.ly 19)).trans (by simp [slyV₂, slyPV, hly])
  · exact (hw (.ly 20)).trans (by simp [slyV₂, slyPV, hly])
  · exact (hw (.ly 21)).trans (by simp [slyV₂, slyPV, hly])
  · exact (hw (.ly 22)).trans (by simp [slyV₂, slyPV, hly])
  · exact ht 0
  · exact ht 1
  · exact ht 2
  · exact ht 3
  · exact ht 4
  · exact ht 5
  · exact ht 6
  · intro r
    cases r with
    | v i => exact (ht _).trans rfl
    | wr => rw [show ldgRv slyGr .wr = sreg (.s 1) from rfl, hw]; simp [slyV₂, slyPV, ldgIdle]
    | wn => exact (ht _).trans rfl
    | acc => exact (ht _).trans rfl
    | z j => exact (ht _).trans rfl
  · simp
  · rw [show slyGr .uN = sreg (.p .N) from rfl, hw]; simp [slyV₂, slyPV, hv₀.hN]
  · rw [show slyGr .uL = sreg (.p .ℓ) from rfl, hw]; simp [slyV₂, slyPV, hv₀.hℓ]
  · rw [show slyGr .uK = sreg (.p .K) from rfl, hw]; simp [slyV₂, slyPV, hv₀.hK]
  · rw [show slyGr .uD = sreg (.p .D) from rfl, hw]; simp [slyV₂, slyPV, hv₀.hD]
  · rw [show slyGr .uB = sreg (.s 0) from rfl, hw]; simp [slyV₂]
  · rw [show slyGr .eW = sreg (.s 2) from rfl, hw]; simp [slyV₂, slyPV]
  · exact ht 7

end Pre

/-! ### The file after the layout machine, and the cleanup -/

section Clean

variable {Q A : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q A U)

/-- The registers outside the wires after the layout machine: the headers `hs`, the word
counters `cN`, `cW`. -/
noncomputable def slyRo (io P' : List (Fin (A + 4))) (N wX : ℕ) (hs : Fin 5 → List (Fin (A + 4))) :
    Fin (nT SXReg) → List (Fin (A + 4)) :=
  Function.update (Function.update (ldlSetH slyRg sxHd (synIdle io P') hs) (slyT 2)
    (List.replicate N tick)) (slyT 3) (List.replicate wX tick)

/-- The wires after the layout machine: the masks `mA`, `mB` and the loop counters. -/
def slyV₃ (W E N B : ℕ) (v₀ : SynW → List (Fin (A + 4))) (csM csX mA mB : List (Fin (A + 4))) :
    SynW → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (slyV₂ W E N B v₀) (.ly 14) mA)
    (.ly 15) mB) (.ly 19) csM) (.ly 21) csX

/-- Clear the loop counters, masks, word counters, headers, the counters of the moves and `B`,
then park `W`, `E`. -/
noncomputable def slyClean : Pr P (nT SXReg) Q A U :=
  .seq (uclear (sreg (.ly 19))) <| .seq (uclear (sreg (.ly 21))) <|
  .seq (uclear (sreg (.ly 14))) <| .seq (uclear (sreg (.ly 15))) <|
  .seq (uclear (slyT 2)) <| .seq (uclear (slyT 3)) <|
  .seq (uclear (ldlH slyRg sxHd 0)) <| .seq (uclear (ldlH slyRg sxHd 1)) <|
  .seq (uclear (ldlH slyRg sxHd 2)) <| .seq (uclear (ldlH slyRg sxHd 3)) <|
  .seq (uclear (ldlH slyRg sxHd 4)) <|
  .seq (uclear (sreg (.ly 9))) <| .seq (uclear (sreg (.ly 10))) <|
  .seq (uclear (sreg (.ly 13))) <| .seq (uclear (sreg (.s 0)))
    (synStash (lreg .park) blank ([SynW.s 1, .s 2].map sreg))

/-- The step bound of the cleanup. -/
def slyCleanCost (xM xX N wX B W : ℕ) : ℕ :=
  (2 * xM + 2) + (2 * xX + 2) + (2 * N + 2) + (2 * N + 2) + (2 * N + 2) + (2 * wX + 2) +
    5 * (2 * (wX + 1) + 2) + (2 * B + 2) + (2 * 2 ^ N + 2) + (2 * N + 2) + (2 * B + 2) +
    (4 * W + 8)

theorem slyRo_T2 (io P' : List (Fin (A + 4))) (N wX : ℕ) (hs : Fin 5 → List (Fin (A + 4))) :
    slyRo io P' N wX hs (slyT 2) = List.replicate N tick := by
  simp [slyRo]

theorem slyRo_T3 (io P' : List (Fin (A + 4))) (N wX : ℕ) (hs : Fin 5 → List (Fin (A + 4))) :
    slyRo io P' N wX hs (slyT 3) = List.replicate wX tick := by
  simp [slyRo]

theorem slyRo_H (io P' : List (Fin (A + 4))) (N wX : ℕ) (hs : Fin 5 → List (Fin (A + 4)))
    (k : Fin 5) : slyRo io P' N wX hs (ldlH slyRg sxHd k) = hs k := by
  rw [slyRo, Function.update_of_ne (slyH_ne_slyT k 3), Function.update_of_ne (slyH_ne_slyT k 2),
    ldlSetH_H slyRg_injective sxHd_inj]

/-- The registers outside the wires after the cleanup. -/
theorem slyRo_clean (io P' : List (Fin (A + 4))) (N wX : ℕ) (hs : Fin 5 → List (Fin (A + 4)))
    (X : List (Fin (A + 4))) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (slyRo io P' N wX hs)
        (slyT 2) []) (slyT 3) []) (ldlH slyRg sxHd 0) []) (ldlH slyRg sxHd 1) [])
        (ldlH slyRg sxHd 2) []) (ldlH slyRg sxHd 3) []) (ldlH slyRg sxHd 4) [])
        (lreg .park) X = synIdle io X := by
  funext z
  by_cases hp : z = lreg .park
  · subst hp
    simp [synIdle, lreg]
  by_cases hi : z = lreg .io
  · subst hi
    simp [slyRo, ldlSetH, synIdle, lreg, (slyH_ne_io 0).symm,
      (slyH_ne_io 1).symm, (slyH_ne_io 2).symm, (slyH_ne_io 3).symm, (slyH_ne_io 4).symm,
      (slyT_ne_io 2).symm, (slyT_ne_io 3).symm, hp]
  simp only [Function.update_apply, ite_eq_right hp]
  split_ifs <;> simp_all [slyRo, ldlSetH, synIdle, lreg]

theorem slyRo_chain_park (io P' : List (Fin (A + 4))) (N wX : ℕ)
    (hs : Fin 5 → List (Fin (A + 4))) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (slyRo io P' N wX hs)
        (slyT 2) []) (slyT 3) []) (ldlH slyRg sxHd 0) []) (ldlH slyRg sxHd 1) [])
        (ldlH slyRg sxHd 2) []) (ldlH slyRg sxHd 3) []) (ldlH slyRg sxHd 4) [] (lreg .park) = P' := by
  rw [Function.update_of_ne (slyH_ne_park 4).symm, Function.update_of_ne (slyH_ne_park 3).symm,
    Function.update_of_ne (slyH_ne_park 2).symm, Function.update_of_ne (slyH_ne_park 1).symm,
    Function.update_of_ne (slyH_ne_park 0).symm, Function.update_of_ne (slyT_ne_park 3).symm,
    Function.update_of_ne (slyT_ne_park 2).symm, slyRo,
    Function.update_of_ne (slyT_ne_park 3).symm, Function.update_of_ne (slyT_ne_park 2).symm,
    ldlSetH, Function.update_of_ne (slyH_ne_park 4).symm, Function.update_of_ne (slyH_ne_park 3).symm,
    Function.update_of_ne (slyH_ne_park 2).symm, Function.update_of_ne (slyH_ne_park 1).symm,
    Function.update_of_ne (slyH_ne_park 0).symm]
  simp [synIdle]

/-- The wires after the cleanup. -/
theorem slyV₃_clean {es : List ℕ} {ℓ K w l : ℕ} {L : Equiv.Perm (Fin es.sum)}
    {v₀ : SynW → List (Fin (A + 4))} (hv₀ : SynV v₀ es ℓ K w l 0 L) (W E N B : ℕ)
    (csM csX mA mB : List (Fin (A + 4))) :
    synClrW (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (slyV₃ W E N B v₀ csM csX mA mB)
        (.ly 19) []) (.ly 21) []) (.ly 14) []) (.ly 15) []) (.ly 9) []) (.ly 10) []) (.ly 13) [])
        (.s 0) []) [.s 1, .s 2] = v₀ := by
  have hs := hv₀.hs
  have hly := hv₀.hly
  funext x
  rcases x with a | i | a | i
  · simp [synClrW, slyV₃, slyV₂, slyPV]
  · simp only [synClrW, slyV₃, slyV₂, slyPV, Function.update_apply, List.mem_cons,
      List.not_mem_nil, or_false, SynW.ly.injEq, reduceCtorEq, ite_false]
    split_ifs <;> simp_all
  · simp [synClrW, slyV₃, slyV₂, slyPV]
  · simp only [synClrW, slyV₃, slyV₂, slyPV, Function.update_apply, List.mem_cons,
      List.not_mem_nil, or_false, SynW.s.injEq, reduceCtorEq, ite_false]
    split_ifs <;> simp_all

theorem slyV₃_park (v₀ : SynW → List (Fin (A + 4))) (W E N B : ℕ)
    (csM csX mA mB : List (Fin (A + 4))) (P' : List (Fin (A + 4))) :
    synStkW (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (slyV₃ W E N B v₀ csM csX mA mB)
        (.ly 19) []) (.ly 21) []) (.ly 14) []) (.ly 15) []) (.ly 9) []) (.ly 10) []) (.ly 13) [])
        (.s 0) []) blank [.s 1, .s 2] ++ blank :: P' = slyPark W E P' := by
  simp [synStkW, slyV₃, slyV₂, slyPV, slyPark]

/-- **The cleanup.** From the file after the layout machine (loop counters of at most `xM`,
`xX` symbols, masks of at most `N`, headers of at most `wX + 1`) to the idle file with `W`, `E`
parked again. -/
theorem sg_slyClean {es : List ℕ} {ℓ K w l : ℕ} {L : Equiv.Perm (Fin es.sum)}
    {v₀ : SynW → List (Fin (A + 4))} (hv₀ : SynV v₀ es ℓ K w l 0 L) (io P' : List (Fin (A + 4)))
    (W E N wX B xM xX : ℕ) (hs : Fin 5 → List (Fin (A + 4))) (hhs : ∀ k, (hs k).length ≤ wX + 1)
    (csM csX mA mB : List (Fin (A + 4))) (hM : csM.length ≤ xM) (hX : csX.length ≤ xX)
    (hmA : mA.length ≤ N) (hmB : mB.length ≤ N) :
    LayRuns body slyClean (synG (slyRo io P' N wX hs) (slyV₃ W E N B v₀ csM csX mA mB))
      (synG (synIdle io (slyPark W E P')) v₀) (slyCleanCost xM xX N wX B W) := by
  have hs' := hv₀.hs
  have hly := hv₀.hly
  have hT23 : slyT 3 ≠ slyT 2 := by simp [slyT_inj]
  have hHT : ∀ k c, ldlH slyRg sxHd k ≠ slyT c := slyH_ne_slyT
  have hHH : ∀ k k' : Fin 5, k ≠ k' → ldlH slyRg sxHd k ≠ ldlH slyRg sxHd k' :=
    fun k k' h => slyH_injective.ne h
  refine lr_weaken body
    ((sgL_clear body (a := .ly 19) (x := xM) (by simp [slyV₃]; exact hM)).seq <|
    (sgL_clear body (a := .ly 21) (x := xX) (by simp [slyV₃]; exact hX)).seq <|
    (sgL_clear body (a := .ly 14) (x := N) (by simp [slyV₃]; exact hmA)).seq <|
    (sgL_clear body (a := .ly 15) (x := N) (by simp [slyV₃]; exact hmB)).seq <|
    (soL_clear body (slyT_out 2) (x := N) (by rw [slyRo_T2]; simp)).seq <|
    (soL_clear body (slyT_out 3) (x := wX)
      (by rw [Function.update_of_ne hT23, slyRo_T3]; simp)).seq <|
    (soL_clear body (slyH_out 0) (x := wX + 1)
      (by rw [Function.update_of_ne (hHT 0 3), Function.update_of_ne (hHT 0 2), slyRo_H]
          exact hhs 0)).seq <|
    (soL_clear body (slyH_out 1) (x := wX + 1)
      (by rw [Function.update_of_ne (hHH 1 0 (by decide)), Function.update_of_ne (hHT 1 3),
            Function.update_of_ne (hHT 1 2), slyRo_H]
          exact hhs 1)).seq <|
    (soL_clear body (slyH_out 2) (x := wX + 1)
      (by rw [Function.update_of_ne (hHH 2 1 (by decide)), Function.update_of_ne (hHH 2 0 (by decide)),
            Function.update_of_ne (hHT 2 3), Function.update_of_ne (hHT 2 2), slyRo_H]
          exact hhs 2)).seq <|
    (soL_clear body (slyH_out 3) (x := wX + 1)
      (by rw [Function.update_of_ne (hHH 3 2 (by decide)), Function.update_of_ne (hHH 3 1 (by decide)),
            Function.update_of_ne (hHH 3 0 (by decide)), Function.update_of_ne (hHT 3 3),
            Function.update_of_ne (hHT 3 2), slyRo_H]
          exact hhs 3)).seq <|
    (soL_clear body (slyH_out 4) (x := wX + 1)
      (by rw [Function.update_of_ne (hHH 4 3 (by decide)), Function.update_of_ne (hHH 4 2 (by decide)),
            Function.update_of_ne (hHH 4 1 (by decide)), Function.update_of_ne (hHH 4 0 (by decide)),
            Function.update_of_ne (hHT 4 3), Function.update_of_ne (hHT 4 2), slyRo_H]
          exact hhs 4)).seq <|
    (sgL_clear body (a := .ly 9) (x := B) (by simp [slyV₃, slyV₂])).seq <|
    (sgL_clear body (a := .ly 10) (x := 2 ^ N) (by simp [slyV₃, slyV₂])).seq <|
    (sgL_clear body (a := .ly 13) (x := N) (by simp [slyV₃, slyV₂])).seq <|
    (sgL_clear body (a := .s 0) (x := B) (by simp [slyV₃, slyV₂])).seq <|
    sg_synStash body (pk := lreg .park) (lreg_out (by simp)) blank [.s 1, .s 2] (by decide))
    ?_ ?_
  · rw [slyV₃_clean hv₀, slyRo_clean, slyRo_chain_park, slyV₃_park]
  · simp only [slyCleanCost, synStashCostW, slyV₃, slyV₂, slyPV, Function.update_apply]
    simp
    omega

end Clean

end IntegerMultBounds.MathlibTM2.Fast
