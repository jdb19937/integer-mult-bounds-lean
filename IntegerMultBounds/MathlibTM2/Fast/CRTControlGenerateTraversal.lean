module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerateSetup
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Concrete iteration of the runtime descriptor generator -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Binary state after consuming the first `j` original axes. -/
def crtControlTraversalState (st : TblSt 10 A) (a s : List ℕ) : ℕ → TblSt 10 A
  | 0 => st
  | j + 1 => crtControlGenerateNextState
      (crtControlPreparedState (crtControlTraversalState st a s j) (s.getD j 0) ((a.take j).sum))

/-- Exact register trajectory of the fixed runtime axis program. -/
noncomputable def crtControlTraversalRegs (rg : TblR 10 → Fin T)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst : Fin T) (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 10 A) (R : Regs T A) (a s : List ℕ) : ℕ → Regs T A
  | 0 => R
  | j + 1 => crtControlGenerateAxisRegs rg widths moduli savedWidths savedModuli
      axisWidth axisModulus lower left past packet zero dst W wl nl
      (crtControlTraversalState st a s j)
      (crtControlTraversalRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
        lower left past packet zero dst W wl nl st R a s j)
      (a.getD j 0) (s.getD j 0) ((a.take j).sum) (a.drop (j + 1)) (s.drop (j + 1))

/-- Structural facts maintained by every concrete iteration. The output and
parked packet are deliberately left to the separate layout invariant. -/
structure CrtControlTraversalInvariant (rg : TblR 10 → Fin T)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left packet pad tmp : Fin T)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt 10 A)
    (a s : List ℕ) (i j : ℕ) (R : Regs T A) : Prop where
  bank : ∀ r, R (rg r) = tblRho W wl nl st r
  widths : R widths = crtEnts (a.drop j)
  moduli : R moduli = crtEnts (s.drop j)
  savedWidths : R savedWidths = crtEnts (a.take j).reverse
  savedModuli : R savedModuli = crtEnts (s.take j).reverse
  axisWidth : R axisWidth = []
  axisModulus : R axisModulus = []
  lower : R lower = List.replicate (a.take j).sum tick
  left : R left = List.replicate (i - j) tick
  packet : R packet = []
  pad : R pad = []
  tmp : R tmp = []

private theorem crtTraversal_take_succ (a : List ℕ) {j : ℕ} (hj : j < a.length) :
    a.take (j + 1) = a.take j ++ [a.getD j 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
  rfl

/-- Concrete pure axis transition preserves the structural traversal invariant. -/
theorem crtControlTraversalInvariant_step {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst pad tmp : Fin T)
    (hreg : [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus, lower, left,
      past, packet, zero, dst, pad, tmp].Nodup)
    (hd : ∀ k, ∀ r ∈ [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst, pad, tmp], rg k ≠ r)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt 10 A) (R : Regs T A)
    (a s : List ℕ) (i j : ℕ) (hja : j < a.length) (hjs : j < s.length)
    (h : CrtControlTraversalInvariant rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left packet pad tmp W wl nl st a s i j R) :
    CrtControlTraversalInvariant rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left packet pad tmp W wl nl
      (crtControlGenerateNextState (crtControlPreparedState st (s.getD j 0) (a.take j).sum)) a s i (j + 1)
      (crtControlGenerateAxisRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
        lower left past packet zero dst W wl nl st R (a.getD j 0) (s.getD j 0)
        (a.take j).sum (a.drop (j + 1)) (s.drop (j + 1))) := by
  obtain ⟨hw, hm, hsw, hsm, haw, ham, hl, hi, hp, hpad, htmp⟩ :=
    crtControlGenerateAxisRegs_streams widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left past packet zero dst pad tmp hreg hd W wl nl st R
      (a.getD j 0) (s.getD j 0) (a.take j).sum (a.drop (j + 1)) (s.drop (j + 1))
  refine ⟨?_, hw, hm, ?_, ?_, haw, ham, ?_, ?_, hp, ?_, ?_⟩
  · apply crtControlGenerateAxisRegs_bank hrg
    intro k r hr
    apply hd k r
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [hsw, h.savedWidths, crtTraversal_take_succ a hja]
    simp [List.reverse_append, crtEnts_cons]
  · rw [hsm, h.savedModuli, crtTraversal_take_succ s hjs]
    simp [List.reverse_append, crtEnts_cons]
  · rw [hl, h.lower, crtTraversal_take_succ a hja]
    simp [Nat.add_comm]
  · rw [hi, h.left, List.tail_replicate]
    congr 1
  · exact hpad.trans h.pad
  · exact htmp.trans h.tmp

/-- Structural induction for the exact executable register trajectory. -/
theorem crtControlTraversal_invariant {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst pad tmp : Fin T)
    (hreg : [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus, lower, left,
      past, packet, zero, dst, pad, tmp].Nodup)
    (hd : ∀ k, ∀ r ∈ [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst, pad, tmp], rg k ≠ r)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt 10 A) (R : Regs T A)
    (a s : List ℕ) (i : ℕ) (hlen : a.length = s.length)
    (hinit : CrtControlTraversalInvariant rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left packet pad tmp W wl nl st a s i 0 R) :
    ∀ j ≤ a.length,
      CrtControlTraversalInvariant rg widths moduli savedWidths savedModuli axisWidth axisModulus
        lower left packet pad tmp W wl nl (crtControlTraversalState st a s j) a s i j
        (crtControlTraversalRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
          lower left past packet zero dst W wl nl st R a s j) := by
  intro j
  induction j with
  | zero => intro _; exact hinit
  | succ j ih =>
    intro hj
    exact crtControlTraversalInvariant_step hrg widths moduli savedWidths savedModuli
      axisWidth axisModulus lower left past packet zero dst pad tmp hreg hd W wl nl
      (crtControlTraversalState st a s j) _ a s i j (by omega) (by omega) (ih (by omega))

/-- Full runtime traversal. All per-axis execution obligations are discharged
by the concrete axis theorem; only arithmetic size bounds remain as inputs. -/
theorem crtControlTraversal_runs {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst pad tmp : Fin T)
    (hreg : [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus, lower, left,
      past, packet, zero, dst, pad, tmp].Nodup)
    (hd : ∀ k, ∀ r ∈ [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst, pad, tmp], rg k ≠ r)
    {W w : ℕ} (hW : 0 < W) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (st : TblSt 10 A) (R : Regs T A) (a s : List ℕ) (i b : ℕ) (hlen : a.length = s.length)
    (hinit : CrtControlTraversalInvariant rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left packet pad tmp W wl nl st a s i 0 R)
    (hfit : ∀ j < a.length, ∀ k, (crtControlTraversalState st a s j).val k < 2 ^ W)
    (hmod : ∀ j < a.length, s.getD j 0 < 2 ^ W)
    (hexp : ∀ j < a.length, (a.take j).sum < W)
    (hweight : ∀ j < a.length, (crtControlTraversalState st a s j).val 6 * s.getD j 0 < 2 ^ W)
    (hindex : ∀ j < a.length, (crtControlTraversalState st a s j).val 0 + 1 < 2 ^ W)
    (hcost : ∀ j < a.length,
      crtControlGenerateAxisCost W w (a.getD j 0) (s.getD j 0) (a.take j).sum
        ((crtControlTraversalRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
          lower left past packet zero dst W wl nl st R a s j) zero).length ≤ b) :
    let Ψ := crtControlTraversalRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left past packet zero dst W wl nl st R a s
    crtRuns body (crtControlGenerateLoop rg widths moduli savedWidths savedModuli
      axisWidth axisModulus lower left past packet zero dst pad tmp) R
      (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Ψ a.length)
          savedWidths []) widths (crtEnts a)) savedModuli []) moduli (crtEnts s)) lower []) past [])
      (a.length * (b + 2) + 2 + (2 * (crtEnts (A := A) a).length + 2) +
        (2 * (crtEnts (A := A) s).length + 2) +
        (2 * a.sum + 2) + (2 * (Ψ a.length past).length + 2)) := by
  let Ψ := crtControlTraversalRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
    lower left past packet zero dst W wl nl st R a s
  have hinv := crtControlTraversal_invariant hrg widths moduli savedWidths savedModuli
    axisWidth axisModulus lower left past packet zero dst pad tmp hreg hd W wl nl st R a s i hlen hinit
  have hstep : ∀ j < a.length, Ψ j widths ≠ [] ∧
      crtRuns body (crtControlGenerateAxis rg widths moduli savedWidths savedModuli
        axisWidth axisModulus lower left past packet zero dst pad tmp) (Ψ j) (Ψ (j + 1)) b := by
    intro j hj
    have h := hinv j hj.le
    have hjs : j < s.length := by omega
    have ha : a.drop j = a.getD j 0 :: a.drop (j + 1) := by
      rw [List.getD_eq_getElem _ _ hj, List.drop_eq_getElem_cons hj]
    have hs : s.drop j = s.getD j 0 :: s.drop (j + 1) := by
      rw [List.getD_eq_getElem _ _ hjs, List.drop_eq_getElem_cons hjs]
    refine ⟨?_, ?_⟩
    · dsimp only [Ψ]
      rw [h.widths, ha]
      exact crtEnts_ne_nil (List.cons_ne_nil _ _)
    · apply crtRuns_mono (crtControlGenerateAxis_runs (body := body) hrg widths moduli
        savedWidths savedModuli axisWidth axisModulus lower left past packet zero dst pad tmp
        hreg hd hW wl nl hwl hnl hw (crtControlTraversalState st a s j) (hfit j hj)
        (a.getD j 0) (s.getD j 0) (a.take j).sum (a.drop (j + 1)) (s.drop (j + 1))
        (hmod j hj) (hexp j hj) (hweight j hj) (hindex j hj) (Ψ j) h.bank
        (h.widths.trans (congrArg crtEnts ha)) (h.moduli.trans (congrArg crtEnts hs))
        h.axisWidth h.axisModulus ?_ h.packet h.pad h.tmp)
      · exact hcost j hj
      · dsimp only [Ψ]
        rw [h.lower, List.length_replicate]
  have hfinal := hinv a.length le_rfl
  have hregs : [widths, moduli, savedWidths, savedModuli, lower, past].Nodup := by
    have hreg' := hreg
    regs_ne hreg'
    regs_nodup
  have hr := crtControlGenerateLoop_runs (body := body) hregs Ψ a s b hstep
    (by simpa using hfinal.widths) (by simpa [hlen] using hfinal.moduli)
    (by simpa [crtEnts_reverse] using hfinal.savedWidths)
    (by simpa [hlen, crtEnts_reverse] using hfinal.savedModuli)
  have hzero : Ψ 0 = R := rfl
  have hlower : (Ψ a.length lower).length = a.sum := by
    dsimp only [Ψ]
    rw [hfinal.lower]
    simp
  rw [hzero, hlower] at hr
  exact hr

/-- Original-axis index advances once per consumed runtime entry. -/
@[simp] theorem crtControlTraversalState_index (st : TblSt 10 A) (a s : List ℕ) (j : ℕ) :
    (crtControlTraversalState st a s j).val 0 = st.val 0 + j := by
  induction j with
  | zero => simp [crtControlTraversalState]
  | succ j ih =>
    simp [crtControlTraversalState, crtControlGenerateNextState, crtControlPreparedState, ih, Nat.add_assoc]

/-- Target index and target/zero powers are fixed across the traversal. -/
theorem crtControlTraversalState_fixed (st : TblSt 10 A) (a s : List ℕ) (j : ℕ)
    (k : Fin 10) (h0 : k ≠ 0) (h2 : k ≠ 2) (h5 : k ≠ 5)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) :
    (crtControlTraversalState st a s j).val k = st.val k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simpa [crtControlTraversalState, crtControlGenerateNextState, crtControlGeneratedState,
      crtControlPreparedState, h0, h2, h5, h6, h7, h8] using ih

/-- Accumulator contents are untouched by every generator step. -/
@[simp] theorem crtControlTraversalState_acc (st : TblSt 10 A) (a s : List ℕ) (j : ℕ) :
    (crtControlTraversalState st a s j).acc = st.acc := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

/-- The maintained weight is the original, unpermuted modulus prefix product. -/
theorem crtControlTraversalState_weight (st : TblSt 10 A) (a s : List ℕ) :
    ∀ j ≤ s.length, (crtControlTraversalState st a s j).val 6 = st.val 6 * (s.take j).prod := by
  intro j
  induction j with
  | zero => intro _; simp [crtControlTraversalState]
  | succ j ih =>
    intro hj
    simp [crtControlTraversalState, crtControlGenerateNextState, crtControlPreparedState,
      ih (by omega), crtTraversal_take_succ s (show j < s.length by omega), Nat.mul_assoc]

/-- All ten binary variables fit throughout the concrete traversal whenever
the loaded values, running product, and next index fit. -/
theorem crtControlTraversalState_fit {W : ℕ} (hW : 0 < W)
    (st : TblSt 10 A) (a s : List ℕ) (N : ℕ)
    (hinit : ∀ k, st.val k < 2 ^ W)
    (hmod : ∀ j < N, s.getD j 0 < 2 ^ W)
    (hexp : ∀ j < N, (a.take j).sum < W)
    (hweight : ∀ j < N, (crtControlTraversalState st a s j).val 6 * s.getD j 0 < 2 ^ W)
    (hindex : ∀ j < N, (crtControlTraversalState st a s j).val 0 + 1 < 2 ^ W) :
    ∀ j ≤ N, ∀ k, (crtControlTraversalState st a s j).val k < 2 ^ W := by
  intro j
  induction j with
  | zero => intro _; exact hinit
  | succ j ih =>
    intro hj
    have hjN : j < N := by omega
    have hs := ih (by omega)
    let t := crtControlPreparedState (crtControlTraversalState st a s j) (s.getD j 0) (a.take j).sum
    have ht : ∀ k, t.val k < 2 ^ W := by
      intro k
      by_cases h2 : k = 2
      · subst k
        simpa [t, crtControlPreparedState] using Nat.pow_lt_pow_right (by decide : 1 < 2) (hexp j hjN)
      · by_cases h5 : k = 5
        · subst k; simpa [t, crtControlPreparedState] using hmod j hjN
        · simpa [t, crtControlPreparedState, h2, h5] using hs k
    have hgen : ∀ k, (crtControlGeneratedState t).val k < 2 ^ W := by
      intro k
      by_cases h7 : k = 7
      · subst k
        simp only [crtControlGeneratedState, Function.update_self, crtControlGeneratedField]
        split_ifs <;> apply lt_of_le_of_lt (Nat.div_le_self _ _) <;> apply ht
      · by_cases h8 : k = 8
        · subst k
          have h1 := Nat.one_lt_two_pow hW.ne'
          simp [crtControlGeneratedState]
          split_ifs <;> omega
        · simpa [crtControlGeneratedState, h7, h8] using ht k
    intro k
    change (crtControlGenerateNextState t).val k < 2 ^ W
    by_cases h0 : k = 0
    · subst k; simpa [crtControlGenerateNextState, t, crtControlPreparedState] using hindex j hjN
    · by_cases h6 : k = 6
      · subst k; simpa [crtControlGenerateNextState, t, crtControlPreparedState] using hweight j hjN
      · simpa [crtControlGenerateNextState, h0, h6] using hgen k

/-- Registers outside the bank and twelve traversal outputs are framed by
one concrete axis transition. -/
theorem crtControlGenerateAxisRegs_off (rg : TblR 10 → Fin T)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst : Fin T) (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 10 A) (R : Regs T A) (a b e : ℕ) (as bs : List ℕ)
    (r : Fin T) (hd : ∀ k, rg k ≠ r)
    (hn : ∀ x ∈ [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst], r ≠ x) :
    crtControlGenerateAxisRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left past packet zero dst W wl nl st R a b e as bs r = R r := by
  simp only [crtControlGenerateAxisRegs, Function.update_of_ne (hn savedModuli (by simp)),
    Function.update_of_ne (hn axisModulus (by simp)),
    Function.update_of_ne (hn savedWidths (by simp)),
    Function.update_of_ne (hn axisWidth (by simp)),
    Function.update_of_ne (hn left (by simp)), Function.update_of_ne (hn lower (by simp))]
  rw [crtControlGenerateSelectRegs_off _ _ _ _ _ _ _ _ _ _ _ _ _ hd
    (hn packet (by simp)) (hn zero (by simp)) (hn dst (by simp)) (hn past (by simp)),
    crtBankOverlay_off _ _ _ _ hd]
  simp only [crtControlPoppedRegs, Function.update_of_ne (hn axisModulus (by simp)),
    Function.update_of_ne (hn moduli (by simp)), Function.update_of_ne (hn axisWidth (by simp)),
    Function.update_of_ne (hn widths (by simp))]

/-- The full recursive runtime trajectory preserves every unrelated register. -/
theorem crtControlTraversalRegs_off (rg : TblR 10 → Fin T)
    (widths moduli savedWidths savedModuli axisWidth axisModulus lower left past
      packet zero dst : Fin T) (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 10 A) (R : Regs T A) (a s : List ℕ)
    (r : Fin T) (hd : ∀ k, rg k ≠ r)
    (hn : ∀ x ∈ [widths, moduli, savedWidths, savedModuli, axisWidth, axisModulus,
      lower, left, past, packet, zero, dst], r ≠ x) (j : ℕ) :
    crtControlTraversalRegs rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left past packet zero dst W wl nl st R a s j r = R r := by
  induction j with
  | zero => rfl
  | succ j ih =>
    dsimp only [crtControlTraversalRegs]
    rw [crtControlGenerateAxisRegs_off rg widths moduli savedWidths savedModuli axisWidth axisModulus
      lower left past packet zero dst W wl nl _ _ _ _ _ _ _ r hd hn, ih]

/-- Runtime ascending entry prefixes have exactly the original CRT weight. -/
theorem crtControlTraversalState_weight_prefix {d : ℕ} (st : TblSt 10 A)
    (a s : Fin d → ℕ) (hweight : st.val 6 = 1) (j : Fin d) :
    (crtControlTraversalState st (List.ofFn a) (List.ofFn s) j.val).val 6 =
      IntegerMultBounds.MathlibTM2.Mult.prefixProd s j := by
  rw [crtControlTraversalState_weight st (List.ofFn a) (List.ofFn s) j.val
    (by rw [List.length_ofFn]; exact j.isLt.le), hweight, Nat.one_mul, List.prod_take_ofFn]
  exact crtProd_eq_prefixProd s j.isLt

/-- Every original prefix width is bounded by the total address width. -/
theorem crtControl_pre_le_sum {d : ℕ} (a : Fin d → ℕ) (j : ℕ) :
    crtPre a j ≤ ∑ k, a k := by
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Modulus prefix products fit within the corresponding address widths. -/
theorem crtControl_prod_le_pow {d : ℕ} (a s : Fin d → ℕ)
    (hs : ∀ k, s k ≤ 2 ^ a k) (j : ℕ) : crtProd s j ≤ 2 ^ crtPre a j := by
  calc
    crtProd s j ≤ ∏ k ∈ crtLow j, 2 ^ a k := Finset.prod_le_prod (fun k _ => hs k)
    _ = 2 ^ crtPre a j := Finset.prod_pow_eq_pow_sum _ _ _

/-- The actual initialized generator bank fits at the common `3B+1` width. -/
theorem crtControlGenerateSetupState_fit {d B : ℕ} (a : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (hB : (∑ k, a k) ≤ B) (hd : d + 1 ≤ B)
    (acc : List (Fin (A + 4))) :
    ∀ k, (crtControlGenerateSetupState i.val (a i) (a 0) (crtPre a i.val) acc).val k <
      2 ^ (3 * B + 1) := by
  have hpow : 2 ^ B < 2 ^ (3 * B + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hi : a i ≤ B := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hB
  have h0 : a 0 ≤ B := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)).trans hB
  have hp : crtPre a i.val ≤ B := (crtControl_pre_le_sum a i.val).trans hB
  have hip := (Nat.pow_le_pow_right (by decide : 0 < 2) hi).trans_lt hpow
  have h0p := (Nat.pow_le_pow_right (by decide : 0 < 2) h0).trans_lt hpow
  have hpp := (Nat.pow_le_pow_right (by decide : 0 < 2) hp).trans_lt hpow
  have hBp : B < 2 ^ (3 * B + 1) := (show B < 2 ^ B from Nat.lt_two_pow_self).trans hpow
  have hone : 1 < 2 ^ (3 * B + 1) := Nat.one_lt_two_pow (by omega)
  intro k
  fin_cases k <;> simp [crtControlGenerateSetupState, crtControlGenerateInitial] <;> omega

/-- All arithmetic preconditions of the runtime traversal follow from the
original radix widths and the dimension bound; no per-step bank oracle remains. -/
theorem crtControlTraversal_arithmetic {d B : ℕ} (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (hs : ∀ k, s k ≤ 2 ^ a k)
    (hB : (∑ k, a k) ≤ B) (hd : d + 1 ≤ B) (acc : List (Fin (A + 4))) :
    let st := crtControlGenerateSetupState i.val (a i) (a 0) (crtPre a i.val) acc
    ∀ j < d + 1,
      (∀ k, (crtControlTraversalState st (List.ofFn a) (List.ofFn s) j).val k < 2 ^ (3 * B + 1)) ∧
      (List.ofFn s).getD j 0 < 2 ^ (3 * B + 1) ∧
      ((List.ofFn a).take j).sum < 3 * B + 1 ∧
      (crtControlTraversalState st (List.ofFn a) (List.ofFn s) j).val 6 *
        (List.ofFn s).getD j 0 < 2 ^ (3 * B + 1) ∧
      (crtControlTraversalState st (List.ofFn a) (List.ofFn s) j).val 0 + 1 < 2 ^ (3 * B + 1) := by
  let st := crtControlGenerateSetupState i.val (a i) (a 0) (crtPre a i.val) acc
  have hpow : 2 ^ B < 2 ^ (3 * B + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hBp : B < 2 ^ (3 * B + 1) := (show B < 2 ^ B from Nat.lt_two_pow_self).trans hpow
  have hpre : ∀ j, crtPre a j ≤ B := fun j => (crtControl_pre_le_sum a j).trans hB
  have hmod : ∀ j < d + 1, (List.ofFn s).getD j 0 < 2 ^ (3 * B + 1) := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
    exact (hs ⟨j, hj⟩).trans_lt ((Nat.pow_le_pow_right (by decide)
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨j, hj⟩)).trans hB)).trans_lt hpow)
  have hexp : ∀ j < d + 1, ((List.ofFn a).take j).sum < 3 * B + 1 := by
    intro j _
    rw [List.sum_take_ofFn]
    have := hpre j
    change crtPre a j < 3 * B + 1
    omega
  have hweight : ∀ j < d + 1,
      (crtControlTraversalState st (List.ofFn a) (List.ofFn s) j).val 6 *
        (List.ofFn s).getD j 0 < 2 ^ (3 * B + 1) := by
    intro j hj
    rw [crtControlTraversalState_weight st _ _ j (by simp; omega)]
    have h6 : st.val 6 = 1 := by simp [st, crtControlGenerateSetupState, crtControlGenerateInitial]
    rw [h6, Nat.one_mul]
    rw [List.prod_take_ofFn, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
    change crtProd s j * s ⟨j, hj⟩ < _
    rw [← crtProd_succ s hj]
    exact (crtControl_prod_le_pow a s hs (j + 1)).trans_lt
      ((Nat.pow_le_pow_right (by decide) (hpre (j + 1))).trans_lt hpow)
  have hindex : ∀ j < d + 1,
      (crtControlTraversalState st (List.ofFn a) (List.ofFn s) j).val 0 + 1 < 2 ^ (3 * B + 1) := by
    intro j hj
    simp only [crtControlTraversalState_index]
    have h0 : st.val 0 = 0 := by simp [st, crtControlGenerateSetupState, crtControlGenerateInitial]
    rw [h0]
    omega
  have hfit := crtControlTraversalState_fit (show 0 < 3 * B + 1 by omega) st
    (List.ofFn a) (List.ofFn s) (d + 1)
    (crtControlGenerateSetupState_fit a i hB hd acc) hmod hexp hweight hindex
  dsimp only
  intro j hj
  exact ⟨hfit j hj.le, hmod j hj, hexp j hj, hweight j hj, hindex j hj⟩

end IntegerMultBounds.MathlibTM2.Fast
