module

public import IntegerMultBounds.MathlibTM2.Fast.DistSrcP2
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# Phase 2b of the converter: constants and the layout parameters

`dsP2b rg g`: the constant `csyms A w (cstDiskC p)` of the chirp stage on `k .kc` (`p + 2`
symbols `pairSym true false` above `w - (p + 2)` symbols `pairSym false false`, from two unary
counters), the zero record `csyms A w 0` on `c .zr`, and the parameters of the layout stage:
`B = r w`, `W_L = r w + N² + N + 4`, `binSyms W_L E`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ChirpSt


section Consts

variable {A : ℕ}

/-- The constant of the chirp stage: `p + 2` ones above `w - (p + 2)` zeros. -/
theorem ds_csyms_disk {p w : ℕ} (hpw : p + 2 ≤ w) :
    csyms A w (cstDiskC p) = List.replicate (p + 2) (pairSym A true false) ++
      List.replicate (w - (p + 2)) (pairSym A false false) := by
  have hlen : w = p + 2 + (w - (p + 2)) := by omega
  have hlt : 2 ^ (p + 2) - 1 < 2 ^ w := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hpw
    have := Nat.two_pow_pos (p + 2)
    omega
  have hre : ((cstDiskC p).re : ZMod (2 ^ w)).val = 2 ^ (p + 2) - 1 := by
    have e : (cstDiskC p).re = ((2 ^ (p + 2) - 1 : ℕ) : ℤ) := by
      simp [cstDiskC, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]
    rw [e, Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  apply List.ext_getElem (by simpa using hlen)
  intro i h1 h2
  simp only [csyms, coeffSyms, red, List.getElem_ofFn, hre]
  simp only [length_coeffSyms] at h1
  rw [List.getElem_append]
  split_ifs with hi
  · simp only [List.length_replicate] at hi
    simp [Nat.testBit_two_pow_sub_one, hi, cstDiskC]
  · simp only [List.length_replicate, not_lt] at hi
    simp [Nat.testBit_two_pow_sub_one, show ¬ i < p + 2 by omega, cstDiskC]

/-- The zero coefficient. -/
theorem ds_csyms_zero (w : ℕ) : csyms A w 0 = List.replicate w (pairSym A false false) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [csyms, coeffSyms, red]

end Consts

section P2b

variable {T Q A t₀ : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {g : DsY t₀ → Fin T}

/-- Phase 2b. -/
def dsP2b (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) : Pr P T Q A U :=
  .seq (dsStep rg dsCwp2 (g (.o .uq))) <|
  .seq (umulSym 1 (pairSym A false false) (g (.o .uq)) (g (.s (.k .kc))) (g (.o .tm))) <|
  .seq (uclear (g (.o .uq))) <| .seq (dsStep rg dsCp2 (g (.o .uq))) <|
  .seq (umulSym 1 (pairSym A true false) (g (.o .uq)) (g (.s (.k .kc))) (g (.o .tm))) <|
  .seq (uclear (g (.o .uq))) <|
  .seq (umulSym 1 (pairSym A false false) (g (.o .uw)) (g (.s (.c .zr))) (g (.o .tm))) <|
  .seq (dsUMul (g (.o .uw)) (g (.o .rR)) (g (.o .lB)) (g (.o .tm)) (g (.o .xT))) <|
  .seq (ucopy (g (.o .lB)) (g (.o .lW)) (g (.o .tm))) <| .seq (dsStep rg dsCWL (g (.o .lW)))
    (dsStepB rg dsCE (g (.o .lE)) (g (.o .lW)))

/-- The writes of phase 2b. -/
def dsP2bW (n w : ℕ) : List (DsY t₀ × List (Fin (A + 4))) :=
  [(.s (.k .kc), csyms A w (cstDiskC (p n))), (.s (.c .zr), csyms A w 0),
   (.o .lB, List.replicate (r n * w) tick), (.o .lW, List.replicate (dsWL n w) tick),
   (.o .lE, binSyms (dsWL n w) (dsE n))]

/-- The step bound of phase 2b. -/
def dsP2bCost (n w : ℕ) : ℕ :=
  dsStepCost (pmW n) 4 (w - (p n + 2)) + (4 * (w - (p n + 2)) + 4) +
    (2 * (w - (p n + 2)) + 2) + dsStepCost (pmW n) 3 (p n + 2) + (4 * (p n + 2) + 4) +
    (2 * (p n + 2) + 2) + (4 * w + 4) + (w * (4 * r n + 7) + 2 * w + 4) + (4 * (r n * w) + 4) +
    dsStepCost (pmW n) 7 ((logT n - ℓ n) ^ 2 + (logT n - ℓ n) + 4) +
    dsStepBCost (pmW n) (dsEK n) (dsWL n w)

variable (h : DsLay rg g)
include h

set_option maxHeartbeats 2000000 in
/-- **Phase 2b.** -/
theorem ds_P2b (R : Regs T A) {n w : ℕ} (hB : Big n) (hpw : p n + 2 ≤ w)
    (hw4 : 4 * w + 2 < 2 ^ pmW n) (hWL : pmW n ≤ dsWL n w) (wl : List (Fin (A + 4)))
    (hwl : wl.length = pmW n) (X : DsY t₀ → List (Fin (A + 4))) (huw : (X (.o .uw)).length = w)
    (hrR : (X (.o .rR)).length = r n) (htm : X (.o .tm) = []) (hxT : X (.o .xT) = [])
    (huq : X (.o .uq) = [])
    (h0 : ∀ y ∈ (dsP2bW (A := A) (t₀ := t₀) n w).map Prod.fst, X y = []) :
    dsRuns body (dsP2b rg g) (dsF rg g R X (pmW n) wl (dsV1 n 0 w))
      (dsF rg g R (dsUpdL X (dsP2bW n w)) (pmW n) wl (dsV1 n 0 w)) (dsP2bCost n w) := by
  have hw2 : w < 2 ^ pmW n := by omega
  set V := dsV1 n 0 w with hV
  have hVlt : ∀ j, V j < 2 ^ pmW n := dsV1_lt hB (Nat.two_pow_pos _) hw2
  have hV0 := dsV1_scr n 0 w
  simp only [dsP2bW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h0
  obtain ⟨eKc, eZr, eB, eW, eE⟩ := h0
  -- the constant of the chirp stage
  have s1 := dsF_step (body := body) h R wl X V (.o .uq)
    (dsCwp2_do (A := A) (w' := pmW n) (n := n) hpw hw2) hV0 hVlt hwl huq
  rw [List.append_nil] at s1
  set X₁ := Function.update X (.o .uq) (List.replicate (w - (p n + 2)) (tick : Fin (A + 4)))
    with hX₁
  have s2 := dsF_umulSym (body := body) (W := pmW n) h R wl X₁ V 1 (pairSym A false false)
    (.o .uq) (.s (.k .kc)) (.o .tm) (fun e => by cases e) (fun e => by cases e)
    (fun e => by cases e) (k := w - (p n + 2)) (l := []) (by simp [hX₁]) (by simp [hX₁, eKc])
    (by simp [hX₁, htm])
  rw [one_mul, List.append_nil] at s2
  set X₂ := Function.update X₁ (.s (.k .kc)) (List.replicate (w - (p n + 2)) (pairSym A false false))
    with hX₂
  have s3 := dsF_uclear (body := body) (W := pmW n) h R wl X₂ V (.o .uq) (c := w - (p n + 2))
    (by simp [hX₂, hX₁])
  set X₃ := Function.update X₂ (.o .uq) [] with hX₃
  have s4 := dsF_step (body := body) h R wl X₃ V (.o .uq)
    (dsCp2_do (A := A) (w' := pmW n) (n := n) (w := w)) hV0 hVlt hwl (l := []) (by simp [hX₃])
  rw [List.append_nil] at s4
  set X₄ := Function.update X₃ (.o .uq) (List.replicate (p n + 2) (tick : Fin (A + 4))) with hX₄
  have s5 := dsF_umulSym (body := body) (W := pmW n) h R wl X₄ V 1 (pairSym A true false)
    (.o .uq) (.s (.k .kc)) (.o .tm) (fun e => by cases e) (fun e => by cases e)
    (fun e => by cases e) (k := p n + 2)
    (l := List.replicate (w - (p n + 2)) (pairSym A false false)) (by simp [hX₄])
    (by simp [hX₄, hX₃, hX₂]) (by simp [hX₄, hX₃, hX₂, hX₁, htm])
  rw [one_mul, ← ds_csyms_disk hpw] at s5
  set X₅ := Function.update X₄ (.s (.k .kc)) (csyms A w (cstDiskC (p n))) with hX₅
  have s6 := dsF_uclear (body := body) (W := pmW n) h R wl X₅ V (.o .uq) (c := p n + 2)
    (by simp [hX₅, hX₄])
  set X₆ := Function.update X₅ (.o .uq) [] with hX₆
  -- the zero record
  have s7 := dsF_umulSym (body := body) (W := pmW n) h R wl X₆ V 1 (pairSym A false false)
    (.o .uw) (.s (.c .zr)) (.o .tm) (fun e => by cases e) (fun e => by cases e)
    (fun e => by cases e) (k := w) (l := [])
    (by simp [hX₆, hX₅, hX₄, hX₃, hX₂, hX₁, huw])
    (by simp [hX₆, hX₅, hX₄, hX₃, hX₂, hX₁, eZr]) (by simp [hX₆, hX₅, hX₄, hX₃, hX₂, hX₁, htm])
  rw [one_mul, List.append_nil, ← ds_csyms_zero] at s7
  set X₇ := Function.update X₆ (.s (.c .zr)) (csyms A w 0) with hX₇
  -- the layout parameters
  have s8 := dsF_umul (body := body) (W := pmW n) h R wl X₇ V (.o .uw) (.o .rR) (.o .lB)
    (.o .tm) (.o .xT) (by simp [List.nodup_cons]) (k₁ := w) (k₂ := r n) (l := [])
    (by simp [hX₇, hX₆, hX₅, hX₄, hX₃, hX₂, hX₁, huw])
    (by simp [hX₇, hX₆, hX₅, hX₄, hX₃, hX₂, hX₁, hrR])
    (by simp [hX₇, hX₆, hX₅, hX₄, hX₃, hX₂, hX₁, eB])
    (by simp [hX₇, hX₆, hX₅, hX₄, hX₃, hX₂, hX₁, htm])
    (by simp [hX₇, hX₆, hX₅, hX₄, hX₃, hX₂, hX₁, hxT])
  rw [List.append_nil, mul_comm w (r n)] at s8
  set X₈ := Function.update X₇ (.o .lB) (List.replicate (r n * w) (tick : Fin (A + 4))) with hX₈
  have s9 := dsF_ucopy (body := body) (W := pmW n) h R wl X₈ V (.o .lB) (.o .lW) (.o .tm)
    (fun e => by cases e) (fun e => by cases e) (fun e => by cases e) (c := r n * w) (l := [])
    (by simp [hX₈]) (by simp [hX₈, hX₇, hX₆, hX₅, hX₄, hX₃, hX₂, hX₁, eW])
    (by simp [hX₈, hX₇, hX₆, hX₅, hX₄, hX₃, hX₂, hX₁, htm])
  rw [List.append_nil] at s9
  set X₉ := Function.update X₈ (.o .lW) (List.replicate (r n * w) (tick : Fin (A + 4))) with hX₉
  have s10 := dsF_step (body := body) h R wl X₉ V (.o .lW)
    (dsCWL_do (A := A) (w' := pmW n) (n := n) (Wt := 0) (w := w) hB) hV0 hVlt hwl
    (l := List.replicate (r n * w) tick) (by simp [hX₉])
  rw [List.replicate_append_replicate] at s10
  have eL : (logT n - ℓ n) ^ 2 + (logT n - ℓ n) + 4 + r n * w = dsWL n w := by
    unfold dsWL; ring
  rw [eL] at s10
  set X₁₀ := Function.update X₉ (.o .lW) (List.replicate (dsWL n w) (tick : Fin (A + 4)))
    with hX₁₀
  have s11 := dsF_stepB (body := body) h R wl X₁₀ V (.o .lE) (.o .lW) (fun e => by cases e)
    (dsCE_do (A := A) (w' := pmW n) (n := n) (Wt := 0) (w := w) hB) hV0 hVlt hwl hWL
    (by simp [hX₁₀, hX₉, hX₈, hX₇, hX₆, hX₅, hX₄, hX₃, hX₂, hX₁, eE]) (by simp [hX₁₀])
  have eX : Function.update X₁₀ (.o .lE) (binSyms (dsWL n w) (dsE n)) =
      dsUpdL X (dsP2bW n w) := by
    funext y
    simp only [dsUpdL, dsP2bW, List.foldl_cons, List.foldl_nil, hX₁₀, hX₉, hX₈, hX₇, hX₆, hX₅, hX₄,
      hX₃, hX₂, hX₁, Function.update_apply]
    by_cases hy : y = .o .uq
    · subst hy; simp [huq]
    · simp only [hy, ite_false]
      split_ifs <;> simp_all
  rw [eX] at s11
  refine (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    s11)))))))))).mono ?_
  unfold dsP2bCost
  omega

end P2b

end IntegerMultBounds.MathlibTM2.Fast.TableVM
