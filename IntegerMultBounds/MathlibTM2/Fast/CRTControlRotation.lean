module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlAllFibers
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlWorkspace
import IntegerMultBounds.MathlibTM2.Fast.CRTControlBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! # The concrete indexed scanner implements the CRT rotation

The all-fibers machine is specialized to the actual CRT descriptors and box
layout. A word width of `3*B+1`, where B bounds total address width, discharges
all intermediate arithmetic fits, including invalid padding addresses.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

lemma crtControlAllOut_eq_rotOut {d : ℕ} (a s : Fin d → ℕ)
    (pre : List (Fin d)) (i : Fin d) (post : List (Fin d)) (μ : ℕ) (fwd : Bool)
    (C : (Fin d → ℕ) → List (Fin (A + 4))) (F : ℕ) :
    crtControlAllOut (crtControlFields a s i.val pre) (s i) μ fwd
      (crtControlSlots a pre i post C) F = crtControlRotOut a s pre i post μ fwd C F := by
  unfold crtControlAllOut crtControlRotOut
  split_ifs <;> rfl

lemma crtControlSlots_flatten {d : ℕ} (a : Fin d → ℕ)
    (pre : List (Fin d)) (i : Fin d) (post : List (Fin d))
    (C : (Fin d → ℕ) → List (Fin (A + 4))) :
    (List.range (2 ^ crtW a pre)).flatMap (fun F => (crtControlSlots a pre i post C F).flatten) =
      (crtBox a (pre ++ i :: post) C 0).flatten := by
  rw [crtBox_append, crt_flatten_flatMap]
  refine List.flatMap_congr fun F _ => ?_
  rw [crtBox_cons, crt_flatten_flatMap]
  simp only [crtControlSlots, List.flatMap_def]

/-- Exact machine realization of the original CRT rotation in an arbitrary
physical prefix layout. The loop, descriptor scan, modular arithmetic, physical
movement and restoration are all concrete; no assumed body execution remains. -/
theorem crtControlRotation_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (e : Fin 14 → Fin T) (he : Function.Injective e) (hrge : ∀ r j, rg r ≠ e j)
    {d : ℕ} (a s : Fin d → ℕ) (pre : List (Fin d)) (i : Fin d) (post : List (Fin d))
    (hnd : (pre ++ i :: post).Nodup) (hctrl : ∀ j : Fin d, j.val < i.val → j ∈ pre)
    (hs : ∀ j, s j ≤ 2 ^ a j) (hsi : 0 < s i) (μ : ℕ) (hμ : μ ≤ s i) (fwd : Bool)
    (B c w : ℕ) (hB : (∑ j, a j) ≤ B) (hpre : crtW a pre ≤ B)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = 3 * B + 1)
    (hnl : nl.length = w) (hw : w ≤ 3 * B + 1)
    (C : (Fin d → ℕ) → List (Fin (A + 4))) (hC : ∀ x, (C x).length = c)
    (R : Regs T A)
    (htape : R (e 0) = crtControlTape (3 * B + 1) (crtControlFields a s i.val pre))
    (hsave : R (e 1) = [])
    (hmod : R (e 2) = binSyms (3 * B + 1) (s i))
    (hmul : R (e 3) = binSyms (3 * B + 1) μ)
    (hpadding : (R (e 4)).length = 2 ^ a i - s i)
    (hslot : (R (e 5)).length = 2 ^ crtW a post * c)
    (hexponent : (R (e 8)).length = crtW a pre)
    (hclean : ∀ j : Fin 14, 9 ≤ j.val → R (e j) = [])
    (hsource : R (e 6) = (crtBox a (pre ++ i :: post) C 0).flatten)
    (hacc : R (e 7) = []) :
    crtRuns body (crtControlAllFibers rg e fwd)
      (crtBankOverlay rg R (tblRho (3 * B + 1) wl nl (crtControlState 0 0 true [])))
      (Function.update (Function.update (crtBankOverlay rg R
        (tblRho (3 * B + 1) wl nl (crtControlState
          (crtControlBoundary (crtControlFields a s i.val pre) (2 ^ crtW a pre)) 0 true [])))
        (e 7) []) (e 6) (crtBox a (pre ++ i :: post) (crtRotC s i.val i.isLt μ fwd C) 0).flatten)
      (crtControlAllCost (crtControlFields a s i.val pre).length (3 * B + 1) w
        (crtW a pre) (s i) (2 ^ a i) (2 ^ crtW a post * c)) := by
  let fs := crtControlFields a s i.val pre
  have hpow : (2 : ℕ) ^ (B + 1) ≤ 2 ^ (3 * B + 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hfields : ∀ f ∈ fs, 0 < f.place ∧ f.place < 2 ^ (3 * B + 1) ∧
      f.bound < 2 ^ (3 * B + 1) ∧ f.weight < 2 ^ (3 * B + 1) ∧ f.weight ≤ 2 ^ B := by
    intro f hf
    have hfit := crtControlFields_fit a s hs i.val B pre hB hpre f hf
    have hweight := (crtControlFields_weight_le a s hs i.val pre f hf).2
    exact ⟨hfit.1, hfit.2.1.trans_le hpow, hfit.2.2.1.trans_le hpow,
      hfit.2.2.2.trans_le hpow, hweight.trans (Nat.pow_le_pow_right (by decide) hB)⟩
  have hai : a i ≤ B := (Finset.single_le_sum (fun j _ => Nat.zero_le (a j))
    (Finset.mem_univ i)).trans hB
  have hsiB : s i ≤ 2 ^ B := (hs i).trans (Nat.pow_le_pow_right (by decide) hai)
  have hμB : μ ≤ 2 ^ B := hμ.trans hsiB
  have hBpow : (2 : ℕ) ^ B < 2 ^ (3 * B + 1) := by
    apply Nat.pow_lt_pow_right (by decide)
    omega
  have hFfit : ∀ F < 2 ^ crtW a pre, F < 2 ^ B := by
    intro F hF
    exact hF.trans_le (Nat.pow_le_pow_right (by decide) hpre)
  have hbudget : ∀ F < 2 ^ crtW a pre, F * 2 ^ B < 2 ^ (3 * B + 1) := by
    intro F hF
    have hp := Nat.mul_lt_mul_of_pos_right (hFfit F hF) (show 0 < (2 : ℕ) ^ B by positivity)
    have heq : (2 : ℕ) ^ B * 2 ^ B = 2 ^ (2 * B) := by rw [← pow_add]; congr 1; omega
    rw [heq] at hp
    exact hp.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hprod : ∀ F < 2 ^ crtW a pre, μ * crtControlValue fs F < 2 ^ (3 * B + 1) := by
    intro F hF
    exact crtControl_offset_mul_lt B μ _ hμB
      (crtControlValue_lt_pow a s hs i.val pre F B hB (hFfit F hF))
  have hslots : ∀ F < 2 ^ crtW a pre,
      (crtControlSlots a pre i post C F).length = 2 ^ a i ∧
      ∀ x ∈ crtControlSlots a pre i post C F, x.length = 2 ^ crtW a post * c := by
    intro F _
    constructor
    · simp [crtControlSlots]
    · intro x hx
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
      exact crtBox_flatten_length a post C _ c hC
  have h := crtControlAllFibers_runs (body := body) hrg e he hrge (by omega)
    (show crtW a pre ≤ 3 * B + 1 by omega) wl nl hwl hnl hw fs (2 ^ B) (s i) μ
    (2 ^ a i) (2 ^ crtW a post * c) fwd hfields hbudget hsi (hsiB.trans_lt hBpow)
    (hμB.trans_lt hBpow) hprod (crtControlSlots a pre i post C) hslots R htape hsave hmod hmul
    (by rw [hpadding]; exact (Nat.add_sub_of_le (hs i)).symm) hslot hexponent hclean
    (by rw [crtControlSlots_flatten]; exact hsource) hacc
  have hout : (List.range (2 ^ crtW a pre)).flatMap
      (crtControlAllOut fs (s i) μ fwd (crtControlSlots a pre i post C)) =
      (crtBox a (pre ++ i :: post) (crtRotC s i.val i.isLt μ fwd C) 0).flatten := by
    have hfun : crtControlAllOut fs (s i) μ fwd (crtControlSlots a pre i post C) =
        crtControlRotOut a s pre i post μ fwd C := by
      funext F
      exact crtControlAllOut_eq_rotOut a s pre i post μ fwd C F
    rw [hfun]
    exact crtControlRotOut_top a s pre i post hnd hctrl ⟨hsi, hs i⟩ μ hμ fwd C
  rw [hout] at h
  exact h

/-- A complete CRT rotation starting and ending with an empty arithmetic
workspace. Only the data source changes; all descriptor and permanent parameter
tapes, unary widths, and other registers are preserved exactly. -/
theorem crtControlRotationWorkspace_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (e : Fin 14 → Fin T) (he : Function.Injective e) (hrge : ∀ r j, rg r ≠ e j)
    {d : ℕ} (a s : Fin d → ℕ) (pre : List (Fin d)) (i : Fin d) (post : List (Fin d))
    (hnd : (pre ++ i :: post).Nodup) (hctrl : ∀ j : Fin d, j.val < i.val → j ∈ pre)
    (hs : ∀ j, s j ≤ 2 ^ a j) (hsi : 0 < s i) (μ : ℕ) (hμ : μ ≤ s i) (fwd : Bool)
    (B c w : ℕ) (hB : (∑ j, a j) ≤ B) (hpre : crtW a pre ≤ B)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = 3 * B + 1)
    (hnl : nl.length = w) (hw : w ≤ 3 * B + 1)
    (C : (Fin d → ℕ) → List (Fin (A + 4))) (hC : ∀ x, (C x).length = c)
    (R : Regs T A)
    (htape : R (e 0) = crtControlTape (3 * B + 1) (crtControlFields a s i.val pre))
    (hsave : R (e 1) = [])
    (hmod : R (e 2) = binSyms (3 * B + 1) (s i))
    (hmul : R (e 3) = binSyms (3 * B + 1) μ)
    (hpadding : (R (e 4)).length = 2 ^ a i - s i)
    (hslot : (R (e 5)).length = 2 ^ crtW a post * c)
    (hexponent : (R (e 8)).length = crtW a pre)
    (hclean : ∀ j : Fin 14, 9 ≤ j.val → R (e j) = [])
    (hsource : R (e 6) = (crtBox a (pre ++ i :: post) C 0).flatten)
    (hacc : R (e 7) = [])
    (hwr : R (rg .wr) = wl) (hwn : R (rg .wn) = nl)
    (hv : ∀ j, R (rg (.v j)) = []) (hz : ∀ j, R (rg (.z j)) = [])
    (hbankacc : R (rg .acc) = []) :
    crtRuns body
      (.seq (crtControlWorkspaceInit rg)
        (.seq (crtControlAllFibers rg e fwd) (crtControlWorkspaceClear rg))) R
      (Function.update R (e 6)
        (crtBox a (pre ++ i :: post) (crtRotC s i.val i.isLt μ fwd C) 0).flatten)
      ((10 * (4 * (3 * B + 1) + 4) + 1 + 10 * tblC (3 * B + 1) w) +
        crtControlAllCost (crtControlFields a s i.val pre).length (3 * B + 1) w
          (crtW a pre) (s i) (2 ^ a i) (2 ^ crtW a post * c) +
        (10 * (2 * (3 * B + 1) + 2) + 1)) := by
  have hinit := crtControlWorkspaceInit_runs (body := body) hrg (by omega) wl nl hwl hnl hw
    R hwr hwn hv hz
  rw [hbankacc] at hinit
  have hpass := crtControlRotation_runs (body := body) hrg e he hrge a s pre i post
    hnd hctrl hs hsi μ hμ fwd B c w hB hpre wl nl hwl hnl hw C hC R
    htape hsave hmod hmul hpadding hslot hexponent hclean hsource hacc
  let out := (crtBox a (pre ++ i :: post) (crtRotC s i.val i.isLt μ fwd C) 0).flatten
  let R' := Function.update R (e 6) out
  let st : TblSt 10 A := crtControlState
    (crtControlBoundary (crtControlFields a s i.val pre) (2 ^ crtW a pre)) 0 true []
  have hout : Function.update (Function.update (crtBankOverlay rg R
      (tblRho (3 * B + 1) wl nl st)) (e 7) []) (e 6) out =
      crtBankOverlay rg R' (tblRho (3 * B + 1) wl nl st) := by
    funext j
    by_cases hj : ∃ r, rg r = j
    · obtain ⟨r, rfl⟩ := hj
      simp [crtBankOverlay_on hrg, hrge]
    · have hj' : ∀ r, rg r ≠ j := by simpa using hj
      simp only [crtBankOverlay_off _ _ _ _ hj', R', Function.update_apply]
      split_ifs <;> simp_all
  have hclear := crtControlWorkspace_restore (body := body) hrg (3 * B + 1) wl nl st R'
    (by intro j; simpa [R', hrge] using hv j)
    (by intro j; simpa [R', hrge] using hz j)
    (by simpa [R', hrge] using hwr) (by simpa [R', hrge] using hwn)
    (by simp [R', st, crtControlState, hrge, hbankacc])
  exact crtRuns_mono (crtRuns_seq hinit (crtRuns_seq (crtRuns_congr hpass hout) hclear)) (by omega)

end IntegerMultBounds.MathlibTM2.Fast
