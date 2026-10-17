module

public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectEntry
public import IntegerMultBounds.MathlibTM2.Fast.SrcStage
public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectBacking
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Direct CRT layouts at the source-stage interface -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Mult
open scoped Function
noncomputable section
variable {T Q K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- The entry cost extended to arbitrary dimensions; zero is excluded by the run contract. -/
def crtDirectSourceCost (fwd : Bool) (T c : ℕ) : {d : ℕ} → (Fin d → ℕ) → (Fin d → ℕ) → (Fin d → ℕ) → ℕ
  | 0, _, _, _ => 0
  | _ + 1, a, s, m => crtDirectEntryCost (K := K) fwd T c a s m

lemma crtDirectSource_dimension {d : ℕ} (a s : Fin d → ℕ)
    (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j) : d ≤ crtPre a d := by
  have ha : ∀ j, 1 ≤ a j := by
    intro j
    have h := hs j
    by_contra hn
    have hz : a j = 0 := by omega
    simp [hz] at h
    omega
  rw [crtPre, crtLow_of_le le_rfl]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => ha j)
  simpa using h

/-- The fixed direct program with its legacy register backing. -/
def crtDirectSourceForward
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (r : CrtReg → Fin T) : Pr P T Q (prime + K) U :=
  crtDirectEntryForward hQ ι hι hT (r ∘ crtDirectBank) (r ∘ crtDirectExternal)

def crtDirectSourceInverse
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (r : CrtReg → Fin T) : Pr P T Q (prime + K) U :=
  crtDirectEntryInverse hQ ι hι hT (r ∘ crtDirectBank) (r ∘ crtDirectExternal)

theorem crtDirectSourceForward_runs {d : ℕ} (hd0 : 0 < d)
    (a s : Fin d → ℕ) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hcop : Pairwise (Nat.Coprime on s)) (hadj : ∀ j k, a j ≤ a k + 1)
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (r : CrtReg → Fin T) (hr : Function.Injective r) (hrι : ∀ q j, r q ≠ ι j)
    (l : List (List (Fin (prime + K + 4)))) (z : List (Fin (prime + K + 4))) (c : ℕ) (hc : 0 < c)
    (hl : l.length = crtProd s d) (hlc : ∀ x ∈ l, x.length = c) (hzc : z.length = c)
    (hl8 : ∀ x ∈ l, ∀ b ∈ x, b.val < 8) (hz8 : ∀ b ∈ z, b.val < 8)
    (R : Regs T (prime + K)) (hstr : R (r .str) = l.flatten)
    (hwt : R (r .wT) = crtEnts ((crtRevAx d).map a))
    (hst : R (r .sT) = crtEnts ((crtRevAx d).map s))
    (hmt : R (r .mT) = crtEnts ((crtRevAx d).map fun j => (crtMu s hcop j : ZMod (s j)).val))
    (hsig : R (r .sig) = binSyms (crtPre a d) (crtSig a s d))
    (hmask : R (r .msk) = binSyms (crtPre a d) (crtMask a d))
    (hzr : R (r .zr) = z)
    (hrest : ∀ q ∈ crtRestEmpty, R (r q) = []) (hbank : ∀ j, R (ι j) = []) :
    crtRuns body (crtDirectSourceForward hQ ι hι hT r) R
      (Function.update R (r .str) (crtBox a (List.finRange d) (crtSpecC s hcop l z) 0).flatten)
      (crtDirectSourceCost (K := K) true T c a s (fun j => (crtMu s hcop j : ZMod (s j)).val)) := by
  cases d with
  | zero => omega
  | succ d =>
    let m := fun j => (crtMu s hcop j : ZMod (s j)).val
    let : ∀ j, NeZero (s j) := fun j => ⟨(hs j).1.ne'⟩
    have hm : ∀ j, m j ≤ s j := fun j => (ZMod.val_lt _).le
    have hin : CrtDirectEntryInputs (r ∘ crtDirectBank) (r ∘ crtDirectExternal) ι R a s m c := by
      constructor
      · exact hwt
      · exact hst
      · exact hmt
      · exact hsig
      · exact hmask
      · rw [show (r ∘ crtDirectExternal) 11 = r .zr from rfl, hzr]; exact hzc
      · intro j hj
        apply hrest _ (crtDirectExternal_mem_rest j ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        all_goals intro h; subst j; simp at hj
      · intro q; exact hrest _ (crtDirectBank_mem_rest q)
      · exact hbank
    have h := crtDirectEntryForward_runs (bodyC := body) hQ ι hι hT
      (r ∘ crtDirectBank) (hr.comp crtDirectBank_injective)
      (r ∘ crtDirectExternal) (hr.comp crtDirectExternal_injective)
      (fun q j => hr.ne (crtDirectBank_ne_external q j))
      (fun j k => (hrι _ _).symm) (fun j q => (hrι _ _).symm)
      a s m hadj hs hm (crtDirectSource_dimension a s hs) c hc R hin
      l z hl hlc hzc hl8 hz8 hstr hzr
    rw [crtFwdC_spec s (fun j => (hs j).1) hcop] at h
    exact h

theorem crtDirectSourceInverse_runs {d : ℕ} (hd0 : 0 < d)
    (a s : Fin d → ℕ) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hcop : Pairwise (Nat.Coprime on s)) (hadj : ∀ j k, a j ≤ a k + 1)
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (r : CrtReg → Fin T) (hr : Function.Injective r) (hrι : ∀ q j, r q ≠ ι j)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (c : ℕ) (hc : 0 < c)
    (hC : ∀ x, (C x).length = c) (h8 : ∀ x, ∀ b ∈ C x, b.val < 8)
    (R : Regs T (prime + K)) (hstr : R (r .str) = (crtBox a (List.finRange d) C 0).flatten)
    (hwt : R (r .wT) = crtEnts ((crtRevAx d).map a))
    (hst : R (r .sT) = crtEnts ((crtRevAx d).map s))
    (hmt : R (r .mT) = crtEnts ((crtRevAx d).map fun j => (crtMu s hcop j : ZMod (s j)).val))
    (hsig : R (r .sig) = binSyms (crtPre a d) (crtSig a s d))
    (hmask : R (r .msk) = binSyms (crtPre a d) (crtMask a d))
    (hzr : (R (r .zr)).length = c)
    (hrest : ∀ q ∈ crtRestEmpty, R (r q) = []) (hbank : ∀ j, R (ι j) = []) :
    crtRuns body (crtDirectSourceInverse hQ ι hι hT r) R
      (Function.update R (r .str) ((List.range (∏ j, s j)).map fun k => C fun j => (crtPhi s hcop ((k : ℕ) : ZMod (∏ i, s i)) j).val).flatten)
      (crtDirectSourceCost (K := K) false T c a s (fun j => (crtMu s hcop j : ZMod (s j)).val)) := by
  cases d with
  | zero => omega
  | succ d =>
    let m := fun j => (crtMu s hcop j : ZMod (s j)).val
    let : ∀ j, NeZero (s j) := fun j => ⟨(hs j).1.ne'⟩
    have hm : ∀ j, m j ≤ s j := fun j => (ZMod.val_lt _).le
    have hin : CrtDirectEntryInputs (r ∘ crtDirectBank) (r ∘ crtDirectExternal) ι R a s m c := by
      constructor
      · exact hwt
      · exact hst
      · exact hmt
      · exact hsig
      · exact hmask
      · exact hzr
      · intro j hj
        apply hrest _ (crtDirectExternal_mem_rest j ?_ ?_ ?_ ?_ ?_ ?_ ?_)
        all_goals intro h; subst j; simp at hj
      · intro q; exact hrest _ (crtDirectBank_mem_rest q)
      · exact hbank
    have h := crtDirectEntryInverse_runs (bodyC := body) hQ ι hι hT
      (r ∘ crtDirectBank) (hr.comp crtDirectBank_injective)
      (r ∘ crtDirectExternal) (hr.comp crtDirectExternal_injective)
      (fun q j => hr.ne (crtDirectBank_ne_external q j))
      (fun j k => (hrι _ _).symm) (fun j q => (hrι _ _).symm)
      a s m hadj hs hm (crtDirectSource_dimension a s hs) c hc R hin
      C hC h8 hstr
    have hout : ((List.range (crtProd s (d + 1))).map fun k =>
        crtInvC s m C (d + 1) (crtUnrank s k)).flatten =
        ((List.range (∏ j, s j)).map fun k => C fun j =>
          (crtPhi s hcop ((k : ℕ) : ZMod (∏ i, s i)) j).val).flatten := by
      rw [crtProd, crtLow_of_le le_rfl]
      congr 1
      apply List.map_congr_left
      intro k hk
      exact crtInvC_spec s (fun j => (hs j).1) hcop C (List.mem_range.mp hk)
    rw [hout] at h
    exact h

end
end IntegerMultBounds.MathlibTM2.Fast

namespace IntegerMultBounds.MathlibTM2.Fast.Src

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open scoped Function

variable {t₀ T Q K n : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- Exact direct CRT cost at the source-stage dimensions and record width. -/
noncomputable def srcDirectCrtCost (fwd : Bool) (T n w : ℕ) :=
  crtDirectSourceCost (K := K) fwd T w (srcAx n) (s n)
    (fun j => (crtMu (s n) (s_pairwise n) j : ZMod (s n j)).val)

theorem srcDirectCrtF_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) (hbig : Big n) {w : ℕ}
    (hw : 1 ≤ w) (E : SrcF t₀ (prime + K)) (hC : SrcCrtBase E.c E.cb n w)
    (u : ZMod (∏ i, s n i) → ℂ)
    (hstr : E.c .str = cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) u)) :
    RsaRuns body M.rg M.ι (crtDirectSourceForward M.hQc M.rcb M.hrcb M.hTc M.rc) E.get
      { E with c := (Function.update E.c .str (cstream (prime + K) w
          (srcPad (p n) (s n) (t n) fun x => u ((crtPhi (s n) (s_pairwise n)).symm x)))) }.get
      (srcDirectCrtCost (K := K) true T n w) := by
  have h := src_of_crt (body := body) (ι := M.ι) M.hrg (ρ := E.get) (x := .c .str)
    (l := cstream (prime + K) w
      (srcPad (p n) (s n) (t n) fun x => u ((crtPhi (s n) (s_pairwise n)).symm x)))
    (b := srcDirectCrtCost (K := K) true T n w) fun S _ hS => by
      have hb := fun j => src_ax_bounds (n := n) j
      have H := crtDirectSourceForward_runs (body := body) (srcHd0 hbig) (srcAx n) (s n) (src_crt_hs hbig) (s_pairwise n)
        (fun j j' => by have := hb j; have := hb j'; omega) M.hQc M.rcb M.hrcb M.hTc M.rc M.hrc
        (src_crt_rι M) ((srcCoef (p n) (∏ i, s n i) u).map (csyms (prime + K) w))
        (csyms (prime + K) w 0) w hw (by simp [src_length_coef, crtProd, crtLow_of_le le_rfl])
        (fun x hx => by
          obtain ⟨N, -, rfl⟩ := List.mem_map.1 hx
          simp [csyms])
        (by simp [csyms])
        (fun x hx => by
          obtain ⟨N, -, rfl⟩ := List.mem_map.1 hx
          exact src_csyms_lt (by omega) N)
        (src_csyms_lt (by omega) 0) S.R
        (by rw [show S.R (M.rc .str) = E.c .str from hS (.c .str), hstr, cstream,
          List.flatMap_def])
        (by rw [show S.R (M.rc .wT) = E.c .wT from hS (.c .wT), hC.wT])
        (by rw [show S.R (M.rc .sT) = E.c .sT from hS (.c .sT), hC.sT])
        (by rw [show S.R (M.rc .mT) = E.c .mT from hS (.c .mT), hC.mT])
        (by rw [show S.R (M.rc .sig) = E.c .sig from hS (.c .sig), hC.sig])
        (by rw [show S.R (M.rc .msk) = E.c .msk from hS (.c .msk), hC.msk])
        (by rw [show S.R (M.rc .zr) = E.c .zr from hS (.c .zr), hC.zr])
        (fun x hx => by rw [show S.R (M.rc x) = E.c x from hS (.c x)]; exact hC.rest x hx)
        (fun i => by rw [show S.R (M.rcb i) = E.cb i from hS (.cb i)]; exact hC.bank i)
      rw [src_crt_fwd (s n) (s_pairwise n) (srcAx n) (t n) (src_t_eq n)] at H
      exact H
  rwa [SrcF.upd_c] at h

theorem srcDirectCrtI_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) (hbig : Big n) {w : ℕ}
    (hw : 1 ≤ w) (E : SrcF t₀ (prime + K)) (hC : SrcCrtBase E.c E.cb n w)
    (g : ((i : Fin (d n)) → ZMod (s n i)) → ℂ)
    (hstr : E.c .str = cstream (prime + K) w (srcPad (p n) (s n) (t n) g)) :
    RsaRuns body M.rg M.ι (crtDirectSourceInverse M.hQc M.rcb M.hrcb M.hTc M.rc) E.get
      { E with c := (Function.update E.c .str (cstream (prime + K) w
          (srcCoef (p n) (∏ i, s n i) fun k => g (crtPhi (s n) (s_pairwise n) k)))) }.get
      (srcDirectCrtCost (K := K) false T n w) := by
  have h := src_of_crt (body := body) (ι := M.ι) M.hrg (ρ := E.get) (x := .c .str)
    (l := cstream (prime + K) w
      (srcCoef (p n) (∏ i, s n i) fun k => g (crtPhi (s n) (s_pairwise n) k)))
    (b := srcDirectCrtCost (K := K) false T n w) fun S _ hS => by
      have hb := fun j => src_ax_bounds (n := n) j
      have H := crtDirectSourceInverse_runs (body := body) (srcHd0 hbig) (srcAx n) (s n) (src_crt_hs hbig) (s_pairwise n)
        (fun j j' => by have := hb j; have := hb j'; omega) M.hQc M.rcb M.hrcb M.hTc M.rc M.hrc
        (src_crt_rι M) (fun y => csyms (prime + K) w (srcRec (p n) (s n) g y)) w hw
        (fun y => by simp [csyms]) (fun y => src_csyms_lt (by omega) _) S.R
        (by rw [show S.R (M.rc .str) = E.c .str from hS (.c .str), hstr,
          src_crt_inv_box (s n) (srcAx n) (t n) (src_t_eq n)])
        (by rw [show S.R (M.rc .wT) = E.c .wT from hS (.c .wT), hC.wT])
        (by rw [show S.R (M.rc .sT) = E.c .sT from hS (.c .sT), hC.sT])
        (by rw [show S.R (M.rc .mT) = E.c .mT from hS (.c .mT), hC.mT])
        (by rw [show S.R (M.rc .sig) = E.c .sig from hS (.c .sig), hC.sig])
        (by rw [show S.R (M.rc .msk) = E.c .msk from hS (.c .msk), hC.msk])
        (by rw [show S.R (M.rc .zr) = E.c .zr from hS (.c .zr), hC.zr]; simp [csyms])
        (fun x hx => by rw [show S.R (M.rc x) = E.c x from hS (.c x)]; exact hC.rest x hx)
        (fun i => by rw [show S.R (M.rcb i) = E.cb i from hS (.cb i)]; exact hC.bank i)
      rw [src_crt_inv (s n) (s_pairwise n)] at H
      exact H
  rwa [SrcF.upd_c] at h

end IntegerMultBounds.MathlibTM2.Fast.Src
