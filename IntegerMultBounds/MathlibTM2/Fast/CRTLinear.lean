module

public import IntegerMultBounds.MathlibTM2.Fast.CRTGap
public import IntegerMultBounds.MathlibTM2.Fast.CRTSchedule
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # Executable distant CRT routing
Header preparation, one distant exchange, and header cleanup form a finite-host
program. This module does not implement the descriptor-controlled rotation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2

variable {T Q A : ℕ} {U F : Type}

/-- Prepare adjacent headers and upgrade the middle-count header for a gap. -/
def crtGapHdrP (uU gU vU aJ aK e3B tu t₁ t₂ : Fin T) (hdr : Fin 5 → Fin T) :
    Pr F T Q A U :=
  .seq (crtHdrP uU vU aJ aK e3B tu t₁ t₂ hdr) (crtGapHeaderP gU (hdr 1) t₁)

def crtGapHdrRegs (hdr : Fin 5 → Fin T) (R : Regs T A)
    (u g v h w : ℕ) (e : List Bool) : Regs T A :=
  Function.update (crtHdrRegs hdr R u v h w e) (hdr 1)
    (separator :: (List.replicate g false ++ [true]).map bitSymbol)

lemma crtGapHdrRegs_hdr {hdr : Fin 5 → Fin T} (hinj : Function.Injective hdr)
    (R : Regs T A) (u g v h w : ℕ) (e : List Bool) (k : Fin 5) :
    crtGapHdrRegs hdr R u g v h w e (hdr k) =
      separator :: (crtGapHdrBits u g v h w e k).map bitSymbol := by
  by_cases hk : k = 1
  · subst k; simp [crtGapHdrRegs, crtGapHdrBits]
  · rw [crtGapHdrRegs, Function.update_of_ne (fun h => hk (hinj h)),
      crtHdrRegs_hdr hinj, crtGapHdrBits, Function.update_of_ne hk]

lemma crtGapHdrRegs_of_ne {hdr : Fin 5 → Fin T} (R : Regs T A)
    (u g v h w : ℕ) (e : List Bool) {r : Fin T} (hr : ∀ k, hdr k ≠ r) :
    crtGapHdrRegs hdr R u g v h w e r = R r := by
  rw [crtGapHdrRegs, Function.update_of_ne (hr 1).symm,
    crtHdrRegs_of_ne R _ _ _ _ e hr]

theorem crtGapHdrP_runs {body : F → Pr F T Q A U}
    {uU gU vU aJ aK e3B tu t₁ t₂ : Fin T} {hdr : Fin 5 → Fin T}
    (hreg : [uU, gU, vU, aJ, aK, e3B, tu, t₁, t₂, hdr 0, hdr 1, hdr 2, hdr 3, hdr 4].Nodup)
    (R : Regs T A) (e : List Bool) (he3 : R e3B = e.map bitSymbol)
    (htu : R tu = []) (ht₁ : R t₁ = []) (ht₂ : R t₂ = []) (hh : ∀ k, R (hdr k) = []) :
    crtRuns body (crtGapHdrP uU gU vU aJ aK e3B tu t₁ t₂ hdr) R
      (crtGapHdrRegs hdr R (R uU).length (R gU).length (R vU).length
        (R aJ).length (R aK).length e)
      (4 * (R uU).length + 4 * (R gU).length + 4 * (R vU).length + 6 * e.length +
        (R aJ).length * (4 * (R aJ).length + 11) +
        (R aK).length * (4 * (R aK).length + 11) + 48) := by
  have hreg' := hreg
  regs_ne hreg'
  have hinj : Function.Injective hdr := List.nodup_ofFn.mp (by
    change [hdr 0, hdr 1, hdr 2, hdr 3, hdr 4].Nodup
    regs_nodup)
  have hp := crtHdrP_runs (body := body) (uU := uU) (vU := vU)
    (aJ := aJ) (aK := aK) (e3B := e3B) (tu := tu) (t₁ := t₁) (t₂ := t₂)
    (hdr := hdr) (by regs_nodup) R e he3 htu ht₁ ht₂ hh
  let R₁ := crtHdrRegs hdr R (R uU).length (R vU).length (R aJ).length (R aK).length e
  have hgap : R₁ gU = R gU := crtHdrRegs_of_ne R _ _ _ _ e (by
    intro k; fin_cases k <;> apply Ne.symm <;> assumption)
  have hg := crtGapHeaderP_runs (body := body) ‹gU ≠ hdr 1› ‹gU ≠ t₁›
    (Ne.symm ‹t₁ ≠ hdr 1›) R₁
    (by dsimp only [R₁]; rw [crtHdrRegs_hdr hinj]; simp [crtHdrBits])
    (by dsimp only [R₁]; rw [crtHdrRegs_of_ne R _ _ _ _ e (by intro k; fin_cases k <;> apply Ne.symm <;> assumption)]; exact ht₁)
  rw [hgap] at hg
  exact crtRuns_mono (crtRuns_seq hp hg) (by omega)

noncomputable section
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {K d : ℕ}

/-- Prepare all five headers, exchange across the gap, then empty the headers. -/
def crtGapSwapStep (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (str stmp uU gU vU aJ aK e3B tu t₁ t₂ : Fin T) : Pr F T Q (prime + K) U :=
  .seq (crtGapHdrP uU gU vU aJ aK e3B tu t₁ t₂ fun k => ι (reg (crtHd k)))
    (.seq (swapPass crtHd crtPay crtHd_inj hQ ι hι hT str stmp)
      (crtHdrClear fun k => ι (reg (crtHd k))))

variable (a : Fin d → ℕ)
theorem crtGapSwapStep_runs {body : F → Pr F T Q (prime + K) U}
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    {str stmp uU gU vU aJ aK e3B tu t₁ t₂ : Fin T}
    (hreg : [str, stmp, uU, gU, vU, aJ, aK, e3B, tu, t₁, t₂].Nodup)
    (hbank : ∀ r ∈ [str, stmp, uU, gU, vU, aJ, aK, e3B, tu, t₁, t₂], ∀ j, ι j ≠ r)
    (pre gap post : List (Fin d)) (j k : Fin d) (hjk : j ≠ k) (hjgap : j ∉ gap) (hkgap : k ∉ gap) (hj : a j ≤ a k + 1)
    (hk : a k ≤ a j + 1)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ s ∈ C y, s.val < 8) (x : Fin d → ℕ)
    (R : Regs T (prime + K)) (hstr : R str = (crtBox a (pre ++ j :: (gap ++ k :: post)) C x).flatten)
    (hu : (R uU).length = crtW a pre) (hg : (R gU).length = crtW a gap) (hv : (R vU).length = crtW a post)
    (haJ : (R aJ).length = a j) (haK : (R aK).length = a k)
    (he3 : R e3B = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (hstmp : R stmp = []) (htu : R tu = []) (ht₁ : R t₁ = []) (ht₂ : R t₂ = [])
    (hι0 : ∀ i, R (ι i) = []) :
    crtRuns body (crtGapSwapStep hQ ι hι hT str stmp uU gU vU aJ aK e3B tu t₁ t₂) R
      (Function.update R str (crtBox a (pre ++ k :: (gap ++ j :: post)) C x).flatten)
      ((T + 12 * swapT 6 + 5) * crtSwapCostN (3 * (2 ^ crtW a (pre ++ j :: (gap ++ k :: post)) * B))
          (a j) (a k) +
        (6 * swapT 6 + 10) * (crtW a pre + crtW a gap + crtW a post + 3 * B + a j + a k + 2) +
        34 * (2 ^ crtW a (pre ++ j :: (gap ++ k :: post)) * B) + 2 * T + 6 * swapT 6 +
        4 * crtW a pre + 4 * crtW a gap + 4 * crtW a post + 18 * B +
        a j * (4 * a j + 11) + a k * (4 * a k + 11) + 88) := by
  have hreg' := hreg
  regs_ne hreg'
  set hdr : Fin 5 → Fin T := fun k => ι (reg (crtHd k)) with hhdr
  have hdr_inj : Function.Injective hdr := fun a b h =>
    crtHd_inj (BinaryInterchangeRun.slot_injective (hι h))
  have hb : ∀ r ∈ [str, stmp, uU, gU, vU, aJ, aK, e3B, tu, t₁, t₂], ∀ k, hdr k ≠ r :=
    fun r hr k => hbank r hr _
  have hreg₂ : [uU, gU, vU, aJ, aK, e3B, tu, t₁, t₂, hdr 0, hdr 1, hdr 2, hdr 3, hdr 4].Nodup := by
    have e : [uU, gU, vU, aJ, aK, e3B, tu, t₁, t₂, hdr 0, hdr 1, hdr 2, hdr 3, hdr 4] =
        [uU, gU, vU, aJ, aK, e3B, tu, t₁, t₂] ++ List.ofFn hdr := rfl
    rw [e, List.nodup_append]
    refine ⟨by regs_nodup, List.nodup_ofFn.2 hdr_inj, ?_⟩
    intro r hr r' hr' hrr
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hr'
    exact hb r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)) k hrr.symm
  set n := 2 ^ crtW a (pre ++ j :: (gap ++ k :: post)) * B with hn
  set e := GrowingCounterData.advance (3 * B) [] with he
  have hevalue : Counter.value e = 3 * B := GrowingCounterData.empty_value _
  have helen : e.length ≤ 3 * B := crt_advance_length _
  have helast : e.getLast? = some true := by
    rcases GrowingCounterData.advance_canonical (3 * B) [] (Or.inl rfl) with h | h
    · rw [← he] at h; rw [h] at hevalue; simp [Counter.value] at hevalue; omega
    · exact h
  -- the headers
  have h₁ := crtGapHdrP_runs (body := body) hreg₂ R e he3 htu ht₁ ht₂ (fun k => hι0 _)
  rw [hu, hg, hv, haJ, haK] at h₁
  set R₁ := crtGapHdrRegs hdr R (crtW a pre) (crtW a gap) (crtW a post) (a j) (a k) e with hR₁
  have hR₁hdr : ∀ k', R₁ (hdr k') =
      separator :: (crtGapHdrBits (crtW a pre) (crtW a gap) (crtW a post) (a j) (a k) e k').map bitSymbol :=
    crtGapHdrRegs_hdr hdr_inj R _ _ _ _ _ e
  have hR₁oth : ∀ r, (∀ k', hdr k' ≠ r) → R₁ r = R r := fun r hr =>
    crtGapHdrRegs_of_ne R _ _ _ _ _ e hr
  set H := crtW a pre + crtW a gap + crtW a post + 3 * B + a j + a k + 2 with hH
  have hbits : ∀ k', (crtGapHdrBits (crtW a pre) (crtW a gap) (crtW a post) (a j) (a k) e k').length + 1 ≤ H := by
    intro k'
    have l3 := crt_advance_length (a j)
    have l4 := crt_advance_length (a k)
    fin_cases k' <;> simp [crtGapHdrBits, crtHdrBits, hH] <;> omega
  have hR₁len : ∀ i, (R₁ (ι i)).length ≤ H := by
    intro i
    by_cases hi : ∃ k', hdr k' = ι i
    · obtain ⟨k', hk'⟩ := hi
      rw [← hk', hR₁hdr]; simpa using hbits k'
    · rw [hR₁oth _ (fun k' hk' => hi ⟨k', hk'⟩), hι0]; simp
  -- the swap pass
  have hvals : ∀ k', Counter.value (crtGapHdrBits (crtW a pre) (crtW a gap)
      (crtW a post) (a j) (a k) e k') = BinaryInterchangeRun.values
      (2 ^ crtW a pre) (2 ^ crtW a gap) (3 * (2 ^ crtW a post * B)) (a j) (a k) k' := by
    intro k'
    rw [crtGapHdrBits_value, hevalue]
    congr 1
    ring
  have h₂raw := crtSwapGapPass_runs (body := body) a hQ ι hι hT str stmp ‹str ≠ stmp›
    (fun i => hbank str (by simp) i) (fun i => hbank stmp (by simp) i)
    pre gap post j k hjk hjgap hkgap ⟨hj, hk⟩ C B hB hC h8 x
    (crtGapHdrBits (crtW a pre) (crtW a gap) (crtW a post) (a j) (a k) e)
    hvals (crtGapHdrBits_canonical _ _ _ _ _ e helast) R₁
    (by rw [hR₁oth _ (hb str (by simp)), hstr])
    (by rw [hR₁oth _ (hb stmp (by simp)), hstmp])
    (by
      rw [hR₁oth _ (fun k' hk' => crtHd_ne_pay k'
        (BinaryInterchangeRun.slot_injective (hι hk'))), hι0])
    (fun i hi => by
      rw [hR₁oth _ (fun k' hk' => by
        have h2 : (reg (crtHd k')).val = i.val := congrArg Fin.val (hι hk')
        rw [reg_val] at h2
        have := (crtHd k').isLt
        omega), hι0])
    hR₁hdr
  have h₂ : crtRuns body (swapPass crtHd crtPay crtHd_inj hQ ι hι hT str stmp) R₁
      (Function.update R₁ str (crtBox a (pre ++ k :: (gap ++ j :: post)) C x).flatten)
      ((T + 12 * swapT 6 + 5) * crtSwapCostN (3 * n) (a j) (a k) + 6 * (swapT 6 * H) +
        34 * n + 2 * T + 6 * swapT 6 + 23) := by
    apply crtRuns_mono h₂raw
    have hsum : ∑ i, (R₁ (ι i)).length ≤ swapT 6 * H := by
      calc ∑ i, (R₁ (ι i)).length ≤ ∑ _i : Fin (swapT 6), H :=
          Finset.sum_le_sum fun i _ => hR₁len i
        _ = swapT 6 * H := by simp
    dsimp [n]
    omega
  -- clearing the headers
  set R₂ := Function.update R₁ str (crtBox a (pre ++ k :: (gap ++ j :: post)) C x).flatten with hR₂
  have hR₂hdr : ∀ k', R₂ (hdr k') = R₁ (hdr k') := fun k' =>
    Function.update_of_ne (hb str (by simp) k') _ _
  have c₀ := crtClear_runs (body := body) (hdr 0) R₂
  have c₁ := crtClear_runs (body := body) (hdr 1) (Function.update R₂ (hdr 0) [])
  have c₂ := crtClear_runs (body := body) (hdr 2)
    (Function.update (Function.update R₂ (hdr 0) []) (hdr 1) [])
  have c₃ := crtClear_runs (body := body) (hdr 3)
    (Function.update (Function.update (Function.update R₂ (hdr 0) []) (hdr 1) []) (hdr 2) [])
  have c₄ := crtClear_runs (body := body) (hdr 4)
    (Function.update (Function.update (Function.update (Function.update R₂ (hdr 0) []) (hdr 1) [])
      (hdr 2) []) (hdr 3) [])
  have hne : ∀ x y : Fin 5, x ≠ y → hdr x ≠ hdr y := fun x y h e => h (hdr_inj e)
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq c₀
    (crtRuns_seq c₁ (crtRuns_seq c₂ (crtRuns_seq c₃ c₄)))))) ?_) ?_
  · funext r
    by_cases hr : ∃ k', hdr k' = r
    · obtain ⟨k', rfl⟩ := hr
      rw [Function.update_of_ne (hb str (by simp) k'), show R (hdr k') = [] from hι0 _]
      fin_cases k' <;> simp [hdr_inj.eq_iff]
    · have hr' : ∀ k', hdr k' ≠ r := fun k' hk' => hr ⟨k', hk'⟩
      simp only [Function.update_of_ne (Ne.symm (hr' 0)), Function.update_of_ne (Ne.symm (hr' 1)),
        Function.update_of_ne (Ne.symm (hr' 2)), Function.update_of_ne (Ne.symm (hr' 3)),
        Function.update_of_ne (Ne.symm (hr' 4)), hR₂]
      by_cases hs : r = str
      · rw [hs]; simp
      · rw [Function.update_of_ne hs, Function.update_of_ne hs, hR₁oth r hr']
  · have l : ∀ k', (R₂ (hdr k')).length ≤ H := fun k' => by
      rw [hR₂hdr, hR₁hdr]; simpa using hbits k'
    simp only [Function.update_of_ne (hne _ _ (by decide : (1 : Fin 5) ≠ 0)),
      Function.update_of_ne (hne _ _ (by decide : (2 : Fin 5) ≠ 0)),
      Function.update_of_ne (hne _ _ (by decide : (2 : Fin 5) ≠ 1)),
      Function.update_of_ne (hne _ _ (by decide : (3 : Fin 5) ≠ 0)),
      Function.update_of_ne (hne _ _ (by decide : (3 : Fin 5) ≠ 1)),
      Function.update_of_ne (hne _ _ (by decide : (3 : Fin 5) ≠ 2)),
      Function.update_of_ne (hne _ _ (by decide : (4 : Fin 5) ≠ 0)),
      Function.update_of_ne (hne _ _ (by decide : (4 : Fin 5) ≠ 1)),
      Function.update_of_ne (hne _ _ (by decide : (4 : Fin 5) ≠ 2)),
      Function.update_of_ne (hne _ _ (by decide : (4 : Fin 5) ≠ 3))]
    have l0 := l 0
    have l1 := l 1
    have l2 := l 2
    have l3 := l 3
    have l4 := l 4
    nlinarith

/-- Every nonzero target has the required concrete prefix/gap decomposition. -/
theorem crtExpose_split {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) :
    ∃ pre gap, crtOuterAxes n = pre ++ i :: gap := by
  apply List.mem_iff_append.mp
  have h := (crt_mem_revAx (m := n + 1) i).mpr i.isLt
  rw [crtRevAx_eq_outer] at h
  simpa [hi] using h

/-- Decompose exposure into the physical gap exchanged by the host program. -/
theorem crtExpose_gap_layout {n : ℕ} (i : Fin (n + 1))
    (pre gap : List (Fin (n + 1))) (hsplit : crtOuterAxes n = pre ++ i :: gap) :
    crtRevAx (d := n + 1) (n + 1) = pre ++ i :: (gap ++ 0 :: []) ∧
      crtExposePrefix i ++ [i] = pre ++ 0 :: (gap ++ i :: []) ∧
      i ∉ gap ∧ (0 : Fin (n + 1)) ∉ gap := by
  have hlay : crtRevAx (d := n + 1) (n + 1) = pre ++ i :: (gap ++ 0 :: []) := by
    rw [crtRevAx_eq_outer, hsplit]; simp only [List.append_assoc, List.cons_append]
  have hnd : (pre ++ i :: gap ++ (0 : Fin (n + 1)) :: []).Nodup := by
    simpa only [List.append_assoc, List.cons_append] using hlay ▸ crtRevAx_nodup (n + 1)
  have he : crtExposePrefix i ++ [i] = pre ++ 0 :: (gap ++ i :: []) := by
    rw [← crtExpose_layout, hlay]
    simpa only [List.append_assoc, List.cons_append] using
      crtAxisExchange_gap pre gap [] i 0 hnd
  refine ⟨hlay, he, ?_, ?_⟩
  · have hn := (List.nodup_append.mp hnd).1
    exact (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  · have hn := (List.nodup_append.mp hnd).2.2
    intro hz
    exact hn 0 (by simp [hz]) 0 (by simp) rfl

/-- Execute exposure of the target as innermost axis, including header preparation and cleanup. -/
theorem crtExposeStep_runs {n : ℕ} (a : Fin (n + 1) → ℕ) {body : F → Pr F T Q (prime + K) U}
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    {str stmp uU gU vU aJ aK e3B tu t₁ t₂ : Fin T}
    (hreg : [str, stmp, uU, gU, vU, aJ, aK, e3B, tu, t₁, t₂].Nodup)
    (hbank : ∀ r ∈ [str, stmp, uU, gU, vU, aJ, aK, e3B, tu, t₁, t₂], ∀ i, ι i ≠ r)
    (i : Fin (n + 1)) (hi : i ≠ 0) (pre gap : List (Fin (n + 1)))
    (hsplit : crtOuterAxes n = pre ++ i :: gap) (hj : a i ≤ a 0 + 1)
    (hk : a 0 ≤ a i + 1)
    (C : (Fin (n + 1) → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ s ∈ C y, s.val < 8) (x : Fin (n + 1) → ℕ)
    (R : Regs T (prime + K)) (hstr : R str = (crtBox a (crtRevAx (d := n + 1) (n + 1)) C x).flatten)
    (hu : (R uU).length = crtW a pre) (hg : (R gU).length = crtW a gap) (hv : (R vU).length = 0)
    (haJ : (R aJ).length = a i) (haK : (R aK).length = a 0)
    (he3 : R e3B = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (hstmp : R stmp = []) (htu : R tu = []) (ht₁ : R t₁ = []) (ht₂ : R t₂ = [])
    (hι0 : ∀ i, R (ι i) = []) :
    crtRuns body (crtGapSwapStep hQ ι hι hT str stmp uU gU vU aJ aK e3B tu t₁ t₂) R
      (Function.update R str (crtBox a (crtExposePrefix i ++ [i]) C x).flatten)
      ((T + 12 * swapT 6 + 5) * crtSwapCostN (3 * (2 ^ crtW a (pre ++ i :: (gap ++ 0 :: [])) * B))
          (a i) (a 0) +
        (6 * swapT 6 + 10) * (crtW a pre + crtW a gap + 3 * B + a i + a 0 + 2) +
        34 * (2 ^ crtW a (pre ++ i :: (gap ++ 0 :: [])) * B) + 2 * T + 6 * swapT 6 +
        4 * crtW a pre + 4 * crtW a gap + 18 * B +
        a i * (4 * a i + 11) + a 0 * (4 * a 0 + 11) + 88) := by
  obtain ⟨hlay, he, hig, hzg⟩ := crtExpose_gap_layout i pre gap hsplit
  have h := crtGapSwapStep_runs (body := body) a hQ ι hι hT hreg hbank pre gap [] i 0 hi hig hzg
    hj hk C B hB hC h8 x R (by rwa [← hlay])
    hu hg hv haJ haK he3 hstmp htu ht₁ ht₂ hι0
  rw [← he] at h
  simpa only [crtW_nil, Nat.add_zero, Nat.mul_zero] using h

/-- Execute restoration to full reverse order, including header preparation and cleanup. -/
theorem crtUnexposeStep_runs {n : ℕ} (a : Fin (n + 1) → ℕ) {body : F → Pr F T Q (prime + K) U}
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    {str stmp uU gU vU aJ aK e3B tu t₁ t₂ : Fin T}
    (hreg : [str, stmp, uU, gU, vU, aJ, aK, e3B, tu, t₁, t₂].Nodup)
    (hbank : ∀ r ∈ [str, stmp, uU, gU, vU, aJ, aK, e3B, tu, t₁, t₂], ∀ j, ι j ≠ r)
    (i : Fin (n + 1)) (hi : i ≠ 0) (pre gap : List (Fin (n + 1)))
    (hsplit : crtOuterAxes n = pre ++ i :: gap) (hj : a 0 ≤ a i + 1)
    (hk : a i ≤ a 0 + 1)
    (C : (Fin (n + 1) → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ s ∈ C y, s.val < 8) (x : Fin (n + 1) → ℕ)
    (R : Regs T (prime + K)) (hstr : R str = (crtBox a (crtExposePrefix i ++ [i]) C x).flatten)
    (hu : (R uU).length = crtW a pre) (hg : (R gU).length = crtW a gap) (hv : (R vU).length = 0)
    (haJ : (R aJ).length = a 0) (haK : (R aK).length = a i)
    (he3 : R e3B = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (hstmp : R stmp = []) (htu : R tu = []) (ht₁ : R t₁ = []) (ht₂ : R t₂ = [])
    (hι0 : ∀ i, R (ι i) = []) :
    crtRuns body (crtGapSwapStep hQ ι hι hT str stmp uU gU vU aJ aK e3B tu t₁ t₂) R
      (Function.update R str (crtBox a (crtRevAx (d := n + 1) (n + 1)) C x).flatten)
      ((T + 12 * swapT 6 + 5) * crtSwapCostN (3 * (2 ^ crtW a (pre ++ 0 :: (gap ++ i :: [])) * B))
          (a 0) (a i) +
        (6 * swapT 6 + 10) * (crtW a pre + crtW a gap + 3 * B + a 0 + a i + 2) +
        34 * (2 ^ crtW a (pre ++ 0 :: (gap ++ i :: [])) * B) + 2 * T + 6 * swapT 6 +
        4 * crtW a pre + 4 * crtW a gap + 18 * B +
        a 0 * (4 * a 0 + 11) + a i * (4 * a i + 11) + 88) := by
  obtain ⟨hlay, he, hig, hzg⟩ := crtExpose_gap_layout i pre gap hsplit
  have h := crtGapSwapStep_runs (body := body) a hQ ι hι hT hreg hbank pre gap [] 0 i hi.symm hzg hig
    hj hk C B hB hC h8 x R (by rwa [← he])
    hu hg hv haJ haK he3 hstmp htu ht₁ ht₂ hι0
  rw [← hlay] at h
  simpa only [crtW_nil, Nat.add_zero, Nat.mul_zero] using h

end
end IntegerMultBounds.MathlibTM2.Fast
