module

public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectMachineCore
import IntegerMultBounds.MathlibTM2.Fast.CRTMachine
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! # The concrete direct CRT driver -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {T Q K : ℕ} {U F : Type} {body : F → Pr F T Q (prime + K) U}

def crtDirectMachineScanCost (L c : ℕ) := 2 ^ L * (10 * c + 10 * L + 29) + 25 * L + 6 * c + 29

def crtDirectMachineReverseCost {d : ℕ} (T c : ℕ) (a : Fin (d + 1) → ℕ) (ascending : Bool) :=
  crtReverseLoopCost T a c (crtDirectMachineOrder ascending) [] [] +
    14 * (crtEnts (A := prime + K) ((crtDirectMachineOrder ascending).map a)).length +
    6 * crtPre a (d + 1) + 4 * (d + 1) + 28

def crtDirectMachineForwardCoreCost {d : ℕ} (T B w c : ℕ) (a s m : Fin (d + 1) → ℕ) :=
  (4 * (d + 1) + 4 * crtPre a (d + 1) + 8) + crtDirectMachineLoopCost (K := K) T B w c a s m +
    (2 * ((crtEnts (A := prime + K) ((List.finRange (d + 1)).map a)).length +
      (crtEnts (A := prime + K) ((List.finRange (d + 1)).map s)).length +
      (crtEnts (A := prime + K) ((List.finRange (d + 1)).map m)).length + crtW a (List.finRange (d + 1))) + 10)

def crtDirectMachineInverseCoreCost {d : ℕ} (T B w c : ℕ) (a s m : Fin (d + 1) → ℕ) :=
  (4 * crtPre a (d + 1) + 2 * ((crtEnts (A := prime + K) ((crtRevAx (d + 1)).map a)).length +
      (crtEnts (A := prime + K) ((crtRevAx (d + 1)).map s)).length +
      (crtEnts (A := prime + K) ((crtRevAx (d + 1)).map m)).length) + 10) +
    crtDirectMachineLoopCost (K := K) T B w c a s m + (2 * crtPre a (d + 1) + 2 * (d + 1) + 4)

def crtDirectMachineFullForwardCost {d : ℕ} (T B w c : ℕ) (a s m : Fin (d + 1) → ℕ) :=
  crtDirectMachineScanCost (crtPre a (d + 1)) c +
    crtDirectMachineForwardCoreCost (K := K) T B w c a s m + crtDirectMachineReverseCost (K := K) T c a false

def crtDirectMachineFullInverseCost {d : ℕ} (T B w c : ℕ) (a s m : Fin (d + 1) → ℕ) :=
  crtDirectMachineReverseCost (K := K) T c a true +
    crtDirectMachineInverseCoreCost (K := K) T B w c a s m + crtDirectMachineScanCost (crtPre a (d + 1)) c

lemma CrtDirectMachineReady.update_data {d : ℕ}
    {rg : TblR 10 → Fin T} {e : Fin 38 → Fin T} (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j) {a s : Fin (d + 1) → ℕ} {c : ℕ}
    {wl nl : List (Fin (prime + K + 4))} {R : Regs T (prime + K)}
    (hR : CrtDirectMachineReady rg e a s c wl nl R) (data : List (Fin (prime + K + 4))) :
    CrtDirectMachineReady rg e a s c wl nl (Function.update R (e 0) data) := by
  constructor
  · simpa [he.eq_iff] using hR.widths
  · simpa [he.eq_iff] using hR.moduli
  · simpa [he.eq_iff] using hR.zeroWidth
  · simpa [he.eq_iff] using hR.totalWidth
  · simpa [he.eq_iff] using hR.slotWidth
  · simpa [he.eq_iff] using hR.tripleWidth
  · intro j hj hj'; rw [Function.update_of_ne (he.ne (by intro h; subst j; simp at hj))]; exact hR.empty j hj hj'
  · simpa [hrge] using hR.width
  · simpa [hrge] using hR.count
  · intro j; simpa [hrge] using hR.vars j
  · intro j; simpa [hrge] using hR.scratch j
  · simpa [hrge] using hR.acc

lemma crtDirectMachinePad_content {d : ℕ} {α : Type*} (s : Fin d → ℕ)
    (l : List α) (z : α) (P : α → Prop) (hl : ∀ x ∈ l, P x) (hz : P z) :
    ∀ x, P (crtPadC s l z x) := by
  intro x
  unfold crtPadC
  split_ifs
  · rw [List.getD_eq_getElem?_getD]
    rcases h : l[∑ j, x j * Mult.prefixProd s j]? with _ | y
    · exact hz
    · exact hl y (List.mem_of_getElem? h)
  · exact hz

def crtDirectMachineFullForward
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T) : Pr F T Q (prime + K) U :=
  .seq (crtPadP (crtDirectMachineScan e) (e 0) (e 22) (e 11) (e 23) (e 24) (e 25) (e 26)) (.seq (crtDirectMachineForwardCore hQ ι hι hT rg (e ∘ crtDirectMachineCore) (e 39) (e 8)) (crtReverseFull hQ ι hι hT (e ∘ crtDirectMachineReverse false) (e 39) (e 8) (e 26)))

def crtDirectMachineFullInverse
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (e : Fin 40 → Fin T) : Pr F T Q (prime + K) U :=
  .seq (crtReverseFull hQ ι hι hT (e ∘ crtDirectMachineReverse true) (e 39) (e 8) (e 26)) (.seq (crtDirectMachineInverseCore hQ ι hι hT rg (e ∘ crtDirectMachineCore) (e 39) (e 8)) (crtDelP (crtDirectMachineScan e) (e 0) (e 22) (e 11) (e 23) (e 24)))

theorem crtDirectMachineFullForward_runs
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (hrg : Function.Injective rg)
    (e : Fin 40 → Fin T) (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j) (hιe : ∀ j k, ι j ≠ e k)
    {d B w : ℕ} (a s m : Fin (d + 1) → ℕ)
    (hadj : ∀ j k, a j ≤ a k + 1) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hm : ∀ j, m j ≤ s j) (hB : (∑ j, a j) ≤ B) (hd : d + 1 ≤ B)
    (c : ℕ) (hc : 0 < c) (wl nl : List (Fin (prime + K + 4)))
    (hwl : wl.length = 3 * B + 1) (hnl : nl.length = w) (hw : w ≤ 3 * B + 1)
    (R : Regs T (prime + K)) (hR : CrtDirectMachineReady rg (e ∘ crtDirectMachineCore) a s c wl nl R)
    (hι0 : ∀ j, R (ι j) = [])
    (hwt : R (e 31) = crtEnts ((crtRevAx (d + 1)).map a))
    (hst : R (e 32) = crtEnts ((crtRevAx (d + 1)).map s))
    (hmt : R (e 33) = crtEnts ((crtRevAx (d + 1)).map m))
    (hz : ∀ j ∈ ([3, 4, 6, 7, 9, 10, 34, 35, 36, 37] : List (Fin 40)), R (e j) = [])
    (haxes : (R (e 39)).length = d + 1)
    (hsig : R (e 38) = binSyms (crtPre a (d + 1)) (crtSig a s (d + 1)))
    (hmask : R (e 8) = binSyms (crtPre a (d + 1)) (crtMask a (d + 1)))
    (l : List (List (Fin (prime + K + 4)))) (z : List (Fin (prime + K + 4)))
    (hl : l.length = crtProd s (d + 1)) (hlc : ∀ x ∈ l, x.length = c) (hzc : z.length = c)
    (hl8 : ∀ x ∈ l, ∀ b ∈ x, b.val < 8) (hz8 : ∀ b ∈ z, b.val < 8)
    (hstr : R (e 0) = l.flatten) (hzr : R (e 11) = z) :
    crtRuns body (crtDirectMachineFullForward hQ ι hι hT rg e) R
      (Function.update R (e 0) (crtBox a (List.finRange (d + 1)) (crtFwdC s m (crtPadC s l z) (d + 1)) 0).flatten)
      (crtDirectMachineFullForwardCost (K := K) T B w c a s m) := by
  let ec := e ∘ crtDirectMachineCore
  have hec : Function.Injective ec := he.comp crtDirectMachineCore_injective
  have hrgec : ∀ r j, rg r ≠ ec j := fun r j => hrge r _
  have hιec : ∀ j k, ι j ≠ ec k := fun j k => hιe j _
  have hempty : ∀ j : Fin 40, 13 ≤ j.val → j.val ≤ 30 → R (e j) = [] := by
    intro j hj hj'
    exact hR.empty ⟨j.val, by omega⟩ hj hj'
  have hC := crtDirectMachinePad_content s l z (fun x => x.length = c) hlc hzc
  have h8 := crtDirectMachinePad_content s l z (fun x => ∀ b ∈ x, b.val < 8) hl8 hz8
  have hfirst := crtDirectMachinePad_runs (body := body) e he a s hs l z c hl hlc hzc R hstr hzr hsig hmask hempty
  let R₁ := Function.update R (e 0) (crtBox a (crtRevAx (d + 1)) (crtPadC s l z) 0).flatten
  have hR₁ : CrtDirectMachineReady rg ec a s c wl nl R₁ := hR.update_data hec hrgec _
  have hz₁ : ∀ q ∈ [CrtDirectReg.wD, .sD, .mD, .lower, .upper, .index, .tmp, .aI, .sI, .muI],
      R₁ ((ec ∘ crtDirectMachineDriver) q) = [] := by
    intro q hq
    cases q <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq]
    all_goals simp [R₁, ec, Function.comp_def, crtDirectMachineCore, crtDirectMachineDriver, he.eq_iff, hz]
  have hcore := crtDirectMachineForwardCore_runs (body := body) hQ ι hι hT rg hrg ec hec hrgec hιec a s m hadj
    (fun j => ⟨(hs j).1, (hs j).2.le⟩) hm hB hd c hc wl nl hwl hnl hw R₁ hR₁
    (by intro j; simp [R₁, hιe, hι0]) (crtPadC s l z) hC h8 (e 39) (e 8)
    (by intro q; apply he.ne; cases q <;> decide)
    (by intro q; apply he.ne; cases q <;> decide)
    (by simpa [R₁, he.eq_iff] using haxes)
    (by simpa [R₁, ec, crtDirectMachineCore, he.eq_iff] using hR.totalWidth)
    (by simpa [R₁, ec, Function.comp_def, crtDirectMachineCore, crtDirectMachineDriver, he.eq_iff] using hwt)
    (by simpa [R₁, ec, Function.comp_def, crtDirectMachineCore, crtDirectMachineDriver, he.eq_iff] using hst)
    (by simpa [R₁, ec, Function.comp_def, crtDirectMachineCore, crtDirectMachineDriver, he.eq_iff] using hmt)
    hz₁ (by simp [R₁, ec, Function.comp_def, crtDirectMachineCore, crtDirectMachineDriver])
  let D := crtFwdC s m (crtPadC s l z) (d + 1)
  let R₂ := Function.update R (e 0) (crtBox a (crtRevAx (d + 1)) D 0).flatten
  have hcore' : crtRuns body (crtDirectMachineForwardCore hQ ι hι hT rg ec (e 39) (e 8)) R₁ R₂
      (crtDirectMachineForwardCoreCost (K := K) T B w c a s m) := by
    simpa [crtDirectMachineForwardCoreCost, R₁, R₂, D, ec, Function.comp_def, crtDirectMachineCore, crtDirectMachineDriver,
      Function.update_idem] using hcore
  have hD := crtFwdC_mem s m (fun x => x.length = c) (crtPadC s l z) hC (d + 1)
  have hD8 := crtFwdC_mem s m (fun x => ∀ b ∈ x, b.val < 8) (crtPadC s l z) h8 (d + 1)
  have hlast := crtDirectMachineReverse_runs (body := body) hQ ι hι hT e he hιe a hadj c hc D hD hD8 false R₂
    (by simp [R₂, crtDirectMachineOrder])
    (by simpa [R₂, he.eq_iff] using hwt)
    (by simpa [R₂, ec, crtDirectMachineCore, he.eq_iff] using hR.widths)
    (by simpa [R₂, he.eq_iff] using haxes)
    (by simpa [R₂, ec, crtDirectMachineCore, he.eq_iff] using hR.totalWidth)
    (by simpa [R₂, ec, crtDirectMachineCore, he.eq_iff] using hR.tripleWidth)
    (by intro j hj hj'; dsimp only [R₂]; rw [Function.update_of_ne (he.ne (by intro h; subst j; simp at hj))]; exact hempty j hj hj')
    (by intro j; simp [R₂, hιe, hι0])
  have h := crtRuns_seq hfirst (crtRuns_seq hcore' hlast)
  simpa [crtDirectMachineFullForward, crtDirectMachineFullForwardCost, crtDirectMachineScanCost,
    crtDirectMachineReverseCost, R₂, Function.update_idem, crtDirectMachineOrder, ite_false, ite_true,
    crtRevAx_full, List.reverse_reverse, D, Nat.add_assoc] using h

theorem crtDirectMachineFullInverse_runs
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (hrg : Function.Injective rg)
    (e : Fin 40 → Fin T) (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j) (hιe : ∀ j k, ι j ≠ e k)
    {d B w : ℕ} (a s m : Fin (d + 1) → ℕ)
    (hadj : ∀ j k, a j ≤ a k + 1) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hm : ∀ j, m j ≤ s j) (hB : (∑ j, a j) ≤ B) (hd : d + 1 ≤ B)
    (c : ℕ) (hc : 0 < c) (wl nl : List (Fin (prime + K + 4)))
    (hwl : wl.length = 3 * B + 1) (hnl : nl.length = w) (hw : w ≤ 3 * B + 1)
    (R : Regs T (prime + K)) (hR : CrtDirectMachineReady rg (e ∘ crtDirectMachineCore) a s c wl nl R)
    (hι0 : ∀ j, R (ι j) = [])
    (hwt : R (e 31) = crtEnts ((crtRevAx (d + 1)).map a))
    (hst : R (e 32) = crtEnts ((crtRevAx (d + 1)).map s))
    (hmt : R (e 33) = crtEnts ((crtRevAx (d + 1)).map m))
    (hz : ∀ j ∈ ([3, 4, 6, 7, 9, 10, 34, 35, 36, 37] : List (Fin 40)), R (e j) = [])
    (haxes : (R (e 39)).length = d + 1)
    (hsig : R (e 38) = binSyms (crtPre a (d + 1)) (crtSig a s (d + 1)))
    (hmask : R (e 8) = binSyms (crtPre a (d + 1)) (crtMask a (d + 1)))
    (C : (Fin (d + 1) → ℕ) → List (Fin (prime + K + 4)))
    (hC : ∀ x, (C x).length = c) (h8 : ∀ x, ∀ b ∈ C x, b.val < 8)
    (hstr : R (e 0) = (crtBox a (List.finRange (d + 1)) C 0).flatten) :
    crtRuns body (crtDirectMachineFullInverse hQ ι hι hT rg e) R
      (Function.update R (e 0) ((List.range (crtProd s (d + 1))).map fun k => crtInvC s m C (d + 1) (crtUnrank s k)).flatten)
      (crtDirectMachineFullInverseCost (K := K) T B w c a s m) := by
  let ec := e ∘ crtDirectMachineCore
  have hec : Function.Injective ec := he.comp crtDirectMachineCore_injective
  have hrgec : ∀ r j, rg r ≠ ec j := fun r j => hrge r _
  have hιec : ∀ j k, ι j ≠ ec k := fun j k => hιe j _
  have hempty : ∀ j : Fin 40, 13 ≤ j.val → j.val ≤ 30 → R (e j) = [] := by
    intro j hj hj'
    exact hR.empty ⟨j.val, by omega⟩ hj hj'
  have hfirst := crtDirectMachineReverse_runs (body := body) hQ ι hι hT e he hιe a hadj c hc C hC h8 true R
    hstr hwt hR.widths haxes hR.totalWidth hR.tripleWidth hempty hι0
  simp only [crtDirectMachineOrder, ite_true, ← crtRevAx_full] at hfirst
  let R₁ := Function.update R (e 0) (crtBox a (crtRevAx (d + 1)) (C) 0).flatten
  have hR₁ : CrtDirectMachineReady rg ec a s c wl nl R₁ := hR.update_data hec hrgec _
  have hz₁ : ∀ q ∈ [CrtDirectReg.wD, .sD, .mD, .lower, .upper, .index, .tmp, .aI, .sI, .muI],
      R₁ ((ec ∘ crtDirectMachineDriver) q) = [] := by
    intro q hq
    cases q <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq]
    all_goals simp [R₁, ec, Function.comp_def, crtDirectMachineCore, crtDirectMachineDriver, he.eq_iff, hz]
  have hcore := crtDirectMachineInverseCore_runs (body := body) hQ ι hι hT rg hrg ec hec hrgec hιec a s m hadj
    (fun j => ⟨(hs j).1, (hs j).2.le⟩) hm hB hd c hc wl nl hwl hnl hw R₁ hR₁
    (by intro j; simp [R₁, hιe, hι0]) (C) hC h8 (e 39) (e 8)
    (by intro q; apply he.ne; cases q <;> decide)
    (by intro q; apply he.ne; cases q <;> decide)
    (by simpa [R₁, he.eq_iff] using haxes)
    (by simpa [R₁, ec, crtDirectMachineCore, he.eq_iff] using hR.totalWidth)
    (by simpa [R₁, ec, Function.comp_def, crtDirectMachineCore, crtDirectMachineDriver, he.eq_iff] using hwt)
    (by simpa [R₁, ec, Function.comp_def, crtDirectMachineCore, crtDirectMachineDriver, he.eq_iff] using hst)
    (by simpa [R₁, ec, Function.comp_def, crtDirectMachineCore, crtDirectMachineDriver, he.eq_iff] using hmt)
    hz₁ (by simp [R₁, ec, Function.comp_def, crtDirectMachineCore, crtDirectMachineDriver])
  let D := crtInvC s m (C) (d + 1)
  let R₂ := Function.update R (e 0) (crtBox a (crtRevAx (d + 1)) D 0).flatten
  have hcore' : crtRuns body (crtDirectMachineInverseCore hQ ι hι hT rg ec (e 39) (e 8)) R₁ R₂
      (crtDirectMachineInverseCoreCost (K := K) T B w c a s m) := by
    simpa [crtDirectMachineInverseCoreCost, R₁, R₂, D, ec, Function.comp_def, crtDirectMachineCore, crtDirectMachineDriver,
      Function.update_idem] using hcore
  have hD := crtInvC_mem s m (fun x => x.length = c) (C) hC (d + 1)
  have hlast := crtDirectMachineDel_runs (body := body) e he a s hs D c hD R₂
    (by simp [R₂]) (by simpa [R₂, ec, crtDirectMachineCore, he.eq_iff] using hR.slotWidth)
    (by simpa [R₂, he.eq_iff] using hsig) (by simpa [R₂, he.eq_iff] using hmask)
    (by intro j hj hj'; dsimp only [R₂]; rw [Function.update_of_ne (he.ne (by intro h; subst j; simp at hj))]; exact hempty j hj hj')
  have h := crtRuns_seq hfirst (crtRuns_seq hcore' hlast)
  simpa [crtDirectMachineFullInverse, crtDirectMachineFullInverseCost, crtDirectMachineScanCost,
    crtDirectMachineReverseCost, R₂, Function.update_idem, crtDirectMachineOrder, ite_false, ite_true,
    crtRevAx_full, List.reverse_reverse, D, Nat.add_assoc] using h

end
end IntegerMultBounds.MathlibTM2.Fast
