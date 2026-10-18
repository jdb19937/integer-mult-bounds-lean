module

public import IntegerMultBounds.MathlibTM2.Fast.CompactDistWires
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-! Execute the actual wire builder from compact distribution outputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter


noncomputable section

def compactDsyTailCost (n : ℕ) : ℕ :=
  (2 * CompactSizes.K n + 2) + ((2 * ℓ n + 2) + ((2 * (dsyEs n).length + 2) + ((2 * (dsyEs n).sum + 2) +
    ((2 * dsW n + 2) + ((2 * r n + 2) + ((2 * dsWL n (dsW n) + 2) + ((2 * dsWL n (dsW n) + 2) +
    ((2 * (r n * dsW n) + 2) + (2 * dsWW n + 2)))))))))

/-- The step bound of the wires program. -/
def compactDsyWiresCost (n : ℕ) : ℕ :=
  dsySynCostG (dsyEs n).sum (ℓ n) (CompactSizes.K n) (dsyEs n).length (dsWL n (dsW n)) + compactDsyTailCost n

theorem compactDsyWires_spec : ∀ᶠ n in atTop, ∀ mainP : MnPr bdA,
    ∀ (v : HS mnT mnQ bdA Unit) (S : Stacks mnT bdA),
    (∀ y, S.L y = []) → (∀ j, S.R (mnι j) = []) → CompactBdWiresPre S.R n →
    ∃ (v' : HS mnT mnQ bdA Unit) (S' : Stacks mnT bdA) (m : ℕ), m ≤ compactDsyWiresCost n ∧
      Exec (mnBody mnLb mainP) dsyProg (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ (∀ j, S'.R (mnι j) = []) ∧
      (∀ x, S'.R (mnLay x) = mnσ (blP₀ dsW n) (compactDsyV₀ n) x) ∧
      ∀ r, bdWKeep r → S'.R (mnRg r) = S.R (mnRg r) := by
  filter_upwards [eventually_big] with n hbig
  intro mainP v S _ hι hP
  have hn := hbig.1
  have H := compactDs_layHyp hbig
  have hE := ds_lay_E hn
  have hw1 : 1 ≤ dsW n := by unfold dsW; omega
  obtain ⟨hEW, -, -, -, -⟩ := ds_lay_widths hbig hw1
  have hsum := ds_sum_cvAx hn
  have hlen := ds_length_cvAx n
  have hℓr : ℓ n ≤ 2 ^ ℓ n * dsW n :=
    le_trans Nat.lt_two_pow_self.le (Nat.le_mul_of_pos_right _ hw1)
  have hio : ∀ x, S.R (bdIo x) = compactBdO n x := hP.io
  have hio' : ∀ x, S.R (mnLay (bdLayX x)) = compactBdO n x := hio
  set es := dsyEs n with hes
  -- the machine
  have hrun := dsySyn_runs (body := mnBody mnLb mainP) bl_hA dsyRg_inj
    (fun r x => dsyRg_ne_lay r _) dsy_outs_nodup
    (fun o ho r => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact dsyRg_ne_lay _ _)
    (fun o ho x => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fun h => bdLayX_ne_park x (mnLay_inj h)
      all_goals exact fun h => bdLayX_ne_wire x _ (mnLay_inj h))
    H hE (by rw [hlen]; exact dsE_lt n)
    (by
      rw [hsum]; unfold dsyW dsWL
      rw [pow_two, show r n = 2 ^ ℓ n from rfl]
      omega)
    hEW S.R (fun r => hι _) (by rw [hio', hsum]; rfl) (by rw [hio']; rfl) (by rw [hio']; rfl)
    (by rw [hio', hlen]; rfl) (by rw [hio']; rfl) (by rw [hio']; rfl)
  rw [dsy_park_eq hn, dsy_nRounds hbig] at hrun
  set R₇ := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update S.R
      (mnLay .park) (blP₀ dsW n ++ S.R (mnLay .park)))
      (dsyWr (.p .b)) (List.replicate (layB (ℓ n) (CompactSizes.K n)) tick ++ S.R (dsyWr (.p .b))))
      (dsyWr (.p .Lg)) (List.replicate (layLongs es (ℓ n)).length tick ++ S.R (dsyWr (.p .Lg))))
      (dsyWr (.p .lr)) (List.replicate (ℓ n) tick ++ S.R (dsyWr (.p .lr))))
      (dsyWr (.p .c)) (List.replicate (nRounds (cvAx (t n))) tick ++ S.R (dsyWr (.p .c))))
      (dsyWr (.p .es)) (topRec es ++ S.R (dsyWr (.p .es))))
      (dsyWr (.tw .pz)) (twPosReg bdA es.sum (twPosL (layPerm es (ℓ n) (CompactSizes.K n))) ++
        S.R (dsyWr (.tw .pz))) with hR₇
  set F₀ : Regs mnT bdA := dsOv dsyRg R₇ fun _ => [] with hF₀
  -- lookups
  have hlayW : ∀ y : SynW, S.R (dsyWr y) = [] := fun y =>
    hP.lay _ fun z => bdLayX_ne_wire z _
  have hpark : S.R (mnLay .park) = [] := hP.lay _ fun z => bdLayX_ne_park z
  have hwne : ∀ x : DsX, ∀ y : SynW, bdIo x ≠ dsyWr y := fun x y h =>
    bdLayX_ne_wire x _ (mnLay_inj h)
  have hpne : ∀ x : DsX, bdIo x ≠ mnLay .park := fun x h => bdLayX_ne_park x (mnLay_inj h)
  have l7io : ∀ x : DsX, F₀ (bdIo x) = compactBdO n x := fun x => by
    rw [hF₀, bdIo, dsyOv_lay, ← bdIo, hR₇]
    simp only [Function.update_of_ne (hwne x _), Function.update_of_ne (hpne x)]
    exact hio x
  have l7w : ∀ y : SynW, y ∉ [SynW.p .b, .p .Lg, .p .lr, .p .c, .p .es, .tw .pz] →
      F₀ (dsyWr y) = [] := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [hF₀, dsyWr, dsyOv_lay, ← dsyWr, hR₇]
    simp only [Function.update_apply, dsyWr, mnLay_inj.eq_iff, LReg.wire.injEq, synWire_eq_iff,
      hy, ite_false, reduceCtorEq]
    exact hlayW y
  -- the tail
  have hK : (compactBdO n .lK).length = CompactSizes.K n := by simp [compactBdO]
  have hL : (compactBdO n .lL).length = ℓ n := by simp [compactBdO,bdO, dsSrcO]
  have hD : (compactBdO n .lD).length = es.length := by simp [compactBdO,bdO, dsSrcO, hes, hlen]
  have hN : (compactBdO n .lN).length = es.sum := by simp [compactBdO,bdO, dsSrcO, hes, hsum]
  have hw : (compactBdO n .uw).length = dsW n := by simp [compactBdO,bdO]
  have hr : (compactBdO n .rR).length = r n := by simp [compactBdO,bdO, dsSrcO]
  have hlE : (compactBdO n .lE).length = dsWL n (dsW n) := by simp [compactBdO,bdO, dsSrcO]
  have hlW : (compactBdO n .lW).length = dsWL n (dsW n) := by simp [compactBdO,bdO, dsSrcO]
  have hlB : (compactBdO n .lB).length = r n * dsW n := by simp [compactBdO,bdO, dsSrcO]
  have huW : (compactBdO n .uW).length = dsWW n := by simp [compactBdO,bdO]
  have hKv : compactBdO n .lK = List.replicate (CompactSizes.K n) tick := rfl
  have hLv : compactBdO n .lL = List.replicate (ℓ n) tick := rfl
  have hDv : compactBdO n .lD = List.replicate es.length tick := by rw [hes, hlen]; rfl
  have hNv : compactBdO n .lN = List.replicate es.sum tick := by rw [hes, hsum]; rfl
  have hwv : compactBdO n .uw = List.replicate (dsW n) tick := rfl
  have hrv : compactBdO n .rR = List.replicate (r n) tick := rfl
  have hine : ∀ x x' : DsX, x ≠ x' → bdIo x ≠ bdIo x' := fun x x' h => bdIo_inj.ne h
  have hwinj : ∀ y y' : SynW, y ≠ y' → dsyWr y ≠ dsyWr y' := fun y y' h e =>
    h (synWire_inj (LReg.wire.inj (mnLay_inj e)))
  -- the moves
  have m1 := dsyRuns_moveR (body := mnBody mnLb mainP) (hwne .lK (.p .K)) F₀
  rw [l7io, l7w _ (by decide), hKv, List.reverse_replicate, List.append_nil,
    List.length_replicate] at m1
  set F₁ := Function.update (Function.update F₀ (bdIo .lK) []) (dsyWr (.p .K))
    (List.replicate (CompactSizes.K n) tick) with hF₁
  have f1 : ∀ k, k ≠ bdIo .lK → k ≠ dsyWr (.p .K) → F₁ k = F₀ k := fun k h1 h2 => by
    rw [hF₁, Function.update_of_ne h2, Function.update_of_ne h1]
  have m2 := dsyRuns_moveR (body := mnBody mnLb mainP) (hwne .lL (.p .ℓ)) F₁
  rw [f1 _ (hine _ _ (by decide)) (hwne _ _), f1 _ (hwne _ _).symm (hwinj _ _ (by decide)),
    l7io, l7w _ (by decide), hLv, List.reverse_replicate, List.append_nil,
    List.length_replicate] at m2
  set F₂ := Function.update (Function.update F₁ (bdIo .lL) []) (dsyWr (.p .ℓ))
    (List.replicate (ℓ n) tick) with hF₂
  have f2 : ∀ k, k ≠ bdIo .lK → k ≠ dsyWr (.p .K) → k ≠ bdIo .lL → k ≠ dsyWr (.p .ℓ) →
      F₂ k = F₀ k := fun k h1 h2 h3 h4 => by
    rw [hF₂, Function.update_of_ne h4, Function.update_of_ne h3, f1 k h1 h2]
  have m3 := dsyRuns_moveR (body := mnBody mnLb mainP) (hwne .lD (.p .D)) F₂
  rw [f2 _ (hine _ _ (by decide)) (hwne _ _) (hine _ _ (by decide)) (hwne _ _),
    f2 _ (hwne _ _).symm (hwinj _ _ (by decide)) (hwne _ _).symm (hwinj _ _ (by decide)),
    l7io, l7w _ (by decide), hDv, List.reverse_replicate, List.append_nil,
    List.length_replicate] at m3
  set F₃ := Function.update (Function.update F₂ (bdIo .lD) []) (dsyWr (.p .D))
    (List.replicate es.length tick) with hF₃
  have f3 : ∀ k, k ≠ bdIo .lK → k ≠ dsyWr (.p .K) → k ≠ bdIo .lL → k ≠ dsyWr (.p .ℓ) →
      k ≠ bdIo .lD → k ≠ dsyWr (.p .D) → F₃ k = F₀ k := fun k h1 h2 h3 h4 h5 h6 => by
    rw [hF₃, Function.update_of_ne h6, Function.update_of_ne h5, f2 k h1 h2 h3 h4]
  have m4 := dsyRuns_moveR (body := mnBody mnLb mainP) (hwne .lN (.p .N)) F₃
  rw [f3 _ (hine _ _ (by decide)) (hwne _ _) (hine _ _ (by decide)) (hwne _ _)
      (hine _ _ (by decide)) (hwne _ _),
    f3 _ (hwne _ _).symm (hwinj _ _ (by decide)) (hwne _ _).symm (hwinj _ _ (by decide))
      (hwne _ _).symm (hwinj _ _ (by decide)),
    l7io, l7w _ (by decide), hNv, List.reverse_replicate, List.append_nil,
    List.length_replicate] at m4
  set F₄ := Function.update (Function.update F₃ (bdIo .lN) []) (dsyWr (.p .N))
    (List.replicate es.sum tick) with hF₄
  have f4 : ∀ k, k ≠ bdIo .lK → k ≠ dsyWr (.p .K) → k ≠ bdIo .lL → k ≠ dsyWr (.p .ℓ) →
      k ≠ bdIo .lD → k ≠ dsyWr (.p .D) → k ≠ bdIo .lN → k ≠ dsyWr (.p .N) → F₄ k = F₀ k :=
    fun k h1 h2 h3 h4 h5 h6 h7 h8 => by
      rw [hF₄, Function.update_of_ne h8, Function.update_of_ne h7, f3 k h1 h2 h3 h4 h5 h6]
  have m5 := dsyRuns_moveR (body := mnBody mnLb mainP) (hwne .uw (.p .w)) F₄
  rw [f4 _ (hine _ _ (by decide)) (hwne _ _) (hine _ _ (by decide)) (hwne _ _)
      (hine _ _ (by decide)) (hwne _ _) (hine _ _ (by decide)) (hwne _ _),
    f4 _ (hwne _ _).symm (hwinj _ _ (by decide)) (hwne _ _).symm (hwinj _ _ (by decide))
      (hwne _ _).symm (hwinj _ _ (by decide)) (hwne _ _).symm (hwinj _ _ (by decide)),
    l7io, l7w _ (by decide), hwv, List.reverse_replicate, List.append_nil,
    List.length_replicate] at m5
  set F₅ := Function.update (Function.update F₄ (bdIo .uw) []) (dsyWr (.p .w))
    (List.replicate (dsW n) tick) with hF₅
  have f5 : ∀ k, k ≠ bdIo .lK → k ≠ dsyWr (.p .K) → k ≠ bdIo .lL → k ≠ dsyWr (.p .ℓ) →
      k ≠ bdIo .lD → k ≠ dsyWr (.p .D) → k ≠ bdIo .lN → k ≠ dsyWr (.p .N) →
      k ≠ bdIo .uw → k ≠ dsyWr (.p .w) → F₅ k = F₀ k :=
    fun k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
      rw [hF₅, Function.update_of_ne h10, Function.update_of_ne h9, f4 k h1 h2 h3 h4 h5 h6 h7 h8]
  have m6 := dsyRuns_moveR (body := mnBody mnLb mainP) (hwne .rR (.p .r)) F₅
  rw [f5 _ (hine _ _ (by decide)) (hwne _ _) (hine _ _ (by decide)) (hwne _ _)
      (hine _ _ (by decide)) (hwne _ _) (hine _ _ (by decide)) (hwne _ _)
      (hine _ _ (by decide)) (hwne _ _),
    f5 _ (hwne _ _).symm (hwinj _ _ (by decide)) (hwne _ _).symm (hwinj _ _ (by decide))
      (hwne _ _).symm (hwinj _ _ (by decide)) (hwne _ _).symm (hwinj _ _ (by decide))
      (hwne _ _).symm (hwinj _ _ (by decide)),
    l7io, l7w _ (by decide), hrv, List.reverse_replicate, List.append_nil,
    List.length_replicate] at m6
  set F₆ := Function.update (Function.update F₅ (bdIo .rR) []) (dsyWr (.p .r))
    (List.replicate (r n) tick) with hF₆
  have f6 : ∀ k, k ≠ bdIo .lK → k ≠ dsyWr (.p .K) → k ≠ bdIo .lL → k ≠ dsyWr (.p .ℓ) →
      k ≠ bdIo .lD → k ≠ dsyWr (.p .D) → k ≠ bdIo .lN → k ≠ dsyWr (.p .N) →
      k ≠ bdIo .uw → k ≠ dsyWr (.p .w) → k ≠ bdIo .rR → k ≠ dsyWr (.p .r) → F₆ k = F₀ k :=
    fun k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => by
      rw [hF₆, Function.update_of_ne h12, Function.update_of_ne h11,
        f5 k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]
  have f6io : ∀ x : DsX, x ∉ [DsX.lK, .lL, .lD, .lN, .uw, .rR] → F₆ (bdIo x) = compactBdO n x :=
    fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [f6 _ (hine _ _ hx.1) (hwne _ _) (hine _ _ hx.2.1) (hwne _ _) (hine _ _ hx.2.2.1)
        (hwne _ _) (hine _ _ hx.2.2.2.1) (hwne _ _) (hine _ _ hx.2.2.2.2.1) (hwne _ _)
        (hine _ _ hx.2.2.2.2.2) (hwne _ _), l7io]
  -- the clears
  have c1 := dsyRuns_bclear (body := mnBody mnLb mainP) (bdIo .lE) F₆
  rw [f6io _ (by decide), hlE] at c1
  set F₇ := Function.update F₆ (bdIo .lE) [] with hF₇
  have e7 : F₇ (bdIo .lW) = compactBdO n .lW := by
    rw [hF₇, Function.update_of_ne (hine _ _ (by decide)), f6io _ (by decide)]
  have c2 := dsyRuns_bclear (body := mnBody mnLb mainP) (bdIo .lW) F₇
  rw [e7, hlW] at c2
  set F₈ := Function.update F₇ (bdIo .lW) [] with hF₈
  have e8 : F₈ (bdIo .lB) = compactBdO n .lB := by
    rw [hF₈, Function.update_of_ne (hine _ _ (by decide)), hF₇,
      Function.update_of_ne (hine _ _ (by decide)), f6io _ (by decide)]
  have c3 := dsyRuns_bclear (body := mnBody mnLb mainP) (bdIo .lB) F₈
  rw [e8, hlB] at c3
  set F₉ := Function.update F₈ (bdIo .lB) [] with hF₉
  have e9 : F₉ (bdIo .uW) = compactBdO n .uW := by
    rw [hF₉, Function.update_of_ne (hine _ _ (by decide)), hF₈,
      Function.update_of_ne (hine _ _ (by decide)), hF₇,
      Function.update_of_ne (hine _ _ (by decide)), f6io _ (by decide)]
  have c4 := dsyRuns_bclear (body := mnBody mnLb mainP) (bdIo .uW) F₉
  rw [e9, huW] at c4
  set F₁₀ := Function.update F₉ (bdIo .uW) [] with hF₁₀
  have hall := hrun.seq (m1.seq (m2.seq (m3.seq (m4.seq (m5.seq (m6.seq (c1.seq (c2.seq
    (c3.seq c4)))))))))
  obtain ⟨v', S', m, -, hm, he, hR, hinp, hout, hL'⟩ := hall v S rfl
  -- the final file off the layer registers
  have hoff : ∀ k, (∀ x, k ≠ mnLay x) → F₁₀ k = F₀ k := fun k hk => by
    have h1 : ∀ x, k ≠ bdIo x := fun x => hk _
    have h2 : ∀ y, k ≠ dsyWr y := fun y => hk _
    rw [hF₁₀, Function.update_of_ne (h1 _), hF₉, Function.update_of_ne (h1 _), hF₈,
      Function.update_of_ne (h1 _), hF₇, Function.update_of_ne (h1 _),
      f6 k (h1 _) (h2 _) (h1 _) (h2 _) (h1 _) (h2 _) (h1 _) (h2 _) (h1 _) (h2 _) (h1 _) (h2 _)]
  have hoff7 : ∀ k, (∀ x, k ≠ mnLay x) → R₇ k = S.R k := fun k hk => by
    rw [hR₇]
    simp only [dsyWr] at hk ⊢
    rw [Function.update_of_ne (hk _), Function.update_of_ne (hk _), Function.update_of_ne (hk _),
      Function.update_of_ne (hk _), Function.update_of_ne (hk _), Function.update_of_ne (hk _),
      Function.update_of_ne (hk _)]
  refine ⟨v', S', m, ?_, he, hinp, hout, hL', fun j => ?_, fun x => ?_, fun r _ => ?_⟩
  · -- the cost
    refine hm.trans ?_
    unfold compactDsyWiresCost compactDsyTailCost
    rw [← hes]
  · -- the scratch registers
    rw [hR, hoff _ (fun x => mnι_ne_lay j x), hF₀]
    by_cases h : ∃ r, dsyRg r = mnι j
    · obtain ⟨r, hr⟩ := h
      rw [← hr, dsOv_rg dsyRg_inj]
    · push Not at h
      rw [dsOv_off _ _ h, hoff7 _ (fun x => mnι_ne_lay j x)]
      exact hι j
  · -- the layer registers
    rw [hR]
    have hlayW' : ∀ y : SynW, S.R (mnLay (.wire (synWire y))) = [] := hlayW
    have hev : ∀ x : LReg SXReg, x ≠ .park → (∀ y, x ≠ .wire (synWire y)) →
        (∀ z, x ≠ bdLayX z) → F₁₀ (mnLay x) = S.R (mnLay x) := fun x h1 h2 h3 => by
      have h1' : ∀ y, mnLay x ≠ dsyWr y := fun y e => h2 y (mnLay_inj e)
      have h3' : ∀ z, mnLay x ≠ bdIo z := fun z e => h3 z (mnLay_inj e)
      rw [hF₁₀, Function.update_of_ne (h3' _), hF₉, Function.update_of_ne (h3' _), hF₈,
        Function.update_of_ne (h3' _), hF₇, Function.update_of_ne (h3' _),
        f6 _ (h3' _) (h1' _) (h3' _) (h1' _) (h3' _) (h1' _) (h3' _) (h1' _) (h3' _) (h1' _)
          (h3' _) (h1' _), hF₀, dsyOv_lay, hR₇]
      rw [Function.update_of_ne (h1' _), Function.update_of_ne (h1' _),
        Function.update_of_ne (h1' _), Function.update_of_ne (h1' _),
        Function.update_of_ne (h1' _), Function.update_of_ne (h1' _),
        Function.update_of_ne (fun e => h1 (mnLay_inj e))]
    have hevw : ∀ y, y ∉ [SynW.p .K, .p .ℓ, .p .D, .p .N, .p .w, .p .r, .p .b, .p .Lg, .p .lr,
        .p .c, .p .es, .tw .pz] → F₁₀ (dsyWr y) = [] := fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      rw [hF₁₀, Function.update_of_ne (hwne _ _).symm, hF₉, Function.update_of_ne (hwne _ _).symm,
        hF₈, Function.update_of_ne (hwne _ _).symm, hF₇, Function.update_of_ne (hwne _ _).symm,
        f6 _ (hwne _ _).symm (hwinj _ _ hy.1) (hwne _ _).symm (hwinj _ _ hy.2.1)
          (hwne _ _).symm (hwinj _ _ hy.2.2.1) (hwne _ _).symm (hwinj _ _ hy.2.2.2.1)
          (hwne _ _).symm (hwinj _ _ hy.2.2.2.2.1) (hwne _ _).symm (hwinj _ _ hy.2.2.2.2.2.1),
        l7w _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hy.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.1,
            hy.2.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2.2.2⟩)]
    have hpw : ∀ y, mnLay .park ≠ dsyWr y := fun y e => by
      have := mnLay_inj e; simp at this
    cases x
    case park =>
      rw [mnσ_park, hF₁₀, Function.update_of_ne (hpne _).symm, hF₉,
        Function.update_of_ne (hpne _).symm, hF₈, Function.update_of_ne (hpne _).symm, hF₇,
        Function.update_of_ne (hpne _).symm,
        f6 _ (hpne _).symm (hpw _) (hpne _).symm (hpw _) (hpne _).symm (hpw _) (hpne _).symm
          (hpw _) (hpne _).symm (hpw _) (hpne _).symm (hpw _), hF₀, dsyOv_lay, hR₇]
      rw [Function.update_of_ne (hpw _), Function.update_of_ne (hpw _),
        Function.update_of_ne (hpw _), Function.update_of_ne (hpw _),
        Function.update_of_ne (hpw _), Function.update_of_ne (hpw _), Function.update_self,
        hpark, List.append_nil]
    case wire v =>
      by_cases hv : ∃ y, synWire y = v
      · obtain ⟨y, rfl⟩ := hv
        rw [mnσ_wire]
        show F₁₀ (dsyWr y) = _
        rcases y with w | i | q | i
        · by_cases hw : w = .pz
          · subst hw
            simp only [hF₁₀, hF₉, hF₈, hF₇, hF₆, hF₅, hF₄, hF₃, hF₂, hF₁, hF₀, dsyOv_lay, hR₇,
              Function.update_apply, dsyWr, bdIo, mnLay_inj.eq_iff, LReg.wire.injEq,
              synWire_eq_iff, dsy_wire_ne_bdLayX, reduceCtorEq,
              ite_true, ite_false, hlayW', List.append_nil]
            rfl
          · rw [hevw _ (by simp [hw])]
            cases w <;> first | rfl | exact absurd rfl hw
        · rw [hevw _ (by simp)]; rfl
        · cases q
          all_goals first
            | (rw [hevw _ (by decide)]; rfl)
            | (simp only [hF₁₀, hF₉, hF₈, hF₇, hF₆, hF₅, hF₄, hF₃, hF₂, hF₁, hF₀, dsyOv_lay,
                hR₇, Function.update_apply, dsyWr, bdIo, mnLay_inj.eq_iff, LReg.wire.injEq,
                synWire_eq_iff, SynW.p.injEq, dsy_wire_ne_bdLayX, reduceCtorEq,
                ite_true, ite_false, hlayW', List.append_nil]
               rfl)
        · rw [hevw _ (by simp)]; rfl
      · rw [dsy_mnσ_wire_off _ _ (fun y h => hv ⟨y, h⟩),
          hev _ (by simp) (fun y e => hv ⟨y, (LReg.wire.inj e).symm⟩)
            (fun z => dsy_wire_ne_bdLayX _ _),
          hP.lay _ (fun z => bdLayX_ne_wire z v)]
    case wtmp v =>
      rw [mnσ_eq_nil _ _ (by simp) (by simp)]
      by_cases hz : ∃ z, bdLayX z = .wtmp v
      · obtain ⟨z, hz⟩ := hz
        rw [← hz]
        show F₁₀ (bdIo z) = []
        cases z
        all_goals
          simp only [hF₁₀, hF₉, hF₈, hF₇, hF₆, hF₅, hF₄, hF₃, hF₂, hF₁, Function.update_apply,
            bdIo_inj.eq_iff, hwne, reduceCtorEq, ite_true, ite_false, l7io]
        all_goals rfl
      · rw [hev _ (by simp) (fun y => by simp) (fun z h => hz ⟨z, h.symm⟩),
          hP.lay _ (fun z h => hz ⟨z, h⟩)]
    all_goals
      rw [hev _ (by simp) (fun y => by simp) (fun z => by simp [bdLayX]),
        hP.lay _ (fun z => by simp [bdLayX]), mnσ_eq_nil _ _ (fun y => by simp) (by simp)]
  · -- the kept registers
    rw [hR, hoff _ (fun x => mnRg_ne_lay r x), hF₀,
      dsOv_off (rg := dsyRg) _ _ (fun q => (mnRg_ne_ι r (dsyIdx q)).symm),
      hoff7 _ (fun x => mnRg_ne_lay r x)]


end
end IntegerMultBounds.MathlibTM2.Fast.Main
