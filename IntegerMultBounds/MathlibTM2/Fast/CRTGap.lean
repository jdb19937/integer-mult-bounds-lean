module

public import IntegerMultBounds.MathlibTM2.Fast.CRTSwap
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# Distant exchanges of CRT axes

The middle layout is preserved by a single arbitrary-gap interchange. These
lemmas describe the actual box and bit streams, including unequal axis widths.
They do not yet replace the adjacent walks in `CRTDrive`: its rotation scanner
requires the control prefix in reverse axis order.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack

/-- Interchange two levels across an arbitrary middle level of uniform blocks. -/
theorem crtSwapGapList {α : Type*} (dflt : α) (P H G D E : ℕ)
    (f : ℕ → ℕ → ℕ → ℕ → List α) (hf : ∀ p y g z, (f p y g z).length = E) :
    swapList P H G D E dflt
        ((List.range P).flatMap fun p => (List.range H).flatMap fun y =>
          (List.range G).flatMap fun g => (List.range D).flatMap fun z => f p y g z) =
      (List.range P).flatMap fun p => (List.range D).flatMap fun z =>
        (List.range G).flatMap fun g => (List.range H).flatMap fun y => f p y g z := by
  have hz : ∀ p y g, ((List.range D).flatMap fun z => f p y g z).length = D * E :=
    fun p y g => crt_length_flatMap_range D E _ (hf p y g)
  have hg : ∀ p y, ((List.range G).flatMap fun g =>
      (List.range D).flatMap fun z => f p y g z).length = G * (D * E) :=
    fun p y => crt_length_flatMap_range G _ _ (hz p y)
  have hy : ∀ p, ((List.range H).flatMap fun y => (List.range G).flatMap fun g =>
      (List.range D).flatMap fun z => f p y g z).length = H * (G * (D * E)) :=
    fun p => crt_length_flatMap_range H _ _ (hg p)
  have hy' : ∀ p z g, ((List.range H).flatMap fun y => f p y g z).length = H * E :=
    fun p z g => crt_length_flatMap_range H E _ (fun y => hf p y g z)
  have hg' : ∀ p z, ((List.range G).flatMap fun g =>
      (List.range H).flatMap fun y => f p y g z).length = G * (H * E) :=
    fun p z => crt_length_flatMap_range G _ _ (hy' p z)
  have hz' : ∀ p, ((List.range D).flatMap fun z => (List.range G).flatMap fun g =>
      (List.range H).flatMap fun y => f p y g z).length = D * (G * (H * E)) :=
    fun p => crt_length_flatMap_range D _ _ (hg' p)
  set l := (List.range P).flatMap fun p => (List.range H).flatMap fun y =>
    (List.range G).flatMap fun g => (List.range D).flatMap fun z => f p y g z with hl
  have hlen : l.length = P * H * G * D * E := by
    rw [hl, crt_length_flatMap_range P _ _ hy]; ring
  apply List.ext_getElem?
  intro i
  by_cases hi : i < P * D * G * H * E
  · have hE : 0 < E := by
      by_contra h
      have hzero : E = 0 := by omega
      simp [hzero] at hi
    have hH : 0 < H := by
      by_contra h
      have hzero : H = 0 := by omega
      simp [hzero] at hi
    have hG : 0 < G := by
      by_contra h
      have hzero : G = 0 := by omega
      simp [hzero] at hi
    have hD : 0 < D := by
      by_contra h
      have hzero : D = 0 := by omega
      simp [hzero] at hi
    set e := i % E
    set y := i / E % H
    set g := i / E / H % G
    set z := i / E / H / G % D
    set p := i / E / H / G / D
    have he : e < E := Nat.mod_lt _ hE
    have hy₁ : y < H := Nat.mod_lt _ hH
    have hg₁ : g < G := Nat.mod_lt _ hG
    have hz₁ : z < D := Nat.mod_lt _ hD
    have hp : p < P := by
      simp only [p]
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
      exact Nat.div_lt_of_lt_mul (by nlinarith)
    have hi' : i = (((p * D + z) * G + g) * H + y) * E + e := by
      simp only [p, z, g, y, e]
      rw [Nat.div_add_mod' (i / E / H / G) D, Nat.div_add_mod' (i / E / H) G,
        Nat.div_add_mod' (i / E) H, Nat.div_add_mod' i E]
    rw [hi', swapList_getElem? dflt l hlen hp hy₁ hg₁ hz₁ he]
    rw [show (((p * H + y) * G + g) * D + z) * E + e =
        p * (H * (G * (D * E))) + (y * (G * (D * E)) + (g * (D * E) + (z * E + e))) by ring,
      crt_getElem?_flatMap_range P _ _ hy hp (mix_lt hy₁ (mix_lt hg₁ (mix_lt hz₁ he))),
      crt_getElem?_flatMap_range H _ _ (hg p) hy₁ (mix_lt hg₁ (mix_lt hz₁ he)),
      crt_getElem?_flatMap_range G _ _ (hz p y) hg₁ (mix_lt hz₁ he),
      crt_getElem?_flatMap_range D E _ (hf p y g) hz₁ he]
    rw [show (((p * D + z) * G + g) * H + y) * E + e =
        p * (D * (G * (H * E))) + (z * (G * (H * E)) + (g * (H * E) + (y * E + e))) by ring,
      crt_getElem?_flatMap_range P _ _ hz' hp (mix_lt hz₁ (mix_lt hg₁ (mix_lt hy₁ he))),
      crt_getElem?_flatMap_range D _ _ (hg' p) hz₁ (mix_lt hg₁ (mix_lt hy₁ he)),
      crt_getElem?_flatMap_range G _ _ (hy' p z) hg₁ (mix_lt hy₁ he),
      crt_getElem?_flatMap_range H E _ (fun y => hf p y g z) hy₁ he]
  · rw [List.getElem?_eq_none, List.getElem?_eq_none]
    · rw [crt_length_flatMap_range P _ _ hz']; nlinarith
    · simp only [swapList, List.length_map, List.length_range]; omega

/-- One distant exchange preserves the intervening axes and all record contents. -/
theorem crtSwapGapBox {α : Type*} {d : ℕ} (a : Fin d → ℕ) (dflt : α)
    (pre gap post : List (Fin d)) (j k : Fin d) (hjk : j ≠ k)
    (hj : j ∉ gap) (hk : k ∉ gap)
    (C : (Fin d → ℕ) → List α) (B : ℕ) (hC : ∀ y, (C y).length = B) (x : Fin d → ℕ) :
    swapList (2 ^ crtW a pre) (2 ^ a j) (2 ^ crtW a gap) (2 ^ a k)
        (2 ^ crtW a post * B) dflt
        (crtBox a (pre ++ j :: (gap ++ k :: post)) C x).flatten =
      (crtBox a (pre ++ k :: (gap ++ j :: post)) C x).flatten := by
  have expand : ∀ j k : Fin d,
      (crtBox a (pre ++ j :: (gap ++ k :: post)) C x).flatten =
        (List.range (2 ^ crtW a pre)).flatMap fun p => (List.range (2 ^ a j)).flatMap fun y =>
          (List.range (2 ^ crtW a gap)).flatMap fun g => (List.range (2 ^ a k)).flatMap fun z =>
            (crtBox a post C (Function.update
              (crtDec a gap g (Function.update (crtDec a pre p x) j y)) k z)).flatten := by
    intro j k
    rw [crtBox_append, crt_flatten_flatMap]
    refine List.flatMap_congr fun p _ => ?_
    rw [crtBox_cons, crt_flatten_flatMap]
    refine List.flatMap_congr fun y _ => ?_
    rw [crtBox_append, crt_flatten_flatMap]
    refine List.flatMap_congr fun g _ => ?_
    rw [crtBox_cons, crt_flatten_flatMap]
  rw [expand j k, expand k j]
  simp_rw [crtDec_update_of_not_mem a gap _ _ j _ hj,
    crtDec_update_of_not_mem a gap _ _ k _ hk]
  conv_rhs =>
    congr; ext p; congr; ext z; congr; ext g; congr; ext y
    rw [Function.update_comm hjk.symm]
  exact crtSwapGapList dflt _ _ _ _ _ _ fun p y g z =>
    crtBox_flatten_length a post C _ B hC

/-- Bit expansion commutes with the same distant CRT exchange. -/
theorem crtSwapGapBoxBits {A d : ℕ} (a : Fin d → ℕ)
    (pre gap post : List (Fin d)) (j k : Fin d) (hjk : j ≠ k)
    (hj : j ∉ gap) (hk : k ∉ gap)
    (C : (Fin d → ℕ) → List (Fin (A + 4))) (B : ℕ) (hC : ∀ y, (C y).length = B)
    (x : Fin d → ℕ) :
    swapList (2 ^ crtW a pre) (2 ^ a j) (2 ^ crtW a gap) (2 ^ a k)
        (3 * (2 ^ crtW a post * B)) blank
        (toBits (crtBox a (pre ++ j :: (gap ++ k :: post)) C x).flatten) =
      toBits (crtBox a (pre ++ k :: (gap ++ j :: post)) C x).flatten := by
  have hmap : ∀ o : List (Fin d), (crtBox a o C x).map toBits = crtBox a o (toBits ∘ C) x := by
    intro o; simp [crtBox, List.map_map]
  rw [crt_toBits_flatten, crt_toBits_flatten, hmap, hmap,
    show 3 * (2 ^ crtW a post * B) = 2 ^ crtW a post * (3 * B) by ring]
  exact crtSwapGapBox a blank pre gap post j k hjk hj hk (toBits ∘ C) (3 * B)
    (fun y => by simp [length_toBits, hC]) x

/-- Upgrade the adjacent interchange's middle-count header from one to `2^g`.
The unary gap-width register is preserved, and the temporary register is restored. -/
def crtGapHeaderP {T Q A : ℕ} {U F : Type} (gap hdr tmp : Fin T) : Pr F T Q A U :=
  .seq (crtPop hdr) (.seq (zeroBits gap hdr tmp) (crtPush hdr separator))

theorem crtGapHeaderP_runs {T Q A : ℕ} {U F : Type} {body : F → Pr F T Q A U}
    {gap hdr tmp : Fin T} (hgh : gap ≠ hdr) (hgt : gap ≠ tmp) (hht : hdr ≠ tmp)
    (R : Regs T A) (hh : R hdr = [separator, bitSymbol true]) (ht : R tmp = []) :
    crtRuns body (crtGapHeaderP gap hdr tmp) R
      (Function.update R hdr
        (separator :: (List.replicate (R gap).length false ++ [true]).map bitSymbol))
      (4 * (R gap).length + 8) := by
  have s₁ := crtPop_runs (body := body) hdr R
  let R₁ := Function.update R hdr (R hdr).tail
  have hR₁gap : R₁ gap = R gap := Function.update_of_ne hgh _ _
  have s₂ := crtZeroBits_runs (body := body) hgh hgt hht R₁
    (by simp [R₁, hht.symm, ht])
  let R₂ := Function.update R₁ hdr (binSyms (R₁ gap).length 0 ++ R₁ hdr)
  have s₃ := crtPush_runs (body := body) hdr separator R₂
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ s₃)) ?_) ?_
  · funext i
    by_cases hi : i = hdr
    · subst i
      simp [R₂, R₁, hh, hgh, binSyms_zero_right]
    · simp [R₂, R₁, hi]
  · rw [hR₁gap]; omega

/-- Canonical headers for a distant exchange, extending the adjacent headers. -/
def crtGapHdrBits (u g v h w : ℕ) (e : List Bool) : Fin 5 → List Bool :=
  Function.update (crtHdrBits u v h w e) 1 (List.replicate g false ++ [true])

lemma crtGapHdrBits_canonical (u g v h w : ℕ) (e : List Bool)
    (he : e.getLast? = some true) :
    ∀ i, GrowingCounterData.Canonical (crtGapHdrBits u g v h w e i) := by
  intro i
  by_cases hi : i = 1
  · subst i
    right
    simp [crtGapHdrBits]
  · rw [crtGapHdrBits, Function.update_of_ne hi]
    exact crtHdrBits_canonical u v h w e he i

lemma crtGapHdrBits_value (u g v h w : ℕ) (e : List Bool) :
    ∀ i, Counter.value (crtGapHdrBits u g v h w e i) =
      BinaryInterchangeRun.values (2 ^ u) (2 ^ g) (2 ^ v * Counter.value e) h w i := by
  intro i
  fin_cases i <;>
    simp [crtGapHdrBits, crtHdrBits, BinaryInterchangeRun.values,
      crt_value_replicate_false, Counter.value, GrowingCounterData.empty_value]

noncomputable section

open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2

/-- A single executable distant exchange with prepared canonical headers. The
interchange bank and arbitrary spectator registers are restored. Header generation
and cleanup are separate costs, not included in this pass contract. -/
theorem crtSwapGapPass_runs {T Q K d : ℕ} {U F : Type}
    {body : F → Pr F T Q (prime + K) U} (a : Fin d → ℕ)
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (str tmp : Fin T) (hst : str ≠ tmp)
    (hstrBank : ∀ i, ι i ≠ str) (htmpBank : ∀ i, ι i ≠ tmp)
    (pre gap post : List (Fin d)) (j k : Fin d) (hjk : j ≠ k)
    (hj : j ∉ gap) (hk : k ∉ gap) (hw : a j ≤ a k + 1 ∧ a k ≤ a j + 1)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ s ∈ C y, s.val < 8)
    (x : Fin d → ℕ) (hs : Fin 5 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryInterchangeRun.values
      (2 ^ crtW a pre) (2 ^ crtW a gap) (3 * (2 ^ crtW a post * B)) (a j) (a k) i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (R : Regs T (prime + K))
    (hstr : R str = (crtBox a (pre ++ j :: (gap ++ k :: post)) C x).flatten)
    (htmp : R tmp = []) (hpay : R (ι (reg crtPay)) = [])
    (hpriv : ∀ i : Fin (swapT 6), 6 ≤ i.val → R (ι i) = [])
    (hhdr : ∀ i, R (ι (reg (crtHd i))) = separator :: (hs i).map bitSymbol) :
    crtRuns body (swapPass crtHd crtPay crtHd_inj hQ ι hι hT str tmp) R
      (Function.update R str (crtBox a (pre ++ k :: (gap ++ j :: post)) C x).flatten)
      ((T + 12 * swapT 6 + 5) *
        crtSwapCostN (3 * (2 ^ crtW a (pre ++ j :: (gap ++ k :: post)) * B)) (a j) (a k) +
        6 * ∑ i, (R (ι i)).length +
        34 * (2 ^ crtW a (pre ++ j :: (gap ++ k :: post)) * B) +
        2 * T + 6 * swapT 6 + 23) := by
  intro v S hS hL
  have hP : 0 < 2 ^ crtW a pre := by positivity
  have hG : 0 < 2 ^ crtW a gap := by positivity
  have hE : 0 < 2 ^ crtW a post * B := by positivity
  have hxlen : (crtBox a (pre ++ j :: (gap ++ k :: post)) C x).flatten.length =
      2 ^ crtW a pre * 2 ^ a j * 2 ^ crtW a gap * 2 ^ a k * (2 ^ crtW a post * B) := by
    rw [crtBox_flatten_length a _ C x B hC]
    simp only [crtW_append, crtW_cons, pow_add]; ring
  obtain ⟨v', m, hu, hm, he⟩ := crtSwapPass_exec body crtHd crtPay crtHd_inj hQ ι hι hT
    str tmp hst hstrBank htmpBank
    (2 ^ crtW a pre) (2 ^ crtW a gap) (2 ^ crtW a post * B) (a j) (a k)
    hP hG hE hw.1 hw.2 _ _ hxlen
    (by
      intro s hs'
      obtain ⟨y, hy, hsy⟩ := List.mem_flatten.1 hs'
      simp only [crtBox, List.mem_map] at hy
      obtain ⟨_, _, rfl⟩ := hy
      exact h8 _ s hsy)
    (crtSwapGapBoxBits a pre gap post j k hjk hj hk C B hC x) hs hv hc v S hL
    (by rw [hS, hstr]) (by rw [hS, htmp]) (by rw [hS, hpay])
    (fun i hi => by rw [hS, hpriv i hi]) (fun i => by rw [hS, hhdr])
    (fun i hip hi => absurd (crt_eq_hd_of_ne_pay i hip) (fun ⟨k, hk⟩ => hi k hk))
  refine ⟨v', m, hu, hm.trans ?_, by rw [hS] at he; exact he⟩
  have hcost := crt_cost_le (2 ^ crtW a pre) (2 ^ crtW a gap)
    (3 * (2 ^ crtW a post * B)) (a j) (a k) hs hP hG (by positivity) hw.1 hw.2 hv hc
  have hvol : BinaryAdjacentWidthInterchange.volume (2 ^ crtW a pre) (2 ^ a j)
      (2 ^ crtW a gap) (2 ^ a k) (3 * (2 ^ crtW a post * B)) =
      3 * (2 ^ crtW a (pre ++ j :: (gap ++ k :: post)) * B) := by
    simp only [BinaryAdjacentWidthInterchange.volume, crtW_append, crtW_cons, pow_add]; ring
  rw [hvol] at hcost
  rw [hS, crtBox_flatten_length a _ C x B hC]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ hcost) _) _) _) _) _

end

end IntegerMultBounds.MathlibTM2.Fast
