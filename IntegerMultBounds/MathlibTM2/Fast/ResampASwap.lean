module

public import IntegerMultBounds.MathlibTM2.Fast.ResampAAxis
public import IntegerMultBounds.MathlibTM2.Fast.ResampABox
public import IntegerMultBounds.MathlibTM2.Node.SwapPass

/-!
# Moving an axis of the box innermost

`rsaSwapP` interchanges two axes of the box stream on register `ln`, a coefficient stream
`cstream A w L` laid out as `[P] × [2^h] × [G] × [2^d]` records: it expands the stream to bits
(`toBitsPass`, three bits per pair symbol, `3 w` bits per record), runs the vendored binary
interchange `placedSwapProg` on the placed bank `rg (.x (sw j))` with the inner block of `3 w`
bits, and packs the result (`ofBitsPass`). Afterwards `ln` holds
`cstream A w (swapList P (2^h) G (2^d) 1 0 L)`, the stream laid out as
`[P] × [2^d] × [G] × [2^h]` (`rsa_swap`). The widths satisfy `h ≤ d + 1`, `d ≤ h + 1`.

**Register interface.** The bank `rg (.x (sw j))`, `j : Fin (swapT t₀)`: the five header
registers `sw (reg (hd k))` hold `separator :: (hs k).map bitSymbol` for canonical counters of
`values P G (3 w) h d`; every other bank register is empty. `rg (.x xt)` is an empty spare off the
bank. The alphabet is `Fin (prime + K + 4)`. Every register other than `ln` ends as it started.

**Cost** (`rsaSwapCost`): `(T + 12 swapT t₀ + 5)` host steps per step of the interchange machine
(`BinaryInterchangeRun.cost`), plus `6` per symbol on the bank and `34` per stream symbol.
`rsa_swap_le` bounds the interchange by `BinaryInterchangeBudget.uniform_bound`: in total
`O(T_box · 3 w · max(1, h, d)^τ)` steps for a box of `T_box` records.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ResampA

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ### Interchanges of lists of records -/

lemma rsa_decomp5 {P D G H B z : ℕ} (hz : z < P * D * G * H * B) :
    ∃ p d g h b, p < P ∧ d < D ∧ g < G ∧ h < H ∧ b < B ∧
      z = (((p * D + d) * G + g) * H + h) * B + b := by
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp at hz
    · exact h
  have hz' : z / B < P * D * G * H := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hz)
  obtain ⟨p, d, g, h, hp, hd, hg, hh, he⟩ := rsa_decomp4 hz'
  exact ⟨p, d, g, h, z % B, hp, hd, hg, hh, Nat.mod_lt _ hB, by
    rw [← he, Nat.div_add_mod']⟩

lemma rsa_length_swapList {α : Type} (P H G D B : ℕ) (dflt : α) (l : List α) :
    (swapList P H G D B dflt l).length = P * D * G * H * B := by
  simp [swapList]

/-- The default element of an interchange of a list of the right length is irrelevant. -/
lemma rsa_swapList_dflt {α : Type} (P H G D B : ℕ) (d₁ d₂ : α) (l : List α)
    (hl : l.length = P * H * G * D * B) : swapList P H G D B d₁ l = swapList P H G D B d₂ l := by
  apply List.ext_getElem?
  intro z
  by_cases hz : z < P * D * G * H * B
  · obtain ⟨p, d, g, h, b, hp, hd, hg, hh, hb, rfl⟩ := rsa_decomp5 hz
    rw [swapList_getElem? d₁ l hl hp hh hg hd hb, swapList_getElem? d₂ l hl hp hh hg hd hb]
  · rw [List.getElem?_eq_none (by rw [rsa_length_swapList]; omega),
      List.getElem?_eq_none (by rw [rsa_length_swapList]; omega)]

lemma rsa_swapList_map {α β : Type} (f : α → β) (P H G D B : ℕ) (a : α) (l : List α) :
    swapList P H G D B (f a) (l.map f) = (swapList P H G D B a l).map f := by
  simp [swapList, List.getD_eq_getElem?_getD, List.getElem?_map]

/-- The interchange of a concatenation of blocks of `B` symbols is the concatenation of the
interchanged blocks. -/
lemma rsa_swapList_flatten {α : Type} (P H G D B : ℕ) (dflt : α) (blocks : List (List α))
    (hl : blocks.length = P * H * G * D) (hB : ∀ b ∈ blocks, b.length = B) :
    swapList P H G D B dflt blocks.flatten = (swapList P H G D 1 [] blocks).flatten := by
  have hlf : blocks.flatten.length = P * H * G * D * B := by
    rw [length_flatten_uniform _ hB, hl]
  have hl1 : blocks.length = P * H * G * D * 1 := by rw [hl, Nat.mul_one]
  have hmem : ∀ x ∈ swapList P H G D 1 [] blocks, x.length = B := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < P * D * G * H * 1 := by rwa [rsa_length_swapList] at hi
    obtain ⟨p, d, g, h, b, hp, hd, hg, hh, hb, rfl⟩ := rsa_decomp5 hi'
    have e := swapList_getElem? [] blocks hl1 hp hh hg hd hb
    rw [List.getElem?_eq_getElem hi] at e
    have hlt : (((p * H + h) * G + g) * D + d) * 1 + b < blocks.length := by
      rw [hl1]; exact mix_lt (mix_lt (mix_lt (mix_lt hp hh) hg) hd) hb
    rw [List.getElem?_eq_getElem hlt] at e
    rw [Option.some_inj.1 e]
    exact hB _ (List.getElem_mem _)
  apply List.ext_getElem?
  intro z
  by_cases hz : z < P * D * G * H * B
  · obtain ⟨p, d, g, h, b, hp, hd, hg, hh, hb, rfl⟩ := rsa_decomp5 hz
    rw [swapList_getElem? dflt _ hlf hp hh hg hd hb, flatten_getElem?_uniform _ hB _ _ hb,
      flatten_getElem?_uniform _ hmem _ _ hb]
    have e := swapList_getElem? [] blocks hl1 hp hh hg hd (Nat.zero_lt_one)
    simp only [Nat.mul_one, Nat.add_zero] at e
    rw [e]
  · rw [List.getElem?_eq_none (by rw [rsa_length_swapList]; omega), List.getElem?_eq_none]
    rw [length_flatten_uniform _ hmem, rsa_length_swapList]
    nlinarith

/-- The interchange of a coefficient stream, in bits. -/
lemma rsa_swapList_cstream_bits {A : ℕ} (P H G D w : ℕ) (L : List GaussianInt)
    (hL : L.length = P * H * G * D) :
    swapList P H G D (3 * w) blank (toBits (cstream A w L)) =
      toBits (cstream A w (swapList P H G D 1 0 L)) := by
  have hcs : ∀ L' : List GaussianInt, cstream A w L' = (L'.map (csyms A w)).flatten := by
    intro L'; simp [cstream, List.flatMap_def]
  rw [hcs, hcs, toBits_flatten, toBits_flatten,
    rsa_swapList_flatten P H G D (3 * w) blank _ (by simp [hL]) (by simp [length_toBits, csyms]),
    List.map_map, List.map_map]
  congr 1
  rw [rsa_swapList_dflt P H G D 1 [] ((toBits ∘ csyms A w) 0) _ (by simp [hL]),
    rsa_swapList_map (toBits ∘ csyms A w)]

lemma rsa_pairSym_lt_eight {A : ℕ} (hA : 4 ≤ A) (a b : Bool) : (pairSym A a b).val < 8 := by
  rw [pairSym_val hA]; cases a <;> cases b <;> simp

lemma rsa_cstream_lt_eight {A w : ℕ} (hA : 4 ≤ A) (L : List GaussianInt) :
    ∀ s ∈ cstream A w L, s.val < 8 := by
  intro s hs
  simp only [cstream, List.mem_flatMap, csyms, coeffSyms, List.mem_ofFn] at hs
  obtain ⟨_, _, t, rfl⟩ := hs
  exact rsa_pairSym_lt_eight hA _ _

noncomputable section

/-! ### The interchange machine on the box register -/

section Machine

variable {t₀ T Q K : ℕ} {U F X : Type}

/-- Interchange two axes of the box stream on `ln`: bits onto the spare `xt`, into the payload
register of the placed bank `rg (.x (sw j))`, the vendored interchange, back, packed onto
`ln`. -/
def rsaSwapP (rg : RsaR X → Fin T) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q) (sw : Fin (swapT t₀) → X)
    (hsw : Function.Injective fun j => rg (.x (sw j))) (hT : swapT t₀ ≤ T) (xt : X) :
    Pr F T Q (prime + K) U :=
  .seq (toBitsPass (rg .ln) (rg (.x xt)))
    (.seq (moveR (rg (.x xt)) (rg (.x (sw (reg pay)))) id)
      (.seq (placedSwapProg hd pay hi hQ (fun j => rg (.x (sw j))) hsw hT)
        (.seq (moveR (rg (.x (sw (reg pay)))) (rg (.x xt)) id) (ofBitsPass (rg (.x xt)) (rg .ln)))))

/-- The step bound of one interchange: `c` steps of the interchange machine, `sb` symbols on the
bank, `n` stream symbols. -/
def rsaSwapCost (T t₀ c sb n : ℕ) : ℕ :=
  (T + 12 * swapT t₀ + 5) * c + 6 * sb + 34 * n + 2 * T + 6 * swapT t₀ + 23

variable [DecidableEq X]

set_option maxHeartbeats 1000000 in
/-- **Interchange of two axes of the box.** `ln` holds the coefficient stream of `L`, laid out
as `[P] × [2^h] × [G] × [2^d]` records of `w` symbols; afterwards it holds the stream of
`swapList P (2^h) G (2^d) 1 0 L` (layout `[P] × [2^d] × [G] × [2^h]`); every other register is
as before. -/
theorem rsa_swap (body : F → Pr F T Q (prime + K) U) {rg : RsaR X → Fin T}
    {ι : Fin 64 → Fin T} (hrg : Function.Injective rg) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q) (sw : Fin (swapT t₀) → X)
    (hsw : Function.Injective fun j => rg (.x (sw j))) (hT : swapT t₀ ≤ T) (xt : X)
    (hxt : ∀ j, sw j ≠ xt) {P G h d w : ℕ} (hP : 0 < P) (hG : 0 < G) (hw : 0 < w)
    (hhd : h ≤ d + 1) (hdh : d ≤ h + 1) (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) = BinaryInterchangeRun.values P G (3 * w) h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hA : 4 ≤ prime + K)
    (V : RsaV X (prime + K)) (L : List GaussianInt) (hL : L.length = P * 2 ^ h * G * 2 ^ d)
    (hln : V.ln = cstream (prime + K) w L) (hxt0 : V.xr xt = [])
    (hpay0 : V.xr (sw (reg pay)) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → V.xr (sw j) = [])
    (hhdr : ∀ k, V.xr (sw (reg (hd k))) = separator :: (hs k).map bitSymbol)
    (hoth : ∀ i : Fin t₀, i ≠ pay → (∀ k, hd k ≠ i) → V.xr (sw (reg i)) = []) :
    RsaRuns body rg ι (rsaSwapP rg hd pay hi hQ sw hsw hT xt) V.get
      { V with ln := cstream (prime + K) w (swapList P (2 ^ h) G (2 ^ d) 1 0 L) }.get
      (rsaSwapCost T t₀ (BinaryInterchangeRun.cost P G (3 * w) h d hs)
        (∑ j, (V.xr (sw j)).length) (L.length * w)) := by
  classical
  refine RsaRuns.of_raw fun v S hcl hS => ?_
  have hL0 : ∀ y, S.L y = [] := hcl.1
  set ιp : Fin (swapT t₀) → Fin T := fun j => rg (.x (sw j)) with hιp
  set str := rg .ln with hstr_def
  set tmp := rg (.x xt) with htmp_def
  set M := L.length with hM
  set B' := 3 * w with hB'
  set ws := cstream (prime + K) w L with hws
  set ws' := cstream (prime + K) w (swapList P (2 ^ h) G (2 ^ d) 1 0 L) with hws'
  set pr := ιp (reg pay) with hpr
  have hst : str ≠ tmp := hrg.ne (by simp)
  have hstr : ∀ j, ιp j ≠ str := fun j => hrg.ne (by simp)
  have htmp : ∀ j, ιp j ≠ tmp := fun j => hrg.ne (fun h => hxt j (RsaR.x.inj h))
  have hpay_str : pr ≠ str := hstr _
  have hpay_tmp : pr ≠ tmp := htmp _
  have hR : S.R str = ws := by rw [hS .ln]; exact hln
  have htmp0 : S.R tmp = [] := by rw [hS (.x xt)]; exact hxt0
  have hSι : ∀ j, S.R (ιp j) = V.xr (sw j) := fun j => hS (.x (sw j))
  -- lengths
  have hwlen : ws.length = M * w := by rw [hws, length_cstream]
  have hw'len : ws'.length = M * w := by
    rw [hws', length_cstream, rsa_length_swapList, hL]; ring
  have hvol : P * 2 ^ h * G * 2 ^ d * B' = M * (3 * w) := by rw [hL, hB']
  have hBpos : 0 < B' := by omega
  have hswap : swapList P (2 ^ h) G (2 ^ d) B' blank (toBits ws) = toBits ws' :=
    rsa_swapList_cstream_bits P (2 ^ h) G (2 ^ d) w L hL
  have h8' : ∀ s ∈ ws', s.val < 8 := rsa_cstream_lt_eight (by omega) _
  have hhd_pay : ∀ k, hd k ≠ pay := by
    intro k hk
    have h' := hhdr k
    rw [hk, hpay0] at h'
    exact List.cons_ne_nil _ _ h'.symm
  have hreg_pay : ∀ j : Fin (swapT t₀), j ≠ reg pay → ιp j ≠ pr := fun j hj h' => hj (hsw h')
  -- step 1: expand the stream to bits on `tmp`
  obtain ⟨v₁, hu₁, he₁⟩ := toBitsPass_exec body str tmp hst v S
  set S₁ : Stacks T (prime + K) := { S with R := pushedR S.R str tmp (toBits (S.R str)).reverse }
    with hS₁
  -- step 2: move the bits to the payload register
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tmp pr hpay_tmp.symm id v₁ S₁
  set S₂ : Stacks T (prime + K) := { S₁ with R := movedR S₁.R tmp pr id (S₁.R tmp) } with hS₂
  have hS₁tmp : S₁.R tmp = (toBits ws).reverse := by
    show pushedR S.R str tmp (toBits (S.R str)).reverse tmp = _
    rw [pushedR, Function.update_self, hR, htmp0, List.append_nil]
  have hS₁pr : S₁.R pr = [] := by
    show pushedR S.R str tmp (toBits (S.R str)).reverse pr = _
    rw [pushedR, Function.update_of_ne hpay_tmp, Function.update_of_ne hpay_str, hSι, hpay0]
  have hS₂pr : S₂.R pr = toBits ws := by
    show movedR S₁.R tmp pr id (S₁.R tmp) pr = _
    rw [movedR, Function.update_self, hS₁tmp, hS₁pr, List.map_id, List.reverse_reverse,
      List.append_nil]
  have hS₂oth : ∀ y, y ≠ pr → y ≠ str → y ≠ tmp → S₂.R y = S.R y := by
    intro y h₁' h₂' h₃'
    simp [hS₂, movedR, hS₁, pushedR, h₁', h₂', h₃']
  have hS₂str : S₂.R str = [] := by
    simp [hS₂, movedR, hS₁, pushedR, hst, Ne.symm hpay_str]
  have hS₂tmp : S₂.R tmp = [] := by
    simp [hS₂, movedR, hS₁, pushedR, Ne.symm hpay_tmp]
  have hS₂ι : ∀ j, j ≠ reg pay → S₂.R (ιp j) = S.R (ιp j) := fun j hj =>
    hS₂oth _ (hreg_pay j hj) (hstr j) (htmp j)
  -- step 3: the placed interchange
  have hblen :
      (toBits ws).length = BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) B' := by
    rw [length_toBits, hwlen, BinaryAdjacentWidthInterchange.volume, hvol]; ring
  obtain ⟨x, hx⟩ := exists_ofFn_bits (toBits ws) (fun s hs' => mem_toBits hs') hblen
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := placedSwapProg_exec body hd pay hi hQ ιp hsw hT P G B' h d hs
    hhd hdh hv hc hP hG hBpos x v₂ S₂ (fun y => by rw [show S₂.L = S.L from rfl]; exact hL0 y)
    (fun j hj => by
      rw [hS₂ι j (fun h' => by rw [h', reg_val] at hj; exact absurd pay.isLt (by omega)), hSι]
      exact hpriv j hj)
    (fun k => by
      rw [hS₂ι _ (fun h' => hhd_pay k (BinaryInterchangeRun.slot_injective h')), hSι]
      exact hhdr k)
    (by rw [hS₂pr, ← hx])
    (fun i hip hk => by
      rw [hS₂ι _ (fun h' => hip (BinaryInterchangeRun.slot_injective h')), hSι,
        hoth i hip hk]
      simp)
  set S₃ : Stacks T (prime + K) := { S₂ with
    L := fun _ => []
    R := Function.update S₂.R pr (swapList P (2 ^ h) G (2 ^ d) B' blank (S₂.R pr)) } with hS₃
  have hS₃pr : S₃.R pr = toBits ws' := by
    show Function.update S₂.R pr (swapList P (2 ^ h) G (2 ^ d) B' blank (S₂.R pr)) pr = _
    rw [Function.update_self, hS₂pr, hswap]
  -- step 4: move the interchanged bits back to `tmp`
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body pr tmp hpay_tmp id v₃ S₃
  set S₄ : Stacks T (prime + K) := { S₃ with R := movedR S₃.R pr tmp id (S₃.R pr) } with hS₄
  have hS₃tmp : S₃.R tmp = [] := by
    show Function.update S₂.R pr (swapList P (2 ^ h) G (2 ^ d) B' blank (S₂.R pr)) tmp = _
    rw [Function.update_of_ne (Ne.symm hpay_tmp), hS₂tmp]
  have hS₄tmp : S₄.R tmp = (toBits ws').reverse := by
    show movedR S₃.R pr tmp id (S₃.R pr) tmp = _
    rw [movedR, Function.update_self, hS₃pr, hS₃tmp, List.map_id, List.append_nil]
  -- step 5: pack the bits onto the stream register
  obtain ⟨v₅, hu₅, he₅⟩ := ofBitsPass_exec body tmp str hst.symm ws' h8' v₄ S₄ hS₄tmp
  -- the sum over the placed registers
  have hsum : ∑ j, (S₂.R (ιp j)).length ≤ ∑ j, (V.xr (sw j)).length + 3 * (M * w) := by
    have hpt : ∀ j, (S₂.R (ιp j)).length ≤
        (V.xr (sw j)).length + if j = reg pay then 3 * (M * w) else 0 := by
      intro j
      by_cases hj : j = reg pay
      · subst hj
        simp only [↓reduceIte]
        rw [← hpr, hS₂pr, length_toBits, hwlen]
        omega
      · simp only [hj, ↓reduceIte]
        rw [hS₂ι j hj, hSι]
        omega
    calc ∑ j, (S₂.R (ιp j)).length
        ≤ ∑ j, ((V.xr (sw j)).length + if j = reg pay then 3 * (M * w) else 0) :=
          Finset.sum_le_sum fun j _ => hpt j
      _ = ∑ j, (V.xr (sw j)).length + 3 * (M * w) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp
  refine ⟨v₅, Function.update S.R str ws', _,
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))) rfl ?_, ?_, ?_⟩
  · have e₁ : (S.R str).length = M * w := by rw [hR, hwlen]
    have e₂ : (S₁.R tmp).length = 3 * (M * w) := by
      rw [hS₁tmp, List.length_reverse, length_toBits, hwlen]
    have e₄ : (S₃.R pr).length = 3 * (M * w) := by
      rw [hS₃pr, length_toBits, hw'len]
    rw [e₁, e₂, e₄, hw'len]
    unfold rsaSwapCost
    nlinarith [hm₃, hsum]
  · congr 1
    refine Stacks.ext rfl rfl ?_ ?_
    · funext y
      exact (hL0 y).symm
    · funext y
      by_cases hy₁ : y = str
      · subst hy₁
        simp [pushedR, hst, hS₄, movedR, hS₃, Ne.symm hpay_str, hS₂str]
      · by_cases hy₂ : y = tmp
        · subst hy₂
          simp [pushedR, hy₁, htmp0]
        · by_cases hy₃ : y = pr
          · rw [hy₃]
            have hpr0 : S.R pr = [] := by rw [hpr, hSι, hpay0]
            show pushedR S₄.R tmp str ws' pr = Function.update S.R str ws' pr
            rw [pushedR, Function.update_of_ne hpay_str, Function.update_of_ne hpay_tmp,
              Function.update_of_ne hpay_str, hpr0]
            show movedR S₃.R pr tmp id (S₃.R pr) pr = []
            rw [movedR, Function.update_of_ne hpay_tmp, Function.update_self]
          · simp [pushedR, hy₁, hy₂, hy₃, hS₄, movedR, hS₃, hS₂oth y hy₃ hy₁ hy₂]
  · intro r
    by_cases hr : r = .ln
    · rw [hr, hstr_def, Function.update_self]; rfl
    · rw [Function.update_of_ne (hrg.ne hr), hS r]
      cases r <;> first | rfl | exact absurd rfl hr
  · intro k hk
    rw [Function.update_of_ne (fun h => hk .ln h.symm)]

end Machine

/-- **The interchange cost.** For the counters of `values P G (3 w) h d`, the step bound of
`rsaSwapP` is at most `3 C (T + 12 swapT t₀ + 5) · (P 2^h G 2^d w) · max(1, h, d)^τ` plus
`6 sb + 34 n + 2 T + 6 swapT t₀ + 23`, `C = swapConst` the constant of the vendored interchange
bound: `O(T_box · 3w · ℓ^τ)` for a box of `T_box = P 2^h G 2^d` records of `w` symbols. -/
theorem rsaSwapCost_le (T t₀ : ℕ) {P G h d w : ℕ} (hP : 0 < P) (hG : 0 < G) (hw : 0 < w)
    (hhd : h ≤ d + 1) (hdh : d ≤ h + 1) (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) = BinaryInterchangeRun.values P G (3 * w) h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (sb n : ℕ) :
    (rsaSwapCost T t₀ (BinaryInterchangeRun.cost P G (3 * w) h d hs) sb n : ℝ) ≤
      3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (P * 2 ^ h * G * 2 ^ d * w : ℕ) *
        ((max 1 (max h d) : ℕ) : ℝ) ^ Parameters.tau +
      (6 * sb + 34 * n + 2 * T + 6 * swapT t₀ + 23 : ℕ) := by
  have hC := (Classical.choose_spec BinaryInterchangeRun.uniform_bound).2 P G (3 * w) h d hs hP hG
    (by omega) hhd hdh hv hc
  have hvol : (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) (3 * w) : ℝ) =
      3 * ((P * 2 ^ h * G * 2 ^ d * w : ℕ) : ℝ) := by
    unfold BinaryAdjacentWidthInterchange.volume; push_cast; ring
  rw [hvol] at hC
  have hF : (0 : ℝ) ≤ ((max 1 (max h d) : ℕ) : ℝ) ^ Parameters.tau := by positivity
  have hk : (0 : ℝ) ≤ ((T + 12 * swapT t₀ + 5 : ℕ) : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_left hC hk
  have e : rsaSwapCost T t₀ (BinaryInterchangeRun.cost P G (3 * w) h d hs) sb n =
      (T + 12 * swapT t₀ + 5) * BinaryInterchangeRun.cost P G (3 * w) h d hs +
        (6 * sb + 34 * n + 2 * T + 6 * swapT t₀ + 23) := by
    unfold rsaSwapCost; ring
  rw [e, Nat.cast_add, Nat.cast_mul]
  unfold swapConst
  linarith [this]

end

end IntegerMultBounds.MathlibTM2.Fast.ResampA
