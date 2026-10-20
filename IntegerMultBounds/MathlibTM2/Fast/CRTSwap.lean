module

public import IntegerMultBounds.MathlibTM2.Fast.CRTBase
public import IntegerMultBounds.MathlibTM2.Fast.CRTBox
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star
public import IntegerMultBounds.MathlibTM2.Node.SwapPass

/-!
# Exchanging two adjacent axes of a box

**Counters.** The vendored interchange reads five header registers, each holding `separator`
followed by a canonical binary counter (least significant bit first, no trailing zero bit;
`GrowingCounterData.Canonical`). `crtIncP e t` increments a growing counter held on `e` (least
significant bit on top), `crtEncP u tu e t` builds the counter `GrowingCounterData.advance |u| []`
of value `|u|` on the empty register `e` (one increment per symbol of `u`).

**Headers.** `crtHdrP` writes the headers of an interchange with outer count `2 ^ u`, one middle
block, inner length `2 ^ v · 3B` (as `v` zero bits below the counter `e3B` of `3B`) and chunk
widths `h`, `w` (`u`, `v`, `h`, `w` in unary). `crtHdrClear` empties them.

**Swap pass.** `crtSwapPass_exec` is the record stream form of `IntegerMultBounds.MathlibTM2.Node.swapPass` for any
interchange dimensions `(P, G, E, h, w)` with adjacent widths `|h - w| ≤ 1`: a stream `x` of
symbols below `8` whose bit expansion is interchanged into the bit expansion of `x'` becomes
`x'`. `crtSwapBoxBits`: for boxes, the bit expansions of the boxes along
`pre ++ j :: k :: post` and `pre ++ k :: j :: post` are related by the interchange with
`P = 2 ^ crtW pre`, `H = 2 ^ a j`, `D = 2 ^ a k`, `E = 2 ^ crtW post · B`.

**Swap step.** `crtSwapStep` writes the headers, runs the swap pass on the stream register and
empties the headers. `crtSwapStep_runs` turns the flattened box along `pre ++ j :: k :: post`
into the flattened box along `pre ++ k :: j :: post`; its cost is bounded through
`swapCost` (`crtSwapStep_runs`) and through `swapCost_le`
(`crtSwapStep_runs_le`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node


variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-! ### Growing counters -/

section Counter

open GrowingCounterData

lemma crt_increment_rep (rest : List Bool) (hr : rest.head? ≠ some true) :
    ∀ c, increment (List.replicate c true ++ rest) = List.replicate c false ++ true :: rest.tail
  | 0 => by
      rcases rest with _ | ⟨b, r⟩
      · rfl
      · cases b
        · rfl
        · simp at hr
  | c + 1 => by
      simp only [List.replicate_succ, List.cons_append]
      rw [increment, crt_increment_rep rest hr c]

lemma crt_split_trues : ∀ bs : List Bool,
    ∃ c rest, bs = List.replicate c true ++ rest ∧ rest.head? ≠ some true
  | [] => ⟨0, [], rfl, by simp⟩
  | false :: bs => ⟨0, false :: bs, rfl, by simp⟩
  | true :: bs => by
      obtain ⟨c, rest, h, hr⟩ := crt_split_trues bs
      exact ⟨c + 1, rest, by rw [h, List.replicate_succ, List.cons_append], hr⟩

lemma crt_advance_succ (n : ℕ) (bs : List Bool) : advance (n + 1) bs = increment (advance n bs) := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => rw [advance, ih, advance]

lemma crt_advance_length (n : ℕ) : (advance n []).length ≤ n := by
  induction n with
  | zero => simp [advance]
  | succ n ih =>
      rw [crt_advance_succ]
      have := (increment_length (advance n [])).2
      omega

lemma crt_value_replicate_false (n : ℕ) (bs : List Bool) :
    Counter.value (List.replicate n false ++ bs) = 2 ^ n * Counter.value bs := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, Counter.value, ih, pow_succ]; ring

end Counter

/-- Move register `i` onto `j`, writing `x` for every symbol. -/
theorem crtMvConst_runs {i j : Fin T} (hij : i ≠ j) (x : Fin (A + 4)) (R : Regs T A) :
    crtRuns body (moveR i j fun _ => x) R
      (Function.update (Function.update R i []) j (List.replicate (R i).length x ++ R j))
      (2 * (R i).length + 2) := by
  refine crtRuns_of_exec fun v S hS => ?_
  obtain ⟨v', hu, he⟩ := moveR_exec body i j hij (fun _ => x) v S
  subst hS
  refine ⟨v', _, hu, le_rfl, Exec.cast he rfl ?_⟩
  simp [movedR, List.map_const']

/-- One increment of the growing counter on `e` (least significant bit on top), through the
empty `t`: move the low run of ones onto `t`, replace the next bit (or the empty end) by a one,
and move the run back as zeros. -/
def crtIncP (e t : Fin T) : Pr P T Q A U :=
  .seq (crtMvWhile e t (bitSymbol true))
    (.seq (crtPop e) (.seq (crtPush e (bitSymbol true)) (moveR t e fun _ => bitSymbol false)))

theorem crtIncP_runs {e t : Fin T} (het : e ≠ t) (R : Regs T A) (bs : List Bool)
    (he : R e = bs.map bitSymbol) (ht : R t = []) :
    crtRuns body (crtIncP e t) R
      (Function.update R e ((GrowingCounterData.increment bs).map bitSymbol))
      (4 * bs.length + 6) := by
  obtain ⟨c, rest, rfl, hr⟩ := crt_split_trues bs
  have hr' : (rest.map bitSymbol : List (Fin (A + 4))).head? ≠ some (bitSymbol true) := by
    rcases rest with _ | ⟨b, r⟩
    · simp
    · cases b
      · simp [bitSymbol, Fin.ext_iff]
      · simp at hr
  have h₁ := crtMvWhile_runs (body := body) het (bitSymbol true) c (rest.map bitSymbol) hr' R
    (by rw [he]; simp [List.map_replicate])
  set R₁ := Function.update (Function.update R e (rest.map bitSymbol)) t
    (List.replicate c (bitSymbol true) ++ R t) with hR₁
  have h₂ := crtPop_runs (body := body) e R₁
  set R₂ := Function.update R₁ e (R₁ e).tail with hR₂
  have h₃ := crtPush_runs (body := body) e (bitSymbol true) R₂
  set R₃ := Function.update R₂ e (bitSymbol true :: R₂ e) with hR₃
  have h₄ := crtMvConst_runs (body := body) (Ne.symm het) (bitSymbol false) R₃
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq h₁ (crtRuns_seq h₂ (crtRuns_seq h₃ h₄))) ?_) ?_
  · rw [crt_increment_rep rest hr c]
    funext k
    by_cases k1 : k = e
    · rw [k1]
      simp [hR₃, hR₂, hR₁, Function.update_of_ne het, Function.update_of_ne (Ne.symm het), ht,
        List.map_replicate, List.map_tail]
    · by_cases k2 : k = t
      · rw [k2]; simp [hR₃, hR₂, hR₁, Ne.symm het, ht]
      · simp [hR₃, hR₂, hR₁, k1, k2]
  · simp [hR₃, hR₂, hR₁, Function.update_of_ne het, Function.update_of_ne (Ne.symm het), ht]
    omega

/-- The counter `advance |u| []` of value `|u|` on the empty register `e`. -/
def crtEncP (u tu e t : Fin T) : Pr P T Q A U := crtFor u tu (crtIncP e t)

theorem crtEncP_runs {u tu e t : Fin T} (hreg : [u, tu, e, t].Nodup) (R : Regs T A)
    (htu : R tu = []) (he : R e = []) (ht : R t = []) :
    crtRuns body (crtEncP u tu e t) R
      (Function.update R e ((GrowingCounterData.advance (R u).length []).map bitSymbol))
      ((R u).length * (4 * (R u).length + 9) + 2 * (R u).length + 4) := by
  have hreg' := hreg
  regs_ne hreg'
  set n := (R u).length with hn
  let Ψ : ℕ → Regs T A := fun j =>
    Function.update R e ((GrowingCounterData.advance j []).map bitSymbol)
  have hit : crtIter (body := body) (crtIncP e t) u tu Ψ (4 * n + 6) n := by
    intro j hj R' hR'
    have hRe : R' e = (GrowingCounterData.advance j []).map bitSymbol := by
      rw [hR' e (Ne.symm ‹u ≠ e›) (Ne.symm ‹tu ≠ e›)]; simp [Ψ]
    have hRt : R' t = [] := by
      rw [hR' t (Ne.symm ‹u ≠ t›) (Ne.symm ‹tu ≠ t›)]; simp [Ψ, Ne.symm ‹e ≠ t›, ht]
    refine crtRuns_mono (crtRuns_congr (crtIncP_runs (body := body) ‹e ≠ t› R' _ hRe hRt) ?_) ?_
    · funext k
      by_cases hk : k = u ∨ k = tu
      · have hke : k ≠ e := by rcases hk with h | h <;> rw [h] <;> assumption
        simp [hk, hke]
      · rw [not_or] at hk
        simp only [hk.1, hk.2, or_self, ↓reduceIte]
        by_cases k1 : k = e
        · rw [k1]; simp [Ψ, crt_advance_succ]
        · simp [Ψ, k1, hR' k hk.1 hk.2]
    · have := crt_advance_length j
      omega
  have h := crtFor_runs (body := body) ‹u ≠ tu› hit (R u) rfl
  have e0 : crtForRegs u tu (Ψ 0) (R u) [] = R := by
    funext k
    by_cases k1 : k = u
    · rw [k1]; simp [crtForRegs]
    · by_cases k2 : k = tu
      · rw [k2]; simp [crtForRegs, Ne.symm ‹u ≠ tu›, htu]
      · simp only [crtForRegs, k1, k2, ↓reduceIte, Ψ]
        by_cases k3 : k = e
        · rw [k3]; simp [he, GrowingCounterData.advance]
        · simp [k3]
  rw [e0] at h
  refine crtRuns_mono (crtRuns_congr h ?_) (by nlinarith)
  funext k
  by_cases k1 : k = u
  · rw [k1]; simp [crtForRegs, ‹u ≠ e›]
  · by_cases k2 : k = tu
    · rw [k2]; simp [crtForRegs, Ψ, Ne.symm ‹u ≠ tu›, ‹tu ≠ e›, htu]
    · simp [crtForRegs, k1, k2, Ψ]

/-! ### The swap pass on a symbol stream -/

section SwapPass

noncomputable section

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {t₀ T Q K : ℕ} {U F : Type}

/-- `IntegerMultBounds.MathlibTM2.Node.swapPass` for any interchange dimensions `(P, G, E, h, w)` with `|h - w| ≤ 1`:
the stream `x` (symbols below `8`) on `str` becomes `x'` when the interchange of the bit expansion
of `x` (inner blocks of `3 E` bits) is the bit expansion of `x'`. -/
theorem crtSwapPass_exec (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (str tmp : Fin T) (hst : str ≠ tmp) (hstr : ∀ j, ι j ≠ str) (htmp : ∀ j, ι j ≠ tmp)
    (Pp G E h w : ℕ) (hP : 0 < Pp) (hG : 0 < G) (hE : 0 < E) (hhw : h ≤ w + 1)
    (hwh : w ≤ h + 1)
    (x x' : List (Fin (prime + K + 4))) (hx : x.length = Pp * 2 ^ h * G * 2 ^ w * E)
    (h8' : ∀ s ∈ x', s.val < 8)
    (hsw : swapList Pp (2 ^ h) G (2 ^ w) (3 * E) blank (toBits x) = toBits x')
    (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) = swapValues Pp G (3 * E) h w k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ y, S.L y = [])
    (hR : S.R str = x) (htmp0 : S.R tmp = []) (hpay0 : S.R (ι (reg pay)) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator :: (hs k).map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime + 4) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (T + 12 * swapT t₀ + 5) * swapCost Pp G (3 * E) h w hs +
        6 * ∑ j, (S.R (ι j)).length + 34 * x.length + 2 * T + 6 * swapT t₀ + 23 ∧
      Exec body (swapPass hd pay hi hQ ι hι hT str tmp) (mk v S) m
        (mk v' { S with R := Function.update S.R str x' }) := by
  classical
  set n := x.length with hn
  set pr := ι (reg pay) with hpr
  have hpay_str : pr ≠ str := hstr _
  have hpay_tmp : pr ≠ tmp := htmp _
  have hvol : Pp * 2 ^ h * G * 2 ^ w * (3 * E) = 3 * n := by rw [hx]; ring
  have hx'len : x'.length = n := by
    have h1 := congrArg List.length hsw
    rw [swapList, List.length_map, List.length_range, length_toBits] at h1
    have : Pp * 2 ^ w * G * 2 ^ h * (3 * E) = 3 * n := by rw [← hvol]; ring
    omega
  have hhd_pay : ∀ k, hd k ≠ pay := by
    intro k hk
    have h' := hhdr k
    rw [hk, hpay0] at h'
    exact List.cons_ne_nil _ _ h'.symm
  have hreg_pay : ∀ j : Fin (swapT t₀), j ≠ reg pay → ι j ≠ pr := fun j hj h' => hj (hι h')
  -- step 1: expand the stream to bits on `tmp`
  obtain ⟨v₁, hu₁, he₁⟩ := toBitsPass_exec body str tmp hst v S
  set S₁ : Stacks T (prime + K) := { S with R := pushedR S.R str tmp (toBits (S.R str)).reverse }
    with hS₁
  -- step 2: move the bits to the payload register
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tmp pr hpay_tmp.symm id v₁ S₁
  set S₂ : Stacks T (prime + K) := { S₁ with R := movedR S₁.R tmp pr id (S₁.R tmp) } with hS₂
  have hS₁tmp : S₁.R tmp = (toBits x).reverse := by
    show pushedR S.R str tmp (toBits (S.R str)).reverse tmp = _
    rw [pushedR, Function.update_self, hR, htmp0, List.append_nil]
  have hS₁pr : S₁.R pr = [] := by
    show pushedR S.R str tmp (toBits (S.R str)).reverse pr = _
    rw [pushedR, Function.update_of_ne hpay_tmp, Function.update_of_ne hpay_str, hpay0]
  have hS₂pr : S₂.R pr = toBits x := by
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
  have hS₂ι : ∀ j, j ≠ reg pay → S₂.R (ι j) = S.R (ι j) := fun j hj =>
    hS₂oth _ (hreg_pay j hj) (hstr j) (htmp j)
  -- step 3: the placed interchange
  have hblen :
      (toBits x).length = BinaryAdjacentWidthInterchange.volume Pp (2 ^ h) G (2 ^ w) (3 * E) := by
    rw [length_toBits, BinaryAdjacentWidthInterchange.volume, hvol]
  obtain ⟨xb, hxb⟩ := exists_ofFn_bits (toBits x) (fun s hs' => mem_toBits hs') hblen
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := placedSwapProg_exec body hd pay hi hQ ι hι hT Pp G (3 * E) h w
    hs hhw hwh hv hc hP hG (by omega) xb v₂ S₂ hL
    (fun j hj => by
      rw [hS₂ι j (fun h' => by rw [h', reg_val] at hj; exact absurd pay.isLt (by omega))]
      exact hpriv j hj)
    (fun k => by
      rw [hS₂ι _ (fun h' => hhd_pay k (swapReg_injective h'))]
      exact hhdr k)
    (by rw [hS₂pr, ← hxb])
    (fun i hip hk => by
      rw [hS₂ι _ (fun h' => hip (swapReg_injective h'))]
      exact hother i hip hk)
  set S₃ : Stacks T (prime + K) := { S₂ with
    L := fun _ => []
    R := Function.update S₂.R pr (swapList Pp (2 ^ h) G (2 ^ w) (3 * E) blank (S₂.R pr)) }
    with hS₃
  have hS₃pr : S₃.R pr = toBits x' := by
    show Function.update S₂.R pr (swapList Pp (2 ^ h) G (2 ^ w) (3 * E) blank (S₂.R pr)) pr = _
    rw [Function.update_self, hS₂pr, hsw]
  -- step 4: move the interchanged bits back to `tmp`
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body pr tmp hpay_tmp id v₃ S₃
  set S₄ : Stacks T (prime + K) := { S₃ with R := movedR S₃.R pr tmp id (S₃.R pr) } with hS₄
  have hS₃tmp : S₃.R tmp = [] := by
    show Function.update S₂.R pr (swapList Pp (2 ^ h) G (2 ^ w) (3 * E) blank (S₂.R pr)) tmp = _
    rw [Function.update_of_ne (Ne.symm hpay_tmp), hS₂tmp]
  have hS₄tmp : S₄.R tmp = (toBits x').reverse := by
    show movedR S₃.R pr tmp id (S₃.R pr) tmp = _
    rw [movedR, Function.update_self, hS₃pr, hS₃tmp, List.map_id, List.append_nil]
  -- step 5: pack the bits onto the stream register
  obtain ⟨v₅, hu₅, he₅⟩ := ofBitsPass_exec body tmp str hst.symm x' h8' v₄ S₄ hS₄tmp
  have hsum : ∑ j, (S₂.R (ι j)).length ≤ ∑ j, (S.R (ι j)).length + 3 * n := by
    have hpt : ∀ j, (S₂.R (ι j)).length ≤
        (S.R (ι j)).length + if j = reg pay then 3 * n else 0 := by
      intro j
      by_cases hj : j = reg pay
      · subst hj
        simp only [↓reduceIte]
        rw [← hpr, hS₂pr, length_toBits]
        omega
      · simp only [hj, ↓reduceIte]
        rw [hS₂ι j hj]
        omega
    calc ∑ j, (S₂.R (ι j)).length
        ≤ ∑ j, ((S.R (ι j)).length + if j = reg pay then 3 * n else 0) :=
          Finset.sum_le_sum fun j _ => hpt j
      _ = ∑ j, (S.R (ι j)).length + 3 * n := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp
  refine ⟨v₅, _, hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))) rfl ?_⟩
  · have e₁ : (S.R str).length = n := by rw [hR]
    have e₂ : (S₁.R tmp).length = 3 * n := by
      rw [hS₁tmp, List.length_reverse, length_toBits]
    have e₄ : (S₃.R pr).length = 3 * n := by
      rw [hS₃pr, length_toBits, hx'len]
    rw [e₁, e₂, e₄, hx'len]
    nlinarith [hm₃, hsum]
  · congr 1
    refine Stacks.ext rfl rfl ?_ ?_
    · funext y
      exact (hL y).symm
    · funext y
      by_cases hy₁ : y = str
      · subst hy₁
        simp [pushedR, hst, hS₄, movedR, hS₃, Ne.symm hpay_str, hS₂str]
      · by_cases hy₂ : y = tmp
        · subst hy₂
          simp [pushedR, hy₁, htmp0]
        · by_cases hy₃ : y = pr
          · subst hy₃
            simp [pushedR, hy₁, hy₂, hS₄, movedR, hpay0]
          · simp [pushedR, hy₁, hy₂, hy₃, hS₄, movedR, hS₃, hS₂oth y hy₃ hy₁ hy₂]

end

end SwapPass

/-! ### Box streams -/

section BoxBits

variable {d : ℕ} (a : Fin d → ℕ)

lemma crt_toBits_flatten {A : ℕ} (l : List (List (Fin (A + 4)))) :
    toBits l.flatten = (l.map toBits).flatten := toBits_flatten l

/-- The bit-level interchange of the flattened boxes along `pre ++ j :: k :: post` and
`pre ++ k :: j :: post`, records of `B` symbols. -/
theorem crtSwapBoxBits {A : ℕ} (pre post : List (Fin d)) (j k : Fin d) (hjk : j ≠ k)
    (C : (Fin d → ℕ) → List (Fin (A + 4))) (B : ℕ) (hC : ∀ y, (C y).length = B)
    (x : Fin d → ℕ) :
    swapList (2 ^ crtW a pre) (2 ^ a j) 1 (2 ^ a k) (3 * (2 ^ crtW a post * B)) blank
        (toBits (crtBox a (pre ++ j :: k :: post) C x).flatten) =
      toBits (crtBox a (pre ++ k :: j :: post) C x).flatten := by
  have hmap : ∀ o : List (Fin d), (crtBox a o C x).map toBits = crtBox a o (toBits ∘ C) x := by
    intro o; simp [crtBox, List.map_map]
  rw [crt_toBits_flatten, crt_toBits_flatten, hmap, hmap,
    show 3 * (2 ^ crtW a post * B) = 2 ^ crtW a post * (3 * B) by ring]
  exact crtSwapBox a blank pre post j k hjk (toBits ∘ C) (3 * B)
    (fun y => by simp [length_toBits, hC]) x

end BoxBits

/-! ### Headers -/

section Headers

/-- The header registers of an interchange with outer count `2 ^ |uU|`, one middle block,
inner length `2 ^ |vU|` times the counter `e3B`, and chunk widths `|aJ|`, `|aK|`. -/
def crtHdrP (uU vU aJ aK e3B tu t₁ t₂ : Fin T) (hdr : Fin 5 → Fin T) : Pr P T Q A U :=
  .seq (crtPush (hdr 0) (bitSymbol true)) <| .seq (zeroBits uU (hdr 0) t₁) <|
  .seq (crtPush (hdr 0) separator) <|
  .seq (crtPush (hdr 1) (bitSymbol true)) <| .seq (crtPush (hdr 1) separator) <|
  .seq (bcopy e3B (hdr 2) t₁ t₂) <| .seq (zeroBits vU (hdr 2) t₁) <|
  .seq (crtPush (hdr 2) separator) <|
  .seq (crtEncP aJ tu (hdr 3) t₁) <| .seq (crtPush (hdr 3) separator) <|
  .seq (crtEncP aK tu (hdr 4) t₁) (crtPush (hdr 4) separator)

/-- Empty the five header registers. -/
def crtHdrClear (hdr : Fin 5 → Fin T) : Pr P T Q A U :=
  .seq (uclear (hdr 0)) <| .seq (uclear (hdr 1)) <| .seq (uclear (hdr 2)) <|
  .seq (uclear (hdr 3)) (uclear (hdr 4))

/-- The header counters: `2 ^ u`, `1`, `2 ^ v` times the counter `e`, and the counters of
`h` and `w`. -/
def crtHdrBits (u v h w : ℕ) (e : List Bool) : Fin 5 → List Bool :=
  ![List.replicate u false ++ [true], [true], List.replicate v false ++ e,
    GrowingCounterData.advance h [], GrowingCounterData.advance w []]

lemma crtHdrBits_canonical (u v h w : ℕ) (e : List Bool) (he : e.getLast? = some true) :
    ∀ k, GrowingCounterData.Canonical (crtHdrBits u v h w e k) := by
  intro k
  fin_cases k
  · right; simp [crtHdrBits]
  · right; simp [crtHdrBits]
  · right
    simp only [crtHdrBits]
    rcases e with _ | ⟨b, e⟩
    · simp at he
    · show (List.replicate v false ++ b :: e).getLast? = some true
      rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      exact he
  · exact GrowingCounterData.advance_canonical _ _ (Or.inl rfl)
  · exact GrowingCounterData.advance_canonical _ _ (Or.inl rfl)

lemma crtHdrBits_value (u v h w : ℕ) (e : List Bool) :
    ∀ k, Counter.value (crtHdrBits u v h w e k) =
      swapValues (2 ^ u) 1 (2 ^ v * Counter.value e) h w k := by
  intro k
  fin_cases k
  · simp [crtHdrBits, swapValues, crt_value_replicate_false, Counter.value]
  · simp [crtHdrBits, swapValues]
  · simp [crtHdrBits, swapValues, crt_value_replicate_false]
  · simp [crtHdrBits, swapValues, GrowingCounterData.empty_value]
  · simp [crtHdrBits, swapValues, GrowingCounterData.empty_value]

/-- The header registers after `crtHdrP`. -/
def crtHdrRegs (hdr : Fin 5 → Fin T) (R : Regs T A) (u v h w : ℕ) (e : List Bool) : Regs T A :=
  fun r => if r = hdr 0 then separator :: (crtHdrBits u v h w e 0).map bitSymbol
    else if r = hdr 1 then separator :: (crtHdrBits u v h w e 1).map bitSymbol
    else if r = hdr 2 then separator :: (crtHdrBits u v h w e 2).map bitSymbol
    else if r = hdr 3 then separator :: (crtHdrBits u v h w e 3).map bitSymbol
    else if r = hdr 4 then separator :: (crtHdrBits u v h w e 4).map bitSymbol
    else R r

lemma crtHdrRegs_hdr {hdr : Fin 5 → Fin T} (hinj : Function.Injective hdr) (R : Regs T A)
    (u v h w : ℕ) (e : List Bool) (k : Fin 5) :
    crtHdrRegs hdr R u v h w e (hdr k) = separator :: (crtHdrBits u v h w e k).map bitSymbol := by
  fin_cases k <;> simp [crtHdrRegs, hinj.eq_iff]

lemma crtHdrRegs_of_ne {hdr : Fin 5 → Fin T} (R : Regs T A) (u v h w : ℕ) (e : List Bool)
    {r : Fin T} (hr : ∀ k, hdr k ≠ r) : crtHdrRegs hdr R u v h w e r = R r := by
  simp [crtHdrRegs, Ne.symm (hr 0), Ne.symm (hr 1), Ne.symm (hr 2), Ne.symm (hr 3),
    Ne.symm (hr 4)]

theorem crtHdrP_runs {uU vU aJ aK e3B tu t₁ t₂ : Fin T} {hdr : Fin 5 → Fin T}
    (hreg : [uU, vU, aJ, aK, e3B, tu, t₁, t₂, hdr 0, hdr 1, hdr 2, hdr 3, hdr 4].Nodup)
    (R : Regs T A) (e : List Bool) (he3 : R e3B = e.map bitSymbol)
    (htu : R tu = []) (ht₁ : R t₁ = []) (ht₂ : R t₂ = []) (hh : ∀ k, R (hdr k) = []) :
    crtRuns body (crtHdrP uU vU aJ aK e3B tu t₁ t₂ hdr) R
      (crtHdrRegs hdr R (R uU).length (R vU).length (R aJ).length (R aK).length e)
      (4 * (R uU).length + 4 * (R vU).length + 6 * e.length +
        (R aJ).length * (4 * (R aJ).length + 11) + (R aK).length * (4 * (R aK).length + 11) +
        40) := by
  have hreg' := hreg
  regs_ne hreg'
  have hinj : Function.Injective hdr := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp_all)
  -- header 0
  have s₁ := crtPush_runs (body := body) (hdr 0) (bitSymbol true) R
  set R₁ := Function.update R (hdr 0) (bitSymbol true :: R (hdr 0)) with hR₁
  have s₂ := crtZeroBits_runs (body := body) ‹uU ≠ hdr 0› ‹uU ≠ t₁› (Ne.symm ‹t₁ ≠ hdr 0›) R₁
    (by simp [hR₁, ‹t₁ ≠ hdr 0›, ht₁])
  set R₂ := Function.update R₁ (hdr 0) (binSyms (R₁ uU).length 0 ++ R₁ (hdr 0)) with hR₂
  have s₃ := crtPush_runs (body := body) (hdr 0) separator R₂
  set R₃ := Function.update R₂ (hdr 0) (separator :: R₂ (hdr 0)) with hR₃
  -- header 1
  have s₄ := crtPush_runs (body := body) (hdr 1) (bitSymbol true) R₃
  set R₄ := Function.update R₃ (hdr 1) (bitSymbol true :: R₃ (hdr 1)) with hR₄
  have s₅ := crtPush_runs (body := body) (hdr 1) separator R₄
  set R₅ := Function.update R₄ (hdr 1) (separator :: R₄ (hdr 1)) with hR₅
  -- header 2
  have s₆ := crtBcopy_runs (body := body) (a := e3B) (c := hdr 2) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) R₅ (by simp [hR₅, hR₄, hR₃, hR₂, hR₁, ‹t₁ ≠ hdr 0›, 
      ‹t₁ ≠ hdr 1›, ht₁])
    (by simp [hR₅, hR₄, hR₃, hR₂, hR₁, ‹t₂ ≠ hdr 0›, ‹t₂ ≠ hdr 1›, ht₂])
  set R₆ := Function.update R₅ (hdr 2) (R₅ e3B ++ R₅ (hdr 2)) with hR₆
  have s₇ := crtZeroBits_runs (body := body) ‹vU ≠ hdr 2› ‹vU ≠ t₁› (Ne.symm ‹t₁ ≠ hdr 2›) R₆
    (by simp [hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, ‹t₁ ≠ hdr 0›, ‹t₁ ≠ hdr 1›, 
      ‹t₁ ≠ hdr 2›, ht₁])
  set R₇ := Function.update R₆ (hdr 2) (binSyms (R₆ vU).length 0 ++ R₆ (hdr 2)) with hR₇
  have s₈ := crtPush_runs (body := body) (hdr 2) separator R₇
  set R₈ := Function.update R₇ (hdr 2) (separator :: R₇ (hdr 2)) with hR₈
  -- header 3
  have s₉ := crtEncP_runs (body := body) (u := aJ) (tu := tu) (e := hdr 3) (t := t₁)
    (by regs_nodup) R₈
    (by simp [hR₈, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, ‹tu ≠ hdr 0›, ‹tu ≠ hdr 1›, 
      ‹tu ≠ hdr 2›, htu])
    (by simp [hR₈, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, Ne.symm ‹hdr 0 ≠ hdr 3›, Ne.symm ‹hdr 1 ≠ hdr 3›,
      Ne.symm ‹hdr 2 ≠ hdr 3›, hh])
    (by simp [hR₈, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, ‹t₁ ≠ hdr 0›, ‹t₁ ≠ hdr 1›, 
      ‹t₁ ≠ hdr 2›, ht₁])
  set R₉ := Function.update R₈ (hdr 3)
    ((GrowingCounterData.advance (R₈ aJ).length []).map bitSymbol) with hR₉
  have s₁₀ := crtPush_runs (body := body) (hdr 3) separator R₉
  set R₁₀ := Function.update R₉ (hdr 3) (separator :: R₉ (hdr 3)) with hR₁₀
  -- header 4
  have s₁₁ := crtEncP_runs (body := body) (u := aK) (tu := tu) (e := hdr 4) (t := t₁)
    (by regs_nodup) R₁₀
    (by simp [hR₁₀, hR₉, hR₈, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, ‹tu ≠ hdr 0›, 
      ‹tu ≠ hdr 1›, ‹tu ≠ hdr 2›, ‹tu ≠ hdr 3›, htu])
    (by simp [hR₁₀, hR₉, hR₈, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, Ne.symm ‹hdr 0 ≠ hdr 4›,
      Ne.symm ‹hdr 1 ≠ hdr 4›, Ne.symm ‹hdr 2 ≠ hdr 4›, Ne.symm ‹hdr 3 ≠ hdr 4›, hh])
    (by simp [hR₁₀, hR₉, hR₈, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, ‹t₁ ≠ hdr 0›, 
      ‹t₁ ≠ hdr 1›, ‹t₁ ≠ hdr 2›, ‹t₁ ≠ hdr 3›, ht₁])
  set R₁₁ := Function.update R₁₀ (hdr 4)
    ((GrowingCounterData.advance (R₁₀ aK).length []).map bitSymbol) with hR₁₁
  have s₁₂ := crtPush_runs (body := body) (hdr 4) separator R₁₁
  -- the lengths read along the way
  have lu : (R₁ uU).length = (R uU).length := by simp [hR₁, ‹uU ≠ hdr 0›]
  have lv : (R₆ vU).length = (R vU).length := by
    simp [hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, ‹vU ≠ hdr 0›, ‹vU ≠ hdr 1›, ‹vU ≠ hdr 2›]
  have le : R₅ e3B = R e3B := by
    simp [hR₅, hR₄, hR₃, hR₂, hR₁, ‹e3B ≠ hdr 0›, ‹e3B ≠ hdr 1›]
  have lj : (R₈ aJ).length = (R aJ).length := by
    simp [hR₈, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, ‹aJ ≠ hdr 0›, ‹aJ ≠ hdr 1›, ‹aJ ≠ hdr 2›]
  have lk : (R₁₀ aK).length = (R aK).length := by
    simp [hR₁₀, hR₉, hR₈, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, ‹aK ≠ hdr 0›, ‹aK ≠ hdr 1›,
      ‹aK ≠ hdr 2›, ‹aK ≠ hdr 3›]
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ (crtRuns_seq s₃
    (crtRuns_seq s₄ (crtRuns_seq s₅ (crtRuns_seq s₆ (crtRuns_seq s₇ (crtRuns_seq s₈
    (crtRuns_seq s₉ (crtRuns_seq s₁₀ (crtRuns_seq s₁₁ s₁₂))))))))))) ?_) ?_
  · crt_ne_symm
    funext r
    by_cases hr : ∃ k, hdr k = r
    · obtain ⟨k, rfl⟩ := hr
      rw [crtHdrRegs_hdr hinj]
      fin_cases k
      · simp [crtHdrBits,
          binSyms_zero_right, List.map_replicate, *]
      · simp [crtHdrBits, *]
      · simp [crtHdrBits,
          binSyms_zero_right, List.map_replicate, *]
      · simp [crtHdrBits, *]
      · simp [crtHdrBits, *]
    · have hr' : ∀ k, hdr k ≠ r := fun k hk => hr ⟨k, hk⟩
      rw [crtHdrRegs_of_ne R _ _ _ _ e hr']
      simp [hR₁₁, hR₁₀, hR₉, hR₈, hR₇, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, Function.update_of_ne
        (Ne.symm (hr' 0)), Function.update_of_ne (Ne.symm (hr' 1)),
        Function.update_of_ne (Ne.symm (hr' 2)), Function.update_of_ne (Ne.symm (hr' 3)),
        Function.update_of_ne (Ne.symm (hr' 4))]
  · rw [lu, lv, lj, lk, le, he3, List.length_map]
    nlinarith

end Headers

/-! ### The swap step -/

section Step

noncomputable section

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- The header slots `0, …, 4` of a six-tape interchange bank. -/
def crtHd : Fin 5 → Fin 6 := Fin.castSucc

/-- The payload slot of a six-tape interchange bank. -/
def crtPay : Fin 6 := Fin.last 5

lemma crtHd_inj : Function.Injective crtHd := Fin.castSucc_injective 5

lemma crtHd_ne_pay (k : Fin 5) : crtHd k ≠ crtPay := by
  simp [crtHd, crtPay, Fin.ext_iff]; omega

lemma crt_eq_hd_of_ne_pay (i : Fin 6) (hi : i ≠ crtPay) : ∃ k, crtHd k = i :=
  ⟨⟨i.val, by have := i.isLt; simp [crtPay, Fin.ext_iff] at hi; omega⟩, Fin.ext rfl⟩

/-- A natural upper bound of the interchange cost from `swapCost_le`:
volume `V`, chunk widths `h`, `w`. -/
def crtSwapCostN (V h w : ℕ) : ℕ :=
  ⌈swapConst * V * ((max 1 (max h w) : ℕ) : ℝ) ^ Parameters.tau⌉₊

lemma crt_cost_le (Pp G E h w : ℕ) (hs : Fin 5 → List Bool) (hP : 0 < Pp) (hG : 0 < G)
    (hE : 0 < E) (hhw : h ≤ w + 1) (hwh : w ≤ h + 1)
    (hv : ∀ k, Counter.value (hs k) = swapValues Pp G E h w k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) :
    swapCost Pp G E h w hs ≤
      crtSwapCostN (BinaryAdjacentWidthInterchange.volume Pp (2 ^ h) G (2 ^ w) E) h w := by
  have hC := (Classical.choose_spec swapCost_le).2 Pp G E h w hs hP hG hE
    hhw hwh hv hc
  unfold crtSwapCostN
  exact Nat.cast_le.1 (hC.trans (Nat.le_ceil _))

variable {T Q K : ℕ} {U F : Type}

/-- One exchange of adjacent axes: write the headers into the bank `ι`, run the swap pass on
`str` (spare `stmp`), empty the headers. -/
def crtSwapStep (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (str stmp uU vU aJ aK e3B tu t₁ t₂ : Fin T) : Pr F T Q (prime + K) U :=
  .seq (crtHdrP uU vU aJ aK e3B tu t₁ t₂ fun k => ι (reg (crtHd k)))
    (.seq (swapPass crtHd crtPay crtHd_inj hQ ι hι hT str stmp)
      (crtHdrClear fun k => ι (reg (crtHd k))))

variable {d : ℕ} (a : Fin d → ℕ)

theorem crtSwapStep_runs {body : F → Pr F T Q (prime + K) U}
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    {str stmp uU vU aJ aK e3B tu t₁ t₂ : Fin T}
    (hreg : [str, stmp, uU, vU, aJ, aK, e3B, tu, t₁, t₂].Nodup)
    (hbank : ∀ r ∈ [str, stmp, uU, vU, aJ, aK, e3B, tu, t₁, t₂], ∀ j, ι j ≠ r)
    (pre post : List (Fin d)) (j k : Fin d) (hjk : j ≠ k) (hj : a j ≤ a k + 1)
    (hk : a k ≤ a j + 1)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ s ∈ C y, s.val < 8) (x : Fin d → ℕ)
    (R : Regs T (prime + K)) (hstr : R str = (crtBox a (pre ++ j :: k :: post) C x).flatten)
    (hu : (R uU).length = crtW a pre) (hv : (R vU).length = crtW a post)
    (haJ : (R aJ).length = a j) (haK : (R aK).length = a k)
    (he3 : R e3B = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (hstmp : R stmp = []) (htu : R tu = []) (ht₁ : R t₁ = []) (ht₂ : R t₂ = [])
    (hι0 : ∀ i, R (ι i) = []) :
    crtRuns body (crtSwapStep hQ ι hι hT str stmp uU vU aJ aK e3B tu t₁ t₂) R
      (Function.update R str (crtBox a (pre ++ k :: j :: post) C x).flatten)
      ((T + 12 * swapT 6 + 5) * crtSwapCostN (3 * (2 ^ crtW a (pre ++ j :: k :: post) * B))
          (a j) (a k) +
        (6 * swapT 6 + 10) * (crtW a pre + crtW a post + 3 * B + a j + a k + 2) +
        34 * (2 ^ crtW a (pre ++ j :: k :: post) * B) + 2 * T + 6 * swapT 6 +
        4 * crtW a pre + 4 * crtW a post + 18 * B +
        a j * (4 * a j + 11) + a k * (4 * a k + 11) + 80) := by
  have hreg' := hreg
  regs_ne hreg'
  set hdr : Fin 5 → Fin T := fun k => ι (reg (crtHd k)) with hhdr
  have hdr_inj : Function.Injective hdr := fun a b h =>
    crtHd_inj (swapReg_injective (hι h))
  have hb : ∀ r ∈ [str, stmp, uU, vU, aJ, aK, e3B, tu, t₁, t₂], ∀ k, hdr k ≠ r :=
    fun r hr k => hbank r hr _
  have hreg₂ : [uU, vU, aJ, aK, e3B, tu, t₁, t₂, hdr 0, hdr 1, hdr 2, hdr 3, hdr 4].Nodup := by
    have e : [uU, vU, aJ, aK, e3B, tu, t₁, t₂, hdr 0, hdr 1, hdr 2, hdr 3, hdr 4] =
        [uU, vU, aJ, aK, e3B, tu, t₁, t₂] ++ List.ofFn hdr := rfl
    rw [e, List.nodup_append]
    refine ⟨by regs_nodup, List.nodup_ofFn.2 hdr_inj, ?_⟩
    intro r hr r' hr' hrr
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hr'
    exact hb r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)) k hrr.symm
  set n := 2 ^ crtW a (pre ++ j :: k :: post) * B with hn
  set e := GrowingCounterData.advance (3 * B) [] with he
  have hevalue : Counter.value e = 3 * B := GrowingCounterData.empty_value _
  have helen : e.length ≤ 3 * B := crt_advance_length _
  have helast : e.getLast? = some true := by
    rcases GrowingCounterData.advance_canonical (3 * B) [] (Or.inl rfl) with h | h
    · rw [← he] at h; rw [h] at hevalue; simp [Counter.value] at hevalue; omega
    · exact h
  -- the headers
  have h₁ := crtHdrP_runs (body := body) hreg₂ R e he3 htu ht₁ ht₂ (fun k => hι0 _)
  rw [hu, hv, haJ, haK] at h₁
  set R₁ := crtHdrRegs hdr R (crtW a pre) (crtW a post) (a j) (a k) e with hR₁
  have hR₁hdr : ∀ k', R₁ (hdr k') =
      separator :: (crtHdrBits (crtW a pre) (crtW a post) (a j) (a k) e k').map bitSymbol :=
    crtHdrRegs_hdr hdr_inj R _ _ _ _ e
  have hR₁oth : ∀ r, (∀ k', hdr k' ≠ r) → R₁ r = R r := fun r hr =>
    crtHdrRegs_of_ne R _ _ _ _ e hr
  set H := crtW a pre + crtW a post + 3 * B + a j + a k + 2 with hH
  have hbits : ∀ k', (crtHdrBits (crtW a pre) (crtW a post) (a j) (a k) e k').length + 1 ≤ H := by
    intro k'
    have l3 := crt_advance_length (a j)
    have l4 := crt_advance_length (a k)
    fin_cases k' <;> simp [crtHdrBits, hH] <;> omega
  have hR₁len : ∀ i, (R₁ (ι i)).length ≤ H := by
    intro i
    by_cases hi : ∃ k', hdr k' = ι i
    · obtain ⟨k', hk'⟩ := hi
      rw [← hk', hR₁hdr]; simpa using hbits k'
    · rw [hR₁oth _ (fun k' hk' => hi ⟨k', hk'⟩), hι0]; simp
  -- the swap pass
  have hsw := crtSwapBoxBits a pre post j k hjk C B hC x
  have h₂ : crtRuns body (swapPass crtHd crtPay crtHd_inj hQ ι hι hT str stmp) R₁
      (Function.update R₁ str (crtBox a (pre ++ k :: j :: post) C x).flatten)
      ((T + 12 * swapT 6 + 5) * crtSwapCostN (3 * n) (a j) (a k) + 6 * (swapT 6 * H) +
        34 * n + 2 * T + 6 * swapT 6 + 23) := by
    intro v₀ S hS hL
    have hP : 0 < 2 ^ crtW a pre := by positivity
    have hE : 0 < 2 ^ crtW a post * B := by positivity
    have hxlen : (crtBox a (pre ++ j :: k :: post) C x).flatten.length =
        2 ^ crtW a pre * 2 ^ a j * 1 * 2 ^ a k * (2 ^ crtW a post * B) := by
      rw [crtBox_flatten_length a _ C x B hC, crtW_append, crtW_cons, crtW_cons]
      simp only [pow_add]; ring
    have hvals : ∀ k', Counter.value (crtHdrBits (crtW a pre) (crtW a post) (a j) (a k) e k') =
        swapValues (2 ^ crtW a pre) 1 (3 * (2 ^ crtW a post * B)) (a j) (a k)
          k' := by
      intro k'
      rw [crtHdrBits_value, hevalue]
      congr 1
      ring
    obtain ⟨v', m, hu', hm, he'⟩ := crtSwapPass_exec body crtHd crtPay crtHd_inj hQ ι hι hT
      str stmp ‹str ≠ stmp› (fun i => hbank str (by simp) i) (fun i => hbank stmp (by simp) i)
      (2 ^ crtW a pre) 1 (2 ^ crtW a post * B) (a j) (a k) hP Nat.one_pos hE hj hk
      (crtBox a (pre ++ j :: k :: post) C x).flatten (crtBox a (pre ++ k :: j :: post) C x).flatten
      hxlen
      (by
        intro s hs
        obtain ⟨y, hy, hsy⟩ := List.mem_flatten.1 hs
        simp only [crtBox, List.mem_map] at hy
        obtain ⟨_, _, rfl⟩ := hy
        exact h8 _ s hsy)
      hsw _ hvals (crtHdrBits_canonical _ _ _ _ e helast) v₀ S hL
      (by rw [hS, hR₁oth _ (hb str (by simp)), hstr])
      (by rw [hS, hR₁oth _ (hb stmp (by simp)), hstmp])
      (by
        rw [hS, hR₁oth _ (fun k' hk' => crtHd_ne_pay k'
          (swapReg_injective (hι hk'))), hι0])
      (fun i hi => by
        rw [hS, hR₁oth _ (fun k' hk' => by
          have h2 : (reg (crtHd k')).val = i.val := congrArg Fin.val (hι hk')
          rw [reg_val] at h2
          have := (crtHd k').isLt
          omega), hι0])
      (fun k' => by rw [hS, hR₁hdr])
      (fun i hip hk' => absurd (crt_eq_hd_of_ne_pay i hip) (fun ⟨k'', h''⟩ => hk' k'' h''))
    refine ⟨v', m, hu', hm.trans ?_, by rw [hS] at he'; exact he'⟩
    have hcost := crt_cost_le (2 ^ crtW a pre) 1 (3 * (2 ^ crtW a post * B)) (a j) (a k)
      (crtHdrBits (crtW a pre) (crtW a post) (a j) (a k) e) hP Nat.one_pos (by positivity) hj hk
      hvals (crtHdrBits_canonical _ _ _ _ e helast)
    have hvol : BinaryAdjacentWidthInterchange.volume (2 ^ crtW a pre) (2 ^ a j) 1 (2 ^ a k)
        (3 * (2 ^ crtW a post * B)) = 3 * n := by
      rw [BinaryAdjacentWidthInterchange.volume, hn, crtW_append, crtW_cons, crtW_cons]
      simp only [pow_add]; ring
    rw [hvol] at hcost
    have hsum : ∑ i, (S.R (ι i)).length ≤ swapT 6 * H := by
      rw [hS]
      calc ∑ i, (R₁ (ι i)).length ≤ ∑ _i : Fin (swapT 6), H := Finset.sum_le_sum fun i _ => hR₁len i
        _ = swapT 6 * H := by simp
    rw [hxlen, ← show n = 2 ^ crtW a pre * 2 ^ a j * 1 * 2 ^ a k * (2 ^ crtW a post * B) by
      rw [hn, crtW_append, crtW_cons, crtW_cons]; simp only [pow_add]; ring]
    have := Nat.mul_le_mul_left (T + 12 * swapT 6 + 5) hcost
    omega
  -- clearing the headers
  set R₂ := Function.update R₁ str (crtBox a (pre ++ k :: j :: post) C x).flatten with hR₂
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

end

end Step

end IntegerMultBounds.MathlibTM2.Fast
