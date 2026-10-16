module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBList
public import IntegerMultBounds.MathlibTM2.Fast.ResampBAxis

/-!
# Moving an axis of the box innermost, on any register type

`swapPass` (`Node/SwapPass`) interchanges two axes of the box stream on a register `rl`, a
coefficient stream `cstream A w L` laid out as `[P] × [2^h] × [G] × [2^d]` records: it expands the
stream to bits on the spare `rx`, runs the vendored binary interchange `placedSwapProg` on the
bank `rb j`, and packs the result. `rsb_swap` states it as a contract `RsbRuns` for any register
type: afterwards `rl` holds `cstream A w (swapList P (2^h) G (2^d) 1 0 L)`, laid out as
`[P] × [2^d] × [G] × [2^h]`; the widths satisfy `h ≤ d + 1`, `d ≤ h + 1`; every other register is
as before. The bank holds the five header counters of `values P G (3 w) h d` (`rsbBank`) and is
otherwise empty.

The proof follows `rsb_swap`, stated there for the register type of `Ã`.

`rsb_lift`: a contract on registers `R₁` is a contract on any register type `R₂` into which
`R₁` embeds, the registers off the image unchanged.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


noncomputable section

/-! ### Contracts along embeddings -/

section Lift

variable {T Q A : ℕ} {U : Type} {P : Type} {R₁ R₂ : Type}
  {body : P → Pr P T Q A U} {ι : Fin 64 → Fin T}

/-- A contract from a raw execution. -/
theorem RsbRuns.of_raw {R : Type} {rg : R → Fin T} {p : Pr P T Q A U}
    {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : ∀ v S, RsbClean ι S → RsbHolds rg S ρ →
      ∃ (v' : HS T Q A U) (Rs : Fin T → List (Fin (A + 4))) (n : ℕ), v'.user = v.user ∧ n ≤ b ∧
        Exec body p (mk v S) n (mk v' { S with R := Rs }) ∧ (∀ r, Rs (rg r) = ρ' r) ∧
        ∀ k, (∀ r, rg r ≠ k) → Rs k = S.R k) :
    RsbRuns body rg ι p ρ ρ' b := by
  intro v S hc hS
  obtain ⟨v', Rs, n, hu, hn, he, h₁, h₂⟩ := h v S hc hS
  exact ⟨v', _, n, hu, hn, he, h₁, rfl, rfl, rfl, h₂⟩

/-- **Lifting a contract along an embedding** `e : R₁ → R₂` with `rg₁ = rg₂ ∘ e`: the registers
`e x` change as in the contract, all others are kept. -/
theorem rsb_lift {rg₂ : R₂ → Fin T} (hrg₂ : Function.Injective rg₂) (e : R₁ → R₂)
    {p : Pr P T Q A U} {ρ₁ ρ₁' : R₁ → List (Fin (A + 4))} {b : ℕ}
    (h : RsbRuns body (fun x => rg₂ (e x)) ι p ρ₁ ρ₁' b) (ρ₂ ρ₂' : R₂ → List (Fin (A + 4)))
    (h₀ : ∀ x, ρ₂ (e x) = ρ₁ x) (h₁ : ∀ x, ρ₂' (e x) = ρ₁' x)
    (h₂ : ∀ r, (∀ x, e x ≠ r) → ρ₂' r = ρ₂ r) :
    RsbRuns body rg₂ ι p ρ₂ ρ₂' b := by
  classical
  intro v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hfr⟩ := h v S hc (fun x => by rw [hS, h₀])
  refine ⟨v', S', n, hu, hn, he, fun r => ?_, ⟨hfr.1, hfr.2.1, hfr.2.2.1, fun k hk => ?_⟩⟩
  · by_cases hr : ∃ x, e x = r
    · obtain ⟨x, rfl⟩ := hr
      rw [hS' x, h₁]
    · simp only [not_exists] at hr
      rw [h₂ r hr, ← hS r]
      exact hfr.2.2.2 _ (fun x hx => hr x (hrg₂ hx))
  · exact hfr.2.2.2 k (fun x => hk _)

/-- Lifting along the left summand. -/
theorem rsb_lift_inl {R₃ : Type} {rg : R₁ → Fin T} {rgx : R₃ → Fin T}
    (hrg : Function.Injective (Sum.elim rg rgx)) {p : Pr P T Q A U}
    {ρ ρ' : R₁ → List (Fin (A + 4))} {b : ℕ} (h : RsbRuns body rg ι p ρ ρ' b)
    (ξ : R₃ → List (Fin (A + 4))) :
    RsbRuns body (Sum.elim rg rgx) ι p (Sum.elim ρ ξ) (Sum.elim ρ' ξ) b :=
  rsb_lift hrg Sum.inl h _ _ (fun _ => rfl) (fun _ => rfl) (fun r hr => by
    cases r with
    | inl x => exact absurd rfl (hr x)
    | inr y => rfl)

end Lift

/-! ### The interchange -/

section Swap

variable {t₀ T Q K : ℕ} {U F R : Type} [DecidableEq R]

set_option maxHeartbeats 1000000 in
/-- **Interchange of two axes of the box.** Register `rl` holds the coefficient stream of `L`,
laid out as `[P] × [2^h] × [G] × [2^d]` records of `w` symbols; afterwards it holds the stream of
`swapList P (2^h) G (2^d) 1 0 L` (layout `[P] × [2^d] × [G] × [2^h]`); every other register is as
before. -/
theorem rsb_swap (body : F → Pr F T Q (prime + K) U) {rg : R → Fin T} {ι : Fin 64 → Fin T}
    (hrg : Function.Injective rg) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q) (rb : Fin (swapT t₀) → R)
    (hsw : Function.Injective fun j => rg (rb j)) (hT : swapT t₀ ≤ T) (rl rx : R)
    (hlx : rl ≠ rx) (hbl : ∀ j, rb j ≠ rl) (hbx : ∀ j, rb j ≠ rx)
    {P G h d w : ℕ} (hP : 0 < P) (hG : 0 < G) (hw : 0 < w)
    (hhd : h ≤ d + 1) (hdh : d ≤ h + 1) (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) = BinaryInterchangeRun.values P G (3 * w) h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hA : 4 ≤ prime + K)
    (ρ : R → List (Fin (prime + K + 4))) (L : List GaussianInt)
    (hL : L.length = P * 2 ^ h * G * 2 ^ d)
    (hln : ρ rl = cstream (prime + K) w L) (hxt0 : ρ rx = [])
    (hpay0 : ρ (rb (reg pay)) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → ρ (rb j) = [])
    (hhdr : ∀ k, ρ (rb (reg (hd k))) = separator :: (hs k).map bitSymbol)
    (hoth : ∀ i : Fin t₀, i ≠ pay → (∀ k, hd k ≠ i) → ρ (rb (reg i)) = []) :
    RsbRuns body rg ι (swapPass hd pay hi hQ (fun j => rg (rb j)) hsw hT (rg rl) (rg rx)) ρ
      (Function.update ρ rl (cstream (prime + K) w (swapList P (2 ^ h) G (2 ^ d) 1 0 L)))
      (rsbSwapCost T t₀ (BinaryInterchangeRun.cost P G (3 * w) h d hs)
        (∑ j, (ρ (rb j)).length) (L.length * w)) := by
  classical
  refine RsbRuns.of_raw fun v S hcl hS => ?_
  have hL0 : ∀ y, S.L y = [] := hcl.1
  set ιp : Fin (swapT t₀) → Fin T := fun j => rg (rb j) with hιp
  set str := rg rl with hstr_def
  set tmp := rg rx with htmp_def
  set M := L.length with hM
  set B' := 3 * w with hB'
  set ws := cstream (prime + K) w L with hws
  set ws' := cstream (prime + K) w (swapList P (2 ^ h) G (2 ^ d) 1 0 L) with hws'
  set pr := ιp (reg pay) with hpr
  have hst : str ≠ tmp := hrg.ne hlx
  have hstr : ∀ j, ιp j ≠ str := fun j => hrg.ne (hbl j)
  have htmp : ∀ j, ιp j ≠ tmp := fun j => hrg.ne (hbx j)
  have hpay_str : pr ≠ str := hstr _
  have hpay_tmp : pr ≠ tmp := htmp _
  have hR : S.R str = ws := by rw [hS rl]; exact hln
  have htmp0 : S.R tmp = [] := by rw [hS rx]; exact hxt0
  have hSι : ∀ j, S.R (ιp j) = ρ (rb j) := fun j => hS (rb j)
  -- lengths
  have hwlen : ws.length = M * w := by rw [hws, length_cstream]
  have hw'len : ws'.length = M * w := by
    rw [hws', length_cstream, rsb_length_swapList, hL]; ring
  have hvol : P * 2 ^ h * G * 2 ^ d * B' = M * (3 * w) := by rw [hL, hB']
  have hBpos : 0 < B' := by omega
  have hswap : swapList P (2 ^ h) G (2 ^ d) B' blank (toBits ws) = toBits ws' :=
    rsb_swapList_cstream_bits P (2 ^ h) G (2 ^ d) w L hL
  have h8' : ∀ s ∈ ws', s.val < 8 := rsb_cstream_lt_eight (by omega) _
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
  have hsum : ∑ j, (S₂.R (ιp j)).length ≤ ∑ j, (ρ (rb j)).length + 3 * (M * w) := by
    have hpt : ∀ j, (S₂.R (ιp j)).length ≤
        (ρ (rb j)).length + if j = reg pay then 3 * (M * w) else 0 := by
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
        ≤ ∑ j, ((ρ (rb j)).length + if j = reg pay then 3 * (M * w) else 0) :=
          Finset.sum_le_sum fun j _ => hpt j
      _ = ∑ j, (ρ (rb j)).length + 3 * (M * w) := by
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
    unfold rsbSwapCost
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
    by_cases hr : r = rl
    · subst hr; rw [hstr_def, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (hrg.ne hr), hS r, Function.update_of_ne hr]
  · intro k hk
    rw [Function.update_of_ne (fun h => hk rl h.symm)]

end Swap

end

end IntegerMultBounds.MathlibTM2.Fast
