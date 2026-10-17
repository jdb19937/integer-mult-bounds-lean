module

import IntegerMultBounds.MathlibTM2.Fast.ResampBSwap
public import IntegerMultBounds.MathlibTM2.Fast.ResampBBox
public import IntegerMultBounds.MathlibTM2.Fast.ResampBAxis
public import IntegerMultBounds.MathlibTM2.Fast.ResampBLine
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# `B̃₀` along every axis of the padded box: the generic driver

The machine runs on the registers `RsbR ⊕ RsbX t₀`: the registers of the line machine (`inl`)
and the interchange bank `sw j`, the bit spare `xt`, the axis counter `ax` with its spare `ax'`,
and the spares `e1`, `e2` of the header exchange (`inr`). The box register is `inl src`; it holds
the padded box stream (`rsbBox`), axis `0` most significant.

* `rsbLineAt H Q L p q`: the line `(p, ·, q)` of a list laid out as `[P] × [H] × [Q]`;
  `rsb_chunks_swap`, `rsb_chunks_inner`: the lines the machine feeds to the line map are lines
  of the box along the axis.
* `rsbStepAxG`: an axis program along an axis `i` other than the last: interchange it with the
  last axis, run the axis program, exchange the two width headers of the bank (`rsbXchgP`),
  interchange back, exchange the headers back (`rsb_stepAxG_runs`, cost `rsbStepAxCostG`).
* `rsbAllG prep`: `prep` loads the parameters of the last axis and the axis program runs along
  it; then for each other axis `prep` loads its parameters and `rsbStepAxG` runs.
  `rsb_allG_runs`, `rsb_allG_tensor`: with line maps related to numeric maps
  (`RsbLineRel`), the box register ends holding the padded stream of `tensorZR d t s A u`;
  cost `rsbAllCostG`.

The Neumann instance (`rsbAllP`, `rsb_all_tensor`, `rsbAllCost`) was removed with the Neumann
`B̃₀`; restore from `1cb2723b`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


noncomputable section

/-! ### Lines of a layout -/

section Lines

/-- The line `(p, ·, q)` of a list laid out as `[P] × [H] × [Q]`. -/
def rsbLineAt (H Q : ℕ) (L : List GaussianInt) (p q : ℕ) : List GaussianInt :=
  (List.range H).map fun h => L.getD ((p * H + h) * Q + q) 0

lemma length_rsbLineAt (H Q : ℕ) (L : List GaussianInt) (p q : ℕ) :
    (rsbLineAt H Q L p q).length = H := by simp [rsbLineAt]

/-- The chunks of the interchanged stream are the lines along the interchanged axis. -/
lemma rsb_chunks_swap (P H G D : ℕ) (L : List GaussianInt) (hL : L.length = P * H * G * D)
    {c : List GaussianInt} (hc : c ∈ rsbChunks H (P * D * G) (swapList P H G D 1 0 L)) :
    ∃ p < P, ∃ q < G * D, c = rsbLineAt H (G * D) L p q := by
  simp only [rsbChunks, List.mem_map, List.mem_range] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  have hl1 : L.length = P * H * G * D * 1 := by rw [hL, Nat.mul_one]
  have hlsw : (swapList P H G D 1 0 L).length = P * D * G * H := by
    rw [rsb_length_swapList]; ring
  have hG : 0 < G := by
    rcases Nat.eq_zero_or_pos G with h0 | h0
    · rw [h0, Nat.mul_zero] at hc'; omega
    · exact h0
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · rw [h0, Nat.mul_zero, Nat.zero_mul] at hc'; omega
    · exact h0
  have hDG : 0 < D * G := Nat.mul_pos hD hG
  set p := c' / (D * G) with hpdef
  set d := c' % (D * G) / G with hddef
  set g := c' % (D * G) % G with hgdef
  have hp : p < P := Nat.div_lt_of_lt_mul (by rw [show D * G * P = P * D * G by ring]; exact hc')
  have hd : d < D := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm G D]; exact Nat.mod_lt _ hDG)
  have hg : g < G := Nat.mod_lt _ hG
  have he : c' = (p * D + d) * G + g := by
    have h1 := Nat.div_add_mod c' (D * G)
    have h2 := Nat.div_add_mod (c' % (D * G)) G
    rw [← hpdef] at h1
    rw [← hddef, ← hgdef] at h2
    linarith
  have hcH : c' * H + H ≤ P * D * G * H := by
    have : c' + 1 ≤ P * D * G := hc'
    nlinarith
  refine ⟨p, hp, g * D + d, by nlinarith, ?_⟩
  apply List.ext_getElem
    (by simp only [List.length_take, List.length_drop, hlsw, length_rsbLineAt]; omega)
  intro x h₁ h₂
  have hx : x < H := by simpa [rsbLineAt] using h₂
  simp only [rsbLineAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  have e := swapList_getElem? 0 L hl1 hp hx hg hd (Nat.zero_lt_one)
  simp only [Nat.mul_one, Nat.add_zero] at e
  rw [List.getD_eq_getElem?_getD, show (p * H + x) * (G * D) + (g * D + d) =
    ((p * H + x) * G + g) * D + d by ring, ← e, ← he, List.getElem?_eq_getElem]
  rfl

/-- The chunks of a stream are its lines along the innermost axis. -/
lemma rsb_chunks_inner (P H : ℕ) (L : List GaussianInt) (hL : L.length = P * H)
    {c : List GaussianInt} (hc : c ∈ rsbChunks H P L) :
    ∃ p < P, ∃ q < 1, c = rsbLineAt H 1 L p q := by
  simp only [rsbChunks, List.mem_map, List.mem_range] at hc
  obtain ⟨p, hp, rfl⟩ := hc
  refine ⟨p, hp, 0, Nat.zero_lt_one, ?_⟩
  have hpH : p * H + H ≤ P * H := by
    have : p + 1 ≤ P := hp
    nlinarith
  apply List.ext_getElem
    (by simp only [List.length_take, List.length_drop, hL, length_rsbLineAt]; omega)
  intro x h₁ h₂
  have hx : x < H := by simpa [rsbLineAt] using h₂
  have hlt : p * H + x < L.length := by rw [hL]; nlinarith
  simp only [rsbLineAt, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop,
    Nat.mul_one, Nat.add_zero]
  rw [List.getD_eq_getElem _ _ hlt]

end Lines

/-! ### Extra registers, the bank, and the header exchange -/

/-- The registers of the all-axes stage beyond those of the line machine: the interchange bank,
the bit spare `xt`, the axis counter `ax` with its spare `ax'`, and the spares `e1`, `e2` of the
header exchange. -/
inductive RsbX (t₀ : ℕ) where
  | sw (j : Fin (swapT t₀))
  | xt | ax | ax' | e1 | e2
  | vx (j : Fin 12)
  deriving DecidableEq

section Bank

variable {t₀ A : ℕ}

/-- The bank with the five header registers `reg (hd k)` holding the counters `hs k`; every
other bank register empty. -/
def rsbBank (hd : Fin 5 → Fin t₀) (hs : Fin 5 → List Bool) (j : Fin (swapT t₀)) :
    List (Fin (A + 4)) :=
  if h : ∃ k, reg (hd k) = j then separator :: (hs (Classical.choose h)).map bitSymbol else []

lemma rsbBank_hd {hd : Fin 5 → Fin t₀} (hi : Function.Injective hd) (hs : Fin 5 → List Bool)
    (k : Fin 5) : (rsbBank hd hs (reg (hd k)) : List (Fin (A + 4))) =
      separator :: (hs k).map bitSymbol := by
  have h : ∃ k', reg (hd k') = reg (hd k) := ⟨k, rfl⟩
  rw [rsbBank, dite_eq_left h]
  have := Classical.choose_spec h
  rw [hi (BinaryInterchangeRun.slot_injective this)]

lemma rsbBank_other {hd : Fin 5 → Fin t₀} (hs : Fin 5 → List Bool) {j : Fin (swapT t₀)}
    (hj : ∀ k, reg (hd k) ≠ j) : (rsbBank hd hs j : List (Fin (A + 4))) = [] := by
  rw [rsbBank, dite_eq_right (fun ⟨k, hk⟩ => hj k hk)]

/-- Exchanging the last two headers. -/
lemma rsbBank_xchg {hd : Fin 5 → Fin t₀} (hi : Function.Injective hd) (hs : Fin 5 → List Bool) :
    Function.update (Function.update (rsbBank hd hs : Fin (swapT t₀) → List (Fin (A + 4)))
      (reg (hd 3)) (rsbBank hd hs (reg (hd 4)))) (reg (hd 4)) (rsbBank hd hs (reg (hd 3))) =
      rsbBank hd (fun k => hs (Equiv.swap 3 4 k)) := by
  funext j
  by_cases h4 : j = reg (hd 4)
  · subst h4
    rw [Function.update_self, rsbBank_hd hi, rsbBank_hd hi]
    simp [Equiv.swap_apply_right]
  · rw [Function.update_of_ne h4]
    by_cases h3 : j = reg (hd 3)
    · subst h3
      rw [Function.update_self, rsbBank_hd hi, rsbBank_hd hi]
      simp [Equiv.swap_apply_left]
    · rw [Function.update_of_ne h3]
      by_cases hk : ∃ k, reg (hd k) = j
      · obtain ⟨k, rfl⟩ := hk
        have k3 : k ≠ 3 := fun h => h3 (by rw [h])
        have k4 : k ≠ 4 := fun h => h4 (by rw [h])
        rw [rsbBank_hd hi, rsbBank_hd hi, Equiv.swap_apply_of_ne_of_ne k3 k4]
      · simp only [not_exists] at hk
        rw [rsbBank_other _ hk, rsbBank_other _ hk]

lemma rsb_values_swap34 (P G B h d : ℕ) (k : Fin 5) :
    BinaryInterchangeRun.values P G B h d (Equiv.swap 3 4 k) =
      BinaryInterchangeRun.values P G B d h k := by
  fin_cases k <;> rfl

end Bank

section Xchg

variable {T Q A : ℕ} {U P R : Type} [DecidableEq R] {body : P → Pr P T Q A U} {rg : R → Fin T}
  {ι : Fin 64 → Fin T}

/-- Exchange the contents of `a` and `b` through the empty spares `e₁`, `e₂`. -/
def rsbXchgP (rg : R → Fin T) (a b e₁ e₂ : R) : Pr P T Q A U :=
  .seq (moveR (rg a) (rg e₁) id) (.seq (moveR (rg b) (rg e₂) id)
    (.seq (moveR (rg e₂) (rg a) id) (moveR (rg e₁) (rg b) id)))

theorem rsb_xchg (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {a b e₁ e₂ : R}
    (hd : [a, b, e₁, e₂].Nodup) (ρ : R → List (Fin (A + 4))) (h₁ : ρ e₁ = []) (h₂ : ρ e₂ = []) :
    RsbRuns body rg ι (rsbXchgP rg a b e₁ e₂) ρ
      (Function.update (Function.update ρ a (ρ b)) b (ρ a))
      (4 * (ρ a).length + 4 * (ρ b).length + 8) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hab, hae₁, hae₂⟩, ⟨hbe₁, hbe₂⟩, he₁₂, -⟩ := hd
  have s1 := rsb_moveR_runs (body := body) (ι := ι) hrg hae₁ ρ
  have s2 := rsb_moveR_runs (body := body) (ι := ι) hrg hbe₂
    (Function.update (Function.update ρ a []) e₁ ((ρ a).reverse ++ ρ e₁))
  have s3 := rsb_moveR_runs (body := body) (ι := ι) hrg (Ne.symm hae₂)
    (Function.update (Function.update (Function.update (Function.update ρ a []) e₁
      ((ρ a).reverse ++ ρ e₁)) b []) e₂ ((Function.update (Function.update ρ a []) e₁
        ((ρ a).reverse ++ ρ e₁) b).reverse ++ Function.update (Function.update ρ a []) e₁
          ((ρ a).reverse ++ ρ e₁) e₂))
  refine ((s1.seq hdisj (s2.seq hdisj (s3.seq hdisj (rsb_moveR_runs (body := body) (ι := ι) hrg
    (Ne.symm hbe₁) _)))).congr ?_).mono ?_
  · funext r
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · simp [Ne.symm hab, hae₁, Ne.symm hae₂, Ne.symm hbe₁, he₁₂,
      Ne.symm he₁₂, Ne.symm hae₁, hab, hae₂, hbe₁, h₁, h₂]
    omega

end Xchg

/-! ### Layout of the axes -/

section Mid

/-- The product of the sizes of the axes strictly between `i` and the last axis. -/
def rsbMid {d : ℕ} (t : Fin d → ℕ) (i : ℕ) : ℕ := (((List.ofFn t).drop (i + 1)).dropLast).prod

lemma rsb_suf_last {d : ℕ} (t : Fin d → ℕ) (i : ℕ) (hi : i + 1 < d) :
    rsbSuf t i = rsbMid t i * t ⟨d - 1, by omega⟩ := by
  unfold rsbSuf rsbMid
  have hne : (List.ofFn t).drop (i + 1) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [List.prod_append, List.prod_singleton, List.getLast_drop, List.getLast_ofFn]

lemma rsb_suf_lastAxis {d : ℕ} (t : Fin d → ℕ) (i : Fin d) (hi : (i : ℕ) + 1 = d) :
    rsbSuf t i = 1 := by
  unfold rsbSuf
  rw [List.drop_eq_nil_of_le (by simp; omega)]
  rfl

end Mid

/-! ### The configuration of one axis -/

section Cfg

/-- The registers of the line machine configured for one axis: counters and scratch
(`RsbEnv`), the mask, the tables, the halving constant, the step count `K`, the padding counter;
`dst` and the other scratch registers empty. -/
structure RsbAxisCfg {A : ℕ} (ρ : RsbR → List (Fin (A + 4))) (w p s t m K : ℕ)
    (E : ZMod s → ℤ → ℤ) (D : ZMod s → ℤ) : Prop where
  env : RsbEnv ρ w p s m
  dst : ρ .dst = []
  msk : ρ .msk = (rsbMask s t).map bitSymbol
  ef : ρ .ef = cstream A w (rsbETab s m E)
  df : ρ .df = cstream A w (rsbArr fun ℓ => rsbReal (D ℓ))
  hf : ρ .hf = csyms A w (rsbReal (2 ^ (p - 1)))
  kn : (ρ .kn).length = K
  tswn : (ρ .tswn).length = (t - s) * w
  ms : ρ .ms = []
  sr : ρ .sr = []
  sel : ρ .sel = []
  hv : ρ .hv = []
  vk : ρ .vk = []
  dout : ρ .dout = []
  tK : ρ .tK = []

lemma RsbAxisCfg.with_src {A : ℕ} {ρ : RsbR → List (Fin (A + 4))} {w p s t m K : ℕ}
    {E : ZMod s → ℤ → ℤ} {D : ZMod s → ℤ} (h : RsbAxisCfg ρ w p s t m K E D)
    (l : List (Fin (A + 4))) : RsbAxisCfg (Function.update ρ .src l) w p s t m K E D :=
  ⟨h.env.update (by simp [RsbFreeReg]) l, by simp [h.dst], by simp [h.msk], by simp [h.ef],
    by simp [h.df], by simp [h.hf], by simp [h.kn], by simp [h.tswn], by simp [h.ms],
    by simp [h.sr], by simp [h.sel], by simp [h.hv], by simp [h.vk], by simp [h.dout],
    by simp [h.tK]⟩

variable {s t : ℕ} [NeZero s] [NeZero t]
variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {rg : RsbR → Fin T}
  {ι : Fin 64 → Fin T}

end Cfg

/-! ### One axis other than the last -/

section StepAx

variable {t₀ T Q K : ℕ} {U F : Type}

/-- `B̃₀` along a non-last axis with the axis program `ax`: interchange the axis with the last
axis, `ax` along the innermost axis, exchange the header registers of the two widths,
interchange back, exchange the headers back. -/
def rsbStepAxG (rg : RsbR → Fin T) (rgx : RsbX t₀ → Fin T) (ax : Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rgx (.sw j))
    (hTs : swapT t₀ ≤ T) : Pr F T Q (prime + K) U :=
  .seq (swapPass hd pay hi hQs (fun j => rgx (.sw j)) hsw hTs (rg .src) (rgx .xt))
  (.seq ax
  (.seq (rsbXchgP rgx (.sw (reg (hd 3))) (.sw (reg (hd 4))) .e1 .e2)
  (.seq (swapPass hd pay hi hQs (fun j => rgx (.sw j)) hsw hTs (rg .src) (rgx .xt))
    (rsbXchgP rgx (.sw (reg (hd 3))) (.sw (reg (hd 4))) .e1 .e2))))

/-- The step bound of `B̃₀` along a non-last axis of a box of `n` records: the two interchanges
(`c₁`, `c₂` interchange steps, `b₁`, `b₂` bank symbols), the `n / ti` lines, and the two header
exchanges (headers of `e` symbols). -/
def rsbStepAxCostG (T t₀ w a n c₁ c₂ b₁ b₂ e : ℕ) : ℕ :=
  rsbSwapCost T t₀ c₁ b₁ (n * w) + a + (4 * e + 8) + rsbSwapCost T t₀ c₂ b₂ (n * w) + (4 * e + 8)

variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

set_option maxHeartbeats 4000000 in
/-- **An axis program along a non-last axis `i`.** As `rsb_stepAx_runs`, for any axis program
`ax` computing the line map `g` on admissible lines (`Ok`) within `cax` steps.

**`B̃₀` along a non-last axis `i`.** The box register `src` holds the stream of `L` (the
box `∏ [0, t j)`); afterwards it holds the line map along axis `i`
(`rsbAxisL (rsbPre t i) (t i) (rsbSuf t i)`) of the line machine, and every other register is as
before. The line registers are configured for the axis (`RsbAxisCfg`), every line of `L` along
axis `i` is admissible (`RsbLineOk`), the spares are empty, and the bank holds the headers of the
interchange of axis `i` (width `2^Lb`) with the last axis (width `2^Ld`). -/
theorem rsb_stepAxG_runs (ax : Pr F T Q (prime + K) U) (hrg₂ : Function.Injective (Sum.elim rg rgx))
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) (hA : 96 ≤ prime + K) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQs : swapStates hd pay hi ≤ Q)
    (hsw : Function.Injective fun j => rgx (.sw j)) (hTs : swapT t₀ ≤ T) (hdpay : ∀ k, hd k ≠ pay)
    {d : ℕ} (t : Fin d → ℕ) (i : Fin d) (hi1 : (i : ℕ) + 1 < d)
    {w Lb Ld : ℕ} [NeZero (t i)] (hw : 1 ≤ w) (ht : t i = 2 ^ Lb)
    (htd : t ⟨d - 1, by omega⟩ = 2 ^ Ld) (hhd : Lb ≤ Ld + 1) (hdh : Ld ≤ Lb + 1)
    (g : List GaussianInt → List GaussianInt) (hglen : ∀ x, (g x).length = t i)
    (Ok : List GaussianInt → Prop) (cax : ℕ → ℕ)
    (hP : 0 < rsbPre t i) (hG : 0 < rsbMid t i) (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) =
      BinaryInterchangeRun.values (rsbPre t i) (rsbMid t i) (3 * w) Lb Ld k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k))
    (ρ : RsbR → List (Fin (prime + K + 4))) (ξ : RsbX t₀ → List (Fin (prime + K + 4)))
    (hax : ∀ lines : List (List GaussianInt), (∀ c ∈ lines, Ok c) →
      RsbRuns body rg ι ax (Function.update ρ .src (cstream (prime + K) w lines.flatten))
        (Function.update ρ .src (cstream (prime + K) w (lines.flatMap g))) (cax lines.length))
    (hbank : ∀ j, ξ (.sw j) = rsbBank hd hs j) (hxt : ξ .xt = []) (he1 : ξ .e1 = [])
    (he2 : ξ .e2 = []) (L : List GaussianInt) (hL : L.length = ∏ j, t j)
    (hsrc : ρ .src = cstream (prime + K) w L)
    (hok : ∀ p' < rsbPre t i, ∀ q < rsbSuf t i,
      Ok (rsbLineAt (t i) (rsbSuf t i) L p' q)) :
    RsbRuns body (Sum.elim rg rgx) ι (rsbStepAxG rg rgx ax hd pay hi hQs hsw hTs)
      (Sum.elim ρ ξ)
      (Sum.elim (Function.update ρ .src (cstream (prime + K) w
        (rsbAxisL (rsbPre t i) (t i) (rsbSuf t i) g L))) ξ)
      (rsbStepAxCostG T t₀ w (cax (L.length / t i)) L.length
        (BinaryInterchangeRun.cost (rsbPre t i) (rsbMid t i) (3 * w) Lb Ld hs)
        (BinaryInterchangeRun.cost (rsbPre t i) (rsbMid t i) (3 * w) Ld Lb
          (fun k => hs (Equiv.swap 3 4 k)))
        (∑ j, (rsbBank hd hs j : List (Fin (prime + K + 4))).length)
        (∑ j, (rsbBank hd (fun k => hs (Equiv.swap 3 4 k)) j :
          List (Fin (prime + K + 4))).length)
        ((hs 3).length + (hs 4).length + 2)) := by
  have hrg : Function.Injective rg := fun a b h => Sum.inl_injective (hrg₂ (a₁ := .inl a) h)
  have hrgx : Function.Injective rgx := fun a b h => Sum.inr_injective (hrg₂ (a₁ := .inr a) h)
  have hdisj : ∀ r j, rg r ≠ ι j := fun r j => hdisj₂ (.inl r) j
  set Pp := rsbPre t i with hPdef
  set G := rsbMid t i with hGdef
  have hH0 : 0 < t i := Nat.pos_of_ne_zero (NeZero.ne _)
  set H := t i with hHdef
  set Dl := t ⟨d - 1, by omega⟩ with hDdef
  have hsuf : rsbSuf t i = G * Dl := rsb_suf_last t i hi1
  have hL' : L.length = Pp * H * G * Dl := by
    rw [hL, ← rsbPre_mul t i, hsuf]; ring
  have hinj : Function.Injective fun k => reg (hd k) :=
    fun a b h => hi (BinaryInterchangeRun.slot_injective h)
  have hreg : ∀ k, reg (hd k) ≠ reg pay :=
    fun k h => hdpay k (BinaryInterchangeRun.slot_injective h)
  set hs' : Fin 5 → List Bool := fun k => hs (Equiv.swap 3 4 k) with hhs'
  -- 1. interchange axis `i` with the last axis
  set Lsw := swapList Pp (2 ^ Lb) G (2 ^ Ld) 1 0 L with hLsw
  have hbank_bad : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → ∀ hs₀ : Fin 5 → List Bool,
      (rsbBank hd hs₀ j : List (Fin (prime + K + 4))) = [] := by
    intro j hj hs₀
    rw [rsbBank_other]
    intro k hk
    have : (reg (hd k)).val < t₀ := by rw [reg_val]; exact (hd k).isLt
    rw [hk] at this; omega
  have h1 := rsb_swap body (R := RsbR ⊕ RsbX t₀) (ι := ι) (w := w) hrg₂ hd pay hi hQs
    (fun j => .inr (.sw j)) hsw hTs (.inl .src) (.inr .xt) (by simp) (by simp) (by simp)
    hP hG (by omega) hhd hdh hs hv hc (by omega) (Sum.elim ρ ξ) L
    (by rw [hL', ← ht, ← htd]) hsrc hxt
    (by simp only [Sum.elim_inr]; rw [hbank, rsbBank_other _ hreg])
    (fun j hj => by simp only [Sum.elim_inr]; rw [hbank]; exact hbank_bad j hj hs)
    (fun k => by simp only [Sum.elim_inr]; rw [hbank, rsbBank_hd hi])
    (fun i' _ hk => by
      simp only [Sum.elim_inr]
      rw [hbank, rsbBank_other]
      intro k h; exact hk k (BinaryInterchangeRun.slot_injective h))
  rw [Sum.update_elim_inl, ← hLsw] at h1
  -- 2. `B̃₀` along the innermost axis
  have hlsw : Lsw.length = Pp * Dl * G * H := by
    rw [hLsw, rsb_length_swapList, ← ht, ← htd]; ring
  set lines := rsbChunks H (Pp * Dl * G) Lsw with hlines
  have hlinesf : lines.flatten = Lsw := flatten_rsbChunks H (Pp * Dl * G) Lsw hlsw
  have hok' : ∀ c ∈ lines, Ok c := by
    intro c hc
    have hL'' : L.length = Pp * H * G * Dl := hL'
    rw [hlines, hLsw, ← ht, ← htd] at hc
    obtain ⟨p', hp', q, hq, rfl⟩ := rsb_chunks_swap Pp H G Dl L hL'' hc
    rw [← hsuf] at hq ⊢
    exact hok p' hp' q hq
  have h2 := rsb_lift_inl hrg₂ (hax lines hok') ξ
  rw [hlinesf] at h2
  -- 3. exchange the headers
  have hab : (RsbX.sw (reg (hd 3)) : RsbX t₀) ≠ RsbX.sw (reg (hd 4)) :=
    fun h => hinj.ne (show (3 : Fin 5) ≠ 4 by decide) (RsbX.sw.inj h)
  set ξ' := Function.update (Function.update ξ (.sw (reg (hd 3))) (ξ (.sw (reg (hd 4)))))
    (.sw (reg (hd 4))) (ξ (.sw (reg (hd 3)))) with hξ'
  have h3 := (rsb_xchg (body := body) (ι := ι) hrg₂ hdisj₂ (a := .inr (.sw (reg (hd 3))))
    (b := .inr (.sw (reg (hd 4)))) (e₁ := .inr .e1) (e₂ := .inr .e2)
    (by simp [hab]) (Sum.elim (Function.update ρ .src (cstream (prime + K) w
      (lines.flatMap g))) ξ) (by simp [he1]) (by simp [he2])).congr
    (show _ = Sum.elim (Function.update ρ .src (cstream (prime + K) w (lines.flatMap g))) ξ' by
      rw [Sum.update_elim_inr, Sum.update_elim_inr]; rfl)
  have hbank' : ∀ j, ξ' (.sw j) = rsbBank hd hs' j := by
    intro j
    rw [hhs', ← rsbBank_xchg hi hs]
    simp only [hξ', Function.update_apply, RsbX.sw.injEq]
    split_ifs <;> simp [hbank]
  have hξ'3 : ξ' (.sw (reg (hd 3))) = ξ (.sw (reg (hd 4))) := by
    rw [hξ', Function.update_of_ne hab, Function.update_self]
  have hξ'4 : ξ' (.sw (reg (hd 4))) = ξ (.sw (reg (hd 3))) := by
    rw [hξ', Function.update_self]
  -- 4. interchange back
  have hax : lines.flatMap g = rsbAxisL (Pp * Dl * G) H 1 g Lsw := by
    rw [rsbAxisL_inner (Pp * Dl * G) H g Lsw hlsw (fun x _ => hglen x)]
    rfl
  have hlax : (lines.flatMap g).length = Pp * 2 ^ Ld * G * 2 ^ Lb := by
    rw [hax, length_rsbAxisL, ← ht, ← htd]; ring
  have h4 := rsb_swap body (R := RsbR ⊕ RsbX t₀) (ι := ι) (w := w) hrg₂ hd pay hi hQs
    (fun j => .inr (.sw j)) hsw hTs (.inl .src) (.inr .xt) (by simp) (by simp) (by simp)
    hP hG (by omega) hdh hhd hs' (fun k => by rw [hhs', hv, rsb_values_swap34]) (fun k => hc _)
    (by omega) (Sum.elim (Function.update ρ .src (cstream (prime + K) w (lines.flatMap g))) ξ')
    (lines.flatMap g) hlax (by simp)
    (by simp [hξ', hxt])
    (by simp only [Sum.elim_inr]; rw [hbank', rsbBank_other _ hreg])
    (fun j hj => by simp only [Sum.elim_inr]; rw [hbank']; exact hbank_bad j hj hs')
    (fun k => by simp only [Sum.elim_inr]; rw [hbank', rsbBank_hd hi])
    (fun i' _ hk => by
      simp only [Sum.elim_inr]
      rw [hbank', rsbBank_other]
      intro k h; exact hk k (BinaryInterchangeRun.slot_injective h))
  have hsw_back : swapList Pp (2 ^ Ld) G (2 ^ Lb) 1 0 (lines.flatMap g) =
      rsbAxisL Pp H (rsbSuf t i) g L := by
    rw [hax, hLsw, ← ht, ← htd, rsbAxisL_swap Pp H G Dl g hglen L hL', hsuf]
  rw [Sum.update_elim_inl, Function.update_idem, hsw_back] at h4
  -- 5. exchange the headers back
  have h5 := (rsb_xchg (body := body) (ι := ι) hrg₂ hdisj₂ (a := .inr (.sw (reg (hd 3))))
    (b := .inr (.sw (reg (hd 4)))) (e₁ := .inr .e1) (e₂ := .inr .e2)
    (by simp [hab]) (Sum.elim (Function.update ρ .src (cstream (prime + K) w
      (rsbAxisL Pp H (rsbSuf t i) g L))) ξ') (by simp [hξ', he1]) (by simp [hξ', he2])).congr
    (show _ = Sum.elim (Function.update ρ .src (cstream (prime + K) w
      (rsbAxisL Pp H (rsbSuf t i) g L))) ξ by
      rw [Sum.update_elim_inr, Sum.update_elim_inr]
      congr 1
      funext x
      by_cases h4' : x = .sw (reg (hd 4))
      · rw [h4', Function.update_self]; simp [hξ'3]
      · rw [Function.update_of_ne h4']
        by_cases h3' : x = .sw (reg (hd 3))
        · rw [h3', Function.update_self]; simp [hξ'4]
        · rw [Function.update_of_ne h3']
          simp [hξ', Function.update_of_ne h4', Function.update_of_ne h3'])
  refine (RsbRuns.seq hdisj₂ h1 (RsbRuns.seq hdisj₂ h2 (RsbRuns.seq hdisj₂ h3
    (RsbRuns.seq hdisj₂ h4 h5)))).mono ?_
  have hnl : lines.length = L.length / H := by
    rw [hlines, rsbChunks, List.length_map, List.length_range, hL']
    rw [show Pp * H * G * Dl = (Pp * Dl * G) * H by ring, Nat.mul_div_cancel _ (by omega)]
  have hb1 : ∑ j, ((Sum.elim ρ ξ) (.inr (.sw j))).length =
      ∑ j, (rsbBank hd hs j : List (Fin (prime + K + 4))).length := by
    simp only [Sum.elim_inr, hbank]
  have hb2 : ∑ j, ((Sum.elim (Function.update ρ .src (cstream (prime + K) w (lines.flatMap g)))
      ξ') (.inr (.sw j))).length =
      ∑ j, (rsbBank hd hs' j : List (Fin (prime + K + 4))).length := by
    simp only [Sum.elim_inr, hbank']
  rw [hb1, hb2, hnl, hlax]
  simp only [Sum.elim_inr, hbank, hξ'3, hξ'4, rsbBank_hd hi, List.length_cons,
    List.length_map]
  unfold rsbStepAxCostG
  rw [show Pp * 2 ^ Ld * G * 2 ^ Lb = L.length by rw [hL', ← ht, ← htd]; ring]
  simp only [hhs']
  omega

end StepAx

/-! ### All axes -/

section All

variable {t₀ T Q K : ℕ} {U F : Type}

/-- The parameters of `B̃₀` on one axis: source length `s`, target length `2^Lb`, the integer
weight tables `E`, `D` (scale `2^p`), and the headers `hs` of the interchange with the last
axis. -/
structure RsbAxisData where
  s : ℕ
  Lb : ℕ
  E : ZMod s → ℤ → ℤ
  D : ZMod s → ℤ
  hs : Fin 5 → List Bool

/-- The integer line map of an axis with `t` target records, `K` Horner steps and window `m`. -/
def RsbAxisData.g (Dt : RsbAxisData) (p K m t : ℕ) : List GaussianInt → List GaussianInt :=
  rsbLineG Dt.s t p K m Dt.E Dt.D

/-- The register file `σ` with the box stream `l` and the axis counter `a`, spare `a'`. -/
def rsbWith {A : ℕ} (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (l a a' : List (Fin (A + 4))) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Sum.elim (Function.update (fun r => σ (.inl r)) .src l)
    (Function.update (Function.update (fun x => σ (.inr x)) .ax a) .ax' a')

lemma rsbWith_upd {A : ℕ} (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)))
    (l a a' b b' : List (Fin (A + 4))) :
    rsbUpd2 (rsbWith σ l a a') (.inr .ax) b (.inr .ax') b' = rsbWith σ l b b' := by
  simp only [rsbUpd2, rsbWith, Sum.update_elim_inr]
  congr 1
  funext x
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- The axis processed at step `k`: `d - 1 - k`. -/
def rsbAx {d : ℕ} (hd0 : 0 < d) (k : ℕ) : Fin d := ⟨d - 1 - k, by omega⟩

/-- An axis program along all axes: `prep` loads the parameters of the last axis and `ax`
runs along it; then for each other axis (the counter `ax` holds one symbol per axis) `prep`
loads its parameters and `rsbStepAxG` runs. -/
def rsbAllG (prep ax : Pr F T Q (prime + K) U) (rg : RsbR → Fin T) (rgx : RsbX t₀ → Fin T)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rgx (.sw j))
    (hTs : swapT t₀ ≤ T) : Pr F T Q (prime + K) U :=
  .seq prep (.seq ax
    (rsbRep (rgx .ax) (rgx .ax') (.seq prep (rsbStepAxG rg rgx ax hd pay hi hQs hsw hTs))))

/-- The step bound of an axis program along all axes of a box of `n` records; `cax i` bounds the
axis program on `n / t i` lines of axis `i`. -/
def rsbAllCostG (T t₀ w d : ℕ) (t : Fin d → ℕ) (hd0 : 0 < d) (Lb : Fin d → ℕ)
    (hs : Fin d → Fin 5 → List Bool) (cax : Fin d → ℕ → ℕ)
    (A : ℕ) (hd : Fin 5 → Fin t₀) (cp : ℕ → ℕ) (n : ℕ) : ℕ :=
  cp 0 + cax (rsbAx hd0 0) (n / t (rsbAx hd0 0)) +
  ((∑ j ∈ Finset.range (d - 1), (cp (j + 1) +
    rsbStepAxCostG T t₀ w (cax (rsbAx hd0 (j + 1)) (n / t (rsbAx hd0 (j + 1)))) n
      (BinaryInterchangeRun.cost (rsbPre t (rsbAx hd0 (j + 1)))
        (rsbMid t (rsbAx hd0 (j + 1))) (3 * w) (Lb (rsbAx hd0 (j + 1)))
        (Lb (rsbAx hd0 0)) (hs (rsbAx hd0 (j + 1))))
      (BinaryInterchangeRun.cost (rsbPre t (rsbAx hd0 (j + 1)))
        (rsbMid t (rsbAx hd0 (j + 1))) (3 * w) (Lb (rsbAx hd0 0))
        (Lb (rsbAx hd0 (j + 1)))
        (fun k => hs (rsbAx hd0 (j + 1)) (Equiv.swap 3 4 k)))
      (∑ i, (rsbBank hd (hs (rsbAx hd0 (j + 1))) i : List (Fin (A + 4))).length)
      (∑ i, (rsbBank hd (fun k => hs (rsbAx hd0 (j + 1)) (Equiv.swap 3 4 k)) i :
        List (Fin (A + 4))).length)
      ((hs (rsbAx hd0 (j + 1)) 3).length + (hs (rsbAx hd0 (j + 1)) 4).length + 2) +
      4)) + 2 * (d - 1) + 4)

end All

section AllProof

variable {t₀ T Q K : ℕ} {U F : Type}
variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

lemma rsb_prod_pos {l : List ℕ} (h : ∀ x ∈ l, 0 < x) : 0 < l.prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons]
    exact Nat.mul_pos (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

lemma rsb_pre_pos {d : ℕ} (t : Fin d → ℕ) (ht : ∀ i, 0 < t i) (i : ℕ) : 0 < rsbPre t i :=
  rsb_prod_pos fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hx)
    exact ht j

lemma rsb_mid_pos {d : ℕ} (t : Fin d → ℕ) (ht : ∀ i, 0 < t i) (i : ℕ) : 0 < rsbMid t i :=
  rsb_prod_pos fun x hx => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop (List.mem_of_mem_dropLast hx))
    exact ht j

set_option maxHeartbeats 4000000 in
/-- **An axis program along all axes of the padded box.** As `rsb_all_runs`, for any axis
program `ax` computing the line maps `g i` on admissible lines (`Ok i`) within `cax i` steps.

**`B̃₀` along all axes of the padded box.** The box register holds the stream `l₀` of the
padded box `∏_{i<d} [0, t_i)`; the axis counter `ax` holds `d - 1` symbols. `prep` takes the
register file `V₀` (resp. `cfg k`) to `cfg 0` (resp. `cfg (k + 1)`), whatever the box stream
and the axis counter, where `cfg k` is configured for the axis `rsbAx k = d - 1 - k` with the
parameters `Dt` (`RsbAxisCfg`; for `k > 0` the bank holding the headers of the interchange of the
axis with the last one, the spares empty). Every line along axis `i` of the box before axis `i`
is processed is admissible (`RsbLineOk`). Afterwards the box register holds the line maps along
the axes `d - 1, …, 0` of `l₀` (`rsbFlat d t g 0 l₀`, `g i` the line map of axis `i`), the
register file is `cfg (d - 1)` and the counter is restored. -/
theorem rsb_allG_runs (prep ax : Pr F T Q (prime + K) U)
    (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j)
    (hA : 96 ≤ prime + K)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rgx (.sw j))
    (hTs : swapT t₀ ≤ T) (hdpay : ∀ k, hd k ≠ pay)
    {d : ℕ} (hd0 : 0 < d) (t : Fin d → ℕ) {w : ℕ} (hw : 1 ≤ w)
    (Lb : Fin d → ℕ) (hs : Fin d → Fin 5 → List Bool)
    (g : Fin d → List GaussianInt → List GaussianInt) (hglen : ∀ i x, (g i x).length = t i)
    (Ok : Fin d → List GaussianInt → Prop) (cax : Fin d → ℕ → ℕ)
    (hDt : ∀ i, t i = 2 ^ Lb i)
    (hDw : ∀ i : Fin d, (i : ℕ) + 1 < d → Lb i ≤ Lb (rsbAx hd0 0) + 1 ∧
      Lb (rsbAx hd0 0) ≤ Lb i + 1 ∧
      (∀ k, Counter.value (hs i k) = BinaryInterchangeRun.values (rsbPre t i) (rsbMid t i)
        (3 * w) (Lb i) (Lb (rsbAx hd0 0)) k) ∧
      ∀ k, GrowingCounterData.Canonical (hs i k))
    (V₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (cfg : ℕ → RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (hcfg : ∀ k < d, (∀ lines : List (List GaussianInt), (∀ c ∈ lines, Ok (rsbAx hd0 k) c) →
        RsbRuns body rg ι ax
          (Function.update (fun r => cfg k (.inl r)) .src (cstream (prime + K) w lines.flatten))
          (Function.update (fun r => cfg k (.inl r)) .src
            (cstream (prime + K) w (lines.flatMap (g (rsbAx hd0 k)))))
          (cax (rsbAx hd0 k) lines.length)) ∧
      (0 < k → (∀ j, cfg k (.inr (.sw j)) = rsbBank hd (hs (rsbAx hd0 k)) j) ∧
        cfg k (.inr .xt) = [] ∧ cfg k (.inr .e1) = [] ∧ cfg k (.inr .e2) = []))
    (cp : ℕ → ℕ)
    (hprep₀ : ∀ l a a', RsbRuns body (Sum.elim rg rgx) ι prep (rsbWith V₀ l a a')
      (rsbWith (cfg 0) l a a') (cp 0))
    (hprep : ∀ k, k + 1 < d → ∀ l a a', RsbRuns body (Sum.elim rg rgx) ι prep
      (rsbWith (cfg k) l a a') (rsbWith (cfg (k + 1)) l a a') (cp (k + 1)))
    (l₀ : List GaussianInt) (hl₀ : l₀.length = ∏ i, t i)
    (hok : ∀ i : Fin d, ∀ p' < rsbPre t i, ∀ q < rsbSuf t i,
      Ok i (rsbLineAt (t i) (rsbSuf t i) (rsbFlat d t g (i + 1) l₀) p' q))
    (axs : List (Fin (prime + K + 4))) (haxs : axs.length = d - 1) :
    RsbRuns body (Sum.elim rg rgx) ι (rsbAllG prep ax rg rgx hd pay hi hQs hsw hTs)
      (rsbWith V₀ (cstream (prime + K) w l₀) axs [])
      (rsbWith (cfg (d - 1)) (cstream (prime + K) w
        (rsbFlat d t g 0 l₀)) axs [])
      (rsbAllCostG T t₀ w d t hd0 Lb hs cax (prime + K) hd cp l₀.length) := by
  set last := rsbAx hd0 0 with hlast
  have hlastv : (last : ℕ) = d - 1 := by simp [hlast, rsbAx]
  have hrg : Function.Injective rg := fun a b h => Sum.inl_injective (hrg₂ (a₁ := .inl a) h)
  have hdisj : ∀ r j, rg r ≠ ι j := fun r j => hdisj₂ (.inl r) j
  have htpos : ∀ i, 0 < t i := fun i => by rw [hDt i]; positivity
  have hlen_flat : ∀ k, (rsbFlat d t g k l₀).length = ∏ i, t i := by
    intro k
    rw [rsbFlat]
    induction ((List.finRange d).drop k) with
    | nil => exact hl₀
    | cons j js ih =>
        rw [List.foldr_cons, rsbAxisOp, length_rsbAxisL, rsbPre_mul]
  -- 1. load the parameters of the last axis
  have h1 := hprep₀ (cstream (prime + K) w l₀) axs []
  -- 2. `B̃₀` along the last axis
  have : NeZero (t last) := ⟨(htpos last).ne'⟩
  have hsuf : rsbSuf t last = 1 := rsb_suf_lastAxis t last (by omega)
  have hpre : rsbPre t last * t last = ∏ i, t i := by
    have := rsbPre_mul t last
    rw [hsuf, Nat.mul_one] at this; exact this
  set lines := rsbChunks (t last) (rsbPre t last) l₀ with hlines
  have hl₀' : l₀.length = rsbPre t last * t last := by rw [hl₀, hpre]
  have hok_last : ∀ c ∈ lines, Ok last c := by
    intro c hc
    obtain ⟨p', hp', q, hq, rfl⟩ := rsb_chunks_inner _ _ l₀ hl₀' hc
    have := hok last p' hp' q (by rw [hsuf]; exact hq)
    rw [hsuf, rsbFlat_ge d t g (by omega : d ≤ (last : ℕ) + 1)] at this
    exact this
  have hbox1 : rsbFlat d t g (d - 1) l₀ = lines.flatMap (g last) := by
    rw [rsbFlat_lt d t g (by omega : d - 1 < d), rsbFlat_ge d t g (by omega : d ≤ d - 1 + 1),
      rsbAxisOp]
    have e : (⟨d - 1, by omega⟩ : Fin d) = last := Fin.ext (by rw [hlastv])
    rw [e, hsuf, rsbAxisL_inner (rsbPre t last) (t last) (g last) l₀ hl₀'
      (fun x _ => hglen last x)]
    rfl
  have hfl : lines.flatten = l₀ := by rw [hlines, flatten_rsbChunks _ _ _ hl₀']
  have h2a := (hcfg 0 hd0).1 lines hok_last
  rw [hfl] at h2a
  have h2 := rsb_lift hrg₂ Sum.inl h2a (rsbWith (cfg 0) (cstream (prime + K) w l₀) axs [])
    (rsbWith (cfg 0) (cstream (prime + K) w (rsbFlat d t g (d - 1) l₀)) axs [])
    (fun x => rfl)
    (fun x => by simp only [rsbWith, Sum.elim_inl, hbox1]; rfl)
    (fun r hr => by
      cases r with
      | inl x => exact absurd rfl (hr x)
      | inr y => rfl)
  -- 3. the other axes
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)), Ψ = fun j =>
      rsbWith (cfg j) (cstream (prime + K) w (rsbFlat d t g (d - 1 - j) l₀)) [] [] := ⟨_, rfl⟩
  have hstep : ∀ j < axs.length, ∀ X Y, RsbRuns body (Sum.elim rg rgx) ι
      (.seq prep (rsbStepAxG rg rgx ax hd pay hi hQs hsw hTs))
      (rsbUpd2 (Ψ j) (.inr .ax) X (.inr .ax') Y) (rsbUpd2 (Ψ (j + 1)) (.inr .ax) X (.inr .ax') Y)
      (cp (j + 1) + rsbStepAxCostG T t₀ w
        (cax (rsbAx hd0 (j + 1)) (l₀.length / t (rsbAx hd0 (j + 1)))) l₀.length
        (BinaryInterchangeRun.cost (rsbPre t (rsbAx hd0 (j + 1)))
          (rsbMid t (rsbAx hd0 (j + 1))) (3 * w) (Lb (rsbAx hd0 (j + 1)))
          (Lb (rsbAx hd0 0)) (hs (rsbAx hd0 (j + 1))))
        (BinaryInterchangeRun.cost (rsbPre t (rsbAx hd0 (j + 1)))
          (rsbMid t (rsbAx hd0 (j + 1))) (3 * w) (Lb (rsbAx hd0 0))
          (Lb (rsbAx hd0 (j + 1)))
          (fun k => hs (rsbAx hd0 (j + 1)) (Equiv.swap 3 4 k)))
        (∑ i, (rsbBank hd (hs (rsbAx hd0 (j + 1))) i : List (Fin (prime + K + 4))).length)
        (∑ i, (rsbBank hd (fun k => hs (rsbAx hd0 (j + 1)) (Equiv.swap 3 4 k)) i :
          List (Fin (prime + K + 4))).length)
        ((hs (rsbAx hd0 (j + 1)) 3).length + (hs (rsbAx hd0 (j + 1)) 4).length + 2))
      := by
    intro j hj X Y
    rw [haxs] at hj
    set i := rsbAx hd0 (j + 1) with hidef
    have hiv : (i : ℕ) = d - 1 - (j + 1) := rfl
    have hi1 : (i : ℕ) + 1 < d := by rw [hiv]; omega
    have : NeZero (t i) := ⟨(htpos i).ne'⟩
    obtain ⟨hwl, hwr, hv, hc⟩ := hDw i hi1
    obtain ⟨hcfg1, hbank⟩ := hcfg (j + 1) (by omega)
    obtain ⟨hb, hxt, he1, he2⟩ := hbank (by omega)
    have hLd : t ⟨d - 1, by omega⟩ = 2 ^ Lb (rsbAx hd0 0) := by
      rw [← hDt (rsbAx hd0 0)]; congr 1
    have hpre' := hprep j (by omega) (cstream (prime + K) w (rsbFlat d t g (d - 1 - j) l₀)) X Y
    have hst := rsb_stepAxG_runs (body := body) ax hrg₂ hdisj₂ hA hd pay hi hQs hsw hTs hdpay
      t i hi1 hw (hDt i) hLd hwl hwr (g i) (hglen i) (Ok i) (cax i)
      (rsb_pre_pos t htpos i) (rsb_mid_pos t htpos i) (hs i) hv hc
      (Function.update (fun r => cfg (j + 1) (.inl r)) .src
        (cstream (prime + K) w (rsbFlat d t g (d - 1 - j) l₀)))
      (Function.update (Function.update (fun x => cfg (j + 1) (.inr x)) .ax X) .ax' Y)
      (fun lines hok' => by rw [Function.update_idem, Function.update_idem]; exact hcfg1 lines hok')
      (fun j' => by simp [hb, hidef]) (by simp [hxt]) (by simp [he1])
      (by simp [he2]) (rsbFlat d t g (d - 1 - j) l₀) (hlen_flat _) (by simp)
      (fun p' hp' q hq => by
        have h := hok i p' hp' q hq
        have hidx : (i : ℕ) + 1 = d - 1 - j := by rw [hiv]; omega
        simp only [hidx] at h
        exact h)
    have hnext : rsbAxisL (rsbPre t i) (t i) (rsbSuf t i) (g i) (rsbFlat d t g (d - 1 - j) l₀) =
        rsbFlat d t g (d - 1 - (j + 1)) l₀ := by
      rw [rsbFlat_lt d t g (by omega : d - 1 - (j + 1) < d),
        show d - 1 - (j + 1) + 1 = d - 1 - j by omega]
      rfl
    have hlenL : (rsbFlat d t g (d - 1 - j) l₀).length = l₀.length := by rw [hlen_flat, hl₀]
    rw [hlenL] at hst
    simp only [hΨ]
    rw [rsbWith_upd, rsbWith_upd]
    refine RsbRuns.seq hdisj₂ hpre' (hst.congr ?_)
    simp only [rsbWith]
    rw [Function.update_idem]
    congr 2
    exact congrArg _ hnext
  have h3 := rsb_rep_runs' (body := body) (ι := ι) hrg₂ hdisj₂ (ra := .inr .ax) (rt := .inr .ax')
    (by simp) (.seq prep (rsbStepAxG rg rgx ax hd pay hi hQs hsw hTs)) axs Ψ _ hstep
  rw [hΨ] at h3
  simp only [rsbWith_upd, Nat.sub_zero, haxs] at h3
  rw [show d - 1 - (d - 1) = 0 by omega] at h3
  refine (RsbRuns.seq hdisj₂ h1 (RsbRuns.seq hdisj₂ h2 h3)).mono ?_
  have hnl : lines.length = l₀.length / t last := by
    rw [hlines, rsbChunks, List.length_map, List.length_range, hl₀',
      Nat.mul_div_cancel _ (htpos last)]
  rw [hnl]
  unfold rsbAllCostG
  simp only [← hlast]
  omega

end AllProof

/-! ### The tensor semantics -/

section AllTensor

variable {t₀ T Q K : ℕ} {U F : Type}
variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

open IntegerMultBounds.NLogN in
/-- **An axis program along all axes, exactly.** The tensor semantics of `rsb_allG_runs` for line
maps related to numeric maps `A i` (`RsbLineRel`). -/
theorem rsb_allG_tensor (prep ax : Pr F T Q (prime + K) U)
    (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j)
    (hA : 96 ≤ prime + K)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rgx (.sw j))
    (hTs : swapT t₀ ≤ T) (hdpay : ∀ k, hd k ≠ pay)
    {d : ℕ} (hd0 : 0 < d) (t : Fin d → ℕ) {w : ℕ} (hw : 1 ≤ w)
    (Lb : Fin d → ℕ) (hs : Fin d → Fin 5 → List Bool)
    (g : Fin d → List GaussianInt → List GaussianInt) (hglen : ∀ i x, (g i x).length = t i)
    (Ok : Fin d → List GaussianInt → Prop) (cax : Fin d → ℕ → ℕ)
    (hDt : ∀ i, t i = 2 ^ Lb i)
    (hDw : ∀ i : Fin d, (i : ℕ) + 1 < d → Lb i ≤ Lb (rsbAx hd0 0) + 1 ∧
      Lb (rsbAx hd0 0) ≤ Lb i + 1 ∧
      (∀ k, Counter.value (hs i k) = BinaryInterchangeRun.values (rsbPre t i) (rsbMid t i)
        (3 * w) (Lb i) (Lb (rsbAx hd0 0)) k) ∧
      ∀ k, GrowingCounterData.Canonical (hs i k))
    (V₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (cfg : ℕ → RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (hcfg : ∀ k < d, (∀ lines : List (List GaussianInt), (∀ c ∈ lines, Ok (rsbAx hd0 k) c) →
        RsbRuns body rg ι ax
          (Function.update (fun r => cfg k (.inl r)) .src (cstream (prime + K) w lines.flatten))
          (Function.update (fun r => cfg k (.inl r)) .src
            (cstream (prime + K) w (lines.flatMap (g (rsbAx hd0 k)))))
          (cax (rsbAx hd0 k) lines.length)) ∧
      (0 < k → (∀ j, cfg k (.inr (.sw j)) = rsbBank hd (hs (rsbAx hd0 k)) j) ∧
        cfg k (.inr .xt) = [] ∧ cfg k (.inr .e1) = [] ∧ cfg k (.inr .e2) = []))
    (cp : ℕ → ℕ)
    (hprep₀ : ∀ l a a', RsbRuns body (Sum.elim rg rgx) ι prep (rsbWith V₀ l a a')
      (rsbWith (cfg 0) l a a') (cp 0))
    (hprep : ∀ k, k + 1 < d → ∀ l a a', RsbRuns body (Sum.elim rg rgx) ι prep
      (rsbWith (cfg k) l a a') (rsbWith (cfg (k + 1)) l a a') (cp (k + 1)))
    (s : Fin d → ℕ) [∀ i, NeZero (t i)] [∀ i, NeZero (s i)] (hst : ∀ i, s i ≤ t i)
    (A : (i : Fin d) → (ZMod (t i) → ℂ) → ZMod (s i) → ℂ) (q : ℕ)
    (hrel : ∀ i, RsbLineRel (t i) (s i) (A i) (g i) q)
    (u : ((i : Fin d) → ZMod (t i)) → ℂ) (Fn : ((i : Fin d) → Fin (t i)) → GaussianInt)
    (hF : ∀ x : (i : Fin d) → Fin (t i),
      u (fun i => ((x i : ℕ) : ZMod (t i))) = GaussianInt.toComplex (Fn x) / 2 ^ q)
    (hok : ∀ i : Fin d, ∀ p' < rsbPre t i, ∀ q' < rsbSuf t i,
      Ok i (rsbLineAt (t i) (rsbSuf t i) (rsbFlat d t g (i + 1) (rsbBox d t Fn)) p' q'))
    (axs : List (Fin (prime + K + 4))) (haxs : axs.length = d - 1) :
    ∃ G : ((i : Fin d) → Fin (t i)) → GaussianInt,
      (∀ x : (i : Fin d) → Fin (t i), (∀ i, (x i : ℕ) < s i) →
        tensorZR d t s A u (fun i => ((x i : ℕ) : ZMod (s i))) =
          GaussianInt.toComplex (G x) / 2 ^ q) ∧
      (∀ x : (i : Fin d) → Fin (t i), (∃ i, s i ≤ x i) → G x = 0) ∧
      RsbRuns body (Sum.elim rg rgx) ι (rsbAllG prep ax rg rgx hd pay hi hQs hsw hTs)
        (rsbWith V₀ (cstream (prime + K) w (rsbBox d t Fn)) axs [])
        (rsbWith (cfg (d - 1)) (cstream (prime + K) w (rsbBox d t G)) axs [])
        (rsbAllCostG T t₀ w d t hd0 Lb hs cax (prime + K) hd cp (∏ i, t i)) := by
  obtain ⟨G, hG1, hG2, hG3⟩ := rsb_tensor d t s hst A g q hrel u Fn hF
  have hl₀ : (rsbBox d t Fn).length = ∏ i, t i := length_rsbBox d t Fn
  have H := rsb_allG_runs (body := body) prep ax hrg₂ hdisj₂ hA hd pay hi hQs hsw hTs hdpay hd0 t
    hw Lb hs g hglen Ok cax hDt hDw V₀ cfg hcfg cp hprep₀ hprep (rsbBox d t Fn) hl₀ hok axs haxs
  rw [← rsbAxesL_flat d t _ _ hl₀, hG3, hl₀] at H
  exact ⟨G, hG1, hG2, H⟩

end AllTensor


end

end IntegerMultBounds.MathlibTM2.Fast
