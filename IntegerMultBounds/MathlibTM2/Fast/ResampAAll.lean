module

public import IntegerMultBounds.MathlibTM2.Fast.ResampASwap
public import IntegerMultBounds.MathlibTM2.Mult.Pipeline
public import IntegerMultBounds.MathlibTM2.Fast.ResampABox
public import IntegerMultBounds.MathlibTM2.Fast.ResampAAxis
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The numeric `Ã` along every axis of the padded box

The box register `ln` holds the stream `rsaBox d t F` of an array on the padded box
`∏_{i<d} [0, t_i)` (axis `0` most significant, `t_i = 2^{L_i}`), each value a coefficient of `w`
pair symbols. The stage applies the line machine along the axes `d - 1, d - 2, …, 0`, the order
of `tensorZR`:

* the last axis directly (`rsaAxisP`, its lines are contiguous);
* every other axis `i` with `rsaStepP`: interchange axis `i` with the last axis (`rsaSwapP` on
  the layout `[rsaPre t i] × [t_i] × [rsaMid t i] × [t_{d-1}]`), `rsaAxisP`, exchange the two
  width headers of the interchange bank (`rsaXchgP`), interchange back, exchange back
  (`rsa_step`, through `rsaAxisL_swap`).

`rsaAllP prep` runs `prep` before each axis: `prep` is the caller's parameter loader, which puts
the table, the counters, the shift `q` (the length of `pn`) and the interchange headers of the
next axis into the register file. Its contract is a hypothesis of `rsa_all`: it takes
`rsaWith (cfg k) l a a'` to `rsaWith (cfg (k + 1)) l a a'` for every box stream `l` and axis
counter `a`, `a'`. The loop over the axes is `scanP` on the counter `ax` (`d - 1` symbols).

**Registers.** `RsaR (RsaX t₀)`: the line-machine registers (`Fast/ResampALine`) and the extra
family `RsaX t₀`: the interchange bank `sw j`, `j : Fin (swapT t₀)`, holding the five headers
`rsaBank hd hs` (every other bank register empty), the bit spare `xt`, the axis counter `ax`
with spare `ax'`, and the exchange spares `e1`, `e2`. The alphabet is `Fin (prime + K + 4)` with
`96 ≤ prime + K`.

**Results.**
* `rsa_all`: the box register ends with `rsaFlat d t g 0 l₀`, the line maps `g i` along the
  axes `d - 1, …, 0` (`g i` the line machine of axis `i`), the register file `cfg (d - 1)`.
* `rsa_all_tensor`: if `l₀ = rsaBox d t F` is the padded stream of the numerators of `u` at
  scale `qi` and every `g i` gives the numerators of `A i` (`RsaLineRel`; scale `qi` into the
  last axis, `qo` into the others), the box register ends with `rsaBox d t G`, `G` the
  numerators of `tensorZR d s t A u` at scale `qo` (`rsa_tensor`, `rsaAxesL_flat`).
* `rsa_all_lineA`: the instance of the pipeline (`Mult/Pipeline`): `A = lineA n`, weights
  `tableA` on the windows (`rsaPipeData`), input scale `p n` (shift `p n` on the last axis),
  output scale `p n + 1` (shift `p n + 1` on the others): the box ends with the numerators of
  `tensorZR (d n) (s n) (t n) (lineA n) u`.

**Cost** (`rsaAllCost`): `prep` on every axis; `Ã` along the last axis (`rsaAxisCost`, at most
`T_box ((2m + 1)(rmulCost T w + 13 w + 17) + 60 w + 8 L + 80) + 4` by `rsaAxisCost_le`); for
each other axis `rsaStepCost`: two interchanges (`rsaSwapCost`, each at most
`3 C (T + 12 swapT t₀ + 5) T_box w max(1, L_i, L_{d-1})^τ + O(T_box w)` by `rsaSwapCost_le`),
the same `rsaAxisCost`, and two header exchanges of `O(L)` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ResampA

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


noncomputable section

/-- The extra registers of the stage: the interchange bank, the bit spare `xt`, the axis counter
`ax` with its spare `ax'`, and the spares `e1`, `e2` of the header exchange. -/
inductive RsaX (t₀ : ℕ) where
  | sw (j : Fin (swapT t₀))
  | xt | ax | ax' | e1 | e2
  deriving DecidableEq

lemma RsaX.sw_injective {t₀ : ℕ} : Function.Injective (RsaX.sw : Fin (swapT t₀) → RsaX t₀) :=
  fun _ _ h => RsaX.sw.inj h

/-! ### Lists -/

lemma rsa_fits_zero (w : ℕ) : Fits w 0 := by
  constructor <;> simp

lemma rsa_mem_swapList {α : Type} {P H G D B : ℕ} {dflt : α} {l : List α} {y : α}
    (hy : y ∈ swapList P H G D B dflt l) : y ∈ l ∨ y = dflt := by
  simp only [swapList, List.mem_map, List.mem_range] at hy
  obtain ⟨z, _, rfl⟩ := hy
  rw [List.getD_eq_getElem?_getD]
  cases h : l[swapSrc H G D B z]? with
  | none => right; rfl
  | some a => left; exact List.mem_of_getElem? h

lemma mem_rsaChunks {α : Type} {Q n : ℕ} {l : List α} {c : List α} (hc : c ∈ rsaChunks Q n l)
    {y : α} (hy : y ∈ c) : y ∈ l := by
  simp only [rsaChunks, List.mem_map, List.mem_range] at hc
  obtain ⟨k, _, rfl⟩ := hc
  exact List.mem_of_mem_drop (List.mem_of_mem_take hy)

lemma length_rsaChunks_mem {α : Type} {Q n : ℕ} {l : List α} (hl : l.length = n * Q)
    {c : List α} (hc : c ∈ rsaChunks Q n l) : c.length = Q := by
  simp only [rsaChunks, List.mem_map, List.mem_range] at hc
  obtain ⟨k, hk, rfl⟩ := hc
  simp only [List.length_take, List.length_drop, hl]
  have : (k + 1) * Q ≤ n * Q := Nat.mul_le_mul_right _ hk
  rw [Nat.succ_mul] at this
  omega

/-- The axes strictly between `i` and the last axis. -/
def rsaMid {d : ℕ} (t : Fin d → ℕ) (i : ℕ) : ℕ := (((List.ofFn t).drop (i + 1)).dropLast).prod

lemma rsaSuf_last {d : ℕ} (t : Fin d → ℕ) (i : ℕ) (hi : i + 1 < d) :
    rsaSuf t i = rsaMid t i * t ⟨d - 1, by omega⟩ := by
  unfold rsaSuf rsaMid
  have hne : (List.ofFn t).drop (i + 1) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  conv_lhs => rw [← List.dropLast_append_getLast hne]
  rw [List.prod_append, List.prod_singleton, List.getLast_drop, List.getLast_ofFn]

lemma rsaSuf_lastAxis {d : ℕ} (t : Fin d → ℕ) (i : Fin d) (hi : (i : ℕ) + 1 = d) :
    rsaSuf t i = 1 := by
  unfold rsaSuf
  rw [List.drop_eq_nil_of_le (by simp; omega)]
  rfl

/-! ### Exchanging two registers -/

section Xchg

variable {T Q A : ℕ} {U P R : Type} [DecidableEq R] {body : P → Pr P T Q A U} {rg : R → Fin T}
  {ι : Fin 64 → Fin T}

/-- Exchange the contents of `a` and `b` through the empty spares `e₁`, `e₂`. -/
def rsaXchgP (rg : R → Fin T) (a b e₁ e₂ : R) : Pr P T Q A U :=
  .seq (moveR (rg a) (rg e₁) id) (.seq (moveR (rg b) (rg e₂) id)
    (.seq (moveR (rg e₂) (rg a) id) (moveR (rg e₁) (rg b) id)))

theorem rsa_xchg (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {a b e₁ e₂ : R}
    (hd : [a, b, e₁, e₂].Nodup) (ρ : R → List (Fin (A + 4))) (h₁ : ρ e₁ = []) (h₂ : ρ e₂ = []) :
    RsaRuns body rg ι (rsaXchgP rg a b e₁ e₂) ρ
      (Function.update (Function.update ρ a (ρ b)) b (ρ a))
      (4 * (ρ a).length + 4 * (ρ b).length + 8) := by
  have hd' := hd
  regs_ne hd'
  have s1 := rsa_moveR (body := body) (ι := ι) hrg ‹a ≠ e₁› ρ
  have s2 := rsa_moveR (body := body) (ι := ι) hrg ‹b ≠ e₂›
    (Function.update (Function.update ρ a []) e₁ ((ρ a).reverse ++ ρ e₁))
  have s3 := rsa_moveR (body := body) (ι := ι) hrg (Ne.symm ‹a ≠ e₂›)
    (Function.update (Function.update (Function.update (Function.update ρ a []) e₁
      ((ρ a).reverse ++ ρ e₁)) b []) e₂ ((Function.update (Function.update ρ a []) e₁
        ((ρ a).reverse ++ ρ e₁) b).reverse ++ Function.update (Function.update ρ a []) e₁
          ((ρ a).reverse ++ ρ e₁) e₂))
  refine ((s1.seq hdisj (s2.seq hdisj (s3.seq hdisj (rsa_moveR (body := body) (ι := ι) hrg
    (Ne.symm ‹b ≠ e₁›) _)))).congr ?_).mono ?_
  · funext r
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
    omega

end Xchg

/-! ### The interchange bank -/

section Bank

variable {t₀ A : ℕ}

/-- The bank with the five header registers `reg (hd k)` holding the counters `hs k`; every
other bank register empty. -/
def rsaBank (hd : Fin 5 → Fin t₀) (hs : Fin 5 → List Bool) (j : Fin (swapT t₀)) :
    List (Fin (A + 4)) :=
  if h : ∃ k, reg (hd k) = j then separator :: (hs (Classical.choose h)).map bitSymbol else []

lemma rsaBank_hd {hd : Fin 5 → Fin t₀} (hi : Function.Injective hd) (hs : Fin 5 → List Bool)
    (k : Fin 5) : (rsaBank hd hs (reg (hd k)) : List (Fin (A + 4))) =
      separator :: (hs k).map bitSymbol := by
  have h : ∃ k', reg (hd k') = reg (hd k) := ⟨k, rfl⟩
  rw [rsaBank, dite_eq_left h]
  have := Classical.choose_spec h
  rw [hi (BinaryInterchangeRun.slot_injective this)]

lemma rsaBank_other {hd : Fin 5 → Fin t₀} (hs : Fin 5 → List Bool) {j : Fin (swapT t₀)}
    (hj : ∀ k, reg (hd k) ≠ j) : (rsaBank hd hs j : List (Fin (A + 4))) = [] := by
  rw [rsaBank, dite_eq_right (fun ⟨k, hk⟩ => hj k hk)]

/-- Exchanging the last two headers. -/
lemma rsaBank_xchg {hd : Fin 5 → Fin t₀} (hi : Function.Injective hd) (hs : Fin 5 → List Bool) :
    Function.update (Function.update (rsaBank hd hs : Fin (swapT t₀) → List (Fin (A + 4)))
      (reg (hd 3)) (rsaBank hd hs (reg (hd 4)))) (reg (hd 4)) (rsaBank hd hs (reg (hd 3))) =
      rsaBank hd (fun k => hs (Equiv.swap 3 4 k)) := by
  have hinj : Function.Injective fun k => reg (hd k) :=
    fun a b h => hi (BinaryInterchangeRun.slot_injective h)
  funext j
  by_cases h4 : j = reg (hd 4)
  · subst h4
    rw [Function.update_self, rsaBank_hd hi, rsaBank_hd hi]
    simp [Equiv.swap_apply_right]
  · rw [Function.update_of_ne h4]
    by_cases h3 : j = reg (hd 3)
    · subst h3
      rw [Function.update_self, rsaBank_hd hi, rsaBank_hd hi]
      simp [Equiv.swap_apply_left]
    · rw [Function.update_of_ne h3]
      by_cases hk : ∃ k, reg (hd k) = j
      · obtain ⟨k, rfl⟩ := hk
        have k3 : k ≠ 3 := fun h => h3 (by rw [h])
        have k4 : k ≠ 4 := fun h => h4 (by rw [h])
        rw [rsaBank_hd hi, rsaBank_hd hi, Equiv.swap_apply_of_ne_of_ne k3 k4]
      · push Not at hk
        rw [rsaBank_other _ hk, rsaBank_other _ hk]

end Bank

/-! ### One axis other than the last -/

section Step

variable {t₀ T Q K : ℕ} {U F : Type}

/-- `Ã` along a non-last axis: interchange it with the last axis, `Ã` along the innermost axis,
exchange the header registers of the two widths, interchange back, exchange the headers back. -/
def rsaStepP (rg : RsaR (RsaX t₀) → Fin T) (ι : Fin 64 → Fin T) (hι : Function.Injective ι)
    (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQs : swapStates hd pay hi ≤ Q)
    (hsw : Function.Injective fun j => rg (.x (.sw j))) (hTs : swapT t₀ ≤ T) :
    Pr F T Q (prime + K) U :=
  .seq (rsaSwapP rg hd pay hi hQs RsaX.sw hsw hTs .xt)
  (.seq (rsaAxisP rg ι hι hT hQ)
  (.seq (rsaXchgP rg (.x (.sw (reg (hd 3)))) (.x (.sw (reg (hd 4)))) (.x .e1) (.x .e2))
  (.seq (rsaSwapP rg hd pay hi hQs RsaX.sw hsw hTs .xt)
    (rsaXchgP rg (.x (.sw (reg (hd 3)))) (.x (.sw (reg (hd 4)))) (.x .e1) (.x .e2)))))

/-- The step bound of `Ã` along a non-last axis `i` of a box of `n` records: the two
interchanges (`c₁`, `c₂` interchange steps, `b₁`, `b₂` bank symbols), the lines
(`n / t_i` of them), and the two header exchanges (headers `e` symbols). -/
def rsaStepCost (T t₀ w s ti m L n c₁ c₂ b₁ b₂ e : ℕ) : ℕ :=
  rsaSwapCost T t₀ c₁ b₁ (n * w) + rsaAxisCost T w s ti m L (n / ti) + (4 * e + 8) +
    rsaSwapCost T t₀ c₂ b₂ (n * w) + (4 * e + 8)

lemma rsa_values_swap34 (P G B h d : ℕ) (k : Fin 5) :
    BinaryInterchangeRun.values P G B h d (Equiv.swap 3 4 k) =
      BinaryInterchangeRun.values P G B d h k := by
  fin_cases k <;> rfl

variable {body : F → Pr F T Q (prime + K) U}
  {rg : RsaR (RsaX t₀) → Fin T} {ι : Fin 64 → Fin T}

set_option maxHeartbeats 2000000 in
/-- **`Ã` along a non-last axis `i`.** The box register holds the stream of `L` (all records
fitting `w` bits); afterwards it holds the line map along axis `i`
(`rsaAxisL (rsaPre t i) (t i) (rsaSuf t i)`) of the line machine with shift `q`, and every
other register is as before. The register file is idle for the axis (`RsaIdle`), `ob` and the
spares are empty, and the bank holds the headers of the interchange of axis `i` (width `2^Lb`)
with the last axis (width `2^Ld`). -/
theorem rsa_step (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ prime + K)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rg (.x (.sw j)))
    (hTs : swapT t₀ ≤ T) (hdpay : ∀ k, hd k ≠ pay) {d : ℕ} (t : Fin d → ℕ) (i : Fin d)
    (hi1 : (i : ℕ) + 1 < d) {w q Lb Ld s m : ℕ} (hw : 1 ≤ w) (hq : q ≤ w)
    {wt : ℕ → ℕ → GaussianInt} (ht : t i = 2 ^ Lb) (htd : t ⟨d - 1, by omega⟩ = 2 ^ Ld)
    (hhd : Lb ≤ Ld + 1) (hdh : Ld ≤ Lb + 1) (hst : s < t i) (hms : m ≤ s) (hs0 : 0 < s)
    (hFT : ∀ y ∈ rsaTabL (t i) (2 * m + 1) wt, Fits w y ∧ y.im = 0)
    (hP : 0 < rsaPre t i) (hG : 0 < rsaMid t i) (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) =
      BinaryInterchangeRun.values (rsaPre t i) (rsaMid t i) (3 * w) Lb Ld k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (V : RsaV (RsaX t₀) (prime + K))
    (hI : RsaIdle V w q Lb s (t i) m wt) (hob : V.ob = [])
    (hbank : ∀ j, V.xr (.sw j) = rsaBank hd hs j) (hxt : V.xr .xt = [])
    (he1 : V.xr .e1 = []) (he2 : V.xr .e2 = []) (L : List GaussianInt)
    (hL : L.length = ∏ j, t j) (hFL : ∀ x ∈ L, Fits w x)
    (hln : V.ln = cstream (prime + K) w L) :
    RsaRuns body rg ι (rsaStepP rg ι hι hT hQ hd pay hi hQs hsw hTs) V.get
      { V with
        ln := cstream (prime + K) w
          (rsaAxisL (rsaPre t i) (t i) (rsaSuf t i) (rsaLineMap q s (t i) m wt) L) }.get
      (rsaStepCost T t₀ w s (t i) m Lb L.length
        (BinaryInterchangeRun.cost (rsaPre t i) (rsaMid t i) (3 * w) Lb Ld hs)
        (BinaryInterchangeRun.cost (rsaPre t i) (rsaMid t i) (3 * w) Ld Lb
          (fun k => hs (Equiv.swap 3 4 k)))
        (∑ j, (rsaBank hd hs j : List (Fin (prime + K + 4))).length)
        (∑ j, (rsaBank hd (fun k => hs (Equiv.swap 3 4 k)) j :
          List (Fin (prime + K + 4))).length)
        ((hs 3).length + (hs 4).length + 2)) := by
  set P := rsaPre t i with hPdef
  set G := rsaMid t i with hGdef
  set H := t i with hHdef
  set D := t ⟨d - 1, by omega⟩ with hDdef
  set g := rsaLineMap q s H m wt with hg
  have hsuf : rsaSuf t i = G * D := rsaSuf_last t i hi1
  have hL' : L.length = P * H * G * D := by
    rw [hL, ← rsaPre_mul t i, hsuf]; ring
  have hinj : Function.Injective fun k => reg (hd k) :=
    fun a b h => hi (BinaryInterchangeRun.slot_injective h)
  have hreg : ∀ k, reg (hd k) ≠ reg pay := fun k h => hdpay k (BinaryInterchangeRun.slot_injective h)
  set hs' : Fin 5 → List Bool := fun k => hs (Equiv.swap 3 4 k) with hhs'
  -- 1. interchange axis `i` with the last axis
  set Lsw := swapList P (2 ^ Lb) G (2 ^ Ld) 1 0 L with hLsw
  set V₁ : RsaV (RsaX t₀) (prime + K) := { V with ln := cstream (prime + K) w Lsw } with hV₁
  have h1 := rsa_swap body (ι := ι) hrg hd pay hi hQs RsaX.sw hsw hTs .xt (by simp) hP hG
    (by omega) hhd hdh hs hv hc (by omega) V L (by rw [hL', ← ht, ← htd]) hln hxt
    (by rw [hbank, rsaBank_other _ hreg]) (fun j hj => by
      rw [hbank, rsaBank_other]
      intro k hk
      have : (reg (hd k)).val < t₀ := by rw [reg_val]; exact (hd k).isLt
      rw [hk] at this; omega)
    (fun k => by rw [hbank, rsaBank_hd hi])
    (fun i' _ hk => by
      rw [hbank, rsaBank_other]
      intro k h; exact hk k (BinaryInterchangeRun.slot_injective h))
  -- 2. `Ã` along the innermost axis
  have hlsw : Lsw.length = P * D * G * H := by
    rw [hLsw, rsa_length_swapList, ← ht, ← htd]; ring
  set lines := rsaChunks H (P * D * G) Lsw with hlines
  have hlinesf : lines.flatten = Lsw := flatten_rsaChunks H (P * D * G) Lsw hlsw
  have hFsw : ∀ x ∈ Lsw, Fits w x := by
    intro x hx
    rcases rsa_mem_swapList hx with h | h
    · exact hFL x h
    · rw [h]; exact rsa_fits_zero w
  set V₂ : RsaV (RsaX t₀) (prime + K) := { V with ln := cstream (prime + K) w (lines.flatMap g) }
    with hV₂
  have h2 : RsaRuns body rg ι (rsaAxisP rg ι hι hT hQ) V₁.get V₂.get
      (rsaAxisCost T w s H m Lb lines.length) :=
    rsa_axis hrg hdisj hι hT hQ hA hw hq V₁ (hI.with_ln_ob _ V.ob) ht hst hms hs0 hFT lines
      (fun l hl => length_rsaChunks_mem hlsw hl)
      (fun l hl x hx => hFsw x (mem_rsaChunks hl (List.mem_of_mem_take hx)))
      (by rw [hV₁, hlinesf]) hob
  -- 3. exchange the headers
  set xr' := Function.update (Function.update V.xr (.sw (reg (hd 3))) (V.xr (.sw (reg (hd 4)))))
    (.sw (reg (hd 4))) (V.xr (.sw (reg (hd 3)))) with hxr'
  set V₃ : RsaV (RsaX t₀) (prime + K) := { V₂ with xr := xr' } with hV₃
  have h3 : RsaRuns body rg ι
      (rsaXchgP rg (.x (.sw (reg (hd 3)))) (.x (.sw (reg (hd 4)))) (.x .e1) (.x .e2))
      V₂.get V₃.get (4 * ((hs 3).length + (hs 4).length + 2) + 8) :=
    ((rsa_xchg (body := body) (ι := ι) hrg hdisj (a := .x (.sw (reg (hd 3))))
      (b := .x (.sw (reg (hd 4)))) (e₁ := .x .e1) (e₂ := .x .e2)
      (by simp [hinj.ne (show (3 : Fin 5) ≠ 4 by decide)]) V₂.get (by simp [hV₂, he1])
      (by simp [hV₂, he2])).congr (by
        rw [RsaV.upd_x, RsaV.upd_x]
        simp [hV₃, hV₂, hxr'])).mono (by
        simp only [hV₂, RsaV.get_x, hbank, rsaBank_hd hi, List.length_cons, List.length_map]
        omega)
  have hbank' : ∀ j, xr' (.sw j) = rsaBank hd hs' j := by
    intro j
    rw [← rsaBank_xchg hi hs]
    simp only [hxr', Function.update_apply, RsaX.sw.injEq]
    split_ifs <;> simp [hbank]
  have hab : (RsaX.sw (reg (hd 3)) : RsaX t₀) ≠ RsaX.sw (reg (hd 4)) :=
    fun h => hinj.ne (show (3 : Fin 5) ≠ 4 by decide) (RsaX.sw.inj h)
  have hxr'3 : xr' (.sw (reg (hd 3))) = V.xr (.sw (reg (hd 4))) := by
    rw [hxr', Function.update_of_ne hab, Function.update_self]
  have hxr'4 : xr' (.sw (reg (hd 4))) = V.xr (.sw (reg (hd 3))) := by
    rw [hxr', Function.update_self]
  -- 4. interchange back
  have hax : lines.flatMap g = rsaAxisL (P * D * G) H 1 g Lsw := by
    rw [rsaAxisL_inner (P * D * G) H g Lsw hlsw (fun x _ => length_rsaLineMap _ _ _ _ _ _)]
    rfl
  have hlax : (lines.flatMap g).length = P * 2 ^ Ld * G * 2 ^ Lb := by
    rw [hax, length_rsaAxisL, ← ht, ← htd]; ring
  set V₄ : RsaV (RsaX t₀) (prime + K) := { V₃ with
    ln := cstream (prime + K) w (rsaAxisL P H (rsaSuf t i) g L) } with hV₄
  have h4 : RsaRuns body rg ι (rsaSwapP rg hd pay hi hQs RsaX.sw hsw hTs .xt) V₃.get V₄.get
      (rsaSwapCost T t₀ (BinaryInterchangeRun.cost P G (3 * w) Ld Lb hs')
        (∑ j, (rsaBank hd hs' j : List (Fin (prime + K + 4))).length) (L.length * w)) := by
    have h := rsa_swap body (ι := ι) hrg hd pay hi hQs RsaX.sw hsw hTs .xt (by simp) hP hG
      (by omega) hdh hhd hs' (fun k => by rw [hhs', hv, rsa_values_swap34]) (fun k => hc _)
      (by omega) V₃ (lines.flatMap g) hlax rfl (by simp [hV₃, hxr', hxt])
      (by rw [show V₃.xr = xr' from rfl, hbank', rsaBank_other _ hreg]) (fun j hj => by
        rw [show V₃.xr = xr' from rfl, hbank', rsaBank_other]
        intro k hk
        have : (reg (hd k)).val < t₀ := by rw [reg_val]; exact (hd k).isLt
        rw [hk] at this; omega)
      (fun k => by rw [show V₃.xr = xr' from rfl, hbank', rsaBank_hd hi])
      (fun i' _ hk => by
        rw [show V₃.xr = xr' from rfl, hbank', rsaBank_other]
        intro k h; exact hk k (BinaryInterchangeRun.slot_injective h))
    have hbs : ∑ j, (V₃.xr (.sw j)).length =
        ∑ j, (rsaBank hd hs' j : List (Fin (prime + K + 4))).length := by
      simp only [show V₃.xr = xr' from rfl, hbank']
    rw [hbs, hlax] at h
    refine (h.congr ?_).mono ?_
    · congr 1
      simp only [hV₄, hV₃]
      congr 2
      rw [hax, hLsw, ← ht, ← htd, rsaAxisL_swap P H G D g (fun x => length_rsaLineMap _ _ _ _ _ _)
        L hL', hsuf]
    · unfold rsaSwapCost
      rw [show P * 2 ^ Ld * G * 2 ^ Lb = L.length by rw [hL', ← ht, ← htd]; ring]
  -- 5. exchange the headers back
  have h5 : RsaRuns body rg ι
      (rsaXchgP rg (.x (.sw (reg (hd 3)))) (.x (.sw (reg (hd 4)))) (.x .e1) (.x .e2))
      V₄.get { V with
        ln := cstream (prime + K) w (rsaAxisL P H (rsaSuf t i) g L) }.get
      (4 * ((hs 3).length + (hs 4).length + 2) + 8) :=
    ((rsa_xchg (body := body) (ι := ι) hrg hdisj (a := .x (.sw (reg (hd 3))))
      (b := .x (.sw (reg (hd 4)))) (e₁ := .x .e1) (e₂ := .x .e2)
      (by simp [hinj.ne (show (3 : Fin 5) ≠ 4 by decide)]) V₄.get (by simp [hV₄, hV₃, hxr', he1])
      (by simp [hV₄, hV₃, hxr', he2])).congr (by
        rw [RsaV.upd_x, RsaV.upd_x]
        congr 1
        simp only [hV₄, hV₃, hV₂]
        congr 1
        funext x
        simp only [RsaV.get_x]
        by_cases h4 : x = .sw (reg (hd 4))
        · rw [h4, Function.update_self, hxr'3]
        · rw [Function.update_of_ne h4]
          by_cases h3 : x = .sw (reg (hd 3))
          · rw [h3, Function.update_self, hxr'4]
          · rw [Function.update_of_ne h3, hxr', Function.update_of_ne h4,
              Function.update_of_ne h3])).mono (by
        simp only [hV₄, hV₃, RsaV.get_x, hxr'3, hxr'4, hbank, rsaBank_hd hi, List.length_cons,
          List.length_map]
        omega)
  have hb1 : ∑ j, (V.xr (.sw j)).length = ∑ j, (rsaBank hd hs j : List (Fin (prime + K + 4))).length := by
    simp only [hbank]
  rw [hb1] at h1
  refine ((h1.seq hdisj (h2.seq hdisj (h3.seq hdisj (h4.seq hdisj h5)))).congr ?_).mono ?_
  · rfl
  · have hnl : lines.length = L.length / H := by
      rw [hlines, rsaChunks, List.length_map, List.length_range, hL']
      rw [show P * H * G * D = (P * D * G) * H by ring, Nat.mul_div_cancel _ (by omega)]
    rw [hnl]
    unfold rsaStepCost
    simp only [hhs']
    omega

end Step

/-! ### All axes -/

section All

variable {t₀ T Q K : ℕ} {U F : Type}

/-- The parameters of `Ã` on one axis: source length `s`, target length `2^Lb`, product shift
`q`, weights `wt`, and the headers `hs` of the interchange with the last axis. -/
structure RsaAxisData where
  s : ℕ
  Lb : ℕ
  q : ℕ
  wt : ℕ → ℕ → GaussianInt
  hs : Fin 5 → List Bool

/-- The integer line map of an axis. -/
def RsaAxisData.g (D : RsaAxisData) (m t : ℕ) : List GaussianInt → List GaussianInt :=
  rsaLineMap D.q D.s t m D.wt

/-- The register file `V` with the box stream `l` and the axis counter `a`, spare `a'`. -/
def rsaWith {A : ℕ} (V : RsaV (RsaX t₀) A) (l a a' : List (Fin (A + 4))) : RsaV (RsaX t₀) A :=
  { V with ln := l, xr := Function.update (Function.update V.xr .ax a) .ax' a' }

lemma RsaIdle.with_ln_xr {X : Type} {A : ℕ} {V : RsaV X A} {w q L s t m : ℕ}
    {wt : ℕ → ℕ → GaussianInt} (h : RsaIdle V w q L s t m wt) (l : List (Fin (A + 4)))
    (f : X → List (Fin (A + 4))) : RsaIdle { V with ln := l, xr := f } w q L s t m wt :=
  ⟨h.ready, h.xs, h.xsv, h.ys, h.ysv, h.acc, h.ea, h.eb, h.er, h.ka, h.kb, h.kx, h.kW, h.kT,
    h.atm, h.sm, h.pz, h.sm2, h.bxa, h.bya, h.bza, h.cS, h.cM, h.cP, h.cW, h.cT, h.rr, h.bS⟩

lemma rsaWith_upd {A : ℕ} (V : RsaV (RsaX t₀) A)
    (l a a' b b' : List (Fin (A + 4))) :
    Function.update (Function.update (rsaWith V l a a').get (.x .ax) b) (.x .ax') b' =
      (rsaWith V l b b').get := by
  rw [RsaV.upd_x, RsaV.upd_x]
  congr 1
  simp only [rsaWith]
  congr 1
  funext x
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- `Ã` along all axes: `prep` loads the parameters of the last axis and `Ã` runs along it; then
for each other axis (the counter `ax` holds one symbol per axis) `prep` loads its parameters and
`rsaStepP` runs. -/
def rsaAllP (prep : Pr F T Q (prime + K) U) (rg : RsaR (RsaX t₀) → Fin T) (ι : Fin 64 → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hd : Fin 5 → Fin t₀)
    (pay : Fin t₀) (hi : Function.Injective hd) (hQs : swapStates hd pay hi ≤ Q)
    (hsw : Function.Injective fun j => rg (.x (.sw j))) (hTs : swapT t₀ ≤ T) :
    Pr F T Q (prime + K) U :=
  .seq prep (.seq (rsaAxisP rg ι hι hT hQ)
    (scanP (rg (.x .ax)) (rg (.x .ax'))
      (.seq prep (rsaStepP rg ι hι hT hQ hd pay hi hQs hsw hTs))))

/-- The axis processed at step `k`: `d - 1 - k`. -/
def rsaStepAx {d : ℕ} (hd0 : 0 < d) (k : ℕ) : Fin d := ⟨d - 1 - k, by omega⟩

/-- The step bound of `Ã` along all axes. -/
def rsaAllCost (T t₀ w m d : ℕ) (t : Fin d → ℕ) (hd0 : 0 < d) (Dt : Fin d → RsaAxisData)
    (hd : Fin 5 → Fin t₀) (cp : ℕ → ℕ) (n : ℕ) : ℕ :=
  cp 0 + rsaAxisCost T w (Dt (rsaStepAx hd0 0)).s (t (rsaStepAx hd0 0)) m
    (Dt (rsaStepAx hd0 0)).Lb (n / t (rsaStepAx hd0 0)) +
  (∑ j ∈ Finset.range (d - 1), (cp (j + 1) +
    rsaStepCost T t₀ w (Dt (rsaStepAx hd0 (j + 1))).s (t (rsaStepAx hd0 (j + 1))) m
      (Dt (rsaStepAx hd0 (j + 1))).Lb n
      (BinaryInterchangeRun.cost (rsaPre t (rsaStepAx hd0 (j + 1)))
        (rsaMid t (rsaStepAx hd0 (j + 1))) (3 * w) (Dt (rsaStepAx hd0 (j + 1))).Lb
        (Dt (rsaStepAx hd0 0)).Lb (Dt (rsaStepAx hd0 (j + 1))).hs)
      (BinaryInterchangeRun.cost (rsaPre t (rsaStepAx hd0 (j + 1)))
        (rsaMid t (rsaStepAx hd0 (j + 1))) (3 * w) (Dt (rsaStepAx hd0 0)).Lb
        (Dt (rsaStepAx hd0 (j + 1))).Lb
        (fun k => (Dt (rsaStepAx hd0 (j + 1))).hs (Equiv.swap 3 4 k)))
      (∑ i, (rsaBank hd (Dt (rsaStepAx hd0 (j + 1))).hs i : List (Fin (prime + K + 4))).length)
      (∑ i, (rsaBank hd (fun k => (Dt (rsaStepAx hd0 (j + 1))).hs (Equiv.swap 3 4 k)) i :
        List (Fin (prime + K + 4))).length)
      (((Dt (rsaStepAx hd0 (j + 1))).hs 3).length + ((Dt (rsaStepAx hd0 (j + 1))).hs 4).length
        + 2) + 3) + 2 * (d - 1) + 4)

variable {body : F → Pr F T Q (prime + K) U}
  {rg : RsaR (RsaX t₀) → Fin T} {ι : Fin 64 → Fin T}

set_option maxHeartbeats 2000000 in
/-- **`Ã` along all axes of the padded box.** The box register holds the stream `l₀` of the
padded box `∏_{i<d} [0, t_i)`; the axis counter `ax` holds `d - 1` symbols. `prep` takes the
register file `V₀` (resp. `cfg k`) to `cfg 0` (resp. `cfg (k + 1)`), whatever the box stream
and the axis counter, where `cfg k` is configured for the axis `rsaStepAx k = d - 1 - k` with
the parameters `Dt` (`RsaIdle`, `ob` and the spares empty, the bank holding the headers of the
interchange of the axis with the last one). Afterwards the box register holds the line maps
along the axes `d - 1, …, 0` of `l₀` (`rsaFlat d t g 0 l₀`, `g i` the line machine of axis `i`),
the register file is `cfg (d - 1)` and the counter is restored; every intermediate box fits
`w` bits. -/
theorem rsa_all (prep : Pr F T Q (prime + K) U) (hrg : Function.Injective rg)
    (hdisj : ∀ r j, rg r ≠ ι j) (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ prime + K) (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rg (.x (.sw j)))
    (hTs : swapT t₀ ≤ T) (hdpay : ∀ k, hd k ≠ pay) {d : ℕ} (hd0 : 0 < d) (t : Fin d → ℕ)
    {w m : ℕ} (hw : 1 ≤ w) (Dt : Fin d → RsaAxisData)
    (hDt : ∀ i, t i = 2 ^ (Dt i).Lb ∧ (Dt i).s < t i ∧ m ≤ (Dt i).s ∧ 0 < (Dt i).s ∧
      (Dt i).q ≤ w ∧ ∀ y ∈ rsaTabL (t i) (2 * m + 1) (Dt i).wt, Fits w y ∧ y.im = 0)
    (hDw : ∀ i : Fin d, (i : ℕ) + 1 < d → (Dt i).Lb ≤ (Dt (rsaStepAx hd0 0)).Lb + 1 ∧
      (Dt (rsaStepAx hd0 0)).Lb ≤ (Dt i).Lb + 1 ∧
      (∀ k, Counter.value ((Dt i).hs k) = BinaryInterchangeRun.values (rsaPre t i) (rsaMid t i)
        (3 * w) (Dt i).Lb (Dt (rsaStepAx hd0 0)).Lb k) ∧
      ∀ k, GrowingCounterData.Canonical ((Dt i).hs k))
    (V₀ : RsaV (RsaX t₀) (prime + K)) (cfg : ℕ → RsaV (RsaX t₀) (prime + K))
    (hcfg : ∀ k (_ : k < d), RsaIdle (cfg k) w (Dt (rsaStepAx hd0 k)).q (Dt (rsaStepAx hd0 k)).Lb
      (Dt (rsaStepAx hd0 k)).s (t (rsaStepAx hd0 k)) m (Dt (rsaStepAx hd0 k)).wt ∧
      (cfg k).ob = [] ∧ (0 < k → (∀ j, (cfg k).xr (.sw j) = rsaBank hd (Dt (rsaStepAx hd0 k)).hs j) ∧
        (cfg k).xr .xt = [] ∧ (cfg k).xr .e1 = [] ∧ (cfg k).xr .e2 = []))
    (cp : ℕ → ℕ)
    (hprep₀ : ∀ l a a', RsaRuns body rg ι prep (rsaWith V₀ l a a').get (rsaWith (cfg 0) l a a').get
      (cp 0))
    (hprep : ∀ k, k + 1 < d → ∀ l a a', RsaRuns body rg ι prep (rsaWith (cfg k) l a a').get
      (rsaWith (cfg (k + 1)) l a a').get (cp (k + 1)))
    (l₀ : List GaussianInt) (hl₀ : l₀.length = ∏ i, t i)
    (hfits : ∀ k ≤ d, ∀ x ∈ rsaFlat d t (fun i => (Dt i).g m (t i)) k l₀, Fits w x)
    (axs : List (Fin (prime + K + 4))) (haxs : axs.length = d - 1) :
    RsaRuns body rg ι (rsaAllP prep rg ι hι hT hQ hd pay hi hQs hsw hTs)
      (rsaWith V₀ (cstream (prime + K) w l₀) axs []).get
      (rsaWith (cfg (d - 1)) (cstream (prime + K) w
        (rsaFlat d t (fun i => (Dt i).g m (t i)) 0 l₀)) axs []).get
      (rsaAllCost (K := K) T t₀ w m d t hd0 Dt hd cp l₀.length) := by
  set g : Fin d → List GaussianInt → List GaussianInt := fun i => (Dt i).g m (t i) with hg
  set last : Fin d := rsaStepAx hd0 0 with hlast
  have hlastv : (last : ℕ) = d - 1 := by simp [hlast, rsaStepAx]
  have htpos : ∀ i, 0 < t i := fun i => by rw [(hDt i).1]; positivity
  have hlen_flat : ∀ k, (rsaFlat d t g k l₀).length = ∏ i, t i := by
    intro k
    rw [rsaFlat]
    induction ((List.finRange d).drop k) with
    | nil => exact hl₀
    | cons j js ih =>
        rw [List.foldr_cons, rsaAxisOp, length_rsaAxisL, rsaPre_mul]
  -- 1. load the parameters of the last axis
  have h1 := hprep₀ (cstream (prime + K) w l₀) axs []
  -- 2. `Ã` along the last axis
  have hsuf : rsaSuf t last = 1 := rsaSuf_lastAxis t last (by omega)
  have hpre : rsaPre t last * t last = ∏ i, t i := by
    have := rsaPre_mul t last
    rw [hsuf, Nat.mul_one] at this; exact this
  set lines := rsaChunks (t last) (rsaPre t last) l₀ with hlines
  have hl₀' : l₀.length = rsaPre t last * t last := by rw [hl₀, hpre]
  have h2 := rsa_axis (body := body) hrg hdisj hι hT hQ hA hw (hDt last).2.2.2.2.1
    (rsaWith (cfg 0) (cstream (prime + K) w l₀) axs []) ((hcfg 0 hd0).1.with_ln_xr _ _)
    (hDt last).1 (hDt last).2.1 (hDt last).2.2.1 (hDt last).2.2.2.1 (hDt last).2.2.2.2.2 lines
    (fun l hl => length_rsaChunks_mem hl₀' hl)
    (fun l hl x hx => hfits d le_rfl x (by
      rw [rsaFlat_ge d t g le_rfl]; exact mem_rsaChunks hl (List.mem_of_mem_take hx)))
    (by simp [rsaWith, hlines, flatten_rsaChunks _ _ _ hl₀']) (by simp [rsaWith, (hcfg 0 hd0).2.1])
  have hfl1 : lines.flatMap (rsaLineMap (Dt last).q (Dt last).s (t last) m (Dt last).wt) =
      rsaFlat d t g (d - 1) l₀ := by
    rw [rsaFlat_lt d t g (by omega), rsaFlat_ge d t g (by omega)]
    have hfin : (⟨d - 1, by omega⟩ : Fin d) = last := Fin.ext (by rw [hlastv])
    rw [hfin, rsaAxisOp, hsuf, rsaAxisL_inner _ _ _ _ hl₀' (fun x _ => by
      simp [hg, RsaAxisData.g, length_rsaLineMap])]
    rfl
  rw [hfl1] at h2
  have h2' : RsaRuns body rg ι (rsaAxisP rg ι hι hT hQ)
      (rsaWith (cfg 0) (cstream (prime + K) w l₀) axs []).get
      (rsaWith (cfg 0) (cstream (prime + K) w (rsaFlat d t g (d - 1) l₀)) axs []).get
      (rsaAxisCost T w (Dt last).s (t last) m (Dt last).Lb (l₀.length / t last)) := by
    have hnl : lines.length = l₀.length / t last := by
      rw [hlines, rsaChunks, List.length_map, List.length_range, hl₀',
        Nat.mul_div_cancel _ (htpos last)]
    rw [← hnl]
    exact h2
  -- 3. the other axes
  set Φ : ℕ → RsaR (RsaX t₀) → List (Fin (prime + K + 4)) := fun j =>
    (rsaWith (cfg j) (cstream (prime + K) w (rsaFlat d t g (d - 1 - j) l₀)) [] []).get with hΦ
  have hloop := rsa_scanP_sum (body := body) (ι := ι) hrg hdisj (a := .x .ax) (t := .x .ax')
    (by simp) (p := .seq prep (rsaStepP rg ι hι hT hQ hd pay hi hQs hsw hTs)) Φ
    (b := fun j => cp (j + 1) + rsaStepCost T t₀ w (Dt (rsaStepAx hd0 (j + 1))).s
      (t (rsaStepAx hd0 (j + 1))) m (Dt (rsaStepAx hd0 (j + 1))).Lb l₀.length
      (BinaryInterchangeRun.cost (rsaPre t (rsaStepAx hd0 (j + 1)))
        (rsaMid t (rsaStepAx hd0 (j + 1))) (3 * w) (Dt (rsaStepAx hd0 (j + 1))).Lb
        (Dt (rsaStepAx hd0 0)).Lb (Dt (rsaStepAx hd0 (j + 1))).hs)
      (BinaryInterchangeRun.cost (rsaPre t (rsaStepAx hd0 (j + 1)))
        (rsaMid t (rsaStepAx hd0 (j + 1))) (3 * w) (Dt (rsaStepAx hd0 0)).Lb
        (Dt (rsaStepAx hd0 (j + 1))).Lb
        (fun k => (Dt (rsaStepAx hd0 (j + 1))).hs (Equiv.swap 3 4 k)))
      (∑ i, (rsaBank hd (Dt (rsaStepAx hd0 (j + 1))).hs i : List (Fin (prime + K + 4))).length)
      (∑ i, (rsaBank hd (fun k => (Dt (rsaStepAx hd0 (j + 1))).hs (Equiv.swap 3 4 k)) i :
        List (Fin (prime + K + 4))).length)
      (((Dt (rsaStepAx hd0 (j + 1))).hs 3).length + ((Dt (rsaStepAx hd0 (j + 1))).hs 4).length
        + 2)) axs
    (fun j hj => by
      rw [haxs] at hj
      rw [hΦ]
      simp only
      rw [rsaWith_upd, rsaWith_upd]
      set i := rsaStepAx hd0 (j + 1) with hidef
      have hiv : (i : ℕ) = d - 2 - j := by simp [hidef, rsaStepAx]; omega
      have hi1 : (i : ℕ) + 1 < d := by omega
      have hstep := rsa_step (body := body) hrg hdisj hι hT hQ hA hd pay hi hQs hsw hTs hdpay t i
        hi1 hw (hDt i).2.2.2.2.1 (hDt i).1 (by
          rw [show (⟨d - 1, by omega⟩ : Fin d) = last from Fin.ext (by rw [hlastv])]
          exact (hDt last).1) (hDw i hi1).1 (hDw i hi1).2.1 (hDt i).2.1 (hDt i).2.2.1
        (hDt i).2.2.2.1 (hDt i).2.2.2.2.2
        (List.prod_pos fun x hx => by
          obtain ⟨k, -, rfl⟩ := List.mem_iff_getElem.1 (List.mem_of_mem_take hx)
          simp only [List.getElem_ofFn]; exact htpos _)
        (List.prod_pos fun x hx => by
          obtain ⟨k, -, rfl⟩ := List.mem_iff_getElem.1
            (List.mem_of_mem_drop (List.mem_of_mem_dropLast hx))
          simp only [List.getElem_ofFn]; exact htpos _)
        (Dt i).hs (hDw i hi1).2.2.1 (hDw i hi1).2.2.2
        (rsaWith (cfg (j + 1)) (cstream (prime + K) w (rsaFlat d t g (d - 1 - j) l₀))
          (axs.drop (j + 1)) (axs.take (j + 1)).reverse)
        ((hcfg (j + 1) (by omega)).1.with_ln_xr _ _) (hcfg (j + 1) (by omega)).2.1
        (fun j' => by
          simp only [rsaWith]
          rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
          exact ((hcfg (j + 1) (by omega)).2.2 (by omega)).1 j')
        (by simp [rsaWith, ((hcfg (j + 1) (by omega)).2.2 (by omega)).2.1])
        (by simp [rsaWith, ((hcfg (j + 1) (by omega)).2.2 (by omega)).2.2.1])
        (by simp [rsaWith, ((hcfg (j + 1) (by omega)).2.2 (by omega)).2.2.2])
        (rsaFlat d t g (d - 1 - j) l₀) (hlen_flat _)
        (hfits (d - 1 - j) (by omega)) rfl
      rw [hlen_flat, ← hl₀] at hstep
      have hnext : rsaAxisL (rsaPre t i) (t i) (rsaSuf t i)
          (rsaLineMap (Dt i).q (Dt i).s (t i) m (Dt i).wt) (rsaFlat d t g (d - 1 - j) l₀) =
          rsaFlat d t g (d - 1 - (j + 1)) l₀ := by
        rw [rsaFlat_lt d t g (show d - 1 - (j + 1) < d by omega)]
        have hfin : (⟨d - 1 - (j + 1), by omega⟩ : Fin d) = i :=
          Fin.ext (by simp only; rw [hiv]; omega)
        rw [hfin, show d - 1 - (j + 1) + 1 = d - 1 - j by omega]
        rfl
      rw [hnext] at hstep
      exact (hprep j (by omega) _ _ _).seq hdisj hstep)
  rw [haxs] at hloop
  have e0 : Function.update (Function.update (Φ 0) (.x .ax) axs) (.x .ax') [] =
      (rsaWith (cfg 0) (cstream (prime + K) w (rsaFlat d t g (d - 1) l₀)) axs []).get := by
    rw [hΦ]; simp only [Nat.sub_zero]; rw [rsaWith_upd]
  have e1 : Function.update (Function.update (Φ (d - 1)) (.x .ax) axs) (.x .ax') [] =
      (rsaWith (cfg (d - 1)) (cstream (prime + K) w (rsaFlat d t g 0 l₀)) axs []).get := by
    rw [hΦ]; simp only; rw [rsaWith_upd, show d - 1 - (d - 1) = 0 by omega]
  rw [e0, e1] at hloop
  exact (h1.seq hdisj (h2'.seq hdisj hloop)).mono (by unfold rsaAllCost; rw [← hlast]; omega)

end All

/-! ### The tensor of the numeric `Ã` -/

open IntegerMultBounds.NLogN in
/-- The line machine with the weights `rsaWA s t m WA` and shift `q` gives the numerators at
scale `p + 1` of `resampANum s t m (termW p (WA / 2^p))` from scale `q`. -/
theorem rsaLineRel_resampA {s t : ℕ} [NeZero s] [NeZero t] (p q m : ℕ) (WA : ZMod t → ℤ → ℤ)
    (hst : s ≤ t) (hm : m ≤ s) :
    RsaLineRel s t (resampANum s t m
        (IntegerMultBounds.Resampling.WindowSum.termW p fun k j => (WA k j : ℝ) / 2 ^ p))
      (rsaLineMap q s t m (rsaWA s t m WA)) q (p + 1) := by
  refine ⟨fun N => length_rsaLineMap _ _ _ _ _ _, fun N v hN hv k hk => ?_⟩
  have hNs : (N.take s).length = s := by simp [hN, hst]
  rw [rsaOut_resampANum p q m WA (N.take s) hNs hst hm v (fun j => by
    rw [hv j, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (ZMod.val_lt j)]) hk]
  rfl

section Tensor

variable {t₀ T Q K : ℕ} {U F : Type} {body : F → Pr F T Q (prime + K) U}
  {rg : RsaR (RsaX t₀) → Fin T} {ι : Fin 64 → Fin T}

open IntegerMultBounds.NLogN in
set_option maxHeartbeats 1000000 in
/-- **The machine computes the tensor.** Under the hypotheses of `rsa_all`, with `l₀` the padded
stream `rsaBox d t F` of the numerators `F` of `u` at scale `qi` and every line map giving the
numerators of the numeric map `A i` (`RsaLineRel`, input scale `qi` on the last axis and `qo` on
the others), the stage ends with the stream `rsaBox d t G` of the numerators `G` of
`tensorZR d s t A u` at scale `qo`. -/
theorem rsa_all_tensor (prep : Pr F T Q (prime + K) U) (hrg : Function.Injective rg)
    (hdisj : ∀ r j, rg r ≠ ι j) (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ prime + K) (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rg (.x (.sw j)))
    (hTs : swapT t₀ ≤ T) (hdpay : ∀ k, hd k ≠ pay) {d : ℕ} (hd0 : 0 < d) (t : Fin d → ℕ)
    {w m : ℕ} (hw : 1 ≤ w) (Dt : Fin d → RsaAxisData)
    (hDt : ∀ i, t i = 2 ^ (Dt i).Lb ∧ (Dt i).s < t i ∧ m ≤ (Dt i).s ∧ 0 < (Dt i).s ∧
      (Dt i).q ≤ w ∧ ∀ y ∈ rsaTabL (t i) (2 * m + 1) (Dt i).wt, Fits w y ∧ y.im = 0)
    (hDw : ∀ i : Fin d, (i : ℕ) + 1 < d → (Dt i).Lb ≤ (Dt (rsaStepAx hd0 0)).Lb + 1 ∧
      (Dt (rsaStepAx hd0 0)).Lb ≤ (Dt i).Lb + 1 ∧
      (∀ k, Counter.value ((Dt i).hs k) = BinaryInterchangeRun.values (rsaPre t i) (rsaMid t i)
        (3 * w) (Dt i).Lb (Dt (rsaStepAx hd0 0)).Lb k) ∧
      ∀ k, GrowingCounterData.Canonical ((Dt i).hs k))
    (V₀ : RsaV (RsaX t₀) (prime + K)) (cfg : ℕ → RsaV (RsaX t₀) (prime + K))
    (hcfg : ∀ k (_ : k < d), RsaIdle (cfg k) w (Dt (rsaStepAx hd0 k)).q (Dt (rsaStepAx hd0 k)).Lb
      (Dt (rsaStepAx hd0 k)).s (t (rsaStepAx hd0 k)) m (Dt (rsaStepAx hd0 k)).wt ∧
      (cfg k).ob = [] ∧ (0 < k → (∀ j, (cfg k).xr (.sw j) = rsaBank hd (Dt (rsaStepAx hd0 k)).hs j) ∧
        (cfg k).xr .xt = [] ∧ (cfg k).xr .e1 = [] ∧ (cfg k).xr .e2 = []))
    (cp : ℕ → ℕ)
    (hprep₀ : ∀ l a a', RsaRuns body rg ι prep (rsaWith V₀ l a a').get (rsaWith (cfg 0) l a a').get
      (cp 0))
    (hprep : ∀ k, k + 1 < d → ∀ l a a', RsaRuns body rg ι prep (rsaWith (cfg k) l a a').get
      (rsaWith (cfg (k + 1)) l a a').get (cp (k + 1)))
    (A : (i : Fin d) → (ZMod (Dt i).s → ℂ) → ZMod (t i) → ℂ) (qi qo : ℕ)
    (hrel : ∀ i : Fin d, RsaLineRel (Dt i).s (t i) (A i) ((Dt i).g m (t i))
      (if (i : ℕ) + 1 = d then qi else qo) qo)
    (u : ((i : Fin d) → ZMod (Dt i).s) → ℂ) (F₀ : ((i : Fin d) → Fin (t i)) → GaussianInt)
    (hF : ∀ x : (i : Fin d) → Fin (t i), (∀ i, (x i : ℕ) < (Dt i).s) →
      u (fun i => ((x i : ℕ) : ZMod (Dt i).s)) = GaussianInt.toComplex (F₀ x) / 2 ^ qi)
    (hF0 : ∀ x : (i : Fin d) → Fin (t i), (∃ i, (Dt i).s ≤ x i) → F₀ x = 0)
    (hfits : ∀ k ≤ d, ∀ x ∈ rsaFlat d t (fun i => (Dt i).g m (t i)) k (rsaBox d t F₀), Fits w x)
    (axs : List (Fin (prime + K + 4))) (haxs : axs.length = d - 1) :
    ∃ G : ((i : Fin d) → Fin (t i)) → GaussianInt,
      (∀ x : (i : Fin d) → Fin (t i),
        tensorZR d (fun i => (Dt i).s) t A u (fun i => ((x i : ℕ) : ZMod (t i))) =
          GaussianInt.toComplex (G x) / 2 ^ qo) ∧
      RsaRuns body rg ι (rsaAllP prep rg ι hι hT hQ hd pay hi hQs hsw hTs)
        (rsaWith V₀ (cstream (prime + K) w (rsaBox d t F₀)) axs []).get
        (rsaWith (cfg (d - 1)) (cstream (prime + K) w (rsaBox d t G)) axs []).get
        (rsaAllCost (K := K) T t₀ w m d t hd0 Dt hd cp (∏ i, t i)) := by
  have : ∀ i, NeZero (Dt i).s := fun i => ⟨by have := (hDt i).2.2.2.1; omega⟩
  have : ∀ i, NeZero (t i) := fun i => ⟨by rw [(hDt i).1]; positivity⟩
  obtain ⟨G, hG, hbox⟩ := rsa_tensor d (fun i => (Dt i).s) t (fun i => (hDt i).2.1.le) A
    (fun i => (Dt i).g m (t i)) qi qo hrel u F₀ hF hF0
  refine ⟨G, fun x => by rw [hG x, ite_eq_right (by omega)], ?_⟩
  have hl₀ := length_rsaBox d t F₀
  have H := rsa_all prep hrg hdisj hι hT hQ hA hd pay hi hQs hsw hTs hdpay hd0 t hw Dt hDt hDw V₀
    cfg hcfg cp hprep₀ hprep (rsaBox d t F₀) hl₀ hfits axs haxs (body := body)
  rw [← rsaAxesL_flat d t _ _ hl₀, hbox, hl₀] at H
  exact H

end Tensor

/-! ### The pipeline's `Ã` -/

section Pipeline

open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.NLogN
open IntegerMultBounds.Resampling.WeightTable (tableA)

/-- The parameters of `Ã` on axis `i` of the pipeline at length `n`: `s n i` source records,
`t n i = 2^(log₂ t n i)` target records, shift `p n` on the last axis (the input scale) and
`p n + 1` on the others, the weights `tableA` on the windows `truncWindow`, and the interchange
headers `hs i`. -/
def rsaPipeData (n : ℕ) (hs : Fin (d n) → Fin 5 → List Bool) (i : Fin (d n)) : RsaAxisData where
  s := s n i
  Lb := Nat.log 2 (t n i)
  q := if (i : ℕ) + 1 = d n then p n else p n + 1
  wt := rsaWA (s n i) (t n i) (windowA (p n) (alpha n)) (tableA (s n i) (t n i) (alpha n) (p n))
  hs := hs i

/-- The line machine of axis `i` gives the numerators of `lineA n i`. -/
theorem rsaLineRel_lineA (n : ℕ) (hs : Fin (d n) → Fin 5 → List Bool) (i : Fin (d n))
    (hst : s n i ≤ t n i) (hm : windowA (p n) (alpha n) ≤ s n i) :
    RsaLineRel (s n i) (t n i) (lineA n i)
      ((rsaPipeData n hs i).g (windowA (p n) (alpha n)) (t n i))
      (if (i : ℕ) + 1 = d n then p n else p n + 1) (p n + 1) :=
  rsaLineRel_resampA (p n) _ (windowA (p n) (alpha n)) _ hst hm

lemma rsaTabL_rsaWA_im {s t m : ℕ} (WA : ZMod t → ℤ → ℤ) (n : ℕ) :
    ∀ y ∈ rsaTabL t n (rsaWA s t m WA), y.im = 0 := by
  intro y hy
  simp only [rsaTabL, List.mem_flatMap, List.mem_range, List.mem_map] at hy
  obtain ⟨_, _, _, _, rfl⟩ := hy
  rfl

variable {t₀ T Q K : ℕ} {U F : Type} {body : F → Pr F T Q (prime + K) U}
  {rg : RsaR (RsaX t₀) → Fin T} {ι : Fin 64 → Fin T}

set_option maxHeartbeats 1000000 in
/-- **`Ã` along every axis of the pipeline's padded box.** At operand length `n` (with
`1 ≤ d n`, `s n i < t n i`, the window `m = windowA (p n) (α n) ≤ s n i`, widths `w ≥ p n + 1`
fitting every table entry and every intermediate box), the box register starts with the padded
stream `rsaBox (d n) (t n) F₀` of the numerators of `u` at scale `p n` and ends with the stream of
an array `G` of numerators of `tensorZR (d n) (s n) (t n) (lineA n) u` at scale `p n + 1`, the
`Ã` stage of `srcMap n`. The parameter loader `prep` and the configured register files `cfg k`
are as in `rsa_all`, with the parameters `rsaPipeData n hs`. -/
theorem rsa_all_lineA (n : ℕ) (prep : Pr F T Q (prime + K) U) (hrg : Function.Injective rg)
    (hdisj : ∀ r j, rg r ≠ ι j) (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ prime + K) (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rg (.x (.sw j)))
    (hTs : swapT t₀ ≤ T) (hdpay : ∀ k, hd k ≠ pay) (hd0 : 0 < d n) {w : ℕ}
    (hw : p n + 1 ≤ w) (hst : ∀ i, s n i < t n i)
    (hm : ∀ i, windowA (p n) (alpha n) ≤ s n i)
    (hFT : ∀ i, ∀ y ∈ rsaTabL (t n i) (2 * windowA (p n) (alpha n) + 1)
      (rsaWA (s n i) (t n i) (windowA (p n) (alpha n)) (tableA (s n i) (t n i) (alpha n) (p n))),
      Fits w y)
    (hs : Fin (d n) → Fin 5 → List Bool)
    (hDw : ∀ i : Fin (d n), (i : ℕ) + 1 < d n →
      (rsaPipeData n hs i).Lb ≤ (rsaPipeData n hs (rsaStepAx hd0 0)).Lb + 1 ∧
      (rsaPipeData n hs (rsaStepAx hd0 0)).Lb ≤ (rsaPipeData n hs i).Lb + 1 ∧
      (∀ k, Counter.value (hs i k) = BinaryInterchangeRun.values (rsaPre (t n) i)
        (rsaMid (t n) i) (3 * w) (rsaPipeData n hs i).Lb (rsaPipeData n hs (rsaStepAx hd0 0)).Lb
          k) ∧
      ∀ k, GrowingCounterData.Canonical (hs i k))
    (V₀ : RsaV (RsaX t₀) (prime + K)) (cfg : ℕ → RsaV (RsaX t₀) (prime + K))
    (hcfg : ∀ k (_ : k < d n), RsaIdle (cfg k) w (rsaPipeData n hs (rsaStepAx hd0 k)).q
      (rsaPipeData n hs (rsaStepAx hd0 k)).Lb (rsaPipeData n hs (rsaStepAx hd0 k)).s
      (t n (rsaStepAx hd0 k)) (windowA (p n) (alpha n)) (rsaPipeData n hs (rsaStepAx hd0 k)).wt ∧
      (cfg k).ob = [] ∧ (0 < k →
        (∀ j, (cfg k).xr (.sw j) = rsaBank hd (rsaPipeData n hs (rsaStepAx hd0 k)).hs j) ∧
        (cfg k).xr .xt = [] ∧ (cfg k).xr .e1 = [] ∧ (cfg k).xr .e2 = []))
    (cp : ℕ → ℕ)
    (hprep₀ : ∀ l a a', RsaRuns body rg ι prep (rsaWith V₀ l a a').get (rsaWith (cfg 0) l a a').get
      (cp 0))
    (hprep : ∀ k, k + 1 < d n → ∀ l a a', RsaRuns body rg ι prep (rsaWith (cfg k) l a a').get
      (rsaWith (cfg (k + 1)) l a a').get (cp (k + 1)))
    (u : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) (F₀ : ((i : Fin (d n)) → Fin (t n i)) → GaussianInt)
    (hF : ∀ x : (i : Fin (d n)) → Fin (t n i), (∀ i, (x i : ℕ) < s n i) →
      u (fun i => ((x i : ℕ) : ZMod (s n i))) = GaussianInt.toComplex (F₀ x) / 2 ^ p n)
    (hF0 : ∀ x : (i : Fin (d n)) → Fin (t n i), (∃ i, s n i ≤ x i) → F₀ x = 0)
    (hfits : ∀ k ≤ d n, ∀ x ∈ rsaFlat (d n) (t n)
      (fun i => (rsaPipeData n hs i).g (windowA (p n) (alpha n)) (t n i)) k (rsaBox (d n) (t n) F₀),
      Fits w x)
    (axs : List (Fin (prime + K + 4))) (haxs : axs.length = d n - 1) :
    ∃ G : ((i : Fin (d n)) → Fin (t n i)) → GaussianInt,
      (∀ x : (i : Fin (d n)) → Fin (t n i),
        tensorZR (d n) (s n) (t n) (lineA n) u (fun i => ((x i : ℕ) : ZMod (t n i))) =
          GaussianInt.toComplex (G x) / 2 ^ (p n + 1)) ∧
      RsaRuns body rg ι (rsaAllP prep rg ι hι hT hQ hd pay hi hQs hsw hTs)
        (rsaWith V₀ (cstream (prime + K) w (rsaBox (d n) (t n) F₀)) axs []).get
        (rsaWith (cfg (d n - 1)) (cstream (prime + K) w (rsaBox (d n) (t n) G)) axs []).get
        (rsaAllCost (K := K) T t₀ w (windowA (p n) (alpha n)) (d n) (t n) hd0 (rsaPipeData n hs)
          hd cp (∏ i, t n i)) := by
  have hpos : ∀ i, 0 < s n i := fun i => Nat.pos_of_ne_zero (NeZero.ne (s n i))
  exact rsa_all_tensor prep hrg hdisj hι hT hQ hA hd pay hi hQs hsw hTs hdpay hd0 (t n)
    (by omega) (rsaPipeData n hs)
    (fun i => ⟨t_pow_log n i, hst i, hm i, hpos i, by
      simp only [rsaPipeData]; split_ifs <;> omega,
      fun y hy => ⟨hFT i y hy, rsaTabL_rsaWA_im _ _ y hy⟩⟩)
    hDw V₀ cfg hcfg cp hprep₀ hprep (lineA n) (p n) (p n + 1)
    (fun i => rsaLineRel_lineA n hs i (hst i).le (hm i)) u F₀ hF hF0 hfits axs haxs

end Pipeline

end

end IntegerMultBounds.MathlibTM2.Fast.ResampA
