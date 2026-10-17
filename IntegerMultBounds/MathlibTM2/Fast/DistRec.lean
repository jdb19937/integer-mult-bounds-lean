module

public import IntegerMultBounds.MathlibTM2.Fast.DistAxis
public import IntegerMultBounds.MathlibTM2.Fast.PrepB
public import IntegerMultBounds.MathlibTM2.Fast.LoadChirp
public import IntegerMultBounds.MathlibTM2.Fast.PrepA
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The record formats of the axis loop

The pushes of the axis loop (`Fast/DistAxis.lean`) and the formats the stage loaders read.

* `dsFA`, `dsFB`: the variables of the fields of an `Ã` record (`PreAxA.fields`: `t, q, m, s,
  L, Ld, P, G, α, p, W`) and of a `B̃₀` record (`PreAxB.fields`: `t, s, m, L, Ld, P, G, α, p,
  W`); `dsRecPush o fs` pushes the fields `fs` onto `o` in reverse order, so `o` gains the record
  `preRec` with the first field on top (`dsOut_recPush`).
* `dsL₀ oA oB xT xS`: the pushes of the composite loop: the `Ã` record onto `oA`, the `B̃₀`
  record onto `oB`, the reversed blocks of `t_i` and `s_i` onto `xT`, `xS`.
* `ds_acc_A`, `ds_acc_B`: after the `d` iterations `oA`, `oB` hold `preRecsA n Wt hd0 0` and
  `preRecsB n Wt hd0 0` (records in the axis order `d - 1, …, 0`), from `ds_preDA`,
  `ds_preDB`: the record of step `k` is the axis state `dsAV n Wt (d - 1 - k)` read through
  `dsFA`, `dsFB` (`ds_rsaPre`: `P_i = rsaPre t i`; `ds_rsaMid`: `G_i = rsaMid t i`;
  `ds_log_t`: `log₂ t_i = dsL n i`).
* `ds_acc_T`, `ds_acc_S`: `xT`, `xS` hold the description streams `ldcBlocks (List.ofFn t)`,
  `ldcBlocks (List.ofFn s)` of the chirp loader reversed.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Moduli
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt


/-! ### Lengths, products and logarithms -/

section Values

variable {n : ℕ}

theorem ds_ofFn_t (n : ℕ) : List.ofFn (t n) = (List.range (d n)).map (dsT n) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact (dsT_eq n ⟨i, by simpa using h1⟩).symm

theorem ds_ofFn_s (n : ℕ) : List.ofFn (s n) = (List.range (d n)).map (dsS n) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  rfl

theorem ds_log_t (n : ℕ) (i : Fin (d n)) : Nat.log 2 (t n i) = dsL n i := by
  unfold t dsL
  split_ifs <;> exact Nat.log_pow (by norm_num) _

theorem ds_log_last (hn : 2 ≤ n) (hd0 : 0 < d n) :
    Nat.log 2 (t n (rsaStepAx hd0 0)) = ℓ n := by
  rw [ds_log_t]
  have h := numHalf_lt (one_le_d hn)
  have h' : ¬ ((rsaStepAx hd0 0 : Fin (d n)) : ℕ) < numHalf n := by simp [rsaStepAx]; omega
  simp [dsL, h']

theorem ds_rsaPre (n : ℕ) : ∀ i, i ≤ d n → rsaPre (t n) i = dsP n i
  | 0, _ => by simp [rsaPre, dsP]
  | i + 1, hi => by
    rw [rsaPre, List.prod_take_succ _ _ (by simpa using hi), ← rsaPre, ds_rsaPre n i (by omega),
      dsP_succ, List.getElem_ofFn, dsT_eq n ⟨i, hi⟩]

theorem ds_rsaMid (hn : 2 ≤ n) {i : ℕ} (hi : i < d n) : rsaMid (t n) i = dsG n i := by
  by_cases h : i + 1 < d n
  · have hT : (List.ofFn (t n)).prod = T n := by rw [List.prod_ofFn, prod_t (one_le_d hn)]
    rw [← List.prod_take_mul_prod_drop _ (i + 1), ← rsaPre, ← rsaSuf, rsaSuf_last _ _ h,
      ds_rsaPre n (i + 1) (by omega), dsP_succ] at hT
    have hl : t n ⟨d n - 1, by omega⟩ = r n := by
      rw [← dsT_eq]; exact dsT_last hn
    rw [hl] at hT
    have hG := dsG_mul hn h
    have hpos : 0 < dsP n i * dsT n i * r n :=
      Nat.mul_pos (Nat.mul_pos (dsP_pos n i) (dsT_pos n i)) (by unfold r; positivity)
    have e : dsP n i * dsT n i * r n * rsaMid (t n) i = dsP n i * dsT n i * r n * dsG n i := by
      rw [show dsP n i * dsT n i * r n * rsaMid (t n) i = dsP n i * dsT n i * (rsaMid (t n) i *
        r n) by ring, hT, ← hG]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos e
  · have hd : i + 1 = d n := by omega
    unfold rsaMid dsG
    rw [ite_eq_right h, hd, List.drop_eq_nil_of_le (by simp)]
    rfl

theorem ds_rsbPre (n i : ℕ) : rsbPre (t n) i = rsaPre (t n) i := rfl

theorem ds_rsbMid (n i : ℕ) : rsbMid (t n) i = rsaMid (t n) i := rfl

end Values

/-! ### Records -/

section Records

variable {T A : ℕ}

/-- The variables of the fields of an `Ã` record: `t, q, m, s, L, Ld, P, G, α, p, W`. -/
def dsFA : List (Fin pmNV) := [33, 36, 19, 35, 34, 7, 32, 37, 12, 2, 38]

/-- The variables of the fields of a `B̃₀` record: `t, s, m, L, Ld, P, G, α, p, W`. -/
def dsFB : List (Fin pmNV) := [33, 35, 20, 34, 7, 32, 37, 12, 2, 38]

/-- Push the fields `fs` onto `o`, the last field first. -/
def dsRecPush (o : Fin T) (fs : List (Fin pmNV)) : List (Fin T × Fin pmNV × DsMode) :=
  fs.reverse.map fun x => (o, x, .fld)

/-- The pushes of the composite loop. -/
def dsL₀ (oA oB xT xS : Fin T) : List (Fin T × Fin pmNV × DsMode) :=
  dsRecPush oA dsFA ++ dsRecPush oB dsFB ++ [(xT, 33, .rev), (xS, 35, .rev)]

theorem dsOut_map (val : Fin pmNV → ℕ) (o : Fin T) (b : DsMode) (l : List (Fin pmNV)) :
    dsOut (A := A) val (l.map fun x => (o, x, b)) o = l.reverse.flatMap fun x => dsBlk b (val x) := by
  unfold dsOut
  have e : (l.map fun x => (o, x, b)).filter (fun e => decide (e.1 = o)) =
      l.map fun x => (o, x, b) := List.filter_eq_self.2 (by simp)
  rw [e, ← List.map_reverse, List.flatMap_map]

theorem dsOut_recPush (val : Fin pmNV → ℕ) (o : Fin T) (fs : List (Fin pmNV)) :
    dsOut (A := A) val (dsRecPush o fs) o = preRec (fs.map val) := by
  rw [dsRecPush, dsOut_map, List.reverse_reverse, preRec, List.flatMap_map]
  rfl

theorem dsOut_L₀_A {oA oB xT xS : Fin T} (h1 : oB ≠ oA) (h2 : xT ≠ oA) (h3 : xS ≠ oA)
    (val : Fin pmNV → ℕ) : dsOut (A := A) val (dsL₀ oA oB xT xS) oA = preRec (dsFA.map val) := by
  rw [dsL₀, dsOut_append, dsOut_append, dsOut_none _ _ (by simp [h2, h3]),
    dsOut_none _ _ (by simp [dsRecPush, h1]), dsOut_recPush]
  simp

theorem dsOut_L₀_B {oA oB xT xS : Fin T} (h1 : oA ≠ oB) (h2 : xT ≠ oB) (h3 : xS ≠ oB)
    (val : Fin pmNV → ℕ) : dsOut (A := A) val (dsL₀ oA oB xT xS) oB = preRec (dsFB.map val) := by
  rw [dsL₀, dsOut_append, dsOut_append, dsOut_none _ _ (by simp [h2, h3]),
    dsOut_recPush, dsOut_none _ (dsRecPush oA dsFA) (by simp [dsRecPush, h1])]
  simp

theorem dsOut_L₀_T {oA oB xT xS : Fin T} (h1 : oA ≠ xT) (h2 : oB ≠ xT) (h3 : xS ≠ xT)
    (val : Fin pmNV → ℕ) :
    dsOut (A := A) val (dsL₀ oA oB xT xS) xT = (dsFld (val 33)).reverse := by
  rw [dsL₀, dsOut_append, dsOut_append, dsOut_none _ (dsRecPush oA dsFA) (by simp [dsRecPush, h1]),
    dsOut_none _ (dsRecPush oB dsFB) (by simp [dsRecPush, h2])]
  simp [dsOut, h3, dsBlk]

theorem dsOut_L₀_S {oA oB xT xS : Fin T} (h1 : oA ≠ xS) (h2 : oB ≠ xS) (h3 : xT ≠ xS)
    (val : Fin pmNV → ℕ) :
    dsOut (A := A) val (dsL₀ oA oB xT xS) xS = (dsFld (val 35)).reverse := by
  rw [dsL₀, dsOut_append, dsOut_append, dsOut_none _ (dsRecPush oA dsFA) (by simp [dsRecPush, h1]),
    dsOut_none _ (dsRecPush oB dsFB) (by simp [dsRecPush, h2])]
  simp [dsOut, h3, dsBlk]

end Records

/-! ### The formats -/

section Formats

variable {T A : ℕ} {n : ℕ}

theorem ds_range_reverse (m : ℕ) :
    (List.range m).reverse = (List.range m).map fun k => m - 1 - k := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_reverse, List.getElem_range, List.getElem_map, List.length_range]

/-- The `Ã` record of step `k` is the axis state of axis `d - 1 - k` read through `dsFA`. -/
theorem ds_preDA (hn : 2 ≤ n) (hd0 : 0 < d n) (Wt : ℕ) {k : ℕ} (hk : k < d n) :
    (preDA n Wt hd0 k).fields = dsFA.map (dsAV n Wt (d n - 1 - k)) := by
  have hi : d n - 1 - k < d n := by omega
  have hx : ((rsaStepAx hd0 k : Fin (d n)) : ℕ) = d n - 1 - k := rfl
  simp only [PreAxA.fields, preDA, dsFA, List.map_cons, List.map_nil]
  simp only [dsAV, dsLV, pmNV, Fin.isValue, pmVal]
  norm_num
  refine ⟨?_, ?_, rfl, ?_, ds_log_last hn hd0, ?_, ?_⟩
  · rw [← dsT_eq]; rfl
  · rw [hx, dsQ]; split_ifs <;> omega
  · rw [ds_log_t]; rfl
  · rw [hx]; exact ds_rsaPre n _ hi.le
  · rw [hx]; exact ds_rsaMid hn hi

/-- The `B̃₀` record of step `k` is the axis state of axis `d - 1 - k` read through `dsFB`. -/
theorem ds_preDB (hn : 2 ≤ n) (hd0 : 0 < d n) (Wt : ℕ) {k : ℕ} (hk : k < d n) :
    (preDB n Wt hd0 k).fields = dsFB.map (dsAV n Wt (d n - 1 - k)) := by
  have hi : d n - 1 - k < d n := by omega
  have hx : ((rsbAx hd0 k : Fin (d n)) : ℕ) = d n - 1 - k := rfl
  simp only [PreAxB.fields, preDB, dsFB, List.map_cons, List.map_nil]
  simp only [dsAV, dsLV, pmNV, Fin.isValue, pmVal]
  norm_num
  refine ⟨?_, rfl, ?_, ds_log_last hn hd0, ?_, ?_⟩
  · rw [← dsT_eq]; rfl
  · rw [ds_log_t]; rfl
  · rw [ds_rsbPre, hx]; exact ds_rsaPre n _ hi.le
  · rw [ds_rsbMid, hx]; exact ds_rsaMid hn hi

/-- The records pushed in the axis order `0, …, d - 1` form `preRecsA`. -/
theorem ds_recsA (hn : 2 ≤ n) (hd0 : 0 < d n) (Wt : ℕ) :
    ((List.range (d n)).reverse.flatMap fun i => preRec (dsFA.map (dsAV n Wt i))) =
      (preRecsA n Wt hd0 0 : List (Fin (A + 4))) := by
  rw [preRecsA, List.drop_zero, ds_range_reverse, List.flatMap_map]
  refine List.flatMap_congr fun k hk => ?_
  rw [ds_preDA hn hd0 Wt (List.mem_range.1 hk)]

/-- The records pushed in the axis order `0, …, d - 1` form `preRecsB`. -/
theorem ds_recsB (hn : 2 ≤ n) (hd0 : 0 < d n) (Wt : ℕ) :
    ((List.range (d n)).reverse.flatMap fun i => preRec (dsFB.map (dsAV n Wt i))) =
      (preRecsB n Wt hd0 0 : List (Fin (A + 4))) := by
  rw [preRecsB, List.drop_zero, ds_range_reverse, List.flatMap_map]
  refine List.flatMap_congr fun k hk => ?_
  rw [ds_preDB hn hd0 Wt (List.mem_range.1 hk)]

theorem ds_flatMap_reverse {α β : Type} (f : α → List β) (l : List α) :
    (l.reverse.flatMap fun x => (f x).reverse) = (l.flatMap f).reverse := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, List.reverse_append, ih]

/-- The reversed blocks of `t_i` pushed in the axis order form the reversed stream of the chirp
loader. -/
theorem ds_blocksT (Wt : ℕ) :
    ((List.range (d n)).reverse.flatMap fun i => (dsFld (dsAV n Wt i 33)).reverse) =
      (ldcBlocks (List.ofFn (t n)) : List (Fin (A + 4))).reverse := by
  rw [ds_flatMap_reverse, ds_ofFn_t, ldcBlocks, List.flatMap_map]
  rfl

/-- The reversed blocks of `s_i` pushed in the axis order form the reversed stream of the chirp
loader. -/
theorem ds_blocksS (Wt : ℕ) :
    ((List.range (d n)).reverse.flatMap fun i => (dsFld (dsAV n Wt i 35)).reverse) =
      (ldcBlocks (List.ofFn (s n)) : List (Fin (A + 4))).reverse := by
  rw [ds_flatMap_reverse, ds_ofFn_s, ldcBlocks, List.flatMap_map]
  rfl

end Formats

end IntegerMultBounds.MathlibTM2.Fast.TableVM
