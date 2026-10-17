module

public import IntegerMultBounds.MathlibTM2.Fast.ParamProg
public import IntegerMultBounds.MathlibTM2.Node.SlotXor
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The parameter machine

A host program computing, from the operand length `n ≥ 2` held in unary, every parameter of the
numeric pipeline (`Fast/ParamProg.lean`: the sizes of `Mult/Sizes.lean`, the moduli data of
`Mult/Moduli.lean`, the windows, Neumann steps, guards and precisions of `Mult/Pipeline.lean` and
`Mult/Chirp.lean`), exactly.

## Program (`pmParams rg uN oT oS us`)

The table machine has `pmNV = 40` variables on the injective register layout `rg`, in words of
`pmW n = 4 · size n + 32` bits (`pmW_ge`: at least `4 b + 32`).

1. **Prelude** (`pmPrelude`). `sxBinConv` turns the unary register `uN` (`n` symbols, kept) into the
   canonical binary digits of `n` on variable `0`, `binSyms (size n) n` (`pm_sxBits_syms`), in at
   most `16 n + 4` steps. Then (`pmPrelude2`, `pm_prelude2_runs`) `wr` gets `4 · size n + 32` ticks
   (`umul`, a constant push), `wn` a copy, variable `0` is widened to `pmW n` bits (`bwiden`), and
   variables `1, …, 39` are set to `0` (`pmZeroList`): the layout carries the state `pmSt0 A n`
   (`pm_prelude_exec`), within `pmPreCost n = 4 size n + 172 pmW n + 200` more steps.
2. **`pmCode1`** (`pmHost`, `pm_host_runs`): all parameters, the axis lengths emitted as pair
   symbols, then moved onto `oT` through `pmBitOfPair`, which gives the stream `pmTStream` of
   `pmW n`-bit words `t_0, …, t_{d-1}` (`pm_TList_map`).
3. **`pmCode2`**: the source lengths onto `oS` as `pmSStream` (`pm_SList_map`).
4. **Unary copies** (`pmUnary`, `pm_unary_exec`): for each `(i, o) ∈ us`, `toUnary` pushes
   `pmVals n i` ticks onto `o`, in at most `W (4 x + 11) + 2 x + 6` steps for the value `x`.

## Result

`pmParams_exec`: exact final contents of every register (variables `binSyms (pmW n) (pmVals n i)`,
width registers `pmW n` ticks, `acc` and scratch empty, the two streams and the unary copies on
top of their registers, every other register unchanged), within `pmCost n us` steps.
`pmCost_le`: `pmCost n us ≤ 16 n + (2^23) (size n + 5)^4 + pmUnaryCost (pmW n) (pmVals n) us`.
The unary copies of the parameters bounded by a polynomial in `b` cost `poly(log n)`; those of
`T` and `r` cost `O(n)` (`pm_W_T_le`: `pmW n · T ≤ (2^9) n`, `pm_r_le_T`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Moduli


/-! ### Binary words -/

theorem pm_map_bitSymbol {A : ℕ} :
    ∀ bs : List Bool, bs.map (bitSymbol (a := A)) = binSyms bs.length (Counter.value bs)
  | [] => by simp [binSyms]
  | b :: bs => by
    rw [List.map_cons, List.length_cons, binSyms, List.ofFn_succ, pm_map_bitSymbol bs, binSyms]
    have hv : Counter.value (b :: bs) = (if b then 1 else 0) + 2 * Counter.value bs := rfl
    congr 1
    · congr 1
      rw [hv]
      cases b <;> simp [Nat.testBit_zero]
    · congr 1
      funext t
      congr 1
      rw [hv, Fin.val_succ, Nat.testBit_succ]
      congr 1
      cases b <;> simp; omega

theorem pm_value_ge : ∀ bs : List Bool, bs.getLast? = some true →
    2 ^ (bs.length - 1) ≤ Counter.value bs
  | [], h => by simp at h
  | [b], h => by
    simp at h
    subst h
    simp [Counter.value]
  | b :: c :: rest, h => by
    have ih := pm_value_ge (c :: rest) (by simpa using h)
    have hv : Counter.value (b :: c :: rest) = (if b then 1 else 0) + 2 * Counter.value (c :: rest) :=
      rfl
    rw [hv]
    simp only [List.length_cons] at ih ⊢
    rw [show rest.length + 1 + 1 - 1 = (rest.length + 1 - 1) + 1 by omega, pow_succ]
    split_ifs <;> omega

/-- The canonical binary digits of `n` have `Nat.size n` digits. -/
theorem pm_length_sxBits (n : ℕ) : (sxBits n).length = Nat.size n := by
  have h1 := lt_two_pow_length_sxBits n
  apply le_antisymm
  · rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [sxBits, GrowingCounterData.advance]
    · have hc := canonical_sxBits n
      have hne := sxBits_ne_nil h
      have hlast : (sxBits n).getLast? = some true := hc.resolve_left hne
      have h2 := pm_value_ge _ hlast
      rw [value_sxBits] at h2
      have hl : 0 < (sxBits n).length := List.length_pos_iff.2 hne
      have := Nat.lt_size.2 h2
      omega
  · exact Nat.size_le.2 h1

theorem pm_sxBits_syms {A : ℕ} (n : ℕ) :
    (sxBits n).map (bitSymbol (a := A)) = binSyms (Nat.size n) n := by
  rw [pm_map_bitSymbol, value_sxBits, pm_length_sxBits]

theorem pm_b_le_size (n : ℕ) : b n ≤ Nat.size n :=
  (Nat.clog_le_iff_le_pow one_lt_two).2 (Nat.size_le.1 le_rfl).le

/-- The word width of the parameter machine: `4 · size n + 32` bits. -/
def pmW (n : ℕ) : ℕ := 4 * Nat.size n + 32

theorem pmW_ge (n : ℕ) : 4 * b n + 32 ≤ pmW n := by
  have := pm_b_le_size n; unfold pmW; omega

theorem pm_n_lt_W (n : ℕ) : n < 2 ^ pmW n :=
  (Nat.size_le.1 le_rfl).trans_le (pm_two_pow_le (by unfold pmW; omega))

/-! ### Streams -/

/-- The bit of the real part of a pair symbol, as a bit symbol. -/
def pmBitOfPair {A : ℕ} (x : Fin (A + 4)) : Fin (A + 4) := bitSymbol (pairRe x)

theorem pm_map_tblPairs {A : ℕ} (hA : 4 ≤ A) (W x : ℕ) :
    (tblPairs A W x x).map pmBitOfPair = binSyms W x := by
  simp only [tblPairs, coeffSyms, List.map_ofFn, binSyms]
  congr 1
  funext t
  simp only [Function.comp_apply, pmBitOfPair, pairRe_pairSym hA, ZMod.val_natCast,
    Nat.testBit_mod_two_pow]
  simp [t.isLt]

theorem pm_flatMap_range {β : Type} (g : ℕ → List β) (m : ℕ) :
    (List.range m).flatMap g = (List.ofFn fun i : Fin m => g i).flatten := by
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.flatMap_map]
  simp [List.flatMap_def]

/-- The axis lengths `t_0, …, t_{d-1}` as `W`-bit words, `t_0` first, each least significant
bit first. -/
def pmTStream (A W n : ℕ) : List (Fin (A + 4)) :=
  (List.ofFn fun i : Fin (d n) => binSyms W (t n i)).flatten

/-- The source lengths `s_0, …, s_{d-1}` as `W`-bit words, `s_0` first. -/
def pmSStream (A W n : ℕ) : List (Fin (A + 4)) :=
  (List.ofFn fun i : Fin (d n) => binSyms W (s n i)).flatten

theorem pm_TList_map {A : ℕ} (hA : 4 ≤ A) (W n : ℕ) :
    (pmTList A W n).map pmBitOfPair = pmTStream A W n := by
  rw [pmTList, pmEmitList, List.map_flatMap, pmTStream]
  simp only [pm_map_tblPairs hA]
  rw [pm_flatMap_range]
  simp only [pmTv_eq]

theorem pm_SList_map {A : ℕ} (hA : 4 ≤ A) (W n : ℕ) :
    (pmSList A W n).map pmBitOfPair = pmSStream A W n := by
  rw [pmSList, pmEmitList, List.map_flatMap, pmSStream]
  simp only [pm_map_tblPairs hA]
  rw [pm_flatMap_range]
  rfl

theorem pm_length_TList (A W n : ℕ) : (pmTList A W n).length = d n * W := by
  simp [pmTList, pmEmitList, List.length_flatMap]

theorem pm_length_SList (A W n : ℕ) : (pmSList A W n).length = d n * W := by
  simp [pmSList, pmEmitList, List.length_flatMap]

/-! ### Layout primitives -/

section Prims

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {m : ℕ}
  {rg : TblR m → Fin T}

theorem pm_umul_runs (hrg : Function.Injective rg) (c : ℕ) {a b t : TblR m} (hab : a ≠ b)
    (hat : a ≠ t) (hbt : b ≠ t) (ρ : TblR m → List (Fin (A + 4))) (ht : ρ t = []) :
    tblRuns body rg (umul c (rg a) (rg b) (rg t)) ρ
      (Function.update ρ b (List.replicate (c * (ρ a).length) tick ++ ρ b))
      (4 * (ρ a).length + 4) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := umul_exec body c (hrg.ne hab) (hrg.ne hat) (hrg.ne hbt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [tbl_holds_upd hrg hS b, hS, hS]

theorem pm_ucopy_runs (hrg : Function.Injective rg) {a b t : TblR m} (hab : a ≠ b)
    (hat : a ≠ t) (hbt : b ≠ t) (ρ : TblR m → List (Fin (A + 4))) (ht : ρ t = []) :
    tblRuns body rg (ucopy (rg a) (rg b) (rg t)) ρ
      (Function.update ρ b (List.replicate (ρ a).length tick ++ ρ b)) (4 * (ρ a).length + 4) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := ucopy_exec body (hrg.ne hab) (hrg.ne hat) (hrg.ne hbt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [tbl_holds_upd hrg hS b, hS, hS]

theorem pm_push_runs (hrg : Function.Injective rg) (b : TblR m) (k : ℕ)
    (ρ : TblR m → List (Fin (A + 4))) :
    tblRuns body rg (.act (pushN (rg b) (fun _ => tick) k .done)) ρ
      (Function.update ρ b (List.replicate k tick ++ ρ b)) 1 := by
  intro v S hS
  have he := Exec.act (body := body) (pushN (rg b) (fun _ => tick) k .done) (mk v S)
  rw [pushN_run, run_done] at he
  refine ⟨v, _, 1, rfl, le_rfl, he, ?_, ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [tbl_holds_upd hrg hS b, hS]

theorem pm_bwiden_runs (hrg : Function.Injective rg) {a wR cnt t₁ t₂ : TblR m}
    (hd : [a, wR, cnt, t₁, t₂].Nodup) {L W x : ℕ} (hLW : L ≤ W) (hx : x < 2 ^ L)
    (ρ : TblR m → List (Fin (A + 4))) (ha : ρ a = binSyms L x) (hw : (ρ wR).length = W)
    (hc : ρ cnt = []) (ht₁ : ρ t₁ = []) (ht₂ : ρ t₂ = []) :
    tblRuns body rg (bwiden (rg a) (rg wR) (rg cnt) (rg t₁) (rg t₂)) ρ
      (Function.update ρ a (binSyms W x)) (12 * W + 18) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := bwiden_exec body (tbl_nodup hrg hd) hLW hx v S (by rw [hS, ha])
    (by rw [hS, hw]) (by rw [hS, hc]) (by rw [hS, ht₁]) (by rw [hS, ht₂])
  refine ⟨v', _, _, hu, le_rfl, he, ?_, ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [tbl_holds_upd hrg hS a]

end Prims

/-! ### Zeroing the variables -/

section Zero

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U}
  {rg : TblR pmNV → Fin T}

/-- `bzero` on the variables of `l`, through `z 0`. -/
def pmZeroList (rg : TblR pmNV → Fin T) : List (Fin pmNV) → Pr P T Q A U
  | [] => .act .done
  | i :: l => .seq (bzero (rg .wr) (rg (.v i)) (rg (.z 0))) (pmZeroList rg l)

/-- The register file after zeroing the variables of `l`. -/
def pmZeroed (W : ℕ) (l : List (Fin pmNV)) (ρ : TblR pmNV → List (Fin (A + 4))) :
    TblR pmNV → List (Fin (A + 4)) :=
  l.foldl (fun ρ i => Function.update ρ (.v i) (binSyms W 0 ++ ρ (.v i))) ρ

theorem pm_zeroList_runs (hrg : Function.Injective rg) (W : ℕ) :
    ∀ (l : List (Fin pmNV)) (ρ : TblR pmNV → List (Fin (A + 4))), (ρ .wr).length = W →
      ρ (.z 0) = [] →
      tblRuns body rg (pmZeroList rg l) ρ (pmZeroed W l ρ) (l.length * (4 * W + 4) + 1)
  | [], ρ, _, _ => by
    intro v S hS
    have he := Exec.act (body := body) .done (mk v S)
    rw [run_done] at he
    exact ⟨v, S, 1, rfl, by simp, he, hS, tblFr.refl S⟩
  | i :: l, ρ, hw, hz => by
    have h₁ := tbl_bzero_runs (body := body) hrg (wR := .wr) (c := .v i) (t := .z 0)
      (by simp) ρ hz
    rw [hw] at h₁
    have h₂ := pm_zeroList_runs hrg W l
      (Function.update ρ (.v i) (binSyms W 0 ++ ρ (.v i))) (by simp [hw]) (by simp [hz])
    refine (h₁.seq h₂).mono ?_
    simp only [List.length_cons]
    ring_nf
    omega

theorem pm_zeroed_apply (W : ℕ) :
    ∀ (l : List (Fin pmNV)) (ρ : TblR pmNV → List (Fin (A + 4))) (r : TblR pmNV), l.Nodup →
      pmZeroed W l ρ r = if ∃ i ∈ l, r = .v i then binSyms W 0 ++ ρ r else ρ r
  | [], ρ, r, _ => by simp [pmZeroed]
  | i :: l, ρ, r, hl => by
    rw [pmZeroed, List.foldl_cons, ← pmZeroed, pm_zeroed_apply W l _ r (List.nodup_cons.1 hl).2]
    have hi := (List.nodup_cons.1 hl).1
    by_cases hr : r = .v i
    · subst hr
      have : ¬ ∃ j ∈ l, (TblR.v i : TblR pmNV) = .v j := by
        rintro ⟨j, hj, he⟩
        cases he
        exact hi hj
      rw [ite_eq_right this, ite_eq_left ⟨i, List.mem_cons_self, rfl⟩]
      simp
    · rw [Function.update_of_ne hr]
      by_cases hex : ∃ j ∈ l, r = .v j
      · have : ∃ j ∈ i :: l, r = .v j := by
          obtain ⟨j, hj, he⟩ := hex; exact ⟨j, List.mem_cons_of_mem _ hj, he⟩
        rw [ite_eq_left hex, ite_eq_left this]
      · have : ¬ ∃ j ∈ i :: l, r = .v j := by
          rintro ⟨j, hj, he⟩
          rcases List.mem_cons.1 hj with h | h
          · subst h; exact hr he
          · exact hex ⟨j, h, he⟩
        rw [ite_eq_right hex, ite_eq_right this]

/-- The variables `1, …, 39`. -/
def pmZeroIdx : List (Fin pmNV) := (List.finRange 39).map Fin.succ

theorem pm_mem_zeroIdx (i : Fin pmNV) : i ∈ pmZeroIdx ↔ i ≠ 0 := by
  unfold pmZeroIdx
  constructor
  · intro h
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 h
    exact Fin.succ_ne_zero j
  · intro h
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 h
    exact List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩

theorem pm_nodup_zeroIdx : pmZeroIdx.Nodup :=
  (List.nodup_finRange 39).map (Fin.succ_injective _)

theorem pm_length_zeroIdx : pmZeroIdx.length = 39 := by simp [pmZeroIdx]

end Zero

/-! ### The prelude -/

section Prelude

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U}
  {rg : TblR pmNV → Fin T}

/-- The prelude after the conversion of `n` to binary: the width registers `wr`, `wn` get
`pmW n = 4 · size n + 32` ticks, variable `0` is widened to `pmW n` bits, and the other variables
are set to `0`. -/
def pmPrelude2 (rg : TblR pmNV → Fin T) : Pr P T Q A U :=
  .seq (umul 4 (rg (.v 0)) (rg .wr) (rg (.z 0)))
    (.seq (.act (pushN (rg .wr) (fun _ => tick) 32 .done))
      (.seq (ucopy (rg .wr) (rg .wn) (rg (.z 0)))
        (.seq (bwiden (rg (.v 0)) (rg .wr) (rg (.z 0)) (rg (.z 1)) (rg (.z 2)))
          (pmZeroList rg pmZeroIdx))))

/-- The prelude: `n` from the unary register `uN` to binary (`sxBinConv`), then `pmPrelude2`. -/
def pmPrelude (rg : TblR pmNV → Fin T) (uN : Fin T) : Pr P T Q A U :=
  .seq (sxBinConv uN (rg (.v 0)) (rg (.z 0)) (rg (.z 1))) (pmPrelude2 rg)

/-- The initial state of the parameter programs: `n` in variable `0`, every other variable `0`. -/
def pmSt0 (A n : ℕ) : TblSt pmNV A := ⟨Function.update (fun _ => 0) 0 n, []⟩

/-- `W` ticks: the contents of the width registers. -/
def pmTicks (A W : ℕ) : List (Fin (A + 4)) := List.replicate W tick

/-- The steps of `pmPrelude2`. -/
def pmPreCost (n : ℕ) : ℕ := 4 * Nat.size n + 172 * pmW n + 200

theorem pm_prelude2_runs (hrg : Function.Injective rg) (n : ℕ) :
    tblRuns body rg (pmPrelude2 rg)
      (Function.update (fun _ => []) (.v 0) (binSyms (Nat.size n) n))
      (tblRho (pmW n) (pmTicks A (pmW n)) (pmTicks A (pmW n)) (pmSt0 A n)) (pmPreCost n) := by
  set L := Nat.size n
  set W := pmW n with hW
  have hLW : L ≤ W := by rw [hW]; unfold pmW; omega
  have hWL : W = 4 * L + 32 := rfl
  set ρ₁ : TblR pmNV → List (Fin (A + 4)) := Function.update (fun _ => []) (.v 0) (binSyms L n)
  have ha := pm_umul_runs (body := body) hrg 4 (a := .v 0) (b := .wr) (t := .z 0) (by decide)
    (by decide) (by decide) ρ₁ (by simp [ρ₁])
  set ρ₂ := Function.update ρ₁ .wr (List.replicate (4 * (ρ₁ (.v 0)).length) tick ++ ρ₁ .wr)
  have hb := pm_push_runs (body := body) hrg .wr 32 ρ₂
  set ρ₃ := Function.update ρ₂ .wr (List.replicate 32 tick ++ ρ₂ .wr)
  have h3w : ρ₃ .wr = List.replicate W tick := by
    have e1 : ρ₂ .wr = List.replicate (4 * L) tick := by simp [ρ₂, ρ₁]
    simp only [ρ₃, Function.update_self, e1, List.replicate_append_replicate, hWL]
    congr 1
    omega
  have hc := pm_ucopy_runs (body := body) hrg (a := .wr) (b := .wn) (t := .z 0) (by decide)
    (by decide) (by decide) ρ₃ (by simp [ρ₃, ρ₂, ρ₁])
  set ρ₄ := Function.update ρ₃ .wn (List.replicate (ρ₃ .wr).length tick ++ ρ₃ .wn)
  have hd := pm_bwiden_runs (body := body) hrg (a := .v 0) (wR := .wr) (cnt := .z 0) (t₁ := .z 1)
    (t₂ := .z 2) (by decide) hLW (Nat.size_le.1 le_rfl) ρ₄ (by simp [ρ₄, ρ₃, ρ₂, ρ₁])
    (by simp [ρ₄, h3w]) (by simp [ρ₄, ρ₃, ρ₂, ρ₁]) (by simp [ρ₄, ρ₃, ρ₂, ρ₁])
    (by simp [ρ₄, ρ₃, ρ₂, ρ₁])
  set ρ₅ := Function.update ρ₄ (.v 0) (binSyms W n)
  have h4w : ρ₄ .wr = List.replicate W tick := by
    simp only [ρ₄]; rw [Function.update_of_ne (by decide), h3w]
  have h4n : ρ₄ .wn = List.replicate W tick := by
    have : ρ₃ .wn = [] := by simp [ρ₃, ρ₂, ρ₁]
    simp only [ρ₄, Function.update_self, h3w, List.length_replicate, this, List.append_nil]
  have h1v : (ρ₁ (.v 0)).length = L := by simp [ρ₁]
  have he := pm_zeroList_runs (body := body) hrg W pmZeroIdx ρ₅ (by simp [ρ₅, ρ₄, h3w])
    (by simp [ρ₅, ρ₄, ρ₃, ρ₂, ρ₁])
  refine (ha.seq (hb.seq (hc.seq (hd.seq he)))).congr ?_ |>.mono ?_
  · funext r
    rw [pm_zeroed_apply W _ _ _ pm_nodup_zeroIdx]
    rcases r with i | _ | _ | _ | j
    · by_cases hi : i = 0
      · subst hi
        have : ¬ ∃ j ∈ pmZeroIdx, (TblR.v 0 : TblR pmNV) = .v j := by
          rintro ⟨j, hj, he⟩
          cases he
          exact (pm_mem_zeroIdx 0).1 hj rfl
        rw [ite_eq_right this]
        simp [ρ₅, tblRho, pmSt0]
      · have : ∃ j ∈ pmZeroIdx, (TblR.v i : TblR pmNV) = .v j :=
          ⟨i, (pm_mem_zeroIdx i).2 hi, rfl⟩
        rw [ite_eq_left this]
        simp [ρ₅, ρ₄, ρ₃, ρ₂, ρ₁, tblRho, pmSt0, hi]
    · rw [ite_eq_right (show ¬ ∃ j ∈ pmZeroIdx, (TblR.wr : TblR pmNV) = .v j by simp)]
      simp only [ρ₅]
      rw [Function.update_of_ne (by decide), h4w]
      rfl
    · rw [ite_eq_right (show ¬ ∃ j ∈ pmZeroIdx, (TblR.wn : TblR pmNV) = .v j by simp)]
      simp only [ρ₅]
      rw [Function.update_of_ne (by decide), h4n]
      rfl
    · simp [ρ₅, ρ₄, ρ₃, ρ₂, ρ₁, tblRho, pmSt0]
    · simp [ρ₅, ρ₄, ρ₃, ρ₂, ρ₁, tblRho]
  · rw [h1v, h3w, List.length_replicate, pm_length_zeroIdx]
    unfold pmPreCost
    rw [← hW]
    omega

theorem pm_prelude_exec (hrg : Function.Injective rg) {uN : Fin T} (huN : ∀ r, rg r ≠ uN)
    (n : ℕ) (v : HS T Q A U) (S : Stacks T A) (hlen : (S.R uN).length = n)
    (hS : ∀ r, S.R (rg r) = []) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ 16 * n + 4 + pmPreCost n ∧
      Exec body (pmPrelude rg uN) (mk v S) m (mk v' S') ∧
      tblHolds rg S' (tblRho (pmW n) (pmTicks A (pmW n)) (pmTicks A (pmW n)) (pmSt0 A n)) ∧
      tblFr rg S S' := by
  have hreg : [uN, rg (.v 0), rg (.z 0), rg (.z 1)].Nodup := by
    have h := tbl_nodup hrg (l := [.v 0, .z 0, .z 1]) (by decide)
    simp only [List.map_cons, List.map_nil] at h
    exact List.nodup_cons.2 ⟨by simp [Ne.symm (huN _)], h⟩
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := sxBinConv_exec body hreg v S (hS _) (hS _) (hS _)
  rw [hlen, pm_sxBits_syms] at he₁
  rw [hlen] at hm₁
  set S₁ : Stacks T A := { S with R := Function.update S.R (rg (.v 0)) (binSyms (Nat.size n) n) }
  have hS₁ : tblHolds rg S₁ (Function.update (fun _ => []) (.v 0) (binSyms (Nat.size n) n)) :=
    tbl_holds_upd hrg (ρ := fun _ => []) hS (.v 0) _
  obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hf₂⟩ := pm_prelude2_runs (body := body) hrg n v₁ S₁ hS₁
  refine ⟨v₂, S₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hS₂, ?_⟩
  exact (show tblFr rg S S₁ from ⟨rfl, rfl, rfl, fun k hk => tbl_upd_off _ _ _ hk⟩).trans hf₂

end Prelude

/-! ### A table program and a stream move -/

section Host

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {m : ℕ}
  {rg : TblR m → Fin T}

/-- `tblHost` with a symbol map: the program `c`, then `acc` moved onto `out` through `f`. -/
def pmHost (rg : TblR m → Fin T) (c : TblCode m) (out : Fin T) (f : Fin (A + 4) → Fin (A + 4)) :
    Pr P T Q A U :=
  .seq (tblCompile rg c) (moveR (rg .acc) out f)

/-- `tblHost_runs` with a symbol map `f`; the final values stay below `2 ^ W`. -/
theorem pm_host_runs (hrg : Function.Injective rg) {out : Fin T} (hout : ∀ r, rg r ≠ out)
    (f : Fin (A + 4) → Fin (A + 4)) {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W)
    (hnl : nl.length = w) (hw : w ≤ W) {c : TblCode m} {st : TblSt m A}
    {Post : TblSt m A → Prop} {K : ℕ} (h : TblDo A W w c st Post K)
    (hst : ∀ j, st.val j < 2 ^ W) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m st', Post st' ∧ (∀ j, st'.val j < 2 ^ W) ∧ v'.user = v.user ∧
      m ≤ K * tblC W w + 2 * st'.acc.length + 2 ∧
      Exec body (pmHost rg c out f) (mk v S) m (mk v' S') ∧
      S'.R out = (st'.acc.map f).reverse ++ S.R out ∧
      tblHolds rg S' (tblRho W wl nl ⟨st'.val, []⟩) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧
      S'.L = S.L ∧ ∀ k, k ≠ out → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  obtain ⟨st', k, hb, hp, hk⟩ := h
  have hr := (tblCompile_runs (body := body) hrg wl nl hwl hnl hw hb hst).mono
    (Nat.mul_le_mul_right (tblC W w) hk)
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ := hr v S hS
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (rg .acc) out (hout .acc) f v₁ S₁
  have hacc₁ : S₁.R (rg .acc) = st'.acc := hS₁ .acc
  refine ⟨v₂, _, _, st', hp, hb.lt hst, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, ?_, ?_, hf₁.1,
    hf₁.2.1, hf₁.2.2.1, fun k hk1 hk2 => ?_⟩
  · rw [hacc₁]; omega
  · simp only [movedR, Function.update_self, hacc₁]
    rw [hf₁.2.2.2 out hout]
  · intro r
    simp only [movedR]
    rw [Function.update_of_ne (hout r)]
    by_cases hr : r = .acc
    · subst hr; simp [tblRho]
    · rw [Function.update_of_ne (hrg.ne hr), hS₁ r]
      cases r <;> simp_all [tblRho]
  · simp only [movedR]
    rw [Function.update_of_ne hk1, Function.update_of_ne (Ne.symm (hk2 .acc)), hf₁.2.2.2 k hk2]

end Host

/-! ### Unary outputs -/

section Unary

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U}
  {rg : TblR pmNV → Fin T}

/-- `toUnary` from the variables onto output registers: for each `x ∈ us`, the register `x.2`
gains `val x.1` ticks (through the scratch registers `z 0`, `z 1`, `z 2`). -/
def pmUnary (rg : TblR pmNV → Fin T) : List (Fin pmNV × Fin T) → Pr P T Q A U
  | [] => .act .done
  | x :: l => .seq (toUnary (rg (.v x.1)) x.2 (rg (.z 0)) (rg (.z 1)) (rg (.z 2))) (pmUnary rg l)

/-- The steps of `pmUnary`: `W (4 x + 11) + 2 x + 6` per value `x`. -/
def pmUnaryCost {α : Type} (W : ℕ) (val : Fin pmNV → ℕ) (us : List (Fin pmNV × α)) : ℕ :=
  (us.map fun x => W * (4 * val x.1 + 11) + 2 * val x.1 + 6).sum + 1

theorem pm_unary_exec (hrg : Function.Injective rg) {W : ℕ} (wl nl : List (Fin (A + 4)))
    (val : Fin pmNV → ℕ) (hval : ∀ j, val j < 2 ^ W) :
    ∀ (us : List (Fin pmNV × Fin T)) (v : HS T Q A U) (S : Stacks T A),
      (∀ x ∈ us, ∀ r, rg r ≠ x.2) → (us.map Prod.snd).Nodup →
      tblHolds rg S (tblRho W wl nl ⟨val, []⟩) →
      ∃ v' R' m, v'.user = v.user ∧ m ≤ pmUnaryCost W val us ∧
        Exec body (pmUnary rg us) (mk v S) m (mk v' { S with R := R' }) ∧
        (∀ x ∈ us, R' x.2 = List.replicate (val x.1) tick ++ S.R x.2) ∧
        (∀ k, (∀ x ∈ us, x.2 ≠ k) → R' k = S.R k)
  | [], v, S, _, _, _ => by
    have he := Exec.act (body := body) .done (mk v S)
    rw [run_done] at he
    exact ⟨v, S.R, 1, rfl, by simp [pmUnaryCost], he, by simp, fun _ _ => rfl⟩
  | x :: l, v, S, hus, hnd, hS => by
    have hx : ∀ r, rg r ≠ x.2 := hus x List.mem_cons_self
    have hreg : [rg (.v x.1), x.2, rg (.z 0), rg (.z 1), rg (.z 2)].Nodup := by
      have h3 : [rg (.z 0), rg (.z 1), rg (.z 2)].Nodup := by
        have := tbl_nodup hrg (l := [.z 0, .z 1, .z 2]) (by decide)
        simpa using this
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, h3⟩⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hx _, hrg.ne (by simp), hrg.ne (by simp), hrg.ne (by simp)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun h => hx _ h.symm, fun h => hx _ h.symm, fun h => hx _ h.symm⟩
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := toUnary_exec body hreg (hval x.1) v S
      (by rw [hS]; rfl) (by rw [hS]; rfl) (by rw [hS]; rfl) (by rw [hS]; rfl)
    set S₁ : Stacks T A :=
      { S with R := Function.update S.R x.2 (List.replicate (val x.1) tick ++ S.R x.2) }
    have hS₁ : tblHolds rg S₁ (tblRho W wl nl ⟨val, []⟩) := by
      intro r
      simp only [S₁]
      rw [Function.update_of_ne (hx r), hS]
    have hnd' := List.nodup_cons.1 hnd
    obtain ⟨v₂, R₂, m₂, hu₂, hm₂, he₂, hR₂, hR₂'⟩ :=
      pm_unary_exec hrg wl nl val hval l v₁ S₁ (fun y hy => hus y (List.mem_cons_of_mem _ hy))
        hnd'.2 hS₁
    have hxl : ∀ y ∈ l, y.2 ≠ x.2 := fun y hy h => hnd'.1 (List.mem_map.2 ⟨y, hy, h⟩)
    refine ⟨v₂, R₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, ?_, ?_⟩
    · simp only [pmUnaryCost, List.map_cons, List.sum_cons] at hm₂ ⊢
      omega
    · intro y hy
      rcases List.mem_cons.1 hy with h | h
      · subst h
        rw [hR₂' _ hxl]
        simp [S₁]
      · rw [hR₂ y h]
        simp [S₁, Function.update_of_ne (hxl y h)]
    · intro k hk
      rw [hR₂' k (fun y hy => hk y (List.mem_cons_of_mem _ hy))]
      simp [S₁, Function.update_of_ne (Ne.symm (hk x List.mem_cons_self))]

end Unary

/-! ### The parameter machine -/

section Machine

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U}
  {rg : TblR pmNV → Fin T}

/-- **The parameter machine.** The prelude (`n` from the unary register `uN` to binary, the
width registers, the zeroed variables), `pmCode1` with the axis lengths moved onto `oT`, `pmCode2`
with the source lengths moved onto `oS`, and the unary copies `pmUnary rg us`. -/
def pmParams (rg : TblR pmNV → Fin T) (uN oT oS : Fin T) (us : List (Fin pmNV × Fin T)) :
    Pr P T Q A U :=
  .seq (pmPrelude rg uN) (.seq (pmHost rg pmCode1 oT pmBitOfPair)
    (.seq (pmHost rg pmCode2 oS pmBitOfPair) (pmUnary rg us)))

/-- The step bound of `pmParams`. -/
def pmCost {α : Type} (n : ℕ) (us : List (Fin pmNV × α)) : ℕ :=
  16 * n + 4 + pmPreCost n + (pmAtoms1 n + pmAtoms2 n) * tblC (pmW n) (pmW n) +
    4 * d n * pmW n + 4 + pmUnaryCost (pmW n) (pmVals n) us

theorem pm_st0_lt (n : ℕ) (j : Fin pmNV) : (pmSt0 A n).val j < 2 ^ pmW n := by
  unfold pmSt0
  by_cases h : j = 0
  · subst h; simpa using pm_n_lt_W n
  · simp [Function.update_of_ne h]

theorem pm_st0_F (n : ℕ) : PmF n 1 [] (pmSt0 A n) := by
  refine ⟨rfl, fun i hi => ?_⟩
  obtain ⟨k, hk⟩ := i
  obtain rfl : k = 0 := by simpa using hi
  rfl

/-- **The parameter machine.** From a register `uN` holding `n ≥ 2` symbols (any) and an empty
layout `rg`, `pmParams` ends, within `pmCost n us` steps, with:

* variable `i` holding `binSyms (pmW n) (pmVals n i)`, the value table of `Fast/ParamProg.lean`
  (`pm_b_eq`, `pm_d_eq`, …), in words of `pmW n = 4 · size n + 32` bits;
* `wr` and `wn` holding `pmW n` ticks, `acc` and the scratch registers empty;
* `oT` and `oS` gaining the streams `pmTStream` (`t_0, …, t_{d-1}`) and `pmSStream`
  (`s_0, …, s_{d-1}`) of `pmW n`-bit words on top;
* each `x.2` (`x ∈ us`) gaining `pmVals n x.1` ticks on top;
* every other register, the input, output and left stacks unchanged, `user` kept. -/
theorem pmParams_exec (hA : 4 ≤ A) (hrg : Function.Injective rg) {uN oT oS : Fin T}
    (huN : ∀ r, rg r ≠ uN) (hoT : ∀ r, rg r ≠ oT) (hoS : ∀ r, rg r ≠ oS) (hTS : oT ≠ oS)
    (us : List (Fin pmNV × Fin T)) (hus : ∀ x ∈ us, ∀ r, rg r ≠ x.2)
    (husT : ∀ x ∈ us, x.2 ≠ oT) (husS : ∀ x ∈ us, x.2 ≠ oS) (hnd : (us.map Prod.snd).Nodup)
    {n : ℕ} (hB : Big n) (v : HS T Q A U) (S : Stacks T A) (hlen : (S.R uN).length = n)
    (hS : ∀ r, S.R (rg r) = []) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ pmCost n us ∧
      Exec body (pmParams rg uN oT oS us) (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i, S'.R (rg (.v i)) = binSyms (pmW n) (pmVals n i)) ∧
      S'.R (rg .wr) = pmTicks A (pmW n) ∧ S'.R (rg .wn) = pmTicks A (pmW n) ∧
      S'.R (rg .acc) = [] ∧ (∀ j, S'.R (rg (.z j)) = []) ∧
      S'.R oT = pmTStream A (pmW n) n ++ S.R oT ∧ S'.R oS = pmSStream A (pmW n) n ++ S.R oS ∧
      (∀ x ∈ us, S'.R x.2 = List.replicate (pmVals n x.1) tick ++ S.R x.2) ∧
      (∀ k, (∀ r, rg r ≠ k) → k ≠ oT → k ≠ oS → (∀ x ∈ us, x.2 ≠ k) → S'.R k = S.R k) := by
  have hn : 2 ≤ n := hB.1
  set W := pmW n with hW
  have hW' : 4 * b n + 32 ≤ W := pmW_ge n
  have hwl : (pmTicks A W).length = W := by simp [pmTicks]
  -- the prelude
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hS₁, hf₁⟩ := pm_prelude_exec (body := body) hrg huN n v S hlen hS
  -- the first program
  obtain ⟨v₂, S₂, m₂, st₁, ⟨hv₁, ha₁⟩, hlt₁, hu₂, hm₂, he₂, hT₂, hS₂, hi₂, ho₂, hL₂, hk₂⟩ :=
    pm_host_runs (body := body) hrg hoT pmBitOfPair (pmTicks A W) (pmTicks A W) hwl hwl le_rfl
      (pmCode1_do (w := W) hB hW' (pmSt0 A n) (pm_st0_F n)) (pm_st0_lt n) v₁ S₁ hS₁
  rw [hv₁] at hS₂ hlt₁
  -- the second program
  obtain ⟨v₃, S₃, m₃, st₂, ⟨hv₂, ha₂⟩, hlt₂, hu₃, hm₃, he₃, hT₃, hS₃, hi₃, ho₃, hL₃, hk₃⟩ :=
    pm_host_runs (body := body) hrg hoS pmBitOfPair (pmTicks A W) (pmTicks A W) hwl hwl le_rfl
      (pmCode2_do (w := W) hn hW' ⟨pmVals n, []⟩ ⟨rfl, fun i _ => rfl⟩) hlt₁ v₂ S₂ hS₂
  rw [hv₂] at hS₃
  -- the unary copies
  obtain ⟨v₄, R₄, m₄, hu₄, hm₄, he₄, hR₄, hR₄'⟩ :=
    pm_unary_exec (body := body) hrg (pmTicks A W) (pmTicks A W) (pmVals n) hlt₁ us v₃ S₃ hus hnd
      hS₃
  have hlay : ∀ r, R₄ (rg r) = S₃.R (rg r) := fun r => hR₄' _ (fun x hx => (hus x hx r).symm)
  refine ⟨v₄, { S₃ with R := R₄ }, m₁ + (m₂ + (m₃ + m₄)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    ?_, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [ha₁, List.length_append, List.length_reverse, pm_length_TList, List.length_nil] at hm₂
    rw [ha₂, List.length_append, List.length_reverse, pm_length_SList, List.length_nil] at hm₃
    unfold pmCost
    rw [← hW]
    have e : 4 * d n * W = 2 * (d n * W) + 2 * (d n * W) := by ring
    nlinarith
  · simp only; rw [hi₃, hi₂, hf₁.1]
  · simp only; rw [ho₃, ho₂, hf₁.2.1]
  · simp only; rw [hL₃, hL₂, hf₁.2.2.1]
  · intro i; simp only; rw [hlay, hS₃]; rfl
  · simp only; rw [hlay, hS₃]; rfl
  · simp only; rw [hlay, hS₃]; rfl
  · simp only; rw [hlay, hS₃]; rfl
  · intro j; simp only; rw [hlay, hS₃]; rfl
  · simp only
    rw [hR₄' _ (fun x hx => husT x hx), hk₃ oT hTS hoT, hT₂, ha₁, List.append_nil, List.map_reverse,
      List.reverse_reverse, pm_TList_map hA, hf₁.2.2.2 oT hoT]
  · simp only
    rw [hR₄' _ (fun x hx => husS x hx), hT₃, ha₂, List.append_nil, List.map_reverse,
      List.reverse_reverse, pm_SList_map hA, hk₂ oS (Ne.symm hTS) hoS, hf₁.2.2.2 oS hoS]
  · intro x hx
    simp only
    rw [hR₄ x hx, hk₃ x.2 (husS x hx) (hus x hx), hk₂ x.2 (husT x hx) (hus x hx),
      hf₁.2.2.2 x.2 (hus x hx)]
  · intro k hk hkT hkS hku
    simp only
    rw [hR₄' k hku, hk₃ k hkS hk, hk₂ k hkT hk, hf₁.2.2.2 k hk]

end Machine

/-! ### Cost -/

theorem pm_size_le {n : ℕ} : Nat.size n ≤ b n + 1 :=
  Nat.size_le.2 ((le_two_pow_b n).trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)))

/-- `pmCost n us ≤ 16 n + (2^23) (size n + 5)^4 + pmUnaryCost`: linear in `n` for the
conversion of `n` to binary, polynomial in `log n` for everything else but the unary copies. -/
theorem pmCost_le {n : ℕ} (hn : 2 ≤ n) {α : Type} (us : List (Fin pmNV × α)) :
    pmCost n us ≤ 16 * n + (2^23) * (Nat.size n + 5) ^ 4 + pmUnaryCost (pmW n) (pmVals n) us := by
  have h1 := pmAtoms1_le hn
  have h2 := pmAtoms2_le n
  have hb := pm_b_le_size n
  have hd := d_le_b n
  set L := Nat.size n
  have hA : pmAtoms1 n + pmAtoms2 n ≤ 2525 * (L + 5) ^ 2 := by
    have : (b n + 1) ^ 2 ≤ (L + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hC : tblC (pmW n) (pmW n) ≤ (2^11) * (L + 5) ^ 2 := by
    unfold tblC pmW
    nlinarith
  have hP : (pmAtoms1 n + pmAtoms2 n) * tblC (pmW n) (pmW n) ≤
      2525 * (L + 5) ^ 2 * ((2^11) * (L + 5) ^ 2) := Nat.mul_le_mul hA hC
  have hdW : 4 * d n * pmW n ≤ 32 * (L + 5) ^ 2 := by
    unfold pmW
    have : d n ≤ L := hd.trans hb
    nlinarith
  have e : 2525 * (L + 5) ^ 2 * ((2^11) * (L + 5) ^ 2) = 5171200 * (L + 5) ^ 4 := by ring
  have h4 : 1 ≤ (L + 5) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h5 : (L + 5) ^ 2 ≤ (L + 5) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h6 : L + 5 ≤ (L + 5) ^ 4 := Nat.le_self_pow (by norm_num) _
  unfold pmCost pmPreCost
  have hW : pmW n = 4 * L + 32 := rfl
  rw [hW] at hdW hP ⊢
  omega

/-- The unary copy of `T` (and of `r ≤ T`) costs `O(n)`: `pmW n · T ≤ (2^9) n`. -/
theorem pm_W_T_le {n : ℕ} (hn : 2 ≤ n) : pmW n * T n ≤ (2^9) * n := by
  have h1 := bT_lt hn
  have h2 : Nat.size n ≤ b n + 1 := pm_size_le
  have hb := one_le_b hn
  have hT : T n ≤ 8 * n := by nlinarith
  unfold pmW
  nlinarith

theorem pm_r_le_T {n : ℕ} (hn : 2 ≤ n) : r n ≤ T n :=
  pm_two_pow_le (pm_ℓ_le_logT hn)

end IntegerMultBounds.MathlibTM2.Fast.TableVM
