module

public import IntegerMultBounds.MathlibTM2.Mult.CRT
public import IntegerMultBounds.MathlibTM2.Host.ChunkSwap
public import IntegerMultBounds.MathlibTM2.Host.Index
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# Padded boxes, layouts and the counting of valid addresses

Pure list and number facts behind the CRT layout machines.

**Layouts.** An axis `j : Fin d` has width `a j`, so `2 ^ a j` coordinate values. A layout is a
list `o` of axes, most significant first, of total width `crtW a o`. `crtDec a o n x` writes the
coordinates of the address `n` in the layout `o` over the vector `x` (the top axis gets
`n / 2 ^ (width below)`), and `crtBox a o C x` is the list of the values `C (crtDec a o n x)` for
`n < 2 ^ crtW a o`. `crtBox_append` splits a box along a layout `o₁ ++ o₂` into the boxes of
`o₂` for every address of `o₁`; `crtBox_cons` is the case `o₁ = [j]`.

**Swaps.** `crtSwapList`: the vendored list interchange `swapList P H 1 D E` exchanges the two
middle levels of a triple `flatMap` of blocks of length `E`. `crtSwapBox` applies it to the boxes
of the layouts `pre ++ j :: k :: post` and `pre ++ k :: j :: post`.

**Fields and counting.** `crtPre a m` is the total width of the axes `j < m` and
`crtDig a j F = F / 2 ^ crtPre a j % 2 ^ a j` the digit of axis `j` in a field index `F` (axis
`0` least significant). `crtVal a s m F`: every digit `j < m` is below `s j`; `crtK a s m F` is
the mixed-radix value `∑_{j < m} digit_j · prefixProd s j`; `crtCnt a s m F` counts the valid
`F' < F`. `crtCnt_valid`: for `s j ≤ 2 ^ a j` and a valid `F < 2 ^ crtPre a m`,
`crtCnt a s m F = crtK a s m F`; `crtCnt_top`: all `2 ^ crtPre a m` indices contain
`∏_{j < m} s j` valid ones.

**Validity automaton.** `crtVA` is a code automaton on three bits per step (index, packed
bounds `crtSig`, field-end mask `crtMask`) with states `crtVS ok lt`; `crtVA_run`: after
`crtPre a m` steps from `crtVS true false` its state is `crtVS (crtVal a s m F) false`, when
`0 < s j < 2 ^ a j`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.Machine


/-! ### Flattened lists of uniform blocks -/

section Blocks

variable {α : Type*}

lemma crt_length_flatMap_range (M E : ℕ) (g : ℕ → List α) (hg : ∀ i, (g i).length = E) :
    ((List.range M).flatMap g).length = M * E := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih]
      simp [hg]; ring

lemma crt_getElem?_flatMap_range (M E : ℕ) (g : ℕ → List α) (hg : ∀ i, (g i).length = E)
    {i e : ℕ} (hi : i < M) (he : e < E) :
    ((List.range M).flatMap g)[i * E + e]? = (g i)[e]? := by
  induction M with
  | zero => omega
  | succ M ih =>
      rw [List.range_succ, List.flatMap_append]
      have hlen := crt_length_flatMap_range M E g hg
      by_cases hiM : i < M
      · rw [List.getElem?_append_left (by rw [hlen]; nlinarith), ih hiM]
      · have hi' : i = M := by omega
        subst hi'
        rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
        simp

lemma crt_flatten_flatMap {β : Type*} (l : List β) (f : β → List (List α)) :
    (l.flatMap f).flatten = l.flatMap fun x => (f x).flatten := by
  rw [List.flatMap_def, List.flatten_flatten, List.map_map, List.flatMap_def]
  rfl

lemma crt_range_mul (m n : ℕ) :
    List.range (m * n) = (List.range m).flatMap fun i => (List.range n).map (i * n + ·) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append]
      simp

end Blocks

/-! ### Layouts and boxes -/

section Layout

variable {d : ℕ} (a : Fin d → ℕ)

/-- The total width of a list of axes. -/
def crtW (o : List (Fin d)) : ℕ := (o.map a).sum

@[simp] lemma crtW_nil : crtW a [] = 0 := rfl

@[simp] lemma crtW_cons (j : Fin d) (o : List (Fin d)) : crtW a (j :: o) = a j + crtW a o := by
  simp [crtW]

lemma crtW_append (o₁ o₂ : List (Fin d)) : crtW a (o₁ ++ o₂) = crtW a o₁ + crtW a o₂ := by
  simp [crtW]

/-- The coordinates of the address `n` in the layout `o` (most significant axis first), written
over `x`. -/
def crtDec : List (Fin d) → ℕ → (Fin d → ℕ) → (Fin d → ℕ)
  | [], _, x => x
  | j :: o, n, x => crtDec o (n % 2 ^ crtW a o) (Function.update x j (n / 2 ^ crtW a o))

@[simp] lemma crtDec_nil (n : ℕ) (x : Fin d → ℕ) : crtDec a [] n x = x := rfl

lemma crtDec_cons (j : Fin d) (o : List (Fin d)) (n : ℕ) (x : Fin d → ℕ) :
    crtDec a (j :: o) n x = crtDec a o (n % 2 ^ crtW a o) (Function.update x j (n / 2 ^ crtW a o)) :=
  rfl

/-- Decoding along a concatenation of layouts. -/
theorem crtDec_append :
    ∀ (o₁ o₂ : List (Fin d)) (n₁ n₂ : ℕ) (x : Fin d → ℕ), n₁ < 2 ^ crtW a o₁ →
      n₂ < 2 ^ crtW a o₂ →
      crtDec a (o₁ ++ o₂) (n₁ * 2 ^ crtW a o₂ + n₂) x = crtDec a o₂ n₂ (crtDec a o₁ n₁ x)
  | [], o₂, n₁, n₂, x, h₁, h₂ => by
      simp only [crtW_nil, pow_zero, Nat.lt_one_iff] at h₁
      subst h₁
      simp
  | j :: o₁, o₂, n₁, n₂, x, h₁, h₂ => by
      rw [List.cons_append, crtDec_cons, crtDec_cons, crtW_append]
      have hpos : 0 < 2 ^ crtW a o₂ := by positivity
      have hdiv : (n₁ * 2 ^ crtW a o₂ + n₂) / 2 ^ (crtW a o₁ + crtW a o₂) =
          n₁ / 2 ^ crtW a o₁ := by
        rw [pow_add, Nat.mul_comm (2 ^ crtW a o₁), ← Nat.div_div_eq_div_mul,
          Nat.mul_comm n₁, Nat.mul_add_div hpos, Nat.div_eq_of_lt h₂, Nat.add_zero]
      have hmod : (n₁ * 2 ^ crtW a o₂ + n₂) % 2 ^ (crtW a o₁ + crtW a o₂) =
          (n₁ % 2 ^ crtW a o₁) * 2 ^ crtW a o₂ + n₂ := by
        rw [pow_add, Nat.mul_comm (2 ^ crtW a o₁), Nat.mod_mul, Nat.mul_comm n₁,
          Nat.mul_add_mod, Nat.mul_add_div hpos, Nat.div_eq_of_lt h₂, Nat.add_zero,
          Nat.mod_eq_of_lt h₂]
        ring
      rw [hdiv, hmod]
      exact crtDec_append o₁ o₂ _ n₂ _ (Nat.mod_lt _ (by positivity)) h₂

/-- An axis outside the layout keeps its coordinate. -/
theorem crtDec_apply_of_not_mem :
    ∀ (o : List (Fin d)) (n : ℕ) (x : Fin d → ℕ) (i : Fin d), i ∉ o → crtDec a o n x i = x i
  | [], _, _, _, _ => rfl
  | j :: o, n, x, i, hi => by
      have hij : i ≠ j := by rintro rfl; exact hi List.mem_cons_self
      rw [crtDec_cons, crtDec_apply_of_not_mem o _ _ i (fun h => hi (List.mem_cons_of_mem _ h)),
        Function.update_of_ne hij]

/-- Writing an axis outside the layout commutes with decoding. -/
theorem crtDec_update_of_not_mem :
    ∀ (o : List (Fin d)) (n : ℕ) (x : Fin d → ℕ) (i : Fin d) (y : ℕ), i ∉ o →
      crtDec a o n (Function.update x i y) = Function.update (crtDec a o n x) i y
  | [], _, _, _, _, _ => rfl
  | j :: o, n, x, i, y, hi => by
      have hij : i ≠ j := by rintro rfl; exact hi List.mem_cons_self
      rw [crtDec_cons, crtDec_cons, Function.update_comm hij,
        crtDec_update_of_not_mem o _ _ i y (fun h => hi (List.mem_cons_of_mem _ h))]

/-- The box of content `C` in layout `o` over `x`: the values at the addresses `n < 2 ^ crtW a o`,
in increasing order. -/
def crtBox {α : Type*} (o : List (Fin d)) (C : (Fin d → ℕ) → α) (x : Fin d → ℕ) : List α :=
  (List.range (2 ^ crtW a o)).map fun n => C (crtDec a o n x)

variable {α : Type*}

@[simp] lemma crtBox_length (o : List (Fin d)) (C : (Fin d → ℕ) → α) (x : Fin d → ℕ) :
    (crtBox a o C x).length = 2 ^ crtW a o := by
  simp [crtBox]

lemma crtBox_getElem (o : List (Fin d)) (C : (Fin d → ℕ) → α) (x : Fin d → ℕ) (n : ℕ)
    (h : n < (crtBox a o C x).length) : (crtBox a o C x)[n] = C (crtDec a o n x) := by
  simp [crtBox]

@[simp] lemma crtBox_nil (C : (Fin d → ℕ) → α) (x : Fin d → ℕ) : crtBox a [] C x = [C x] := by
  simp [crtBox]

/-- A box along `o₁ ++ o₂`: the boxes along `o₂` for the addresses of `o₁`, in order. -/
theorem crtBox_append (o₁ o₂ : List (Fin d)) (C : (Fin d → ℕ) → α) (x : Fin d → ℕ) :
    crtBox a (o₁ ++ o₂) C x =
      (List.range (2 ^ crtW a o₁)).flatMap fun n => crtBox a o₂ C (crtDec a o₁ n x) := by
  rw [crtBox, crtW_append, pow_add, crt_range_mul, List.map_flatMap]
  refine List.flatMap_congr fun n hn => ?_
  rw [crtBox, List.map_map]
  refine List.map_congr_left fun e he => ?_
  simp only [Function.comp_apply]
  rw [crtDec_append a o₁ o₂ n e x (List.mem_range.1 hn) (List.mem_range.1 he)]

theorem crtBox_cons (j : Fin d) (o : List (Fin d)) (C : (Fin d → ℕ) → α) (x : Fin d → ℕ) :
    crtBox a (j :: o) C x =
      (List.range (2 ^ a j)).flatMap fun y => crtBox a o C (Function.update x j y) := by
  have h := crtBox_append a [j] o C x
  simp only [List.singleton_append, crtW_cons, crtW_nil, Nat.add_zero] at h
  rw [h]
  refine List.flatMap_congr fun y _ => ?_
  simp [crtDec_cons]

lemma crtBox_flatten_length (o : List (Fin d)) (C : (Fin d → ℕ) → List α) (x : Fin d → ℕ)
    (B : ℕ) (hC : ∀ y, (C y).length = B) :
    (crtBox a o C x).flatten.length = 2 ^ crtW a o * B := by
  rw [crtBox, ← List.flatMap_def]
  exact crt_length_flatMap_range _ B _ fun n => hC _

end Layout

/-! ### Exchanging two middle levels -/

section Swap

variable {α : Type*}

/-- The list interchange with one middle block exchanges the two middle levels of a triple
`flatMap` of blocks of length `E`. -/
theorem crtSwapList (dflt : α) (P H D E : ℕ) (f : ℕ → ℕ → ℕ → List α)
    (hf : ∀ p y z, (f p y z).length = E) :
    swapList P H 1 D E dflt ((List.range P).flatMap fun p => (List.range H).flatMap fun y =>
        (List.range D).flatMap fun z => f p y z) =
      (List.range P).flatMap fun p => (List.range D).flatMap fun z =>
        (List.range H).flatMap fun y => f p y z := by
  have hz : ∀ p y, ((List.range D).flatMap fun z => f p y z).length = D * E := fun p y =>
    crt_length_flatMap_range D E _ (hf p y)
  have hy : ∀ p, ((List.range H).flatMap fun y => (List.range D).flatMap fun z => f p y z).length =
      H * (D * E) := fun p => crt_length_flatMap_range H _ _ (hz p)
  have hy' : ∀ p z, ((List.range H).flatMap fun y => f p y z).length = H * E := fun p z =>
    crt_length_flatMap_range H E _ (fun y => hf p y z)
  have hz' : ∀ p, ((List.range D).flatMap fun z => (List.range H).flatMap fun y => f p y z).length =
      D * (H * E) := fun p => crt_length_flatMap_range D _ _ (hy' p)
  set l := (List.range P).flatMap fun p => (List.range H).flatMap fun y =>
    (List.range D).flatMap fun z => f p y z with hl
  have hlen : l.length = P * H * 1 * D * E := by
    rw [hl, crt_length_flatMap_range P _ _ hy]; ring
  have hlen' : ((List.range P).flatMap fun p => (List.range D).flatMap fun z =>
      (List.range H).flatMap fun y => f p y z).length = P * (D * (H * E)) :=
    crt_length_flatMap_range P _ _ hz'
  apply List.ext_getElem?
  intro i
  by_cases hi : i < P * D * 1 * H * E
  · have hE : 0 < E := by
      rcases Nat.eq_zero_or_pos E with h | h
      · rw [h, Nat.mul_zero] at hi; omega
      · exact h
    have hH : 0 < H := by
      rcases Nat.eq_zero_or_pos H with h | h
      · rw [h] at hi; simp at hi
      · exact h
    have hD : 0 < D := by
      rcases Nat.eq_zero_or_pos D with h | h
      · rw [h] at hi; simp at hi
      · exact h
    -- decompose `i = (((p * D + z) * 1 + 0) * H + y) * E + e`
    set e := i % E
    set y := i / E % H
    set z := i / E / H % D
    set p := i / E / H / D
    have he : e < E := Nat.mod_lt _ hE
    have hy₁ : y < H := Nat.mod_lt _ hH
    have hz₁ : z < D := Nat.mod_lt _ hD
    have hp : p < P := by
      simp only [p]
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
      exact Nat.div_lt_of_lt_mul (by nlinarith)
    have hi' : i = (((p * D + z) * 1 + 0) * H + y) * E + e := by
      simp only [p, z, y, e, Nat.mul_one, Nat.add_zero]
      rw [Nat.div_add_mod' (i / E / H) D, Nat.div_add_mod' (i / E) H, Nat.div_add_mod' i E]
    rw [hi', swapList_getElem? dflt l hlen hp hy₁ (Nat.zero_lt_one) hz₁ he]
    simp only [Nat.mul_one, Nat.add_zero]
    rw [show ((p * H + y) * D + z) * E + e = p * (H * (D * E)) + (y * (D * E) + (z * E + e)) by
      ring, crt_getElem?_flatMap_range P _ _ hy hp (mix_lt hy₁ (mix_lt hz₁ he)),
      crt_getElem?_flatMap_range H _ _ (hz p) hy₁ (mix_lt hz₁ he),
      crt_getElem?_flatMap_range D E _ (hf p y) hz₁ he]
    rw [show ((p * D + z) * H + y) * E + e = p * (D * (H * E)) + (z * (H * E) + (y * E + e)) by
      ring, crt_getElem?_flatMap_range P _ _ hz' hp (mix_lt hz₁ (mix_lt hy₁ he)),
      crt_getElem?_flatMap_range D _ _ (hy' p) hz₁ (mix_lt hy₁ he),
      crt_getElem?_flatMap_range H E _ (fun y => hf p y z) hy₁ he]
  · rw [List.getElem?_eq_none, List.getElem?_eq_none]
    · rw [hlen']; nlinarith
    · rw [swapList, List.length_map, List.length_range]; omega

variable {d : ℕ} (a : Fin d → ℕ)

/-- Exchanging adjacent axes `j`, `k` of a box whose records have length `B`: the list
interchange with `P = 2 ^ crtW pre`, `H = 2 ^ a j`, `D = 2 ^ a k` and `E = 2 ^ crtW post * B`
turns the flattened box along `pre ++ j :: k :: post` into the flattened box along
`pre ++ k :: j :: post`. -/
theorem crtSwapBox (dflt : α) (pre post : List (Fin d)) (j k : Fin d) (hjk : j ≠ k)
    (C : (Fin d → ℕ) → List α) (B : ℕ) (hC : ∀ y, (C y).length = B) (x : Fin d → ℕ) :
    swapList (2 ^ crtW a pre) (2 ^ a j) 1 (2 ^ a k) (2 ^ crtW a post * B) dflt
        (crtBox a (pre ++ j :: k :: post) C x).flatten =
      (crtBox a (pre ++ k :: j :: post) C x).flatten := by
  have e₁ : (crtBox a (pre ++ j :: k :: post) C x).flatten =
      (List.range (2 ^ crtW a pre)).flatMap fun p => (List.range (2 ^ a j)).flatMap fun y =>
        (List.range (2 ^ a k)).flatMap fun z => (crtBox a post C
          (Function.update (Function.update (crtDec a pre p x) j y) k z)).flatten := by
    rw [crtBox_append, crt_flatten_flatMap]
    refine List.flatMap_congr fun p _ => ?_
    rw [crtBox_cons, crt_flatten_flatMap]
    refine List.flatMap_congr fun y _ => ?_
    rw [crtBox_cons, crt_flatten_flatMap]
  have e₂ : (crtBox a (pre ++ k :: j :: post) C x).flatten =
      (List.range (2 ^ crtW a pre)).flatMap fun p => (List.range (2 ^ a k)).flatMap fun z =>
        (List.range (2 ^ a j)).flatMap fun y => (crtBox a post C
          (Function.update (Function.update (crtDec a pre p x) j y) k z)).flatten := by
    rw [crtBox_append, crt_flatten_flatMap]
    refine List.flatMap_congr fun p _ => ?_
    rw [crtBox_cons, crt_flatten_flatMap]
    refine List.flatMap_congr fun z _ => ?_
    rw [crtBox_cons, crt_flatten_flatMap]
    refine List.flatMap_congr fun y _ => ?_
    rw [Function.update_comm hjk]
  rw [e₁, e₂]
  exact crtSwapList dflt _ _ _ _ _ fun p y z => crtBox_flatten_length a post C _ B hC

end Swap

/-! ### Fields of an index -/

section Fields

variable {d : ℕ} (a s : Fin d → ℕ)

/-- The axes `j < m`. -/
abbrev crtLow (m : ℕ) : Finset (Fin d) := Finset.univ.filter fun j : Fin d => j.val < m

/-- The total width of the axes `j < m`. -/
def crtPre (m : ℕ) : ℕ := ∑ j ∈ crtLow m, a j

/-- The product of the lengths of the axes `j < m`. -/
def crtProd (m : ℕ) : ℕ := ∏ j ∈ crtLow m, s j

/-- The digit of axis `j` in the field index `F` (axis `0` least significant). -/
def crtDig (j : Fin d) (F : ℕ) : ℕ := F / 2 ^ crtPre a j.val % 2 ^ a j

/-- Every digit `j < m` of `F` is below `s j`. -/
def crtVal (m F : ℕ) : Bool := decide (∀ j : Fin d, j.val < m → crtDig a j F < s j)

/-- The mixed-radix value `∑_{j < m} digit_j · prefixProd s j`. -/
def crtK (m F : ℕ) : ℕ := ∑ j ∈ crtLow m, crtDig a j F * prefixProd s j

/-- The number of valid indices below `F`. -/
def crtCnt (m F : ℕ) : ℕ := ((List.range F).filter (crtVal a s m)).length

/-- The packed bounds `∑_{j < m} s j · 2 ^ crtPre a j`. -/
def crtSig (m : ℕ) : ℕ := ∑ j ∈ crtLow m, s j * 2 ^ crtPre a j.val

/-- The field-end mask `∑_{j < m} 2 ^ (crtPre a j + a j - 1)`. -/
def crtMask (m : ℕ) : ℕ := ∑ j ∈ crtLow m, 2 ^ (crtPre a j.val + a j - 1)

lemma crtLow_zero : crtLow (d := d) 0 = ∅ := by
  ext j; simp

lemma crtLow_succ {m : ℕ} (h : m < d) : crtLow (d := d) (m + 1) = insert ⟨m, h⟩ (crtLow m) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

lemma crt_not_mem_low {m : ℕ} (h : m < d) : (⟨m, h⟩ : Fin d) ∉ crtLow (d := d) m := by simp

lemma crtLow_of_le {m : ℕ} (h : d ≤ m) : crtLow (d := d) m = Finset.univ := by
  ext j; simp; omega

@[simp] lemma crtPre_zero : crtPre a 0 = 0 := by simp [crtPre, crtLow_zero]

lemma crtPre_succ {m : ℕ} (h : m < d) : crtPre a (m + 1) = crtPre a m + a ⟨m, h⟩ := by
  rw [crtPre, crtLow_succ h, Finset.sum_insert (crt_not_mem_low h), Nat.add_comm]; rfl

@[simp] lemma crtProd_zero : crtProd s 0 = 1 := by simp [crtProd, crtLow_zero]

lemma crtProd_succ {m : ℕ} (h : m < d) : crtProd s (m + 1) = crtProd s m * s ⟨m, h⟩ := by
  rw [crtProd, crtLow_succ h, Finset.prod_insert (crt_not_mem_low h), Nat.mul_comm]; rfl

lemma crtProd_eq_prefixProd {m : ℕ} (h : m < d) : crtProd s m = prefixProd s ⟨m, h⟩ := by
  rw [crtProd, prefixProd]
  congr 1
  ext j; simp [Fin.lt_def]

@[simp] lemma crtSig_zero : crtSig a s 0 = 0 := by simp [crtSig, crtLow_zero]

lemma crtSig_succ {m : ℕ} (h : m < d) :
    crtSig a s (m + 1) = crtSig a s m + s ⟨m, h⟩ * 2 ^ crtPre a m := by
  rw [crtSig, crtLow_succ h, Finset.sum_insert (crt_not_mem_low h), Nat.add_comm]; rfl

@[simp] lemma crtMask_zero : crtMask a 0 = 0 := by simp [crtMask, crtLow_zero]

lemma crtMask_succ {m : ℕ} (h : m < d) :
    crtMask a (m + 1) = crtMask a m + 2 ^ (crtPre a m + a ⟨m, h⟩ - 1) := by
  rw [crtMask, crtLow_succ h, Finset.sum_insert (crt_not_mem_low h), Nat.add_comm]; rfl

@[simp] lemma crtK_zero (F : ℕ) : crtK a s 0 F = 0 := by simp [crtK, crtLow_zero]

lemma crtPre_mono {m m' : ℕ} (h : m ≤ m') : crtPre a m ≤ crtPre a m' :=
  Finset.sum_le_sum_of_subset (fun j hj => by simp at hj ⊢; omega)

lemma crtPre_add_le (j : Fin d) {m : ℕ} (h : j.val < m) : crtPre a j.val + a j ≤ crtPre a m := by
  rw [← crtPre_succ a j.isLt]
  exact crtPre_mono a (by omega)

/-- Digit `j < m` depends only on the index modulo `2 ^ crtPre a m`. -/
lemma crtDig_mod (j : Fin d) {m : ℕ} (h : j.val < m) (F : ℕ) :
    crtDig a j (F % 2 ^ crtPre a m) = crtDig a j F := by
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (crtPre_add_le a j h)
  unfold crtDig
  rw [he, Nat.pow_add, Nat.pow_add, Nat.mul_assoc, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Dvd.intro _ rfl)]

/-- The top digit of an index `x * 2 ^ crtPre a m + r`. -/
lemma crtDig_top {m : ℕ} (h : m < d) {x r : ℕ} (hx : x < 2 ^ a ⟨m, h⟩) (hr : r < 2 ^ crtPre a m) :
    crtDig a ⟨m, h⟩ (x * 2 ^ crtPre a m + r) = x := by
  unfold crtDig
  rw [Nat.mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hr, Nat.add_zero,
    Nat.mod_eq_of_lt hx]

lemma crtDig_low {m : ℕ} (j : Fin d) (hj : j.val < m) (x r : ℕ) (hr : r < 2 ^ crtPre a m) :
    crtDig a j (x * 2 ^ crtPre a m + r) = crtDig a j r := by
  rw [← crtDig_mod a j hj, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

lemma crtVal_succ {m : ℕ} (h : m < d) {x r : ℕ} (hx : x < 2 ^ a ⟨m, h⟩)
    (hr : r < 2 ^ crtPre a m) :
    crtVal a s (m + 1) (x * 2 ^ crtPre a m + r) = (crtVal a s m r && decide (x < s ⟨m, h⟩)) := by
  simp only [crtVal]
  rw [← Bool.decide_and, decide_eq_decide]
  constructor
  · intro H
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [← crtDig_low a j hj x r hr]; exact H j (by omega)
    · rw [← crtDig_top a h hx hr]; exact H ⟨m, h⟩ (by simp)
  · rintro ⟨H₁, H₂⟩ j hj
    by_cases hjm : j.val < m
    · rw [crtDig_low a j hjm x r hr]; exact H₁ j hjm
    · have : j = ⟨m, h⟩ := Fin.ext (by simp; omega)
      subst this
      rw [crtDig_top a h hx hr]; exact H₂

lemma crtK_succ {m : ℕ} (h : m < d) {x r : ℕ} (hx : x < 2 ^ a ⟨m, h⟩) (hr : r < 2 ^ crtPre a m) :
    crtK a s (m + 1) (x * 2 ^ crtPre a m + r) = crtK a s m r + x * crtProd s m := by
  rw [crtK, crtLow_succ h, Finset.sum_insert (crt_not_mem_low h), crtDig_top a h hx hr,
    ← crtProd_eq_prefixProd s h, Nat.add_comm, crtK]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  rw [crtDig_low a j hj x r hr]

lemma crtCnt_succ_arg (m F : ℕ) :
    crtCnt a s m (F + 1) = crtCnt a s m F + (crtVal a s m F).toNat := by
  rw [crtCnt, crtCnt, List.range_succ, List.filter_append, List.length_append]
  cases hv : crtVal a s m F <;> simp [hv]

lemma crt_count_map (r : ℕ) (f : ℕ → ℕ) (p q : ℕ → Bool) (hpq : ∀ i < r, p (f i) = q i) :
    (((List.range r).map f).filter p).length = ((List.range r).filter q).length := by
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro i hi
  simp only [Function.comp_apply]
  exact hpq i (List.mem_range.1 hi)

lemma crt_sum_ite_lt (x s c : ℕ) :
    ((List.range x).map fun y => if y < s then c else 0).sum = min x s * c := by
  induction x with
  | zero => simp
  | succ x ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      by_cases hx : x < s
      · simp [hx, Nat.min_eq_left (by omega : x ≤ s)]
        ring
      · simp [hx, Nat.min_eq_right (by omega : s ≤ x + 1), Nat.min_eq_right (by omega : s ≤ x)]

/-- The count over the first `x` full blocks of the top axis and `r` more indices. -/
lemma crtCnt_split {m : ℕ} (h : m < d) (x r : ℕ) (hx : x ≤ 2 ^ a ⟨m, h⟩)
    (hr : r < 2 ^ crtPre a m) (hxr : x < 2 ^ a ⟨m, h⟩ ∨ r = 0) :
    crtCnt a s (m + 1) (x * 2 ^ crtPre a m + r) =
      min x (s ⟨m, h⟩) * crtCnt a s m (2 ^ crtPre a m) +
        (if x < s ⟨m, h⟩ then crtCnt a s m r else 0) := by
  set M := 2 ^ crtPre a m with hM
  have hblock : ∀ y, y < 2 ^ a ⟨m, h⟩ → ∀ r', r' ≤ M →
      (((List.range r').map (y * M + ·)).filter (crtVal a s (m + 1))).length =
        if y < s ⟨m, h⟩ then crtCnt a s m r' else 0 := by
    intro y hy r' hr'
    by_cases hys : y < s ⟨m, h⟩
    · rw [ite_eq_left hys, crtCnt]
      exact crt_count_map r' _ _ _ fun i hi => by
        rw [crtVal_succ a s h hy (by omega)]; simp [hys]
    · rw [ite_eq_right hys]
      rw [crt_count_map r' _ _ (fun _ => false) fun i hi => by
        rw [crtVal_succ a s h hy (by omega)]; simp [hys]]
      simp
  rw [crtCnt, List.range_add, crt_range_mul, List.filter_append, List.length_append,
    List.filter_flatMap, List.length_flatMap]
  congr 1
  · rw [← crt_sum_ite_lt x (s ⟨m, h⟩) (crtCnt a s m M)]
    congr 1
    refine List.map_congr_left fun y hy => ?_
    exact hblock y (by have := List.mem_range.1 hy; omega) M le_rfl
  · rcases hxr with hxr | rfl
    · exact hblock x hxr r hr.le
    · simp [crtCnt]

/-- The count of valid indices: all `2 ^ crtPre a m` indices contain `crtProd s m` valid ones,
and a valid index `F` has `crtK a s m F` valid indices below it. -/
theorem crtCnt_main (hs : ∀ j, s j ≤ 2 ^ a j) :
    ∀ m ≤ d, crtCnt a s m (2 ^ crtPre a m) = crtProd s m ∧
      ∀ F < 2 ^ crtPre a m, crtVal a s m F = true → crtCnt a s m F = crtK a s m F
  | 0, _ => by
      refine ⟨?_, fun F hF _ => ?_⟩
      · simp [crtCnt, crtVal]
      · simp only [crtPre_zero, pow_zero, Nat.lt_one_iff] at hF
        subst hF; simp [crtCnt]
  | m + 1, hm => by
      have h : m < d := by omega
      obtain ⟨ih₁, ih₂⟩ := crtCnt_main hs m (by omega)
      refine ⟨?_, fun F hF hv => ?_⟩
      · have e := crtCnt_split a s h (2 ^ a ⟨m, h⟩) 0 le_rfl (by positivity) (Or.inr rfl)
        rw [← pow_add, Nat.add_comm (a ⟨m, h⟩), ← crtPre_succ a h] at e
        simp only [Nat.add_zero] at e
        rw [e, ih₁, Nat.min_eq_right (hs _), crtProd_succ s h]
        simp [crtCnt]; ring
      · set M := 2 ^ crtPre a m
        have hM : 0 < M := by positivity
        have hF' : F / M < 2 ^ a ⟨m, h⟩ := by
          rw [crtPre_succ a h, pow_add] at hF
          exact Nat.div_lt_of_lt_mul hF
        have hdec : F = F / M * M + F % M := (Nat.div_add_mod' F M).symm
        have hr : F % M < M := Nat.mod_lt _ hM
        rw [hdec, crtVal_succ a s h hF' hr] at hv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
        rw [hdec, crtCnt_split a s h _ _ hF'.le hr (Or.inl hF'), ih₁, ite_eq_left hv.2,
          ih₂ _ hr hv.1, crtK_succ a s h hF' hr, Nat.min_eq_left hv.2.le]
        ring

end Fields

/-! ### Reversed prefixes of the axes -/

section RevAx

variable {d : ℕ} (a s : Fin d → ℕ)

/-- The axes `m - 1, …, 1, 0`: the layout of the field indices of `crtDig` (axis `0` least
significant). -/
def crtRevAx (m : ℕ) : List (Fin d) := ((List.finRange d).take m).reverse

@[simp] lemma crtRevAx_zero : crtRevAx (d := d) 0 = [] := by simp [crtRevAx]

lemma crtRevAx_succ {m : ℕ} (h : m < d) : crtRevAx (d := d) (m + 1) = ⟨m, h⟩ :: crtRevAx m := by
  rw [crtRevAx, List.take_add_one, List.reverse_append, crtRevAx,
    List.getElem?_eq_getElem (by simpa using h)]
  simp

lemma crtW_revAx : ∀ m ≤ d, crtW a (crtRevAx m) = crtPre a m
  | 0, _ => by simp
  | m + 1, h => by
      rw [crtRevAx_succ (by omega), crtW_cons, crtW_revAx m (by omega), crtPre_succ a (by omega),
        Nat.add_comm]

lemma crt_mem_revAx {m : ℕ} (j : Fin d) : j ∈ crtRevAx (d := d) m ↔ j.val < m := by
  simp [crtRevAx, List.mem_take_iff_getElem, List.getElem_finRange]
  constructor
  · rintro ⟨i, hi, rfl⟩; simpa using hi.1
  · intro hj; exact ⟨j.val, ⟨hj, j.isLt⟩, rfl⟩

lemma crtRevAx_nodup (m : ℕ) : (crtRevAx (d := d) m).Nodup :=
  List.nodup_reverse.2 ((List.nodup_finRange d).sublist (List.take_sublist _ _))

/-- Decoding a field index along `crtRevAx m` gives its digits. -/
theorem crtDec_revAx : ∀ m ≤ d, ∀ F < 2 ^ crtPre a m, ∀ x : Fin d → ℕ,
    crtDec a (crtRevAx m) F x = fun j => if j.val < m then crtDig a j F else x j
  | 0, _, F, hF, x => by
      funext j; simp
  | m + 1, hm, F, hF, x => by
      have h : m < d := by omega
      rw [crtRevAx_succ h, crtDec_cons, crtW_revAx a m (by omega),
        crtDec_revAx m (by omega) _ (Nat.mod_lt _ (by positivity))]
      funext j
      by_cases hj : j.val < m
      · simp [hj, crtDig_mod a j hj, show j.val < m + 1 by omega]
      · by_cases hjm : j.val = m
        · have : j = ⟨m, h⟩ := Fin.ext hjm
          subst this
          have hlt : F / 2 ^ crtPre a m < 2 ^ a ⟨m, h⟩ := by
            rw [crtPre_succ a h, pow_add] at hF
            exact Nat.div_lt_of_lt_mul hF
          simp [crtDig, Nat.mod_eq_of_lt hlt]
        · have hne : j ≠ ⟨m, h⟩ := fun e => hjm (by rw [e])
          simp [hj, hne, show ¬ j.val < m + 1 by omega]

end RevAx

/-! ### The validity automaton -/

section Auto

variable {A : ℕ}

/-- Validity automaton states: `ok` (every closed field is below its bound) and `lt` (the low
bits of the current field are below those of its bound). -/
def crtVS (ok lt : Bool) : Fin (A + 4) :=
  ⟨2 * ok.toNat + lt.toNat, by cases ok <;> cases lt <;> simp⟩

lemma crtVS_ok (ok lt : Bool) : decide (2 ≤ (crtVS (A := A) ok lt).val) = ok := by
  cases ok <;> cases lt <;> simp [crtVS]

lemma crtVS_lt (ok lt : Bool) : decide ((crtVS (A := A) ok lt).val % 2 = 1) = lt := by
  cases ok <;> cases lt <;> simp [crtVS]

/-- The validity automaton on the bits of a field index (input `0`), the packed bounds
(input `1`) and the field-end mask (input `2`), least significant first. -/
def crtVA (A : ℕ) : CAuto A 3 2 where
  init := crtVS true false
  step st col :=
    if col 2 then crtVS (decide (2 ≤ st.val) &&
        ((!col 0 && col 1) || (col 0 == col 1 && decide (st.val % 2 = 1)))) false
    else crtVS (decide (2 ≤ st.val))
        ((!col 0 && col 1) || (col 0 == col 1 && decide (st.val % 2 = 1)))
  out st := if 2 ≤ st.val then 1 else 0

lemma crtVA_out (ok lt : Bool) : (crtVA A).out (crtVS ok lt) = if ok then 1 else 0 := by
  cases ok <;> cases lt <;> simp [crtVA, crtVS]

/-- Running a code automaton over `k₁ + k₂` bits. -/
lemma crt_run_add {nr nd : ℕ} (C : CAuto A nr nd) :
    ∀ (k₁ k₂ : ℕ) (st : Fin (A + 4)) (vals : Fin nr → ℕ),
      C.run (k₁ + k₂) st vals = C.run k₂ (C.run k₁ st vals) fun r => vals r / 2 ^ k₁
  | 0, k₂, st, vals => by simp [CAuto.run]
  | k₁ + 1, k₂, st, vals => by
      rw [Nat.add_right_comm, CAuto.run, CAuto.run, crt_run_add C k₁ k₂]
      congr 1
      funext r
      rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

/-- The comparison of the low `k + 1` bits from the low bit and the comparison of the bits above. -/
lemma crt_cmp_step (x y k : ℕ) (lt : Bool) :
    (decide (x / 2 % 2 ^ k < y / 2 % 2 ^ k) || (decide (x / 2 % 2 ^ k = y / 2 % 2 ^ k) &&
      ((!x.testBit 0 && y.testBit 0) || (x.testBit 0 == y.testBit 0 && lt)))) =
    (decide (x % 2 ^ (k + 1) < y % 2 ^ (k + 1)) ||
      (decide (x % 2 ^ (k + 1) = y % 2 ^ (k + 1)) && lt)) := by
  have hx : x % 2 ^ (k + 1) = 2 * (x / 2 % 2 ^ k) + x % 2 := by
    rw [pow_succ', Nat.mod_mul]; ring
  have hy : y % 2 ^ (k + 1) = 2 * (y / 2 % 2 ^ k) + y % 2 := by
    rw [pow_succ', Nat.mod_mul]; ring
  have bx : x.testBit 0 = decide (x % 2 = 1) := by simp [Nat.testBit_zero]
  have hby : y.testBit 0 = decide (y % 2 = 1) := by simp [Nat.testBit_zero]
  rw [hx, hy, bx, hby]
  have h0 := Nat.mod_lt x (show 0 < 2 by norm_num)
  have h1 := Nat.mod_lt y (show 0 < 2 by norm_num)
  generalize x / 2 % 2 ^ k = X
  generalize y / 2 % 2 ^ k = Y
  generalize x % 2 = x0 at h0 ⊢
  generalize y % 2 = y0 at h1 ⊢
  interval_cases x0 <;> interval_cases y0 <;> cases lt <;> simp <;>
    first | omega | (rw [Bool.eq_iff_iff]; simp; omega)

/-- The comparison of `k + 1` low bits from the top bit and the comparison of the `k` bits
below. -/
lemma crt_cmp_top (x y k : ℕ) :
    ((!(x / 2 ^ k).testBit 0 && (y / 2 ^ k).testBit 0) ||
      ((x / 2 ^ k).testBit 0 == (y / 2 ^ k).testBit 0 && decide (x % 2 ^ k < y % 2 ^ k))) =
    decide (x % 2 ^ (k + 1) < y % 2 ^ (k + 1)) := by
  have hx : x % 2 ^ (k + 1) = 2 ^ k * (x / 2 ^ k % 2) + x % 2 ^ k := by
    rw [pow_succ, Nat.mod_mul]; ring
  have hy : y % 2 ^ (k + 1) = 2 ^ k * (y / 2 ^ k % 2) + y % 2 ^ k := by
    rw [pow_succ, Nat.mod_mul]; ring
  have bx : (x / 2 ^ k).testBit 0 = decide (x / 2 ^ k % 2 = 1) := by simp [Nat.testBit_zero]
  have hby : (y / 2 ^ k).testBit 0 = decide (y / 2 ^ k % 2 = 1) := by simp [Nat.testBit_zero]
  rw [hx, hy, bx, hby]
  have hK : 0 < 2 ^ k := by positivity
  have hX := Nat.mod_lt x hK
  have hY := Nat.mod_lt y hK
  have h0 := Nat.mod_lt (x / 2 ^ k) (show 0 < 2 by norm_num)
  have h1 := Nat.mod_lt (y / 2 ^ k) (show 0 < 2 by norm_num)
  generalize x % 2 ^ k = X at hX ⊢
  generalize y % 2 ^ k = Y at hY ⊢
  generalize x / 2 ^ k % 2 = x0 at h0 ⊢
  generalize y / 2 ^ k % 2 = y0 at h1 ⊢
  generalize 2 ^ k = K at hK hX hY ⊢
  interval_cases x0 <;> interval_cases y0 <;> simp <;> omega

lemma crtVA_step (ok lt : Bool) (col : Fin 3 → Bool) :
    (crtVA A).step (crtVS ok lt) col =
      if col 2 then crtVS (ok && ((!col 0 && col 1) || (col 0 == col 1 && lt))) false
      else crtVS ok ((!col 0 && col 1) || (col 0 == col 1 && lt)) := by
  simp only [crtVA, crtVS_ok, crtVS_lt]

lemma crtVA_run_low (ok : Bool) :
    ∀ (k : ℕ) (vals : Fin 3 → ℕ) (lt : Bool), vals 2 % 2 ^ k = 0 →
      (crtVA A).run k (crtVS ok lt) vals = crtVS ok
        (decide (vals 0 % 2 ^ k < vals 1 % 2 ^ k) ||
          (decide (vals 0 % 2 ^ k = vals 1 % 2 ^ k) && lt))
  | 0, vals, lt, _ => by simp [CAuto.run, Nat.mod_one]
  | k + 1, vals, lt, h2 => by
      have hb : (vals 2).testBit 0 = false := by
        have : vals 2 % 2 = 0 := by
          have := Nat.mod_mod_of_dvd (vals 2) (pow_dvd_pow 2 (Nat.le_add_left 1 k))
          rw [h2, pow_one] at this; omega
        simp [Nat.testBit_zero, this]
      rw [CAuto.run, crtVA_step, ite_eq_right (by simp [hb])]
      rw [crtVA_run_low ok k _ _ (by
        rw [← Nat.mod_mul_right_div_self, ← pow_succ', h2, Nat.zero_div])]
      rw [crt_cmp_step]

/-- One field of width `w ≥ 1` whose mask bit is set exactly at its top bit. -/
lemma crtVA_run_field (ok : Bool) (w : ℕ) (hw : 1 ≤ w) (vals : Fin 3 → ℕ)
    (h2 : vals 2 % 2 ^ w = 2 ^ (w - 1)) :
    (crtVA A).run w (crtVS ok false) vals =
      crtVS (ok && decide (vals 0 % 2 ^ w < vals 1 % 2 ^ w)) false := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h2
  have hlow : vals 2 % 2 ^ k = 0 := by
    have := Nat.mod_mod_of_dvd (vals 2) (pow_dvd_pow 2 (Nat.le_add_right k 1))
    rw [h2, Nat.mod_self] at this; exact this.symm
  rw [crt_run_add, crtVA_run_low ok k vals false hlow]
  have hb : (vals 2 / 2 ^ k).testBit 0 = true := by
    have : vals 2 / 2 ^ k % 2 = 1 := by
      rw [← Nat.mod_mul_right_div_self, ← pow_succ, h2, Nat.div_self (by positivity)]
    simp [Nat.testBit_zero, this]
  simp only [Bool.and_false, Bool.or_false]
  rw [CAuto.run, crtVA_step, ite_eq_left hb, CAuto.run, crt_cmp_top]

variable {d : ℕ} (a s : Fin d → ℕ)

lemma crtSig_lt (hs : ∀ j, s j < 2 ^ a j) : ∀ m ≤ d, crtSig a s m < 2 ^ crtPre a m
  | 0, _ => by simp
  | m + 1, h => by
      have hm : m < d := by omega
      have ih := crtSig_lt hs m (by omega)
      rw [crtSig_succ a s hm, crtPre_succ a hm, pow_add]
      have := hs ⟨m, hm⟩
      nlinarith

lemma crtMask_lt (ha : ∀ j, 1 ≤ a j) : ∀ m ≤ d, crtMask a m < 2 ^ crtPre a m
  | 0, _ => by simp
  | m + 1, h => by
      have hm : m < d := by omega
      have ih := crtMask_lt ha m (by omega)
      rw [crtMask_succ a hm, crtPre_succ a hm, pow_add]
      have h1 := ha ⟨m, hm⟩
      have : 2 ^ (crtPre a m + a ⟨m, hm⟩ - 1) = 2 ^ crtPre a m * 2 ^ (a ⟨m, hm⟩ - 1) := by
        rw [← pow_add]; congr 1; omega
      rw [this]
      have h2 : 2 ^ (a ⟨m, hm⟩ - 1) * 2 = 2 ^ a ⟨m, hm⟩ := by
        rw [← pow_succ]; congr 1; omega
      have h3 : 1 ≤ 2 ^ (a ⟨m, hm⟩ - 1) := Nat.one_le_two_pow
      rw [← h2]
      nlinarith

lemma crtVal_succ' {m : ℕ} (h : m < d) (F : ℕ) :
    crtVal a s (m + 1) F = (crtVal a s m F && decide (crtDig a ⟨m, h⟩ F < s ⟨m, h⟩)) := by
  simp only [crtVal]
  rw [← Bool.decide_and, decide_eq_decide]
  constructor
  · intro H; exact ⟨fun j hj => H j (by omega), H ⟨m, h⟩ (by simp)⟩
  · rintro ⟨H₁, H₂⟩ j hj
    by_cases hjm : j.val < m
    · exact H₁ j hjm
    · have : j = ⟨m, h⟩ := Fin.ext (by simp; omega)
      subst this; exact H₂

/-- The validity automaton decides `crtVal a s m` on the low `crtPre a m` bits. -/
theorem crtVA_run (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j) :
    ∀ m ≤ d, ∀ (vals : Fin 3 → ℕ) (ok : Bool), vals 1 % 2 ^ crtPre a m = crtSig a s m →
      vals 2 % 2 ^ crtPre a m = crtMask a m →
      (crtVA A).run (crtPre a m) (crtVS ok false) vals = crtVS (ok && crtVal a s m (vals 0)) false
  | 0, _, vals, ok, _, _ => by simp [CAuto.run, crtVal]
  | m + 1, hm, vals, ok, h1, h2 => by
      have h : m < d := by omega
      have ha : ∀ j, 1 ≤ a j := fun j => by
        by_contra hz
        have : a j = 0 := by omega
        have := hs j; rw [‹a j = 0›] at this; omega
      have hsl : ∀ j, s j < 2 ^ a j := fun j => (hs j).2
      set M := 2 ^ crtPre a m with hM
      have hMpos : 0 < M := by positivity
      have hsplit : 2 ^ crtPre a (m + 1) = M * 2 ^ a ⟨m, h⟩ := by
        rw [crtPre_succ a h, pow_add]
      have hmod : ∀ n, n % 2 ^ crtPre a (m + 1) % M = n % M := fun n => by
        rw [hsplit, Nat.mod_mul_right_mod]
      have hdiv : ∀ n, n / M % 2 ^ a ⟨m, h⟩ = n % 2 ^ crtPre a (m + 1) / M := fun n => by
        rw [hsplit, Nat.mod_mul_right_div_self]
      have hsig : crtSig a s (m + 1) = crtSig a s m + s ⟨m, h⟩ * M := crtSig_succ a s h
      have hsigm := crtSig_lt a s hsl m (by omega)
      have hmsk : crtMask a (m + 1) = crtMask a m + 2 ^ (a ⟨m, h⟩ - 1) * M := by
        rw [crtMask_succ a h, hM, ← pow_add]; congr 2; have := ha ⟨m, h⟩; omega
      have hmskm := crtMask_lt a ha m (by omega)
      rw [crtPre_succ a h, crt_run_add,
        crtVA_run hs m (by omega) vals ok (by rw [← hmod, h1, hsig, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt hsigm]) (by rw [← hmod, h2, hmsk, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt hmskm]),
        crtVA_run_field _ _ (ha ⟨m, h⟩)]
      · have hv1 : vals 1 / 2 ^ crtPre a m % 2 ^ a ⟨m, h⟩ = s ⟨m, h⟩ := by
          rw [← hM, hdiv, h1, hsig, Nat.add_mul_div_right _ _ hMpos, Nat.div_eq_of_lt hsigm,
            Nat.zero_add]
        rw [crtVal_succ' a s h, Bool.and_assoc, hv1]
        rfl
      · show vals 2 / 2 ^ crtPre a m % 2 ^ a ⟨m, h⟩ = 2 ^ (a ⟨m, h⟩ - 1)
        rw [← hM, hdiv, h2, hmsk, Nat.add_mul_div_right _ _ hMpos, Nat.div_eq_of_lt hmskm,
          Nat.zero_add]

lemma crtSig_mod_pre (hs : ∀ j, s j < 2 ^ a j) {i : ℕ} (hid : i ≤ d) :
    ∀ m, i ≤ m → m ≤ d → crtSig a s m % 2 ^ crtPre a i = crtSig a s i := by
  intro m him hmd
  induction m, him using Nat.le_induction with
  | base => exact Nat.mod_eq_of_lt (crtSig_lt a s hs i hid)
  | succ m hm ih =>
      have h : m < d := by omega
      rw [crtSig_succ a s h]
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (crtPre_mono a hm)
      rw [he, pow_add, show crtSig a s m + s ⟨m, h⟩ * (2 ^ crtPre a i * 2 ^ e) =
        crtSig a s m + 2 ^ crtPre a i * (s ⟨m, h⟩ * 2 ^ e) by ring, Nat.add_mul_mod_self_left,
        ih (by omega)]

lemma crtMask_mod_pre (ha : ∀ j, 1 ≤ a j) {i : ℕ} (hid : i ≤ d) :
    ∀ m, i ≤ m → m ≤ d → crtMask a m % 2 ^ crtPre a i = crtMask a i := by
  intro m him hmd
  induction m, him using Nat.le_induction with
  | base => exact Nat.mod_eq_of_lt (crtMask_lt a ha i hid)
  | succ m hm ih =>
      have h : m < d := by omega
      rw [crtMask_succ a h]
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (crtPre_mono a hm)
      have h1 := ha ⟨m, h⟩
      rw [show crtPre a m + a ⟨m, h⟩ - 1 = crtPre a i + (e + (a ⟨m, h⟩ - 1)) by omega, pow_add,
        Nat.add_mul_mod_self_left, ih (by omega)]

end Auto

end IntegerMultBounds.MathlibTM2.Fast
