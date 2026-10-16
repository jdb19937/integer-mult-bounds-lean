module

public import IntegerMultBounds.MathlibTM2.Layer.Enc
public import IntegerMultBounds.MathlibTM2.Layer.GaussStream
public import IntegerMultBounds.MathlibTM2.Host.IndexRoute

/-!
# The leaf: doubled kernels on address bits

Host programs applying the doubled kernel `k2` (`IntegerMultBounds.MathlibTM2.Layer.NodeZ`) to a stored
Gaussian-integer array `Z : ZArr (Fin R × Fin r) n`, held on a register as `encZ A w Z`
(`IntegerMultBounds.MathlibTM2.Layer.Enc`): records of `r w` symbols, row by row, the `2^n` addresses of a row in
increasing order.

**One kernel pass** (`kernelPass`, `kernelPass_exec`) applies `k2` on the address bit `t` held by
a mask register (`binSyms n (2 ^ t)`, `t < n`). It routes the records by bit `t` of their address
(`routeIdx` with the code automaton `bitAuto` reading a one-field address counter and the mask),
brings both classes to forward order, runs `GR.kernel2` on them (`kernel2_exec`), brings the two
outputs to forward order and merges them back with the same code (`mergeIdx`). Record `k` of the
bit-0 class and record `k` of the bit-1 class sit at addresses `p` and `flip t p` of one row
(`bitClass_one`), so the two outputs are the two classes of `k2 t Z`
(`zipWith_bitClassCoeffs_fst`, `zipWith_bitClassCoeffs_snd`). Every register other than the array
ends as it started; the address counter wraps to `0` after the `R 2^n` records. At most
`R 2^n (29 r w + 20 n + 36) + 18` steps.

**The leaf** (`leafProg`, `leafProg_exec`) runs `u` kernel passes, counted by the `u` symbols of a
register `ur`; between two passes `shiftMask` moves the mask bit up by `K`, the length of a
register `kr`. From the mask bit `ρ + K c₀` it applies `k2` on the bits `ρ + K (c₀ + i)`, `i < u`,
in increasing order of `i` (`k2l`, with the defining equations of `IntegerMultBounds.MathlibTM2.Layer.k2s`). At most
`u (R 2^n (29 r w + 20 n + 36) + 10 n + 33) + 4` steps.

Register interface: `KReg` names the registers of a kernel pass and `KAux` states the contents of
its auxiliary registers; `LReg` adds `kr`, `ur` and the spare `ut`. Register maps are injective.
The code automaton and the Gaussian automaton keep their state in the scan slot of the spare
`tmp`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Host


/-! ### Bit arithmetic -/

/-- Adding `2 ^ t` to a number with bit `t` clear sets bit `t` and keeps the other bits. -/
private lemma testBit_add_two_pow {a t : ℕ} (ha : a.testBit t = false) (j : ℕ) :
    (a + 2 ^ t).testBit j = (a.testBit j ^^ decide (j = t)) := by
  have hb : a % 2 ^ t < 2 ^ t := Nat.mod_lt _ (Nat.two_pow_pos t)
  have ha' : a = 2 ^ t * (a / 2 ^ t) + a % 2 ^ t := (Nat.div_add_mod a (2 ^ t)).symm
  have h1 : a + 2 ^ t = 2 ^ t * (a / 2 ^ t + 1) + a % 2 ^ t := by
    conv_lhs => rw [ha']
    ring
  have hm : (a / 2 ^ t).testBit 0 = false := by
    rw [Nat.testBit_div_two_pow]; simpa using ha
  rw [h1, Nat.testBit_two_pow_mul_add _ hb]
  conv_rhs => rw [ha', Nat.testBit_two_pow_mul_add _ hb]
  by_cases hj : j < t
  · simp [hj, show j ≠ t by omega]
  · simp only [hj, ite_false]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hj)
    simp only [Nat.add_sub_cancel_left]
    set m := a / 2 ^ t
    have hm2 : m % 2 = 0 := by
      rw [Nat.testBit_zero] at hm; simpa using hm
    cases k with
    | zero =>
        clear h1 ha' hb
        simp only [Nat.add_zero, Nat.testBit_zero]
        have : (m + 1) % 2 = 1 := by omega
        simp [this, hm2]
    | succ k =>
        rw [Nat.testBit_add_one, Nat.testBit_add_one, show (m + 1) / 2 = m / 2 by omega]
        simp

/-- Setting a clear bit `t < n` keeps the quotient by `2 ^ n`. -/
private lemma div_add_two_pow {a t n : ℕ} (ht : t < n) (ha : a.testBit t = false) :
    (a + 2 ^ t) / 2 ^ n = a / 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, testBit_add_two_pow ha]
  simp [show j + n ≠ t by omega]

private lemma addrBits_mod {n : ℕ} (a : ℕ) : addrBits n (a % 2 ^ n) = addrBits n a := by
  funext j
  simp [addrBits, Nat.testBit_mod_two_pow, j.isLt]

/-- Setting a clear address bit `t` flips bit `t` of the bit vector. -/
private lemma addrBits_add_two_pow {n t a : ℕ} (ht : t < n) (ha : a.testBit t = false) :
    addrBits n (a + 2 ^ t) = Layer.flip ⟨t, ht⟩ (addrBits n a) := by
  funext j
  simp only [addrBits, Layer.flip, Pi.add_apply, Pi.single_apply, testBit_add_two_pow ha]
  by_cases hj : (j : ℕ) = t
  · have hj' : j = ⟨t, ht⟩ := Fin.ext hj
    subst hj'
    simp [ha]
  · have hj' : j ≠ ⟨t, ht⟩ := fun e => hj (by rw [e])
    simp [hj, hj']

/-! ### Records -/

variable {R r n w : ℕ}

/-- Record `i` of an array in stream order (empty past the end). -/
def recAt (w : ℕ) (Z : ZArr (Fin R × Fin r) n) (i : ℕ) : List (GR w) := (recList w Z).getD i []

/-- Record `i` is the record of row `i / 2 ^ n` at the address with bits `addrBits n i`. -/
lemma recAt_eq (Z : ZArr (Fin R × Fin r) n) {i : ℕ} (hi : i < R * 2 ^ n) :
    recAt w Z i = List.ofFn fun c : Fin r =>
      red w (Z ((⟨i / 2 ^ n, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)).2 hi⟩, c),
        addrBits n i)) := by
  have hu : i / 2 ^ n < R := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)).2 hi
  have ha : i % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have key : ∀ j (hj : j < (recList w Z).length), j = 2 ^ n * (i / 2 ^ n) + i % 2 ^ n →
      (recList w Z)[j] = List.ofFn fun c : Fin r =>
        red w (Z ((⟨i / 2 ^ n, hu⟩, c), addrBits n (i % 2 ^ n))) := by
    intro j hj e
    subst e
    simp only [recList]
    rw [getElem_flatMap_const _ (2 ^ n) (by simp) _ (i / 2 ^ n) (i % 2 ^ n) (by simpa using hu) ha]
    simp
  have hlen : i < (recList w Z).length := by rw [length_recList]; exact hi
  rw [recAt, List.getD_eq_getElem _ _ hlen, key i hlen (Nat.div_add_mod i (2 ^ n)).symm,
    addrBits_mod]

lemma length_recAt (Z : ZArr (Fin R × Fin r) n) {i : ℕ} (hi : i < R * 2 ^ n) :
    (recAt w Z i).length = r := by
  rw [recAt_eq Z hi]; simp

private lemma add_two_pow_lt {i t : ℕ} (ht : t < n) (hb : i.testBit t = false)
    (hi : i < R * 2 ^ n) : i + 2 ^ t < R * 2 ^ n := by
  have h1 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)).2 hi
  rw [← div_add_two_pow ht hb] at h1
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)).1 h1

private lemma red_k2 (t : Fin n) (Z : ZArr (Fin R × Fin r) n)
    (p : (Fin R × Fin r) × (Fin n → ZMod 2)) :
    red w (k2 t Z p) =
      GR.mulG 1 1 (red w (Z p)) + GR.mulG 1 (-1) (red w (Z (p.1, Layer.flip t p.2))) := by
  rw [k2, red_add, red_mulG, red_mulG]

/-- The doubled kernel on a record pair: the record with bit `t` clear. -/
lemma recAt_k2_lo (Z : ZArr (Fin R × Fin r) n) {t i : ℕ} (ht : t < n) (hb : i.testBit t = false)
    (hi : i < R * 2 ^ n) :
    recAt w (k2 ⟨t, ht⟩ Z) i =
      List.zipWith (fun u v => (GR.kernel2 u v).1) (recAt w Z i) (recAt w Z (i + 2 ^ t)) := by
  have hi' := add_two_pow_lt ht hb hi
  rw [recAt_eq _ hi, recAt_eq _ hi, recAt_eq _ hi']
  apply List.ext_getElem (by simp)
  intro c h1 h2
  simp only [List.getElem_ofFn, List.getElem_zipWith, red_k2, GR.kernel2,
    addrBits_add_two_pow ht hb]
  congr 4
  simp only [div_add_two_pow ht hb]

/-- The doubled kernel on a record pair: the record with bit `t` set. -/
lemma recAt_k2_hi (Z : ZArr (Fin R × Fin r) n) {t i : ℕ} (ht : t < n) (hb : i.testBit t = false)
    (hi : i < R * 2 ^ n) :
    recAt w (k2 ⟨t, ht⟩ Z) (i + 2 ^ t) =
      List.zipWith (fun u v => (GR.kernel2 u v).2) (recAt w Z i) (recAt w Z (i + 2 ^ t)) := by
  have hi' := add_two_pow_lt ht hb hi
  rw [recAt_eq _ hi', recAt_eq _ hi, recAt_eq _ hi']
  apply List.ext_getElem (by simp)
  intro c h1 h2
  simp only [List.getElem_ofFn, List.getElem_zipWith, red_k2, GR.kernel2,
    addrBits_add_two_pow ht hb, Layer.flip_flip]
  rw [add_comm]
  congr 4
  simp only [div_add_two_pow ht hb]

/-! ### Lists of blocks -/

section Lists

variable {α β γ δ : Type}

/-- Block `m` of `l.flatMap f`, all pieces of length `k`, is the piece of element `m` of `l`. -/
private lemma blk_flatMap {f : α → List β} {k : ℕ} : ∀ {l : List α}, (∀ x ∈ l, (f x).length = k) →
    ∀ m, blk (l.flatMap f) k m = (blk l 1 m).flatMap f
  | [], _, m => by simp [blk]
  | x :: l, hf, m => by
      have hx := hf x List.mem_cons_self
      cases m with
      | zero => simp [blk, List.take_left' hx]
      | succ m =>
          have ih := blk_flatMap (l := l) (fun y hy => hf y (List.mem_cons_of_mem _ hy)) m
          rw [blk, List.flatMap_cons, show (m + 1) * k = (f x).length + m * k by rw [hx]; ring,
            List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
            Nat.add_sub_cancel_left]
          rw [blk] at ih
          rw [ih]
          simp [blk]

private lemma flatten_flatMap' (g : α → List β) : ∀ L : List (List α),
    L.flatten.flatMap g = L.flatMap (fun l => l.flatMap g)
  | [] => rfl
  | l :: L => by simp [List.flatMap_append, flatten_flatMap' g L]

private lemma length_flatten_map {g : ℕ → List α} {k : ℕ} :
    ∀ {l : List ℕ}, (∀ i ∈ l, (g i).length = k) → ((l.map g).flatten).length = l.length * k
  | [], _ => by simp
  | i :: l, h => by
      rw [List.map_cons, List.flatten_cons, List.length_append, h i List.mem_cons_self,
        length_flatten_map (fun j hj => h j (List.mem_cons_of_mem _ hj))]
      simp; ring

/-- `zipWith` of two concatenations of pieces of equal lengths, piece by piece. -/
private lemma zipWith_flatten_map {f : γ → γ → δ} {g₁ g₂ : ℕ → List γ} : ∀ {l : List ℕ},
    (∀ i ∈ l, (g₁ i).length = (g₂ i).length) →
    List.zipWith f (l.map g₁).flatten (l.map g₂).flatten =
      (l.map fun i => List.zipWith f (g₁ i) (g₂ i)).flatten
  | [], _ => by simp
  | i :: l, h => by
      rw [List.map_cons, List.map_cons, List.flatten_cons, List.flatten_cons,
        List.zipWith_append (h i List.mem_cons_self),
        zipWith_flatten_map (fun j hj => h j (List.mem_cons_of_mem _ hj))]
      simp

/-- Blocks of length one are singletons. -/
private lemma blocksIdx_one {nd : ℕ} (l : List α) (x₀ : α) (nb : ℕ) (code : ℕ → Fin nd) (d : Fin nd)
    (hl : nb ≤ l.length) :
    blocksIdx l 1 nb code 0 d =
      ((List.range nb).filter fun i => code i = d).map fun i => l.getD i x₀ := by
  unfold blocksIdx
  simp only [Nat.zero_add]
  rw [← List.flatMap_pure_eq_map]
  apply List.flatMap_congr
  intro i hi
  have hi' : i < l.length := by
    have := List.mem_range.1 (List.mem_filter.1 hi).1; omega
  rw [blk, Nat.mul_one, List.drop_eq_getElem_cons hi', Function.comp_apply,
    List.getD_eq_getElem _ _ hi']
  rfl

end Lists

/-! ### The two classes of an address bit -/

/-- Bit `t` of a record index as a destination code. -/
def bitCode (t i : ℕ) : Fin 2 := if i.testBit t then 1 else 0

private lemma bitCode_block (t q j : ℕ) (hj : j < 2 ^ (t + 1)) :
    bitCode t (q * 2 ^ (t + 1) + j) = bitCode t j := by
  unfold bitCode
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hj]
  simp

private lemma bitCode_low {t j : ℕ} (hj : j < 2 ^ t) : bitCode t j = 0 := by
  simp [bitCode, Nat.testBit_lt_two_pow hj]

private lemma bitCode_high {t j : ℕ} (hj : j < 2 ^ t) : bitCode t (2 ^ t + j) = 1 := by
  simp [bitCode, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj]

/-- The indices below `M 2^(t+1)` with bit `t` equal to `d`, in increasing order. -/
lemma filter_bitCode (t M : ℕ) (d : Fin 2) :
    (List.range (M * 2 ^ (t + 1))).filter (fun i => bitCode t i = d) =
      (List.range M).flatMap fun q =>
        (List.range (2 ^ t)).map fun j => q * 2 ^ (t + 1) + d.val * 2 ^ t + j := by
  induction M with
  | zero => simp
  | succ M ih =>
      have h2 : List.range (2 ^ (t + 1)) =
          List.range (2 ^ t) ++ (List.range (2 ^ t)).map (2 ^ t + ·) := by
        rw [pow_succ, mul_two, List.range_add]
      rw [Nat.succ_mul, List.range_add, List.filter_append, ih, List.range_succ,
        List.flatMap_append]
      congr 1
      rw [List.filter_map, h2, List.filter_append, List.filter_map]
      have hlo : ∀ j ∈ List.range (2 ^ t),
          ((fun i => decide (bitCode t i = d)) ∘ (M * 2 ^ (t + 1) + ·)) j = decide (d = 0) := by
        intro j hj
        have hj' := List.mem_range.1 hj
        simp only [Function.comp_apply]
        rw [bitCode_block t M j (by rw [pow_succ]; omega), bitCode_low hj']
        simp [eq_comm]
      have hhi : ∀ j ∈ List.range (2 ^ t),
          (((fun i => decide (bitCode t i = d)) ∘ (M * 2 ^ (t + 1) + ·)) ∘ (2 ^ t + ·)) j =
            decide (d = 1) := by
        intro j hj
        have hj' := List.mem_range.1 hj
        simp only [Function.comp_apply]
        rw [bitCode_block t M _ (by rw [pow_succ]; omega), bitCode_high hj']
        simp [eq_comm]
      rw [List.filter_congr hlo, List.filter_congr hhi]
      fin_cases d
      · simp
      · simp [List.map_map, Function.comp_def, Nat.add_assoc]


/-- The record indices below `N` with bit `t` equal to `d`, in increasing order. -/
def bitClass (t N : ℕ) (d : Fin 2) : List ℕ := (List.range N).filter fun i => bitCode t i = d

private lemma pow_split {t n : ℕ} (ht : t < n) : 2 ^ n = 2 ^ (n - (t + 1)) * 2 ^ (t + 1) := by
  rw [← pow_add]; congr 1; omega

/-- The bit-1 class is the bit-0 class shifted by `2 ^ t`: record `k` of each class sits at the
addresses `p` and `flip t p` of one row. -/
lemma bitClass_one {t : ℕ} (ht : t < n) (R : ℕ) :
    bitClass t (R * 2 ^ n) 1 = (bitClass t (R * 2 ^ n) 0).map (· + 2 ^ t) := by
  rw [bitClass, bitClass, pow_split ht, ← Nat.mul_assoc, filter_bitCode, filter_bitCode,
    List.map_flatMap]
  refine List.flatMap_congr fun q _ => ?_
  simp only [List.map_map, Function.comp_def]
  congr 1
  funext j
  simp; ring

lemma mem_bitClass {t N i : ℕ} {d : Fin 2} (h : i ∈ bitClass t N d) : i < N ∧ bitCode t i = d := by
  simpa [bitClass] using h

private lemma testBit_of_bitCode {t i : ℕ} (h : bitCode t i = 0) : i.testBit t = false := by
  unfold bitCode at h
  by_contra h'
  simp [h'] at h

private lemma length_of_mem_recList {Z : ZArr (Fin R × Fin r) n} {x : List (GR w)}
    (hx : x ∈ recList w Z) : x.length = r := by
  simp only [recList, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨_, _, _, _, rfl⟩ := hx
  simp

lemma encZ_eq_flatMap (A : ℕ) (Z : ZArr (Fin R × Fin r) n) :
    encZ A w Z = (recList w Z).flatMap fun rec => rec.flatMap (coeffSyms A w) := by
  rw [encZ, coeffList, flatten_flatMap']

/-- The records of class `d`, as a coefficient list. -/
def bitClassCoeffs (w t : ℕ) (Z : ZArr (Fin R × Fin r) n) (d : Fin 2) : List (GR w) :=
  ((bitClass t (R * 2 ^ n) d).map (recAt w Z)).flatten

/-- Routing the stream of an array by bit `t` of the record index gives the coefficient lists
of the two classes. -/
lemma blocksIdx_encZ (A t : ℕ) (Z : ZArr (Fin R × Fin r) n) (d : Fin 2) :
    blocksIdx (encZ A w Z) (r * w) (R * 2 ^ n) (bitCode t) 0 d =
      (bitClassCoeffs w t Z d).flatMap (coeffSyms A w) := by
  have hf : ∀ x ∈ recList w Z, (x.flatMap (coeffSyms A w)).length = r * w := by
    intro x hx
    rw [length_flatMap_const _ w (length_coeffSyms A w), length_of_mem_recList hx]
  have h1 : blocksIdx ((recList w Z).flatMap fun rec => rec.flatMap (coeffSyms A w)) (r * w)
      (R * 2 ^ n) (bitCode t) 0 d =
      (blocksIdx (recList w Z) 1 (R * 2 ^ n) (bitCode t) 0 d).flatMap
        fun rec => rec.flatMap (coeffSyms A w) := by
    unfold blocksIdx
    rw [List.flatMap_assoc]
    exact List.flatMap_congr fun m _ => blk_flatMap hf m
  rw [bitClassCoeffs, flatten_flatMap', encZ_eq_flatMap, h1,
    blocksIdx_one _ [] _ _ _ (by rw [length_recList])]
  simp only [List.flatMap_map]
  rfl

lemma length_bitClassCoeffs (t : ℕ) (Z : ZArr (Fin R × Fin r) n) (d : Fin 2) :
    (bitClassCoeffs w t Z d).length = (bitClass t (R * 2 ^ n) d).length * r :=
  length_flatten_map fun _ hi => length_recAt Z (mem_bitClass hi).1

lemma length_bitClass_le (t N : ℕ) (d : Fin 2) : (bitClass t N d).length ≤ N := by
  simpa [bitClass] using List.length_filter_le (fun i => decide (bitCode t i = d)) (List.range N)

/-- The kernel on the classes: the first output of `GR.kernel2` on the aligned classes of `Z`
is class `0` of `k2 t Z`. -/
lemma zipWith_bitClassCoeffs_fst {t : ℕ} (ht : t < n) (Z : ZArr (Fin R × Fin r) n) :
    List.zipWith (fun u v => (GR.kernel2 u v).1) (bitClassCoeffs w t Z 0) (bitClassCoeffs w t Z 1) =
      bitClassCoeffs w t (k2 ⟨t, ht⟩ Z) 0 := by
  rw [bitClassCoeffs, bitClassCoeffs, bitClassCoeffs, bitClass_one ht, List.map_map,
    zipWith_flatten_map (fun i hi => by
      have h := mem_bitClass hi
      rw [Function.comp_apply, length_recAt Z h.1,
        length_recAt Z (add_two_pow_lt ht (testBit_of_bitCode h.2) h.1)])]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have h := mem_bitClass hi
  exact (recAt_k2_lo Z ht (testBit_of_bitCode h.2) h.1).symm

lemma zipWith_bitClassCoeffs_snd {t : ℕ} (ht : t < n) (Z : ZArr (Fin R × Fin r) n) :
    List.zipWith (fun u v => (GR.kernel2 u v).2) (bitClassCoeffs w t Z 0) (bitClassCoeffs w t Z 1) =
      bitClassCoeffs w t (k2 ⟨t, ht⟩ Z) 1 := by
  rw [bitClassCoeffs, bitClassCoeffs, bitClassCoeffs, bitClass_one ht, List.map_map, List.map_map,
    zipWith_flatten_map (fun i hi => by
      have h := mem_bitClass hi
      rw [Function.comp_apply, length_recAt Z h.1,
        length_recAt Z (add_two_pow_lt ht (testBit_of_bitCode h.2) h.1)])]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have h := mem_bitClass hi
  exact (recAt_k2_hi Z ht (testBit_of_bitCode h.2) h.1).symm

lemma length_bitClassCoeffs_one {t : ℕ} (ht : t < n) (Z : ZArr (Fin R × Fin r) n) :
    (bitClassCoeffs w t Z 1).length = (bitClassCoeffs w t Z 0).length := by
  rw [length_bitClassCoeffs, length_bitClassCoeffs, bitClass_one ht, List.length_map]

/-! ### The code automaton of an address bit -/

variable {A : ℕ}

/-- The code automaton of an address bit: on the bits of the address field and of a mask, it
records whether some bit is set in both. -/
def bitAuto (A : ℕ) : CAuto A 2 2 where
  init := 0
  step s b := if b 0 && b 1 then 1 else s
  out s := if s = 1 then 1 else 0

private lemma foldl_hit (P : ℕ → Bool) (x : Fin (A + 4)) : ∀ (l : List ℕ) (s : Fin (A + 4)),
    l.foldl (fun s j => if P j then x else s) s = if l.any P then x else s
  | [], s => by simp
  | j :: l, s => by
      rw [List.foldl_cons, foldl_hit P x l]
      by_cases h : P j <;> simp [h]

/-- With the address field (one field of `n` bits) and the mask `2 ^ t`, `t < n`, the code of
record index `i` is bit `t` of `i`. -/
lemma idxCode_bitAuto {t n : ℕ} (ht : t < n) :
    idxCode (bitAuto A) n (fun _ : Fin 1 => n) ![.inl 0, .inr (2 ^ t)] = bitCode t := by
  funext i
  have hd : digit (fun _ : Fin 1 => n) 0 i = i % 2 ^ n := by
    simp [digit, fieldOff_zero _ (0 : Fin 1) rfl]
  have hstep : (fun s j => (bitAuto A).step s fun r =>
      (regVal (fun _ : Fin 1 => n) ![.inl 0, .inr (2 ^ t)] i r).testBit j) =
      fun s j => if (decide (j < n) && i.testBit j && decide (t = j)) then 1 else s := by
    funext s j
    simp [bitAuto, regVal, hd, Nat.testBit_two_pow]
  have hany : (List.range n).any (fun j => decide (j < n) && i.testBit j && decide (t = j)) =
      i.testBit t := by
    rw [Bool.eq_iff_iff, List.any_eq_true]
    constructor
    · rintro ⟨j, _, hj⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
      rw [hj.2]; exact hj.1.2
    · intro h
      exact ⟨t, List.mem_range.2 ht, by simp [ht, h]⟩
  simp only [idxCode, CAuto.eval, CAuto.run_eq_foldl, hstep, foldl_hit, hany]
  unfold bitCode
  by_cases h : i.testBit t <;> simp [h, bitAuto]


/-! ### The kernel pass -/

/-- Registers of a kernel pass. -/
inductive KReg
  | arr | mask | cf | tm0 | tm1 | rctr | wctr | tmp | cnt | ctmp | r0 | r1 | e0 | e1 | o0 | o1
  deriving DecidableEq

section Machine

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack

variable {T Q : ℕ} {U P : Type} (body : P → Pr P T Q A U)

private lemma inj_two {a b : Fin T} (h : a ≠ b) : Function.Injective ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- A register file that agrees with `Rg` outside four registers is four updates of `Rg`. -/
private lemma update_frame4 {α : Type} {Rg Rg' : Fin T → α} (a b c d : Fin T) (va vb vc vd : α)
    (ha : Rg' a = va) (hb : Rg' b = vb) (hc : Rg' c = vc) (hd : Rg' d = vd)
    (hrest : ∀ k, k ≠ a → k ≠ b → k ≠ c → k ≠ d → Rg' k = Rg k) :
    Rg' = Function.update (Function.update (Function.update (Function.update Rg a va) b vb) c vc)
      d vd := by
  funext k
  by_cases h4 : k = d
  · subst h4; simp [hd]
  by_cases h3 : k = c
  · subst h3; simp [h4, hc]
  by_cases h2 : k = b
  · subst h2; simp [h4, h3, hb]
  by_cases h1 : k = a
  · subst h1; simp [h4, h3, h2, ha]
  simp [h1, h2, h3, h4, hrest k h1 h2 h3 h4]

/-- The auxiliary registers of a kernel pass: the address counter at `0`, the record counter
`rctr` (`r w` symbols), the word counter `wctr` (`w` symbols), the record count `cnt`
(`N` symbols), and empty spares. -/
structure KAux (reg : KReg → Fin T) (n r w N : ℕ) (Rg : Fin T → List (Fin (A + 4))) : Prop where
  cf : Rg (reg .cf) = binSyms n 0
  rctr : (Rg (reg .rctr)).length = r * w
  wctr : (Rg (reg .wctr)).length = w
  cnt : (Rg (reg .cnt)).length = N
  empty : ∀ x ∈ [KReg.tm0, .tm1, .tmp, .ctmp, .r0, .r1, .e0, .e1, .o0, .o1], Rg (reg x) = []

/-- One kernel pass: the doubled kernel `k2` on the address bit selected by the mask. -/
def kernelPass (reg : KReg → Fin T) : Pr P T Q A U :=
  .seq (routeIdx (reg .arr) ![reg .r0, reg .r1] (reg .rctr) (reg .tmp) (fun _ : Fin 1 => reg .cf)
      ![reg .cf, reg .mask] ![reg .tm0, reg .tm1] (reg .tmp) (bitAuto A))
  (.seq (moveR (reg .r0) (reg .e0) id)
  (.seq (moveR (reg .r1) (reg .e1) id)
  (.seq (autoWords ![reg .e0, reg .e1] ![reg .o0, reg .o1] (reg .tmp) (reg .wctr) (reg .tmp)
      (gaussAuto A gKernel2 4 false))
  (.seq (moveR (reg .o0) (reg .r0) id)
  (.seq (moveR (reg .o1) (reg .r1) id)
  (.seq (mergeIdx ![reg .r0, reg .r1] (reg .e0) (reg .rctr) (reg .tmp) (reg .cnt) (reg .ctmp)
      (fun _ : Fin 1 => reg .cf) ![reg .cf, reg .mask] ![reg .tm0, reg .tm1] (reg .tmp)
      (bitAuto A))
    (moveR (reg .e0) (reg .arr) id)))))))

variable {reg : KReg → Fin T}

/-- The index layout of the routing step. -/
lemma idxLayout_route (hreg : Function.Injective reg) (n t : ℕ) :
    IdxLayout (fun _ : Fin 1 => reg .cf) (fun _ => n) n ![reg .cf, reg .mask] ![reg .tm0, reg .tm1]
      ![.inl 0, .inr (2 ^ t)] (reg .tmp)
      (routeRegs (reg .arr) ![reg .r0, reg .r1] (reg .rctr) (reg .tmp)) := by
  refine ⟨⟨inj_two (hreg.ne (by decide)), inj_two (hreg.ne (by decide)), ?_, ?_, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hreg.eq_iff]
  · intro i; fin_cases i <;> simp [hreg.eq_iff]
  · intro i; fin_cases i <;> simp [hreg.eq_iff]
  · intro i j _; exact Subsingleton.elim i j
  · intro i j; fin_cases i <;> simp [hreg.eq_iff]
  · intro i f h; fin_cases i <;> simp_all
  · intro i p f h; fin_cases i <;> simp_all [hreg.eq_iff]
  · intro f; simp [routeRegs, hreg.eq_iff, Fin.exists_fin_two]
  · intro i; fin_cases i <;> simp [routeRegs, hreg.eq_iff, Fin.exists_fin_two]
  · intro i; fin_cases i <;> simp [routeRegs, hreg.eq_iff, Fin.exists_fin_two]

/-- The index layout of the merging step. -/
lemma idxLayout_merge (hreg : Function.Injective reg) (n t : ℕ) :
    IdxLayout (fun _ : Fin 1 => reg .cf) (fun _ => n) n ![reg .cf, reg .mask] ![reg .tm0, reg .tm1]
      ![.inl 0, .inr (2 ^ t)] (reg .tmp)
      (mergeRegs ![reg .r0, reg .r1] (reg .e0) (reg .rctr) (reg .tmp) (reg .cnt) (reg .ctmp)) := by
  refine ⟨⟨inj_two (hreg.ne (by decide)), inj_two (hreg.ne (by decide)), ?_, ?_, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hreg.eq_iff]
  · intro i; fin_cases i <;> simp [hreg.eq_iff]
  · intro i; fin_cases i <;> simp [hreg.eq_iff]
  · intro i j _; exact Subsingleton.elim i j
  · intro i j; fin_cases i <;> simp [hreg.eq_iff]
  · intro i f h; fin_cases i <;> simp_all
  · intro i p f h; fin_cases i <;> simp_all [hreg.eq_iff]
  · intro f; simp [mergeRegs, hreg.eq_iff, Fin.exists_fin_two]
  · intro i; fin_cases i <;> simp [mergeRegs, hreg.eq_iff, Fin.exists_fin_two]
  · intro i; fin_cases i <;> simp [mergeRegs, hreg.eq_iff, Fin.exists_fin_two]

/-- The register layout of the Gaussian automaton. -/
lemma autoLayout_kernel (hreg : Function.Injective reg) :
    AutoLayout ![reg .e0, reg .e1] ![reg .o0, reg .o1] (reg .tmp) (reg .wctr) (reg .tmp) := by
  refine ⟨inj_two (hreg.ne (by decide)), inj_two (hreg.ne (by decide)), ?_, ?_, ?_, ?_, ?_,
    hreg.ne (by decide), ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hreg.eq_iff]
  all_goals intro i; fin_cases i <;> simp [hreg.eq_iff]

private lemma length_encZ (A : ℕ) {R r n w : ℕ} (Z : ZArr (Fin R × Fin r) n) :
    (encZ A w Z).length = R * 2 ^ n * (r * w) := by
  rw [encZ, length_flatMap_const _ w (length_coeffSyms A w), length_coeffList]; ring

private lemma length_bitClassSyms {R r n w : ℕ} (t : ℕ) (Z : ZArr (Fin R × Fin r) n) (d : Fin 2) :
    ((bitClassCoeffs w t Z d).flatMap (coeffSyms A w)).length ≤ R * 2 ^ n * (r * w) := by
  rw [length_flatMap_const _ w (length_coeffSyms A w), length_bitClassCoeffs]
  have := length_bitClass_le t (R * 2 ^ n) d
  calc (bitClass t (R * 2 ^ n) d).length * r * w ≤ R * 2 ^ n * r * w := by gcongr
    _ = _ := by ring

private lemma digit_one_field (n : ℕ) (f : Fin 1) (i : ℕ) :
    digit (fun _ : Fin 1 => n) f i = i % 2 ^ n := by
  simp [digit, fieldOff_zero _ f (Nat.lt_one_iff.1 f.isLt)]

/-- **One kernel pass.** The array register holds `encZ A w Z`, the mask register holds
`binSyms n (2 ^ t)` with `t < n`, and the auxiliary registers are as in `KAux`. The pass replaces
the array by `encZ A w (k2 t Z)` and leaves every other register as it was. -/
theorem kernelPass_exec (hreg : Function.Injective reg) (hA : 9 ^ 4 ≤ A + 4) {R r n w : ℕ}
    (hr : 0 < r) (hw : 0 < w) {t : ℕ} (ht : t < n) (Z : ZArr (Fin R × Fin r) n)
    (v : HS T Q A U) (S : Stacks T A) (haux : KAux reg n r w (R * 2 ^ n) S.R)
    (harr : S.R (reg .arr) = encZ A w Z) (hmask : S.R (reg .mask) = binSyms n (2 ^ t)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ R * 2 ^ n * (29 * r * w + 20 * n + 36) + 18 ∧
      Exec body (kernelPass reg) (mk v S) m
        (mk v' { S with R := Function.update S.R (reg .arr) (encZ A w (k2 ⟨t, ht⟩ Z)) }) := by
  have e_tm0 := haux.empty .tm0 (by simp)
  have e_tm1 := haux.empty .tm1 (by simp)
  have e_tmp := haux.empty .tmp (by simp)
  have e_ctmp := haux.empty .ctmp (by simp)
  have e_r0 := haux.empty .r0 (by simp)
  have e_r1 := haux.empty .r1 (by simp)
  have e_e0 := haux.empty .e0 (by simp)
  have e_e1 := haux.empty .e1 (by simp)
  have e_o0 := haux.empty .o0 (by simp)
  have e_o1 := haux.empty .o1 (by simp)
  have hne : ∀ x y : KReg, x ≠ y → reg x ≠ reg y := fun x y h => hreg.ne h
  have hI0 : IdxState (fun _ : Fin 1 => reg .cf) (fun _ => n) n ![reg .cf, reg .mask]
      ![reg .tm0, reg .tm1] ![.inl 0, .inr (2 ^ t)] S.R 0 := by
    refine ⟨fun f => by simp [digit_one_field, haux.cf], fun i p hi => ?_, fun i => ?_⟩
    · fin_cases i
      · simp at hi
      · simp at hi; subst hi; simpa using hmask
    · fin_cases i <;> simp [e_tm0, e_tm1]
  -- 1. route the records by bit `t` of the address
  obtain ⟨v₁, R₁, hu₁, he₁, hsrc₁, hdst₁, hcf₁, hoth₁⟩ := routeIdx_exec body (reg .arr)
    ![reg .r0, reg .r1] (reg .rctr) (reg .tmp) (fun _ : Fin 1 => reg .cf) (fun _ => n) n
    ![reg .cf, reg .mask] ![reg .tm0, reg .tm1] ![.inl 0, .inr (2 ^ t)] (reg .tmp) (bitAuto A)
    (idxLayout_route hreg n t) (by simp [hreg.eq_iff])
    (fun d => by fin_cases d <;> simp [hreg.eq_iff]) (inj_two (hne _ _ (by decide)))
    (Nat.mul_pos hr hw) (length_encZ A Z) haux.rctr v S harr rfl e_tmp hI0
  rw [idxCode_bitAuto ht] at hdst₁
  have hR₁ : R₁ = Function.update (Function.update (Function.update (Function.update S.R
      (reg .arr) []) (reg .r0) ((bitClassCoeffs w t Z 0).flatMap (coeffSyms A w)).reverse)
      (reg .r1) ((bitClassCoeffs w t Z 1).flatMap (coeffSyms A w)).reverse) (reg .cf)
      (S.R (reg .cf)) :=
    update_frame4 _ _ _ _ _ _ _ _ hsrc₁
      (by simpa [e_r0, blocksIdx_encZ] using hdst₁ 0)
      (by simpa [e_r1, blocksIdx_encZ] using hdst₁ 1)
      (by rw [hcf₁ 0, digit_one_field, haux.cf]; simp)
      (fun k h1 h2 h3 h4 => hoth₁ k h1 (fun d => by fin_cases d <;> simp [Ne.symm h2, Ne.symm h3])
        (fun _ => Ne.symm h4))
  -- 2, 3. both classes in forward order
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (reg .r0) (reg .e0) (hne _ _ (by decide)) id v₁
    { S with R := R₁ }
  dsimp only at he₂
  generalize hR₂ : movedR R₁ (reg .r0) (reg .e0) id (R₁ (reg .r0)) = R₂ at he₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body (reg .r1) (reg .e1) (hne _ _ (by decide)) id v₂
    { S with R := R₂ }
  dsimp only at he₃
  generalize hR₃ : movedR R₂ (reg .r1) (reg .e1) id (R₂ (reg .r1)) = R₃ at he₃
  -- 4. the kernel on the aligned classes
  obtain ⟨v₄, m₄, S₄, hu₄, hm₄, he₄, hi₄, ho₄, hl₄, hin0, hin1, hout0, hout1, hoth₄⟩ :=
    kernel2_exec body (autoLayout_kernel hreg) hA hw haux.wctr (bitClassCoeffs w t Z 0)
      (bitClassCoeffs w t Z 1) (length_bitClassCoeffs_one ht Z) v₃ { S with R := R₃ }
      (by rw [← hR₃, ← hR₂, hR₁]; simp [movedR, hreg.eq_iff])
      (by rw [← hR₃, ← hR₂, hR₁]; simp [movedR, hreg.eq_iff, e_tmp])
      (by rw [← hR₃, ← hR₂, hR₁]; simp [movedR, hreg.eq_iff, e_e0])
      (by rw [← hR₃, ← hR₂, hR₁]; simp [movedR, hreg.eq_iff, e_e1])
  obtain ⟨R₄, rfl⟩ : ∃ R₄, S₄ = { S with R := R₄ } := ⟨S₄.R, Stacks.ext hi₄ ho₄ hl₄ rfl⟩
  dsimp only at hin0 hin1 hout0 hout1 hoth₄
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hin0 hin1 hout0 hout1
  rw [zipWith_bitClassCoeffs_fst ht] at hout0
  rw [zipWith_bitClassCoeffs_snd ht] at hout1
  have hR₄ : R₄ = Function.update (Function.update (Function.update (Function.update R₃
      (reg .e0) []) (reg .e1) []) (reg .o0)
      ((bitClassCoeffs w t (k2 ⟨t, ht⟩ Z) 0).flatMap (coeffSyms A w)).reverse) (reg .o1)
      ((bitClassCoeffs w t (k2 ⟨t, ht⟩ Z) 1).flatMap (coeffSyms A w)).reverse :=
    update_frame4 _ _ _ _ _ _ _ _ hin0 hin1
      (by rw [hout0, ← hR₃, ← hR₂, hR₁]; simp [movedR, hreg.eq_iff, e_o0])
      (by rw [hout1, ← hR₃, ← hR₂, hR₁]; simp [movedR, hreg.eq_iff, e_o1])
      (fun k h1 h2 h3 h4 => hoth₄ k
        (by rintro ⟨i, hi⟩; fin_cases i; exacts [h1 hi.symm, h2 hi.symm])
        (by rintro ⟨i, hi⟩; fin_cases i; exacts [h3 hi.symm, h4 hi.symm]))
  -- 5, 6. the outputs in forward order
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body (reg .o0) (reg .r0) (hne _ _ (by decide)) id v₄
    { S with R := R₄ }
  dsimp only at he₅
  generalize hR₅ : movedR R₄ (reg .o0) (reg .r0) id (R₄ (reg .o0)) = R₅ at he₅
  obtain ⟨v₆, hu₆, he₆⟩ := moveR_exec body (reg .o1) (reg .r1) (hne _ _ (by decide)) id v₅
    { S with R := R₅ }
  dsimp only at he₆
  generalize hR₆ : movedR R₅ (reg .o1) (reg .r1) id (R₅ (reg .o1)) = R₆ at he₆
  -- 7. merge the classes back by bit `t` of the address
  obtain ⟨v₇, R₇, hu₇, he₇, hdst₇, hsrc₇, hcf₇, hoth₇⟩ := mergeIdx_exec_blocks body
    ![reg .r0, reg .r1] (reg .e0) (reg .rctr) (reg .tmp) (reg .cnt) (reg .ctmp)
    (fun _ : Fin 1 => reg .cf) (fun _ => n) n ![reg .cf, reg .mask] ![reg .tm0, reg .tm1]
    ![.inl 0, .inr (2 ^ t)] (reg .tmp) (bitAuto A) (idxLayout_merge hreg n t)
    (by simp [hreg.eq_iff]) (fun d => by fin_cases d <;> simp [hreg.eq_iff])
    (inj_two (hne _ _ (by decide))) (l := encZ A w (k2 ⟨t, ht⟩ Z)) (i₀ := 0) (length_encZ A _)
    haux.rctr haux.cnt (fun _ => []) v₆ { S with R := R₆ }
    (by
      intro d
      rw [idxCode_bitAuto ht, blocksIdx_encZ, ← hR₆, ← hR₅, hR₄, ← hR₃, ← hR₂, hR₁]
      fin_cases d <;> simp [movedR, hreg.eq_iff])
    (by
      rw [← hR₆, ← hR₅, hR₄, ← hR₃, ← hR₂, hR₁]
      simp [movedR, hreg.eq_iff])
    (by
      rw [← hR₆, ← hR₅, hR₄, ← hR₃, ← hR₂, hR₁]
      simp [movedR, hreg.eq_iff, e_tmp])
    (by
      rw [← hR₆, ← hR₅, hR₄, ← hR₃, ← hR₂, hR₁]
      simp [movedR, hreg.eq_iff])
    (by
      rw [← hR₆, ← hR₅, hR₄, ← hR₃, ← hR₂, hR₁]
      simp [movedR, hreg.eq_iff, e_ctmp])
    (by
      have h6 : ∀ x, x ≠ KReg.arr → x ≠ .r0 → x ≠ .r1 → x ≠ .e0 → x ≠ .e1 → x ≠ .o0 → x ≠ .o1 →
          R₆ (reg x) = S.R (reg x) := by
        intro x h1 h2 h3 h4 h5 h6 h7
        rw [← hR₆, ← hR₅, hR₄, ← hR₃, ← hR₂, hR₁]
        simp [movedR, Function.update_apply, hreg.eq_iff, h1, h2, h3, h4, h5, h6, h7]
        try (intro h; subst h; rfl)
      have h0 : IdxState (fun _ : Fin 1 => reg .cf) (fun _ => n) n ![reg .cf, reg .mask]
          ![reg .tm0, reg .tm1] ![.inl 0, .inr (2 ^ t)] S.R 0 := hI0
      refine ⟨fun f => ?_, fun i p hi => ?_, fun i => ?_⟩
      · show R₆ (reg .cf) = binSyms n (digit (fun _ => n) f 0)
        rw [h6 .cf (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)]
        exact h0.1 f
      · fin_cases i
        · simp at hi
        · simp at hi; subst hi; simpa [h6 .mask (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)] using hmask
      · fin_cases i
        · simpa [h6 .tm0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)] using e_tm0
        · simpa [h6 .tm1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide)] using e_tm1)
  dsimp only at hdst₇ hsrc₇ hoth₇
  have hR₇ : R₇ = Function.update (Function.update (Function.update (Function.update R₆
      (reg .e0) (encZ A w (k2 ⟨t, ht⟩ Z)).reverse) (reg .r0) []) (reg .r1) []) (reg .cf)
      (S.R (reg .cf)) :=
    update_frame4 _ _ _ _ _ _ _ _
      (by rw [hdst₇, ← hR₆, ← hR₅, hR₄, ← hR₃, ← hR₂, hR₁]
          simp [movedR, hreg.eq_iff, e_e0])
      (hsrc₇ 0) (hsrc₇ 1)
      (by rw [hcf₇ 0, digit_one_field, haux.cf]; simp)
      (fun k h1 h2 h3 h4 => hoth₇ k h1
        (fun d => by fin_cases d; exacts [Ne.symm h2, Ne.symm h3]) (fun _ => Ne.symm h4))
  -- 8. the result in forward order on the array register
  obtain ⟨v₈, hu₈, he₈⟩ := moveR_exec body (reg .e0) (reg .arr) (hne _ _ (by decide)) id v₇
    { S with R := R₇ }
  dsimp only at he₈
  have hfin : movedR R₇ (reg .e0) (reg .arr) id (R₇ (reg .e0)) =
      Function.update S.R (reg .arr) (encZ A w (k2 ⟨t, ht⟩ Z)) := by
    funext k
    rw [hR₇, ← hR₆, ← hR₅, hR₄, ← hR₃, ← hR₂, hR₁]
    by_cases ha : k = reg .arr
    · subst ha; simp [movedR, hreg.eq_iff]
    by_cases h1 : k = reg .e0
    · subst h1; simp [movedR, hreg.eq_iff, e_e0]
    by_cases h2 : k = reg .e1
    · subst h2; simp [movedR, hreg.eq_iff, e_e1]
    by_cases h3 : k = reg .o0
    · subst h3; simp [movedR, hreg.eq_iff, e_o0]
    by_cases h4 : k = reg .o1
    · subst h4; simp [movedR, hreg.eq_iff, e_o1]
    by_cases h5 : k = reg .r0
    · subst h5; simp [movedR, hreg.eq_iff, e_r0]
    by_cases h6 : k = reg .r1
    · subst h6; simp [movedR, hreg.eq_iff, e_r1]
    by_cases h7 : k = reg .cf
    · subst h7; simp [movedR, hreg.eq_iff]
    simp [movedR, Function.update_apply, ha, h1, h2, h3, h4, h5, h6, h7]
  -- step count
  have hl2 : (R₁ (reg .r0)).length ≤ R * 2 ^ n * (r * w) := by
    rw [hR₁]; simpa [Function.update_apply, hreg.eq_iff] using length_bitClassSyms (A := A) t Z 0
  have hl3 : (R₂ (reg .r1)).length ≤ R * 2 ^ n * (r * w) := by
    rw [← hR₂, hR₁]
    simpa [movedR, Function.update_apply, hreg.eq_iff] using length_bitClassSyms (A := A) t Z 1
  have hl5 : (R₄ (reg .o0)).length ≤ R * 2 ^ n * (r * w) := by
    rw [hR₄]
    simpa [Function.update_apply, hreg.eq_iff] using
      length_bitClassSyms (A := A) t (k2 ⟨t, ht⟩ Z) 0
  have hl6 : (R₅ (reg .o1)).length ≤ R * 2 ^ n * (r * w) := by
    rw [← hR₅, hR₄]
    simpa [movedR, Function.update_apply, hreg.eq_iff] using
      length_bitClassSyms (A := A) t (k2 ⟨t, ht⟩ Z) 1
  have hl8 : (R₇ (reg .e0)).length = R * 2 ^ n * (r * w) := by
    rw [hR₇]; simp [hreg.eq_iff, length_encZ]
  have hc0 : (bitClassCoeffs w t Z 0).length * (5 * w + 6) ≤ R * 2 ^ n * (r * w) * 11 := by
    rw [length_bitClassCoeffs]
    have h1 := length_bitClass_le t (R * 2 ^ n) 0
    calc (bitClass t (R * 2 ^ n) 0).length * r * (5 * w + 6) ≤ R * 2 ^ n * r * (11 * w) := by
          gcongr; omega
      _ = R * 2 ^ n * (r * w) * 11 := by ring
  refine ⟨v₈, _, by rw [hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅
      (Exec.seq he₆ (Exec.seq he₇ he₈))))))) rfl (by rw [hfin])⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
  nlinarith

/-! ### Shifting the mask -/

/-- Push `false` onto the mask `ms` and move one symbol of `kr` onto `kt`. -/
def padStep (ms kr kt : Fin T) : Act T Q A U :=
  .push (.rt ms) (fun _ => bitSymbol false) (moveStep kr kt id)

/-- Discard the top of `tmp` and move one symbol of `kt` back onto `kr`. -/
def dropStep (kr kt tmp : Fin T) : Act T Q A U :=
  .pop (.rt tmp) (fun v _ => v) (moveStep kt kr id)

/-- Shift the binary number on `ms` up by `|kr|` bits, keeping its length: push `|kr|` zero bits
on top, then drop as many bits from the bottom (through the spare registers `kt`, `tmp`). -/
def shiftMask (ms kr kt tmp : Fin T) : Pr P T Q A U :=
  .seq (whileR kr (padStep ms kr kt))
  (.seq (moveR ms tmp id)
  (.seq (whileR kt (dropStep kr kt tmp))
    (moveR tmp ms id)))

private lemma replicate_append_cons {α : Type} (k : ℕ) (a : α) (l : List α) :
    List.replicate k a ++ a :: l = a :: (List.replicate k a ++ l) := by
  rw [← List.singleton_append, ← List.append_assoc, ← List.replicate_succ', List.replicate_succ,
    List.cons_append]

/-- The padding loop: `|kr|` zero bits on top of `ms`, `kr` moved onto `kt` reversed. -/
theorem padStep_loop (ms kr kt : Fin T) (h1 : ms ≠ kr) (h2 : ms ≠ kt) (h3 : kr ≠ kt) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.R kr = l → v.flag = l.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (padStep ms kr kt))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := Function.update (Function.update (Function.update S.R kr []) kt
            (l.reverse ++ S.R kt)) ms (List.replicate l.length (bitSymbol false) ++ S.R ms) }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      simp only [List.length_nil, List.reverse_nil, List.nil_append, List.replicate_zero]
      have : ({ S with R := Function.update (Function.update
          (Function.update S.R kr []) kt (S.R kt)) ms (S.R ms) } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          by_cases hk : k = ms
          · subst hk; simp
          · by_cases hk' : k = kt
            · subst hk'; simp [hk]
            · by_cases hk'' : k = kr
              · subst hk''; simp [hk, hk', hS]
              · simp [hk, hk', hk'']
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hu, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
        { S with R := Function.update (Function.update (Function.update S.R ms
          (bitSymbol false :: S.R ms)) kr rest) kt (e :: S.R kt) }
        (by simp [Function.update_of_ne h3]) rfl
      refine ⟨v', hu, ?_⟩
      have hrun : (padStep ms kr kt : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, flag := rest.head?.isSome }
            { S with R := Function.update (Function.update (Function.update S.R ms
              (bitSymbol false :: S.R ms)) kr rest) kt (e :: S.R kt) } := by
        simp [padStep, moveStep, peekR, Action.run, hS, update_rt, 
          Function.update_of_ne h1.symm, Function.update_of_ne h2.symm,
          Function.update_of_ne h3, Function.update_of_ne h3.symm]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (padStep ms kr kt) (mk v S)) he) (by simp; ring) ?_
      congr 2
      funext k
      by_cases hk : k = ms
      · subst hk
        simp [Function.update_of_ne h1, Function.update_of_ne h2, replicate_append_cons,
          List.replicate_succ]
      · by_cases hk' : k = kt
        · subst hk'; simp [hk]
        · by_cases hk'' : k = kr
          · subst hk''; simp [hk, hk']
          · simp [hk, hk', hk'']

/-- The dropping loop: `|kt|` symbols dropped from `tmp`, `kt` moved back onto `kr`. -/
theorem dropStep_loop (kr kt tmp : Fin T) (h1 : tmp ≠ kt) (h2 : tmp ≠ kr) (h3 : kt ≠ kr) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.R kt = l → v.flag = l.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (dropStep kr kt tmp))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := Function.update (Function.update (Function.update S.R kt []) kr
            (l.reverse ++ S.R kr)) tmp ((S.R tmp).drop l.length) }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      simp only [List.length_nil, List.reverse_nil, List.nil_append, List.drop_zero]
      have : ({ S with R := Function.update (Function.update
          (Function.update S.R kt []) kr (S.R kr)) tmp (S.R tmp) } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          by_cases hk : k = tmp
          · subst hk; simp
          · by_cases hk' : k = kr
            · subst hk'; simp [hk]
            · by_cases hk'' : k = kt
              · subst hk''; simp [hk, hk', hS]
              · simp [hk, hk', hk'']
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hu, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
        { S with R := Function.update (Function.update (Function.update S.R tmp
          (S.R tmp).tail) kt rest) kr (e :: S.R kr) }
        (by simp [Function.update_of_ne h3]) rfl
      refine ⟨v', hu, ?_⟩
      have hrun : (dropStep kr kt tmp : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, flag := rest.head?.isSome }
            { S with R := Function.update (Function.update (Function.update S.R tmp
              (S.R tmp).tail) kt rest) kr (e :: S.R kr) } := by
        simp [dropStep, moveStep, peekR, Action.run, hS, update_rt, 
          Function.update_of_ne h1.symm, Function.update_of_ne h2.symm,
          Function.update_of_ne h3, Function.update_of_ne h3.symm]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (dropStep kr kt tmp) (mk v S)) he) (by simp; ring) ?_
      congr 2
      funext k
      by_cases hk : k = tmp
      · subst hk
        simp [Function.update_of_ne h1, Function.update_of_ne h2, List.drop_tail]
      · by_cases hk' : k = kr
        · subst hk'; simp [hk]
        · by_cases hk'' : k = kt
          · subst hk''; simp [hk, hk']
          · simp [hk, hk', hk'']

private lemma take_shift (K n a : ℕ) :
    (List.replicate K (bitSymbol false) ++ binSyms n a : List (Fin (A + 4))).take n =
      binSyms n (a * 2 ^ K) := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_take, List.length_append, List.length_replicate, length_binSyms] at h1
  rw [List.getElem_take, List.getElem_append]
  simp only [binSyms, List.getElem_ofFn, Nat.testBit_mul_two_pow, List.length_replicate]
  by_cases hj : j < K
  · simp [hj, show ¬ K ≤ j by omega]
  · simp [hj, show K ≤ j by omega]

/-- Shifting the mask: the binary number `a` on `ms` (`n` bits) becomes `a 2^|kr|` (`n` bits);
`kr` is restored and the spares `kt`, `tmp` stay empty. Exactly `4 n + 6 |kr| + 8` steps. -/
theorem shiftMask_exec (ms kr kt tmp : Fin T) (h : [ms, kr, kt, tmp].Nodup) (n a : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hms : S.R ms = binSyms n a) (hkt : S.R kt = [])
    (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (shiftMask ms kr kt tmp) (mk v S) (4 * n + 6 * (S.R kr).length + 8)
        (mk v' { S with R := Function.update S.R ms (binSyms n (a * 2 ^ (S.R kr).length)) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩ := h
  -- 1. pad with zeros on top
  obtain ⟨v₁, hu₁, he₁⟩ := padStep_loop body ms kr kt h1 h2 h4 (S.R kr)
    { v with flag := (S.R kr).head?.isSome } S rfl rfl
  have he₁' := Exec.seq (peekR_run kr v S ▸ Exec.act (body := body) (peekR kr) (mk v S)) he₁
  generalize hR₁ : Function.update (Function.update (Function.update S.R kr []) kt
    ((S.R kr).reverse ++ S.R kt)) ms
    (List.replicate (S.R kr).length (bitSymbol false) ++ S.R ms) = R₁ at he₁'
  -- 2. reverse onto `tmp`
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body ms tmp h3 id v₁ { S with R := R₁ }
  dsimp only at he₂
  generalize hR₂ : movedR R₁ ms tmp id (R₁ ms) = R₂ at he₂
  -- 3. drop the low bits, restoring `kr`
  obtain ⟨v₃, hu₃, he₃⟩ := dropStep_loop body kr kt tmp (Ne.symm h6) (Ne.symm h5) (Ne.symm h4)
    (R₂ kt) { v₂ with flag := (R₂ kt).head?.isSome } { S with R := R₂ } rfl rfl
  have he₃' := Exec.seq (peekR_run kt v₂ { S with R := R₂ } ▸
    Exec.act (body := body) (peekR kt) (mk v₂ { S with R := R₂ })) he₃
  dsimp only at he₃'
  generalize hR₃ : Function.update (Function.update (Function.update R₂ kt []) kr
    ((R₂ kt).reverse ++ R₂ kr)) tmp ((R₂ tmp).drop (R₂ kt).length) = R₃ at he₃'
  -- 4. back onto `ms`
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body tmp ms (Ne.symm h3) id v₃ { S with R := R₃ }
  dsimp only at he₄
  have h1' := Ne.symm h1
  have h2' := Ne.symm h2
  have h3' := Ne.symm h3
  have h4' := Ne.symm h4
  have h5' := Ne.symm h5
  have h6' := Ne.symm h6
  have hkt₂ : R₂ kt = (S.R kr).reverse := by
    rw [← hR₂, ← hR₁]
    simp [movedR, h6, h2', h3', h5', h6', hkt]
  have htmp₂ :
      R₂ tmp = (List.replicate (S.R kr).length (bitSymbol false) ++ binSyms n a).reverse := by
    rw [← hR₂, ← hR₁]
    simp [movedR, h3', h5', h6', hms,
      htmp]
  have hms₃ : R₃ ms = [] := by
    rw [← hR₃, ← hR₂]
    simp [movedR, h1, h2, h3, h5, h6, h1', h2']
  have htmp₃ : R₃ tmp = (binSyms n (a * 2 ^ (S.R kr).length)).reverse := by
    rw [← hR₃, htmp₂, hkt₂, List.length_reverse]
    simp only [Function.update_self]
    rw [← List.reverse_reverse (List.drop _ _), List.reverse_drop, List.reverse_reverse,
      List.length_reverse, List.length_append, List.length_replicate, length_binSyms,
      Nat.add_sub_cancel_left, take_shift]
  refine ⟨v₄, by rw [hu₄, hu₃, hu₂, hu₁],
    Exec.cast (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' he₄))) ?_ ?_⟩
  · rw [hkt₂, htmp₃, ← hR₁]
    simp [hms]
    ring
  · congr 2
    funext k
    by_cases hk1 : k = ms
    · subst hk1; simp [movedR, htmp₃, hms₃]
    by_cases hk2 : k = tmp
    · subst hk2; simp [movedR, h3', htmp]
    rw [movedR, Function.update_of_ne hk1, Function.update_of_ne hk2, ← hR₃, ← hR₂, ← hR₁]
    simp [movedR, Function.update_apply, h4, h5, h6, h1', h2', h3', h5', h6',
      hk1, hk2, hkt]
    split_ifs <;> subst_vars <;> simp [hkt]

/-- `KAux` depends only on the registers other than the array and the mask. -/
lemma KAux.of_eq {reg : KReg → Fin T} {n r w N : ℕ} {Rg Rg' : Fin T → List (Fin (A + 4))}
    (h : KAux reg n r w N Rg) (h' : ∀ x, x ≠ .arr → x ≠ .mask → Rg' (reg x) = Rg (reg x)) :
    KAux reg n r w N Rg' :=
  ⟨by rw [h' _ (by decide) (by decide), h.cf], by rw [h' _ (by decide) (by decide), h.rctr],
    by rw [h' _ (by decide) (by decide), h.wctr], by rw [h' _ (by decide) (by decide), h.cnt],
    fun x hx => by
      rw [h' x (by rintro rfl; simp at hx) (by rintro rfl; simp at hx)]
      exact h.empty x hx⟩

/-! ### The leaf -/

/-- The doubled kernels on a list of bits, the first bit first. -/
def k2l {Y : Type} {n : ℕ} : List (Fin n) → ZArr Y n → ZArr Y n
  | [], f => f
  | t :: ts, f => k2l ts (k2 t f)

/-- The bits `s, s + K, …, s + K (m - 1)`. -/
def bitsFrom (n K : ℕ) : (s m : ℕ) → (∀ i < m, s + K * i < n) → List (Fin n)
  | _, 0, _ => []
  | s, m + 1, h => ⟨s, by simpa using h 0 (Nat.succ_pos m)⟩ ::
      bitsFrom n K (s + K) m fun i hi => by
        have := h (i + 1) (by omega)
        rw [show s + K + K * i = s + K * (i + 1) by ring]; exact this

/-- `bitsFrom` as a map over `List.finRange`. -/
lemma bitsFrom_eq (n K : ℕ) : ∀ (m s : ℕ) (h : ∀ i < m, s + K * i < n),
    bitsFrom n K s m h = (List.finRange m).map fun i => ⟨s + K * i, h i i.2⟩
  | 0, _, _ => rfl
  | m + 1, s, h => by
      rw [bitsFrom, bitsFrom_eq n K m, List.finRange_succ, List.map_cons, List.map_map]
      simp only [List.cons.injEq, Fin.val_zero, Nat.mul_zero, Nat.add_zero,
        true_and]
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, Fin.val_succ, Fin.mk.injEq]
      ring

/-- Registers of the leaf: those of a kernel pass, the shift `K` in unary on `kr`, and the pass
counter `ur` with its spare `ut`. -/
inductive LReg
  | k (x : KReg)
  | kr | ur | ut
  deriving DecidableEq

/-- One pass of the leaf: count it, run the kernel pass, and shift the mask when another pass
follows. -/
def leafIter (lreg : LReg → Fin T) : Pr P T Q A U :=
  .seq (.act (moveStep (lreg .ur) (lreg .ut) id))
  (.seq (kernelPass fun x => lreg (.k x))
  (.seq (.act (peekR (lreg .ur)))
  (.seq (.cond (·.flag)
      (shiftMask (lreg (.k .mask)) (lreg .kr) (lreg (.k .ctmp)) (lreg (.k .tmp))) (.act .done))
    (.act (peekR (lreg .ur))))))

/-- The leaf: one kernel pass per symbol of `ur`, on the bits selected by the successive masks;
the counter `ur` is restored at the end. -/
def leafProg (lreg : LReg → Fin T) : Pr P T Q A U :=
  .seq (.act (peekR (lreg .ur)))
  (.seq (.loop (·.flag) (leafIter lreg))
    (moveR (lreg .ut) (lreg .ur) id))

variable {lreg : LReg → Fin T}

/-- The pass loop of the leaf, from the mask bit `s` with the passes left counted by `l`. -/
theorem leafLoop (hreg : Function.Injective lreg) (hA : 9 ^ 4 ≤ A + 4) {R r n w K : ℕ}
    (hr : 0 < r) (hw : 0 < w) :
    ∀ (l : List (Fin (A + 4))) (s : ℕ) (hfit : ∀ i < l.length, s + K * i < n)
      (Z : ZArr (Fin R × Fin r) n) (v : HS T Q A U) (S : Stacks T A),
      S.R (lreg .ur) = l → v.flag = l.head?.isSome →
      KAux (fun x => lreg (.k x)) n r w (R * 2 ^ n) S.R →
      S.R (lreg (.k .arr)) = encZ A w Z → S.R (lreg (.k .mask)) = binSyms n (2 ^ s) →
      (S.R (lreg .kr)).length = K →
      ∃ v' m, v'.user = v.user ∧
        m ≤ l.length * (R * 2 ^ n * (29 * r * w + 20 * n + 36) + 10 * n + 31) + 1 ∧
        Exec body (.loop (·.flag) (leafIter lreg)) (mk v S) m
          (mk v' { S with R := (Function.update (Function.update (Function.update
            (Function.update S.R (lreg .ur) []) (lreg .ut) (l.reverse ++ S.R (lreg .ut)))
            (lreg (.k .mask)) (binSyms n (2 ^ (s + K * (l.length - 1))))) (lreg (.k .arr))
            (encZ A w (k2l (bitsFrom n K s l.length hfit) Z))) }) := by
  have hkreg : Function.Injective fun x => lreg (.k x) := fun x y h => LReg.k.inj (hreg h)
  intro l
  induction l with
  | nil =>
      intro s hfit Z v S hS hf haux harr hmask hK
      refine ⟨v, 1, rfl, by simp, Exec.cast (.loop_false (by simpa using hf)) rfl ?_⟩
      congr 1
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      simp only [List.length_nil, List.reverse_nil, List.nil_append, Nat.zero_sub, Nat.mul_zero,
        Nat.add_zero]
      show S.R k = Function.update (Function.update (Function.update (Function.update S.R
        (lreg .ur) []) (lreg .ut) (S.R (lreg .ut))) (lreg (.k .mask)) (binSyms n (2 ^ s)))
        (lreg (.k .arr)) (encZ A w Z) k
      by_cases h1 : k = lreg (.k .arr)
      · subst h1; simp [harr]
      by_cases h2 : k = lreg (.k .mask)
      · subst h2; simp [h1, hmask]
      by_cases h3 : k = lreg .ut
      · subst h3; simp [h1, h2]
      by_cases h4 : k = lreg .ur
      · subst h4; simp [h1, h2, h3, hS]
      simp [h1, h2, h3, h4]
  | cons e rest ih =>
      intro s hfit Z v S hS hf haux harr hmask hK
      have hs : s < n := by simpa using hfit 0 (by simp)
      have hne : ∀ x y : LReg, x ≠ y → lreg x ≠ lreg y := fun x y h => hreg.ne h
      -- count the pass
      have hrun : (moveStep (lreg .ur) (lreg .ut) id : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, flag := rest.head?.isSome }
            { S with R := (Function.update (Function.update S.R (lreg .ur) rest) (lreg .ut)
              (e :: S.R (lreg .ut))) } := by
        simp [moveStep, peekR, Action.run, hS, update_rt,
          Function.update_of_ne (hne LReg.ur LReg.ut (by decide)),
          Function.update_of_ne (hne LReg.ut LReg.ur (by decide))]
      have hea := hrun ▸ Exec.act (body := body) (moveStep (lreg .ur) (lreg .ut) id) (mk v S)
      generalize hR₁ : Function.update (Function.update S.R (lreg .ur) rest) (lreg .ut)
        (e :: S.R (lreg .ut)) = R₁ at hea
      have hR₁k : ∀ x, R₁ (lreg (.k x)) = S.R (lreg (.k x)) := by
        intro x; rw [← hR₁]; simp [hreg.eq_iff]
      -- the kernel pass on bit `s`
      obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := kernelPass_exec body hkreg hA hr hw hs Z
        { v with sym := some e, flag := rest.head?.isSome } { S with R := R₁ }
        (haux.of_eq fun x _ _ => hR₁k x) (by show R₁ _ = _; rw [hR₁k]; exact harr)
        (by show R₁ _ = _; rw [hR₁k]; exact hmask)
      dsimp only at he₂
      generalize hR₂ : Function.update R₁ (lreg (.k .arr)) (encZ A w (k2 ⟨s, hs⟩ Z)) = R₂ at he₂
      have hR₂ur : R₂ (lreg .ur) = rest := by
        rw [← hR₂, ← hR₁]; simp [hreg.eq_iff]
      have heb := Exec.act (body := body) (peekR (lreg .ur)) (mk v₂ { S with R := R₂ })
      rw [peekR_run] at heb
      dsimp only at heb
      rw [hR₂ur] at heb
      have hR₂k : ∀ x, x ≠ .arr → R₂ (lreg (.k x)) = S.R (lreg (.k x)) := by
        intro x hx; rw [← hR₂, ← hR₁]; simp [hreg.eq_iff, hx]
      rcases rest with _ | ⟨e', rest'⟩
      · -- the last pass: no shift
        have hec := Exec.cond_false (body := body) (f := (·.flag))
          (p := shiftMask (lreg (.k .mask)) (lreg .kr) (lreg (.k .ctmp)) (lreg (.k .tmp))) rfl
          (Exec.act (body := body) .done
            (mk { v₂ with flag := ([] : List (Fin (A + 4))).head?.isSome } { S with R := R₂ }))
        have hed := Exec.act (body := body) (peekR (lreg .ur))
          (Action.done.run (mk { v₂ with flag := ([] : List (Fin (A + 4))).head?.isSome }
            { S with R := R₂ }))
        rw [run_done, peekR_run] at hed
        dsimp only at hed
        rw [hR₂ur] at hed
        have hiter := Exec.seq hea (Exec.seq he₂ (Exec.seq heb (Exec.seq hec hed)))
        refine ⟨_, _, ?_, ?_, Exec.cast (Exec.loop_true (body := body) (f := (·.flag))
          (by simpa using hf) hiter (Exec.loop_false rfl)) rfl (congrArg (mk _) ?_)⟩
        · simp [hu₂]
        · simp only [List.length_cons, List.length_nil]
          nlinarith
        · congr 1
          funext k
          rw [← hR₂, ← hR₁]
          by_cases h1 : k = lreg (.k .arr)
          · subst h1; simp; rfl
          by_cases h2 : k = lreg (.k .mask)
          · subst h2; simp [h1, hreg.eq_iff, hmask]
          by_cases h3 : k = lreg .ut
          · subst h3; simp [h1, h2]
          by_cases h4 : k = lreg .ur
          · subst h4; simp [h1, h2, h3]
          simp [h1, h2, h3, h4]
      · -- shift the mask, then the remaining passes
        have hKn : K ≤ n := by have := hfit 1 (by simp); omega
        obtain ⟨v₄, hu₄, he₄⟩ := shiftMask_exec body (lreg (.k .mask)) (lreg .kr) (lreg (.k .ctmp))
          (lreg (.k .tmp)) (by simp [hreg.eq_iff]) n (2 ^ s)
          { v₂ with flag := (e' :: rest').head?.isSome } { S with R := R₂ }
          (by show R₂ _ = _; rw [hR₂k _ (by decide)]; exact hmask)
          (by show R₂ _ = _; rw [hR₂k _ (by decide)]; exact haux.empty .ctmp (by simp))
          (by show R₂ _ = _; rw [hR₂k _ (by decide)]; exact haux.empty .tmp (by simp))
        dsimp only at he₄
        have hK₂ : (R₂ (lreg .kr)).length = K := by
          rw [← hR₂, ← hR₁]; simpa [Function.update_apply, hreg.eq_iff] using hK
        rw [hK₂, ← pow_add] at he₄
        have hec := Exec.cond_true (body := body) (f := (·.flag)) (q := .act .done) rfl he₄
        generalize hR₄ : Function.update R₂ (lreg (.k .mask)) (binSyms n (2 ^ (s + K))) = R₄ at hec
        have hed := Exec.act (body := body) (peekR (lreg .ur)) (mk v₄ { S with R := R₄ })
        rw [peekR_run] at hed
        dsimp only at hed
        have hR₄ur : R₄ (lreg .ur) = e' :: rest' := by
          rw [← hR₄, Function.update_of_ne (hne _ _ (by decide)), hR₂ur]
        rw [hR₄ur] at hed
        have hR₄k : ∀ x, x ≠ .arr → x ≠ .mask → R₄ (lreg (.k x)) = S.R (lreg (.k x)) := by
          intro x hx hx'
          rw [← hR₄, Function.update_of_ne (fun h => hx' (LReg.k.inj (hreg h))), hR₂k x hx]
        have hfit' : ∀ i < (e' :: rest').length, s + K + K * i < n := by
          intro i hi
          have := hfit (i + 1) (by simp at hi ⊢; omega)
          rw [show s + K + K * i = s + K * (i + 1) by ring]; exact this
        obtain ⟨v₆, m₆, hu₆, hm₆, he₆⟩ := ih (s + K) hfit' (k2 ⟨s, hs⟩ Z)
          { v₄ with flag := (e' :: rest').head?.isSome } { S with R := R₄ } hR₄ur rfl
          (haux.of_eq fun x hx hx' => hR₄k x hx hx')
          (by
            show R₄ _ = _
            rw [← hR₄, Function.update_of_ne (hne _ _ (by decide)), ← hR₂]
            simp)
          (by show R₄ _ = _; rw [← hR₄]; simp)
          (by
            show (R₄ _).length = _
            rw [← hR₄, Function.update_of_ne (hne _ _ (by decide))]; exact hK₂)
        have hiter := Exec.seq hea (Exec.seq he₂ (Exec.seq heb (Exec.seq hec hed)))
        refine ⟨v₆, _, by simp [hu₆, hu₄, hu₂], ?_, Exec.cast (Exec.loop_true (body := body)
          (f := (·.flag)) (by simpa using hf) hiter he₆) rfl ?_⟩
        · simp only [List.length_cons] at hm₆ ⊢
          nlinarith
        · congr 2
          funext k
          rw [← hR₄, ← hR₂, ← hR₁]
          by_cases h1 : k = lreg (.k .arr)
          · subst h1; simp; rfl
          by_cases h2 : k = lreg (.k .mask)
          · subst h2
            simp [h1, hreg.eq_iff]
            rw [show s + K + K * rest'.length = s + K * (rest'.length + 1) by ring]
          by_cases h3 : k = lreg .ut
          · subst h3; simp [h1, h2]
          by_cases h4 : k = lreg .ur
          · subst h4; simp [h1, h2, h3]
          simp [h1, h2, h3, h4]

/-- The leaf bits lie below `n`. -/
lemma leaf_lt {n ρ K c₀ u : ℕ} (hfit : 0 < u → ρ + K * (c₀ + u - 1) < n) {i : ℕ} (hi : i < u) :
    ρ + K * (c₀ + i) < n := by
  have h := hfit (by omega)
  have : K * (c₀ + i) ≤ K * (c₀ + u - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **The leaf.** The array register holds `encZ A w Z`, the mask register
`binSyms n (2 ^ (ρ + K c₀))`, the register `kr` holds `K` symbols and `ur` holds `u` symbols, `ut`
is empty, and the kernel-pass auxiliaries are as in `KAux`; the bits `ρ + K (c₀ + i)`, `i < u`,
are below `n`. The leaf applies `k2` on these bits in increasing order of `i`
(`k2l`), leaves the mask at bit `ρ + K (c₀ + u - 1)` (at bit `ρ + K c₀` when `u = 0`), and leaves
every other register as it was. -/
theorem leafProg_exec (hreg : Function.Injective lreg) (hA : 9 ^ 4 ≤ A + 4) {R r n w : ℕ}
    (hr : 0 < r) (hw : 0 < w) {u K ρ c₀ : ℕ} (hfit : 0 < u → ρ + K * (c₀ + u - 1) < n)
    (Z : ZArr (Fin R × Fin r) n) (v : HS T Q A U) (S : Stacks T A)
    (haux : KAux (fun x => lreg (.k x)) n r w (R * 2 ^ n) S.R)
    (harr : S.R (lreg (.k .arr)) = encZ A w Z)
    (hmask : S.R (lreg (.k .mask)) = binSyms n (2 ^ (ρ + K * c₀)))
    (hK : (S.R (lreg .kr)).length = K) (hu : (S.R (lreg .ur)).length = u)
    (hut : S.R (lreg .ut) = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ u * (R * 2 ^ n * (29 * r * w + 20 * n + 36) + 10 * n + 33) + 4 ∧
      Exec body (leafProg lreg) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R (lreg (.k .mask))
          (binSyms n (2 ^ (ρ + K * (c₀ + (u - 1)))))) (lreg (.k .arr))
          (encZ A w (k2l ((List.finRange u).map fun i : Fin u =>
            ⟨ρ + K * (c₀ + i), leaf_lt hfit i.2⟩) Z))) }) := by
  subst hu
  set l := S.R (lreg .ur) with hl
  have hfit' : ∀ i < l.length, ρ + K * c₀ + K * i < n := fun i hi => by
    rw [show ρ + K * c₀ + K * i = ρ + K * (c₀ + i) by ring]; exact leaf_lt hfit hi
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := leafLoop body hreg hA hr hw l (ρ + K * c₀) hfit' Z
    { v with flag := l.head?.isSome } S rfl rfl haux harr hmask hK
  have he₀ := Exec.act (body := body) (peekR (lreg .ur)) (mk v S)
  rw [peekR_run] at he₀
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body (lreg .ut) (lreg .ur) (hreg.ne (by decide)) id v₁
    { S with R := (Function.update (Function.update (Function.update
      (Function.update S.R (lreg .ur) []) (lreg .ut) (l.reverse ++ S.R (lreg .ut)))
      (lreg (.k .mask)) (binSyms n (2 ^ (ρ + K * c₀ + K * (l.length - 1))))) (lreg (.k .arr))
      (encZ A w (k2l (bitsFrom n K (ρ + K * c₀) l.length hfit') Z))) }
  dsimp only at he₂
  have hne : ∀ x y : LReg, x ≠ y → lreg x ≠ lreg y := fun x y h => hreg.ne h
  refine ⟨v₂, _, by simp [hu₂, hu₁], ?_, Exec.cast (Exec.seq he₀ (Exec.seq he₁ he₂)) rfl
    (congrArg (mk _) ?_)⟩
  · simp [hreg.eq_iff, hut]
    nlinarith
  · congr 1
    funext k
    by_cases h1 : k = lreg (.k .arr)
    · subst h1
      simp [movedR, hreg.eq_iff, bitsFrom_eq]
      have hlist : (List.finRange l.length).map (fun i : Fin l.length =>
          (⟨ρ + K * c₀ + K * i, hfit' i i.2⟩ : Fin n)) =
          (List.finRange l.length).map (fun i : Fin l.length =>
            (⟨ρ + K * (c₀ + i), leaf_lt hfit i.2⟩ : Fin n)) :=
        List.map_congr_left fun i _ => Fin.ext (by dsimp only; ring)
      rw [hlist]
    by_cases h2 : k = lreg (.k .mask)
    · subst h2
      simp [movedR, hreg.eq_iff]
      congr 2
      ring
    by_cases h3 : k = lreg .ut
    · subst h3; simp [movedR, hreg.eq_iff, hut]
    by_cases h4 : k = lreg .ur
    · subst h4; simp [movedR, hreg.eq_iff, hut, hl]
    simp [movedR, Function.update_apply, h1, h2, h3, h4]

end Machine

end IntegerMultBounds.MathlibTM2.Node
