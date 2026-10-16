module

public import IntegerMultBounds.MathlibTM2.Fast.SynMath

/-!
# The round records of the layer, computed at run time

Paper §6, proof of `lem:synthetic-transform-cost`. Round `h` of the synthetic transforms applies
the layer `topProg` (`Node/TopProc.lean`) to the selected bits of the round in the layout
`L = layPerm es ℓ K` (`Fast/LayoutMath.lean`). `synRec` is one fixed program that computes the
configuration record `topCfg …` and the piece record `topPcRec K pcs` of round `h` from unary
parameters on its wires.

## Register format (`SynW` wires, unary values are any lists of that length)

Inputs: `p .h` (`h`), `p .K` (`K`), `p .ℓ` (`ℓ`), `p .b` (`b = (ℓ - 1) mod K`), `p .D`
(`D = |es|`), `p .Lg` (the number of long axes), `p .N` (`N = Σ es`), `p .w` (the stream width
`w`). Outputs (empty before): `p .cf` the configuration record reversed (it is moved onto `park`
by one `moveR`), `p .pr` the piece record, `p .kh` the bit stride `K_h`, `p .rh` the offset
`ρ_h`, `p .w2` the working width `w'`. The scratch wires `s i` are empty before and after.

## The records (`synCfg`, `synPcsR`)

The prefix bits of the layout (`|layPre| = a = Lg + b D`, `synA`) are the top `a` address bits;
the layer turns them into rows. The rounds come in three kinds:
* top round `h = ℓ - 1` (`¬ h + 1 < ℓ`): the `Lg` long axes, selected bits `N - Lg, …, N - 1`;
  stride `1`, all bits are top kernels (`q = Lg`, `aT = N - Lg`), no pieces, `2^a` rows;
* low rounds `h < b`: `D` consecutive bits from `N - Lg - (b - h) D`, stride `1`, top kernels,
  `2^a` rows;
* chunk rounds `b ≤ h < ℓ - 1` (`synChunk`): the bits `ρ + K (c₀ + j)`, `j < D`,
  `ρ = (h - b) mod K`, `c₀ = ⌊(h - b)/K⌋ D`, all below the prefix. The highest
  `q₀ = min (46 J) D` of them (`synQK`, `J = ⌊log_m D⌋`, `m = 25³`, `NW ≤ 2^46`) are top
  kernels at `aT = oS + K D'`, `D' = D - q₀`; the rows are the top `a' = a + K q₀` address bits
  (`synAc`), so that `2^a' ≥ NW^J'` for the top level `J' = ⌊log_m D'⌋` of the pieces. The
  remaining `D'` bits are selected by one piece per nonzero base-`m` digit `d_j` of `D'`
  (`synDg`): level `j`, `d_j` leaf bits, offset `oS + K (D' mod m^j)`, on
  `R₂ = 2^X NW^J'` rows (`synR2c`), `X = a' - ⌊log₂ NW^J'⌋` (`synX`, `synLb`), so that
  `2^a' ≤ R₂ < 2^(a'+1)` (`synR2c_ge`, `synR2c_lt` in `SynRecB`): the padding at most doubles
  the volume.

The shift is `s = ⌈D'/2⌉ + q + E` (`D'` the selected bits, `E` the sum of the piece exponents),
the working width is `w' = w + s + D` and `R = 1` row.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Node hiding LReg

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ### The records -/

section Records

/-- The number of `j < t` with `0 < X / k^j`: the passes of a division count by `k`. -/
def synJk (k X t : ℕ) : ℕ := ((List.range t).filter fun j => 0 < X / k ^ j).length

/-- Digit `j` of `D` in base `m = 25³`. -/
def synDg (D j : ℕ) : ℕ := D / m ^ j % m

/-- The number of passes `j < t` of the digit loop with `D / m^j > 0`. -/
def synJ (D t : ℕ) : ℕ := synJk m D t

/-- The bits of one row level: `NW ≤ 2^46`. -/
def synCW : ℕ := 46

/-- The kernel bits `q₀ = min (46 J) D` of a chunk round, as the machine computes them. -/
def synQKn (D J : ℕ) : ℕ := D - (D - synCW * J)

/-- The piece of digit `j`: level `j`, `d_j` leaf bits, base rows `rowsAt (2^X) (J - j)`, offset
`oS + K (D mod m^j)`. -/
noncomputable def synPc (K X D oS J j : ℕ) : TopPc :=
  ⟨j, synDg D j, rowsAt (2 ^ X) (J - j), oS + K * (D % m ^ j)⟩

/-- The pieces of the digits `j < t` with `d_j ≠ 0`, the highest level first. -/
noncomputable def synPcs (K X D oS J t : ℕ) : List TopPc :=
  (List.range t).reverse.filterMap fun j =>
    if synDg D j = 0 then none else some (synPc K X D oS J j)

/-- The exponent sum of the pieces of the digits `j < t`. -/
def synE (G F D t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range t, if synDg D j = 0 then 0 else expSeq G F (synDg D j) j

variable (es : List ℕ) (ℓ K : ℕ)

/-- The number of long axes. -/
abbrev synLg : ℕ := (layLongs es ℓ).length

/-- The number `a = Lg + b D` of prefix bits. -/
def synA : ℕ := synLg es ℓ + layB ℓ K * es.length

/-- Chunk rounds: `b ≤ h < ℓ - 1`. -/
def synChunk (h : ℕ) : Prop := h + 1 < ℓ ∧ layB ℓ K ≤ h

instance (h : ℕ) : Decidable (synChunk ℓ K h) := by unfold synChunk; infer_instance

/-- The bit stride of round `h`. -/
def synKh (h : ℕ) : ℕ := if synChunk ℓ K h then K else 1

/-- The common offset of round `h`. -/
def synRh (h : ℕ) : ℕ := if synChunk ℓ K h then (h - layB ℓ K) % K else 0

/-- The number of selected bits of round `h`. -/
def synDp (h : ℕ) : ℕ := if h + 1 < ℓ then es.length else synLg es ℓ

/-- The offset `oS` of the selected bits `ρ + oS + K i` of round `h`. -/
def synOS (h : ℕ) : ℕ :=
  if h + 1 < ℓ then
    (if h < layB ℓ K then es.sum - synLg es ℓ - (layB ℓ K - h) * es.length
      else K * ((h - layB ℓ K) / K * es.length))
  else es.sum - synLg es ℓ

/-- The top level `J = ⌊log_m D⌋` of `D`. -/
def synJt : ℕ := synJ es.length es.length - 1

/-- The kernel bits `q₀ = min (46 J) D` of a chunk round. -/
def synQK : ℕ := synQKn es.length (synJt es)

/-- The piece bits `D' = D - q₀` of a chunk round. -/
def synDpp : ℕ := es.length - synQK es

/-- The row bits `a' = K q₀ + a` of a chunk round. -/
def synAc : ℕ := K * synQK es + synA es ℓ K

/-- The top level `J' = ⌊log_m D'⌋` of the pieces of a chunk round. -/
def synJp : ℕ := synJ (synDpp es) (synDpp es) - 1

/-- `L = ⌊log₂ NW^J'⌋`: the division count of `NW^J'` by `2` over `a' + 1` passes, less one. -/
noncomputable def synLb : ℕ := synJk 2 (NW ^ synJp es) (synAc es ℓ K + 1) - 1

/-- The base row exponent `X = a' - L` of a chunk round. -/
noncomputable def synX : ℕ := synAc es ℓ K - synLb es ℓ K

/-- The padded rows `R₂ = 2^X NW^J'` of a chunk round. -/
noncomputable def synR2c : ℕ := 2 ^ synX es ℓ K * NW ^ synJp es

/-- The number of top kernels of round `h`. -/
def synQ (h : ℕ) : ℕ := if synChunk ℓ K h then synQK es else synDp es ℓ h

/-- The offset of the top kernels of round `h`. -/
def synAT (h : ℕ) : ℕ :=
  if synChunk ℓ K h then synOS es ℓ K h + K * synDpp es else synOS es ℓ K h

/-- The number of row address bits of round `h`. -/
def synAR (h : ℕ) : ℕ := if synChunk ℓ K h then synAc es ℓ K else synA es ℓ K

/-- The pieces of round `h`. -/
noncomputable def synPcsR (h : ℕ) : List TopPc :=
  if synChunk ℓ K h then
    synPcs K (synX es ℓ K) (synDpp es) (synOS es ℓ K h) (synJp es) (synDpp es)
  else []

variable (G F : ℕ)

/-- The piece exponents of round `h` (`G`, `F` the gate and factor counts of the node). -/
def synER (h : ℕ) : ℕ := if synChunk ℓ K h then synE G F (synDpp es) (synDpp es) else 0

/-- The shift of round `h`. -/
def synS (h : ℕ) : ℕ := (synDp es ℓ h + 1) / 2 + synQ es ℓ K h + synER es ℓ K G F h

/-- The padded row count of round `h`. -/
noncomputable def synR2 (h : ℕ) : ℕ :=
  if synChunk ℓ K h then synR2c es ℓ K else 2 ^ synA es ℓ K

/-- The working width of round `h`. -/
def synW2 (w h : ℕ) : ℕ := w + synS es ℓ K G F h + es.length

/-- The configuration record of round `h`. -/
noncomputable def synCfg (w h : ℕ) : List ℕ :=
  topCfg w (synS es ℓ K G F h) (synAR es ℓ K h) 1 (synR2 es ℓ K h) (synQ es ℓ K h)
    (synAT es ℓ K h) (synKh ℓ K h) (synOS es ℓ K h) (synDp es ℓ h)

end Records

/-! ### The digit loop -/

section Digits

theorem m_pos : 0 < m := by norm_num [m]

theorem one_lt_m : 1 < m := by norm_num [m]

theorem bits_eq_mul (u : ℕ) : ∀ j, bits u j = u * m ^ j
  | 0 => by simp [bits]
  | j + 1 => by rw [bits, bits_eq_mul u j, pow_succ]; ring

theorem synJk_succ (k X t : ℕ) :
    synJk k X (t + 1) = synJk k X t + if 0 < X / k ^ t then 1 else 0 := by
  unfold synJk
  rw [List.range_succ, List.filter_append, List.length_append]
  congr 1
  by_cases h : 0 < X / k ^ t
  · rw [ite_eq_left h, List.filter_cons_of_pos (by simpa using h)]; rfl
  · rw [ite_eq_right h, List.filter_cons_of_neg (by simpa using h)]; rfl

theorem synJk_le (k X t : ℕ) : synJk k X t ≤ t := by
  unfold synJk
  exact (List.length_filter_le _ _).trans (by simp)

theorem synJk_zero_left (k t : ℕ) : synJk k 0 t = 0 := by
  unfold synJk
  simp

theorem div_pow_pos_of_le' {k X j t : ℕ} (hk : 0 < k) (hjt : j ≤ t) (h : 0 < X / k ^ t) :
    0 < X / k ^ j :=
  lt_of_lt_of_le h (Nat.div_le_div_left (Nat.pow_le_pow_right hk hjt) (by positivity))

theorem synJk_eq_of_pos {k X t : ℕ} (hk : 0 < k) (h : 0 < X / k ^ t) : synJk k X t = t := by
  unfold synJk
  rw [List.filter_eq_self.2]
  · simp
  · intro j hj
    simp only [decide_eq_true_eq]
    exact div_pow_pos_of_le' hk (List.mem_range.1 hj).le h

theorem synJk_eq_of_zero {k X t : ℕ} (h : X / k ^ t = 0) : synJk k X (t + 1) = synJk k X t := by
  rw [synJk_succ]; simp [h]

/-- `0 < X / k^t` exactly when `k^t ≤ X`. -/
theorem div_pow_pos_iff {k X t : ℕ} (hk : 0 < k) : 0 < X / k ^ t ↔ k ^ t ≤ X := by
  constructor
  · intro h
    by_contra h'
    rw [Nat.div_eq_of_lt (by omega)] at h
    exact Nat.lt_irrefl _ h
  · intro h
    exact Nat.div_pos h (Nat.pow_pos hk)

/-- The division count of `X ≥ 1` by `k ≥ 2` over `t` passes is `min t (⌊log_k X⌋ + 1)`. -/
theorem synJk_eq_min {k X : ℕ} (hk : 1 < k) (hX : X ≠ 0) :
    ∀ t, synJk k X t = min t (Nat.log k X + 1)
  | 0 => by simp [synJk]
  | t + 1 => by
      rw [synJk_succ, synJk_eq_min hk hX t]
      have e : 0 < X / k ^ t ↔ t ≤ Nat.log k X := by
        rw [div_pow_pos_iff (by omega), Nat.le_log_iff_pow_le hk hX]
      by_cases h : t ≤ Nat.log k X
      · rw [ite_eq_left (e.2 h)]; omega
      · rw [ite_eq_right (fun h' => h (e.1 h'))]; omega

theorem synJ_succ (D t : ℕ) :
    synJ D (t + 1) = synJ D t + if 0 < D / m ^ t then 1 else 0 := synJk_succ m D t

theorem synJ_le (D t : ℕ) : synJ D t ≤ t := synJk_le m D t

theorem div_pow_pos_of_le {D j t : ℕ} (hjt : j ≤ t) (h : 0 < D / m ^ t) : 0 < D / m ^ j :=
  div_pow_pos_of_le' m_pos hjt h

theorem synJ_eq_of_pos {D t : ℕ} (h : 0 < D / m ^ t) : synJ D t = t := synJk_eq_of_pos m_pos h

theorem synJ_eq_of_zero {D t : ℕ} (h : D / m ^ t = 0) : synJ D (t + 1) = synJ D t :=
  synJk_eq_of_zero h

/-- `synJ D D = ⌊log_m D⌋ + 1` for `D ≥ 1`. -/
theorem synJ_self_eq {D : ℕ} (hD : D ≠ 0) : synJ D D = Nat.log m D + 1 := by
  unfold synJ
  rw [synJk_eq_min one_lt_m hD]
  have := Nat.log_lt_self m hD
  omega

/-- `synJ D D` is monotone in `D`. -/
theorem synJ_self_mono {D D' : ℕ} (h : D' ≤ D) : synJ D' D' ≤ synJ D D := by
  rcases Nat.eq_zero_or_pos D' with rfl | hD'
  · simp [synJ, synJk_zero_left]
  rw [synJ_self_eq (by omega), synJ_self_eq (by omega)]
  have := Nat.log_mono_right (b := m) h
  omega

theorem div_pow_succ' (D t : ℕ) : D / m ^ (t + 1) = D / m ^ t / m := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

theorem synDg_eq (D t : ℕ) : D / m ^ t - m * (D / m ^ t / m) = synDg D t := by
  unfold synDg
  have := Nat.div_add_mod (D / m ^ t) m
  omega

theorem mod_pow_succ_dg (D t : ℕ) : D % m ^ (t + 1) = D % m ^ t + synDg D t * m ^ t := by
  rw [Nat.mod_pow_succ, synDg, Nat.mul_comm]

theorem synDg_of_zero {D t : ℕ} (h : D / m ^ t = 0) : synDg D t = 0 := by
  simp [synDg, h]

theorem mod_pow_of_zero {D t : ℕ} (h : D / m ^ t = 0) : D % m ^ (t + 1) = D % m ^ t := by
  rw [mod_pow_succ_dg, synDg_of_zero h]; simp

theorem div_pow_self (D : ℕ) : D / m ^ D = 0 := by
  apply Nat.div_eq_of_lt
  calc D < 2 ^ D := Nat.lt_two_pow_self
    _ ≤ m ^ D := Nat.pow_le_pow_left (by norm_num [m]) D

theorem mod_pow_self (D : ℕ) : D % m ^ D = D := by
  apply Nat.mod_eq_of_lt
  calc D < 2 ^ D := Nat.lt_two_pow_self
    _ ≤ m ^ D := Nat.pow_le_pow_left (by norm_num [m]) D

theorem synPcs_succ (K a D oS J t : ℕ) :
    synPcs K a D oS J (t + 1) =
      (if synDg D t = 0 then [] else [synPc K a D oS J t]) ++ synPcs K a D oS J t := by
  unfold synPcs
  rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.filterMap_cons]
  by_cases h : synDg D t = 0 <;> simp [h]

theorem synE_succ (G F D t : ℕ) :
    synE G F D (t + 1) =
      synE G F D t + if synDg D t = 0 then 0 else expSeq G F (synDg D t) t := by
  unfold synE; rw [Finset.sum_range_succ]

theorem topPcFields_synPc (K a D oS J t : ℕ) :
    topPcFields K (synPc K a D oS J t) =
      [t, synDg D t, oS + K * (D % m ^ t), K * (synDg D t * m ^ t)] := by
  simp [topPcFields, synPc, bits_eq_mul]

end Digits

/-! ### Record lists -/

section RecLists

variable {A : ℕ}

theorem topRec_reverse_snoc (l : List ℕ) (x : ℕ) :
    (topRec (l ++ [x]) : List (Fin (A + 4))).reverse =
      topSep :: (List.replicate x tick ++ (topRec l).reverse) := by
  simp [topRec_append, topRec_cons, List.reverse_append, List.reverse_replicate]

theorem topRec_cons_eq (x : ℕ) (l : List ℕ) :
    (topRec (x :: l) : List (Fin (A + 4))) = List.replicate x tick ++ topSep :: topRec l :=
  topRec_cons x l

end RecLists

/-! ### Programs -/

section Programs

variable {Q A : ℕ} {U P : Type}

/-- `s 0 := Lg + b D`. -/
noncomputable def synPreA : Pr P (nT SXReg) Q A U :=
  .seq (synMulR (sreg (.p .b)) (sreg (.p .D)) (sreg (.s 0)) (sreg (.s 2)) (sreg (.s 3)))
    (ucopy (sreg (.p .Lg)) (sreg (.s 0)) (sreg (.s 2)))

/-- `s 5 := (|x| + 1)/2 + |y|`. -/
noncomputable def synHalfAdd (x y : SynW) : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg x) (sreg (.s 1)) (sreg (.s 2))) (.seq (synPush (sreg (.s 1)) tick)
    (.seq (udiv 2 (sreg (.s 1)) (sreg (.s 5)) (sreg (.s 2))) (.seq (uclear (sreg (.s 1)))
      (ucopy (sreg y) (sreg (.s 5)) (sreg (.s 2))))))

/-- `s 5 := (|x| + 1)/2 + |x|`. -/
noncomputable def synHalfPlus (x : SynW) : Pr P (nT SXReg) Q A U := synHalfAdd x x

/-- Push a reversed field of `|x|` ticks onto `p .cf`. -/
noncomputable def synCF (x : SynW) : Pr P (nT SXReg) Q A U :=
  synFieldR (sreg x) (sreg (.p .cf)) (sreg (.s 2))

/-- `p .w2 := w + |x| + D`. -/
noncomputable def synW2P (x : SynW) : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.p .w)) (sreg (.p .w2)) (sreg (.s 2)))
    (.seq (ucopy (sreg x) (sreg (.p .w2)) (sreg (.s 2)))
      (ucopy (sreg (.p .D)) (sreg (.p .w2)) (sreg (.s 2))))

/-- The prefix branches from `s 6 = oS`: `K_h = 1`, `s = (D' + 1)/2 + D'` (`D'` on `dp`),
`R₂ = 2^a`, the record `w, s, a, 1, 2^a, D', oS, D', oS, D'`, `w' = w + s + D`; scratch
cleared. -/
noncomputable def synPreBr (dp : SynW) : Pr P (nT SXReg) Q A U :=
  .seq (synPush (sreg (.p .kh)) tick) <|
  .seq (synHalfPlus dp) <|
  .seq (synPush (sreg (.s 7)) tick) <|
  .seq (upow2 (sreg (.s 0)) (sreg (.s 7)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (synCF (.p .w)) <| .seq (synCF (.s 5)) <| .seq (synCF (.s 0)) <|
  .seq (.seq (synPush (sreg (.p .cf)) tick) (synPush (sreg (.p .cf)) topSep)) <|
  .seq (synCF (.s 7)) <| .seq (synCF dp) <| .seq (synCF (.s 6)) <| .seq (synCF dp) <|
  .seq (synCF (.s 6)) <| .seq (synCF dp) <|
  .seq (synW2P (.s 5)) <|
  .seq (uclear (sreg (.s 5))) <| .seq (uclear (sreg (.s 6))) <| .seq (uclear (sreg (.s 7)))
    (uclear (sreg (.s 0)))

/-- The top round: `oS = N - Lg`, `D' = Lg`. -/
noncomputable def synTopB : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.p .N)) (sreg (.s 6)) (sreg (.s 2)))
    (.seq (usub (sreg (.p .Lg)) (sreg (.s 6)) (sreg (.s 2))) (synPreBr (.p .Lg)))

/-- A low round, from `s 1 = b - h`: `oS = N - Lg - (b - h) D`, `D' = D`. -/
noncomputable def synLowB : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.p .N)) (sreg (.s 6)) (sreg (.s 2))) <|
  .seq (usub (sreg (.p .Lg)) (sreg (.s 6)) (sreg (.s 2))) <|
  .seq (synMulR (sreg (.s 1)) (sreg (.p .D)) (sreg (.s 8)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (usub (sreg (.s 8)) (sreg (.s 6)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.s 8))) <| .seq (uclear (sreg (.s 1))) (synPreBr (.p .D))

/-- One piece of the digit loop, from `s 18 = d`, `s 13 = m^t`, `s 14 = t`, `s 15 = a₀`:
the fields `t, d, a₀, K d m^t` onto `p .pr`, `s 16 += expSeq G F d t`, `s 15 += K d m^t`. -/
noncomputable def synPieceP (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (synMulR (sreg (.s 18)) (sreg (.s 13)) (sreg (.s 19)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (synMulR (sreg (.p .K)) (sreg (.s 19)) (sreg (.s 20)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (synFieldF (sreg (.s 20)) (sreg (.p .pr)) (sreg (.s 2))) <|
  .seq (synFieldF (sreg (.s 15)) (sreg (.p .pr)) (sreg (.s 2))) <|
  .seq (synFieldF (sreg (.s 18)) (sreg (.p .pr)) (sreg (.s 2))) <|
  .seq (synFieldF (sreg (.s 14)) (sreg (.p .pr)) (sreg (.s 2))) <|
  .seq (expProg G F (sreg (.s 18)) (sreg (.s 14)) (sreg (.s 21)) (sreg (.s 2)) (sreg (.s 3))
    (sreg (.s 4))) <|
  .seq (ucopy (sreg (.s 21)) (sreg (.s 16)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.s 21))) <|
  .seq (ucopy (sreg (.s 20)) (sreg (.s 15)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.s 19))) (uclear (sreg (.s 20)))

/-- One pass of the digit loop from `s 12 = x`: `y = x / m`, the digit `d = x - m y`, the piece
when `d ≠ 0`, then `x := y`, `m^t := m^(t+1)`, `t := t + 1`. -/
noncomputable def synDigBody (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (udiv m (sreg (.s 12)) (sreg (.s 17)) (sreg (.s 2))) <|
  .seq (umul m (sreg (.s 17)) (sreg (.s 24)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.s 12)) (sreg (.s 18)) (sreg (.s 2))) <|
  .seq (usub (sreg (.s 24)) (sreg (.s 18)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.s 24))) <|
  .seq (synIfNE (sreg (.s 18)) (synPieceP G F) synSkip) <|
  .seq (uclear (sreg (.s 18))) <|
  .seq (uclear (sreg (.s 12))) <|
  .seq (moveR (sreg (.s 17)) (sreg (.s 12)) id) <|
  .seq (synMulIn m (sreg (.s 13)) (sreg (.s 2)) (sreg (.s 3))) (synPush (sreg (.s 14)) tick)

/-- The digit loop over the `D'` passes of the counter `s 26` (spare `s 23`), from `s 6 = oS`.
It leaves the piece record on `p .pr`, the exponent sum on `s 16` and the number of levels on
`s 14`. -/
noncomputable def synDigits (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.s 26)) (sreg (.s 12)) (sreg (.s 2))) <|
  .seq (synPush (sreg (.s 13)) tick) <|
  .seq (ucopy (sreg (.s 6)) (sreg (.s 15)) (sreg (.s 2))) <|
  .seq (scanP (sreg (.s 26)) (sreg (.s 23)) (synIfNE (sreg (.s 12)) (synDigBody G F) synSkip)) <|
  .seq (uclear (sreg (.s 12))) <| .seq (uclear (sreg (.s 13))) (uclear (sreg (.s 15)))

/-- One pass of a division count by `k`: when `x` is nonempty, `x := |x| / k` and one tick onto
`cnt`. -/
noncomputable def synCntBody (k : ℕ) (x cnt : SynW) : Pr P (nT SXReg) Q A U :=
  synIfNE (sreg x)
    (.seq (udiv k (sreg x) (sreg (.s 17)) (sreg (.s 2))) <| .seq (uclear (sreg x)) <|
      .seq (moveR (sreg (.s 17)) (sreg x) id) (synPush (sreg cnt) tick))
    synSkip

/-- The division count of `x` by `k` over the counter `ctr` (spare `s 23`): `cnt` gains one tick
per pass with `x` nonempty. -/
noncomputable def synCntLoop (k : ℕ) (x cnt ctr : SynW) : Pr P (nT SXReg) Q A U :=
  scanP (sreg ctr) (sreg (.s 23)) (synCntBody k x cnt)

/-- `R₂`: `s 7 := NW^|s 22| · |s 7|` (counter `s 22`, spare `s 23`). -/
noncomputable def synNWLoop : Pr P (nT SXReg) Q A U :=
  scanP (sreg (.s 22)) (sreg (.s 23)) (synMulIn NW (sreg (.s 7)) (sreg (.s 2)) (sreg (.s 3)))

/-- Chunk round, first stage: `K_h = K` on `p .kh`, `ρ_h = (h - b) mod K` on `p .rh`,
`oS = K (⌊(h - b)/K⌋ D)` on `s 6`. -/
noncomputable def synChunkA : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.p .K)) (sreg (.p .kh)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.p .h)) (sreg (.s 9)) (sreg (.s 2))) <|
  .seq (usub (sreg (.p .b)) (sreg (.s 9)) (sreg (.s 2))) <|
  .seq (synDivModR (sreg (.s 9)) (sreg (.p .K)) (sreg (.s 10)) (sreg (.s 11)) (sreg (.s 2))
    (sreg (.s 3)) (sreg (.s 4))) <|
  .seq (ucopy (sreg (.s 11)) (sreg (.p .rh)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.s 11))) <| .seq (uclear (sreg (.s 9))) <|
  .seq (synMulR (sreg (.s 10)) (sreg (.p .D)) (sreg (.s 8)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (synMulR (sreg (.p .K)) (sreg (.s 8)) (sreg (.s 6)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (uclear (sreg (.s 8))) (uclear (sreg (.s 10)))

/-- Chunk round, kernels: from `s 6 = oS` and `s 0 = a`: `s 14 := synJ D D` (the division count
of `D` by `m`), `q₀ = D - (D - 46 J)` on `s 25` (`J = synJ D D - 1`), `D' = D - q₀` on `s 26`,
`K q₀` on `s 27`, `a' = K q₀ + a` on `s 0`, `aT = oS + K D'` on `s 28`. -/
noncomputable def synChunkQ : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.p .D)) (sreg (.s 12)) (sreg (.s 2))) <|
  .seq (synCntLoop m (.s 12) (.s 14) (.p .D)) <|
  .seq (ucopy (sreg (.s 14)) (sreg (.s 22)) (sreg (.s 2))) <|
  .seq (synPop (sreg (.s 22))) <|
  .seq (umul synCW (sreg (.s 22)) (sreg (.s 9)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.p .D)) (sreg (.s 10)) (sreg (.s 2))) <|
  .seq (usub (sreg (.s 9)) (sreg (.s 10)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.p .D)) (sreg (.s 25)) (sreg (.s 2))) <|
  .seq (usub (sreg (.s 10)) (sreg (.s 25)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.p .D)) (sreg (.s 26)) (sreg (.s 2))) <|
  .seq (usub (sreg (.s 25)) (sreg (.s 26)) (sreg (.s 2))) <|
  .seq (synMulR (sreg (.p .K)) (sreg (.s 25)) (sreg (.s 27)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (ucopy (sreg (.s 27)) (sreg (.s 0)) (sreg (.s 2))) <|
  .seq (synMulR (sreg (.p .K)) (sreg (.s 26)) (sreg (.s 28)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (ucopy (sreg (.s 6)) (sreg (.s 28)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.s 14))) <| .seq (uclear (sreg (.s 22))) <| .seq (uclear (sreg (.s 9)))
    (uclear (sreg (.s 10)))

/-- Chunk round, rows: from `s 0 = a'` and `s 14 = J' + 1`: `NW^J'` on `s 7`, its division
count by `2` over `a' + 1` passes on `s 30` (counter `s 31`), `X = a' - (|s 30| - 1)` on `s 8`,
then `s 7 := 2^X NW^J'`. -/
noncomputable def synChunkR2 : Pr P (nT SXReg) Q A U :=
  .seq (synPush (sreg (.s 7)) tick) <|
  .seq (ucopy (sreg (.s 14)) (sreg (.s 22)) (sreg (.s 2))) <| .seq (synPop (sreg (.s 22))) <|
  .seq synNWLoop <| .seq (uclear (sreg (.s 22))) <|
  .seq (ucopy (sreg (.s 7)) (sreg (.s 29)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.s 0)) (sreg (.s 31)) (sreg (.s 2))) <| .seq (synPush (sreg (.s 31)) tick) <|
  .seq (synCntLoop 2 (.s 29) (.s 30) (.s 31)) <|
  .seq (uclear (sreg (.s 31))) <| .seq (uclear (sreg (.s 29))) <|
  .seq (synPop (sreg (.s 30))) <|
  .seq (ucopy (sreg (.s 0)) (sreg (.s 8)) (sreg (.s 2))) <|
  .seq (usub (sreg (.s 30)) (sreg (.s 8)) (sreg (.s 2))) <|
  .seq (upow2 (sreg (.s 8)) (sreg (.s 7)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (uclear (sreg (.s 8))) (uclear (sreg (.s 30)))

/-- Chunk round, record: `s 5 := (D + 1)/2 + q₀`, `s 16 := s = (D + 1)/2 + q₀ + E` and the fields
`w, s, a', 1, R₂, q₀, aT, K q₀, oS, D`. -/
noncomputable def synChunkCfg : Pr P (nT SXReg) Q A U :=
  .seq (synHalfAdd (.p .D) (.s 25)) <|
  .seq (ucopy (sreg (.s 5)) (sreg (.s 16)) (sreg (.s 2))) <|
  .seq (synCF (.p .w)) <| .seq (synCF (.s 16)) <| .seq (synCF (.s 0)) <|
  .seq (.seq (synPush (sreg (.p .cf)) tick) (synPush (sreg (.p .cf)) topSep)) <|
  .seq (synCF (.s 7)) <| .seq (synCF (.s 25)) <| .seq (synCF (.s 28)) <| .seq (synCF (.s 27)) <|
  .seq (synCF (.s 6)) (synCF (.p .D))

/-- Chunk round, end: `w' = w + s + D` and the scratch cleared. -/
noncomputable def synChunkEnd : Pr P (nT SXReg) Q A U :=
  .seq (synW2P (.s 16)) <|
  .seq (uclear (sreg (.s 5))) <| .seq (uclear (sreg (.s 6))) <| .seq (uclear (sreg (.s 7))) <|
  .seq (uclear (sreg (.s 14))) <| .seq (uclear (sreg (.s 16))) <| .seq (uclear (sreg (.s 25))) <|
  .seq (uclear (sreg (.s 26))) <| .seq (uclear (sreg (.s 27))) <| .seq (uclear (sreg (.s 28)))
    (uclear (sreg (.s 0)))

/-- A chunk round, from `s 0 = a`: `K_h = K`, `ρ_h = (h - b) mod K`, `oS = K (⌊(h - b)/K⌋ D)`,
the kernel bits `q₀` and `a' = K q₀ + a` (`synChunkQ`), the pieces of the base-`m` digits of
`D' = D - q₀` (`synDigits`), `R₂ = 2^X NW^J'` (`synChunkR2`), `s = (D + 1)/2 + q₀ + E`, the
record `w, s, a', 1, R₂, q₀, oS + K D', K q₀, oS, D`, `w' = w + s + D`; scratch cleared. -/
noncomputable def synChunkB (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq synChunkA <| .seq synChunkQ <| .seq (synDigits G F) <| .seq synChunkR2 <|
    .seq synChunkCfg synChunkEnd

/-- **The record builder of round `h`.** `s 0 := a`; `s 1 := ℓ - h - 1`: the top round when it
is empty; otherwise `s 1 := b - h`: a low round when it is nonempty, else a chunk round. -/
noncomputable def synRec (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq synPreA <|
  .seq (.seq (ucopy (sreg (.p .ℓ)) (sreg (.s 1)) (sreg (.s 2)))
    (.seq (usub (sreg (.p .h)) (sreg (.s 1)) (sreg (.s 2))) (synPop (sreg (.s 1))))) <|
  synIfNE (sreg (.s 1))
    (.seq (.seq (uclear (sreg (.s 1))) (.seq (ucopy (sreg (.p .b)) (sreg (.s 1)) (sreg (.s 2)))
        (usub (sreg (.p .h)) (sreg (.s 1)) (sreg (.s 2)))))
      (synIfNE (sreg (.s 1)) synLowB (.seq (uclear (sreg (.s 1))) (synChunkB G F))))
    (.seq (uclear (sreg (.s 1))) synTopB)

end Programs

/-! ### The prefix branches -/

section PreBr

variable {Q A : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q A U)
  {R : Fin (nT SXReg) → List (Fin (A + 4))}

theorem sg_synHalfAdd {x y : SynW} (hx1 : x ≠ .s 1) (hx2 : x ≠ .s 2) (hy1 : y ≠ .s 1)
    (hy2 : y ≠ .s 2) (hy5 : y ≠ .s 5)
    (v : SynW → List (Fin (A + 4))) (X Y : ℕ) (hX : (v x).length = X) (hY : (v y).length = Y)
    (h1 : v (.s 1) = []) (h2 : v (.s 2) = []) (h5 : v (.s 5) = []) :
    LayRuns body (synHalfAdd x y) (synG R v)
      (synG R (Function.update v (.s 5) (List.replicate ((X + 1) / 2 + Y) tick)))
      (4 * X + 4 + (1 + (4 * (X + 1) + 4 + (2 * (X + 1) + 2 + (4 * Y + 4))))) := by
  refine lr_weaken body
    ((sgU_copy body (a := x) (b := .s 1) (t := .s 2) (x := X) (y := 0) hx1 hx2 (by decide)
      (by simpa using h2) hX (by simpa using h1)).seq <|
    (sgU_push body (a := .s 1) (y := X) (by simp)).seq <|
    (sgU_div body (k := 2) (a := .s 1) (b := .s 5) (t := .s 2) (x := X + 1) (y := 0) (by norm_num)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [h5])).seq <|
    (sgU_clear body (a := .s 1) (x := X + 1) (by simp)).seq <|
    sgU_copy body (a := y) (b := .s 5) (t := .s 2) (x := Y) (y := (X + 1) / 2) hy5 hy2
      (by decide) (by simp [h2]) (by simp [hy1, hy5, hY]) (by simp))
    ?_ le_rfl
  refine congrArg (synG R) ?_
  funext y
  simp only [Function.update_apply]
  split_ifs <;> (try simp_all) <;> omega

/-- A reversed record field on `p .cf`. -/
theorem sg_synCF {x : SynW} (hx : x ≠ .p .cf) (hx2 : x ≠ .s 2) (v : SynW → List (Fin (A + 4)))
    (l : List ℕ) (X : ℕ) (h2 : v (.s 2) = []) (hX : (v x).length = X)
    (hcf : v (.p .cf) = (topRec l).reverse) :
    LayRuns body (synCF x) (synG R v)
      (synG R (Function.update v (.p .cf) (topRec (l ++ [X])).reverse)) (4 * X + 5) :=
  lr_weaken body (sgR_fieldR body (a := x) (b := .p .cf) (t := .s 2) hx hx2 (by decide) h2 hX hcf)
    (by rw [topRec_reverse_snoc]) le_rfl

/-- A reversed constant field `1`. -/
theorem sg_synCF1 (v : SynW → List (Fin (A + 4))) (l : List ℕ)
    (hcf : v (.p .cf) = (topRec l).reverse) :
    LayRuns body (.seq (synPush (sreg (.p .cf)) tick) (synPush (sreg (.p .cf)) topSep)) (synG R v)
      (synG R (Function.update v (.p .cf) (topRec (l ++ [1])).reverse)) 2 :=
  lr_weaken body ((sgR_push body (a := .p .cf) tick hcf).seq (sgR_push body (a := .p .cf) topSep
    (l := tick :: (topRec l).reverse) (by simp)))
    (by rw [topRec_reverse_snoc]; simp) le_rfl

/-- A reversed constant field `0`. -/
theorem sg_synCF0 (v : SynW → List (Fin (A + 4))) (l : List ℕ)
    (hcf : v (.p .cf) = (topRec l).reverse) :
    LayRuns body (synPush (sreg (.p .cf)) topSep) (synG R v)
      (synG R (Function.update v (.p .cf) (topRec (l ++ [0])).reverse)) 1 :=
  lr_weaken body (sgR_push body (a := .p .cf) topSep hcf) (by rw [topRec_reverse_snoc]; simp)
    le_rfl

theorem sg_synW2P {x : SynW} (hx : x ≠ .p .w2) (hx2 : x ≠ .s 2) (v : SynW → List (Fin (A + 4))) (W X Dv : ℕ) (h2 : v (.s 2) = [])
    (hw2 : v (.p .w2) = []) (hW : (v (.p .w)).length = W) (hX : (v x).length = X)
    (hD : (v (.p .D)).length = Dv) :
    LayRuns body (synW2P x) (synG R v)
      (synG R (Function.update v (.p .w2) (List.replicate (W + X + Dv) tick)))
      (4 * W + 4 + (4 * X + 4 + (4 * Dv + 4))) := by
  refine lr_weaken body
    ((sgU_copy body (a := .p .w) (b := .p .w2) (t := .s 2) (x := W) (y := 0) (by decide)
      (by decide) (by decide) h2 hW (by simp [hw2])).seq <|
    (sgU_copy body (a := x) (b := .p .w2) (t := .s 2) (x := X) (y := W) hx hx2 (by decide)
      (by simp [h2]) (by simp [hx, hX]) (by simp)).seq <|
    sgU_copy body (a := .p .D) (b := .p .w2) (t := .s 2) (x := Dv) (y := X + W) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hD]) (by simp)) ?_ le_rfl
  refine congrArg (synG R) ?_
  funext y
  simp only [Function.update_apply]
  split_ifs <;> (try simp_all) <;> omega

/-- The step bound of `synPreBr`. -/
def synPreBrCost (w a dp oS D : ℕ) : ℕ :=
  1 + (4 * dp + 4 + (1 + (4 * (dp + 1) + 4 + (2 * (dp + 1) + 2 + (4 * dp + 4))))) + 1 +
    (4 * (2 ^ a * 1) + 9 * a + 4) +
    (4 * w + 5) + (4 * ((dp + 1) / 2 + dp) + 5) + (4 * a + 5) + 2 + (4 * (2 ^ a * 1) + 5) +
    (4 * dp + 5) + (4 * oS + 5) + (4 * dp + 5) + (4 * oS + 5) + (4 * dp + 5) +
    (4 * w + 4 + (4 * ((dp + 1) / 2 + dp) + 4 + (4 * D + 4))) +
    (2 * ((dp + 1) / 2 + dp) + 2) + (2 * oS + 2) + (2 * (2 ^ a * 1) + 2) + (2 * a + 2)

theorem sg_synPreBr {dp : SynW} (hdp : ∀ i, dp ≠ .s i) (hdp1 : dp ≠ .p .cf)
    (hdp2 : dp ≠ .p .kh) (_hdp3 : dp ≠ .p .w2)
    (v : SynW → List (Fin (A + 4))) (a oS W Dp Dv : ℕ)
    (hs : ∀ i, i ≠ 0 → i ≠ 6 → v (.s i) = []) (ha : v (.s 0) = List.replicate a tick)
    (hoS : v (.s 6) = List.replicate oS tick) (hcf : v (.p .cf) = []) (hkh : v (.p .kh) = [])
    (hw2 : v (.p .w2) = []) (hW : (v (.p .w)).length = W) (hDp : (v dp).length = Dp)
    (hD : (v (.p .D)).length = Dv) :
    LayRuns body (synPreBr dp) (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update
        (Function.update v (.s 0) []) (.s 6) []) (.p .kh) [tick]) (.p .cf)
          (topRec [W, (Dp + 1) / 2 + Dp, a, 1, 2 ^ a * 1, Dp, oS, Dp, oS, Dp]).reverse) (.p .w2)
          (List.replicate (W + ((Dp + 1) / 2 + Dp) + Dv) tick)))
      (synPreBrCost W a Dp oS Dv) := by
  have h1 : v (.s 1) = [] := hs 1 (by decide) (by decide)
  have h2 : v (.s 2) = [] := hs 2 (by decide) (by decide)
  have h3 : v (.s 3) = [] := hs 3 (by decide) (by decide)
  have h5 : v (.s 5) = [] := hs 5 (by decide) (by decide)
  have h7 : v (.s 7) = [] := hs 7 (by decide) (by decide)
  have hd0 := hdp 0
  have hd1 := hdp 1
  have hd2 := hdp 2
  have hd5 := hdp 5
  have hd6 := hdp 6
  have hd7 := hdp 7
  refine lr_weaken body
    ((sgU_push body (a := .p .kh) (y := 0) (by simp [hkh])).seq <|
    (sg_synHalfAdd body hd1 hd2 hd1 hd2 hd5 _ Dp Dp (by simp [hdp2, hDp]) (by simp [hdp2, hDp])
      (by simp [h1]) (by simp [h2]) (by simp [h5])).seq <|
    (sgU_push body (a := .s 7) (y := 0) (by simp [h7])).seq <|
    (sgU_pow2 body (a := .s 0) (b := .s 7) (t₁ := .s 2) (t₂ := .s 3) (x := a) (y := 1)
      (by decide) (by simp [h2]) (by simp [h3]) (by simp [ha]) (by simp)).seq <|
    (sg_synCF body (x := .p .w) (by decide) (by decide) _ [] W (by simp [h2]) (by simp [hW])
      (by simp [hcf])).seq <|
    (sg_synCF body (x := .s 5) (by decide) (by decide) _ [W] ((Dp + 1) / 2 + Dp) (by simp [h2])
      (by simp) (by simp)).seq <|
    (sg_synCF body (x := .s 0) (by decide) (by decide) _ [W, (Dp + 1) / 2 + Dp] a (by simp [h2])
      (by simp [ha]) (by simp)).seq <|
    (sg_synCF1 body _ [W, (Dp + 1) / 2 + Dp, a] (by simp)).seq <|
    (sg_synCF body (x := .s 7) (by decide) (by decide) _ [W, (Dp + 1) / 2 + Dp, a, 1] (2 ^ a * 1)
      (by simp [h2]) (by simp) (by simp)).seq <|
    (sg_synCF body (x := dp) hdp1 hd2 _ [W, (Dp + 1) / 2 + Dp, a, 1, 2 ^ a * 1] Dp (by simp [h2])
      (by simp [hdp1, hdp2, hd7, hd5, hDp]) (by simp)).seq <|
    (sg_synCF body (x := .s 6) (by decide) (by decide) _
      [W, (Dp + 1) / 2 + Dp, a, 1, 2 ^ a * 1, Dp] oS (by simp [h2]) (by simp [hoS])
      (by simp)).seq <|
    (sg_synCF body (x := dp) hdp1 hd2 _ [W, (Dp + 1) / 2 + Dp, a, 1, 2 ^ a * 1, Dp, oS] Dp
      (by simp [h2]) (by simp [hdp1, hdp2, hd7, hd5, hDp]) (by simp)).seq <|
    (sg_synCF body (x := .s 6) (by decide) (by decide) _
      [W, (Dp + 1) / 2 + Dp, a, 1, 2 ^ a * 1, Dp, oS, Dp] oS (by simp [h2]) (by simp [hoS])
      (by simp)).seq <|
    (sg_synCF body (x := dp) hdp1 hd2 _ [W, (Dp + 1) / 2 + Dp, a, 1, 2 ^ a * 1, Dp, oS, Dp, oS] Dp
      (by simp [h2]) (by simp [hdp1, hdp2, hd7, hd5, hDp]) (by simp)).seq <|
    (sg_synW2P body (x := .s 5) (by decide) (by decide) _ W
      ((Dp + 1) / 2 + Dp) Dv (by simp [h2]) (by simp [hw2]) (by simp [hW]) (by simp)
      (by simp [hD])).seq <|
    (sgU_clear body (a := .s 5) (x := (Dp + 1) / 2 + Dp) (by simp)).seq <|
    (sgU_clear body (a := .s 6) (x := oS) (by simp [hoS])).seq <|
    (sgU_clear body (a := .s 7) (x := 2 ^ a * 1) (by simp)).seq <|
    sgU_clear body (a := .s 0) (x := a) (by simp [ha])) ?_ ?_
  · refine congrArg (synG R) ?_
    funext y
    simp only [Function.update_apply]
    split_ifs <;> (try simp_all) <;> omega
  · simp only [synPreBrCost]
    omega

theorem sg_synTopB (v : SynW → List (Fin (A + 4))) (a Nv Lg W Dv : ℕ)
    (hs : ∀ i, i ≠ 0 → v (.s i) = []) (ha : v (.s 0) = List.replicate a tick)
    (hcf : v (.p .cf) = []) (hkh : v (.p .kh) = []) (hw2 : v (.p .w2) = [])
    (hN : (v (.p .N)).length = Nv) (hLg : (v (.p .Lg)).length = Lg)
    (hW : (v (.p .w)).length = W) (hD : (v (.p .D)).length = Dv) :
    LayRuns body synTopB (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update v (.s 0) [])
        (.p .kh) [tick]) (.p .cf)
          (topRec [W, (Lg + 1) / 2 + Lg, a, 1, 2 ^ a * 1, Lg, Nv - Lg, Lg, Nv - Lg, Lg]).reverse)
          (.p .w2) (List.replicate (W + ((Lg + 1) / 2 + Lg) + Dv) tick)))
      (4 * Nv + 4 + (4 * Lg + 4 + synPreBrCost W a Lg (Nv - Lg) Dv)) := by
  have h2 : v (.s 2) = [] := hs 2 (by decide)
  have h6 : v (.s 6) = [] := hs 6 (by decide)
  refine lr_weaken body
    ((sgU_copy body (a := .p .N) (b := .s 6) (t := .s 2) (x := Nv) (y := 0) (by decide)
      (by decide) (by decide) h2 hN (by simp [h6])).seq <|
    (sgU_sub body (a := .p .Lg) (b := .s 6) (t := .s 2) (x := Lg) (y := Nv) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hLg]) (by simp)).seq <|
    sg_synPreBr body (dp := .p .Lg) (fun i => by simp) (by decide) (by decide) (by decide) _ a
      (Nv - Lg) W Lg Dv (fun i hi0 hi6 => by simp [hi6, hs i hi0]) (by simp [ha])
      (by simp) (by simp [hcf]) (by simp [hkh]) (by simp [hw2]) (by simp [hW]) (by simp [hLg])
      (by simp [hD])) ?_ le_rfl
  refine congrArg (synG R) ?_
  funext y
  simp only [Function.update_apply]
  split_ifs <;> (try simp_all) <;> omega

theorem sg_synLowB (v : SynW → List (Fin (A + 4))) (a Nv Lg W Dv bh : ℕ)
    (hs : ∀ i, i ≠ 0 → i ≠ 1 → v (.s i) = []) (ha : v (.s 0) = List.replicate a tick)
    (h1 : v (.s 1) = List.replicate bh tick)
    (hcf : v (.p .cf) = []) (hkh : v (.p .kh) = []) (hw2 : v (.p .w2) = [])
    (hN : (v (.p .N)).length = Nv) (hLg : (v (.p .Lg)).length = Lg)
    (hW : (v (.p .w)).length = W) (hD : (v (.p .D)).length = Dv) :
    LayRuns body synLowB (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update
        (Function.update v (.s 0) []) (.s 1) []) (.p .kh) [tick]) (.p .cf)
          (topRec [W, (Dv + 1) / 2 + Dv, a, 1, 2 ^ a * 1, Dv, Nv - Lg - bh * Dv, Dv,
            Nv - Lg - bh * Dv, Dv]).reverse)
          (.p .w2) (List.replicate (W + ((Dv + 1) / 2 + Dv) + Dv) tick)))
      (4 * Nv + 4 + (4 * Lg + 4 + (synMulRCost bh Dv + (4 * (bh * Dv) + 4 +
        (2 * (bh * Dv) + 2 + (2 * bh + 2 + synPreBrCost W a Dv (Nv - Lg - bh * Dv) Dv)))))) := by
  have h2 : v (.s 2) = [] := hs 2 (by decide) (by decide)
  have h3 : v (.s 3) = [] := hs 3 (by decide) (by decide)
  have h6 : v (.s 6) = [] := hs 6 (by decide) (by decide)
  have h8 : v (.s 8) = [] := hs 8 (by decide) (by decide)
  refine lr_weaken body
    ((sgU_copy body (a := .p .N) (b := .s 6) (t := .s 2) (x := Nv) (y := 0) (by decide)
      (by decide) (by decide) h2 hN (by simp [h6])).seq <|
    (sgU_sub body (a := .p .Lg) (b := .s 6) (t := .s 2) (x := Lg) (y := Nv) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hLg]) (by simp)).seq <|
    (sgU_mulR body (a := .s 1) (b := .p .D) (c := .s 8) (t₁ := .s 2) (t₂ := .s 3) (x := bh)
      (y := Dv) (z := 0) (by decide) (by simp [h2]) (by simp [h3]) (by simp [h1])
      (by simp [hD]) (by simp [h8])).seq <|
    (sgU_sub body (a := .s 8) (b := .s 6) (t := .s 2) (x := bh * Dv) (y := Nv - Lg) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp) (by simp)).seq <|
    (sgU_clear body (a := .s 8) (x := bh * Dv) (by simp)).seq <|
    (sgU_clear body (a := .s 1) (x := bh) (by simp [h1])).seq <|
    sg_synPreBr body (dp := .p .D) (fun i => by simp) (by decide) (by decide) (by decide) _ a
      (Nv - Lg - bh * Dv) W Dv Dv (fun i hi0 hi6 => by
        by_cases hi1 : i = 1
        · subst hi1; simp
        by_cases hi8 : i = 8
        · subst hi8; simp
        simp [hi6, hi1, hi8, hs i hi0 hi1]) (by simp [ha])
      (by simp) (by simp [hcf]) (by simp [hkh]) (by simp [hw2]) (by simp [hW]) (by simp [hD])
      (by simp [hD])) ?_ le_rfl
  refine congrArg (synG R) ?_
  funext y
  simp only [Function.update_apply]
  split_ifs <;> (try simp_all) <;> omega

end PreBr

/-! ### The digit loop -/

section DigitLoop

variable {Q A : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q A U)
  {R : Fin (nT SXReg) → List (Fin (A + 4))}

/-- The step bound of pass `t` of a division count by `k` on `X`. -/
def synCntPassCost (k X t : ℕ) : ℕ :=
  if X / k ^ t = 0 then 3
  else (4 * (X / k ^ t) + 4) + (2 * (X / k ^ t) + 2) + (2 * (X / k ^ t / k) + 2) + 1 + 2

/-- The step bound of a division count over `n` passes. -/
def synCntCost (k X n : ℕ) : ℕ :=
  (∑ t ∈ Finset.range n, (synCntPassCost k X t + 3)) + 2 * n + 4

theorem div_pow_succ_gen (k X t : ℕ) : X / k ^ (t + 1) = X / k ^ t / k := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

/-- **The division count.** From `x = X` ticks, `cnt` empty and a counter of `n` symbols,
`synCntLoop k x cnt ctr` leaves `X / k^n` on `x` and `synJk k X n` on `cnt`. -/
theorem sg_synCntLoop (k : ℕ) (hk : 1 ≤ k) {x cnt ctr : SynW} (v : SynW → List (Fin (A + 4)))
    (X n : ℕ) (hxc : x ≠ cnt) (hxr : x ≠ ctr) (hcr : cnt ≠ ctr) (hx17 : x ≠ .s 17)
    (hx2 : x ≠ .s 2) (hx23 : x ≠ .s 23) (hc17 : cnt ≠ .s 17) (hc2 : cnt ≠ .s 2)
    (hc23 : cnt ≠ .s 23) (hr17 : ctr ≠ .s 17) (hr2 : ctr ≠ .s 2) (hr23 : ctr ≠ .s 23)
    (hx : v x = List.replicate X tick) (hcnt : v cnt = []) (hctr : (v ctr).length = n)
    (h17 : v (.s 17) = []) (h2 : v (.s 2) = []) (h23 : v (.s 23) = []) :
    LayRuns body (synCntLoop k x cnt ctr) (synG R v)
      (synG R (Function.update (Function.update v x (List.replicate (X / k ^ n) tick)) cnt
        (List.replicate (synJk k X n) tick)))
      (synCntCost k X n) := by
  have hcx : cnt ≠ x := hxc.symm
  have hrx : ctr ≠ x := hxr.symm
  have hrc : ctr ≠ cnt := hcr.symm
  have h17x : SynW.s 17 ≠ x := hx17.symm
  have h17c : SynW.s 17 ≠ cnt := hc17.symm
  have h17r : SynW.s 17 ≠ ctr := hr17.symm
  have h2x : SynW.s 2 ≠ x := hx2.symm
  have h2c : SynW.s 2 ≠ cnt := hc2.symm
  have h23x : SynW.s 23 ≠ x := hx23.symm
  have h23c : SynW.s 23 ≠ cnt := hc23.symm
  set cs := v ctr with hcs
  let Φ : ℕ → SynW → List (Fin (A + 4)) := fun t =>
    Function.update (Function.update v x (List.replicate (X / k ^ t) tick)) cnt
      (List.replicate (synJk k X t) tick)
  have hstep : ∀ t < cs.length, LayRuns body (synCntBody k x cnt)
      (synG R (Function.update (Function.update (Φ t) ctr (cs.drop (t + 1))) (.s 23)
        (cs.take (t + 1)).reverse))
      (synG R (Function.update (Function.update (Φ (t + 1)) ctr (cs.drop (t + 1))) (.s 23)
        (cs.take (t + 1)).reverse)) (synCntPassCost k X t) := by
    intro t _
    set w := Function.update (Function.update (Φ t) ctr (cs.drop (t + 1))) (.s 23)
      (cs.take (t + 1)).reverse with hw
    have wx : w x = List.replicate (X / k ^ t) tick := by
      simp [hw, Φ, Function.update_apply, hxr, hx23, hxc]
    have wc : w cnt = List.replicate (synJk k X t) tick := by
      simp [hw, Φ, Function.update_apply, hcr, hc23]
    have w17 : w (.s 17) = [] := by
      simp [hw, Φ, Function.update_apply, h17r, h17c, h17x, h17]
    have w2 : w (.s 2) = [] := by
      simp [hw, Φ, Function.update_apply, hr2.symm, h2c, h2x, h2]
    by_cases hz : X / k ^ t = 0
    · have e : Φ (t + 1) = Φ t := by
        simp only [Φ, div_pow_succ_gen, hz, synJk_eq_of_zero hz, Nat.zero_div]
      rw [e]
      exact lr_weaken body (sg_ifNE_neg body (by rw [wx, hz]; rfl) (sg_skip body)) rfl
        (by simp [synCntPassCost, hz])
    · have hne : w x ≠ [] := by rw [wx]; simpa using hz
      have hJ : synJk k X (t + 1) = synJk k X t + 1 := by
        rw [synJk_succ, ite_eq_left (Nat.pos_of_ne_zero hz)]
      refine lr_weaken body (sg_ifNE_pos body (q := synSkip) hne
        ((sgU_div body (k := k) (a := x) (b := .s 17) (t := .s 2) (x := X / k ^ t) (y := 0) hk
          hx17 hx2 (by decide) w2 (by rw [wx]; simp) (by simp [w17])).seq <|
        (sgU_clear body (a := x) (x := X / k ^ t) (by simp [Function.update_apply, hx17, wx])).seq <|
        (sgU_move body (a := .s 17) (b := x) (x := X / k ^ t / k) h17x
          (by simp [Function.update_apply, h17x]) (by simp)).seq <|
        sgU_push body (a := cnt) (y := synJk k X t)
          (by simp [Function.update_apply, hcx, hc17, wc]))) ?_ ?_
      · refine congrArg (synG R) ?_
        funext y
        simp only [hw, Φ, Function.update_apply, hJ, div_pow_succ_gen]
        split_ifs <;> simp_all
      · simp only [synCntPassCost, hz, ite_false]
        omega
  have h := sg_scan body (R := R) (a := ctr) (t := .s 23) hr23 Φ cs
    (fun t => synCntPassCost k X t) hstep
  rw [hctr] at h
  refine lr_weaken body (lr_congr_left body h ?_) ?_ le_rfl
  · refine congrArg (synG R) ?_
    funext z
    simp only [Φ, Function.update_apply, synJk, List.range_zero, List.filter_nil,
      List.length_nil, pow_zero, Nat.div_one, List.replicate_zero]
    split_ifs <;> simp_all
  · refine congrArg (synG R) ?_
    funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all

/-- The step bound of one piece. -/
def synPieceCost (G F Kv d t A0 : ℕ) : ℕ :=
  synMulRCost d (m ^ t) + synMulRCost Kv (d * m ^ t) + (4 * (Kv * (d * m ^ t)) + 5) +
    (4 * A0 + 5) + (4 * d + 5) + (4 * t + 5) +
    (4 * d + 2 * t + 8 + (∑ i ∈ Finset.range t, (8 * expSeq G F d i + 12))) +
    (4 * expSeq G F d t + 4) + (2 * expSeq G F d t + 2) + (4 * (Kv * (d * m ^ t)) + 4) +
    (2 * (d * m ^ t) + 2) + (2 * (Kv * (d * m ^ t)) + 2)

theorem sg_synPiece (G F : ℕ) (v : SynW → List (Fin (A + 4))) (Kv d t A0 E : ℕ)
    (Prl : List (Fin (A + 4))) (hd : v (.s 18) = List.replicate d tick)
    (hP : v (.s 13) = List.replicate (m ^ t) tick) (hJ : v (.s 14) = List.replicate t tick)
    (hA0 : v (.s 15) = List.replicate A0 tick) (hE : v (.s 16) = List.replicate E tick)
    (hpr : v (.p .pr) = Prl) (hK : (v (.p .K)).length = Kv) (h2 : v (.s 2) = [])
    (h3 : v (.s 3) = []) (h4 : v (.s 4) = []) (h19 : v (.s 19) = []) (h20 : v (.s 20) = [])
    (h21 : v (.s 21) = []) :
    LayRuns body (synPieceP G F) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.s 15)
        (List.replicate (Kv * (d * m ^ t) + A0) tick)) (.s 16)
          (List.replicate (expSeq G F d t + E) tick)) (.p .pr)
          (topRec [t, d, A0, Kv * (d * m ^ t)] ++ Prl)))
      (synPieceCost G F Kv d t A0) := by
  refine lr_weaken body
    ((sgU_mulR body (a := .s 18) (b := .s 13) (c := .s 19) (t₁ := .s 2) (t₂ := .s 3) (x := d)
      (y := m ^ t) (z := 0) (by decide) h2 h3 (by simp [hd]) (by simp [hP])
      (by simp [h19])).seq <|
    (sgU_mulR body (a := .p .K) (b := .s 19) (c := .s 20) (t₁ := .s 2) (t₂ := .s 3) (x := Kv)
      (y := d * m ^ t) (z := 0) (by decide) (by simp [h2]) (by simp [h3]) (by simp [hK])
      (by simp) (by simp [h20])).seq <|
    (sgR_fieldF body (a := .s 20) (b := .p .pr) (t := .s 2) (x := Kv * (d * m ^ t)) (l := Prl)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [hpr])).seq <|
    (sgR_fieldF body (a := .s 15) (b := .p .pr) (t := .s 2) (x := A0)
      (l := List.replicate (Kv * (d * m ^ t)) tick ++ topSep :: Prl)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hA0]) (by simp)).seq <|
    (sgR_fieldF body (a := .s 18) (b := .p .pr) (t := .s 2) (x := d)
      (l := List.replicate A0 tick ++ topSep ::
        (List.replicate (Kv * (d * m ^ t)) tick ++ topSep :: Prl))
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hd]) (by simp)).seq <|
    (sgR_fieldF body (a := .s 14) (b := .p .pr) (t := .s 2) (x := t)
      (l := List.replicate d tick ++ topSep :: (List.replicate A0 tick ++ topSep ::
        (List.replicate (Kv * (d * m ^ t)) tick ++ topSep :: Prl)))
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hJ]) (by simp)).seq <|
    (sgU_exp body G F (uR := .s 18) (jR := .s 14) (eR := .s 21) (t₁ := .s 2) (t₂ := .s 3)
      (t₃ := .s 4) (x := d) (y := t) (by decide) (by simp [h21]) (by simp [h2]) (by simp [h3])
      (by simp [h4]) (by simp [hd]) (by simp [hJ])).seq <|
    (sgU_copy body (a := .s 21) (b := .s 16) (t := .s 2) (x := expSeq G F d t) (y := E)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [hE])).seq <|
    (sgU_clear body (a := .s 21) (x := expSeq G F d t) (by simp)).seq <|
    (sgU_copy body (a := .s 20) (b := .s 15) (t := .s 2) (x := Kv * (d * m ^ t)) (y := A0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [hA0])).seq <|
    (sgU_clear body (a := .s 19) (x := d * m ^ t) (by simp)).seq <|
    sgU_clear body (a := .s 20) (x := Kv * (d * m ^ t)) (by simp)) ?_ ?_
  · refine congrArg (synG R) ?_
    funext y
    simp only [Function.update_apply]
    split_ifs <;> (try simp_all [topRec_cons]) <;> omega
  · simp only [synPieceCost]
    omega

/-- The step bound of one pass of the digit loop on `x`. -/
def synDigBodyCost (G F Kv x t A0 : ℕ) : ℕ :=
  (4 * x + 4) + (4 * (x / m) + 4) + (4 * x + 4) + (4 * (m * (x / m)) + 4) +
    (2 * (m * (x / m)) + 2) +
    ((if x - m * (x / m) = 0 then 1 else synPieceCost G F Kv (x - m * (x / m)) t A0) + 2) +
    (2 * (x - m * (x / m)) + 2) + (2 * x + 2) + (2 * (x / m) + 2) + (8 * m ^ t + 8) + 1

theorem sg_synDigBody (G F : ℕ) (v : SynW → List (Fin (A + 4))) (Kv x t A0 E : ℕ)
    (Prl : List (Fin (A + 4))) (hx : v (.s 12) = List.replicate x tick)
    (hP : v (.s 13) = List.replicate (m ^ t) tick) (hJ : v (.s 14) = List.replicate t tick)
    (hA0 : v (.s 15) = List.replicate A0 tick) (hE : v (.s 16) = List.replicate E tick)
    (hpr : v (.p .pr) = Prl) (hK : (v (.p .K)).length = Kv) (h2 : v (.s 2) = [])
    (h3 : v (.s 3) = []) (h4 : v (.s 4) = []) (h17 : v (.s 17) = []) (h18 : v (.s 18) = [])
    (h19 : v (.s 19) = []) (h20 : v (.s 20) = []) (h21 : v (.s 21) = [])
    (h24 : v (.s 24) = []) :
    LayRuns body (synDigBody G F) (synG R v)
      (synG R (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update v (.s 12) (List.replicate (x / m) tick)) (.s 13)
          (List.replicate (m * m ^ t) tick)) (.s 14) (List.replicate (t + 1) tick)) (.s 15)
          (List.replicate (if x - m * (x / m) = 0 then A0
            else Kv * ((x - m * (x / m)) * m ^ t) + A0) tick)) (.s 16)
          (List.replicate (if x - m * (x / m) = 0 then E
            else expSeq G F (x - m * (x / m)) t + E) tick)) (.p .pr)
          (if x - m * (x / m) = 0 then Prl
            else topRec [t, x - m * (x / m), A0, Kv * ((x - m * (x / m)) * m ^ t)] ++ Prl)))
      (synDigBodyCost G F Kv x t A0) := by
  have hm1 : 1 ≤ m := m_pos
  have s1 := sgU_div body (R := R) (v := v) (k := m) (a := .s 12) (b := .s 17) (t := .s 2) (x := x)
    (y := 0) hm1 (by decide) (by decide) (by decide) h2 (by simp [hx]) (by simp [h17])
  have s2 := sgU_umul body (R := R) m (a := .s 17) (b := .s 24) (t := .s 2) (x := x / m) (y := 0)
    (v := Function.update v (.s 17) (List.replicate (x / m + 0) tick)) (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp [h24])
  have s3 := sgU_copy body (R := R) (a := .s 12) (b := .s 18) (t := .s 2) (x := x) (y := 0)
    (v := Function.update (Function.update v (.s 17) (List.replicate (x / m + 0) tick)) (.s 24)
      (List.replicate (m * (x / m) + 0) tick))
    (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hx]) (by simp [h18])
  have s4 := sgU_sub body (R := R) (a := .s 24) (b := .s 18) (t := .s 2) (x := m * (x / m))
    (y := x + 0)
    (v := Function.update (Function.update (Function.update v (.s 17)
      (List.replicate (x / m + 0) tick)) (.s 24) (List.replicate (m * (x / m) + 0) tick)) (.s 18)
      (List.replicate (x + 0) tick))
    (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp)
  have s5 := sgU_clear body (R := R) (a := .s 24) (x := m * (x / m))
    (v := Function.update (Function.update (Function.update (Function.update v (.s 17)
      (List.replicate (x / m + 0) tick)) (.s 24) (List.replicate (m * (x / m) + 0) tick)) (.s 18)
      (List.replicate (x + 0) tick)) (.s 18) (List.replicate (x + 0 - m * (x / m)) tick))
    (by simp)
  set d := x - m * (x / m) with hd
  set v₅ := Function.update (Function.update (Function.update (Function.update (Function.update v
    (.s 17) (List.replicate (x / m + 0) tick)) (.s 24) (List.replicate (m * (x / m) + 0) tick))
    (.s 18) (List.replicate (x + 0) tick)) (.s 18) (List.replicate (x + 0 - m * (x / m)) tick))
    (.s 24) [] with hv₅
  have e18 : v₅ (.s 18) = List.replicate d tick := by simp [hv₅, hd]
  -- the tail after the branch
  have tail : ∀ (A0' E' : ℕ) (Prl' : List (Fin (A + 4))) (w : SynW → List (Fin (A + 4))),
      w (.s 18) = List.replicate d tick → w (.s 12) = List.replicate x tick →
      w (.s 17) = List.replicate (x / m) tick → w (.s 13) = List.replicate (m ^ t) tick →
      w (.s 14) = List.replicate t tick → w (.s 2) = [] → w (.s 3) = [] →
      LayRuns body (.seq (uclear (sreg (.s 18))) <| .seq (uclear (sreg (.s 12))) <|
          .seq (moveR (sreg (.s 17)) (sreg (.s 12)) id) <|
          .seq (synMulIn m (sreg (.s 13)) (sreg (.s 2)) (sreg (.s 3)))
            (synPush (sreg (.s 14)) tick)) (synG R w)
        (synG R (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update w (.s 18) []) (.s 12) []) (.s 17) []) (.s 12)
            (List.replicate (x / m) tick)) (.s 13) (List.replicate (m * m ^ t) tick)) (.s 14)
            (List.replicate (t + 1) tick)))
        (2 * d + 2 + (2 * x + 2 + (2 * (x / m) + 2 + (8 * m ^ t + 8 + 1)))) := by
    intro A0' E' Prl' w w18 w12 w17 w13 w14 w2 w3
    exact lr_weaken body
      ((sgU_clear body (a := .s 18) (x := d) (by simp [w18])).seq <|
      (sgU_clear body (a := .s 12) (x := x) (by simp [w12])).seq <|
      (sgU_move body (a := .s 17) (b := .s 12) (x := x / m) (by decide) (by simp [w17])
        (by simp)).seq <|
      (sgU_mulIn body m (a := .s 13) (t := .s 2) (t₁ := .s 3) (x := m ^ t) (by decide)
        (by simp [w2]) (by simp [w3]) (by simp [w13])).seq <|
      sgU_push body (a := .s 14) (y := t) (by simp [w14])) rfl le_rfl
  by_cases hd0 : d = 0
  · have s6 := sg_ifNE_neg body (p := synPieceP G F) (x := .s 18) (R := R) (v := v₅)
      (by rw [e18, hd0]; rfl) (sg_skip body)
    have s7 := tail A0 E Prl v₅ e18 (by simp [hv₅, hx]) (by simp [hv₅]) (by simp [hv₅, hP])
      (by simp [hv₅, hJ]) (by simp [hv₅, h2]) (by simp [hv₅, h3])
    refine lr_weaken body (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))) ?_ ?_
    · simp only [hd0, ite_true]
      refine congrArg (synG R) ?_
      funext y
      simp only [hv₅, Function.update_apply]
      split_ifs <;> (try simp_all) <;> omega
    · simp only [synDigBodyCost, ← hd, hd0, ite_true]
      omega
  · have s6 := sg_ifNE_pos body (p := synPieceP G F) (q := synSkip) (x := .s 18) (R := R)
      (v := v₅) (by rw [e18]; simpa using hd0)
      (sg_synPiece body G F v₅ Kv d t A0 E Prl e18 (by simp [hv₅, hP]) (by simp [hv₅, hJ])
        (by simp [hv₅, hA0]) (by simp [hv₅, hE]) (by simp [hv₅, hpr]) (by simp [hv₅, hK])
        (by simp [hv₅, h2]) (by simp [hv₅, h3]) (by simp [hv₅, h4]) (by simp [hv₅, h19])
        (by simp [hv₅, h20]) (by simp [hv₅, h21]))
    have s7 := tail (Kv * (d * m ^ t) + A0) (expSeq G F d t + E)
      (topRec [t, d, A0, Kv * (d * m ^ t)] ++ Prl)
      (Function.update (Function.update (Function.update v₅ (.s 15)
        (List.replicate (Kv * (d * m ^ t) + A0) tick)) (.s 16)
          (List.replicate (expSeq G F d t + E) tick)) (.p .pr)
          (topRec [t, d, A0, Kv * (d * m ^ t)] ++ Prl))
      (by simp [e18]) (by simp [hv₅, hx])
      (by simp [hv₅]) (by simp [hv₅, hP]) (by simp [hv₅, hJ]) (by simp [hv₅, h2])
      (by simp [hv₅, h3])
    refine lr_weaken body (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))) ?_ ?_
    · simp only [hd0, ite_false]
      refine congrArg (synG R) ?_
      funext y
      simp only [hv₅, Function.update_apply]
      split_ifs <;> (try simp_all) <;> omega
    · simp only [synDigBodyCost, ← hd, hd0, ite_false]
      omega

/-- The wire file after `t` passes of the digit loop. -/
noncomputable def synDigSt (G F Kv a oS J D : ℕ) (v : SynW → List (Fin (A + 4))) (t : ℕ) :
    SynW → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update v (.s 12) (List.replicate (D / m ^ t) tick)) (.s 13)
      (List.replicate (m ^ synJ D t) tick)) (.s 14) (List.replicate (synJ D t) tick)) (.s 15)
      (List.replicate (oS + Kv * (D % m ^ t)) tick)) (.s 16)
      (List.replicate (synE G F D t) tick)) (.p .pr)
      (topRec (topPcRec Kv (synPcs Kv a D oS J t)))

/-- The step bound of pass `t` of the digit loop. -/
def synDigPassCost (G F Kv oS D t : ℕ) : ℕ :=
  if D / m ^ t = 0 then 3
  else synDigBodyCost G F Kv (D / m ^ t) t (oS + Kv * (D % m ^ t)) + 2

/-- The step bound of the digit loop. -/
def synDigitsCost (G F Kv oS D : ℕ) : ℕ :=
  (4 * D + 4) + 1 + (4 * oS + 4) +
    ((∑ t ∈ Finset.range D, (synDigPassCost G F Kv oS D t + 3)) + 2 * D + 4) +
    2 + (2 * m ^ synJ D D + 2) + (2 * (oS + Kv * D) + 2)

theorem synDigSt_zero_pass {G F Kv a oS J D : ℕ} (v : SynW → List (Fin (A + 4))) {t : ℕ}
    (h : D / m ^ t = 0) : synDigSt G F Kv a oS J D v (t + 1) = synDigSt G F Kv a oS J D v t := by
  have h1 : D / m ^ (t + 1) = 0 := by rw [div_pow_succ', h]; simp
  simp only [synDigSt, h1, h, synJ_eq_of_zero h, mod_pow_of_zero h, synE_succ, synPcs_succ,
    synDg_of_zero h, ite_true, add_zero, List.nil_append]

theorem sg_synDigits (G F : ℕ) (v : SynW → List (Fin (A + 4))) (Kv a oS J D : ℕ)
    (hoS : v (.s 6) = List.replicate oS tick) (hK : (v (.p .K)).length = Kv)
    (hD : (v (.s 26)).length = D) (hpr : v (.p .pr) = [])
    (hs : ∀ i, 12 ≤ i → i ≤ 24 → v (.s i) = []) (h2 : v (.s 2) = []) (h3 : v (.s 3) = [])
    (h4 : v (.s 4) = []) :
    LayRuns body (synDigits G F) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.s 14)
        (List.replicate (synJ D D) tick)) (.s 16) (List.replicate (synE G F D D) tick)) (.p .pr)
        (topRec (topPcRec Kv (synPcs Kv a D oS J D)))))
      (synDigitsCost G F Kv oS D) := by
  have hz : ∀ i : Fin 32, 12 ≤ (i : ℕ) → (i : ℕ) ≤ 24 → v (.s i) = [] := fun i h1 h2 => hs i h1 h2
  have h12 := hz 12 (by decide) (by decide)
  have h13 := hz 13 (by decide) (by decide)
  have h14 := hz 14 (by decide) (by decide)
  have h15 := hz 15 (by decide) (by decide)
  have h16 := hz 16 (by decide) (by decide)
  have h17 := hz 17 (by decide) (by decide)
  have h18 := hz 18 (by decide) (by decide)
  have h19 := hz 19 (by decide) (by decide)
  have h20 := hz 20 (by decide) (by decide)
  have h21 := hz 21 (by decide) (by decide)
  have h23 := hz 23 (by decide) (by decide)
  have h24 := hz 24 (by decide) (by decide)
  set cs := v (.s 26) with hcs
  set Φ := synDigSt G F Kv a oS J D v with hΦ
  have hstep : ∀ t < cs.length, LayRuns body (synIfNE (sreg (.s 12)) (synDigBody G F) synSkip)
      (synG R (Function.update (Function.update (Φ t) (.s 26) (cs.drop (t + 1))) (.s 23)
        (cs.take (t + 1)).reverse))
      (synG R (Function.update (Function.update (Φ (t + 1)) (.s 26) (cs.drop (t + 1))) (.s 23)
        (cs.take (t + 1)).reverse)) (synDigPassCost G F Kv oS D t) := by
    intro t _
    set w := Function.update (Function.update (Φ t) (.s 26) (cs.drop (t + 1))) (.s 23)
      (cs.take (t + 1)).reverse with hw
    by_cases hx : D / m ^ t = 0
    · rw [hΦ, synDigSt_zero_pass v hx]
      refine lr_weaken body (sg_ifNE_neg body (by simp [hw, hΦ, synDigSt, hx]) (sg_skip body))
        rfl (by simp [synDigPassCost, hx])
    · have hJt : synJ D t = t := synJ_eq_of_pos (Nat.pos_of_ne_zero hx)
      have hb := sg_synDigBody body (R := R) G F w Kv (D / m ^ t) t (oS + Kv * (D % m ^ t))
        (synE G F D t) (topRec (topPcRec Kv (synPcs Kv a D oS J t)))
        (by simp [hw, hΦ, synDigSt]) (by simp [hw, hΦ, synDigSt, hJt])
        (by simp [hw, hΦ, synDigSt, hJt]) (by simp [hw, hΦ, synDigSt])
        (by simp [hw, hΦ, synDigSt]) (by simp [hw, hΦ, synDigSt]) (by simp [hw, hΦ, synDigSt, hK])
        (by simp [hw, hΦ, synDigSt, h2]) (by simp [hw, hΦ, synDigSt, h3])
        (by simp [hw, hΦ, synDigSt, h4]) (by simp [hw, hΦ, synDigSt, h17])
        (by simp [hw, hΦ, synDigSt, h18]) (by simp [hw, hΦ, synDigSt, h19])
        (by simp [hw, hΦ, synDigSt, h20]) (by simp [hw, hΦ, synDigSt, h21])
        (by simp [hw, hΦ, synDigSt, h24])
      refine lr_weaken body (sg_ifNE_pos body (q := synSkip)
        (by
          rw [show w (.s 12) = List.replicate (D / m ^ t) tick by simp [hw, hΦ, synDigSt]]
          intro h; exact hx (by simpa using congrArg List.length h)) hb) ?_
        (by simp [synDigPassCost, hx])
      have hJ1 : synJ D (t + 1) = t + 1 := by rw [synJ_succ, hJt]; simp [Nat.pos_of_ne_zero hx]
      have hdg := synDg_eq D t
      rw [hdg]
      refine congrArg (synG R) ?_
      have e12 : D / m ^ t / m = D / m ^ (t + 1) := (div_pow_succ' D t).symm
      have e13 : m * m ^ t = m ^ (t + 1) := (pow_succ' m t).symm
      have e15 : (if synDg D t = 0 then oS + Kv * (D % m ^ t)
          else Kv * (synDg D t * m ^ t) + (oS + Kv * (D % m ^ t))) =
          oS + Kv * (D % m ^ (t + 1)) := by
        rw [mod_pow_succ_dg]
        split_ifs with h0
        · rw [h0]; ring
        · ring
      have e16 : (if synDg D t = 0 then synE G F D t
          else expSeq G F (synDg D t) t + synE G F D t) = synE G F D (t + 1) := by
        rw [synE_succ]; split_ifs <;> ring
      have epr : (if synDg D t = 0 then topRec (topPcRec Kv (synPcs Kv a D oS J t))
          else topRec [t, synDg D t, oS + Kv * (D % m ^ t), Kv * (synDg D t * m ^ t)] ++
            topRec (topPcRec Kv (synPcs Kv a D oS J t))) =
          (topRec (topPcRec Kv (synPcs Kv a D oS J (t + 1))) : List (Fin (A + 4))) := by
        rw [synPcs_succ]
        split_ifs with h0
        · simp
        · rw [show topPcRec Kv ([synPc Kv a D oS J t] ++ synPcs Kv a D oS J t) =
              topPcFields Kv (synPc Kv a D oS J t) ++ topPcRec Kv (synPcs Kv a D oS J t) by
              simp [topPcRec], topRec_append, topPcFields_synPc]
      rw [e12, e13, e15, e16, epr]
      funext y
      simp only [hw, hΦ, synDigSt, Function.update_apply, hJ1]
      split_ifs <;> simp_all
  have hscan := sg_scan body (R := R) (a := .s 26) (t := .s 23) (by decide) Φ cs
    (fun t => synDigPassCost G F Kv oS D t) hstep
  have hcsl : cs.length = D := hD
  rw [hcsl] at hscan
  have hfin : Φ D (.s 12) = [] := by simp [hΦ, synDigSt, div_pow_self]
  refine lr_weaken body
    ((sgU_copy body (a := .s 26) (b := .s 12) (t := .s 2) (x := D) (y := 0) (by decide)
      (by decide) (by decide) h2 hD (by simp [h12])).seq <|
    (sgU_push body (a := .s 13) (y := 0) (by simp [h13])).seq <|
    (sgU_copy body (a := .s 6) (b := .s 15) (t := .s 2) (x := oS) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hoS]) (by simp [h15])).seq <|
    (lr_congr_left body hscan ?_).seq <|
    (sgU_clear body (a := .s 12) (x := 0) (by simp [hΦ, synDigSt, div_pow_self])).seq <|
    (sgU_clear body (a := .s 13) (x := m ^ synJ D D) (by simp [hΦ, synDigSt])).seq <|
    sgU_clear body (a := .s 15) (x := oS + Kv * D) (by simp [hΦ, synDigSt, mod_pow_self])) ?_ ?_
  · refine congrArg (synG R) ?_
    funext y
    simp only [hΦ, synDigSt, Function.update_apply, synJ, synJk, synE, synPcs, Nat.pow_zero,
      Nat.div_one, Nat.mod_one]
    split_ifs <;> simp_all [topPcRec]
  · refine congrArg (synG R) ?_
    funext y
    simp only [hΦ, synDigSt, Function.update_apply]
    split_ifs <;> simp_all [div_pow_self]
  · simp only [synDigitsCost]
    omega

theorem sg_synNWLoop (v : SynW → List (Fin (A + 4))) (n y : ℕ) (h22 : (v (.s 22)).length = n)
    (h23 : v (.s 23) = []) (h7 : v (.s 7) = List.replicate y tick) (h2 : v (.s 2) = [])
    (h3 : v (.s 3) = []) :
    LayRuns body synNWLoop (synG R v)
      (synG R (Function.update v (.s 7) (List.replicate (NW ^ n * y) tick)))
      (∑ j ∈ Finset.range n, (8 * (NW ^ j * y) + 8 + 3) + 2 * n + 4) := by
  set cs := v (.s 22) with hcs
  let Φ : ℕ → SynW → List (Fin (A + 4)) := fun j =>
    Function.update v (.s 7) (List.replicate (NW ^ j * y) tick)
  have hstep : ∀ j < cs.length, LayRuns body (synMulIn NW (sreg (.s 7)) (sreg (.s 2)) (sreg (.s 3)))
      (synG R (Function.update (Function.update (Φ j) (.s 22) (cs.drop (j + 1))) (.s 23)
        (cs.take (j + 1)).reverse))
      (synG R (Function.update (Function.update (Φ (j + 1)) (.s 22) (cs.drop (j + 1))) (.s 23)
        (cs.take (j + 1)).reverse)) (8 * (NW ^ j * y) + 8) := by
    intro j _
    refine lr_weaken body (sgU_mulIn body NW (a := .s 7) (t := .s 2) (t₁ := .s 3)
      (x := NW ^ j * y) (by decide) (by simp [Φ, h2]) (by simp [Φ, h3]) (by simp [Φ])) ?_ le_rfl
    refine congrArg (synG R) ?_
    funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all [pow_succ]; ring
  have h := sg_scan body (R := R) (a := .s 22) (t := .s 23) (by decide) Φ cs
    (fun j => 8 * (NW ^ j * y) + 8) hstep
  rw [h22] at h
  refine lr_weaken body (lr_congr_left body h ?_) ?_ le_rfl
  · refine congrArg (synG R) ?_
    funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all
  · refine congrArg (synG R) ?_
    funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all

end DigitLoop

end IntegerMultBounds.MathlibTM2.Fast
