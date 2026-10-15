module

public import IntegerMultBounds.Schoenhage.TwistRound
public import IntegerMultBounds.Schoenhage.DifRound
public import IntegerMultBounds.Schoenhage.Lists

/-! The twist descriptors of a §6 slot round, computed on tapes. The round's
exponent at physical address `y` is a bilinear form in the address bits: for
each participating axis, its slot bit times the axis bits below the slot,
weighted by powers of two (`slotExp`). A table lists one entry per pair
(slot bit position, lower bit position, doubled weight); its value at `y` is
twice the exponent (`tableVal_slotTable`). One word program walks the records
in physical order with a binary address counter, sums each record's entries in
doubled unary modulo `4r`, negates, splits at `2r`, and appends the record's
four descriptor words for the array monomial. -/

@[expose] public section

set_option maxRecDepth 100000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct NLogN

namespace TwistDescriptors

/-! ### Exponent tables -/

/-- A table entry: a slot bit position, a lower bit position and a doubled weight. -/
abbrev Entry := ℕ × ℕ × ℕ

/-- The entry's contribution at address `y`: its weight when both bits are set. -/
def entryVal (y : ℕ) (e : Entry) : ℕ := if bitAt y e.1 = 1 ∧ bitAt y e.2.1 = 1 then e.2.2 else 0

/-- The table's value at address `y`. -/
def tableVal (y : ℕ) (es : List Entry) : ℕ := (es.map (entryVal y)).sum

/-- The table of a slot round: for each participating axis `i` and each slot `h' < h`, the
physical positions of its slot bit and of its bit `h'`, with weight `2 · (2r / 2^(h+1)) · 2^h'`. -/
def slotTable {n : ℕ} (π : BitPerm n) (r : ℕ) (ts : List ℕ) (Is : List ℕ) (h : ℕ) : List Entry :=
  Is.flatMap fun i => (List.range h).map fun h' =>
    (π.σ (axOff ts i + h), π.σ (axOff ts i + h'), 2 * (2 * r / 2 ^ (h + 1) * 2 ^ h'))

theorem bitAt_le_one (x h : ℕ) : bitAt x h ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))

/-- The bits `o, …, o + h - 1` of `x` as a number. -/
theorem div_mod_eq_sum (x o : ℕ) : ∀ h : ℕ,
    x / 2 ^ o % 2 ^ h = ((List.range h).map fun h' => 2 ^ h' * bitAt x (o + h')).sum
  | 0 => by simp [Nat.mod_one]
  | h + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, ← div_mod_eq_sum x o h]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have hb : bitAt x (o + h) = x / 2 ^ o / 2 ^ h % 2 := by
      unfold bitAt; rw [Nat.div_div_eq_div_mul, ← pow_add]
    rw [hb, pow_succ, Nat.mod_mul, Nat.mul_comm (2 ^ h)]

theorem sum_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → ℕ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- `tableVal_slotTable`: the table's value is twice the round's exponent. -/
theorem tableVal_slotTable {n : ℕ} (π : BitPerm n) (r : ℕ) (ts : List ℕ) (Is : List ℕ) (h : ℕ)
    (hpos : ∀ i ∈ Is, axOff ts i + h < n) (y : ℕ) :
    tableVal y (slotTable π r ts Is h) = 2 * slotExp π r ts Is h y := by
  unfold tableVal slotTable slotExp
  rw [sum_map_flatMap, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hih := hpos i hi
  simp only [List.map_map, Function.comp_def]
  unfold axExp rexp
  have hslot : bitAt y (π.σ (axOff ts i + h)) = bitAt (π.logi y) (axOff ts i + h) :=
    (π.bitAt_logi y hih).symm
  have hlow : ∀ h' ∈ List.range h, bitAt y (π.σ (axOff ts i + h')) = bitAt (π.logi y) (axOff ts i + h') :=
    fun h' hh' => (π.bitAt_logi y (by have := List.mem_range.mp hh'; omega)).symm
  rw [div_mod_eq_sum (π.logi y) (axOff ts i) h]
  by_cases hz : bitAt (π.logi y) (axOff ts i + h) = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hz), mul_zero]
    apply List.sum_eq_zero
    intro v hv
    simp only [List.mem_map, List.mem_range] at hv
    obtain ⟨h', hh', rfl⟩ := hv
    simp [entryVal, hslot, hz]
  · have hone : bitAt (π.logi y) (axOff ts i + h) = 1 := by
      have := bitAt_le_one (π.logi y) (axOff ts i + h); omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false hz), ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro h' hh'
    simp only [entryVal, hslot, hone, hlow h' hh', true_and]
    by_cases hb : bitAt (π.logi y) (axOff ts i + h') = 0
    · simp [hb]
    · have : bitAt (π.logi y) (axOff ts i + h') = 1 := by
        have := bitAt_le_one (π.logi y) (axOff ts i + h'); omega
      simp only [this, ↓reduceIte, mul_one]

/-! ### Stream rules -/

/-- Emit the driver's bit at the position given by the other input's length. -/
abbrev pick : Rule 1 where
  Q := Bool
  q0 := false
  step q b o := if q then (true, none, fun _ => false)
    else match o 0 with
      | some _ => (false, none, fun _ => true)
      | none => (true, some (some b), fun _ => false)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

theorem go_pick_done : ∀ (y : List Bool) (ws : Fin 1 → List Bool), (go pick true y ws).2.1 = []
  | [], _ => rfl
  | b :: y, ws => by simp [go, go_pick_done y]

theorem go_pick : ∀ (P : ℕ) (y : List Bool), P < y.length →
    (go pick false y (fun _ => ones P)).2.1 = [some (y.getD P false)]
  | _, [], h => by simp at h
  | 0, b :: y, _ => by
    simp only [go]
    simp [ones, go_pick_done]
  | P + 1, b :: y, h => by
    simp only [go]
    have ih := go_pick P y (by simp at h; omega)
    have e : (fun j : Fin 1 => if (fun _ => true : Fin 1 → Bool) j then (ones (P + 1)).tail else ones (P + 1)) =
        fun _ => ones P := by funext j; simp [ones, List.replicate_succ]
    simp [ones, List.replicate_succ] at ih ⊢
    exact ih

theorem output_pick {P : ℕ} {y : List Bool} (h : P < y.length) :
    output pick y (fun _ => ones P) = syms [[y.getD P false]] := by
  simp [output, go_pick P y h, syms]

/-- Emit whether the driver is longer than the other input. -/
abbrev geq : Rule 1 where
  Q := Bool
  q0 := false
  step q _ o := (q || (o 0).isNone, none, fun _ => true)
  flush q := [some q, none]
  B := 2
  hB _ := le_rfl

theorem go_geq : ∀ (q : Bool) (x : List Bool) (c : ℕ),
    go geq q x (fun _ => ones c) = (q || decide (c < x.length), [], fun _ => ones (c - x.length))
  | q, [], c => by simp [go]
  | q, b :: x, c => by
    have ih := go_geq (q || (ones c).head?.isNone) x (c - 1)
    have htail : (ones c).tail = ones (c - 1) := by simp [ones, List.tail_replicate]
    simp only [go, ite_true, htail, ih]
    rcases c with _ | c
    · simp [ones]
    · refine Prod.ext ?_ (Prod.ext (by simp) ?_) <;> (try funext j) <;>
        simp [ones, List.replicate_succ]

theorem output_geq (x : List Bool) (c : ℕ) :
    output geq x (fun _ => ones c) = syms [[decide (c < x.length)]] := by
  simp [output, go_geq, syms]

/-- Binary increment modulo `2^|y|`, least significant bit first. -/
abbrev inc : Rule 0 where
  Q := Bool
  q0 := true
  step c b _ := (b && c, some (some (b ^^ c)), fun _ => false)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

/-- The incremented word. -/
def incW : Bool → List Bool → List Bool
  | _, [] => []
  | c, b :: y => (b ^^ c) :: incW (b && c) y

theorem go_inc : ∀ (c : Bool) (y : List Bool) (ws : Fin 0 → List Bool),
    (go inc c y ws).2.1 = (incW c y).map some
  | _, [], _ => rfl
  | c, b :: y, ws => by simp only [go]; simp [incW, go_inc]

theorem output_inc (y : List Bool) (ws : Fin 0 → List Bool) : output inc y ws = syms [incW true y] := by
  simp [output, go_inc, syms]

theorem length_incW : ∀ (c : Bool) (y : List Bool), (incW c y).length = y.length
  | _, [] => rfl
  | c, b :: y => by simp [incW, length_incW]

theorem incW_bits : ∀ (n v : ℕ) (c : Bool), incW c (bits n v) = bits n (v + if c then 1 else 0)
  | 0, _, _ => rfl
  | n + 1, v, c => by
    simp only [bits, incW]
    rw [incW_bits n]
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;> cases c <;> simp [hv] <;> omega
    · congr 1
      rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;> cases c <;> simp [hv] <;> omega

theorem getD_bits : ∀ (n v P : ℕ), P < n → (bits n v).getD P false = decide (bitAt v P = 1)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, v, 0, _ => by simp [bits, bitAt]
  | n + 1, v, P + 1, h => by
    simp only [bits, List.getD_cons_succ]
    rw [getD_bits n (v / 2) P (by omega)]
    unfold bitAt
    rw [pow_succ, mul_comm, ← Nat.div_div_eq_div_mul]

/-! ### The record arithmetic -/

/-- One entry added to the accumulator in doubled unary modulo `4r`: one subtraction suffices. -/
def accStep (r y m : ℕ) (e : Entry) : ℕ :=
  if 4 * r - 1 < m + entryVal y e then m + entryVal y e - 4 * r else m + entryVal y e

theorem entryVal_le (y : ℕ) (e : Entry) : entryVal y e ≤ e.2.2 := by
  unfold entryVal; split_ifs <;> omega

theorem foldl_accStep {r y : ℕ} (hr : 1 ≤ r) :
    ∀ (es : List Entry), (∀ e ∈ es, e.2.2 ≤ 4 * r) → ∀ m, m < 4 * r →
      es.foldl (accStep r y) m = (m + tableVal y es) % (4 * r)
  | [], _, m, hm => by simp [tableVal, Nat.mod_eq_of_lt hm]
  | e :: es, hw, m, hm => by
    have hv := (entryVal_le y e).trans (hw e (by simp))
    have hstep : accStep r y m e = (m + entryVal y e) % (4 * r) := by
      unfold accStep
      split_ifs with h
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_of_lt (by omega)]
    rw [List.foldl_cons, hstep, foldl_accStep hr es (fun e he => hw e (by simp [he])) _
      (Nat.mod_lt _ (by omega))]
    simp only [tableVal, List.map_cons, List.sum_cons]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, add_assoc]

/-- The negated sum: `4r - E`, with `4r` itself replaced by zero. -/
def negE (r E : ℕ) : ℕ := if 4 * r - 1 < 4 * r - E then 0 else 4 * r - E

/-- The flag of the split at `2r`. -/
def splitFlag (r X : ℕ) : Bool := decide (2 * r - 1 < X)

/-- The remainder of the split at `2r`. -/
def splitRem (r X : ℕ) : ℕ := if splitFlag r X then X - 2 * r else X

/-- The record arithmetic yields the array monomial's descriptors of `twistExp r e`. -/
theorem desc_math {r : ℕ} (hr : 1 ≤ r) (e : ℕ) :
    negE r (2 * e % (4 * r)) = 2 * TwistRound.twistExp r e ∧
      splitRem r (negE r (2 * e % (4 * r))) = 2 * (TwistRound.twistExp r e % r) ∧
      2 * r - splitRem r (negE r (2 * e % (4 * r))) = 2 * (r - TwistRound.twistExp r e % r) ∧
      splitFlag r (negE r (2 * e % (4 * r))) = decide (TwistRound.twistExp r e / r % 2 = 1) := by
  have h2r : 0 < 2 * r := by omega
  have hmod : 2 * e % (4 * r) = 2 * (e % (2 * r)) := by
    rw [show 4 * r = 2 * (2 * r) by ring, Nat.mul_mod_mul_left]
  set a := e % (2 * r) with ha
  have halt : a < 2 * r := Nat.mod_lt _ h2r
  have hX : negE r (2 * e % (4 * r)) = 2 * TwistRound.twistExp r e := by
    rw [hmod]
    unfold negE TwistRound.twistExp
    rw [← ha]
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · rw [h0]; simp [Nat.mod_self]
    · split_ifs with hc
      · omega
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨T, hTdef⟩ : ∃ T, T = TwistRound.twistExp r e := ⟨_, rfl⟩
  rw [← hTdef] at hX ⊢
  have hTlt : T < 2 * r := hTdef ▸ Nat.mod_lt _ h2r
  refine ⟨hX, ?_, ?_, ?_⟩ <;> rw [hX] <;> simp only [splitRem, splitFlag]
  · by_cases hge : r ≤ T
    · have hflag : decide (2 * r - 1 < 2 * T) = true := by simp; omega
      simp only [hflag, ↓reduceIte]
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]; omega
    · have hflag : decide (2 * r - 1 < 2 * T) = false := by simp; omega
      simp only [hflag, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega)]
  · by_cases hge : r ≤ T
    · have hflag : decide (2 * r - 1 < 2 * T) = true := by simp; omega
      simp only [hflag, ↓reduceIte]
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]; omega
    · have hflag : decide (2 * r - 1 < 2 * T) = false := by simp; omega
      simp only [hflag, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
  · by_cases hge : r ≤ T
    · have : T / r = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      simp [this]; omega
    · have : T / r = 0 := Nat.div_eq_of_lt (by omega)
      simp [this]; omega

/-! ### The program -/

/-- The address counter (binary, least significant bit first). -/
abbrev gY : Fin 18 := 0
/-- The exponent table: three words per entry. -/
abbrev gT : Fin 18 := 1
/-- One tick per record. -/
abbrev gC : Fin 18 := 2
/-- The accumulator (doubled unary). -/
abbrev gA : Fin 18 := 3
abbrev gB1 : Fin 18 := 4
abbrev gB2 : Fin 18 := 5
abbrev gB3 : Fin 18 := 6
/-- `ones (4r - 1)`. -/
abbrev gK3 : Fin 18 := 7
/-- `ones (4r)`. -/
abbrev gK4 : Fin 18 := 8
/-- `ones (2r - 1)`. -/
abbrev gH1 : Fin 18 := 9
/-- `ones (2r)`. -/
abbrev gH2 : Fin 18 := 10
abbrev gS : Fin 18 := 11
/-- The junk tape. -/
abbrev gJ : Fin 18 := 12
/-- The negated sum. -/
abbrev gE : Fin 18 := 13
/-- The four descriptor lists. -/
abbrev gdH : Fin 18 := 14
abbrev gdT : Fin 18 := 15
abbrev gdF : Fin 18 := 16
abbrev gdG : Fin 18 := 17

/-- Subtract `4r` from the accumulator. -/
noncomputable def sub4 : Cmd 0 18 :=
  .seq (rewind gA) <| .seq (op1 Rules.drop false gA gK4 gS (by decide) (by decide) (by decide)) <|
  .seq (rewind gK4) <| .seq (clear gA) <| .seq (rewind gS) <| .seq (cpy gS gA (by decide)) (clear gS)

/-- Test whether the accumulator reached `4r`, into `gB3`. -/
noncomputable def testAcc : Cmd 0 18 :=
  .seq (rewind gA) <| .seq (op1 geq false gA gK3 gB3 (by decide) (by decide) (by decide)) <|
  .seq (rewind gK3) (rewind gB3)

/-- Subtract `4r` once if the accumulator reached it. -/
noncomputable def reduce : Cmd 0 18 := .seq testAcc <| .seq (.cond gB3 sub4 (rewind gJ)) (clear gB3)

/-- Add the entry's weight to the accumulator, modulo `4r`. -/
noncomputable def addWeight : Cmd 0 18 := .seq (op0 Rules.copy true gT gA (by decide)) reduce

/-- Read the entry's two address bits into `gB1` and `gB2`. -/
noncomputable def readBits : Cmd 0 18 :=
  .seq (op1 pick false gY gT gB1 (by decide) (by decide) (by decide)) <| .seq (rewind gY) <|
  .seq (op1 pick false gY gT gB2 (by decide) (by decide) (by decide)) <| .seq (rewind gY) <|
  .seq (rewind gB1) (rewind gB2)

/-- One table entry: read both address bits, and add the weight when both are set. -/
noncomputable def entry : Cmd 0 18 :=
  .seq readBits <|
  .seq (.cond gB1 (.cond gB2 addWeight (skp gT gJ (by decide))) (skp gT gJ (by decide))) <|
  .seq (clear gB1) (clear gB2)

theorem startsOne_reg (b : Bool) : StartsOne (⟨[], [[b]]⟩ : WTape) ↔ b = true := startsOne_mk [] b [] []

theorem ones_append (m w : ℕ) : ones m ++ ones w = ones (m + w) := by unfold ones; rw [List.replicate_add]

set_option maxHeartbeats 4000000 in
theorem runs_sub4 {r m : ℕ} (σ : Fin 18 → WTape) (hA : σ gA = ⟨[ones m], []⟩)
    (hK4 : σ gK4 = reg (ones (4 * r))) (hS : σ gS = emp) :
    Runs sub4 σ (· = Function.update σ gA ⟨[ones (m - 4 * r)], []⟩) (10 * m + 20 * r + 60) := by
  have t1 := time_le Rules.drop (ones m) (fun _ => ones (4 * r)) (4 * r) (fun _ => by simp)
  apply Runs.of_wp
  simp only [sub4, cpy, WP, wp_op1, wp_op0, wp_rewind, wp_clear]
  tsimp [hA, hK4, hS, emp, reg, Rules.output_drop, Rules.output_copy]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hA, hK4, hS, emp, reg]
  · have := Nat.sub_le m (4 * r)
    simp [clen, WTape.words, time_copy] at t1 ⊢; omega

set_option maxHeartbeats 4000000 in
theorem runs_reduce {r m : ℕ} (hr : 1 ≤ r) (σ : Fin 18 → WTape) (hA : σ gA = ⟨[ones m], []⟩)
    (hK3 : σ gK3 = reg (ones (4 * r - 1))) (hK4 : σ gK4 = reg (ones (4 * r))) (hB3 : σ gB3 = emp)
    (hS : σ gS = emp) (hJ : σ gJ = emp) :
    Runs reduce σ (· = Function.update σ gA ⟨[ones (if 4 * r - 1 < m then m - 4 * r else m)], []⟩)
      (14 * m + 40 * r + 120) := by
  have t1 : time geq (ones m) (fun _ => ones (4 * r - 1)) ≤ m + 4 * r + 7 :=
    (time_le geq (ones m) (fun _ => ones (4 * r - 1)) (4 * r) (fun _ => by simp)).trans (by simp)
  have hg := output_geq (ones m) (4 * r - 1)
  simp only [length_ones] at hg
  -- the test
  set σ₁ := Function.update (Function.update (Function.update σ gA ⟨[ones m], []⟩) gK3 (reg (ones (4 * r - 1))))
    gB3 ⟨[], [[decide (4 * r - 1 < m)]]⟩ with hσ₁
  have s1 : Runs testAcc σ (· = σ₁) (2 * m + 10 * r + 30) := by
    apply Runs.of_wp
    simp only [testAcc, WP, wp_op1, wp_rewind]
    tsimp [hA, hK3, hB3, emp, reg, hg]
    refine ⟨?_, ?_⟩
    · funext i; fin_cases i <;> rfl
    · omega
  have hA₁ : σ₁ gA = ⟨[ones m], []⟩ := by tsimp [hσ₁]
  have hK4₁ : σ₁ gK4 = reg (ones (4 * r)) := by tsimp [hσ₁, hK4]
  have hS₁ : σ₁ gS = emp := by tsimp [hσ₁, hS]
  have hJ₁ : σ₁ gJ = emp := by tsimp [hσ₁, hJ]
  have hB3₁ : σ₁ gB3 = ⟨[], [[decide (4 * r - 1 < m)]]⟩ := by tsimp [hσ₁]
  by_cases hf : 4 * r - 1 < m
  · have s2 := runs_sub4 σ₁ hA₁ hK4₁ hS₁
    have s3 := runs_clear (a := 0) gB3 (Function.update σ₁ gA ⟨[ones (m - 4 * r)], []⟩)
    have sc := Runs.cond_true (d := rewind gJ) (by rw [hB3₁, startsOne_reg]; simpa using hf) s2
    refine (Runs.then s1 (Runs.then sc s3)).mono (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, hf, hA, hK3, hK4, hB3, hS, hJ, emp, reg]
    · tsimp [clen, WTape.words, hσ₁]; omega
  · have s2 := runs_rewind (a := 0) gJ σ₁
    have s3 := runs_clear (a := 0) gB3 (Function.update σ₁ gJ ⟨[], (σ₁ gJ).left.reverse ++ (σ₁ gJ).right⟩)
    have sc := Runs.cond_false (c := sub4) (by rw [hB3₁, startsOne_reg]; simpa using hf) s2
    refine (Runs.then s1 (Runs.then sc s3)).mono (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, hf, hA, hK3, hK4, hB3, hS, hJ, emp, reg]
    · tsimp [clen, WTape.words, hσ₁, hJ, emp]; omega

set_option maxHeartbeats 4000000 in
theorem runs_readBits {Ps Pl : ℕ} {y : List Bool} (hPs : Ps < y.length) (hPl : Pl < y.length)
    (σ : Fin 18 → WTape) (hY : σ gY = reg y) {LT R : List (List Bool)}
    (hT : σ gT = ⟨LT, ones Ps :: ones Pl :: R⟩) (hB1 : σ gB1 = emp) (hB2 : σ gB2 = emp) :
    Runs readBits σ (· = Function.update (Function.update (Function.update σ gT ⟨ones Pl :: ones Ps :: LT, R⟩)
      gB1 ⟨[], [[y.getD Ps false]]⟩) gB2 ⟨[], [[y.getD Pl false]]⟩) (8 * y.length + 50) := by
  have t1 : time pick y (fun _ => ones Ps) ≤ 2 * y.length + 7 :=
    (time_le pick y (fun _ => ones Ps) Ps (fun _ => by simp)).trans (by simp; omega)
  have t2 : time pick y (fun _ => ones Pl) ≤ 2 * y.length + 7 :=
    (time_le pick y (fun _ => ones Pl) Pl (fun _ => by simp)).trans (by simp; omega)
  have o1 := output_pick hPs
  have o2 := output_pick hPl
  apply Runs.of_wp
  simp only [readBits, WP, wp_op1, wp_rewind]
  tsimp [hY, hT, hB1, hB2, emp, reg, o1, o2]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hY, hT, hB1, hB2, emp, reg]
  · omega

set_option maxHeartbeats 4000000 in
theorem runs_addWeight {r m w : ℕ} (hr : 1 ≤ r) (σ : Fin 18 → WTape) {LT R : List (List Bool)}
    (hT : σ gT = ⟨LT, ones w :: R⟩) (hA : σ gA = ⟨[ones m], []⟩)
    (hK3 : σ gK3 = reg (ones (4 * r - 1))) (hK4 : σ gK4 = reg (ones (4 * r))) (hB3 : σ gB3 = emp)
    (hS : σ gS = emp) (hJ : σ gJ = emp) :
    Runs addWeight σ (· = Function.update (Function.update σ gT ⟨ones w :: LT, R⟩) gA
      ⟨[ones (if 4 * r - 1 < m + w then m + w - 4 * r else m + w)], []⟩) (15 * (m + w) + 40 * r + 140) := by
  have s1 := runs_op0 (a := 0) Rules.copy true (show gT ≠ gA by decide) σ (by simp [hT]) (by simp [hA])
    [ones w] (by simp [hT, Rules.output_copy]) (fun _ => ⟨by simp [hA], by simp⟩)
  set σ₁ := Function.update (Function.update σ gT (σ gT).next) gA ((σ gA).put true [ones w]) with hσ₁
  have hA₁ : σ₁ gA = ⟨[ones (m + w)], []⟩ := by tsimp [hσ₁, hA, ones_append]
  have s2 := runs_reduce hr σ₁ hA₁ (by tsimp [hσ₁, hK3]) (by tsimp [hσ₁, hK4]) (by tsimp [hσ₁, hB3])
    (by tsimp [hσ₁, hS]) (by tsimp [hσ₁, hJ])
  refine (Runs.then s1 s2).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, hT, hA]
  · have : time Rules.copy (σ gT).cur (fun j => j.elim0) = w + 6 := by simp [hT, time_copy]
    rw [this]; omega

/-- The scratch tapes are empty and the constants are in place. -/
def Ready (r : ℕ) (σ : Fin 18 → WTape) : Prop :=
  σ gB1 = emp ∧ σ gB2 = emp ∧ σ gB3 = emp ∧ σ gS = emp ∧ σ gJ = emp ∧
    σ gK3 = reg (ones (4 * r - 1)) ∧ σ gK4 = reg (ones (4 * r)) ∧
    σ gH1 = reg (ones (2 * r - 1)) ∧ σ gH2 = reg (ones (2 * r))

set_option maxHeartbeats 8000000 in
/-- `runs_entry`: one entry adds its weight to the accumulator, modulo `4r`, when both address
bits are set. -/
theorem runs_entry {r n Y m Ps Pl w : ℕ} (hr : 1 ≤ r) (hPs : Ps < n) (hPl : Pl < n) (hm : m < 4 * r)
    (hw : w ≤ 4 * r) (σ : Fin 18 → WTape) (hR : Ready r σ) (hY : σ gY = reg (bits n Y))
    {LT RT : List (List Bool)} (hT : σ gT = ⟨LT, ones Ps :: ones Pl :: ones w :: RT⟩)
    (hA : σ gA = ⟨[ones m], []⟩) :
    Runs entry σ (· = Function.update (Function.update σ gT ⟨ones w :: ones Pl :: ones Ps :: LT, RT⟩) gA
      ⟨[ones (accStep r Y m (Ps, Pl, w))], []⟩) (8 * n + 200 * r + 300) := by
  obtain ⟨h1, h2, h3, hS, hJ, hK3, hK4, -, -⟩ := hR
  have hlen : (bits n Y).length = n := length_bits n Y
  have s1 := runs_readBits (by rw [hlen]; exact hPs) (by rw [hlen]; exact hPl) σ hY hT h1 h2
  set σ₁ := Function.update (Function.update (Function.update σ gT ⟨ones Pl :: ones Ps :: LT, ones w :: RT⟩)
      gB1 ⟨[], [[(bits n Y).getD Ps false]]⟩) gB2 ⟨[], [[(bits n Y).getD Pl false]]⟩ with hσ₁
  have bs := getD_bits n Y Ps hPs
  have bl := getD_bits n Y Pl hPl
  have hT₁ : σ₁ gT = ⟨ones Pl :: ones Ps :: LT, ones w :: RT⟩ := by tsimp [hσ₁]
  have hA₁ : σ₁ gA = ⟨[ones m], []⟩ := by tsimp [hσ₁, hA]
  have hB1₁ : σ₁ gB1 = ⟨[], [[decide (bitAt Y Ps = 1)]]⟩ := by rw [hσ₁, ← bs]; tsimp
  have hB2₁ : σ₁ gB2 = ⟨[], [[decide (bitAt Y Pl = 1)]]⟩ := by rw [hσ₁, ← bl]; tsimp
  -- the clears at the end
  have hclear : ∀ τ : Fin 18 → WTape, Runs (.seq (clear (a := 0) gB1) (clear gB2)) τ
      (· = Function.update (Function.update τ gB1 emp) gB2 emp) (2 * clen (τ gB1).words + 2 * clen (τ gB2).words + 5) := by
    intro τ
    refine (Runs.then (runs_clear (a := 0) gB1 τ) (runs_clear (a := 0) gB2 _)).mono (fun τ' e => ?_) ?_
    · rw [e]; rfl
    · tsimp; omega
  have skipT : Runs (skp (a := 0) gT gJ (by decide)) σ₁ (· = Function.update σ₁ gT ⟨ones w :: ones Pl :: ones Ps :: LT, RT⟩)
      (w + 5) := by
    refine (runs_skp (a := 0) (show gT ≠ gJ by decide) σ₁ (by simp [hT₁]) (by tsimp [hσ₁, hJ, emp])).mono
      (fun τ e => ?_) (by simp [hT₁])
    rw [e, hT₁]; rfl
  by_cases hs : bitAt Y Ps = 1 <;> by_cases hl : bitAt Y Pl = 1
  · have s2 := runs_addWeight hr σ₁ hT₁ hA₁ (by tsimp [hσ₁, hK3]) (by tsimp [hσ₁, hK4]) (by tsimp [hσ₁, h3])
      (by tsimp [hσ₁, hS]) (by tsimp [hσ₁, hJ])
    have sc := Runs.cond_true (d := skp gT gJ (by decide))
      (by rw [hB1₁, startsOne_reg]; simpa using hs)
      (Runs.cond_true (d := skp gT gJ (by decide)) (by rw [hB2₁, startsOne_reg]; simpa using hl) s2)
    refine (Runs.then s1 (Runs.then sc (hclear _))).mono (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, hT, hA, h1, h2, accStep, entryVal, hs, hl]
    · tsimp [hσ₁, clen, WTape.words]; omega
  · have sc := Runs.cond_true (d := skp gT gJ (by decide))
      (by rw [hB1₁, startsOne_reg]; simpa using hs)
      (Runs.cond_false (c := addWeight) (by rw [hB2₁, startsOne_reg]; simpa using hl) skipT)
    refine (Runs.then s1 (Runs.then sc (hclear _))).mono (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl |
        tsimp [hσ₁, hT, hA, h1, h2, accStep, entryVal, hs, hl, Nat.not_lt.mpr (show m ≤ 4 * r - 1 by omega)]
    · tsimp [hσ₁, clen, WTape.words]; omega
  · have sc := Runs.cond_false (c := .cond gB2 addWeight (skp gT gJ (by decide)))
      (by rw [hB1₁, startsOne_reg]; simpa using hs) skipT
    refine (Runs.then s1 (Runs.then sc (hclear _))).mono (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl |
        tsimp [hσ₁, hT, hA, h1, h2, accStep, entryVal, hs, hl, Nat.not_lt.mpr (show m ≤ 4 * r - 1 by omega)]
    · tsimp [hσ₁, clen, WTape.words]; omega
  · have sc := Runs.cond_false (c := .cond gB2 addWeight (skp gT gJ (by decide)))
      (by rw [hB1₁, startsOne_reg]; simpa using hs) skipT
    refine (Runs.then s1 (Runs.then sc (hclear _))).mono (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl |
        tsimp [hσ₁, hT, hA, h1, h2, accStep, entryVal, hs, hl, Nat.not_lt.mpr (show m ≤ 4 * r - 1 by omega)]
    · tsimp [hσ₁, clen, WTape.words]; omega

/-- The table's words: three per entry. -/
def tableWords (es : List Entry) : List (List Bool) := es.flatMap fun e => [ones e.1, ones e.2.1, ones e.2.2]

/-- The entries fit the address width and the modulus. -/
def TableOK (r n : ℕ) (es : List Entry) : Prop := ∀ e ∈ es, e.1 < n ∧ e.2.1 < n ∧ e.2.2 ≤ 4 * r

theorem Ready_update_gT_gA {r : ℕ} {σ : Fin 18 → WTape} (h : Ready r σ) (T A : WTape) :
    Ready r (Function.update (Function.update σ gT T) gA A) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> tsimp [h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- `runs_entries`: the table loop sums the remaining entries into the accumulator, modulo `4r`. -/
theorem runs_entries {r n Y : ℕ} (hr : 1 ≤ r) :
    ∀ (es : List Entry) (σ : Fin 18 → WTape) (LT : List (List Bool)) (m : ℕ), TableOK r n es → m < 4 * r →
      Ready r σ → σ gY = reg (bits n Y) → σ gT = ⟨LT, tableWords es⟩ → σ gA = ⟨[ones m], []⟩ →
      Runs (.loop gT entry) σ (· = Function.update (Function.update σ gT ⟨(tableWords es).reverse ++ LT, []⟩) gA
        ⟨[ones (es.foldl (accStep r Y) m)], []⟩) (es.length * (8 * n + 200 * r + 302))
  | [], σ, LT, m, _, _, _, _, hT, hA => by
    refine (Runs.loop_done (by simp [hT, tableWords]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    funext i
    fin_cases i <;> first | rfl | tsimp [hT, hA, tableWords]
  | e :: es, σ, LT, m, hok, hm, hR, hY, hT, hA => by
    obtain ⟨hPs, hPl, hw⟩ := hok e (by simp)
    have hT' : σ gT = ⟨LT, ones e.1 :: ones e.2.1 :: ones e.2.2 :: tableWords es⟩ := by
      rw [hT]; simp [tableWords]
    have s1 := runs_entry hr hPs hPl hm hw σ hR hY hT' hA
    set σ₁ := Function.update (Function.update σ gT ⟨ones e.2.2 :: ones e.2.1 :: ones e.1 :: LT, tableWords es⟩)
      gA ⟨[ones (accStep r Y m (e.1, e.2.1, e.2.2))], []⟩ with hσ₁
    have hm₁ : accStep r Y m (e.1, e.2.1, e.2.2) < 4 * r := by
      have hv : entryVal Y (e.1, e.2.1, e.2.2) ≤ e.2.2 := entryVal_le _ _
      unfold accStep; split_ifs <;> omega
    have ih := runs_entries (r := r) (n := n) (Y := Y) hr es σ₁ (ones e.2.2 :: ones e.2.1 :: ones e.1 :: LT) _
      (fun f hf => hok f (by simp [hf])) hm₁ (Ready_update_gT_gA hR _ _) (by tsimp [hσ₁, hY])
      (by tsimp [hσ₁]) (by tsimp [hσ₁])
    refine (Runs.loop_step (by simp [hT']) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono (fun τ h => ?_) ?_
    · rw [h]
      funext i
      fin_cases i <;> first | rfl | tsimp [hσ₁, tableWords]
    · simp only [List.length_cons]; ring_nf; omega

/-! ### The record's descriptors -/

/-- Negate the sum: `gE` gets `4r - E` in doubled unary. -/
noncomputable def negate : Cmd 0 18 :=
  .seq (rewind gA) <| .seq (op1 Rules.drop false gK4 gA gE (by decide) (by decide) (by decide)) <|
  .seq (rewind gK4) (clear gA)

/-- Test whether the word on `s` is longer than the constant on `k`, into `gB3`. -/
noncomputable def test (s k : Fin 18) (h1 : s ≠ k) (h2 : s ≠ gB3) (h3 : k ≠ gB3) : Cmd 0 18 :=
  .seq (rewind s) <| .seq (op1 geq false s k gB3 h1 h2 h3) <| .seq (rewind k) (rewind gB3)

/-- Replace `4r` by zero. -/
noncomputable def zeroFix : Cmd 0 18 :=
  .seq (test gE gK3 (by decide) (by decide) (by decide)) <|
  .seq (.cond gB3 (.seq (clear gE) (emit [[]] gE)) (rewind gJ)) (clear gB3)

/-- At least `2r`: subtract it and record the flag. -/
noncomputable def hiBranch : Cmd 0 18 :=
  .seq (rewind gE) <| .seq (op1 Rules.drop false gE gH2 gS (by decide) (by decide) (by decide)) <|
  .seq (rewind gH2) <| .seq (clear gE) <| .seq (rewind gS) <| .seq (cpy gS gE (by decide)) <|
  .seq (clear gS) <| .seq (emit [[true]] gdF) (emit [[false]] gdG)

/-- Below `2r`: record the flag. -/
noncomputable def loBranch : Cmd 0 18 := .seq (emit [[false]] gdF) (emit [[true]] gdG)

/-- Split at `2r`. -/
noncomputable def splitE : Cmd 0 18 :=
  .seq (test gE gH1 (by decide) (by decide) (by decide)) <|
  .seq (.cond gB3 hiBranch loBranch) (clear gB3)

/-- Append the head and tail counts. -/
noncomputable def emitCounts : Cmd 0 18 :=
  .seq (rewind gE) <| .seq (cpy gE gdT (by decide)) <| .seq (rewind gE) <|
  .seq (op1 Rules.drop false gH2 gE gdH (by decide) (by decide) (by decide)) <| .seq (rewind gH2) (clear gE)

/-- Increment the address counter. -/
noncomputable def incY : Cmd 0 18 :=
  .seq (op0 inc false gY gS (by decide)) <| .seq (clear gY) <| .seq (rewind gS) <|
  .seq (cpy gS gY (by decide)) <| .seq (clear gS) (rewind gY)

set_option maxHeartbeats 4000000 in
theorem runs_negate {r E : ℕ} (σ : Fin 18 → WTape) (hA : σ gA = ⟨[ones E], []⟩)
    (hK4 : σ gK4 = reg (ones (4 * r))) (hE : σ gE = emp) :
    Runs negate σ (· = Function.update (Function.update σ gA emp) gE ⟨[ones (4 * r - E)], []⟩)
      (4 * E + 12 * r + 30) := by
  have t1 : time Rules.drop (ones (4 * r)) (fun _ => ones E) ≤ 4 * r + E + 6 :=
    (time_le Rules.drop (ones (4 * r)) (fun _ => ones E) E (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [negate, WP, wp_op1, wp_rewind, wp_clear]
  tsimp [hA, hK4, hE, emp, reg, Rules.output_drop]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hA, hK4, hE, emp, reg]
  · (try simp [clen, WTape.words]); omega

set_option maxHeartbeats 4000000 in
theorem runs_test {s k : Fin 18} (h1 : s ≠ k) (h2 : s ≠ gB3) (h3 : k ≠ gB3) {x : List Bool} {c : ℕ}
    (σ : Fin 18 → WTape) (hs : σ s = ⟨[x], []⟩) (hk : σ k = reg (ones c)) (hB3 : σ gB3 = emp) :
    Runs (test s k h1 h2 h3) σ (· = Function.update σ gB3 ⟨[], [[decide (c < x.length)]]⟩)
      (2 * x.length + 2 * c + 30) := by
  have t1 : time geq x (fun _ => ones c) ≤ x.length + c + 7 :=
    (time_le geq x (fun _ => ones c) c (fun _ => by simp)).trans (by simp)
  have hg := output_geq x c
  apply Runs.of_wp
  simp only [test, WP, wp_op1, wp_rewind]
  simp only [Function.update_apply, hs, hk, hB3, emp, reg, h1.symm, h2.symm, h3.symm,
    ↓reduceIte, WTape.next_mk, WTape.cur_mk, List.headD_cons, List.tail_cons, List.reverse_cons,
    List.reverse_nil, List.nil_append, ne_eq, not_false_eq_true, true_and, ↓parse_syms, WTape.put_false,
    List.cons_ne_nil, List.append_nil, hg]
  refine ⟨by simp, ?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [reg]
  · simp [clen, h3]; omega

set_option maxHeartbeats 4000000 in
theorem runs_zeroFix {r X : ℕ} (σ : Fin 18 → WTape) (hE : σ gE = ⟨[ones X], []⟩)
    (hK3 : σ gK3 = reg (ones (4 * r - 1))) (hB3 : σ gB3 = emp) (hJ : σ gJ = emp) :
    Runs zeroFix σ (· = Function.update σ gE ⟨[ones (if 4 * r - 1 < X then 0 else X)], []⟩)
      (6 * X + 8 * r + 60) := by
  have s1 := runs_test (show gE ≠ gK3 by decide) (show gE ≠ gB3 by decide) (show gK3 ≠ gB3 by decide) σ hE hK3 hB3
  simp only [length_ones] at s1
  set σ₁ := Function.update σ gB3 ⟨[], [[decide (4 * r - 1 < X)]]⟩ with hσ₁
  have hB3₁ : σ₁ gB3 = ⟨[], [[decide (4 * r - 1 < X)]]⟩ := by tsimp [hσ₁]
  by_cases hf : 4 * r - 1 < X
  · have s2 := Runs.then (runs_clear (a := 0) gE σ₁) (runs_emit (a := 0) [[]] gE _ (by simp))
    have sc := Runs.cond_true (d := rewind gJ) (by rw [hB3₁, startsOne_reg]; simpa using hf) s2
    refine (Runs.then s1 (Runs.then sc (runs_clear (a := 0) gB3 _))).mono (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, hf, hB3, hE, ones, emp]
    · tsimp [hσ₁, hE, clen, WTape.words]; omega
  · have sc := Runs.cond_false (c := .seq (clear gE) (emit [[]] gE)) (by rw [hB3₁, startsOne_reg]; simpa using hf)
      (runs_rewind (a := 0) gJ σ₁)
    refine (Runs.then s1 (Runs.then sc (runs_clear (a := 0) gB3 _))).mono (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl | tsimp [hσ₁, hf, hB3, hE, hJ, emp]
    · tsimp [hσ₁, hE, hJ, emp, clen, WTape.words]; omega

set_option maxHeartbeats 4000000 in
theorem runs_hiBranch {r X : ℕ} (σ : Fin 18 → WTape) (hE : σ gE = ⟨[ones X], []⟩)
    (hH2 : σ gH2 = reg (ones (2 * r))) (hS : σ gS = emp) {LF LG : List (List Bool)}
    (hF : σ gdF = ⟨LF, []⟩) (hG : σ gdG = ⟨LG, []⟩) :
    Runs hiBranch σ (· = Function.update (Function.update (Function.update σ gE ⟨[ones (X - 2 * r)], []⟩)
      gdF ⟨[true] :: LF, []⟩) gdG ⟨[false] :: LG, []⟩) (10 * X + 10 * r + 60) := by
  have t1 : time Rules.drop (ones X) (fun _ => ones (2 * r)) ≤ X + 2 * r + 6 :=
    (time_le Rules.drop (ones X) (fun _ => ones (2 * r)) (2 * r) (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [hiBranch, cpy, WP, wp_op1, wp_op0, wp_rewind, wp_clear, wp_emit]
  tsimp [hE, hH2, hS, hF, hG, emp, reg, Rules.output_drop, Rules.output_copy]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hE, hH2, hS, hF, hG, emp, reg]
  · have := Nat.sub_le X (2 * r)
    (try simp [clen, WTape.words, time_copy]); omega

theorem runs_loBranch (σ : Fin 18 → WTape) {LF LG : List (List Bool)}
    (hF : σ gdF = ⟨LF, []⟩) (hG : σ gdG = ⟨LG, []⟩) :
    Runs loBranch σ (· = Function.update (Function.update σ gdF ⟨[false] :: LF, []⟩) gdG ⟨[true] :: LG, []⟩) 10 := by
  apply Runs.of_wp
  simp only [loBranch, WP, wp_emit]
  tsimp [hF, hG, clen]

set_option maxHeartbeats 4000000 in
theorem runs_splitE {r X : ℕ} (σ : Fin 18 → WTape) (hE : σ gE = ⟨[ones X], []⟩)
    (hH1 : σ gH1 = reg (ones (2 * r - 1))) (hH2 : σ gH2 = reg (ones (2 * r))) (hB3 : σ gB3 = emp)
    (hS : σ gS = emp) {LF LG : List (List Bool)} (hF : σ gdF = ⟨LF, []⟩) (hG : σ gdG = ⟨LG, []⟩) :
    Runs splitE σ (· = Function.update (Function.update (Function.update σ gE ⟨[ones (splitRem r X)], []⟩)
      gdF ⟨[splitFlag r X] :: LF, []⟩) gdG ⟨[!splitFlag r X] :: LG, []⟩) (12 * X + 14 * r + 110) := by
  have s1 := runs_test (show gE ≠ gH1 by decide) (show gE ≠ gB3 by decide) (show gH1 ≠ gB3 by decide) σ hE hH1 hB3
  simp only [length_ones] at s1
  set σ₁ := Function.update σ gB3 ⟨[], [[decide (2 * r - 1 < X)]]⟩ with hσ₁
  have hB3₁ : σ₁ gB3 = ⟨[], [[decide (2 * r - 1 < X)]]⟩ := by tsimp [hσ₁]
  by_cases hf : 2 * r - 1 < X
  · have s2 := runs_hiBranch (r := r) (X := X) (LF := LF) (LG := LG) σ₁ (by tsimp [hσ₁, hE]) (by tsimp [hσ₁, hH2]) (by tsimp [hσ₁, hS])
      (by tsimp [hσ₁, hF]) (by tsimp [hσ₁, hG])
    have sc := Runs.cond_true (d := loBranch) (by rw [hB3₁, startsOne_reg]; simpa using hf) s2
    refine (Runs.then s1 (Runs.then sc (runs_clear (a := 0) gB3 _))).mono (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl |
        tsimp [hσ₁, hf, hB3, splitRem, splitFlag, emp]
    · tsimp [hσ₁, clen, WTape.words]; omega
  · have s2 := runs_loBranch (LF := LF) (LG := LG) σ₁ (by tsimp [hσ₁, hF]) (by tsimp [hσ₁, hG])
    have sc := Runs.cond_false (c := hiBranch) (by rw [hB3₁, startsOne_reg]; simpa using hf) s2
    refine (Runs.then s1 (Runs.then sc (runs_clear (a := 0) gB3 _))).mono (fun τ e => ?_) ?_
    · rw [e]; funext i; fin_cases i <;> first | rfl |
        tsimp [hσ₁, hf, hB3, hE, splitRem, splitFlag, emp]
    · tsimp [hσ₁, clen, WTape.words]; omega

set_option maxHeartbeats 4000000 in
theorem runs_emitCounts {r R : ℕ} (σ : Fin 18 → WTape) (hE : σ gE = ⟨[ones R], []⟩)
    (hH2 : σ gH2 = reg (ones (2 * r))) {LT LH : List (List Bool)} (hT : σ gdT = ⟨LT, []⟩)
    (hH : σ gdH = ⟨LH, []⟩) :
    Runs emitCounts σ (· = Function.update (Function.update (Function.update σ gE emp)
      gdT ⟨ones R :: LT, []⟩) gdH ⟨ones (2 * r - R) :: LH, []⟩) (6 * R + 6 * r + 40) := by
  have t1 : time Rules.drop (ones (2 * r)) (fun _ => ones R) ≤ 2 * r + R + 6 :=
    (time_le Rules.drop (ones (2 * r)) (fun _ => ones R) R (fun _ => by simp)).trans (by simp)
  apply Runs.of_wp
  simp only [emitCounts, cpy, WP, wp_op1, wp_op0, wp_rewind, wp_clear]
  tsimp [hE, hH2, hT, hH, emp, reg, Rules.output_drop, Rules.output_copy]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hE, hH2, hT, hH, emp, reg]
  · (try simp [clen, WTape.words, time_copy]); omega

set_option maxHeartbeats 4000000 in
theorem runs_incY {n Y : ℕ} (σ : Fin 18 → WTape) (hY : σ gY = reg (bits n Y)) (hS : σ gS = emp) :
    Runs incY σ (· = Function.update σ gY (reg (bits n (Y + 1)))) (10 * n + 40) := by
  have hi : incW true (bits n Y) = bits n (Y + 1) := by rw [incW_bits]; simp
  have t1 : time inc (bits n Y) (fun j => j.elim0) ≤ n + 6 :=
    (time_le inc (bits n Y) (fun j => j.elim0) 0 (fun j => j.elim0)).trans (by simp)
  apply Runs.of_wp
  simp only [incY, cpy, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hY, hS, emp, reg, output_inc, Rules.output_copy, hi]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> first | rfl | tsimp [hY, hS, emp, reg]
  · (try simp [clen, WTape.words, time_copy]); omega

/-- One record: sum the table, negate, split, append the four descriptor words, step the
address counter and consume one tick. -/
noncomputable def record : Cmd 0 18 :=
  .seq (emit [[]] gA) <| .seq (.loop gT entry) <| .seq (rewind gT) <| .seq negate <| .seq zeroFix <|
  .seq splitE <| .seq emitCounts <| .seq incY (skp gC gJ (by decide))

/-- The record's sum in doubled unary: the table value modulo `4r`. -/
def recSum (r Y : ℕ) (es : List Entry) : ℕ := es.foldl (accStep r Y) 0

theorem recSum_eq {r Y : ℕ} (hr : 1 ≤ r) {es : List Entry} (hw : ∀ e ∈ es, e.2.2 ≤ 4 * r) :
    recSum r Y es = tableVal Y es % (4 * r) := by
  rw [recSum, foldl_accStep hr es hw 0 (by omega), zero_add]

theorem clen_tableWords (es : List Entry) :
    clen (tableWords es) = (es.map fun e => e.1 + e.2.1 + e.2.2 + 3).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [tableWords, List.flatMap_cons, clen, List.map_append, List.sum_append] at ih ⊢
    rw [ih]; simp; ring

theorem clen_eq_sum (ws : List (List Bool)) : clen ws = (ws.map List.length).sum + ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [clen, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢; omega

theorem clen_tableWords_le {r n : ℕ} {es : List Entry} (hok : TableOK r n es) :
    clen (tableWords es) ≤ es.length * (2 * n + 4 * r + 3) := by
  rw [clen_tableWords]
  calc (es.map fun e => e.1 + e.2.1 + e.2.2 + 3).sum ≤ (es.map fun _ => 2 * n + 4 * r + 3).sum :=
        List.sum_le_sum (fun e he => by
          obtain ⟨h1, h2, h3⟩ := hok e he; omega)
    _ = es.length * (2 * n + 4 * r + 3) := by simp

/-- The step bound of one record. -/
def recordCost (n r : ℕ) (es : List Entry) (c : List Bool) : ℕ :=
  es.length * (10 * n + 210 * r + 320) + 10 * n + 160 * r + c.length + 500

set_option maxHeartbeats 8000000 in
/-- `runs_record`: one record appends its four descriptor words of the negated, split sum. -/
theorem runs_record {r n Y : ℕ} (hr : 1 ≤ r) {es : List Entry} (hok : TableOK r n es)
    (σ : Fin 18 → WTape) (hR : Ready r σ) (hY : σ gY = reg (bits n Y)) (hT : σ gT = ⟨[], tableWords es⟩)
    (hA : σ gA = emp) (hE : σ gE = emp) {LC RC LH LT LF LG : List (List Bool)} {c : List Bool}
    (hC : σ gC = ⟨LC, c :: RC⟩) (hH : σ gdH = ⟨LH, []⟩) (hDT : σ gdT = ⟨LT, []⟩) (hF : σ gdF = ⟨LF, []⟩)
    (hG : σ gdG = ⟨LG, []⟩) :
    Runs record σ (· = Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update σ gY (reg (bits n (Y + 1)))) gC ⟨c :: LC, RC⟩)
      gdH ⟨ones (2 * r - splitRem r (negE r (recSum r Y es))) :: LH, []⟩)
      gdT ⟨ones (splitRem r (negE r (recSum r Y es))) :: LT, []⟩)
      gdF ⟨[splitFlag r (negE r (recSum r Y es))] :: LF, []⟩)
      gdG ⟨[!splitFlag r (negE r (recSum r Y es))] :: LG, []⟩) (recordCost n r es c) := by
  obtain ⟨h1, h2, h3, hS, hJ, hK3, hK4, hH1, hH2⟩ := hR
  have hw : ∀ e ∈ es, e.2.2 ≤ 4 * r := fun e he => (hok e he).2.2
  set E2 := recSum r Y es with hE2
  have hE2lt : E2 < 4 * r := by rw [hE2, recSum_eq hr hw]; exact Nat.mod_lt _ (by omega)
  set X := negE r E2 with hX
  have hXle : X ≤ 4 * r := by rw [hX, negE]; split_ifs <;> omega
  set f := splitFlag r X with hf
  set R := splitRem r X with hRdef
  have hRlt : R ≤ 4 * r := by rw [hRdef, splitRem]; split_ifs <;> omega
  -- the steps
  have s0 := runs_emit (a := 0) [[]] gA σ (by simp [hA, emp])
  set σ₀ := Function.update σ gA ⟨[[]].reverse ++ (σ gA).left, []⟩ with hσ₀
  have hR₀ : Ready r σ₀ := ⟨by tsimp [hσ₀, h1], by tsimp [hσ₀, h2], by tsimp [hσ₀, h3], by tsimp [hσ₀, hS],
    by tsimp [hσ₀, hJ], by tsimp [hσ₀, hK3], by tsimp [hσ₀, hK4], by tsimp [hσ₀, hH1], by tsimp [hσ₀, hH2]⟩
  have s1 := runs_entries (n := n) (Y := Y) hr es σ₀ [] 0 hok (by omega) hR₀ (by tsimp [hσ₀, hY])
    (by tsimp [hσ₀, hT]) (by tsimp [hσ₀, hA, emp, ones])
  set σ₁ := Function.update (Function.update σ₀ gT ⟨(tableWords es).reverse ++ [], []⟩) gA
    ⟨[ones (es.foldl (accStep r Y) 0)], []⟩ with hσ₁
  have s2 := runs_rewind (a := 0) gT σ₁
  set σ₂ := Function.update σ₁ gT ⟨[], (σ₁ gT).left.reverse ++ (σ₁ gT).right⟩ with hσ₂
  have s3 := runs_negate (r := r) (E := E2) σ₂ (by tsimp [hσ₂, hσ₁, hE2, recSum]) (by tsimp [hσ₂, hσ₁, hσ₀, hK4])
    (by tsimp [hσ₂, hσ₁, hσ₀, hE])
  set σ₃ := Function.update (Function.update σ₂ gA emp) gE ⟨[ones (4 * r - E2)], []⟩ with hσ₃
  have s4 := runs_zeroFix (r := r) (X := 4 * r - E2) σ₃ (by tsimp [hσ₃]) (by tsimp [hσ₃, hσ₂, hσ₁, hσ₀, hK3])
    (by tsimp [hσ₃, hσ₂, hσ₁, hσ₀, h3]) (by tsimp [hσ₃, hσ₂, hσ₁, hσ₀, hJ])
  have hXdef : (if 4 * r - 1 < 4 * r - E2 then 0 else 4 * r - E2) = X := by rw [hX, negE]
  rw [hXdef] at s4
  set σ₄ := Function.update σ₃ gE ⟨[ones X], []⟩ with hσ₄
  have s5 := runs_splitE (r := r) (X := X) (LF := LF) (LG := LG) σ₄ (by tsimp [hσ₄])
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hH1]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hH2])
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, h3]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hS])
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hF]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hG])
  set σ₅ := Function.update (Function.update (Function.update σ₄ gE ⟨[ones R], []⟩) gdF ⟨[f] :: LF, []⟩)
    gdG ⟨[!f] :: LG, []⟩ with hσ₅
  have s6 := runs_emitCounts (r := r) (R := R) (LT := LT) (LH := LH) σ₅ (by tsimp [hσ₅])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hH2]) (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hDT])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hH])
  set σ₆ := Function.update (Function.update (Function.update σ₅ gE emp) gdT ⟨ones R :: LT, []⟩) gdH
    ⟨ones (2 * r - R) :: LH, []⟩ with hσ₆
  have s7 := runs_incY (n := n) (Y := Y) σ₆ (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hY])
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hS])
  set σ₇ := Function.update σ₆ gY (reg (bits n (Y + 1))) with hσ₇
  have s8 := runs_skp (a := 0) (show gC ≠ gJ by decide) σ₇ (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hC])
    (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hJ, emp])
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5
    (Runs.then s6 (Runs.then s7 s8)))))))).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> first | rfl |
      tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hA, hE, hT, hC, emp, ones]
  · have hcl := clen_tableWords_le hok
    have hcC : (σ₇ gC).cur.length = c.length := by
      tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ₀, hC]
    rw [hcC]
    rw [clen_eq_sum] at hcl
    tsimp [hσ₂, hσ₁, hσ₀, hA, emp, clen, WTape.words, recordCost]
    have hsub := Nat.sub_le (4 * r) E2
    have hL1 : es.length * (2 * n + 4 * r + 3) + es.length * (8 * n + 200 * r + 302) ≤
        es.length * (10 * n + 210 * r + 320) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    omega

/-- The descriptor program: one record per tick. -/
noncomputable def gen : Cmd 0 18 := .loop gC record

/-- The record's four descriptor words, from its sum. -/
def hdD (r S : ℕ) : List Bool := ones (2 * r - splitRem r (negE r S))
def tlD (r S : ℕ) : List Bool := ones (splitRem r (negE r S))
def hfD (r S : ℕ) : List Bool := [splitFlag r (negE r S)]
def tfD (r S : ℕ) : List Bool := [!splitFlag r (negE r S)]

/-- The descriptor words of records `Y, …, Y + k - 1`, last first. -/
def descRev (D : ℕ → List Bool) (Y : ℕ) (k : ℕ) : List (List Bool) := ((List.range k).map fun j => D (Y + j)).reverse

theorem descRev_succ (D : ℕ → List Bool) (Y k : ℕ) : descRev D Y (k + 1) = descRev D (Y + 1) k ++ [D Y] := by
  unfold descRev
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.reverse_cons]
  congr 3
  funext j; simp; ring_nf

/-- A second descriptor update overwrites all six fields from the first one.
Keep this calculation abstract so recursive proofs do not reduce descriptor words. -/
private theorem descriptor_updates_overwrite (σ : Fin 18 → WTape)
    (y c h t f g y' c' h' t' f' g' : WTape) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update σ gY y) gC c) gdH h) gdT t) gdF f) gdG g)
        gY y') gC c') gdH h') gdT t') gdF f') gdG g' =
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update σ gY y') gC c') gdH h') gdT t') gdF f') gdG g' := by
  funext i
  fin_cases i <;> rfl

set_option maxHeartbeats 8000000 in
/-- `runs_gen`: over `k` ticks the program appends the descriptor words of records
`Y, …, Y + k - 1`. -/
theorem runs_gen {r n : ℕ} (hr : 1 ≤ r) {es : List Entry} (hok : TableOK r n es) :
    ∀ (k : ℕ) (σ : Fin 18 → WTape) (Y : ℕ) {LC LH LT LF LG : List (List Bool)},
      Ready r σ → σ gY = reg (bits n Y) → σ gT = ⟨[], tableWords es⟩ → σ gA = emp → σ gE = emp →
      σ gC = ⟨LC, List.replicate k []⟩ → σ gdH = ⟨LH, []⟩ → σ gdT = ⟨LT, []⟩ → σ gdF = ⟨LF, []⟩ →
      σ gdG = ⟨LG, []⟩ →
      Runs gen σ (· = Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update σ gY (reg (bits n (Y + k)))) gC ⟨List.replicate k [] ++ LC, []⟩)
        gdH ⟨descRev (fun y => hdD r (recSum r y es)) Y k ++ LH, []⟩)
        gdT ⟨descRev (fun y => tlD r (recSum r y es)) Y k ++ LT, []⟩)
        gdF ⟨descRev (fun y => hfD r (recSum r y es)) Y k ++ LF, []⟩)
        gdG ⟨descRev (fun y => tfD r (recSum r y es)) Y k ++ LG, []⟩) (k * (recordCost n r es [] + 2))
  | 0, σ, Y, LC, LH, LT, LF, LG, _, hY, _, _, _, hC, hH, hDT, hF, hG => by
    refine (Runs.loop_done (by simp [hC]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    simp only [Nat.add_zero, descRev, List.range_zero, List.map_nil, List.reverse_nil,
      List.replicate_zero, List.nil_append]
    simp only [List.replicate_zero] at hC
    rw [← hY, ← hC, ← hH, ← hDT, ← hF, ← hG]
    simp only [Function.update_eq_self]
  | k + 1, σ, Y, LC, LH, LT, LF, LG, hR, hY, hT, hA, hE, hC, hH, hDT, hF, hG => by
    have hC' : σ gC = ⟨LC, [] :: List.replicate k []⟩ := by rw [hC]; rfl
    have s1 := runs_record hr hok σ hR hY hT hA hE hC' hH hDT hF hG
    obtain ⟨h1, h2, h3, hS, hJ, hK3, hK4, hH1, hH2⟩ := hR
    set σ₁ := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update σ gY (reg (bits n (Y + 1)))) gC ⟨[] :: LC, List.replicate k []⟩)
      gdH ⟨ones (2 * r - splitRem r (negE r (recSum r Y es))) :: LH, []⟩)
      gdT ⟨ones (splitRem r (negE r (recSum r Y es))) :: LT, []⟩)
      gdF ⟨[splitFlag r (negE r (recSum r Y es))] :: LF, []⟩)
      gdG ⟨[!splitFlag r (negE r (recSum r Y es))] :: LG, []⟩ with hσ₁
    have hR₁ : Ready r σ₁ := ⟨by tsimp [hσ₁, h1], by tsimp [hσ₁, h2], by tsimp [hσ₁, h3], by tsimp [hσ₁, hS],
      by tsimp [hσ₁, hJ], by tsimp [hσ₁, hK3], by tsimp [hσ₁, hK4], by tsimp [hσ₁, hH1], by tsimp [hσ₁, hH2]⟩
    have ih := runs_gen hr hok k σ₁ (Y + 1) (LC := [] :: LC)
      (LH := ones (2 * r - splitRem r (negE r (recSum r Y es))) :: LH)
      (LT := ones (splitRem r (negE r (recSum r Y es))) :: LT)
      (LF := [splitFlag r (negE r (recSum r Y es))] :: LF)
      (LG := [!splitFlag r (negE r (recSum r Y es))] :: LG) hR₁ (by tsimp [hσ₁]) (by tsimp [hσ₁, hT]) (by tsimp [hσ₁, hA])
      (by tsimp [hσ₁, hE]) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁])
    refine (Runs.loop_step (by simp [hC']) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]
      simp only [hσ₁, descriptor_updates_overwrite, descRev_succ, hdD, tlD, hfD, tfD,
        List.replicate_succ', add_assoc, add_comm 1 k, List.append_assoc, List.singleton_append]
    · simp only [recordCost]; ring_nf; omega

/-! ### The slot round's descriptors -/

theorem slotTable_ok {n : ℕ} (π : BitPerm n) (r : ℕ) (ts Is : List ℕ) (h : ℕ)
    (hpos : ∀ i ∈ Is, axOff ts i + h < n) : TableOK r n (slotTable π r ts Is h) := by
  intro e he
  simp only [slotTable, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨i, hi, h', hh', rfl⟩ := he
  have hih := hpos i hi
  refine ⟨π.σ_lt _ hih, π.σ_lt _ (by omega), ?_⟩
  have h1 : 2 * r / 2 ^ (h + 1) * 2 ^ h' ≤ 2 * r / 2 ^ (h + 1) * 2 ^ (h + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 := Nat.div_mul_le_self (2 * r) (2 ^ (h + 1))
  show 2 * (2 * r / 2 ^ (h + 1) * 2 ^ h') ≤ 4 * r
  omega

theorem desc_slot {n : ℕ} (π : BitPerm n) {r : ℕ} (hr : 1 ≤ r) (ts Is : List ℕ) (h : ℕ)
    (hpos : ∀ i ∈ Is, axOff ts i + h < n) (y : ℕ) :
    let S := recSum r y (slotTable π r ts Is h)
    let E := TwistRound.twistExp r (slotExp π r ts Is h y)
    hdD r S = TwistArray.hdW r E ∧ tlD r S = TwistArray.tlW r E ∧ hfD r S = TwistArray.hfW r E ∧
      tfD r S = TwistArray.tfW r E := by
  intro S E
  have hw : ∀ e ∈ slotTable π r ts Is h, e.2.2 ≤ 4 * r := fun e he =>
    (slotTable_ok π r ts Is h hpos e he).2.2
  have hS : S = 2 * slotExp π r ts Is h y % (4 * r) := by
    show recSum r y _ = _
    rw [recSum_eq hr hw, tableVal_slotTable π r ts Is h hpos]
  obtain ⟨-, hrem, hhead, hflag⟩ := desc_math hr (slotExp π r ts Is h y)
  simp only [hdD, tlD, hfD, tfD, TwistArray.hdW, TwistArray.tlW, TwistArray.hfW, TwistArray.tfW, hS, hrem,
    hflag, E]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | (congr 1; omega)

set_option maxHeartbeats 8000000 in
/-- `runs_slotDescriptors`: from a zero address counter and one tick per record, the program writes
the four descriptor lists of the slot round's twist exponents `twistExp r (slotExp π r ts Is h y)`,
for the records `y < M` in order, within `M · (recordCost + 2)` steps. -/
theorem runs_slotDescriptors {n : ℕ} (π : BitPerm n) {r : ℕ} (hr : 1 ≤ r) (ts Is : List ℕ) (h : ℕ)
    (hpos : ∀ i ∈ Is, axOff ts i + h < n) (M : ℕ) (σ : Fin 18 → WTape) (hR : Ready r σ)
    (hY : σ gY = reg (bits n 0)) (hT : σ gT = ⟨[], tableWords (slotTable π r ts Is h)⟩) (hA : σ gA = emp)
    (hE : σ gE = emp) (hC : σ gC = ⟨[], List.replicate M []⟩) (hH : σ gdH = emp) (hDT : σ gdT = emp)
    (hF : σ gdF = emp) (hG : σ gdG = emp) :
    Runs gen σ (fun σ' =>
      σ' gdH = ⟨((List.range M).map fun y => TwistArray.hdW r (TwistRound.twistExp r (slotExp π r ts Is h y))).reverse, []⟩ ∧
      σ' gdT = ⟨((List.range M).map fun y => TwistArray.tlW r (TwistRound.twistExp r (slotExp π r ts Is h y))).reverse, []⟩ ∧
      σ' gdF = ⟨((List.range M).map fun y => TwistArray.hfW r (TwistRound.twistExp r (slotExp π r ts Is h y))).reverse, []⟩ ∧
      σ' gdG = ⟨((List.range M).map fun y => TwistArray.tfW r (TwistRound.twistExp r (slotExp π r ts Is h y))).reverse, []⟩)
      (M * (recordCost n r (slotTable π r ts Is h) [] + 2)) := by
  have hok := slotTable_ok π r ts Is h hpos
  have s := runs_gen (LH := []) (LT := []) (LF := []) (LG := []) hr hok M σ 0 hR hY hT hA hE hC hH hDT hF hG
  refine s.mono (fun τ e => ?_) le_rfl
  have hD : ∀ (D : ℕ → List Bool) (D' : ℕ → List Bool), (∀ y, D y = D' y) →
      descRev D 0 M = ((List.range M).map D').reverse := by
    intro D D' hDD
    simp only [descRev, zero_add]
    congr 1; exact List.map_congr_left (fun y _ => hDD y)
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> tsimp
  · exact hD _ _ (fun y => (desc_slot π hr ts Is h hpos y).1)
  · exact hD _ _ (fun y => (desc_slot π hr ts Is h hpos y).2.1)
  · exact hD _ _ (fun y => (desc_slot π hr ts Is h hpos y).2.2.1)
  · exact hD _ _ (fun y => (desc_slot π hr ts Is h hpos y).2.2.2)

/-! ### The slot round's twist on tapes -/

/-- The descriptor program's tapes inside the twist bank: its four descriptor lists are the
monomial's descriptor tapes, its other tapes are fresh. -/
def φ (i : Fin 18) : Fin 29 :=
  if h : i.val < 14 then ⟨15 + i.val, by omega⟩ else ⟨i.val - 3, by have := i.isLt; omega⟩

theorem φ_injective : Function.Injective φ := by
  intro i j hij
  have := congrArg Fin.val hij
  unfold φ at this
  split_ifs at this <;> simp at this <;> ext <;> omega

/-- The monomial's tapes inside the twist bank. -/
def ψ : Fin 15 → Fin 29 := Fin.castLE (by norm_num)

theorem ψ_injective : Function.Injective ψ := Fin.castLE_injective _

/-- Write the round's descriptors, rewind them, and twist every record. -/
noncomputable def slotTwist : Cmd 0 29 :=
  .seq (gen.map φ φ_injective) <|
  .seq (.seq (rewind 11) <| .seq (rewind 12) <| .seq (rewind 13) (rewind 14))
    (TwistArray.twistArray.map ψ ψ_injective)

/-- The descriptor program's start: constants, a zero counter, the round's table, one tick per record. -/
def GenPre {n : ℕ} (π : BitPerm n) (r : ℕ) (ts Is : List ℕ) (h M : ℕ) (ρ : Fin 18 → WTape) : Prop :=
  Ready r ρ ∧ ρ gY = reg (bits n 0) ∧ ρ gT = ⟨[], tableWords (slotTable π r ts Is h)⟩ ∧ ρ gA = emp ∧
    ρ gE = emp ∧ ρ gC = ⟨[], List.replicate M []⟩ ∧ ρ gdH = emp ∧ ρ gdT = emp ∧ ρ gdF = emp ∧ ρ gdG = emp

theorem clen_map_le {α : Type*} (l : List α) (g : α → List Bool) (c : ℕ) (hg : ∀ a ∈ l, (g a).length ≤ c) :
    clen (l.map g) ≤ l.length * (c + 1) := by
  rw [clen_eq_sum, List.length_map, List.map_map]
  have : (l.map (List.length ∘ g)).sum ≤ (l.map fun _ => c).sum :=
    List.sum_le_sum (fun a ha => hg a ha)
  simp at this; nlinarith [this]

set_option maxHeartbeats 16000000 in
/-- `runs_slotTwist`: one fixed program writes the slot round's twist descriptors and applies the
round's twist `y^(-slotExp y)` to every record of the array. -/
theorem runs_slotTwist {n : ℕ} (π : BitPerm n) {r : ℕ} [NeZero r] (ts Is : List ℕ) (h : ℕ)
    (hpos : ∀ i ∈ Is, axOff ts i + h < n) (p w : ℕ) (fs : List (Rec r)) (σ : Fin 29 → WTape)
    (hgen : GenPre π r ts Is h fs.length (σ ∘ φ)) (hI : TwistArray.Idle r (σ ∘ ψ))
    {Lx R D : List (List Bool)} (hX : σ 0 = ⟨Lx, TwistArray.arrWords w fs ++ R⟩) (hO : σ 1 = ⟨D, []⟩) :
    arrayVec p (TwistRound.twistRecs (slotExp π r ts Is h) fs) = twist (slotExp π r ts Is h) (arrayVec p fs) ∧
    Runs slotTwist σ
      (fun σ' => σ' 1 = ⟨(TwistArray.arrWords w (TwistRound.twistRecs (slotExp π r ts Is h) fs)).reverse ++ D, []⟩)
      (fs.length * (recordCost n r (slotTable π r ts Is h) [] + 2) + 1 +
        (fs.length * (4 * r + 6) + 20 + fs.length * (2 * r * (25 * w + 200) + 50 * r + 402))) := by
  have hr : 1 ≤ r := NeZero.one_le
  refine ⟨TwistRound.arrayVec_twist p _ fs, ?_⟩
  obtain ⟨hR, hY, hT, hA, hE, hC, hH, hDT, hF, hG⟩ := hgen
  set f := slotExp π r ts Is h
  set M := fs.length
  obtain ⟨LH, hLH⟩ : ∃ L, L = (List.range M).map fun y => TwistArray.hdW r (TwistRound.twistExp r (f y)) :=
    ⟨_, rfl⟩
  obtain ⟨LT, hLT⟩ : ∃ L, L = (List.range M).map fun y => TwistArray.tlW r (TwistRound.twistExp r (f y)) :=
    ⟨_, rfl⟩
  obtain ⟨LF, hLF⟩ : ∃ L, L = (List.range M).map fun y => TwistArray.hfW r (TwistRound.twistExp r (f y)) :=
    ⟨_, rfl⟩
  obtain ⟨LG, hLG⟩ : ∃ L, L = (List.range M).map fun y => TwistArray.tfW r (TwistRound.twistExp r (f y)) :=
    ⟨_, rfl⟩
  have s1 := (runs_slotDescriptors π hr ts Is h hpos M (σ ∘ φ) hR hY hT hA hE hC hH hDT hF hG).map φ φ_injective σ rfl
  apply Runs.seq
  refine s1.mono (fun τ hτ => ?_) le_rfl
  obtain ⟨⟨eH, eT, eF, eG⟩, hout⟩ := hτ
  have k11 : τ 11 = ⟨LH.reverse, []⟩ := by rw [hLH]; exact eH
  have k12 : τ 12 = ⟨LT.reverse, []⟩ := by rw [hLT]; exact eT
  have k13 : τ 13 = ⟨LF.reverse, []⟩ := by rw [hLF]; exact eF
  have k14 : τ 14 = ⟨LG.reverse, []⟩ := by rw [hLG]; exact eG
  have klow : ∀ x : Fin 29, x.val < 11 → τ x = σ x := fun x hx => hout x (fun y e => by
    have := congrArg Fin.val e; unfold φ at this; split_ifs at this <;> simp at this <;> omega)
  -- the rewinds
  set τ₄ := Function.update (Function.update (Function.update (Function.update τ 11 ⟨[], LH⟩) 12 ⟨[], LT⟩)
    13 ⟨[], LF⟩) 14 ⟨[], LG⟩ with hτ₄
  have sR : Runs (Cmd.seq (rewind (a := 0) (11 : Fin 29)) <| .seq (rewind 12) <| .seq (rewind 13) (rewind 14)) τ
      (· = τ₄) (M * (4 * r + 6) + 16) := by
    apply Runs.of_wp
    simp only [WP, wp_rewind]
    tsimp [k11, k12, k13, k14]
    refine ⟨?_, ?_⟩
    · rw [hτ₄]
    · have c1 : clen LH.reverse ≤ M * (2 * r + 1) := by
        rw [clen_eq_sum, List.map_reverse, List.sum_reverse, List.length_reverse, ← clen_eq_sum]
        rw [hLH]
        exact (clen_map_le _ _ (2 * r) (fun y _ => by simp [TwistArray.hdW])).trans (by simp [M])
      have c2 : clen LT.reverse ≤ M * (2 * r + 1) := by
        rw [clen_eq_sum, List.map_reverse, List.sum_reverse, List.length_reverse, ← clen_eq_sum]
        rw [hLT]
        exact (clen_map_le _ _ (2 * r) (fun y _ => by
          simp [TwistArray.tlW]; have := Nat.mod_lt (TwistRound.twistExp r (f y)) (show 0 < r by omega); omega)).trans
          (by simp [M])
      have c3 : clen LF.reverse ≤ M * (1 + 1) := by
        rw [clen_eq_sum, List.map_reverse, List.sum_reverse, List.length_reverse, ← clen_eq_sum]
        rw [hLF]
        exact (clen_map_le _ _ 1 (fun y _ => by simp [TwistArray.hfW])).trans (by simp [M])
      have c4 : clen LG.reverse ≤ M * (1 + 1) := by
        rw [clen_eq_sum, List.map_reverse, List.sum_reverse, List.length_reverse, ← clen_eq_sum]
        rw [hLG]
        exact (clen_map_le _ _ 1 (fun y _ => by simp [TwistArray.tfW])).trans (by simp [M])
      have : M * (2 * r + 1) + M * (2 * r + 1) + M * (1 + 1) + M * (1 + 1) = M * (4 * r + 6) := by ring
      omega
  -- the monomial
  have hτψ : ∀ x : Fin 15, x.val < 11 → (τ₄ ∘ ψ) x = (σ ∘ ψ) x := fun x hx => by
    simp only [Function.comp_apply, hτ₄, ψ]
    rw [Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega)]
    exact klow _ (by simp; omega)
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ := hI
  have hI₄ : TwistArray.Idle r (τ₄ ∘ ψ) := ⟨(hτψ 3 (by decide)).trans i1, (hτψ 2 (by decide)).trans i2,
    (hτψ 4 (by decide)).trans i3, (hτψ 5 (by decide)).trans i4, (hτψ 6 (by decide)).trans i5,
    (hτψ 7 (by decide)).trans i6, (hτψ 8 (by decide)).trans i7, (hτψ 9 (by decide)).trans i8,
    (hτψ 10 (by decide)).trans i9⟩
  set ps : List (ℕ × Rec r) := fs.mapIdx fun y g => (TwistRound.twistExp r (f y), g)
  have hsnd : ps.map Prod.snd = fs := by
    apply List.ext_getElem (by simp [ps]); intro k h1 h2; simp [ps]
  have hdesc : ∀ (q : ℕ → List Bool), ps.map (fun p => q p.1) =
      (List.range M).map fun y => q (TwistRound.twistExp r (f y)) := by
    intro q; apply List.ext_getElem (by simp [ps, M]); intro k h1 h2; simp [ps]
  have htw : ps.map (fun p => twistRec p.1 p.2) = TwistRound.twistRecs f fs := by
    apply List.ext_getElem (by simp [ps, TwistRound.twistRecs]); intro k h1 h2; simp [ps, TwistRound.twistRecs]
  have s3 := TwistArray.runs_twistArray w ps (τ₄ ∘ ψ) Lx R [] [] [] [] D hI₄
    (by rw [hsnd, hτψ 0 (by decide)]; exact hX) (by rw [hτψ 1 (by decide)]; exact hO)
    (by rw [hdesc, ← hLH]; show τ₄ 11 = _; rw [hτ₄]; tsimp)
    (by rw [hdesc, ← hLT]; show τ₄ 12 = _; rw [hτ₄]; tsimp)
    (by rw [hdesc, ← hLF]; show τ₄ 13 = _; rw [hτ₄]; tsimp)
    (by rw [hdesc, ← hLG]; show τ₄ 14 = _; rw [hτ₄]; tsimp)
  have s3' := s3.map ψ ψ_injective τ₄ rfl
  have hlen : ps.length = M := by simp [ps, M]
  rw [hlen] at s3'
  refine (Runs.then sR s3').mono (fun τ' hτ' => ?_) ?_
  · have := congrFun hτ'.1 1
    simp only [Function.comp_apply] at this
    rw [show ψ 1 = 1 from rfl] at this
    rw [this, htw]
    tsimp
  · omega


/-! ### The opposite round: the inverse monomial -/

/-- Move the sum to `gE` unchanged. -/
noncomputable def moveAE : Cmd 0 18 := .seq (rewind gA) <| .seq (cpy gA gE (by decide)) (clear gA)

set_option maxHeartbeats 4000000 in
theorem runs_moveAE {E : ℕ} (σ : Fin 18 → WTape) (hA : σ gA = ⟨[ones E], []⟩) (hE : σ gE = emp) :
    Runs moveAE σ (· = Function.update (Function.update σ gA emp) gE ⟨[ones E], []⟩) (4 * E + 20) := by
  apply Runs.of_wp
  simp only [moveAE, cpy, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hA, hE, emp, Rules.output_copy]
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> rfl
  · (try simp [clen, WTape.words, time_copy]); omega

/-- The opposite record's arithmetic yields the descriptors of `e mod 2r`. -/
theorem desc_mathOpp {r : ℕ} (hr : 1 ≤ r) (e : ℕ) :
    splitRem r (2 * e % (4 * r)) = 2 * (e % (2 * r) % r) ∧
      2 * r - splitRem r (2 * e % (4 * r)) = 2 * (r - e % (2 * r) % r) ∧
      splitFlag r (2 * e % (4 * r)) = decide (e % (2 * r) / r % 2 = 1) := by
  have h2r : 0 < 2 * r := by omega
  have hmod : 2 * e % (4 * r) = 2 * (e % (2 * r)) := by
    rw [show 4 * r = 2 * (2 * r) by ring, Nat.mul_mod_mul_left]
  rw [hmod]
  obtain ⟨T, hTdef⟩ : ∃ T, T = e % (2 * r) := ⟨_, rfl⟩
  rw [← hTdef]
  have hTlt : T < 2 * r := hTdef ▸ Nat.mod_lt _ h2r
  simp only [splitRem, splitFlag]
  refine ⟨?_, ?_, ?_⟩
  · by_cases hge : r ≤ T
    · have hflag : decide (2 * r - 1 < 2 * T) = true := by simp; omega
      simp only [hflag, ↓reduceIte]
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]; omega
    · have hflag : decide (2 * r - 1 < 2 * T) = false := by simp; omega
      simp only [hflag, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega)]
  · by_cases hge : r ≤ T
    · have hflag : decide (2 * r - 1 < 2 * T) = true := by simp; omega
      simp only [hflag, ↓reduceIte]
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]; omega
    · have hflag : decide (2 * r - 1 < 2 * T) = false := by simp; omega
      simp only [hflag, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (by omega)]; omega
  · by_cases hge : r ≤ T
    · have : T / r = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
      simp [this]; omega
    · have : T / r = 0 := Nat.div_eq_of_lt (by omega)
      simp [this]; omega

/-- One recordOpp: sum the table, negate, split, append the four descriptor words, step the
address counter and consume one tick. -/
noncomputable def recordOpp : Cmd 0 18 :=
  .seq (emit [[]] gA) <| .seq (.loop gT entry) <| .seq (rewind gT) <| .seq moveAE <|
  .seq splitE <| .seq emitCounts <| .seq incY (skp gC gJ (by decide))

set_option maxHeartbeats 8000000 in
/-- `runs_recordOpp`: one recordOpp appends its four descriptor words of the negated, split sum. -/
theorem runs_recordOpp {r n Y : ℕ} (hr : 1 ≤ r) {es : List Entry} (hok : TableOK r n es)
    (σ : Fin 18 → WTape) (hR : Ready r σ) (hY : σ gY = reg (bits n Y)) (hT : σ gT = ⟨[], tableWords es⟩)
    (hA : σ gA = emp) (hE : σ gE = emp) {LC RC LH LT LF LG : List (List Bool)} {c : List Bool}
    (hC : σ gC = ⟨LC, c :: RC⟩) (hH : σ gdH = ⟨LH, []⟩) (hDT : σ gdT = ⟨LT, []⟩) (hF : σ gdF = ⟨LF, []⟩)
    (hG : σ gdG = ⟨LG, []⟩) :
    Runs recordOpp σ (· = Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update σ gY (reg (bits n (Y + 1)))) gC ⟨c :: LC, RC⟩)
      gdH ⟨ones (2 * r - splitRem r (recSum r Y es)) :: LH, []⟩)
      gdT ⟨ones (splitRem r (recSum r Y es)) :: LT, []⟩)
      gdF ⟨[splitFlag r (recSum r Y es)] :: LF, []⟩)
      gdG ⟨[!splitFlag r (recSum r Y es)] :: LG, []⟩) (recordCost n r es c) := by
  obtain ⟨h1, h2, h3, hS, hJ, hK3, hK4, hH1, hH2⟩ := hR
  have hw : ∀ e ∈ es, e.2.2 ≤ 4 * r := fun e he => (hok e he).2.2
  set E2 := recSum r Y es with hE2
  have hE2lt : E2 < 4 * r := by rw [hE2, recSum_eq hr hw]; exact Nat.mod_lt _ (by omega)
  set X := E2 with hX
  have hXle : X ≤ 4 * r := by omega
  set f := splitFlag r X with hf
  set R := splitRem r X with hRdef
  have hRlt : R ≤ 4 * r := by rw [hRdef, splitRem]; split_ifs <;> omega
  -- the steps
  have s0 := runs_emit (a := 0) [[]] gA σ (by simp [hA, emp])
  set σ₀ := Function.update σ gA ⟨[[]].reverse ++ (σ gA).left, []⟩ with hσ₀
  have hR₀ : Ready r σ₀ := ⟨by tsimp [hσ₀, h1], by tsimp [hσ₀, h2], by tsimp [hσ₀, h3], by tsimp [hσ₀, hS],
    by tsimp [hσ₀, hJ], by tsimp [hσ₀, hK3], by tsimp [hσ₀, hK4], by tsimp [hσ₀, hH1], by tsimp [hσ₀, hH2]⟩
  have s1 := runs_entries (n := n) (Y := Y) hr es σ₀ [] 0 hok (by omega) hR₀ (by tsimp [hσ₀, hY])
    (by tsimp [hσ₀, hT]) (by tsimp [hσ₀, hA, emp, ones])
  set σ₁ := Function.update (Function.update σ₀ gT ⟨(tableWords es).reverse ++ [], []⟩) gA
    ⟨[ones (es.foldl (accStep r Y) 0)], []⟩ with hσ₁
  have s2 := runs_rewind (a := 0) gT σ₁
  set σ₂ := Function.update σ₁ gT ⟨[], (σ₁ gT).left.reverse ++ (σ₁ gT).right⟩ with hσ₂
  have s3 := runs_moveAE (E := E2) σ₂ (by tsimp [hσ₂, hσ₁, hE2, recSum]; rfl) (by tsimp [hσ₂, hσ₁, hσ₀, hE])
  set σ₄ := Function.update (Function.update σ₂ gA emp) gE ⟨[ones X], []⟩ with hσ₄
  have s5 := runs_splitE (r := r) (X := X) (LF := LF) (LG := LG) σ₄ (by tsimp [hσ₄])
    (by tsimp [hσ₄, hσ₂, hσ₁, hσ₀, hH1]) (by tsimp [hσ₄, hσ₂, hσ₁, hσ₀, hH2])
    (by tsimp [hσ₄, hσ₂, hσ₁, hσ₀, h3]) (by tsimp [hσ₄, hσ₂, hσ₁, hσ₀, hS])
    (by tsimp [hσ₄, hσ₂, hσ₁, hσ₀, hF]) (by tsimp [hσ₄, hσ₂, hσ₁, hσ₀, hG])
  set σ₅ := Function.update (Function.update (Function.update σ₄ gE ⟨[ones R], []⟩) gdF ⟨[f] :: LF, []⟩)
    gdG ⟨[!f] :: LG, []⟩ with hσ₅
  have s6 := runs_emitCounts (r := r) (R := R) (LT := LT) (LH := LH) σ₅ (by tsimp [hσ₅])
    (by tsimp [hσ₅, hσ₄, hσ₂, hσ₁, hσ₀, hH2]) (by tsimp [hσ₅, hσ₄, hσ₂, hσ₁, hσ₀, hDT])
    (by tsimp [hσ₅, hσ₄, hσ₂, hσ₁, hσ₀, hH])
  set σ₆ := Function.update (Function.update (Function.update σ₅ gE emp) gdT ⟨ones R :: LT, []⟩) gdH
    ⟨ones (2 * r - R) :: LH, []⟩ with hσ₆
  have s7 := runs_incY (n := n) (Y := Y) σ₆ (by tsimp [hσ₆, hσ₅, hσ₄, hσ₂, hσ₁, hσ₀, hY])
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₂, hσ₁, hσ₀, hS])
  set σ₇ := Function.update σ₆ gY (reg (bits n (Y + 1))) with hσ₇
  have s8 := runs_skp (a := 0) (show gC ≠ gJ by decide) σ₇ (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₂, hσ₁, hσ₀, hC])
    (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₂, hσ₁, hσ₀, hJ, emp])
  refine (Runs.then s0 (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s5
    (Runs.then s6 (Runs.then s7 s8))))))).mono (fun τ e => ?_) ?_
  · rw [e]; funext i; fin_cases i <;> first | rfl |
      tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₂, hσ₁, hσ₀, hA, hE, hT, hC, emp, ones]
  · have hcl := clen_tableWords_le hok
    have hcC : (σ₇ gC).cur.length = c.length := by
      tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₂, hσ₁, hσ₀, hC]
    rw [hcC]
    rw [clen_eq_sum] at hcl
    tsimp [hσ₂, hσ₁, hσ₀, hA, emp, clen, WTape.words, recordCost]
    have hsub := Nat.sub_le (4 * r) E2
    have hL1 : es.length * (2 * n + 4 * r + 3) + es.length * (8 * n + 200 * r + 302) ≤
        es.length * (10 * n + 210 * r + 320) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
    omega

/-- The descriptor program: one recordOpp per tick. -/
noncomputable def genOpp : Cmd 0 18 := .loop gC recordOpp

/-- The recordOpp's four descriptor words, from its sum. -/
def hdO (r S : ℕ) : List Bool := ones (2 * r - splitRem r S)
def tlO (r S : ℕ) : List Bool := ones (splitRem r S)
def hfO (r S : ℕ) : List Bool := [splitFlag r S]
def tfO (r S : ℕ) : List Bool := [!splitFlag r S]

set_option maxHeartbeats 8000000 in
/-- `runs_genOpp`: over `k` ticks the program appends the descriptor words of records
`Y, …, Y + k - 1`. -/
theorem runs_genOpp {r n : ℕ} (hr : 1 ≤ r) {es : List Entry} (hok : TableOK r n es) :
    ∀ (k : ℕ) (σ : Fin 18 → WTape) (Y : ℕ) {LC LH LT LF LG : List (List Bool)},
      Ready r σ → σ gY = reg (bits n Y) → σ gT = ⟨[], tableWords es⟩ → σ gA = emp → σ gE = emp →
      σ gC = ⟨LC, List.replicate k []⟩ → σ gdH = ⟨LH, []⟩ → σ gdT = ⟨LT, []⟩ → σ gdF = ⟨LF, []⟩ →
      σ gdG = ⟨LG, []⟩ →
      Runs genOpp σ (· = Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update σ gY (reg (bits n (Y + k)))) gC ⟨List.replicate k [] ++ LC, []⟩)
        gdH ⟨descRev (fun y => hdO r (recSum r y es)) Y k ++ LH, []⟩)
        gdT ⟨descRev (fun y => tlO r (recSum r y es)) Y k ++ LT, []⟩)
        gdF ⟨descRev (fun y => hfO r (recSum r y es)) Y k ++ LF, []⟩)
        gdG ⟨descRev (fun y => tfO r (recSum r y es)) Y k ++ LG, []⟩) (k * (recordCost n r es [] + 2))
  | 0, σ, Y, LC, LH, LT, LF, LG, _, hY, _, _, _, hC, hH, hDT, hF, hG => by
    refine (Runs.loop_done (by simp [hC]) rfl).mono (fun τ e => ?_) (by simp)
    subst e
    simp only [Nat.add_zero, descRev, List.range_zero, List.map_nil, List.reverse_nil,
      List.replicate_zero, List.nil_append]
    simp only [List.replicate_zero] at hC
    rw [← hY, ← hC, ← hH, ← hDT, ← hF, ← hG]
    simp only [Function.update_eq_self]
  | k + 1, σ, Y, LC, LH, LT, LF, LG, hR, hY, hT, hA, hE, hC, hH, hDT, hF, hG => by
    have hC' : σ gC = ⟨LC, [] :: List.replicate k []⟩ := by rw [hC]; rfl
    have s1 := runs_recordOpp hr hok σ hR hY hT hA hE hC' hH hDT hF hG
    obtain ⟨h1, h2, h3, hS, hJ, hK3, hK4, hH1, hH2⟩ := hR
    set σ₁ := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update σ gY (reg (bits n (Y + 1)))) gC ⟨[] :: LC, List.replicate k []⟩)
      gdH ⟨ones (2 * r - splitRem r (recSum r Y es)) :: LH, []⟩)
      gdT ⟨ones (splitRem r (recSum r Y es)) :: LT, []⟩)
      gdF ⟨[splitFlag r (recSum r Y es)] :: LF, []⟩)
      gdG ⟨[!splitFlag r (recSum r Y es)] :: LG, []⟩ with hσ₁
    have hR₁ : Ready r σ₁ := ⟨by tsimp [hσ₁, h1], by tsimp [hσ₁, h2], by tsimp [hσ₁, h3], by tsimp [hσ₁, hS],
      by tsimp [hσ₁, hJ], by tsimp [hσ₁, hK3], by tsimp [hσ₁, hK4], by tsimp [hσ₁, hH1], by tsimp [hσ₁, hH2]⟩
    have ih := runs_genOpp hr hok k σ₁ (Y + 1) (LC := [] :: LC)
      (LH := ones (2 * r - splitRem r (recSum r Y es)) :: LH)
      (LT := ones (splitRem r (recSum r Y es)) :: LT)
      (LF := [splitFlag r (recSum r Y es)] :: LF)
      (LG := [!splitFlag r (recSum r Y es)] :: LG) hR₁ (by tsimp [hσ₁]) (by tsimp [hσ₁, hT]) (by tsimp [hσ₁, hA])
      (by tsimp [hσ₁, hE]) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁])
    refine (Runs.loop_step (by simp [hC']) (s1.mono (fun τ h => by rw [h]; exact ih) le_rfl)).mono
      (fun τ h => ?_) ?_
    · rw [h]
      simp only [hσ₁, descriptor_updates_overwrite, descRev_succ, hdO, tlO, hfO, tfO,
        List.replicate_succ', add_assoc, add_comm 1 k, List.append_assoc, List.singleton_append]
    · simp only [recordCost]; ring_nf; omega

theorem desc_slotOpp {n : ℕ} (π : BitPerm n) {r : ℕ} (hr : 1 ≤ r) (ts Is : List ℕ) (h : ℕ)
    (hpos : ∀ i ∈ Is, axOff ts i + h < n) (y : ℕ) :
    let S := recSum r y (slotTable π r ts Is h)
    let E := slotExp π r ts Is h y % (2 * r)
    hdO r S = TwistArray.hdW r E ∧ tlO r S = TwistArray.tlW r E ∧ hfO r S = TwistArray.hfW r E ∧
      tfO r S = TwistArray.tfW r E := by
  intro S E
  have hw : ∀ e ∈ slotTable π r ts Is h, e.2.2 ≤ 4 * r := fun e he =>
    (slotTable_ok π r ts Is h hpos e he).2.2
  have hS : S = 2 * slotExp π r ts Is h y % (4 * r) := by
    show recSum r y _ = _
    rw [recSum_eq hr hw, tableVal_slotTable π r ts Is h hpos]
  obtain ⟨hrem, hhead, hflag⟩ := desc_mathOpp hr (slotExp π r ts Is h y)
  simp only [hdO, tlO, hfO, tfO, TwistArray.hdW, TwistArray.tlW, TwistArray.hfW, TwistArray.tfW, hS, hrem,
    hflag, E]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | (congr 1; omega)

set_option maxHeartbeats 8000000 in
/-- `runs_slotDescriptorsOpp`: from a zero address counter and one tick per recordOpp, the program writes
the four descriptor lists of the opposite round's exponents `slotExp π r ts Is h y % 2r`,
for the records `y < M` in order, within `M · (recordCost + 2)` steps. -/
theorem runs_slotDescriptorsOpp {n : ℕ} (π : BitPerm n) {r : ℕ} (hr : 1 ≤ r) (ts Is : List ℕ) (h : ℕ)
    (hpos : ∀ i ∈ Is, axOff ts i + h < n) (M : ℕ) (σ : Fin 18 → WTape) (hR : Ready r σ)
    (hY : σ gY = reg (bits n 0)) (hT : σ gT = ⟨[], tableWords (slotTable π r ts Is h)⟩) (hA : σ gA = emp)
    (hE : σ gE = emp) (hC : σ gC = ⟨[], List.replicate M []⟩) (hH : σ gdH = emp) (hDT : σ gdT = emp)
    (hF : σ gdF = emp) (hG : σ gdG = emp) :
    Runs genOpp σ (fun σ' =>
      σ' gdH = ⟨((List.range M).map fun y => TwistArray.hdW r (slotExp π r ts Is h y % (2 * r))).reverse, []⟩ ∧
      σ' gdT = ⟨((List.range M).map fun y => TwistArray.tlW r (slotExp π r ts Is h y % (2 * r))).reverse, []⟩ ∧
      σ' gdF = ⟨((List.range M).map fun y => TwistArray.hfW r (slotExp π r ts Is h y % (2 * r))).reverse, []⟩ ∧
      σ' gdG = ⟨((List.range M).map fun y => TwistArray.tfW r (slotExp π r ts Is h y % (2 * r))).reverse, []⟩)
      (M * (recordCost n r (slotTable π r ts Is h) [] + 2)) := by
  have hok := slotTable_ok π r ts Is h hpos
  have s := runs_genOpp (LH := []) (LT := []) (LF := []) (LG := []) hr hok M σ 0 hR hY hT hA hE hC hH hDT hF hG
  refine s.mono (fun τ e => ?_) le_rfl
  have hD : ∀ (D : ℕ → List Bool) (D' : ℕ → List Bool), (∀ y, D y = D' y) →
      descRev D 0 M = ((List.range M).map D').reverse := by
    intro D D' hDD
    simp only [descRev, zero_add]
    congr 1; exact List.map_congr_left (fun y _ => hDD y)
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> tsimp
  · exact hD _ _ (fun y => (desc_slotOpp π hr ts Is h hpos y).1)
  · exact hD _ _ (fun y => (desc_slotOpp π hr ts Is h hpos y).2.1)
  · exact hD _ _ (fun y => (desc_slotOpp π hr ts Is h hpos y).2.2.1)
  · exact hD _ _ (fun y => (desc_slotOpp π hr ts Is h hpos y).2.2.2)

/-- Write the opposite round's descriptors, rewind them, and multiply every record by its monomial. -/
noncomputable def slotUntwist : Cmd 0 29 :=
  .seq (genOpp.map φ φ_injective) <|
  .seq (.seq (rewind 11) <| .seq (rewind 12) <| .seq (rewind 13) (rewind 14))
    (TwistArray.twistArray.map ψ ψ_injective)

set_option maxHeartbeats 16000000 in
/-- `runs_slotUntwist`: one fixed program writes the opposite round's descriptors and multiplies every
record by the inverse monomial `y^(slotExp y)`. -/
theorem runs_slotUntwist {n : ℕ} (π : BitPerm n) {r : ℕ} [NeZero r] (ts Is : List ℕ) (h : ℕ)
    (hpos : ∀ i ∈ Is, axOff ts i + h < n) (p w : ℕ) (fs : List (Rec r)) (σ : Fin 29 → WTape)
    (hgen : GenPre π r ts Is h fs.length (σ ∘ φ)) (hI : TwistArray.Idle r (σ ∘ ψ))
    {Lx R D : List (List Bool)} (hX : σ 0 = ⟨Lx, TwistArray.arrWords w fs ++ R⟩) (hO : σ 1 = ⟨D, []⟩) :
    arrayVec p (TwistRound.untwistRecs (slotExp π r ts Is h) fs) = untwist (slotExp π r ts Is h) (arrayVec p fs) ∧
    Runs slotUntwist σ
      (fun σ' => σ' 1 = ⟨(TwistArray.arrWords w (TwistRound.untwistRecs (slotExp π r ts Is h) fs)).reverse ++ D, []⟩)
      (fs.length * (recordCost n r (slotTable π r ts Is h) [] + 2) + 1 +
        (fs.length * (4 * r + 6) + 20 + fs.length * (2 * r * (25 * w + 200) + 50 * r + 402))) := by
  have hr : 1 ≤ r := NeZero.one_le
  refine ⟨TwistRound.arrayVec_untwist p _ fs, ?_⟩
  obtain ⟨hR, hY, hT, hA, hE, hC, hH, hDT, hF, hG⟩ := hgen
  set f := slotExp π r ts Is h
  set M := fs.length
  obtain ⟨LH, hLH⟩ : ∃ L, L = (List.range M).map fun y => TwistArray.hdW r (f y % (2 * r)) :=
    ⟨_, rfl⟩
  obtain ⟨LT, hLT⟩ : ∃ L, L = (List.range M).map fun y => TwistArray.tlW r (f y % (2 * r)) :=
    ⟨_, rfl⟩
  obtain ⟨LF, hLF⟩ : ∃ L, L = (List.range M).map fun y => TwistArray.hfW r (f y % (2 * r)) :=
    ⟨_, rfl⟩
  obtain ⟨LG, hLG⟩ : ∃ L, L = (List.range M).map fun y => TwistArray.tfW r (f y % (2 * r)) :=
    ⟨_, rfl⟩
  have s1 := (runs_slotDescriptorsOpp π hr ts Is h hpos M (σ ∘ φ) hR hY hT hA hE hC hH hDT hF hG).map φ φ_injective σ rfl
  apply Runs.seq
  refine s1.mono (fun τ hτ => ?_) le_rfl
  obtain ⟨⟨eH, eT, eF, eG⟩, hout⟩ := hτ
  have k11 : τ 11 = ⟨LH.reverse, []⟩ := by rw [hLH]; exact eH
  have k12 : τ 12 = ⟨LT.reverse, []⟩ := by rw [hLT]; exact eT
  have k13 : τ 13 = ⟨LF.reverse, []⟩ := by rw [hLF]; exact eF
  have k14 : τ 14 = ⟨LG.reverse, []⟩ := by rw [hLG]; exact eG
  have klow : ∀ x : Fin 29, x.val < 11 → τ x = σ x := fun x hx => hout x (fun y e => by
    have := congrArg Fin.val e; unfold φ at this; split_ifs at this <;> simp at this <;> omega)
  -- the rewinds
  set τ₄ := Function.update (Function.update (Function.update (Function.update τ 11 ⟨[], LH⟩) 12 ⟨[], LT⟩)
    13 ⟨[], LF⟩) 14 ⟨[], LG⟩ with hτ₄
  have sR : Runs (Cmd.seq (rewind (a := 0) (11 : Fin 29)) <| .seq (rewind 12) <| .seq (rewind 13) (rewind 14)) τ
      (· = τ₄) (M * (4 * r + 6) + 16) := by
    apply Runs.of_wp
    simp only [WP, wp_rewind]
    tsimp [k11, k12, k13, k14]
    refine ⟨?_, ?_⟩
    · rw [hτ₄]
    · have c1 : clen LH.reverse ≤ M * (2 * r + 1) := by
        rw [clen_eq_sum, List.map_reverse, List.sum_reverse, List.length_reverse, ← clen_eq_sum]
        rw [hLH]
        exact (clen_map_le _ _ (2 * r) (fun y _ => by simp [TwistArray.hdW])).trans (by simp [M])
      have c2 : clen LT.reverse ≤ M * (2 * r + 1) := by
        rw [clen_eq_sum, List.map_reverse, List.sum_reverse, List.length_reverse, ← clen_eq_sum]
        rw [hLT]
        exact (clen_map_le _ _ (2 * r) (fun y _ => by
          simp [TwistArray.tlW]; have := Nat.mod_lt (f y % (2 * r)) (show 0 < r by omega)
          have := Nat.mod_lt (f y) (show 0 < r by omega); omega)).trans
          (by simp [M])
      have c3 : clen LF.reverse ≤ M * (1 + 1) := by
        rw [clen_eq_sum, List.map_reverse, List.sum_reverse, List.length_reverse, ← clen_eq_sum]
        rw [hLF]
        exact (clen_map_le _ _ 1 (fun y _ => by simp [TwistArray.hfW])).trans (by simp [M])
      have c4 : clen LG.reverse ≤ M * (1 + 1) := by
        rw [clen_eq_sum, List.map_reverse, List.sum_reverse, List.length_reverse, ← clen_eq_sum]
        rw [hLG]
        exact (clen_map_le _ _ 1 (fun y _ => by simp [TwistArray.tfW])).trans (by simp [M])
      have : M * (2 * r + 1) + M * (2 * r + 1) + M * (1 + 1) + M * (1 + 1) = M * (4 * r + 6) := by ring
      omega
  -- the monomial
  have hτψ : ∀ x : Fin 15, x.val < 11 → (τ₄ ∘ ψ) x = (σ ∘ ψ) x := fun x hx => by
    simp only [Function.comp_apply, hτ₄, ψ]
    rw [Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega),
      Function.update_of_ne (by intro e; have := congrArg Fin.val e; simp at this; omega)]
    exact klow _ (by simp; omega)
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ := hI
  have hI₄ : TwistArray.Idle r (τ₄ ∘ ψ) := ⟨(hτψ 3 (by decide)).trans i1, (hτψ 2 (by decide)).trans i2,
    (hτψ 4 (by decide)).trans i3, (hτψ 5 (by decide)).trans i4, (hτψ 6 (by decide)).trans i5,
    (hτψ 7 (by decide)).trans i6, (hτψ 8 (by decide)).trans i7, (hτψ 9 (by decide)).trans i8,
    (hτψ 10 (by decide)).trans i9⟩
  set ps : List (ℕ × Rec r) := fs.mapIdx fun y g => (f y % (2 * r), g)
  have hsnd : ps.map Prod.snd = fs := by
    apply List.ext_getElem (by simp [ps]); intro k h1 h2; simp [ps]
  have hdesc : ∀ (q : ℕ → List Bool), ps.map (fun p => q p.1) =
      (List.range M).map fun y => q (f y % (2 * r)) := by
    intro q; apply List.ext_getElem (by simp [ps, M]); intro k h1 h2; simp [ps]
  have htw : ps.map (fun p => twistRec p.1 p.2) = TwistRound.untwistRecs f fs := by
    apply List.ext_getElem (by simp [ps, TwistRound.untwistRecs]); intro k h1 h2; simp [ps, TwistRound.untwistRecs]
  have s3 := TwistArray.runs_twistArray w ps (τ₄ ∘ ψ) Lx R [] [] [] [] D hI₄
    (by rw [hsnd, hτψ 0 (by decide)]; exact hX) (by rw [hτψ 1 (by decide)]; exact hO)
    (by rw [hdesc, ← hLH]; show τ₄ 11 = _; rw [hτ₄]; tsimp)
    (by rw [hdesc, ← hLT]; show τ₄ 12 = _; rw [hτ₄]; tsimp)
    (by rw [hdesc, ← hLF]; show τ₄ 13 = _; rw [hτ₄]; tsimp)
    (by rw [hdesc, ← hLG]; show τ₄ 14 = _; rw [hτ₄]; tsimp)
  have s3' := s3.map ψ ψ_injective τ₄ rfl
  have hlen : ps.length = M := by simp [ps, M]
  rw [hlen] at s3'
  refine (Runs.then sR s3').mono (fun τ' hτ' => ?_) ?_
  · have := congrFun hτ'.1 1
    simp only [Function.comp_apply] at this
    rw [show ψ 1 = 1 from rfl] at this
    rw [this, htw]
    tsimp
  · omega

end TwistDescriptors

end IntegerMultBounds.Schoenhage
