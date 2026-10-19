module

public import IntegerMultBounds.MathlibTM2.M8.Local.Kernel
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Finset.Insert
public import Mathlib.Tactic.NormNum

/-!
# What the support checks mean

A support denotes a set of triples (`Supp.mem`): the triple itself, the triples `{x, y, z}` for
the third points `z` of `Z`, or the triples `{c, u, w}` for the pairs `{u, w}` of `P`
(`PairIn`). For a valid support (`Supp.Ok`):
* `relP c` gives its pair mask relative to a point `c` of all its triples (`relP_spec`), and
  `relZ x y` its third points relative to two (`relZ_spec`);
* a passed `supportOk` makes a support the disjoint union of two others (`supportOk_spec`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

open Nat

/-! ### Bits -/

theorem testB_eq (m k : ℕ) : testB m k = m.testBit k := by
  have h1 : Nat.land (Nat.shiftRight m k) 1 = (m >>> k) % 2 := Nat.and_one_is_mod _
  have h2 : m.testBit k = (1 &&& (m >>> k) != 0) := rfl
  rw [testB, h1, h2, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (m >>> k) with h | h <;> rw [h] <;> rfl

theorem testBit_bit (k i : ℕ) : (bit k).testBit i = decide (k = i) := by
  rw [bit, show Nat.shiftLeft 1 k = 1 <<< k from rfl, Nat.one_shiftLeft, testBit_two_pow]

theorem cond_ite {α : Type*} (b : Bool) (x y : α) : (bif b then x else y) = if b = true then x else y := by
  cases b <;> rfl

theorem blt_iff (a b : ℕ) : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem beq_iff (a b : ℕ) : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

/-! ### Pair bits -/

theorem pb_of_lt {u w : ℕ} (h : u < w) : pb u w = 23 * u + w := by
  simp [pb, h, Nat.add_eq, Nat.mul_eq]

theorem pb_comm (u w : ℕ) : pb u w = pb w u := by
  unfold pb
  simp only [cond_ite, blt_iff]
  split_ifs <;> simp_all [Nat.add_eq, Nat.mul_eq] <;> omega

/-- The pair of a bit. -/
theorem pb_inj {u w u' w' : ℕ} (h : u < w) (hw : w < 23) (h' : u' < w') (hw' : w' < 23)
    (he : pb u w = pb u' w') : u = u' ∧ w = w' := by
  rw [pb_of_lt h, pb_of_lt h'] at he
  omega

/-- The pair bits of the triples through `c`. -/
def PairIn (c P : ℕ) (S : Finset ℕ) : Prop :=
  ∃ u w, u < w ∧ w < 23 ∧ u ≠ c ∧ w ≠ c ∧ S = {c, u, w} ∧ P.testBit (pb u w) = true

/-- The pair of a triple through `c` is unique. -/
theorem triple_pair_unique {c u w u' w' : ℕ} (huw : u < w) (hu'w' : u' < w') (_hcu : u ≠ c)
    (_hcw : w ≠ c) (_hcu' : u' ≠ c) (_hcw' : w' ≠ c)
    (h : ({c, u, w} : Finset ℕ) = {c, u', w'}) : u = u' ∧ w = w' := by
  have hu : u ∈ ({c, u', w'} : Finset ℕ) := h ▸ by simp
  have hw : w ∈ ({c, u', w'} : Finset ℕ) := h ▸ by simp
  have hu' : u' ∈ ({c, u, w} : Finset ℕ) := h.symm ▸ by simp
  have hw' : w' ∈ ({c, u, w} : Finset ℕ) := h.symm ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw hu' hw'
  omega

theorem pairIn_bit {c p q : ℕ} {S : Finset ℕ} (hq : q < 23) (hcp : p ≠ c) (hcq : q ≠ c) (hpq : p < q) :
    PairIn c (bit (pb p q)) S ↔ S = {c, p, q} := by
  constructor
  · rintro ⟨u, w, huw, hw, hcu, hcw, rfl, hb⟩
    rw [testBit_bit, decide_eq_true_eq] at hb
    obtain ⟨rfl, rfl⟩ := pb_inj hpq hq huw hw hb
    rfl
  · rintro rfl
    exact ⟨p, q, hpq, hq, hcp, hcq, rfl, by rw [testBit_bit]; simp⟩

theorem pairIn_or {c A B : ℕ} {S : Finset ℕ} :
    PairIn c (Nat.lor A B) S ↔ PairIn c A S ∨ PairIn c B S := by
  constructor
  · rintro ⟨u, w, huw, hw, hcu, hcw, rfl, hb⟩
    rw [show Nat.lor A B = A ||| B from rfl, testBit_lor, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact Or.inl ⟨u, w, huw, hw, hcu, hcw, rfl, hb⟩
    · exact Or.inr ⟨u, w, huw, hw, hcu, hcw, rfl, hb⟩
  · rintro (⟨u, w, huw, hw, hcu, hcw, rfl, hb⟩ | ⟨u, w, huw, hw, hcu, hcw, rfl, hb⟩)
    · exact ⟨u, w, huw, hw, hcu, hcw, rfl, by
        rw [show Nat.lor A B = A ||| B from rfl, testBit_lor, hb, Bool.true_or]⟩
    · exact ⟨u, w, huw, hw, hcu, hcw, rfl, by
        rw [show Nat.lor A B = A ||| B from rfl, testBit_lor, hb, Bool.or_true]⟩

theorem pairIn_disjoint {c A B : ℕ} {S : Finset ℕ} (h : Nat.land A B = 0)
    (hA : PairIn c A S) (hB : PairIn c B S) : False := by
  obtain ⟨u, w, huw, hw, hcu, hcw, rfl, ha⟩ := hA
  obtain ⟨u', w', hu'w', hw', hcu', hcw', he, hb⟩ := hB
  obtain ⟨rfl, rfl⟩ := triple_pair_unique huw hu'w' hcu hcw hcu' hcw' he
  have := congrArg (fun n => n.testBit (pb u w)) h
  simp only [show Nat.land A B = A &&& B from rfl, testBit_land, ha, hb, Bool.and_self,
    zero_testBit] at this
  cases this

theorem disjUnion_spec {a b c : ℕ} (h : disjUnion a b c = true) : Nat.land a b = 0 ∧ Nat.lor a b = c := by
  simpa only [disjUnion, Bool.and_eq_true, beq_iff] using h

theorem subB_spec {S T : ℕ} (h : subB S T = true) (i : ℕ) (hi : S.testBit i = true) : T.testBit i = true := by
  have := congrArg (fun n => n.testBit i) ((beq_iff _ _).mp h)
  simp only [show Nat.land S T = S &&& T from rfl, testBit_land, hi, Bool.true_and] at this
  exact this

/-! ### Star masks -/

theorem testBit_starAux (o Z : ℕ) :
    ∀ k i, (starAux o Z k).testBit i = true ↔ ∃ z < k, Z.testBit z = true ∧ i = pb o z := by
  intro k
  induction k with
  | zero => intro i; simp [starAux]
  | succ k ih =>
    intro i
    show (Nat.lor (starAux o Z k) (bif testB Z k then bit (pb o k) else 0)).testBit i = true ↔ _
    rw [show ∀ a b : ℕ, Nat.lor a b = a ||| b from fun _ _ => rfl, testBit_lor, Bool.or_eq_true, ih,
      cond_ite, testB_eq]
    by_cases hz : Z.testBit k = true
    · rw [ite_eq_left hz, testBit_bit, decide_eq_true_eq]
      constructor
      · rintro (⟨z, hz', hb, rfl⟩ | h)
        · exact ⟨z, by omega, hb, rfl⟩
        · exact ⟨k, by omega, hz, h.symm⟩
      · rintro ⟨z, hz', hb, rfl⟩
        by_cases hzk : z < k
        · exact Or.inl ⟨z, hzk, hb, rfl⟩
        · exact Or.inr (by rw [show z = k by omega])
    · rw [ite_eq_right hz]
      simp only [zero_testBit, Bool.false_eq_true, or_false]
      constructor
      · rintro ⟨z, hz', hb, rfl⟩; exact ⟨z, by omega, hb, rfl⟩
      · rintro ⟨z, hz', hb, rfl⟩
        refine ⟨z, ?_, hb, rfl⟩
        by_contra hzk
        exact hz (by rw [show k = z by omega]; exact hb)

theorem testBit_starMask (o Z i : ℕ) :
    (starMask o Z).testBit i = true ↔ ∃ z < 23, Z.testBit z = true ∧ i = pb o z :=
  testBit_starAux o Z 23 i

/-- The two-point support relative to one of its points. -/
theorem pairIn_star {c o Z : ℕ} {S : Finset ℕ} (ho : o < 23) (hco : c ≠ o)
    (hZ : ∀ z, Z.testBit z = true → z < 23 ∧ z ≠ c ∧ z ≠ o) :
    PairIn c (starMask o Z) S ↔ ∃ z, z < 23 ∧ z ≠ c ∧ z ≠ o ∧ Z.testBit z = true ∧ S = {c, o, z} := by
  constructor
  · rintro ⟨u, w, huw, hw, hcu, hcw, rfl, hb⟩
    obtain ⟨z, _, hzb, he⟩ := (testBit_starMask o Z _).mp hb
    obtain ⟨hz23, hzc, hzo⟩ := hZ z hzb
    rcases lt_or_gt_of_ne hzo with h | h
    · rw [pb_comm o z] at he
      obtain ⟨rfl, rfl⟩ := pb_inj huw hw h ho he
      exact ⟨u, hz23, hzc, hzo, hzb, by rw [Finset.pair_comm]⟩
    · obtain ⟨rfl, rfl⟩ := pb_inj huw hw h hz23 he
      exact ⟨w, hz23, hzc, hzo, hzb, rfl⟩
  · rintro ⟨z, hz, hzc, hzo, hzb, rfl⟩
    have hb : (starMask o Z).testBit (pb o z) = true := (testBit_starMask o Z _).mpr ⟨z, hz, hzb, rfl⟩
    rcases lt_or_gt_of_ne hzo with h | h
    · exact ⟨z, o, h, ho, hzc, Ne.symm hco, by rw [Finset.pair_comm], by rw [pb_comm]; exact hb⟩
    · exact ⟨o, z, h, hz, Ne.symm hco, hzc, rfl, hb⟩

/-! ### Supports -/

/-- The triples of a support. -/
def Supp.mem : Supp → Finset ℕ → Prop
  | .three p0 p1 p2, S => S = {p0, p1, p2}
  | .two x y Z, S => ∃ z, z < 23 ∧ z ≠ x ∧ z ≠ y ∧ Z.testBit z = true ∧ S = {x, y, z}
  | .one c P, S => PairIn c P S

/-- A valid support. -/
def Supp.Ok : Supp → Prop
  | .three p0 p1 p2 => p0 < p1 ∧ p1 < p2 ∧ p2 < 23
  | .two x y Z => x < y ∧ y < 23 ∧ ∀ z, Z.testBit z = true → z < 23 ∧ z ≠ x ∧ z ≠ y
  | .one c P => c < 23 ∧ ∀ i, P.testBit i = true → ∃ u w, u < w ∧ w < 23 ∧ u ≠ c ∧ w ≠ c ∧ i = pb u w

private theorem validZ_small : ∀ x < 23, ∀ y < 23, x ≠ y → ∀ z < 23,
    (validZ x y).testBit z = decide (z ≠ x ∧ z ≠ y) := by
  decide +kernel

theorem validZ_lt {x y : ℕ} (hx : x < 23) (hy : y < 23) : validZ x y < 2 ^ 23 := by
  unfold validZ bit
  simp only [show ∀ a b : ℕ, Nat.xor a b = a ^^^ b from fun _ _ => rfl,
    show ∀ a b : ℕ, Nat.shiftLeft a b = a <<< b from fun _ _ => rfl]
  apply Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (by norm_num) _) <;>
    rw [Nat.one_shiftLeft] <;> exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem testBit_validZ {x y z : ℕ} (hx : x < 23) (hy : y < 23) (hxy : x ≠ y) :
    (validZ x y).testBit z = true ↔ z < 23 ∧ z ≠ x ∧ z ≠ y := by
  by_cases hz : z < 23
  · rw [validZ_small x hx y hy hxy z hz, decide_eq_true_eq]
    exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (validZ_lt hx hy)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [hz]

/-- A bit is a pair bit exactly when its row is below its column. -/
theorem isPairBit_iff (i : ℕ) :
    (∃ u w, u < w ∧ w < 23 ∧ i = pb u w) ↔ i < 529 ∧ i / 23 < i % 23 := by
  constructor
  · rintro ⟨u, w, huw, hw, rfl⟩
    rw [pb_of_lt huw]
    omega
  · rintro ⟨hi, hlt⟩
    refine ⟨i / 23, i % 23, hlt, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [pb_of_lt hlt]
    omega

theorem allPairs_lt : allPairs < 2 ^ 529 := by decide +kernel

private theorem allPairs_bits : ∀ i < 529, allPairs.testBit i = decide (i / 23 < i % 23) := by
  decide +kernel

theorem testBit_allPairs (i : ℕ) : allPairs.testBit i = true ↔ ∃ u w, u < w ∧ w < 23 ∧ i = pb u w := by
  rw [isPairBit_iff]
  by_cases hi : i < 529
  · rw [allPairs_bits i hi, decide_eq_true_eq]
    exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le allPairs_lt (Nat.pow_le_pow_right (by norm_num)
      (by omega)))]
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro h; omega

theorem testBit_touch {c : ℕ} (i : ℕ) :
    (touch c).testBit i = true ↔ ∃ z < 23, z ≠ c ∧ i = pb c z := by
  rw [touch, testBit_starMask]
  constructor
  · rintro ⟨z, hz, hb, rfl⟩
    refine ⟨z, hz, ?_, rfl⟩
    rintro rfl
    simp only [show ∀ a b : ℕ, Nat.xor a b = a ^^^ b from fun _ _ => rfl, testBit_xor, testBit_bit,
      decide_true, Bool.xor_true, Bool.not_eq_true'] at hb
    rw [show (0x7fffff : ℕ) = 2 ^ 23 - 1 by norm_num, testBit_two_pow_sub_one] at hb
    simp [hz] at hb
  · rintro ⟨z, hz, hzc, rfl⟩
    refine ⟨z, hz, ?_, rfl⟩
    simp only [show ∀ a b : ℕ, Nat.xor a b = a ^^^ b from fun _ _ => rfl, testBit_xor, testBit_bit,
      show (0x7fffff : ℕ) = 2 ^ 23 - 1 by norm_num, testBit_two_pow_sub_one, decide_eq_true hz,
      Bool.true_xor]
    simp [Ne.symm hzc]

/-- The bits of `pairsWithout c` are the pairs avoiding `c`. -/
theorem testBit_pairsWithout {c : ℕ} (hc : c < 23) (i : ℕ) :
    (pairsWithout c).testBit i = true ↔ ∃ u w, u < w ∧ w < 23 ∧ u ≠ c ∧ w ≠ c ∧ i = pb u w := by
  simp only [pairsWithout, show ∀ a b : ℕ, Nat.xor a b = a ^^^ b from fun _ _ => rfl,
    show ∀ a b : ℕ, Nat.land a b = a &&& b from fun _ _ => rfl, testBit_xor, testBit_land]
  cases ha : allPairs.testBit i <;> cases ht : (touch c).testBit i <;> simp only [Bool.and_true,
    Bool.and_false, Bool.xor_false, Bool.xor_self, Bool.false_eq_true, 
    false_iff, true_iff, not_exists, not_and]
  · intro u w huw hw _ _ he
    have := (testBit_allPairs i).mpr ⟨u, w, huw, hw, he⟩
    rw [ha] at this; cases this
  · intro u w huw hw _ _ he
    have := (testBit_allPairs i).mpr ⟨u, w, huw, hw, he⟩
    rw [ha] at this; cases this
  · obtain ⟨u, w, huw, hw, rfl⟩ := (testBit_allPairs i).mp ha
    refine ⟨u, w, huw, hw, ?_, ?_, rfl⟩
    · rintro rfl
      have := (testBit_touch (c := u) (pb u w)).mpr ⟨w, hw, by omega, rfl⟩
      rw [ht] at this; cases this
    · rintro rfl
      have := (testBit_touch (c := w) (pb u w)).mpr ⟨u, by omega, by omega, pb_comm u w⟩
      rw [ht] at this; cases this
  · intro u w huw hw hu hw' he
    obtain ⟨z, hz, hzc, he'⟩ := (testBit_touch i).mp ht
    rw [he] at he'
    rcases lt_or_gt_of_ne hzc with h | h
    · rw [pb_comm c z] at he'
      obtain ⟨rfl, rfl⟩ := pb_inj huw hw h (by omega) he'
      exact hw' rfl
    · obtain ⟨rfl, rfl⟩ := pb_inj huw hw h hz he'
      exact hu rfl

/-! ### The relative masks -/

theorem rot3 (a b c : ℕ) : ({a, b, c} : Finset ℕ) = {c, a, b} := by
  ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

theorem beq_cond {α : Type*} (a b : ℕ) (x y : α) : (bif Nat.beq a b then x else y) = if a = b then x else y := by
  by_cases h : a = b
  · subst h; simp
  · rw [ite_eq_right h, show Nat.beq a b = false from Bool.eq_false_iff.mpr fun h' => h ((beq_iff a b).mp h')]
    rfl

/-- **`relP`.** A valid support's triples relative to a point of all of them. -/
theorem relP_spec {c M : ℕ} {s : Supp} (hs : s.Ok) (hc : c < 23) (h : relP c s = some M) :
    ∀ S, s.mem S ↔ PairIn c M S := by
  intro S
  cases s with
  | three p0 p1 p2 =>
    obtain ⟨h01, h12, h2⟩ := hs
    simp only [relP, beq_cond] at h
    simp only [Supp.mem]
    split_ifs at h with e0 e1 e2
    · cases h; subst e0
      rw [pairIn_bit h2 (by omega) (by omega) h12]
    · cases h; subst e1
      rw [pairIn_bit h2 (by omega) (by omega) (by omega), Finset.insert_comm]
    · cases h; subst e2
      rw [pairIn_bit (by omega) (by omega) (by omega) h01, rot3]
  | two x y Z =>
    obtain ⟨hxy, hy, hZ⟩ := hs
    simp only [relP, beq_cond] at h
    simp only [Supp.mem]
    split_ifs at h with e0 e1
    · cases h; subst e0
      rw [pairIn_star hy (by omega) (fun z hz => hZ z hz)]
    · cases h; subst e1
      rw [pairIn_star (by omega) (by omega) (fun z hz => by have := hZ z hz; omega)]
      constructor
      · rintro ⟨z, hz, h1, h2, h3, rfl⟩; exact ⟨z, hz, h2, h1, h3, by rw [Finset.insert_comm]⟩
      · rintro ⟨z, hz, h1, h2, h3, rfl⟩; exact ⟨z, hz, h2, h1, h3, by rw [Finset.insert_comm]⟩
  | one c' P =>
    simp only [relP, beq_cond] at h
    split_ifs at h with e
    cases h; subst e
    rfl

/-- **`relZ`.** A valid support's triples relative to two points of all of them. -/
theorem relZ_spec {x y Z' : ℕ} {s : Supp} (hs : s.Ok) (h : relZ x y s = some Z') :
    ∀ S, s.mem S ↔ ∃ z, z < 23 ∧ z ≠ x ∧ z ≠ y ∧ Z'.testBit z = true ∧ S = {x, y, z} := by
  intro S
  have hone : ∀ p z, (bit p).testBit z = true ↔ z = p := by
    intro p z; rw [testBit_bit, decide_eq_true_eq, eq_comm]
  cases s with
  | three p0 p1 p2 =>
    obtain ⟨h01, h12, h2⟩ := hs
    simp only [relZ, Bool.cond_eq_ite, Bool.and_eq_true, beq_iff] at h
    simp only [Supp.mem]
    split_ifs at h with e0 e1 e2
    · cases h; obtain ⟨rfl, rfl⟩ := e0
      simp only [hone]
      constructor
      · rintro rfl; exact ⟨_, h2, by omega, by omega, rfl, rfl⟩
      · rintro ⟨z, _, _, _, rfl, rfl⟩; rfl
    · cases h; obtain ⟨rfl, rfl⟩ := e1
      simp only [hone]
      constructor
      · rintro rfl; exact ⟨_, by omega, by omega, by omega, rfl, by rw [Finset.pair_comm]⟩
      · rintro ⟨z, _, _, _, rfl, rfl⟩; rw [Finset.pair_comm]
    · cases h; obtain ⟨rfl, rfl⟩ := e2
      simp only [hone]
      constructor
      · rintro rfl
        exact ⟨_, by omega, by omega, by omega, rfl, by
          ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
      · rintro ⟨z, _, _, _, rfl, rfl⟩
        ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  | two x' y' Z =>
    simp only [relZ, Bool.cond_eq_ite, Bool.and_eq_true, beq_iff] at h
    split_ifs at h with e
    cases h; obtain ⟨rfl, rfl⟩ := e
    rfl
  | one _ _ => simp [relZ] at h

/-- **Additions.** A passed support check makes the support valid and the disjoint union of the
arguments' supports. -/
theorem supportOk_spec {s sa sb : Supp} (ha : sa.Ok) (hb : sb.Ok) (h : supportOk s sa sb = true) :
    s.Ok ∧ (∀ S, s.mem S ↔ sa.mem S ∨ sb.mem S) ∧ ∀ S, sa.mem S → sb.mem S → False := by
  cases s with
  | three _ _ _ => simp [supportOk] at h
  | two x y Z =>
    simp only [supportOk, Bool.and_eq_true, blt_iff] at h
    obtain ⟨⟨⟨hxy, hy⟩, hZ⟩, hu⟩ := h
    unfold optUnion at hu
    split at hu
    · rename_i za zb hza hzb
      obtain ⟨hand, hor⟩ := disjUnion_spec hu
      have hok : (Supp.two x y Z).Ok := ⟨hxy, hy, fun z hz =>
        (testBit_validZ (by omega) hy (by omega)).mp (subB_spec hZ z hz)⟩
      refine ⟨hok, ?_, ?_⟩
      · intro S
        rw [relZ_spec ha hza, relZ_spec hb hzb]
        simp only [Supp.mem, ← hor, show ∀ a b : ℕ, Nat.lor a b = a ||| b from fun _ _ => rfl]
        constructor
        · rintro ⟨z, hz, hz0, hz1, hzt, rfl⟩
          rw [testBit_lor, Bool.or_eq_true] at hzt
          rcases hzt with hzt | hzt
          · exact Or.inl ⟨z, hz, hz0, hz1, hzt, rfl⟩
          · exact Or.inr ⟨z, hz, hz0, hz1, hzt, rfl⟩
        · rintro (⟨z, hz, hz0, hz1, hzt, rfl⟩ | ⟨z, hz, hz0, hz1, hzt, rfl⟩)
          · exact ⟨z, hz, hz0, hz1, by rw [testBit_lor, hzt, Bool.true_or], rfl⟩
          · exact ⟨z, hz, hz0, hz1, by rw [testBit_lor, hzt, Bool.or_true], rfl⟩
      · intro S hsa hsb
        rw [relZ_spec ha hza] at hsa
        rw [relZ_spec hb hzb] at hsb
        obtain ⟨z, _, hz0, hz1, hzt, rfl⟩ := hsa
        obtain ⟨z', _, hz0', hz1', hzt', he⟩ := hsb
        have hzz : z = z' := by
          have hm : z ∈ ({x, y, z'} : Finset ℕ) := he ▸ by simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          omega
        subst hzz
        have := congrArg (fun n => n.testBit z) hand
        simp only [show ∀ a b : ℕ, Nat.land a b = a &&& b from fun _ _ => rfl, testBit_land, hzt,
          hzt', Bool.and_self, zero_testBit] at this
        cases this
    · cases hu
  | one c P =>
    simp only [supportOk, Bool.and_eq_true, blt_iff] at h
    obtain ⟨⟨hc, hP⟩, hu⟩ := h
    unfold optUnion at hu
    split at hu
    · rename_i pa pb' hpa hpb
      obtain ⟨hand, hor⟩ := disjUnion_spec hu
      have hok : (Supp.one c P).Ok := ⟨hc, fun i hi =>
        (testBit_pairsWithout hc i).mp (subB_spec hP i hi)⟩
      refine ⟨hok, ?_, ?_⟩
      · intro S
        rw [relP_spec ha hc hpa, relP_spec hb hc hpb, ← pairIn_or, hor]
        rfl
      · intro S hsa hsb
        rw [relP_spec ha hc hpa] at hsa
        rw [relP_spec hb hc hpb] at hsb
        exact pairIn_disjoint hand hsa hsb
    · cases hu

end IntegerMultBounds.MathlibTM2.M8.Local
