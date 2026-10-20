module

public import IntegerMultBounds.MathlibTM2.Layer.Carry
public import IntegerMultBounds.MathlibTM2.Layer.Format
import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords

/-!
# Gaussian linear combinations, one bit position per step

An automaton with `k` Gaussian inputs and `l` Gaussian outputs computes
`wⱼ = Σᵢ gⱼᵢ zᵢ` modulo `2^W`, with integer coefficients `gⱼᵢ = (a, b)` read as `a + b i`.
Each step reads one bit position of every input (real bit, imaginary bit) and emits the same bit
position of every output. The state is one signed carry for the real part and one for the
imaginary part of each output; each part runs one column of the signed-carry adder `carryRun`
on its column sum

* real part of output `j`: `Σᵢ (aⱼᵢ reᵢ - bⱼᵢ imᵢ)`,
* imaginary part of output `j`: `Σᵢ (aⱼᵢ imᵢ + bⱼᵢ reᵢ)`.

`grun_correct`: from zero carries, the `W` columns of the inputs `gcols zs` produce the `W`
columns of `glin g zs`. `gcarry_zero_bound`: if `B ≥ Σᵢ (|aⱼᵢ| + |bⱼᵢ|)` for every output, all
carries stay in `[-B, B]`, so the automaton has finitely many reachable states.

Instances: `GR.kernel2` (`grun_kernel2`), multiplication by a Gaussian integer
(`grun_mulG`, with `grun_mulI` and `grun_neg`), and conjugation (`grun_conj`). Conjugation is
not Gaussian-linear; the automaton computes it from the input columns with real and imaginary
bits swapped, since `conj z = -i · (im z + i re z)`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

/-! ### One column of the signed-carry adder -/

/-- One column of `carryRun`: the emitted bit and the new carry. -/
def cstep (c s : ℤ) : Bool × ℤ :=
  let b := (c + s) % 2 = 1
  (b, (c + s - (if b then 1 else 0)) / 2)

lemma carryRun_cons_fst (c s : ℤ) (ss : List ℤ) :
    (carryRun c (s :: ss)).1 = (cstep c s).1 :: (carryRun (cstep c s).2 ss).1 := rfl

/-- The new carry stays within a bound `B` that also bounds the column sum. -/
lemma cstep_bound {B c s : ℤ} (hc : |c| ≤ B) (hs : |s| ≤ B) : |(cstep c s).2| ≤ B := by
  simp only [cstep]
  rw [abs_le] at hc hs ⊢
  split_ifs <;> omega

/-! ### Bit lists of fixed length -/

lemma valBits_lt (bs : List Bool) : valBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [valBits]
  | cons b bs ih =>
      simp only [valBits, List.length_cons, pow_succ]
      cases b <;> simp <;> omega

/-- `valBits` of a bit list of length `W` is below `2^W`. -/
lemma valBits_lt_of_length {W : ℕ} (bs : List Bool) (h : bs.length = W) : valBits bs < 2 ^ W :=
  h ▸ valBits_lt bs

lemma eq_ofFn_testBit (bs : List Bool) :
    bs = List.ofFn fun t : Fin bs.length => (valBits bs).testBit t := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons, List.ofFn_succ]
      congr 1
      · cases b <;> simp [valBits, Nat.testBit_zero]
      · conv_lhs => rw [ih]
        congr 1
        funext t
        simp only [Fin.val_succ, valBits, Nat.testBit_succ]
        congr 1
        cases b <;> simp
        omega

/-- A bit list of length `W` is the `W` low bits of its value. -/
lemma eq_ofFn_testBit_of_length {W : ℕ} (bs : List Bool) (h : bs.length = W) :
    bs = List.ofFn fun t : Fin W => (valBits bs).testBit t := by
  subst h
  exact eq_ofFn_testBit bs

lemma getD_ofFn_testBit (W n : ℕ) (t : Fin W) :
    (List.ofFn fun s : Fin W => n.testBit s).getD t false = n.testBit t := by
  simp [List.getD_eq_getElem?_getD]

/-- The bits emitted for an integer combination of residues are the bits of the combination
modulo `2^W`. -/
theorem carryRun_bits (W m : ℕ) (a : Fin m → ℤ) (xs : Fin m → ZMod (2 ^ W)) :
    (carryRun 0 (List.ofFn fun t : Fin W =>
        ∑ i, a i * (((xs i).val.testBit t).toNat : ℤ))).1 =
      List.ofFn fun t : Fin W => (∑ i, (a i : ZMod (2 ^ W)) * xs i).val.testBit t := by
  have hlin := carryRun_lin W m a (fun i => List.ofFn fun t : Fin W => (xs i).val.testBit t)
    (by simp)
  simp only [getD_ofFn_testBit, valBits_val] at hlin
  generalize hbits : (carryRun 0 (List.ofFn fun t : Fin W =>
        ∑ i, a i * (((xs i).val.testBit t).toNat : ℤ))).1 = bits at hlin
  have hlen : bits.length = W := by rw [← hbits, carryRun_length, List.length_ofFn]
  have h1 : ((valBits bits : ℕ) : ZMod (2 ^ W)) = ∑ i, (a i : ZMod (2 ^ W)) * xs i := by
    push_cast at hlin
    simpa [ZMod.natCast_val, ZMod.cast_id] using hlin
  have hv : valBits bits = (∑ i, (a i : ZMod (2 ^ W)) * xs i).val := by
    rw [← h1, ZMod.val_natCast_of_lt (valBits_lt_of_length bits hlen)]
  rw [eq_ofFn_testBit_of_length bits hlen, hv]

/-- Two-family form of `carryRun_bits`. -/
theorem carryRun_bits₂ (W k : ℕ) (a b : Fin k → ℤ) (xs ys : Fin k → ZMod (2 ^ W)) :
    (carryRun 0 (List.ofFn fun t : Fin W => ∑ i, (a i * (((xs i).val.testBit t).toNat : ℤ) +
        b i * (((ys i).val.testBit t).toNat : ℤ)))).1 =
      List.ofFn fun t : Fin W =>
        (∑ i, ((a i : ZMod (2 ^ W)) * xs i + (b i : ZMod (2 ^ W)) * ys i)).val.testBit t := by
  have h := carryRun_bits W (k + k) (Fin.append a b) (Fin.append xs ys)
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right] at h
  simpa only [Finset.sum_add_distrib] using h

/-! ### The automaton -/

section Gauss

variable {k l : ℕ}

/-- Real column sum of output `j`: `Σᵢ (aⱼᵢ reᵢ - bⱼᵢ imᵢ)`. -/
def gre (g : Fin l → Fin k → ℤ × ℤ) (x : Fin k → Bool × Bool) (j : Fin l) : ℤ :=
  ∑ i, ((g j i).1 * ((x i).1.toNat : ℤ) - (g j i).2 * ((x i).2.toNat : ℤ))

/-- Imaginary column sum of output `j`: `Σᵢ (aⱼᵢ imᵢ + bⱼᵢ reᵢ)`. -/
def gim (g : Fin l → Fin k → ℤ × ℤ) (x : Fin k → Bool × Bool) (j : Fin l) : ℤ :=
  ∑ i, ((g j i).1 * ((x i).2.toNat : ℤ) + (g j i).2 * ((x i).1.toNat : ℤ))

/-- One step: from the carries and the input bit pairs at one position, the new carries and the
output bit pairs at that position. -/
def gstep (g : Fin l → Fin k → ℤ × ℤ) (c : Fin l → ℤ × ℤ) (x : Fin k → Bool × Bool) :
    (Fin l → ℤ × ℤ) × (Fin l → Bool × Bool) :=
  (fun j => ((cstep (c j).1 (gre g x j)).2, (cstep (c j).2 (gim g x j)).2),
   fun j => ((cstep (c j).1 (gre g x j)).1, (cstep (c j).2 (gim g x j)).1))

/-- The output columns of a run over input columns, least significant first. -/
def grun (g : Fin l → Fin k → ℤ × ℤ) :
    (Fin l → ℤ × ℤ) → List (Fin k → Bool × Bool) → List (Fin l → Bool × Bool)
  | _, [] => []
  | c, x :: xs => (gstep g c x).2 :: grun g (gstep g c x).1 xs

/-- The carries after a run over input columns. -/
def gcarry (g : Fin l → Fin k → ℤ × ℤ) :
    (Fin l → ℤ × ℤ) → List (Fin k → Bool × Bool) → Fin l → ℤ × ℤ
  | c, [] => c
  | c, x :: xs => gcarry g (gstep g c x).1 xs

lemma grun_length (g : Fin l → Fin k → ℤ × ℤ) (c : Fin l → ℤ × ℤ)
    (xs : List (Fin k → Bool × Bool)) : (grun g c xs).length = xs.length := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp [grun, ih]

/-- A run splits at any position; the second part starts from the carries `gcarry`. -/
lemma grun_append (g : Fin l → Fin k → ℤ × ℤ) (c : Fin l → ℤ × ℤ)
    (xs ys : List (Fin k → Bool × Bool)) :
    grun g c (xs ++ ys) = grun g c xs ++ grun g (gcarry g c xs) ys := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp [grun, gcarry, ih]

/-- The real output bits of `j` are the bits of the carry adder on the real column sums. -/
lemma grun_fst (g : Fin l → Fin k → ℤ × ℤ) (c : Fin l → ℤ × ℤ)
    (xs : List (Fin k → Bool × Bool)) (j : Fin l) :
    (grun g c xs).map (fun o => (o j).1) = (carryRun (c j).1 (xs.map fun x => gre g x j)).1 := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, carryRun_cons_fst]
      exact congrArg₂ List.cons rfl (ih _)

/-- The imaginary output bits of `j` are the bits of the carry adder on the imaginary column
sums. -/
lemma grun_snd (g : Fin l → Fin k → ℤ × ℤ) (c : Fin l → ℤ × ℤ)
    (xs : List (Fin k → Bool × Bool)) (j : Fin l) :
    (grun g c xs).map (fun o => (o j).2) = (carryRun (c j).2 (xs.map fun x => gim g x j)).1 := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih =>
      rw [List.map_cons, carryRun_cons_fst]
      exact congrArg₂ List.cons rfl (ih _)

/-- Lists of output columns agree if they have the same length and the same bit sequence in
every output part. -/
lemma colList_ext (L₁ L₂ : List (Fin l → Bool × Bool)) (hlen : L₁.length = L₂.length)
    (h₁ : ∀ j, L₁.map (fun o => (o j).1) = L₂.map (fun o => (o j).1))
    (h₂ : ∀ j, L₁.map (fun o => (o j).2) = L₂.map (fun o => (o j).2)) : L₁ = L₂ := by
  apply List.ext_getElem hlen
  intro n hn₁ hn₂
  funext j
  have e₁ := congrArg (fun L => L[n]?) (h₁ j)
  have e₂ := congrArg (fun L => L[n]?) (h₂ j)
  simp [hn₁, hn₂] at e₁ e₂
  exact Prod.ext e₁ e₂

end Gauss

/-! ### Columns of residues and correctness -/

section Residues

variable {W k l : ℕ}

/-- The `W` columns of a family of residues, least significant first: at position `t`, the real
bit and the imaginary bit of each residue. -/
def gcols (zs : Fin k → GR W) : List (Fin k → Bool × Bool) :=
  List.ofFn fun t : Fin W => fun i => ((zs i).1.val.testBit t, (zs i).2.val.testBit t)

/-- The output residues `wⱼ = Σᵢ (aⱼᵢ + bⱼᵢ i) zᵢ` modulo `2^W`. -/
def glin (g : Fin l → Fin k → ℤ × ℤ) (zs : Fin k → GR W) : Fin l → GR W := fun j =>
  (∑ i, (((g j i).1 : ZMod (2 ^ W)) * (zs i).1 - ((g j i).2 : ZMod (2 ^ W)) * (zs i).2),
   ∑ i, (((g j i).1 : ZMod (2 ^ W)) * (zs i).2 + ((g j i).2 : ZMod (2 ^ W)) * (zs i).1))

lemma glin_eq_sum_mulG (g : Fin l → Fin k → ℤ × ℤ) (zs : Fin k → GR W) (j : Fin l) :
    glin g zs j = ∑ i, GR.mulG (g j i).1 (g j i).2 (zs i) := by
  simp [glin, GR.mulG, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]

lemma length_gcols (zs : Fin k → GR W) : (gcols zs).length = W := by simp [gcols]

/-- From zero carries, the automaton maps the columns of the inputs to the columns of the
outputs. -/
theorem grun_correct (g : Fin l → Fin k → ℤ × ℤ) (zs : Fin k → GR W) :
    grun g (fun _ => (0, 0)) (gcols zs) = gcols (glin g zs) := by
  apply colList_ext
  · rw [grun_length, length_gcols, length_gcols]
  · intro j
    rw [grun_fst]
    have h := carryRun_bits₂ W k (fun i => (g j i).1) (fun i => -(g j i).2)
      (fun i => (zs i).1) (fun i => (zs i).2)
    simp only [neg_mul, ← sub_eq_add_neg, Int.cast_neg] at h
    simp only [gcols, List.map_ofFn, Function.comp_def, gre, glin]
    exact h
  · intro j
    rw [grun_snd]
    have h := carryRun_bits₂ W k (fun i => (g j i).1) (fun i => (g j i).2)
      (fun i => (zs i).2) (fun i => (zs i).1)
    simp only [gcols, List.map_ofFn, Function.comp_def, gim, glin]
    exact h

end Residues

/-! ### Carry bound -/

section Bound

variable {k l : ℕ}

/-- All carries lie in `[-B, B]`. -/
def CarryLe (B : ℤ) (c : Fin l → ℤ × ℤ) : Prop := ∀ j, |(c j).1| ≤ B ∧ |(c j).2| ≤ B

lemma abs_term_le (a b : ℤ) (r m : Bool) :
    |a * (r.toNat : ℤ) - b * (m.toNat : ℤ)| ≤ |a| + |b| ∧
      |a * (m.toNat : ℤ) + b * (r.toNat : ℤ)| ≤ |a| + |b| := by
  have ha := le_abs_self a
  have ha' := neg_abs_le a
  have hb := le_abs_self b
  have hb' := neg_abs_le b
  cases r <;> cases m <;> simp only [Bool.toNat_true, Bool.toNat_false] <;> push_cast <;>
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith

lemma abs_gre_le (g : Fin l → Fin k → ℤ × ℤ) (x : Fin k → Bool × Bool) (j : Fin l) :
    |gre g x j| ≤ ∑ i, (|(g j i).1| + |(g j i).2|) :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => (abs_term_le _ _ (x i).1 (x i).2).1)

lemma abs_gim_le (g : Fin l → Fin k → ℤ × ℤ) (x : Fin k → Bool × Bool) (j : Fin l) :
    |gim g x j| ≤ ∑ i, (|(g j i).1| + |(g j i).2|) :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => (abs_term_le _ _ (x i).1 (x i).2).2)

/-- If `B ≥ Σᵢ (|aⱼᵢ| + |bⱼᵢ|)` for every output, a step keeps carries in `[-B, B]`. -/
theorem gstep_bound (g : Fin l → Fin k → ℤ × ℤ) {B : ℤ}
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ B) {c : Fin l → ℤ × ℤ} (hc : CarryLe B c)
    (x : Fin k → Bool × Bool) : CarryLe B (gstep g c x).1 := fun j =>
  ⟨cstep_bound (hc j).1 ((abs_gre_le g x j).trans (hB j)),
    cstep_bound (hc j).2 ((abs_gim_le g x j).trans (hB j))⟩

theorem gcarry_bound (g : Fin l → Fin k → ℤ × ℤ) {B : ℤ}
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ B) {c : Fin l → ℤ × ℤ} (hc : CarryLe B c)
    (xs : List (Fin k → Bool × Bool)) : CarryLe B (gcarry g c xs) := by
  induction xs generalizing c with
  | nil => exact hc
  | cons x xs ih => exact ih (gstep_bound g hB hc x)

/-- Every state reached from zero carries (the carries after any prefix of the input columns,
see `grun_append`) lies in `[-B, B]`. -/
theorem gcarry_zero_bound (g : Fin l → Fin k → ℤ × ℤ) {B : ℤ}
    (hB : ∀ j, ∑ i, (|(g j i).1| + |(g j i).2|) ≤ B) (xs : List (Fin k → Bool × Bool)) :
    CarryLe B (gcarry g (fun _ => (0, 0)) xs) := by
  refine gcarry_bound g hB (fun j => ?_) xs
  have h0 : (0 : ℤ) ≤ B :=
    (Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hB j)
  simpa using h0

end Bound

/-! ### Instances -/

section Instances

variable {W : ℕ}

/-- Coefficients of `GR.kernel2`: `((1 + i) u + (1 - i) v, (1 - i) u + (1 + i) v)`. -/
def gKernel2 : Fin 2 → Fin 2 → ℤ × ℤ := ![![(1, 1), (1, -1)], ![(1, -1), (1, 1)]]

theorem grun_kernel2 (u v : GR W) :
    grun gKernel2 (fun _ => (0, 0)) (gcols ![u, v]) =
      gcols ![(GR.kernel2 u v).1, (GR.kernel2 u v).2] := by
  rw [grun_correct]
  congr 1
  funext j
  rw [glin_eq_sum_mulG]
  fin_cases j <;> simp [gKernel2, GR.kernel2, Fin.sum_univ_two]

/-- Multiplication by the Gaussian integer `a + b i`. -/
theorem grun_mulG (a b : ℤ) (z : GR W) :
    grun ![![(a, b)]] (fun _ => (0, 0)) (gcols ![z]) = gcols ![GR.mulG a b z] := by
  rw [grun_correct]
  congr 1
  funext j
  rw [glin_eq_sum_mulG]
  fin_cases j
  simp

theorem grun_mulI (z : GR W) :
    grun ![![(0, 1)]] (fun _ => (0, 0)) (gcols ![z]) = gcols ![GR.mulI z] := by
  rw [grun_mulG]
  congr 3
  simp [GR.mulG, GR.mulI]

theorem grun_neg (z : GR W) :
    grun ![![(-1, 0)]] (fun _ => (0, 0)) (gcols ![z]) = gcols ![-z] := by
  rw [grun_mulG]
  congr 3
  simp [GR.mulG, Prod.ext_iff]

/-- Swapping the real and imaginary bit of every input column swaps the parts of the inputs. -/
lemma gcols_swap {k : ℕ} (zs : Fin k → GR W) :
    (gcols zs).map (fun x i => (x i).swap) = gcols fun i => (zs i).swap := by
  simp [gcols, List.map_ofFn, Function.comp_def]

/-- `a + b i` times the conjugate: the coefficient `b - a i` applied to the swapped columns,
since `(a + b i) · conj z = (b - a i) · (im z + i re z)`. -/
theorem grun_mulG_conj (a b : ℤ) (z : GR W) :
    grun ![![(b, -a)]] (fun _ => (0, 0)) ((gcols ![z]).map fun x i => (x i).swap) =
      gcols ![GR.mulG a b (GR.conj z)] := by
  rw [gcols_swap, grun_correct]
  congr 1
  funext j
  rw [glin_eq_sum_mulG]
  fin_cases j
  simp [GR.mulG, GR.conj, Prod.ext_iff]
  constructor <;> ring

/-- Conjugation: the coefficient `-i` applied to the swapped columns. -/
theorem grun_conj (z : GR W) :
    grun ![![(0, -1)]] (fun _ => (0, 0)) ((gcols ![z]).map fun x i => (x i).swap) =
      gcols ![GR.conj z] := by
  rw [grun_mulG_conj 1 0 z]
  congr 3
  simp [GR.mulG, GR.conj]

end Instances

end IntegerMultBounds.MathlibTM2.Layer
