module

public import IntegerMultBounds.Machine.FlatCoordinateShift

/-!
# The coordinate shift with a padded prefix

`FlatCoordinateShift` counts every earlier coordinate as its own prefix field, so its program
has `t` fields and depends on the target `t`. Here the prefix has three fields whatever the
target: the control coordinate `k` (field `0`, width `b`), the coordinates strictly between the
control and the target (field `1`, width `b (t - 1 - k)`, less significant), and the coordinates
before the control (field `2`, width `b k`, more significant). The program
`FlatControlledShiftReady.program r (low ++ 0 :: high)`, the order `[1, 0, 2]`, is one fixed program for every
target, control and coordinate count; only the width descriptors change. Its semantics are the
same ordered-affine shift (`array_entry`), and its cost is `886 V + 116` (`realizes_hoare`).
-/

@[expose] public section

namespace IntegerMultBounds.Machine.FlatPaddedShift
open Networks
open FlatCoordinateLayout
noncomputable section
variable {d radix b W : ℕ} [Fact radix.Prime]
local instance : NeZero (radix^b) := ⟨Nat.ne_of_gt (pow_pos (Fact.out : radix.Prime).pos b)⟩

/-- The spectator between the control and the target is less significant than the control. -/
def low : List (Fin 3) := [1]

/-- The spectator before the control is more significant. -/
def high : List (Fin 3) := [2]

theorem order_full : (low ++ 0 :: high).Perm (List.finRange 3) := by decide

/-- The three prefix widths: the control, the middle and the head. -/
def width (b : ℕ) (t k : Fin d) : Fin 3 → ℕ := ![b, b * (t.val - 1 - k.val), b * k.val]

@[simp] theorem width_zero (t k : Fin d) : width b t k 0 = b := rfl

theorem low_width (t k : Fin d) : PrefixAddressData.widthSum low (width b t k) = b * (t.val - 1 - k.val) := by
  simp [PrefixAddressData.widthSum, low, width]

theorem full_width (t k : Fin d) (hk : k < t) :
    PrefixAddressData.widthSum (low ++ 0 :: high) (width b t k) = b * t.val := by
  simp only [PrefixAddressData.widthSum, low, high, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, width, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have : (k : ℕ) < t := hk
  have ht : (t : ℕ) = (t.val - 1 - k.val) + 1 + k.val := by omega
  conv_rhs => rw [ht]
  ring

omit [Fact radix.Prime] in
theorem volume (t k : Fin d) (hk : k < t) :
    (radix^b)^d*W =
      radix^PrefixAddressData.widthSum (low ++ 0 :: high) (width b t k)*
        (radix^b*suffixSize (Q := radix^b) (W := W) t) := by
  rw [full_width t k hk, pow_mul]
  exact split_volume t

def view (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t) :
    Fin (radix^PrefixAddressData.widthSum (low ++ 0 :: high) (width b t k)*
      (radix^(width b t k 0)*suffixSize (Q := radix^b) (W := W) t)) → Fin 4 :=
  fun i => a (Fin.cast (volume t k hk).symm i)

omit [Fact radix.Prime] in
theorem view_word (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t) :
    List.ofFn (view a t k hk) = List.ofFn a := (List.ofFn_congr (volume t k hk) a).symm

/-- The selected slice of the padded prefix is the control coordinate. -/
theorem physicalOffset_eq (r : ℚ) (x : Fin d → ZMod (radix^b)) (t k : Fin d) (hk : k < t) :
    FlatControlledShift.physicalOffset (radix := radix) r low (width b t k) (prefixIndex x t) =
      (Swap.Modular.ratMod (radix^b) r*x k).val := by
  unfold FlatControlledShift.physicalOffset FlatControlledShift.control
  rw [low_width]
  change (Swap.Modular.ratMod (radix^b) r *
    (((prefixIndex x t / radix^(b*(t.val-1-k.val))) % radix^b : ℕ) : ZMod (radix^b))).val = _
  rw [earlier_control_radix x t k hk, ZMod.natCast_zmod_val]

def array (r : ℚ) (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t) :
    Fin ((radix^b)^d*W) → Fin 4 :=
  fun i => FlatControlledShiftArray.array r low high (width b t k)
    (view a t k hk) (Fin.cast (volume t k hk) i)

omit [Fact radix.Prime] in
theorem array_word (r : ℚ) (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t) :
    List.ofFn (array r a t k hk) =
      List.ofFn (FlatControlledShiftArray.array r low high (width b t k) (view a t k hk)) :=
  (List.ofFn_congr (volume t k hk).symm _).symm

/-- The padded shift has the ordered-affine shift semantics. -/
theorem array_entry (r : ℚ) (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t)
    (x : Fin d → ZMod (radix^b)) (j : Fin W) :
    array r a t k hk (index (OrderedAffine.execute (.shift t k (Swap.Modular.ratMod (radix^b) r)) x) j) =
      a (index x j) := by
  have hp : prefixIndex x t < radix^PrefixAddressData.widthSum (low ++ 0 :: high) (width b t k) := by
    simpa only [full_width t k hk, pow_mul, prefixSize] using prefix_lt x t
  have hh := FlatControlledShiftArray.array_entry r low high (width b t k)
    (view a t k hk) ⟨prefixIndex x t, hp⟩ ⟨(x t).val, ZMod.val_lt _⟩
    ⟨suffix x t j, suffix_lt x t j⟩
  have hin : view a t k hk (FiberLayoutData.index ⟨prefixIndex x t, hp⟩
      ⟨(x t).val, ZMod.val_lt _⟩ ⟨suffix x t j, suffix_lt x t j⟩) = a (index x j) := by
    unfold view
    congr 1
    apply Fin.ext
    simpa only [Fin.val_cast, FiberLayoutData.index_val, width_zero] using (index_split x t j).symm
  rw [hin] at hh
  unfold array
  convert hh using 1
  congr 1
  apply Fin.ext
  simp only [Fin.val_cast, shift_destination, FiberLayoutData.index_val, physicalOffset_eq r x t k hk,
    width_zero]

/-- Source slot in the initialized prefix-counter bank of three fields. -/
def sourceSlot :=
  PrefixCounterInitPlacement.handoff (RationalPrefixTranslationInit.streamPlacement 2)
    (Fin.castAdd (PrefixCounterInitPlacement.extras (2+1)) (10 : Fin ((16+2)+2)))

theorem output_source (r : ℚ) (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t)
    (ws : Fin (2+1) → List Bool) (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool) :
    (FlatControlledShiftReady.output r low high (width b t k) ws
      (view a t k hk) source dest p q bs qs ns).tape sourceSlot =
      fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
        (putWord source p (List.ofFn (array r a t k hk)) z) := by
  rw [sourceSlot, FlatControlledShiftArray.output_source, array_word]

/-- **The padded shift on the machine.** One fixed program for every target and control: all
initialization, shift, copying and head restoration are paid, at `886 V + 116`. -/
theorem realizes_hoare (r : ℚ) (hden : r.den < radix)
    (a : Fin ((radix^b)^d*W) → Fin 4) (t k : Fin d) (hk : k < t) (hW : 0 < W)
    (ws : Fin (2+1) → List Bool)
    (hw : ∀ i, Counter.value (ws i) = width b t k i) (cw : ∀ i, GrowingCounterData.Canonical (ws i))
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs qs ns : List Bool)
    (hb : Counter.value bs = suffixSize (Q := radix^b) (W := W) t)
    (hq : Counter.value qs = radix^b) (hn : Counter.value ns = (radix^b)^t.val)
    (cb : GrowingCounterData.Canonical bs) (cq : GrowingCounterData.Canonical qs)
    (cn : GrowingCounterData.Canonical ns)
    (hblank : ∀ z, q ≤ z → z < q+(((radix^b)^d*W : ℕ) : ℤ) → dest z = blank) :
    HoareTime (FlatControlledShiftReady.program (radix := radix) r (low ++ 0 :: high) (by simp))
      (fun v => v = RationalPrefixTranslationBootstrap.input r (low ++ 0 :: high) (width b t k)
        ws (view a t k hk) source dest p q bs qs ns)
      (fun v => v = FlatControlledShiftReady.output r low high (width b t k)
          ws (view a t k hk) source dest p q bs qs ns ∧
        v.tape sourceSlot = (fun z => (RadixToBinary.binaryEncoding (q := radix)).encode
          (putWord source p (List.ofFn (array r a t k hk)) z)) ∧
        ∀ (x : Fin d → ZMod (radix^b)) (j : Fin W),
          array r a t k hk (index (OrderedAffine.execute (.shift t k (Swap.Modular.ratMod (radix^b) r)) x) j) =
            a (index x j))
      ((878+4*2)*((radix^b)^d*W)+29*(2+1)+29) := by
  have hv := volume (radix := radix) (b := b) (W := W) t k hk
  have hs := FlatControlledShiftReady.realizes_hoare (B := suffixSize (Q := radix^b) (W := W) t)
    r hden low high order_full (width b t k) ws hw cw
    (Nat.mul_pos (pow_pos (pow_pos (Fact.out : radix.Prime).pos b) _) hW)
    (view a t k hk) source dest p q bs qs ns hb hq
    (by simpa only [full_width t k hk, pow_mul] using hn) cb cq cn
    (by
      intro z hz hz'
      apply hblank z hz
      rw [FlatControlledShiftNormalize.word_length] at hz'
      rw [width_zero] at hz'
      rw [← hv] at hz'
      exact hz')
  apply hs.consequence (fun _ h => h) ?_ ?_
  · intro v hv
    subst v
    exact ⟨rfl, output_source r a t k hk ws source dest p q bs qs ns, array_entry r a t k hk⟩
  · rw [width_zero, ← hv]

end
end IntegerMultBounds.Machine.FlatPaddedShift
