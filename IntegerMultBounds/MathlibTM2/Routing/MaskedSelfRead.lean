module

public import IntegerMultBounds.MathlibTM2.Routing.Mask

/-!
# Selective shears reading all preserved target coordinates

The source observation retains upper bits at active targets and complete digits
at inactive positions. Each complete early pass preserves that observation. The
actual load/unload reads it at execution time, so inactive low bits may be sources.
The result is a permutation on every address and has the specified selective XOR
endpoint on the good set. No host execution or source-gathering cost is assumed.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.Packed

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix

/-- Masked dirty-control passes with loads from the actual preserved coordinates. -/
def maskedSelfRead (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (read : List ℤ → List ℤ) : Equiv.Perm (LateAddress B L n) :=
  let E := maskedEarly B L hB hL (n := n) active
  let load := rotateLeft (pow_pos (show 0 < B by omega) n)
    (fun x : EarlyAddress B L n => pack B (read (sourceView B L active x)))
  E.trans (load.trans (E.trans load.symm))

theorem maskedSelfRead_eq_frozen (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (ha : active.length = n) (read : List ℤ → List ℤ)
    (x : LateAddress B L n) (hx : earlyGood B L n x.2) :
    maskedSelfRead B L hB hL active read x =
      maskedFrozen B L hB hL active (read (sourceView B L active x.2)) x := by
  let E := maskedEarly B L hB hL (n := n) active
  let load := rotateLeft (pow_pos (show 0 < B by omega) n)
    (fun y : EarlyAddress B L n => pack B (read (sourceView B L active y)))
  let fixed := rotateLeft (pow_pos (show 0 < B by omega) n)
    (fun _ : EarlyAddress B L n => pack B (read (sourceView B L active x.2)))
  obtain ⟨_, _, haGood, haView⟩ := maskedEarly_endpoint B L hB hL active ha x hx
  have hload : load (E x) = fixed (E x) := by
    change (fieldAdd _ (E x).1 (pack B (read (sourceView B L active (E x).2))), (E x).2) = _
    rw [haView]
    rfl
  obtain ⟨_, _, _, hbView⟩ :=
    maskedEarly_endpoint B L hB hL active ha (fixed (E x)) haGood
  have hunload : load.symm (E (fixed (E x))) = fixed.symm (E (fixed (E x))) := by
    change (fieldAdd _ _ (-pack B (read (sourceView B L active (E (fixed (E x))).2))), _) = _
    rw [hbView]
    change (fieldAdd _ _ (-pack B (read (sourceView B L active (E x).2))), _) = _
    rw [haView]
    rfl
  change load.symm (E (load (E x))) = fixed.symm (E (fixed (E x)))
  rw [hload]
  exact hunload

/-- The full masked good-set correctness theorem, including dynamically read sources. -/
theorem maskedSelfRead_good (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (ha : active.length = n) (read : List ℤ → List ℤ)
    (x : LateAddress B L n) (hx : lateGood B L n x)
    (hlen : (read (sourceView B L active x.2)).length = n)
    (hz : Bits (read (sourceView B L active x.2))) :
    maskedSelfRead B L hB hL active read x =
      ideal B L hL (maskBits active (read (sourceView B L active x.2)))
        ((maskBits_length active _ (ha.trans hlen.symm)).trans ha)
        (maskBits_bits active _ hz) x := by
  rw [maskedSelfRead_eq_frozen B L hB hL active ha read x hx.1]
  exact maskedFrozen_good B L hB hL active ha _ hlen hz x hx

private theorem ideal_sourceView (B L : ℤ) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (ha : active.length = n) (zs : List ℤ) (hlen : zs.length = n)
    (hz : Bits zs) (x : LateAddress B L n) :
    sourceView B L active
      (ideal B L hL (maskBits active zs)
        ((maskBits_length active zs (ha.trans hlen.symm)).trans ha)
        (maskBits_bits active zs hz) x).2 = sourceView B L active x.2 := by
  have hm : (maskBits active zs).length = n :=
    (maskBits_length active zs (ha.trans hlen.symm)).trans ha
  have hd : digits (2 * L) n
      (ideal B L hL (maskBits active zs) hm (maskBits_bits active zs hz) x).2.1.val =
        toggleList (digits (2 * L) n x.2.1.val) (maskBits active zs) := by
    exact ideal_digits B L hL _ hm _ x
  unfold sourceView
  rw [hd]
  exact visible_toggle active _ zs (by simp [digits_length, ha]) (ha.trans hlen.symm) hz

/-- The ideal selective shear on all addresses. -/
def maskedIdealFun (B L : ℤ) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (ha : active.length = n) (read : List ℤ → List ℤ)
    (hlen : ∀ vs, (read vs).length = n) (hbits : ∀ vs, Bits (read vs))
    (x : LateAddress B L n) : LateAddress B L n :=
  ideal B L hL (maskBits active (read (sourceView B L active x.2)))
    ((maskBits_length active _ (ha.trans (hlen _).symm)).trans ha)
    (maskBits_bits active _ (hbits _)) x

theorem maskedIdeal_view (B L : ℤ) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (ha : active.length = n) (read : List ℤ → List ℤ)
    (hlen : ∀ vs, (read vs).length = n) (hbits : ∀ vs, Bits (read vs))
    (x : LateAddress B L n) :
    sourceView B L active (maskedIdealFun B L hL active ha read hlen hbits x).2 =
      sourceView B L active x.2 :=
  ideal_sourceView B L hL active ha _ (hlen _) (hbits _) x

theorem maskedIdeal_involutive (B L : ℤ) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (ha : active.length = n) (read : List ℤ → List ℤ)
    (hlen : ∀ vs, (read vs).length = n) (hbits : ∀ vs, Bits (read vs)) :
    Function.Involutive (maskedIdealFun B L hL active ha read hlen hbits) := by
  intro x
  have hv := maskedIdeal_view B L hL active ha read hlen hbits x
  let run (vs : List ℤ) (y : LateAddress B L n) :=
    ideal B L hL (maskBits active (read vs))
      ((maskBits_length active _ (ha.trans (hlen vs).symm)).trans ha)
      (maskBits_bits active _ (hbits vs)) y
  change run (sourceView B L active (maskedIdealFun B L hL active ha read hlen hbits x).2)
    (maskedIdealFun B L hL active ha read hlen hbits x) = x
  rw [hv]
  exact ideal_twice B L hL _ _ _ x

def maskedIdeal (B L : ℤ) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (ha : active.length = n) (read : List ℤ → List ℤ)
    (hlen : ∀ vs, (read vs).length = n) (hbits : ∀ vs, Bits (read vs)) :
    Equiv.Perm (LateAddress B L n) where
  toFun := maskedIdealFun B L hL active ha read hlen hbits
  invFun := maskedIdealFun B L hL active ha read hlen hbits
  left_inv := maskedIdeal_involutive B L hL active ha read hlen hbits
  right_inv := maskedIdeal_involutive B L hL active ha read hlen hbits

theorem maskedIdeal_good (B L : ℤ) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (ha : active.length = n) (read : List ℤ → List ℤ)
    (hlen : ∀ vs, (read vs).length = n) (hbits : ∀ vs, Bits (read vs))
    (x : LateAddress B L n) :
    lateGood B L n (maskedIdeal B L hL active ha read hlen hbits x) ↔ lateGood B L n x :=
  ideal_good B L hL _ _ _ x

theorem maskedSelfRead_bad (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (ha : active.length = n) (read : List ℤ → List ℤ)
    (hlen : ∀ vs, (read vs).length = n) (hbits : ∀ vs, Bits (read vs))
    (x : LateAddress B L n) :
    (¬lateGood B L n (maskedSelfRead B L hB hL active read x)) ↔ ¬lateGood B L n x := by
  apply actual_preserves_bad (maskedSelfRead B L hB hL active read)
    (maskedIdeal B L hL active ha read hlen hbits) (fun y => ¬lateGood B L n y)
  · intro y
    exact not_congr (maskedIdeal_good B L hL active ha read hlen hbits y)
  · intro y hy
    exact maskedSelfRead_good B L hB hL active ha read y
      (Classical.not_not.mp hy) (hlen _) (hbits _)

theorem repair_maskedSelfRead (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (active : List Bool) (ha : active.length = n) (read : List ℤ → List ℤ)
    (hlen : ∀ vs, (read vs).length = n) (hbits : ∀ vs, Bits (read vs))
    (x : LateAddress B L n) :
    let S := maskedSelfRead B L hB hL active read
    let T := maskedIdeal B L hL active ha read hlen hbits
    (if ¬lateGood B L n (S x) then T (S.symm (S x)) else S x) = T x := by
  apply repair_exact (maskedSelfRead B L hB hL active read)
    (maskedIdeal B L hL active ha read hlen hbits) (fun y => ¬lateGood B L n y)
  · intro y
    exact not_congr (maskedIdeal_good B L hL active ha read hlen hbits y)
  · intro y hy
    exact maskedSelfRead_good B L hB hL active ha read y
      (Classical.not_not.mp hy) (hlen _) (hbits _)

end IntegerMultBounds.MathlibTM2.Routing.Packed
