module

public import IntegerMultBounds.MathlibTM2.Routing.PackedShear

/-!
# Loads from upper target bits in the actual intermediate state

Sources may be unselected upper bits of target digits. A complete early pass
restores those bits, even though its individual rotations need not. The dynamic
load below reads the current target field, not a saved original address. It is a
permutation on every address because the load offset is independent of the field
being rotated. On good addresses it agrees with the frozen-source packed gadget.
This is still address arithmetic; the host reader and rotations need binding.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.Packed

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix

/-- All target bits except the selected low bit of each digit. -/
def upper (B L : ℤ) {n : ℕ} (x : EarlyAddress B L n) : List ℤ :=
  (digits (2 * L) n x.1.val).map (fun v => v / 2)

private theorem early_good_upper (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    {n : ℕ} (zs : List ℤ) (hlen : zs.length = n) (hz : Bits zs)
    (x : EarlyAddress B L n) (hx : earlyGood B L n x) :
    let y := packedEarlyPermN (2 * L) B (by omega) (by omega) n zs x
    earlyGood B L n y ∧ upper B L y = upper B L x := by
  subst n
  change earlyGood B L zs.length (packedEarlyPerm (2 * L) B _ _ zs x) ∧
    upper B L (packedEarlyPerm (2 * L) B _ _ zs x) = upper B L x
  rw [early_program_agrees_on_good B L hB hL zs hz x hx]
  refine ⟨(earlyIdeal_preserves_good B L hL zs hz x).mpr hx, ?_⟩
  change (digits (2 * L) zs.length (idealTarget L hL zs hz x.1).val).map _ = _
  rw [idealTarget_digits, upper_toggleList _ _ (digits_length ..) hz]
  rfl

/-- One complete dirty-control pass with arbitrary current control digits. -/
def earlyPass (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) (n : ℕ) :
    Equiv.Perm (LateAddress B L n) :=
  fiberPerm fun u => packedEarlyPermN (2 * L) B (by omega) (by omega) n
    ((digits B n u.val).map (· % 2))

theorem earlyPass_good_upper (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (x : LateAddress B L n) (hx : earlyGood B L n x.2) :
    earlyGood B L n (earlyPass B L hB hL n x).2 ∧
      upper B L (earlyPass B L hB hL n x).2 = upper B L x.2 := by
  apply early_good_upper B L hB hL _ (by simp [digits_length]) _ x.2 hx
  intro z hz
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
  omega

/-- The old constant-source composition, before its source-length transport. -/
def frozen (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) (n : ℕ) (zs : List ℤ) :
    Equiv.Perm (LateAddress B L n) :=
  let E := earlyPass B L hB hL n
  let load := rotateLeft (pow_pos (show 0 < B by omega) n)
    (fun _ : EarlyAddress B L n => pack B zs)
  E.trans (load.trans (E.trans load.symm))

theorem frozen_eq_step (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (zs : List ℤ) (hlen : zs.length = n) :
    frozen B L hB hL n zs = step B L hB hL zs hlen := by
  subst n
  rfl

/-- Load and unload using the actual current upper target digits. -/
def selfRead (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) (n : ℕ)
    (read : List ℤ → List ℤ) : Equiv.Perm (LateAddress B L n) :=
  let E := earlyPass B L hB hL n
  let load := rotateLeft (pow_pos (show 0 < B by omega) n)
    (fun x : EarlyAddress B L n => pack B (read (upper B L x)))
  E.trans (load.trans (E.trans load.symm))

/-- Both loads read the original upper bits, because the preceding complete early
passes preserve them. The second pass uses the actual newly loaded controls. -/
theorem selfRead_eq_frozen (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (read : List ℤ → List ℤ) (x : LateAddress B L n) (hx : earlyGood B L n x.2) :
    selfRead B L hB hL n read x = frozen B L hB hL n (read (upper B L x.2)) x := by
  let E := earlyPass B L hB hL n
  let load := rotateLeft (pow_pos (show 0 < B by omega) n)
    (fun y : EarlyAddress B L n => pack B (read (upper B L y)))
  let fixed := rotateLeft (pow_pos (show 0 < B by omega) n)
    (fun _ : EarlyAddress B L n => pack B (read (upper B L x.2)))
  have ha := earlyPass_good_upper B L hB hL x hx
  have hload : load (E x) = fixed (E x) := by
    change (fieldAdd _ (E x).1 (pack B (read (upper B L (E x).2))), (E x).2) = _
    rw [ha.2]
    rfl
  have hb := earlyPass_good_upper B L hB hL (fixed (E x)) ha.1
  have hunload : load.symm (E (fixed (E x))) = fixed.symm (E (fixed (E x))) := by
    change (fieldAdd _ _ (-pack B (read (upper B L (E (fixed (E x))).2))), _) = _
    rw [hb.2]
    change (fieldAdd _ _ (-pack B (read (upper B L (E x).2))), _) = _
    rw [ha.2]
    rfl
  change load.symm (E (load (E x))) = fixed.symm (E (fixed (E x)))
  rw [hload]
  exact hunload

/-- The self-reading permutation has the same good-set endpoint as the existing
proved packed gadget, without a copied or initialized source field. -/
theorem selfRead_good (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (read : List ℤ → List ℤ) (x : LateAddress B L n) (hx : lateGood B L n x)
    (hlen : (read (upper B L x.2)).length = n) (hz : Bits (read (upper B L x.2))) :
    selfRead B L hB hL n read x = ideal B L hL (read (upper B L x.2)) hlen hz x := by
  rw [selfRead_eq_frozen B L hB hL read x hx.1, frozen_eq_step B L hB hL _ hlen]
  exact step_eq_ideal B L hB hL _ hlen hz x hx

/-- Full good-set endpoint: both borrowed fields return, all upper target bits
return, and the selected low bits receive exactly the dynamically read source. -/
theorem selfRead_endpoint (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (read : List ℤ → List ℤ) (x : LateAddress B L n) (hx : lateGood B L n x)
    (hlen : (read (upper B L x.2)).length = n) (hz : Bits (read (upper B L x.2))) :
    let y := selfRead B L hB hL n read x
    y.1 = x.1 ∧ y.2.2 = x.2.2 ∧ upper B L y.2 = upper B L x.2 ∧
      (digits (2 * L) n y.2.1.val).map parity =
        List.zipWith Bool.xor ((digits (2 * L) n x.2.1.val).map parity)
          ((read (upper B L x.2)).map parity) := by
  dsimp only
  rw [selfRead_good B L hB hL read x hx hlen hz]
  obtain ⟨hu, hw, hp⟩ := ideal_endpoint B L hL _ hlen hz x
  exact ⟨hu, hw, ideal_upper B L hL _ hlen hz x, hp⟩

/-- The fixed-source ideal is its own inverse. -/
theorem ideal_twice (B L : ℤ) (hL : 0 < L) {n : ℕ}
    (zs : List ℤ) (hlen : zs.length = n) (hz : Bits zs) (x : LateAddress B L n) :
    ideal B L hL zs hlen hz (ideal B L hL zs hlen hz x) = x := by
  subst n
  exact (lateIdeal B L hL zs hz).symm_apply_apply x

/-- The variable-source ideal endpoint, reading upper target bits. -/
def selfIdealFun (B L : ℤ) (hL : 0 < L) (n : ℕ) (read : List ℤ → List ℤ)
    (hlen : ∀ us, (read us).length = n) (hbits : ∀ us, Bits (read us))
    (x : LateAddress B L n) : LateAddress B L n :=
  ideal B L hL (read (upper B L x.2)) (hlen _) (hbits _) x

/-- Its source observation is preserved on every address, not just good ones. -/
theorem selfIdeal_upper (B L : ℤ) (hL : 0 < L) {n : ℕ} (read : List ℤ → List ℤ)
    (hlen : ∀ us, (read us).length = n) (hbits : ∀ us, Bits (read us))
    (x : LateAddress B L n) :
    upper B L (selfIdealFun B L hL n read hlen hbits x).2 = upper B L x.2 :=
  ideal_upper B L hL _ (hlen _) (hbits _) x

theorem selfIdeal_involutive (B L : ℤ) (hL : 0 < L) {n : ℕ} (read : List ℤ → List ℤ)
    (hlen : ∀ us, (read us).length = n) (hbits : ∀ us, Bits (read us)) :
    Function.Involutive (selfIdealFun B L hL n read hlen hbits) := by
  intro x
  have hu := selfIdeal_upper B L hL read hlen hbits x
  change ideal B L hL (read (upper B L (selfIdealFun B L hL n read hlen hbits x).2))
    (hlen _) (hbits _) (selfIdealFun B L hL n read hlen hbits x) = x
  rw [hu]
  exact ideal_twice B L hL _ (hlen _) (hbits _) x

/-- The variable-source target is a permutation of the entire rectangle. -/
def selfIdeal (B L : ℤ) (hL : 0 < L) (n : ℕ) (read : List ℤ → List ℤ)
    (hlen : ∀ us, (read us).length = n) (hbits : ∀ us, Bits (read us)) :
    Equiv.Perm (LateAddress B L n) where
  toFun := selfIdealFun B L hL n read hlen hbits
  invFun := selfIdealFun B L hL n read hlen hbits
  left_inv := selfIdeal_involutive B L hL read hlen hbits
  right_inv := selfIdeal_involutive B L hL read hlen hbits

theorem selfIdeal_good (B L : ℤ) (hL : 0 < L) {n : ℕ} (read : List ℤ → List ℤ)
    (hlen : ∀ us, (read us).length = n) (hbits : ∀ us, Bits (read us))
    (x : LateAddress B L n) :
    lateGood B L n (selfIdeal B L hL n read hlen hbits x) ↔ lateGood B L n x :=
  ideal_good B L hL _ (hlen _) (hbits _) x

/-- Reading sources inside the target field does not lose or introduce bad addresses. -/
theorem selfRead_bad (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (read : List ℤ → List ℤ) (hlen : ∀ us, (read us).length = n)
    (hbits : ∀ us, Bits (read us)) (x : LateAddress B L n) :
    (¬lateGood B L n (selfRead B L hB hL n read x)) ↔ ¬lateGood B L n x := by
  apply actual_preserves_bad (selfRead B L hB hL n read)
    (selfIdeal B L hL n read hlen hbits) (fun y => ¬lateGood B L n y)
  · intro y
    exact not_congr (selfIdeal_good B L hL read hlen hbits y)
  · intro y hy
    exact selfRead_good B L hB hL read y (Classical.not_not.mp hy) (hlen _) (hbits _)

/-- The exact-repair identity applies to the actual self-reading program too. -/
theorem repair_selfRead (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L) {n : ℕ}
    (read : List ℤ → List ℤ) (hlen : ∀ us, (read us).length = n)
    (hbits : ∀ us, Bits (read us)) (x : LateAddress B L n) :
    let S := selfRead B L hB hL n read
    let T := selfIdeal B L hL n read hlen hbits
    (if ¬lateGood B L n (S x) then T (S.symm (S x)) else S x) = T x := by
  apply repair_exact (selfRead B L hB hL n read) (selfIdeal B L hL n read hlen hbits)
    (fun y => ¬lateGood B L n y)
  · intro y
    exact not_congr (selfIdeal_good B L hL read hlen hbits y)
  · intro y hy
    exact selfRead_good B L hB hL read y (Classical.not_not.mp hy) (hlen _) (hbits _)

end IntegerMultBounds.MathlibTM2.Routing.Packed
