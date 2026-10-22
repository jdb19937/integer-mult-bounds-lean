module

public import IntegerMultBounds.MathlibTM2.Routing.HeaderRot
public import IntegerMultBounds.MathlibTM2.Routing.PlainPatterns
public import IntegerMultBounds.MathlibTM2.Layer.CompactGadgetIndex

/-!
# Mixed offsets read from actual higher field counters

The descriptor windows are measured inside the copied header. This bridge
identifies those windows with digits of the actual live record index, so the
executed AND/XOR rotations have exactly the masked compact-gadget offsets.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

/-- A field wholly inside the header is read at its relative bit offset. -/
theorem headerWindow {nf : ℕ} (len : Fin nf → ℕ) (f : Fin nf) (o r W i : ℕ)
    (hoff : o + r = fieldOff len f) (hwidth : r + len f ≤ W) :
    window r (len f) ((i / 2 ^ o) % 2 ^ W) = digit len f i := by
  rw [window_mod hwidth]
  unfold window digit
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, hoff]

variable (p : Par) {nf W : ℕ} {len : Fin nf → ℕ} {F : Fields nf}

/-- The concrete executed AND offset reads the actual temporary and control digits. -/
theorem aHeaderOffset_eq (hF : F.Valid p len) (hG : 0 < p.G) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (o uOff tOff : ℕ)
    (hu : uOff + p.wc ≤ W) (ht : tOff + p.wc ≤ W)
    (huOff : o + uOff = fieldOff len F.u) (htOff : o + tOff = fieldOff len F.t) (i : ℕ) :
    headerOffset o Bool.and (aPatterns p hG active uOff tOff hu ht) i =
      Off.eval p .A { view len F i with u := maskedControls p active (digit len F.u i) } := by
  unfold headerOffset
  rw [aPatterns_eq p hG hGK active uOff tOff hu ht]
  have hu' := headerWindow len F.u o uOff W i huOff (by simpa [hF.lu] using hu)
  have ht' := headerWindow len F.t o tOff W i htOff (by simpa [hF.lt] using ht)
  rw [hF.lu] at hu'
  rw [hF.lt] at ht'
  rw [hu', ht']
  rfl

/-- The concrete executed XOR offset reads actual target and dirty-control parities. -/
theorem yzHeaderOffset_eq (hF : F.Valid p len) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (o uOff yOff : ℕ)
    (hu : uOff + p.wc ≤ W) (hy : yOff + p.wy ≤ W)
    (huOff : o + uOff = fieldOff len F.u) (hyOff : o + yOff = fieldOff len F.y) (i : ℕ) :
    headerOffset o Bool.xor (yzPatterns p hG hK active uOff yOff hu hy) i =
      Off.eval p .YZ { view len F i with u := maskedControls p active (digit len F.u i) } := by
  unfold headerOffset
  rw [yzPatterns_eq p hG hK active uOff yOff hu hy]
  have hu' := headerWindow len F.u o uOff W i huOff (by simpa [hF.lu] using hu)
  have hy' := headerWindow len F.y o yOff W i hyOff (by simpa [hF.ly] using hy)
  rw [hF.lu] at hu'
  rw [hF.ly] at hy'
  rw [hu', hy']
  rfl

/-- The executed plain Z offset reads the active actual dirty-control parities. -/
theorem zHeaderOffset_eq (hF : F.Valid p len) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (o uOff : ℕ) (hu : uOff + p.wc ≤ W)
    (huOff : o + uOff = fieldOff len F.u) (i : ℕ) :
    headerOffset o (fun a _ => a) (zPatterns p hG active uOff hu) i =
      Off.eval p .Z { view len F i with u := maskedControls p active (digit len F.u i) } := by
  unfold headerOffset
  rw [zPatterns_eq p hG hK active uOff hu]
  have hu' := headerWindow len F.u o uOff W i huOff (by simpa [hF.lu] using hu)
  rw [hF.lu] at hu'
  rw [hu']
  rfl

/-- The executed plain Y offset reads the actual current target parities. -/
theorem yHeaderOffset_eq (hF : F.Valid p len) (hG : 0 < p.G) (hK : 0 < p.K)
    (o yOff : ℕ) (hy : yOff + p.wy ≤ W)
    (hyOff : o + yOff = fieldOff len F.y) (i : ℕ) :
    headerOffset o (fun a _ => a) (yPatterns p hK yOff hy) i =
      Off.eval p .Y (view len F i) := by
  unfold headerOffset
  rw [yPatterns_eq p hG hK yOff hy]
  have hy' := headerWindow len F.y o yOff W i hyOff (by simpa [hF.ly] using hy)
  rw [hF.ly] at hy'
  rw [hy']
  rfl

/-- Arbitrarily ordered source wires load from the actual current address bits. -/
theorem sourceHeaderOffset_eq (hG : 0 < p.G) (o : ℕ) (src : Fin p.n → Fin W) (i : ℕ) :
    headerOffset o (fun a _ => a)
        (plainPatterns (L := p.wc) (posC p) (fun c => some (src c))) i =
      placeVal p.n (posC p) (fun c => if hc : c < p.n then
        i.testBit (o + (src ⟨c, hc⟩).val) else false) := by
  unfold headerOffset
  rw [plainPatterns_eq (m := p.n) (L := p.wc) (posC_mono hG)
    (fun c hc => Nat.mul_lt_mul_of_pos_right hc hG) (fun c => some (src c))]
  unfold placeVal
  apply Finset.sum_congr rfl
  intro c hc
  have hc' : c < p.n := Finset.mem_range.mp hc
  simp [hc', selectorBit, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.add_comm]

end IntegerMultBounds.MathlibTM2.Routing
