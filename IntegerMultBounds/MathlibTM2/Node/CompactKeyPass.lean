module

public import IntegerMultBounds.MathlibTM2.Node.KeyPass
public import IntegerMultBounds.MathlibTM2.Layer.CompactKey

/-!
# The key pass of the compact selected-bit XOR

The key pass of `IntegerMultBounds.MathlibTM2.Node.KeyPass` on the gadget fields: field `y`
gets `y ⊕ (x ∧ mm)` and every other field is copied, so the key of record `i` is the index
`xorIdx mm i` (`keyBitsAt_xor`); with the selected-bit mask this is the ideal map
(`idealIdx_eq_xorIdx`). `cxKey_exec`: the pass leaves the keyed records
`keyRecs (fieldsLen len) (xorPerm …) l`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {nf : ℕ} {len : Fin nf → ℕ} {F : Fields nf}

/-- The key symbols of record `i` are the bits of `xorIdx mm i`. -/
lemma keyBitsAt_xor {A : ℕ} (hX : XorFields len F) (mm i : ℕ) :
    keyBitsAt (A := A) F.y F.x len mm i = binSyms (fieldsLen len) (xorIdx len F mm i) := by
  have hkey : ∀ j, keyDig F.y F.x mm (fun g => digit len g i) j =
      digit len j (xorIdx len F mm i) := fun j => by
    unfold keyDig
    split_ifs with hj
    · subst hj; rw [digit_xorIdx_y hX]
    · rw [digit_xorIdx_ne hj]
  rw [keyBitsAt]
  simp only [hkey, binSyms_eq]
  rw [← List.map_flatMap, flatMap_binBits_digit]

/-- The keyed records of the key pass are `keyRecs` of the masked exclusive or. -/
lemma keyedFrom_xor {A q R : ℕ} (hX : XorFields len F) (hq : fieldOff len F.y + len F.y ≤ q)
    (mm : ℕ) (l : List (List (Fin (A + 4)))) (hl : l.length = R * 2 ^ q) :
    keyedFrom (keyBitsAt F.y F.x len mm) 0 l =
      keyRecs (fieldsLen len) (xorPerm (R := R) hX hq mm) l := by
  rw [keyedFrom_eq, keyRecs, hl]
  symm
  apply ofFn_eq_range_map
  intro j
  rw [Nat.zero_add, keyBitsAt_xor hX]
  rfl

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- **The compact key pass.** On the stream `l` of `R 2^q` records of `B ≥ 1` symbols, with the
fields at index `0` and the mask `mm` in `cm`, the key pass leaves in `src` the records keyed by
the masked exclusive or; every other register ends as it started. -/
theorem cxKey_exec (hX : XorFields len F) {q R : ℕ} (hq : fieldOff len F.y + len F.y ≤ q)
    {src acc ctrB tmp cm t0 t1 t2 st : Fin T}
    {cf : Fin nf → Fin T} (h : KeyRegs src acc ctrB tmp cm t0 t1 t2 st cf) {B : ℕ} (hB : 1 ≤ B)
    (l : List (List (Fin (A + 4)))) (hl : l.length = R * 2 ^ q) (hlB : ∀ r ∈ l, r.length = B)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = l.flatten) (hacc : S.R acc = [])
    (hctr : (S.R ctrB).length = B) (htmp : S.R tmp = []) {mm : ℕ}
    (hS : KeyState cf len (len F.y) cm t0 t1 t2 (fun _ => 0) mm S.R) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (keyPassAt F.y F.x src acc ctrB tmp cm t0 t1 t2 st cf) (mk v S)
        (1 + (l.length * (keyRecCost F.y len B + 1) + 1) +
          (2 * (l.length * ((∑ j, len j) + B)) + 2) + (4 * (∑ f, len f) + 4 * nf + 1))
        (mk v' { S with R := (Function.update S.R src
          (keyRecs (fieldsLen len) (xorPerm (R := R) hX hq mm) l).flatten) }) := by
  obtain ⟨v', hu, he⟩ := keyPassAt_exec body (Ne.symm hX.ne) h (len := len) hX.len_eq hB l hlB
    v S hsrc hacc hctr htmp hS
  rw [keyedFrom_xor hX hq mm l hl] at he
  exact ⟨v', hu, he⟩

end IntegerMultBounds.MathlibTM2.Node
