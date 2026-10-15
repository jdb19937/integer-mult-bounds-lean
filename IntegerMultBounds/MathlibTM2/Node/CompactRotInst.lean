module

public import IntegerMultBounds.MathlibTM2.Node.OffPrep

/-!
# Instantiating the rotation pass on the compact-control offsets

The rotation pass of `Node/RotGen.lean` rotates a field `tf` by an offset `off` that may depend
only on the fields above `tf` (`HighOff len tf off`) and is bounded by `2 ^ len tf`, after a
preparation satisfying `PrepSpec`. This file supplies all three for the four offsets of the
compact slot XOR (`IntegerMultBounds.MathlibTM2.Layer.CompactXor.core`):

* `highOff_offYW`, `highOff_offYb`, `highOff_offBb`, `highOff_offBx`: each offset is built from
  the digits of fields lying above the rotated one, so it is a `HighOff`
  (`highOff_of_above`, `highOff_of_above₂`).
* `offYW_lt`, `offYb_lt`, `offBb_lt`, `offBx_lt`: the bounds `2 ^ ((n + 1) K)` for the rotations
  of the slot and `2 ^ (n G)` for the rotations of the borrow field.
* `prepSpec_offYW`, `prepSpec_offYb`, `prepSpec_offBb`, `prepSpec_offBx`: the preparation
  contract `prepOff_spec` with the concrete parameters of each offset
  (`offYW_offSum`, `offYb_offSum`, `offBb_offSum`, `offBx_offSum`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Layer.CompactXor

/-! ### Offsets depending only on the fields above the rotated one -/

section High

variable {nf : ℕ} (len : Fin nf → ℕ)

/-- A field above `tf` is determined by the bits above `tf`. -/
lemma dig_eq_of_div_eq (tf A : Fin nf) (hAbove : foff len tf + len tf ≤ foff len A) {i j : ℕ}
    (hij : i / 2 ^ (foff len tf + len tf) = j / 2 ^ (foff len tf + len tf)) :
    dig len A i = dig len A j := by
  have key : ∀ k, k / 2 ^ foff len A =
      k / 2 ^ (foff len tf + len tf) / 2 ^ (foff len A - (foff len tf + len tf)) := by
    intro k
    rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_sub_of_le hAbove]
  unfold dig
  rw [key i, key j, hij]

/-- An offset computed from one field above `tf`. -/
lemma highOff_of_above (tf A : Fin nf) (hAbove : foff len tf + len tf ≤ foff len A)
    (F : ℕ → ℕ) : HighOff len tf (fun i => F (dig len A i)) := by
  intro i j hij
  simp only [dig_eq_of_div_eq len tf A hAbove hij]

/-- An offset computed from two fields above `tf`. -/
lemma highOff_of_above₂ (tf A D : Fin nf) (hAbove : foff len tf + len tf ≤ foff len A)
    (hDAbove : foff len tf + len tf ≤ foff len D) (F : ℕ → ℕ → ℕ) :
    HighOff len tf (fun i => F (dig len A i) (dig len D i)) := by
  intro i j hij
  simp only [dig_eq_of_div_eq len tf A hAbove hij, dig_eq_of_div_eq len tf D hDAbove hij]

variable (T Y B A : Fin nf) (K ρ G n oA sA : ℕ)

lemma highOff_offYW (hAbove : foff len Y + len Y ≤ foff len A)
    (hTAbove : foff len Y + len Y ≤ foff len T) :
    HighOff len Y (offYW len T K ρ G n A oA sA) := by
  intro i j hij
  simp only [offYW, bitAt, digAt, dig_eq_of_div_eq len Y A hAbove hij,
    dig_eq_of_div_eq len Y T hTAbove hij]

lemma highOff_offYb (hAbove : foff len Y + len Y ≤ foff len A) :
    HighOff len Y (offYb len K ρ n A oA sA) := by
  intro i j hij
  simp only [offYb, bitAt, dig_eq_of_div_eq len Y A hAbove hij]

lemma highOff_offBb (hAbove : foff len B + len B ≤ foff len A) :
    HighOff len B (offBb len G n A oA sA) := by
  intro i j hij
  simp only [offBb, bitAt, dig_eq_of_div_eq len B A hAbove hij]

lemma highOff_offBx (hAbove : foff len B + len B ≤ foff len A)
    (hYAbove : foff len B + len B ≤ foff len Y) :
    HighOff len B (offBx len Y K ρ G n A oA sA) := by
  intro i j hij
  simp only [offBx, bitAt, dig_eq_of_div_eq len B A hAbove hij,
    dig_eq_of_div_eq len B Y hYAbove hij]

end High

/-! ### Bounds on the offsets -/

section Bounds

variable {nf : ℕ} (len : Fin nf → ℕ) (T Y A : Fin nf) (K ρ G n oA sA : ℕ)

lemma offYW_lt (hρ : ρ < K) (hGK : G + 1 ≤ K) (i : ℕ) :
    offYW len T K ρ G n A oA sA i < 2 ^ ((n + 1) * K) := by
  rw [offYW_eq len A A oA sA i]
  calc _ < 2 ^ (ρ + n * K) :=
        offSum_lt _ ρ K (fun c => coefU_lt len false true A A T oA sA ρ K G c i K
          (by rw [ite_eq_left (rfl : (true : Bool) = true)]; exact hGK)) n
    _ ≤ 2 ^ ((n + 1) * K) :=
        Nat.pow_le_pow_right (by norm_num) (by rw [Nat.add_mul, one_mul]; omega)

lemma offYb_lt (hρ : ρ < K) (hK : 1 ≤ K) (i : ℕ) :
    offYb len K ρ n A oA sA i < 2 ^ ((n + 1) * K) := by
  rw [offYb_eq len A A A oA sA 0 i]
  calc _ < 2 ^ (ρ + n * K) :=
        offSum_lt _ ρ K (fun c => coefU_lt len false false A A A oA sA ρ K 0 c i K
          (by rw [ite_eq_right (by decide : ¬ ((false : Bool) = true))]; exact hK)) n
    _ ≤ 2 ^ ((n + 1) * K) :=
        Nat.pow_le_pow_right (by norm_num) (by rw [Nat.add_mul, one_mul]; omega)

lemma offBb_lt (hG : 1 ≤ G) (i : ℕ) : offBb len G n A oA sA i < 2 ^ (n * G) := by
  rw [offBb_eq len A A A oA sA 0 0 i]
  have h := offSum_lt _ 0 G (fun c => coefU_lt len false false A A A oA sA 0 0 G c i G
    (by rw [ite_eq_right (by decide : ¬ ((false : Bool) = true))]; exact hG)) n
  rwa [zero_add] at h

lemma offBx_lt (hG : 1 ≤ G) (i : ℕ) : offBx len Y K ρ G n A oA sA i < 2 ^ (n * G) := by
  rw [offBx_eq len A A oA sA i]
  have h := offSum_lt _ 0 G (fun c => coefU_lt len true false A Y A oA sA ρ K G c i G
    (by rw [ite_eq_right (by decide : ¬ ((false : Bool) = true))]; exact hG)) n
  rwa [zero_add] at h

end Bounds

/-! ### The preparation parameters of each offset -/

section Params

variable {nf : ℕ} (len : Fin nf → ℕ) (fA fY fT : Fin nf) (oA sA : ℕ)

/-- `offYW`: control field `fA`, digit field `fT`, output offset `ρ`, stride `K = 1 + G + pad`. -/
lemma offYW_offSum (K ρ G n : ℕ) (hGK : G + 1 ≤ K) (i : ℕ) :
    offYW len fT K ρ G n fA oA sA i =
      offSum (fun c => coefU len false true fA fY fT oA sA ρ K G c i) ρ
        (1 + (if (true : Bool) then G else 0) + (K - 1 - G)) n := by
  rw [ite_eq_left (rfl : (true : Bool) = true), show 1 + G + (K - 1 - G) = K by omega]
  exact offYW_eq len fA fY oA sA i

/-- `offYb`: control field `fA`, output offset `ρ`, stride `K = 1 + pad`. -/
lemma offYb_offSum (K ρ G n : ℕ) (hK : 1 ≤ K) (i : ℕ) :
    offYb len K ρ n fA oA sA i =
      offSum (fun c => coefU len false false fA fY fT oA sA ρ K G c i) ρ
        (1 + (if (false : Bool) then G else 0) + (K - 1)) n := by
  rw [ite_eq_right (by decide : ¬ ((false : Bool) = true)), show 1 + 0 + (K - 1) = K by omega]
  exact offYb_eq len fA fY fT oA sA G i

/-- `offBb`: control field `fA`, output offset `0`, stride `G = 1 + pad`; the slot parameters
`oY`, `KY` are unused. -/
lemma offBb_offSum (oY KY G n : ℕ) (hG : 1 ≤ G) (i : ℕ) :
    offBb len G n fA oA sA i =
      offSum (fun c => coefU len false false fA fY fT oA sA oY KY G c i) 0
        (1 + (if (false : Bool) then G else 0) + (G - 1)) n := by
  rw [ite_eq_right (by decide : ¬ ((false : Bool) = true)), show 1 + 0 + (G - 1) = G by omega]
  exact offBb_eq len fA fY fT oA sA oY KY i

/-- `offBx`: control field `fA` XORed with the slot `fY` at `ρ + cK`, output offset `0`, stride
`G = 1 + pad`. -/
lemma offBx_offSum (K ρ G n : ℕ) (hG : 1 ≤ G) (i : ℕ) :
    offBx len fY K ρ G n fA oA sA i =
      offSum (fun c => coefU len true false fA fY fT oA sA ρ K G c i) 0
        (1 + (if (false : Bool) then G else 0) + (G - 1)) n := by
  rw [ite_eq_right (by decide : ¬ ((false : Bool) = true)), show 1 + 0 + (G - 1) = G by omega]
  exact offBx_eq len fA fT oA sA i

end Params

/-! ### The preparation contracts of the four rotations -/

section Spec

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U) {nf : ℕ} (len : Fin nf → ℕ)

/-- Rotation of the slot `fY` by `offYW` (control field `fA`, digit field `fT`). -/
theorem prepSpec_offYW {ι : RotGReg nf 8 9 → Fin T} (hι : Function.Injective ι)
    (fA fY fT : Fin nf) (hAY : fA ≠ fY) (hAT : fA ≠ fT) (hYT : fY ≠ fT) (oA sA K ρ G n : ℕ)
    (hA : oA + n * sA ≤ len fA) (hY : len fY = (n + 1) * K) (hT : len fT = n * G)
    (hρ : ρ < K) (hGK : G + 1 ≤ K) :
    PrepSpec body (prepOff false true (ι ∘ embedP fA fY fT)) (fun g => ι (.fld g)) len (len fY)
      (fun r => ι (RotGReg.rsRegG fY r)) (fun r => ι (.spare r))
      (rsrcR fY (offYW len fT K ρ G n fA oA sA))
      (fun s => ι (.scr s)) (fun q => ι (.prm q)) (prmP (len fY) ρ oA ρ sA K G n (K - 1 - G))
      (prepCost true (pdataP len fA fY fT (len fY) ρ oA ρ sA K G n (K - 1 - G) 0) (len fY)) :=
  prepOff_spec body len hι fY fA fY fT hAY hAT hYT false true ρ oA ρ sA K G n (K - 1 - G) hA
    (by rw [hY, Nat.add_mul, one_mul]; omega) (fun _ => hT.ge) _
    (offYW_offSum len fA fY fT oA sA K ρ G n hGK)

/-- Rotation of the slot `fY` by `offYb` (control field `fA`; `fT` is any third field). -/
theorem prepSpec_offYb {ι : RotGReg nf 8 9 → Fin T} (hι : Function.Injective ι)
    (fA fY fT : Fin nf) (hAY : fA ≠ fY) (hAT : fA ≠ fT) (hYT : fY ≠ fT) (oA sA K ρ G n : ℕ)
    (hA : oA + n * sA ≤ len fA) (hY : len fY = (n + 1) * K) (hρ : ρ < K) (hK : 1 ≤ K) :
    PrepSpec body (prepOff false false (ι ∘ embedP fA fY fT)) (fun g => ι (.fld g)) len (len fY)
      (fun r => ι (RotGReg.rsRegG fY r)) (fun r => ι (.spare r))
      (rsrcR fY (offYb len K ρ n fA oA sA))
      (fun s => ι (.scr s)) (fun q => ι (.prm q)) (prmP (len fY) ρ oA ρ sA K G n (K - 1))
      (prepCost false (pdataP len fA fY fT (len fY) ρ oA ρ sA K G n (K - 1) 0) (len fY)) :=
  prepOff_spec body len hι fY fA fY fT hAY hAT hYT false false ρ oA ρ sA K G n (K - 1) hA
    (by rw [hY, Nat.add_mul, one_mul]; omega) (fun h => nomatch h) _
    (offYb_offSum len fA fY fT oA sA K ρ G n hK)

/-- Rotation of the borrow field `fB` by `offBb` with control field `fA` (bits at `oA + c sA`);
`fY` and `fT` are any two further fields, `fY` long enough for the unused slot parameters. -/
theorem prepSpec_offBb {ι : RotGReg nf 8 9 → Fin T} (hι : Function.Injective ι)
    (fB fA fY fT : Fin nf) (hAY : fA ≠ fY) (hAT : fA ≠ fT) (hYT : fY ≠ fT)
    (oA sA oY KY G n : ℕ) (hA : oA + n * sA ≤ len fA) (hY : oY + n * KY ≤ len fY)
    (hG : 1 ≤ G) :
    PrepSpec body (prepOff false false (ι ∘ embedP fA fY fT)) (fun g => ι (.fld g)) len (len fB)
      (fun r => ι (RotGReg.rsRegG fB r)) (fun r => ι (.spare r))
      (rsrcR fB (offBb len G n fA oA sA))
      (fun s => ι (.scr s)) (fun q => ι (.prm q)) (prmP (len fB) 0 oA oY sA KY G n (G - 1))
      (prepCost false (pdataP len fA fY fT (len fB) 0 oA oY sA KY G n (G - 1) 0) (len fB)) :=
  prepOff_spec body len hι fB fA fY fT hAY hAT hYT false false 0 oA oY sA KY G n (G - 1) hA hY
    (fun h => nomatch h) _ (offBb_offSum len fA fY fT oA sA oY KY G n hG)

/-- Rotation of the borrow field `fB` by `offBx` (control field `fA` XORed with the slot `fY`;
`fT` is any third field). -/
theorem prepSpec_offBx {ι : RotGReg nf 8 9 → Fin T} (hι : Function.Injective ι)
    (fB fA fY fT : Fin nf) (hAY : fA ≠ fY) (hAT : fA ≠ fT) (hYT : fY ≠ fT) (oA sA K ρ G n : ℕ)
    (hA : oA + n * sA ≤ len fA) (hY : len fY = (n + 1) * K) (hρ : ρ < K) (hG : 1 ≤ G) :
    PrepSpec body (prepOff true false (ι ∘ embedP fA fY fT)) (fun g => ι (.fld g)) len (len fB)
      (fun r => ι (RotGReg.rsRegG fB r)) (fun r => ι (.spare r))
      (rsrcR fB (offBx len fY K ρ G n fA oA sA))
      (fun s => ι (.scr s)) (fun q => ι (.prm q)) (prmP (len fB) 0 oA ρ sA K G n (G - 1))
      (prepCost false (pdataP len fA fY fT (len fB) 0 oA ρ sA K G n (G - 1) 0) (len fB)) :=
  prepOff_spec body len hι fB fA fY fT hAY hAT hYT true false 0 oA ρ sA K G n (G - 1) hA
    (by rw [hY, Nat.add_mul, one_mul]; omega) (fun h => nomatch h) _
    (offBx_offSum len fA fY fT oA sA K ρ G n hG)

end Spec

end IntegerMultBounds.MathlibTM2.Node
