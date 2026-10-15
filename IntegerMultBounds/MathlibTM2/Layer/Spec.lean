module

public import IntegerMultBounds.MathlibTM2.Layer.H0
public import IntegerMultBounds.Spec.SimultaneousLayer

/-!
# The vendored layer specification

The vendored specification `Spec.SignedRingProduct.hadamard` acts on arrays indexed by natural
addresses, selecting one bit in each of `D` address chunks. Viewing an array as an array on
`D` active bits — the spectator is the address, whose selected bits are overwritten by the
active bits — the vendored `hadamard` is `Hfull` read at the address's own selected bits
(`hadamard_eq_Hfull`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Spec.SignedRingProduct

variable {r : ℕ}

/-- An address array viewed on its `D` selected bits. -/
noncomputable def specView (D K ρ S : ℕ) (z : ℕ → Fin r → ℂ) : Arr (ℕ × Fin r) D :=
  fun p => z (setSel (D := D) K ρ S p.1.1 (fun j => p.2 j = 1)) p.1.2

/-- The selected bits of an address as active bits. -/
def selBits (D K ρ S : ℕ) (x : ℕ) : Fin D → ZMod 2 := fun j => if selBit K ρ S x j then 1 else 0

/-- The vendored `hadamard` is `Hfull` on the selected-bit view. -/
lemma Hfull_eq_Hl {X : Type} (D : ℕ) (f : Arr X D) : Hfull X D f = Hl X (List.finRange D) f := by
  rw [Hfull, Hl, List.ofFn_eq_map]

/-- Bit vectors over `ZMod 2` as Boolean selections. -/
def boolEquiv (D : ℕ) : (Fin D → ZMod 2) ≃ (Fin D → Bool) where
  toFun b j := b j = 1
  invFun c j := if c j then 1 else 0
  left_inv b := by
    funext j; rcases zmod2_cases (b j) with h | h <;> simp [h]
  right_inv c := by funext j; by_cases h : c j <;> simp [h]

lemma sgn_card (D : ℕ) (a b : Fin D → ZMod 2) :
    sgn (List.finRange D) a b =
      (-1 : ℂ) ^ (Finset.univ.filter fun j => (a j = 1 ∧ b j = 1 : Prop)).card := by
  rw [sgn, ← List.ofFn_eq_map, List.prod_ofFn, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const]

theorem hadamard_eq_Hfull (D K ρ S : ℕ) (z : ℕ → Fin r → ℂ) (x : ℕ) (k : Fin r) :
    hadamard D K ρ S z x k = Hfull (ℕ × Fin r) D (specView D K ρ S z) ((x, k), selBits D K ρ S x) := by
  rw [Hfull_eq_Hl, Hl_apply _ (List.nodup_finRange D), List.length_finRange]
  have hall : Finset.univ.filter (agree (List.finRange D) (selBits D K ρ S x)) = Finset.univ := by
    ext b; simp [agree]
  rw [hall, hadamard]
  congr 1
  rw [← (boolEquiv D).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  rw [sgn_card]
  have hb : (fun j => ((boolEquiv D).symm c j = 1 : Prop)) = fun j => c j = true := by
    funext j; by_cases h : c j <;> simp [boolEquiv, h]
  simp only [specView]
  congr 2
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, selBits, boolEquiv, Equiv.coe_fn_symm_mk,
      Bool.and_eq_true]
    by_cases h1 : selBit K ρ S x j <;> by_cases h2 : c j <;> simp [h1, h2]
  · congr 1
    funext j
    simp [boolEquiv]

end IntegerMultBounds.MathlibTM2.Layer
