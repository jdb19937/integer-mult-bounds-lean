module

public import IntegerMultBounds.MathlibTM2.Routing.PackedShear
public import IntegerMultBounds.Compact.Density

/-!
# Exceptional density with complete spectator fields

A complete nonempty source/spectator factor does not alter the fraction of bad
packed addresses. Reindexing the complete rectangle does not alter it either.
No assumption about source values, initialized scratch, or source order enters
this count. Physical extraction and repair remain separate machine obligations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.Packed

open IntegerMultBounds.Compact

/-- Reindexing all addresses preserves the exceptional fraction. -/
theorem badFraction_equiv {A D : Type*} (e : A ≃ D) (P : D → Prop) :
    badFraction (fun x => P (e x)) = badFraction P := by
  let f : {x : A // ¬P (e x)} ≃ {x : D // ¬P x} := {
    toFun := fun x => ⟨e x.val, x.property⟩
    invFun := fun x => ⟨e.symm x.val, by simpa using x.property⟩
    left_inv := fun x => by simp
    right_inv := fun x => by simp }
  unfold badFraction
  rw [Nat.card_congr f, Nat.card_congr e]

/-- Keeping every spectator value, rather than fixing one, leaves density unchanged. -/
theorem badFraction_prod (C : Type*) [Fintype C] [Nonempty C] {D : Type*}
    (P : D → Prop) : badFraction (fun x : C × D => P x.2) = badFraction P := by
  let e : {x : C × D // ¬P x.2} ≃ C × {x : D // ¬P x} := {
    toFun := fun x => (x.val.1, ⟨x.val.2, x.property⟩)
    invFun := fun x => ⟨(x.1, x.2.val), x.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc : (Nat.card C : ℝ) ≠ 0 := by
    have : 0 < Fintype.card C := Fintype.card_pos
    rw [Nat.card_eq_fintype_card]
    positivity
  unfold badFraction
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_left _ _ hc

/-- The union bound counts the full source/target/borrowed/spectator rectangle. -/
theorem program_bad_fraction_le (C : Type*) [Fintype C] [Nonempty C]
    (B L : ℤ) (hB : 0 < B) (hL : 0 < L) (hguard : 4 * B ≤ L) (n : ℕ) :
    badFraction (fun x : C × LateAddress B L n => lateGood B L n x.2) ≤
      2 * (n : ℝ) / B + 8 * n * B / (2 * L) := by
  rw [badFraction_prod]
  exact late_bad_fraction_le B L hB hL hguard n

/-- Uniform repair density on any complete encoding of the routing rectangle.
The radix hypotheses are explicit, so the eventual choice of guard widths must
prove them before using this estimate. -/
theorem encoded_repair_density {A C : Type*} [Fintype C] [Nonempty C]
    (B L : ℤ) (hB : 0 < B) (hL : 0 < L) (hguard : 4 * B ≤ L) (n : ℕ)
    (e : A ≃ C × LateAddress B L n) (p : ℝ) (hp : 0 < p)
    (hn : (n : ℝ) ≤ p) (hradix : 64 * p ^ 4 ≤ (B : ℝ))
    (hgap : 1024 * p ^ 4 ≤ 2 * (L : ℝ) / B) :
    badFraction (fun x => lateGood B L n (e x).2) ≤ 5 / (128 * p ^ 3) := by
  rw [badFraction_equiv e (fun x => lateGood B L n x.2)]
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hB)
  have hl : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have hratio : 8 * (n : ℝ) * B / (2 * L) = 8 * n / (2 * (L : ℝ) / B) := by
    field_simp
  calc
    _ ≤ 2 * (n : ℝ) / B + 8 * n * B / (2 * L) :=
      program_bad_fraction_le C B L hB hL hguard n
    _ = 2 * (n : ℝ) / B + 8 * n / (2 * (L : ℝ) / B) := by rw [hratio]
    _ ≤ _ := repair_density_bound p n B (2 * (L : ℝ) / B)
      hp (by positivity) hn hradix hgap

end IntegerMultBounds.MathlibTM2.Routing.Packed
