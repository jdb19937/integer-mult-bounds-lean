module

public import IntegerMultBounds.MathlibTM2.Cost.CompactTopBound

/-! Actual row reshaping and padding controls charged to their stream volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Node

private theorem compactRowVolume_bounds (n a r w : ℕ) (hrw : 1 ≤ r*w) :
    1 ≤ 2^(n+a)*(r*w) ∧ n+a ≤ 2^(n+a)*(r*w) ∧
      r*w ≤ 2^(n+a)*(r*w) ∧ 2^n*(r*w) ≤ 2^(n+a)*(r*w) := by
  have hp : 1 ≤ 2^(n+a) := Nat.one_le_pow _ _ (by decide)
  have hpos : 1 ≤ 2^(n+a)*(r*w) := Nat.mul_le_mul hp hrw
  have hadd : n+a ≤ 2^(n+a) := (Nat.lt_two_pow_self).le
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (Nat.le_add_right n a)
  exact ⟨hpos,hadd.trans (Nat.le_mul_of_pos_right _ hrw),
    Nat.le_mul_of_pos_left _ hp,Nat.mul_le_mul_right _ hpow⟩

/-- Moving the high spectators into row metadata costs linear stream volume. -/
theorem compactTopDownCost_linear (cfg : List ℕ) (n a r w : ℕ) (hrw : 1 ≤ r*w) :
    compactTopDownCost cfg n a r w ≤ topGetCost cfg + 64*(2^(n+a)*(r*w)) := by
  obtain ⟨hpos,haddr,hbase,hsmall⟩ := compactRowVolume_bounds n a r w hrw
  unfold compactTopDownCost
  nlinarith only [hpos,haddr,hbase,hsmall,Nat.zero_le n,Nat.zero_le a]

/-- Restoring high spectators has linear stream-volume cost. -/
theorem compactTopUpCost_linear (cfg : List ℕ) (n a r w : ℕ) (hrw : 1 ≤ r*w) :
    compactTopUpCost cfg n a r w ≤ topGetCost cfg + 64*(2^(n+a)*(r*w)) := by
  obtain ⟨hpos,haddr,hbase,hsmall⟩ := compactRowVolume_bounds n a r w hrw
  unfold compactTopUpCost
  nlinarith only [hpos,haddr,hsmall,Nat.zero_le n,Nat.zero_le a]

private theorem compactPaddingVolume_bounds (a R R₂ L : ℕ)
    (hR : 1 ≤ R) (hL : 1 ≤ L) (hcap : 2^a*R ≤ R₂) :
    1 ≤ R₂*L ∧ a ≤ R₂*L ∧ 2^a*R ≤ R₂*L ∧
      R₂-2^a*R ≤ R₂*L ∧ (R₂-2^a*R)*L ≤ R₂*L ∧ (2^a*R)*L ≤ R₂*L := by
  have hp : 1 ≤ 2^a := Nat.one_le_pow _ _ (by decide)
  have hbase : 1 ≤ 2^a*R := Nat.mul_le_mul hp hR
  have hR₂ : R₂ ≤ R₂*L := Nat.le_mul_of_pos_right _ hL
  have ha : a ≤ 2^a*R := (Nat.lt_two_pow_self).le.trans (Nat.le_mul_of_pos_right _ hR)
  exact ⟨(hbase.trans hcap).trans hR₂, (ha.trans hcap).trans hR₂,
    hcap.trans hR₂, (Nat.sub_le _ _).trans hR₂,
    Nat.mul_le_mul_right L (Nat.sub_le _ _), Nat.mul_le_mul_right L hcap⟩

/-- Padding charges every added row and all unary row counters. -/
theorem compactTopPadCost_linear (cfg : List ℕ) (a R R₂ L V : ℕ)
    (hR : 1 ≤ R) (hL : 1 ≤ L) (hcap : 2^a*R ≤ R₂) (hV : V ≤ R₂*L) :
    compactTopPadCost cfg a R R₂ L V ≤ 3*topGetCost cfg + 128*(R₂*L) := by
  obtain ⟨hpos,ha,hbase,hdiff,hdiffL,hbaseL⟩ := compactPaddingVolume_bounds a R R₂ L hR hL hcap
  unfold compactTopPadCost
  nlinarith only [hpos,ha,hbase,hdiff,hdiffL,hV]

/-- Unpadding is linear in the padded input volume, including discarded rows. -/
theorem compactTopUnpadCost_linear (cfg : List ℕ) (a R R₂ L V : ℕ)
    (hR : 1 ≤ R) (hL : 1 ≤ L) (hcap : 2^a*R ≤ R₂) (hV : V ≤ R₂*L) :
    compactTopUnpadCost cfg a R L V ≤ 2*topGetCost cfg + 64*(R₂*L) := by
  obtain ⟨hpos,ha,hbase,hdiff,hdiffL,hbaseL⟩ := compactPaddingVolume_bounds a R R₂ L hR hL hcap
  unfold compactTopUnpadCost
  nlinarith only [hpos,ha,hbase,hbaseL,hV]

end IntegerMultBounds.MathlibTM2.Cost
