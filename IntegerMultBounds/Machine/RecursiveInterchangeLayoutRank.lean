module

public import IntegerMultBounds.Machine.RecursiveInterchangeLayout

/-!
# Variable-width child descriptors

`RecursiveInterchangeLayout.child` selects the `i`th `H` and `j`th `D` sub-fields, each `b` digits
wide, of a parent of width `m·b`. A rank-`r` child of a variable-rank supplier interchanges `r`
consecutive sub-fields of each: `H` sub-fields `i, …, i+r-1` and `D` sub-fields `j, …, j+r-1`,
width `r·b`. `childR` is that descriptor. The spectators regroup into the same seven-factor form,
and every layout fact of `child` holds:
* `childR_index`: no symbol moves within a role stream;
* `childR_volume`, `childR_volume_div`: a child holds one role stream's volume;
* `childR_positive`, `childR_rows_divisible`: positivity and row divisibility at the next depth;
* `childR_spectators_bounded`: the regrouped spectator addresses lie in their ranges.

`child_eq_childR` recovers `child` at `r = 1`. `childR_width` gives the width ratio `r/m`, the size
premise of a variable-rank recurrence such as `BitRecurrence.bit_variable_closed`. As with
`child`, these are row-major address and size equalities, not tape operations.
-/

@[expose] public section

namespace IntegerMultBounds.Machine.RecursiveInterchangeLayout

/-- The rank-`r` child on `H` sub-fields `i, …, i+r-1` and `D` sub-fields `j, …, j+r-1` of a
parent of `m` sub-fields. -/
def childR (q roles b m r i j : ℕ) (v : Descriptor) : Descriptor where
  beforeRows := v.beforeRows
  rows := v.rows / roles
  beforeH := v.beforeH * q ^ (i * b)
  width := r * b
  between := q ^ ((m - i - r) * b) * v.between * q ^ (j * b)
  afterD := q ^ ((m - j - r) * b) * v.afterD

theorem split_power_rank (q b m r i : ℕ) (hi : i + r ≤ m) :
    q ^ (m * b) = q ^ (i * b) * q ^ (r * b) * q ^ ((m - i - r) * b) := by
  rw [← pow_add, ← pow_add]
  congr 1
  have hm : i + r + (m - i - r) = m := by omega
  nlinarith

/-- The rank-one child is `child`. -/
theorem child_eq_childR (q roles b : ℕ) (v : Descriptor) {m : ℕ} (i j : Fin m) :
    child q roles b v i j = childR q roles b m 1 i.val j.val v := by
  simp only [child, childR, one_mul]
  rw [show m - 1 - i.val = m - i.val - 1 by omega, show m - 1 - j.val = m - j.val - 1 by omega]

/-- The width of a rank-`r` child is `r/m` of the parent's. -/
theorem childR_width (q roles b m r i j : ℕ) (v : Descriptor) (hw : v.width = m * b) :
    (childR q roles b m r i j v).width * m = r * v.width := by
  simp only [childR, hw]
  ring

/-- Regrouping spectators does not move a single symbol within a role stream. -/
theorem childR_index (q roles b m r i j : ℕ) (v : Descriptor) (hi : i + r ≤ m) (hj : j + r ≤ m)
    (hw : v.width = m * b) (a row before hp h hs middle dp d ds after : ℕ) :
    index q (childR q roles b m r i j v) a row (before * q ^ (i * b) + hp) h
      ((hs * v.between + middle) * q ^ (j * b) + dp) d (ds * v.afterD + after) =
    index q (role v roles) a row before
      ((hp * q ^ (r * b) + h) * q ^ ((m - i - r) * b) + hs) middle
      ((dp * q ^ (r * b) + d) * q ^ ((m - j - r) * b) + ds) after := by
  simp only [index, childR, role, hw]
  nth_rw 1 [split_power_rank q b m r i hi]
  rw [split_power_rank q b m r j hj]
  ring

/-- A rank-`r` child holds the complete volume of one role stream. -/
theorem childR_volume (q roles b m r i j : ℕ) (v : Descriptor) (hi : i + r ≤ m) (hj : j + r ≤ m)
    (hw : v.width = m * b) : volume q (childR q roles b m r i j v) = volume q (role v roles) := by
  simp only [volume, childR, role, hw]
  nth_rw 1 [split_power_rank q b m r i hi]
  rw [split_power_rank q b m r j hj]
  ring

theorem childR_volume_div (q roles b m r i j : ℕ) (v : Descriptor) (hi : i + r ≤ m)
    (hj : j + r ≤ m) (hw : v.width = m * b) (hr : 0 < roles) (hdiv : roles ∣ v.rows) :
    volume q (childR q roles b m r i j v) = volume q v / roles := by
  rw [childR_volume q roles b m r i j v hi hj hw, ← role_volume_mul q roles v hdiv]
  exact (Nat.mul_div_cancel _ hr).symm

theorem childR_positive (q roles b m r i j : ℕ) (v : Descriptor) (hq : 0 < q) (hr : 0 < roles)
    (hdiv : roles ∣ v.rows) (hv : v.Positive) : (childR q roles b m r i j v).Positive := by
  rcases hv with ⟨ha, hrow, hb, hc, he⟩
  exact ⟨ha, Nat.div_pos (Nat.le_of_dvd hrow hdiv) hr, Nat.mul_pos hb (pow_pos hq _),
    Nat.mul_pos (Nat.mul_pos (pow_pos hq _) hc) (pow_pos hq _), Nat.mul_pos (pow_pos hq _) he⟩

/-- A rank-`r` child has precisely the row divisibility required at the next depth. -/
theorem childR_rows_divisible (q roles b m r i j k : ℕ) (v : Descriptor) (hr : 0 < roles)
    (hdiv : roles ^ (k + 1) ∣ v.rows) : roles ^ k ∣ (childR q roles b m r i j v).rows := by
  obtain ⟨n, hn⟩ := hdiv
  change roles ^ k ∣ v.rows / roles
  rw [hn, pow_succ]
  have he : roles ^ k * roles * n = (roles ^ k * n) * roles := by ring
  rw [he, Nat.mul_div_cancel _ hr]
  exact dvd_mul_right _ _

private theorem pack_lt' {a A b B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  nlinarith

/-- The regrouped spectator addresses lie in exactly their declared ranges. -/
theorem childR_spectators_bounded (q roles b m r i j : ℕ) (v : Descriptor)
    (before hp hs middle dp ds after : ℕ)
    (hb : before < v.beforeH) (hp' : hp < q ^ (i * b)) (hs' : hs < q ^ ((m - i - r) * b))
    (hc : middle < v.between) (dp' : dp < q ^ (j * b)) (ds' : ds < q ^ ((m - j - r) * b))
    (he : after < v.afterD) :
    before * q ^ (i * b) + hp < (childR q roles b m r i j v).beforeH ∧
    (hs * v.between + middle) * q ^ (j * b) + dp < (childR q roles b m r i j v).between ∧
    ds * v.afterD + after < (childR q roles b m r i j v).afterD :=
  ⟨pack_lt' hb hp', pack_lt' (pack_lt' hs' hc) dp', pack_lt' ds' he⟩

end IntegerMultBounds.Machine.RecursiveInterchangeLayout
