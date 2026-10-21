module

public import IntegerMultBounds.Machine.RecursiveInterchangeLayout

/-!
# Atom views of the reversed interchange

The stage-2 machine keeps the seven-factor descriptor of the recursive interchange machine,
with each address field made of `n` atoms of `w` digits (`v.width = n w`). Its target is the
reversed interchange `F_n`: the head becomes the tail with its atoms in reverse order, and the
tail becomes the head reversed (`RevT`), atom `p` of one field pairing with atom `n - 1 - p` of the
other (`revAtoms`).

Every call of the family is a view (`sub s c`): head atoms `s, …, s + c - 1` and their partner
tail atoms `n - s - c, …, n - s - 1`, the other atoms regrouped into the spectators, with no
symbol moved (`sub_index`, `sub_volume`). The block child of rank `r` over `f` atoms per
coordinate is `sub 0 (r f)` of the node's field; the remainder is `sub 0 δ` and the node's middle
`sub δ (n - δ)`; a leaf is `sub i 1`.

`revT_partition`: the reversed interchanges of the views `sub 0 c` and `sub c (n - c)`, in
either order, make the reversed interchange of the whole field. By induction, so do the views of
any partition into consecutive blocks.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine

open IntegerMultBounds.Machine.RecursiveInterchangeLayout

/-! ### Atom reversal -/

/-- The `k` base-`Q` digits of `h`, least significant first, written most significant first. -/
def revAtoms (Q : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, h => h % Q * Q ^ k + revAtoms Q k (h / Q)

theorem revAtoms_lt {Q : ℕ} (hQ : 0 < Q) : ∀ k h, revAtoms Q k h < Q ^ k
  | 0, _ => by simp [revAtoms]
  | k + 1, h => by
    have ih := revAtoms_lt hQ k (h / Q)
    have hm := Nat.mod_lt h hQ
    rw [revAtoms, pow_succ]
    nlinarith [Nat.zero_le (h % Q), pow_pos hQ k]

/-- Reversal of a concatenation: `x` of `k₁` atoms before `y` of `k₂` atoms becomes `y` reversed
before `x` reversed. -/
theorem revAtoms_append {Q : ℕ} (hQ : 0 < Q) (k₁ : ℕ) : ∀ (k₂ x y : ℕ), y < Q ^ k₂ →
    revAtoms Q (k₁ + k₂) (x * Q ^ k₂ + y) = revAtoms Q k₂ y * Q ^ k₁ + revAtoms Q k₁ x
  | 0, x, y, hy => by
    have : y = 0 := by simpa using hy
    simp [revAtoms, this]
  | k₂ + 1, x, y, hy => by
    have hdiv : (x * Q ^ (k₂ + 1) + y) / Q = x * Q ^ k₂ + y / Q := by
      rw [pow_succ, ← mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ hQ, Nat.add_comm]
    have hmod : (x * Q ^ (k₂ + 1) + y) % Q = y % Q := by
      rw [pow_succ, ← mul_assoc, Nat.add_comm, Nat.add_mul_mod_self_right]
    have hy' : y / Q < Q ^ k₂ := by
      rw [Nat.div_lt_iff_lt_mul hQ]; rwa [← pow_succ]
    rw [show k₁ + (k₂ + 1) = (k₁ + k₂) + 1 by ring, revAtoms, hdiv, hmod,
      revAtoms_append hQ k₁ k₂ x (y / Q) hy', revAtoms]
    rw [pow_add]
    ring

theorem revAtoms_revAtoms {Q : ℕ} (hQ : 0 < Q) : ∀ k h, h < Q ^ k → revAtoms Q k (revAtoms Q k h) = h
  | 0, h, hh => by simp at hh; simp [revAtoms, hh]
  | k + 1, h, hh => by
    have hlt := revAtoms_lt hQ k (h / Q)
    have hm := Nat.mod_lt h hQ
    have e := revAtoms_append hQ 1 k (h % Q) (revAtoms Q k (h / Q)) hlt
    rw [show 1 + k = k + 1 by ring] at e
    have hdef : revAtoms Q (k + 1) h = h % Q * Q ^ k + revAtoms Q k (h / Q) := rfl
    rw [hdef, e, revAtoms_revAtoms hQ k (h / Q) (by
      rw [Nat.div_lt_iff_lt_mul hQ]; rwa [← pow_succ]), show revAtoms Q 1 (h % Q) = h % Q by
      simp [revAtoms, Nat.mod_eq_of_lt hm]]
    rw [pow_one, Nat.mul_comm]
    exact Nat.div_add_mod h Q

/-! ### Views -/

/-- The view of head atoms `s, …, s + c - 1` and tail atoms `n - s - c, …, n - s - 1`: the
other head atoms go before the head or between, the other tail atoms between or after. -/
def sub (q w n s c : ℕ) (v : Descriptor) : Descriptor where
  beforeRows := v.beforeRows
  rows := v.rows
  beforeH := v.beforeH * q ^ (s * w)
  width := c * w
  between := q ^ ((n - s - c) * w) * v.between * q ^ ((n - s - c) * w)
  afterD := q ^ (s * w) * v.afterD

theorem split_atoms (q w n s c : ℕ) (h : s + c ≤ n) :
    q ^ (n * w) = q ^ (s * w) * q ^ (c * w) * q ^ ((n - s - c) * w) := by
  rw [← pow_add, ← pow_add]
  congr 1
  rw [← Nat.add_mul, ← Nat.add_mul]
  congr 1
  omega

theorem sub_volume (q w n s c : ℕ) (v : Descriptor) (hw : v.width = n * w) (h : s + c ≤ n) :
    volume q (sub q w n s c v) = volume q v := by
  simp only [volume, sub, hw, split_atoms q w n s c h]
  ring

/-- **The view moves no symbol.** The head `hp | hc | hs` (`s`, `c`, `n - s - c` atoms) and the
tail `dp | dc | ds` (`n - s - c`, `c`, `s` atoms) of the parent are the child's head `hc` and
tail `dc`, with `hp` before and `hs, dp` between and `ds` after. -/
theorem sub_index (q w n s c : ℕ) (v : Descriptor) (hw : v.width = n * w) (h : s + c ≤ n)
    (a row before hp hc hs mid dp dc ds after : ℕ) :
    index q (sub q w n s c v) a row (before * q ^ (s * w) + hp) hc
      ((hs * v.between + mid) * q ^ ((n - s - c) * w) + dp) dc (ds * v.afterD + after) =
    index q v a row before ((hp * q ^ (c * w) + hc) * q ^ ((n - s - c) * w) + hs) mid
      ((dp * q ^ (c * w) + dc) * q ^ (s * w) + ds) after := by
  simp only [index, sub, hw, split_atoms q w n s c h]
  ring

/-! ### The reversed interchange -/

/-- `y` is the reversed interchange of `x` on every address of the descriptor `v` whose fields
have `n` atoms of `w` digits. -/
def RevT {α : Type*} (q w n : ℕ) (v : Descriptor) (x y : ℕ → α) : Prop :=
  ∀ a < v.beforeRows, ∀ row < v.rows, ∀ before < v.beforeH, ∀ h < q ^ (n * w),
    ∀ mid < v.between, ∀ d < q ^ (n * w), ∀ after < v.afterD,
      y (index q v a row before h mid d after) =
        x (index q v a row before (revAtoms (q ^ w) n d) mid (revAtoms (q ^ w) n h) after)

private theorem pack_lt {a A b B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  nlinarith

/-- **A view's reversed interchange on the parent.** If `y` is the reversed interchange of `x` on
the view `sub s c`, then on the parent the middle blocks `hc`, `dc` are exchanged reversed and
every other atom stays. -/
theorem revT_sub_apply {α : Type*} {q w n s c : ℕ} (hq : 0 < q) {v : Descriptor}
    (hw : v.width = n * w) (h : s + c ≤ n) {x y : ℕ → α} (hT : RevT q w c (sub q w n s c v) x y)
    {a row before hp hc hs mid dp dc ds after : ℕ} (ha : a < v.beforeRows) (hrow : row < v.rows)
    (hbefore : before < v.beforeH) (hhp : hp < q ^ (s * w)) (hhc : hc < q ^ (c * w))
    (hhs : hs < q ^ ((n - s - c) * w)) (hmid : mid < v.between) (hdp : dp < q ^ ((n - s - c) * w))
    (hdc : dc < q ^ (c * w)) (hds : ds < q ^ (s * w)) (hafter : after < v.afterD) :
    y (index q v a row before ((hp * q ^ (c * w) + hc) * q ^ ((n - s - c) * w) + hs) mid
        ((dp * q ^ (c * w) + dc) * q ^ (s * w) + ds) after) =
      x (index q v a row before ((hp * q ^ (c * w) + revAtoms (q ^ w) c dc) * q ^ ((n - s - c) * w) + hs)
        mid ((dp * q ^ (c * w) + revAtoms (q ^ w) c hc) * q ^ (s * w) + ds) after) := by
  have hQ : 0 < q ^ w := pow_pos hq w
  have hrev (k z : ℕ) : revAtoms (q ^ w) c z < q ^ (c * w) := by
    rw [Nat.mul_comm, pow_mul]; exact revAtoms_lt hQ c z
  rw [← sub_index q w n s c v hw h, ← sub_index q w n s c v hw h]
  have hbetween : (hs * v.between + mid) * q ^ ((n - s - c) * w) + dp <
      (sub q w n s c v).between := by
    show _ < q ^ ((n - s - c) * w) * v.between * q ^ ((n - s - c) * w)
    exact pack_lt (pack_lt hhs hmid) hdp
  have hT' := hT a ha row hrow (before * q ^ (s * w) + hp) (pack_lt hbefore hhp) hc
    (by rw [Nat.mul_comm c, pow_mul]; rwa [← pow_mul, Nat.mul_comm]) _ hbetween dc
    (by rw [Nat.mul_comm c, pow_mul]; rwa [← pow_mul, Nat.mul_comm]) (ds * v.afterD + after)
    (by show _ < q ^ (s * w) * v.afterD; exact pack_lt hds hafter)
  rw [hT']

/-- **The partition.** The reversed interchanges of the first `c` atom pairs and of the other
`n - c` pairs, in this order, make the reversed interchange of the whole field. -/
theorem revT_partition {α : Type*} {q w n c : ℕ} (hq : 0 < q) {v : Descriptor} (hw : v.width = n * w)
    (hc : c ≤ n) {x y z : ℕ → α} (h₁ : RevT q w c (sub q w n 0 c v) x y)
    (h₂ : RevT q w (n - c) (sub q w n c (n - c) v) y z) : RevT q w n v x z := by
  have hQ : 0 < q ^ w := pow_pos hq w
  have hp (k : ℕ) : q ^ (k * w) = (q ^ w) ^ k := by rw [Nat.mul_comm, pow_mul]
  intro a ha row hrow before hbefore h hh mid hmid d hd after hafter
  -- split the head after `c` atoms and the tail before its last `c` atoms
  have hsplit : q ^ (n * w) = q ^ (c * w) * q ^ ((n - c) * w) := by
    rw [← pow_add, ← Nat.add_mul, Nat.add_sub_cancel' hc]
  set H₁ := h / q ^ ((n - c) * w)
  set H₂ := h % q ^ ((n - c) * w)
  set D₁ := d / q ^ (c * w)
  set D₂ := d % q ^ (c * w)
  have hpos₁ : 0 < q ^ ((n - c) * w) := pow_pos hq _
  have hpos₂ : 0 < q ^ (c * w) := pow_pos hq _
  have hH : h = H₁ * q ^ ((n - c) * w) + H₂ := by rw [Nat.mul_comm]; exact (Nat.div_add_mod _ _).symm
  have hD : d = D₁ * q ^ (c * w) + D₂ := by rw [Nat.mul_comm]; exact (Nat.div_add_mod _ _).symm
  have hH₁ : H₁ < q ^ (c * w) := by
    rw [Nat.div_lt_iff_lt_mul hpos₁, ← hsplit]; exact hh
  have hH₂ : H₂ < q ^ ((n - c) * w) := Nat.mod_lt _ hpos₁
  have hD₁ : D₁ < q ^ ((n - c) * w) := by
    rw [Nat.div_lt_iff_lt_mul hpos₂, Nat.mul_comm, ← hsplit]; exact hd
  have hD₂ : D₂ < q ^ (c * w) := Nat.mod_lt _ hpos₂
  have e0 : n - c - (n - c) = 0 := by omega
  have e1 : n - 0 - c = n - c := by omega
  -- the second view: head `H₁ | H₂ | ·`, tail `· | D₁ | D₂`
  have s2 := revT_sub_apply (s := c) (c := n - c) hq hw (by omega) h₂ (hp := H₁) (hc := H₂)
    (hs := 0) (dp := 0) (dc := D₁) (ds := D₂) ha hrow hbefore hH₁ hH₂ (by rw [e0]; simp)
    hmid (by rw [e0]; simp) hD₁ hD₂ hafter
  simp only [e0, zero_mul, zero_add, pow_zero, mul_one, add_zero] at s2
  -- the first view: head `· | H₁ | rev D₁`, tail `rev H₂ | D₂ | ·`
  have hrD : revAtoms (q ^ w) (n - c) D₁ < q ^ ((n - c) * w) := by rw [hp]; exact revAtoms_lt hQ _ _
  have hrH : revAtoms (q ^ w) (n - c) H₂ < q ^ ((n - c) * w) := by rw [hp]; exact revAtoms_lt hQ _ _
  have s1 := revT_sub_apply (s := 0) (c := c) hq hw (by omega) h₁ (hp := 0) (hc := H₁)
    (hs := revAtoms (q ^ w) (n - c) D₁) (dp := revAtoms (q ^ w) (n - c) H₂) (dc := D₂) (ds := 0)
    ha hrow hbefore (by simp) hH₁ (by rw [e1]; exact hrD) hmid (by rw [e1]; exact hrH) hD₂
    (by simp) hafter
  simp only [e1, zero_mul, zero_add, pow_zero, mul_one, add_zero] at s1
  have eD : revAtoms (q ^ w) n (D₁ * q ^ (c * w) + D₂) =
      revAtoms (q ^ w) c D₂ * q ^ ((n - c) * w) + revAtoms (q ^ w) (n - c) D₁ := by
    have := revAtoms_append hQ (n - c) c D₁ D₂ (by rw [← hp]; exact hD₂)
    rw [show n - c + c = n by omega] at this
    rw [hp, hp, this]
  have eH : revAtoms (q ^ w) n (H₁ * q ^ ((n - c) * w) + H₂) =
      revAtoms (q ^ w) (n - c) H₂ * q ^ (c * w) + revAtoms (q ^ w) c H₁ := by
    have := revAtoms_append hQ c (n - c) H₁ H₂ (by rw [← hp]; exact hH₂)
    rw [show c + (n - c) = n by omega] at this
    rw [hp, hp, this]
  rw [hH, hD, s2, s1, eD, eH]

end IntegerMultBounds.MathlibTM2.M8.RevMachine
