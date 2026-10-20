module

public import IntegerMultBounds.MathlibTM2.Layer.CompactCodes
public import IntegerMultBounds.MathlibTM2.Layer.CompactMasks

/-!
# The offsets of the compact gadget read by automata

The offsets `Off.eval` of the gadget, as numbers built on host registers by gathering and
spreading at masks (`IntegerMultBounds.MathlibTM2.Layer.CompactMasks`) and read by the offset rules
of the wrap-class automata (`IntegerMultBounds.MathlibTM2.Layer.CompactGadget.ORule`).

Positions: `posS c = ρ + c K` (the selected bits of a slot), `posC c = c G` (the digit starts of a
compact field), `posA j = ρ + (j / G) K + 1 + j % G` (the bits of the temporary `t` placed above
the selected bits). The rules:

* `rPlain`: the offset is register `1` (`offv_rPlain`);
* `rXor`: offset bit `q` is `mask_q ∧ (r₁_q ⊕ r₂_q)` (`offv_rXor`);
* `rLatch`: offset bit `q` is `r₁_q` and the bit of `r₂` at the last set mask bit up to `q`
  (`offv_rLatch`).

`offZ_eq`, `offY_eq`, `offX_eq`, `offYZ_eq` and `offA_eq` identify the five offsets.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.CompactGadget

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactMasks
  IntegerMultBounds.MathlibTM2.Host Finset

variable (p : Par)

/-- Selected bit `c` of a slot. -/
def posS (c : ℕ) : ℕ := p.ρ + c * p.K

/-- Start of digit `c` of a compact field. -/
def posC (c : ℕ) : ℕ := c * p.G

/-- Bit `j` of the temporary placed above the selected bits. -/
def posA (j : ℕ) : ℕ := p.ρ + j / p.G * p.K + 1 + j % p.G

variable {p}

lemma posS_mono (hK : 0 < p.K) : StrictMono (posS p) := fun a b h => by
  unfold posS; nlinarith

lemma posC_mono (hG : 0 < p.G) : StrictMono (posC p) := fun a b h => by
  unfold posC; nlinarith

lemma posA_mono (hG : 0 < p.G) (hGK : p.G < p.K) : StrictMono (posA p) := by
  intro a b h
  unfold posA
  have ha := Nat.div_add_mod a p.G
  have hb := Nat.div_add_mod b p.G
  have hma := Nat.mod_lt a hG
  have hmb := Nat.mod_lt b hG
  rcases Nat.lt_or_ge (a / p.G) (b / p.G) with hq | hq
  · have : (a / p.G + 1) * p.K ≤ b / p.G * p.K := Nat.mul_le_mul_right _ hq
    nlinarith
  · have hq' : a / p.G = b / p.G := le_antisymm (Nat.div_le_div_right h.le) hq
    rw [hq']
    have : a % p.G < b % p.G := by
      have := Nat.div_add_mod a p.G; have := Nat.div_add_mod b p.G
      rw [hq'] at *; omega
    omega

lemma posA_lt (hG : 0 < p.G) (hGK : p.G < p.K) {j : ℕ} (hj : j < p.n * p.G) :
    posA p j < p.wy := by
  have hq : j / p.G < p.n := (Nat.div_lt_iff_lt_mul hG).2 hj
  have hr := Nat.mod_lt j hG
  have : (j / p.G + 1) * p.K ≤ p.n * p.K := Nat.mul_le_mul_right _ hq
  rw [Nat.add_mul, Nat.one_mul] at this
  unfold posA Par.wy
  omega

/-! ### Bits of parities and digits -/

lemma toNat_testBit (x j : ℕ) : (x.testBit j).toNat = x / 2 ^ j % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ j) with h | h <;> simp [h]

lemma par_eq (hK : 0 < p.K) (c Y : ℕ) : par p c Y = (Y.testBit (posS p c)).toNat := by
  rw [toNat_testBit, par, seg, window, posS, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]

lemma zc_eq (hG : 0 < p.G) (c : ℕ) (v : V) : zc p c v = (v.u.testBit (posC p c)).toNat := by
  rw [toNat_testBit, zc, cdig, window, posC, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]

/-! ### Offsets from gathered and spread bits -/

/-- `Off.Z` places the control bits at the selected positions. -/
lemma offZ_eq (hG : 0 < p.G) (v : V) :
    Off.eval p .Z v = placeVal p.n (posS p) fun c => v.u.testBit (posC p c) := by
  simp only [Off.eval, placeVal, posS]
  exact sum_congr rfl fun c _ => by rw [zc_eq hG]

/-- `Off.Y` places the selected bits of `y` at the digit starts. -/
lemma offY_eq (hK : 0 < p.K) (v : V) :
    Off.eval p .Y v = placeVal p.n (posC p) fun c => v.y.testBit (posS p c) := by
  simp only [Off.eval, casm, placeVal, posC]
  exact sum_congr rfl fun c _ => by rw [par_eq hK]

/-- `Off.X` places the selected bits of `x` at the digit starts. -/
lemma offX_eq (hK : 0 < p.K) (v : V) :
    Off.eval p .X v = placeVal p.n (posC p) fun c => v.x.testBit (posS p c) := by
  simp only [Off.eval, casm, placeVal, posC]
  exact sum_congr rfl fun c _ => by rw [par_eq hK]

/-- `Off.YZ` places the sums of the selected bits of `y` and the controls at the digit starts. -/
lemma offYZ_eq (hK : 0 < p.K) (hG : 0 < p.G) (v : V) :
    Off.eval p .YZ v = placeVal p.n (posC p) fun c =>
      xor (v.y.testBit (posS p c)) (v.u.testBit (posC p c)) := by
  simp only [Off.eval, casm, placeVal]
  refine sum_congr rfl fun c _ => ?_
  rw [par_eq hK, zc_eq hG]
  simp only [posC]
  cases v.y.testBit (posS p c) <;> cases v.u.testBit (c * p.G) <;> rfl

/-! ### The offset rules -/

/-- The offset is register `1`. -/
def rPlain : ORule 2 := ⟨fun a col => (col 1, a)⟩

/-- Offset bit `mask ∧ (r₁ ⊕ r₂)`, registers `(·, r₁, r₂, mask)`. -/
def rXor : ORule 4 := ⟨fun a col => (col 3 && xor (col 1) (col 2), a)⟩

/-- Offset bit `r₁` and the latched bit of `r₂`, latched at the set bits of the mask, registers
`(·, r₁, r₂, mask)`. -/
def rLatch : ORule 4 :=
  ⟨fun a col => ((if col 3 then col 2 else a) && col 1, if col 3 then col 2 else a)⟩

lemma auxAt_succ {k : ℕ} (R : ORule k) : ∀ (q : ℕ) (a : Bool) (vals : Fin k → ℕ),
    auxAt R (q + 1) a vals = (R.ob (auxAt R q a vals) fun r => (vals r).testBit q).2
  | 0, a, vals => by simp [auxAt]
  | q + 1, a, vals => by
    rw [auxAt, auxAt_succ R q, auxAt]
    simp [Nat.testBit_div_two]

lemma auxAt_rPlain (q : ℕ) (vals : Fin 2 → ℕ) : auxAt rPlain q false vals = false := by
  induction q with
  | zero => rfl
  | succ q ih => rw [auxAt_succ, ih]; rfl

lemma auxAt_rXor (q : ℕ) (vals : Fin 4 → ℕ) : auxAt rXor q false vals = false := by
  induction q with
  | zero => rfl
  | succ q ih => rw [auxAt_succ, ih]; rfl

lemma offv_rPlain (L x y : ℕ) : offv rPlain L false ![x, y] = y % 2 ^ L := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_offv, auxAt_rPlain, Nat.testBit_mod_two_pow]
  simp [rPlain, Bool.and_comm]

lemma offv_rXor (L x y z m : ℕ) : (offv rXor L false ![x, y, z, m]).testBit =
    fun q => decide (q < L) && (m.testBit q && xor (y.testBit q) (z.testBit q)) := by
  funext q
  rw [testBit_offv, auxAt_rXor]
  rfl

/-- Inside the block of selected bit `c` the latch holds the bit of `r₂` at that selected bit. -/
lemma auxAt_rLatch (hK : 0 < p.K) (x y z : ℕ) {c : ℕ} (hc : c < p.n) : ∀ d < p.K,
    auxAt rLatch (posS p c + 1 + d) false ![x, y, z, maskVal p.n (posS p)] =
      z.testBit (posS p c) := by
  have hmono := posS_mono (p := p) hK
  intro d
  induction d with
  | zero =>
    intro _
    rw [Nat.add_zero, auxAt_succ]
    simp only [rLatch, Matrix.cons_val_three, Matrix.cons_val_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.tail_cons, Matrix.head_cons, testBit_maskVal hmono]
    rw [if_pos (by simp; exact ⟨c, hc, rfl⟩)]
  | succ d ih =>
    intro hd
    rw [show posS p c + 1 + (d + 1) = posS p c + 1 + d + 1 by ring, auxAt_succ,
      ih (by omega)]
    simp only [rLatch, Matrix.cons_val_three, Matrix.cons_val_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.tail_cons, Matrix.head_cons, testBit_maskVal hmono]
    rw [if_neg]
    simp only [decide_eq_true_eq, not_exists, not_and]
    intro c' _ h
    unfold posS at h
    rcases lt_trichotomy c' c with hc' | rfl | hc'
    · have : (c' + 1) * p.K ≤ c * p.K := Nat.mul_le_mul_right _ hc'
      nlinarith
    · omega
    · have : (c + 1) * p.K ≤ c' * p.K := Nat.mul_le_mul_right _ hc'
      nlinarith

/-- The low `G` bits as a sum. -/
lemma mod_pow_eq_sum (x : ℕ) : ∀ G, x % 2 ^ G = ∑ g ∈ range G, (x.testBit g).toNat * 2 ^ g
  | 0 => by simp [Nat.mod_one]
  | G + 1 => by
    rw [Nat.mod_pow_succ, mod_pow_eq_sum x G, sum_range_succ, toNat_testBit]
    ring

/-- A compact digit as a sum of its bits. -/
lemma cdig_eq_sum (c t : ℕ) :
    cdig p.G c t = ∑ g ∈ range p.G, (t.testBit (posC p c + g)).toNat * 2 ^ g := by
  rw [cdig, window, mod_pow_eq_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [Nat.testBit_div_two_pow, posC, Nat.add_comm]

lemma posA_split (hG : 0 < p.G) (c g : ℕ) (hg : g < p.G) :
    posA p (c * p.G + g) = posS p c + 1 + g := by
  unfold posA posS
  rw [Nat.add_comm (c * p.G) g, Nat.add_mul_div_right _ _ hG, Nat.div_eq_of_lt hg, Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hg]

/-- `Off.A` places the temporary bits, masked by their controls, above the selected bits. -/
lemma offA_eq (hG : 0 < p.G) (v : V) :
    Off.eval p .A v = placeVal (p.n * p.G) (posA p) fun j =>
      v.u.testBit (posC p (j / p.G)) && v.t.testBit j := by
  simp only [Off.eval]
  induction p.n with
  | zero => simp [placeVal]
  | succ n ih =>
    rw [sum_range_succ, ih, show (n + 1) * p.G = n * p.G + p.G by ring]
    conv_rhs => rw [placeVal, sum_range_add]
    rw [← placeVal]
    congr 1
    rw [zc_eq hG, cdig_eq_sum, mul_sum, sum_mul]
    refine sum_congr rfl fun g hg => ?_
    have hg' : g < p.G := mem_range.1 hg
    have hdiv : (n * p.G + g) / p.G = n := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hG, Nat.div_eq_of_lt hg', Nat.zero_add]
    rw [posA_split hG n g hg', hdiv]
    simp only [posS, posC]
    cases v.u.testBit (n * p.G) <;> cases v.t.testBit (n * p.G + g) <;>
      simp [Nat.pow_add, Nat.pow_succ] <;> ring

lemma rLatch_fst (a : Bool) (col : Fin 4 → Bool) :
    (rLatch.ob a col).1 = ((if col 3 then col 2 else a) && col 1) := rfl

omit p in
lemma testBit_placeVal_at {pos : ℕ → ℕ} (hpos : StrictMono pos) {n c : ℕ} (hc : c < n)
    (b : ℕ → Bool) : (placeVal n pos b).testBit (pos c) = b c := by
  rw [testBit_placeVal hpos]
  cases hb : b c
  · simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro c' _ h
    rw [hpos.injective h, hb]
    simp
  · simp only [decide_eq_true_eq]
    exact ⟨c, hc, rfl, hb⟩

/-- **The latch automaton reads `Off.A`.** The registers hold the slot `y`, the temporary bits
spread to `posA`, the control bits spread to `posS`, and the selected-bit mask. -/
theorem offv_rLatch (hK : 0 < p.K) (hG : 0 < p.G) (hGK : p.G < p.K) {W : ℕ}
    (hW : ∀ j < p.n * p.G, posA p j < W) (v : V) :
    offv rLatch W false ![v.y, placeVal (p.n * p.G) (posA p) (fun j => v.t.testBit j),
      placeVal p.n (posS p) (fun c => v.u.testBit (posC p c)), maskVal p.n (posS p)] =
      Off.eval p .A v := by
  rw [offA_eq hG]
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_offv, rLatch_fst]
  simp only [Matrix.cons_val_three, Matrix.cons_val_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.tail_cons, Matrix.head_cons]
  by_cases hq : ∃ j < p.n * p.G, posA p j = q
  · obtain ⟨j, hj, rfl⟩ := hq
    have hjg := Nat.mod_lt j hG
    have hjc : j / p.G < p.n := (Nat.div_lt_iff_lt_mul hG).2 hj
    have hsplit := posA_split hG (j / p.G) (j % p.G) hjg
    rw [Nat.div_add_mod' j p.G] at hsplit
    have hns : ¬ ∃ c < p.n, posS p c = posA p j := by
      rintro ⟨c, _, h⟩
      rw [hsplit] at h
      unfold posS at h
      rcases lt_trichotomy c (j / p.G) with hc' | rfl | hc'
      · have : (c + 1) * p.K ≤ j / p.G * p.K := Nat.mul_le_mul_right _ hc'
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      · omega
      · have : (j / p.G + 1) * p.K ≤ c * p.K := Nat.mul_le_mul_right _ hc'
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
    have hmask : (maskVal p.n (posS p)).testBit (posA p j) = false := by
      rw [testBit_maskVal (posS_mono hK)]
      simpa using hns
    have hlatch : auxAt rLatch (posA p j) false ![v.y, placeVal (p.n * p.G) (posA p)
        (fun j => v.t.testBit j), placeVal p.n (posS p) (fun c => v.u.testBit (posC p c)),
        maskVal p.n (posS p)] = v.u.testBit (posC p (j / p.G)) := by
      rw [hsplit, auxAt_rLatch hK _ _ _ hjc (j % p.G) (by omega),
        testBit_placeVal_at (posS_mono hK) hjc]
    rw [hmask, hlatch, testBit_placeVal_at (posA_mono hG hGK) hj,
      testBit_placeVal_at (posA_mono hG hGK) hj]
    simp [hW j hj]
  · have h1 : (placeVal (p.n * p.G) (posA p) fun j => v.t.testBit j).testBit q = false := by
      rw [testBit_placeVal (posA_mono hG hGK)]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      exact fun j hj h _ => hq ⟨j, hj, h⟩
    have h2 : (placeVal (p.n * p.G) (posA p) fun j =>
        v.u.testBit (posC p (j / p.G)) && v.t.testBit j).testBit q = false := by
      rw [testBit_placeVal (posA_mono hG hGK)]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      exact fun j hj h _ => hq ⟨j, hj, h⟩
    rw [h1, h2]
    simp

end IntegerMultBounds.MathlibTM2.Layer.CompactGadget
