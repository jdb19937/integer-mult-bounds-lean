module

public import IntegerMultBounds.Schoenhage.DifLayout

/-! One slot's round over several axes in a bit layout, as the paper groups
it: every axis's butterfly first, then one twist by the sum of the axes'
exponents (`run_group`). The exponent of the record at physical address `y`
is `slotExp`: for each participating axis, the twiddle `(2r/2^(h+1)) k` when
the axis's bit at the slot is set, `k` its bits below the slot. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

variable {r : ℕ} [NeZero r]

theorem bfly_twist_comm' {P : ℕ} {f : ℕ → ℕ} (hf0 : ∀ x, bitAt x P = 0 → f (x + 2 ^ P) = f x)
    (z : ℕ → Fin r → ℂ) : twist f (bfly P z) = bfly P (twist f z) := (bfly_twist_comm hf0 z).symm

/-- Butterflies on a list of bits. -/
noncomputable def bflys (Ps : List ℕ) : (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ := run (Ps.map bfly)

theorem twist_bflys {f : ℕ → ℕ} : ∀ (Ps : List ℕ), (∀ P ∈ Ps, ∀ x, bitAt x P = 0 → f (x + 2 ^ P) = f x) →
    ∀ z : ℕ → Fin r → ℂ, bflys Ps (twist f z) = twist f (bflys Ps z)
  | [], _, z => rfl
  | P :: Ps, h, z => by
    show bflys Ps (bfly P (twist f z)) = twist f (bflys Ps (bfly P z))
    rw [bfly_twist_comm (h P (by simp)), twist_bflys Ps (fun Q hQ => h Q (by simp [hQ]))]

/-- The exponent of axis `i` at slot `h` for the record at physical address `y`. -/
def axExp {n : ℕ} (π : BitPerm n) (r : ℕ) (ts : List ℕ) (i h y : ℕ) : ℕ := rexp r (axOff ts i) h (π.logi y)

/-- The round's exponent: the sum over the participating axes. -/
def slotExp {n : ℕ} (π : BitPerm n) (r : ℕ) (ts : List ℕ) (Is : List ℕ) (h y : ℕ) : ℕ :=
  (Is.map fun i => axExp π r ts i h y).sum

omit [NeZero r] in
/-- An axis's exponent ignores the slot bits of the other axes. -/
theorem axExp_flip {n : ℕ} (π : BitPerm n) {ts : List ℕ} (hts : PowAxes r ts) (hn : ts.prod = 2 ^ n)
    {i j h : ℕ} (hi : i < ts.length) (hj : j < ts.length) (hij : i ≠ j) (hhi : h < axLen ts i)
    (hhj : h < axLen ts j) :
    ∀ y, bitAt y (π.σ (axOff ts j + h)) = 0 →
      axExp π r ts i h (y + 2 ^ π.σ (axOff ts j + h)) = axExp π r ts i h y := by
  intro y hy
  have hlog : Nat.log 2 ts.prod = n := by rw [hn, Nat.log_pow (by norm_num)]
  have hP : axOff ts j + h < n := by have := axOff_add_len_le hts hj; omega
  unfold axExp
  rw [π.logi_add hP hy]
  apply rexp_add
  · rcases Nat.lt_or_gt_of_ne hij with hl | hl
    · have := axOff_le hts hl hj; omega
    · have := axOff_le hts hl hi; omega
  · rw [π.bitAt_logi y hP]; exact hy

/-- The bits of a slot's round. -/
def slotBits {n : ℕ} (π : BitPerm n) (ts : List ℕ) (Is : List ℕ) (h : ℕ) : List ℕ :=
  Is.map fun i => π.σ (axOff ts i + h)

/-- `run_group`: a slot's rounds over distinct axes are their butterflies, then one twist by the summed
exponent. -/
theorem run_group {n : ℕ} (π : BitPerm n) {ts : List ℕ} (hts : PowAxes r ts) (hn : ts.prod = 2 ^ n) (h : ℕ) :
    ∀ Is : List ℕ, Is.Nodup → (∀ i ∈ Is, i < ts.length ∧ h < axLen ts i) → ∀ w : ℕ → Fin r → ℂ,
      run (Is.map fun i => physRound π ts i h) w = twist (slotExp π r ts Is h) (bflys (slotBits π ts Is h) w)
  | [], _, _, w => by
    funext y; simp [run, slotExp, bflys, slotBits, twist, shiftInv_zero]
  | i :: Is, hnd, hI, w => by
    have hnd' := (List.nodup_cons.mp hnd)
    show run (Is.map fun i => physRound π ts i h) (physRound π ts i h w) = _
    rw [run_group π hts hn h Is hnd'.2 (fun j hj => hI j (by simp [hj]))]
    show twist _ (bflys _ (twist (axExp π r ts i h) (bfly (π.σ (axOff ts i + h)) w))) = _
    rw [twist_bflys]
    · rw [twist_twist]
      simp only [slotBits, List.map_cons, slotExp]
      congr 1
      funext y; simp only [slotExp, List.map_cons, List.sum_cons]; ring
    · intro P hP
      simp only [slotBits, List.mem_map] at hP
      obtain ⟨j, hj, rfl⟩ := hP
      have hji : i ≠ j := fun e => hnd'.1 (e ▸ hj)
      exact axExp_flip π hts hn (hI i (by simp)).1 (hI j (by simp [hj])).1 hji (hI i (by simp)).2
        (hI j (by simp [hj])).2

end IntegerMultBounds.Schoenhage
