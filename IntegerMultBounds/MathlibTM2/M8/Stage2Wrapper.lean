module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Address
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Fin.Basic

/-!
# The `F L F` wrapper on the descriptor

The stage-2 supplier runs the ordinary interchange of a descriptor `v` whose fields have `e`
digits as two pieces (`swap_split`): the top `e - r` digits of both fields (`top`) and the low `r`
digits (`low`), each an ordinary interchange with the other digits regrouped into spectators.
The low piece is a leaf interchange. The top piece has `n` atoms of `w` digits and runs as the
`F L F` wrapper (`flf`): the atomwise shears `d ← d - h`, `d ← d + h`, `d ← h - d` around two
reversed interchanges `RevT` of the reversed family. Field values are atom vectors through the
base-`q^w` code `enc` (`rev_enc`: the digit reversal `revAtoms` is the reversal of the atoms).

The steps are stated as array moves (`Moves g`: the record at fields `(h, d)` goes to `g (h, d)`,
every spectator fixed), which compose (`Moves.trans`); the ordinary interchange is
`Moves Prod.swap`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Wrapper

open IntegerMultBounds.Machine.RecursiveInterchangeLayout
open RevMachine (revAtoms RevT revAtoms_lt revAtoms_revAtoms revAtoms_digit eq_of_digits)

variable {α : Type*}

/-! ### Array moves -/

/-- `y` holds at fields `g (h, d)` the record of `x` at fields `(h, d)`, on every address of `v`. -/
def Moves (q : ℕ) (v : Descriptor) (g : ℕ × ℕ → ℕ × ℕ) (x y : ℕ → α) : Prop :=
  ∀ a < v.beforeRows, ∀ row < v.rows, ∀ before < v.beforeH, ∀ h < q ^ v.width,
    ∀ mid < v.between, ∀ d < q ^ v.width, ∀ after < v.afterD,
      y (index q v a row before (g (h, d)).1 mid (g (h, d)).2 after) =
        x (index q v a row before h mid d after)

/-- `g` keeps the fields below `B`. -/
def Keeps (B : ℕ) (g : ℕ × ℕ → ℕ × ℕ) : Prop :=
  ∀ h < B, ∀ d < B, (g (h, d)).1 < B ∧ (g (h, d)).2 < B

variable {q : ℕ} {v : Descriptor}

theorem Moves.trans {g g' : ℕ × ℕ → ℕ × ℕ} {x y z : ℕ → α} (hk : Keeps (q ^ v.width) g)
    (h₁ : Moves q v g x y) (h₂ : Moves q v g' y z) : Moves q v (g' ∘ g) x z := by
  intro a ha row hrow before hb h hh mid hm d hd after haf
  obtain ⟨k₁, k₂⟩ := hk h hh d hd
  exact (h₂ a ha row hrow before hb _ k₁ mid hm _ k₂ after haf).trans
    (h₁ a ha row hrow before hb h hh mid hm d hd after haf)

theorem Moves.congr {g g' : ℕ × ℕ → ℕ × ℕ} {x y : ℕ → α}
    (he : ∀ h < q ^ v.width, ∀ d < q ^ v.width, g (h, d) = g' (h, d)) (hm : Moves q v g x y) :
    Moves q v g' x y := by
  intro a ha row hrow before hb h hh mid hmid d hd after haf
  rw [← he h hh d hd]
  exact hm a ha row hrow before hb h hh mid hmid d hd after haf

theorem Keeps.comp {B : ℕ} {g g' : ℕ × ℕ → ℕ × ℕ} (hk : Keeps B g) (hk' : Keeps B g') :
    Keeps B (g' ∘ g) := fun h hh d hd => by
  obtain ⟨k₁, k₂⟩ := hk h hh d hd
  exact hk' _ k₁ _ k₂

/-! ### Atom codes -/

section Atoms

variable (Q n : ℕ) [NeZero Q]

/-- `n` atoms of `Q` values. -/
abbrev Atoms := Fin n → Fin Q

/-- The base-`Q` code of an atom vector, atom `j` the digit of `Q^j`. -/
def enc (e : Atoms Q n) : ℕ := finFunctionFinEquiv e

/-- The atoms of a field value below `Q^n`. -/
def dec (h : ℕ) : Atoms Q n :=
  finFunctionFinEquiv.symm ⟨h % Q ^ n, Nat.mod_lt _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne Q)) n)⟩

variable {Q n}

omit [NeZero Q] in
theorem enc_lt (e : Atoms Q n) : enc Q n e < Q ^ n := (finFunctionFinEquiv e).isLt

theorem dec_enc (e : Atoms Q n) : dec Q n (enc Q n e) = e := by
  unfold dec
  convert finFunctionFinEquiv.symm_apply_apply e using 2
  exact Fin.ext (Nat.mod_eq_of_lt (enc_lt e))

theorem enc_dec {h : ℕ} (hh : h < Q ^ n) : enc Q n (dec Q n h) = h := by
  unfold dec enc
  rw [Equiv.apply_symm_apply]
  exact Nat.mod_eq_of_lt hh

omit [NeZero Q] in
theorem enc_digit (e : Atoms Q n) (j : Fin n) : enc Q n e / Q ^ j.val % Q = e j := by
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv e) j
  rw [Equiv.symm_apply_apply] at this
  exact this.symm

/-- **The digit reversal of a code is the code of the reversed atoms.** -/
theorem rev_enc (e : Atoms Q n) : revAtoms Q n (enc Q n e) = enc Q n (e ∘ Fin.rev) := by
  have hQ : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  refine eq_of_digits hQ n _ _ (revAtoms_lt hQ n _) (enc_lt _) fun j hj => ?_
  rw [revAtoms_digit hQ n _ j hj, enc_digit e ⟨n - 1 - j, by omega⟩, enc_digit _ ⟨j, hj⟩]
  simp only [Function.comp_apply, Fin.rev]
  congr 3
  omega

end Atoms

/-! ### The `F L F` wrapper -/

section Wrapper

variable (Q n : ℕ) [NeZero Q]

/-- The reversed interchange of fields of `n` atoms. -/
def revMap (p : ℕ × ℕ) : ℕ × ℕ := (revAtoms Q n p.2, revAtoms Q n p.1)

/-- The atomwise shear `d ← s h d`. -/
def shear (s : Atoms Q n → Atoms Q n → Atoms Q n) (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1, enc Q n (s (dec Q n p.1) (dec Q n p.2)))

variable {Q n}

theorem keeps_rev : Keeps (Q ^ n) (revMap Q n) := fun _ _ _ _ =>
  ⟨revAtoms_lt (Nat.pos_of_ne_zero (NeZero.ne Q)) n _, revAtoms_lt (Nat.pos_of_ne_zero (NeZero.ne Q)) n _⟩

theorem keeps_shear (s : Atoms Q n → Atoms Q n → Atoms Q n) : Keeps (Q ^ n) (shear Q n s) :=
  fun _ hh _ _ => ⟨hh, enc_lt _⟩

/-- On the atom codes, the five steps are the ordinary interchange. -/
theorem flf_map {h d : ℕ} (hh : h < Q ^ n) (hd : d < Q ^ n) :
    (shear Q n (fun h d => h - d) ∘ revMap Q n ∘ shear Q n (fun h d => d + h) ∘ revMap Q n ∘
      shear Q n (fun h d => d - h)) (h, d) = Prod.swap (h, d) := by
  obtain ⟨a, rfl⟩ : ∃ a, enc Q n a = h := ⟨dec Q n h, enc_dec hh⟩
  obtain ⟨b, rfl⟩ : ∃ b, enc Q n b = d := ⟨dec Q n d, enc_dec hd⟩
  have hr (e : Atoms Q n) : e ∘ Fin.rev ∘ Fin.rev = e := by
    funext j; simp [Fin.rev_rev]
  simp only [Function.comp_apply, shear, revMap, dec_enc, rev_enc, Prod.swap_prod_mk]
  refine Prod.ext ?_ ?_
  · show enc Q n ((a ∘ Fin.rev + (b - a) ∘ Fin.rev) ∘ Fin.rev) = enc Q n b
    congr 1; funext j; simp [Fin.rev_rev]
  · show enc Q n ((a ∘ Fin.rev + (b - a) ∘ Fin.rev) ∘ Fin.rev - ((b - a) ∘ Fin.rev) ∘ Fin.rev) =
      enc Q n a
    congr 1; funext j; simp [Fin.rev_rev]

/-- A reversed interchange is the move of `revMap`. -/
theorem revT_moves {w : ℕ} (hq : 0 < q) (hw : v.width = n * w) {x y : ℕ → α}
    (hT : RevT q w n v x y) : Moves q v (revMap (q ^ w) n) x y := by
  have hQ : 0 < q ^ w := pow_pos hq w
  have hp : q ^ v.width = (q ^ w) ^ n := by rw [hw, Nat.mul_comm, pow_mul]
  intro a ha row hrow before hb h hh mid hm d hd after haf
  rw [hp] at hh hd
  have := hT a ha row hrow before hb (revAtoms (q ^ w) n d) (by rw [Nat.mul_comm, pow_mul]; exact revAtoms_lt hQ n d)
    mid hm (revAtoms (q ^ w) n h) (by rw [Nat.mul_comm, pow_mul]; exact revAtoms_lt hQ n h) after haf
  rwa [revAtoms_revAtoms hQ n d hd, revAtoms_revAtoms hQ n h hh] at this

/-- **The `F L F` wrapper**: `d ← d - h`, the reversed interchange, `d ← d + h`, the reversed
interchange, `d ← h - d` make the ordinary interchange. -/
theorem flf {w : ℕ} [NeZero (q ^ w)] (hq : 0 < q) (hw : v.width = n * w)
    {x y₁ y₂ y₃ y₄ y₅ : ℕ → α}
    (h₁ : Moves q v (shear (q ^ w) n fun h d => d - h) x y₁) (h₂ : RevT q w n v y₁ y₂)
    (h₃ : Moves q v (shear (q ^ w) n fun h d => d + h) y₂ y₃) (h₄ : RevT q w n v y₃ y₄)
    (h₅ : Moves q v (shear (q ^ w) n fun h d => h - d) y₄ y₅) :
    Moves q v Prod.swap x y₅ := by
  have hp : q ^ v.width = (q ^ w) ^ n := by rw [hw, Nat.mul_comm, pow_mul]
  have kr : Keeps (q ^ v.width) (revMap (q ^ w) n) := hp ▸ keeps_rev
  have ks (s) : Keeps (q ^ v.width) (shear (q ^ w) n s) := hp ▸ keeps_shear s
  have m := (((h₁.trans (ks _) (revT_moves hq hw h₂)).trans ((ks _).comp kr) h₃).trans
    (((ks _).comp kr).comp (ks _)) (revT_moves hq hw h₄)).trans
    ((((ks _).comp kr).comp (ks _)).comp kr) h₅
  refine m.congr fun h hh d hd => ?_
  rw [hp] at hh hd
  exact flf_map hh hd

end Wrapper

/-! ### Splitting off the low digits -/

/-- The top `width - r` digits of each field, the low `r` digits regrouped into the spectators. -/
def top (q r : ℕ) (v : Descriptor) : Descriptor :=
  { v with
    width := v.width - r
    between := q ^ r * v.between
    afterD := q ^ r * v.afterD }

/-- The low `r` digits of each field. -/
def low (q r : ℕ) (v : Descriptor) : Descriptor :=
  { v with
    beforeH := v.beforeH * q ^ (v.width - r)
    width := r
    between := v.between * q ^ (v.width - r) }

theorem top_index {r : ℕ} (hr : r ≤ v.width) (a row before h₁ h₂ mid d₁ d₂ after : ℕ) :
    index q (top q r v) a row before h₁ (h₂ * v.between + mid) d₁ (d₂ * v.afterD + after) =
      index q v a row before (h₁ * q ^ r + h₂) mid (d₁ * q ^ r + d₂) after := by
  have he : q ^ v.width = q ^ (v.width - r) * q ^ r := by rw [← pow_add, Nat.sub_add_cancel hr]
  simp only [index, top, he]
  ring

theorem low_index {r : ℕ} (hr : r ≤ v.width) (a row before h₁ h₂ mid d₁ d₂ after : ℕ) :
    index q (low q r v) a row (before * q ^ (v.width - r) + h₁) h₂ (mid * q ^ (v.width - r) + d₁)
      d₂ after = index q v a row before (h₁ * q ^ r + h₂) mid (d₁ * q ^ r + d₂) after := by
  have he : q ^ v.width = q ^ (v.width - r) * q ^ r := by rw [← pow_add, Nat.sub_add_cancel hr]
  simp only [index, low, he]
  ring

private theorem pack_lt {a A b B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  nlinarith

/-- **The split**: the interchanges of the top and the low digits make the interchange of `v`. -/
theorem swap_split (hq : 0 < q) {r : ℕ} (hr : r ≤ v.width) {x y z : ℕ → α}
    (ht : Moves q (top q r v) Prod.swap x z) (hl : Moves q (low q r v) Prod.swap z y) :
    Moves q v Prod.swap x y := by
  intro a ha row hrow before hb h hh mid hm d hd after haf
  have hpr : 0 < q ^ r := pow_pos hq r
  have he : q ^ v.width = q ^ (v.width - r) * q ^ r := by rw [← pow_add, Nat.sub_add_cancel hr]
  have hsplit (z : ℕ) (hz : z < q ^ v.width) : z = z / q ^ r * q ^ r + z % q ^ r ∧
      z / q ^ r < q ^ (v.width - r) ∧ z % q ^ r < q ^ r := by
    refine ⟨(Nat.div_add_mod' z _).symm, ?_, Nat.mod_lt _ hpr⟩
    rw [Nat.div_lt_iff_lt_mul hpr, ← he]; exact hz
  obtain ⟨eh, hh₁, hh₂⟩ := hsplit h hh
  obtain ⟨ed, hd₁, hd₂⟩ := hsplit d hd
  set h₁ := h / q ^ r; set h₂ := h % q ^ r; set d₁ := d / q ^ r; set d₂ := d % q ^ r
  show y (index q v a row before d mid h after) = x (index q v a row before h mid d after)
  have hlow := hl a ha row hrow (before * q ^ (v.width - r) + d₁) (by show _ < v.beforeH * q ^ (v.width - r); exact pack_lt hb hd₁) h₂ hh₂
    (mid * q ^ (v.width - r) + h₁) (by show _ < v.between * q ^ (v.width - r); exact pack_lt hm hh₁) d₂ hd₂ after haf
  have htop := ht a ha row hrow before hb h₁ hh₁ (h₂ * v.between + mid)
    (by show _ < q ^ r * v.between; exact pack_lt hh₂ hm) d₁ hd₁
    (d₂ * v.afterD + after) (by show _ < q ^ r * v.afterD; exact pack_lt hd₂ haf)
  simp only [Prod.swap_prod_mk] at hlow htop
  rw [low_index hr, low_index hr] at hlow
  rw [top_index hr, top_index hr] at htop
  rw [eh, ed, hlow, htop]

end IntegerMultBounds.MathlibTM2.M8.Stage2Wrapper
