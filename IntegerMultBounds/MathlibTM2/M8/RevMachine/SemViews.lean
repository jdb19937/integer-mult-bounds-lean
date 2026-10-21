module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Views
public import Mathlib.Data.ZMod.Defs

/-!
# Reversed interchanges of nested views

A frame's data is a bit array over its volume; `ext` reads it on every index. The views of a
view are views (`sub_sub`), and the whole field is the view of all its atoms (`sub_all`). With no
atoms the reversed interchange keeps everything (`revT_zero`); one atom is the plain interchange
(`revT_one`). `revT_partition_rev` is `revT_partition` in the other order, and `revT_grow` adds one
atom pair before a run of reversed pairs: the leaves of a frame, last atom first, make the
reversed interchange of their view.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine

open IntegerMultBounds.Machine.RecursiveInterchangeLayout

/-- An array read on every index, zero beyond its volume. -/
def ext {V : ℕ} (x : Fin V → ZMod 2) : ℕ → ZMod 2 := fun i => if h : i < V then x ⟨i, h⟩ else 0

theorem ext_apply {V : ℕ} (x : Fin V → ZMod 2) (i : Fin V) : ext x i = x i := by
  simp [ext]

theorem ext_cast {V V' : ℕ} (h : V = V') (x : Fin V' → ZMod 2) : ext (fun i : Fin V => x (Fin.cast h i)) = ext x := by
  subst h; rfl

theorem revAtoms_one {Q h : ℕ} (hh : h < Q) : revAtoms Q 1 h = h := by
  simp [revAtoms, Nat.mod_eq_of_lt hh]

/-- With no atoms the reversed interchange keeps every entry. -/
theorem revT_zero {α : Type*} (q w : ℕ) (v : Descriptor) (x : ℕ → α) : RevT q w 0 v x x := by
  intro a _ row _ before _ h hh mid _ d hd after _
  simp only [zero_mul, pow_zero, Nat.lt_one_iff] at hh hd
  subst hh hd
  rfl

/-- One atom: the plain interchange. -/
theorem revT_one {α : Type*} {q w : ℕ} {v : Descriptor} {x y : ℕ → α}
    (h : ∀ a < v.beforeRows, ∀ row < v.rows, ∀ before < v.beforeH, ∀ h < q ^ w,
      ∀ mid < v.between, ∀ d < q ^ w, ∀ after < v.afterD,
        y (index q v a row before h mid d after) = x (index q v a row before d mid h after)) :
    RevT q w 1 v x y := by
  intro a ha row hrow before hb hh hhh mid hm d hd after haf
  rw [one_mul] at hhh hd
  rw [revAtoms_one hhh, revAtoms_one hd]
  exact h a ha row hrow before hb hh hhh mid hm d hd after haf

/-- A view of a view is a view. -/
theorem sub_sub (q w n s c s' c' : ℕ) (v : Descriptor) (h : s + c ≤ n) (h' : s' + c' ≤ c) :
    sub q w c s' c' (sub q w n s c v) = sub q w n (s + s') c' v := by
  have e : (n - (s + s') - c') * w = (n - s - c) * w + (c - s' - c') * w := by
    rw [← Nat.add_mul]; congr 1; omega
  simp only [sub, e, Nat.add_mul, pow_add]
  congr 1 <;> ring

/-- The view of all atoms is the field. -/
theorem sub_all (q w n : ℕ) (v : Descriptor) (hw : v.width = n * w) : sub q w n 0 n v = v := by
  cases v
  simp only [sub, zero_mul, pow_zero, mul_one, Nat.sub_zero, Nat.sub_self, one_mul] at hw ⊢
  rw [hw]

private theorem pack_lt {a A b B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  nlinarith

/-- **The partition, the other way round.** The reversed interchanges of the last `n - c` atom
pairs and of the first `c`, in this order, make the reversed interchange of the whole field. -/
theorem revT_partition_rev {α : Type*} {q w n c : ℕ} (hq : 0 < q) {v : Descriptor} (hw : v.width = n * w)
    (hc : c ≤ n) {x y z : ℕ → α} (h₁ : RevT q w (n - c) (sub q w n c (n - c) v) x y)
    (h₂ : RevT q w c (sub q w n 0 c v) y z) : RevT q w n v x z := by
  have hQ : 0 < q ^ w := pow_pos hq w
  have hp (k : ℕ) : q ^ (k * w) = (q ^ w) ^ k := by rw [Nat.mul_comm, pow_mul]
  intro a ha row hrow before hbefore h hh mid hmid d hd after hafter
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
  have hrD : revAtoms (q ^ w) c D₂ < q ^ (c * w) := by rw [hp]; exact revAtoms_lt hQ _ _
  have hrH : revAtoms (q ^ w) c H₁ < q ^ (c * w) := by rw [hp]; exact revAtoms_lt hQ _ _
  -- the second view: head `· | H₁ | H₂`, tail `D₁ | D₂ | ·`
  have s2 := revT_sub_apply (s := 0) (c := c) hq hw (by omega) h₂ (hp := 0) (hc := H₁)
    (hs := H₂) (dp := D₁) (dc := D₂) (ds := 0) ha hrow hbefore (by simp) hH₁ (by rw [e1]; exact hH₂)
    hmid (by rw [e1]; exact hD₁) hD₂ (by simp) hafter
  simp only [e1, zero_mul, zero_add, pow_zero, mul_one, add_zero] at s2
  -- the first view: head `rev D₂ | H₂ | ·`, tail `· | D₁ | rev H₁`
  have s1 := revT_sub_apply (s := c) (c := n - c) hq hw (by omega) h₁ (hp := revAtoms (q ^ w) c D₂)
    (hc := H₂) (hs := 0) (dp := 0) (dc := D₁) (ds := revAtoms (q ^ w) c H₁)
    ha hrow hbefore hrD hH₂ (by rw [e0]; simp) hmid (by rw [e0]; simp) hD₁ hrH hafter
  simp only [e0, zero_mul, zero_add, pow_zero, mul_one, add_zero] at s1
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

/-- **One more pair in front.** The reversed interchange of the `i` pairs after atom `k`, then
the interchange of atom `k`, is the reversed interchange of the `i + 1` pairs from atom `k`. -/
theorem revT_grow {α : Type*} {q w n k i : ℕ} (hq : 0 < q) {v : Descriptor} (h : k + (i + 1) ≤ n)
    {x y z : ℕ → α} (h₁ : RevT q w i (sub q w n (k + 1) i v) x y) (h₂ : RevT q w 1 (sub q w n k 1 v) y z) :
    RevT q w (i + 1) (sub q w n k (i + 1) v) x z := by
  have e₁ : sub q w (i + 1) 1 (i + 1 - 1) (sub q w n k (i + 1) v) = sub q w n (k + 1) i v := by
    rw [sub_sub q w n k (i + 1) 1 (i + 1 - 1) v h (by omega), Nat.add_sub_cancel]
  have e₂ : sub q w (i + 1) 0 1 (sub q w n k (i + 1) v) = sub q w n k 1 v := by
    rw [sub_sub q w n k (i + 1) 0 1 v h (by omega), Nat.add_zero]
  refine revT_partition_rev hq rfl (by omega) ?_ (e₂ ▸ h₂)
  rw [e₁, Nat.add_sub_cancel]
  exact h₁

end IntegerMultBounds.MathlibTM2.M8.RevMachine
