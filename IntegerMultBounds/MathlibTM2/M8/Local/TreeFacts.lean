module

public import IntegerMultBounds.MathlibTM2.M8.Local.Kernel
public import Mathlib.Tactic.Ring

/-!
# Record trees

`Tree.Perfect t w`: the leaves of `t` sit at depth `log₂ w`. For a perfect tree, `Tree.get` is the
in-order indexing of its leaves (`get_node`), and a passed `Tree.all` check holds at every index
(`all_get`), with padding entries past the bound (`all_get_pad`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

variable {α : Type}

/-- Perfect of width `w`: a leaf for `w = 1`, otherwise two perfect halves of an even width. -/
def Tree.Perfect : Tree α → ℕ → Prop
  | .leaf _, w => w = 1
  | .node l r, w => 2 ≤ w ∧ w % 2 = 0 ∧ l.Perfect (w / 2) ∧ r.Perfect (w / 2)

/-- A `Bool` check of perfection, for the kernel. -/
def Tree.perfectB : Tree α → ℕ → Bool
  | .leaf _, w => Nat.beq w 1
  | .node l r, w => Nat.ble 2 w && Nat.beq (w % 2) 0 && l.perfectB (w / 2) && r.perfectB (w / 2)

theorem Tree.perfect_of_perfectB : ∀ (t : Tree α) (w : ℕ), t.perfectB w = true → t.Perfect w
  | .leaf _, w, h => by simpa [perfectB, Perfect] using h
  | .node l r, w, h => by
    simp only [perfectB, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
    exact ⟨h.1.1.1, h.1.1.2, perfect_of_perfectB l _ h.1.2, perfect_of_perfectB r _ h.2⟩

theorem Tree.get_leaf (v : α) (w i : ℕ) : (Tree.leaf v).get w i = v := rfl

theorem Tree.get_congr {t : Tree α} {w w' i i' : ℕ} (hw : w = w') (hi : i = i') :
    t.get w i = t.get w' i' := by rw [hw, hi]

theorem Tree.get_node (l r : Tree α) (w i : ℕ) :
    (Tree.node l r).get w i = if i < w / 2 then l.get (w / 2) i else r.get (w / 2) (i - w / 2) := by
  show (bif Nat.blt i (w / 2) then l.get (w / 2) i else r.get (w / 2) (i - w / 2)) = _
  by_cases h : i < w / 2
  · rw [ite_eq_left h, show Nat.blt i (w / 2) = true from Nat.blt_eq.mpr h]; rfl
  · rw [ite_eq_right h, show Nat.blt i (w / 2) = false from
      Bool.eq_false_iff.mpr fun h' => h (Nat.blt_eq.mp h')]; rfl

/-- A passed check holds at every index of a perfect tree. -/
theorem Tree.all_get (f : ℕ → α → Bool) (pad : α → Bool) (bound : ℕ) :
    ∀ (t : Tree α) (w n : ℕ), t.Perfect w → Tree.all f pad bound t n w = true →
      ∀ i < w, n + i < bound → f (n + i) (t.get w i) = true
  | .leaf v, w, n, hp, h, i, hi, hb => by
    simp only [Perfect] at hp
    subst hp
    have : i = 0 := by omega
    subst this
    simp only [Tree.all, Bool.cond_eq_ite, Nat.blt_eq] at h
    split_ifs at h with hn
    · simpa [Tree.get_leaf] using h
    · omega
  | .node l r, w, n, hp, h, i, hi, hb => by
    obtain ⟨hw, hev, hl, hr⟩ := hp
    simp only [Tree.all, Bool.and_eq_true] at h
    rw [Tree.get_node]
    split_ifs with hi'
    · exact all_get f pad bound l (w / 2) n hl h.1 i hi' hb
    · have := all_get f pad bound r (w / 2) (n + w / 2) hr h.2 (i - w / 2) (by omega) (by omega)
      rwa [show n + w / 2 + (i - w / 2) = n + i by omega] at this

/-- Past the bound, the entries of a passed check are padding. -/
theorem Tree.all_get_pad (f : ℕ → α → Bool) (pad : α → Bool) (bound : ℕ) :
    ∀ (t : Tree α) (w n : ℕ), t.Perfect w → Tree.all f pad bound t n w = true →
      ∀ i < w, bound ≤ n + i → pad (t.get w i) = true
  | .leaf v, w, n, hp, h, i, hi, hb => by
    simp only [Perfect] at hp
    subst hp
    have : i = 0 := by omega
    subst this
    simp only [Tree.all, Bool.cond_eq_ite, Nat.blt_eq] at h
    split_ifs at h with hn
    · omega
    · simpa [Tree.get_leaf] using h
  | .node l r, w, n, hp, h, i, hi, hb => by
    obtain ⟨hw, hev, hl, hr⟩ := hp
    simp only [Tree.all, Bool.and_eq_true] at h
    rw [Tree.get_node]
    split_ifs with hi'
    · exact all_get_pad f pad bound l (w / 2) n hl h.1 i hi' hb
    · exact all_get_pad f pad bound r (w / 2) (n + w / 2) hr h.2 (i - w / 2) (by omega) (by omega)

/-- Past its width, a perfect tree returns its last entry. -/
theorem Tree.get_ge : ∀ (t : Tree α) (w i : ℕ), t.Perfect w → w ≤ i → t.get w i = t.get w (w - 1)
  | .leaf v, w, i, _, _ => rfl
  | .node l r, w, i, hp, hi => by
    obtain ⟨hw, hev, _, hr⟩ := hp
    rw [Tree.get_node, Tree.get_node]
    simp only [show ¬ i < w / 2 by omega, show ¬ w - 1 < w / 2 by omega, ite_false]
    rw [get_ge r (w / 2) (i - w / 2) hr (by omega)]
    congr 1
    omega

end IntegerMultBounds.MathlibTM2.M8.Local
