module

public import IntegerMultBounds.MathlibTM2.M8.StoppedRecurrence

/-!
# The budget of the reversed family

A field of `n` atoms costs, normalized by its volume, `T n`. Below the cutoff `m` the field is
`n < m` leaf interchanges, at most `C L`. Above it, `n = m f + δ`: the node runs its moves, one
block child of `r f` atoms for each move of rank `r` (`ranks`), on one role stream, so each child
weighs `1 / W` of the volume; the `δ < m` remainder leaves and the atom adapters cost at most
`C n + C L`. With the two moment gaps of the rank list, `StoppedRecurrence.stopped_closed` closes
the recurrence (`family_closed`): `T n ≤ C/(1-q₁) n + C/(1-q_τ) n^τ L`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine

open Finset

/-- An atom count, at least one. -/
abbrev Width := {n : ℕ // 1 ≤ n}

/-- The children of a node: one block child of `r ⌊n/m⌋` atoms per move of rank `r`. -/
def children (m : ℕ) (ranks : List ℕ) (n : Width) : ℕ :=
  if m ≤ n.val then ranks.length else 0

/-- **The closed budget of the family.** Every rank is positive and below `m`; the moments of
the rank list on `W` roles are below `q₁` and `q_τ`. A cost that obeys the leaf bound below `m`
and the node recurrence above it is at most `C/(1-q₁) n + C/(1-q_τ) n^τ L`. -/
theorem family_closed (m W : ℕ) (hm : 2 ≤ m) (hW : 0 < W) (ranks : List ℕ)
    (hpos : ∀ r ∈ ranks, 1 ≤ r) (hle : ∀ r ∈ ranks, r < m)
    (T : ℕ → ℝ) {τ q₁ qτ C L : ℝ} (hτ : 0 ≤ τ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hq₁ : q₁ < 1) (hqτ0 : 0 ≤ qτ) (hqτ : qτ < 1)
    (hleaf : ∀ n, 1 ≤ n → n < m → T n ≤ C * L)
    (hnode : ∀ n, m ≤ n →
      T n ≤ (ranks.map fun r : ℕ => T (r * (n / m)) / W).sum + C * n + C * L)
    (hmom₁ : (ranks.map fun r : ℕ => (1 / (W : ℝ)) * ((r : ℝ) / m)).sum ≤ q₁)
    (hmomτ : (ranks.map fun r : ℕ => (1 / (W : ℝ)) * ((r : ℝ) / m) ^ τ).sum ≤ qτ) :
    ∀ n, 1 ≤ n → T n ≤ C / (1 - q₁) * n + C / (1 - qτ) * ((n : ℝ) ^ τ * L) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  -- the node type: atom counts, the children by position in the rank list
  let arity : Width → ℕ := children m ranks
  have harity (x : Width) (hx : m ≤ x.val) : arity x = ranks.length := by
    simp [arity, children, hx]
  have hf (x : Width) (hx : m ≤ x.val) : 1 ≤ x.val / m :=
    (Nat.one_le_div_iff (by omega)).mpr hx
  let rk : (x : Width) → Fin (arity x) → ℕ := fun x i =>
    if hx : m ≤ x.val then ranks[(Fin.cast (harity x hx) i).val] else 0
  let child : (x : Width) → Fin (arity x) → Width := fun x i =>
    if hx : m ≤ x.val then
      ⟨ranks[(Fin.cast (harity x hx) i).val] * (x.val / m), Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by have := hpos _ (List.getElem_mem (Fin.cast (harity x hx) i).isLt); omega)
          (by have := hf x hx; omega))⟩
    else x
  have hsum (x : Width) (hx : m ≤ x.val) (g : ℕ → ℝ) :
      ∑ i : Fin (arity x), g (rk x i) = (ranks.map g).sum := by
    rw [← Fin.sum_univ_fun_getElem ranks g]
    exact Fintype.sum_equiv (finCongr (harity x hx)) _ _ fun i => by simp [rk, hx]
  have hchild (x : Width) (hx : m ≤ x.val) (i : Fin (arity x)) :
      (child x i).val = rk x i * (x.val / m) := by
    simp [child, rk, hx]
  have key := StoppedRecurrence.stopped_closed (fun x : Width => x.val) arity child rk
    (fun _ _ => 1 / (W : ℝ)) (fun x => T x.val) m hm0 hτ hC hL hq₁ hqτ0 hqτ
    (fun _ _ => by positivity) (fun x => x.property)
    (fun x hx => hleaf x.val x.property hx)
    (fun x hx i => by
      rw [hchild x hx i]
      have hrm : rk x i < m := by
        simp only [rk, hx, dite_true]; exact hle _ (List.getElem_mem _)
      have h1 := hf x hx
      have h2 : m * (x.val / m) ≤ x.val := Nat.mul_div_le _ _
      have h3 : rk x i * (x.val / m) + x.val / m ≤ m * (x.val / m) := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hrm
      omega)
    (fun x hx i => by
      rw [hchild x hx i]
      push_cast
      have hd : ((x.val / m : ℕ) : ℝ) ≤ (x.val : ℝ) / m := Nat.cast_div_le
      have hr0 : (0 : ℝ) ≤ rk x i := Nat.cast_nonneg _
      calc (rk x i : ℝ) * ((x.val / m : ℕ) : ℝ) ≤ (rk x i : ℝ) * ((x.val : ℝ) / m) :=
            mul_le_mul_of_nonneg_left hd hr0
        _ = (rk x i : ℝ) / m * x.val := by ring)
    (fun x hx => by
      have h := hnode x.val hx
      have hs := hsum x hx (fun r : ℕ => T (r * (x.val / m)) / W)
      have hs' : ∑ i, 1 / (W : ℝ) * T (child x i).val = ∑ i : Fin (arity x), T (rk x i * (x.val / m)) / W :=
        Finset.sum_congr rfl fun i _ => by rw [hchild x hx i]; ring
      rw [hs', hs]
      exact h)
    (fun x hx => by
      have hs := hsum x hx (fun r : ℕ => (1 / (W : ℝ)) * ((r : ℝ) / m))
      rw [hs]; exact hmom₁)
    (fun x hx => by
      have hs := hsum x hx (fun r : ℕ => (1 / (W : ℝ)) * ((r : ℝ) / m) ^ τ)
      rw [hs]; exact hmomτ)
  intro n hn
  exact key ⟨n, hn⟩

end IntegerMultBounds.MathlibTM2.M8.RevMachine
