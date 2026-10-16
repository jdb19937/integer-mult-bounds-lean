module

public import IntegerMultBounds.MathlibTM2.Layer.Node

/-!
# Kernels through placements of active bits

A child computation acts on `k` active bits with arbitrary spectators. Placed on bits
`e : Fin k → Fin n` of a larger array, with the remaining bits as spectators, `C` on every
child bit becomes the product of the kernels on the placed bits (`view_Cfull`). Kernels on
distinct bits commute, so a product of forward kernels over any enumeration of all bits is
`Cfull` (`prod_perm_Cfull`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks BinaryWalsh BinaryPhase

variable {X Y : Type} {n k : ℕ}


/-! ### Products of commuting kernels -/

lemma pairwise_commute_kBit (q : ZMod 4) (l : List (Fin n)) :
    (l.map (kBit (X := X) q)).Pairwise Commute := by
  rw [List.pairwise_map]
  exact List.Pairwise.imp_of_mem (fun _ _ _ => kBit_commute q q _ _)
    (List.pairwise_of_forall (fun _ _ => trivial))

lemma Cfull_eq_map (X : Type) (n : ℕ) :
    Cfull X n = ((List.finRange n).map (kBit (X := X) 1)).prod := by
  rw [Cfull, List.ofFn_eq_map]

/-- A product of forward kernels over any enumeration of all bits is `Cfull`. -/
lemma prod_perm_Cfull (l : List (Fin n)) (hl : l.Perm (List.finRange n)) :
    (l.map (kBit (X := X) 1)).prod = Cfull X n := by
  rw [Cfull_eq_map]
  exact (hl.map _).prod_eq' (pairwise_commute_kBit 1 l)

/-! ### Viewing chosen bits as the active bits of a child -/

/-- Overwrite the bits `e` of `r` with `a`. -/
noncomputable def merge (e : Fin k → Fin n) (r : Fin n → ZMod 2) (a : Fin k → ZMod 2) : Fin n → ZMod 2 :=
  fun t => if h : ∃ i, e i = t then a h.choose else r t

/-- The child's view of an array: active bits `e`, spectators the original spectator and the
whole bit vector (whose bits `e` are overwritten). -/
noncomputable def view (e : Fin k → Fin n) (f : Arr Y n) : Arr (Y × (Fin n → ZMod 2)) k :=
  fun p => f (p.1.1, merge e p.1.2 p.2)

lemma merge_extract (e : Fin k → Fin n) (r : Fin n → ZMod 2) :
    merge e r (fun i => r (e i)) = r := by
  funext t
  simp only [merge]
  split_ifs with h
  · rw [h.choose_spec]
  · rfl

lemma merge_flip (e : Fin k → Fin n) (he : Function.Injective e) (r : Fin n → ZMod 2)
    (a : Fin k → ZMod 2) (i : Fin k) :
    merge e r (flip i a) = flip (e i) (merge e r a) := by
  funext t
  simp only [merge, flip, Pi.add_apply]
  by_cases h : ∃ j, e j = t
  · have hj := h.choose_spec
    rw [dite_eq_left h, dite_eq_left h]
    by_cases hi : h.choose = i
    · rw [hi] at hj ⊢; subst hj; simp
    · have : t ≠ e i := fun ht => hi (he (hj.trans ht))
      simp [hi, this]
  · rw [dite_eq_right h, dite_eq_right h]
    have : t ≠ e i := fun ht => h ⟨i, ht.symm⟩
    simp [this]

lemma kBit_view (e : Fin k → Fin n) (he : Function.Injective e) (q : ZMod 4) (i : Fin k)
    (f : Arr Y n) : kBit q i (view e f) = view e (kBit q (e i) f) := by
  funext p
  simp only [kBit_apply, view, merge_flip e he]

lemma prod_view (e : Fin k → Fin n) (he : Function.Injective e) (q : ZMod 4) (l : List (Fin k))
    (f : Arr Y n) :
    (l.map (kBit q)).prod (view e f) = view e ((l.map (fun i => kBit q (e i))).prod f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, kBit_view e he]

/-- Applying `C` to every child bit through the view is the product of kernels on the placed
bits. -/
theorem view_Cfull (e : Fin k → Fin n) (he : Function.Injective e) (f : Arr Y n)
    (y : Y) (r : Fin n → ZMod 2) :
    Cfull (Y × (Fin n → ZMod 2)) k (view e f) ((y, r), fun i => r (e i)) =
      ((List.finRange k).map (fun i => kBit 1 (e i))).prod f (y, r) := by
  rw [Cfull_eq_map, prod_view e he]
  simp only [view, merge_extract e]

/-- `C` on every bit is the product of `C` on the pieces of any partition of the bits. -/
theorem Cfull_pieces (pieces : List (List (Fin n))) (hperm : pieces.flatten.Perm (List.finRange n))
    (f : Arr X n) :
    Cfull X n f = (pieces.map fun l => (l.map (kBit (X := X) 1)).prod).prod f := by
  rw [← prod_perm_Cfull _ hperm, List.map_flatten, List.prod_flatten, List.map_map]
  rfl

end IntegerMultBounds.MathlibTM2.Layer
