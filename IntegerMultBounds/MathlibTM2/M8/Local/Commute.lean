module

public import IntegerMultBounds.MathlibTM2.M8.Local.Word

/-!
# Reordering commuting gates

Two gates commute when neither reads the other's target (`GateCommute`); they may write the same
register. Commuting blocks swap (`run_append_comm`), a permutation of pairwise commuting gates
runs alike (`run_perm`), and a program splits into the gates of a predicate followed by the
others when every gate outside it commutes with every later gate inside it (`run_split`). Two XOR
programs that run alike have reverses that run alike (`run_reverse_congr`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

open Networks

section
variable {ι R : Type*} [DecidableEq ι] [CommRing R]

/-- Neither gate reads the other's target. -/
def GateCommute (g h : Circuit.Gate ι R) : Prop :=
  (∀ t ∈ h.terms, t.1 ≠ g.target) ∧ ∀ t ∈ g.terms, t.1 ≠ h.target

omit [DecidableEq ι] [CommRing R] in
theorem GateCommute.symm {g h : Circuit.Gate ι R} (hc : GateCommute g h) : GateCommute h g :=
  ⟨hc.2, hc.1⟩

/-- A gate's sum ignores a write to a register it does not read. -/
theorem terms_sum_update (h : Circuit.Gate ι R) (c : ι → R) (k : ι) (a : R)
    (hk : ∀ t ∈ h.terms, t.1 ≠ k) :
    (h.terms.map fun p => p.2 * Function.update c k a p.1).sum =
      (h.terms.map fun p => p.2 * c p.1).sum := by
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [Function.update_of_ne (hk p hp)]

theorem gate_run_comm {g h : Circuit.Gate ι R} (hc : GateCommute g h) (c : ι → R) :
    h.run (g.run c) = g.run (h.run c) := by
  simp only [Circuit.Gate.run]
  rw [terms_sum_update h c _ _ hc.1, terms_sum_update g c _ _ hc.2]
  by_cases he : g.target = h.target
  · rw [he]
    simp only [Function.update_self, Function.update_idem]
    congr 1
    ring
  · rw [Function.update_of_ne (Ne.symm he), Function.update_of_ne he]
    exact Function.update_comm he _ _ _

/-- A gate commuting with a program moves across it. -/
theorem run_cons_comm {g : Circuit.Gate ι R} :
    ∀ {p : Circuit.Program ι R}, (∀ h ∈ p, GateCommute g h) →
      ∀ c, Circuit.run (g :: p) c = Circuit.run (p ++ [g]) c
  | [], _, _ => rfl
  | h :: p, hp, c => by
    rw [Circuit.run_cons, List.cons_append, Circuit.run_cons,
      gate_run_comm (hp h List.mem_cons_self) c, ← Circuit.run_cons,
      run_cons_comm (fun h' hh => hp h' (List.mem_cons_of_mem _ hh)), Circuit.run_cons]

/-- **Commuting blocks swap.** -/
theorem run_append_comm :
    ∀ {p q : Circuit.Program ι R}, (∀ g ∈ p, ∀ h ∈ q, GateCommute g h) →
      Circuit.run (p ++ q) = Circuit.run (q ++ p)
  | [], q, _ => by simp
  | g :: p, q, hpq => by
    funext c
    have ih := run_append_comm (p := p) (q := q) fun g' hg h hh =>
      hpq g' (List.mem_cons_of_mem _ hg) h hh
    have hg := run_cons_comm (hpq g List.mem_cons_self) c
    rw [List.cons_append, Circuit.run_cons, ih]
    simp only [Circuit.run_cons, Circuit.run_append, Circuit.run_nil] at hg ⊢
    rw [hg]

/-- **Permutations** of pairwise commuting gates run alike. -/
theorem run_perm {p q : Circuit.Program ι R} (hpq : p.Perm q)
    (hc : ∀ g ∈ p, ∀ h ∈ p, GateCommute g h) : Circuit.run p = Circuit.run q := by
  induction hpq with
  | nil => rfl
  | cons g _ ih =>
    funext c
    rw [Circuit.run_cons, Circuit.run_cons,
      ih fun a ha b hb => hc a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)]
  | swap g h l =>
    funext c
    rw [Circuit.run_cons, Circuit.run_cons, Circuit.run_cons, Circuit.run_cons,
      gate_run_comm (hc h (by simp) g (by simp)) c]
  | trans h₁ _ ih₁ ih₂ =>
    rw [ih₁ hc, ih₂ fun a ha b hb => hc a (h₁.mem_iff.mpr ha) b (h₁.mem_iff.mpr hb)]

/-- **Splitting by a predicate.** If every gate outside `P` commutes with every later gate in
`P`, the program runs as its `P`-gates followed by the others. -/
theorem run_split {α : Type*} (f : α → Circuit.Gate ι R) (P : α → Bool) :
    ∀ {l : List α},
      l.Pairwise (fun a b => P a = false → P b = true → GateCommute (f a) (f b)) →
      Circuit.run (l.map f) = Circuit.run ((l.filter P).map f ++ (l.filter fun a => !P a).map f)
  | [], _ => rfl
  | a :: l, hl => by
    rw [List.pairwise_cons] at hl
    have ih := run_split f P hl.2
    funext c
    rw [List.map_cons, Circuit.run_cons, ih]
    cases ha : P a
    · have hcomm : ∀ h ∈ (l.filter P).map f, GateCommute (f a) h := by
        intro h hh
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hh
        exact hl.1 b (List.mem_filter.mp hb).1 ha (by simpa using (List.mem_filter.mp hb).2)
      have h1 := run_cons_comm hcomm c
      rw [List.filter_cons_of_neg (by simp [ha]), List.filter_cons_of_pos (by simp [ha])]
      simp only [List.map_cons, Circuit.run_cons, Circuit.run_append, Circuit.run_nil] at h1 ⊢
      rw [h1]
    · rw [List.filter_cons_of_pos (by simp [ha]), List.filter_cons_of_neg (by simp [ha]),
        List.map_cons, List.cons_append, Circuit.run_cons]

/-- Programs that run alike stay alike between the same prefix and suffix. -/
theorem run_congr_mid (a b : Circuit.Program ι R) {p q : Circuit.Program ι R}
    (h : Circuit.run p = Circuit.run q) : Circuit.run (a ++ p ++ b) = Circuit.run (a ++ q ++ b) := by
  funext c
  simp only [Circuit.run_append, h]

end

/-- **Reverses.** XOR programs that run alike have reverses that run alike. -/
theorem run_reverse_congr {ι : Type*} [DecidableEq ι] {p q : Circuit.Program ι (ZMod 2)}
    (hp : IsXorProg p) (hq : IsXorProg q) (h : Circuit.run p = Circuit.run q) :
    Circuit.run p.reverse = Circuit.run q.reverse := by
  funext c
  have hc : Circuit.run p (Circuit.run p.reverse c) = c := by
    have := xor_run_reverse hp.reverse c
    rwa [List.reverse_reverse] at this
  conv_rhs => rw [← hc, h, xor_run_reverse hq]

/-! ### XOR gates on the local registers -/

/-- Two XOR gates commute when neither reads the other's target. -/
theorem add_commute {dst src dst' src' : Reg} (h₁ : src' ≠ dst) (h₂ : src ≠ dst') :
    GateCommute (ReversibleFanout.add dst src) (ReversibleFanout.add dst' src') := by
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩ <;>
    simp only [ReversibleFanout.add, List.mem_singleton] at ht <;> subst ht <;> assumption

end IntegerMultBounds.MathlibTM2.M8.Local
