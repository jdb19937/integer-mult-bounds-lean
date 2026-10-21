module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SemFiber
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SemViews

/-!
# Reversed interchanges of views as moves of atom states

On a field of `m f` atoms, the reversed interchange of the view `sub 0 (r f)` (`RevT`) is, on
every fiber, the twisted interchanges of the reversed pivots `revPivots m r` (`call_link`): a
block call of rank `r` realizes the twisted action of its pivots. The reversed interchange of all
atoms is the node theorem's reading `(σ(C d), σ(C h))` (`full_link`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics

noncomputable section
open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume index)
open Machine.FlatCoordinateLayout (rank)
open ReversedExchange (revPivots)
open TwistedExchange (revSwaps atomRev twist)
open Matrix

variable {m f b : ℕ} {v : Descriptor}

local instance : NeZero (prime ^ b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

theorem prime_pow_mul (k : ℕ) : prime ^ (k * b) = (prime ^ b) ^ k := by rw [Nat.mul_comm, pow_mul]

theorem rank_lt (y : Fin (m * f) → ZMod (prime ^ b)) : (rank y).val < (prime ^ b) ^ (m * f) := (rank y).isLt

/-- **A block call's view.** The reversed interchange of the view `sub 0 (r f)` moves every atom
state's record to the state's twisted reversed pivots. -/
theorem call_link (hw : v.width = (m * f) * b) {r : ℕ} (hr : r ≤ m) (In Out : Fin (volume prime v) → ZMod 2)
    (hT : RevT prime b (r * f) (RevMachine.sub prime b (m * f) 0 (r * f) v) (ext In) (ext Out))
    (x : RecursiveScalarCoordinates.Address (m * f) b v) (s : Rev.Addr m (SA f b)) :
    Out (pos hw x s) = In (pos hw x (revSwaps (atomRev f) (revPivots m r) s)) := by
  set Q := prime ^ b
  have hQ : 0 < Q := pow_pos Networks.Shared50ModularControl.prime_prime.pos b
  have hq : 0 < prime := Networks.Shared50ModularControl.prime_prime.pos
  have hc : r * f ≤ m * f := Nat.mul_le_mul_right _ hr
  set H := (rank (AtomOps.refine s.1)).val
  set D := (rank (AtomOps.refine s.2)).val
  have hH : H < Q ^ (m * f) := rank_lt _
  have hD : D < Q ^ (m * f) := rank_lt _
  have hsplit : Q ^ (m * f) = Q ^ (r * f) * Q ^ (m * f - r * f) := by
    rw [← pow_add, Nat.add_sub_cancel' hc]
  have hp1 : 0 < Q ^ (m * f - r * f) := pow_pos hQ _
  have hp2 : 0 < Q ^ (r * f) := pow_pos hQ _
  have key := revT_sub_apply (q := prime) (w := b) (n := m * f) (s := 0) (c := r * f) hq hw (by omega) hT
    (a := x.beforeRows.val) (row := x.row.val) (before := x.before.val) (mid := x.middle.val)
    (after := x.after.val) (hp := 0) (hc := H / Q ^ (m * f - r * f)) (hs := H % Q ^ (m * f - r * f))
    (dp := D / Q ^ (r * f)) (dc := D % Q ^ (r * f)) (ds := 0)
    x.beforeRows.isLt x.row.isLt x.before.isLt (by simp)
    (by rw [prime_pow_mul, Nat.div_lt_iff_lt_mul hp1, ← hsplit]; exact hH)
    (by rw [prime_pow_mul, Nat.sub_zero]; exact Nat.mod_lt _ hp1) x.middle.isLt
    (by rw [prime_pow_mul, Nat.sub_zero, Nat.div_lt_iff_lt_mul hp2, Nat.mul_comm, ← hsplit]; exact hD)
    (by rw [prime_pow_mul]; exact Nat.mod_lt _ hp2) (by simp) x.after.isLt
  simp only [prime_pow_mul, zero_mul, zero_add, Nat.sub_zero, pow_zero, mul_one, add_zero] at key
  rw [Nat.div_add_mod' H, Nat.div_add_mod' D,
    ← rank_head hc (AtomOps.refine s.1) (AtomOps.refine s.2) _ (refine_swap_fst s),
    ← rank_tail hc (AtomOps.refine s.1) (AtomOps.refine s.2) _ (refine_swap_snd s)] at key
  rw [← ext_apply Out, ← ext_apply In, pos_val, pos_val]
  exact key

/-- **The full view.** Every index of a field of `m f` atoms is an atom state's, and the node
theorem's reading of the state is at the reversed interchange of the index. -/
theorem full_pos (hw : v.width = (m * f) * b) {a row before H mid D after : ℕ} (ha : a < v.beforeRows)
    (hrow : row < v.rows) (hb : before < v.beforeH) (hH : H < prime ^ ((m * f) * b)) (hm : mid < v.between)
    (hD : D < prime ^ ((m * f) * b)) (haf : after < v.afterD) :
    ∃ x s, (pos hw x s).val = index prime v a row before H mid D after ∧
      (pos hw x (twist (atomRev f) (Rev.revS (d := m) (atomScalar prime b f) *ᵥ s.2),
        twist (atomRev f) (Rev.revS (d := m) (atomScalar prime b f) *ᵥ s.1))).val =
        index prime v a row before (revAtoms (prime ^ b) (m * f) D) mid (revAtoms (prime ^ b) (m * f) H) after := by
  have hH' : H < (prime ^ b) ^ (m * f) := by rwa [← prime_pow_mul]
  have hD' : D < (prime ^ b) ^ (m * f) := by rwa [← prime_pow_mul]
  set A : RecursiveScalarCoordinates.Address (m * f) b v :=
    ⟨⟨a, ha⟩, ⟨row, hrow⟩, ⟨before, hb⟩,
      Machine.FlatCoordinateLayout.coordinates (Q := prime ^ b) (⟨H, hH'⟩ : Fin ((prime ^ b) ^ (m * f))),
      ⟨mid, hm⟩, Machine.FlatCoordinateLayout.coordinates (Q := prime ^ b) (⟨D, hD'⟩ : Fin ((prime ^ b) ^ (m * f))),
      ⟨after, haf⟩⟩
  have rH : (rank (Q := prime ^ b) A.h).val = H := by
    have := Machine.FlatCoordinateLayout.rank_coordinates (Q := prime ^ b) (⟨H, hH'⟩ : Fin ((prime ^ b) ^ (m * f)))
    exact congrArg Fin.val this
  have rD : (rank (Q := prime ^ b) A.d).val = D := by
    have := Machine.FlatCoordinateLayout.rank_coordinates (Q := prime ^ b) (⟨D, hD'⟩ : Fin ((prime ^ b) ^ (m * f)))
    exact congrArg Fin.val this
  refine ⟨A, stateOf A, ?_, ?_⟩
  · rw [pos, withState_stateOf, RecursiveScalarCoordinates.index_val]
    exact congrArg₂ (fun h d => index prime v a row before h mid d after) rH rD
  · rw [pos_val]
    have e1 : AtomOps.refine (twist (atomRev f) (Rev.revS (d := m) (atomScalar prime b f) *ᵥ (stateOf A).2)) =
        (A.d : Fin (m * f) → ZMod (prime ^ b)) ∘ Fin.rev := by
      funext k
      rw [refine_twist, Function.comp_apply]
      obtain ⟨i, l, hk⟩ := exists_at k.rev
      rw [hk, AtomOps.refine_at]; rfl
    have e2 : AtomOps.refine (twist (atomRev f) (Rev.revS (d := m) (atomScalar prime b f) *ᵥ (stateOf A).1)) =
        (A.h : Fin (m * f) → ZMod (prime ^ b)) ∘ Fin.rev := by
      funext k
      rw [refine_twist, Function.comp_apply]
      obtain ⟨i, l, hk⟩ := exists_at k.rev
      rw [hk, AtomOps.refine_at]; rfl
    rw [e1, e2]
    have r1 := rank_comp_rev (Q := prime ^ b) (k := m * f) A.d
    have r2 := rank_comp_rev (Q := prime ^ b) (k := m * f) A.h
    rw [rD] at r1
    rw [rH] at r2
    exact congrArg₂ (fun h d => index prime v A.beforeRows.val A.row.val A.before.val h A.middle.val d A.after.val) r1 r2

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics
