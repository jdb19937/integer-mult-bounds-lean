module

public import IntegerMultBounds.MathlibTM2.M8.Local.InternalBoundaryWeightsB

/-! Soundness of local use-coefficient equations for the actual compiler covariance. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
noncomputable section
open Classical

/-- Local equations for a proposed backward use weight and garbage coefficient vector.
The kept use of an internal node allocates no fresh slot and needs no allocation equation. -/
structure UseRecurrence (D : Dag) (c : Use → ZMod 2) (g : Reg →₀ ZMod 2) : Prop where
  leaf : ∀ k, k < D.v → ∀ u ∈ D.freeUses k,
    c u = g (.aux ((D.step (D.compileTo k) k).pend u))
  copy : ∀ k, D.v ≤ k → k < D.N → ∀ u ∈ (D.freeUses k).tail,
    c u = g (.aux ((D.step (D.compileTo k) k).pend u))
  argument : ∀ k, D.v ≤ k → k < D.N → ∀ side,
    c (.gate k side) = ((D.freeUses k).map c).sum +
      match D.link k with
      | none => 0
      | some (o, t, pos) => if side = o then c (.gate t pos) else 0

private theorem compileTo_step (D : Dag) (k : Nat) :
    D.compileTo (k + 1) = D.step (D.compileTo k) k := by
  simp [Dag.compileTo, List.range_succ, List.foldl_append]

/-- Composing the local boundary identities proves the backward observation for
all compiler prefixes, including arbitrary dirty auxiliary inputs. -/
theorem UseRecurrence.prefix (D : Dag) (hv : D.Valid) (c : Use → ZMod 2)
    (g : Reg →₀ ZMod 2) (h : UseRecurrence D c g) (k : Nat) (hk : k ≤ D.N) :
    AuxEq (pullOps ((D.compileTo k).ops.map D.vop)
      (boundaryWeights D k (D.compileTo k) c g)) (futureWeights 0 g) := by
  induction k with
  | zero =>
    intro s
    simp [Dag.compileTo, boundaryWeights, Dag.pendingWeights, Dag.start, pullOps]
  | succ k ih =>
    have hkN : k < D.N := by omega
    have hi := D.inv_compileTo hv (fun _ => 0) k (by omega)
    have hold := ih (by omega)
    rw [compileTo_step]
    by_cases hn : k < D.v
    · have hs := boundary_pullOps_step_leaf D hv k hn (D.compileTo k) c g (h.leaf k hn)
      exact fun s => (hs s).trans (hold s)
    · have hn' : D.v ≤ k := Nat.le_of_not_lt hn
      cases hu : D.freeUses k with
      | nil => exact (hv.free_ne k hkN hu).elim
      | cons u us =>
        have hc : ∀ v ∈ us, c v = g (.aux ((D.step (D.compileTo k) k).pend v)) := by
          intro v hv'
          exact h.copy k hn' hkN v (by simpa only [hu, List.tail_cons] using hv')
        cases hl : D.link k with
        | none =>
          have ha : ∀ side, c (.gate k side) = ((D.freeUses k).map c).sum := by
            intro side
            simpa only [hl, add_zero] using h.argument k hn' hkN side
          have hs := boundary_pullOps_step_unlinked D hv k hn' hkN hl
            (D.compileTo k) hi u us hu c g hc ha
          exact fun s => (congrArg (fun w => w (Reg.aux s)) hs).trans (hold s)
        | some l =>
          obtain ⟨o, t, pos⟩ := l
          have ha : ∀ side, c (.gate k side) = ((D.freeUses k).map c).sum +
              if side = o then c (.gate t pos) else 0 := by
            intro side
            simpa only [hl] using h.argument k hn' hkN side
          have hs := boundary_pullOps_step_linked D hv k hn' hkN o t pos hl
            (D.compileTo k) hi u us hu c g hc ha
          exact fun s => (congrArg (fun w => w (Reg.aux s)) hs).trans (hold s)

/-- Kernel-checking the local equations and root weights suffices to identify
all actual readout coefficients; no concrete compiler prefix is reduced. -/
theorem UseRecurrence.cov_eq (D : Dag) (hv : D.Valid) (targets : Nat → List Nat)
    (t : Nat) (c : Use → ZMod 2) (g : Reg →₀ ZMod 2) (h : UseRecurrence D c g)
    (hroot : ∀ r < D.rootCount, c (.root r) = ((targets r).count t : ZMod 2))
    (hfresh : ∀ s, D.compile.next ≤ s → g (.aux s) = 0) (s : Nat) :
    D.cov targets s t = g (.aux s) := by
  have hp := h.prefix D hv c g D.N le_rfl s
  change (pullOps D.opsB (boundaryWeights D D.N D.compile c g)) (Reg.aux s) = _ at hp
  rw [boundaryWeights_final D hv targets t c g hroot hfresh] at hp
  rw [cov_eq_compiler_pullOps]
  simpa only [futureWeights_aux, Nat.zero_le, ite_true] using hp

end
end IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
