module

public import IntegerMultBounds.MathlibTM2.M8.Local.WordB
public import Mathlib.Data.Finsupp.Basic

/-! Backward observation weights for arbitrary compiler operation lists.
This isolates scalar covariance from the concrete DAG and its certificates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
noncomputable section
open IntegerMultBounds.Networks
open Classical

section Pairing
variable {ι R : Type*} [DecidableEq ι] [CommRing R]

def pairing (w : ι →₀ R) (x : ι → R) : R := w.sum fun i a => a * x i

omit [DecidableEq ι] in
theorem pairing_add (w v : ι →₀ R) (x : ι → R) :
    pairing (w + v) x = pairing w x + pairing v x := by
  unfold pairing
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ a b => add_mul a b _)

omit [DecidableEq ι] in
theorem pairing_single (i : ι) (a : R) (x : ι → R) :
    pairing (Finsupp.single i a) x = a * x i := by
  simp [pairing]

theorem pairing_update (w : ι →₀ R) (x : ι → R) (i : ι) (a : R) :
    pairing w (Function.update x i (x i + a)) = pairing w x + w i * a := by
  unfold pairing Finsupp.sum
  calc
    _ = ∑ j ∈ w.support, (w j * x j + if j = i then w i * a else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases he : j = i
      · subst j; simp [mul_add]
      · simp [he]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      by_cases hi : i ∈ w.support
      · simp [hi]
      · have hw : w i = 0 := Finsupp.notMem_support_iff.mp hi
        simp [hw]

/-- Pulling an addition back adds the destination weight to the source weight. -/
def pullAdd (dst src : ι) (w : ι →₀ R) : ι →₀ R :=
  w + Finsupp.single src (w dst)

theorem pairing_pullAdd (dst src : ι) (w : ι →₀ R) (x : ι → R) :
    pairing (pullAdd dst src w) x =
      pairing w (Function.update x dst (x dst + x src)) := by
  rw [pullAdd, pairing_add, pairing_single, pairing_update]

theorem pairing_point (w : ι →₀ R) (i : ι) : pairing w (Pi.single i 1) = w i := by
  unfold pairing Finsupp.sum
  by_cases hi : i ∈ w.support
  · simp [Pi.single_apply, hi]
  · have hw : w i = 0 := Finsupp.notMem_support_iff.mp hi
    simp [Pi.single_apply, hi, hw]

omit [DecidableEq ι] in
theorem pairing_sum (ws : List (ι →₀ R)) (x : ι → R) :
    pairing ws.sum x = (ws.map fun w => pairing w x).sum := by
  induction ws with
  | nil => simp [pairing]
  | cons w ws ih => simp only [List.sum_cons, pairing_add, List.map_cons, ih]

end Pairing

/-- One operation's adjoint acts on finite register weights. -/
def pullOp : Op → (Reg →₀ ZMod 2) → (Reg →₀ ZMod 2)
  | .src s n => pullAdd (.aux s) (.x n)
  | .add p o _ => pullAdd (.aux p) (.aux o)
  | .copy p f _ => pullAdd (.aux f) (.aux p)

def pullOps (ops : List Op) (w : Reg →₀ ZMod 2) : Reg →₀ ZMod 2 := ops.foldr pullOp w

theorem pairing_pullOp (op : Op) (w : Reg →₀ ZMod 2) (x : Reg → ZMod 2) :
    pairing (pullOp op w) x = pairing w ((opGate op).run x) := by
  cases op <;> simp only [pullOp, opGate, ReversibleFanout.add_run, pairing_pullAdd]

/-- Adjoint evaluation is structural in the operation list, with no finiteness
or zero-state assumptions on the register contents. -/
theorem pairing_pullOps (ops : List Op) (w : Reg →₀ ZMod 2) (x : Reg → ZMod 2) :
    pairing (pullOps ops w) x = pairing w (Circuit.run (ops.map opGate) x) := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    rw [pullOps, List.foldr_cons, pairing_pullOp]
    exact ih ((opGate op).run x)

def rootWeights (D : Dag) (targets : Nat → List Nat) (t : Nat) : Reg →₀ ZMod 2 :=
  ((List.range D.rootCount).map fun j =>
    Finsupp.single (.aux (D.compile.pend (.root j))) ((targets j).count t : ZMod 2)).sum

theorem pairing_rootWeights (D : Dag) (targets : Nat → List Nat) (t : Nat)
    (x : Reg → ZMod 2) : pairing (rootWeights D targets t) x = D.readDelta targets x (.y t) := by
  rw [rootWeights, pairing_sum, D.readDelta_y]
  simp only [List.map_map, pairing_single, Function.comp_def]

/-- The actual readout coefficient is the initial slot's backward root weight. -/
theorem cov_eq_pullOps (D : Dag) (targets : Nat → List Nat) (s t : Nat) :
    D.cov targets s t = (pullOps D.sideB (rootWeights D targets t)) (.aux s) := by
  rw [Dag.cov, ← pairing_rootWeights, Dag.sideGatesB, ← pairing_pullOps, pairing_point]

end
end IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
