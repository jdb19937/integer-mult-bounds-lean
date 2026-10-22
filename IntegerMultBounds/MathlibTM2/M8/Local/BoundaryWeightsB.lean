module

public import IntegerMultBounds.MathlibTM2.M8.Local.ServingWeightsB

/-! Boundary observations include garbage in slots not yet allocated. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
noncomputable section
open Classical

/-- The proposed garbage observation restricted to future auxiliary slots. -/
def futureWeights (b : Nat) (g : Reg →₀ ZMod 2) : Reg →₀ ZMod 2 :=
  g.filter fun r => match r with
    | .aux s => b ≤ s
    | _ => False

@[simp] theorem futureWeights_aux (b s : Nat) (g : Reg →₀ ZMod 2) :
    futureWeights b g (.aux s) = if b ≤ s then g (.aux s) else 0 := by simp [futureWeights, Finsupp.filter_apply]

/-- Allocating the next slot transfers precisely its old garbage weight to the frontier. -/
theorem futureWeights_succ (b : Nat) (g : Reg →₀ ZMod 2) :
    futureWeights b g = Finsupp.single (.aux b) (g (.aux b)) + futureWeights (b + 1) g := by
  ext r
  cases r with
  | x n => simp [futureWeights]
  | y n => simp [futureWeights]
  | aux s =>
    by_cases he : s = b
    · subst s; simp
    · by_cases hb : b ≤ s
      · have hs : b + 1 ≤ s := by omega
        simp [hb, hs, he]
      · have hs : ¬b + 1 ≤ s := by omega
        simp [hb, hs, he]

/-- The garbage observation of a fresh interval plus that of all later slots. -/
theorem futureWeights_split (b m : Nat) (g : Reg →₀ ZMod 2) :
    futureWeights b g =
      ((List.range' b m).map fun s => Finsupp.single (.aux s) (g (.aux s))).sum +
        futureWeights (b + m) g := by
  induction m generalizing b with
  | zero => simp
  | succ m ih =>
    rw [futureWeights_succ b g, ih (b + 1)]
    simp [List.range'_succ, add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Live uses plus the untouched garbage of future slots form the compiler boundary. -/
def boundaryWeights (D : Dag) (k : Nat) (st : State) (c : Use → ZMod 2)
    (g : Reg →₀ ZMod 2) : Reg →₀ ZMod 2 :=
  D.pendingWeights k st c + futureWeights st.next g

@[simp] theorem boundaryWeights_start (D : Dag) (c : Use → ZMod 2) (g : Reg →₀ ZMod 2) :
    boundaryWeights D 0 Dag.start c g = futureWeights 0 g := by
  simp [boundaryWeights, Dag.pendingWeights, Dag.start]

/-- A proposed garbage vector supported in the allocated slots leaves only root
observations at the terminal boundary. -/
theorem boundaryWeights_final (D : Dag) (hv : D.Valid) (targets : Nat → List Nat) (t : Nat)
    (c : Use → ZMod 2) (g : Reg →₀ ZMod 2)
    (hc : ∀ r < D.rootCount, c (.root r) = ((targets r).count t : ZMod 2))
    (hg : ∀ s, D.compile.next ≤ s → g (.aux s) = 0) :
    boundaryWeights D D.N D.compile c g = rootWeights D targets t := by
  have hf : futureWeights D.compile.next g = 0 := by
    ext r
    cases r with
    | aux s => by_cases hs : D.compile.next ≤ s <;> simp [hs, hg s]
    | x n => simp [futureWeights]
    | y n => simp [futureWeights]
  rw [boundaryWeights, hf, add_zero, D.pendingWeights_final hv targets t c hc]

end
end IntegerMultBounds.MathlibTM2.M8.Local.AdjointB
