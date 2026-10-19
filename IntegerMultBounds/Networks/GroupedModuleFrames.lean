module

public import IntegerMultBounds.Networks.GroupedFrames

/-! The actual grouped common-frame compiler over an arbitrary module. Scalar
coefficients and the exact physical incidence/label trace are unchanged when
the stored values live in another module, including complex-valued arrays
viewed as a rational module. -/

@[expose] public section

namespace IntegerMultBounds.Networks.GroupedModuleFrames

open GroupedCircuit GroupedFrames
variable {ι L R E : Type*} [DecidableEq ι] [CommRing R]
  [AddCommGroup E] [Module R E]

theorem moduleRun_append (p q : Circuit.Program ι R) (x : ι → E) :
    FramedCircuit.moduleRun (p ++ q) x =
      FramedCircuit.moduleRun q (FramedCircuit.moduleRun p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _

section Compiler
variable [DecidableEq R] (frameOf : L → FramedCircuit.Frame R E)

def profile (current : ι → L) : ι → FramedCircuit.Frame R E := fun i => frameOf (current i)

theorem after_profile (current : ι → L) (v : Vertex ι L R) :
    FramedCircuit.afterEdges (profile frameOf current) (fun _ => frameOf v.label) (touched v.group) =
      profile frameOf (after current v) := by
  funext i
  rw [FramedCircuit.afterEdges_apply]
  change (if i ∈ touched v.group then frameOf v.label else frameOf (current i)) =
    frameOf (RankTrace.finish current ((touched v.group).map fun j => (j, v.label)) i)
  rw [RankTrace.finish_align]
  split_ifs <;> rfl

/-- Compile the same labeled groups, now permitting any module-valued wires. -/
def compile (current : ι → L) : List (Vertex ι L R) → List (FramedCircuit.Instruction ι R E)
  | [] => []
  | v :: rest => compileFramed v.group (profile frameOf current) (frameOf v.label) ++
      compile (after current v) rest

/-- The grouped frame invariant holds for the actual scalar programs acting
by scalar multiplication on the module. -/
theorem compile_invariant (current : ι → L) (vs : List (Vertex ι L R)) (x : ι → E) :
    FramedCircuit.run (compile frameOf current vs) (FramedCircuit.encode (profile frameOf current) x) =
      FramedCircuit.encode (profile frameOf (finalLabels current vs))
        (FramedCircuit.moduleRun (compileGroups (vs.map Vertex.group)) x) := by
  induction vs generalizing current x with
  | nil => rfl
  | cons v rest ih =>
    rw [compile, FramedCircuit.run_append, compileFramed_invariant, after_profile, ih]
    simp only [List.map_cons, compileGroups, List.flatMap_cons, moduleRun_append, finalLabels]

/-- Append precisely the old compiler's sink incidence list. -/
def network (wires : List ι) (input output : ι → L) (vs : List (Vertex ι L R)) :
    List (FramedCircuit.Instruction ι R E) :=
  compile frameOf input vs ++ FramedCircuit.edges (profile frameOf (finalLabels input vs))
    (profile frameOf output) wires

/-- The label history is literally the existing global rank-accounting trace;
it is independent of the module that holds the wire values. -/
abbrev networkUpdates := GroupedFrames.networkUpdates (ι := ι) (L := L) (R := R)

theorem network_trace_final (wires : List ι) (hall : ∀ i, i ∈ wires)
    (input output : ι → L) (vs : List (Vertex ι L R)) :
    RankTrace.finish input (networkUpdates wires output vs) = output :=
  GroupedFrames.network_trace_final wires hall input output vs

/-- Extract ordered old/new frame pairs from the literal instruction list. -/
def edgePairs : List (FramedCircuit.Instruction ι R E) →
    List (FramedCircuit.Frame R E × FramedCircuit.Frame R E)
  | [] => []
  | .edge _ old next :: rest => (old, next) :: edgePairs rest
  | .gate _ :: rest => edgePairs rest

omit [DecidableEq ι] [DecidableEq R] in
@[simp] theorem edgePairs_append (p q : List (FramedCircuit.Instruction ι R E)) :
    edgePairs (p ++ q) = edgePairs p ++ edgePairs q := by
  induction p with
  | nil => rfl
  | cons instr p ih => cases instr <;> simp [edgePairs, ih]

omit [DecidableEq ι] [DecidableEq R] in
@[simp] theorem edgePairs_gates (rows : Circuit.Program ι R) :
    edgePairs (E := E) (rows.map FramedCircuit.Instruction.gate) = [] := by
  induction rows with
  | nil => rfl
  | cons g gs ih => exact ih

end Compiler

section Transfer

/-- Each scalar gate is a linear operator on any module-valued wire bank. -/
def gateLinear (g : Circuit.Gate ι R) : (ι → E) →ₗ[R] (ι → E) :=
  LinearMap.id + (LinearMap.single R (fun _ : ι => E) g.target).comp
    ((g.terms.map fun p => p.2 • (LinearMap.proj p.1 : (ι → E) →ₗ[R] E)).sum)

theorem gateLinear_apply (g : Circuit.Gate ι R) (x : ι → E) :
    gateLinear g x = FramedCircuit.moduleGate g x := by
  have hsum : ((g.terms.map fun p => p.2 • (LinearMap.proj p.1 : (ι → E) →ₗ[R] E)).sum) x =
      (g.terms.map fun p => p.2 • x p.1).sum := by
    induction g.terms with
    | nil => simp
    | cons p ps ih => simp [ih]
  funext i
  by_cases hi : i = g.target
  · subst i
    simp [gateLinear, FramedCircuit.moduleGate, hsum]
  · simp [gateLinear, FramedCircuit.moduleGate, hsum, hi]

/-- The actual compiled elementary program as a module-linear operator. -/
def runLinear : Circuit.Program ι R → ((ι → E) →ₗ[R] (ι → E))
  | [] => LinearMap.id
  | g :: gs => (runLinear gs).comp (gateLinear g)

theorem runLinear_apply (p : Circuit.Program ι R) (x : ι → E) :
    runLinear p x = FramedCircuit.moduleRun p x := by
  induction p generalizing x with
  | nil => rfl
  | cons g gs ih => simp only [runLinear, LinearMap.comp_apply, gateLinear_apply, ih, FramedCircuit.moduleRun_cons]

variable {F : Type*} [AddCommGroup F] [Module R F]

/-- Module-valued execution commutes with every linear change of value module. -/
theorem moduleGate_map (f : E →ₗ[R] F) (g : Circuit.Gate ι R) (x : ι → E) :
    FramedCircuit.moduleGate g (fun i => f (x i)) = fun i => f (FramedCircuit.moduleGate g x i) := by
  funext i
  by_cases hi : i = g.target
  · subst i
    simp [FramedCircuit.moduleGate, map_list_sum, List.map_map, Function.comp_def]
  · simp [FramedCircuit.moduleGate, hi]

theorem moduleRun_map (f : E →ₗ[R] F) (p : Circuit.Program ι R) (x : ι → E) :
    FramedCircuit.moduleRun p (fun i => f (x i)) = fun i => f (FramedCircuit.moduleRun p x i) := by
  induction p generalizing x with
  | nil => rfl
  | cons g gs ih => rw [FramedCircuit.moduleRun_cons, moduleGate_map, ih]; rfl

/-- Scalar module execution is exactly the original executable circuit. -/
theorem moduleRun_scalar (p : Circuit.Program ι R) (x : ι → R) :
    FramedCircuit.moduleRun p x = Circuit.run p x := by
  induction p generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [FramedCircuit.moduleRun_cons, ih, Circuit.run_cons]
    rfl

variable [Fintype ι]

/-- Every output value is the same finite scalar coefficient row applied to
module-valued inputs. No freeness or basis assumption is made on the module. -/
theorem moduleRun_coefficients (p : Circuit.Program ι R) (x : ι → E) (i : ι) :
    FramedCircuit.moduleRun p x i = ∑ j, Circuit.run p (Pi.single j 1) i • x j := by
  have hsingle (j : ι) : FramedCircuit.moduleRun p (Pi.single j (x j)) =
      fun i => Circuit.run p (Pi.single j 1) i • x j := by
    have h := moduleRun_map (LinearMap.toSpanSingleton R E (x j)) p (Pi.single j 1)
    rw [moduleRun_scalar] at h
    have he : (fun i => (LinearMap.toSpanSingleton R E (x j)) ((Pi.single j (1 : R) : ι → R) i)) = Pi.single j (x j) := by
      funext i
      by_cases hi : i = j <;> simp [hi]
    rw [he] at h
    exact h
  rw [← runLinear_apply]
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [runLinear_apply, hsingle]

/-- A scalar routing identity transfers directly to arbitrary module values. -/
theorem moduleRun_route (p : Circuit.Program ι R) (route : ι → ι)
    (h : ∀ x : ι → R, Circuit.run p x = fun i => x (route i)) (x : ι → E) :
    FramedCircuit.moduleRun p x = fun i => x (route i) := by
  funext i
  rw [moduleRun_coefficients]
  simp [h, Pi.single_apply]

end Transfer
section RoutedNetwork
variable [Fintype ι] [DecidableEq R] (frameOf : L → FramedCircuit.Frame R E)

end RoutedNetwork

end IntegerMultBounds.Networks.GroupedModuleFrames
