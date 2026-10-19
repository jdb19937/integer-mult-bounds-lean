module

public import IntegerMultBounds.Networks.GroupedModuleFrames

/-! Lower actual framed instructions to same-wire linear factors and unchanged
scalar gates. Product lists execute in reverse order because linear-map
multiplication composes right to left. Correctness concerns actual register
states; factor counts here are instruction counts, not tape runtimes. -/

@[expose] public section

namespace IntegerMultBounds.Networks.FramedFactorExecution

variable {ι R E : Type*} [DecidableEq ι] [CommRing R]
  [AddCommGroup E] [Module R E]

inductive Instruction (ι R E : Type*) [CommRing R] [AddCommGroup E] [Module R E] where
  | linear (wire : ι) (op : E →ₗ[R] E)
  | gate (g : Circuit.Gate ι R)

def execute : Instruction ι R E → (ι → E) → (ι → E)
  | .linear i op, x => Function.update x i (op (x i))
  | .gate g, x => FramedCircuit.moduleGate g x

def run : List (Instruction ι R E) → (ι → E) → (ι → E)
  | [], x => x
  | instr :: rest, x => run rest (execute instr x)

theorem run_append (p q : List (Instruction ι R E)) (x : ι → E) :
    run (p ++ q) x = run q (run p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons instr rest ih => exact ih _

/-- Place every factor on its original physical wire, in execution order. -/
def onWire (i : ι) (fs : List (E →ₗ[R] E)) : List (Instruction ι R E) :=
  fs.reverse.map (Instruction.linear i)

/-- Consume one factor list for each actual edge; scalar gates consume none.
The correctness premise below guarantees that the supplied lists match exactly. -/
def lower : List (FramedCircuit.Instruction ι R E) → List (List (E →ₗ[R] E)) →
    List (Instruction ι R E)
  | [], _ => []
  | .edge i _ _ :: rest, fs => onWire i (fs.headD []) ++ lower rest fs.tail
  | .gate g :: rest, fs => .gate g :: lower rest fs

def gates : List (Instruction ι R E) → List (Circuit.Gate ι R)
  | [] => []
  | .linear _ _ :: rest => gates rest
  | .gate g :: rest => g :: gates rest

def originalGates : List (FramedCircuit.Instruction ι R E) → List (Circuit.Gate ι R)
  | [] => []
  | .edge _ _ _ :: rest => originalGates rest
  | .gate g :: rest => g :: originalGates rest

omit [DecidableEq ι] in
@[simp] theorem gates_append (p q : List (Instruction ι R E)) :
    gates (p ++ q) = gates p ++ gates q := by
  induction p with
  | nil => rfl
  | cons instr rest ih => cases instr <;> simp [gates, ih]

omit [DecidableEq ι] in
@[simp] theorem gates_onWire (i : ι) (fs : List (E →ₗ[R] E)) : gates (onWire i fs) = [] := by
  unfold onWire
  generalize fs.reverse = gs
  induction gs with
  | nil => rfl
  | cons f gs ih => exact ih

def linearCount : List (Instruction ι R E) → ℕ
  | [] => 0
  | .linear _ _ :: rest => 1 + linearCount rest
  | .gate _ :: rest => linearCount rest

omit [DecidableEq ι] in
@[simp] theorem linearCount_append (p q : List (Instruction ι R E)) :
    linearCount (p ++ q) = linearCount p + linearCount q := by
  induction p with
  | nil => simp [linearCount]
  | cons instr rest ih => cases instr <;> simp [linearCount, ih, Nat.add_assoc]

omit [DecidableEq ι] in
@[simp] theorem linearCount_onWire (i : ι) (fs : List (E →ₗ[R] E)) :
    linearCount (onWire i fs) = fs.length := by
  have aux (gs : List (E →ₗ[R] E)) :
      linearCount (gs.map (Instruction.linear i)) = gs.length := by
    induction gs with
    | nil => rfl
    | cons f gs ih => simp [linearCount, ih, Nat.add_comm]
  simpa [onWire] using aux fs.reverse

omit [DecidableEq ι] in
/-- Every lowered instruction is either one linear factor or one scalar gate. -/
theorem length_eq (p : List (Instruction ι R E)) :
    p.length = linearCount p + (gates p).length := by
  induction p with
  | nil => rfl
  | cons instr rest ih => cases instr <;> simp [linearCount, gates, ih] <;> omega

omit [DecidableEq ι] in
@[simp] theorem originalGates_append (p q : List (FramedCircuit.Instruction ι R E)) :
    originalGates (p ++ q) = originalGates p ++ originalGates q := by
  induction p with
  | nil => rfl
  | cons instr rest ih => cases instr <;> simp [originalGates, ih]

omit [DecidableEq ι] in
@[simp] theorem originalGates_map (gs : Circuit.Program ι R) :
    originalGates (E := E) (gs.map FramedCircuit.Instruction.gate) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [originalGates, ih]

@[simp] theorem originalGates_edges (current desired : ι → FramedCircuit.Frame R E)
    (wires : List ι) : originalGates (FramedCircuit.edges current desired wires) = [] := by
  induction wires generalizing current with
  | nil => rfl
  | cons i wires ih => simp [FramedCircuit.edges, originalGates, ih]

section Grouped
variable {L : Type*} [DecidableEq R]

@[simp] theorem originalGates_compileFramed (g : GroupedCircuit.Group ι R)
    (current : ι → FramedCircuit.Frame R E) (D : FramedCircuit.Frame R E) :
    originalGates (GroupedCircuit.compileFramed g current D) = GroupedCircuit.compile g := by
  simp [GroupedCircuit.compileFramed]

end Grouped
end IntegerMultBounds.Networks.FramedFactorExecution
