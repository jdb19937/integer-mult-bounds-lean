module

public import IntegerMultBounds.MathlibTM2.Layer.Basic
public import IntegerMultBounds.Networks.Certificates.T16.Impl.LayerProgram

/-!
# One network node of the layer recursion

The node is the T16 complex network: it acts on banks `Wire → Arrays m k` with `m = 73` and the
wires `NWire = Fin 14336 ⊕ Fin 8` (the 14,336 data families and eight private scratch centres).
Its program (`program`, the T16 layer program `Impl.layerProgram`) lists factors `(wire, (q, v))`
with `q = ±1` (child calls), half-integral rational gates, translations by vectors with a zero
coordinate, slot XORs `x_j ← x_j + x_i` and slot phases `i^{c x_i}`, in execution order and
independently of the column count `k`. The direction lists `ds` of the earlier network are kept as
a parameter of `program` and are not used.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks BinaryWalsh ComplexFramedExecution
open IntegerMultBounds.Networks.Certificates.T16

/-- Label dimension of the complex network. -/
abbrev m : ℕ := 73

/-- Wire roles of the complex network: the data families and the private centres. -/
abbrev NWire := Streams.NodeUnit

/-- The data families of a node. -/
abbrev DWire := Fin 14336

/-- A network instruction. -/
inductive Instr where
  | factor (w : NWire) (g : ZMod 4 × BinaryWalsh.Address m)
  | gate (g : Circuit.Gate NWire ℚ)
  | trans (w : NWire) (v : BinaryWalsh.Address m)
  | xor (w : NWire) (i j : Fin m)
  | phase (w : NWire) (i : Fin m) (c : ZMod 4)

/-- The machine instruction of a layer instruction. -/
def ofK : Impl.KInstr NWire → Instr
  | .factor w g => .factor w g
  | .gate g => .gate g
  | .trans w v => .trans w v
  | .xor w i j => .xor w i j
  | .phase w i c => .phase w i c

/-- The network program (the direction lists are not used). -/
@[irreducible] noncomputable def program (_ds : Directions) : List Instr := Impl.layerProgram.map ofK

theorem program_eq (ds : Directions) : program ds = Impl.layerProgram.map ofK := by
  unfold program; rfl

/-- The vendored factor operator, as a function. -/
noncomputable def vf (k : ℕ) (g : ZMod 4 × BinaryWalsh.Address m) :
    BinaryColumns.Arrays m k → BinaryColumns.Arrays m k :=
  fun f => BinaryColumns.vectorFactor k g f

/-- Whether an instruction is a translation, slot XOR or slot phase. -/
def Instr.IsMono : Instr → Prop
  | .trans _ _ => True
  | .xor _ _ _ => True
  | .phase _ _ _ => True
  | _ => False

/-- The instructions of the program run on the machine. -/
def Instr.Fit : Instr → Prop
  | .factor _ g => g.1 = 1 ∨ g.1 = -1
  | .gate g => ∀ t ∈ g.terms, (2 * t.2).den = 1
  | .trans _ v => ∃ x, v x = 0
  | .xor _ i j => i ≠ j
  | .phase _ _ _ => True

theorem program_fit (ds : Directions) : ∀ i ∈ program ds, i.Fit := by
  intro i hi
  rw [program_eq, List.mem_map] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  have := Impl.layerProgram_fit k hk
  cases k <;> exact this

/-- Gate coefficients of the network are halves of integers. -/
theorem program_gate_coeff (ds : Directions) (g : Circuit.Gate NWire ℚ) (hg : Instr.gate g ∈ program ds)
    (t : NWire × ℚ) (ht : t ∈ g.terms) : (2 * t.2).den = 1 :=
  program_fit ds _ hg t ht

end IntegerMultBounds.MathlibTM2.Layer
