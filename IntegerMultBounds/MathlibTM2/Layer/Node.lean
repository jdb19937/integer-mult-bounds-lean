module

public import IntegerMultBounds.MathlibTM2.Layer.Basic

/-!
# One network node of the layer recursion

The vendored `h = 25` complex network acts on banks `Wire → Arrays m k` with `m = 25³`. Its
lowered program (`ComplexFramedExecution.lowered`) interleaves scalar gates with linear factors
`vectorFactor k (q, v)`. Here the program is recorded with its factor data: `program ds` lists
gates and factors `(wire, (q, v))` in execution order, independently of the column count `k`.
`runWith fac` executes it with an arbitrary implementation `fac` of the factors; with
`fac = vectorFactor k` it is the vendored lowered run, so the corrected run is the full forward
frame on every wire (`node_correct`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks BinaryWalsh ComplexFramedExecution ComplexEndpoints

/-- Label dimension of the complex network. -/
abbrev m : ℕ := 25 ^ 3

/-- Wire roles of the complex network. -/
abbrev NWire := ComplexFramedExecution.Wire

/-- A network instruction with its factor data. -/
inductive Instr where
  | factor (w : NWire) (g : ZMod 4 × BinaryWalsh.Address m)
  | gate (g : Circuit.Gate NWire ℚ)

/-- The skeleton of a framed instruction: its wire or gate, without frames. -/
inductive Skel where
  | edge (w : NWire)
  | gate (g : Circuit.Gate NWire ℚ)

/-- Forget the frames of a framed instruction. -/
def skel {E : Type*} [AddCommGroup E] [Module ℚ E] :
    FramedCircuit.Instruction NWire ℚ E → Skel
  | .edge w _ _ => .edge w
  | .gate g => .gate g

/-- Lower a skeleton with one direction list per edge, mirroring `FramedFactorExecution.lower`. -/
def lowerSkel : List Skel → Directions → List Instr
  | [], _ => []
  | .edge w :: rest, ds => (ds.headD []).reverse.map (Instr.factor w) ++ lowerSkel rest ds.tail
  | .gate g :: rest, ds => .gate g :: lowerSkel rest ds

section Skeleton

variable {E F : Type*} [AddCommGroup E] [Module ℚ E] [AddCommGroup F] [Module ℚ F]

lemma skel_edges (cur des : NWire → FramedCircuit.Frame ℚ E)
    (cur' des' : NWire → FramedCircuit.Frame ℚ F) (ws : List NWire) :
    (FramedCircuit.edges cur des ws).map skel = (FramedCircuit.edges cur' des' ws).map skel := by
  induction ws generalizing cur cur' with
  | nil => rfl
  | cons w ws ih =>
    simp only [FramedCircuit.edges, List.map_cons, skel]
    exact congrArg _ (ih _ _)

lemma skel_compileFramed (g : GroupedCircuit.Group NWire ℚ)
    (cur : NWire → FramedCircuit.Frame ℚ E) (D : FramedCircuit.Frame ℚ E)
    (cur' : NWire → FramedCircuit.Frame ℚ F) (D' : FramedCircuit.Frame ℚ F) :
    (GroupedCircuit.compileFramed g cur D).map skel =
      (GroupedCircuit.compileFramed g cur' D').map skel := by
  simp only [GroupedCircuit.compileFramed, List.map_append, List.map_map]
  rw [skel_edges cur _ cur' (fun _ => D')]
  rfl

lemma skel_compile {L : Type*} (FE : L → FramedCircuit.Frame ℚ E) (FF : L → FramedCircuit.Frame ℚ F)
    (cur : NWire → L) (vs : List (GroupedFrames.Vertex NWire L ℚ)) :
    (GroupedModuleFrames.compile FE cur vs).map skel =
      (GroupedModuleFrames.compile FF cur vs).map skel := by
  induction vs generalizing cur with
  | nil => rfl
  | cons v rest ih =>
      simp only [GroupedModuleFrames.compile, List.map_append]
      rw [skel_compileFramed _ _ _ (GroupedModuleFrames.profile FF cur) (FF v.label), ih]

end Skeleton

/-- The network's instruction skeleton is independent of the column count. -/
lemma skel_network (k k' : ℕ) : (network k).map skel = (network k').map skel := by
  simp only [network, GroupedModuleFrames.network, List.map_append]
  rw [skel_compile (frameOf k) (frameOf k'), skel_edges _ _
    (GroupedModuleFrames.profile (frameOf k') _) (GroupedModuleFrames.profile (frameOf k') _)]

/-- The common instruction skeleton. -/
noncomputable def skeleton : List Skel := (network 0).map skel

/-- The lowered network program with factor data. -/
noncomputable def program (ds : Directions) : List Instr := lowerSkel skeleton ds

/-- Execute one instruction on a bank, with factors implemented by `fac`. -/
def execWith {V : Type*} [AddCommGroup V] [Module ℚ V] (fac : ZMod 4 × BinaryWalsh.Address m → V → V) :
    Instr → (NWire → V) → (NWire → V)
  | .factor w g, x => Function.update x w (fac g (x w))
  | .gate g, x => FramedCircuit.moduleGate g x

/-- Execute a program on a bank, with factors implemented by `fac`. -/
def runWith {V : Type*} [AddCommGroup V] [Module ℚ V] (fac : ZMod 4 × BinaryWalsh.Address m → V → V) :
    List Instr → (NWire → V) → (NWire → V)
  | [], x => x
  | i :: rest, x => runWith fac rest (execWith fac i x)

lemma runWith_append {V : Type*} [AddCommGroup V] [Module ℚ V]
    (fac : ZMod 4 × BinaryWalsh.Address m → V → V) (p q : List Instr) (x : NWire → V) :
    runWith fac (p ++ q) x = runWith fac q (runWith fac p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons i rest ih => exact ih _


section Lowering

variable (k : ℕ)

/-- The vendored factor operator, as a function. -/
noncomputable def vf (g : ZMod 4 × BinaryWalsh.Address m) :
    BinaryColumns.Arrays m k → BinaryColumns.Arrays m k :=
  fun f => BinaryColumns.vectorFactor k g f

lemma run_factors (w : NWire) (gs : List (ZMod 4 × BinaryWalsh.Address m))
    (x : NWire → BinaryColumns.Arrays m k) :
    FramedFactorExecution.run
        ((gs.map fun g => (BinaryColumns.vectorFactor k g).restrictScalars ℚ).map
          (FramedFactorExecution.Instruction.linear w)) x =
      runWith (vf k) (gs.map (Instr.factor w)) x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _

lemma run_lowerSkel (p : List (FramedCircuit.Instruction NWire ℚ (BinaryColumns.Arrays m k)))
    (ds : Directions) (x : NWire → BinaryColumns.Arrays m k) :
    FramedFactorExecution.run (FramedFactorExecution.lower p (factorMaps k ds)) x =
      runWith (vf k) (lowerSkel (p.map skel) ds) x := by
  induction p generalizing ds x with
  | nil => rfl
  | cons instr rest ih =>
      cases instr with
      | edge w old next =>
          simp only [FramedFactorExecution.lower, List.map_cons, skel, lowerSkel,
            FramedFactorExecution.run_append, runWith_append]
          have hh : (factorMaps k ds).headD [] =
              (ds.headD []).map fun g => (BinaryColumns.vectorFactor k g).restrictScalars ℚ := by
            cases ds <;> rfl
          have ht : (factorMaps k ds).tail = factorMaps k ds.tail := by cases ds <;> rfl
          rw [hh, ht, ih, FramedFactorExecution.onWire, ← List.map_reverse, run_factors,
            List.map_reverse]
      | gate g =>
          simp only [FramedFactorExecution.lower, List.map_cons, skel, lowerSkel]
          exact ih ds _

/-- With the vendored factors, the program is the vendored lowered network. -/
lemma runWith_vf (ds : Directions) (x : NWire → BinaryColumns.Arrays m k) :
    runWith (vf k) (program ds) x = FramedFactorExecution.run (lowered k ds) x := by
  rw [lowered, run_lowerSkel, program, skeleton, skel_network k 0]

/-- The corrected node program applies the full forward frame on every wire. -/
theorem node_correct (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (stored : NWire → BinaryColumns.Arrays m k) :
    correctOutput k (runWith (vf k) (program ds) (correctInput k stored)) =
      fun i => fullFrame k (stored i) := by
  rw [runWith_vf]
  exact corrected_lowered_run k ds hd stored

end Lowering

end IntegerMultBounds.MathlibTM2.Layer
