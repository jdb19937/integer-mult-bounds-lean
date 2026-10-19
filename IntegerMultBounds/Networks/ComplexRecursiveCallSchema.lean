module

public import IntegerMultBounds.Networks.ComplexPhaseRowSchedule

/-! Literal recursive call occurrences retain the wire and edge position of
the actual complex25 label-update trace. Repeated equal labels remain distinct
call sites. This is the fixed finite call schema, not a tape controller. -/

@[expose] public section

namespace IntegerMultBounds.Networks.ComplexRecursiveCallSchema
noncomputable section
open ComplexPhaseBudget ComplexPhaseRowSchedule
abbrev Wire := Wires.ComplexRole 25

private theorem trace_length {ι L : Type*} [DecidableEq ι]
    (current : ι → L) (us : List (ι × L)) : (RankTrace.edges current us).length = us.length := by
  induction us generalizing current with
  | nil => rfl
  | cons u us ih => simp only [RankTrace.edges, List.length_cons, ih]

theorem edge_length : edges.length = updates.length :=
  trace_length (GlobalLabels.source ComplexRank25.vector) updates

def sites : List Edge := edges.attach
abbrev Occurrence := Fin sites.length

def edge (site : Occurrence) : Edge := sites[site.val]

def role (site : Occurrence) : Wire := (updates[site.val]'(by
  have hi := site.isLt
  simpa only [sites, List.length_attach, edge_length] using hi)).1

structure CallFor (es : List Edge) where
  site : Fin es.length
  coordinate : Fin (dimension es[site.val])

abbrev Call := CallFor sites

def Call.role (call : Call) : Wire := ComplexRecursiveCallSchema.role call.site
def Call.slot (call : Call) : Fin (25 ^ 3) := ComplexPhaseRowSchedule.slot (edge call.site) call.coordinate

/-- The actual chosen residual coordinate carries its own fourth-root phase.
Orthonormality ensures this is positive or negative one, rather than fixing
the sign uniformly across all coordinates of an edge. -/
def Call.phaseWeightValue (call : Call) : ZMod 4 :=
  BinaryPhase.weightPhase
    (BinaryPhaseResidualRowProgram.basis ComplexPhaseBudget.coordinateSymm
      (low (edge call.site)) (high (edge call.site))
      (low_nondegenerate (edge call.site)) (high_nondegenerate (edge call.site))
      (comparable (edge call.site)) (residual_good (edge call.site)) call.coordinate :
        Fin (25 ^ 3) → ZMod 2)

/-- Symbolic storage avoids reducing the full chosen basis when checking
fixed dispatcher state types; its exact original value is proved below. -/
def Call.phaseWeight (call : Call) : ZMod 4 :=
  Classical.choose (show ∃ weight : ZMod 4, weight=call.phaseWeightValue from
    ⟨call.phaseWeightValue,rfl⟩)

theorem Call.phaseWeight_eq (call : Call) : call.phaseWeight=call.phaseWeightValue :=
  Classical.choose_spec (show ∃ weight : ZMod 4, weight=call.phaseWeightValue from
    ⟨call.phaseWeightValue,rfl⟩)

/-- Recursive direction realizes the signed residual phase of this actual
coordinate, combining its basis weight with the original edge direction. -/
def Call.inverse (call : Call) : Bool :=
  if call.phaseWeight=1 then direction (edge call.site) else !direction (edge call.site)

def callsAtFor (es : List Edge) (site : Fin es.length) : List (CallFor es) :=
  List.ofFn (fun i => ⟨site,i⟩)
def callsFor (es : List Edge) : List (CallFor es) := (List.ofFn (callsAtFor es)).flatten

def callsAt (site : Occurrence) : List Call := callsAtFor sites site
def calls : List Call := callsFor sites

/-- The manuscript's exact integer stop test for beta=1/1000. Exponent-zero
nodes are leaves even in the finite small-d regime. -/
def stopped (globalAxes remainingExponent : ℕ) : Bool :=
  decide (remainingExponent = 0 ∨ ((25 ^ 3)^remainingExponent)^1000 < globalAxes)

end
end IntegerMultBounds.Networks.ComplexRecursiveCallSchema
