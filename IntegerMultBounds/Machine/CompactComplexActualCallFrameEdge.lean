module

public import IntegerMultBounds.Networks.ComplexRecursiveCallSchema
public import IntegerMultBounds.Networks.ComplexFramedExecution

/-! The actual schema-chosen residual coordinates factor the named original
frame edge. Each coordinate retains its own phase weight as well as the edge
orientation; orthonormality alone does not fix every weight to positive one. -/

@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexActualCallFrameEdge
noncomputable section
open Networks
open ComplexRecursiveCallSchema (Call Occurrence edge callsAt)
open ComplexPhaseRowSchedule (Edge direction low high dimension)
open BinaryWalsh BinaryColumns
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  ComplexPhaseBudget.edges ComplexPhaseBudget.updates

def basisVector (e : Edge) (i : Fin (dimension e)) : BinaryWalsh.Address (25^3) :=
  BinaryPhaseResidualRowProgram.basis ComplexPhaseBudget.coordinateSymm
    (low e) (high e) (ComplexPhaseRowSchedule.low_nondegenerate e)
    (ComplexPhaseRowSchedule.high_nondegenerate e) (ComplexPhaseRowSchedule.comparable e)
    (ComplexPhaseRowSchedule.residual_good e) i

def weight (e : Edge) (i : Fin (dimension e)) : ZMod 4 := BinaryPhase.weightPhase (basisVector e i)

def signedWeight (e : Edge) (i : Fin (dimension e)) : ZMod 4 :=
  if direction e then -weight e i else weight e i

/-- Actual call occurrence retains its own chosen residual direction. -/
@[irreducible] def kernel (call : Call) : ZMod 4 × BinaryWalsh.Address (25^3) :=
  (signedWeight (edge call.site) call.coordinate,basisVector (edge call.site) call.coordinate)

theorem weight_unit (e : Edge) (i : Fin (dimension e)) : weight e i=1 ∨ weight e i=-1 := by
  apply BinaryPhase.unit_weightPhase
  exact (BinaryPhaseResidualRowProgram.gram ComplexPhaseBudget.coordinateSymm
    (low e) (high e) (ComplexPhaseRowSchedule.low_nondegenerate e)
    (ComplexPhaseRowSchedule.high_nondegenerate e) (ComplexPhaseRowSchedule.comparable e)
    (ComplexPhaseRowSchedule.residual_good e) i i).trans (by simp)

/-- The child direction required by the original edge includes the sign of
the selected basis vector as well as the edge's orientation. -/
def requiredInverse (call : Call) : Bool :=
  if weight (edge call.site) call.coordinate=1 then direction (edge call.site) else !direction (edge call.site)

theorem requiredInverse_weight (call : Call) :
    signedWeight (edge call.site) call.coordinate=if requiredInverse call then -1 else 1 := by
  rcases weight_unit (edge call.site) call.coordinate with hp | hn
  · simp only [requiredInverse,hp,ite_true,signedWeight]
  · have hne : weight (edge call.site) call.coordinate≠1 := by rw [hn]; decide
    simp only [requiredInverse,signedWeight,hn,neg_neg]
    cases direction (edge call.site) <;> rfl

/-- The actual schema now uses precisely the proved coordinate direction. -/
theorem inverse_eq_required (call : Call) : call.inverse=requiredInverse call := by
  unfold Call.inverse
  rw [Call.phaseWeight_eq]
  rfl

theorem inverse_signedWeight (call : Call) :
    signedWeight (edge call.site) call.coordinate=if call.inverse then -1 else 1 := by
  rw [inverse_eq_required]
  exact requiredInverse_weight call

theorem kernel_inverse (call : Call) :
    kernel call=(if call.inverse then -1 else 1,basisVector (edge call.site) call.coordinate) := by
  unfold kernel
  rw [inverse_signedWeight]

private theorem listPhase_sum (gs : List (ZMod 4 × BinaryWalsh.Address (25^3)))
    (x : BinaryWalsh.Address (25^3)) :
    listPhase gs x=(gs.map (fun g => g.1*BinaryPhase.bitLift (Labels.binary (25^3) g.2 x))).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih => exact congrArg (g.1*BinaryPhase.bitLift (Labels.binary (25^3) g.2 x)+·) ih

private theorem selected (e : Edge) (i : Fin (dimension e)) (x : BinaryWalsh.Address (25^3)) :
    BinaryRowProgram.run (ComplexPhaseRowSchedule.word e) x (ComplexPhaseRowSchedule.slot e i)=
      Labels.binary (25^3) (basisVector e i) x :=
  BinaryPhaseResidualRowProgram.selected ComplexPhaseBudget.coordinateSymm
    (low e) (high e) (ComplexPhaseRowSchedule.low_nondegenerate e)
    (ComplexPhaseRowSchedule.high_nondegenerate e) (ComplexPhaseRowSchedule.comparable e)
    (ComplexPhaseRowSchedule.residual_good e) x i

def edgeKernels (e : Edge) : List (ZMod 4 × BinaryWalsh.Address (25^3)) :=
  List.ofFn (fun i : Fin (dimension e) => (signedWeight e i,basisVector e i))

private theorem calls_kernels (site : Occurrence) : (callsAt site).map kernel=edgeKernels (edge site) := by
  simp only [callsAt,ComplexRecursiveCallSchema.callsAtFor,List.map_ofFn,edgeKernels]
  apply congrArg List.ofFn
  funext i
  unfold kernel
  rfl

private theorem kernels_phase_sum (e : Edge) (x : BinaryWalsh.Address (25^3)) :
    listPhase (edgeKernels e) x=∑ i : Fin (dimension e),
      signedWeight e i*BinaryPhase.bitLift (Labels.binary (25^3) (basisVector e i) x) := by
  rw [listPhase_sum]
  simp only [edgeKernels,List.map_ofFn,List.sum_ofFn,Function.comp_def]

private theorem unsigned_phase (e : Edge) (x : BinaryWalsh.Address (25^3)) :
    (∑ i : Fin (dimension e),weight e i*BinaryPhase.bitLift (Labels.binary (25^3) (basisVector e i) x))=
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (high e) (ComplexPhaseRowSchedule.high_nondegenerate e) x)-
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (low e) (ComplexPhaseRowSchedule.low_nondegenerate e) x) := by
  apply Eq.trans _ (ComplexPhaseRowSchedule.phase e x).symm
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun z : ZMod 2 => weight e i*BinaryPhase.bitLift z) (selected e i x).symm

private theorem signed_sum {n : ℕ} (reverse : Bool) (weights terms : Fin n → ZMod 4) :
    (∑ i,(if reverse then -weights i else weights i)*terms i)=
      if reverse then -(∑ i,weights i*terms i) else ∑ i,weights i*terms i := by
  cases reverse
  · rfl
  · simp only [ite_true,neg_mul,Finset.sum_neg_distrib]

private theorem signed_phase (e : Edge) (x : BinaryWalsh.Address (25^3)) :
    (∑ i : Fin (dimension e),signedWeight e i*BinaryPhase.bitLift (Labels.binary (25^3) (basisVector e i) x))=
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (ComplexPhaseRowSchedule.target e) (ComplexPhaseRowSchedule.target_nondegenerate e) x)-
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (ComplexPhaseRowSchedule.source e) (ComplexPhaseRowSchedule.source_nondegenerate e) x) := by
  exact (signed_sum (direction e) (weight e)
      (fun i => BinaryPhase.bitLift (Labels.binary (25^3) (basisVector e i) x))).trans
    ((congrArg (fun z : ZMod 4 => if direction e then -z else z) (unsigned_phase e x)).trans
      (ComplexPhaseRowSchedule.original_phase e x).symm)

/-- The exact actual basis, in actual coordinate order, realizes the original edge phase. -/
theorem edge_phase (e : Edge) (x : BinaryWalsh.Address (25^3)) :
    listPhase (edgeKernels e) x=
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (ComplexPhaseRowSchedule.target e) (ComplexPhaseRowSchedule.target_nondegenerate e) x)-
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (ComplexPhaseRowSchedule.source e) (ComplexPhaseRowSchedule.source_nondegenerate e) x) :=
  (kernels_phase_sum e x).trans (signed_phase e x)

theorem calls_phase (site : Occurrence) (x : BinaryWalsh.Address (25^3)) :
    listPhase ((callsAt site).map kernel) x=
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (ComplexPhaseRowSchedule.target (edge site)) (ComplexPhaseRowSchedule.target_nondegenerate (edge site)) x)-
      BinaryPhase.weightPhase (ProjectionRank.project (Labels.binary (25^3)) ComplexPhaseBudget.coordinateSymm
        (ComplexPhaseRowSchedule.source (edge site)) (ComplexPhaseRowSchedule.source_nondegenerate (edge site)) x) := by
  rw [calls_kernels]
  exact edge_phase (edge site) x

/-- The genuine all-column frame edge equals the product indexed by the
actual site's calls; this is the original named framed instruction operator. -/
theorem calls_frame_edge (columns : ℕ) (site : Occurrence) :
    BinaryRankFactors.edgeOperator ComplexPhaseBudget.coordinateSymm columns
      (ComplexPhaseRowSchedule.source (edge site)) (ComplexPhaseRowSchedule.target (edge site))=
      (((callsAt site).map kernel).map (vectorFactor columns)).prod := by
  unfold BinaryRankFactors.edgeOperator BinaryRankFactors.labelFrame
  rw [ProjectionTrace.projector_eq _ _ _ (ComplexPhaseRowSchedule.source_nondegenerate (edge site)),
    ProjectionTrace.projector_eq _ _ _ (ComplexPhaseRowSchedule.target_nondegenerate (edge site))]
  apply edge_factor_product
  intro f
  rw [frame_edge,kernelRun_eq_frame]
  apply congrArg (fun q : BinaryWalsh.Address (25^3) → ZMod 4 => frame q f)
  funext x
  exact (calls_phase site x).symm

end
end IntegerMultBounds.Machine.CompactComplexActualCallFrameEdge
