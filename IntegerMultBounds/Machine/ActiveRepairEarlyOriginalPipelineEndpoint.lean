module

public import IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineCleanup
import Mathlib.Tactic.Positivity.Finset

/-! Actual original-input early repair from literal source and blank scan
workspace through preparation, varying-rank scan, sort/reinsert and complete
final cleanup. Only original source, metadata and repaired output survive. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineEndpoint
noncomputable section
open ActiveRepairEarlyKeyOriginalData ActiveRepairEarlyKeyOriginalValid
open SharedPlacementAlphabet (setTape)

def bodyProgram (side : ActiveRepairRankHeadersData.SourceSide) :=
  extend (ActiveRepairEarlyOriginalPipelineRun.program side) 3
def program (side : ActiveRepairRankHeadersData.SourceSide) := seq
  (seq ActiveRepairEarlyOriginalPipelinePrepare.program (bodyProgram side))
  ActiveRepairEarlyOriginalPipelineCleanup.program
def input := ActiveRepairEarlyOriginalPipelinePrepare.input
def output := ActiveRepairEarlyOriginalPipelineCleanup.output
def cost (d : Data) (rs : List Partition.Record) :=
  200*(d.geom.addressBits+1)+1+
    ActiveRepairEarlyOriginalPipelineRun.cost d d.geom.addressBits rs+1+
    ActiveRepairEarlyOriginalPipelineCleanup.cost d rs

theorem runs (d : Data) (h : Valid d) (rs : List Partition.Record) :
    HoareTime (program d.side) (fun v => v=input d rs) (fun v => v=output d rs) (cost d rs) := by
  have hp := ActiveRepairEarlyOriginalPipelinePrepare.runs_linear d h rs
  have hb := hoare_extend_eq (ActiveRepairEarlyOriginalPipelineRun.runs d h d.geom.addressBits rs)
    (SharedBank.empty 3 1)
  exact (hp.seq hb).seq (ActiveRepairEarlyOriginalPipelineCleanup.runs d rs)

theorem output_tape (d : Data) (rs : List Partition.Record) :
    (output d rs).tape 10=RepairStage.encTape
      (Partition.encode (ActiveRepairEarlyOriginalPipelineCleanup.repaired d rs)) := rfl

theorem source_tape (d : Data) (rs : List Partition.Record) :
    (output d rs).tape 11=RepairScan.srcTape rs := rfl

def metadataSlot (i : Fin 166) : Fin 183 := Fin.castAdd 3 (Fin.natAdd 14 i)

end
end IntegerMultBounds.Machine.ActiveRepairEarlyOriginalPipelineEndpoint
