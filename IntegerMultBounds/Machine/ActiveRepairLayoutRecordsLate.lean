module

public import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsMove
public import IntegerMultBounds.Machine.ActivePrefixDirtyControlLateGlobal
public import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalRun
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPermutation
import Mathlib.Tactic.Positivity.Finset

/-! The actual prepared later array supplies exactly the global late repair
records, with full physical-width payloads and a paid machine execution. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsLate
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes CompactActiveTargetLayout
open ActiveRepairLayoutRecordsShape ActiveRepairLayoutRecordsData
open Compact ActiveRepairLayoutPermutation
variable (s : Shape) (p : Parameters s) (offset : ℕ) (rows : ℕ)
variable (hfit : offset+p.f*p.q≤p.after)
variable (hn : 0<p.n) (hb : 2≤p.b) (hrecord : s.bits+1≤s.payload)
variable (hrows : 0<rows) (hK : 0<s.chunk) (hd : 0<s.axes) (hg : 0<s.guard)
local notation "g" => ActivePrefixDirtyControlSequenceGeometry.geometry s p rows offset hfit hn hb hrecord hrows hK hd hg
variable (array : ActivePrefixDirtyControlConjugationData.FullArray s rows)
local notation "E" => indexEquiv (addressShape s) (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize
local notation "P" => lateActual s p.q p.b p.n p.before p.after rows p.rho offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.after (ActivePrefixDirtyControlLateGlobal.positive s p)
local notation "Q" => lateActual (addressShape s) p.q p.b p.n p.before p.after rows p.rho offset (p.f*p.q) ActiveRepairRankHeadersData.SourceSide.after (ActivePrefixDirtyControlLateGlobal.positive s p)

theorem result_move :
    ActivePrefixDirtyControlSequenceData.later g array=
    ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
      p.compactFits p.activeSize P array := by
  let f := indexEquiv s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize
  funext i
  have hh := ActivePrefixDirtyControlLateGlobal.entry s p offset hfit hn hb hrecord hrows hK hd hg array ((P).symm (f.symm i))
  change ActivePrefixDirtyControlSequenceData.later g array (f (P ((P).symm (f.symm i))))=
    array (f ((P).symm (f.symm i))) at hh
  rw [(P).apply_symm_apply] at hh
  exact (congrArg (fun j : Fin (rows*s.recordWidth) => ActivePrefixDirtyControlSequenceData.later g array j)
    (f.apply_symm_apply i).symm).trans hh

theorem runs (d : ActivePrefixDirtyControlSequenceData.Inputs s g) :
    HoareTime ActivePrefixDirtyControlSequenceRun.program
      (fun v => v=ActivePrefixDirtyControlSequenceStages.bank (ActivePrefixDirtyControlSequenceData.caller d array))
      (fun v => v=ActivePrefixDirtyControlSequenceStages.bank (ActivePrefixDirtyControlSequenceData.caller d
        (ActiveRepairLayoutRecordsMove.move s (p.n*p.b) (p.n*p.q) p.before p.after rows
          p.compactFits p.activeSize P array)))
      (ActivePrefixDirtyControlSequenceRun.cost s g) := by
  rw [←result_move s p offset rows hfit hn hb hrecord hrows hK hd hg array]
  exact ActivePrefixDirtyControlSequenceRun.runs d array

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsLate
