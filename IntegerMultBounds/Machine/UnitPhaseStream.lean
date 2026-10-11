module

public import IntegerMultBounds.Machine.UnitPhaseStreamBudget
public import IntegerMultBounds.Machine.UnitPhaseStreamInitBudget

/-! Whole physical coefficient phase stream: derive full address width from
original headers, fill the live counter/readout, run the original-count loop,
and erase generated width and loop controls. All costs are paid linearly in
reserved payload and exact signed coefficient width. The contract records
the full physical endpoint, including restored workspace and generated loop
controls, and bounds actual machine transitions. -/

@[expose] public section

namespace IntegerMultBounds.Machine.UnitPhaseStream
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open DelimitedRadixRecord (Context)
open SharedPlacementAlphabet (setTape)
open BinaryAddressTableData (row)
open CountedLoopReuseAlphabet (binary)
variable {s : Shape}

def program (m : ℕ) (ws : List (ZMod 4)) :=
  seq (extend UnitPhaseStreamInit.program 2) (UnitPhaseStreamLoop.program m ws)
def tailReady (tail : Tapes 4 2) := setTape tail 1 (binary (row s.bits 0)) 1
def input (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (tail : Tapes 4 2) :=
  CountedLoopHeaderClean.bank (UnitPhaseStreamInit.input order v rows axis tail)
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (ctx : ℕ → Context 2) (tail : Tapes 4 2) :=
  CountedLoopHeaderClean.bank (UnitPhaseStreamLoop.state order v rows axis m ws ctx (tailReady (s := s) tail) rows)

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) (m : ℕ)
    (ws : List (ZMod 4)) (hm : 0<m) (hslots : m≤v.slots) (hl : m=ws.length)
    (ctx : ℕ → Context 2) (w : ℕ)
    (hw : ∀ i<rows,(ctx i).re.length=w ∧ (ctx i).im.length=w)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) (tail : Tapes 4 2)
    (ht : tail.tape 0=(ctx 0).tape ∧ tail.head 0=(ctx 0).start)
    (hc : tail.tape 1=(fun _ => blank) ∧ tail.head 1=0)
    (hnext : ∀ i<rows,(ctx (i+1)).tape=(ctx i).tape ∧
      (ctx (i+1)).start=(ctx i).start+(ctx i).re.length+(ctx i).im.length+2) :
    HoareTime (program m ws) (fun z => z=input order v rows axis tail)
      (fun z => z=output order v rows axis m ws ctx tail)
      (rows*(10620*s.payload+24*w)+1200*s.payload) := by
  have h0 := hoare_extend_eq (UnitPhaseStreamInit.runs order v rows axis (ctx 0) tail hc)
    (SharedBank.empty 2 2)
  have h1 := UnitPhaseStreamLoop.runs order v rows axis m ws hm hslots hl ctx w hw hspan hrecord
    (tailReady (s := s) tail) (by simpa [tailReady,setTape] using ht) (by exact ⟨rfl,rfl⟩) hnext
  have hready : UnitPhaseStreamInit.ready order v rows axis (ctx 0) tail=
      UnitPhaseStreamLoop.state order v rows axis m ws ctx (tailReady (s := s) tail) 0 := rfl
  rw [hready] at h0
  apply (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) _
  have hb := UnitPhaseStreamBudget.loop_bound v axis m w rows hm hslots hspan hrecord
  have hi := UnitPhaseStreamInitBudget.cost_payload order v rows axis hrecord
  omega

end
end IntegerMultBounds.Machine.UnitPhaseStream
