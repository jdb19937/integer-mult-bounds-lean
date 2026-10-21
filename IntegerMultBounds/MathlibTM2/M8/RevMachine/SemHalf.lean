module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SemNode
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Rev97Node

/-!
# The node half of the stage-2 PR97 family with its data

The node's bank between the split and the merge (`NodeSem`): its data represents, on every fiber
of the role view, the schedule's run of the split's streams up to the current piece. The split
reaches it (`split_sem`), every nonrecursive piece keeps it (`seg_sem`), a block call enters a
child frame on the wire's bits and recovers the child's reversed interchange of them (`call_sem`),
and the merge returns the reversed interchange of the middle view (`merge_sem`). The blocks and
costs are those of `RevHalf`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics

noncomputable section
open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open GraphContract (Runs)
open CommonBank (bank K)
open Blocks (runs_mono)
open Routines (hdr)
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveRoleSerialization (roles)
open RecursiveRowsSerialization (roleData)
open NodeBank (tapes io wireSlot wires)
open NodePark (childRoles)
open NodeCall (nodeC)
open NodeSplit (midView roleView NodeInv zeroBit)
open Family (leafC Frame)
open RevHalf (pcs Ok)

local instance (b : ℕ) : NeZero (prime ^ b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

variable {k : ℕ} {capacity : Fintype.card (Graph.PC (pcs rev97m).length) ≤ 2^k}

/-- **The node's bank with its data**: after `i` pieces, on the split of the leaves' output `YL`. -/
def NodeSem (σ : Frame (pcs rev97m) capacity) (YL : Fin (volume prime σ.v) → ZMod 2) (i : ℕ)
    (y : Tapes (CommonBank.count (tapes rev97m)) prime) : Prop :=
  ∃ hd : rev97m.roleCount ∣ σ.v.rows, ∃ data : RecursiveMixedSchedule.Data (tapes rev97m) (roleView rev97m σ.b σ.n σ.v),
    NodeInv rev97m data ∧
    y = bank (roles data) (hdr (roleView rev97m σ.b σ.n σ.v)) σ.f σ.p
      (RecursiveViewFrame.savedStack (hdr (midView rev97m σ.b σ.n σ.v)) (RecursiveViewFrame.savedStack (hdr σ.v) σ.node))
      σ.scalar (nodeC rev97m σ.b (σ.n / rev97m.width)) σ.st ∧
    ∀ x, Represents rev97m rfl x data (run97 ((pcs rev97m).take i) (init hd (midBits σ.hw YL) x))

/-! ### Split and merge -/

/-- **The split.** -/
theorem split_sem {b₀ : ℕ} (σ : Frame (pcs rev97m) capacity) (hok : Ok rev97m b₀ σ) (hm : rev97m.width ≤ σ.n)
    (YL : Fin (volume prime σ.v) → ZMod 2) :
    ∃ y, NodeSem σ YL 0 y ∧ Runs (NodeSplit.splitB rev97m) (σ.at (rolesOf rev97m YL) (leafC σ.b rev97m.width σ.n 0)) y
      (NodeSplit.splitCost (N := rev97m) σ.v σ.b σ.n) := by
  have hd := RevHalf.rows_dvd hok hm
  refine ⟨_, ⟨hd, _, ?_, rfl, fun x => ?_⟩,
    NodeSplit.split_runs_data σ.hpos σ.hb σ.hw hm hd (Shared50RecursiveNodeSemantics.encoded YL)⟩
  · exact NodeSplit.init_inv (v := midView rev97m σ.b σ.n σ.v) hd _ (fun i => ⟨_, rfl⟩)
  · rw [List.take_zero, run97_nil]
    exact split_represents σ.hw hd YL x

/-- **The merge**: the reversed interchange of the middle view. -/
theorem merge_sem {b₀ : ℕ} (σ : Frame (pcs rev97m) capacity) (YL : Fin (volume prime σ.v) → ZMod 2)
    (y : Tapes (CommonBank.count (tapes rev97m)) prime) (_hok : Ok rev97m b₀ σ) (_hm : rev97m.width ≤ σ.n)
    (hy : NodeSem σ YL (pcs rev97m).length y) :
    ∃ Y : Fin (volume prime σ.v) → ZMod 2,
      RevT prime σ.b (rev97m.width * (σ.n / rev97m.width)) (midView rev97m σ.b σ.n σ.v) (ext YL) (ext Y) ∧
      Runs (NodeSplit.mergeB rev97m) y (σ.at (rolesOf rev97m Y) (leafC σ.b rev97m.width σ.n 0))
        (NodeSplit.mergeCost (N := rev97m) σ.v σ.b σ.n) := by
  obtain ⟨hd, data, hinv, rfl, hrep⟩ := hy
  rw [List.take_length] at hrep
  obtain ⟨hio₁, ht₁⟩ := NodeRows.run_tempOps rev97m blank data
  have hio₁' : NodeRows.NodeData rev97m (Machine.RoleOps.run (NodeRows.tempOps rev97m blank) data) := hio₁.trans hinv.1
  obtain ⟨x', hx', hcells⟩ := NodeRows.roleData_surjective rev97m (v := midView rev97m σ.b σ.n σ.v)
    (NodeSplit.mid_dvd rev97m hd) _ hio₁' ht₁
  have hbits : SegmentBits.Bits x' := by
    intro i
    obtain ⟨j, z, hz⟩ := hcells i
    have hne : wires rev97m (Fin.natAdd 1 j) ≠ io rev97m := by
      simp only [wires, Fin.addCases_right]; exact NodeBank.wireSlot_ne_io rev97m _
    rw [hz, NodeSplit.merge_world]
    exact hinv.2 _ hne z
  obtain ⟨Ym, hYm⟩ := RevNode.bits_encoded hbits
  have hvol := NodeSplit.mid_volume rev97m σ.hw
  refine ⟨fun i => Ym (Fin.cast hvol.symm i), ?_, ?_⟩
  · have h := merge_revT hd (midBits σ.hw YL) data hrep Ym (by rw [show Shared50RecursiveNodeSemantics.encoded Ym = x' from hYm.symm]; exact hx')
    have e1 : ext (midBits σ.hw YL) = ext YL := ext_cast hvol YL
    have e2 : ext Ym = ext (fun i => Ym (Fin.cast hvol.symm i)) := (ext_cast hvol.symm Ym).symm
    rw [e1, e2] at h
    exact h
  · have h := NodeSplit.merge_runs_data (fs := σ.f) (p := σ.p) (scalar := σ.scalar) (st := σ.st) σ.hpos σ.hb σ.hw hd
      data σ.hfree x' hx'
    rw [hYm] at h
    exact h

/-! ### The pieces -/

theorem mem_gate {g : Circuit.Gate (rev97m.World ⊕ rev97m.Temp) (ZMod 2)}
    (h : Graph.Piece.seg (Schedule.Seg.gate g) ∈ pcs rev97m) : Step.gate g ∈ rev97m.control := by
  obtain ⟨step, hs, hp⟩ := List.mem_flatMap.mp h
  cases step with
  | edge j p =>
    simp only [Schedule.stepPieces] at hp
    split_ifs at hp <;> simp at hp
  | gate g' =>
    simp only [Schedule.stepPieces, List.mem_singleton, Graph.Piece.seg.injEq, Schedule.Seg.gate.injEq] at hp
    rw [hp]; exact hs
  | reset w => simp [Schedule.stepPieces] at hp

/-- **A nonrecursive piece** keeps the data. -/
theorem seg_sem {b₀ : ℕ} (σ : Frame (pcs rev97m) capacity) (YL : Fin (volume prime σ.v) → ZMod 2)
    (y : Tapes (CommonBank.count (tapes rev97m)) prime) (_hok : Ok rev97m b₀ σ) (hm : rev97m.width ≤ σ.n)
    (i : Graph.Site (pcs rev97m)) (s : Schedule.Seg (rev97m.World ⊕ rev97m.Temp) rev97m.width)
    (hi : (pcs rev97m)[i] = .seg s) (hy : NodeSem σ YL i.val y) :
    ∃ y', NodeSem σ YL (i.val + 1) y' ∧ Runs (RevNode.segB rev97m s) y y' (RevHalf.segCost rev97m σ s) := by
  obtain ⟨hd, data, hinv, rfl, hrep⟩ := hy
  have htake : (pcs rev97m).take (i.val + 1) = (pcs rev97m).take i.val ++ [.seg s] := by
    rw [List.take_succ_eq_append_getElem i.isLt]
    congr 2
  have hp := NodeSplit.roleView_positive rev97m (b := σ.b) (n := σ.n) σ.hpos hd
  have hV := Routines.hdr_headers (roleView rev97m σ.b σ.n σ.v)
  have hmem : Graph.Piece.seg s ∈ pcs rev97m := hi ▸ List.getElem_mem _
  cases s with
  | edge w ops =>
    have hfits := RevHalf.fits runs_rev97m hi
    have hfree := seg_free rev97m edgeForm97 hmem
    have hn : ∀ op ∈ ops, AffineFieldCoordinates.Nonrecursive op := by
      intro op hop
      have := hfree op hop
      cases op <;> trivial
    have hf : 0 < σ.n / rev97m.width := Nat.div_pos hm (by have := rev97m.two_le_width; omega)
    have hw : (roleView rev97m σ.b σ.n σ.v).width = (rev97m.width * (σ.n / rev97m.width)) * σ.b := rfl
    set l := AtomRoleSegment.sops ops hfits
    have hh := AtomRoleSegment.chain_hoare σ.hb (RevNode.segT rev97m w l) hf (wireSlot rev97m w) _ hw hp _ hV l
      (RevNode.segT_ge rev97m w l) data
    have hsem := (AtomRoleSegment.segment_twisted ops hfits hn σ.hb hf (wireSlot rev97m w) (RevNode.segT rev97m w l)
      (RevNode.segT_ge rev97m w l) _ hw hp _ hV data).2
    have hc : NodeSegment.SegCounters (nodeC rev97m σ.b (σ.n / rev97m.width)) σ.b (σ.n / rev97m.width) :=
      ⟨by simp [nodeC, Prepare.rest], by simp [nodeC, Prepare.rest], by simp [nodeC, Prepare.rest],
        by simp [nodeC, Prepare.rest], by simp [nodeC, Prepare.rest], by simp [nodeC], by simp [nodeC, Prepare.rest],
        by simp [nodeC, Prepare.rest], by simp [nodeC]⟩
    have hr := NodeSegment.seg_runs (fs := σ.f) (p := σ.p)
      (node := RecursiveViewFrame.savedStack (hdr (midView rev97m σ.b σ.n σ.v)) (RecursiveViewFrame.savedStack (hdr σ.v) σ.node))
      (scalar := σ.scalar) (st := σ.st) (RevNode.segT_le rev97m w l) _ hc hh
    obtain ⟨pr, hpc, hsub⟩ := RevHalf.edge_mem rev97m hi
    have hleg : ∀ op ∈ specialize (prime ^ σ.b) ops, AffineFieldProgram.Legal op := by
      intro op hop
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hop
      exact rev97m.legal_mod σ.b w pr hpc _ (List.mem_map.mpr ⟨o, hsub o ho, rfl⟩)
    have hb := twMap_bijective (φ := atomScalar prime σ.b (σ.n / rev97m.width))
      (TwistedExchange.atomRev_atomRev _) (fun c => funext fun _ => rfl) ops hleg
    set data' := AtomRoleSegment.chainData hf (wireSlot rev97m w) _ hw l data
    refine ⟨_, ⟨hd, data', ⟨?_, fun j hj => ?_⟩, rfl, fun x => ?_⟩, ?_⟩
    · exact (AtomRoleSegment.chain_other hf _ _ hw (io rev97m) (NodeBank.wireSlot_ne_io rev97m w).symm l data).trans hinv.1
    · by_cases hjw : j = wireSlot rev97m w
      · subst hjw
        exact SegmentBits.chain_bits hf _ _ hw l data (hinv.2 _ (NodeBank.wireSlot_ne_io rev97m w))
      · rw [show data' j = data j from AtomRoleSegment.chain_other hf _ _ hw j hjw l data]
        exact hinv.2 j hj
    · rw [htake, run97_edge]
      exact represents_seg (hrep x) w ops hb (fun s' y' z' h₁ h₂ h₃ => hsem.2 s' y' z' h₁ h₂ h₃) hsem.1
    · have hsc : RevHalf.segCost rev97m σ (.edge w ops) = AtomRoleSegment.chainConst (wireSlot rev97m w) l *
          (σ.n / rev97m.width) * volume prime (roleView rev97m σ.b σ.n σ.v) := by
        simp only [RevHalf.segCost]; split_ifs; rfl
      have hsb : RevNode.segB rev97m (.edge w ops) = NodeSegment.place (AtomRoleSegment.chain (RevNode.segT rev97m w l)
          (wireSlot rev97m w) l (RevNode.segT_ge rev97m w l)).2 (RevNode.segT_le rev97m w l) := by
        simp only [RevNode.segB]; split_ifs; rfl
      rw [hsc, hsb]
      exact runs_mono hr (AtomRoleSegment.chainCost_le σ.hb hf _ _ hw hp l)
  | gate g =>
    have hg := rev97m.xor_gate g (mem_gate hmem)
    refine ⟨_, ⟨hd, _, RevHalf.ops_inv _ (RevHalf.gateOp_ok g) data hinv, rfl, fun x => ?_⟩,
      NodeBank.ops_runs (RevNode.gateOp rev97m g) hV hp data _ _ _ _ _ _⟩
    rw [htake, run97_gate]
    exact represents_gate (hrep x) g hg
  | reset w =>
    refine ⟨_, ⟨hd, _, RevHalf.ops_inv _ ?_ data hinv, rfl, fun x => ?_⟩, NodeBank.ops_runs _ hV hp data _ _ _ _ _ _⟩
    · intro o ho
      simp only [List.mem_singleton] at ho
      subst ho
      exact ⟨NodeBank.wireSlot_ne_io rev97m w, 0, rfl⟩
    · rw [htake, run97_reset]
      exact represents_reset (hrep x) w

/-- **A block call**: a child frame on the wire's bits, and the recovery of the child's reversed
interchange of them. -/
theorem call_sem {b₀ : ℕ} (σ : Frame (pcs rev97m) capacity) (YL : Fin (volume prime σ.v) → ZMod 2)
    (y : Tapes (CommonBank.count (tapes rev97m)) prime) (hok : Ok rev97m b₀ σ) (hm : rev97m.width ≤ σ.n)
    (i : Graph.Site (pcs rev97m)) (c : Schedule.Call (rev97m.World ⊕ rev97m.Temp)) (hi : (pcs rev97m)[i] = .call c)
    (hy : NodeSem σ YL i.val y) :
    ∃ τ : Frame (pcs rev97m) capacity, Ok rev97m b₀ τ ∧ τ.n = c.2 * (σ.n / rev97m.width) ∧
      (volume prime τ.v : ℝ) = volume prime σ.v / rev97m.roleCount ∧ τ.ret = .recover i ∧ τ.b = σ.b ∧
      ∃ Xτ : Fin (volume prime τ.v) → ZMod 2, ∃ E R, E + R ≤ RevHalf.callCost rev97m σ c ∧
        Runs ((RevNode.blocks rev97m k).enter c (Graph.returnCode (pcs rev97m) capacity i)) y
          (τ.at (rolesOf rev97m Xτ) (Prepare.rest τ.b rev97m.width)) E ∧
        ∀ Yτ : Fin (volume prime τ.v) → ZMod 2, RevT prime τ.b τ.n τ.v (ext Xτ) (ext Yτ) →
          ∃ y', NodeSem σ YL (i.val + 1) y' ∧
            Runs ((RevNode.blocks rev97m k).recover c) (τ.exitAt (rolesOf rev97m Yτ) rev97m.width) y' R := by
  obtain ⟨hd, data, hinv, rfl, hrep⟩ := hy
  have htake : (pcs rev97m).take (i.val + 1) = (pcs rev97m).take i.val ++ [.call c] := by
    rw [List.take_succ_eq_append_getElem i.isLt]
    congr 2
  obtain ⟨w, r⟩ := c
  have hrr := Rev97Node.rk97 r (GraphContract.rank_mem Prod.snd (pcs rev97m) i.val i.isLt (w, r) hi)
  have hp : (roleView rev97m σ.b σ.n σ.v).Positive := NodeSplit.roleView_positive rev97m σ.hpos hd
  have hf : 0 < (σ.n / rev97m.width) := Nat.div_pos hm (by have := rev97m.two_le_width; omega)
  have hwv : (roleView rev97m σ.b σ.n σ.v).width = (rev97m.width * (σ.n / rev97m.width)) * σ.b := rfl
  have hsc : 0 + r * (σ.n / rev97m.width) ≤ rev97m.width * (σ.n / rev97m.width) := by
    rw [zero_add]; exact Nat.mul_le_mul_right _ hrr.2.le
  have hvτ : volume prime (NodeCall.childView (N := rev97m) σ.b (σ.n / rev97m.width) r (roleView rev97m σ.b σ.n σ.v)) =
      volume prime (roleView rev97m σ.b σ.n σ.v) :=
    RevMachine.sub_volume _ _ _ _ _ (roleView rev97m σ.b σ.n σ.v) hwv hsc
  set τ := RevHalf.childFrame σ hok hm i w r data with hτ
  have hτok : Ok rev97m b₀ τ := RevHalf.childFrame_ok Rev97Node.rk97 σ hok hm i w r hi data
  have hτv : volume prime τ.v = volume prime (roleView rev97m σ.b σ.n σ.v) := hvτ
  obtain ⟨xd, hxd⟩ := RevNode.bits_encoded (hinv.2 _ (NodeBank.wireSlot_ne_io rev97m w))
  have hroles : rolesOf rev97m (v := τ.v) (fun j => xd (Fin.cast hτv j)) =
      childRoles rev97m (RecursiveShiftRoleBank.source (data (wireSlot rev97m w))) := by
    rw [hxd]
    exact congrArg (childRoles rev97m) (NodeSplit.source_cast hτv (fun i => SparseRoleCircuit.encode (xd i)))
  refine ⟨τ, hτok, rfl, ?_, rfl, rfl, fun j => xd (Fin.cast hτv j), _, _, le_rfl, ?_, ?_⟩
  · -- the volume
    have h1 := RecursiveInterchangeLayout.role_volume_mul prime rev97m.roleCount (midView rev97m σ.b σ.n σ.v) hd
    have h2 := NodeSplit.mid_volume rev97m (b := σ.b) (n := σ.n) (v := σ.v) σ.hw
    have hW : (rev97m.roleCount : ℝ) ≠ 0 := by exact_mod_cast (NodeSplit.roleCount_pos rev97m σ.hpos hd).ne'
    change (volume prime (NodeCall.childView (N := rev97m) σ.b (σ.n / rev97m.width) r (roleView rev97m σ.b σ.n σ.v)) : ℝ) = _
    rw [hvτ, eq_div_iff hW]
    exact_mod_cast h1.trans h2
  · simp only [Family.Frame.at]
    rw [hroles]
    simp only [τ, RevHalf.childFrame]
    exact NodeCall.enter_runs w (Graph.returnCode (pcs rev97m) capacity i) hp σ.hb hf hwv hrr.1 hrr.2 data hinv.1
  · intro Yτ hT
    set out : Fin (volume prime (roleView rev97m σ.b σ.n σ.v)) → Fin 4 :=
      fun j => SparseRoleCircuit.encode (Yτ (Fin.cast hτv.symm j))
    have hout : RecursiveShiftRoleBank.source (Shared50RecursiveNodeSemantics.encoded Yτ) =
        RecursiveShiftRoleBank.source out :=
      (NodeSplit.source_cast hτv.symm (fun j => SparseRoleCircuit.encode (Yτ j))).symm
    have hpop := RevNode.popped_saved (hdr (roleView rev97m σ.b σ.n σ.v)) σ.st (Graph.returnCode (pcs rev97m) capacity i)
    refine ⟨_, ⟨hd, Function.update data (wireSlot rev97m w) out, ⟨?_, fun j hj => ?_⟩, rfl, fun x => ?_⟩, ?_⟩
    · rw [Function.update_of_ne (NodeBank.wireSlot_ne_io rev97m w).symm]; exact hinv.1
    · by_cases hjw : j = wireSlot rev97m w
      · subst hjw; rw [Function.update_self]; exact fun z => ⟨_, rfl⟩
      · rw [Function.update_of_ne hjw]; exact hinv.2 j hj
    · rw [htake, run97_call]
      refine represents_call (hrep x) w r out (fun s => ?_)
      have hT' : RevT prime σ.b (r * (σ.n / rev97m.width)) (RevMachine.sub prime σ.b (rev97m.width * (σ.n / rev97m.width)) 0 (r * (σ.n / rev97m.width))
          (roleView rev97m σ.b σ.n σ.v)) (ext xd) (ext (fun j => Yτ (Fin.cast hτv.symm j))) := by
        rw [ext_cast hτv.symm Yτ, ← ext_cast hτv xd]
        exact hT
      have h := call_link hwv hrr.2.le xd (fun j => Yτ (Fin.cast hτv.symm j)) hT' x s
      show SparseRoleCircuit.encode (Yτ (Fin.cast hτv.symm (pos rfl x s))) = _
      rw [h, hxd]
    · change Runs (NodeCall.recoverB rev97m w) (bank _ (hdr τ.v) τ.f τ.p τ.node τ.scalar
        (Prepare.rest τ.b rev97m.width) (Family.popped τ.st τ.g τ.q)) _ _
      simp only [rolesOf]
      rw [hout]
      simp only [τ, RevHalf.childFrame]
      rw [hpop]
      exact NodeCall.recover_runs w hp σ.hb hf hwv data hinv.1 hok.pay hok.desc out

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics
