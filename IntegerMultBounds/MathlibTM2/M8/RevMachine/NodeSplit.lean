module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeCall
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SegmentBits
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Family

/-!
# The split and the merge of the reversed node

A frame of `n ≥ m` atoms holds its data on `io`. The split (`splitB`) computes `δ = n mod m`
and `m f` with `f = ⌊n/m⌋`, saves the headers and installs the middle view `midView`, the
`m f` atoms after the first `δ` head atoms, then splits its rows over the contract roles
(`NodeRows.split`) and fills the temporaries with the zero bit. The node's data is then on the
role view `roleView` with a blank `io` and bits on every wire (`NodeInv`, `split_runs`).

The merge (`mergeB`) clears the temporaries, merges the rows back to `io`, restores the
headers and recomputes the leaf loop's counters (`merge_runs`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSplit

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs)
open CommonBank (bank K)
open Blocks (seqB seq_runs runs_mono Leading)
open Routines (hdr)
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveRoleSerialization (roles)
open RecursiveRowsSerialization (sourceData roleData)
open NodeBank (tapes io wireSlot wires tempSlot)
open NodePark (childRoles)
open NodeCall (nodeC)
open SegmentBits (Bits)
open Family (leafC NodeFree)

variable (N : RevNetwork)

/-! ### Views and data -/

/-- The middle view: the `m f` atoms after the first `δ` head atoms. -/
def midView (b n : ℕ) (v : Descriptor) : Descriptor :=
  RevMachine.sub prime b n (n % N.width) (N.width * (n / N.width)) v

/-- The role view of the middle view. -/
def roleView (b n : ℕ) (v : Descriptor) : Descriptor := role (midView N b n v) N.roleCount

/-- The node's data: a blank `io`, bits on every wire. -/
def NodeInv {v : Descriptor} (data : RecursiveMixedSchedule.Data (tapes N) v) : Prop :=
  data (io N) = (fun _ => blank) ∧ ∀ i, i ≠ io N → Bits (data i)

theorem source_cast {u v : Descriptor} (h : volume prime u = volume prime v) (a : Fin (volume prime v) → Fin 4) :
    RecursiveShiftRoleBank.source (v := u) (fun i => a (Fin.cast h i)) = RecursiveShiftRoleBank.source (v := v) a := by
  have key : ∀ {n m : ℕ} (h : n = m) (a : Fin m → Fin 4),
      (FlatRepeatedControlArray.pair (radix := prime) (fun i : Fin n => a (Fin.cast h i))).tape 0 =
        (FlatRepeatedControlArray.pair (radix := prime) a).tape 0 := by
    intro n m h a; subst h; rfl
  exact key h a

theorem mid_sum (n : ℕ) : n % N.width + N.width * (n / N.width) = n := Nat.mod_add_div n N.width

theorem mid_le (n : ℕ) : n % N.width + N.width * (n / N.width) ≤ n := (mid_sum N n).le

theorem mid_volume {v : Descriptor} {b n : ℕ} (hw : v.width = n * b) :
    volume prime (midView N b n v) = volume prime v := RevMachine.sub_volume _ _ _ _ _ v hw (mid_le N n)

theorem mid_width {v : Descriptor} {b n : ℕ} : (midView N b n v).width = (N.width * (n / N.width)) * b := rfl

theorem mid_rows {v : Descriptor} {b n : ℕ} : (midView N b n v).rows = v.rows := rfl

theorem mid_positive {v : Descriptor} {b n : ℕ} (hpos : v.Positive) : (midView N b n v).Positive :=
  Family.sub_positive hpos

theorem roleCount_pos {v : Descriptor} (hpos : v.Positive) (hd : N.roleCount ∣ v.rows) : 0 < N.roleCount := by
  rcases Nat.eq_zero_or_pos N.roleCount with h | h
  · rw [h, zero_dvd_iff] at hd; have := hpos.2.1; omega
  · exact h

theorem roleView_positive {v : Descriptor} {b n : ℕ} (hpos : v.Positive) (hd : N.roleCount ∣ v.rows) :
    (roleView N b n v).Positive :=
  RecursiveRowsNodeLayout.role_positive _ _ (roleCount_pos N hpos hd) (mid_positive N hpos) hd

/-! ### The split -/

/-- The split's counters: `δ`, `m f`, the zero rest and `f - 1`. -/
def splitCountersB : Graph.Block (CommonBank.count (tapes N)) prime :=
  seqB (Counters.erase 11) (seqB (Counters.div 9 10 16 12 ⟨by decide, by decide, by decide, by decide, by decide,
    by decide⟩) (seqB (Counters.erase 16) (seqB (Counters.mul 10 5 13 (by decide) (by decide) (by decide))
      (seqB (Counters.zero 14) (Counters.diff 5 15 8 (by decide) (by decide) (by decide))))))

/-- Erase the view's counters. -/
def viewEraseB : Graph.Block (CommonBank.count (tapes N)) prime :=
  seqB (Counters.erase 9) (seqB (Counters.erase 12) (seqB (Counters.erase 13) (Counters.erase 14)))

/-- The zero bit. -/
abbrev zeroBit : Fin 4 := SparseRoleCircuit.encode (a := 0) 0

/-- **The node's split.** -/
def splitB : Graph.Block (CommonBank.count (tapes N)) prime :=
  seqB (splitCountersB N) (seqB Blocks.push (seqB LeafRoutines.view (seqB (viewEraseB N)
    (seqB (NodeRows.split N) (NodeBank.ops (NodeRows.tempOps N zeroBit))))))

variable {N}
variable {rr : Tapes (tapes N) prime} {hs : Fin 6 → List Bool} {fs : ℤ → Fin (prime+4)} {p : ℤ}
  {node scalar : Tapes 1 prime} {st : Tapes 2 prime}

/-- The counters of the middle view. -/
def viewC (b n : ℕ) : Fin K → Option ℕ :=
  Function.update (Function.update (Function.update (Function.update (nodeC N b (n / N.width)) 9 (some n))
    12 (some (n % N.width))) 13 (some (N.width * (n / N.width))) ) 14 (some 0)

def splitCountersCost (n m : ℕ) : ℕ :=
  (2*(bits 0).length+4) + BinaryDescriptorDivMod.linearConstant (bits m) * (n + 1) +
    (2*(bits (n / m)).length+4) + (53*(m * (n / m))+28) + 6 + (6*(n / m)+27) + 5

theorem splitCounters_runs {b n : ℕ} (hn : N.width ≤ n) :
    Runs (splitCountersB N) (bank rr hs fs p node scalar (leafC b N.width n 0) st)
      (bank rr hs fs p node scalar (viewC (N := N) b n) st) (splitCountersCost n N.width) := by
  have hm : 0 < N.width := by have := N.two_le_width; omega
  have hf : 0 < n / N.width := Nat.div_pos hn hm
  set c₀ := leafC b N.width n 0
  have h₁ := Counters.erase_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₀) (j := 11) (x := 0) (by simp [c₀, leafC])
  set c₁ := Function.update c₀ 11 none
  obtain ⟨B₂, hB₂, h₂⟩ := Counters.div_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node)
    (scalar := scalar) (st := st) (c := c₁) (y := 9) (d := 10) (qo := 16) (ro := 12)
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩ (Y := n) (D := N.width) hm
    (by simp [c₁, c₀, leafC]) (by simp [c₁, c₀, leafC, Prepare.rest]) (by simp [c₁, c₀, leafC, Prepare.rest])
    (by simp [c₁, c₀, leafC, Prepare.rest])
  set c₂ := Function.update (Function.update c₁ 16 (some (n / N.width))) 12 (some (n % N.width))
  have h₃ := Counters.erase_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₂) (j := 16) (x := n / N.width) (by simp [c₂])
  set c₃ := Function.update c₂ 16 none
  have h₄ := Counters.mul_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₃) (x := 10) (y := 5) (o := 13) (by decide) (by decide) (by decide)
    (X := N.width) (Y := n / N.width) hf (by simp [c₃, c₂, c₁, c₀, leafC, Prepare.rest])
    (by simp [c₃, c₂, c₁, c₀, leafC]) (by simp [c₃, c₂, c₁, c₀, leafC, Prepare.rest])
  set c₄ := Function.update c₃ 13 (some (N.width * (n / N.width)))
  have h₅ := Counters.zero_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₄) (j := 14) (by simp [c₄, c₃, c₂, c₁, c₀, leafC, Prepare.rest])
  set c₅ := Function.update c₄ 14 (some 0)
  have h₆ := Counters.diff_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₅) (x := 5) (y := 15) (o := 8) (by decide) (by decide) (by decide) (X := n / N.width) (Y := 1) hf
    (by simp [c₅, c₄, c₃, c₂, c₁, c₀, leafC]) (by simp [c₅, c₄, c₃, c₂, c₁, c₀, leafC, Prepare.rest])
    (by simp [c₅, c₄, c₃, c₂, c₁, c₀, leafC, Prepare.rest])
  have he : Function.update c₅ 8 (some (n / N.width - 1)) = viewC (N := N) b n := by
    funext j; fin_cases j <;> simp [c₅, c₄, c₃, c₂, c₁, c₀, leafC, viewC, nodeC, Prepare.rest, Function.update,
      Fin.ext_iff, CommonBank.K]
  rw [he] at h₆
  have L₅ := seq_runs (Counters.blk_leading _ _ _) (Counters.blk_leading _ _ _) h₅ h₆
  have L₄ := seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₄ L₅
  have L₃ := seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₃ L₄
  have L₂ := seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₂ L₃
  have L₁ := seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₁ L₂
  exact runs_mono L₁ (by unfold splitCountersCost; omega)

/-- The cost of the split. -/
def splitCost (v : Descriptor) (b n : ℕ) : ℕ :=
  splitCountersCost n N.width + RecursiveViewFrame.pushCost (hdr v) + 1500 * volume prime v +
    ((2*(bits n).length+4) + (2*(bits (n % N.width)).length+4) + (2*(bits (N.width * (n / N.width))).length+4) +
      (2*(bits 0).length+4) + 3) +
    (RecursiveViewFrame.pushCost (hdr (midView N b n v)) +
      RecursiveRowsClean.bound N.roleCount (volume prime (midView N b n v)) +
      RecursiveRowsNodeRoleBank.constant N.roleCount * volume prime (midView N b n v) + 2) +
    M8.Machine.RoleOpsClean.coefficient (NodeRows.tempOps N zeroBit) * volume prime (roleView N b n v) + 5

theorem roleData_bits {v : Descriptor} (hd : N.roleCount ∣ v.rows) (x : Fin (volume prime v) → Fin 4) (hx : Bits x)
    (j : Fin N.roleCount) : Bits (roleData (wires N) (Equiv.refl _) hd x (wires N (Fin.natAdd 1 j))) := by
  unfold roleData
  rw [RecursiveRowsSerialization.putData_selected _ (NodeBank.wires_injective N)]
  intro z
  simp only [RecursiveRowsSerialization.roleLocal, Fin.addCases_right]
  exact hx _

/-- After the split and the temporaries' fill, the node's data holds. -/
theorem init_inv {v : Descriptor} (hd : N.roleCount ∣ v.rows) (x : Fin (volume prime v) → Fin 4) (hx : Bits x) :
    NodeInv N (M8.Machine.RoleOps.run (NodeRows.tempOps N zeroBit) (roleData (wires N) (Equiv.refl _) hd x)) := by
  obtain ⟨h₁, h₂⟩ := NodeRows.run_tempOps N zeroBit (roleData (wires N) (Equiv.refl _) hd x)
  refine ⟨?_, fun i hi => ?_⟩
  · rw [h₁]
    unfold roleData
    rw [← NodeBank.wires_zero N, RecursiveRowsSerialization.putData_selected _ (NodeBank.wires_injective N)]
    simp only [RecursiveRowsSerialization.roleLocal, Fin.addCases_left]
  · obtain ⟨w, rfl⟩ := NodeBank.eq_wireSlot N i hi
    cases w with
    | inr t =>
      have := h₂ (N.tempEquiv.symm t)
      simp only [tempSlot, Equiv.apply_symm_apply] at this
      rw [this]; exact fun _ => ⟨0, rfl⟩
    | inl a =>
      have hk : ¬ ∃ k ∈ List.finRange N.tempCount, tempSlot N k = wireSlot N (.inl a) := by
        rintro ⟨k, -, hk⟩
        have := NodeBank.wireSlot_injective N hk
        simp at this
      rw [NodeRows.tempOps, NodeRows.run_fills, ite_eq_right hk]
      have he : wireSlot N (.inl a) = wires N (Fin.natAdd 1 (N.roleEquiv.symm a)) := by
        simp [wires]
      rw [he]
      exact roleData_bits hd x hx _

/-! ### The merge -/

variable (N) in
/-- The leaf loop's counters from the node's. -/
def mergeCountersB : Graph.Block (CommonBank.count (tapes N)) prime :=
  seqB (Counters.erase 5) (seqB (Counters.erase 8) (seqB Prepare.atoms (seqB Prepare.divide
    (seqB (Counters.erase 11) (Counters.zero 11)))))

variable (N) in
/-- **The node's merge.** -/
def mergeB : Graph.Block (CommonBank.count (tapes N)) prime :=
  seqB (NodeBank.ops (NodeRows.tempOps N blank)) (seqB (NodeRows.merge N) (seqB Blocks.restore (mergeCountersB N)))

/-- **The node's split.** -/
theorem split_runs {v : Descriptor} {b n : ℕ} (hpos : v.Positive) (hb : 0 < b) (hw : v.width = n * b)
    (hn : N.width ≤ n) (hd : N.roleCount ∣ v.rows) (x : Fin (volume prime v) → Fin 4) (hx : Bits x) :
    ∃ data : RecursiveMixedSchedule.Data (tapes N) (roleView N b n v), NodeInv N data ∧
      Runs (splitB N) (bank (childRoles N (RecursiveShiftRoleBank.source x)) (hdr v) fs p node scalar
          (leafC b N.width n 0) st)
        (bank (roles data) (hdr (roleView N b n v)) fs p
          (RecursiveViewFrame.savedStack (hdr (midView N b n v)) (RecursiveViewFrame.savedStack (hdr v) node))
          scalar (nodeC N b (n / N.width)) st) (splitCost (N := N) v b n) := by
  set mv := midView N b n v
  have hvol : volume prime mv = volume prime v := mid_volume N hw
  set x' : Fin (volume prime mv) → Fin 4 := fun i => x (Fin.cast hvol i)
  have hx' : Bits x' := fun i => hx _
  have hd' : N.roleCount ∣ mv.rows := hd
  set data := M8.Machine.RoleOps.run (NodeRows.tempOps N zeroBit) (roleData (wires N) (Equiv.refl _) hd' x')
  refine ⟨data, init_inv hd' x' hx', ?_⟩
  -- counters
  have h₁ := splitCounters_runs (N := N) (rr := childRoles N (RecursiveShiftRoleBank.source x)) (hs := hdr v)
    (fs := fs) (p := p) (node := node) (scalar := scalar) (st := st) (b := b) hn
  -- save the headers
  have h₂ := Blocks.push_runs (childRoles N (RecursiveShiftRoleBank.source x)) (hdr v) fs p node scalar
    (viewC (N := N) b n) st
  -- the middle view
  have he : 0 = n - n % N.width - N.width * (n / N.width) := by have := mid_sum N n; omega
  have h₃ := LeafRoutines.view_runs (roles := childRoles N (RecursiveShiftRoleBank.source x)) (f := fs) (p := p)
    (node := RecursiveViewFrame.savedStack (hdr v) node) (scalar := scalar) (st := st) (c := viewC (N := N) b n)
    (Routines.hdr_headers v) hpos hb hw (mid_le N n) he
    (by simp [viewC, nodeC, Prepare.rest]) (by simp [viewC]) (by simp [viewC]) (by simp [viewC])
  rw [Routines.hdr_eq (Headers.child_headers (Routines.hdr_headers v) he)] at h₃
  -- erase the view's counters
  have h₄₁ := Counters.erase_runs (roles := childRoles N (RecursiveShiftRoleBank.source x)) (hs := hdr mv) (f := fs)
    (p := p) (node := RecursiveViewFrame.savedStack (hdr v) node) (scalar := scalar) (st := st)
    (c := viewC (N := N) b n) (j := 9) (x := n) (by simp [viewC])
  have h₄₂ := Counters.erase_runs (roles := childRoles N (RecursiveShiftRoleBank.source x)) (hs := hdr mv) (f := fs)
    (p := p) (node := RecursiveViewFrame.savedStack (hdr v) node) (scalar := scalar) (st := st)
    (c := Function.update (viewC (N := N) b n) 9 none) (j := 12) (x := n % N.width) (by simp [viewC])
  have h₄₃ := Counters.erase_runs (roles := childRoles N (RecursiveShiftRoleBank.source x)) (hs := hdr mv) (f := fs)
    (p := p) (node := RecursiveViewFrame.savedStack (hdr v) node) (scalar := scalar) (st := st)
    (c := Function.update (Function.update (viewC (N := N) b n) 9 none) 12 none) (j := 13)
    (x := N.width * (n / N.width)) (by simp [viewC])
  have h₄₄ := Counters.erase_runs (roles := childRoles N (RecursiveShiftRoleBank.source x)) (hs := hdr mv) (f := fs)
    (p := p) (node := RecursiveViewFrame.savedStack (hdr v) node) (scalar := scalar) (st := st)
    (c := Function.update (Function.update (Function.update (viewC (N := N) b n) 9 none) 12 none) 13 none) (j := 14)
    (x := 0) (by simp [viewC])
  have hc : Function.update (Function.update (Function.update (Function.update (viewC (N := N) b n) 9 none) 12 none)
      13 none) 14 none = nodeC N b (n / N.width) := by
    funext j; fin_cases j <;> simp [viewC, nodeC, Prepare.rest, Function.update, Fin.ext_iff, CommonBank.K]
  rw [hc] at h₄₄
  -- the row split
  have hroles : childRoles N (RecursiveShiftRoleBank.source x) = roles (sourceData (v := mv) (wires N) x') := by
    rw [NodePark.source_roles, source_cast]
  have hent : ∀ R : Tapes (Shared50RecursiveBank.AuxCount K - 1) prime,
      HoareTime (RecursiveRowsNode.entry (u := Shared50RecursiveBank.AuxCount K - 1) (wires N)
          (NodeBank.wires_injective N)).program
        (fun w => w = SharedBankStageInput.raw (RecursiveViewFrameRoleBank.bank (roles (sourceData (wires N) x'))
          (hdr mv) (RecursiveViewFrame.savedStack (hdr v) node) R) _)
        (fun w => w = SharedBankStageInput.raw (RecursiveViewFrameRoleBank.bank
          (roles (roleData (wires N) (Equiv.refl _) hd' x')) (hdr (roleView N b n v))
          (RecursiveViewFrame.savedStack (hdr mv) (RecursiveViewFrame.savedStack (hdr v) node)) R) _)
        (RecursiveViewFrame.pushCost (hdr mv) + RecursiveRowsClean.bound N.roleCount (volume prime mv) +
          RecursiveRowsNodeRoleBank.constant N.roleCount * volume prime mv + 2) := by
    intro R
    obtain ⟨rs, hrs, h⟩ := RecursiveRowsNode.entry_hoare (wires N) (NodeBank.wires_injective N) (hdr mv)
      (RecursiveViewFrame.savedStack (hdr v) node) R mv (roleCount_pos N hpos hd) (Routines.hdr_headers mv)
      (mid_positive N hpos) hd' x'
    rw [Routines.hdr_eq hrs] at h
    exact h
  have h₅ := NodeBank.role_runs hent fs p scalar (nodeC N b (n / N.width)) st
  rw [← hroles] at h₅
  -- the temporaries
  have h₆ := NodeBank.ops_runs (NodeRows.tempOps N zeroBit) (Routines.hdr_headers (roleView N b n v))
    (roleView_positive N hpos hd) (roleData (wires N) (Equiv.refl _) hd' x') fs p
    (RecursiveViewFrame.savedStack (hdr mv) (RecursiveViewFrame.savedStack (hdr v) node)) scalar
    (nodeC N b (n / N.width)) st
  have L₆ := seq_runs (NodeBank.roleBlock_leading _) (NodeBank.roleBlock_leading _) h₅ h₆
  have L₄ := seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₄₁
    (seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₄₂
      (seq_runs (Counters.blk_leading _ _ _) (Counters.blk_leading _ _ _) h₄₃ h₄₄))
  have L₄' := seq_runs (Blocks.seq_leading _ _) (Blocks.seq_leading _ _) L₄ L₆
  have L₃ := seq_runs (Blocks.place_leading _ _ _ _) (Blocks.seq_leading _ _) h₃ L₄'
  have L₂ := seq_runs (Blocks.adapt_leading _ _) (Blocks.seq_leading _ _) h₂ L₃
  have L₁ := seq_runs (Blocks.seq_leading _ _) (Blocks.seq_leading _ _) h₁ L₂
  simp only [mv] at L₁
  exact runs_mono L₁ (by unfold splitCost; omega)

def mergeCountersCost (b n m : ℕ) : ℕ :=
  (2*(bits (n / m)).length+4) + (2*(bits (n / m - 1)).length+4) +
    (BinaryDescriptorDivMod.linearConstant (bits b) * (n * b + 1) + 2 * b + 6) +
    BinaryDescriptorDivMod.linearConstant (bits m) * (n + 1) + (2*(bits (n % m)).length+4) + 6 + 5

theorem mergeCounters_runs {v : Descriptor} {b n : ℕ} (hb : 0 < b) (hw : v.width = n * b) :
    Runs (mergeCountersB N) (bank rr (hdr v) fs p node scalar (nodeC N b (n / N.width)) st)
      (bank rr (hdr v) fs p node scalar (leafC b N.width n 0) st) (mergeCountersCost b n N.width) := by
  have hm : 0 < N.width := by have := N.two_le_width; omega
  have h₁ := Counters.erase_runs (roles := rr) (hs := hdr v) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := nodeC N b (n / N.width)) (j := 5) (x := n / N.width) (by simp [nodeC])
  have h₂ := Counters.erase_runs (roles := rr) (hs := hdr v) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := Function.update (nodeC N b (n / N.width)) 5 none) (j := 8) (x := n / N.width - 1)
    (by simp [nodeC])
  have hc : Function.update (Function.update (nodeC N b (n / N.width)) 5 none) 8 none = Prepare.rest b N.width := by
    funext j; fin_cases j <;> simp [nodeC, Prepare.rest, Function.update, Fin.ext_iff, CommonBank.K]
  rw [hc] at h₂
  obtain ⟨B₃, hB₃, h₃⟩ := Prepare.atoms_runs (roles := rr) (f := fs) (p := p) (node := node)
    (scalar := scalar) (st := st) (c := Prepare.rest b N.width) (hs := hdr v) hb
    (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_canonical _) rfl rfl
  have hwb : (RecursiveDimensionBank.values v 3) / b = n := by
    change v.width / b = _; rw [hw, Nat.mul_div_cancel _ hb]
  rw [hwb] at h₃
  have hw' : RecursiveDimensionBank.values v 3 = n * b := hw
  rw [hw'] at hB₃
  obtain ⟨B₄, hB₄, h₄⟩ := Prepare.divide_runs (roles := rr) (f := fs) (p := p) (node := node)
    (scalar := scalar) (st := st) (hs := hdr v) (c := Function.update (Prepare.rest b N.width) 9 (some n))
    (n := n) (m := N.width) hm (by simp) (by simp [Prepare.rest]) (by simp [Prepare.rest]) (by simp [Prepare.rest])
  set c₄ := Function.update (Function.update (Function.update (Prepare.rest b N.width) 9 (some n)) 5
    (some (n / N.width))) 11 (some (n % N.width))
  have h₅ := Counters.erase_runs (roles := rr) (hs := hdr v) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₄) (j := 11) (x := n % N.width) (by simp [c₄])
  have h₆ := Counters.zero_runs (roles := rr) (hs := hdr v) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := Function.update c₄ 11 none) (j := 11) (by simp)
  have he : Function.update (Function.update c₄ 11 none) 11 (some 0) = leafC b N.width n 0 := by
    simp only [c₄, Function.update_idem, leafC]
  rw [he] at h₆
  have L₅ := seq_runs (Counters.blk_leading _ _ _) (Counters.blk_leading _ _ _) h₅ h₆
  have L₄ := seq_runs (fun _ => rfl) (Blocks.seq_leading _ _) h₄ L₅
  have L₃ := seq_runs (fun _ => rfl) (Blocks.seq_leading _ _) h₃ L₄
  have L₂ := seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₂ L₃
  have L₁ := seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₁ L₂
  exact runs_mono L₁ (by unfold mergeCountersCost; omega)

/-- The cost of the merge. -/
def mergeCost (v : Descriptor) (b n : ℕ) : ℕ :=
  M8.Machine.RoleOpsClean.coefficient (NodeRows.tempOps N blank) * volume prime (roleView N b n v) +
    (RecursiveViewFrame.restoreCost (hdr (midView N b n v)) (hdr (roleView N b n v)) +
      RecursiveRowsClean.bound N.roleCount (volume prime (midView N b n v)) + 1) +
    RecursiveViewFrame.restoreCost (hdr v) (hdr (midView N b n v)) + mergeCountersCost b n N.width + 3

/-- **The node's merge.** -/
theorem merge_runs {v : Descriptor} {b n : ℕ} (hpos : v.Positive) (hb : 0 < b) (hw : v.width = n * b)
    (hd : N.roleCount ∣ v.rows) (data : RecursiveMixedSchedule.Data (tapes N) (roleView N b n v))
    (hinv : NodeInv N data) (hfree : NodeFree node) :
    ∃ x : Fin (volume prime v) → Fin 4, Bits x ∧
      Runs (mergeB N) (bank (roles data) (hdr (roleView N b n v)) fs p
          (RecursiveViewFrame.savedStack (hdr (midView N b n v)) (RecursiveViewFrame.savedStack (hdr v) node))
          scalar (nodeC N b (n / N.width)) st)
        (bank (childRoles N (RecursiveShiftRoleBank.source x)) (hdr v) fs p node scalar (leafC b N.width n 0) st)
        (mergeCost (N := N) v b n) := by
  set mv := midView N b n v
  have hvol : volume prime v = volume prime mv := (mid_volume N hw).symm
  have hd' : N.roleCount ∣ mv.rows := hd
  -- clear the temporaries
  have h₁ := NodeBank.ops_runs (NodeRows.tempOps N blank) (Routines.hdr_headers (roleView N b n v))
    (roleView_positive N hpos hd) data fs p
    (RecursiveViewFrame.savedStack (hdr mv) (RecursiveViewFrame.savedStack (hdr v) node)) scalar
    (nodeC N b (n / N.width)) st
  set data₁ := M8.Machine.RoleOps.run (NodeRows.tempOps N blank) data
  obtain ⟨hio₁, ht₁⟩ := NodeRows.run_tempOps N blank data
  have hworld : ∀ j, data₁ (wires N (Fin.natAdd 1 j)) = data (wires N (Fin.natAdd 1 j)) := by
    intro j
    have hk : ¬ ∃ k ∈ List.finRange N.tempCount, tempSlot N k = wires N (Fin.natAdd 1 j) := by
      rintro ⟨k, -, hk⟩
      simp only [wires, Fin.addCases_right] at hk
      have := NodeBank.wireSlot_injective N hk
      simp at this
    simp only [data₁]
    rw [NodeRows.tempOps, NodeRows.run_fills, ite_eq_right hk]
  have hio₁' : NodeRows.NodeData N data₁ := by
    exact hio₁.trans hinv.1
  obtain ⟨x', hx', hcells⟩ := NodeRows.roleData_surjective N (v := mv) hd' data₁ hio₁' ht₁
  -- the row merge
  have hfree' : RecursiveViewFrame.Free (hdr mv) (RecursiveViewFrame.savedStack (hdr v) node) :=
    RecursiveRowsNode.free_of_available _ _ (RecursiveRowsNode.saved_available _ _ hfree)
  have hexit := fun R => RecursiveRowsNode.exit_hoare (u := Shared50RecursiveBank.AuxCount K - 1) (NodeBank.mergeRoute N)
    (wires N) (NodeBank.wires_injective N) (hdr mv) (hdr (roleView N b n v)) (RecursiveViewFrame.savedStack (hdr v) node)
    R hfree' mv (roleCount_pos N hpos hd) (Routines.hdr_headers mv) (mid_positive N hpos) hd' x'
  have h₂ := NodeBank.role_runs hexit fs p scalar (nodeC N b (n / N.width)) st
  rw [hx'] at h₂
  -- restore the headers
  have h₃ := Blocks.restore_runs (roles (sourceData (wires N) x')) (hdr mv) fs p node scalar
    (nodeC N b (n / N.width)) st (hdr v) (Family.nodeFree_free hfree _)
  -- the counters
  have h₄ := mergeCounters_runs (N := N) (rr := roles (sourceData (wires N) x')) (fs := fs) (p := p) (node := node)
    (scalar := scalar) (st := st) hb hw
  set x : Fin (volume prime v) → Fin 4 := fun i => x' (Fin.cast hvol i)
  have hrx : roles (sourceData (wires N) x') = childRoles N (RecursiveShiftRoleBank.source x) := by
    rw [NodePark.source_roles, source_cast]
  rw [hrx] at h₂ h₃ h₄
  refine ⟨x, fun i => ?_, ?_⟩
  · obtain ⟨j, z, hz⟩ := hcells (Fin.cast hvol i)
    have hne : wires N (Fin.natAdd 1 j) ≠ io N := by
      simp only [wires, Fin.addCases_right]; exact NodeBank.wireSlot_ne_io N _
    rw [show x i = x' (Fin.cast hvol i) from rfl, hz, hworld]
    exact hinv.2 _ hne z
  have L₃ := seq_runs (Blocks.adapt_leading _ _) (Blocks.seq_leading _ _) h₃ h₄
  have L₂ := seq_runs (NodeBank.roleBlock_leading _) (Blocks.seq_leading _ _) h₂ L₃
  have L₁ := seq_runs (NodeBank.roleBlock_leading _) (Blocks.seq_leading _ _) h₁ L₂
  simp only [mv] at L₁
  exact runs_mono L₁ (by unfold mergeCost; omega)

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSplit
