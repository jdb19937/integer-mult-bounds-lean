module

public import IntegerMultBounds.MathlibTM2.M8.Machine.PieceExecution
public import IntegerMultBounds.MathlibTM2.M8.Machine.NodeBoundary

/-!
# A recursive node on the fixed cyclic graph

A recursive node runs the split, the temporaries' zero fill, the piece schedule, the
temporaries' clear, the merge, the ancestor header restoration and the decoded return on one
fixed cyclic graph (`split_return`, `guard_return`), as `Shared50RecursiveNodeExecution` does for
Shared50. The piece semantics give the exact merge input (`NodeData.clear_network`). Only the
recursive child graph traces remain premises (`Calls`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.NodeExecution
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Control
open Implementation (commonCount implementation widthSlot pcStack)
open BaseExecution (entryConfig)
open PieceExecution (dataBank actualCallBound overhead)
open NodeLayout (wires mergeRoute tempOps)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeRows (transpose)
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveViewedAction (Data)
open RecursiveRowsSerialization (sourceData roleData)
open SharedBankStageInput (raw)
variable {k b : ℕ} {v : Descriptor}

/-- Exactly the remaining child trace obligation at each reachable binary
call boundary. Its budget includes the physical entry and recovery work. -/
def Calls (capacity : Fintype.card PC ≤ 2^k) (hw : v.width=Machine.width*b)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node : Tapes 1 prime) (st : Tapes 2 prime) (C : ℕ) : Prop :=
  ∀ (site : Site) w i j, pieces[site] = .call w i j →
    ∀ data : Data payloadCount v, BinaryInvariant.Ready data →
      ∃ n ≤ actualCallBound (v := v) k C w i j,
        Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
          (entryConfig capacity (.piece site) (dataBank hs f p node st data)) =
        some (entryConfig capacity (successor site) (dataBank hs f p node st
          (ChildPermutation.child hw w i j data)))

def entryCoefficient : ℕ :=
  74+RecursiveRowsNode.rowConstant roleCount+RecursiveRowsNodeRoleBank.constant roleCount
def exitCoefficient : ℕ := 128+RecursiveRowsNode.rowConstant roleCount

/-- The zero fill and the clear of the temporaries. -/
def tempCoefficient : ℕ :=
  RoleOpsClean.coefficient (tempOps (SparseRoleCircuit.encode (a := 0) 0))+
    RoleOpsClean.coefficient (tempOps blank)

/-- Everything charged on the role volume: the pieces and the temporaries. -/
def scheduleCoefficient (k : ℕ) : ℕ := (pieces.map (overhead k)).sum+tempCoefficient

omit [Net] in
theorem join {t q a n₁ n₂ : ℕ} {P : Program t q a} {c₁ c₂ c₃ : Config t q a}
    (h₁ : Machine.run P n₁ c₁ = some c₂) (h₂ : Machine.run P n₂ c₂ = some c₃) :
    Machine.run P (n₁+n₂) c₁ = some c₃ := by
  rw [run_add, h₁, Option.bind_some, h₂]

/-- Shared restoration and exact decoded return, independent of the completed
node's payload array. This keeps framed stack reduction outside node assembly. -/
theorem restore_return (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (roles : Tapes payloadCount prime) (old hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (hd : RecursiveStackAllocation.Available 0 st) (hpc : RecursiveStackAllocation.Available 1 st) :
    ∃ steps ≤ RecursiveChildCallReturn.cost old hs+k+3,
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) steps
        (entryConfig capacity .restore (Shared50RecursiveBank.bank roles hs f p node
          (SharedBank.empty 1 prime) (SharedBank.empty 0 prime)
          (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target))))) =
        some (entryConfig capacity target (Shared50RecursiveBank.bank roles old f p node
          (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st)) := by
  let code := FiniteReturnStack.address capacity (encoding target)
  let before := Shared50RecursiveBank.bank roles hs f p node (SharedBank.empty 1 prime)
    (SharedBank.empty 0 prime) (RecursiveChildCallSetup.savedStacks old st code)
  let pending := Shared50RecursiveBank.bank roles old f p node (SharedBank.empty 1 prime)
    (SharedBank.empty 0 prime) (RecursiveChildCallReturn.pending st code)
  let after := Shared50RecursiveBank.bank roles old f p node (SharedBank.empty 1 prime)
    (SharedBank.empty 0 prime) st
  have hrestore := Shared50RecursiveBankReturn.restore_hoare roles old hs f p node
    (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st code hd
  obtain ⟨nr,hnr,hrr⟩ := BlockExecution.block_jump capacity widthSlot pcStack
    (implementation k) .restore .pop before pending (RecursiveChildCallReturn.cost old hs) hrestore (fun _ => rfl)
  obtain ⟨hhead,htape⟩ := Shared50RecursiveBankReturn.pending_pc roles
    old f p node (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st code
  have hfree : ∀ j < k, st.tape 1 (st.head 1+j)=blank := RecursiveStackAllocation.pc_free 1 st hpc
  have hpop := ReturnExecution.pop_jump capacity widthSlot pcStack (implementation k)
    target pending (st.tape 1) (st.head 1) htape hhead hfree
  have hreset : SharedPlacementAlphabet.setTape pending pcStack (st.tape 1) (st.head 1) = after :=
    Shared50RecursiveBankReturn.reset_pending roles old f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st code
  rw [hreset] at hpop
  change Machine.run _ nr (entryConfig capacity .restore before) = some (entryConfig capacity .pop pending) at hrr
  change Machine.run _ (k+2) (entryConfig capacity .pop pending) = some (entryConfig capacity target after) at hpop
  exact ⟨nr+(k+2),by omega,join hrr hpop⟩

/-- The split block and its edge to the temporaries' zero fill. -/
theorem entry_run (capacity : Fintype.card PC ≤ 2^k) (hp : v.Positive)
    (hdiv : roleCount ∣ v.rows) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node : Tapes 1 prime) (st : Tapes 2 prime) (x : Fin (volume prime v) → Fin 4) :
    ∃ rs : List Bool, RecursiveDimensionBank.Headers (role v roleCount)
        (RecursiveRowsNodeHeaders.headers hs rs) ∧
      ∃ n ≤ entryCoefficient*volume prime v+1,
        Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
          (entryConfig capacity .split (dataBank hs f p node st (sourceData wires x))) =
          some (entryConfig capacity .tempInit (dataBank (RecursiveRowsNodeHeaders.headers hs rs) f p
            (RecursiveViewFrame.savedStack hs node) st (roleData wires (Equiv.refl _) hdiv x))) := by
  obtain ⟨rs,hrs,hentry⟩ := BankNodes.entry_hoare (u := 0) hs node
    (SharedBank.empty 1 prime) f p (SharedBank.empty 0 prime) st v hv hp hdiv x
  have hb : HoareTime (block capacity widthSlot pcStack (implementation k) .split).program
      (fun ww => ww = raw (dataBank hs f p node st (sourceData wires x))
        (block capacity widthSlot pcStack (implementation k) .split).tapes)
      (fun ww => ww = raw (dataBank (RecursiveRowsNodeHeaders.headers hs rs) f p
        (RecursiveViewFrame.savedStack hs node) st (roleData wires (Equiv.refl _) hdiv x))
        (block capacity widthSlot pcStack (implementation k) .split).tapes)
      (entryCoefficient*volume prime v) :=
    hentry.consequence (fun _ h => h) (fun _ h => h)
      (RecursiveRowsNode.entry_cost_linear (c := roleCount) v hp hs hv)
  exact ⟨rs,hrs,BlockExecution.block_jump capacity widthSlot pcStack (implementation k)
    .split .tempInit _ _ _ hb (fun _ => rfl)⟩

/-- The temporaries' zero fill and its edge to the first piece. -/
theorem tempInit_run (capacity : Fintype.card PC ≤ 2^k) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node : Tapes 1 prime) (st : Tapes 2 prime) (data : Data payloadCount v) :
    ∃ n ≤ RoleOpsClean.coefficient (tempOps (SparseRoleCircuit.encode (a := 0) 0))*volume prime v+1,
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
        (entryConfig capacity .tempInit (dataBank hs f p node st data)) =
        some (entryConfig capacity first (dataBank hs f p node st
          (RoleOps.run (tempOps (SparseRoleCircuit.encode (a := 0) 0)) data))) :=
  BlockExecution.block_jump capacity widthSlot pcStack (implementation k) .tempInit first _ _ _
    (BankNodes.ops_hoare (u := 0) (tempOps (SparseRoleCircuit.encode (a := 0) 0)) hp hs hv f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st data) (fun _ => rfl)

/-- The temporaries' clear and its edge to the merge. -/
theorem tempClear_run (capacity : Fintype.card PC ≤ 2^k) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node : Tapes 1 prime) (st : Tapes 2 prime) (data : Data payloadCount v) :
    ∃ n ≤ RoleOpsClean.coefficient (tempOps blank)*volume prime v+1,
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
        (entryConfig capacity .tempClear (dataBank hs f p node st data)) =
        some (entryConfig capacity .merge (dataBank hs f p node st (RoleOps.run (tempOps blank) data))) :=
  BlockExecution.block_jump capacity widthSlot pcStack (implementation k) .tempClear .merge _ _ _
    (BankNodes.ops_hoare (u := 0) (tempOps blank) hp hs hv f p node (SharedBank.empty 1 prime)
      (SharedBank.empty 0 prime) st data) (fun _ => rfl)

/-- The merge block and its edge to the header restoration. -/
theorem merge_run (capacity : Fintype.card PC ≤ 2^k) (hp : v.Positive) (hdiv : roleCount ∣ v.rows)
    (hs reduced : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (hrs : RecursiveDimensionBank.Headers (role v roleCount) reduced)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (hn : RecursiveStackAllocation.Available 0 node) (x : Fin (volume prime v) → Fin 4) :
    ∃ n ≤ exitCoefficient*volume prime v+1,
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
        (entryConfig capacity .merge (dataBank reduced f p (RecursiveViewFrame.savedStack hs node) st
          (roleData wires mergeRoute hdiv x))) =
        some (entryConfig capacity .restore (dataBank hs f p node st (sourceData wires x))) := by
  have hexit := BankNodes.exit_hoare (u := 0) hs reduced node (SharedBank.empty 1 prime) f p
    (SharedBank.empty 0 prime) st (RecursiveRowsNode.free_of_available hs node hn) v hv hp hdiv x
  have hb : HoareTime (block capacity widthSlot pcStack (implementation k) .merge).program
      (fun ww => ww = raw (dataBank reduced f p (RecursiveViewFrame.savedStack hs node) st
        (roleData wires mergeRoute hdiv x)) (block capacity widthSlot pcStack (implementation k) .merge).tapes)
      (fun ww => ww = raw (dataBank hs f p node st (sourceData wires x))
        (block capacity widthSlot pcStack (implementation k) .merge).tapes)
      (exitCoefficient*volume prime v) :=
    hexit.consequence (fun _ h => h) (fun _ h => h)
      (RecursiveRowsNode.exit_cost_linear v hp roleCount_pos hdiv hs reduced hv hrs)
  exact BlockExecution.block_jump capacity widthSlot pcStack (implementation k)
    .merge .restore _ _ _ hb (fun _ => rfl)

omit [Net] in
/-- Arithmetic assembly is checked before the fixed machine coefficients are
instantiated. -/
theorem assembly_bound {E I X Z T S C R V W k ne ni ns nc nm nr : ℕ}
    (he : ne ≤ E*V+1) (hi : ni ≤ I*W+1) (hs : ns ≤ T*W+S*C) (hc : nc ≤ Z*W+1)
    (hm : nm ≤ X*V+1) (hr : nr ≤ R+k+3) :
    ne+ni+ns+nc+nm+nr ≤ (E+X)*V+(T+(I+Z))*W+S*C+R+k+7 := by
  nlinarith

/-- Full non-base node execution starting at its split block. No abstract
network or merge oracle is supplied: actual piece semantics yield the exact
physical merge input. Shared return restores the caller's headers and stacks. -/
theorem split_return (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (hw : v.width=Machine.width*b) (hp : v.Positive) (hdiv : roleCount ∣ v.rows)
    (old hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (hn : RecursiveStackAllocation.Available 0 node)
    (hd : RecursiveStackAllocation.Available 0 st) (hpc : RecursiveStackAllocation.Available 1 st)
    (x : Fin (volume prime v) → ZMod 2) (C : ℕ)
    (calls : ∀ rs : List Bool, RecursiveDimensionBank.Headers (role v roleCount)
        (RecursiveRowsNodeHeaders.headers hs rs) →
      Calls capacity (v := role v roleCount) hw (RecursiveRowsNodeHeaders.headers hs rs) f p
        (RecursiveViewFrame.savedStack hs node)
        (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target))) C) :
    ∃ steps ≤ (entryCoefficient+exitCoefficient)*volume prime v+
        scheduleCoefficient k*volume prime (role v roleCount)+
        (Net.net).rankSum*C+RecursiveChildCallReturn.cost old hs+k+7,
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) steps
        (entryConfig capacity .split (dataBank hs f p node
          (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
          (sourceData wires (encoded x)))) =
        some (entryConfig capacity target (dataBank old f p node st
          (sourceData wires (encoded (transpose (one_dvd _) x))))) := by
  let saved := RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target))
  let nodeSaved := RecursiveViewFrame.savedStack hs node
  have hpRole := RecursiveRowsNodeLayout.role_positive roleCount v roleCount_pos hp hdiv
  obtain ⟨rs,hrs,ne,hne,hre⟩ := entry_run capacity hp hdiv hs hv f p node saved (encoded x)
  let reduced := RecursiveRowsNodeHeaders.headers hs rs
  obtain ⟨ni,hni,hri⟩ := tempInit_run capacity (v := role v roleCount) hpRole reduced hrs f p
    nodeSaved saved (roleData wires (Equiv.refl _) hdiv (encoded x))
  rw [NodeData.init_encoded] at hri
  obtain ⟨ns,hns,hrsched⟩ := PieceExecution.binary_schedule_bound capacity
    (v := role v roleCount) hw (ChildPermutation.child hw) hpRole reduced hrs f p
    nodeSaved saved (ChildPermutation.child_spec (v := role v roleCount) hw) C (calls rs hrs)
    (encodedBits (NodeData.splitWire hdiv x) (fun _ => blank))
    (BinaryInvariant.of_encoded _)
  obtain ⟨nc,hnc,hrc⟩ := tempClear_run capacity (v := role v roleCount) hpRole reduced hrs f p
    nodeSaved saved (Transport.run hw (ChildPermutation.child hw) pieces
      (encodedBits (NodeData.splitWire hdiv x) (fun _ => blank)))
  rw [NodeData.clear_network hw hdiv _ (ChildPermutation.child_spec (v := role v roleCount) hw) x] at hrc
  obtain ⟨nm,hnm,hrm⟩ := merge_run capacity hp hdiv hs reduced hv hrs f p node saved hn
    (transpose hdiv (encoded x))
  obtain ⟨nr,hnr,hrr⟩ := restore_return capacity target
    (RecursiveRoleSerialization.roles (sourceData wires (transpose hdiv (encoded x))))
    old hs f p node st hd hpc
  have hout : transpose hdiv (encoded x) = encoded (transpose (one_dvd _) x) := by
    rw [Shared50RecursiveChildPermutation.transpose_independent roleCount_pos (by decide : 0 < 1)
      hdiv (one_dvd _)]
    rfl
  refine ⟨ne+ni+ns+nc+nm+nr, ?_, ?_⟩
  · exact assembly_bound hne hni hns hnc hnm hnr
  · have h := join (join (join (join (join hre hri) hrsched) hrc) hrm) hrr
    rw [hout] at h
    exact h

omit [Net] in
theorem guard_assembly_bound {A R k ng nn : ℕ} (hg : ng ≤ 3)
    (hn : nn ≤ A+R+k+7) : ng+nn ≤ A+R+k+10 := by omega

/-- Starting at the actual width guard, execute the complete recursive node
and return to the physically decoded caller address on the exact final bank. -/
theorem guard_return (capacity : Fintype.card PC ≤ 2^k) (target : PC)
    (hw : v.width=Machine.width*b) (hp : v.Positive) (hdiv : roleCount ∣ v.rows)
    (old hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (hn : RecursiveStackAllocation.Available 0 node)
    (hd : RecursiveStackAllocation.Available 0 st) (hpc : RecursiveStackAllocation.Available 1 st)
    (x : Fin (volume prime v) → ZMod 2) (C : ℕ)
    (calls : ∀ rs : List Bool, RecursiveDimensionBank.Headers (role v roleCount)
        (RecursiveRowsNodeHeaders.headers hs rs) →
      Calls capacity (v := role v roleCount) hw (RecursiveRowsNodeHeaders.headers hs rs) f p
        (RecursiveViewFrame.savedStack hs node)
        (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target))) C) :
    ∃ steps ≤ (entryCoefficient+exitCoefficient)*volume prime v+
        scheduleCoefficient k*volume prime (role v roleCount)+
        (Net.net).rankSum*C+RecursiveChildCallReturn.cost old hs+k+10,
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) steps
        (entryConfig capacity .guard (dataBank hs f p node
          (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
          (sourceData wires (encoded x)))) =
        some (entryConfig capacity target (dataBank old f p node st
          (sourceData wires (encoded (transpose (one_dvd _) x))))) := by
  let before := dataBank hs f p node
    (RecursiveChildCallSetup.savedStacks old st (FiniteReturnStack.address capacity (encoding target)))
    (sourceData wires (encoded x))
  obtain ⟨ng,hng,hg⟩ := Execution.guard_jump capacity widthSlot pcStack
    (implementation k) before (hs 3) (BankFacts.bank_header _ _ _ _ _ _ _ _ 3).1
    ((BankFacts.bank_header _ _ _ _ _ _ _ _ 3).2.trans
      (BinaryDescriptorStackRoundtrip.descriptor_encoded (hs 3)).symm) (hv.2 3)
  have hbranch : Execution.branch (Counter.value (hs 3)) = PC.split := by
    unfold Execution.branch
    have hh : Counter.value (hs 3) = v.width := hv.1 3
    have hne : Counter.value (hs 3) ≠ 1 := by
      rw [hh, hw]
      intro h1
      have := two_le_width
      have := Nat.eq_one_of_mul_eq_one_right h1
      omega
    rw [ite_eq_right hne]
  rw [hbranch] at hg
  change Machine.run _ ng (entryConfig capacity .guard before) = some (entryConfig capacity .split before) at hg
  obtain ⟨nn,hnn,hr⟩ := split_return capacity target hw hp hdiv old hs hv f p node st hn hd hpc x C calls
  exact ⟨ng+nn,guard_assembly_bound hng hnn,join hg hr⟩

end
end IntegerMultBounds.MathlibTM2.M8.Machine.NodeExecution
