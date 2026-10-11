module

public import IntegerMultBounds.Machine.CompactComplexActualEventNetwork

/-! The literal completed-event schedule realizes the original compiler,
with every scalar block between its own actual alignment and next group,
and all original terminal sink incidences retained. -/
@[expose] public section

namespace IntegerMultBounds.Machine.CompactComplexActualInterleavedNetwork
noncomputable section
open Networks
open CompactComplexCompletedLiveLower
open ComplexRecursiveCallSchema (calls)
open CompactComplexActualEventNetwork
open CompactComplexScalarIntegerRows (GroupIndex gates)
open CompactComplexActualScalarNetworkPrefix (networkPrefix networkTail alignment)
attribute [local irreducible] ComplexRank25.program groups schedule

def instructions (columns : ℕ) : Event →
    List (FramedFactorExecution.Instruction ComplexFramedExecution.Wire ℚ (BinaryColumns.Arrays (25^3) columns))
  | .scalar g => (gates g).map FramedFactorExecution.Instruction.gate
  | .child call => [childInstruction columns call]

def expand (columns : ℕ) (es : List Event) := es.flatMap (instructions columns)

def scheduleSuffix (n : ℕ) := assembleWith groupCalls (groups.drop n) (calls.drop (callBoundary n))

private theorem expand_append (columns : ℕ) (xs ys : List Event) :
    expand columns (xs++ys)=expand columns xs++expand columns ys :=
  List.flatMap_append

private theorem expand_scalar (columns : ℕ) (g : GroupIndex) (es : List Event) :
    expand columns (Event.scalar g::es)=
      (gates g).map FramedFactorExecution.Instruction.gate++expand columns es := rfl

private theorem expand_children (columns : ℕ) (cs : List ComplexRecursiveCallSchema.Call) :
    expand columns (cs.map Event.child)=cs.map (childInstruction columns) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simpa only [expand,List.map_cons,List.flatMap_cons,instructions,List.singleton_append] using
      congrArg (List.cons (childInstruction columns c)) ih

theorem suffix_step (g : GroupIndex) :
    scheduleSuffix g.val=(callInterval g).map Event.child++Event.scalar g::scheduleSuffix (g.val+1) := by
  have hg : g.val<groups.length := by simpa only [groups,List.length_ofFn] using g.isLt
  have hs := List.drop_eq_getElem_cons hg
  have he : groups[g.val]'hg=g := by
    simp only [groups,List.getElem_ofFn]
    apply Fin.ext
    rfl
  rw [he] at hs
  unfold scheduleSuffix
  rw [hs,assembleWith,←callInterval_next]
  rfl

theorem suffix_terminal : scheduleSuffix ComplexRank25.program.length=
    (calls.drop (callBoundary ComplexRank25.program.length)).map Event.child := by
  unfold scheduleSuffix
  have h : groups.length=ComplexRank25.program.length := by simp only [groups,List.length_ofFn]
  rw [←h,List.drop_length,assembleWith]

theorem original_tail_step (columns : ℕ) (g : GroupIndex) :
    networkTail columns g.val=alignment columns g++
      (gates g).map (FramedCircuit.Instruction.gate (E:=BinaryColumns.Arrays (25^3) columns))++
      networkTail columns (g.val+1) := by
  have hg := CompactComplexActualScalarNetworkPrefix.original_network_split columns g.val
  have hn := CompactComplexActualScalarNetworkPrefix.original_network_split columns (g.val+1)
  rw [CompactComplexActualScalarNetworkPrefix.prefix_step] at hn
  have h := hg.symm.trans hn
  simp only [List.append_assoc] at h
  simpa only [List.append_assoc] using List.append_cancel_left h

private theorem run_gates (columns : ℕ) (gs : Circuit.Program ComplexFramedExecution.Wire ℚ)
    (stored : Stored columns) :
    FramedFactorExecution.run (gs.map FramedFactorExecution.Instruction.gate) stored=
      FramedCircuit.run (gs.map FramedCircuit.Instruction.gate) stored := by
  induction gs generalizing stored with
  | nil => rfl
  | cons g gs ih => exact ih _

/-- Backward induction consumes each real call prefix before its own scalar
block, and concludes with the original compiler's complete sink suffix. -/
theorem suffix_run (columns n : ℕ) (hn : n≤ComplexRank25.program.length)
    (stored : Stored columns) :
    FramedFactorExecution.run (expand columns (scheduleSuffix n)) stored=
      FramedCircuit.run (networkTail columns n) stored := by
  have h : ∀ n (hn : n≤ComplexRank25.program.length) (stored : Stored columns),
      FramedFactorExecution.run (expand columns (scheduleSuffix n)) stored=
        FramedCircuit.run (networkTail columns n) stored := by
    intro n hn
    apply Nat.decreasingInduction (motive:=fun n _ => ∀ stored : Stored columns,
      FramedFactorExecution.run (expand columns (scheduleSuffix n)) stored=
        FramedCircuit.run (networkTail columns n) stored) ?_ ?_ hn
    · intro k hk ih stored
      let g : GroupIndex := ⟨k,hk⟩
      rw [suffix_step g,original_tail_step columns g]
      rw [expand_append,expand_children,expand_scalar]
      simp only [FramedFactorExecution.run_append,FramedCircuit.run_append,
        run_callInterval_alignment,run_gates]
      exact ih _
    · intro stored
      rw [suffix_terminal,expand_children,run_terminalCalls_sink]
  exact h n hn stored

/-- Exact action of the literal schedule on the named original network.
No alternate event fold or assumed full-network equality is the target. -/
theorem schedule_run (columns : ℕ) (stored : Stored columns) :
    FramedFactorExecution.run (expand columns schedule) stored=
      FramedCircuit.run (ComplexFramedExecution.network columns) stored := by
  have hs : scheduleSuffix 0=schedule := by
    unfold scheduleSuffix schedule assemble
    rw [callBoundary_zero,List.drop_zero,List.drop_zero]
  have ht := CompactComplexActualScalarNetworkPrefix.original_network_split columns 0
  have hp : networkPrefix columns 0=[] := by
    unfold networkPrefix
    simp only [List.take_zero,GroupedModuleFrames.compile]
  rw [hp,List.nil_append] at ht
  rw [←hs,ht]
  exact suffix_run columns 0 (Nat.zero_le _) stored

/-- The actual original call family and original scalar blocks agree with
the already-certified literal lowering of the original framed compiler. -/
theorem schedule_lowered_run (columns : ℕ) (stored : Stored columns) :
    FramedFactorExecution.run (expand columns schedule) stored=
      FramedFactorExecution.run (ComplexFramedExecution.lowered columns
        CompactComplexActualCallLoweredNetwork.directions) stored := by
  rw [schedule_run,ComplexFramedExecution.lowered,FramedFactorExecution.run_lower _ _
    (ComplexFramedExecution.factor_certificate columns _ CompactComplexActualCallLoweredNetwork.realizes)]

end
end IntegerMultBounds.Machine.CompactComplexActualInterleavedNetwork
