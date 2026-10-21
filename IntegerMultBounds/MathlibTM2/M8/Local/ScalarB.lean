module

public import IntegerMultBounds.MathlibTM2.M8.Local.WitnessB

/-!
# The design-B word on scalars

The plan `planB` defers the slots of the deferred uses, in readout order, and orders the V gates
as upstream does. The phase invariant gives the conditions of `Dag.wordB_run`: the first phase
leaves the deferred slots alone (`planB_first`), the second the centres (`planB_rest`), and no
centre is deferred (`planB_cen`). So the design-B word `wordPR97B`, like the plain word, adds
every source into the target of the same triple (`wordPR97B_target`) and leaves sources and side
slots unchanged (`wordPR97B_other`), on arbitrary contents.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

noncomputable section

open Networks

namespace Dag
variable {D : Dag} {Φ Ψ : ℕ → Bool}

theorem vop_eq_of_side {o : Op} (h : (D.vop o).isSrc = false) : D.vop o = o := by
  cases o with
  | copy p f n =>
    by_cases hn : n < D.v
    · simp [vop, hn, Op.isSrc] at h
    · simp [vop, hn]
  | _ => rfl

theorem mem_sideB {op : Op} (h : op ∈ D.sideB) :
    op ∈ D.compile.ops ∧ D.side op = true ∧ D.vop op = op := by
  obtain ⟨hm, hs⟩ := List.mem_filter.mp h
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hm
  have hs' : (D.vop o).isSrc = false := by simpa using hs
  have e := vop_eq_of_side hs'
  rw [e] at hs' ⊢
  exact ⟨ho, by simp [side, e, hs'], e⟩

/-- The side operations inherit the phase order of the compiled operations. -/
theorem sideB_pairwise (hs : D.Sorted Φ Ψ D.compile.ops) :
    D.sideB.Pairwise fun o o' => phase Φ Ψ o = false → phase Φ Ψ o' = true →
      ∀ s ∈ o'.slots, s ∉ o.slots := by
  unfold sideB opsB
  rw [List.pairwise_filter, List.pairwise_map]
  refine hs.imp fun {o o'} h ho ho' hp hp' => ?_
  have e : D.vop o = o := vop_eq_of_side (by simpa using ho)
  have e' : D.vop o' = o' := vop_eq_of_side (by simpa using ho')
  rw [e] at hp ho
  rw [e'] at hp' ho'
  rw [e, e']
  exact h (by simp [side, e, (by simpa using ho : o.isSrc = false)]) hp
    (by simp [side, e', (by simpa using ho' : o'.isSrc = false)]) hp'

/-- Every design-B gate is an executable XOR between distinct registers. -/
theorem wordB_xor (D : Dag) (targets : ℕ → List ℕ) (nY : ℕ) (pl : BPlan)
    (hv : D.Valid) : IsXorProg (D.wordB targets nY pl) := by
  have hops (ops : List Op) (h : ∀ op ∈ ops, op ∈ D.opsB) :
      IsXorProg (ops.map opGate) := by
    intro g hg
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hg
    exact opGate_xor (D.opsB_ok hv op (h op hop)).1
  have hnow := hops (D.vNow pl) (by
    intro op h
    simp only [vNow, keyedOps, List.mem_mergeSort, List.mem_filter, srcB] at h
    exact h.1.1)
  have hlate := hops (D.vLate pl) (by
    intro op h
    simp only [vLate, keyedOps, List.mem_mergeSort, List.mem_filter, srcB] at h
    exact h.1.1)
  have hfirst := hops (D.opsFirst pl) (by
    intro op h
    exact (List.mem_filter.mp (List.mem_filter.mp h).1).1)
  have hrest := hops (D.opsRest pl) (by
    intro op h
    exact (List.mem_filter.mp (List.mem_filter.mp h).1).1)
  have hroots (js : List ℕ) : IsXorProg (D.rootReadsAt targets js) := by
    intro g hg
    simp only [rootReadsAt, List.mem_flatMap, List.mem_map] at hg
    obtain ⟨j, _, T, _, rfl⟩ := hg
    exact ⟨_, _, by simp, rfl⟩
  have hreverse : IsXorProg
      (((D.vNow pl ++ D.vLate pl ++ D.opsFirst pl ++ D.opsRest pl).map opGate).reverse) := by
    simpa only [List.map_append] using (((hnow.append hlate).append hfirst).append hrest).reverse
  exact ((((((((D.readouts_xor targets nY _).append hnow).append hfirst).append
    (hroots _)).append (D.readouts_xor targets nY _)).append hlate).append hrest).append
      (hroots _)).append hreverse

end Dag

theorem lastNode_some : ∀ {ops : List Op} {cur : ℕ → Option ℕ} {s n : ℕ},
    ops.foldl touchOp cur s = some n → cur s = some n ∨ ∃ op ∈ ops, s ∈ op.slots ∧ op.node = n
  | [], _, _, _, h => Or.inl h
  | op :: ops, cur, s, n, h => by
    rcases lastNode_some (ops := ops) h with h' | ⟨o, ho, h2⟩
    · by_cases hs : s ∈ op.slots
      · simp only [touchOp, hs, ite_true, Option.some.injEq] at h'
        exact Or.inr ⟨op, List.mem_cons_self, hs, h'⟩
      · simp only [touchOp, hs, ite_false] at h'
        exact Or.inl h'
    · exact Or.inr ⟨o, List.mem_cons_of_mem _ ho, h2⟩

/-! ### The plan -/

/-- The plan of the design-B word: phases and deferred uses from the data, upstream's orders. -/
def planB : BPlan where
  Φ := phiB
  Ψ := psiB
  cen := cenB
  defS := deferredUses.map dagB.compile.pend
  keyD := deferredUses.map dagB.compile.pend
  keyE := earlyV.map dagB.compile.pend
  keyV := lateV.map dagB.compile.pend

/-- **The design-B word** of the PR97 side slots. -/
def wordPR97B : Circuit.Program Reg (ZMod 2) := dagB.wordB targets leafCount planB

theorem targets_lt : ∀ j T, T ∈ targets j → T < leafCount := by
  intro j T h
  unfold targets at h
  split_ifs at h with hj
  · rw [List.mem_singleton] at h
    rw [h]
    exact Nat.div_lt_of_lt_mul (by omega)
  · exact List.mem_range.mp (List.mem_filter.mp h).1

theorem planB_isDef {s : ℕ} (h : planB.isDef s = true) :
    ∃ u ∈ deferredUses, dagB.compile.pend u = s := by
  simpa [BPlan.isDef, planB] using h

theorem planB_first : ∀ op ∈ dagB.sideB, Dag.phase planB.Φ planB.Ψ op = true →
    ∀ s ∈ op.slots, planB.isDef s = false := by
  intro op hop hph s hs
  by_contra hd
  obtain ⟨u, hu, rfl⟩ := planB_isDef (by simpa using hd)
  obtain ⟨hm, hside, -⟩ := Dag.mem_sideB hop
  exact Dag.phase_deferred dagB_valid phaseHypB hu ⟨op, hm, hside, hph, hs⟩

theorem planB_rest : ∀ op ∈ dagB.sideB, Dag.phase planB.Φ planB.Ψ op = false → ∀ j,
    j < dagB.rootCount → planB.cen j = true → dagB.compile.pend (.root j) ∉ op.slots := by
  intro op hop hph j hj hc hs
  obtain ⟨hm, hside, -⟩ := Dag.mem_sideB hop
  exact Dag.phase_centre dagB_valid phaseHypB hj hc ⟨op, hm, hside, hph, hs⟩

/-- A retained centre's slot is touched in the first phase. -/
theorem centre_hit {j : ℕ} (hj : j < dagB.rootCount) (hc : cenB j = true) :
    dagB.Hit phiB psiB true dagB.compile.ops (dagB.compile.pend (.root j)) := by
  have hl := dagB.compile_root_last dagB_valid (Le := fun _ _ => True) ⟨fun _ => trivial,
    fun _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩ hj
  rcases lastNode_some hl with h | ⟨op, hop, hs, hn⟩
  · simp at h
  · have hco := centreOk_of hj hc
    simp only [centreOk, Bool.and_eq_true, Nat.ble_eq] at hco
    obtain ⟨hv, hpsi⟩ := hco
    have hy : dagB.rootNode j = (rootAt j).node := rfl
    rw [hy] at hn
    have hnode : dagB.v ≤ op.node := by rw [hn]; exact hv
    refine ⟨op, hop, ?_, ?_, hs⟩
    · cases op with
      | src s' n' =>
        have := ((dagB.compile_ops_node _ hop).2 s' n' rfl)
        simp only [Op.node] at hnode
        omega
      | _ => exact Dag.side_of_le hnode rfl
    · cases op with
      | src s' n' =>
        have := ((dagB.compile_ops_node _ hop).2 s' n' rfl)
        simp only [Op.node] at hnode
        omega
      | add p o k =>
        simp only [Op.node] at hn
        simp only [Dag.phase, hn]
        exact psiB_phiB _ hpsi
      | copy p f k =>
        simp only [Op.node] at hn
        simp only [Dag.phase, hn]
        exact hpsi

theorem planB_cen : ∀ j, j < dagB.rootCount → planB.cen j = true →
    planB.isDef (dagB.compile.pend (.root j)) = false := by
  intro j hj hc
  by_contra hd
  obtain ⟨u, hu, he⟩ := planB_isDef (by simpa using hd)
  apply Dag.phase_deferred dagB_valid phaseHypB hu
  rw [he]
  exact centre_hit hj hc

/-- **The design-B word on arbitrary contents.** -/
theorem wordPR97B_run (c : Reg → ZMod 2) :
    Circuit.run wordPR97B c =
      c + dagB.readDelta targets (Circuit.run dagB.opsGatesB (part Reg.isX c)) :=
  dagB.wordB_run targets leafCount planB dagB_valid targets_lt
    (Dag.sideB_pairwise (Dag.phase_sorted dagB_valid phaseHypB)) planB_first planB_rest planB_cen c

/-- Readouts may be reordered without changing the source-gate schedule. -/
def planWithReadoutOrder (keyD : List ℕ) : BPlan := { planB with keyD := keyD }

def wordWithReadoutOrder (keyD : List ℕ) : Circuit.Program Reg (ZMod 2) :=
  dagB.wordB targets leafCount (planWithReadoutOrder keyD)

theorem wordWithReadoutOrder_run (keyD : List ℕ) (c : Reg → ZMod 2) :
    Circuit.run (wordWithReadoutOrder keyD) c =
      c + dagB.readDelta targets (Circuit.run dagB.opsGatesB (part Reg.isX c)) :=
  dagB.wordB_run targets leafCount (planWithReadoutOrder keyD) dagB_valid targets_lt
    (Dag.sideB_pairwise (Dag.phase_sorted dagB_valid phaseHypB)) planB_first planB_rest planB_cen c

theorem wordWithReadoutOrder_target (keyD : List ℕ) (c : Reg → ZMod 2)
    {t : ℕ} (ht : t < leafCount) :
    Circuit.run (wordWithReadoutOrder keyD) c (.y t) = c (.y t) + c (.x t) := by
  rw [wordWithReadoutOrder_run, Pi.add_apply, Dag.readDelta_y, ← roots_sum c ht]
  refine congrArg (c (.y t) + ·) (congrArg List.sum (List.map_congr_left fun j hj => ?_))
  have h := dagB.opsB_root dagB_valid c (List.mem_range.mp hj)
  rw [dagB_val] at h
  exact congrArg _ h

theorem wordWithReadoutOrder_other (keyD : List ℕ) (c : Reg → ZMod 2)
    (r : Reg) (hr : r.isY = false) :
    Circuit.run (wordWithReadoutOrder keyD) c r = c r := by
  rw [wordWithReadoutOrder_run, Pi.add_apply, Dag.readDelta_off_y _ _ _ r hr, add_zero]

theorem wordWithReadoutOrder_reverse_run (keyD : List ℕ) (c : Reg → ZMod 2) :
    Circuit.run (wordWithReadoutOrder keyD)
      (Circuit.run (wordWithReadoutOrder keyD).reverse c) = c := by
  have h := xor_run_reverse
    (Dag.wordB_xor dagB targets leafCount (planWithReadoutOrder keyD) dagB_valid).reverse c
  simpa only [wordWithReadoutOrder, List.reverse_reverse] using h

theorem wordWithReadoutOrder_reverse_other (keyD : List ℕ) (c : Reg → ZMod 2)
    (r : Reg) (hr : r.isY = false) :
    Circuit.run (wordWithReadoutOrder keyD).reverse c r = c r := by
  have h := congrFun (wordWithReadoutOrder_reverse_run keyD c) r
  rwa [wordWithReadoutOrder_other keyD _ r hr] at h

theorem wordWithReadoutOrder_reverse_target (keyD : List ℕ) (c : Reg → ZMod 2)
    {t : ℕ} (ht : t < leafCount) :
    Circuit.run (wordWithReadoutOrder keyD).reverse c (.y t) = c (.y t) + c (.x t) := by
  have h := congrFun (wordWithReadoutOrder_reverse_run keyD c) (.y t)
  rw [wordWithReadoutOrder_target keyD _ ht,
    wordWithReadoutOrder_reverse_other keyD c (.x t) rfl] at h
  calc
    _ = (Circuit.run (wordWithReadoutOrder keyD).reverse c (.y t) + c (.x t)) + c (.x t) := by
      rw [add_assoc, ← mul_two, show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero]
    _ = c (.y t) + c (.x t) := by rw [h]

/-- **The design-B word** adds every source into the target of the same triple. -/
theorem wordPR97B_target (c : Reg → ZMod 2) {t : ℕ} (ht : t < leafCount) :
    Circuit.run wordPR97B c (.y t) = c (.y t) + c (.x t) := by
  rw [wordPR97B_run, Pi.add_apply, Dag.readDelta_y, ← roots_sum c ht]
  refine congrArg (c (.y t) + ·) (congrArg List.sum (List.map_congr_left fun j hj => ?_))
  have h := dagB.opsB_root dagB_valid c (List.mem_range.mp hj)
  rw [dagB_val] at h
  exact congrArg _ h

theorem wordPR97B_other (c : Reg → ZMod 2) (r : Reg) (hr : r.isY = false) :
    Circuit.run wordPR97B c r = c r := by
  rw [wordPR97B_run, Pi.add_apply, Dag.readDelta_off_y _ _ _ r hr, add_zero]

end

end IntegerMultBounds.MathlibTM2.M8.Local
