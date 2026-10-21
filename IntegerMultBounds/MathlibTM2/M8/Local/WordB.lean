module

public import IntegerMultBounds.MathlibTM2.M8.Local.Phase
public import Mathlib.Algebra.BigOperators.Pi

/-!
# The design-B word

The design-B word reads the garbage of the side slots directly into the targets: slot `s` is
added into every target its garbage reaches through the side operations and the root reads
(`cov`, `readout`). On arbitrary contents the readouts of all slots add the garbage of the pass
(`run_readouts`), so the canonical word `RD ++ OPS ++ RR ++ OPS⁻¹` adds the root values only
(`canonB_run`).

The design-B word (`wordB`) is a reordering of it, for a plan (`BPlan`) of phases and deferred
slots:

`RDₙ ++ Vₑ ++ OPS₁ ++ CR ++ RD_d ++ V_d ++ OPS₂ ++ OR ++ (Vₑ ++ V_d ++ OPS₁ ++ OPS₂)⁻¹`.

* `RDₙ`: the readouts of the slots that are not deferred, at the start;
* `Vₑ`, `V_d`: the source gates of the slots that are not deferred, and of the deferred ones;
* `OPS₁`, `OPS₂`: the side operations of the first phase, and the others;
* `CR`, `OR`: the reads of the retained centres, and of the outputs;
* `RD_d`: the readouts of the deferred slots.

The blocks within `RDₙ`, `RD_d`, `Vₑ` and `V_d` are ordered by keys, which do not matter here.
If the first phase leaves the deferred slots alone, the second leaves the centres' slots alone,
the centres are not deferred and no side operation outside the first phase shares a slot with a
later one inside it, the word runs as the canonical word (`wordB_run`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

open Networks

namespace Dag
variable (D : Dag) (targets : ℕ → List ℕ) (nY : ℕ)

/-- The side operations as gates. -/
def sideGatesB : Circuit.Program Reg (ZMod 2) := D.sideB.map opGate

/-- The V operations as gates. -/
def opsGatesB : Circuit.Program Reg (ZMod 2) := D.opsB.map opGate

/-- The garbage coefficient of slot `s` in target `T`. -/
def cov (s T : ℕ) : ZMod 2 :=
  D.readDelta targets (Circuit.run D.sideGatesB (Pi.single (Reg.aux s) 1)) (.y T)

/-- The readout of slot `s`: into every target its garbage reaches. -/
def readout (s : ℕ) : Circuit.Program Reg (ZMod 2) :=
  ((List.range nY).filter fun T => D.cov targets s T = 1).map fun T =>
    ReversibleFanout.add (.y T) (.aux s)

/-- The readouts of a list of slots. -/
def readouts (ss : List ℕ) : Circuit.Program Reg (ZMod 2) := ss.flatMap (D.readout targets nY)

/-- The reads of a list of roots. -/
def rootReadsAt (js : List ℕ) : Circuit.Program Reg (ZMod 2) :=
  js.flatMap fun j => (targets j).map fun T => ReversibleFanout.add (.y T) (.aux (D.compile.pend (.root j)))

/-- The canonical word: all readouts, the V operations, the root reads and the uncompute. -/
def canonB : Circuit.Program Reg (ZMod 2) :=
  D.readouts targets nY (List.range D.compile.next) ++ D.opsGatesB ++ D.rootReads targets ++
    D.opsGatesB.reverse

end Dag

/-- A plan of the design-B word: the phases of the side operations, the centres, the deferred
slots and the keys ordering the readout and source blocks. -/
structure BPlan where
  Φ : ℕ → Bool
  Ψ : ℕ → Bool
  cen : ℕ → Bool
  defS : List ℕ
  keyD : List ℕ
  keyE : List ℕ
  keyV : List ℕ

/-- Order slots by their positions in a key. -/
def keyed (key ss : List ℕ) : List ℕ := ss.mergeSort fun a b => decide (key.idxOf a ≤ key.idxOf b)

/-- Order operations by the positions of their targets in a key. -/
def keyedOps (key : List ℕ) (ops : List Op) : List Op :=
  ops.mergeSort fun a b => decide (key.idxOf a.target ≤ key.idxOf b.target)

/-- The deferred slots. -/
def BPlan.isDef (pl : BPlan) (s : ℕ) : Bool := decide (s ∈ pl.defS)

namespace Dag
variable (D : Dag) (targets : ℕ → List ℕ) (nY : ℕ) (pl : BPlan)

/-- The readouts of the slots that are not deferred. -/
def rdNow : Circuit.Program Reg (ZMod 2) :=
  D.readouts targets nY ((List.range D.compile.next).filter fun s => !pl.isDef s)

/-- The readouts of the deferred slots, in key order. -/
def rdLate : Circuit.Program Reg (ZMod 2) :=
  D.readouts targets nY (keyed pl.keyD ((List.range D.compile.next).filter pl.isDef))

/-- The source gates of the slots that are not deferred. -/
def vNow : List Op := keyedOps pl.keyE (D.srcB.filter fun op => !pl.isDef op.target)

/-- The source gates of the deferred slots. -/
def vLate : List Op := keyedOps pl.keyV (D.srcB.filter fun op => pl.isDef op.target)

/-- The side operations of the first phase. -/
def opsFirst : List Op := D.sideB.filter (phase pl.Φ pl.Ψ)

/-- The other side operations. -/
def opsRest : List Op := D.sideB.filter fun op => !phase pl.Φ pl.Ψ op

/-- The reads of the retained centres. -/
def centreReads : Circuit.Program Reg (ZMod 2) :=
  D.rootReadsAt targets ((List.range D.rootCount).filter pl.cen)

/-- The reads of the outputs. -/
def outReads : Circuit.Program Reg (ZMod 2) :=
  D.rootReadsAt targets ((List.range D.rootCount).filter fun j => !pl.cen j)

/-- **The design-B word.** -/
def wordB : Circuit.Program Reg (ZMod 2) :=
  D.rdNow targets nY pl ++ (D.vNow pl).map opGate ++ (D.opsFirst pl).map opGate ++
    D.centreReads targets pl ++ D.rdLate targets nY pl ++ (D.vLate pl).map opGate ++
    (D.opsRest pl).map opGate ++ D.outReads targets pl ++
    ((D.vNow pl ++ D.vLate pl ++ D.opsFirst pl ++ D.opsRest pl).map opGate).reverse

end Dag

/-! ### Gates of operations and reads -/

theorem opGate_target_side {o : Op} (ho : o.isSrc = false) :
    ∃ s ∈ o.slots, (opGate o).target = .aux s := by
  cases o with
  | src => simp [Op.isSrc] at ho
  | add p q k => exact ⟨p, by simp [Op.slots], rfl⟩
  | copy p f k => exact ⟨f, by simp [Op.slots], rfl⟩

theorem opGate_terms_side {o : Op} (ho : o.isSrc = false) :
    ∀ t ∈ (opGate o).terms, ∃ s ∈ o.slots, t.1 = .aux s := by
  cases o with
  | src => simp [Op.isSrc] at ho
  | add p q k =>
    intro t ht
    simp only [opGate, ReversibleFanout.add, List.mem_singleton] at ht
    exact ⟨q, by simp [Op.slots], by rw [ht]⟩
  | copy p f k =>
    intro t ht
    simp only [opGate, ReversibleFanout.add, List.mem_singleton] at ht
    exact ⟨p, by simp [Op.slots], by rw [ht]⟩

theorem opGate_src {o : Op} (ho : o.isSrc = true) :
    ∃ s n, o = .src s n ∧ opGate o = ReversibleFanout.add (.aux s) (.x n) := by
  cases o with
  | src s n => exact ⟨s, n, rfl, rfl⟩
  | _ => simp [Op.isSrc] at ho

/-- A read gate: some target receives some side slot. -/
def IsRead (g : Circuit.Gate Reg (ZMod 2)) : Prop := ∃ T s, g = ReversibleFanout.add (.y T) (.aux s)

theorem read_commute {g h : Circuit.Gate Reg (ZMod 2)} (hg : IsRead g) (hh : IsRead h) :
    GateCommute g h := by
  obtain ⟨T, s, rfl⟩ := hg
  obtain ⟨T', s', rfl⟩ := hh
  exact add_commute (by simp) (by simp)

/-- A read of slot `s` commutes with a side operation not touching `s`. -/
theorem read_commute_side {T s : ℕ} {o : Op} (ho : o.isSrc = false) (hs : s ∉ o.slots) :
    GateCommute (ReversibleFanout.add (.y T) (.aux s)) (opGate o) := by
  obtain ⟨p, hp, ht⟩ := opGate_target_side ho
  refine ⟨fun t ht' => ?_, fun t ht' => ?_⟩
  · obtain ⟨q, -, hq⟩ := opGate_terms_side ho t ht'
    rw [hq]; simp [ReversibleFanout.add]
  · simp only [ReversibleFanout.add, List.mem_singleton] at ht'
    rw [ht', ht]
    simp only [ne_eq, Reg.aux.injEq]
    exact fun h => hs (h ▸ hp)

/-- A read commutes with a source gate on another slot. -/
theorem read_commute_src {T s : ℕ} {o : Op} (ho : o.isSrc = true) (hs : o.target ≠ s) :
    GateCommute (ReversibleFanout.add (.y T) (.aux s)) (opGate o) := by
  obtain ⟨f, n, rfl, he⟩ := opGate_src ho
  rw [he]
  refine add_commute (by simp) ?_
  simp only [Op.target] at hs
  simpa using Ne.symm hs

/-- A source gate commutes with a side operation not touching its slot. -/
theorem src_commute_side {o o' : Op} (ho : o.isSrc = true) (ho' : o'.isSrc = false)
    (hs : o.target ∉ o'.slots) : GateCommute (opGate o) (opGate o') := by
  obtain ⟨f, n, rfl, he⟩ := opGate_src ho
  rw [he]
  obtain ⟨p, hp, ht⟩ := opGate_target_side ho'
  refine ⟨fun t ht' => ?_, fun t ht' => ?_⟩
  · obtain ⟨q, hq, hq'⟩ := opGate_terms_side ho' t ht'
    rw [hq']
    simp only [ReversibleFanout.add, ne_eq, Reg.aux.injEq]
    exact fun h => hs (h ▸ hq)
  · simp only [ReversibleFanout.add, List.mem_singleton] at ht'
    rw [ht', ht]
    simp

theorem src_commute_src {o o' : Op} (ho : o.isSrc = true) (ho' : o'.isSrc = true) :
    GateCommute (opGate o) (opGate o') := by
  obtain ⟨f, n, rfl, he⟩ := opGate_src ho
  obtain ⟨f', n', rfl, he'⟩ := opGate_src ho'
  rw [he, he']
  exact add_commute (by simp) (by simp)

/-- Side operations with disjoint slots commute. -/
theorem side_commute_side {o o' : Op} (ho : o.isSrc = false) (ho' : o'.isSrc = false)
    (hs : ∀ s ∈ o'.slots, s ∉ o.slots) : GateCommute (opGate o) (opGate o') := by
  obtain ⟨p, hp, ht⟩ := opGate_target_side ho
  obtain ⟨p', hp', ht'⟩ := opGate_target_side ho'
  refine ⟨fun t htm => ?_, fun t htm => ?_⟩
  · obtain ⟨q, hq, hq'⟩ := opGate_terms_side ho' t htm
    rw [hq', ht]
    simp only [ne_eq, Reg.aux.injEq]
    exact fun h => hs q hq (h ▸ hp)
  · obtain ⟨q, hq, hq'⟩ := opGate_terms_side ho t htm
    rw [hq', ht']
    simp only [ne_eq, Reg.aux.injEq]
    exact fun h => hs p' hp' (h ▸ hq)

theorem isRead_readouts (D : Dag) (targets : ℕ → List ℕ) (nY : ℕ) (ss : List ℕ) :
    ∀ g ∈ D.readouts targets nY ss, IsRead g := by
  intro g hg
  simp only [Dag.readouts, Dag.readout, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨s, -, T, -, rfl⟩ := hg
  exact ⟨T, s, rfl⟩

theorem isRead_rootReadsAt (D : Dag) (targets : ℕ → List ℕ) (js : List ℕ) :
    ∀ g ∈ D.rootReadsAt targets js, IsRead g := by
  intro g hg
  simp only [Dag.rootReadsAt, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨j, -, T, -, rfl⟩ := hg
  exact ⟨T, _, rfl⟩

/-! ### The readouts of all slots -/

namespace Dag
variable (D : Dag) (targets : ℕ → List ℕ) (nY : ℕ)

theorem readouts_untouched (ss : List ℕ) : ReadsUntouched (D.readouts targets nY ss) := by
  intro g hg g' hg' t ht
  obtain ⟨T, s, rfl⟩ := isRead_readouts D targets nY ss g hg
  obtain ⟨T', s', rfl⟩ := isRead_readouts D targets nY ss g' hg'
  simp only [ReversibleFanout.add, List.mem_singleton] at ht
  rw [ht]
  simp [ReversibleFanout.add]

theorem readouts_xor (ss : List ℕ) : IsXorProg (D.readouts targets nY ss) := by
  intro g hg
  obtain ⟨T, s, rfl⟩ := isRead_readouts D targets nY ss g hg
  exact ⟨_, _, by simp, rfl⟩

theorem sideGatesB_xor (hv : D.Valid) : IsXorProg D.sideGatesB := by
  intro g hg
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hg
  exact opGate_xor (D.opsB_ok hv op (List.mem_filter.mp hop).1).1

theorem opsGatesB_xor (hv : D.Valid) : IsXorProg D.opsGatesB := by
  intro g hg
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hg
  exact opGate_xor (D.opsB_ok hv op hop).1

/-- An XOR program maps zero to zero. -/
theorem xor_run_zero {p : Circuit.Program Reg (ZMod 2)} (hp : IsXorProg p) :
    Circuit.run p 0 = 0 := by
  have h := xor_run_add hp 0 0
  rw [add_zero] at h
  have : Circuit.run p 0 + Circuit.run p 0 = 0 := by
    funext r; simp only [Pi.add_apply, Pi.zero_apply]
    generalize Circuit.run p 0 r = a
    revert a; decide
  rw [← h] at this
  exact this

/-- An XOR program on a sum over slots. -/
theorem xor_run_sum {p : Circuit.Program Reg (ZMod 2)} (hp : IsXorProg p) (f : ℕ → Reg → ZMod 2) :
    ∀ n, Circuit.run p (∑ s ∈ Finset.range n, f s) = ∑ s ∈ Finset.range n, Circuit.run p (f s)
  | 0 => by simp [xor_run_zero hp]
  | n + 1 => by rw [Finset.sum_range_succ, xor_run_add hp, xor_run_sum hp f n, Finset.sum_range_succ]

theorem readDelta_sum (f : ℕ → Reg → ZMod 2) :
    ∀ n, D.readDelta targets (∑ s ∈ Finset.range n, f s) =
      ∑ s ∈ Finset.range n, D.readDelta targets (f s)
  | 0 => by simp [readDelta_zero]
  | n + 1 => by rw [Finset.sum_range_succ, readDelta_add, readDelta_sum f n, Finset.sum_range_succ]

theorem sideB_slots (hv : D.Valid) : ∀ op ∈ D.sideB, op.SlotsLt D.compile.next :=
  fun op hop => (D.opsB_ok hv op (List.mem_filter.mp hop).1).2

theorem sideB_isSrc : ∀ op ∈ D.sideB, op.isSrc = false := fun op hop => by
  simpa using (List.mem_filter.mp hop).2

/-- Contents vanishing on the slots below `next` pass the side gates and give no reads. -/
theorem high_slots (hv : D.Valid) {d : Reg → ZMod 2}
    (hd : ∀ s, s < D.compile.next → d (.aux s) = 0) :
    Circuit.run D.sideGatesB d = d ∧ D.readDelta targets d = 0 := by
  have hlt : ∀ op ∈ D.sideB, ∀ s ∈ op.slots, s < D.compile.next := by
    intro op hop s hs
    have h := D.sideB_slots hv op hop
    cases op <;> simp_all [Op.SlotsLt, Op.slots] <;> omega
  refine ⟨run_silent _ d fun g hg => ?_, ?_⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hg
    have hs := D.sideB_isSrc op hop
    obtain ⟨p, hp, ht⟩ := opGate_target_side hs
    refine ⟨by rw [ht]; exact hd p (hlt op hop p hp), fun t ht' => ?_⟩
    obtain ⟨q, hq, hq'⟩ := opGate_terms_side hs t ht'
    rw [hq']; exact hd q (hlt op hop q hq)
  · funext r
    cases r with
    | y T =>
      rw [readDelta_y]
      simp only [Pi.zero_apply]
      apply List.sum_eq_zero
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      rw [hd _ (D.root_slot_lt hv (List.mem_range.mp hj)), mul_zero]
    | x n => rfl
    | aux s => rfl

/-- A single slot through the side gates: its garbage coefficients. -/
theorem readDelta_single (hv : D.Valid) (s : ℕ) (b : ZMod 2) (T : ℕ) :
    D.readDelta targets (Circuit.run D.sideGatesB (Pi.single (Reg.aux s) b)) (.y T) =
      b * D.cov targets s T := by
  have hb : b = 0 ∨ b = 1 := (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b
  rcases hb with rfl | rfl
  · rw [Pi.single_zero, zero_mul, xor_run_zero (D.sideGatesB_xor hv), readDelta_zero]
    rfl
  · rw [one_mul]; rfl

/-- The coefficients vanish off the targets of the roots. -/
theorem cov_eq_zero (hT : ∀ j T, T ∈ targets j → T < nY) (s T : ℕ) (h : nY ≤ T) :
    D.cov targets s T = 0 := by
  rw [cov, readDelta_y]
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
  rw [List.count_eq_zero_of_not_mem (fun hm => by have := hT j T hm; omega), Nat.cast_zero,
    zero_mul]

theorem ite_one (a : ZMod 2) : (if a = 1 then (1 : ZMod 2) else 0) = a := by
  revert a; decide

/-- The side-slot contents from slot `n` on. -/
def restAux (c : Reg → ZMod 2) (n : ℕ) : Reg → ZMod 2
  | .aux s => if n ≤ s then c (.aux s) else 0
  | _ => 0

theorem part_aux_split (c : Reg → ZMod 2) (n : ℕ) :
    part Reg.isAux c = (∑ s ∈ Finset.range n, Pi.single (Reg.aux s) (c (.aux s))) +
      restAux c n := by
  funext r
  rw [Pi.add_apply, Finset.sum_apply]
  cases r with
  | x m => simp [part, Reg.isAux, restAux]
  | y T => simp [part, Reg.isAux, restAux]
  | aux s =>
    simp only [part, Reg.isAux, ite_true, Pi.single_apply, Reg.aux.injEq, restAux]
    rw [Finset.sum_ite_eq (Finset.range n) s fun s => c (.aux s)]
    by_cases h : n ≤ s
    · simp [Finset.mem_range, h, Nat.not_lt.mpr h]
    · simp [Finset.mem_range, h, Nat.lt_of_not_le h]

theorem list_sum_range' (f : ℕ → ZMod 2) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- **The readouts of all slots** add the garbage of the side gates and the root reads. -/
theorem run_readouts (hv : D.Valid) (hT : ∀ j T, T ∈ targets j → T < nY) (c : Reg → ZMod 2) :
    Circuit.run (D.readouts targets nY (List.range D.compile.next)) c =
      c + D.readDelta targets (Circuit.run D.sideGatesB (part Reg.isAux c)) := by
  funext r
  rw [run_readsUntouched _ (D.readouts_untouched targets nY _), Pi.add_apply]
  congr 1
  cases r with
  | x m =>
    rw [D.readDelta_off_y targets _ _ rfl]
    exact contrib_not_target _ c _ fun g hg h => by
      obtain ⟨T, s, rfl⟩ := isRead_readouts D targets nY _ g hg
      simp [ReversibleFanout.add] at h
  | aux s' =>
    rw [D.readDelta_off_y targets _ _ rfl]
    exact contrib_not_target _ c _ fun g hg h => by
      obtain ⟨T, s, rfl⟩ := isRead_readouts D targets nY _ g hg
      simp [ReversibleFanout.add] at h
  | y T =>
    -- the right side: one coefficient per slot below `next`
    set n := D.compile.next
    obtain ⟨hrun, hdel⟩ := D.high_slots targets hv
      (d := restAux c n)
      (fun s hs => by simp [restAux, show ¬ n ≤ s by omega])
    rw [part_aux_split c n, xor_run_add (D.sideGatesB_xor hv), hrun, readDelta_add, hdel,
      add_zero, xor_run_sum (D.sideGatesB_xor hv), readDelta_sum, Finset.sum_apply]
    simp_rw [D.readDelta_single targets hv]
    -- the left side: the readouts, slot by slot
    unfold readouts
    rw [contrib_flatMap, list_sum_range']
    apply Finset.sum_congr rfl
    intro s _
    unfold readout
    rw [contrib_reads, mul_comm]
    congr 1
    by_cases hTn : T < nY
    · by_cases hc : D.cov targets s T = 1
      · rw [List.count_filter (by simpa using hc),
          List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr hTn), hc]
        simp
      · rw [List.count_eq_zero_of_not_mem (by simp [hc])]
        have : D.cov targets s T = 0 :=
          (by decide : ∀ a : ZMod 2, ¬ a = 1 → a = 0) _ hc
        simp [this]
    · rw [List.count_eq_zero_of_not_mem (by simp [hTn]),
        D.cov_eq_zero targets nY hT s T (Nat.le_of_not_lt hTn)]
      simp

/-! ### The canonical word -/

/-- Operations never touch the targets. -/
theorem ops_yOnly (L : List Op) {d : Reg → ZMod 2} (hd : YOnly d) :
    Circuit.run (L.map opGate) d = d := by
  refine run_silent _ d fun g hg => ?_
  obtain ⟨op, -, rfl⟩ := List.mem_map.mp hg
  refine ⟨hd _ (by have := opGate_target op; revert this; cases (opGate op).target <;>
    simp [Reg.isY, Reg.isAux]), fun t ht => hd _ (opGate_terms op t ht)⟩

theorem ops_reverse_yOnly (L : List Op) {d : Reg → ZMod 2} (hd : YOnly d) :
    Circuit.run (L.map opGate).reverse d = d := by
  refine run_silent _ d fun g hg => ?_
  obtain ⟨op, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hg)
  refine ⟨hd _ (by have := opGate_target op; revert this; cases (opGate op).target <;>
    simp [Reg.isY, Reg.isAux]), fun t ht => hd _ (opGate_terms op t ht)⟩

theorem sideGatesB_aux_free {d : Reg → ZMod 2} (hd : ∀ r, r.isAux = true → d r = 0) :
    Circuit.run D.sideGatesB d = d := by
  refine run_silent _ d fun g hg => ?_
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hg
  exact ⟨hd _ (opGate_target op), fun t ht => hd _ (side_terms (D.sideB_isSrc op hop) t ht)⟩

/-- **The canonical word** adds the root values on the sources. -/
theorem canonB_run (hv : D.Valid) (hT : ∀ j T, T ∈ targets j → T < nY) (c : Reg → ZMod 2) :
    Circuit.run (D.canonB targets nY) c =
      c + D.readDelta targets (Circuit.run D.opsGatesB (part Reg.isX c)) := by
  have hB := D.opsGatesB_xor hv
  have hA := D.sideGatesB_xor hv
  set δ1 := D.readDelta targets (Circuit.run D.sideGatesB (part Reg.isAux c))
  have hδ1 : YOnly δ1 := D.readDelta_yOnly targets _
  have hδδ : ∀ d, D.readDelta targets (D.readDelta targets d) = 0 := fun d =>
    D.readDelta_aux_free targets (yOnly_aux_free (D.readDelta_yOnly targets d))
  have h2 : Circuit.run D.opsGatesB (c + δ1) = Circuit.run D.opsGatesB c + δ1 := by
    rw [xor_run_add hB]
    exact congrArg _ (ops_yOnly D.opsB hδ1)
  have h3 : Circuit.run (D.rootReads targets) (Circuit.run D.opsGatesB c + δ1) =
      Circuit.run D.opsGatesB c + (δ1 + D.readDelta targets (Circuit.run D.opsGatesB c)) := by
    rw [run_rootReads, D.readDelta_add, hδδ, add_zero]
    abel
  have hsum : YOnly (δ1 + D.readDelta targets (Circuit.run D.opsGatesB c)) :=
    hδ1.add (D.readDelta_yOnly _ _)
  have h4 : Circuit.run D.opsGatesB.reverse (Circuit.run D.opsGatesB c +
      (δ1 + D.readDelta targets (Circuit.run D.opsGatesB c))) =
      c + (δ1 + D.readDelta targets (Circuit.run D.opsGatesB c)) := by
    rw [xor_run_add hB.reverse, xor_run_reverse hB]
    exact congrArg _ (ops_reverse_yOnly D.opsB hsum)
  -- the garbage of the pass is the garbage of the readouts
  have hkey : D.readDelta targets (Circuit.run D.opsGatesB c) =
      D.readDelta targets (Circuit.run D.opsGatesB (part Reg.isX c)) + δ1 := by
    have hc : c = part Reg.isX c + (part Reg.isY c + part Reg.isAux c) := by
      rw [← add_assoc]; exact part_split c
    have hsrc : Circuit.run D.opsGatesB (part Reg.isY c + part Reg.isAux c) =
        Circuit.run D.sideGatesB (part Reg.isY c + part Reg.isAux c) :=
      run_ops_srcfree _ _ (part_rest_x c)
    have hy : ∀ r, r.isAux = true → part Reg.isY c r = 0 := fun r hr => by
      cases r with
      | aux s => simp [part, Reg.isY]
      | _ => simp [Reg.isAux] at hr
    conv_lhs => rw [hc]
    rw [xor_run_add hB, hsrc, xor_run_add hA, D.sideGatesB_aux_free hy, D.readDelta_add,
      D.readDelta_add, D.readDelta_aux_free targets hy, zero_add]
  simp only [canonB, Circuit.run_append]
  rw [D.run_readouts targets nY hv hT, h2, h3, h4, hkey]
  congr 1
  funext r
  simp only [Pi.add_apply]
  generalize δ1 r = a
  generalize D.readDelta targets (Circuit.run D.opsGatesB (part Reg.isX c)) r = b
  revert a b
  decide

/-! ### The design-B word -/

variable (pl : BPlan)

theorem swap_apply {p q : Circuit.Program Reg (ZMod 2)} (h : ∀ g ∈ p, ∀ h ∈ q, GateCommute g h)
    (c : Reg → ZMod 2) : Circuit.run q (Circuit.run p c) = Circuit.run p (Circuit.run q c) := by
  have := congrFun (run_append_comm h) c
  simpa only [Circuit.run_append] using this

theorem mem_rdLate {g : Circuit.Gate Reg (ZMod 2)} (hg : g ∈ D.rdLate targets nY pl) :
    ∃ T s, g = ReversibleFanout.add (.y T) (.aux s) ∧ pl.isDef s = true := by
  simp only [rdLate, readouts, readout, keyed, List.mem_flatMap, List.mem_mergeSort,
    List.mem_filter, List.mem_map] at hg
  obtain ⟨s, ⟨-, hs⟩, T, -, rfl⟩ := hg
  exact ⟨T, s, rfl, hs⟩

theorem mem_centreReads {g : Circuit.Gate Reg (ZMod 2)} (hg : g ∈ D.centreReads targets pl) :
    ∃ T j, g = ReversibleFanout.add (.y T) (.aux (D.compile.pend (.root j))) ∧
      j < D.rootCount ∧ pl.cen j = true := by
  simp only [centreReads, rootReadsAt, List.mem_flatMap, List.mem_filter, List.mem_range,
    List.mem_map] at hg
  obtain ⟨j, ⟨hj, hc⟩, T, -, rfl⟩ := hg
  exact ⟨T, j, rfl, hj, hc⟩

theorem mem_vNow {o : Op} (ho : o ∈ D.vNow pl) : o.isSrc = true ∧ pl.isDef o.target = false := by
  simp only [vNow, keyedOps, List.mem_mergeSort, List.mem_filter, srcB] at ho
  exact ⟨ho.1.2, by simpa using ho.2⟩

theorem mem_vLate {o : Op} (ho : o ∈ D.vLate pl) : o.isSrc = true ∧ pl.isDef o.target = true := by
  simp only [vLate, keyedOps, List.mem_mergeSort, List.mem_filter, srcB] at ho
  exact ⟨ho.1.2, ho.2⟩

theorem mem_opsFirst {o : Op} (ho : o ∈ D.opsFirst pl) :
    o ∈ D.sideB ∧ phase pl.Φ pl.Ψ o = true := List.mem_filter.mp ho

theorem mem_opsRest {o : Op} (ho : o ∈ D.opsRest pl) :
    o ∈ D.sideB ∧ phase pl.Φ pl.Ψ o = false := by
  have := List.mem_filter.mp ho
  exact ⟨this.1, by simpa using this.2⟩

/-- **The design-B word on arbitrary contents.** Under the plan's conditions it adds the root
values on the sources and leaves the rest. -/
theorem wordB_run (hv : D.Valid) (hT : ∀ j T, T ∈ targets j → T < nY)
    (hsplit : D.sideB.Pairwise fun o o' => phase pl.Φ pl.Ψ o = false →
      phase pl.Φ pl.Ψ o' = true → ∀ s ∈ o'.slots, s ∉ o.slots)
    (hfirst : ∀ op ∈ D.sideB, phase pl.Φ pl.Ψ op = true → ∀ s ∈ op.slots, pl.isDef s = false)
    (hrest : ∀ op ∈ D.sideB, phase pl.Φ pl.Ψ op = false → ∀ j, j < D.rootCount →
      pl.cen j = true → D.compile.pend (.root j) ∉ op.slots)
    (hcen : ∀ j, j < D.rootCount → pl.cen j = true → pl.isDef (D.compile.pend (.root j)) = false)
    (c : Reg → ZMod 2) :
    Circuit.run (D.wordB targets nY pl) c =
      c + D.readDelta targets (Circuit.run D.opsGatesB (part Reg.isX c)) := by
  set A := D.rdNow targets nY pl
  set B := D.rdLate targets nY pl
  set C := D.centreReads targets pl
  set O := D.outReads targets pl
  set Ve := (D.vNow pl).map opGate
  set Vl := (D.vLate pl).map opGate
  set F := (D.opsFirst pl).map opGate
  set Rs := (D.opsRest pl).map opGate
  -- the swaps
  have hBC : ∀ t, Circuit.run B (Circuit.run C t) = Circuit.run C (Circuit.run B t) :=
    swap_apply fun g hg h hh => read_commute (isRead_rootReadsAt D targets _ g hg)
      (isRead_readouts D targets nY _ h hh)
  have hVlC : ∀ t, Circuit.run Vl (Circuit.run C t) = Circuit.run C (Circuit.run Vl t) := by
    refine swap_apply fun g hg h hh => ?_
    obtain ⟨T, j, rfl, hj, hc⟩ := D.mem_centreReads targets pl hg
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hh
    obtain ⟨hs, hd⟩ := D.mem_vLate pl ho
    exact read_commute_src hs fun he => by rw [he, hcen j hj hc] at hd; cases hd
  have hRsC : ∀ t, Circuit.run Rs (Circuit.run C t) = Circuit.run C (Circuit.run Rs t) := by
    refine swap_apply fun g hg h hh => ?_
    obtain ⟨T, j, rfl, hj, hc⟩ := D.mem_centreReads targets pl hg
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hh
    obtain ⟨hs, hph⟩ := D.mem_opsRest pl ho
    exact read_commute_side (D.sideB_isSrc o hs) (hrest o hs hph j hj hc)
  have hBF : ∀ t, Circuit.run B (Circuit.run F t) = Circuit.run F (Circuit.run B t) := by
    refine swap_apply fun g hg h hh => ?_
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hg
    obtain ⟨T, s, rfl, hd⟩ := D.mem_rdLate targets nY pl hh
    obtain ⟨hs, hph⟩ := D.mem_opsFirst pl ho
    exact (read_commute_side (D.sideB_isSrc o hs) fun hm => by
      rw [hfirst o hs hph s hm] at hd; cases hd).symm
  have hVlF : ∀ t, Circuit.run Vl (Circuit.run F t) = Circuit.run F (Circuit.run Vl t) := by
    refine swap_apply fun g hg h hh => ?_
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hg
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hh
    obtain ⟨hs, hph⟩ := D.mem_opsFirst pl ho
    obtain ⟨hs', hd⟩ := D.mem_vLate pl ho'
    exact (src_commute_side hs' (D.sideB_isSrc o hs) fun hm => by
      rw [hfirst o hs hph _ hm] at hd; cases hd).symm
  have hBVe : ∀ t, Circuit.run B (Circuit.run Ve t) = Circuit.run Ve (Circuit.run B t) := by
    refine swap_apply fun g hg h hh => ?_
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hg
    obtain ⟨T, s, rfl, hd⟩ := D.mem_rdLate targets nY pl hh
    obtain ⟨hs, hd'⟩ := D.mem_vNow pl ho
    exact (read_commute_src hs fun he => by rw [he, hd] at hd'; cases hd').symm
  -- the blocks
  have hAB : ∀ t, Circuit.run B (Circuit.run A t) =
      Circuit.run (D.readouts targets nY (List.range D.compile.next)) t := by
    intro t
    have hp : (A ++ B).Perm (D.readouts targets nY (List.range D.compile.next)) := by
      simp only [A, B, rdNow, rdLate, readouts, ← List.flatMap_append]
      refine List.Perm.flatMap_right _ ?_
      refine ((List.Perm.append_left _ (List.mergeSort_perm _ _)).trans ?_)
      exact (List.perm_append_comm.trans (List.filter_append_perm _ _))
    have := congrFun (run_perm hp fun g hg h hh => read_commute
      (isRead_readouts D targets nY _ g (hp.subset hg)) (isRead_readouts D targets nY _ h (hp.subset hh))) t
    simpa only [Circuit.run_append] using this
  have hVL : Circuit.run (Ve ++ Vl ++ F ++ Rs) = Circuit.run D.opsGatesB := by
    have hV : Circuit.run (Ve ++ Vl) = Circuit.run (D.srcB.map opGate) := by
      have hp : (Ve ++ Vl).Perm (D.srcB.map opGate) := by
        simp only [Ve, Vl, vNow, vLate, keyedOps, ← List.map_append]
        refine List.Perm.map _ ?_
        refine (List.Perm.append (List.mergeSort_perm _ _) (List.mergeSort_perm _ _)).trans ?_
        exact List.perm_append_comm.trans (List.filter_append_perm _ _)
      refine run_perm hp fun g hg h hh => ?_
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (hp.subset hg)
      obtain ⟨o', ho', rfl⟩ := List.mem_map.mp (hp.subset hh)
      exact src_commute_src (List.mem_filter.mp ho).2 (List.mem_filter.mp ho').2
    have hL : Circuit.run (F ++ Rs) = Circuit.run D.sideGatesB := by
      refine (run_split opGate (phase pl.Φ pl.Ψ) ?_).symm
      refine List.Pairwise.imp_of_mem ?_ hsplit
      intro o o' ho ho' h h1 h2
      exact side_commute_side (D.sideB_isSrc o ho) (D.sideB_isSrc o' ho') (h h1 h2)
    have e : Ve ++ Vl ++ F ++ Rs = (Ve ++ Vl) ++ (F ++ Rs) := by simp
    funext t
    rw [e, Circuit.run_append, hV, hL, opsGatesB, D.run_opsB_front hv, Circuit.run_append]
    rfl
  have hCO : ∀ t, Circuit.run O (Circuit.run C t) = Circuit.run (D.rootReads targets) t := by
    intro t
    have hp : (C ++ O).Perm (D.rootReads targets) := by
      simp only [C, O, centreReads, outReads, rootReadsAt, ← List.flatMap_append]
      exact List.Perm.flatMap_right _ (List.filter_append_perm _ _)
    have hr : ∀ g ∈ C ++ O, IsRead g := fun g hg => by
      rcases List.mem_append.mp hg with h | h
      · exact isRead_rootReadsAt D targets _ g h
      · exact isRead_rootReadsAt D targets _ g h
    have := congrFun (run_perm hp fun g hg h hh => read_commute (hr g hg) (hr h hh)) t
    simpa only [Circuit.run_append] using this
  have hrev : Circuit.run (Ve ++ Vl ++ F ++ Rs).reverse = Circuit.run D.opsGatesB.reverse := by
    have hx : IsXorProg (Ve ++ Vl ++ F ++ Rs) := by
      intro g hg
      simp only [Ve, Vl, F, Rs, ← List.map_append, List.mem_map] at hg
      obtain ⟨o, ho, rfl⟩ := hg
      refine opGate_xor ?_
      simp only [List.mem_append] at ho
      rcases ho with ((ho | ho) | ho) | ho
      · exact (D.opsB_ok hv o (List.mem_filter.mp
          (List.mem_filter.mp (List.mem_mergeSort.mp ho)).1).1).1
      · exact (D.opsB_ok hv o (List.mem_filter.mp
          (List.mem_filter.mp (List.mem_mergeSort.mp ho)).1).1).1
      · exact (D.opsB_ok hv o (List.mem_filter.mp (List.mem_filter.mp ho).1).1).1
      · exact (D.opsB_ok hv o (List.mem_filter.mp (List.mem_filter.mp ho).1).1).1
    exact run_reverse_congr hx (D.opsGatesB_xor hv) hVL
  -- the reordering
  have hw : Circuit.run (D.wordB targets nY pl) c = Circuit.run (D.canonB targets nY) c := by
    simp only [wordB, canonB, Circuit.run_append]
    rw [show ((D.vNow pl ++ D.vLate pl ++ D.opsFirst pl ++ D.opsRest pl).map opGate).reverse =
      (Ve ++ Vl ++ F ++ Rs).reverse by simp [Ve, Vl, F, Rs]]
    rw [hBC, hVlC, hRsC, hBF, hVlF, hBVe, hAB, hCO, hrev]
    have := congrFun hVL (Circuit.run (D.readouts targets nY (List.range D.compile.next)) c)
    simp only [Circuit.run_append] at this
    rw [this]
  rw [hw, D.canonB_run targets nY hv hT]

end Dag

end IntegerMultBounds.MathlibTM2.M8.Local
