module

public import IntegerMultBounds.MathlibTM2.M8.Global.StageFrames
public import IntegerMultBounds.MathlibTM2.M8.Global.Cost
public import IntegerMultBounds.MathlibTM2.M8.Global.Map

/-!
# The PR97 node

The node's contract roles are the data pairs `X S T` and `Y S T`, for triples `S` and `T`, and
the side slots of the two stages' invocations; its temporaries are one per centre and
invocation of each stage, one per data pair for the correction, and one unused wire (`World`,
`Temp`). The framed gate list (`allGates`) runs:
* stage one, invocation `T`: the first local stage on the sources `X ⋅ T` and targets `Y ⋅ T`, its
  frames lifted to `K ⊗ Q_T` (`gates1`);
* stage two, invocation `S`: the second local stage on the sources `Y S ⋅` and targets `X S ⋅`,
  its frames lifted to `(1 − P_S) ⊗ 1 + P_S ⊗ K` (`gates2`);
* the correction of each pair: a fresh temporary copies `X S T` at frame `1` and adds into
  `Y S T` at frame `1 − P_S ⊗ Q_T` (`corrGates`).

The data `X S T` starts in the frame `P_S ⊗ Q_T`; every other wire starts at `0`, and each
temporary in the frame its first gate needs (`gInit`). The side slots end with a move to frame
`1` (`sinks`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- The triples, as leaves. -/
abbrev V := Fin leafCount

/-- The side slots of an invocation. -/
abbrev Slot := Fin dag.compile.next

/-- The contract roles: `X S T`, `Y S T`, and the side slots of each stage and invocation. -/
abbrev World := (V × V) ⊕ (V × V) ⊕ (Bool × V × Slot)

/-- The temporaries: one per stage, invocation and centre; one per pair; one unused. -/
abbrev Temp := (Bool × V × Fin 23) ⊕ (V × V) ⊕ Unit

abbrev Wire := World ⊕ Temp

def wX (S T : V) : Wire := .inl (.inl (S, T))
def wY (S T : V) : Wire := .inl (.inr (.inl (S, T)))
def wSide (b : Bool) (k : V) (s : Slot) : Wire := .inl (.inr (.inr (b, k, s)))
def wCentre (b : Bool) (k : V) (c : Fin 23) : Wire := .inr (.inl (b, k, c))
def wCorr (S T : V) : Wire := .inr (.inr (.inl (S, T)))
def wJunk : Wire := .inr (.inr (.inr ()))

/-- Stage one, invocation `T`. -/
def place1 (T : V) : LW → Wire
  | .inl (.x n) => if h : n < leafCount then wX ⟨n, h⟩ T else wJunk
  | .inl (.y t) => if h : t < leafCount then wY ⟨t, h⟩ T else wJunk
  | .inl (.aux s) => if h : s < dag.compile.next then wSide false T ⟨s, h⟩ else wJunk
  | .inr c => wCentre false T c

/-- Stage two, invocation `S`: the banks exchanged. -/
def place2 (S : V) : LW → Wire
  | .inl (.x n) => if h : n < leafCount then wY S ⟨n, h⟩ else wJunk
  | .inl (.y t) => if h : t < leafCount then wX S ⟨t, h⟩ else wJunk
  | .inl (.aux s) => if h : s < dag.compile.next then wSide true S ⟨s, h⟩ else wJunk
  | .inr c => wCentre true S c

/-- The line of a triple, on one factor. -/
def lineOf (k : V) : LMat := lineFrame (leafTriple k)

/-- The data gauge `P_S ⊗ Q_T`. -/
def uFrame (S T : V) : Mat 529 := kron (lineOf S) (lineOf T)

def gates1 (T : V) : List (FGate Wire 529) := stage1.map (placeG (place1 T) (lift1 (lineOf T)))

def gates2 (S : V) : List (FGate Wire 529) := stage2.map (placeG (place2 S) (lift2 (lineOf S)))

def corrGates (S T : V) : List (FGate Wire 529) :=
  [⟨ReversibleFanout.add (wCorr S T) (wX S T), 1⟩,
    ⟨ReversibleFanout.add (wY S T) (wCorr S T), 1 - uFrame S T⟩]

def allV : List V := List.finRange leafCount

def allPairs : List (V × V) := allV.flatMap fun S => allV.map fun T => (S, T)

/-- The node's framed gates. Irreducible, so that `whnf` of a statement about the node (such as
its validity) stops here instead of running the compiler; `allGates_def` unfolds it. -/
@[irreducible] def allGates : List (FGate Wire 529) :=
  allV.flatMap gates1 ++ allV.flatMap gates2 ++ allPairs.flatMap fun p => corrGates p.1 p.2

attribute [local semireducible] allGates in
theorem allGates_def : allGates =
    allV.flatMap gates1 ++ allV.flatMap gates2 ++ allPairs.flatMap fun p => corrGates p.1 p.2 :=
  rfl

/-- The starting frames. -/
def gInit : Wire → Mat 529
  | .inl (.inl (S, T)) => uFrame S T
  | .inl (.inr _) => 0
  | .inr (.inl (false, T, c)) => lift1 (lineOf T) (starFrame c)
  | .inr (.inl (true, S, c)) => lift2 (lineOf S) (1 - starFrame c)
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr _)) => 0

/-- The side slots. Irreducible, as `allGates` is. -/
@[irreducible] def sideWires : List Wire :=
  [false, true].flatMap fun b => allV.flatMap fun k => (List.finRange dag.compile.next).map (wSide b k)

attribute [local semireducible] sideWires in
theorem sideWires_def : sideWires = [false, true].flatMap fun b => allV.flatMap fun k =>
    (List.finRange dag.compile.next).map (wSide b k) :=
  rfl

/-- Move every side slot to frame `1`. -/
def sinks (F : Wire → Mat 529) : List (FStep Wire 529) := alignMoves F sideWires 1

/-- The framed node. -/
def framedNode : List (FStep Wire 529) :=
  autoSteps gInit allGates ++ sinks (finalFrames (autoSteps gInit allGates) gInit)

/-! ### Runs of disjoint blocks -/

section Disjoint
variable {κ β : Type} [DecidableEq κ]

theorem run_off (p : Circuit.Program κ (ZMod 2)) (c : κ → ZMod 2) (k : κ)
    (hk : ∀ g ∈ p, k ∉ FramedCircuit.touched g) : Circuit.run p c k = c k := by
  induction p generalizing c with
  | nil => rfl
  | cons g p ih =>
    rw [Circuit.run_cons, ih _ fun g' hg' => hk g' (List.mem_cons_of_mem _ hg')]
    simp only [Circuit.Gate.run]
    exact Function.update_of_ne (fun h => hk g (by simp) (by rw [h]; simp [FramedCircuit.touched])) _ _

/-- **Disjoint blocks.** Blocks on disjoint wires run each on its own wires. -/
theorem run_flatMap_disjoint (blk : β → Circuit.Program κ (ZMod 2)) (Wb : β → κ → Prop)
    (hon : ∀ b, OnWires (Wb b) (blk b)) (hdisj : ∀ b b', b ≠ b' → ∀ k, Wb b k → ¬ Wb b' k) :
    ∀ (l : List β), l.Nodup → ∀ c : κ → ZMod 2,
      (∀ b ∈ l, ∀ k, Wb b k → Circuit.run (l.flatMap blk) c k = Circuit.run (blk b) c k) ∧
        ∀ k, (∀ b ∈ l, ¬ Wb b k) → Circuit.run (l.flatMap blk) c k = c k
  | [], _, c => ⟨fun _ h => absurd h (by simp), fun _ _ => rfl⟩
  | a :: l, hl, c => by
    rw [List.nodup_cons] at hl
    obtain ⟨ih1, ih2⟩ := run_flatMap_disjoint blk Wb hon hdisj l hl.2 (Circuit.run (blk a) c)
    have hoff : ∀ b k, Wb b k → ∀ b', b' ≠ b → ∀ g ∈ blk b', k ∉ FramedCircuit.touched g :=
      fun b k hk b' hb' g hg hm => hdisj b b' (Ne.symm hb') k hk (hon b' g hg k hm)
    refine ⟨fun b hb k hk => ?_, fun k hk => ?_⟩
    · rw [List.flatMap_cons, Circuit.run_append]
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [ih2 k fun b' hb' h => hdisj b b' (fun e => hl.1 (e ▸ hb')) k hk h]
      · have hba : b ≠ a := fun e => hl.1 (e ▸ hb)
        rw [ih1 b hb k hk]
        apply run_congr_on _ (hon b) _ _ _ k hk
        intro j hj
        exact run_off _ c j (hoff b j hj a (Ne.symm hba))
    · rw [List.flatMap_cons, Circuit.run_append, ih2 k fun b hb => hk b (List.mem_cons_of_mem _ hb)]
      exact run_off _ c k (fun g hg hm => hk a (by simp) (hon a g hg k hm))

end Disjoint

/-! ### Placements -/

theorem place1_x (T S : V) : place1 T (.inl (.x S)) = wX S T := by simp [place1, wX, S.2]
theorem place1_y (T S : V) : place1 T (.inl (.y S)) = wY S T := by simp [place1, wY, S.2]
theorem place1_aux (T : V) (s : Slot) : place1 T (.inl (.aux s)) = wSide false T s := by
  simp [place1, wSide, s.2]
theorem place2_x (S T : V) : place2 S (.inl (.x T)) = wY S T := by simp [place2, wY, T.2]
theorem place2_y (S T : V) : place2 S (.inl (.y T)) = wX S T := by simp [place2, wX, T.2]
theorem place2_aux (S : V) (s : Slot) : place2 S (.inl (.aux s)) = wSide true S s := by
  simp [place2, wSide, s.2]

/-- The node wire of an in-range local wire, in stage one. -/
theorem place1_cases (T : V) : ∀ w, InR w →
    (∃ S : V, w = .inl (.x S) ∧ place1 T w = wX S T) ∨
    (∃ S : V, w = .inl (.y S) ∧ place1 T w = wY S T) ∨
    (∃ s : Slot, w = .inl (.aux s) ∧ place1 T w = wSide false T s) ∨
    (∃ c, w = .inr c ∧ place1 T w = wCentre false T c)
  | .inl (.x n), h => Or.inl ⟨⟨n, h⟩, rfl, place1_x T ⟨n, h⟩⟩
  | .inl (.y t), h => Or.inr (Or.inl ⟨⟨t, h⟩, rfl, place1_y T ⟨t, h⟩⟩)
  | .inl (.aux s), h => Or.inr (Or.inr (Or.inl ⟨⟨s, h⟩, rfl, place1_aux T ⟨s, h⟩⟩))
  | .inr c, _ => Or.inr (Or.inr (Or.inr ⟨c, rfl, rfl⟩))

theorem place2_cases (S : V) : ∀ w, InR w →
    (∃ T : V, w = .inl (.x T) ∧ place2 S w = wY S T) ∨
    (∃ T : V, w = .inl (.y T) ∧ place2 S w = wX S T) ∨
    (∃ s : Slot, w = .inl (.aux s) ∧ place2 S w = wSide true S s) ∨
    (∃ c, w = .inr c ∧ place2 S w = wCentre true S c)
  | .inl (.x n), h => Or.inl ⟨⟨n, h⟩, rfl, place2_x S ⟨n, h⟩⟩
  | .inl (.y t), h => Or.inr (Or.inl ⟨⟨t, h⟩, rfl, place2_y S ⟨t, h⟩⟩)
  | .inl (.aux s), h => Or.inr (Or.inr (Or.inl ⟨⟨s, h⟩, rfl, place2_aux S ⟨s, h⟩⟩))
  | .inr c, _ => Or.inr (Or.inr (Or.inr ⟨c, rfl, rfl⟩))

theorem place1_injOn (T : V) : InjOn' (place1 T) InR := by
  intro a b ha hb h
  rcases place1_cases T a ha with ⟨S, rfl, e⟩ | ⟨S, rfl, e⟩ | ⟨s, rfl, e⟩ | ⟨c, rfl, e⟩ <;>
    rcases place1_cases T b hb with ⟨S', rfl, e'⟩ | ⟨S', rfl, e'⟩ | ⟨s', rfl, e'⟩ | ⟨c', rfl, e'⟩ <;>
    rw [e, e'] at h <;> simp_all [wX, wY, wSide, wCentre]

theorem place2_injOn (S : V) : InjOn' (place2 S) InR := by
  intro a b ha hb h
  rcases place2_cases S a ha with ⟨T, rfl, e⟩ | ⟨T, rfl, e⟩ | ⟨s, rfl, e⟩ | ⟨c, rfl, e⟩ <;>
    rcases place2_cases S b hb with ⟨T', rfl, e'⟩ | ⟨T', rfl, e'⟩ | ⟨s', rfl, e'⟩ | ⟨c', rfl, e'⟩ <;>
    rw [e, e'] at h <;> simp_all [wX, wY, wSide, wCentre]

/-- The wires of invocation `T` of stage one. -/
def W1 (T : V) (k : Wire) : Prop := ∃ w, InR w ∧ place1 T w = k

/-- The wires of invocation `S` of stage two. -/
def W2 (S : V) (k : Wire) : Prop := ∃ w, InR w ∧ place2 S w = k

theorem W1_disj (T T' : V) (h : T ≠ T') (k : Wire) (hk : W1 T k) : ¬ W1 T' k := by
  rintro ⟨w', hw', rfl⟩
  obtain ⟨w, hw, he⟩ := hk
  rcases place1_cases T w hw with ⟨S, rfl, e⟩ | ⟨S, rfl, e⟩ | ⟨s, rfl, e⟩ | ⟨c, rfl, e⟩ <;>
    rcases place1_cases T' w' hw' with ⟨S', rfl, e'⟩ | ⟨S', rfl, e'⟩ | ⟨s', rfl, e'⟩ | ⟨c', rfl, e'⟩ <;>
    rw [e, e'] at he <;> simp_all [wX, wY, wSide, wCentre]

theorem W2_disj (S S' : V) (h : S ≠ S') (k : Wire) (hk : W2 S k) : ¬ W2 S' k := by
  rintro ⟨w', hw', rfl⟩
  obtain ⟨w, hw, he⟩ := hk
  rcases place2_cases S w hw with ⟨T, rfl, e⟩ | ⟨T, rfl, e⟩ | ⟨s, rfl, e⟩ | ⟨c, rfl, e⟩ <;>
    rcases place2_cases S' w' hw' with ⟨T', rfl, e'⟩ | ⟨T', rfl, e'⟩ | ⟨s', rfl, e'⟩ | ⟨c', rfl, e'⟩ <;>
    rw [e, e'] at he <;> simp_all [wX, wY, wSide, wCentre]

theorem stage1_on : ∀ g ∈ gatesOf stage1, ∀ w ∈ FramedCircuit.touched g, InR w := by
  intro g hg
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
  exact stageGate_inR (stage1_gates v hv)

theorem stage2_on : ∀ g ∈ gatesOf stage2, ∀ w ∈ FramedCircuit.touched g, InR w := by
  intro g hg
  exact stageGate_inR (gatesOf_stage2_mem hg)

theorem W1_on (T : V) : OnWires (W1 T) ((gatesOf stage1).map (gateMap (place1 T))) := by
  intro g hg k hk
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  rw [touched_gateMap, List.mem_map] at hk
  obtain ⟨w, hw, rfl⟩ := hk
  exact ⟨w, stage1_on g' hg' w hw, rfl⟩

theorem W2_on (S : V) : OnWires (W2 S) ((gatesOf stage2).map (gateMap (place2 S))) := by
  intro g hg k hk
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  rw [touched_gateMap, List.mem_map] at hk
  obtain ⟨w, hw, rfl⟩ := hk
  exact ⟨w, stage2_on g' hg' w hw, rfl⟩

/-! ### The node on scalars -/

/-- Invocation `T` of stage one adds `X ⋅ T` into `Y ⋅ T` and restores its side slots. -/
theorem block1_run (T : V) (c : Wire → ZMod 2) (hz : ∀ c', c (wCentre false T c') = 0) :
    (∀ S, Circuit.run ((gatesOf stage1).map (gateMap (place1 T))) c (wY S T) =
      c (wY S T) + c (wX S T)) ∧
    (∀ S, Circuit.run ((gatesOf stage1).map (gateMap (place1 T))) c (wX S T) = c (wX S T)) ∧
    (∀ s, Circuit.run ((gatesOf stage1).map (gateMap (place1 T))) c (wSide false T s) =
      c (wSide false T s)) := by
  obtain ⟨h1, -⟩ := run_map_on (place1_injOn T) _ stage1_on c
  have hrun := stage1_run (c ∘ place1 T) fun c' => hz c'
  refine ⟨fun S => ?_, fun S => ?_, fun s => ?_⟩
  · rw [← place1_y, h1 _ (show InR (.inl (.y S)) from S.2), stage_target hrun S.2]
    simp only [Function.comp, place1_x, place1_y]
  · rw [← place1_x, h1 _ (show InR (.inl (.x S)) from S.2), stage_other hrun rfl]
    simp only [Function.comp, place1_x]
  · rw [← place1_aux, h1 _ (show InR (.inl (.aux s)) from s.2), stage_other hrun rfl]
    simp only [Function.comp, place1_aux]

/-- Invocation `S` of stage two adds `Y S ⋅` into `X S ⋅` and restores its side slots. -/
theorem block2_run (S : V) (c : Wire → ZMod 2) (hz : ∀ c', c (wCentre true S c') = 0) :
    (∀ T, Circuit.run ((gatesOf stage2).map (gateMap (place2 S))) c (wX S T) =
      c (wX S T) + c (wY S T)) ∧
    (∀ T, Circuit.run ((gatesOf stage2).map (gateMap (place2 S))) c (wY S T) = c (wY S T)) ∧
    (∀ s, Circuit.run ((gatesOf stage2).map (gateMap (place2 S))) c (wSide true S s) =
      c (wSide true S s)) := by
  obtain ⟨h1, -⟩ := run_map_on (place2_injOn S) _ stage2_on c
  have hrun := stage2_run (c ∘ place2 S) fun c' => hz c'
  refine ⟨fun T => ?_, fun T => ?_, fun s => ?_⟩
  · rw [← place2_y, h1 _ (show InR (.inl (.y T)) from T.2), stage_target hrun T.2]
    simp only [Function.comp, place2_x, place2_y]
  · rw [← place2_x, h1 _ (show InR (.inl (.x T)) from T.2), stage_other hrun rfl]
    simp only [Function.comp, place2_x]
  · rw [← place2_aux, h1 _ (show InR (.inl (.aux s)) from s.2), stage_other hrun rfl]
    simp only [Function.comp, place2_aux]

theorem allV_nodup : allV.Nodup := List.nodup_finRange _

theorem mem_allV (k : V) : k ∈ allV := List.mem_finRange k

theorem allPairs_nodup : allPairs.Nodup := by
  rw [allPairs]
  refine List.nodup_flatMap.mpr ⟨fun S _ => (List.nodup_finRange _).map fun _ _ h => (Prod.mk.inj h).2,
    allV_nodup.imp fun {S S'} hne => ?_⟩
  simp only [Function.onFun, List.disjoint_left, List.mem_map]
  rintro _ ⟨T, -, rfl⟩ ⟨T', -, h⟩
  exact hne (Prod.mk.inj h).1.symm

theorem mem_allPairs (S T : V) : (S, T) ∈ allPairs := by
  simp [allPairs, mem_allV]

theorem gates_stage1 : (allV.flatMap gates1).map FGate.gate =
    allV.flatMap fun T => (gatesOf stage1).map (gateMap (place1 T)) := by
  rw [List.map_flatMap]
  exact congrArg allV.flatMap (funext fun T => by
    rewrite [gates1, gatesOf]; exact gates_place _ _ _)

theorem gates_stage2 : (allV.flatMap gates2).map FGate.gate =
    allV.flatMap fun S => (gatesOf stage2).map (gateMap (place2 S)) := by
  rw [List.map_flatMap]
  exact congrArg allV.flatMap (funext fun S => by
    rewrite [gates2, gatesOf]; exact gates_place _ _ _)

/-- The wires of a correction. -/
def Wc (p : V × V) (k : Wire) : Prop := k = wX p.1 p.2 ∨ k = wY p.1 p.2 ∨ k = wCorr p.1 p.2

theorem corr_on (p : V × V) : OnWires (Wc p) ((corrGates p.1 p.2).map FGate.gate) := by
  intro g hg k hk
  simp only [corrGates, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> rw [mem_touched_add] at hk <;> rcases hk with rfl | rfl <;>
    simp [Wc]

theorem Wc_disj (p p' : V × V) (h : p ≠ p') (k : Wire) (hk : Wc p k) : ¬ Wc p' k := by
  obtain ⟨S, T⟩ := p
  obtain ⟨S', T'⟩ := p'
  rintro (rfl | rfl | rfl) <;> rcases hk with h1 | h1 | h1 <;>
    simp_all [wX, wY, wCorr]

theorem corr_x (S T : V) (e : Wire → ZMod 2) :
    Circuit.run ((corrGates S T).map FGate.gate) e (wX S T) = e (wX S T) := by
  simp only [corrGates, List.map_cons, List.map_nil, Circuit.run_cons, Circuit.run_nil,
    ReversibleFanout.add_run]
  rw [Function.update_of_ne (by simp [wX, wY]), Function.update_of_ne (by simp [wX, wCorr])]

theorem corr_y (S T : V) (e : Wire → ZMod 2) :
    Circuit.run ((corrGates S T).map FGate.gate) e (wY S T) =
      e (wY S T) + (e (wCorr S T) + e (wX S T)) := by
  simp only [corrGates, List.map_cons, List.map_nil, Circuit.run_cons, Circuit.run_nil,
    ReversibleFanout.add_run]
  rw [Function.update_self, Function.update_of_ne (show wY S T ≠ wCorr S T by simp [wY, wCorr]),
    Function.update_self]

theorem zmod2_cancel (a b : ZMod 2) : a + (b + a) = b := by
  revert a b; decide

theorem zmod2_cancel' (a b : ZMod 2) : a + b + (0 + a) = b := by
  revert a b; decide

/-- **The node on scalars.** On zero temporaries, the data pairs are exchanged and the side slots
restored. -/
theorem node_scalar (c : Wire → ZMod 2) (hz : ∀ t : Temp, c (.inr t) = 0) :
    (∀ S T, Circuit.run (allGates.map FGate.gate) c (wX S T) = c (wY S T)) ∧
    (∀ S T, Circuit.run (allGates.map FGate.gate) c (wY S T) = c (wX S T)) ∧
    (∀ b k s, Circuit.run (allGates.map FGate.gate) c (wSide b k s) = c (wSide b k s)) := by
  rw [allGates_def, List.map_append, List.map_append, Circuit.run_append, Circuit.run_append,
    gates_stage1, gates_stage2, List.map_flatMap]
  obtain ⟨d1, d1'⟩ := run_flatMap_disjoint _ W1 W1_on W1_disj allV allV_nodup c
  generalize Circuit.run (allV.flatMap fun T => (gatesOf stage1).map (gateMap (place1 T))) c = e1
    at d1 d1' ⊢
  obtain ⟨d2, d2'⟩ := run_flatMap_disjoint _ W2 W2_on W2_disj allV allV_nodup e1
  generalize Circuit.run (allV.flatMap fun S => (gatesOf stage2).map (gateMap (place2 S))) e1 = e2
    at d2 d2' ⊢
  obtain ⟨d3, d3'⟩ := run_flatMap_disjoint (fun p => (corrGates p.1 p.2).map FGate.gate) Wc corr_on
    Wc_disj allPairs allPairs_nodup e2
  have hW1X (S T : V) : W1 T (wX S T) := ⟨.inl (.x S), S.2, place1_x T S⟩
  have hW1Y (S T : V) : W1 T (wY S T) := ⟨.inl (.y S), S.2, place1_y T S⟩
  have hW1s (T : V) (s : Slot) : W1 T (wSide false T s) := ⟨.inl (.aux s), s.2, place1_aux T s⟩
  have hW2X (S T : V) : W2 S (wX S T) := ⟨.inl (.y T), T.2, place2_y S T⟩
  have hW2Y (S T : V) : W2 S (wY S T) := ⟨.inl (.x T), T.2, place2_x S T⟩
  have hW2s (S : V) (s : Slot) : W2 S (wSide true S s) := ⟨.inl (.aux s), s.2, place2_aux S s⟩
  have hnot1 : ∀ k, (∀ T w, InR w → place1 T w ≠ k) → ∀ T ∈ allV, ¬ W1 T k :=
    fun k h T _ ⟨w, hw, he⟩ => h T w hw he
  have hnot2 : ∀ k, (∀ S w, InR w → place2 S w ≠ k) → ∀ S ∈ allV, ¬ W2 S k :=
    fun k h S _ ⟨w, hw, he⟩ => h S w hw he
  have hcentre1 : ∀ T c', e1 (wCentre true T c') = 0 := by
    intro T c'
    rw [d1' _ (hnot1 _ fun T' w hw he => by
      rcases place1_cases T' w hw with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
        rw [e] at he <;> simp [wX, wY, wSide, wCentre] at he)]
    exact hz _
  have hcorr2 : ∀ S T, e2 (wCorr S T) = 0 := by
    intro S T
    rw [d2' _ (hnot2 _ fun S' w hw he => by
      rcases place2_cases S' w hw with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
        rw [e] at he <;> simp [wX, wY, wSide, wCentre, wCorr] at he),
      d1' _ (hnot1 _ fun T' w hw he => by
      rcases place1_cases T' w hw with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
        rw [e] at he <;> simp [wX, wY, wSide, wCentre, wCorr] at he)]
    exact hz _
  -- stage one
  have e1X : ∀ S T, e1 (wX S T) = c (wX S T) := fun S T => by
    rw [d1 T (mem_allV T) _ (hW1X S T)]
    exact (block1_run T c fun c' => hz _).2.1 S
  have e1Y : ∀ S T, e1 (wY S T) = c (wY S T) + c (wX S T) := fun S T => by
    rw [d1 T (mem_allV T) _ (hW1Y S T)]
    exact (block1_run T c fun c' => hz _).1 S
  -- stage two
  have e2X : ∀ S T, e2 (wX S T) = c (wY S T) := fun S T => by
    rw [d2 S (mem_allV S) _ (hW2X S T), (block2_run S e1 (hcentre1 S)).1 T, e1X, e1Y,
      zmod2_cancel]
  have e2Y : ∀ S T, e2 (wY S T) = c (wY S T) + c (wX S T) := fun S T => by
    rw [d2 S (mem_allV S) _ (hW2Y S T), (block2_run S e1 (hcentre1 S)).2.1 T, e1Y]
  refine ⟨fun S T => ?_, fun S T => ?_, fun b k s => ?_⟩
  · rw [d3 (S, T) (mem_allPairs S T) _ (Or.inl rfl)]
    exact (corr_x S T e2).trans (e2X S T)
  · rw [d3 (S, T) (mem_allPairs S T) _ (Or.inr (Or.inl rfl))]
    refine (corr_y S T e2).trans ?_
    rw [e2Y, hcorr2, e2X]
    exact zmod2_cancel' _ _
  · rw [d3' _ fun p _ h => by rcases h with h | h | h <;> simp [wX, wY, wSide, wCorr] at h]
    cases b with
    | false =>
      rw [d2' _ (hnot2 _ fun S' w hw he => by
        rcases place2_cases S' w hw with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
          rw [e] at he <;> simp [wX, wY, wSide, wCentre] at he),
        d1 k (mem_allV k) _ (hW1s k s)]
      exact (block1_run k c fun c' => hz _).2.2 s
    | true =>
      rw [d2 k (mem_allV k) _ (hW2s k s), (block2_run k e1 (hcentre1 k)).2.2 s,
        d1' _ (hnot1 _ fun T' w hw he => by
        rcases place1_cases T' w hw with ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ | ⟨_, -, e⟩ <;>
          rw [e] at he <;> simp [wX, wY, wSide, wCentre] at he)]

end

end IntegerMultBounds.MathlibTM2.M8.Global
