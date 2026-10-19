module

public import IntegerMultBounds.MathlibTM2.M8.Local.Schedule
public import IntegerMultBounds.MathlibTM2.M8.Frames.Plain
public import IntegerMultBounds.MathlibTM2.M8.Global.Lift

/-!
# The two local stages

An invocation acts on local wires (`LW`): the registers of the local word and one temporary per
centre. Its first stage (`stage1`) is the local word with frames on every gate:
* the first pass at frame `0`;
* the compiled operations at the frames of their nodes;
* each centre read through its own temporary (`centreBlock`): the temporary copies the centre's
  slot at the centre's star frame, moves to frame `0` and adds into the targets there;
* the output reads at the hyperplane frames of their triples;
* the uncompute at frame `1`.

The second stage (`stage2`) runs the blocks of the first in reverse order with complemented
frames; each centre block keeps its internal order. On local contents with zero temporaries, the
first stage adds every source into its target (`stage1_run`), and so does the second
(`stage2_run`); the other registers end unchanged.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-- Local wires: the registers of one invocation, and one temporary per centre. -/
abbrev LW := Reg ⊕ Fin 23

/-- A register gate on local wires. -/
def gL (g : Circuit.Gate Reg (ZMod 2)) : Circuit.Gate LW (ZMod 2) := gateMap Sum.inl g

/-- The read slot of root `j`. A notation: the compiled state is never unfolded, so terms
mentioning it are compared syntactically. -/
notation:max "slotOf " j:max => State.pend (Dag.compile dag) (Use.root j)

/-- A one-gate block. -/
def single (g : Circuit.Gate LW (ZMod 2)) (F : LMat) : List (FGate LW 23) := [⟨g, F⟩]

/-- The first pass, at frame `0`. -/
def pass1Blocks : List (List (FGate LW 23)) :=
  (dag.sideGates ++ dag.rootReads targets ++ dag.sideGates.reverse).map fun g => single (gL g) 0

/-- The compiled operations, at the frames of their nodes. -/
def computeBlocks : List (List (FGate LW 23)) :=
  dag.compile.ops.map fun op => single (gL (opGate op)) (nodeFrame op.node)

/-- The reads of the centre of `c` through its temporary. -/
def centreBlock (c : Fin 23) : List (FGate LW 23) :=
  ⟨ReversibleFanout.add (.inr c) (.inl (.aux (slotOf (3 * leafCount + c)))), starFrame c⟩ ::
    (targets (3 * leafCount + c)).map fun t => ⟨ReversibleFanout.add (.inl (.y t)) (.inr c), 0⟩

def centreBlocks : List (List (FGate LW 23)) := (List.finRange 23).map centreBlock

/-- The output reads, at the hyperplane frames of their triples. -/
def outputBlocks : List (List (FGate LW 23)) :=
  (List.range (3 * leafCount)).map fun j =>
    single (ReversibleFanout.add (.inl (.y (j / 3))) (.inl (.aux (slotOf j))))
      (hyperFrame (leafTriple (j / 3)))

/-- The uncompute, at frame `1`. -/
def uncomputeBlocks : List (List (FGate LW 23)) :=
  dag.compile.ops.reverse.map fun op => single (gL (opGate op)) 1

def blocks1 : List (List (FGate LW 23)) :=
  pass1Blocks ++ computeBlocks ++ centreBlocks ++ outputBlocks ++ uncomputeBlocks

/-- The first stage. -/
def stage1 : List (FGate LW 23) := blocks1.flatten

/-- A block with complemented frames. -/
def complB (B : List (FGate LW 23)) : List (FGate LW 23) := B.map fun v => ⟨v.gate, 1 - v.frame⟩

/-- The second stage: the blocks in reverse order, with complemented frames. -/
def stage2 : List (FGate LW 23) := (blocks1.reverse.map complB).flatten

/-! ### Register programs on local wires -/

/-- The gates of a framed list. -/
def gatesOf (L : List (FGate LW 23)) : Circuit.Program LW (ZMod 2) := L.map FGate.gate

theorem gatesOf_flatten (Bs : List (List (FGate LW 23))) :
    gatesOf Bs.flatten = Bs.flatMap gatesOf := by
  simp [gatesOf, List.flatMap, List.map_flatten]
  rfl

theorem gatesOf_complB (B : List (FGate LW 23)) : gatesOf (complB B) = gatesOf B := by
  simp [gatesOf, complB]

theorem run_gL (p : Circuit.Program Reg (ZMod 2)) (d : LW → ZMod 2) :
    (fun r => Circuit.run (p.map gL) d (.inl r)) = Circuit.run p (fun r => d (.inl r)) ∧
      ∀ c, Circuit.run (p.map gL) d (.inr c) = d (.inr c) := by
  obtain ⟨h1, h2⟩ := run_map Sum.inl_injective p d
  exact ⟨funext h1, fun c => h2 _ fun r => Sum.inl_ne_inr⟩

theorem singles_gates (p : Circuit.Program Reg (ZMod 2)) (F : Circuit.Gate Reg (ZMod 2) → LMat) :
    ((p.map fun g => single (gL g) (F g)).flatMap gatesOf) = p.map gL := by
  induction p with
  | nil => rfl
  | cons g p ih =>
    rw [List.map_cons, List.flatMap_cons, ih, List.map_cons]
    rfl

theorem flatMap_single {α β : Type*} {l : List α} {f : α → List β} {g : α → β}
    (h : ∀ a ∈ l, f a = [g a]) : l.flatMap f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, h a (by simp), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]
    rfl

/-! ### Centre reads through temporaries -/

/-- The reads of the centre of `c`. -/
def centreReads (c : Fin 23) : Circuit.Program Reg (ZMod 2) :=
  (targets (3 * leafCount + c)).map fun t => ReversibleFanout.add (.y t) (.aux (slotOf (3 * leafCount + c)))

theorem scatter_contrib (Ts : List ℕ) (src : LW) (e : LW → ZMod 2) (k : LW) :
    contrib (Ts.map fun t => ReversibleFanout.add (.inl (.y t)) src) e k =
      (Ts.map fun t => if (.inl (.y t) : LW) = k then e src else 0).sum := by
  simp only [contrib, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp [ReversibleFanout.add, Function.comp]

theorem scatter_untouched (Ts : List ℕ) (src : LW) (hsrc : ∀ t, src ≠ .inl (.y t)) :
    ReadsUntouched (Ts.map fun t => ReversibleFanout.add (.inl (.y t)) src) := by
  intro g hg g' hg' t ht
  simp only [List.mem_map] at hg hg'
  obtain ⟨T, -, rfl⟩ := hg
  obtain ⟨T', -, rfl⟩ := hg'
  simp only [ReversibleFanout.add, List.mem_singleton] at ht
  rw [ht]
  exact hsrc T

/-- Scattering from two wires with equal contents gives equal results. -/
theorem scatter_eq (Ts : List ℕ) (a b : LW) (ha : ∀ t, a ≠ .inl (.y t)) (hb : ∀ t, b ≠ .inl (.y t))
    (e : LW → ZMod 2) (hab : e a = e b) :
    Circuit.run (Ts.map fun t => ReversibleFanout.add (.inl (.y t)) a) e =
      Circuit.run (Ts.map fun t => ReversibleFanout.add (.inl (.y t)) b) e := by
  funext k
  rw [run_readsUntouched _ (scatter_untouched Ts a ha), run_readsUntouched _ (scatter_untouched Ts b hb),
    scatter_contrib, scatter_contrib, hab]

theorem centreBlock_run (c : Fin 23) (d : LW → ZMod 2) (hz : d (.inr c) = 0) :
    (fun r => Circuit.run (gatesOf (centreBlock c)) d (.inl r)) =
        Circuit.run (centreReads c) (fun r => d (.inl r)) ∧
      ∀ c', Circuit.run (gatesOf (centreBlock c)) d (.inr c') =
        if c' = c then d (.inl (.aux (slotOf (3 * leafCount + c)))) else d (.inr c') := by
  obtain ⟨s, hs⟩ : ∃ s, s = slotOf (3 * leafCount + c) := ⟨_, rfl⟩
  obtain ⟨Ts, hTs⟩ : ∃ Ts, Ts = targets (3 * leafCount + c) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : LW → ZMod 2,
      e = Function.update d (.inr c) (d (.inr c) + d (.inl (.aux s))) := ⟨_, rfl⟩
  have hgates : gatesOf (centreBlock c) =
      ReversibleFanout.add (.inr c) (.inl (.aux s)) ::
        Ts.map fun t => ReversibleFanout.add (.inl (.y t)) (.inr c) := by
    rw [hs, hTs]
    simp only [gatesOf, centreBlock, List.map_cons, List.map_map]
    rfl
  have hreads : (centreReads c).map gL = Ts.map fun t => ReversibleFanout.add (.inl (.y t)) (.inl (.aux s)) := by
    rw [hs, hTs]
    simp only [centreReads, List.map_map]
    rfl
  have hrun : Circuit.run (gatesOf (centreBlock c)) d =
      Circuit.run ((centreReads c).map gL) e := by
    rw [hgates, Circuit.run_cons, ReversibleFanout.add_run, ← he, hreads]
    exact scatter_eq _ (.inr c) (.inl (.aux s)) (fun t h => by cases h) (fun t h => by cases h) e
      (by rw [he]; simp [hz])
  have he' : (fun r => e (.inl r)) = fun r => d (.inl r) := by
    funext r; rw [he]; simp
  obtain ⟨h1, h2⟩ := run_gL (centreReads c) e
  refine ⟨by rw [hrun, h1, he'], fun c' => ?_⟩
  rw [hrun, h2, he, ← hs]
  by_cases h : c' = c
  · subst h; simp [hz]
  · simp [h]

/-- All centre reads. -/
def allCentreReads (cs : List (Fin 23)) : Circuit.Program Reg (ZMod 2) := cs.flatMap centreReads

theorem centreBlocks_run : ∀ (cs : List (Fin 23)) (d : LW → ZMod 2), cs.Nodup →
    (∀ c ∈ cs, d (.inr c) = 0) →
      (fun r => Circuit.run ((cs.map centreBlock).flatMap gatesOf) d (.inl r)) =
        Circuit.run (allCentreReads cs) (fun r => d (.inl r))
  | [], d, _, _ => rfl
  | c :: cs, d, hnd, hz => by
    rw [List.nodup_cons] at hnd
    obtain ⟨h1, h2⟩ := centreBlock_run c d (hz c (by simp))
    have hz' : ∀ c' ∈ cs, Circuit.run (gatesOf (centreBlock c)) d (.inr c') = 0 := by
      intro c' hc'
      have hne : c' ≠ c := fun h => hnd.1 (by rw [← h]; exact hc')
      rw [h2, ite_eq_right hne]
      exact hz c' (List.mem_cons_of_mem _ hc')
    simp only [List.map_cons, List.flatMap_cons, Circuit.run_append, allCentreReads]
    rw [centreBlocks_run cs _ hnd.2 hz', h1]
    rfl

/-- The output reads. -/
def outputReads : Circuit.Program Reg (ZMod 2) :=
  (List.range (3 * leafCount)).map fun j => ReversibleFanout.add (.y (j / 3)) (.aux (slotOf j))

theorem outputBlocks_gates : outputBlocks.flatMap gatesOf = outputReads.map gL := by
  rw [outputBlocks, List.flatMap_map, outputReads, List.map_map]
  exact flatMap_single fun j _ => rfl

/-- Splitting a range of reads, generically. -/
theorem split_flatMap {X : Type} (F : ℕ → List X) (a b : ℕ) (G : ℕ → X)
    (hG : ∀ j < a, F j = [G j]) :
    (List.range (a + b)).flatMap F =
      (List.range a).map G ++ (List.finRange b).flatMap fun c : Fin b => F (a + c) := by
  have hval : (List.finRange b).map Fin.val = List.range b := by
    apply List.ext_get <;> simp
  have hfin : ∀ G' : ℕ → List X,
      (List.range b).flatMap G' = (List.finRange b).flatMap fun c : Fin b => G' c := by
    intro G'
    rw [← hval, List.flatMap_map]
  rw [List.range_add, List.flatMap_append, flatMap_single fun j hj => hG j (List.mem_range.mp hj),
    List.flatMap_map, hfin]

/-- The root reads are the output reads and then the centre reads. -/
theorem rootReads_split :
    dag.rootReads targets = outputReads ++ allCentreReads (List.finRange 23) := by
  have hrc : dag.rootCount = 3 * leafCount + 23 := rfl
  show (List.range dag.rootCount).flatMap (fun j => (targets j).map fun T =>
    ReversibleFanout.add (Reg.y T) (Reg.aux (dag.compile.pend (.root j)))) = _
  rw [hrc]
  refine split_flatMap _ (3 * leafCount) 23
    (fun j => ReversibleFanout.add (Reg.y (j / 3)) (Reg.aux (slotOf j))) ?_
  intro j hj
  show (targets j).map _ = _
  rw [targets, ite_eq_left hj]
  rfl

theorem singles_map_gates {α : Type*} (l : List α) (h : α → Circuit.Gate Reg (ZMod 2))
    (F : α → LMat) : ((l.map fun a => single (gL (h a)) (F a)).flatMap gatesOf) = (l.map h).map gL := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.flatMap_cons, ih, List.map_cons, List.map_cons]
    rfl

theorem singles_reverse {α : Type*} (l : List α) (g : α → Circuit.Gate LW (ZMod 2)) (F : α → LMat) :
    ((l.map fun a => single (g a) (F a)).reverse.flatMap gatesOf) =
      ((l.map fun a => single (g a) (F a)).flatMap gatesOf).reverse := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h1 : (single (g a) (F a) :: l.map fun a => single (g a) (F a)).flatMap gatesOf =
        g a :: (l.map fun a => single (g a) (F a)).flatMap gatesOf := rfl
    rw [List.map_cons, List.reverse_cons, List.flatMap_append, ih, h1, List.reverse_cons]
    rfl

/-- Runs of register programs on local wires, on the registers. -/
theorem run_gL_inl (p : Circuit.Program Reg (ZMod 2)) (d : LW → ZMod 2) (r : Reg) :
    Circuit.run (p.map gL) d (.inl r) = Circuit.run p (fun r => d (.inl r)) r :=
  congrFun (run_gL p d).1 r

theorem run_gL_inr (p : Circuit.Program Reg (ZMod 2)) (d : LW → ZMod 2) (c : Fin 23) :
    Circuit.run (p.map gL) d (.inr c) = d (.inr c) :=
  (run_gL p d).2 c

theorem readsLike_out_centre :
    dag.ReadsLike targets (allCentreReads (List.finRange 23) ++ outputReads) :=
  dag.readsLike_perm targets (by rw [rootReads_split]; exact List.perm_append_comm)

theorem readsLike_rev_centre :
    dag.ReadsLike targets (outputReads.reverse ++ allCentreReads (List.finRange 23).reverse) :=
  dag.readsLike_perm targets (by
    rw [rootReads_split]
    refine List.Perm.append (List.reverse_perm _) ?_
    exact List.Perm.flatMap_right _ (List.reverse_perm _))

/-- The register part of a local state. -/
abbrev regs (d : LW → ZMod 2) : Reg → ZMod 2 := fun r => d (.inl r)

theorem regs_run_gL (p : Circuit.Program Reg (ZMod 2)) (d : LW → ZMod 2) :
    regs (Circuit.run (p.map gL) d) = Circuit.run p (regs d) := (run_gL p d).1

theorem regs_centreBlocks (d : LW → ZMod 2) (hz : ∀ c, d (.inr c) = 0) :
    regs (Circuit.run (centreBlocks.flatMap gatesOf) d) =
      Circuit.run (allCentreReads (List.finRange 23)) (regs d) := by
  have h := centreBlocks_run (List.finRange 23) d (List.nodup_finRange 23) fun c _ => hz c
  rw [show centreBlocks = (List.finRange 23).map centreBlock from rfl]
  exact h

theorem regs_centreBlocks' (d : LW → ZMod 2) (hz : ∀ c, d (.inr c) = 0) :
    regs (Circuit.run (((List.finRange 23).reverse.map centreBlock).flatMap gatesOf) d) =
      Circuit.run (allCentreReads (List.finRange 23).reverse) (regs d) := by
  have h := centreBlocks_run (List.finRange 23).reverse d
    (List.nodup_reverse.mpr (List.nodup_finRange 23)) fun c _ => hz c
  exact h

/-- **The first stage.** On zero temporaries, the registers gain the read increments of the
compiled operations on the sources. -/
theorem stage1_run (d : LW → ZMod 2) (hz : ∀ c, d (.inr c) = 0) :
    regs (Circuit.run (gatesOf stage1) d) =
      regs d + dag.readDelta targets (Circuit.run dag.opsGates (part Reg.isX (regs d))) := by
  have hv := dag_valid
  have hgates : gatesOf stage1 = (dag.sideGates ++ dag.rootReads targets ++ dag.sideGates.reverse).map gL ++
      dag.opsGates.map gL ++ (centreBlocks.flatMap gatesOf) ++ outputReads.map gL ++
        dag.opsGates.reverse.map gL := by
    rw [stage1, gatesOf_flatten, blocks1]
    simp only [List.flatMap_append]
    rw [pass1Blocks, singles_gates, computeBlocks, singles_map_gates, outputBlocks_gates,
      uncomputeBlocks, singles_map_gates, Dag.opsGates, List.map_reverse]
  have hz1 : ∀ c, Circuit.run (dag.opsGates.map gL)
      (Circuit.run ((dag.sideGates ++ dag.rootReads targets ++ dag.sideGates.reverse).map gL) d)
      (.inr c) = 0 := fun c => by rw [run_gL_inr, run_gL_inr]; exact hz c
  rw [hgates, Circuit.run_append, Circuit.run_append, Circuit.run_append, Circuit.run_append,
    regs_run_gL, regs_run_gL, regs_centreBlocks _ hz1, regs_run_gL, regs_run_gL,
    show ∀ x, Circuit.run dag.opsGates.reverse (Circuit.run outputReads
      (Circuit.run (allCentreReads (List.finRange 23)) (Circuit.run dag.opsGates x))) =
      Circuit.run (dag.opsGates ++ (allCentreReads (List.finRange 23) ++ outputReads) ++
        dag.opsGates.reverse) x from fun x => by simp only [Circuit.run_append],
    dag.pass_run targets (dag.sideGates_xor hv)
    (fun d hd => dag.sideGates_reverse_yOnly hd) (dag.run_rootReads targets),
    dag.two_passes targets (dag.opsGates_xor hv) (fun d hd => dag.opsGates_yOnly hd)
      (fun d hd => dag.opsGates_reverse_yOnly hd) readsLike_out_centre,
    dag.garbage_cancel hv]

/-- **The second stage.** On zero temporaries it has the register effect of the first. -/
theorem stage2_run (d : LW → ZMod 2) (hz : ∀ c, d (.inr c) = 0) :
    regs (Circuit.run (gatesOf stage2) d) =
      regs d + dag.readDelta targets (Circuit.run dag.opsGates (part Reg.isX (regs d))) := by
  have hv := dag_valid
  have hcompl : ∀ Bs : List (List (FGate LW 23)), (Bs.map complB).flatMap gatesOf = Bs.flatMap gatesOf := by
    intro Bs
    rw [List.flatMap_map]
    congr 1
    funext B
    exact gatesOf_complB B
  have hgates : gatesOf stage2 = dag.opsGates.map gL ++ outputReads.reverse.map gL ++
      (((List.finRange 23).reverse.map centreBlock).flatMap gatesOf) ++ dag.opsGates.reverse.map gL ++
        (dag.sideGates ++ (dag.rootReads targets).reverse ++ dag.sideGates.reverse).map gL := by
    rw [stage2, gatesOf_flatten, hcompl, blocks1]
    simp only [List.reverse_append, List.flatMap_append]
    rw [uncomputeBlocks, singles_reverse, singles_map_gates, outputBlocks, singles_reverse,
      ← outputBlocks, outputBlocks_gates, centreBlocks, ← List.map_reverse, computeBlocks,
      singles_reverse, singles_map_gates, pass1Blocks, singles_reverse, singles_gates]
    simp only [Dag.opsGates, ← List.map_reverse, List.reverse_reverse, List.reverse_append,
      List.append_assoc]
  have hz2 : ∀ c, Circuit.run (outputReads.reverse.map gL) (Circuit.run (dag.opsGates.map gL) d)
      (.inr c) = 0 := fun c => by rw [run_gL_inr, run_gL_inr]; exact hz c
  rw [hgates, Circuit.run_append, Circuit.run_append, Circuit.run_append, Circuit.run_append,
    regs_run_gL, regs_run_gL, regs_centreBlocks' _ hz2, regs_run_gL, regs_run_gL,
    show ∀ x, Circuit.run (dag.sideGates ++ (dag.rootReads targets).reverse ++ dag.sideGates.reverse)
      (Circuit.run dag.opsGates.reverse (Circuit.run (allCentreReads (List.finRange 23).reverse)
        (Circuit.run outputReads.reverse (Circuit.run dag.opsGates x)))) =
      Circuit.run (dag.sideGates ++ (dag.rootReads targets).reverse ++ dag.sideGates.reverse)
        (Circuit.run (dag.opsGates ++ (outputReads.reverse ++
          allCentreReads (List.finRange 23).reverse) ++ dag.opsGates.reverse) x)
      from fun x => by simp only [Circuit.run_append],
    dag.pass_run targets (dag.opsGates_xor hv)
    (fun d hd => dag.opsGates_reverse_yOnly hd) readsLike_rev_centre,
    dag.two_passes targets (dag.sideGates_xor hv) (fun d hd => dag.sideGates_yOnly hd)
      (fun d hd => dag.sideGates_reverse_yOnly hd)
      (dag.readsLike_perm targets (List.reverse_perm _)),
    add_comm (dag.readDelta targets (Circuit.run dag.opsGates _)), dag.garbage_cancel hv]

/-- Each stage adds every source into its target. -/
theorem stage_target {d : LW → ZMod 2} {e : LW → ZMod 2}
    (he : regs e = regs d + dag.readDelta targets (Circuit.run dag.opsGates (part Reg.isX (regs d))))
    {t : ℕ} (ht : t < leafCount) : e (.inl (.y t)) = d (.inl (.y t)) + d (.inl (.x t)) := by
  have := congrFun he (.y t)
  simp only [Pi.add_apply] at this
  rw [readDelta_target _ ht] at this
  exact this

/-- Each stage leaves the sources and side slots unchanged. -/
theorem stage_other {d : LW → ZMod 2} {e : LW → ZMod 2}
    (he : regs e = regs d + dag.readDelta targets (Circuit.run dag.opsGates (part Reg.isX (regs d))))
    {r : Reg} (hr : r.isY = false) : e (.inl r) = d (.inl r) := by
  have := congrFun he r
  simp only [Pi.add_apply] at this
  rw [dag.readDelta_off_y targets _ r hr, add_zero] at this
  exact this

end

end IntegerMultBounds.MathlibTM2.M8.Global
