module

public import IntegerMultBounds.MathlibTM2.M8.Local.Compile
public import IntegerMultBounds.Networks.ReversibleFanout

/-!
# The local word

The local word of an invocation acts on registers `x S` (sources), `y T` (targets) and `aux s`
(side slots). With `OPS` the compiled operations as XOR gates, `OPS'` the same without the source
gates, and `RR` the root reads (each root slot added into the targets of its root), the word is

`OPS' ++ RR ++ OPS'⁻¹ ++ OPS ++ RR ++ OPS⁻¹`.

The first three parts read the side slots' arbitrary contents into the targets and restore them;
the last three add the same garbage again, plus the roots' values. Over `𝔽₂` the garbage cancels
(`word_run`): on arbitrary contents, the targets gain the root values, and sources and side slots
end unchanged.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

open Networks

/-- The registers of one invocation. -/
inductive Reg where
  | x (S : ℕ)
  | y (T : ℕ)
  | aux (s : ℕ)
  deriving DecidableEq

/-- A register kind: sources, targets or side slots. -/
def Reg.isX : Reg → Bool | .x _ => true | _ => false
def Reg.isY : Reg → Bool | .y _ => true | _ => false
def Reg.isAux : Reg → Bool | .aux _ => true | _ => false

/-- The part of `c` on the registers of a kind. -/
def part (k : Reg → Bool) (c : Reg → ZMod 2) : Reg → ZMod 2 := fun r => if k r then c r else 0

theorem part_split (c : Reg → ZMod 2) :
    c = part Reg.isX c + part Reg.isY c + part Reg.isAux c := by
  funext r
  cases r <;> simp [part, Reg.isX, Reg.isY, Reg.isAux]

/-- An operation as an XOR gate. -/
def opGate : Op → Circuit.Gate Reg (ZMod 2)
  | .src s n => ReversibleFanout.add (.aux s) (.x n)
  | .add p o _ => ReversibleFanout.add (.aux p) (.aux o)
  | .copy p f _ => ReversibleFanout.add (.aux f) (.aux p)

/-- A source operation. -/
def Op.isSrc : Op → Bool
  | .src _ _ => true
  | _ => false

namespace Dag
variable (D : Dag)

/-- The compiled operations. -/
def opsGates : Circuit.Program Reg (ZMod 2) := D.compile.ops.map opGate

/-- The compiled operations without the source gates. -/
def sideGates : Circuit.Program Reg (ZMod 2) := (D.compile.ops.filter fun op => !op.isSrc).map opGate

/-- The root reads: each root's slot into each of its targets. -/
def rootReads (targets : ℕ → List ℕ) : Circuit.Program Reg (ZMod 2) :=
  (List.range D.rootCount).flatMap fun j =>
    (targets j).map fun T => ReversibleFanout.add (.y T) (.aux (D.compile.pend (.root j)))

/-- The local word. -/
def word (targets : ℕ → List ℕ) : Circuit.Program Reg (ZMod 2) :=
  D.sideGates ++ D.rootReads targets ++ D.sideGates.reverse ++
    D.opsGates ++ D.rootReads targets ++ D.opsGates.reverse

end Dag

/-! ### XOR programs -/

section Xor
variable {ι : Type*} [DecidableEq ι]

/-- A program of XOR gates between distinct registers. -/
def IsXorProg (p : Circuit.Program ι (ZMod 2)) : Prop :=
  ∀ g ∈ p, ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src

omit [DecidableEq ι] in
theorem IsXorProg.append {p q : Circuit.Program ι (ZMod 2)} (hp : IsXorProg p) (hq : IsXorProg q) :
    IsXorProg (p ++ q) := fun g hg => (List.mem_append.mp hg).elim (hp g) (hq g)

omit [DecidableEq ι] in
theorem IsXorProg.reverse {p : Circuit.Program ι (ZMod 2)} (hp : IsXorProg p) :
    IsXorProg p.reverse := fun g hg => hp g (List.mem_reverse.mp hg)

theorem add_run_add (dst src : ι) (c d : ι → ZMod 2) :
    (ReversibleFanout.add dst src).run (c + d) =
      (ReversibleFanout.add dst src).run c + (ReversibleFanout.add dst src).run d := by
  funext k
  simp only [ReversibleFanout.add_run, Pi.add_apply]
  by_cases hk : k = dst
  · subst hk; simp only [Function.update_self]; ring
  · simp [Function.update_of_ne hk]

/-- XOR programs are additive. -/
theorem xor_run_add {p : Circuit.Program ι (ZMod 2)} (hp : IsXorProg p) (c d : ι → ZMod 2) :
    Circuit.run p (c + d) = Circuit.run p c + Circuit.run p d := by
  induction p generalizing c d with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨dst, src, _, rfl⟩ := hp g (by simp)
    simp only [Circuit.run_cons]
    rw [add_run_add, ih (fun g hg => hp g (by simp [hg]))]

/-- The reversed program undoes an XOR program. -/
theorem xor_run_reverse {p : Circuit.Program ι (ZMod 2)} (hp : IsXorProg p) (c : ι → ZMod 2) :
    Circuit.run p.reverse (Circuit.run p c) = c := by
  induction p generalizing c with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨dst, src, hne, rfl⟩ := hp g (by simp)
    rw [List.reverse_cons, Circuit.run_append, Circuit.run_cons (ReversibleFanout.add dst src) gs,
      ih (fun g hg => hp g (by simp [hg]))]
    simp only [Circuit.run_cons, Circuit.run_nil]
    exact ReversibleFanout.add_involutive dst src hne c

end Xor

/-! ### Programs that never read their own targets -/

section Reads
variable {ι : Type*} [DecidableEq ι]

/-- No gate of `p` reads a register that some gate of `p` writes. -/
def ReadsUntouched (p : Circuit.Program ι (ZMod 2)) : Prop :=
  ∀ g ∈ p, ∀ g' ∈ p, ∀ t ∈ g'.terms, t.1 ≠ g.target

/-- The contribution of `p` to register `k`: the sum of its sources' values. -/
def contrib (p : Circuit.Program ι (ZMod 2)) (c : ι → ZMod 2) (k : ι) : ZMod 2 :=
  (p.map fun g => if g.target = k then (g.terms.map fun t => t.2 * c t.1).sum else 0).sum

theorem run_readsUntouched (p : Circuit.Program ι (ZMod 2)) (hp : ReadsUntouched p)
    (c : ι → ZMod 2) (k : ι) : Circuit.run p c k = c k + contrib p c k := by
  induction p generalizing c with
  | nil => simp [contrib]
  | cons g gs ih =>
    have hgs : ReadsUntouched gs := fun a ha b hb t ht =>
      hp a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) t ht
    rw [Circuit.run_cons, ih hgs]
    -- the sources of the remaining gates are not `g`'s target
    have hsame : contrib gs (g.run c) k = contrib gs c k := by
      unfold contrib
      congr 1
      apply List.map_congr_left
      intro g' hg'
      split_ifs
      · congr 1
        apply List.map_congr_left
        intro t ht
        rw [Circuit.Gate.run, Function.update_of_ne (hp g (by simp) g' (by simp [hg']) t ht)]
      · rfl
    rw [hsame]
    simp only [contrib, List.map_cons, List.sum_cons, Circuit.Gate.run]
    by_cases hk : k = g.target
    · subst hk
      simp only [Function.update_self, ite_true]
      ring
    · rw [Function.update_of_ne hk, ite_eq_right (Ne.symm hk), zero_add]

theorem contrib_add (p : Circuit.Program ι (ZMod 2)) (c d : ι → ZMod 2) (k : ι) :
    contrib p (c + d) k = contrib p c k + contrib p d k := by
  unfold contrib
  rw [← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro g _
  split_ifs
  · rw [← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Pi.add_apply]
    ring
  · simp

end Reads

/-! ### Programs on mapped registers -/

section Map
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- A gate on the registers `e i`. -/
def gateMap (e : ι → κ) (g : Circuit.Gate ι (ZMod 2)) : Circuit.Gate κ (ZMod 2) :=
  ⟨e g.target, g.terms.map fun t => (e t.1, t.2)⟩

theorem gateMap_run {e : ι → κ} (he : Function.Injective e) (g : Circuit.Gate ι (ZMod 2))
    (d : κ → ZMod 2) :
    (∀ i, (gateMap e g).run d (e i) = g.run (d ∘ e) i) ∧
      ∀ k, (∀ i, e i ≠ k) → (gateMap e g).run d k = d k := by
  have hsum : ((g.terms.map fun t => (e t.1, t.2)).map fun t => t.2 * d t.1).sum =
      (g.terms.map fun t => t.2 * (d ∘ e) t.1).sum := by
    rw [List.map_map]
    rfl
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · simp only [gateMap, Circuit.Gate.run, hsum]
    by_cases h : i = g.target
    · subst h
      simp
    · rw [Function.update_of_ne (fun h' => h (he h')), Function.update_of_ne h]
      rfl
  · simp only [gateMap, Circuit.Gate.run]
    exact Function.update_of_ne (Ne.symm (hk _)) _ _

/-- A program on the registers `e i` acts there as the program, and leaves the rest. -/
theorem run_map {e : ι → κ} (he : Function.Injective e) :
    ∀ (p : Circuit.Program ι (ZMod 2)) (d : κ → ZMod 2),
      (∀ i, Circuit.run (p.map (gateMap e)) d (e i) = Circuit.run p (d ∘ e) i) ∧
        ∀ k, (∀ i, e i ≠ k) → Circuit.run (p.map (gateMap e)) d k = d k
  | [], _ => ⟨fun _ => rfl, fun _ _ => rfl⟩
  | g :: p, d => by
    obtain ⟨hin, hout⟩ := run_map he p ((gateMap e g).run d)
    have hcomp : (gateMap e g).run d ∘ e = g.run (d ∘ e) := funext (gateMap_run he g d).1
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · rw [List.map_cons, Circuit.run_cons, hin, hcomp]
      rfl
    · rw [List.map_cons, Circuit.run_cons, hout k hk, (gateMap_run he g d).2 k hk]

end Map

/-! ### The local word on arbitrary contents -/

namespace Dag
variable (D : Dag)

theorem opGate_xor {op : Op} (h : op.Distinct) :
    ∃ dst src, dst ≠ src ∧ opGate op = ReversibleFanout.add dst src := by
  cases op with
  | src s n => exact ⟨_, _, by simp, rfl⟩
  | add p o k => exact ⟨_, _, by simpa [Op.Distinct] using h, rfl⟩
  | copy p f k => exact ⟨_, _, by simpa [Op.Distinct, eq_comm] using h, rfl⟩

theorem compile_ops_ok (hv : D.Valid) :
    ∀ op ∈ D.compile.ops, op.Distinct ∧ op.SlotsLt D.compile.next :=
  (D.inv_compileTo hv (fun _ => 0) D.N le_rfl).ops_ok

theorem opsGates_xor (hv : D.Valid) : IsXorProg D.opsGates := by
  intro g hg
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hg
  exact opGate_xor (D.compile_ops_ok hv op hop).1

theorem sideGates_xor (hv : D.Valid) : IsXorProg D.sideGates := by
  intro g hg
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hg
  exact opGate_xor (D.compile_ops_ok hv op (List.mem_filter.mp hop).1).1

theorem rootReads_xor (targets : ℕ → List ℕ) : IsXorProg (D.rootReads targets) := by
  intro g hg
  simp only [rootReads, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨j, _, T, _, rfl⟩ := hg
  exact ⟨_, _, by simp, rfl⟩

theorem rootReads_untouched (targets : ℕ → List ℕ) : ReadsUntouched (D.rootReads targets) := by
  intro g hg g' hg' t ht
  simp only [rootReads, List.mem_flatMap, List.mem_map] at hg hg'
  obtain ⟨j, _, T, _, rfl⟩ := hg
  obtain ⟨j', _, T', _, rfl⟩ := hg'
  simp [ReversibleFanout.add] at ht
  rw [ht]
  simp [ReversibleFanout.add]

/-! ### Registers that a program leaves alone -/

/-- `c` vanishes on every target and source of `p`'s gates. -/
def Silent (p : Circuit.Program Reg (ZMod 2)) (c : Reg → ZMod 2) : Prop :=
  ∀ g ∈ p, c g.target = 0 ∧ ∀ t ∈ g.terms, c t.1 = 0

theorem run_silent (p : Circuit.Program Reg (ZMod 2)) (c : Reg → ZMod 2) (h : Silent p c) :
    Circuit.run p c = c := by
  induction p with
  | nil => rfl
  | cons g gs ih =>
    rw [Circuit.run_cons]
    have hg : g.run c = c := by
      obtain ⟨ht, hs⟩ := h g (by simp)
      rw [Circuit.Gate.run]
      have hsum : (g.terms.map fun t => t.2 * c t.1).sum = 0 := by
        apply List.sum_eq_zero
        intro a ha
        obtain ⟨t, htm, rfl⟩ := List.mem_map.mp ha
        rw [hs t htm, mul_zero]
      rw [hsum, add_zero]
      exact Function.update_eq_self _ _
    rw [hg]
    exact ih (fun g' hg' => h g' (by simp [hg']))

theorem opGate_target (op : Op) : (opGate op).target.isAux = true := by
  cases op <;> rfl

theorem opGate_terms (op : Op) : ∀ t ∈ (opGate op).terms, t.1.isY = false := by
  cases op <;> simp [opGate, ReversibleFanout.add, Reg.isY]

theorem side_terms {op : Op} (h : op.isSrc = false) : ∀ t ∈ (opGate op).terms, t.1.isAux = true := by
  cases op <;> simp_all [opGate, ReversibleFanout.add, Reg.isAux, Op.isSrc]

/-- The compiled gates never touch the targets: they act on `x` and `aux` only. -/
theorem opsGates_silent_y (c : Reg → ZMod 2) (hc : ∀ r, r.isY = false → c r = 0) :
    Silent D.opsGates c := by
  intro g hg
  obtain ⟨op, _, rfl⟩ := List.mem_map.mp hg
  refine ⟨hc _ (by have := opGate_target op; revert this; cases (opGate op).target <;> simp [Reg.isY, Reg.isAux]),
    fun t ht => hc _ (opGate_terms op t ht)⟩

theorem sideGates_silent (c : Reg → ZMod 2) (hc : ∀ r, r.isAux = true → c r = 0) :
    Silent D.sideGates c := by
  intro g hg
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hg
  exact ⟨hc _ (opGate_target op), fun t ht => hc _ (side_terms (by simpa using (List.mem_filter.mp hop).2) t ht)⟩

/-! ### The compiled gates and the compiler's slots -/

theorem opGate_run_aux (op : Op) (c : Reg → ZMod 2) (s : ℕ) :
    (opGate op).run c (.aux s) = op.run (fun n => c (.x n)) (fun s => c (.aux s)) s := by
  cases op with
  | src t n =>
    simp only [opGate, ReversibleFanout.add_run, Op.run]
    by_cases h : s = t
    · subst h; simp
    · rw [Function.update_of_ne (by simpa using h), Function.update_of_ne h]
  | add p o k =>
    simp only [opGate, ReversibleFanout.add_run, Op.run]
    by_cases h : s = p
    · subst h; simp
    · rw [Function.update_of_ne (by simpa using h), Function.update_of_ne h]
  | copy p f k =>
    simp only [opGate, ReversibleFanout.add_run, Op.run]
    by_cases h : s = f
    · subst h; simp
    · rw [Function.update_of_ne (by simpa using h), Function.update_of_ne h]

theorem opGate_run_x (op : Op) (c : Reg → ZMod 2) (n : ℕ) : (opGate op).run c (.x n) = c (.x n) := by
  cases op <;> simp [opGate, ReversibleFanout.add_run, Function.update_of_ne]

/-- The gates of a list of operations act on the side slots as the operations. -/
theorem run_ops_bridge : ∀ (L : List Op) (c : Reg → ZMod 2),
    (∀ s, Circuit.run (L.map opGate) c (.aux s) = runOps (fun n => c (.x n)) L (fun s => c (.aux s)) s) ∧
      ∀ n, Circuit.run (L.map opGate) c (.x n) = c (.x n)
  | [], c => ⟨fun _ => rfl, fun _ => rfl⟩
  | op :: L, c => by
    obtain ⟨ha, hx⟩ := run_ops_bridge L ((opGate op).run c)
    have hx' : (fun n => (opGate op).run c (.x n)) = fun n => c (.x n) := funext (opGate_run_x op c)
    have ha' : (fun s => (opGate op).run c (.aux s)) =
        op.run (fun n => c (.x n)) (fun s => c (.aux s)) := funext (opGate_run_aux op c)
    refine ⟨fun s => ?_, fun n => ?_⟩
    · rw [List.map_cons, Circuit.run_cons, ha, hx', ha']
      rfl
    · rw [List.map_cons, Circuit.run_cons, hx, opGate_run_x]

/-- With zero sources, the source gates do nothing. -/
theorem run_ops_srcfree : ∀ (L : List Op) (c : Reg → ZMod 2), (∀ n, c (.x n) = 0) →
    Circuit.run (L.map opGate) c = Circuit.run ((L.filter fun op => !op.isSrc).map opGate) c
  | [], _, _ => rfl
  | op :: L, c, hc => by
    have hx : ∀ n, (opGate op).run c (.x n) = 0 := fun n => by rw [opGate_run_x]; exact hc n
    cases op with
    | src t n =>
      have : (opGate (.src t n)).run c = c := by
        simp only [opGate, ReversibleFanout.add_run, hc, add_zero, Function.update_eq_self]
      simp only [List.map_cons, Circuit.run_cons, List.filter_cons, Op.isSrc, Bool.not_true,
        Bool.false_eq_true, ite_false]
      rw [this]
      exact run_ops_srcfree L c hc
    | add p o k =>
      simp only [List.map_cons, Circuit.run_cons, List.filter_cons, Op.isSrc, Bool.not_false,
        ite_true]
      exact run_ops_srcfree L _ hx
    | copy p f k =>
      simp only [List.map_cons, Circuit.run_cons, List.filter_cons, Op.isSrc, Bool.not_false,
        ite_true]
      exact run_ops_srcfree L _ hx

/-! ### Root reads -/

/-- The increments of the root reads: the targets gain their reads, nothing else changes. -/
def readDelta (targets : ℕ → List ℕ) (c : Reg → ZMod 2) : Reg → ZMod 2
  | .y T => contrib (D.rootReads targets) c (.y T)
  | _ => 0

theorem contrib_not_target (p : Circuit.Program Reg (ZMod 2)) (c : Reg → ZMod 2) (r : Reg)
    (h : ∀ g ∈ p, g.target ≠ r) : contrib p c r = 0 := by
  unfold contrib
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
  rw [ite_eq_right (h g hg)]

theorem rootReads_target (targets : ℕ → List ℕ) : ∀ g ∈ D.rootReads targets, g.target.isY = true := by
  intro g hg
  simp only [rootReads, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨j, _, T, _, rfl⟩ := hg
  rfl

theorem rootReads_source (targets : ℕ → List ℕ) :
    ∀ g ∈ D.rootReads targets, ∀ t ∈ g.terms, t.1.isAux = true := by
  intro g hg t ht
  simp only [rootReads, List.mem_flatMap, List.mem_map] at hg
  obtain ⟨j, _, T, _, rfl⟩ := hg
  simp only [ReversibleFanout.add, List.mem_singleton] at ht
  rw [ht]
  rfl

theorem run_rootReads (targets : ℕ → List ℕ) (c : Reg → ZMod 2) :
    Circuit.run (D.rootReads targets) c = c + D.readDelta targets c := by
  funext r
  rw [run_readsUntouched _ (D.rootReads_untouched targets), Pi.add_apply]
  congr 1
  cases r with
  | y T => rfl
  | x n =>
    exact contrib_not_target _ c _ fun g hg h => by
      have := D.rootReads_target targets g hg; rw [h] at this; cases this
  | aux s =>
    exact contrib_not_target _ c _ fun g hg h => by
      have := D.rootReads_target targets g hg; rw [h] at this; cases this

theorem contrib_congr (p : Circuit.Program Reg (ZMod 2)) {c c' : Reg → ZMod 2}
    (h : ∀ g ∈ p, ∀ t ∈ g.terms, c t.1 = c' t.1) (r : Reg) : contrib p c r = contrib p c' r := by
  unfold contrib
  congr 1
  apply List.map_congr_left
  intro g hg
  split_ifs
  · congr 1
    apply List.map_congr_left
    intro t ht
    rw [h g hg t ht]
  · rfl

theorem readDelta_add (targets : ℕ → List ℕ) (c d : Reg → ZMod 2) :
    D.readDelta targets (c + d) = D.readDelta targets c + D.readDelta targets d := by
  funext r
  cases r <;> simp [readDelta, contrib_add]

/-- The read increments depend only on the side slots. -/
theorem readDelta_aux (targets : ℕ → List ℕ) (c : Reg → ZMod 2) :
    D.readDelta targets c = D.readDelta targets (part Reg.isAux c) := by
  funext r
  cases r with
  | y T =>
    exact contrib_congr _ (fun g hg t ht => by
      simp [part, D.rootReads_source targets g hg t ht]) _
  | _ => rfl

theorem readDelta_off_y (targets : ℕ → List ℕ) (c : Reg → ZMod 2) (r : Reg)
    (h : r.isY = false) : D.readDelta targets c r = 0 := by
  cases r <;> simp_all [readDelta, Reg.isY]

/-! ### The word -/

/-- `d` vanishes off the targets. -/
def YOnly (d : Reg → ZMod 2) : Prop := ∀ r, r.isY = false → d r = 0

theorem YOnly.add {d e : Reg → ZMod 2} (hd : YOnly d) (he : YOnly e) : YOnly (d + e) :=
  fun r hr => by rw [Pi.add_apply, hd r hr, he r hr, add_zero]

theorem Silent.reverse {p : Circuit.Program Reg (ZMod 2)} {c : Reg → ZMod 2} (h : Silent p c) :
    Silent p.reverse c := fun g hg => h g (List.mem_reverse.mp hg)

theorem opsGates_yOnly {d : Reg → ZMod 2} (hd : YOnly d) : Circuit.run D.opsGates d = d :=
  run_silent _ d (D.opsGates_silent_y d hd)

theorem opsGates_reverse_yOnly {d : Reg → ZMod 2} (hd : YOnly d) :
    Circuit.run D.opsGates.reverse d = d :=
  run_silent _ d (D.opsGates_silent_y d hd).reverse

theorem sideGates_aux_free {d : Reg → ZMod 2} (hd : ∀ r, r.isAux = true → d r = 0) :
    Circuit.run D.sideGates d = d :=
  run_silent _ d (D.sideGates_silent d hd)

theorem yOnly_aux_free {d : Reg → ZMod 2} (hd : YOnly d) : ∀ r, r.isAux = true → d r = 0 :=
  fun r hr => hd r (by cases r <;> simp_all [Reg.isAux, Reg.isY])

theorem readDelta_yOnly (targets : ℕ → List ℕ) (c : Reg → ZMod 2) : YOnly (D.readDelta targets c) :=
  D.readDelta_off_y targets c

theorem readDelta_zero (targets : ℕ → List ℕ) : D.readDelta targets 0 = 0 := by
  funext r
  cases r <;> simp [readDelta, contrib]

/-- The read increments vanish on contents without side slots. -/
theorem readDelta_aux_free (targets : ℕ → List ℕ) {d : Reg → ZMod 2}
    (hd : ∀ r, r.isAux = true → d r = 0) : D.readDelta targets d = 0 := by
  rw [D.readDelta_aux, show part Reg.isAux d = 0 from funext fun r => by
    by_cases h : r.isAux = true
    · simp [part, h, hd r h]
    · simp [part, h], readDelta_zero]

theorem two_cancel (f g : Reg → ZMod 2) : f + (g + f) = g := by
  funext r
  simp only [Pi.add_apply]
  generalize f r = a
  generalize g r = b
  revert a b
  decide

theorem part_x_aux (c : Reg → ZMod 2) : ∀ r, r.isAux = true → part Reg.isX c r = 0
  | .aux _, _ => by simp [part, Reg.isX]
  | .x _, hr => by simp [Reg.isAux] at hr
  | .y _, hr => by simp [Reg.isAux] at hr

theorem part_rest_x (c : Reg → ZMod 2) (n : ℕ) : (part Reg.isY c + part Reg.isAux c) (.x n) = 0 := by
  simp [part, Reg.isY, Reg.isAux]

/-- **The local word on arbitrary contents.** The word adds the read increments of the compiled
operations on the sources alone. -/
theorem word_run (hv : D.Valid) (targets : ℕ → List ℕ) (c : Reg → ZMod 2) :
    Circuit.run (D.word targets) c =
      c + D.readDelta targets (Circuit.run D.opsGates (part Reg.isX c)) := by
  have hA := D.sideGates_xor hv
  have hB := D.opsGates_xor hv
  have hAr : ∀ d, YOnly d → Circuit.run D.sideGates.reverse d = d := fun d hd =>
    run_silent _ d (D.sideGates_silent d (yOnly_aux_free hd)).reverse
  have hδδ : ∀ d, D.readDelta targets (D.readDelta targets d) = 0 := fun d =>
    D.readDelta_aux_free targets (yOnly_aux_free (D.readDelta_yOnly targets d))
  -- the six parts
  have h3 : Circuit.run D.sideGates.reverse
      (Circuit.run (D.rootReads targets) (Circuit.run D.sideGates c)) =
      c + D.readDelta targets (Circuit.run D.sideGates c) := by
    rw [run_rootReads, xor_run_add hA.reverse, xor_run_reverse hA, hAr _ (D.readDelta_yOnly _ _)]
  have h4 : Circuit.run D.opsGates (c + D.readDelta targets (Circuit.run D.sideGates c)) =
      Circuit.run D.opsGates c + D.readDelta targets (Circuit.run D.sideGates c) := by
    rw [xor_run_add hB, D.opsGates_yOnly (D.readDelta_yOnly _ _)]
  have h5 : Circuit.run (D.rootReads targets)
      (Circuit.run D.opsGates c + D.readDelta targets (Circuit.run D.sideGates c)) =
      Circuit.run D.opsGates c + (D.readDelta targets (Circuit.run D.sideGates c) +
        D.readDelta targets (Circuit.run D.opsGates c)) := by
    rw [run_rootReads, D.readDelta_add, hδδ, add_zero]
    abel
  have hsum : YOnly (D.readDelta targets (Circuit.run D.sideGates c) +
      D.readDelta targets (Circuit.run D.opsGates c)) :=
    (D.readDelta_yOnly _ _).add (D.readDelta_yOnly _ _)
  have h6 : Circuit.run D.opsGates.reverse (Circuit.run D.opsGates c +
      (D.readDelta targets (Circuit.run D.sideGates c) +
        D.readDelta targets (Circuit.run D.opsGates c))) =
      c + (D.readDelta targets (Circuit.run D.sideGates c) +
        D.readDelta targets (Circuit.run D.opsGates c)) := by
    rw [xor_run_add hB.reverse, xor_run_reverse hB, D.opsGates_reverse_yOnly hsum]
  -- the garbage cancels
  have hkey : ∀ c' : Reg → ZMod 2, (∀ n, c' (.x n) = 0) →
      D.readDelta targets (Circuit.run D.sideGates (part Reg.isX c + c')) +
        D.readDelta targets (Circuit.run D.opsGates (part Reg.isX c + c')) =
      D.readDelta targets (Circuit.run D.opsGates (part Reg.isX c)) := by
    intro c' hc'
    have hB' : Circuit.run D.opsGates c' = Circuit.run D.sideGates c' := run_ops_srcfree _ c' hc'
    rw [xor_run_add hA, xor_run_add hB, D.sideGates_aux_free (part_x_aux c), hB', D.readDelta_add,
      D.readDelta_add, D.readDelta_aux_free targets (part_x_aux c), zero_add,
      two_cancel]
  have hc : c = part Reg.isX c + (part Reg.isY c + part Reg.isAux c) := by
    rw [← add_assoc]; exact part_split c
  simp only [word, Circuit.run_append]
  rw [h3, h4, h5, h6]
  congr 1
  conv_lhs => rw [hc]
  exact hkey _ (part_rest_x c)

/-! ### Passes -/

/-- A program reads the side slots into the targets as the root reads do. -/
def ReadsLike (targets : ℕ → List ℕ) (R' : Circuit.Program Reg (ZMod 2)) : Prop :=
  ∀ c, Circuit.run R' c = c + D.readDelta targets c

/-- **A pass**: compute, read, uncompute. -/
theorem pass_run (targets : ℕ → List ℕ) {P R' : Circuit.Program Reg (ZMod 2)} (hP : IsXorProg P)
    (hPy : ∀ d, YOnly d → Circuit.run P.reverse d = d) (hR : D.ReadsLike targets R')
    (c : Reg → ZMod 2) :
    Circuit.run (P ++ R' ++ P.reverse) c = c + D.readDelta targets (Circuit.run P c) := by
  rw [Circuit.run_append, Circuit.run_append, hR, xor_run_add hP.reverse, xor_run_reverse hP,
    hPy _ (D.readDelta_yOnly _ _)]

/-- **Two passes** add both increments, in either order. -/
theorem two_passes (targets : ℕ → List ℕ) {P Q R' : Circuit.Program Reg (ZMod 2)}
    (hQ : IsXorProg Q) (hQy : ∀ d, YOnly d → Circuit.run Q d = d)
    (hQr : ∀ d, YOnly d → Circuit.run Q.reverse d = d) (hR : D.ReadsLike targets R')
    (c : Reg → ZMod 2) :
    Circuit.run (Q ++ R' ++ Q.reverse) (c + D.readDelta targets (Circuit.run P c)) =
      c + (D.readDelta targets (Circuit.run P c) + D.readDelta targets (Circuit.run Q c)) := by
  rw [D.pass_run targets hQ hQr hR, xor_run_add hQ, hQy _ (D.readDelta_yOnly _ _),
    D.readDelta_add,
    D.readDelta_aux_free targets (yOnly_aux_free (D.readDelta_yOnly targets _)), add_zero]
  abel

theorem readsLike_perm (targets : ℕ → List ℕ) {R' : Circuit.Program Reg (ZMod 2)}
    (h : R'.Perm (D.rootReads targets)) : D.ReadsLike targets R' := fun c => by
  rw [← D.run_rootReads]
  have hu := D.rootReads_untouched targets
  have hu' : ReadsUntouched R' := fun g hg g' hg' => hu g (h.subset hg) g' (h.subset hg')
  funext r
  rw [run_readsUntouched _ hu', run_readsUntouched _ hu]
  unfold contrib
  rw [(h.map _).sum_eq]

theorem sideGates_reverse_yOnly {d : Reg → ZMod 2} (hd : YOnly d) :
    Circuit.run D.sideGates.reverse d = d :=
  run_silent _ d (D.sideGates_silent d (yOnly_aux_free hd)).reverse

theorem sideGates_yOnly {d : Reg → ZMod 2} (hd : YOnly d) : Circuit.run D.sideGates d = d :=
  D.sideGates_aux_free (yOnly_aux_free hd)

/-- The side-slot garbage of the two passes cancels. -/
theorem garbage_cancel (hv : D.Valid) (targets : ℕ → List ℕ) (c : Reg → ZMod 2) :
    D.readDelta targets (Circuit.run D.sideGates c) + D.readDelta targets (Circuit.run D.opsGates c) =
      D.readDelta targets (Circuit.run D.opsGates (part Reg.isX c)) := by
  have hA := D.sideGates_xor hv
  have hB := D.opsGates_xor hv
  have hc : c = part Reg.isX c + (part Reg.isY c + part Reg.isAux c) := by
    rw [← add_assoc]; exact part_split c
  have hB' : Circuit.run D.opsGates (part Reg.isY c + part Reg.isAux c) =
      Circuit.run D.sideGates (part Reg.isY c + part Reg.isAux c) :=
    run_ops_srcfree _ _ (part_rest_x c)
  conv_lhs => rw [hc]
  rw [xor_run_add hA, xor_run_add hB, D.sideGates_aux_free (part_x_aux c), hB', D.readDelta_add,
    D.readDelta_add, D.readDelta_aux_free targets (part_x_aux c), zero_add, two_cancel]

theorem contrib_flatMap (L : List ℕ) (f : ℕ → Circuit.Program Reg (ZMod 2)) (d : Reg → ZMod 2)
    (k : Reg) : contrib (L.flatMap f) d k = (L.map fun j => contrib (f j) d k).sum := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    unfold contrib at ih ⊢
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem contrib_reads (Ts : List ℕ) (s : ℕ) (d : Reg → ZMod 2) (T : ℕ) :
    contrib (Ts.map fun T' => ReversibleFanout.add (Reg.y T') (Reg.aux s)) d (.y T) =
      (Ts.count T : ZMod 2) * d (.aux s) := by
  induction Ts with
  | nil => simp [contrib]
  | cons T' Ts ih =>
    simp only [contrib, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, List.count_cons]
    by_cases h : T' = T
    · subst h; simp [ReversibleFanout.add]; ring
    · simp [ReversibleFanout.add, h]

/-- The read increment of a target: each root's slot, counted by the root's targets. -/
theorem readDelta_y (targets : ℕ → List ℕ) (d : Reg → ZMod 2) (T : ℕ) :
    D.readDelta targets d (.y T) = ((List.range D.rootCount).map fun j =>
      ((targets j).count T : ZMod 2) * d (.aux (D.compile.pend (.root j)))).sum := by
  simp only [readDelta, rootReads]
  rw [contrib_flatMap]
  congr 1
  apply List.map_congr_left
  intro j _
  exact contrib_reads _ _ _ _

/-- **The local word, on the targets.** Each target gains the values of its roots on the sources;
sources and side slots end unchanged. -/
theorem word_run_y (hv : D.Valid) (targets : ℕ → List ℕ) (c : Reg → ZMod 2) (T : ℕ) :
    Circuit.run (D.word targets) c (.y T) = c (.y T) + ((List.range D.rootCount).map fun j =>
      ((targets j).count T : ZMod 2) * D.val (fun n => c (.x n)) (D.rootNode j)).sum := by
  rw [D.word_run hv, Pi.add_apply, readDelta_y]
  congr 1
  congr 1
  apply List.map_congr_left
  intro j hj
  congr 1
  rw [opsGates, (run_ops_bridge _ _).1, ← (D.compile_correct hv _ j (List.mem_range.mp hj)).2]
  have hx : (fun n => part Reg.isX c (.x n)) = fun n => c (.x n) := funext fun n => by
    simp [part, Reg.isX]
  have ha : (fun s => part Reg.isX c (.aux s)) = fun _ => 0 := funext fun s => by
    simp [part, Reg.isX]
  rw [hx, ha]
  rfl

theorem word_run_off_y (hv : D.Valid) (targets : ℕ → List ℕ) (c : Reg → ZMod 2) (r : Reg)
    (hr : r.isY = false) : Circuit.run (D.word targets) c r = c r := by
  rw [D.word_run hv, Pi.add_apply, D.readDelta_off_y targets _ r hr, add_zero]

end Dag

end IntegerMultBounds.MathlibTM2.M8.Local
