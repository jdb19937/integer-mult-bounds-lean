module

public import IntegerMultBounds.Networks.Certificates.T16.Streams.All
public import IntegerMultBounds.Networks.Certificates.T16.Streams.PortsCheck

/-! The T16 parent node at the level of unit operations. Units are the 14,336 data families,
numbered `896 r + 112 (2p + side) + a` for replica `r`, pair `p`, side `side` and port `a`, and
eight private scratch units. Every template event, expanded for each replica and port, becomes
unit operations on that group's eight families; operations of different groups act on different
units. Restricted to one group, the node is therefore exactly that group's checked stream
program, and every data family ends with `C_all` applied to its input. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Streams

open Multiplicative

/-- Data families and private scratch units. -/
abbrev NodeUnit := Fin 14336 ⊕ Fin 8

/-- The family of stream `i` of replica `r` and port `a`. -/
def famIdx (r a : ℕ) (i : Fin 8) : ℕ := 896 * r + 112 * i.val + a

def streamUnit (r a : ℕ) (i : Fin 8) : NodeUnit :=
  .inl ⟨famIdx r a i % 14336, Nat.mod_lt _ (by decide)⟩

theorem famIdx_lt {r a : ℕ} (hr : r < 16) (ha : a < 112) (i : Fin 8) : famIdx r a i < 14336 := by
  unfold famIdx; have := i.isLt; omega

theorem streamUnit_inj {r a r' a' : ℕ} (hr : r < 16) (ha : a < 112) (hr' : r' < 16)
    (ha' : a' < 112) {i i' : Fin 8} (h : streamUnit r a i = streamUnit r' a' i') :
    r = r' ∧ a = a' ∧ i = i' := by
  simp only [streamUnit, Sum.inl.injEq, Fin.mk.injEq] at h
  rw [Nat.mod_eq_of_lt (famIdx_lt hr ha i), Nat.mod_eq_of_lt (famIdx_lt hr' ha' i')] at h
  unfold famIdx at h
  have hi := i.isLt
  have hi' := i'.isLt
  refine ⟨by omega, by omega, Fin.ext (by omega)⟩

/-- One operation on node units. Phases carry the port whose operators they use. -/
inductive UnitOp where
  | phase (u : NodeUnit) (port : ℕ) (v : Vec)
  | shear (d s : NodeUnit) (c : ℤ)
  | exchange (x y : NodeUnit)

variable {S : Type*} [AddCommGroup S] [Module ℂ S]

def UnitOp.run (M : ℕ → Op S) : UnitOp → (NodeUnit → S) → (NodeUnit → S)
  | .phase u a v, y => Function.update y u (M a (ofAdd v.toFun) (y u))
  | .shear d s c, y => Function.update y d (y d + c • y s)
  | .exchange x w, y => Function.update (Function.update y x (y w)) w (-y x)

def runUnits (M : ℕ → Op S) : List UnitOp → (NodeUnit → S) → (NodeUnit → S)
  | [], y => y
  | o :: os, y => runUnits M os (o.run M y)

/-- A stream event of group `(r, a)` as a unit operation. -/
def toUnitOp (r a : ℕ) : Event → UnitOp
  | .phase s v => .phase (streamUnit r a s) a v
  | .shear d s c => .shear (streamUnit r a d) (streamUnit r a s) c
  | .exchange p => .exchange (streamUnit r a (pairX p)) (streamUnit r a (pairY p))

def portData (a : ℕ) : PortData := ports.getD a ⟨[], (0, 0), 0, []⟩

def groupData (r a : ℕ) : GroupData := (groups r).getD a ⟨[], []⟩

/-- All unit operations of one template event: each group's expansion, in group order. -/
def eventOps (te : TEvent) : List UnitOp :=
  (List.range 16).flatMap fun r => (List.range 112).flatMap fun a =>
    (expand (portData a) (groupData r a) r localPair localReverse te).map (toUnitOp r a)

/-- The node at the level of unit operations. -/
def nodeOps : List UnitOp := template.flatMap eventOps

/-! ### Restriction to one group -/

theorem view_toUnitOp (M : ℕ → Op S) {r a : ℕ} (hr : r < 16) (ha : a < 112) (e : Event)
    (y : NodeUnit → S) :
    (fun i => (toUnitOp r a e).run M y (streamUnit r a i)) =
      e.run (M a) (fun i => y (streamUnit r a i)) := by
  have inj : ∀ {i j : Fin 8}, streamUnit r a i = streamUnit r a j → i = j :=
    fun h => (streamUnit_inj hr ha hr ha h).2.2
  funext i
  cases e with
  | phase s v =>
    simp only [toUnitOp, UnitOp.run, Event.run]
    by_cases h : i = s
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (inj e)), Function.update_of_ne h]
  | shear d s c =>
    simp only [toUnitOp, UnitOp.run, Event.run]
    by_cases h : i = d
    · subst h; simp
    · rw [Function.update_of_ne (fun e => h (inj e)), Function.update_of_ne h]
  | exchange p =>
    simp only [toUnitOp, UnitOp.run, Event.run]
    by_cases hy : i = pairY p
    · subst hy; simp
    · by_cases hx : i = pairX p
      · subst hx
        rw [Function.update_of_ne (fun e => hy (inj e)), Function.update_self,
          Function.update_of_ne hy, Function.update_self]
      · rw [Function.update_of_ne (fun e => hy (inj e)), Function.update_of_ne (fun e => hx (inj e)),
          Function.update_of_ne hy, Function.update_of_ne hx]

/-- Operations of other groups leave a group's view unchanged. -/
theorem view_other (M : ℕ → Op S) {r a r' a' : ℕ} (hr : r < 16) (ha : a < 112) (hr' : r' < 16)
    (ha' : a' < 112) (hne : ¬(r' = r ∧ a' = a)) (e : Event) (y : NodeUnit → S) :
    (fun i => (toUnitOp r' a' e).run M y (streamUnit r a i)) = fun i => y (streamUnit r a i) := by
  have hdiff : ∀ i j, streamUnit r a i ≠ streamUnit r' a' j := by
    intro i j h
    obtain ⟨h1, h2, -⟩ := streamUnit_inj hr ha hr' ha' h
    exact hne ⟨h1.symm, h2.symm⟩
  funext i
  cases e with
  | phase s v =>
    simp only [toUnitOp, UnitOp.run]
    rw [Function.update_of_ne (hdiff i s)]
  | shear d s c =>
    simp only [toUnitOp, UnitOp.run]
    rw [Function.update_of_ne (hdiff i d)]
  | exchange p =>
    simp only [toUnitOp, UnitOp.run]
    rw [Function.update_of_ne (hdiff i _), Function.update_of_ne (hdiff i _)]

theorem view_map_other (M : ℕ → Op S) {r a r' a' : ℕ} (hr : r < 16) (ha : a < 112) (hr' : r' < 16)
    (ha' : a' < 112) (hne : ¬(r' = r ∧ a' = a)) (es : List Event) (y : NodeUnit → S) :
    (fun i => runUnits M (es.map (toUnitOp r' a')) y (streamUnit r a i)) =
      fun i => y (streamUnit r a i) := by
  induction es generalizing y with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, runUnits]
    rw [ih]
    exact view_other M hr ha hr' ha' hne e y

theorem view_map_self (M : ℕ → Op S) {r a : ℕ} (hr : r < 16) (ha : a < 112) (es : List Event)
    (y : NodeUnit → S) :
    (fun i => runUnits M (es.map (toUnitOp r a)) y (streamUnit r a i)) =
      run (M a) es (fun i => y (streamUnit r a i)) := by
  induction es generalizing y with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, runUnits, run]
    rw [ih, view_toUnitOp M hr ha e y]

theorem runUnits_append (M : ℕ → Op S) (p q : List UnitOp) (y : NodeUnit → S) :
    runUnits M (p ++ q) y = runUnits M q (runUnits M p y) := by
  induction p generalizing y with
  | nil => rfl
  | cons o p ih => exact ih _

theorem runUnits_flatMap {α : Type*} (M : ℕ → Op S) (l : List α) (f : α → List UnitOp)
    (y : NodeUnit → S) :
    runUnits M (l.flatMap f) y = l.foldl (fun y x => runUnits M (f x) y) y := by
  induction l generalizing y with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, runUnits_append, ih]; rfl

/-- One template event, viewed from one group: only that group's expansion acts. -/
theorem view_eventOps (M : ℕ → Op S) {r a : ℕ} (hr : r < 16) (ha : a < 112) (te : TEvent)
    (y : NodeUnit → S) :
    (fun i => runUnits M (eventOps te) y (streamUnit r a i)) =
      run (M a) (expand (portData a) (groupData r a) r localPair localReverse te)
        (fun i => y (streamUnit r a i)) := by
  -- induct over the replica and port loops, tracking the view
  have inner : ∀ (r' : ℕ), r' < 16 → ∀ (as : List ℕ), (∀ a' ∈ as, a' < 112) → as.Nodup →
      ∀ y : NodeUnit → S,
      (fun i => runUnits M (as.flatMap fun a' =>
        (expand (portData a') (groupData r' a') r' localPair localReverse te).map (toUnitOp r' a'))
        y (streamUnit r a i)) =
      if r' = r ∧ a ∈ as then
        run (M a) (expand (portData a) (groupData r a) r localPair localReverse te)
          (fun i => y (streamUnit r a i))
      else fun i => y (streamUnit r a i) := by
    intro r' hr' as has hnd
    induction as with
    | nil => intro y; simp only [List.flatMap_nil, List.not_mem_nil, and_false, ite_false]; rfl
    | cons a' as ih =>
      intro y
      have has' : ∀ x ∈ as, x < 112 := fun x hx => has x (List.mem_cons_of_mem _ hx)
      have hnd' := (List.nodup_cons.mp hnd)
      rw [List.flatMap_cons, runUnits_append]
      rw [ih has' hnd'.2]
      by_cases hsame : r' = r ∧ a' = a
      · obtain ⟨rfl, rfl⟩ := hsame
        have hnot : a' ∉ as := hnd'.1
        simp only [hnot, and_false, ite_false, true_and, List.mem_cons, true_or, ite_true]
        exact view_map_self M hr ha _ y
      · have ho := view_map_other M hr ha hr' (has a' List.mem_cons_self) hsame
          (expand (portData a') (groupData r' a') r' localPair localReverse te) y
        by_cases hin : r' = r ∧ a ∈ as
        · have hmem : r' = r ∧ a ∈ a' :: as := ⟨hin.1, List.mem_cons_of_mem _ hin.2⟩
          rw [show (if r' = r ∧ a ∈ as then run (M a) (expand (portData a) (groupData r a) r
              localPair localReverse te) (fun i => runUnits M ((expand (portData a') (groupData r' a') r'
              localPair localReverse te).map (toUnitOp r' a')) y (streamUnit r a i))
            else fun i => runUnits M ((expand (portData a') (groupData r' a') r'
              localPair localReverse te).map (toUnitOp r' a')) y (streamUnit r a i)) =
            run (M a) (expand (portData a) (groupData r a) r localPair localReverse te)
              (fun i => runUnits M ((expand (portData a') (groupData r' a') r'
              localPair localReverse te).map (toUnitOp r' a')) y (streamUnit r a i)) from
            ite_eq_left_of_eq_true _ _ (eq_true hin), ho, ite_eq_left_of_eq_true _ _ (eq_true hmem)]
        · have hmem : ¬(r' = r ∧ a ∈ a' :: as) := by
            rintro ⟨h1, h2⟩
            rcases List.mem_cons.mp h2 with h | h
            · exact hsame ⟨h1, h.symm⟩
            · exact hin ⟨h1, h⟩
          simp only [hin, hmem, ite_false]
          exact ho
  have outer : ∀ (rs : List ℕ), (∀ r' ∈ rs, r' < 16) → rs.Nodup → ∀ y : NodeUnit → S,
      (fun i => runUnits M (rs.flatMap fun r' => (List.range 112).flatMap fun a' =>
        (expand (portData a') (groupData r' a') r' localPair localReverse te).map (toUnitOp r' a'))
        y (streamUnit r a i)) =
      if r ∈ rs then
        run (M a) (expand (portData a) (groupData r a) r localPair localReverse te)
          (fun i => y (streamUnit r a i))
      else fun i => y (streamUnit r a i) := by
    intro rs hrs hnd
    induction rs with
    | nil => intro y; simp only [List.flatMap_nil, List.not_mem_nil, ite_false]; rfl
    | cons r' rs ih =>
      intro y
      have hrs' : ∀ x ∈ rs, x < 16 := fun x hx => hrs x (List.mem_cons_of_mem _ hx)
      have hnd' := List.nodup_cons.mp hnd
      rw [List.flatMap_cons, runUnits_append, ih hrs' hnd'.2]
      have hi := inner r' (hrs r' List.mem_cons_self) (List.range 112)
        (fun x hx => List.mem_range.mp hx) (List.nodup_range) y
      have ha' : a ∈ List.range 112 := List.mem_range.mpr ha
      by_cases hsame : r' = r
      · subst hsame
        have hnot : r' ∉ rs := hnd'.1
        simp only [hnot, ite_false, List.mem_cons, true_or, ite_true]
        rw [hi]
        simp [ha']
      · by_cases hin : r ∈ rs
        · simp only [hin, ite_true, List.mem_cons, or_true]
          rw [hi]
          simp [hsame]
        · have hmem : r ∉ r' :: rs := by
            intro h; rcases List.mem_cons.mp h with h | h
            · exact hsame h.symm
            · exact hin h
          simp only [hin, hmem, ite_false]
          rw [hi]
          simp [hsame]
  have := outer (List.range 16) (fun x hx => List.mem_range.mp hx) List.nodup_range y
  simpa [eventOps, List.mem_range.mpr hr] using this

/-- **Alignment.** Restricted to one group, the node is that group's stream program. -/
theorem view_nodeOps (M : ℕ → Op S) {r a : ℕ} (hr : r < 16) (ha : a < 112) (y : NodeUnit → S) :
    (fun i => runUnits M nodeOps y (streamUnit r a i)) =
      run (M a) (groupEvents template localPair localReverse (portData a) (groupData r a) r)
        (fun i => y (streamUnit r a i)) := by
  unfold nodeOps groupEvents
  generalize template = ts
  induction ts generalizing y with
  | nil => rfl
  | cons te ts ih =>
    rw [List.flatMap_cons, runUnits_append, List.flatMap_cons]
    rw [ih]
    have hrun : ∀ (p q : List Event) (x : Fin 8 → S), run (M a) (p ++ q) x = run (M a) q (run (M a) p x) := by
      intro p q x
      induction p generalizing x with
      | nil => rfl
      | cons e p ihp => exact ihp _
    rw [hrun, view_eventOps M hr ha te y]

/-! ### The node theorem -/

/-- The T16 operators of each port: the kernel products over the port basis. -/
noncomputable def portOp (a : ℕ) : Op (BinaryWalsh.Arrays 73) := basisOp (portBasis (portData a))

theorem node_accepts {r a : ℕ} (hr : r < 16) (ha : a < 112) :
    accepts (groupEvents template localPair localReverse (portData a) (groupData r a) r)
      (startFrame (portData a)) (fullFrame (portData a)) = true := by
  have hpd : portData a = ports.getD a ⟨[], (0, 0), 0, []⟩ := rfl
  have hgd : groupData r a = (groups r).getD a ⟨[], []⟩ := rfl
  rw [hpd, hgd]
  exact all_accepts r hr a ha

theorem node_run {r a : ℕ} (hr : r < 16) (ha : a < 112) (x : Fin 8 → BinaryWalsh.Arrays 73) :
    @run _ _ _ (portOp a) (groupEvents template localPair localReverse (portData a) (groupData r a) r) x =
      fun i => portOp a (ofAdd (fullFrame (portData a)).toFun) (x i) :=
  run_of_accepts (portOp a) (node_accepts hr ha) x

theorem portData_mem {a : ℕ} (ha : a < 112) : portData a ∈ ports := by
  have hp : ports.length = 112 := by decide
  simp only [portData, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hp ▸ ha),
    Option.getD_some]
  exact List.getElem_mem _

theorem portOp_full {a : ℕ} (ha : a < 112) :
    portOp a (ofAdd (fullFrame (portData a)).toFun) = cAll :=
  port_fullFrame _ (portData_mem ha)

/-- **The T16 node.** Every data family ends with `C_all` applied to its input. -/
theorem node_cAll {r a : ℕ} (hr : r < 16) (ha : a < 112) (y : NodeUnit → BinaryWalsh.Arrays 73)
    (i : Fin 8) : @runUnits _ _ _ portOp nodeOps y (streamUnit r a i) = cAll (y (streamUnit r a i)) :=
  (congrFun (view_nodeOps portOp hr ha y) i).trans
    ((congrFun (node_run hr ha (fun i => y (streamUnit r a i))) i).trans
      (congrArg (fun T => T (y (streamUnit r a i))) (portOp_full ha)))

end IntegerMultBounds.Networks.Certificates.T16.Streams
