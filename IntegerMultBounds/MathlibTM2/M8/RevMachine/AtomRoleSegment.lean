module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleCost

/-!
# Atom segments on the recursive role bank

`AtomSegment.segment_twisted` runs a nonrecursive field segment on a bare `H ++ D` atom array. Here
the same segment runs on the H and D atom fields of a recursive descriptor's role data, with every
spectator (the rows before, the rows, the coordinates before H, between H and D, and after D) kept:
the atom operations run in order on one common bank (`chain`), each as its level family of
refined operations. `segment_twisted`: the chain moves the selected wire's record at every address
to the address whose atom fields are the twisted run of the segment and whose spectators are the
same, keeps every other wire, and restores the rest of the bank, at cost `C f V` with `C`
depending only on the segment and the action wire.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSegment

open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveScalarCoordinates (Address index field)
open AtomRoleLoop (datas)
open AtomRoleOp (execs)
open AtomRolePlan (Fits kind act coord)
open AtomRoleSem (castE)
open AtomRoleRun (ktapes common opRun runCost)
open AtomRoleCost (opConst)
variable {t m f : ℕ}
noncomputable section

/-- An atom operation the role bank runs. -/
abbrev SOp (m : ℕ) := {op : AtomOps.AtomOp (m+m) ℚ // Fits m op}

/-- The tapes of an atom operation's level loop. -/
def tapesOf (hf : 0 < f) (wire : Fin t) (s : SOp m) : ℕ := ktapes (kind hf s.1 s.2) (act wire s.1 s.2)

/-! ### The chain -/

/-- The atom operations in order on the common bank. -/
def chain (T : ℕ) (hf : 0 < f) (wire : Fin t) : (l : List (SOp m)) → (∀ s ∈ l, tapesOf hf wire s ≤ T) →
    (q : ℕ) × Program (T+2) q prime
  | [], _ => ⟨1, skip (T+2) prime (by omega)⟩
  | s :: l, h => ⟨_, seq (opRun T hf s.1 s.2 wire (h s List.mem_cons_self))
      (chain T hf wire l (fun x hx => h x (List.mem_cons_of_mem _ hx))).2⟩

/-- The role data after the chain. -/
def chainData {b : ℕ} (hf : 0 < f) (wire : Fin t) (v : Descriptor) (hw : v.width = (m*f)*b) :
    List (SOp m) → RecursiveViewedAction.Data t v → RecursiveViewedAction.Data t v
  | [], data => data
  | s :: l, data => chainData hf wire v hw l (datas (kind hf s.1 s.2).sel (act wire s.1 s.2) v hw data f)

/-- The cost of the chain. -/
def chainCost (hf : 0 < f) (wire : Fin t) (V : ℕ) : List (SOp m) → ℕ
  | [] => 0
  | s :: l => runCost f hf s.1 s.2 wire V + 1 + chainCost hf wire V l

theorem chain_hoare {b : ℕ} (hb0 : 0 < b) (T : ℕ) (hf : 0 < f) (wire : Fin t) (v : Descriptor)
    (hw : v.width = (m*f)*b) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) :
    ∀ (l : List (SOp m)) (h : ∀ s ∈ l, tapesOf hf wire s ≤ T) (data : RecursiveViewedAction.Data t v),
      HoareTime (chain T hf wire l h).2 (fun x => x = common T hs f b data)
        (fun x => x = common T hs f b (chainData hf wire v hw l data)) (chainCost hf wire (volume prime v) l)
  | [], _, _ => skip_hoare _ _
  | s :: l, h, data =>
    (AtomRoleRun.run_hoare hb0 T hf s.1 s.2 wire (h s List.mem_cons_self) v hw hp hs hv data).seq
      (chain_hoare hb0 T hf wire v hw hp hs hv l (fun x hx => h x (List.mem_cons_of_mem _ hx)) _)

/-- The constant of a chain. -/
def chainConst (wire : Fin t) : List (SOp m) → ℕ
  | [] => 0
  | s :: l => opConst m (act wire s.1 s.2) + 1 + chainConst wire l

theorem chainCost_le {b : ℕ} (hb0 : 0 < b) (hf : 0 < f) (wire : Fin t) (v : Descriptor)
    (hw : v.width = (m*f)*b) (hp : v.Positive) :
    ∀ l : List (SOp m), chainCost hf wire (volume prime v) l ≤ chainConst wire l * f * volume prime v
  | [] => by simp [chainCost, chainConst]
  | s :: l => by
    have h1 := AtomRoleCost.runCost_le hb0 hf s.1 s.2 wire v hw hp
    have h2 := chainCost_le hb0 hf wire v hw hp l
    have hV := AtomRoleCost.atoms_lt_volume hb0 v hw hp
    have h3 : 1 ≤ f * volume prime v := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    simp only [chainCost, chainConst]
    nlinarith

/-! ### The chain's semantics -/

/-- The address after the chain's coordinate operations. -/
def chainAddr {b : ℕ} {v : Descriptor} (hf : 0 < f) : List (SOp m) → Address (m*f) b v → Address (m*f) b v
  | [], x => x
  | s :: l, x => chainAddr hf l (execs (coord b hf s.1 s.2) f x)

theorem chain_entry {b : ℕ} (hf : 0 < f) (wire : Fin t) (v : Descriptor) (hw : v.width = (m*f)*b) :
    ∀ (l : List (SOp m)) (data : RecursiveViewedAction.Data t v) (x : Address (m*f) b v),
      chainData hf wire v hw l data wire (index hw (chainAddr hf l x)) = data wire (index hw x)
  | [], _, _ => rfl
  | s :: l, data, x => by
    simp only [chainData, chainAddr]
    rw [chain_entry hf wire v hw l]
    exact AtomRoleOp.datas_entry _ _ v hw wire _ (AtomRolePlan.coord_entry hf s.1 s.2 wire v hw) data f x

theorem chain_other {b : ℕ} (hf : 0 < f) (wire : Fin t) (v : Descriptor) (hw : v.width = (m*f)*b)
    (other : Fin t) (hne : other ≠ wire) :
    ∀ (l : List (SOp m)) (data : RecursiveViewedAction.Data t v), chainData hf wire v hw l data other = data other
  | [], _ => rfl
  | s :: l, data => by
    simp only [chainData]
    rw [chain_other hf wire v hw other hne l, AtomRolePlan.plan_other hf s.1 s.2 wire v hw data other hne]

theorem chain_field {b : ℕ} {v : Descriptor} (hf : 0 < f) (hw : v.width = (m*f)*b) :
    ∀ (l : List (SOp m)) (x : Address (m*f) b v) (X : Fin (m+m) → Fin f → ZMod (modulus b)),
      field x ∘ castE = AtomOps.refine X →
      field (chainAddr hf l x) ∘ castE =
        AtomOps.refine (AtomOps.atomRun (l.map fun s => AtomSegment.mapOp (Swap.Modular.ratMod (modulus b)) s.1) X)
  | [], _, _, hx => hx
  | s :: l, x, X, hx =>
    chain_field hf hw l _ _
      (AtomRolePlan.plan_field (t := 1) hf s.1 s.2 0 v hw (fun _ _ => 0) x X hx).2

/-- The spectators of an address. -/
def spect {b : ℕ} {v : Descriptor} (x : Address (m*f) b v) :=
  (x.beforeRows, x.row, x.before, x.middle, x.after)

theorem spect_execs {b : ℕ} {v : Descriptor} (e : ℕ → OrderedAffine.Op (Fin (m*f+m*f)) (ZMod (modulus b))) :
    ∀ (l : ℕ) (x : Address (m*f) b v), spect (execs e l x) = spect x
  | 0, _ => rfl
  | l+1, x => by
    rw [execs, ← spect_execs e l x]
    cases e l <;> rfl

theorem spect_chain {b : ℕ} {v : Descriptor} (hf : 0 < f) :
    ∀ (l : List (SOp m)) (x : Address (m*f) b v), spect (chainAddr hf l x) = spect x
  | [], _ => rfl
  | s :: l, x => by rw [chainAddr, spect_chain hf l, spect_execs]

theorem address_ext {b : ℕ} {v : Descriptor} (x y : Address (m*f) b v) (hs : spect x = spect y)
    (hf : field x = field y) : x = y := by
  cases x; cases y
  simp only [spect, Prod.mk.injEq] at hs
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  have hh : ∀ i, field ⟨_, _, _, _, _, _, _⟩ (AffineFieldCoordinates.hIndex i) = _ := fun i => congrFun hf _
  have hd : ∀ i, field ⟨_, _, _, _, _, _, _⟩ (AffineFieldCoordinates.dIndex i) = _ := fun i => congrFun hf _
  simp only [RecursiveScalarCoordinates.field_h, RecursiveScalarCoordinates.field_d] at hh hd
  subst h1 h2 h3 h4 h5
  rw [funext hh, funext hd]

/-! ### Field segments -/

/-- The atom operations of a field segment, with their fit. -/
def sops (ops : List (AffineFieldProgram.Op (Fin m) ℚ)) (hs : ∀ o ∈ AtomSegment.atoms ops, Fits m o) :
    List (SOp m) :=
  (AtomSegment.atoms ops).attach.map fun x => ⟨x.1, hs x.1 x.2⟩

/-- The common bank size of a segment. -/
def bankSize (hf : 0 < f) (wire : Fin t) (l : List (SOp m)) : ℕ := (l.map (tapesOf hf wire)).sum

theorem bankSize_ge (hf : 0 < f) (wire : Fin t) (l : List (SOp m)) :
    ∀ s ∈ l, tapesOf hf wire s ≤ bankSize hf wire l :=
  fun _ hs => List.le_sum_of_mem (List.mem_map_of_mem hs)

/-- **A field segment on the recursive role bank.** For a nonrecursive field segment whose atom
operations the role bank runs, the chain on the common bank padded to `T` tapes changes the role
data so that the record of `wire` at every address moves to the address with the same spectators
whose atom fields are the twisted run of the segment, keeps every other wire, and restores the rest
of the bank, at cost `C f V`. -/
theorem segment_twisted (ops : List (AffineFieldProgram.Op (Fin m) ℚ))
    (hs : ∀ o ∈ AtomSegment.atoms ops, Fits m o) (hn : ∀ op ∈ ops, AffineFieldCoordinates.Nonrecursive op)
    {b : ℕ} (hb0 : 0 < b) (hf : 0 < f) (wire : Fin t) (T : ℕ) (hT : ∀ s ∈ sops ops hs, tapesOf hf wire s ≤ T)
    (v : Descriptor) (hw : v.width = (m*f)*b) (hp : v.Positive) (hh : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hh) (data : RecursiveViewedAction.Data t v) :
    HoareTime (chain T hf wire (sops ops hs) hT).2 (fun x => x = common T hh f b data)
        (fun x => x = common T hh f b (chainData hf wire v hw (sops ops hs) data))
        (chainConst wire (sops ops hs) * f * volume prime v) ∧
      (∀ other, other ≠ wire → chainData hf wire v hw (sops ops hs) data other = data other) ∧
      ∀ (s : Swap.Shear.State (Fin m) (Fin f → ZMod (modulus b))) (x y : Address (m*f) b v),
        spect y = spect x → field x ∘ castE = AtomOps.refine (AffineFieldCoordinates.embed s) →
        field y ∘ castE = AtomOps.refine (AffineFieldCoordinates.embed
          (TwistedProgram.twRun (TwistedExchange.atomRev f)
            ((ops.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (modulus b)))).map
              (AffineFieldProgram.mapOp AtomOps.scalar)) s)) →
        chainData hf wire v hw (sops ops hs) data wire (index hw y) = data wire (index hw x) := by
  refine ⟨(chain_hoare hb0 T hf wire v hw hp hh hv _ hT data).consequence (fun _ h => h) (fun _ h => h)
    (chainCost_le hb0 hf wire v hw hp _), fun other hne => chain_other hf wire v hw other hne _ data, ?_⟩
  intro s x y hsp hx hy
  set g := Swap.Modular.ratMod (modulus b)
  set opsZ := ops.map (AffineFieldProgram.mapOp g)
  have hmap : (sops ops hs).map (fun s => AtomSegment.mapOp g s.1) = opsZ.flatMap AtomOps.atomExpand := by
    have h0 : (sops ops hs).map (fun s => AtomSegment.mapOp g s.1) = (AtomSegment.atoms ops).map (AtomSegment.mapOp g) := by
      simp [sops, List.map_map, Function.comp_def]
    rw [h0, AtomSegment.atoms, List.map_flatMap, List.flatMap_map]
    congr 1
    funext op
    exact AtomSegment.atomExpand_map g (Swap.Modular.ratMod_one (m := modulus b)) (AtomSegment.ratMod_neg_one _) op
  have hnZ : ∀ op ∈ opsZ, AffineFieldCoordinates.Nonrecursive op := by
    intro op hop
    obtain ⟨o, ho', rfl⟩ := List.mem_map.mp hop
    have := hn o ho'
    cases o <;> trivial
  have hc := chain_field hf hw (sops ops hs) x _ hx
  rw [hmap, AtomOps.atom_segment_run opsZ hnZ s, ← hy] at hc
  have hfe : field (chainAddr hf (sops ops hs) x) = field y := by
    funext z
    have := congrFun hc (castE.symm z)
    simpa using this
  rw [← address_ext _ _ (by rw [spect_chain, hsp]) hfe]
  exact chain_entry hf wire v hw _ data x

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSegment
