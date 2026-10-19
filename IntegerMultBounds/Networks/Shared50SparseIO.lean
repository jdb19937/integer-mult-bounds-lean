module

public import IntegerMultBounds.Networks.Shared50Dirty
public import IntegerMultBounds.Networks.DAGSourceRoles
public import IntegerMultBounds.Networks.SparseCircuit

/-! Actual sparse input/output instructions for the shared fifty-point program.
Every update is a one-source XOR, and all destinations are actual physical
source roles or requested data outputs. No dense zero terms are emitted. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Shared50SparseIO

open DisjointCircuit NeighborCounts SharedPointReplay Circuit

attribute [local irreducible] SharedPointReplay.circuit SharedPointExecution.code
  Shared50Finite.program Shared50Finite.output Shared50Dirty.pairIndex Shared50Dirty.partialRole

private theorem bank_load_run {n s : ℕ} (entries : List (Fin s × Fin n))
    (X Y : Fin n → ZMod 2) (S : Fin s → ZMod 2) :
    run (SparseCircuit.copies DirtyLinearCircuit.scratch DirtyLinearCircuit.x entries)
      (DirtyLinearCircuit.contents X Y S) =
      DirtyLinearCircuit.contents X Y
        (S + fun i => (entries.map (fun entry => if entry.1 = i then X entry.2 else 0)).sum) := by
  funext role
  rw [SparseCircuit.copies_run _ _ _ (by intros; simp [DirtyLinearCircuit.scratch, DirtyLinearCircuit.x])]
  rcases role with i | i | i
  · simp [DirtyLinearCircuit.contents, DirtyLinearCircuit.scratch]
  · simp [DirtyLinearCircuit.contents, DirtyLinearCircuit.scratch]
  · simp [DirtyLinearCircuit.contents, DirtyLinearCircuit.scratch, DirtyLinearCircuit.x]

private theorem bank_read_run {n s : ℕ} (entries : List (Fin n × Fin s))
    (X Y : Fin n → ZMod 2) (S : Fin s → ZMod 2) :
    run (SparseCircuit.copies DirtyLinearCircuit.y DirtyLinearCircuit.scratch entries)
      (DirtyLinearCircuit.contents X Y S) =
      DirtyLinearCircuit.contents X
        (Y + fun i => (entries.map (fun entry => if entry.1 = i then S entry.2 else 0)).sum) S := by
  funext role
  rw [SparseCircuit.copies_run _ _ _ (by intros; simp [DirtyLinearCircuit.y, DirtyLinearCircuit.scratch])]
  rcases role with i | i | i
  · simp [DirtyLinearCircuit.contents, DirtyLinearCircuit.y]
  · simp [DirtyLinearCircuit.contents, DirtyLinearCircuit.y, DirtyLinearCircuit.scratch]
  · simp [DirtyLinearCircuit.contents, DirtyLinearCircuit.y]

abbrev Source := {entry : ℕ × ℕ // entry ∈ SharedPointExecution.code.sources}

theorem source_mem_compile (entry : Source) :
    entry.val ∈ (DAGAllocator.compile circuit.nodes outputRefs).sources := by
  simpa only [SharedPointExecution.code] using entry.property

/-- The allocator's physical source slot, with its actual finite bound. -/
def sourceRole (entry : Source) : Fin 509194 :=
  ⟨entry.val.2, (DAGSourceRoles.sources_bound circuit.nodes outputRefs entry.val (source_mem_compile entry)).trans_le
    (by simpa only [SharedPointExecution.code] using Shared50Certificate.role_bound)⟩

/-- The semantic input label of this particular physical source occurrence. -/
def sourceLabel (entry : Source) : Triple 50 :=
  DAGSourceRoles.label circuit.nodes outputRefs entry.val (source_mem_compile entry)

/-- Distinct source entries occupy distinct physical slots, even if their
semantic input labels coincide. -/
theorem sourceRole_injective : Function.Injective sourceRole := by
  intro a b he
  have hn : (SharedPointExecution.code.sources.map Prod.snd).Nodup := by
    simpa only [SharedPointExecution.code] using
      DAGValueTransfer.compile_sources_nodup circuit.nodes outputRefs
  apply Subtype.ext
  exact List.inj_on_of_nodup_map hn a.property b.property (congrArg Fin.val he)

theorem source_roles_nodup : (SharedPointExecution.code.sources.attach.map sourceRole).Nodup := by
  have hn : (SharedPointExecution.code.sources.map Prod.snd).Nodup := by
    simpa only [SharedPointExecution.code] using
      DAGValueTransfer.compile_sources_nodup circuit.nodes outputRefs
  exact List.Nodup.map sourceRole_injective (List.nodup_attach.mpr (List.Nodup.of_map _ hn))

section Lists
variable {n : ℕ}

/-- Exactly one copy for every actual allocator source entry. -/
def sourceEntries (e : Fin n ≃ Triple 50) : List (Fin 509194 × Fin n) :=
  SharedPointExecution.code.sources.attach.map (fun entry => (sourceRole entry, e.symm (sourceLabel entry)))

def load (e : Fin n ≃ Triple 50) : Program (DirtyLinearCircuit.Register n 509194) (ZMod 2) :=
  SparseCircuit.copies DirtyLinearCircuit.scratch DirtyLinearCircuit.x (sourceEntries e)

/-- All three common-point outputs of each target are read, in a fixed finite order. -/
def readEntries (e : Fin n ≃ Triple 50) : List (Fin n × Fin 509194) :=
  (List.ofFn (fun i : Fin n => i)).flatMap (fun i =>
    (Finset.univ : Finset {c : Fin 50 // c ∈ (e i).val}).sort.map
      (fun c => (i, Shared50Dirty.partialRole (e i) c)))

def read (e : Fin n ≃ Triple 50) : Program (DirtyLinearCircuit.Register n 509194) (ZMod 2) :=
  SparseCircuit.copies DirtyLinearCircuit.y DirtyLinearCircuit.scratch (readEntries e)

@[simp] theorem load_length (e : Fin n ≃ Triple 50) : (load e).length = SharedPointExecution.code.sources.length := by
  simp [load, sourceEntries]

theorem load_length_bound (e : Fin n ≃ Triple 50) : (load e).length ≤ 509194 := by
  have hh := source_roles_nodup.length_le_card
  simpa only [List.length_map, List.length_attach, Fintype.card_fin, load_length] using hh

private theorem sum_map_flatMap {α β M : Type*} [AddCommMonoid M]
    (xs : List α) (f : α → List β) (g : β → M) :
    ((xs.flatMap f).map g).sum = (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem sum_map_sort {α M : Type*} [LinearOrder α] [AddCommMonoid M]
    (s : Finset α) (f : α → M) : (s.sort.map f).sum = ∑ x ∈ s, f x := by
  simpa using (List.sum_toFinset f (Finset.sort_nodup s (· ≤ ·))).symm

@[simp] theorem read_length (e : Fin n ≃ Triple 50) : (read e).length = 3 * n := by
  have hc (i : Fin n) : (e i).val.card = 3 := (e i).property
  simp [read, readEntries, List.length_flatMap, List.map_ofFn, List.sum_ofFn, hc, Nat.mul_comm]

/-- The source-copy payload is exactly the original compiler's source initialization. -/
theorem source_sum (e : Fin n ≃ Triple 50) (X : Fin n → ZMod 2) (role : Fin 509194) :
    ((sourceEntries e).map (fun entry => if entry.1 = role then X entry.2 else 0)).sum =
      Shared50Finite.initial (fun T => X (e.symm T)) role := by
  change _ = DAGValueTransfer.initial SharedPointExecution.code.sources
    (DAGValueTransfer.sourceInput circuit.nodes (fun T => X (e.symm T))) role.val
  rw [DAGSourceRoles.initial_as_sum]
  unfold sourceEntries
  rw [List.map_map]
  calc
    _ = (SharedPointExecution.code.sources.attach.map (fun entry =>
        if entry.val.2 = role.val then
          DAGValueTransfer.sourceInput circuit.nodes (fun T => X (e.symm T)) entry.val.1 else 0)).sum := by
      congr 1
      apply List.map_congr_left
      intro entry _
      simp only [Function.comp_def, sourceRole, Fin.ext_iff, sourceLabel,
        DAGSourceRoles.sourceInput_label circuit.nodes outputRefs entry.val (source_mem_compile entry)]
    _ = _ := congrArg List.sum (List.attach_map_val (f := fun entry : ℕ × ℕ =>
      if entry.2 = role.val then DAGValueTransfer.sourceInput circuit.nodes (fun T => X (e.symm T)) entry.1 else 0))

/-- The readout-copy payload sums precisely the three physical partial outputs. -/
theorem read_sum (e : Fin n ≃ Triple 50) (S : Fin 509194 → ZMod 2) (i : Fin n) :
    ((readEntries e).map (fun entry => if entry.1 = i then S entry.2 else 0)).sum =
      mv (Shared50Dirty.readoutMatrix e) S i := by
  rw [Shared50Dirty.readoutMatrix_mv]
  simp only [readEntries, sum_map_flatMap, List.map_map, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, sum_map_sort]
  simp

/-- Sparse loading adds the real source values and preserves all data banks. -/
theorem load_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2) (S : Fin 509194 → ZMod 2) :
    run (load e) (DirtyLinearCircuit.contents X Y S) =
      DirtyLinearCircuit.contents X Y (S + Shared50Finite.initial (fun T => X (e.symm T))) := by
  have hh := bank_load_run (sourceEntries e) X Y S
  have he : (fun i => ((sourceEntries e).map (fun entry => if entry.1 = i then X entry.2 else 0)).sum) =
      Shared50Finite.initial (fun T => X (e.symm T)) := funext (source_sum e X)
  rw [he] at hh
  exact hh

/-- Sparse readout preserves arbitrary scratch while adding its actual partial outputs. -/
theorem read_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2) (S : Fin 509194 → ZMod 2) :
    run (read e) (DirtyLinearCircuit.contents X Y S) =
      DirtyLinearCircuit.contents X (Y + mv (Shared50Dirty.readoutMatrix e) S) S := by
  have hh := bank_read_run (readEntries e) X Y S
  have he : (fun i => ((readEntries e).map (fun entry => if entry.1 = i then S entry.2 else 0)).sum) =
      mv (Shared50Dirty.readoutMatrix e) S := funext (read_sum e S)
  rw [he] at hh
  exact hh

end Lists

end IntegerMultBounds.Networks.Shared50SparseIO
