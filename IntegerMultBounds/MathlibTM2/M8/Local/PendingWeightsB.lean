module

public import IntegerMultBounds.MathlibTM2.M8.Local.CompilerAdjointB
public import Mathlib.Data.Finset.Image
public import IntegerMultBounds.MathlibTM2.M8.Local.FrameFlowB

/-! Finite observation weights on the compiler's pending uses. The frontier
transition separates surviving uses, freshly served uses and a donor's linked use. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Local.Dag
noncomputable section
open Classical
open AdjointB

variable (D : Dag)

/-- The finite universe of legal argument and root uses. -/
def useSet : Finset Use :=
  (((List.range D.N).flatMap fun n =>
    if D.v ≤ n then [Use.gate n false, Use.gate n true] else []) ++
    (List.range D.rootCount).map Use.root).toFinset

theorem mem_useSet_gate (n : Nat) (pos : Bool) :
    Use.gate n pos ∈ D.useSet ↔ D.v ≤ n ∧ n < D.N := by
  simp only [useSet, List.mem_toFinset, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_map]
  constructor
  · rintro (⟨t, ht, hu⟩ | ⟨r, _, he⟩)
    · split_ifs at hu with h
      · simp only [List.mem_cons, List.not_mem_nil, or_false, Use.gate.injEq] at hu
        rcases hu with ⟨he, _⟩ | ⟨he, _⟩ <;> subst t <;> exact ⟨h, ht⟩
      · simp at hu
    · cases he
  · rintro ⟨hv, hn⟩
    left
    refine ⟨n, hn, ?_⟩
    cases pos <;> simp [hv]

theorem mem_useSet_root (r : Nat) : Use.root r ∈ D.useSet ↔ r < D.rootCount := by
  simp [useSet]

theorem mem_useSet_of_free {n : Nat} {u : Use} (h : u ∈ D.freeUses n) : u ∈ D.useSet := by
  have hu := (D.mem_freeUses.mp h).1
  cases u with
  | gate t pos =>
    have ht := (D.mem_uses_gate n t pos).mp hu
    exact (D.mem_useSet_gate t pos).mpr ⟨ht.2.1, ht.1⟩
  | root r => exact (D.mem_useSet_root r).mpr ((D.mem_uses_root n r).mp hu).1

theorem mem_useSet_of_link (hv : D.Valid) {n : Nat} {u : Use}
    (h : D.linkUse n = some u) : u ∈ D.useSet := by
  obtain ⟨o, t, pos, hl, rfl⟩ := D.linkUse_eq.mp h
  have hd := hv.link_donor n o t pos hl
  have ht := hv.link_user n o t pos hl
  exact (D.mem_useSet_gate t pos).mpr ⟨by omega, ht.2.1⟩

theorem pending_mem_useSet (hv : D.Valid) {k : Nat} {u : Use}
    (h : D.Pending k u) : u ∈ D.useSet := by
  rcases h.2 with ⟨n, _, hu⟩ | ⟨n, _, hu⟩
  · exact D.mem_useSet_of_free hu
  · exact D.mem_useSet_of_link hv hu

theorem live_free_succ (hv : D.Valid) {n : Nat} {u : Use}
    (h : u ∈ D.freeUses n) : Live (n + 1) u := by
  have hu := (D.mem_freeUses.mp h).1
  cases u with
  | root r => trivial
  | gate t pos =>
    obtain ⟨ht, hvT, ha⟩ := (D.mem_uses_gate n t pos).mp hu
    have := hv.arg_lt t hvT ht pos
    simp only [Live]
    omega

theorem live_link_succ (hv : D.Valid) {n : Nat} {u : Use}
    (h : D.linkUse n = some u) : Live (n + 1) u := by
  obtain ⟨o, t, pos, hl, rfl⟩ := D.linkUse_eq.mp h
  exact Nat.succ_le_of_lt (hv.link_user n o t pos hl).1

/-- The exact frontier transition, before any slot or coefficient is evaluated. -/
theorem pending_succ_iff (hv : D.Valid) (k : Nat) (u : Use) :
    D.Pending (k + 1) u ↔
      (D.Pending k u ∧ Live (k + 1) u) ∨ u ∈ D.freeUses k ∨ D.linkUse k = some u := by
  constructor
  · intro h
    by_cases hf : u ∈ D.freeUses k
    · exact Or.inr (Or.inl hf)
    by_cases hl : D.linkUse k = some u
    · exact Or.inr (Or.inr hl)
    exact Or.inl ⟨(D.pending_old hv h hf hl).1, h.1⟩
  · rintro (⟨hp, hl⟩ | hf | hl)
    · refine ⟨hl, ?_⟩
      rcases hp.2 with ⟨n, hn, hu⟩ | ⟨n, hn, hu⟩
      · exact Or.inl ⟨n, by omega, hu⟩
      · exact Or.inr ⟨n, by omega, hu⟩
    · exact ⟨D.live_free_succ hv hf, Or.inl ⟨k, by omega, hf⟩⟩
    · exact ⟨D.live_link_succ hv hl, Or.inr ⟨k, by omega, hl⟩⟩

/-- Pending uses form a finite set without choosing or evaluating compiler slots. -/
def pendingUses (k : Nat) : Finset Use := D.useSet.filter (D.Pending k)

@[simp] theorem mem_pendingUses (hv : D.Valid) (k : Nat) (u : Use) :
    u ∈ D.pendingUses k ↔ D.Pending k u := by
  simp only [pendingUses, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨D.pending_mem_useSet hv h, h⟩⟩

@[simp] theorem pendingUses_zero : D.pendingUses 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨_, hp⟩ := Finset.mem_filter.mp hu
  rcases hp.2 with ⟨n, hn, _⟩ | ⟨n, hn, _⟩ <;> omega

/-- The final frontier consists exactly of the roots. -/
theorem pending_final_iff (hv : D.Valid) (u : Use) :
    D.Pending D.N u ↔ ∃ r < D.rootCount, u = .root r := by
  constructor
  · intro hp
    have hu := D.pending_mem_useSet hv hp
    cases u with
    | gate t pos =>
      have ht := (D.mem_useSet_gate t pos).mp hu
      have hl := hp.1
      simp only [Live] at hl
      omega
    | root r => exact ⟨r, (D.mem_useSet_root r).mp hu, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact D.root_pending hv hr

/-- The set form of the frontier transition. -/
theorem pendingUses_succ (hv : D.Valid) (k : Nat) :
    D.pendingUses (k + 1) =
      ((D.pendingUses k).filter (Live (k + 1)) ∪ (D.freeUses k).toFinset) ∪
        (D.linkUse k).toList.toFinset := by
  ext u
  simp only [D.mem_pendingUses hv, Finset.mem_union, Finset.mem_filter,
    List.mem_toFinset, Option.mem_toList]
  rw [D.pending_succ_iff hv]
  tauto

/-- Uses born at this node cannot already belong to the old frontier. -/
theorem pending_free_disjoint (hv : D.Valid) (k : Nat) :
    Disjoint (D.pendingUses k) (D.freeUses k).toFinset := by
  apply Finset.disjoint_left.mpr
  intro u hp hf
  have hs := FrameFlow.pending_src_lt D hv ((D.mem_pendingUses hv k u).mp hp)
  rw [D.srcNode_free (List.mem_toFinset.mp hf)] at hs
  omega

theorem pending_link_disjoint (hv : D.Valid) (k : Nat) (hk : k < D.N) :
    Disjoint (D.pendingUses k) (D.linkUse k).toList.toFinset := by
  apply Finset.disjoint_left.mpr
  intro u hp hl
  have hs := FrameFlow.pending_src_lt D hv ((D.mem_pendingUses hv k u).mp hp)
  have he : D.linkUse k = some u := by simpa using hl
  rw [D.srcNode_linked hv hk he] at hs
  omega

theorem free_link_disjoint (_hv : D.Valid) (k : Nat) (hk : k < D.N) :
    Disjoint (D.freeUses k).toFinset (D.linkUse k).toList.toFinset := by
  apply Finset.disjoint_left.mpr
  intro u hf hl
  have hf' := (D.mem_freeUses.mp (List.mem_toFinset.mp hf)).2
  have he : D.linkUse k = some u := by simpa using hl
  have ht := (D.linkedB_iff u).mpr ⟨k, hk, he⟩
  rw [hf'] at ht
  cases ht

/-- The final finite boundary is the root set. -/
theorem pendingUses_final (hv : D.Valid) :
    D.pendingUses D.N = (Finset.range D.rootCount).image Use.root := by
  ext u
  simp only [D.mem_pendingUses hv, D.pending_final_iff hv, Finset.mem_image,
    Finset.mem_range]
  constructor <;> rintro ⟨r, hr, he⟩ <;> exact ⟨r, hr, he.symm⟩

/-- A finite observation at the live compiler boundary. -/
def pendingWeights (k : Nat) (st : State) (c : Use → ZMod 2) : Reg →₀ ZMod 2 :=
  ∑ u ∈ D.pendingUses k, Finsupp.single (.aux (st.pend u)) (c u)

/-- Frontier weights split into surviving, freshly served and linked observations. -/
theorem pendingWeights_succ (hv : D.Valid) (k : Nat) (hk : k < D.N)
    (st : State) (c : Use → ZMod 2) :
    D.pendingWeights (k + 1) st c =
      (∑ u ∈ (D.pendingUses k).filter (Live (k + 1)),
        Finsupp.single (.aux (st.pend u)) (c u)) +
      (∑ u ∈ (D.freeUses k).toFinset, Finsupp.single (.aux (st.pend u)) (c u)) +
      (∑ u ∈ (D.linkUse k).toList.toFinset, Finsupp.single (.aux (st.pend u)) (c u)) := by
  rw [pendingWeights, D.pendingUses_succ hv]
  rw [Finset.sum_union, Finset.sum_union]
  · exact (D.pending_free_disjoint hv k).mono_left (Finset.filter_subset _ _)
  · exact Finset.disjoint_union_left.mpr
      ⟨(D.pending_link_disjoint hv k hk).mono_left (Finset.filter_subset _ _),
        D.free_link_disjoint hv k hk⟩

/-- The terminal frontier observation agrees with the compiler's root readout. -/
theorem pendingWeights_final (hv : D.Valid) (targets : Nat → List Nat) (t : Nat)
    (c : Use → ZMod 2) (hc : ∀ r < D.rootCount, c (.root r) = ((targets r).count t : ZMod 2)) :
    D.pendingWeights D.N D.compile c = rootWeights D targets t := by
  rw [pendingWeights, D.pendingUses_final hv, Finset.sum_image]
  · simp only [rootWeights]
    rw [← List.sum_toFinset _ List.nodup_range]
    have he : (List.range D.rootCount).toFinset = Finset.range D.rootCount := by
      ext i
      simp
    rw [he]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hc r (Finset.mem_range.mp hr)]
  · intro i _ j _ he
    exact Use.root.inj he

/-- Distinct pending slots carry exactly their named use's observation weight. -/
theorem pendingWeights_at (hv : D.Valid) (k : Nat) (st : State) (c : Use → ZMod 2)
    (hinj : ∀ u v, D.Pending k u → D.Pending k v → st.pend u = st.pend v → u = v)
    (u : Use) (hu : D.Pending k u) :
    D.pendingWeights k st c (.aux (st.pend u)) = c u := by
  simp only [pendingWeights, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single u]
  · simp
  · intro v hv' hne
    have hslots : st.pend v ≠ st.pend u := fun he =>
      hne (hinj v u ((D.mem_pendingUses hv k v).mp hv') hu he)
    simp [hslots]
  · intro h
    exact (h ((D.mem_pendingUses hv k u).mpr hu)).elim

/-- Dead slots have zero frontier weight. -/
theorem pendingWeights_outside (hv : D.Valid) (k : Nat) (st : State) (c : Use → ZMod 2)
    (s : Nat) (hs : ∀ u, D.Pending k u → st.pend u ≠ s) :
    D.pendingWeights k st c (.aux s) = 0 := by
  simp only [pendingWeights, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro u hu
  simp [hs u ((D.mem_pendingUses hv k u).mp hu)]

/-- The compiler invariant supplies the injectivity needed for these observations. -/
theorem pendingWeights_compileTo_at (hv : D.Valid) (k : Nat) (hk : k ≤ D.N)
    (c : Use → ZMod 2) (u : Use) (hu : D.Pending k u) :
    D.pendingWeights k (D.compileTo k) c (.aux ((D.compileTo k).pend u)) = c u := by
  exact D.pendingWeights_at hv k (D.compileTo k) c
    (D.inv_compileTo hv (fun _ => 0) k hk).inj u hu

/-- Slots not yet allocated have no live-frontier contribution. Their garbage
weights can therefore be tracked separately from pending-use weights. -/
theorem pendingWeights_compileTo_fresh (hv : D.Valid) (k : Nat) (hk : k ≤ D.N)
    (c : Use → ZMod 2) (s : Nat) (hs : (D.compileTo k).next ≤ s) :
    D.pendingWeights k (D.compileTo k) c (.aux s) = 0 := by
  apply D.pendingWeights_outside hv
  intro u hu
  have := (D.inv_compileTo hv (fun _ => 0) k hk).slot_lt u hu
  omega

end
end IntegerMultBounds.MathlibTM2.M8.Local.Dag
