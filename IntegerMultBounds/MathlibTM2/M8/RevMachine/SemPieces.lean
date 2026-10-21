module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Schedule
public import IntegerMultBounds.Networks.AffineFieldBijective

/-!
# The schedule on streams

The pieces of the schedule act on the streams of the wires as the control's steps do (`pieceSem`):
an edge segment by the twisted action of its program, a block call of rank `r` by the twisted
interchanges of the reversed pivots `revPivots m r`, a gate and a reset as in the control. When
every edge program is an interchange-free head, one block of disjoint interchanges and an
interchange-free tail (`EdgeForm`), the schedule's run is the control's run (`schedule_run`), so
from zero temporaries every contract role ends with the routed reversed interchange
(`schedule_identity`). The stage-2 PR97 node has this form (`edgeForm97`).

The twisted action composes over programs (`twEdgeAction_append`), since the twisted map of a
legal program is bijective (`twMap_bijective`); the twisted interchanges of disjoint pivots
commute (`revSwaps_perm`) and act coordinatewise (`revSwaps_fst`, `revSwaps_snd`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics

noncomputable section
open IntegerMultBounds.Networks
open Schedule (Seg Call schedule stepPieces before after)
open ReversedExchange (revPivots)
open TwistedExchange (revSwap revSwaps)
open Exchange (swapOps)
open Rev (Addr Streams twMap twEdgeAction)
open Swap.Modular (ratMod)
open Matrix

/-! ### Twisted maps of legal programs -/

section Maps

variable {ι R S : Type*} [Fintype ι] [LinearOrder ι] [CommRing R] [CommRing S]

omit [Fintype ι] in
theorem legal_mapOp (g : R →+* S) {op : AffineFieldProgram.Op ι R} (h : AffineFieldProgram.Legal op) :
    AffineFieldProgram.Legal (AffineFieldProgram.mapOp g op) := by
  cases op with
  | affineH a =>
    cases a with
    | scale i c => exact IsUnit.map g h
    | shift i j c => exact h
  | affineD a =>
    cases a with
    | scale i c => exact IsUnit.map g h
    | shift i j c => exact h
  | addToD => trivial
  | subFromD => trivial
  | interchange => trivial

end Maps

theorem invFun_comp {α : Type*} [Nonempty α] {g h : α → α} (hg : Function.Bijective g)
    (hh : Function.Bijective h) : Function.invFun (h ∘ g) = Function.invFun g ∘ Function.invFun h := by
  funext a
  apply (hh.comp hg).injective
  rw [Function.invFun_eq ((hh.comp hg).surjective a)]
  simp only [Function.comp_apply, Function.invFun_eq (hg.surjective _), Function.invFun_eq (hh.surjective a)]

section Twisted

variable {d q b : ℕ} {S : Type} [CommRing S] {φ : ZMod (q ^ b) →+* S} {σ : S →+* S}

theorem twMap_append (p p' : FieldProgram d) : twMap φ σ (p ++ p') = twMap φ σ p' ∘ twMap φ σ p := by
  funext a
  simp only [twMap, TwistedProgram.twRun, List.map_append, List.foldl_append, Function.comp_apply]

theorem twRun_swapOps (L : List (Fin d × Fin d)) : twMap φ σ (swapOps L) = revSwaps σ L := by
  funext s
  simp only [twMap, swapOps, List.map_map]
  induction L generalizing s with
  | nil => rfl
  | cons p L ih => exact ih (revSwap σ p s)

theorem swapAction_eq (L : List (Fin d × Fin d)) (x : Streams d S) :
    twEdgeAction φ σ (swapOps L) x = fun a => x (Function.invFun (revSwaps σ L) a) := by
  unfold twEdgeAction
  rw [twRun_swapOps]

theorem legal_left {p p' : FieldProgram d} (h : ∀ op ∈ specialize (q ^ b) (p ++ p'), AffineFieldProgram.Legal op) :
    ∀ op ∈ specialize (q ^ b) p, AffineFieldProgram.Legal op := fun op hop =>
  h op (by simp only [specialize, List.map_append, List.mem_append] at hop ⊢; exact Or.inl hop)

theorem legal_right {p p' : FieldProgram d} (h : ∀ op ∈ specialize (q ^ b) (p ++ p'), AffineFieldProgram.Legal op) :
    ∀ op ∈ specialize (q ^ b) p', AffineFieldProgram.Legal op := fun op hop =>
  h op (by simp only [specialize, List.map_append, List.mem_append] at hop ⊢; exact Or.inr hop)

variable (hσ : ∀ x, σ (σ x) = x) (hφ : ∀ c, σ (φ c) = φ c)
include hσ hφ

/-- **The twisted map of a legal program is bijective.** -/
theorem twMap_bijective [Finite S] (p : FieldProgram d)
    (hp : ∀ op ∈ specialize (q ^ b) p, AffineFieldProgram.Legal op) : Function.Bijective (twMap φ σ p) := by
  set ops := (p.map (AffineFieldProgram.mapOp (ratMod (q ^ b)))).map (AffineFieldProgram.mapOp φ)
  have hfix : ∀ op ∈ ops, TwistedProgram.FixedOp σ op := by
    intro op hop
    obtain ⟨o, -, rfl⟩ := List.mem_map.mp hop
    exact TwistedProgram.fixedOp_mapOp hφ o
  have hl : ∀ op ∈ ops, AffineFieldProgram.Legal op := by
    intro op hop
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hop
    exact legal_mapOp φ (hp o ho)
  have hc : Function.Involutive (TwistedExchange.conj σ : Swap.Shear.State (Fin d) S → _) :=
    TwistedExchange.conj_conj hσ
  have he : twMap φ σ p = TwistedExchange.conj σ ∘ AffineFieldProgram.run ops ∘ TwistedExchange.conj σ :=
    funext (TwistedProgram.twRun_eq hσ hfix)
  rw [he]
  exact hc.bijective.comp ((AffineFieldBijective.run_bijective ops hl).comp hc.bijective)

/-- **The twisted action composes.** -/
theorem twEdgeAction_append [Finite S] (p p' : FieldProgram d)
    (hp : ∀ op ∈ specialize (q ^ b) (p ++ p'), AffineFieldProgram.Legal op) (x : Streams d S) :
    twEdgeAction φ σ (p ++ p') x = twEdgeAction φ σ p' (twEdgeAction φ σ p x) := by
  funext a
  simp only [twEdgeAction, twMap_append]
  rw [invFun_comp (twMap_bijective hσ hφ p (legal_left hp)) (twMap_bijective hσ hφ p' (legal_right hp))]
  rfl

end Twisted

/-! ### Twisted interchanges -/

section Swaps

variable {ι S : Type*} [DecidableEq ι] [CommRing S] {σ : S →+* S}

theorem revSwap_comm {p p' : ι × ι} (h₁ : p.1 ≠ p'.1) (h₂ : p.2 ≠ p'.2) (s : Swap.Shear.State ι S) :
    revSwap σ p' (revSwap σ p s) = revSwap σ p (revSwap σ p' s) := by
  simp only [revSwap, Function.update_of_ne h₁, Function.update_of_ne h₂,
    Function.update_of_ne h₁.symm, Function.update_of_ne h₂.symm, Prod.mk.injEq]
  exact ⟨Function.update_comm h₁ _ _ _, Function.update_comm h₂ _ _ _⟩

/-- **Disjoint twisted interchanges commute.** -/
theorem revSwaps_perm {L L' : List (ι × ι)} (hp : L.Perm L') (h₁ : (L.map Prod.fst).Nodup)
    (h₂ : (L.map Prod.snd).Nodup) (s : Swap.Shear.State ι S) : revSwaps σ L s = revSwaps σ L' s := by
  unfold revSwaps
  refine hp.foldl_eq' (fun x hx y hy z => ?_) s
  by_cases hxy : x = y
  · rw [hxy]
  · exact revSwap_comm (fun h => hxy (List.inj_on_of_nodup_map h₁ hx hy h))
      (fun h => hxy (List.inj_on_of_nodup_map h₂ hx hy h)) z

theorem revSwaps_cons (p : ι × ι) (L : List (ι × ι)) (s : Swap.Shear.State ι S) :
    revSwaps σ (p :: L) s = revSwaps σ L (revSwap σ p s) := rfl

/-- The coordinates the pivots do not touch keep their values. -/
theorem revSwaps_fst_not : ∀ (L : List (ι × ι)) (s : Swap.Shear.State ι S) (i : ι), i ∉ L.map Prod.fst →
    (revSwaps σ L s).1 i = s.1 i
  | [], _, _, _ => rfl
  | p :: L, s, i, hi => by
    simp only [List.map_cons, List.mem_cons, not_or] at hi
    rw [revSwaps_cons, revSwaps_fst_not L _ i hi.2]
    simp only [revSwap, Function.update_of_ne hi.1]

theorem revSwaps_snd_not : ∀ (L : List (ι × ι)) (s : Swap.Shear.State ι S) (j : ι), j ∉ L.map Prod.snd →
    (revSwaps σ L s).2 j = s.2 j
  | [], _, _, _ => rfl
  | p :: L, s, j, hj => by
    simp only [List.map_cons, List.mem_cons, not_or] at hj
    rw [revSwaps_cons, revSwaps_snd_not L _ j hj.2]
    simp only [revSwap, Function.update_of_ne hj.1]

/-- A pivot exchanges its two coordinates, twisted. -/
theorem revSwaps_mem : ∀ (L : List (ι × ι)), (L.map Prod.fst).Nodup → (L.map Prod.snd).Nodup →
    ∀ (s : Swap.Shear.State ι S) (p : ι × ι), p ∈ L →
      (revSwaps σ L s).1 p.1 = σ (s.2 p.2) ∧ (revSwaps σ L s).2 p.2 = σ (s.1 p.1)
  | [], _, _, _, _, hp => absurd hp (List.not_mem_nil)
  | p' :: L, h₁, h₂, s, p, hp => by
    simp only [List.map_cons, List.nodup_cons] at h₁ h₂
    rw [revSwaps_cons]
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [revSwaps_fst_not L _ _ h₁.1, revSwaps_snd_not L _ _ h₂.1]
      simp [revSwap]
    · obtain ⟨e₁, e₂⟩ := revSwaps_mem L h₁.2 h₂.2 (revSwap σ p' s) p hp
      rw [e₁, e₂]
      have n₁ : p.1 ≠ p'.1 := fun h => h₁.1 (h ▸ List.mem_map_of_mem hp)
      have n₂ : p.2 ≠ p'.2 := fun h => h₂.1 (h ▸ List.mem_map_of_mem hp)
      simp [revSwap, Function.update_of_ne n₁, Function.update_of_ne n₂]

end Swaps

/-! ### The reversed pivots -/

section Pivots

variable {S : Type*} [CommRing S] {σ : S →+* S} {m r : ℕ}

theorem mem_revPivots_iff (p : Fin m × Fin m) : p ∈ revPivots m r ↔ p.1.val < r ∧ p.2 = p.1.rev := by
  simp only [revPivots, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨hk, rfl⟩
  · rintro ⟨hk, he⟩; exact ⟨p.1, hk, by rw [← he]⟩

theorem revPivots_nodup₁ : ((revPivots m r).map Prod.fst).Nodup := ReversedExchange.revPivots_fst m r
theorem revPivots_nodup₂ : ((revPivots m r).map Prod.snd).Nodup := ReversedExchange.revPivots_snd m r

/-- The head after the twisted reversed pivots. -/
theorem revPivots_fst (s : Swap.Shear.State (Fin m) S) (i : Fin m) :
    (revSwaps σ (revPivots m r) s).1 i = if i.val < r then σ (s.2 i.rev) else s.1 i := by
  split_ifs with hi
  · exact (revSwaps_mem _ revPivots_nodup₁ revPivots_nodup₂ s (i, i.rev)
      ((mem_revPivots_iff _).mpr ⟨hi, rfl⟩)).1
  · refine revSwaps_fst_not _ s i fun hm => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    exact hi ((mem_revPivots_iff p).mp hp).1

/-- The tail after the twisted reversed pivots. -/
theorem revPivots_snd (s : Swap.Shear.State (Fin m) S) (j : Fin m) :
    (revSwaps σ (revPivots m r) s).2 j = if j.rev.val < r then σ (s.1 j.rev) else s.2 j := by
  split_ifs with hj
  · have := (revSwaps_mem (σ := σ) _ revPivots_nodup₁ revPivots_nodup₂ s (j.rev, j.rev.rev)
      ((mem_revPivots_iff _).mpr ⟨hj, rfl⟩)).2
    rwa [Fin.rev_rev] at this
  · refine revSwaps_snd_not _ s j fun hm => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
    obtain ⟨h1, h2⟩ := (mem_revPivots_iff p).mp hp
    exact hj (by rw [h2, Fin.rev_rev]; exact h1)

theorem revSwaps_revPivots_invol (hσ : ∀ x, σ (σ x) = x) (s : Swap.Shear.State (Fin m) S) :
    revSwaps σ (revPivots m r) (revSwaps σ (revPivots m r) s) = s := by
  ext i
  · simp only [revPivots_fst, revPivots_snd, Fin.rev_rev]
    by_cases hi : i.val < r <;> simp only [hi, ↓reduceIte, hσ]
  · simp only [revPivots_fst, revPivots_snd, Fin.rev_rev]
    by_cases hi : i.rev.val < r <;> simp only [hi, ↓reduceIte, hσ]

end Pivots

/-! ### Edge programs of the form head, swaps, tail -/

section Form

variable {m : ℕ}

/-- No interchange. -/
def Free (A : FieldProgram m) : Prop := ∀ op ∈ A, AffineFieldProgram.isInterchange op = false

theorem takeWhile_free {A : FieldProgram m} (hA : Free A) (C : FieldProgram m) :
    (A ++ C).takeWhile (fun op => !AffineFieldProgram.isInterchange op) =
      A ++ C.takeWhile (fun op => !AffineFieldProgram.isInterchange op) := by
  induction A with
  | nil => rfl
  | cons op A ih =>
    have h := hA op List.mem_cons_self
    simp only [List.cons_append, List.takeWhile_cons, h, Bool.not_false, ↓reduceIte]
    rw [ih fun o ho => hA o (List.mem_cons_of_mem _ ho)]

theorem dropWhile_free {A : FieldProgram m} (hA : Free A) (C : FieldProgram m) :
    (A ++ C).dropWhile (fun op => !AffineFieldProgram.isInterchange op) =
      C.dropWhile (fun op => !AffineFieldProgram.isInterchange op) := by
  induction A with
  | nil => rfl
  | cons op A ih =>
    have h := hA op List.mem_cons_self
    simp only [List.cons_append, List.dropWhile_cons, h, Bool.not_false, ↓reduceIte]
    exact ih fun o ho => hA o (List.mem_cons_of_mem _ ho)

theorem takeWhile_swaps (L : List (Fin m × Fin m)) (hL : L ≠ []) (B : FieldProgram m) :
    (swapOps L ++ B).takeWhile (fun op => !AffineFieldProgram.isInterchange op) = [] := by
  obtain ⟨p, L, rfl⟩ := List.exists_cons_of_ne_nil hL
  simp [swapOps, AffineFieldProgram.isInterchange]

theorem dropWhile_swaps_not (L : List (Fin m × Fin m)) (hL : L ≠ []) (B : FieldProgram m) :
    (swapOps L ++ B).dropWhile (fun op => !AffineFieldProgram.isInterchange op) = swapOps L ++ B := by
  obtain ⟨p, L, rfl⟩ := List.exists_cons_of_ne_nil hL
  simp [swapOps, AffineFieldProgram.isInterchange]

theorem dropWhile_swaps (L : List (Fin m × Fin m)) {B : FieldProgram m} (hB : Free B) :
    (swapOps L ++ B).dropWhile AffineFieldProgram.isInterchange = B := by
  induction L with
  | nil =>
    cases B with
    | nil => rfl
    | cons op B =>
      show List.dropWhile AffineFieldProgram.isInterchange (op :: B) = op :: B
      rw [List.dropWhile_cons_of_neg (by simp [hB op List.mem_cons_self])]
  | cons p L ih =>
    show List.dropWhile AffineFieldProgram.isInterchange (AffineFieldProgram.Op.interchange p.1 p.2 :: (swapOps L ++ B)) = B
    rw [List.dropWhile_cons_of_pos (by rfl)]
    exact ih

theorem interchanges_free {A : FieldProgram m} (hA : Free A) : AffineFieldProgram.interchanges A = 0 := by
  simp only [AffineFieldProgram.interchanges, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro op hop; simp [hA op hop]

theorem interchanges_swapOps (L : List (Fin m × Fin m)) :
    AffineFieldProgram.interchanges (swapOps (R := ℚ) L) = L.length := by
  simp [AffineFieldProgram.interchanges, swapOps, AffineFieldProgram.isInterchange, List.filter_map,
    Function.comp_def]

theorem free_of_interchanges {p : FieldProgram m} (h : AffineFieldProgram.interchanges p = 0) : Free p := by
  intro op hop
  simp only [AffineFieldProgram.interchanges, List.length_eq_zero_iff, List.filter_eq_nil_iff] at h
  simpa using h op hop

theorem mem_interchange_free {A : FieldProgram m} (hA : Free A) (i j : Fin m) :
    AffineFieldProgram.Op.interchange i j ∉ A := fun h => by
  have := hA _ h; simp [AffineFieldProgram.isInterchange] at this

/-- The edge programs of a network: an interchange-free head, one block of disjoint interchanges
and an interchange-free tail. -/
def EdgeForm (N : RevNetwork) : Prop :=
  ∀ i p, Step.edge i p ∈ N.control → ∃ A L B, p = A ++ swapOps L ++ B ∧ Free A ∧ Free B ∧
    (L.map Prod.fst).Nodup ∧ (L.map Prod.snd).Nodup

end Form

/-! ### The pieces on streams -/

variable (N : RevNetwork) (b f : ℕ)

local instance : NeZero (N.prime ^ b) := ⟨pow_ne_zero _ N.prime_prime.ne_zero⟩

/-- The atoms of a coordinate. -/
abbrev Atom := Fin f → ZMod (N.prime ^ b)

/-- The streams of the wires. -/
abbrev Wires := N.World ⊕ N.Temp → Streams N.width (Atom N b f)

/-- **One piece on streams.** -/
def pieceSem : Graph.Piece (Seg (N.World ⊕ N.Temp) N.width) (Call (N.World ⊕ N.Temp)) → Wires N b f → Wires N b f
  | .seg (.edge w ops), x =>
    Function.update x w (twEdgeAction (atomScalar N.prime b f) (TwistedExchange.atomRev f) ops (x w))
  | .seg (.gate g), x => FramedCircuit.moduleGate g x
  | .seg (.reset w), x => Function.update x w 0
  | .call c, x => Function.update x c.1
      (twEdgeAction (atomScalar N.prime b f) (TwistedExchange.atomRev f) (swapOps (revPivots N.width c.2)) (x c.1))

/-- The pieces in order. -/
def schedRun (ps : List (Graph.Piece (Seg (N.World ⊕ N.Temp) N.width) (Call (N.World ⊕ N.Temp))))
    (x : Wires N b f) : Wires N b f :=
  ps.foldl (fun x p => pieceSem N b f p x) x

theorem schedRun_append (ps qs : List (Graph.Piece (Seg (N.World ⊕ N.Temp) N.width) (Call (N.World ⊕ N.Temp))))
    (x : Wires N b f) : schedRun N b f (ps ++ qs) x = schedRun N b f qs (schedRun N b f ps x) :=
  List.foldl_append

theorem atomRev_invol (v : Atom N b f) : TwistedExchange.atomRev f (TwistedExchange.atomRev f v) = v :=
  TwistedExchange.atomRev_atomRev f v

theorem atomRev_scalar (c : ZMod (N.prime ^ b)) :
    TwistedExchange.atomRev f (atomScalar N.prime b f c) = atomScalar N.prime b f c :=
  funext fun _ => rfl

/-- The twisted action of a block of disjoint interchanges is that of the reversed pivots it
consists of. -/
theorem swaps_action {L : List (Fin N.width × Fin N.width)} (h₁ : (L.map Prod.fst).Nodup)
    (h₂ : (L.map Prod.snd).Nodup) {r : ℕ} (hmem : ∀ p, p ∈ L ↔ p ∈ revPivots N.width r) (x : Streams N.width (Atom N b f)) :
    twEdgeAction (atomScalar N.prime b f) (TwistedExchange.atomRev f) (swapOps L) x =
      twEdgeAction (atomScalar N.prime b f) (TwistedExchange.atomRev f) (swapOps (revPivots N.width r)) x := by
  have hp : L.Perm (revPivots N.width r) :=
    (List.perm_ext_iff_of_nodup h₁.of_map revPivots_nodup₁.of_map).mpr hmem
  unfold twEdgeAction
  rw [twRun_swapOps, twRun_swapOps, funext (revSwaps_perm hp h₁ h₂)]

/-- **The schedule runs as the control**, for edge programs of the head-swaps-tail form. -/
theorem schedule_run (hE : EdgeForm N) :
    ∀ (s : List (Step (N.World ⊕ N.Temp) (FieldProgram N.width))), (∀ st ∈ s, st ∈ N.control) →
      ∀ x : Wires N b f, schedRun N b f (schedule s) x =
        Step.run (twEdgeAction (atomScalar N.prime b f) (TwistedExchange.atomRev f)) s x
  | [], _, _ => rfl
  | st :: s, hs, x => by
    have ih := schedule_run hE s (fun t ht => hs t (List.mem_cons_of_mem _ ht))
    simp only [schedule, List.flatMap_cons] at ih ⊢
    rw [schedRun_append]
    change _ = Step.run _ s (Step.execute _ st x)
    rw [← ih]
    congr 1
    cases st with
    | edge i p =>
      obtain ⟨A, L, B, rfl, hA, hB, h₁, h₂⟩ := hE i p (hs _ List.mem_cons_self)
      have hleg := N.legal_mod b i _ (hs _ List.mem_cons_self)
      have hi : AffineFieldProgram.interchanges (A ++ swapOps L ++ B) = L.length := by
        rw [AffineFieldProgram.interchanges_append, AffineFieldProgram.interchanges_append,
          interchanges_free hA, interchanges_free hB, interchanges_swapOps]; simp
      by_cases hL : L = []
      · subst hL
        have h0 : ¬ 0 < AffineFieldProgram.interchanges (A ++ swapOps [] ++ B) := by rw [hi]; simp
        simp only [stepPieces, h0, ↓reduceIte]
        rfl
      · have hpos : 0 < AffineFieldProgram.interchanges (A ++ swapOps L ++ B) := by
          rw [hi]; exact List.length_pos_of_ne_nil hL
        have hbefore : before (A ++ swapOps L ++ B) = A := by
          unfold before
          rw [List.append_assoc, takeWhile_free hA, takeWhile_swaps L hL, List.append_nil]
        have hafter : after (A ++ swapOps L ++ B) = B := by
          unfold after
          rw [List.append_assoc, dropWhile_free hA, dropWhile_swaps_not L hL, dropWhile_swaps L hB]
        have hmem : ∀ pr, pr ∈ L ↔ pr ∈ revPivots N.width (AffineFieldProgram.interchanges (A ++ swapOps L ++ B)) := by
          rintro ⟨j, k⟩
          rw [← N.block i _ (hs _ List.mem_cons_self) j k]
          simp only [List.mem_append, swapOps, List.mem_map]
          constructor
          · intro h; exact Or.inl (Or.inr ⟨(j, k), h, rfl⟩)
          · rintro ((h | ⟨⟨j', k'⟩, h, he⟩) | h)
            · exact absurd h (mem_interchange_free hA _ _)
            · simp only [AffineFieldProgram.Op.interchange.injEq] at he
              rw [← he.1, ← he.2]; exact h
            · exact absurd h (mem_interchange_free hB _ _)
        simp only [stepPieces, hpos, ↓reduceIte, hbefore, hafter, schedRun, List.foldl_cons, List.foldl_nil,
          pieceSem, Function.update_idem, Function.update_self, Step.execute]
        congr 1
        rw [twEdgeAction_append (atomRev_invol N b f) (atomRev_scalar N b f) _ _ hleg,
          twEdgeAction_append (atomRev_invol N b f) (atomRev_scalar N b f) _ _ (legal_left hleg),
          swaps_action N b f h₁ h₂ hmem]
    | gate g => rfl
    | reset w => rfl

/-- **The schedule's node theorem**: from zero temporaries, every contract role ends with the
stream of its route read at the reversed interchange. -/
theorem schedule_identity (hE : EdgeForm N) (stored : Wires N b f) (hz : ∀ t, stored (.inr t) = 0)
    (i : N.World) (a : Addr N.width (Atom N b f)) :
    schedRun N b f (schedule N.control) stored (.inl i) a =
      stored (.inl (N.route i))
        (TwistedExchange.twist (TwistedExchange.atomRev f) (Rev.revS (d := N.width) (atomScalar N.prime b f) *ᵥ a.2),
          TwistedExchange.twist (TwistedExchange.atomRev f) (Rev.revS (d := N.width) (atomScalar N.prime b f) *ᵥ a.1)) := by
  rw [schedule_run N b f hE _ (fun _ h => h)]
  exact N.run_identity b f stored hz i a

/-- The segments of the schedule have no interchanges. -/
theorem seg_free (hE : EdgeForm N) {w : N.World ⊕ N.Temp} {ops : FieldProgram N.width}
    (h : Graph.Piece.seg (Seg.edge w ops) ∈ schedule N.control) : Free ops := by
  obtain ⟨step, hs, hp⟩ := List.mem_flatMap.mp h
  cases step with
  | edge j p =>
    obtain ⟨A, L, B, rfl, hA, hB, -, -⟩ := hE j p hs
    simp only [stepPieces] at hp
    split_ifs at hp with hpos
    · simp only [List.mem_cons, Graph.Piece.seg.injEq, Seg.edge.injEq, reduceCtorEq, List.mem_nil_iff,
        or_false] at hp
      by_cases hL : L = []
      · subst hL
        simp [AffineFieldProgram.interchanges_append, interchanges_free hA, interchanges_free hB,
          interchanges_swapOps] at hpos
      rcases hp with ⟨-, hops⟩ | hF | ⟨-, hops⟩
      · rw [hops]
        unfold before
        rw [List.append_assoc, takeWhile_free hA, takeWhile_swaps L hL, List.append_nil]
        exact hA
      · exact hF.elim
      · rw [hops]
        unfold after
        rw [List.append_assoc, dropWhile_free hA, dropWhile_swaps_not L hL, dropWhile_swaps L hB]
        exact hB
    · simp only [List.mem_singleton, Graph.Piece.seg.injEq, Seg.edge.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact free_of_interchanges (by omega)
  | gate g => simp [stepPieces] at hp
  | reset w => simp [stepPieces] at hp

/-! ### The stage-2 PR97 node -/

theorem free_of_not_mem {m : ℕ} {A : FieldProgram m} (h : ∀ i j, AffineFieldProgram.Op.interchange i j ∉ A) :
    Free A := by
  intro op hop
  cases op with
  | interchange i j => exact absurd hop (h i j)
  | _ => rfl

/-- **The stage-2 PR97 edge programs** have the head-swaps-tail form. -/
theorem edgeForm97 : EdgeForm rev97m := by
  intro i p h
  obtain ⟨U, -, rfl, -⟩ := edge_interchanges (rev97m_control ▸ h)
  set V := basis97 * U * basis97'
  refine ⟨Exchange.transformOps (Rev.revFactors V).E₁' (Rev.revFactors V).E₂ ++ Exchange.crossQ (Rev.revCorr V),
    (Rev.revFactors V).L, Exchange.crossQ (-Rev.revCorr V) ++ Exchange.transformOps (Rev.revFactors V).E₁
      (Rev.revFactors V).E₂', ?_, ?_, ?_, (Rev.revFactors V).nodup₁, (Rev.revFactors V).nodup₂⟩
  · simp only [Rev.revProgram, Exchange.exchangeOps, List.append_assoc]
    simp only [← List.append_assoc]
    exact List.append_assoc _ _ _
  · refine free_of_not_mem fun a c hm => ?_
    rcases List.mem_append.mp hm with hm | hm
    · exact Rev.not_interchange_transformOps _ _ a c hm
    · exact Rev.not_interchange_crossOps _ _ _ _ a c hm
  · refine free_of_not_mem fun a c hm => ?_
    rcases List.mem_append.mp hm with hm | hm
    · exact Rev.not_interchange_crossOps _ _ _ _ a c hm
    · exact Rev.not_interchange_transformOps _ _ a c hm

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevSemantics
