module

public import IntegerMultBounds.MathlibTM2.M6.BitStageHost
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Bank

/-!
# The five-class node program

`nodeProgram` is the parent node as a finite program of 29 pieces on the `5W = 142080` roles, one
per schedule entry (`nodeProgram_schedule`):
* `stage n`: the stage piece, 160 class runs of the stage-`n` invocation (`BitStagePiece`);
* `remainder i`: the remainder child of idle `i` on every role of its pair, the exchange on the
  pending interval the hosted residuals left (`remainderSpan`);
* `bridge d s`: bank `2d` receives bank `2s`, then bank `2s + 1` receives bank `2d + 1`;
* `exchangeSides`: the two sides of every pair exchange their roles.

`logicalStep` is the same schedule on logical streams: sweeps and bridges add banks as the recipe
does, idles do nothing.

The frame bookkeeping: `levelAt τ q` is pair `q`'s level after `τ` entries, and a slot is `Pending`
at `τ` when its stage has been swept and its idle not yet run. The facts below are kernel checks
of the schedule and the frozen slots: what each kind of entry finds and leaves (`sweep_facts`,
`idle_facts`, `bridge_facts`, `exchange_facts`), and that a pair's pending slots belong to its
next idle (`pending_curIdle`) and sit above its level (`pending_level`).

**Scope.** The pieces are role-level operators on rational streams, the semantics of upstream's
idealized PR589 node: each frame change is an exact partial swap, and the stage routes and helper
charts are exact coordinate changes. The results built on this program (`runNode_interchange`,
`five_class_node`) are conditional on that idealization; `M6/DESIGN.md`, "Realizability of the
PR589 accounting", has the open realization.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open IntegerMultBounds.MathlibTM2.M6.BitOccurrences
open IntegerMultBounds.MathlibTM2.M6.BitSchedule
open IntegerMultBounds.MathlibTM2.M6.BitHosting
open Matrix

/-! ### Pieces -/

/-- A piece of the node program. -/
inductive Piece where
  | stage (n : Fin 9)
  | remainder (i : ℕ)
  | bridge (dst src : ℕ)
  | exchangeSides
  deriving DecidableEq

/-- The bank `b` role of `ρ`'s replica, port and class. -/
def withBank (ρ : Role) (b : ℕ) : Role := { ρ with bank := ⟨b % 8, Nat.mod_lt _ (by norm_num)⟩ }

/-- The other side of `ρ`'s pair. -/
def otherSide (ρ : Role) : Role :=
  withBank ρ (if ρ.bank.val % 2 = 0 then ρ.bank.val + 1 else ρ.bank.val - 1)

/-- The remainder child of idle `i` on `ρ`: the pending interval left after the hosted slots. -/
noncomputable def remainderSpan (i : ℕ) (ρ : Role) : Matrix Axis Axis ℚ :=
  (port ρ.port.val).span (7 * idleSource i + 8 * copyCount i (roleCopy ρ)) (7 * idleTarget i)

noncomputable def Piece.run : Piece → State → State
  | .stage n, X => stagePiece n X
  | .remainder i, X => fun ρ =>
      if ρ.bank.val / 2 = pairOf i then along (exchange (remainderSpan i ρ)) (X ρ) else X ρ
  | .bridge d s, X => fun ρ =>
      if ρ.bank.val = 2 * d then X ρ + X (withBank ρ (2 * s))
      else if ρ.bank.val = 2 * s + 1 then X ρ + X (withBank ρ (2 * d + 1))
      else X ρ
  | .exchangeSides, X => fun ρ => X (otherSide ρ)

/-- The node's pieces, one per schedule entry; `remainder` numbers the idles in order. -/
def piecesOf : List Entry → ℕ → List Piece
  | [], _ => []
  | .sweep s _ :: rest, i => .stage ⟨s % 9, Nat.mod_lt _ (by norm_num)⟩ :: piecesOf rest i
  | .idle _ _ :: rest, i => .remainder i :: piecesOf rest (i + 1)
  | .bridge d s :: rest, i => .bridge d s :: piecesOf rest i
  | .exchange :: rest, i => .exchangeSides :: piecesOf rest i

/-- **The five-class node**, a finite program of 29 pieces. -/
def nodeProgram : List Piece :=
  [.stage 0, .stage 1, .remainder 0, .bridge 0 1, .stage 2, .remainder 1, .bridge 0 1, .stage 3,
   .remainder 2, .bridge 1 2, .stage 4, .remainder 3, .bridge 1 2, .stage 5, .remainder 4,
   .bridge 2 3, .stage 6, .remainder 5, .bridge 2 3, .stage 7, .stage 8, .remainder 6,
   .remainder 7, .remainder 8, .remainder 9, .bridge 3 2, .bridge 2 1, .bridge 1 0,
   .exchangeSides]

theorem nodeProgram_schedule : nodeProgram = piecesOf (schedule 4) 0 := by
  decide +kernel

noncomputable def runPieces (ps : List Piece) (X : State) : State := ps.foldl (fun Y p => p.run Y) X

/-- The node on all roles. -/
noncomputable def runNode (X : State) : State := runPieces nodeProgram X

/-! ### Logical streams -/

/-- One schedule entry on logical streams. -/
def logicalStep : Entry → State → State
  | .sweep s p, L => fun ρ =>
      if s % 2 = 1 then (if ρ.bank.val = 2 * p then L ρ + L (withBank ρ (2 * p + 1)) else L ρ)
      else (if ρ.bank.val = 2 * p + 1 then L ρ + L (withBank ρ (2 * p)) else L ρ)
  | .idle _ _, L => L
  | .bridge d s, L => fun ρ =>
      if ρ.bank.val = 2 * d then L ρ + L (withBank ρ (2 * s))
      else if ρ.bank.val = 2 * s + 1 then L ρ + L (withBank ρ (2 * d + 1))
      else L ρ
  | .exchange, L => fun ρ => L (otherSide ρ)

/-! ### Positions, levels and pending slots -/

/-- The schedule entry at position `τ`. -/
def entryAt (τ : ℕ) : Entry := (schedule 4).getD τ .exchange

def stagePos (s : ℕ) : ℕ := [0, 1, 4, 7, 10, 13, 16, 19, 20].getD s 0

def idlePos (i : ℕ) : ℕ := [2, 5, 8, 11, 14, 17, 21, 22, 23, 24].getD i 0

def levelTable : List (List ℕ) :=
  [[0, 0, 0, 0], [1, 0, 0, 0], [2, 0, 0, 0], [2, 2, 0, 0], [2, 2, 0, 0], [3, 2, 0, 0],
   [3, 3, 0, 0], [3, 3, 0, 0], [3, 4, 0, 0], [3, 4, 4, 0], [3, 4, 4, 0], [3, 5, 4, 0],
   [3, 5, 5, 0], [3, 5, 5, 0], [3, 5, 6, 0], [3, 5, 6, 6], [3, 5, 6, 6], [3, 5, 7, 6],
   [3, 5, 7, 7], [3, 5, 7, 7], [3, 5, 7, 8], [3, 5, 7, 9], [9, 5, 7, 9], [9, 9, 7, 9],
   [9, 9, 9, 9], [9, 9, 9, 9], [9, 9, 9, 9], [9, 9, 9, 9], [9, 9, 9, 9], [9, 9, 9, 9]]

/-- Pair `q`'s level after `τ` entries. -/
def levelAt (τ q : ℕ) : ℕ := (levelTable.getD τ []).getD q 0

/-- The level table is the schedule's level replay. -/
theorem levelTable_replay : ∀ τ ≤ 29, ∀ q < 4,
    (((schedule 4).take τ).foldl levelStep (some ⟨[0, 0, 0, 0], 0, []⟩)).elim 0
      (fun st => st.levels.getD q 0) = levelAt τ q := by
  decide +kernel

theorem positions_check : (∀ s < 9, entryAt (stagePos s) = .sweep s (activePair s)) ∧
    (∀ i < 10, entryAt (idlePos i) = .idle (pairOf i) ((idleRanks 4).getD i 0)) := by
  decide +kernel

/-- A slot is pending at `τ`: its stage has been swept and its idle has not run. -/
def Pending (τ : ℕ) (σ : Slot) : Prop := stagePos σ.stage < τ ∧ τ ≤ idlePos σ.idle

instance (τ : ℕ) (σ : Slot) : Decidable (Pending τ σ) := by unfold Pending; infer_instance

/-- The next idle of pair `q` at or after position `τ`. -/
def curIdle (τ q : ℕ) : ℕ := ((List.range 10).find? fun i => pairOf i = q ∧ τ ≤ idlePos i).getD 0

/-- The entries that are neither sweeps nor idles: the bridges and the exchange. -/
def bridgeAt (τ : ℕ) : Option (ℕ × ℕ) :=
  match entryAt τ with
  | .bridge d s => some (d, s)
  | _ => none

theorem entry_kinds : ∀ τ < 29, (∃ s < 9, τ = stagePos s) ∨ (∃ i < 10, τ = idlePos i) ∨
    (bridgeAt τ).isSome ∨ τ = 28 := by
  decide +kernel

theorem bridge_entries : ∀ τ < 29, ∀ d s, bridgeAt τ = some (d, s) → entryAt τ = .bridge d s := by
  intro τ _ d s h
  unfold bridgeAt at h
  split at h
  · simp_all
  · simp at h

theorem exchange_entry : entryAt 28 = .exchange := by
  decide +kernel

/-! ### Pending slots through their idle and stage -/

/-- The idle and stage pairs of the hosted slots (`stageCounts`). -/
def idleStagePairs : List (ℕ × ℕ) :=
  [(0, 1), (2, 0), (2, 1), (2, 2), (4, 2), (4, 4), (4, 5), (6, 3), (6, 4), (6, 7), (7, 5), (7, 6),
   (7, 8), (8, 8)]

theorem slot_pair_mem : ∀ σ ∈ slots, (σ.idle, σ.stage) ∈ idleStagePairs := by
  decide +kernel

/-- `Pending` through the slot's idle and stage. -/
def PendingP (τ : ℕ) (x : ℕ × ℕ) : Prop := stagePos x.2 < τ ∧ τ ≤ idlePos x.1

instance (τ : ℕ) (x : ℕ × ℕ) : Decidable (PendingP τ x) := by unfold PendingP; infer_instance

/-- What a sweep finds and leaves. -/
theorem sweep_facts : ∀ s < 9, levelAt (stagePos s) (activePair s) = s ∧
    (∀ q < 4, levelAt (stagePos s + 1) q =
      if q = activePair s then s + 1 else levelAt (stagePos s) q) := by
  decide +kernel

theorem sweep_pending_pairs : ∀ x ∈ idleStagePairs, ∀ s < 9,
    (pairOf x.1 = activePair s → ¬PendingP (stagePos s) x ∧ ¬PendingP (stagePos s + 1) x) ∧
    (PendingP (stagePos s + 1) x ↔ PendingP (stagePos s) x ∨ x.2 = s) ∧
    (x.2 = s → ¬PendingP (stagePos s) x) := by
  decide +kernel

theorem sweep_pending : ∀ σ ∈ slots, ∀ s < 9,
    (pairOf σ.idle = activePair s → ¬Pending (stagePos s) σ ∧ ¬Pending (stagePos s + 1) σ) ∧
    (Pending (stagePos s + 1) σ ↔ Pending (stagePos s) σ ∨ σ.stage = s) ∧
    (σ.stage = s → ¬Pending (stagePos s) σ) :=
  fun σ hσ s hs => sweep_pending_pairs _ (slot_pair_mem σ hσ) s hs

/-- What an idle finds and leaves. -/
theorem idle_facts : ∀ i < 10, levelAt (idlePos i) (pairOf i) = idleSource i ∧
    levelAt (idlePos i + 1) (pairOf i) = idleTarget i ∧
    ∀ q < 4, q ≠ pairOf i → levelAt (idlePos i + 1) q = levelAt (idlePos i) q := by
  decide +kernel

theorem idle_pending_pairs : ∀ x ∈ idleStagePairs, ∀ i < 10,
    (pairOf x.1 = pairOf i → (PendingP (idlePos i) x ↔ x.1 = i)) ∧
    (PendingP (idlePos i + 1) x ↔ PendingP (idlePos i) x ∧ x.1 ≠ i) := by
  decide +kernel

theorem idle_pending : ∀ σ ∈ slots, ∀ i < 10,
    (pairOf σ.idle = pairOf i → (Pending (idlePos i) σ ↔ σ.idle = i)) ∧
    (Pending (idlePos i + 1) σ ↔ Pending (idlePos i) σ ∧ σ.idle ≠ i) :=
  fun σ hσ i hi => idle_pending_pairs _ (slot_pair_mem σ hσ) i hi

/-- What a bridge finds and leaves, as a check. -/
def bridgeOk (τ : ℕ) : Bool :=
  match bridgeAt τ with
  | some (d, s) => decide (d < 4) && decide (s < 4) && decide (d ≠ s) &&
      decide (levelAt τ d = levelAt τ s) &&
      (List.range 4).all (fun q => decide (levelAt (τ + 1) q = levelAt τ q)) &&
      idleStagePairs.all (fun y => decide ((pairOf y.1 = d ∨ pairOf y.1 = s) → ¬PendingP τ y) &&
        decide (PendingP (τ + 1) y ↔ PendingP τ y))
  | none => true

theorem bridgeOk_all : ∀ τ < 29, bridgeOk τ = true := by
  decide +kernel

theorem bridge_unfold (τ : ℕ) (hτ : τ < 29) (x : ℕ × ℕ) (hb : bridgeAt τ = some x) :
    x.1 < 4 ∧ x.2 < 4 ∧ x.1 ≠ x.2 ∧ levelAt τ x.1 = levelAt τ x.2 ∧
      (∀ q < 4, levelAt (τ + 1) q = levelAt τ q) ∧
      ∀ y ∈ idleStagePairs, ((pairOf y.1 = x.1 ∨ pairOf y.1 = x.2) → ¬PendingP τ y) ∧
        (PendingP (τ + 1) y ↔ PendingP τ y) := by
  have h := bridgeOk_all τ hτ
  rw [bridgeOk, hb] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, fun y hy => h6 y hy⟩

/-- What a bridge finds and leaves. -/
theorem bridge_facts (τ : ℕ) (hτ : τ < 29) (d : ℕ) (_hd : d < 4) (s : ℕ) (_hs : s < 4)
    (hb : bridgeAt τ = some (d, s)) :
    d ≠ s ∧ levelAt τ d = levelAt τ s ∧ ∀ q < 4, levelAt (τ + 1) q = levelAt τ q :=
  let h := bridge_unfold τ hτ _ hb
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem bridge_pairs (τ : ℕ) (hτ : τ < 29) (x : ℕ × ℕ) (hb : bridgeAt τ = some x) :
    x.1 < 4 ∧ x.2 < 4 :=
  let h := bridge_unfold τ hτ x hb
  ⟨h.1, h.2.1⟩

theorem bridge_pending : ∀ σ ∈ slots, ∀ τ < 29, ∀ x, bridgeAt τ = some x →
    ((pairOf σ.idle = x.1 ∨ pairOf σ.idle = x.2) → ¬Pending τ σ) ∧
    (Pending (τ + 1) σ ↔ Pending τ σ) :=
  fun σ hσ τ hτ x hx => (bridge_unfold τ hτ x hx).2.2.2.2.2 _ (slot_pair_mem σ hσ)

/-- The exchange finds every pair at level `9` and no slot pending. -/
theorem exchange_facts : (∀ q < 4, levelAt 28 q = 9) ∧ ∀ σ ∈ slots, ¬Pending 28 σ := by
  have h : (∀ q < 4, levelAt 28 q = 9) ∧ ∀ x ∈ idleStagePairs, ¬PendingP 28 x := by
    decide +kernel
  exact ⟨h.1, fun σ hσ => h.2 _ (slot_pair_mem σ hσ)⟩

theorem start_facts : (∀ q < 4, levelAt 0 q = 0) ∧ ∀ σ ∈ slots, ¬Pending 0 σ := by
  have h : (∀ q < 4, levelAt 0 q = 0) ∧ ∀ x ∈ idleStagePairs, ¬PendingP 0 x := by
    decide +kernel
  exact ⟨h.1, fun σ hσ => h.2 _ (slot_pair_mem σ hσ)⟩

/-- A pair's pending slots belong to its next idle. -/
theorem pending_curIdle : ∀ σ ∈ slots, ∀ τ ≤ 29, Pending τ σ → σ.idle = curIdle τ (pairOf σ.idle) := by
  have h : ∀ x ∈ idleStagePairs, ∀ τ ≤ 29, PendingP τ x → x.1 = curIdle τ (pairOf x.1) := by
    decide +kernel
  exact fun σ hσ => h _ (slot_pair_mem σ hσ)

/-- A pending slot sits above its pair's level. -/
theorem pending_level : ∀ σ ∈ slots, ∀ τ ≤ 29, Pending τ σ →
    levelAt τ (pairOf σ.idle) = idleSource σ.idle := by
  have h : ∀ x ∈ idleStagePairs, ∀ τ ≤ 29, PendingP τ x → levelAt τ (pairOf x.1) = idleSource x.1 := by
    decide +kernel
  exact fun σ hσ => h _ (slot_pair_mem σ hσ)

end IntegerMultBounds.MathlibTM2.M6.BitNode
