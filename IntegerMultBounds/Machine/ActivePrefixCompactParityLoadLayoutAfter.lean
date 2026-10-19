module

public import IntegerMultBounds.Machine.ActivePrefixCompactParityLoad
public import IntegerMultBounds.Machine.ActivePrefixLayoutSwap
import Mathlib.Tactic.Positivity.Finset

/-! The physical compact parity action is the literal back-fiber rotation in
the unchanged full array. These views are ordinal casts only, and their offset
lookup is the actual current target parity after the compact T/back exchange. -/

@[expose] public section

namespace IntegerMultBounds.Machine.ActivePrefixCompactParityLoadLayoutAfter
open CompactGadgetReservationShape (Shape)
open CompactActiveTargetGeometry
open ActivePrefixLayoutShapes
open ActivePrefixLayoutGeometry
open RecursiveInterchangeRows (pack)
open BinaryAddressTableData (row)

variable (s : Shape) (p : Parameters s) (offset : ℕ) (hfit : offset+p.f*p.q≤p.after)

def shape := backAfterShape s p offset hfit
def suffix := compactSuffix s (p.n*p.b)

theorem prefix_eq (rows : ℕ) :
    ActivePrefixCompactParityLoadData.prefixCount (shape s p offset hfit) rows=
      backPrefix s (p.n*p.b) (p.n*p.q) p.before p.after rows :=
  (back_count s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits).symm

theorem volume_eq (rows : ℕ) :
    ActivePrefixCompactParityLoadData.volume (shape s p offset hfit) rows (suffix s p)=rows*s.recordWidth := by
  unfold ActivePrefixCompactParityLoadData.volume
  rw [prefix_eq]
  exact back_volume s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize

def view {rows : ℕ} (x : Fin (rows*s.recordWidth) → Bool) :
    ActivePrefixCompactParityLoadData.Array (shape s p offset hfit) rows (suffix s p) :=
  fun i => x (Fin.cast (volume_eq s p offset hfit rows) i)

def prefixIndex {rows : ℕ} (x : Address s p rows) :
    Fin (ActivePrefixCompactParityLoadData.prefixCount (shape s p offset hfit) rows) :=
  Fin.cast (prefix_eq s p offset hfit rows).symm
    (backPrefixIndex s (p.n*p.b) (p.n*p.q) p.before p.after rows x)

def parity {rows : ℕ} (x : Address s p rows) :=
  Counter.value (Gather.gather (fun z _ => z) (PackedArith.parity p.q p.b p.hb p.hbq)
    (row (p.n*p.q) x.target.val) (ActivePrefixLayoutBack.afterControls s p x offset) p.n)

theorem actual_offset {rows : ℕ} (x : Address s p rows) :
    PackedOffsetPayloadValue.offset
      (ActivePrefixCompactParityLoadData.offsets (shape s p offset hfit) rows) (p.n*p.b)
      (prefixIndex s p offset hfit x).val=parity s p offset x := by
  exact congrArg Counter.value (ActivePrefixLayoutBack.pure_after s p offset hfit x)

theorem source_index {rows : ℕ} (x : Address s p rows) :
    Fin.cast (volume_eq s p offset hfit rows)
      (FiberLayoutData.index (prefixIndex s p offset hfit x)
        (splitBack s (p.n*p.b) p.compactFits x.back).1
        (pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload))=
      CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize x := by
  apply Fin.ext
  change (FiberLayoutData.index (prefixIndex s p offset hfit x)
      (splitBack s (p.n*p.b) p.compactFits x.back).1
      (pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload)).val=_
  have h := congrArg Fin.val (back_index s (p.n*p.b) (p.n*p.q) p.before p.after rows p.compactFits p.activeSize x)
  exact h

/-- Forward destination semantics for every original array bit, including
arbitrary dirty back bits, active spectators and all payload coordinates. -/
theorem entry {rows : ℕ} (array : Fin (rows*s.recordWidth) → Bool) (x : Address s p rows) :
    ActivePrefixCompactParityLoad.result (shape s p offset hfit) rows (suffix s p)
      (view s p offset hfit array)
      (FiberLayoutData.index (prefixIndex s p offset hfit x)
        ⟨((splitBack s (p.n*p.b) p.compactFits x.back).1.val+parity s p offset x)%2^(p.n*p.b),
          Nat.mod_lt _ (by positivity)⟩
        (pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload))=
      array (CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize x) := by
  have h := ActivePrefixCompactParityLoad.entry (shape s p offset hfit) rows (suffix s p)
    (view s p offset hfit array) (prefixIndex s p offset hfit x)
    (splitBack s (p.n*p.b) p.compactFits x.back).1
    (pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload)
  change _=array (Fin.cast (volume_eq s p offset hfit rows) _) at h
  rw [source_index] at h
  have hoff : PackedOffsetPayloadValue.offset
      (ActivePrefixCompactParityLoadData.offsets (shape s p offset hfit) rows)
      (ActivePrefixCompactParityLoadData.width (shape s p offset hfit))
      (prefixIndex s p offset hfit x).val=parity s p offset x := actual_offset s p offset hfit x
  rw [hoff] at h
  exact h

/-- After the existing T/back exchange the same paid action rotates original
compact T by pure parity of the unchanged active target. -/
theorem after_swap_entry {rows : ℕ} (array : Fin (rows*s.recordWidth) → Bool) (x : Address s p rows) :
    ActivePrefixCompactParityLoad.result (shape s p offset hfit) rows (suffix s p)
      (view s p offset hfit array)
      (FiberLayoutData.index (prefixIndex s p offset hfit (ActivePrefixLayoutSwap.swapT s p x))
        ⟨(x.t.val+parity s p offset x)%2^(p.n*p.b),Nat.mod_lt _ (by positivity)⟩
        (pack (splitBack s (p.n*p.b) p.compactFits x.back).2 x.payload))=
      array (CompactActiveTargetLayout.index s (p.n*p.b) (p.n*p.q) p.before p.after rows
        p.compactFits p.activeSize (ActivePrefixLayoutSwap.swapT s p x)) := by
  have h := entry s p offset hfit array (ActivePrefixLayoutSwap.swapT s p x)
  rw [ActivePrefixLayoutSwap.split_swap] at h
  exact h

end IntegerMultBounds.Machine.ActivePrefixCompactParityLoadLayoutAfter
