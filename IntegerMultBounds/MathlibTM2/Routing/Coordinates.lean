module

public import IntegerMultBounds.MathlibTM2.Routing.Shear
public import IntegerMultBounds.MathlibTM2.Routing.PackedShear
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Fin

/-!
# Coordinate interpretation of packed shears

The target coordinates are indexed by packed digits. All other logical coordinates
live in the unchanged field; a source descriptor selects them without requiring
contiguity or order. The coordinate equivalence is a mathematical placement, not a
free physical move. The full packed endpoint separately preserves upper digits
and both borrowed fields, which are not discarded by this logical observation.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.Coordinates

open IntegerMultBounds.Compact IntegerMultBounds.Compact.Radix

variable {ι σ : Type*} [DecidableEq ι] {n : ℕ}

/-- Placement of all target and untouched logical coordinates, with no omissions. -/
def targets (e : ι ≃ (Fin n ⊕ σ)) : Finset ι :=
  Finset.univ.image fun j => e.symm (Sum.inl j)

@[simp] theorem mem_targets (e : ι ≃ (Fin n ⊕ σ)) (i : ι) :
    i ∈ targets e ↔ ∃ j, e i = Sum.inl j := by
  simp only [targets, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, e.apply_symm_apply _⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, by rw [← hj, e.symm_apply_apply]⟩

/-- Sources of selected targets; the irrelevant values off the targets are identities. -/
def source (e : ι ≃ (Fin n ⊕ σ)) (s : Fin n → σ) (i : ι) : ι :=
  match e i with
  | .inl j => e.symm (.inr (s j))
  | .inr _ => i

theorem source_off (e : ι ≃ (Fin n ⊕ σ)) (s : Fin n → σ) :
    ∀ i ∈ targets e, source e s i ∉ targets e := by
  intro i hi
  obtain ⟨j, hj⟩ := (mem_targets e i).mp hi
  simp [source, hj]

/-- Actual zero/one list read from the untouched coordinates. -/
def read (s : Fin n → σ) (c : σ → Bool) : List ℤ :=
  List.ofFn fun j => if c (s j) then 1 else 0

@[simp] theorem read_length (s : Fin n → σ) (c : σ → Bool) :
    (read s c).length = n := by simp [read]

theorem read_bits (s : Fin n → σ) (c : σ → Bool) : Bits (read s c) := by
  intro z hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
  cases c (s j) <;> simp

@[simp] theorem read_parities (s : Fin n → σ) (c : σ → Bool) :
    (read s c).map Packed.parity = List.ofFn fun j => c (s j) := by
  simp only [read, List.map_ofFn]
  congr 1
  funext j
  cases h : c (s j) <;> simp [Packed.parity, h]

/-- Observe logical bits, retaining every untouched coordinate. -/
def decode (e : ι ≃ (Fin n ⊕ σ)) (B L : ℤ)
    (x : (σ → Bool) × LateAddress B L n) (i : ι) : Bool :=
  match e i with
  | .inl j => ((digits (2 * L) n x.2.2.1.val).map Packed.parity)[j.val]!
  | .inr k => x.1 k

/-- The actual modular program implements the requested shear on its good set. -/
theorem program_decode (e : ι ≃ (Fin n ⊕ σ)) (s : Fin n → σ)
    (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (x : (σ → Bool) × LateAddress B L n) (hx : lateGood B L n x.2) :
    decode e B L (Packed.program B L hB hL (read s) (read_length s) x) =
      shear (targets e) (source e s) (decode e B L x) := by
  obtain ⟨hc, _, _, _, hp⟩ :=
    Packed.program_endpoint B L hB hL (read s) (read_length s) (read_bits s) x hx
  funext i
  cases hi : e i with
  | inl j =>
    have ht : i ∈ targets e := (mem_targets e i).mpr ⟨j, hi⟩
    simp only [decode, hi]
    rw [hp, read_parities]
    simp [shear, Routing.toggle, ht, source, decode, hi,
      digits_length, j.isLt]
  | inr k =>
    have ht : i ∉ targets e := by simp [hi]
    simp [shear, Routing.toggle, ht, decode, hi, hc]

/-- The same endpoint is the logical borrowed-control construction, for arbitrary controls. -/
theorem program_borrowed (e : ι ≃ (Fin n ⊕ σ)) (s : Fin n → σ)
    (B L : ℤ) (hB : 1 ≤ B) (hL : 0 < L)
    (x : (σ → Bool) × LateAddress B L n) (hx : lateGood B L n x.2)
    (control : ι → Bool) :
    borrowedShear (targets e) (source e s) (decode e B L x) control =
      (decode e B L (Packed.program B L hB hL (read s) (read_length s) x), control) := by
  rw [borrowedShear_eq _ _ (source_off e s), program_decode e s B L hB hL x hx]

end IntegerMultBounds.MathlibTM2.Routing.Coordinates
