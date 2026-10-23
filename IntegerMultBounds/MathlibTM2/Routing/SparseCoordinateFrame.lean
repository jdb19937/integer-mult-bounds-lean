module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateLoop

/-! Closed tape contents after absolute-coordinate traversal: complete archived
input, computed compact frames, final cursor and unchanged spectator tapes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A : ℕ}

def sparseCoordinateEnd (cursor : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => cursor
  | (x, _) :: rest => sparseCoordinateEnd (x + 1) rest

def sparseCoordinateOutput (L Ls cursor : ℕ) : List (ℕ × ℕ) → List (Fin (A + 4))
  | [] => []
  | (x, q) :: rest => sparseCoordinateOutput L Ls (x + 1) rest ++
      (binSyms L (x - cursor) ++ separator :: (binSyms Ls q ++ [separator]))

theorem sparseCoordinateTrace_keep (R : Fin T → List (Fin (A + 4)))
    (rg : SparseCoordinateReg → Fin T) (L Ls cursor : ℕ) (entries : List (ℕ × ℕ))
    (j : Fin T) (hs : j ≠ rg .src) (ha : j ≠ rg .archive) (hc : j ≠ rg .cursor) (hd : j ≠ rg .dst) :
    sparseCoordinateTraceBank R rg L Ls cursor entries j = R j := by
  induction entries generalizing R cursor with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    rw [sparseCoordinateTraceBank, ih]
    simp [sparseCoordinateCallBank, hs, ha, hc, hd]

theorem sparseCoordinateTrace_src (R : Fin T → List (Fin (A + 4)))
    (rg : SparseCoordinateReg → Fin T) (hrg : Function.Injective rg)
    (L Ls cursor : ℕ) (entries : List (ℕ × ℕ))
    (hsrc : R (rg .src) = sparseCoordinateFrames L Ls entries) :
    sparseCoordinateTraceBank R rg L Ls cursor entries (rg .src) = [] := by
  induction entries generalizing R cursor with
  | nil => exact hsrc
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    apply ih
    simp [sparseCoordinateCallBank, hrg.eq_iff]

theorem sparseCoordinateTrace_archive (R : Fin T → List (Fin (A + 4)))
    (rg : SparseCoordinateReg → Fin T) (hrg : Function.Injective rg)
    (L Ls cursor : ℕ) (entries : List (ℕ × ℕ)) :
    sparseCoordinateTraceBank R rg L Ls cursor entries (rg .archive) =
      (sparseCoordinateFrames L Ls entries).reverse ++ R (rg .archive) := by
  induction entries generalizing R cursor with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    rw [sparseCoordinateTraceBank, ih]
    simp [sparseCoordinateCallBank, sparseCoordinateFrames, hrg.eq_iff, List.reverse_append, List.append_assoc]

theorem sparseCoordinateTrace_cursor (R : Fin T → List (Fin (A + 4)))
    (rg : SparseCoordinateReg → Fin T) (L Ls cursor : ℕ) (entries : List (ℕ × ℕ))
    (hc : R (rg .cursor) = binSyms L cursor) :
    sparseCoordinateTraceBank R rg L Ls cursor entries (rg .cursor) =
      binSyms L (sparseCoordinateEnd cursor entries) := by
  induction entries generalizing R cursor with
  | nil => exact hc
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    apply ih
    simp [sparseCoordinateCallBank]

theorem sparseCoordinateTrace_output (R : Fin T → List (Fin (A + 4)))
    (rg : SparseCoordinateReg → Fin T) (hrg : Function.Injective rg)
    (L Ls cursor : ℕ) (entries : List (ℕ × ℕ)) :
    sparseCoordinateTraceBank R rg L Ls cursor entries (rg .dst) =
      sparseCoordinateOutput L Ls cursor entries ++ R (rg .dst) := by
  induction entries generalizing R cursor with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨x, q⟩ := pair
    rw [sparseCoordinateTraceBank, ih]
    simp [sparseCoordinateCallBank, sparseCoordinateOutput, hrg.eq_iff, List.append_assoc]

end IntegerMultBounds.MathlibTM2.Routing
