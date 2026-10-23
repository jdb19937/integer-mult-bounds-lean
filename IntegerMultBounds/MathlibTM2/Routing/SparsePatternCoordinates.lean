module

public import IntegerMultBounds.MathlibTM2.Routing.SparseCoordinateSpecification
public import Mathlib.Data.List.OfFn
public import IntegerMultBounds.MathlibTM2.Routing.SparsePattern

/-! Sparse patterns represented by mirrored absolute coordinates. Mirroring
matches the reversed dense selector order consumed by descriptor compilation.
Inactive entries retain selector zero; repeated sources are unrestricted. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable {W m N : ℕ}

def sparsePatternCoordinates (pos : ℕ → ℕ) (src : Fin m → Option (Fin W)) : List (ℕ × Fin (W + 1)) :=
  (List.ofFn (fun j : Fin m => (N - 1 - pos j.val, (src j).elim 0 Fin.succ))).reverse

theorem sparsePatternCoordinates_target (pos : ℕ → ℕ) (hpos : StrictMono pos)
    (src : Fin m → Option (Fin W)) (hbound : ∀ j < m, pos j < N)
    (x : ℕ) (q : Fin (W + 1)) (hm : (x, q) ∈ sparsePatternCoordinates (N := N) pos src) :
    (List.ofFn (patternIndex (sparsePattern (L := N) pos src))).reverse[x]? = some q := by
  simp only [sparsePatternCoordinates, List.mem_reverse, List.mem_ofFn] at hm
  obtain ⟨j, he⟩ := hm
  have hx : x = N - 1 - pos j.val := (congrArg Prod.fst he).symm
  have hq : q = (src j).elim 0 Fin.succ := (congrArg Prod.snd he).symm
  subst x; subst q
  have hj := hbound j.val j.isLt
  rw [List.getElem?_reverse (by simp; omega), List.length_ofFn, List.getElem?_ofFn]
  have hi : N - 1 - (N - 1 - pos j.val) = pos j.val := by omega
  simp only [hi, hj, ↓reduceDIte]
  have hp := sparsePattern_at hpos src hbound j
  simp only [patternIndex, hp]

theorem sparsePatternCoordinates_gap (pos : ℕ → ℕ)
    (src : Fin m → Option (Fin W)) (hbound : ∀ j < m, pos j < N)
    (x : ℕ) (hx : x < N)
    (hoff : ∀ q, (x, q) ∉ sparsePatternCoordinates (N := N) pos src) :
    (List.ofFn (patternIndex (sparsePattern (L := N) pos src))).reverse[x]? = some 0 := by
  have hi : N - 1 - x < N := by omega
  have hnone : ¬ ∃ j : Fin m, pos j.val = N - 1 - x := by
    rintro ⟨j, hj⟩
    apply hoff ((src j).elim 0 Fin.succ)
    simp only [sparsePatternCoordinates, List.mem_reverse, List.mem_ofFn]
    refine ⟨j, ?_⟩
    apply Prod.ext
    · simp only
      have hb := hbound j.val j.isLt
      omega
    · rfl
  rw [List.getElem?_reverse (by simpa using hx), List.length_ofFn, List.getElem?_ofFn]
  simp only [hi, ↓reduceDIte, patternIndex, sparsePattern_off pos src ⟨N - 1 - x, hi⟩ hnone, Option.elim_none]

theorem sparsePatternCoordinates_ordered (pos : ℕ → ℕ) (hpos : StrictMono pos)
    (src : Fin m → Option (Fin W)) (hbound : ∀ j < m, pos j < N) :
    (sparsePatternCoordinates (N := N) pos src).Pairwise (fun a b => a.1 < b.1) := by
  rw [sparsePatternCoordinates, List.pairwise_reverse, List.pairwise_ofFn]
  intro i j hij
  have hp := hpos (show i.val < j.val from hij)
  have hi := hbound i.val i.isLt
  have hj := hbound j.val j.isLt
  simp only
  omega

end IntegerMultBounds.MathlibTM2.Routing
