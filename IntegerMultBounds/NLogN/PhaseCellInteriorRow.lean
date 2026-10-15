module

public import IntegerMultBounds.NLogN.PhaseCellBoundarySupport
public import IntegerMultBounds.NLogN.PhaseCellToeplitz

/-! Interior rows of the actual rounded periodic Gaussian matrix. A row whose
band stays in the array and in one phase cell has no aliasing, and every
entry is exactly the diagonal similarity of the shared Toeplitz kernel:
`A i l = a i * G(|l-i|) / a l`. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix

open scoped BigOperators
open PhaseCellRow
variable (s t : ℕ) [NeZero s]

theorem window_eq_Icc {E : Type*} [AddCommMonoid E] (f : ℤ → E) (w : ℕ) :
    window f w=∑ k∈Finset.Icc (-(w : ℤ)) w, f k := by
  induction w with
  | zero => simp [window]
  | succ w ih =>
    have hset : Finset.Icc (-((w+1 : ℕ) : ℤ)) ((w+1 : ℕ) : ℤ)=
        insert ((w : ℤ)+1) (insert (-((w : ℤ)+1)) (Finset.Icc (-(w : ℤ)) w)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [hset, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ←ih]
    simp only [window, Finset.sum_range_succ]
    abel

/-- Natural index arithmetic for a band offset from an interior row. -/
theorem interior_offset (w : ℕ) (i l : ZMod s) (hlo : w ≤ i.val) (hhi : i.val+w < s)
    (k : ℤ) (hk : k∈Finset.Icc (-(w : ℤ)) w) :
    i+(k : ZMod s)=l ↔ k=(l.val : ℤ)-i.val := by
  have hk' := Finset.mem_Icc.mp hk
  constructor
  · intro h
    have hv : l=(((i.val : ℤ)+k : ℤ) : ZMod s) := by
      rw [←h, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
    have := congrArg (fun z : ZMod s => (z.val : ℤ)) hv
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (by omega) (by omega)] at this
    omega
  · intro h
    rw [h, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
    ring

/-- An interior row is the diagonal similarity of the shared kernel. -/
theorem interior_row (hst : s<t) (p u : ℕ) (i l : ZMod s)
    (hi : Interior s t (PhaseCellBand.width p u) i)
    (hl : PhaseCellConcreteCoefficients.similarity (2^15*p) s t u l.val≠0) :
    realMatrix s t p u i l=
      (PhaseCellConcreteCoefficients.similarity (2^15*p) s t u i.val : ℝ)*
        PhaseCellToeplitz.coeff (2^15*p) s t u (PhaseCellBand.width p u)
          (ToeplitzInverse.gap i.val l.val)/
        (PhaseCellConcreteCoefficients.similarity (2^15*p) s t u l.val : ℝ) := by
  set w := PhaseCellBand.width p u
  obtain ⟨hlo, hhi, hph⟩ := hi
  have hs : 0<s := Nat.pos_of_ne_zero (NeZero.ne s)
  set k₀ : ℤ := (l.val : ℤ)-i.val
  have hsum : matrix s t p u i l=if k₀∈Finset.Icc (-(w : ℤ)) w then
      PhaseCellCrossCell.entry (2^15*p) s t u w (i.val : ℤ) (i.val+k₀) else 0 := by
    unfold matrix
    rw [window_eq_Icc]
    rw [Finset.sum_congr rfl fun (k : ℤ) hk => show (if i+(k : ZMod s)=l then
        PhaseCellCrossCell.entry (2^15*p) s t u w (i.val : ℤ) (i.val+k) else 0)=
        (if k=k₀ then PhaseCellCrossCell.entry (2^15*p) s t u w (i.val : ℤ) (i.val+k) else 0) by
      simp only [interior_offset s w i l hlo hhi k hk]; rfl]
    rw [Finset.sum_ite_eq']
  have hend : (i.val : ℤ)+k₀=l.val := by ring
  unfold realMatrix
  rw [hsum, hend]
  have hkernel := PhaseCellToeplitz.kernel_natAbs (P := 2^15*p) (s := s) (t := t) (u := u)
    (w := w) ((l.val : ℤ)-i.val)
  have hgap : ((l.val : ℤ)-i.val).natAbs=ToeplitzInverse.gap i.val l.val := by
    unfold ToeplitzInverse.gap
    omega
  split
  · rename_i hin
    have hin' := Finset.mem_Icc.mp hin
    have hph' : PhaseCellCrossCell.phaseQ s t i.val=PhaseCellCrossCell.phaseQ s t l.val := by
      have h1 := PhaseCellIntervals.phase_eq_of_between (l := (i.val : ℤ)) hs hst.le
        (by omega) (by omega) hph
      have h2 := PhaseCellIntervals.phase_eq_of_between (l := (l.val : ℤ)) hs hst.le
        (by omega) (by omega) hph
      rw [PhaseCellCrossCell.phaseQ_eq s t hs, PhaseCellCrossCell.phaseQ_eq s t hs, h1, h2]
    unfold PhaseCellCrossCell.entry
    simp only [hph', ↓reduceIte]
    unfold PhaseCellConcreteCoefficients.entry
    rw [PhaseCellExecutableCoefficients.entry_similarity _ _ _ _ _ _ hl]
    rw [show PhaseCellExecutableCoefficients.kernel (2^15*p) w
        (PhaseCellConcreteCoefficients.gaussianArg s t u) ((l.val : ℤ)-i.val)=
      PhaseCellConcreteCoefficients.kernel (2^15*p) s t u w ((l.val : ℤ)-i.val) from rfl,
      hkernel, hgap]
    push_cast
    rfl
  · rename_i hout
    have hw : w<ToeplitzInverse.gap i.val l.val := by
      rw [←hgap]
      simp only [Finset.mem_Icc, not_and_or, not_le] at hout
      omega
    have hz : PhaseCellToeplitz.coeff (2^15*p) s t u w (ToeplitzInverse.gap i.val l.val)=0 := by
      unfold PhaseCellToeplitz.coeff PhaseCellConcreteCoefficients.kernel
        PhaseCellExecutableCoefficients.kernel
      have h1 : ToeplitzInverse.gap i.val l.val≠0 := by omega
      have h2 : ¬ToeplitzInverse.gap i.val l.val≤w := by omega
      simp [h1, h2]
    rw [hz]
    simp

end IntegerMultBounds.NLogN.PhaseCellMatrix
