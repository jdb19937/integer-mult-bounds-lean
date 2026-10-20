module

public import IntegerMultBounds.NLogN.PhaseCellConcreteCoefficients
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Log
public import IntegerMultBounds.BinaryWords

/-! Executable cross-cell entries of the structured rounded matrix. These
sample the original normalized lattice coefficient directly, whereas entries
within a cell retain the shared Toeplitz kernel. Phase decisions use integer
rounding, not a real oracle. Periodic aliases and the omitted band tail are
separate obligations; this file does not identify a finite matrix with the
complete periodized resampling operator. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellCrossCell

open PhaseCellRationalArgs

def phaseQ (s t : ℕ) (j : ℤ) : ℤ := nearestQ s t j-j

def latticeQ (s t u : ℕ) (j δ : ℤ) : ℚ :=
  (u : ℚ)*(((t : ℚ)*δ/s+betaQ s t j)^2-betaQ s t (j+δ)^2)

def direct (P s t u : ℕ) (j k : ℤ) : ℚ :=
  (PhaseCellConcreteCoefficients.encode (latticeQ s t u j (k-j))).value P

/-- The complete unaliased band: structured within cells, direct across cells. -/
def entry (P s t u w : ℕ) (j k : ℤ) : ℚ :=
  if phaseQ s t j=phaseQ s t k then
    PhaseCellConcreteCoefficients.entry P s t u w j k
  else if (k-j).natAbs≤w then direct P s t u j k else 0

theorem phaseQ_eq (s t : ℕ) (hs : 0 < s) (j : ℤ) :
    phaseQ s t j=PhaseCell.phase s t j := by
  unfold phaseQ PhaseCell.phase
  rw [nearestQ_eq s t hs j]

theorem latticeQ_cast (s t u : ℕ) (hs : 0 < s) (j δ : ℤ) :
    (latticeQ s t u j δ : ℝ) =
      (u : ℝ)*(((t : ℝ)*δ/s+beta s t j)^2-beta s t (j+δ)^2) := by
  simp [latticeQ, betaQ_cast s t hs]

/-- The original nearest-rounding exponent is nonnegative even across cells. -/
theorem latticeQ_nonneg (s t u : ℕ) (hs : 0 < s) (hst : s < t) (j δ : ℤ) :
    0≤latticeQ s t u j δ := by
  by_cases hδ : δ=0
  · subst δ
    simp [latticeQ]
  let instS : NeZero s := ⟨by omega⟩
  let instT : NeZero t := ⟨by omega⟩
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  have hstR : (s : ℝ)≤t := by exact_mod_cast hst.le
  have hgap : 0≤(t : ℝ)/s-1 := by
    have : (1 : ℝ)≤(t : ℝ)/s := (le_div_iff₀ hsR).mpr (by simpa using hstR)
    linarith
  have h := exponent_ge s t hst (beta s t j) (beta s t (j+δ))
    (abs_beta_le s t j) (abs_beta_le s t (j+δ)) δ hδ
  have hφ : 0≤((t : ℝ)*δ/s+beta s t j)^2-beta s t (j+δ)^2 := by
    exact (mul_nonneg (mul_nonneg (by norm_num) hgap) (sq_nonneg _)).trans h
  apply (Rat.cast_nonneg (K := ℝ)).mp
  rw [latticeQ_cast s t u hs j δ]
  exact mul_nonneg (Nat.cast_nonneg u) hφ

theorem direct_target (s t u : ℕ) (hs : 0 < s) (hst : s < t)
    (α : ℝ) (hu : α^2=(u : ℝ)) (j k : ℤ) :
    (PhaseCellConcreteCoefficients.encode (latticeQ s t u j (k-j))).target =
      Real.exp (normExp s t α j (k-j)) := by
  rw [PhaseCellConcreteCoefficients.encode_target _ (latticeQ_nonneg s t u hs hst j (k-j)),
    latticeQ_cast s t u hs j (k-j)]
  unfold normExp
  congr 1
  rw [hu]
  ring

theorem direct_spec (P s t u : ℕ) (hP : 13≤P) (hs : 0<s) (hst : s<t)
    (α : ℝ) (hu : α^2=(u : ℝ)) (j k : ℤ) :
    0≤(direct P s t u j k : ℝ) ∧
      (direct P s t u j k : ℝ)≤Real.exp (normExp s t α j (k-j)) ∧
      |(direct P s t u j k : ℝ)-Real.exp (normExp s t α j (k-j))|≤4/(2 : ℝ)^P := by
  have h := PhaseCellExecutableCoefficients.ExpArg.value_spec P
    (PhaseCellConcreteCoefficients.encode (latticeQ s t u j (k-j))) hP
  rw [direct_target s t u hs hst α hu j k] at h
  exact h

@[simp] theorem entry_diag (P s t u w : ℕ) (j : ℤ) : entry P s t u w j j=1 := by
  simp [entry]

theorem entry_outside (P s t u w : ℕ) (j k : ℤ) (hband : w<(k-j).natAbs) :
    entry P s t u w j k=0 := by
  unfold entry
  split_ifs
  · exact PhaseCellConcreteCoefficients.entry_outside P s t u w j k hband
  · omega
  · rfl

/-- Direct cross-cell accuracy uses the original coefficient, not a shared
Toeplitz surrogate or a discarded cross-cell interaction. -/
theorem entry_cross_error (P s t u w : ℕ) (hP : 13≤P) (hs : 0<s) (hst : s<t)
    (α : ℝ) (hu : α^2=(u : ℝ)) (j k : ℤ)
    (hphase : PhaseCell.phase s t j≠PhaseCell.phase s t k)
    (hband : (k-j).natAbs≤w) :
    |(entry P s t u w j k : ℝ)-Real.exp (normExp s t α j (k-j))|≤4/(2 : ℝ)^P := by
  have hq : phaseQ s t j≠phaseQ s t k := by simpa [phaseQ_eq s t hs] using hphase
  rw [entry, ite_eq_right hq, ite_eq_left hband]
  exact (direct_spec P s t u hP hs hst α hu j k).2.2

/-- Uniform accuracy of every retained unaliased entry, with the actual phase
decision and executable samples in both branches. The omitted tail is excluded
by `hband`, and periodic aliases have not been identified with these entries. -/
theorem selected_entry_error {s t u p w : ℕ} {α d : ℝ} {j k : ℤ}
    (hp : 0<p) (hs : 0<s) (hst : s<t) (hu : α^2=(u : ℝ))
    (htheta : 0<(t : ℝ)/s-1) (hgap : (1 : ℝ)/4≤d*((t : ℝ)/s-1))
    (hbudget : α^2*d≤p) (hband : (k-j).natAbs≤w) :
    |(entry (2^15*p) s t u w j k : ℝ)-Real.exp (normExp s t α j (k-j))|≤
      12*PhaseCellRounded.error (2^15*p)/((1/(2 : ℝ)^(8*p))/2)^2+
        4/(2 : ℝ)^(2^15*p) := by
  by_cases hjk : j=k
  · subst k
    simp only [entry_diag, Rat.cast_one, sub_self, normExp, Int.cast_zero,
      mul_zero, zero_div, zero_add, add_zero]
    have he : -Real.pi*α^2*beta s t j^2+Real.pi*α^2*beta s t j^2=0 := by ring
    rw [he, Real.exp_zero, sub_self, abs_zero]
    unfold PhaseCellRounded.error
    positivity
  by_cases hphase : PhaseCell.phase s t j=PhaseCell.phase s t k
  · have hq : phaseQ s t j=phaseQ s t k := by simpa [phaseQ_eq s t hs] using hphase
    rw [entry, ite_eq_left hq]
    exact (PhaseCellConcreteCoefficients.selected_entry_error hp hs hst hu
      htheta hgap hbudget hphase hjk hband).trans (le_add_of_nonneg_right (by positivity))
  · exact (entry_cross_error _ _ _ _ _ (PhaseCellConcreteCoefficients.selected_precision p hp).1
      hs hst α hu j k hphase hband).trans
        (le_add_of_nonneg_left (by unfold PhaseCellRounded.error; positivity))

end IntegerMultBounds.NLogN.PhaseCellCrossCell
