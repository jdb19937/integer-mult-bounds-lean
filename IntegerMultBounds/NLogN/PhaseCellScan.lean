module

public import IntegerMultBounds.NLogN.PhaseCell

/-!
# Exact additive scan of phase cells

The addition/comparison generator in `downstream-phase-cell-inverse.md`,
"Exact phase-cell structure", upstream input
`bcd4ebde8692383539f8a48734e5fbf3a18a32c2`.
The executable integer scan emits exactly the existing nearest-rounding phase
and offset. This proves arithmetic correctness, not tape execution or bit cost.
-/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellScan

structure State where
  phase : ℤ
  remainder : ℤ
  deriving DecidableEq

/-- Initial state for physical index zero. -/
def initial (s : ℤ) : State := ⟨0, s⟩

/-- One addition and comparison, with at most one correction. -/
def step (s K : ℤ) (x : State) : State :=
  if 2 * s ≤ x.remainder + 2 * K then
    ⟨x.phase + 1, x.remainder + 2 * K - 2 * s⟩
  else ⟨x.phase, x.remainder + 2 * K⟩

/-- Scan state before emitting physical index `j`. -/
def scan (s K : ℤ) : ℕ → State
  | 0 => initial s
  | j + 1 => step s K (scan s K j)

/-- The remainder is the nonnegative representative of the centered offset. -/
def Invariant (s K j : ℤ) (x : State) : Prop :=
  x.remainder = 2 * K * j + s - 2 * s * x.phase ∧
    0 ≤ x.remainder ∧ x.remainder < 2 * s

theorem initial_invariant {s K : ℤ} (hs : 0 < s) :
    Invariant s K 0 (initial s) := by
  simp only [Invariant, initial]
  constructor
  · ring
  · omega

/-- The strict rank-gap bound ensures one subtraction suffices. -/
theorem step_invariant {s K j : ℤ} {x : State}
    (hK : 0 ≤ K) (hKs : K < s) (hx : Invariant s K j x) :
    Invariant s K (j + 1) (step s K x) := by
  rcases hx with ⟨heq, hlo, hhi⟩
  unfold step
  split_ifs with h
  · refine ⟨?_, ?_, ?_⟩
    · dsimp; linear_combination heq
    · dsimp; omega
    · dsimp; omega
  · refine ⟨?_, ?_, ?_⟩
    · dsimp; linear_combination heq
    · dsimp; omega
    · dsimp; omega

theorem scan_invariant {s K : ℤ} (hs : 0 < s) (hK : 0 ≤ K) (hKs : K < s)
    (j : ℕ) : Invariant s K j (scan s K j) := by
  induction j with
  | zero => exact initial_invariant hs
  | succ j ih => simpa only [scan, Nat.cast_add, Nat.cast_one] using step_invariant hK hKs ih

/-- The scan changes phase exactly at the comparison threshold. -/
theorem step_phase (s K : ℤ) (x : State) :
    (step s K x).phase = x.phase + if 2 * s ≤ x.remainder + 2 * K then 1 else 0 := by
  unfold step
  split_ifs <;> simp

/-- Any valid integer state emits the exact nearest-rounding phase, including ties. -/
theorem phase_eq {s t : ℕ} {j : ℤ} {x : State} (hs : 0 < s)
    (hx : Invariant s ((t : ℤ) - s) j x) : x.phase = PhaseCell.phase s t j := by
  rcases hx with ⟨heq, hlo, hhi⟩
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have heqR : (x.remainder : ℝ) =
      2 * ((t : ℝ) - s) * j + s - 2 * s * x.phase := by exact_mod_cast heq
  have hloR : (0 : ℝ) ≤ x.remainder := by exact_mod_cast hlo
  have hhiR : (x.remainder : ℝ) < 2 * s := by exact_mod_cast hhi
  have hnearest : nearest ((t : ℝ) * j / s) = x.phase + j := by
    unfold nearest
    apply Int.floor_eq_iff.mpr
    push_cast
    have hdiv := div_mul_cancel₀ ((t : ℝ) * j) hsR.ne'
    constructor
    · apply (mul_le_mul_iff_right₀ hsR).mp
      nlinarith
    · apply (mul_lt_mul_iff_right₀ hsR).mp
      nlinarith
  unfold PhaseCell.phase
  rw [hnearest]
  omega

/-- The emitted centered remainder is exactly the existing resampling offset. -/
theorem offset_eq {s t : ℕ} {j : ℤ} {x : State} (hs : 0 < s)
    (hx : Invariant s ((t : ℤ) - s) j x) :
    beta s t j = ((x.remainder : ℝ) - s) / (2 * s) := by
  have hphase := phase_eq hs hx
  have heqR : (x.remainder : ℝ) =
      2 * ((t : ℝ) - s) * j + s - 2 * s * x.phase := by exact_mod_cast hx.1
  have hnearest : nearest ((t : ℝ) * j / s) = x.phase + j := by
    unfold PhaseCell.phase at hphase
    omega
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  unfold beta frac
  rw [hnearest]
  push_cast
  field_simp
  nlinarith

/-- Exact outputs at every natural index for `s ≤ t < 2s`. -/
theorem scan_exact {s t : ℕ} (hs : 0 < s) (hst : s ≤ t) (ht : t < 2 * s) (j : ℕ) :
    (scan s ((t : ℤ) - s) j).phase = PhaseCell.phase s t j ∧
    beta s t j = (((scan s ((t : ℤ) - s) j).remainder : ℝ) - s) / (2 * s) := by
  have hx := scan_invariant (s := (s : ℤ)) (K := (t : ℤ) - s)
    (by exact_mod_cast hs) (by omega) (by omega) j
  exact ⟨phase_eq hs hx, offset_eq hs hx⟩

end IntegerMultBounds.NLogN.PhaseCellScan
