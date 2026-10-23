module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFieldPairLayout

/-! Generate one zero field and one full mask in a concrete shared bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks

variable {N T Q A : ℕ} {P U : Type}

theorem fieldPairJob_ready (dst : Fin N) (k : Fin 2) (ones : Bool) (L n : ℕ)
    (R : Fin (N + 6) → List (Fin (A + 4))) (hn : n < 2 ^ L)
    (hwidth : R (fieldAux ⟨k.val, by omega⟩) = binSyms L n)
    (hscratch : ∀ i : Fin 6, 2 ≤ i.val → R (fieldAux i) = []) :
    (fieldPairJob dst k ones L n).Ready R := by
  refine ⟨fieldPairReg_injective dst k, hn, hwidth, ?_⟩
  intro r hw hd
  cases r with
  | width => exact (hw rfl).elim
  | dst => exact (hd rfl).elim
  | unary => exact hscratch 2 (by decide)
  | scratch i => exact hscratch ⟨3 + i.val, by omega⟩ (by change 2 ≤ 3 + i.val; omega)

def fieldPairJobs (row mask : Fin N) (Lr Lm nr nm : ℕ) : List (BinaryFieldJob (N + 6)) :=
  [fieldPairJob row 0 false Lr nr, fieldPairJob mask 1 true Lm nm]

theorem fieldPair_exec (body : P → Pr P (N + 6) Q A U) (row mask : Fin N) (hrm : row ≠ mask)
    (Lr Lm nr nm : ℕ) (hr : nr < 2 ^ Lr) (hm : nm < 2 ^ Lm)
    (v : HS (N + 6) Q A U) (S : Stacks (N + 6) A)
    (hrowWidth : S.R (fieldAux 0) = binSyms Lr nr)
    (hmaskWidth : S.R (fieldAux 1) = binSyms Lm nm)
    (hscratch : ∀ i : Fin 6, 2 ≤ i.val → S.R (fieldAux i) = [])
    (hrow : S.R (fieldCore row) = []) (hmask : S.R (fieldCore mask) = []) :
    ∃ (v' : HS (N + 6) Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (Lr * (4 * nr + 11) + 8 * nr + 12) +
        (Lm * (4 * nm + 11) + 2 * nm + 6) + 1 ∧
      Exec body (binaryFieldBatch (fieldPairJobs row mask Lr Lm nr nm)) (mk v S) m
        (mk v' { S with R := Function.update (Function.update S.R (fieldCore row) (binSyms nr 0)) (fieldCore mask) (binSyms nm (maskVal nm id)) }) := by
  have hsep : ∀ job ∈ fieldPairJobs row mask Lr Lm nr nm,
      ∀ other ∈ fieldPairJobs row mask Lr Lm nr nm, ∀ r : BinaryZeroReg,
        r ≠ .dst → job.dst ≠ other.reg r := by
    intro job hj other ho r hrd
    simp only [fieldPairJobs, List.mem_cons, List.not_mem_nil, or_false] at hj ho
    rcases hj with rfl | rfl <;> rcases ho with rfl | rfl <;>
      exact fieldPairReg_core _ _ _ r hrd
  have hready : ∀ job ∈ fieldPairJobs row mask Lr Lm nr nm, job.Ready S.R := by
    intro job hj
    simp only [fieldPairJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact fieldPairJob_ready row 0 false Lr nr S.R hr hrowWidth hscratch
    · exact fieldPairJob_ready mask 1 true Lm nm S.R hm hmaskWidth hscratch
  obtain ⟨v', m, hu, hc, he⟩ := binaryFieldBatch_exec body _ hsep v S hready
  have hne : fieldCore mask ≠ fieldCore row := (fieldCore_injective.ne hrm).symm
  refine ⟨v', m, hu, ?_, ?_⟩
  · simpa [binaryFieldBatchCost, fieldPairJobs, fieldPairJob, BinaryFieldJob.cost, Nat.add_assoc] using hc
  · simpa [binaryFieldsGenerated, fieldPairJobs, fieldPairJob, BinaryFieldJob.word,
      BinaryFieldJob.dst, fieldPairReg, hrow, hmask, hne] using he

end IntegerMultBounds.MathlibTM2.Routing
