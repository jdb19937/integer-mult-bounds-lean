module

public import IntegerMultBounds.Networks.Certificates.T16.Trace.Framed
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionForward1
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionForward2
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionForward3
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionForward4
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionForward5
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionForward6
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionBackward1
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionBackward2
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionBackward3
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionBackward4
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionBackward5
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionBackward6

/-! The exact rational action of both native local words, by kernel-checked symbolic
execution in seven chunks per orientation. Forward: `(X, Y, H, P) ↦ (X, Y + X, H, 0)` on
sources `0..111`, targets `112..223`, helpers `224..703` and private centres `704..711`.
Backward: `(X, Y, H, P) ↦ (X - Y, Y, H, 0)`. Helpers are restored for arbitrary dirty inputs;
private centres are cleared. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Trace

open Symbolic FramedCircuit

theorem symRun_append (T : Trie) (a b : List (Circuit.Gate ℕ ℚ)) :
    symRun T (a ++ b) = (symRun T a).bind fun T' => symRun T' b := by
  induction a generalizing T with
  | nil => rfl
  | cons g a ih =>
    simp only [List.cons_append, symRun]
    cases symStep T g with
    | none => rfl
    | some U => exact ih U

def forwardRow (i : ℕ) : Row :=
  if i < 112 then [(i, 1)] else if i < 224 then [(i - 112, 1), (i, 1)]
  else if i < 704 then [(i, 1)] else []

def backwardRow (i : ℕ) : Row :=
  if i < 112 then [(i, 1), (i + 112, -1)] else if i < 704 then [(i, 1)] else []

def rowsCheck (expected : ℕ → Row) : Option Trie → Bool
  | some T => checkRegisters 712 (fun i => decide (T.get i = expected i))
  | none => false

theorem rowsCheck_sound {expected : ℕ → Row} {o : Option Trie} (h : rowsCheck expected o = true) :
    ∃ T, o = some T ∧ ∀ i < 712, T.get i = expected i := by
  cases o with
  | none => simp [rowsCheck] at h
  | some T =>
    exact ⟨T, rfl, fun i hi => of_decide_eq_true
      (checkRegisters_sound (p := fun i => decide (T.get i = expected i)) h i hi)⟩

theorem symRun_drop (T : Trie) (P : List (Circuit.Gate ℕ ℚ)) {a b : ℕ} (hab : a ≤ b) :
    symRun T (P.drop a) = (symRun T (slice P a b)).bind fun T' => symRun T' (P.drop b) := by
  conv_lhs => rw [← List.take_append_drop (b - a) (P.drop a)]
  rw [symRun_append, List.drop_drop, show a + (b - a) = b by omega]
  rfl

theorem forward_final :
    rowsCheck forwardRow (symRun (snapshotTrie forwardSnapshot6) (forwardProgram.drop 18000)) =
      true := by
  decide +kernel

theorem backward_final :
    rowsCheck backwardRow (symRun (snapshotTrie backwardSnapshot6) (backwardProgram.drop 18000)) =
      true := by
  decide +kernel

theorem forward_symRun :
    ∃ T, symRun (Trie.init 10 0 1) forwardProgram = some T ∧ ∀ i < 712, T.get i = forwardRow i := by
  obtain ⟨T, hT, hrows⟩ := rowsCheck_sound forward_final
  refine ⟨T, ?_, hrows⟩
  rw [← List.drop_zero (l := forwardProgram), symRun_drop _ _ (b := 3000) (by omega), forward_reach1,
    Option.bind_some, symRun_drop _ _ (a := 3000) (b := 6000) (by omega), forward_reach2,
    Option.bind_some, symRun_drop _ _ (a := 6000) (b := 9000) (by omega), forward_reach3,
    Option.bind_some, symRun_drop _ _ (a := 9000) (b := 12000) (by omega), forward_reach4,
    Option.bind_some, symRun_drop _ _ (a := 12000) (b := 15000) (by omega), forward_reach5,
    Option.bind_some, symRun_drop _ _ (a := 15000) (b := 18000) (by omega), forward_reach6,
    Option.bind_some, hT]

theorem backward_symRun :
    ∃ T, symRun (Trie.init 10 0 1) backwardProgram = some T ∧ ∀ i < 712, T.get i = backwardRow i := by
  obtain ⟨T, hT, hrows⟩ := rowsCheck_sound backward_final
  refine ⟨T, ?_, hrows⟩
  rw [← List.drop_zero (l := backwardProgram), symRun_drop _ _ (b := 3000) (by omega), backward_reach1,
    Option.bind_some, symRun_drop _ _ (a := 3000) (b := 6000) (by omega), backward_reach2,
    Option.bind_some, symRun_drop _ _ (a := 6000) (b := 9000) (by omega), backward_reach3,
    Option.bind_some, symRun_drop _ _ (a := 9000) (b := 12000) (by omega), backward_reach4,
    Option.bind_some, symRun_drop _ _ (a := 12000) (b := 15000) (by omega), backward_reach5,
    Option.bind_some, symRun_drop _ _ (a := 15000) (b := 18000) (by omega), backward_reach6,
    Option.bind_some, hT]

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- **Forward rational action**: sources kept, sources added into targets, helpers restored for
arbitrary dirty values, private centres cleared, everything else untouched. -/
theorem forward_action (x : ℕ → E) (i : ℕ) :
    moduleRun forwardProgram x i =
      if i < 112 then x i else if i < 224 then x (i - 112) + x i
      else if i < 704 then x i else if i < 712 then 0 else x i := by
  obtain ⟨T, hT, hrows⟩ := forward_symRun
  obtain ⟨hlow, hhigh⟩ := moduleRun_eq_of_symRun hT x
  by_cases hi : i < 712
  · rw [hlow i (by unfold bound; exact hi), hrows i hi, forwardRow]
    by_cases h1 : i < 112
    · simp [h1]
    · by_cases h2 : i < 224
      · simp [h1, h2]
      · by_cases h3 : i < 704
        · simp [h1, h2, h3]
        · simp [h1, h2, h3, hi]
  · rw [hhigh i (by unfold bound; omega)]
    simp [show ¬ i < 112 by omega, show ¬ i < 224 by omega, show ¬ i < 704 by omega, hi]

/-- **Backward rational action**: targets subtracted from sources, everything else as forward
except that targets are kept. -/
theorem backward_action (x : ℕ → E) (i : ℕ) :
    moduleRun backwardProgram x i =
      if i < 112 then x i - x (i + 112)
      else if i < 704 then x i else if i < 712 then 0 else x i := by
  obtain ⟨T, hT, hrows⟩ := backward_symRun
  obtain ⟨hlow, hhigh⟩ := moduleRun_eq_of_symRun hT x
  by_cases hi : i < 712
  · rw [hlow i (by unfold bound; exact hi), hrows i hi, backwardRow]
    by_cases h1 : i < 112
    · simp [h1, sub_eq_add_neg]
    · by_cases h3 : i < 704
      · simp [h1, h3]
      · simp [h1, h3, hi]
  · rw [hhigh i (by unfold bound; omega)]
    simp [show ¬ i < 112 by omega, show ¬ i < 704 by omega, hi]

end IntegerMultBounds.Networks.Certificates.T16.Trace
