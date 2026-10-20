module

public import IntegerMultBounds.Networks.Certificates.T16.Trace.Framed
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionForward
public import IntegerMultBounds.Networks.Certificates.T16.Trace.ActionBackward

/-! The exact rational action of both native local words, by kernel-checked symbolic
execution piece by piece. Forward: `(X, Y, H, P) ↦ (X, Y + X, H, 0)` on sources `0..111`,
targets `112..223`, helpers `224..703` and private centres `704..711`. Backward: `(X, Y, H, P) ↦ (X - Y, Y, H, 0)`. Helpers are restored for arbitrary dirty inputs;
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
  if i < 112 then [(i, scale)] else if i < 224 then [(i - 112, scale), (i, scale)]
  else if i < 704 then [(i, scale)] else []

def backwardRow (i : ℕ) : Row :=
  if i < 112 then [(i, scale), (i + 112, -scale)] else if i < 704 then [(i, scale)] else []

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

theorem erase_append (a b : List Event) : erase (a ++ b) = erase a ++ erase b := by
  induction a with
  | nil => rfl
  | cons e a ih => cases e <;> simp [erase, ih]

/-- Piece checks compose: if each piece takes trie `S k` to `S (k + 1)`, all of them take `S 0`
to the trie after the last piece. -/
theorem symRun_chunks (S : ℕ → Trie) :
    ∀ cs : List (List Event), (∀ k < cs.length, symRun (S k) (erase (cs.getD k [])) = some (S (k + 1))) →
      symRun (S 0) (erase cs.flatten) = some (S cs.length)
  | [], _ => rfl
  | c :: cs, h => by
    rw [List.flatten_cons, erase_append, symRun_append, show c = (c :: cs).getD 0 [] from rfl,
      h 0 (by simp), Option.bind_some]
    exact symRun_chunks (fun k => S (k + 1)) cs fun k hk => h (k + 1) (by simp; omega)

theorem forward_final :
    rowsCheck forwardRow (some (snapshotTrie (forwardSnapshots.getD forwardPieces.length []))) =
      true := by
  rw [forwardPieces_length]
  decide +kernel

theorem backward_final :
    rowsCheck backwardRow (some (snapshotTrie (backwardSnapshots.getD backwardPieces.length []))) =
      true := by
  rw [backwardPieces_length]
  decide +kernel

theorem forward_symRun :
    ∃ T, symRun (Trie.init 10 0 1) forwardProgram = some T ∧ ∀ i < 712, T.get i = forwardRow i := by
  obtain ⟨T, hT, hrows⟩ := rowsCheck_sound forward_final
  refine ⟨T, ?_, hrows⟩
  rw [forwardProgram, forwardEvents, ← pieces_flatten (sizes := forwardSizes) (cuts := forwardCuts) rfl,
    ← hT]
  exact symRun_chunks (fun k => snapshotTrie (forwardSnapshots.getD k [])) forwardPieces
    fun k hk => forward_reach k (forwardPieces_length ▸ hk)

theorem backward_symRun :
    ∃ T, symRun (Trie.init 10 0 1) backwardProgram = some T ∧ ∀ i < 712, T.get i = backwardRow i := by
  obtain ⟨T, hT, hrows⟩ := rowsCheck_sound backward_final
  refine ⟨T, ?_, hrows⟩
  rw [backwardProgram, backwardEvents_eq,
    ← pieces_flatten (sizes := backwardSizes) (cuts := backwardCuts) rfl, ← hT]
  exact symRun_chunks (fun k => snapshotTrie (backwardSnapshots.getD k [])) backwardPieces
    fun k hk => backward_reach k (backwardPieces_length ▸ hk)

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
