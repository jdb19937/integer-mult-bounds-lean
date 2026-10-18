module

public import IntegerMultBounds.Networks.GroupedRouting

/-! Scalar invocations whose side bank carries rectangle mixers. A side role is
an input slot of a rectangle (copied from a source), an output slot of a
rectangle (injected into a target), or a direct pair (copied and injected).
Each rectangle's mixer adds the sum of its input slots to every output slot.
The twelve forward rows are: mix, subtract injection, unmix, subtract scatter,
copy, gather, scatter, mix, inject, unmix, undo gather, undo copy. For
arbitrary initial scratch they add `(J (V + P V) + H G) x` to the target bank,
where `P` is the mixer, and restore every scratch register. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Scalar

open GroupedCircuit Circuit

/-- The kind of one side role of an invocation with `n` data registers per bank
and `K` rectangles. -/
inductive Kind (n K : ℕ) where
  | input (k : Fin K) (source : Fin n)
  | output (k : Fin K) (target : Fin n)
  | direct (source target : Fin n)
  deriving DecidableEq

namespace Kind
variable {n K : ℕ}

/-- The data source copied into a role. -/
def owner : Kind n K → Option (Fin n)
  | input _ S => some S
  | output _ _ => none
  | direct S _ => some S

/-- The data target injected from a role. -/
def target : Kind n K → Option (Fin n)
  | input _ _ => none
  | output _ T => some T
  | direct _ T => some T

/-- The rectangle whose mixer reads this role. -/
def inRect : Kind n K → Option (Fin K)
  | input k _ => some k
  | _ => none

/-- The rectangle whose mixer writes this role. -/
def outRect : Kind n K → Option (Fin K)
  | output k _ => some k
  | _ => none

theorem inRect_outRect (κ : Kind n K) (k k' : Fin K) (h : κ.inRect = some k) :
    κ.outRect ≠ some k' := by
  cases κ <;> simp_all [inRect, outRect]

end Kind

variable {R : Type*} [CommRing R] {n a c s K : ℕ}

section Matrices
variable (kind : Fin a → Kind n K)

/-- Copy matrix: each role receives its owner's value. -/
def copyMatrix : Fin a → Fin n → R := fun p j => if (kind p).owner = some j then 1 else 0

/-- Injection matrix with role weights. -/
def injectMatrix (w : Fin a → R) : Fin n → Fin a → R :=
  fun i p => if (kind p).target = some i then w p else 0

/-- The mixer: an output slot receives the sum of its rectangle's input slots. -/
def mix (A : Fin a → R) : Fin a → R := fun p =>
  match (kind p).outRect with
  | some k => ∑ q, if (kind q).inRect = some k then A q else 0
  | none => 0

theorem mix_add (A B : Fin a → R) : mix kind (A + B) = mix kind A + mix kind B := by
  funext p
  simp only [mix, Pi.add_apply]
  split
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp
  · simp

theorem mix_smul (r : R) (A : Fin a → R) : mix kind (r • A) = r • mix kind A := by
  funext p
  simp only [mix, Pi.smul_apply, smul_eq_mul]
  split
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp
  · simp

theorem mix_zero : mix kind (0 : Fin a → R) = 0 := by
  funext p
  simp only [mix, Pi.zero_apply]
  split
  · simp
  · rfl

/-- Mixer outputs vanish on input slots, so mixing twice adds nothing. -/
theorem mix_mix (A : Fin a → R) : mix kind (mix kind A) = 0 := by
  funext p
  simp only [mix, Pi.zero_apply]
  split
  · apply Finset.sum_eq_zero
    intro q _
    split_ifs with hq
    · split
      · rename_i k' hk'
        exact absurd hk' (Kind.inRect_outRect _ _ k' hq)
      · rfl
    · rfl
  · rfl

end Matrices

/-! ### Rows of separated groups -/

section Rows
variable {ι : Type*} [DecidableEq ι]

/-- A list of groups no one of which reads a register that any of them writes. -/
def RowSeparated (gs : List (Group ι R)) : Prop :=
  ∀ g ∈ gs, ∀ h ∈ gs, ∀ row ∈ g.rows, ∀ row' ∈ h.rows, ∀ p ∈ row'.terms, p.1 ≠ row.target

/-- A separated row of groups runs as one simultaneous update. -/
theorem runGroups_rowSeparated (gs : List (Group ι R)) (hs : RowSeparated gs) (r : ι → R) :
    runGroups gs r = evaluateRows (gs.flatMap Group.rows) r := by
  induction gs generalizing r with
  | nil => funext i; simp [runGroups, evaluateRows]
  | cons g gs ih =>
    have hs' : RowSeparated gs := fun g' hg' h hh => hs g' (by simp [hg']) h (by simp [hh])
    rw [runGroups, ih hs']
    funext i
    have hread : ∀ row ∈ gs.flatMap Group.rows, ∀ p ∈ row.terms, evaluate g r p.1 = r p.1 := by
      intro row hrow p hp
      obtain ⟨h, hh, hrow⟩ := List.mem_flatMap.mp hrow
      unfold evaluate evaluateRows
      rw [add_eq_left]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨row', hrow', rfl⟩ := List.mem_map.mp hx
      rw [if_neg]
      exact Ne.symm (hs g (by simp) h (by simp [hh]) row' hrow' row hrow p hp)
    have hsum : ((gs.flatMap Group.rows).map fun row => if row.target = i then
        (row.terms.map fun p => p.2 * evaluate g r p.1).sum else 0).sum =
        ((gs.flatMap Group.rows).map fun row => if row.target = i then
        (row.terms.map fun p => p.2 * r p.1).sum else 0).sum := by
      congr 1
      apply List.map_congr_left
      intro row hrow
      congr 1
      congr 1
      apply List.map_congr_left
      intro p hp
      rw [hread row hrow p hp]
    simp only [evaluateRows] at hsum ⊢
    rw [hsum]
    simp only [evaluate, evaluateRows, List.flatMap_cons, List.map_append, List.sum_append]
    ring

end Rows

/-! ### Mixer and copy groups -/

section Groups
variable (kind : Fin a → Kind n K)

/-- Output-slot rows of one rectangle's mixer, with coefficient `ε`. -/
def mixRows (ε : R) (k : Fin K) : List (Gate (Role n a c s) R) :=
  (List.finRange a).filterMap fun p =>
    if (kind p).outRect = some k then
      some ⟨side p, (List.finRange a).filterMap fun q =>
        if (kind q).inRect = some k then some (side q, ε) else none⟩
    else none

theorem mem_mixRows {ε : R} {k : Fin K} {row : Gate (Role n a c s) R} :
    row ∈ mixRows kind ε k ↔ ∃ p, (kind p).outRect = some k ∧
      row = ⟨side p, (List.finRange a).filterMap fun q =>
        if (kind q).inRect = some k then some (side q, ε) else none⟩ := by
  simp only [mixRows, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨p, hp⟩
    split_ifs at hp with h
    · exact ⟨p, h, (Option.some.inj hp).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, by simp [hp]⟩

theorem mem_mixTerms {ε : R} {k : Fin K} {t : Role n a c s × R} :
    t ∈ ((List.finRange a).filterMap fun q =>
        if (kind q).inRect = some k then some ((side q : Role n a c s), ε) else none) ↔
      ∃ q, (kind q).inRect = some k ∧ t = (side q, ε) := by
  simp only [List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨q, hq⟩
    split_ifs at hq with h
    · exact ⟨q, h, (Option.some.inj hq).symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, by simp [hq]⟩

/-- One rectangle's mixer as a grouped gate. -/
def mixGroup (ε : R) (k : Fin K) : Group (Role n a c s) R where
  rows := mixRows kind ε k
  separated := by
    intro g hg h hh t ht
    obtain ⟨p, hp, rfl⟩ := (mem_mixRows kind).mp hg
    obtain ⟨p', _, rfl⟩ := (mem_mixRows kind).mp hh
    obtain ⟨q, hq, rfl⟩ := (mem_mixTerms kind).mp ht
    intro he
    have : q = p := by simpa [side] using he
    subst this
    exact Kind.inRect_outRect _ _ k hq hp

/-- The mixer row: one group per rectangle. -/
def mixRow (ε : R) : List (Group (Role n a c s) R) :=
  (List.finRange K).map (mixGroup kind ε)

theorem mixRow_separated (ε : R) : RowSeparated (mixRow (s := s) (c := c) kind ε) := by
  intro g hg h hh row hrow row' hrow' t ht
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
  obtain ⟨k', -, rfl⟩ := List.mem_map.mp hh
  obtain ⟨p, hp, rfl⟩ := (mem_mixRows kind).mp hrow
  obtain ⟨p', _, rfl⟩ := (mem_mixRows kind).mp hrow'
  obtain ⟨q, hq, rfl⟩ := (mem_mixTerms kind).mp ht
  intro he
  have : q = p := by simpa [side] using he
  subst this
  exact Kind.inRect_outRect _ _ k hq hp

end Groups

/-! ### Effects of the rows -/

section Effects
variable (kind : Fin a → Kind n K)

theorem sum_filterMap {β γ : Type*} (l : List β) (f : β → Option γ) (g : γ → R) :
    ((l.filterMap f).map g).sum = (l.map fun b => (f b).elim 0 g).sum := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.filterMap_cons]
    cases hb : f b <;> simp [hb, ih]

/-- A separated row of groups adds the increments of its members. -/
theorem sum_flatMap_map {β γ : Type*} (l : List β) (f : β → List γ) (g : γ → R) :
    ((l.flatMap f).map g).sum = (l.map fun b => ((f b).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem runGroups_increments {ι : Type*} [DecidableEq ι] (gs : List (Group ι R))
    (hs : RowSeparated gs) (r : ι → R) (k : ι) :
    runGroups gs r k = r k + (gs.map fun g => evaluate g r k - r k).sum := by
  rw [runGroups_rowSeparated gs hs]
  simp only [evaluateRows, evaluate, add_sub_cancel_left, sum_flatMap_map]

/-- One mixer group adds its rectangle's input sum to its output slots. -/
theorem mixGroup_evaluate (ε : R) (k : Fin K) (r : Role n a c s → R) (t : Role n a c s) :
    evaluate (mixGroup kind ε k) r t = r t + ∑ p, if (kind p).outRect = some k ∧ side p = t then
      ∑ q, (if (kind q).inRect = some k then ε * r (side q) else 0) else 0 := by
  simp only [evaluate, evaluateRows, mixGroup, mixRows, sum_filterMap]
  congr 1
  rw [Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro p _
  by_cases hp : (kind p).outRect = some k
  · simp only [hp, if_true, Option.elim, true_and]
    by_cases ht : side p = t
    · simp only [ht, if_true, sum_filterMap, Fin.sum_univ_def]
      congr 1
      apply List.map_congr_left
      intro q _
      by_cases hq : (kind q).inRect = some k <;> simp [hq]
    · simp [ht]
  · simp [hp]

/-- The total mixer increment at a side role. -/
theorem mix_increment (ε : R) (A : Fin a → R) (p : Fin a) :
    (∑ k : Fin K, ∑ p' : Fin a, if (kind p').outRect = some k ∧ p' = p then
      ∑ q, (if (kind q).inRect = some k then ε * A q else 0) else 0) = ε * mix kind A p := by
  have h1 : ∀ k : Fin K, (∑ p' : Fin a, if (kind p').outRect = some k ∧ p' = p then
      ∑ q, (if (kind q).inRect = some k then ε * A q else 0) else 0) =
      if (kind p).outRect = some k then
        ∑ q, (if (kind q).inRect = some k then ε * A q else 0) else 0 := by
    intro k
    rw [Finset.sum_eq_single p]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  simp only [h1, mix]
  cases hp : (kind p).outRect with
  | none => simp
  | some k₀ =>
    simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> simp

/-- The mixer row adds `ε` times the mixer image of the side bank. -/
theorem mixRow_run (ε : R) (X Y : Fin n → R) (A : Fin a → R) (C : Fin c → R) (S : Fin s → R) :
    runGroups (mixRow (s := s) (c := c) kind ε) (banks X Y A C S) =
      banks X Y (A + ε • mix kind A) C S := by
  funext t
  rw [runGroups_increments _ (mixRow_separated kind ε)]
  simp only [mixRow, List.map_map, Function.comp_def, mixGroup_evaluate, add_sub_cancel_left,
    ← Fin.sum_univ_def]
  rcases t with i | i | p | i | i
  · simp [side, banks]
  · simp [side, banks]
  · have hs : ∀ p' : Fin a, (side p' : Role n a c s) = Sum.inr (Sum.inr (Sum.inl p)) ↔ p' = p := by
      intro p'
      simp [side]
    simp only [hs, banks_side]
    rw [mix_increment kind ε A p]
    rfl
  · simp [side, banks]
  · simp [side, banks]

end Effects

/-! ### The forward and inverse schedules -/

section Program
variable [DecidableEq R] (kind : Fin a → Kind n K)

/-- Copy one data source into every side role it owns, with coefficient `ε`. -/
def copyGroup (ε : R) (j : Fin n) : Group (Role n a c s) R :=
  fanoutGroup side (x j) (fun p => ε * copyMatrix kind p j) (fun p => side_x_sep p j)

/-- The copy row: one group per data source. -/
def copyRow (ε : R) : List (Group (Role n a c s) R) :=
  (List.finRange n).map (copyGroup kind ε)

theorem mem_fanout_rows {ι : Type*} {m : ℕ} {dst : Fin m → ι} {src : ι} {coeff : Fin m → R}
    {sep : ∀ i, dst i ≠ src} {row : Gate ι R} (h : row ∈ (fanoutGroup dst src coeff sep).rows) :
    ∃ i, row = ⟨dst i, [(src, coeff i)]⟩ := by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
  exact ⟨i, rfl⟩

theorem copyRow_separated (ε : R) : RowSeparated (copyRow (s := s) (c := c) kind ε) := by
  intro g hg h hh row hrow row' hrow' t ht
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hg
  obtain ⟨j', -, rfl⟩ := List.mem_map.mp hh
  obtain ⟨i, rfl⟩ := mem_fanout_rows hrow
  obtain ⟨i', rfl⟩ := mem_fanout_rows hrow'
  simp only [List.mem_singleton] at ht
  subst ht
  simp [side, x]

/-- The copy row adds `ε` times the copied data to the side bank. -/
theorem copyRow_run (ε : R) (X Y : Fin n → R) (A : Fin a → R) (C : Fin c → R) (S : Fin s → R) :
    runGroups (copyRow (s := s) (c := c) kind ε) (banks X Y A C S) =
      banks X Y (A + ε • mv (copyMatrix kind) X) C S := by
  funext t
  rw [runGroups_increments _ (copyRow_separated kind ε)]
  simp only [copyRow, List.map_map, Function.comp_def, copyGroup, fanoutGroup_run,
    add_sub_cancel_left, ← Fin.sum_univ_def]
  rcases t with i | i | p | i | i
  · simp [side, banks]
  · simp [side, banks]
  · have hs : ∀ p' : Fin a, (side p' : Role n a c s) = Sum.inr (Sum.inr (Sum.inl p)) ↔ p' = p := by
      intro p'
      simp [side]
    simp only [hs, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    change A p + _ = A p + _
    congr 1
    rw [Pi.smul_apply, smul_eq_mul, mv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [mul_assoc]
  · simp [side, banks]
  · simp [side, banks]

/-- The forward invocation's twelve grouped rows. -/
def forward (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    List (Group (Role n a c s) R) :=
  mixRow kind 1 ++ faninGroups y side (-J) y_side_sep ++ mixRow kind (-1) ++
  [matrixGroup y center (-H) y_center_sep] ++ copyRow kind 1 ++
  [matrixGroup center x G center_x_sep] ++ [matrixGroup y center H y_center_sep] ++
  mixRow kind 1 ++ faninGroups y side J y_side_sep ++ mixRow kind (-1) ++
  [matrixGroup center x (-G) center_x_sep] ++ copyRow kind (-1)

/-- The inverse invocation's twelve grouped rows, before exchanging the data banks. -/
def inverse (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R) :
    List (Group (Role n a c s) R) :=
  copyRow kind 1 ++ [matrixGroup center x G center_x_sep] ++ mixRow kind 1 ++
  faninGroups y side (-J) y_side_sep ++ mixRow kind (-1) ++
  [matrixGroup y center (-H) y_center_sep] ++ [matrixGroup center x (-G) center_x_sep] ++
  copyRow kind (-1) ++ [matrixGroup y center H y_center_sep] ++ mixRow kind 1 ++
  faninGroups y side J y_side_sep ++ mixRow kind (-1)

/-- The forward invocation adds the reconstructed source bank to the target bank and
restores every scratch register, for arbitrary initial scratch. -/
theorem forward_run (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (X Y : Fin n → R) (A : Fin a → R) (C : Fin c → R) (S : Fin s → R) :
    runGroups (forward kind G J H) (banks X Y A C S) =
      banks X (Y + (mv J (mv (copyMatrix kind) X + mix kind (mv (copyMatrix kind) X)) +
        mv H (mv G X))) A C S := by
  simp only [forward, runGroups_append, runGroups, mixRow_run, copyRow_run, faninGroups_run,
    matrixGroup_evaluate, block_y_side, block_y_center, block_center_x, mix_add, mix_smul,
    mix_mix, mv_add, mv_neg_matrix, mv_neg]
  simp only [one_smul, neg_smul, smul_zero, add_zero, zero_add, mix_zero, mv_add, mv_neg]
  congr 1 <;> abel

/-- The inverse invocation subtracts the reconstructed source bank and restores every
scratch register, for arbitrary initial scratch. -/
theorem inverse_run (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
    (X Y : Fin n → R) (A : Fin a → R) (C : Fin c → R) (S : Fin s → R) :
    runGroups (inverse kind G J H) (banks X Y A C S) =
      banks X (Y - (mv J (mv (copyMatrix kind) X + mix kind (mv (copyMatrix kind) X)) +
        mv H (mv G X))) A C S := by
  simp only [inverse, runGroups_append, runGroups, mixRow_run, copyRow_run, faninGroups_run,
    matrixGroup_evaluate, block_y_side, block_y_center, block_center_x, mix_add, mix_smul,
    mix_mix, mv_add, mv_neg_matrix]
  simp only [one_smul, neg_smul, smul_zero, add_zero, mix_zero, mv_add, mv_neg]
  congr 1 <;> abel

end Program

end IntegerMultBounds.Networks.Mixer.Scalar
