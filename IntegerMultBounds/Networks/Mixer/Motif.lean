module

public import IntegerMultBounds.Networks.LabeledMotif
public import IntegerMultBounds.Networks.Mixer.Scalar

/-! Mixer invocations with their common tensor-subspace labels. Every gate label
has the form `common ⊔ (past ⊗ U)` for a subspace `U` of the current factor:
`U = 0` gives `common`, a triple line gives `xMiddle`, a triple complement gives
`yOut`, the whole factor gives `full`, and each rectangle's mixer carries its own
enclosure `U`. Along every side role the labels grow; only the central return
loses dimension, exactly as in the motif without mixers. -/

@[expose] public section

namespace IntegerMultBounds.Networks.Mixer.Motif

open scoped TensorProduct
open GroupedCircuit GroupedFrames Circuit MotifLabels LabeledMotif TensorSubspace Scalar
open Module

section Mid
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] (g : Geometry K E F)

/-- The gate label of a current-factor subspace. -/
def mid (U : Submodule K F) : Submodule K (E ⊗[K] F) := g.common ⊔ space g.past U

theorem mid_mono {U V : Submodule K F} (h : U ≤ V) : mid g U ≤ mid g V :=
  sup_le_sup le_rfl (mono le_rfl h)

theorem common_le_mid (U : Submodule K F) : g.common ≤ mid g U := le_sup_left

theorem mid_le_full (U : Submodule K F) : mid g U ≤ g.full := by
  rw [g.full_eq_top]
  exact le_top

theorem xMiddle_eq_mid (t : F) : g.xMiddle t = mid g (K ∙ t) := rfl

theorem yOut_eq_mid (t : F) : g.yOut t = mid g (g.current.orthogonal (K ∙ t)) := rfl

theorem mid_nondegenerate [FiniteDimensional K E] [FiniteDimensional K F] (U : Submodule K F)
    (hU : (g.current.restrict U).Nondegenerate) :
    (g.pairing.restrict (mid g U)).Nondegenerate :=
  orthogonal_sup_nondegenerate _ g.pairing_symm _ _ g.common_nondegenerate
    (TensorSubspace.nondegenerate _ _ _ _ g.past_nondegenerate hU) (g.common_orthogonal_past _)

end Mid

section Schedules
variable {K E F R : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [CommRing R] [DecidableEq R]
  {n a c s M : ℕ}
variable (g : Geometry K E F) (t : Fin n → F) (kind : Fin a → Kind n M)
  (U U' : Fin M → Submodule K F)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

/-- A labeled mixer row: rectangle `k` carries label `lab k`. -/
def mixRowV (ε : R) (lab : Fin M → Submodule K (E ⊗[K] F)) :
    List (Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R) :=
  (List.finRange M).map fun k => ⟨mixGroup kind ε k, lab k⟩

/-- A labeled copy row: source `j` carries label `lab j`. -/
def copyRowV (ε : R) (lab : Fin n → Submodule K (E ⊗[K] F)) :
    List (Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R) :=
  (List.finRange n).map fun j => ⟨Scalar.copyGroup kind ε j, lab j⟩

/-- A labeled injection row: target `i` carries label `lab i`. -/
def faninRowV (P : Fin n → Fin a → R) (lab : Fin n → Submodule K (E ⊗[K] F)) :
    List (Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R) :=
  List.ofFn fun i : Fin n => ⟨faninGroup (y i) side (P i) (y_side_sep i), lab i⟩

/-- The twelve forward rows with their labels. Rectangle `k`'s middle mixer
carries `mid (U k)`. -/
def forward : List (Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R) :=
  mixRowV kind 1 (fun _ => g.common) ++
  faninRowV (-J) (fun _ => g.common) ++
  mixRowV kind (-1) (fun _ => g.common) ++
  [⟨matrixGroup y center (-H) y_center_sep, g.common⟩] ++
  copyRowV kind 1 (fun j => g.xMiddle (t j)) ++
  [⟨matrixGroup center x G center_x_sep, g.full⟩] ++
  [⟨matrixGroup y center H y_center_sep, g.common⟩] ++
  mixRowV kind 1 (fun k => mid g (U k)) ++
  faninRowV J (fun i => g.yOut (t i)) ++
  mixRowV kind (-1) (fun _ => g.full) ++
  [⟨matrixGroup center x (-G) center_x_sep, g.full⟩] ++
  copyRowV kind (-1) (fun _ => g.full)

/-- The twelve inverse rows, before exchanging the data banks. Rectangle `k`'s
middle unmixer carries `mid (U' k)`. -/
def inverse : List (Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R) :=
  copyRowV kind 1 (fun _ => g.common) ++
  [⟨matrixGroup center x G center_x_sep, g.common⟩] ++
  mixRowV kind 1 (fun _ => g.common) ++
  faninRowV (-J) (fun i => g.xMiddle (t i)) ++
  mixRowV kind (-1) (fun k => mid g (U' k)) ++
  [⟨matrixGroup y center (-H) y_center_sep, g.full⟩] ++
  [⟨matrixGroup center x (-G) center_x_sep, g.common⟩] ++
  copyRowV kind (-1) (fun j => g.yOut (t j)) ++
  [⟨matrixGroup y center H y_center_sep, g.full⟩] ++
  mixRowV kind 1 (fun _ => g.full) ++
  faninRowV J (fun _ => g.full) ++
  mixRowV kind (-1) (fun _ => g.full)

/-- The inverse with physical data-bank names exchanged. -/
def opposite : List (Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R) :=
  (inverse g t kind U' G J H).map fun v => ⟨v.group.rename (exchangeRoles n a c s), v.label⟩

theorem mixRowV_groups (ε : R) (lab : Fin M → Submodule K (E ⊗[K] F)) :
    (mixRowV (s := s) (c := c) kind ε lab).map Vertex.group = mixRow kind ε := by
  simp [mixRowV, mixRow, List.map_map, Function.comp_def]

theorem copyRowV_groups (ε : R) (lab : Fin n → Submodule K (E ⊗[K] F)) :
    (copyRowV (s := s) (c := c) kind ε lab).map Vertex.group = copyRow kind ε := by
  simp [copyRowV, copyRow, List.map_map, Function.comp_def]

theorem faninRowV_groups (P : Fin n → Fin a → R) (lab : Fin n → Submodule K (E ⊗[K] F)) :
    (faninRowV (s := s) (c := c) P lab).map Vertex.group = faninGroups y side P y_side_sep := by
  simp [faninRowV, faninGroups, List.map_ofFn, Function.comp_def]

/-- Forgetting labels recovers the scalar forward schedule. -/
theorem forward_groups :
    (forward (s := s) g t kind U G J H).map Vertex.group = Scalar.forward kind G J H := by
  simp only [forward, Scalar.forward, List.map_append, mixRowV_groups, copyRowV_groups,
    faninRowV_groups, List.map_cons, List.map_nil]

theorem inverse_groups :
    (inverse (s := s) g t kind U' G J H).map Vertex.group = Scalar.inverse kind G J H := by
  simp only [inverse, Scalar.inverse, List.map_append, mixRowV_groups, copyRowV_groups,
    faninRowV_groups, List.map_cons, List.map_nil]

theorem opposite_groups :
    (opposite (s := s) g t kind U' G J H).map Vertex.group =
      renameGroups (exchangeRoles n a c s) (Scalar.inverse kind G J H) := by
  rw [opposite, List.map_map, renameGroups, ← inverse_groups g t kind U' G J H, List.map_map]
  rfl

end Schedules

section Touches
variable {R : Type*} [CommRing R] [DecidableEq R] {n a c s M : ℕ} (kind : Fin a → Kind n M)

theorem copyGroup_touched (ε : R) (hε : ε ≠ 0) (j : Fin n) (k : Role n a c s) :
    k ∈ touched (Scalar.copyGroup (c := c) (s := s) kind ε j) ↔
      (∃ p, (kind p).owner = some j ∧ k = side p) ∨ (k = x j ∧ ∃ p, (kind p).owner = some j) := by
  rw [Scalar.copyGroup, fanoutGroup_touched]
  simp [Scalar.copyMatrix, hε]

theorem mixGroup_touched (ε : R) (hε : ε ≠ 0) (k : Fin M) (r : Role n a c s) :
    r ∈ touched (mixGroup kind ε k) ↔
      (∃ p, (kind p).outRect = some k ∧ r = side p) ∨
        ((∃ q, (kind q).inRect = some k ∧ side q = r) ∧ ∃ p, (kind p).outRect = some k) := by
  rw [touched_iff]
  constructor
  · rintro ⟨row, hrow, hr⟩
    obtain ⟨p, hp, rfl⟩ := (mem_mixRows kind).mp hrow
    rcases hr with hr | ⟨tm, htm, hr, -⟩
    · exact Or.inl ⟨p, hp, hr⟩
    · obtain ⟨q, hq, rfl⟩ := (mem_mixTerms kind).mp htm
      exact Or.inr ⟨⟨q, hq, hr⟩, p, hp⟩
  · rintro (⟨p, hp, rfl⟩ | ⟨⟨q, hq, rfl⟩, p, hp⟩)
    · exact ⟨_, (mem_mixRows kind).mpr ⟨p, hp, rfl⟩, Or.inl rfl⟩
    · refine ⟨_, (mem_mixRows kind).mpr ⟨p, hp, rfl⟩, Or.inr ⟨(side q, ε), ?_, rfl, hε⟩⟩
      exact (mem_mixTerms kind).mpr ⟨q, hq, rfl⟩

end Touches

section Histories
variable {ι L R : Type*} [DecidableEq ι] [CommRing R] [DecidableEq R]

theorem history_map_absent {m : ℕ} (vs : Fin m → Vertex ι L R) (i : ι)
    (h : ∀ j, i ∉ touched (vs j).group) : history ((List.finRange m).map vs) i = [] := by
  rw [← List.ofFn_eq_map]
  exact history_ofFn_absent vs i h

theorem history_map_unique {m : ℕ} (vs : Fin m → Vertex ι L R) (i : ι) (k : Fin m)
    (h : ∀ j, i ∈ touched (vs j).group ↔ j = k) :
    history ((List.finRange m).map vs) i = [(vs k).label] := by
  rw [← List.ofFn_eq_map]
  exact history_ofFn_unique vs i k h

theorem history_map_optional {m : ℕ} (vs : Fin m → Vertex ι L R) (i : ι) (k : Fin m)
    (P : Prop) [Decidable P] (h : ∀ j, i ∈ touched (vs j).group ↔ j = k ∧ P) :
    history ((List.finRange m).map vs) i = if P then [(vs k).label] else [] := by
  rw [← List.ofFn_eq_map]
  exact history_ofFn_optional vs i k P h

end Histories

section RowHistories
variable {K E F R : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [CommRing R] [DecidableEq R] [Nontrivial R]
  {n a c s M : ℕ} (kind : Fin a → Kind n M)

local notation "Lab" => Submodule K (E ⊗[K] F)

theorem mix_data (ε : R) (hε : ε ≠ 0) (lab : Fin M → Lab) (r : Role n a c s)
    (hr : ∀ p, r ≠ side p) : history (mixRowV kind ε lab) r = [] := by
  apply history_map_absent
  intro k hk
  rcases (mixGroup_touched kind ε hε k r).mp hk with ⟨p, -, rfl⟩ | ⟨⟨q, -, rfl⟩, -⟩
  · exact hr p rfl
  · exact hr q rfl

theorem mix_output (ε : R) (hε : ε ≠ 0) (lab : Fin M → Lab) {p : Fin a} {k : Fin M}
    (hp : (kind p).outRect = some k) :
    history (mixRowV (s := s) (c := c) kind ε lab) (side p) = [lab k] := by
  apply history_map_unique (fun k' => (⟨mixGroup kind ε k', lab k'⟩ : Vertex _ Lab R)) _ k
  intro k'
  rw [mixGroup_touched kind ε hε]
  constructor
  · rintro (⟨p', hp', he⟩ | ⟨⟨q, hq, he⟩, -⟩)
    · have : p' = p := by simpa [side] using he.symm
      subst this
      rw [hp] at hp'
      exact (Option.some.inj hp').symm
    · have : q = p := by simpa [side] using he
      subst this
      exact absurd hp (Kind.inRect_outRect _ _ _ hq)
  · rintro rfl
    exact Or.inl ⟨p, hp, rfl⟩

theorem mix_input (ε : R) (hε : ε ≠ 0) (lab : Fin M → Lab) {p : Fin a} {k : Fin M}
    (hp : (kind p).inRect = some k) (hout : ∃ p', (kind p').outRect = some k) :
    history (mixRowV (s := s) (c := c) kind ε lab) (side p) = [lab k] := by
  apply history_map_unique (fun k' => (⟨mixGroup kind ε k', lab k'⟩ : Vertex _ Lab R)) _ k
  intro k'
  rw [mixGroup_touched kind ε hε]
  constructor
  · rintro (⟨p', hp', he⟩ | ⟨⟨q, hq, he⟩, -⟩)
    · have : p' = p := by simpa [side] using he.symm
      subst this
      exact absurd hp' (Kind.inRect_outRect _ _ _ hp)
    · have : q = p := by simpa [side] using he
      subst this
      rw [hp] at hq
      exact (Option.some.inj hq).symm
  · rintro rfl
    exact Or.inr ⟨⟨p, hp, rfl⟩, hout⟩

theorem mix_direct (ε : R) (hε : ε ≠ 0) (lab : Fin M → Lab) {p : Fin a}
    (hi : (kind p).inRect = none) (ho : (kind p).outRect = none) :
    history (mixRowV (s := s) (c := c) kind ε lab) (side p) = [] := by
  apply history_map_absent
  intro k hk
  rcases (mixGroup_touched kind ε hε k (side p)).mp hk with ⟨p', hp', he⟩ | ⟨⟨q, hq, he⟩, -⟩
  · have : p' = p := by simpa [side] using he.symm
    subst this
    rw [ho] at hp'
    simp at hp'
  · have : q = p := by simpa [side] using he
    subst this
    rw [hi] at hq
    simp at hq

theorem copy_data (ε : R) (hε : ε ≠ 0) (lab : Fin n → Lab) (r : Role n a c s)
    (hr : ∀ p, r ≠ side p) (hx : ∀ j, r ≠ x j) : history (copyRowV kind ε lab) r = [] := by
  apply history_map_absent
  intro j hj
  rcases (copyGroup_touched kind ε hε j r).mp hj with ⟨p, -, rfl⟩ | ⟨rfl, -⟩
  · exact hr p rfl
  · exact hx j rfl

theorem copy_x (ε : R) (hε : ε ≠ 0) (lab : Fin n → Lab) (j : Fin n) :
    history (copyRowV (s := s) (c := c) kind ε lab) (x j) =
      if ∃ p, (kind p).owner = some j then [lab j] else [] := by
  apply history_map_optional (fun j' => (⟨Scalar.copyGroup kind ε j', lab j'⟩ : Vertex _ Lab R))
  intro j'
  rw [copyGroup_touched kind ε hε]
  constructor
  · rintro (⟨p, -, he⟩ | ⟨he, hex⟩)
    · simp [x, side] at he
    · have : j = j' := by simpa [x] using he
      subst this
      exact ⟨rfl, hex⟩
  · rintro ⟨rfl, hex⟩
    exact Or.inr ⟨rfl, hex⟩

theorem copy_side (ε : R) (hε : ε ≠ 0) (lab : Fin n → Lab) (p : Fin a) :
    history (copyRowV (s := s) (c := c) kind ε lab) (side p) =
      ((kind p).owner.map fun j => [lab j]).getD [] := by
  cases hp : (kind p).owner with
  | none =>
    apply history_map_absent
    intro j hj
    rcases (copyGroup_touched kind ε hε j (side p)).mp hj with ⟨p', hp', he⟩ | ⟨he, -⟩
    · have : p' = p := by simpa [side] using he.symm
      subst this
      rw [hp] at hp'
      simp at hp'
    · simp [x, side] at he
  | some S =>
    apply history_map_unique (fun j' => (⟨Scalar.copyGroup kind ε j', lab j'⟩ : Vertex _ Lab R)) _ S
    intro j'
    rw [copyGroup_touched kind ε hε]
    constructor
    · rintro (⟨p', hp', he⟩ | ⟨he, -⟩)
      · have : p' = p := by simpa [side] using he.symm
        subst this
        rw [hp] at hp'
        exact (Option.some.inj hp').symm
      · simp [x, side] at he
    · rintro rfl
      exact Or.inl ⟨p, hp, rfl⟩

variable (P : Fin n → Fin a → R) (hP : ∀ i p, P i p ≠ 0 ↔ (kind p).target = some i)

theorem fan_data (lab : Fin n → Lab) (r : Role n a c s)
    (hr : ∀ p, r ≠ side p) (hy : ∀ i, r ≠ y i) : history (faninRowV P lab) r = [] := by
  apply history_ofFn_absent
  intro i hi
  rcases (faninGroup_touched (y i) side (P i) (y_side_sep i) r).mp hi with rfl | ⟨p, rfl, -⟩
  · exact hy i rfl
  · exact hr p rfl

theorem fan_y (lab : Fin n → Lab) (i : Fin n) :
    history (faninRowV (s := s) (c := c) P lab) (y i) = [lab i] := by
  apply history_ofFn_unique
  intro i'
  rw [faninGroup_touched]
  simp [y, side, eq_comm]

include hP in
theorem fan_side (lab : Fin n → Lab) (p : Fin a) :
    history (faninRowV (s := s) (c := c) P lab) (side p) =
      ((kind p).target.map fun i => [lab i]).getD [] := by
  cases hp : (kind p).target with
  | none =>
    apply history_ofFn_absent
    intro i hi
    rcases (faninGroup_touched (y i) side (P i) (y_side_sep i) (side p)).mp hi with
      he | ⟨p', he, hne⟩
    · simp [y, side] at he
    · have : p' = p := by simpa [side] using he
      subst this
      rw [hP, hp] at hne
      simp at hne
  | some T =>
    apply history_ofFn_unique
    intro i
    rw [faninGroup_touched]
    constructor
    · rintro (he | ⟨p', he, hne⟩)
      · simp [y, side] at he
      · have : p' = p := by simpa [side] using he
        subst this
        rw [hP, hp] at hne
        exact (Option.some.inj hne).symm
    · rintro rfl
      exact Or.inr ⟨p, rfl, (hP _ _).mpr hp⟩

end RowHistories

section ForwardHistories
variable {K E F R : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [CommRing R] [DecidableEq R] [Nontrivial R]
  {n a c s M : ℕ}
variable (g : Geometry K E F) (t : Fin n → F) (kind : Fin a → Kind n M)
  (U : Fin M → Submodule K F)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

theorem one_ne : (1 : R) ≠ 0 := one_ne_zero
theorem neg_one_ne : (-1 : R) ≠ 0 := neg_ne_zero.mpr one_ne_zero

theorem forward_x_history (j : Fin n) :
    history (forward (s := s) g t kind U G J H) (x j) =
      (if ∃ p, (kind p).owner = some j then [g.xMiddle (t j)] else []) ++
      (if ∃ i, G i j ≠ 0 then [g.full] else []) ++
      (if ∃ i, G i j ≠ 0 then [g.full] else []) ++
      (if ∃ p, (kind p).owner = some j then [g.full] else []) := by
  have hs : ∀ p, (x j : Role n a c s) ≠ side p := fun p => by simp [x, side]
  have hy : ∀ i, (x j : Role n a c s) ≠ y i := fun i => by simp [x, y]
  simp only [forward, history_append, mix_data kind _ one_ne _ _ hs,
    mix_data kind _ neg_one_ne _ _ hs, fan_data _ _ _ hs hy, copy_x kind _ one_ne,
    copy_x kind _ neg_one_ne, history_cons, history_nil, List.append_nil, List.nil_append]
  simp [matrixGroup_touched, x, y, center, List.append_assoc]

theorem forward_y_history (i : Fin n) :
    history (forward (s := s) g t kind U G J H) (y i) =
      [g.common, g.common, g.common, g.yOut (t i)] := by
  have hs : ∀ p, (y i : Role n a c s) ≠ side p := fun p => by simp [y, side]
  have hx : ∀ j, (y i : Role n a c s) ≠ x j := fun j => by simp [x, y]
  simp only [forward, history_append, mix_data kind _ one_ne _ _ hs,
    mix_data kind _ neg_one_ne _ _ hs, fan_y, copy_data kind _ one_ne _ _ hs hx,
    copy_data kind _ neg_one_ne _ _ hs hx, history_cons, history_nil, List.append_nil,
    List.nil_append]
  simp [matrixGroup_touched, x, y, center]

theorem forward_center_history (j : Fin c) :
    history (forward (s := s) g t kind U G J H) (center j) =
      (if ∃ i, H i j ≠ 0 then [g.common] else []) ++ [g.full] ++
      (if ∃ i, H i j ≠ 0 then [g.common] else []) ++ [g.full] := by
  have hs : ∀ p, (center j : Role n a c s) ≠ side p := fun p => by simp [center, side]
  have hx : ∀ j', (center j : Role n a c s) ≠ x j' := fun j' => by simp [x, center]
  have hy : ∀ i, (center j : Role n a c s) ≠ y i := fun i => by simp [center, y]
  simp only [forward, history_append, mix_data kind _ one_ne _ _ hs,
    mix_data kind _ neg_one_ne _ _ hs, fan_data _ _ _ hs hy,
    copy_data kind _ one_ne _ _ hs hx, copy_data kind _ neg_one_ne _ _ hs hx,
    history_cons, history_nil, List.append_nil, List.nil_append]
  simp [matrixGroup_touched, center, x, y, Pi.neg_apply, List.append_assoc]

theorem forward_spectator_history (j : Fin s) :
    history (forward g t kind U G J H) (spectator j) = [] := by
  have hs : ∀ p, (spectator j : Role n a c s) ≠ side p := fun p => by simp [spectator, side]
  have hx : ∀ j', (spectator j : Role n a c s) ≠ x j' := fun j' => by simp [x, spectator]
  have hy : ∀ i, (spectator j : Role n a c s) ≠ y i := fun i => by simp [spectator, y]
  simp only [forward, history_append, mix_data kind _ one_ne _ _ hs,
    mix_data kind _ neg_one_ne _ _ hs, fan_data _ _ _ hs hy,
    copy_data kind _ one_ne _ _ hs hx, copy_data kind _ neg_one_ne _ _ hs hx,
    history_cons, history_nil, List.append_nil, List.nil_append]
  simp [matrixGroup_touched, spectator, x, y, center]

variable (hJ : ∀ i p, J i p ≠ 0 ↔ (kind p).target = some i)
include hJ

theorem neg_support : ∀ i p, (-J) i p ≠ 0 ↔ (kind p).target = some i := by
  simpa using hJ

theorem forward_input_history (hout : ∀ k, ∃ p, (kind p).outRect = some k)
    {p : Fin a} {k : Fin M} {S : Fin n} (hp : kind p = .input k S) :
    history (forward (s := s) g t kind U G J H) (side p) =
      [g.common, g.common, g.xMiddle (t S), mid g (U k), g.full, g.full] := by
  have hi : (kind p).inRect = some k := by rw [hp]; rfl
  simp only [forward, history_append, mix_input kind _ one_ne _ hi (hout k),
    mix_input kind _ neg_one_ne _ hi (hout k), fan_side kind J hJ,
    fan_side kind (-J) (neg_support kind J hJ), copy_side kind _ one_ne,
    copy_side kind _ neg_one_ne, hp, Kind.owner, Kind.target, history_cons, history_nil,
    List.append_nil, List.nil_append, Option.map_some, Option.map_none, Option.getD_some,
    Option.getD_none]
  simp [matrixGroup_touched, x, y, center, side]

theorem forward_output_history {p : Fin a} {k : Fin M} {T : Fin n}
    (hp : kind p = .output k T) :
    history (forward (s := s) g t kind U G J H) (side p) =
      [g.common, g.common, g.common, mid g (U k), g.yOut (t T), g.full] := by
  have ho : (kind p).outRect = some k := by rw [hp]; rfl
  simp only [forward, history_append, mix_output kind _ one_ne _ ho,
    mix_output kind _ neg_one_ne _ ho, fan_side kind J hJ,
    fan_side kind (-J) (neg_support kind J hJ), copy_side kind _ one_ne,
    copy_side kind _ neg_one_ne, hp, Kind.owner, Kind.target, history_cons, history_nil,
    List.append_nil, List.nil_append, Option.map_some, Option.map_none, Option.getD_some,
    Option.getD_none]
  simp [matrixGroup_touched, x, y, center, side]

theorem forward_direct_history {p : Fin a} {S T : Fin n} (hp : kind p = .direct S T) :
    history (forward (s := s) g t kind U G J H) (side p) =
      [g.common, g.xMiddle (t S), g.yOut (t T), g.full] := by
  have hi : (kind p).inRect = none := by rw [hp]; rfl
  have ho : (kind p).outRect = none := by rw [hp]; rfl
  simp only [forward, history_append, mix_direct kind _ one_ne _ hi ho,
    mix_direct kind _ neg_one_ne _ hi ho, fan_side kind J hJ,
    fan_side kind (-J) (neg_support kind J hJ), copy_side kind _ one_ne,
    copy_side kind _ neg_one_ne, hp, Kind.owner, Kind.target, history_cons, history_nil,
    List.append_nil, List.nil_append, Option.map_some, Option.map_none, Option.getD_some,
    Option.getD_none]
  simp [matrixGroup_touched, x, y, center, side]

end ForwardHistories

section InverseHistories
variable {K E F R : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [CommRing R] [DecidableEq R] [Nontrivial R]
  {n a c s M : ℕ}
variable (g : Geometry K E F) (t : Fin n → F) (kind : Fin a → Kind n M)
  (U' : Fin M → Submodule K F)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

theorem inverse_x_history (j : Fin n) :
    history (inverse (s := s) g t kind U' G J H) (x j) =
      (if ∃ p, (kind p).owner = some j then [g.common] else []) ++
      (if ∃ i, G i j ≠ 0 then [g.common] else []) ++
      (if ∃ i, G i j ≠ 0 then [g.common] else []) ++
      (if ∃ p, (kind p).owner = some j then [g.yOut (t j)] else []) := by
  have hs : ∀ p, (x j : Role n a c s) ≠ side p := fun p => by simp [x, side]
  have hy : ∀ i, (x j : Role n a c s) ≠ y i := fun i => by simp [x, y]
  simp only [inverse, history_append, mix_data kind _ one_ne _ _ hs,
    mix_data kind _ neg_one_ne _ _ hs, fan_data _ _ _ hs hy, copy_x kind _ one_ne,
    copy_x kind _ neg_one_ne, history_cons, history_nil, List.append_nil, List.nil_append]
  simp [matrixGroup_touched, x, y, center, List.append_assoc]

theorem inverse_y_history (i : Fin n) :
    history (inverse (s := s) g t kind U' G J H) (y i) =
      [g.xMiddle (t i), g.full, g.full, g.full] := by
  have hs : ∀ p, (y i : Role n a c s) ≠ side p := fun p => by simp [y, side]
  have hx : ∀ j, (y i : Role n a c s) ≠ x j := fun j => by simp [x, y]
  simp only [inverse, history_append, mix_data kind _ one_ne _ _ hs,
    mix_data kind _ neg_one_ne _ _ hs, fan_y, copy_data kind _ one_ne _ _ hs hx,
    copy_data kind _ neg_one_ne _ _ hs hx, history_cons, history_nil, List.append_nil,
    List.nil_append]
  simp [matrixGroup_touched, x, y, center]

theorem inverse_center_history (j : Fin c) :
    history (inverse (s := s) g t kind U' G J H) (center j) =
      [g.common] ++ (if ∃ i, H i j ≠ 0 then [g.full] else []) ++
      [g.common] ++ (if ∃ i, H i j ≠ 0 then [g.full] else []) := by
  have hs : ∀ p, (center j : Role n a c s) ≠ side p := fun p => by simp [center, side]
  have hx : ∀ j', (center j : Role n a c s) ≠ x j' := fun j' => by simp [x, center]
  have hy : ∀ i, (center j : Role n a c s) ≠ y i := fun i => by simp [center, y]
  simp only [inverse, history_append, mix_data kind _ one_ne _ _ hs,
    mix_data kind _ neg_one_ne _ _ hs, fan_data _ _ _ hs hy,
    copy_data kind _ one_ne _ _ hs hx, copy_data kind _ neg_one_ne _ _ hs hx,
    history_cons, history_nil, List.append_nil, List.nil_append]
  simp [matrixGroup_touched, center, x, y, Pi.neg_apply, List.append_assoc]

theorem inverse_spectator_history (j : Fin s) :
    history (inverse g t kind U' G J H) (spectator j) = [] := by
  have hs : ∀ p, (spectator j : Role n a c s) ≠ side p := fun p => by simp [spectator, side]
  have hx : ∀ j', (spectator j : Role n a c s) ≠ x j' := fun j' => by simp [x, spectator]
  have hy : ∀ i, (spectator j : Role n a c s) ≠ y i := fun i => by simp [spectator, y]
  simp only [inverse, history_append, mix_data kind _ one_ne _ _ hs,
    mix_data kind _ neg_one_ne _ _ hs, fan_data _ _ _ hs hy,
    copy_data kind _ one_ne _ _ hs hx, copy_data kind _ neg_one_ne _ _ hs hx,
    history_cons, history_nil, List.append_nil, List.nil_append]
  simp [matrixGroup_touched, spectator, x, y, center]

variable (hJ : ∀ i p, J i p ≠ 0 ↔ (kind p).target = some i)
include hJ

theorem inverse_input_history (hout : ∀ k, ∃ p, (kind p).outRect = some k)
    {p : Fin a} {k : Fin M} {S : Fin n} (hp : kind p = .input k S) :
    history (inverse (s := s) g t kind U' G J H) (side p) =
      [g.common, g.common, mid g (U' k), g.yOut (t S), g.full, g.full] := by
  have hi : (kind p).inRect = some k := by rw [hp]; rfl
  simp only [inverse, history_append, mix_input kind _ one_ne _ hi (hout k),
    mix_input kind _ neg_one_ne _ hi (hout k), fan_side kind J hJ,
    fan_side kind (-J) (neg_support kind J hJ), copy_side kind _ one_ne,
    copy_side kind _ neg_one_ne, hp, Kind.owner, Kind.target, history_cons, history_nil,
    List.append_nil, List.nil_append, Option.map_some, Option.map_none, Option.getD_some,
    Option.getD_none]
  simp [matrixGroup_touched, x, y, center, side]

theorem inverse_output_history {p : Fin a} {k : Fin M} {T : Fin n}
    (hp : kind p = .output k T) :
    history (inverse (s := s) g t kind U' G J H) (side p) =
      [g.common, g.xMiddle (t T), mid g (U' k), g.full, g.full, g.full] := by
  have ho : (kind p).outRect = some k := by rw [hp]; rfl
  simp only [inverse, history_append, mix_output kind _ one_ne _ ho,
    mix_output kind _ neg_one_ne _ ho, fan_side kind J hJ,
    fan_side kind (-J) (neg_support kind J hJ), copy_side kind _ one_ne,
    copy_side kind _ neg_one_ne, hp, Kind.owner, Kind.target, history_cons, history_nil,
    List.append_nil, List.nil_append, Option.map_some, Option.map_none, Option.getD_some,
    Option.getD_none]
  simp [matrixGroup_touched, x, y, center, side]

theorem inverse_direct_history {p : Fin a} {S T : Fin n} (hp : kind p = .direct S T) :
    history (inverse (s := s) g t kind U' G J H) (side p) =
      [g.common, g.xMiddle (t T), g.yOut (t S), g.full] := by
  have hi : (kind p).inRect = none := by rw [hp]; rfl
  have ho : (kind p).outRect = none := by rw [hp]; rfl
  simp only [inverse, history_append, mix_direct kind _ one_ne _ hi ho,
    mix_direct kind _ neg_one_ne _ hi ho, fan_side kind J hJ,
    fan_side kind (-J) (neg_support kind J hJ), copy_side kind _ one_ne,
    copy_side kind _ neg_one_ne, hp, Kind.owner, Kind.target, history_cons, history_nil,
    List.append_nil, List.nil_append, Option.map_some, Option.map_none, Option.getD_some,
    Option.getD_none]
  simp [matrixGroup_touched, x, y, center, side]

end InverseHistories

section Chains
variable {L : Type*} [Preorder L]

theorem pathRel_le_comparable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {cur : Submodule K V} {xs : List (Submodule K V)} (h : pathRel (· ≤ ·) cur xs) :
    pathRel (fun U W : Submodule K V => U ≤ W ∨ W ≤ U) cur xs := by
  induction xs generalizing cur with
  | nil => trivial
  | cons x xs ih => exact ⟨Or.inl h.1, ih h.2⟩

theorem pathLoss_le_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {cur : Submodule K V} {xs : List (Submodule K V)}
    (h : pathRel (· ≤ ·) cur xs) : pathLoss (fun U : Submodule K V => finrank K U) cur xs = 0 := by
  induction xs generalizing cur with
  | nil => rfl
  | cons x xs ih =>
    simp only [pathLoss]
    rw [ih h.2, Nat.sub_eq_zero_of_le (Submodule.finrank_mono h.1)]

end Chains

section Fits
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] {n a M : ℕ}

/-- Label inclusions along the forward side roles. -/
structure ForwardFit (g : Geometry K E F) (t : Fin n → F) (kind : Fin a → Kind n M)
    (U : Fin M → Submodule K F) : Prop where
  input_le : ∀ {p k S}, kind p = .input k S → K ∙ t S ≤ U k
  output_le : ∀ {p k T}, kind p = .output k T → U k ≤ g.current.orthogonal (K ∙ t T)
  direct_orth : ∀ {p S T}, kind p = .direct S T → g.current (t S) (t T) = 0

/-- Label inclusions along the inverse side roles, where sources and targets swap. -/
structure InverseFit (g : Geometry K E F) (t : Fin n → F) (kind : Fin a → Kind n M)
    (U' : Fin M → Submodule K F) : Prop where
  input_le : ∀ {p k S}, kind p = .input k S → U' k ≤ g.current.orthogonal (K ∙ t S)
  output_le : ∀ {p k T}, kind p = .output k T → K ∙ t T ≤ U' k
  direct_orth : ∀ {p S T}, kind p = .direct S T → g.current (t T) (t S) = 0

end Fits

section Comparability
variable {K E F R : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [CommRing R] [DecidableEq R] [Nontrivial R]
  {n a c s M : ℕ}
variable (g : Geometry K E F) (t : Fin n → F) (kind : Fin a → Kind n M)
  (U U' : Fin M → Submodule K F)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
  (hJ : ∀ i p, J i p ≠ 0 ↔ (kind p).target = some i)
  (hout : ∀ k, ∃ p, (kind p).outRect = some k)

include hJ hout in
/-- Every forward non-central history grows. -/
theorem forward_mono (hf : ForwardFit g t kind U) (i : Role n a c s) (hc : ∀ j, i ≠ center j) :
    pathRel (· ≤ ·) (input g t i) (history (forward g t kind U G J H) i) := by
  rcases i with j | j | p | j | j
  · change pathRel _ (g.xIn (t j)) (history _ (x j))
    rw [forward_x_history]
    have h₁ := g.xIn_le_middle (t j)
    have h₂ := g.middle_le_full (t j)
    have h₃ := h₁.trans h₂
    split_ifs <;> simp [pathRel, h₁, h₂, h₃]
  · change pathRel _ (g.yIn (t j)) (history _ (y j))
    rw [forward_y_history]
    simp [pathRel, g.yIn_le_common, g.common_le_yOut]
  · change pathRel _ ⊥ (history _ (side p))
    cases hp : kind p with
    | input k S =>
      rw [forward_input_history g t kind U G J H hJ hout hp]
      have h₁ : g.common ≤ g.xMiddle (t S) := le_sup_left
      have h₂ : g.xMiddle (t S) ≤ mid g (U k) := mid_mono g (hf.input_le hp)
      simp [pathRel, h₁, h₂, mid_le_full]
    | output k T =>
      rw [forward_output_history g t kind U G J H hJ hp]
      have h₂ : mid g (U k) ≤ g.yOut (t T) := mid_mono g (hf.output_le hp)
      simp [pathRel, common_le_mid, h₂, g.yOut_le_full]
    | direct S T =>
      rw [forward_direct_history g t kind U G J H hJ hp]
      have h₁ : g.common ≤ g.xMiddle (t S) := le_sup_left
      simp [pathRel, h₁, g.side_middle_le_out _ _ (hf.direct_orth hp), g.yOut_le_full]
  · exact absurd rfl (hc j)
  · change pathRel _ ⊥ (history _ (spectator j))
    rw [forward_spectator_history]
    trivial

include hJ hout in
/-- Every inverse non-central history grows. -/
theorem inverse_mono (hf : InverseFit g t kind U') (i : Role n a c s) (hc : ∀ j, i ≠ center j) :
    pathRel (· ≤ ·) (inverseInput g t i) (history (inverse g t kind U' G J H) i) := by
  rcases i with j | j | p | j | j
  · change pathRel _ (g.yIn (t j)) (history _ (x j))
    rw [inverse_x_history]
    have h₁ := g.yIn_le_common (t j)
    have h₂ := g.common_le_yOut (t j)
    have h₃ := h₁.trans h₂
    split_ifs <;> simp [pathRel, h₁, h₂, h₃]
  · change pathRel _ (g.xIn (t j)) (history _ (y j))
    rw [inverse_y_history]
    simp [pathRel, g.xIn_le_middle, g.middle_le_full]
  · change pathRel _ ⊥ (history _ (side p))
    cases hp : kind p with
    | input k S =>
      rw [inverse_input_history g t kind U' G J H hJ hout hp]
      have h₂ : mid g (U' k) ≤ g.yOut (t S) := mid_mono g (hf.input_le hp)
      simp [pathRel, common_le_mid, h₂, g.yOut_le_full]
    | output k T =>
      rw [inverse_output_history g t kind U' G J H hJ hp]
      have h₁ : g.common ≤ g.xMiddle (t T) := le_sup_left
      have h₂ : g.xMiddle (t T) ≤ mid g (U' k) := mid_mono g (hf.output_le hp)
      simp [pathRel, h₁, h₂, mid_le_full]
    | direct S T =>
      rw [inverse_direct_history g t kind U' G J H hJ hp]
      have h₁ : g.common ≤ g.xMiddle (t T) := le_sup_left
      simp [pathRel, h₁, g.side_middle_le_out _ _ (hf.direct_orth hp), g.yOut_le_full]
  · exact absurd rfl (hc j)
  · change pathRel _ ⊥ (history _ (spectator j))
    rw [inverse_spectator_history]
    trivial

end Comparability

section Network
variable {K E F R : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [CommRing R] [DecidableEq R] [Nontrivial R]
  {n a c s M : ℕ}
variable (g : Geometry K E F) (t : Fin n → F) (kind : Fin a → Kind n M)
  (U U' : Fin M → Submodule K F)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

/-- Role exchange preserves the full physical incidence history. -/
theorem opposite_history (i : Role n a c s) :
    history (opposite g t kind U' G J H) (exchangeRoles n a c s i) =
      history (inverse g t kind U' G J H) i := by
  unfold opposite
  generalize inverse (s := s) g t kind U' G J H = vs
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, history_cons]
    have hh := GroupedCircuit.touched_rename (exchangeRoles n a c s) v.group i
    simp only [ih]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact False.elim (h₂ (hh.mp h₁))
    · exact False.elim (h₁ (hh.mpr h₂))
    · rfl

theorem forward_final_le_output (i : Role n a c s) :
    finalLabels (input g t) (forward g t kind U G J H) i ≤ output g t i := by
  rcases i with j | j | j
  · exact le_top
  · change finalLabels (input g t) (forward g t kind U G J H) (y j) ≤ g.yOut (t j)
    rw [finalLabels_history, forward_y_history]
    simp
  · exact le_top

theorem opposite_final_le_output (i : Role n a c s) :
    finalLabels (input g t) (opposite g t kind U' G J H) i ≤ output g t i := by
  rcases i with j | j | j
  · exact le_top
  · have he : (Sum.inr (Sum.inl j) : Role n a c s) = exchangeRoles n a c s (x j) := rfl
    have hi : input g t (exchangeRoles n a c s (x j)) = g.yIn (t j) := rfl
    have ho : output g t (exchangeRoles n a c s (x j)) = g.yOut (t j) := rfl
    rw [he, finalLabels_history, opposite_history, hi, ho, inverse_x_history]
    have h₁ := g.common_le_yOut (t j)
    have h₂ := (g.yIn_le_common (t j)).trans h₁
    split_ifs <;> simp [h₁, h₂]
  · exact le_top

theorem forward_center_comparable (j : Fin c) :
    pathRel Comparable (⊥ : Submodule K (E ⊗[K] F))
      (history (forward (s := s) g t kind U G J H) (center j)) := by
  rw [forward_center_history]
  split_ifs <;> simp [pathRel, Comparable, g.common_le_full]

theorem inverse_center_comparable (j : Fin c) :
    pathRel Comparable (⊥ : Submodule K (E ⊗[K] F))
      (history (inverse (s := s) g t kind U' G J H) (center j)) := by
  rw [inverse_center_history]
  split_ifs <;> simp [pathRel, Comparable, g.common_le_full]

variable (hJ : ∀ i p, J i p ≠ 0 ↔ (kind p).target = some i)
  (hout : ∀ k, ∃ p, (kind p).outRect = some k)
include hJ hout

theorem forward_histories_comparable (hf : ForwardFit g t kind U) (i : Role n a c s) :
    pathRel Comparable (input g t i) (history (forward g t kind U G J H) i) := by
  by_cases hc : ∃ j, i = center j
  · obtain ⟨j, rfl⟩ := hc
    exact forward_center_comparable g t kind U G J H j
  · simp only [not_exists] at hc
    exact pathRel_le_comparable (forward_mono g t kind U G J H hJ hout hf i hc)

theorem inverse_histories_comparable (hf : InverseFit g t kind U') (i : Role n a c s) :
    pathRel Comparable (inverseInput g t i) (history (inverse g t kind U' G J H) i) := by
  by_cases hc : ∃ j, i = center j
  · obtain ⟨j, rfl⟩ := hc
    exact inverse_center_comparable g t kind U' G J H j
  · simp only [not_exists] at hc
    exact pathRel_le_comparable (inverse_mono g t kind U' G J H hJ hout hf i hc)

theorem opposite_histories_comparable (hf : InverseFit g t kind U') (i : Role n a c s) :
    pathRel Comparable (input g t i) (history (opposite g t kind U' G J H) i) := by
  obtain ⟨i, rfl⟩ := (exchangeRoles n a c s).surjective i
  rw [opposite_history]
  have hi : input g t (exchangeRoles n a c s i) = inverseInput g t i := by
    rcases i with j | j | j <;> rfl
  rw [hi]
  exact inverse_histories_comparable g t kind U' G J H hJ hout hf i

theorem forward_edges_comparable (hf : ForwardFit g t kind U) :
    ∀ p ∈ RankTrace.edges (input (s := s) g t) (updates (forward g t kind U G J H)),
      Comparable p.1 p.2 :=
  edges_history_rel Comparable (fun _ => Or.inl le_rfl) _ _
    (forward_histories_comparable g t kind U G J H hJ hout hf)

theorem opposite_edges_comparable (hf : InverseFit g t kind U') :
    ∀ p ∈ RankTrace.edges (input (s := s) g t) (updates (opposite g t kind U' G J H)),
      Comparable p.1 p.2 :=
  edges_history_rel Comparable (fun _ => Or.inl le_rfl) _ _
    (opposite_histories_comparable g t kind U' G J H hJ hout hf)

theorem forward_network_comparable (hf : ForwardFit g t kind U) (wires : List (Role n a c s)) :
    ∀ p ∈ RankTrace.edges (input g t)
      (networkUpdates wires (output g t) (forward g t kind U G J H)), Comparable p.1 p.2 := by
  intro p hp
  rw [networkUpdates, RankTrace.edges_append, List.mem_append] at hp
  rcases hp with hp | hp
  · exact forward_edges_comparable g t kind U G J H hJ hout hf p hp
  · apply edges_endpoints_rel Comparable (fun _ => Or.inl le_rfl) _ _ wires _ p hp
    intro i _
    rw [← finalLabels_trace]
    exact Or.inl (forward_final_le_output g t kind U G J H i)

theorem opposite_network_comparable (hf : InverseFit g t kind U') (wires : List (Role n a c s)) :
    ∀ p ∈ RankTrace.edges (input g t)
      (networkUpdates wires (output g t) (opposite g t kind U' G J H)), Comparable p.1 p.2 := by
  intro p hp
  rw [networkUpdates, RankTrace.edges_append, List.mem_append] at hp
  rcases hp with hp | hp
  · exact opposite_edges_comparable g t kind U' G J H hJ hout hf p hp
  · apply edges_endpoints_rel Comparable (fun _ => Or.inl le_rfl) _ _ wires _ p hp
    intro i _
    rw [← finalLabels_trace]
    exact Or.inl (opposite_final_le_output g t kind U' G J H i)

end Network

section Loss
variable {K E F R : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
  [CommRing R] [DecidableEq R] [Nontrivial R]
  {n a c s M : ℕ}
variable (g : Geometry K E F) (t : Fin n → F) (kind : Fin a → Kind n M)
  (U U' : Fin M → Submodule K F)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)

/-- Only the full-to-common transition on a covered central wire loses rank. -/
theorem forward_center_loss (j : Fin c) :
    pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (⊥ : Submodule K (E ⊗[K] F))
      (history (forward (s := s) g t kind U G J H) (center j)) =
      if ∃ i, H i j ≠ 0 then finrank K F else 0 := by
  rw [forward_center_history]
  have h₁ := Submodule.finrank_mono g.common_le_full
  have h₂ := g.central_dimension_loss
  split_ifs <;> simp [pathLoss]
  omega

theorem inverse_center_loss (j : Fin c) :
    pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (⊥ : Submodule K (E ⊗[K] F))
      (history (inverse (s := s) g t kind U' G J H) (center j)) =
      if ∃ i, H i j ≠ 0 then finrank K F else 0 := by
  rw [inverse_center_history]
  have h₁ := Submodule.finrank_mono g.common_le_full
  have h₂ := g.central_dimension_loss
  split_ifs <;> simp [pathLoss]
  omega

variable (hJ : ∀ i p, J i p ≠ 0 ↔ (kind p).target = some i)
  (hout : ∀ k, ∃ p, (kind p).outRect = some k)
include hJ hout

/-- The exact forward invocation loss comes only from the covered central columns. -/
theorem forward_loss (hf : ForwardFit g t kind U) :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (input (a := a) (c := c) (s := s) g t) (updates (forward g t kind U G J H)) =
      ∑ j : Fin c, if ∃ i, H i j ≠ 0 then finrank K F else 0 := by
  rw [loss_history]
  have hz : ∀ i : Role n a c s, (∀ j, i ≠ center j) →
      pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (input g t i)
        (history (forward g t kind U G J H) i) = 0 :=
    fun i hc => pathLoss_le_zero (forward_mono g t kind U G J H hJ hout hf i hc)
  have hc := forward_center_loss (s := s) g t kind U G J H
  have hx : ∀ j, _ = 0 := fun j => hz (x j) (fun j' => by simp [x, center])
  have hy : ∀ j, _ = 0 := fun j => hz (y j) (fun j' => by simp [y, center])
  have hp : ∀ p, _ = 0 := fun p => hz (side p) (fun j' => by simp [side, center])
  have hs : ∀ j, _ = 0 := fun j => hz (spectator j) (fun j' => by simp [spectator, center])
  simp only [x] at hx
  simp only [y] at hy
  simp only [side] at hp
  simp only [spectator] at hs
  have hc' : ∀ j : Fin c, pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (input g t (center j : Role n a c s)) (history (forward g t kind U G J H) (center j)) =
      if ∃ i, H i j ≠ 0 then finrank K F else 0 := hc
  simp only [center] at hc'
  simp only [Fintype.sum_sum_type, hx, hy, hp, hs, hc', Finset.sum_const_zero, zero_add, add_zero]

theorem inverse_loss (hf : InverseFit g t kind U') :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (inverseInput (a := a) (c := c) (s := s) g t) (updates (inverse g t kind U' G J H)) =
      ∑ j : Fin c, if ∃ i, H i j ≠ 0 then finrank K F else 0 := by
  rw [loss_history]
  have hz : ∀ i : Role n a c s, (∀ j, i ≠ center j) →
      pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (inverseInput g t i)
        (history (inverse g t kind U' G J H) i) = 0 :=
    fun i hc => pathLoss_le_zero (inverse_mono g t kind U' G J H hJ hout hf i hc)
  have hc := inverse_center_loss (s := s) g t kind U' G J H
  have hx : ∀ j, _ = 0 := fun j => hz (x j) (fun j' => by simp [x, center])
  have hy : ∀ j, _ = 0 := fun j => hz (y j) (fun j' => by simp [y, center])
  have hp : ∀ p, _ = 0 := fun p => hz (side p) (fun j' => by simp [side, center])
  have hs : ∀ j, _ = 0 := fun j => hz (spectator j) (fun j' => by simp [spectator, center])
  simp only [x] at hx
  simp only [y] at hy
  simp only [side] at hp
  simp only [spectator] at hs
  have hc' : ∀ j : Fin c, pathLoss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (inverseInput g t (center j : Role n a c s)) (history (inverse g t kind U' G J H) (center j)) =
      if ∃ i, H i j ≠ 0 then finrank K F else 0 := hc
  simp only [center] at hc'
  simp only [Fintype.sum_sum_type, hx, hy, hp, hs, hc', Finset.sum_const_zero, zero_add, add_zero]

theorem forward_loss_le (hf : ForwardFit g t kind U) :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (input (a := a) (c := c) (s := s) g t) (updates (forward g t kind U G J H)) ≤
      c * finrank K F := by
  rw [forward_loss g t kind U G J H hJ hout hf]
  calc
    _ ≤ ∑ _j : Fin c, finrank K F := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
    _ = _ := by simp

theorem inverse_loss_le (hf : InverseFit g t kind U') :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (inverseInput (a := a) (c := c) (s := s) g t) (updates (inverse g t kind U' G J H)) ≤
      c * finrank K F := by
  rw [inverse_loss g t kind U' G J H hJ hout hf]
  calc
    _ ≤ ∑ _j : Fin c, finrank K F := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
    _ = _ := by simp

omit hJ hout in
/-- Physical role exchange preserves the exact loss. -/
theorem opposite_loss_eq_inverse :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (input (a := a) (c := c) (s := s) g t) (updates (opposite g t kind U' G J H)) =
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (inverseInput (a := a) (c := c) (s := s) g t) (updates (inverse g t kind U' G J H)) := by
  rw [loss_history, loss_history]
  symm
  apply Fintype.sum_equiv (exchangeRoles n a c s)
  intro i
  rw [opposite_history]
  congr 1
  rcases i with i | i | i <;> rfl

theorem opposite_loss_le (hf : InverseFit g t kind U') :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (input (a := a) (c := c) (s := s) g t) (updates (opposite g t kind U' G J H)) ≤
      c * finrank K F := by
  rw [opposite_loss_eq_inverse]
  exact inverse_loss_le g t kind U' G J H hJ hout hf

omit hJ hout in
/-- Explicit output edges contribute zero additional loss in the forward invocation. -/
theorem forward_network_loss (wires : List (Role n a c s)) :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (input g t)
      (networkUpdates wires (output g t) (forward (s := s) g t kind U G J H)) =
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (input g t)
      (updates (forward (s := s) g t kind U G J H)) := by
  rw [networkUpdates, loss_append, loss_align]
  have hz : ∀ i : Role n a c s, (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (RankTrace.finish (input g t) (updates (forward (s := s) g t kind U G J H)) i) -
      finrank K (output g t i) = 0 := by
    intro i
    rw [← finalLabels_trace]
    exact Nat.sub_eq_zero_of_le
      (Submodule.finrank_mono (forward_final_le_output g t kind U G J H i))
  simp [hz]

omit hJ hout in
theorem opposite_network_loss (wires : List (Role n a c s)) :
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (input g t)
      (networkUpdates wires (output g t) (opposite (s := s) g t kind U' G J H)) =
    RankTrace.loss (fun U : Submodule K (E ⊗[K] F) => finrank K U) (input g t)
      (updates (opposite (s := s) g t kind U' G J H)) := by
  rw [networkUpdates, loss_append, loss_align]
  have hz : ∀ i : Role n a c s, (fun U : Submodule K (E ⊗[K] F) => finrank K U)
      (RankTrace.finish (input g t) (updates (opposite (s := s) g t kind U' G J H)) i) -
      finrank K (output g t i) = 0 := by
    intro i
    rw [← finalLabels_trace]
    exact Nat.sub_eq_zero_of_le
      (Submodule.finrank_mono (opposite_final_le_output g t kind U' G J H i))
  simp [hz]

end Loss

section Nondegeneracy
variable {K E F R : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
  [CommRing R] [DecidableEq R]
  {n a c s M : ℕ}
variable (g : Geometry K E F) (t : Fin n → F) (kind : Fin a → Kind n M)
  (U U' : Fin M → Submodule K F)
  (G : Fin c → Fin n → R) (J : Fin n → Fin a → R) (H : Fin n → Fin c → R)
  (ht : ∀ j, g.current (t j) (t j) ≠ 0)
include ht

omit ht in
theorem mixRowV_label {ε : R} {lab : Fin M → Submodule K (E ⊗[K] F)}
    {v : Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R} (hv : v ∈ mixRowV kind ε lab) :
    ∃ k, v.label = lab k := by
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hv
  exact ⟨k, rfl⟩

omit ht in
theorem copyRowV_label {ε : R} {lab : Fin n → Submodule K (E ⊗[K] F)}
    {v : Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R} (hv : v ∈ copyRowV kind ε lab) :
    ∃ j, v.label = lab j := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hv
  exact ⟨j, rfl⟩

omit ht in
theorem faninRowV_label {P : Fin n → Fin a → R} {lab : Fin n → Submodule K (E ⊗[K] F)}
    {v : Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R} (hv : v ∈ faninRowV P lab) :
    ∃ i, v.label = lab i := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact ⟨i, rfl⟩

/-- Every forward group carries a nondegenerate label. -/
theorem forward_nondegenerate (hU : ∀ k, (g.current.restrict (U k)).Nondegenerate)
    (v : Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R)
    (hv : v ∈ forward g t kind U G J H) : (g.pairing.restrict v.label).Nondegenerate := by
  simp only [forward, List.mem_append, List.mem_singleton, or_assoc] at hv
  rcases hv with hv | hv | hv | rfl | hv | rfl | rfl | hv | hv | hv | rfl | hv
  · obtain ⟨k, hk⟩ := mixRowV_label kind hv; rw [hk]; exact g.common_nondegenerate
  · obtain ⟨i, hi⟩ := faninRowV_label hv; rw [hi]; exact g.common_nondegenerate
  · obtain ⟨k, hk⟩ := mixRowV_label kind hv; rw [hk]; exact g.common_nondegenerate
  · exact g.common_nondegenerate
  · obtain ⟨j, hj⟩ := copyRowV_label kind hv; rw [hj]; exact g.xMiddle_nondegenerate _ (ht j)
  · exact g.full_nondegenerate
  · exact g.common_nondegenerate
  · obtain ⟨k, hk⟩ := mixRowV_label kind hv; rw [hk]; exact mid_nondegenerate g _ (hU k)
  · obtain ⟨i, hi⟩ := faninRowV_label hv; rw [hi]; exact g.yOut_nondegenerate _ (ht i)
  · obtain ⟨k, hk⟩ := mixRowV_label kind hv; rw [hk]; exact g.full_nondegenerate
  · exact g.full_nondegenerate
  · obtain ⟨j, hj⟩ := copyRowV_label kind hv; rw [hj]; exact g.full_nondegenerate

theorem inverse_nondegenerate (hU' : ∀ k, (g.current.restrict (U' k)).Nondegenerate)
    (v : Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R)
    (hv : v ∈ inverse g t kind U' G J H) : (g.pairing.restrict v.label).Nondegenerate := by
  simp only [inverse, List.mem_append, List.mem_singleton, or_assoc] at hv
  rcases hv with hv | rfl | hv | hv | hv | rfl | rfl | hv | rfl | hv | hv | hv
  · obtain ⟨j, hj⟩ := copyRowV_label kind hv; rw [hj]; exact g.common_nondegenerate
  · exact g.common_nondegenerate
  · obtain ⟨k, hk⟩ := mixRowV_label kind hv; rw [hk]; exact g.common_nondegenerate
  · obtain ⟨i, hi⟩ := faninRowV_label hv; rw [hi]; exact g.xMiddle_nondegenerate _ (ht i)
  · obtain ⟨k, hk⟩ := mixRowV_label kind hv; rw [hk]; exact mid_nondegenerate g _ (hU' k)
  · exact g.full_nondegenerate
  · exact g.common_nondegenerate
  · obtain ⟨j, hj⟩ := copyRowV_label kind hv; rw [hj]; exact g.yOut_nondegenerate _ (ht j)
  · exact g.full_nondegenerate
  · obtain ⟨k, hk⟩ := mixRowV_label kind hv; rw [hk]; exact g.full_nondegenerate
  · obtain ⟨i, hi⟩ := faninRowV_label hv; rw [hi]; exact g.full_nondegenerate
  · obtain ⟨k, hk⟩ := mixRowV_label kind hv; rw [hk]; exact g.full_nondegenerate

theorem opposite_nondegenerate (hU' : ∀ k, (g.current.restrict (U' k)).Nondegenerate)
    (v : Vertex (Role n a c s) (Submodule K (E ⊗[K] F)) R)
    (hv : v ∈ opposite g t kind U' G J H) : (g.pairing.restrict v.label).Nondegenerate := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  exact inverse_nondegenerate g t kind U' G J H ht hU' w hw

end Nondegeneracy

end IntegerMultBounds.Networks.Mixer.Motif
