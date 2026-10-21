module

public import IntegerMultBounds.MathlibTM2.M8.Global.ChainMoments

/-!
# Moments of the PR97 node's moves

For every `φ` that is nonnegative, monotone and subadditive (`φ (a + b) ≤ φ a + φ b`), such as
`r ↦ (r / m) ^ τ`, the moment of the node's moves is at most the moment of the stage-2 rank
histogram (`node_moment_le`):

* a data role `X S T` or `Y S T` climbs by `22`, `484`, `22`: its local chains each pass through
  two frames (`chainMoment_two`), and the junction of the two stages is refined through the
  connector frames;
* a side slot of either stage makes the moves of its local chain `0, …, 1` (`localMoment`), once
  more reflected in stage two (`chainMoment_compl`), and one exterior move of rank `506`;
* a centre temporary makes one move of rank at most `22`, a correction temporary one of rank one.

Lifting by `P_S`, `Q_T` of rank one keeps every local move rank (`chainMoment_lift`), and the
refinements only split moves (`chainMoment_insert`). The side slots' local chains are left as the
sum `Σ_s localMoment φ s`, over the compiled slots.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Global

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Local IntegerMultBounds.MathlibTM2.M8.Frames
open Classical

/-! ### Lifts -/

theorem stepMoment_lift {M : Type} [AddCommMonoid M] (φ : ℕ → M) {f : LMat → Mat 529}
    {a b : LMat} (hab : Le a b) (hr : (f b - f a).rank = (b - a).rank) :
    stepMoment φ (f a) (f b) = stepMoment φ a b := by
  rw [stepMoment_eq, stepMoment_eq, rank_sub_comm, hr, rank_sub_comm b a]
  by_cases h : a = b
  · subst h; simp
  · have hne : f a ≠ f b := by
      intro e
      apply h
      have h0 : (b - a).rank = 0 := by rw [← hr, e, sub_self, Matrix.rank_zero]
      exact (sub_eq_zero.mp (eq_zero_of_rank_eq_zero h0)).symm
    rw [ite_eq_right hne, ite_eq_right h]

/-- **Lifted chains** have the moments of their local chains. -/
theorem chainMoment_lift {M : Type} [AddCommMonoid M] (φ : ℕ → M) {f : LMat → Mat 529}
    (hf : ∀ {a b : LMat}, a * a = a → b * b = b → Le a b → (f b - f a).rank = (b - a).rank) :
    ∀ l : List LMat, l.Pairwise Le → (∀ x ∈ l, x * x = x) →
      chainMoment φ (l.map f) = chainMoment φ l
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | a :: b :: l, hpw, hid => by
    have hab : Le a b := (List.pairwise_cons.mp hpw).1 b (by simp)
    rw [List.map_cons, List.map_cons, chainMoment_cons_cons, ← List.map_cons,
      chainMoment_lift φ hf (b :: l) (List.Pairwise.of_cons hpw)
        (fun x hx => hid x (List.mem_cons_of_mem _ hx)),
      stepMoment_lift φ hab (hf (hid a (by simp)) (hid b (by simp)) hab), chainMoment_cons_cons]

theorem lift1_rank (T : V) {a b : LMat} (ha : a * a = a) (hb : b * b = b) (h : Le a b) :
    (lift1 (lineOf T) b - lift1 (lineOf T) a).rank = (b - a).rank := by
  rw [rank_lift1_sub (lineOf_idem T) ha hb h, rank_lineOf, mul_one]

theorem lift2_rank (S : V) {a b : LMat} (ha : a * a = a) (hb : b * b = b) (h : Le a b) :
    (lift2 (lineOf S) b - lift2 (lineOf S) a).rank = (b - a).rank := by
  rw [rank_lift2_sub (lineOf_idem S) ha hb h, rank_lineOf, one_mul]

theorem lift1_idem (T : V) {a : LMat} (ha : a * a = a) :
    lift1 (lineOf T) a * lift1 (lineOf T) a = lift1 (lineOf T) a := by
  rw [lift1, kron_mul, ha, lineOf_idem]

theorem lift2_idem (S : V) {a : LMat} (ha : a * a = a) :
    lift2 (lineOf S) a * lift2 (lineOf S) a = lift2 (lineOf S) a := by
  rw [lift2_mul (lineOf_idem S), ha]

/-! ### Single moves -/

theorem rank_compl_lineOf (k : V) : (1 - lineOf k).rank = 22 := by
  have := rank_sub_of_le (lineOf_idem k) (Matrix.one_mul (1 : LMat)) (le_one (lineOf k))
  rw [rank_lineOf, rank_one, Fintype.card_fin] at this
  omega

theorem compl_idem {d : ℕ} {A : Mat d} (h : A * A = A) : (1 - A) * (1 - A) = 1 - A := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h]; abel

theorem stepMoment_of_rank {M : Type} [AddCommMonoid M] (φ : ℕ → M) {d : ℕ} {A B : Mat d}
    {r : ℕ} (hr : (A - B).rank = r) (hr0 : r ≠ 0) : stepMoment φ A B = φ r := by
  rw [stepMoment_eq, hr]
  have hne : A ≠ B := by
    intro e; subst e; rw [sub_self, Matrix.rank_zero] at hr; exact hr0 hr.symm
  rw [ite_eq_right hne]

theorem step_lineOf_one {M : Type} [AddCommMonoid M] (φ : ℕ → M) (k : V) :
    stepMoment φ (lineOf k) 1 = φ 22 :=
  stepMoment_of_rank φ (by rw [rank_sub_comm]; exact rank_compl_lineOf k) (by norm_num)

theorem step_zero_compl {M : Type} [AddCommMonoid M] (φ : ℕ → M) (k : V) :
    stepMoment φ 0 (1 - lineOf k) = φ 22 :=
  stepMoment_of_rank φ (by rw [zero_sub, rank_neg]; exact rank_compl_lineOf k) (by norm_num)

theorem rank_kron_compl (S T : V) : (kron (1 - lineOf S) (1 - lineOf T)).rank = 484 := by
  rw [kron_rank (compl_idem (lineOf_idem S)) (compl_idem (lineOf_idem T)), rank_compl_lineOf,
    rank_compl_lineOf]

theorem connector_x_diff (S T : V) :
    lift2 (lineOf S) (lineOf T) - lift1 (lineOf T) 1 = kron (1 - lineOf S) (1 - lineOf T) := by
  have h : kron (1 - lineOf S) (lineOf T) + kron (lineOf S) (lineOf T) = kron 1 (lineOf T) := by
    rw [← kron_add_left, sub_add_cancel]
  rw [lift2, lift1, ← h, kron_sub_right]
  abel

theorem connector_y_diff (S T : V) :
    lift2 (lineOf S) 0 - lift1 (lineOf T) (1 - lineOf S) = kron (1 - lineOf S) (1 - lineOf T) := by
  rw [lift2_zero, lift1, kron_sub_right]

theorem step_connector_x {M : Type} [AddCommMonoid M] (φ : ℕ → M) (S T : V) :
    stepMoment φ (lift1 (lineOf T) 1) (lift2 (lineOf S) (lineOf T)) = φ 484 :=
  stepMoment_of_rank φ (by rw [rank_sub_comm, connector_x_diff, rank_kron_compl]) (by norm_num)

theorem step_connector_y {M : Type} [AddCommMonoid M] (φ : ℕ → M) (S T : V) :
    stepMoment φ (lift1 (lineOf T) (1 - lineOf S)) (lift2 (lineOf S) 0) = φ 484 :=
  stepMoment_of_rank φ (by rw [rank_sub_comm, connector_y_diff, rank_kron_compl]) (by norm_num)

theorem rank_kron_one_lineOf (T : V) : (kron 1 (lineOf T)).rank = 23 := by
  rw [kron_rank (Matrix.one_mul (1 : LMat)) (lineOf_idem T), rank_one, Fintype.card_fin, rank_lineOf]

theorem step_sink1 {M : Type} [AddCommMonoid M] (φ : ℕ → M) (T : V) :
    stepMoment φ (lift1 (lineOf T) 1) 1 = φ 506 := by
  have hidem : kron 1 (lineOf T) * kron 1 (lineOf T) = kron 1 (lineOf T) := by
    rw [kron_mul, Matrix.one_mul, lineOf_idem]
  have h := rank_sub_of_le hidem (Matrix.one_mul (1 : Mat 529)) (le_one (kron 1 (lineOf T)))
  rw [rank_kron_one_lineOf, rank_one529] at h
  exact stepMoment_of_rank φ (by rw [rank_sub_comm, lift1]; omega) (by norm_num)

theorem step_source2 {M : Type} [AddCommMonoid M] (φ : ℕ → M) (S : V) :
    stepMoment φ 0 (lift2 (lineOf S) 0) = φ 506 := by
  refine stepMoment_of_rank φ ?_ (by norm_num)
  rw [zero_sub, rank_neg, lift2_zero, kron_rank (compl_idem (lineOf_idem S))
    (Matrix.one_mul (1 : LMat)), rank_compl_lineOf, rank_one, Fintype.card_fin]

/-- A temporary's chain: one frame, then another. -/
theorem chainMoment_temp (φ : ℕ → ℝ) (h0 : ∀ n, 0 ≤ φ n) {d : ℕ} (a b : Mat d) (l : List ℕ) :
    chainMoment φ (a :: a :: l.map fun _ => b) ≤ φ (a - b).rank := by
  rw [chainMoment_cons_cons, stepMoment, ite_eq_left rfl, zero_add]
  cases l with
  | nil => exact h0 _
  | cons x l =>
    rw [List.map_cons, chainMoment_cons_cons]
    have hc : chainMoment φ (b :: l.map fun _ => b) = 0 := by
      induction l with
      | nil => rfl
      | cons y l ih => rw [List.map_cons, chainMoment_cons_cons, ih, stepMoment, ite_eq_left rfl]; simp
    rw [hc, add_zero, stepMoment_eq]
    split_ifs
    · exact h0 _
    · exact le_rfl

/-! ### Local chains -/

theorem local_idem {l : List LMat} (h : ∀ f ∈ l, ∃ v ∈ stage1, v.frame = f) : ∀ f ∈ l, f * f = f := by
  intro f hf
  obtain ⟨v, hv, rfl⟩ := h f hf
  exact (stage1_frames v hv).idem

theorem fseq_stage1_frames (w : LW) : ∀ f ∈ fseq w stage1, ∃ v ∈ stage1, v.frame = f :=
  fun _ hf => fseq_frames hf

/-- The moments of a side slot's local chain, from `0` to `1`. -/
def localMoment {M : Type} [AddCommMonoid M] (φ : ℕ → M) (s : ℕ) : M :=
  chainMoment φ ((0 : LMat) :: (fseq (.inl (.aux s)) stage1 ++ [1]))

theorem local_pairwise (s : ℕ) : ((0 : LMat) :: (fseq (.inl (.aux s)) stage1 ++ [1])).Pairwise Le := by
  rw [← List.cons_append]
  exact pw_app (chain1_aux s) (List.pairwise_singleton _ _)
    (fun a _ b hb => by rw [List.mem_singleton.mp hb]; exact le_one a)

theorem local_chain_idem (s : ℕ) :
    ∀ f ∈ (0 : LMat) :: (fseq (.inl (.aux s)) stage1 ++ [1]), f * f = f := by
  intro f hf
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | hf | rfl
  · simp
  · exact local_idem (fseq_stage1_frames _) f hf
  · simp

/-! ### Appending a frame -/

theorem chainMoment_append_single {M : Type} [AddCommMonoid M] (φ : ℕ → M) {d : ℕ} :
    ∀ (l : List (Mat d)) (a x : Mat d),
      chainMoment φ ((a :: l) ++ [x]) = chainMoment φ (a :: l) + stepMoment φ ((a :: l).getLast (by simp)) x
  | [], a, x => by simp [chainMoment]
  | b :: l, a, x => by
    rw [List.cons_append, List.cons_append, chainMoment_cons_cons, ← List.cons_append,
      chainMoment_append_single φ l b x, chainMoment_cons_cons, List.getLast_cons_cons, add_assoc]

theorem wireMoment_side {M : Type} [AddCommMonoid M] (φ : ℕ → M) (b : Bool) (k : V) (s : Slot) :
    wireMoment φ (wSide b k s) =
      chainMoment φ ((gInit (wSide b k s) :: fseq (wSide b k s) allGates) ++ [1]) := by
  rw [wireMoment, ite_eq_left (mem_sideWires.mpr ⟨b, k, s, rfl⟩), lastFrame_eq,
    chainMoment_append_single]

/-! ### Wire bounds -/

variable (φ : ℕ → ℝ) (h0 : ∀ n, 0 ≤ φ n) (hmono : Monotone φ)
  (hsub : ∀ a b, φ (a + b) ≤ φ a + φ b)

include hsub in
/-- Stage one along a side slot, for any local chain `0, L, 1`: the lifted chain and its sink. -/
theorem side1_chain (T : V) (L : List LMat) (hpw : ((0 : LMat) :: (L ++ [1])).Pairwise Le)
    (hid : ∀ f ∈ (0 : LMat) :: (L ++ [1]), f * f = f) :
    chainMoment φ ((((0 : LMat) :: L).map (lift1 (lineOf T))) ++ [1]) ≤
      chainMoment φ ((0 : LMat) :: (L ++ [1])) + φ 506 := by
  have hne : ((0 : LMat) :: L) ≠ [] := List.cons_ne_nil _ _
  have hlast : ((0 : LMat) :: L).getLast hne ∈ (0 : LMat) :: (L ++ [1]) := by
    have := List.getLast_mem hne
    simp only [List.mem_cons, List.mem_append] at this ⊢
    tauto
  set A := ((0 : LMat) :: L).getLast hne
  set Z := ((0 : LMat) :: L).map (lift1 (lineOf T))
  have hA := hid A hlast
  have hsplit : Z = Z.dropLast ++ [lift1 (lineOf T) A] := by
    conv_lhs => rw [← List.dropLast_append_getLast (show Z ≠ [] by simp [Z])]
    rw [List.getLast_map]
  have hins := chainMoment_insert φ hsub Z.dropLast []
    (lift1_idem T hA) (Matrix.one_mul (1 : Mat 529)) (lift1_idem T (Matrix.one_mul (1 : LMat)))
    (le_lift1 (lineOf_idem T) (le_one A)) (le_one _)
  have hl : Z ++ [1] = Z.dropLast ++ [lift1 (lineOf T) A, 1] := by
    conv_lhs => rw [hsplit]
    simp
  have hr : Z.dropLast ++ [lift1 (lineOf T) A, lift1 (lineOf T) 1, 1] = Z ++ [lift1 (lineOf T) 1, 1] := by
    conv_rhs => rw [hsplit]
    simp
  have hZ : Z ++ [lift1 (lineOf T) 1] = ((0 : LMat) :: (L ++ [1])).map (lift1 (lineOf T)) := by
    simp [Z]
  rw [hl]
  refine hins.trans (le_of_eq ?_)
  rw [hr, chainMoment_snoc, hZ, step_sink1, chainMoment_lift φ (fun ha hb h => lift1_rank T ha hb h) _ hpw hid]

include hsub in
/-- Stage two along a side slot: the reflected local chain lifted, its source and its sink. -/
theorem side2_chain (S : V) (L : List LMat) (hpw : ((0 : LMat) :: (L ++ [1])).Pairwise Le)
    (hid : ∀ f ∈ (0 : LMat) :: (L ++ [1]), f * f = f) :
    chainMoment φ (((0 : Mat 529) :: ((L.map (1 - ·)).reverse.map (lift2 (lineOf S)))) ++ [1]) ≤
      chainMoment φ ((0 : LMat) :: (L ++ [1])) + φ 506 := by
  set R := (L.map (1 - ·)).reverse with hR
  have hchain : (0 : LMat) :: (R ++ [1]) = (((0 : LMat) :: (L ++ [1])).map (1 - ·)).reverse := by
    rw [hR, List.map_cons, List.map_append, List.reverse_cons, List.reverse_append]
    simp
  have hpw' : ((0 : LMat) :: (R ++ [1])).Pairwise Le := by rw [hchain]; exact pairwise_reflect hpw
  have hid' : ∀ f ∈ (0 : LMat) :: (R ++ [1]), f * f = f := by
    rw [hchain]
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
    exact compl_idem (hid g hg)
  have hlist : ((0 : Mat 529) :: (R.map (lift2 (lineOf S)))) ++ [1] =
      (0 : Mat 529) :: (R ++ [1]).map (lift2 (lineOf S)) := by
    simp [lift2_one]
  rw [hlist]
  obtain ⟨B, rest, hB⟩ : ∃ B rest, R ++ [1] = B :: rest := by
    cases h : R ++ [1] with
    | nil => exact absurd h (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
    | cons B rest => exact ⟨B, rest, rfl⟩
  have hBi : B * B = B := hid' B (by rw [hB]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  rw [hB, List.map_cons]
  have hins := chainMoment_insert φ hsub [] (rest.map (lift2 (lineOf S)))
    (Matrix.zero_mul (0 : Mat 529)) (lift2_idem S hBi) (lift2_idem S (Matrix.zero_mul (0 : LMat)))
    (zero_le _) (le_lift2 (lineOf_idem S) (zero_le B))
  rw [List.nil_append, List.nil_append] at hins
  refine hins.trans (le_of_eq ?_)
  rw [chainMoment_cons_cons, step_source2, ← List.map_cons, ← hB]
  have hl := chainMoment_lift φ (f := lift2 (lineOf S)) (fun ha hb h => lift2_rank S ha hb h) _
    hpw' hid'
  rw [List.map_cons] at hl
  rw [hl, hchain, chainMoment_compl, add_comm]

include hsub in
theorem side1_le (T : V) (s : Slot) :
    wireMoment φ (wSide false T s) ≤ localMoment φ s + φ 506 := by
  rw [wireMoment_side, fseq_side1, show gInit (wSide false T s) = 0 from rfl,
    ← lift1_zero (lineOf T), ← List.map_cons, localMoment]
  have hpw := local_pairwise s
  have hid := local_chain_idem s
  generalize fseq (.inl (.aux s)) stage1 = L at hpw hid ⊢
  exact side1_chain φ hsub T L hpw hid

include hsub in
theorem side2_le (S : V) (s : Slot) :
    wireMoment φ (wSide true S s) ≤ localMoment φ s + φ 506 := by
  rw [wireMoment_side, fseq_side2, show gInit (wSide true S s) = 0 from rfl, fseq2_reg, localMoment]
  have hpw := local_pairwise s
  have hid := local_chain_idem s
  generalize fseq (.inl (.aux s)) stage1 = L at hpw hid ⊢
  exact side2_chain φ hsub S L hpw hid

/-! ### Data roles -/

omit hsub in
theorem pairwise_two {A B : LMat} (hAB : Le A B) (hA : A * A = A) (hB : B * B = B)
    {l : List LMat} (hl : l.Pairwise Le) (hv : ∀ x ∈ l, x = A ∨ x = B) :
    (A :: (l ++ [B])).Pairwise Le := by
  have hleA : ∀ y, y = A ∨ y = B → Le A y := by
    rintro y (rfl | rfl)
    · exact le_refl_of_idem hA
    · exact hAB
  have hleB : ∀ y, y = A ∨ y = B → Le y B := by
    rintro y (rfl | rfl)
    · exact hAB
    · exact le_refl_of_idem hB
  refine List.pairwise_cons.mpr ⟨fun y hy => hleA y ?_, ?_⟩
  · rcases List.mem_append.mp hy with hy | hy
    · exact hv y hy
    · exact Or.inr (List.mem_singleton.mp hy)
  · exact pw_app hl (List.pairwise_singleton _ _)
      (fun a ha b hb => by rw [List.mem_singleton.mp hb]; exact hleB a (hv a ha))

theorem two_idem {A B : LMat} (hA : A * A = A) (hB : B * B = B) {l : List LMat}
    (hv : ∀ x ∈ l, x = A ∨ x = B) : ∀ x ∈ A :: (l ++ [B]), x * x = x := by
  intro x hx
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | hx | rfl
  · exact hA
  · rcases hv x hx with rfl | rfl
    · exact hA
    · exact hB
  · exact hB

theorem lineOf_le_one (k : V) : Le (lineOf k) 1 := le_one _

theorem compl_lineOf_idem (k : V) : (1 - lineOf k) * (1 - lineOf k) = 1 - lineOf k :=
  compl_idem (lineOf_idem k)

include hsub in
/-- A data role through two lifted two-frame chains joined by the connectors. -/
theorem data_chain {f₁ : LMat → Mat 529} {f₂ : LMat → Mat 529}
    {a₁ b₁ a₂ b₂ : LMat} (l₁ l₂ : List LMat)
    (hab₁ : Le a₁ b₁) (hab₂ : Le a₂ b₂) (ha₁ : a₁ * a₁ = a₁) (hb₁ : b₁ * b₁ = b₁)
    (ha₂ : a₂ * a₂ = a₂) (hb₂ : b₂ * b₂ = b₂)
    (hv₁ : ∀ x ∈ l₁, x = a₁ ∨ x = b₁) (hv₂ : ∀ x ∈ l₂, x = a₂ ∨ x = b₂)
    (hp₁ : l₁.Pairwise Le) (hp₂ : l₂.Pairwise Le)
    (hf₁ : ∀ {a b : LMat}, a * a = a → b * b = b → Le a b → (f₁ b - f₁ a).rank = (b - a).rank)
    (hf₂ : ∀ {a b : LMat}, a * a = a → b * b = b → Le a b → (f₂ b - f₂ a).rank = (b - a).rank)
    (hi₁ : ∀ {a : LMat}, a * a = a → f₁ a * f₁ a = f₁ a)
    (hi₂ : ∀ {a : LMat}, a * a = a → f₂ a * f₂ a = f₂ a)
    (hm₁ : ∀ {a b : LMat}, Le a b → Le (f₁ a) (f₁ b)) (hm₂ : ∀ {a b : LMat}, Le a b → Le (f₂ a) (f₂ b))
    (hc₁ : Le (f₁ b₁) (f₂ a₂)) :
    chainMoment φ ((a₁ :: l₁).map f₁ ++ (l₂ ++ [b₂]).map f₂) ≤
      stepMoment φ a₁ b₁ + stepMoment φ (f₁ b₁) (f₂ a₂) + stepMoment φ a₂ b₂ := by
  have hle₁ : ∀ x ∈ a₁ :: l₁, Le x b₁ := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hab₁
    · rcases hv₁ x hx with rfl | rfl
      · exact hab₁
      · exact le_refl_of_idem hb₁
  have hge₂ : ∀ x ∈ l₂ ++ [b₂], Le a₂ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases hv₂ x hx with rfl | rfl
      · exact le_refl_of_idem ha₂
      · exact hab₂
    · rw [List.mem_singleton.mp hx]; exact hab₂
  have hidx₁ : ∀ x ∈ a₁ :: l₁, x * x = x := fun x hx =>
    two_idem ha₁ hb₁ hv₁ x (by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hx))
  have hidx₂ : ∀ x ∈ l₂ ++ [b₂], x * x = x := fun x hx =>
    two_idem ha₂ hb₂ hv₂ x (List.mem_cons_of_mem _ hx)
  have hne₁ : a₁ :: l₁ ≠ [] := List.cons_ne_nil _ _
  set X := (a₁ :: l₁).getLast hne₁
  have hX := hidx₁ X (List.getLast_mem hne₁)
  have hXb : Le X b₁ := hle₁ X (List.getLast_mem hne₁)
  obtain ⟨Y, rest, hY⟩ : ∃ Y rest, l₂ ++ [b₂] = Y :: rest := by
    cases h : l₂ ++ [b₂] with
    | nil => exact absurd h (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
    | cons Y rest => exact ⟨Y, rest, rfl⟩
  have hYm : Y ∈ l₂ ++ [b₂] := by rw [hY]; exact List.mem_cons_self
  have hYi := hidx₂ Y hYm
  have haY : Le a₂ Y := hge₂ Y hYm
  set Z := (a₁ :: l₁).map f₁
  have hsplit : Z = Z.dropLast ++ [f₁ X] := by
    conv_lhs => rw [← List.dropLast_append_getLast (show Z ≠ [] by simp [Z])]
    rw [List.getLast_map]
  have hlist : Z ++ (l₂ ++ [b₂]).map f₂ = Z.dropLast ++ f₁ X :: f₂ Y :: rest.map f₂ := by
    conv_lhs => rw [hsplit, hY]
    simp
  have hins1 := chainMoment_insert φ hsub Z.dropLast (rest.map f₂) (hi₁ hX) (hi₂ hYi) (hi₁ hb₁)
    (hm₁ hXb) (le_trans' hc₁ (hm₂ haY))
  have hins2 := chainMoment_insert φ hsub (Z.dropLast ++ [f₁ X]) (rest.map f₂) (hi₁ hb₁) (hi₂ hYi)
    (hi₂ ha₂) hc₁ (hm₂ haY)
  simp only [List.append_assoc, List.singleton_append] at hins2
  rw [hlist]
  refine (hins1.trans hins2).trans (le_of_eq ?_)
  have hfin : Z.dropLast ++ f₁ X :: f₁ b₁ :: f₂ a₂ :: f₂ Y :: rest.map f₂ =
      Z ++ f₁ b₁ :: f₂ a₂ :: (f₂ Y :: rest.map f₂) := by
    conv_rhs => rw [hsplit]
    simp
  have hZ1 : Z ++ [f₁ b₁] = (a₁ :: (l₁ ++ [b₁])).map f₁ := by simp [Z]
  have hZ2 : f₂ a₂ :: f₂ Y :: rest.map f₂ = (a₂ :: (l₂ ++ [b₂])).map f₂ := by
    rw [hY]; simp
  rw [hfin, chainMoment_append, hZ1, hZ2,
    chainMoment_lift φ hf₁ _ (pairwise_two hab₁ ha₁ hb₁ hp₁ hv₁) (two_idem ha₁ hb₁ hv₁),
    chainMoment_two φ hab₁ l₁ hv₁ (pairwise_two hab₁ ha₁ hb₁ hp₁ hv₁),
    chainMoment_lift φ hf₂ _ (pairwise_two hab₂ ha₂ hb₂ hp₂ hv₂) (two_idem ha₂ hb₂ hv₂),
    chainMoment_two φ hab₂ l₂ hv₂ (pairwise_two hab₂ ha₂ hb₂ hp₂ hv₂)]

theorem wireMoment_of_not_side {M : Type} [AddCommMonoid M] (φ : ℕ → M) {w : Wire}
    (h : w ∉ sideWires) : wireMoment φ w = chainMoment φ (gInit w :: fseq w allGates) := by
  rw [wireMoment, ite_eq_right h, add_zero]

include hsub in
theorem wX_le (S T : V) : wireMoment φ (wX S T) ≤ φ 22 + φ 484 + φ 22 := by
  have hnot : (wX S T) ∉ sideWires := fun h => by
    obtain ⟨_, _, _, h⟩ := mem_sideWires.mp h; simp [wX, wSide] at h
  rw [wireMoment_of_not_side φ hnot, fseq_wX, show gInit (wX S T) = lift1 (lineOf T) (lineOf S) from rfl,
    fseq2_reg]
  obtain ⟨hc1, hel1⟩ := chain1_x S.2
  obtain ⟨hc2, hel2⟩ := chain1_y T.2
  rw [nodeFrame_V] at hc1 hel1
  have hp1 := List.Pairwise.of_cons hc1
  have hp2 := pairwise_reflect (List.Pairwise.of_cons hc2)
  generalize fseq (.inl (.x S)) stage1 = xs at hp1 hel1 ⊢
  generalize fseq (.inl (.y T)) stage1 = ys at hp2 hel2 ⊢
  have hv2 : ∀ x ∈ (ys.map (1 - ·)).reverse, x = lineOf T ∨ x = 1 := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
    rcases hel2 g hg with rfl | rfl
    · exact Or.inr (sub_zero 1)
    · rw [hyper_V, sub_sub_cancel]; exact Or.inl rfl
  have hlist : lift1 (lineOf T) (lineOf S) :: (xs.map (lift1 (lineOf T)) ++
      (ys.map (1 - ·)).reverse.map (lift2 (lineOf S)) ++ [1]) =
      (lineOf S :: xs).map (lift1 (lineOf T)) ++
        ((ys.map (1 - ·)).reverse ++ [1]).map (lift2 (lineOf S)) := by
    rw [List.map_cons, List.map_append, List.map_singleton, lift2_one, List.cons_append,
      List.append_assoc]
  rw [hlist]
  refine (data_chain φ hsub xs _ (lineOf_le_one S) (lineOf_le_one T) (lineOf_idem S)
    (Matrix.one_mul 1) (lineOf_idem T) (Matrix.one_mul 1) hel1 hv2 hp1 hp2
    (fun ha hb h => lift1_rank T ha hb h) (fun ha hb h => lift2_rank S ha hb h)
    (fun ha => lift1_idem T ha) (fun ha => lift2_idem S ha)
    (fun h => le_lift1 (lineOf_idem T) h) (fun h => le_lift2 (lineOf_idem S) h)
    (connector_x (lineOf_idem T))).trans (le_of_eq ?_)
  rw [step_lineOf_one, step_connector_x, step_lineOf_one]

include hsub in
theorem wY_le (S T : V) : wireMoment φ (wY S T) ≤ φ 22 + φ 484 + φ 22 := by
  have hnot : (wY S T) ∉ sideWires := fun h => by
    obtain ⟨_, _, _, h⟩ := mem_sideWires.mp h; simp [wY, wSide] at h
  rw [wireMoment_of_not_side φ hnot, fseq_wY, show gInit (wY S T) = 0 from rfl, fseq2_reg]
  obtain ⟨hc1, hel1⟩ := chain1_y S.2
  obtain ⟨hc2, hel2⟩ := chain1_x T.2
  rw [nodeFrame_V] at hc2 hel2
  have hp1 := List.Pairwise.of_cons hc1
  have hp2 := pairwise_reflect (List.Pairwise.of_cons hc2)
  generalize fseq (.inl (.y S)) stage1 = ys at hp1 hel1 ⊢
  generalize fseq (.inl (.x T)) stage1 = xs at hp2 hel2 ⊢
  have hv1 : ∀ x ∈ ys, x = 0 ∨ x = 1 - lineOf S := by
    intro x hx
    rcases hel1 x hx with h | h
    · exact Or.inl h
    · rw [h, hyper_V]; exact Or.inr rfl
  have hv2 : ∀ x ∈ (xs.map (1 - ·)).reverse, x = 0 ∨ x = 1 - lineOf T := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
    rcases hel2 g hg with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (sub_self 1)
  have hU : 1 - uFrame S T = lift2 (lineOf S) (1 - lineOf T) := (lift2_compl _ _).symm
  have hlist : (0 : Mat 529) :: (ys.map (lift1 (lineOf T)) ++
      (xs.map (1 - ·)).reverse.map (lift2 (lineOf S)) ++ [1 - uFrame S T]) =
      ((0 : LMat) :: ys).map (lift1 (lineOf T)) ++
        ((xs.map (1 - ·)).reverse ++ [1 - lineOf T]).map (lift2 (lineOf S)) := by
    rw [List.map_cons, List.map_append, List.map_singleton, ← hU, lift1_zero, List.cons_append,
      List.append_assoc]
  rw [hlist]
  refine (data_chain φ hsub ys _ (zero_le (1 - lineOf S)) (zero_le (1 - lineOf T))
    (Matrix.zero_mul 0) (compl_lineOf_idem S) (Matrix.zero_mul 0) (compl_lineOf_idem T) hv1 hv2 hp1 hp2
    (fun ha hb h => lift1_rank T ha hb h) (fun ha hb h => lift2_rank S ha hb h)
    (fun ha => lift1_idem T ha) (fun ha => lift2_idem S ha)
    (fun h => le_lift1 (lineOf_idem T) h) (fun h => le_lift2 (lineOf_idem S) h)
    (connector_y (lineOf_idem S))).trans (le_of_eq ?_)
  rw [step_zero_compl, step_connector_y, step_zero_compl]

/-! ### Temporaries -/

include h0 hmono in
theorem centre_le (b : Bool) (k : V) (c : Fin 23) : wireMoment φ (wCentre b k c) ≤ φ 22 := by
  have hnot : (wCentre b k c) ∉ sideWires := fun h => by
    obtain ⟨_, _, _, h⟩ := mem_sideWires.mp h; simp [wCentre, wSide] at h
  have hst := starFrame_idem c.2
  rw [wireMoment_of_not_side φ hnot]
  cases b
  · rw [fseq_centre1, fseq1_tmp, show gInit (wCentre false k c) = lift1 (lineOf k) (starFrame c)
      from rfl, List.map_cons, List.map_map]
    refine (chainMoment_temp φ h0 _ (lift1 (lineOf k) 0) _).trans (hmono ?_)
    rw [lift1_rank k (Matrix.zero_mul 0) hst (zero_le _), sub_zero]
    exact rank_starFrame_le c.2
  · rw [fseq_centre2, fseq2_tmp, show gInit (wCentre true k c) = lift2 (lineOf k) (1 - starFrame c)
      from rfl, List.map_cons, List.map_map]
    refine (chainMoment_temp φ h0 _ (lift2 (lineOf k) 1) _).trans (hmono ?_)
    rw [rank_sub_comm, lift2_rank k (compl_idem hst) (Matrix.one_mul 1) (le_one _), sub_sub_cancel]
    exact rank_starFrame_le c.2

include h0 in
theorem corr_le (S T : V) : wireMoment φ (wCorr S T) ≤ φ 1 := by
  have hnot : (wCorr S T) ∉ sideWires := fun h => by
    obtain ⟨_, _, _, h⟩ := mem_sideWires.mp h; simp [wCorr, wSide] at h
  rw [wireMoment_of_not_side φ hnot, fseq_wCorr, show gInit (wCorr S T) = 1 from rfl]
  have := chainMoment_temp φ h0 (1 : Mat 529) (1 - uFrame S T) [0]
  rw [sub_sub_cancel, rank_uFrame] at this
  exact this

theorem junk_le : wireMoment φ wJunk ≤ 0 := by
  have hnot : wJunk ∉ sideWires := fun h => by
    obtain ⟨_, _, _, h⟩ := mem_sideWires.mp h; simp [wJunk, wSide] at h
  rw [wireMoment_of_not_side φ hnot, fseq_wJunk]
  rfl

/-! ### The node -/

/-- The bound of each wire's moment, by kind. -/
def momentBoundOf {A B C D E F : Type} (x : ℝ) (g : C → ℝ) (y z : ℝ) :
    (A ⊕ B ⊕ C) ⊕ (D ⊕ E ⊕ F) → ℝ
  | .inl (.inl _) => x
  | .inl (.inr (.inl _)) => x
  | .inl (.inr (.inr c)) => g c
  | .inr (.inl _) => y
  | .inr (.inr (.inl _)) => z
  | .inr (.inr (.inr _)) => 0

theorem sum_momentBoundOf {A B C D E F : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype E] [Fintype F] (x : ℝ) (g : C → ℝ) (y z : ℝ) :
    ∑ w : (A ⊕ B ⊕ C) ⊕ (D ⊕ E ⊕ F), momentBoundOf x g y z w =
      Fintype.card A * x + Fintype.card B * x + ∑ c, g c + Fintype.card D * y +
        Fintype.card E * z := by
  simp only [Fintype.sum_sum_type, momentBoundOf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem card_V1771 : Fintype.card V = 1771 := by rw [card_V]; rfl

theorem sum_sides (g : Slot → ℝ) :
    ∑ x : Bool × V × Slot, g x.2.2 = 2 * (1771 * ∑ s, g s) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, card_V1771,
    Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

include h0 hmono hsub in
/-- **The moments of the node's moves.** For a nonnegative, monotone, subadditive `φ`, the
moment of the node's moves is at most the moment of the stage-2 histogram, with each side slot's
local moves left as `localMoment φ s`. -/
theorem node_moment_le :
    edgeMoment φ framedNode ≤ (1771 * 1771 : ℝ) * (4 * φ 22 + 2 * φ 484 + φ 1) +
      2 * 1771 * (23 * φ 22 + ∑ s : Slot, (localMoment φ s + φ 506)) := by
  rw [edgeMoment_node]
  let bound : Wire → ℝ := momentBoundOf (A := V × V) (B := V × V) (C := Bool × V × Slot)
    (D := Bool × V × Fin 23) (E := V × V) (F := Unit) (φ 22 + φ 484 + φ 22)
    (fun x => localMoment φ x.2.2 + φ 506) (φ 22) (φ 1)
  refine (Finset.sum_le_sum (g := bound) fun w _ => ?_).trans (le_of_eq ?_)
  · rcases w with ((⟨S, T⟩ | ⟨S, T⟩ | ⟨b, k, s⟩) | (⟨b, k, c⟩ | ⟨S, T⟩ | ⟨⟩))
    · exact wX_le φ hsub S T
    · exact wY_le φ hsub S T
    · cases b
      · exact side1_le φ hsub k s
      · exact side2_le φ hsub k s
    · exact centre_le φ h0 hmono b k c
    · exact corr_le φ h0 S T
    · exact junk_le φ
  · rw [sum_momentBoundOf, sum_sides (fun s => localMoment φ s + φ 506)]
    have hL : (leafCount : ℝ) = 1771 := by exact_mod_cast (show leafCount = 1771 from rfl)
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    push_cast
    rw [hL]
    ring

end
end IntegerMultBounds.MathlibTM2.M8.Global
