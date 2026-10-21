module

public import IntegerMultBounds.MathlibTM2.M8.Rev97Machine
public import IntegerMultBounds.MathlibTM2.M8.Stage2Link
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Contract

/-!
# The block children of the stage-2 PR97 node

A control's block children are its edge programs with interchanges, one child of rank `r` for a
program of `r` interchanges (`childRanks`). For the stage-2 list of a framed list they are the
ranks of its frame changes (`Rev.programs_revPhysOf`), so their moments are the moments of its
moves (`sum_childRanks`). `ranks97`, the children of `control97` (the control of `rev97` and
`rev97m`), therefore have the two moment gaps of the stage-2 histogram (`moment₁_ranks97`,
`momentτ_ranks97`).

Every child is smaller than the node: no move of the PR97 node has full rank (`ranks97_lt`).
The data and temporary wires move at most `528` ranks in all (their moment bounds at `φ r = r`).
The moves of a side slot are its local moves, of rank at most `23`, and one exterior move, the
sink `lift1 A → 1` or the source `0 → lift2 B`, of rank `529 - rank A`. The local chain of every
slot ends at a nonzero frame `A`, since no slot has a local move of rank `23`
(`localMoment_top`, from the local-step histogram).

`rev97_closed` and `rev97_contract`: with the leaf bound below `529` and the node recurrence
over `ranks97` on `W` roles, the reversed family costs at most
`C/(1-q₁) n + C/(1-q_τ) n^τ* L`, at `τ* = 1 - 969/10⁷`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8

noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Global

/-- The ranks of a control's block children: the interchange counts of its edge programs that
have interchanges. -/
def childRanks {ι : Type} {m : ℕ} (s : List (Step ι (FieldProgram m))) : List ℕ :=
  ((Step.programs s).map AffineFieldProgram.interchanges).filter (0 < ·)

namespace Rev

variable {ι : Type} {d : ℕ}

/-- The interchange counts of the stage-2 list are the ranks of the frame changes. -/
theorem programs_revPhysOf {G G' : Mat d} (h : G * G' = 1) (h' : G' * G = 1) :
    ∀ L : List (FStep ι d), (Step.programs (revPhysOf G G' L)).map AffineFieldProgram.interchanges =
      (edgeMats L).map Matrix.rank
  | [] => rfl
  | s :: rest => by
    have ih := programs_revPhysOf h h' rest
    cases s <;>
      simpa [revPhysOf, Step.programs, edgeMats, revStep, revProgram_interchanges,
        rank_conj h h'] using ih

end Rev

namespace Rev97Ranks

variable {ι : Type} {d : ℕ}

theorem edgeMoment_eq_sum {M : Type} [AddCommMonoid M] (φ : ℕ → M) :
    ∀ L : List (FStep ι d), edgeMoment φ L = ((Rev.edgeMats L).map fun U => φ U.rank).sum
  | [] => rfl
  | s :: rest => by
    cases s <;> simp [edgeMoment, Rev.edgeMats, edgeMoment_eq_sum φ rest]

theorem sum_map_filter_pos {M : Type} [AddCommMonoid M] (φ : ℕ → M) (hz : φ 0 = 0) :
    ∀ l : List ℕ, ((l.filter (0 < ·)).map φ).sum = (l.map φ).sum
  | [] => rfl
  | r :: l => by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp [hz, sum_map_filter_pos φ hz l]
    · simp [hr, sum_map_filter_pos φ hz l]

/-- The moments of the block children of a stage-2 list are the moments of its moves. -/
theorem sum_childRanks {M : Type} [AddCommMonoid M] (φ : ℕ → M) (hz : φ 0 = 0) {G G' : Mat d}
    (h : G * G' = 1) (h' : G' * G = 1) (L : List (FStep ι d)) :
    ((childRanks (Rev.revPhysOf G G' L)).map φ).sum = edgeMoment φ L := by
  rw [childRanks, sum_map_filter_pos φ hz, Rev.programs_revPhysOf h h', edgeMoment_eq_sum,
    List.map_map]
  rfl

theorem mem_childRanks {G G' : Mat d} (h : G * G' = 1) (h' : G' * G = 1) {L : List (FStep ι d)}
    {r : ℕ} (hr : r ∈ childRanks (Rev.revPhysOf G G' L)) : 0 < r ∧ ∃ U ∈ Rev.edgeMats L, U.rank = r := by
  rw [childRanks, List.mem_filter, Rev.programs_revPhysOf h h', List.mem_map] at hr
  obtain ⟨⟨U, hU, rfl⟩, hpos⟩ := hr
  exact ⟨by simpa using hpos, U, hU, rfl⟩

/-! ### Moments in `ℕ` -/

/-- One for a move of full rank. -/
def full (r : ℕ) : ℕ := if 529 ≤ r then 1 else 0

theorem full_le (r : ℕ) : 529 * full r ≤ r := by
  unfold full; split_ifs <;> omega

theorem stepMoment_full {A B : Mat d} (h : (A - B).rank < 529) : stepMoment full A B = 0 := by
  rw [stepMoment_eq]
  split_ifs
  · rfl
  · unfold full; split_ifs <;> omega

theorem chainMoment_scale_le {φ ψ : ℕ → ℕ} {c : ℕ} (h : ∀ r, c * φ r ≤ ψ r) :
    ∀ l : List (Mat d), c * chainMoment φ l ≤ chainMoment ψ l
  | [] => by simp [chainMoment]
  | [_] => by simp [chainMoment]
  | a :: b :: l => by
    rw [chainMoment_cons_cons, chainMoment_cons_cons, mul_add]
    refine Nat.add_le_add ?_ (chainMoment_scale_le h (b :: l))
    rw [stepMoment, stepMoment]
    split_ifs
    · simp
    · exact h _

theorem chainMoment_cast (φ : ℕ → ℕ) : ∀ l : List (Mat d),
    chainMoment (fun r => (φ r : ℝ)) l = ((chainMoment φ l : ℕ) : ℝ)
  | [] => by simp [chainMoment]
  | [_] => by simp [chainMoment]
  | a :: b :: l => by
    rw [chainMoment_cons_cons, chainMoment_cons_cons, chainMoment_cast φ (b :: l), Nat.cast_add,
      stepMoment, stepMoment]
    split_ifs <;> simp

theorem chainMoment_nonneg {φ : ℕ → ℝ} (h : ∀ r, 0 ≤ φ r) : ∀ l : List (Mat d), 0 ≤ chainMoment φ l
  | [] => by simp [chainMoment]
  | [_] => by simp [chainMoment]
  | a :: b :: l => by
    rw [chainMoment_cons_cons]
    refine add_nonneg ?_ (chainMoment_nonneg h (b :: l))
    rw [stepMoment]
    split_ifs
    · exact le_rfl
    · exact h _

/-- A local chain has no move of full rank. -/
theorem chainMoment_local_full : ∀ l : List LMat, chainMoment full l = 0
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    rw [chainMoment_cons_cons, chainMoment_local_full (b :: l), add_zero]
    exact stepMoment_full (lt_of_le_of_lt (Matrix.rank_le_width _) (by norm_num))

theorem wireMoment_scale_le {φ ψ : ℕ → ℕ} {c : ℕ} (h : ∀ r, c * φ r ≤ ψ r) (w : Wire) :
    c * wireMoment φ w ≤ wireMoment ψ w := by
  unfold wireMoment
  rw [mul_add]
  refine Nat.add_le_add (chainMoment_scale_le h _) ?_
  split_ifs
  · rw [stepMoment, stepMoment]
    split_ifs
    · simp
    · exact h _
  · simp

theorem wireMoment_cast (φ : ℕ → ℕ) (w : Wire) :
    wireMoment (fun r => (φ r : ℝ)) w = ((wireMoment φ w : ℕ) : ℝ) := by
  unfold wireMoment
  rw [chainMoment_cast, Nat.cast_add]
  congr 1
  split_ifs
  · rw [stepMoment, stepMoment]
    split_ifs <;> simp
  · simp

/-- A wire that moves at most `528` ranks in all has no move of full rank. -/
theorem wireMoment_full_of_le {w : Wire} (h : wireMoment (fun r : ℕ => (r : ℝ)) w ≤ 528) :
    wireMoment full w = 0 := by
  have h1 := wireMoment_scale_le (ψ := fun r => r) full_le w
  have hc : wireMoment (fun r : ℕ => (r : ℝ)) w = ((wireMoment (fun r : ℕ => r) w : ℕ) : ℝ) :=
    wireMoment_cast (fun r => r) w
  rw [hc] at h
  have h2 : wireMoment (fun r : ℕ => r) w ≤ 528 := by exact_mod_cast h
  omega

/-! ### The side slots -/

/-- One for a local move of rank `23`. -/
def top (r : ℕ) : ℝ := if r = 23 then 1 else 0

theorem top_nonneg (r : ℕ) : 0 ≤ top r := by
  unfold top; split_ifs <;> norm_num

/-- No side slot has a local move of rank `23`. -/
theorem localMoment_top (s : Slot) : localMoment top s = 0 := by
  have h := sum_localMoment_eq top (by simp [top])
  have hrhs : ∑ r ∈ Finset.range 24, (Local.localSteps.getD r 0 : ℝ) * top r = 0 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Local.localSteps, List.getD_cons_succ,
      List.getD_cons_zero, top]
    norm_num
  rw [hrhs] at h
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => chainMoment_nonneg top_nonneg _)).mp h s
    (Finset.mem_univ s)

theorem stepMoment_top_zero_one : stepMoment top (0 : LMat) 1 = 1 := by
  rw [stepMoment_eq]
  simp only [zero_ne_one, ↓reduceIte, zero_sub, Global.rank_neg, Matrix.rank_one, Fintype.card_fin,
    top]

/-- The local chain of every side slot ends at a nonzero frame. -/
theorem local_last (s : Slot) :
    ∃ l₀ A, (0 : LMat) :: fseq (.inl (.aux s)) stage1 = l₀ ++ [A] ∧ A ≠ 0 := by
  have h := localMoment_top s
  unfold localMoment at h
  generalize fseq (.inl (.aux s)) stage1 = L at h ⊢
  obtain ⟨l₀, A, hsplit⟩ : ∃ l₀ A, (0 : LMat) :: L = l₀ ++ [A] :=
    ⟨_, _, (List.dropLast_append_getLast (List.cons_ne_nil _ _)).symm⟩
  refine ⟨l₀, A, hsplit, fun hA => ?_⟩
  rw [← List.cons_append, hsplit, List.append_assoc, List.singleton_append, chainMoment_snoc, hA,
    stepMoment_top_zero_one] at h
  have := chainMoment_nonneg top_nonneg (l₀ ++ [0])
  linarith

theorem side1_full (T : V) (s : Slot) : wireMoment full (wSide false T s) = 0 := by
  rw [wireMoment_side, fseq_side1, show gInit (wSide false T s) = 0 from rfl,
    ← lift1_zero (lineOf T), ← List.map_cons]
  obtain ⟨l₀, A, hsplit, hA0⟩ := local_last s
  have hpw := local_pairwise s
  have hid := local_chain_idem s
  generalize fseq (.inl (.aux s)) stage1 = L at hsplit hpw hid ⊢
  have hsub : ((0 : LMat) :: L).Sublist ((0 : LMat) :: (L ++ [1])) :=
    (List.sublist_append_left L [1]).cons_cons 0
  have hAi : A * A = A := hid A (hsub.subset (by rw [hsplit]; simp))
  have hZ : ((0 : LMat) :: L).map (lift1 (lineOf T)) ++ [1] =
      l₀.map (lift1 (lineOf T)) ++ [lift1 (lineOf T) A, 1] := by
    rw [hsplit]; simp
  have hZ' : l₀.map (lift1 (lineOf T)) ++ [lift1 (lineOf T) A] =
      ((0 : LMat) :: L).map (lift1 (lineOf T)) := by
    rw [hsplit]; simp
  rw [hZ, chainMoment_snoc, hZ', chainMoment_lift full (fun ha hb h => lift1_rank T ha hb h) _
    (hpw.sublist hsub) (fun f hf => hid f (hsub.subset hf)), chainMoment_local_full, zero_add]
  have hX : (lift1 (lineOf T) A).rank = A.rank := by
    rw [lift1, kron_rank hAi (lineOf_idem T), rank_lineOf, mul_one]
  have hsum := rank_sub_of_le (lift1_idem T hAi) (Matrix.one_mul (1 : Mat 529))
    (Global.le_one (lift1 (lineOf T) A))
  rw [rank_one529, hX] at hsum
  have hpos : A.rank ≠ 0 := fun h => hA0 (eq_zero_of_rank_eq_zero h)
  exact stepMoment_full (by rw [rank_sub_comm]; omega)

/-- Stage two along a side slot, for any local chain `0, L, 1` without a local move of rank `23`:
no move of full rank. -/
theorem side2_chain_full (S : V) (L : List LMat) (hpw : ((0 : LMat) :: (L ++ [1])).Pairwise Le)
    (hid : ∀ f ∈ (0 : LMat) :: (L ++ [1]), f * f = f)
    (htop : chainMoment top ((0 : LMat) :: (L ++ [1])) = 0) :
    chainMoment full (((0 : Mat 529) :: ((L.map (1 - ·)).reverse).map (lift2 (lineOf S))) ++ [1]) =
      0 := by
  have hchain : (0 : LMat) :: ((L.map (1 - ·)).reverse ++ [1]) =
      (((0 : LMat) :: (L ++ [1])).map (1 - ·)).reverse := by
    rw [List.map_cons, List.map_append, List.reverse_cons, List.reverse_append]
    simp
  have hpw' : ((0 : LMat) :: ((L.map (1 - ·)).reverse ++ [1])).Pairwise Le := by
    rw [hchain]; exact pairwise_reflect hpw
  have hid' : ∀ f ∈ (0 : LMat) :: ((L.map (1 - ·)).reverse ++ [1]), f * f = f := by
    rw [hchain]
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hf)
    exact compl_idem (hid g hg)
  rw [← chainMoment_compl, ← hchain] at htop
  have hlist : ((0 : Mat 529) :: ((L.map (1 - ·)).reverse).map (lift2 (lineOf S))) ++ [1] =
      (0 : Mat 529) :: ((L.map (1 - ·)).reverse ++ [1]).map (lift2 (lineOf S)) := by
    simp [lift2_one]
  rw [hlist]
  obtain ⟨B, rest, hB⟩ : ∃ B rest, (L.map (1 - ·)).reverse ++ [1] = B :: rest := by
    cases h : (L.map (1 - ·)).reverse ++ [1] with
    | nil => simp at h
    | cons B rest => exact ⟨B, rest, rfl⟩
  rw [hB] at hpw' hid' htop ⊢
  rw [List.map_cons, chainMoment_cons_cons, ← List.map_cons,
    chainMoment_lift full (fun ha hb h => lift2_rank S ha hb h) _ hpw'.of_cons
      (fun f hf => hid' f (List.mem_cons_of_mem _ hf)), chainMoment_local_full, add_zero]
  rw [chainMoment_cons_cons] at htop
  have hB1 : B ≠ 1 := by
    rintro rfl
    rw [stepMoment_top_zero_one] at htop
    have := chainMoment_nonneg top_nonneg ((1 : LMat) :: rest)
    linarith
  have hBi : B * B = B := hid' B (by simp)
  have hr0 : (lift2 (lineOf S) 0).rank = 506 := by
    rw [lift2_zero, kron_rank (compl_idem (lineOf_idem S)) (Matrix.one_mul (1 : LMat)),
      rank_compl_lineOf, Matrix.rank_one, Fintype.card_fin]
  have hsum := rank_sub_of_le (lift2_idem S (Matrix.zero_mul (0 : LMat))) (lift2_idem S hBi)
    (le_lift2 (lineOf_idem S) (Global.zero_le B))
  rw [lift2_rank S (Matrix.zero_mul 0) hBi (Global.zero_le B), sub_zero, hr0] at hsum
  have hB23 := rank_sub_of_le hBi (Matrix.one_mul (1 : LMat)) (Global.le_one B)
  rw [Matrix.rank_one, Fintype.card_fin] at hB23
  have hne : (1 - B).rank ≠ 0 := fun h => hB1 (sub_eq_zero.mp (eq_zero_of_rank_eq_zero h)).symm
  exact stepMoment_full (by rw [zero_sub, Global.rank_neg]; omega)

theorem side2_full (S : V) (s : Slot) : wireMoment full (wSide true S s) = 0 := by
  rw [wireMoment_side, fseq_side2, show gInit (wSide true S s) = 0 from rfl, fseq2_reg]
  have htop := localMoment_top s
  unfold localMoment at htop
  exact side2_chain_full S _ (local_pairwise s) (local_chain_idem s) htop

/-! ### No move of full rank -/

theorem cast_add_le (a b : ℕ) : (((a + b : ℕ) : ℝ)) ≤ (a : ℝ) + b := by push_cast; rfl

theorem wireMoment_full (w : Wire) : wireMoment full w = 0 := by
  have h0 : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) := fun n => Nat.cast_nonneg n
  have hmono : Monotone (fun r : ℕ => (r : ℝ)) := Nat.mono_cast
  rcases w with ((⟨S, T⟩ | ⟨S, T⟩ | ⟨b, k, s⟩) | (⟨b, k, c⟩ | ⟨S, T⟩ | ⟨⟩))
  · exact wireMoment_full_of_le ((wX_le _ cast_add_le S T).trans (by norm_num))
  · exact wireMoment_full_of_le ((wY_le _ cast_add_le S T).trans (by norm_num))
  · cases b
    · exact side1_full k s
    · exact side2_full k s
  · exact wireMoment_full_of_le ((centre_le _ h0 hmono b k c).trans (by norm_num))
  · exact wireMoment_full_of_le ((corr_le _ h0 S T).trans (by norm_num))
  · exact wireMoment_full_of_le ((junk_le _).trans (by norm_num))

/-- **No move of the PR97 node has full rank.** -/
theorem rank_lt {U : Mat 529} (hU : U ∈ Rev.edgeMats framedNode) : U.rank < 529 := by
  have h : edgeMoment full framedNode = 0 := by
    rw [edgeMoment_node]
    exact Finset.sum_eq_zero fun w _ => wireMoment_full w
  rw [edgeMoment_eq_sum] at h
  have hU' := List.sum_eq_zero_iff.mp h _ (List.mem_map.mpr ⟨U, hU, rfl⟩)
  unfold full at hU'
  split_ifs at hU' with hr
  omega

end Rev97Ranks

open Rev97Ranks Stage2Moments
open Global.Branching97 (roleCount)

/-! ### The children of the stage-2 node -/

/-- The ranks of the block children of the stage-2 PR97 node. -/
def ranks97 : List ℕ := childRanks control97

theorem rev97_control : rev97.control = control97 := rfl

theorem rev97m_control : rev97m.control = control97 := rfl

theorem ranks97_pos {r : ℕ} (hr : r ∈ ranks97) : 1 ≤ r :=
  (mem_childRanks basis97_inv basis97_inv' hr).1

theorem ranks97_lt {r : ℕ} (hr : r ∈ ranks97) : r < 529 := by
  obtain ⟨-, U, hU, rfl⟩ := mem_childRanks basis97_inv basis97_inv' hr
  exact rank_lt hU

theorem sum_ranks97 (φ : ℕ → ℝ) (hz : φ 0 = 0) : (ranks97.map φ).sum = edgeMoment φ framedNode :=
  sum_childRanks φ hz basis97_inv basis97_inv' framedNode

/-- The linear moment gap of the children. -/
theorem moment₁_ranks97 :
    (ranks97.map fun r : ℕ => (1 / ((roleCount : ℕ) : ℝ)) * ((r : ℝ) / ((529 : ℕ) : ℝ))).sum ≤ q₁ := by
  have hf : (ranks97.map fun r : ℕ => (1 / ((roleCount : ℕ) : ℝ)) * ((r : ℝ) / ((529 : ℕ) : ℝ))) =
      ranks97.map fun r : ℕ => ((r : ℝ) / 529) ^ (1 : ℝ) / roleCount :=
    List.map_congr_left fun r _ => by rw [Real.rpow_one]; push_cast; ring
  rw [hf, sum_ranks97 _ (by simp)]
  exact linear_premise

/-- The `τ*`-moment gap of the children, at `τ* = 1 - 969/10⁷`. -/
theorem momentτ_ranks97 :
    (ranks97.map fun r : ℕ =>
      (1 / ((roleCount : ℕ) : ℝ)) * ((r : ℝ) / ((529 : ℕ) : ℝ)) ^ (1 - (saving : ℝ))).sum ≤ qτ := by
  have hτ : (1 - (saving : ℝ)) ≠ 0 := by norm_num [saving]
  have hf : (ranks97.map fun r : ℕ =>
      (1 / ((roleCount : ℕ) : ℝ)) * ((r : ℝ) / ((529 : ℕ) : ℝ)) ^ (1 - (saving : ℝ))) =
      ranks97.map fun r : ℕ => ((r : ℝ) / 529) ^ (1 - (saving : ℝ)) / roleCount :=
    List.map_congr_left fun r _ => by push_cast; ring
  rw [hf, sum_ranks97 _ (by rw [Nat.cast_zero, zero_div, Real.zero_rpow hτ, zero_div])]
  exact tau_premise.le

/-! ### The stopped bound of the reversed family -/

/-- **The stage-2 PR97 family closes.** A cost that obeys the leaf bound below `529` atoms and
the node recurrence over the children `ranks97` on `W` roles is at most
`C/(1-q₁) n + C/(1-q_τ) n^τ* L`. -/
theorem rev97_closed (T : ℕ → ℝ) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hleaf : ∀ n, 1 ≤ n → n < 529 → T n ≤ C * L)
    (hnode : ∀ n, 529 ≤ n →
      T n ≤ (ranks97.map fun r : ℕ => T (r * (n / 529)) / roleCount).sum + C * n + C * L) :
    ∀ n, 1 ≤ n →
      T n ≤ C / (1 - q₁) * n + C / (1 - qτ) * ((n : ℝ) ^ (1 - (saving : ℝ)) * L) :=
  RevMachine.family_closed 529 roleCount (by norm_num) (by norm_num [roleCount]) ranks97
    (fun _ => ranks97_pos) (fun _ => ranks97_lt) T (by norm_num [saving]) hC hL
    (by exact_mod_cast q₁_lt_one) (by exact_mod_cast qτ_nonneg) (by exact_mod_cast qτ_lt_one)
    hleaf hnode moment₁_ranks97 momentτ_ranks97

/-- **The contract of the stage-2 PR97 family.** A contract monotone in its budget that holds
below `529` atoms at `C L` and passes from the block children `ranks97` to the node holds for
every atom count at `C/(1-q₁) n + C/(1-q_τ) n^τ* L`. -/
theorem rev97_contract (P : ℕ → ℝ → Prop) (mono : ∀ n B B', P n B → B ≤ B' → P n B')
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (leaf : ∀ n, 1 ≤ n → n < 529 → P n (C * L))
    (node : ∀ n, 529 ≤ n → ∀ T : ℕ → ℝ, (∀ r ∈ ranks97, P (r * (n / 529)) (T (r * (n / 529)))) →
      P n ((ranks97.map fun r : ℕ => T (r * (n / 529)) / roleCount).sum + C * n + C * L)) :
    ∀ n, 1 ≤ n →
      P n (C / (1 - q₁) * n + C / (1 - qτ) * ((n : ℝ) ^ (1 - (saving : ℝ)) * L)) :=
  RevMachine.family_contract P mono 529 roleCount (by norm_num) (by norm_num [roleCount]) ranks97
    (fun _ => ranks97_pos) (fun _ => ranks97_lt) (by norm_num [saving]) hC hL
    (by exact_mod_cast q₁_lt_one) (by exact_mod_cast qτ_nonneg) (by exact_mod_cast qτ_lt_one)
    moment₁_ranks97 momentτ_ranks97 leaf node

end

end IntegerMultBounds.MathlibTM2.M8
