module

public import IntegerMultBounds.NLogN.SchurLURounded

/-! Backward stability of rounded elimination. Each multiplier and each
updated entry is rounded within `η`. A stage keeps dominance with margin
reduced by `2η(n+m)` and row mass increased by `η(n+m)`, where `n` bounds the
active set and `m` the row mass, and the computed unit-lower and pivot-row
factors multiply back to the matrix entrywise within `η(n+m)` per stage. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset
variable {ι : Type*} [DecidableEq ι]

/-- One rounded elimination step: rounded multiplier, rounded update. -/
noncomputable def relim (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (A : Matrix ι ι ℝ) (k : ι) : Matrix ι ι ℝ :=
  fun i j => rd (A i j-mul (A i k) (A k k)*A k j)

/-- Rounded multipliers, recorded in list order. -/
noncomputable def luLr (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (A : Matrix ι ι ℝ) (S : Finset ι) : List ι → Matrix ι ι ℝ
  | [] => fun i j => if i∈S ∧ i=j then 1 else 0
  | k::ks => fun i j => if k∈S then
      (if j=k then (if i=k then 1 else if i∈S then mul (A i k) (A k k) else 0)
      else luLr rd mul (relim rd mul A k) (S.erase k) ks i j)
    else luLr rd mul A S ks i j

/-- Pivot rows of the rounded stages. -/
noncomputable def luUr (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (A : Matrix ι ι ℝ) (S : Finset ι) : List ι → Matrix ι ι ℝ
  | [] => fun i j => if i∈S ∧ j∈S then A i j else 0
  | k::ks => fun i j => if k∈S then
      (if i=k then (if j∈S then A k j else 0)
      else luUr rd mul (relim rd mul A k) (S.erase k) ks i j)
    else luUr rd mul A S ks i j

/-- Stage invariant: margin `μ` and row mass at most `m` on the active set. -/
def StageInv (A : Matrix ι ι ℝ) (S : Finset ι) (μ m : ℝ) : Prop :=
  DominatesOn A S μ ∧ ∀ i∈S, ∑ j∈S, |A i j|≤m

variable (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η)
  (hmul : ∀ a b, |mul a b-a/b|≤η)
include hrd hmul

omit [DecidableEq ι] in
theorem relim_close (A : Matrix ι ι ℝ) (k i j : ι) :
    |relim rd mul A k i j-eliminate A k i j|≤η+η*|A k j| := by
  unfold relim eliminate
  have h1 := hrd (A i j-mul (A i k) (A k k)*A k j)
  have h2 := hmul (A i k) (A k k)
  have h3 : |(mul (A i k) (A k k)-A i k/A k k)*A k j|≤η*|A k j| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  calc |rd (A i j-mul (A i k) (A k k)*A k j)-(A i j-A i k/A k k*A k j)|
      =|(rd (A i j-mul (A i k) (A k k)*A k j)-(A i j-mul (A i k) (A k k)*A k j))-
          (mul (A i k) (A k k)-A i k/A k k)*A k j| := by ring_nf
    _≤_ := (abs_sub _ _).trans (add_le_add h1 h3)

/-- A rounded step keeps the invariant with explicit losses. -/
theorem relim_inv (A : Matrix ι ι ℝ) (S : Finset ι) (μ m n : ℝ) (hμ : 0<μ)
    (hcard : (S.card : ℝ)≤n) (hA : StageInv A S μ m) (k : ι) (hk : k∈S) :
    StageInv (relim rd mul A k) (S.erase k) (μ-2*η*(n+m)) (m+η*(n+m)) := by
  obtain ⟨hdom, hmass⟩ := hA
  have hdiag := pivot_pos A S μ hμ hdom k hk
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hrow (i : ι) : ∑ j∈S.erase k, |relim rd mul A k i j-eliminate A k i j|≤η*(n+m) := by
    calc ∑ j∈S.erase k, |relim rd mul A k i j-eliminate A k i j|
        ≤∑ j∈S.erase k, (η+η*|A k j|) := sum_le_sum fun j _ => relim_close rd mul η hrd hmul A k i j
      _=((S.erase k).card : ℝ)*η+η*∑ j∈S.erase k, |A k j| := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
      _≤n*η+η*m := by
          have hc : ((S.erase k).card : ℝ)≤n := by
            have := card_erase_le (s := S) (a := k)
            have : ((S.erase k).card : ℝ)≤S.card := by exact_mod_cast this
            linarith
          have hm : ∑ j∈S.erase k, |A k j|≤m :=
            (sum_le_sum_of_subset_of_nonneg (erase_subset k S) fun _ _ _ => abs_nonneg _).trans
              (hmass k hk)
          gcongr
      _=η*(n+m) := by ring
  have hQ : 0≤η*(n+m) := le_trans (sum_nonneg fun _ _ => abs_nonneg _) (hrow k)
  constructor
  · intro i hi
    have hiS := mem_of_mem_erase hi
    have hik := ne_of_mem_erase hi
    have hgap := eliminate_gap A S μ hμ hdom k i hk hiS hik
    rw [erase_right_comm] at hgap
    have hsplit := sum_erase_add (S.erase k) (fun j => |relim rd mul A k i j-eliminate A k i j|) hi
    have hD := hrow i
    have hoff : ∑ j∈(S.erase k).erase i, |relim rd mul A k i j|≤
        ∑ j∈(S.erase k).erase i, |eliminate A k i j|+
          ∑ j∈(S.erase k).erase i, |relim rd mul A k i j-eliminate A k i j| := by
      rw [←sum_add_distrib]
      refine sum_le_sum fun j _ => ?_
      have := abs_add_le (eliminate A k i j) (relim rd mul A k i j-eliminate A k i j)
      rw [add_sub_cancel] at this
      linarith
    have hdiagE := neg_abs_le (relim rd mul A k i i-eliminate A k i i)
    linarith
  · intro i hi
    have hD := hrow i
    have hdomk := hdom k hk
    have hm := eliminate_mass A S k i hk hdiag (by linarith)
    have hsum : ∑ j∈S.erase k, |relim rd mul A k i j|≤
        ∑ j∈S.erase k, |eliminate A k i j|+∑ j∈S.erase k, |relim rd mul A k i j-eliminate A k i j| := by
      rw [←sum_add_distrib]
      refine sum_le_sum fun j _ => ?_
      have := abs_add_le (eliminate A k i j) (relim rd mul A k i j-eliminate A k i j)
      rw [add_sub_cancel] at this
      linarith
    linarith [hmass i (mem_of_mem_erase hi)]

omit hrd hmul in
theorem luLr_supp (A : Matrix ι ι ℝ) (S : Finset ι) (ks : List ι) (i j : ι) (hi : i∉S) :
    luLr rd mul A S ks i j=0 := by
  induction ks generalizing A S with
  | nil => simp [luLr, hi]
  | cons k ks ih =>
    by_cases hk : k∈S
    · simp only [luLr, hk, ite_true]
      split
      · have hik : i≠k := fun h => hi (h ▸ hk)
        simp [hik]
      · exact ih _ _ (fun h => hi (mem_of_mem_erase h))
    · simp only [luLr, hk, ite_false]
      exact ih _ _ hi

omit hrd hmul in
theorem luUr_supp_col (A : Matrix ι ι ℝ) (S : Finset ι) (ks : List ι) (i j : ι) (hj : j∉S) :
    luUr rd mul A S ks i j=0 := by
  induction ks generalizing A S with
  | nil => simp [luUr, hj]
  | cons k ks ih =>
    by_cases hk : k∈S
    · simp only [luUr, hk, ite_true]
      split
      · simp
      · exact ih _ _ (fun h => hj (mem_of_mem_erase h))
    · simp only [luUr, hk, ite_false]
      exact ih _ _ hj

omit hrd hmul in
/-- Every rounded pivot is positive and at most `M`. -/
def Good (M : ℝ) : Matrix ι ι ℝ → Finset ι → List ι → Prop
  | _, _, [] => True
  | A, S, k::ks => if k∈S then 0<A k k ∧ A k k≤M ∧ Good M (relim rd mul A k) (S.erase k) ks
      else Good M A S ks

/-- With good pivots the rounded factors reproduce every entry within
`len·η·(1+M)`. -/
theorem lur_product (M : ℝ) (hM : 0≤M) (ks : List ι) :
    ∀ (A : Matrix ι ι ℝ) (S : Finset ι), Good rd mul M A S ks →
      ∀ i∈S, ∀ j∈S, |∑ k∈S, luLr rd mul A S ks i k*luUr rd mul A S ks k j-A i j|≤
        ks.length*(η*(1+M)) := by
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  induction ks with
  | nil =>
    intro A S _ i hi j hj
    simp only [luLr, luUr, List.length_nil, Nat.cast_zero, zero_mul]
    rw [sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (fun h => absurd hi h)]
    simp [hi, hj]
  | cons k ks ih =>
    intro A S hgood i hi j hj
    simp only [List.length_cons, Nat.cast_succ]
    have hstep : (ks.length : ℝ)*(η*(1+M))+η*(1+M)=(ks.length+1)*(η*(1+M)) := by ring
    have hb0 : 0≤(ks.length : ℝ)*(η*(1+M)) := by positivity
    by_cases hk : k∈S
    · simp only [Good, hk, ite_true] at hgood
      obtain ⟨hdiag, hAkk, hnext⟩ := hgood
      simp only [luLr, luUr, hk, ite_true]
      rw [←sum_erase_add S _ hk]
      simp only [ite_true]
      have hrest : ∑ k'∈S.erase k, (if k'=k then (if i=k then (1 : ℝ) else if i∈S then
            mul (A i k) (A k k) else 0) else luLr rd mul (relim rd mul A k) (S.erase k) ks i k')*
          (if k'=k then (if j∈S then A k j else 0) else luUr rd mul (relim rd mul A k) (S.erase k) ks k' j)=
          ∑ k'∈S.erase k, luLr rd mul (relim rd mul A k) (S.erase k) ks i k'*
            luUr rd mul (relim rd mul A k) (S.erase k) ks k' j :=
        sum_congr rfl fun k' hk' => by simp [ne_of_mem_erase hk']
      rw [hrest]
      by_cases hik : i=k
      · subst hik
        rw [sum_eq_zero fun k' _ => mul_eq_zero_of_left (luLr_supp rd mul _ _ ks _ _
          (notMem_erase i S)) _]
        simp only [hj, ite_true, one_mul, zero_add, sub_self, abs_zero]
        positivity
      · have hiS' : i∈S.erase k := mem_erase.mpr ⟨hik, hi⟩
        by_cases hjk : j=k
        · subst hjk
          rw [sum_eq_zero fun k' _ => mul_eq_zero_of_right _ (luUr_supp_col rd mul _ _ ks _ _
            (notMem_erase j S))]
          simp only [hik, ite_false, hi, ite_true, zero_add, hk]
          have h2 := hmul (A i j) (A j j)
          have heq : mul (A i j) (A j j)*A j j-A i j=(mul (A i j) (A j j)-A i j/A j j)*A j j := by
            rw [sub_mul, div_mul_cancel₀ _ hdiag.ne']
          rw [heq, abs_mul, abs_of_pos hdiag]
          calc |mul (A i j) (A j j)-A i j/A j j| * A j j≤η*M := mul_le_mul h2 hAkk hdiag.le hη
            _≤(ks.length+1)*(η*(1+M)) := by nlinarith
        · have hjS' : j∈S.erase k := mem_erase.mpr ⟨hjk, hj⟩
          have hih := ih (relim rd mul A k) (S.erase k) hnext i hiS' j hjS'
          simp only [hik, ite_false, hi, ite_true, hj]
          have hround := hrd (A i j-mul (A i k) (A k k)*A k j)
          calc _=|(∑ k'∈S.erase k, luLr rd mul (relim rd mul A k) (S.erase k) ks i k'*
                luUr rd mul (relim rd mul A k) (S.erase k) ks k' j-relim rd mul A k i j)+
              (rd (A i j-mul (A i k) (A k k)*A k j)-(A i j-mul (A i k) (A k k)*A k j))| := by
                congr 1
                simp only [relim]
                ring
            _≤ks.length*(η*(1+M))+η := (abs_add_le _ _).trans (add_le_add hih hround)
            _≤(ks.length+1)*(η*(1+M)) := by nlinarith
    · simp only [Good, hk, ite_false] at hgood
      simp only [luLr, luUr, hk, ite_false]
      have := ih A S hgood i hi j hj
      nlinarith

omit hrd hmul in
theorem stageInv_mono (A : Matrix ι ι ℝ) (S : Finset ι) {μ μ' m m' : ℝ} (h : StageInv A S μ m)
    (hμ : μ'≤μ) (hm : m≤m') : StageInv A S μ' m' :=
  ⟨fun i hi => le_trans (by linarith) (h.1 i hi), fun i hi => (h.2 i hi).trans hm⟩

/-- Under the stage invariant with total losses kept inside the margin and mass
budgets, every pivot is good, every pivot row keeps margin `μ/2` and mass at most
`M`, and multiplier rows sum to at most `1+len(2M/μ+η)`. -/
theorem lur_good (μ M n : ℝ) (hμ : 0<μ) (hM : 0≤M) (hn : 0≤n) (ks : List ι) :
    ∀ (A : Matrix ι ι ℝ) (S : Finset ι) (μ' m' : ℝ), StageInv A S μ' m' →
      (S.card : ℝ)≤n → 0≤m' → m'+ks.length*(η*(n+M))≤M →
      μ/2+2*ks.length*(η*(n+M))≤μ' →
      Good rd mul M A S ks ∧
      (∀ i∈S, μ/2+∑ j∈S.erase i, |luUr rd mul A S ks i j|≤luUr rd mul A S ks i i ∧
        ∑ j∈S, |luUr rd mul A S ks i j|≤M) ∧
      (∀ i∈S, ∑ k∈S, |luLr rd mul A S ks i k|≤1+ks.length*(2*M/μ+η)) := by
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hQ : 0≤η*(n+M) := by positivity
  induction ks with
  | nil =>
    intro A S μ' m' hinv _ _ hm hmu
    simp only [List.length_nil, Nat.cast_zero, zero_mul, add_zero, mul_zero] at hm hmu ⊢
    refine ⟨trivial, fun i hi => ⟨?_, ?_⟩, fun i hi => ?_⟩
    · simp only [luUr]
      have hsum : ∑ j∈S.erase i, |(if i∈S ∧ j∈S then A i j else 0)|=∑ j∈S.erase i, |A i j| :=
        sum_congr rfl fun j hj => by simp [hi, mem_of_mem_erase hj]
      have hd : (if i∈S ∧ i∈S then A i i else 0)=A i i := by simp [hi]
      rw [hsum, hd]
      have := hinv.1 i hi
      linarith
    · simp only [luUr]
      have hs : ∑ j∈S, |(if i∈S ∧ j∈S then A i j else 0)|=∑ j∈S, |A i j| :=
        sum_congr rfl fun j hj => by simp [hi, hj]
      rw [hs]
      exact (hinv.2 i hi).trans hm
    · simp only [luLr]
      rw [sum_eq_single i (fun k _ hk => by simp [Ne.symm hk]) (fun h => absurd hi h)]
      simp [hi]
  | cons k ks ih =>
    intro A S μ' m' hinv hcard hm0 hm hmu
    simp only [List.length_cons, Nat.cast_succ] at hm hmu ⊢
    have hb0 : 0≤(ks.length : ℝ)*(η*(n+M)) := by positivity
    have hμ' : 0<μ' := by nlinarith
    by_cases hk : k∈S
    · have hdiag := pivot_pos A S μ' hμ' hinv.1 k hk
      have hmk := hinv.2 k hk
      have hAkk : A k k≤m' := by
        have := single_le_sum (f := fun j => |A k j|) (fun _ _ => abs_nonneg _) hk
        rw [abs_of_pos hdiag] at this
        linarith
      have hQ' : η*(n+m')≤η*(n+M) := by
        apply mul_le_mul_of_nonneg_left _ hη
        nlinarith
      have hnext := stageInv_mono _ _ (relim_inv rd mul η hrd hmul A S μ' m' n hμ' hcard hinv k hk)
        (μ' := μ'-2*(η*(n+M))) (m' := m'+η*(n+M)) (by linarith) (by linarith)
      have hcard' : ((S.erase k).card : ℝ)≤n := by
        have := card_erase_le (s := S) (a := k)
        have : ((S.erase k).card : ℝ)≤S.card := by exact_mod_cast this
        linarith
      obtain ⟨hg, hU, hL⟩ := ih (relim rd mul A k) (S.erase k) _ _ hnext hcard' (by linarith)
        (by nlinarith) (by nlinarith)
      refine ⟨?_, fun i hi => ?_, fun i hi => ?_⟩
      · simp only [Good, hk, ite_true]
        exact ⟨hdiag, by nlinarith, hg⟩
      · simp only [luUr, hk, ite_true]
        by_cases hik : i=k
        · subst hik
          simp only [ite_true]
          have hsum : ∑ j∈S.erase i, |(if j∈S then A i j else 0)|=∑ j∈S.erase i, |A i j| :=
            sum_congr rfl fun j hj => by simp [mem_of_mem_erase hj]
          have hs2 : ∑ j∈S, |(if j∈S then A i j else 0)|=∑ j∈S, |A i j| :=
            sum_congr rfl fun j hj => by simp [hj]
          have hd : (if i∈S then A i i else 0)=A i i := by simp [hi]
          rw [hsum, hs2, hd]
          have := hinv.1 i hi
          constructor <;> nlinarith
        · have hiS' : i∈S.erase k := mem_erase.mpr ⟨hik, hi⟩
          obtain ⟨hd, hm'⟩ := hU i hiS'
          simp only [hik, ite_false]
          have hzk := luUr_supp_col rd mul (relim rd mul A k) (S.erase k) ks i k (notMem_erase k S)
          have hs1 := sum_erase_add (S.erase i) (fun j => |luUr rd mul (relim rd mul A k) (S.erase k) ks i j|)
            (mem_erase.mpr ⟨Ne.symm hik, hk⟩)
          have hs2 := sum_erase_add S (fun j => |luUr rd mul (relim rd mul A k) (S.erase k) ks i j|) hk
          rw [hzk, abs_zero, add_zero, erase_right_comm] at hs1
          rw [hzk, abs_zero, add_zero] at hs2
          constructor <;> linarith
      · simp only [luLr, hk, ite_true]
        rw [←sum_erase_add S _ hk]
        simp only [ite_true]
        have hrest : ∑ k'∈S.erase k, |if k'=k then (if i=k then (1 : ℝ) else if i∈S then
              mul (A i k) (A k k) else 0) else luLr rd mul (relim rd mul A k) (S.erase k) ks i k'|=
            ∑ k'∈S.erase k, |luLr rd mul (relim rd mul A k) (S.erase k) ks i k'| :=
          sum_congr rfl fun k' hk' => by simp [ne_of_mem_erase hk']
        rw [hrest]
        have hgrow : 0≤2*M/μ+η := by positivity
        by_cases hik : i=k
        · subst hik
          rw [sum_eq_zero fun k' _ => abs_eq_zero.mpr (luLr_supp rd mul _ _ ks _ _ (notMem_erase i S))]
          simp only [ite_true, abs_one, zero_add]
          nlinarith
        · have hiS' : i∈S.erase k := mem_erase.mpr ⟨hik, hi⟩
          have hLi := hL i hiS'
          simp only [hik, ite_false, hi, ite_true]
          have hr := hmul (A i k) (A k k)
          have hAik : |A i k|≤M := by
            have := single_le_sum (f := fun j => |A i j|) (fun _ _ => abs_nonneg _) hk
            linarith [hinv.2 i hi]
          have hq : |A i k/A k k|≤2*M/μ := by
            rw [abs_div, abs_of_pos hdiag, div_le_div_iff₀ hdiag hμ]
            have : μ/2≤A k k := by
              have := hinv.1 k hk
              have : 0≤∑ j∈S.erase k, |A k j| := sum_nonneg fun _ _ => abs_nonneg _
              linarith
            nlinarith [abs_nonneg (A i k)]
          have : |mul (A i k) (A k k)|≤2*M/μ+η := by
            have := abs_add_le (mul (A i k) (A k k)-A i k/A k k) (A i k/A k k)
            rw [sub_add_cancel] at this
            linarith
          nlinarith
    · simp only [Good, luLr, luUr, hk, ite_false]
      obtain ⟨hg, hU, hL⟩ := ih A S μ' m' hinv hcard hm0 (by nlinarith) (by nlinarith)
      refine ⟨hg, hU, fun i hi => ?_⟩
      have := hL i hi
      have hgrow : 0≤2*M/μ+η := by positivity
      nlinarith

omit hrd hmul in
theorem luLr_diag (A : Matrix ι ι ℝ) (S : Finset ι) (ks : List ι) (i : ι) (hi : i∈S) :
    luLr rd mul A S ks i i=1 := by
  induction ks generalizing A S with
  | nil => simp [luLr, hi]
  | cons k ks ih =>
    by_cases hk : k∈S
    · simp only [luLr, hk, ite_true]
      by_cases hik : i=k
      · simp [hik]
      · simp only [hik, ite_false]
        exact ih _ _ (mem_erase.mpr ⟨hik, hi⟩)
    · simp only [luLr, hk, ite_false]
      exact ih _ _ hi

/-- Rounded elimination followed by rounded triangular solves. With row mass
`m`, margin `μ`, at most `n` active vertices, a list of length `len`, and
rounding `η` small enough that the stage losses stay inside the budgets, the
computed solution is within `2((Λδ+η)/μ+(εS/μ)X)` of the exact one, where
`Λ = 1+len(2M/μ+η)` and `εS = n·len·η(1+M)`. -/
theorem rounded_elimination_solve (A : Matrix ι ι ℝ) (S : Finset ι) (μ m M n : ℝ) (hμ : 0<μ)
    (hM : 0≤M) (hm0 : 0≤m) (hinv : StageInv A S μ m) (hcard : (S.card : ℝ)≤n)
    (ks : List ι) (hm : m+ks.length*(η*(n+M))≤M) (hmu : μ/2+2*ks.length*(η*(n+M))≤μ)
    (x b xh y : ι → ℝ) (hx : Solves A S x b) (δ X : ℝ) (hX : 0≤X)
    (hxX : ∀ j∈S, |x j|≤X)
    (hf : ∀ k∈S, |y k+∑ j∈S.erase k, luLr rd mul A S ks k j*y j-b k|≤η)
    (hb : ∀ k∈S, |∑ j∈S, luUr rd mul A S ks k j*xh j-y k|≤δ)
    (hsmall : n*(ks.length*(η*(1+M)))/μ≤1/2) (j : ι) (hj : j∈S) :
    |xh j-x j|≤2*(((1+ks.length*(2*M/μ+η))*δ+η)/μ+n*(ks.length*(η*(1+M)))/μ*X) := by
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hn : 0≤n := le_trans (Nat.cast_nonneg _) hcard
  obtain ⟨hgood, -, hL⟩ := lur_good rd mul η hrd hmul μ M n hμ hM hn ks A S μ m hinv hcard hm0 hm hmu
  have hprod := lur_product rd mul η hrd hmul M hM ks A S hgood
  have hεS : ∀ i∈S, ∑ j∈S, |∑ k∈S, luLr rd mul A S ks i k*luUr rd mul A S ks k j-A i j|≤
      n*(ks.length*(η*(1+M))) := by
    intro i hi
    calc ∑ j∈S, |∑ k∈S, luLr rd mul A S ks i k*luUr rd mul A S ks k j-A i j|
        ≤∑ _j∈S, (ks.length : ℝ)*(η*(1+M)) := sum_le_sum fun j hj => hprod i hi j hj
      _=(S.card : ℝ)*(ks.length*(η*(1+M))) := by rw [sum_const, nsmul_eq_mul]
      _≤n*(ks.length*(η*(1+M))) := by gcongr
  exact backward_lu A (luLr rd mul A S ks) (luUr rd mul A S ks) S μ hμ hinv.1 x b xh y hx _ _ η δ X
    (by positivity) hX (fun i hi => luLr_diag rd mul A S ks i hi) hL hεS hxX hf hb hsmall j hj

end IntegerMultBounds.NLogN.SchurDominance
