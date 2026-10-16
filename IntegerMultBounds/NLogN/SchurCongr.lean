module

public import IntegerMultBounds.NLogN.SchurSubst

/-! Rounded elimination only consults the multiplier rule on the working range.
Under the stage-invariant budgets every multiplier is taken of an entry of size
at most `M` by a pivot in `[μ/2, M]`, so two rules that agree there produce the
same factors, and two reciprocal rules that agree there produce the same solve.
This lets a tape machine use an unguarded rule (no range test) while the error
analysis uses a total rule. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem luUr_supp_row (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (A : Matrix ι ι ℝ) (S : Finset ι)
    (ks : List ι) (i j : ι) (hi : i∉S) : luUr rd mul A S ks i j=0 := by
  induction ks generalizing A S with
  | nil => simp [luUr, hi]
  | cons k ks ih =>
    by_cases hk : k∈S
    · simp only [luUr, hk, ite_true]
      have hik : i≠k := fun h => hi (h ▸ hk)
      simp only [hik, ite_false]
      exact ih _ _ (fun h => hi (mem_of_mem_erase h))
    · simp only [luUr, hk, ite_false]
      exact ih _ _ hi

theorem bwdM_congr_r (rd : ℝ → ℝ) (U : Matrix ι ι ℝ) (r r' y : ι → ℝ) (ks : List ι)
    (hr : ∀ k∈ks, r' k=r k) : ∀ (done : Finset ι) (x : ι → ℝ),
      bwdM rd U r' y done x ks=bwdM rd U r y done x ks := by
  induction ks with
  | nil => intro _ _; rfl
  | cons k ks ih =>
    intro done x
    simp only [bwdM, hr k List.mem_cons_self]
    exact ih (fun z hz => hr z (List.mem_cons_of_mem _ hz)) _ _

variable (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η)
  (hmul : ∀ a b, |mul a b-a/b|≤η)
include hrd hmul

/-- Factors agree on the active rows when the rules agree on the working range. -/
theorem lur_congr (mul' : ℝ → ℝ → ℝ) (μ M n : ℝ) (hμ : 0<μ) (hM : 0≤M) (hn : 0≤n)
    (hagree : ∀ a c, |a|≤M → μ/2≤c → c≤M → mul' a c=mul a c) (ks : List ι) :
    ∀ (A A' : Matrix ι ι ℝ) (S : Finset ι) (μ' m' : ℝ), StageInv A S μ' m' →
      (∀ i∈S, ∀ j, A' i j=A i j) → (S.card : ℝ)≤n → 0≤m' → m'+ks.length*(η*(n+M))≤M →
      μ/2+2*ks.length*(η*(n+M))≤μ' →
      ∀ i∈S, ∀ j, luLr rd mul' A' S ks i j=luLr rd mul A S ks i j ∧
        luUr rd mul' A' S ks i j=luUr rd mul A S ks i j := by
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  induction ks with
  | nil =>
    intro A A' S μ' m' _ hAA' _ _ _ _ i hi j
    simp [luLr, luUr, hi, hAA' i hi]
  | cons k ks ih =>
    intro A A' S μ' m' hinv hAA' hcard hm0 hm hmu i hi j
    simp only [List.length_cons, Nat.cast_succ] at hm hmu
    have hb0 : 0≤(ks.length : ℝ)*(η*(n+M)) := by positivity
    have hQ : 0≤η*(n+M) := by positivity
    have hμ' : 0<μ' := by nlinarith
    by_cases hk : k∈S
    · have hmM : m'≤M := by nlinarith
      have hent : ∀ x∈S, ∀ y∈S, |A x y|≤M := fun x hx y hy =>
        ((single_le_sum (f := fun z => |A x z|) (fun _ _ => abs_nonneg _) hy).trans
          (hinv.2 x hx)).trans hmM
      have hpiv : μ/2≤A k k ∧ A k k≤M := by
        have h := hinv.1 k hk
        have hs : 0≤∑ j∈S.erase k, |A k j| := sum_nonneg fun _ _ => abs_nonneg _
        refine ⟨by nlinarith, (le_abs_self _).trans (hent k hk k hk)⟩
      have hcol : ∀ x∈S, mul' (A' x k) (A' k k)=mul (A x k) (A k k) := fun x hx => by
        rw [hAA' x hx, hAA' k hk]
        exact hagree _ _ (hent x hx k hk) hpiv.1 hpiv.2
      have hQ' : η*(n+m')≤η*(n+M) := by
        apply mul_le_mul_of_nonneg_left _ hη
        linarith
      have hnext := stageInv_mono _ _ (relim_inv rd mul η hrd hmul A S μ' m' n hμ' hcard hinv k hk)
        (μ' := μ'-2*(η*(n+M))) (m' := m'+η*(n+M)) (by linarith) (by linarith)
      have hcard' : ((S.erase k).card : ℝ)≤n := by
        have := card_erase_le (s := S) (a := k)
        have : ((S.erase k).card : ℝ)≤S.card := by exact_mod_cast this
        linarith
      have hrows : ∀ x∈S.erase k, ∀ y, relim rd mul' A' k x y=relim rd mul A k x y := by
        intro x hx y
        have hxS := mem_of_mem_erase hx
        simp only [relim]
        rw [hcol x hxS, hAA' x hxS, hAA' k hk]
      have hih := ih (relim rd mul A k) (relim rd mul' A' k) (S.erase k) _ _ hnext hrows hcard'
        (by linarith) (by nlinarith) (by nlinarith)
      simp only [luLr, luUr, hk, ite_true]
      by_cases hik : i=k
      · subst hik
        refine ⟨?_, ?_⟩
        · split
          · simp
          · rw [luLr_supp rd mul' _ _ ks i j (notMem_erase i S),
              luLr_supp rd mul _ _ ks i j (notMem_erase i S)]
        · simp only [ite_true]
          split
          · exact hAA' i hi j
          · rfl
      · have hiS' : i∈S.erase k := mem_erase.mpr ⟨hik, hi⟩
        simp only [hik, ite_false, hi, ite_true, hcol i hi]
        exact ⟨by split <;> [rfl; exact (hih i hiS' j).1], (hih i hiS' j).2⟩
    · simp only [luLr, luUr, hk, ite_false]
      exact ih A A' S μ' m' (stageInv_mono _ _ hinv (by linarith) le_rfl) hAA' hcard hm0
        (by linarith) (by linarith) i hi j

/-- Two multiplier rules and two reciprocal rules that agree on the working range
give the same solve. -/
theorem bandSolveG_congr (mul' : ℝ → ℝ → ℝ) (rec rec' : ℝ → ℝ)
    (A : Matrix ι ι ℝ) (S : Finset ι) (μ m M n : ℝ) (hμ : 0<μ) (hM : 0≤M) (hm0 : 0≤m)
    (hinv : StageInv A S μ m) (hcard : (S.card : ℝ)≤n) (ks : List ι) (hks : ks.toFinset=S)
    (hm : m+ks.length*(η*(n+M))≤M) (hmu : μ/2+2*ks.length*(η*(n+M))≤μ)
    (hagree : ∀ a c, |a|≤M → μ/2≤c → c≤M → mul' a c=mul a c)
    (hrec : ∀ c, μ/2≤c → c≤M → rec' c=rec c) (b : ι → ℝ) :
    bandSolveG rd mul' rec' A S ks b=bandSolveG rd mul rec A S ks b := by
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hn : 0≤n := le_trans (Nat.cast_nonneg _) hcard
  have hc := lur_congr rd mul η hrd hmul mul' μ M n hμ hM hn hagree ks A A S μ m hinv
    (fun _ _ _ => rfl) hcard hm0 hm (by linarith)
  have hL : luLr rd mul' A S ks=luLr rd mul A S ks := by
    funext i j
    by_cases hi : i∈S
    · exact (hc i hi j).1
    · rw [luLr_supp rd mul' A S ks i j hi, luLr_supp rd mul A S ks i j hi]
  have hU : luUr rd mul' A S ks=luUr rd mul A S ks := by
    funext i j
    by_cases hi : i∈S
    · exact (hc i hi j).2
    · rw [luUr_supp_row rd mul' A S ks i j hi, luUr_supp_row rd mul A S ks i j hi]
  obtain ⟨_, hUg, _⟩ := lur_good rd mul η hrd hmul μ M n hμ hM hn ks A S μ m hinv hcard hm0 hm hmu
  unfold bandSolveG
  rw [hL, hU]
  refine bwdM_congr_r rd _ _ _ _ _ (fun k hk => ?_) _ _
  have hkS : k∈S := hks ▸ List.mem_toFinset.mpr (List.mem_reverse.mp hk)
  obtain ⟨hd, hmass⟩ := hUg k hkS
  have hs : 0≤∑ j∈S.erase k, |luUr rd mul A S ks k j| := sum_nonneg fun _ _ => abs_nonneg _
  have hle : |luUr rd mul A S ks k k|≤M :=
    (single_le_sum (f := fun j => |luUr rd mul A S ks k j|) (fun _ _ => abs_nonneg _) hkS).trans hmass
  exact hrec _ (by linarith) ((le_abs_self _).trans hle)

end IntegerMultBounds.NLogN.SchurDominance
