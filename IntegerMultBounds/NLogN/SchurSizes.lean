module

public import IntegerMultBounds.NLogN.SchurStages
import IntegerMultBounds.NLogN.SchurFill

/-! Sizes of the values met by the rounded band solve. Every stage matrix of
the rounded elimination keeps the stage invariant, so its active entries are
at most the mass bound `M` and its pivots lie in `[μ/2, M]`; the multiplier
rule is only consulted on that range. The computed solution is within the
error bound of the exact one, and each forward value is reproduced by its
pivot row applied to the solution, so it is at most `M` times the solution
bound up to the residual. These bounds fix the record width of a fixed-point
machine running the solve. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.SchurDominance

open scoped BigOperators
open Finset

section Map

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The stage invariant only sees the active block. -/
theorem stageInv_congr {A A' : Matrix ι ι ℝ} {S : Finset ι} {μ m : ℝ} (h : StageInv A S μ m)
    (hA : ∀ i∈S, ∀ j∈S, A' i j=A i j) : StageInv A' S μ m := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [hA i hi i hi, sum_congr rfl fun j hj => by rw [hA i hi j (mem_of_mem_erase hj)]]
    exact h.1 i hi
  · rw [sum_congr rfl fun j hj => by rw [hA i hi j hj]]
    exact h.2 i hi

/-- Relabelling the vertices by an injection keeps the stage invariant. -/
theorem stageInv_map (f : ι → κ) (hf : Function.Injective f) (A : Matrix ι ι ℝ)
    (A' : Matrix κ κ ℝ) (hA : ∀ a c, A' (f a) (f c)=A a c) (S : Finset ι) (μ m : ℝ)
    (h : StageInv A S μ m) : StageInv A' (S.image f) μ m := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := mem_image.mp hi
    rw [← image_erase hf, sum_image fun x _ y _ e => hf e, hA]
    simpa only [hA] using h.1 a ha
  · obtain ⟨a, ha, rfl⟩ := mem_image.mp hi
    rw [sum_image fun x _ y _ e => hf e]
    simpa only [hA] using h.2 a ha

end Map

section Stages

variable (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x-x|≤η)

theorem stgIco_erase (a b : ℕ) : (Ico a b).erase a=Ico (a+1) b := by
  ext x; simp only [mem_erase, mem_Ico]; omega

include hrd in
/-- **Every stage of the rounded elimination keeps the invariant.** The multiplier rule
need only be accurate on entries at most `M` and pivots in `[μ/2, M]`. -/
theorem stg_invL (μ M n : ℝ) (hμ : 0<μ) (hM : 0≤M)
    (hmul : ∀ a c, |a|≤M → μ/2≤c → c≤M → |mul a c-a/c|≤η)
    (A : Matrix ℕ ℕ ℝ) (k₀ N : ℕ) (m : ℝ) (hcard : (N : ℝ)≤n)
    (hinv : StageInv A (Ico k₀ (k₀+N)) μ m) (hm : m+N*(η*(n+M))≤M)
    (hmu : μ/2+2*N*(η*(n+M))≤μ) :
    ∀ j ≤ N, StageInv (stg rd mul A k₀ j) (Ico (k₀+j) (k₀+N)) (μ-2*j*(η*(n+M)))
      (m+j*(η*(n+M))) := by
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hn : 0≤n := le_trans (Nat.cast_nonneg _) hcard
  have hQ : 0≤η*(n+M) := by positivity
  intro j
  induction j with
  | zero => intro _; simpa [stg] using hinv
  | succ j ih =>
    intro hj
    have hinvj := ih (by omega)
    set Aj := stg rd mul A k₀ j
    set S := Ico (k₀+j) (k₀+N)
    have hjN : (j : ℝ)+1≤N := by exact_mod_cast hj
    have hmj : m+j*(η*(n+M))≤M := by nlinarith
    have hμj : μ/2≤μ-2*j*(η*(n+M)) := by nlinarith
    have hk : k₀+j∈S := by simp [S]; omega
    have hpiv : μ/2≤Aj (k₀+j) (k₀+j) ∧ Aj (k₀+j) (k₀+j)≤M := by
      have h1 := hinvj.1 _ hk
      have h0 : 0≤∑ l∈S.erase (k₀+j), |Aj (k₀+j) l| := sum_nonneg fun _ _ => abs_nonneg _
      have h2 : |Aj (k₀+j) (k₀+j)|≤∑ l∈S, |Aj (k₀+j) l| :=
        single_le_sum (f := fun l => |Aj (k₀+j) l|) (fun _ _ => abs_nonneg _) hk
      have h3 := hinvj.2 _ hk
      constructor
      · linarith
      · linarith [le_abs_self (Aj (k₀+j) (k₀+j))]
    have hent : ∀ i∈S, |Aj i (k₀+j)|≤M := fun i hi =>
      ((single_le_sum (f := fun l => |Aj i l|) (fun _ _ => abs_nonneg _) hk).trans
        (hinvj.2 i hi)).trans hmj
    -- a total rule agreeing with `mul` on the working range
    set mul' : ℝ → ℝ → ℝ := fun a c => if |a|≤M ∧ μ/2≤c ∧ c≤M then mul a c else a/c
    have hmul' : ∀ a c, |mul' a c-a/c|≤η := fun a c => by
      simp only [mul']
      split_ifs with h
      · exact hmul a c h.1 h.2.1 h.2.2
      · simp [hη]
    have hcardS : ((S.card : ℕ) : ℝ)≤n := by
      have : S.card=N-j := by simp [S]; omega
      rw [this]; push_cast [show j ≤ N by omega]; linarith
    have hstep := relim_inv rd mul' η hrd hmul' Aj S _ _ n (by linarith) hcardS hinvj (k₀+j) hk
    rw [stgIco_erase] at hstep
    have hq : η*(n+(m+j*(η*(n+M))))≤η*(n+M) := mul_le_mul_of_nonneg_left (by linarith) hη
    have hmono : StageInv (relim rd mul' Aj (k₀+j)) (Ico (k₀+j+1) (k₀+N))
        (μ-2*((j+1 : ℕ) : ℝ)*(η*(n+M))) (m+((j+1 : ℕ) : ℝ)*(η*(n+M))) :=
      stageInv_mono _ _ hstep (by push_cast; linarith) (by push_cast; linarith)
    refine stageInv_congr (by simpa [add_assoc] using hmono) fun i hi l _ => ?_
    have hiS : i∈S := by simp [S] at hi ⊢; omega
    show relim rd mul Aj (k₀+j) i l=relim rd mul' Aj (k₀+j) i l
    simp only [relim, mul', hent i hiS, hpiv.1, hpiv.2, and_self, ite_true]

include hrd in
/-- The pivots and active entries of every stage. -/
theorem stg_sizes (μ M n : ℝ) (hμ : 0<μ) (hM : 0≤M)
    (hmul : ∀ a c, |a|≤M → μ/2≤c → c≤M → |mul a c-a/c|≤η)
    (A : Matrix ℕ ℕ ℝ) (k₀ N : ℕ) (m : ℝ) (hcard : (N : ℝ)≤n)
    (hinv : StageInv A (Ico k₀ (k₀+N)) μ m) (hm : m+N*(η*(n+M))≤M)
    (hmu : μ/2+2*N*(η*(n+M))≤μ) (j : ℕ) (hj : j<N) :
    (μ/2≤stg rd mul A k₀ j (k₀+j) (k₀+j) ∧ stg rd mul A k₀ j (k₀+j) (k₀+j)≤M) ∧
      ∀ i l, k₀+j ≤ i → i<k₀+N → k₀+j ≤ l → l<k₀+N → |stg rd mul A k₀ j i l|≤M := by
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hn : 0≤n := le_trans (Nat.cast_nonneg _) hcard
  have hQ : 0≤η*(n+M) := by positivity
  have hinvj := stg_invL rd mul η hrd μ M n hμ hM hmul A k₀ N m hcard hinv hm hmu j hj.le
  have hjN : (j : ℝ)≤N := by exact_mod_cast hj.le
  have hmj : m+j*(η*(n+M))≤M := by nlinarith
  have hμj : μ/2≤μ-2*j*(η*(n+M)) := by nlinarith
  have hmem : ∀ i, k₀+j ≤ i → i<k₀+N → i∈Ico (k₀+j) (k₀+N) := fun i h1 h2 => by simp; omega
  have hk := hmem (k₀+j) le_rfl (by omega)
  refine ⟨⟨?_, ?_⟩, fun i l hi1 hi2 hl1 hl2 => ?_⟩
  · have h1 := hinvj.1 _ hk
    have h0 : 0≤∑ l∈(Ico (k₀+j) (k₀+N)).erase (k₀+j), |stg rd mul A k₀ j (k₀+j) l| :=
      sum_nonneg fun _ _ => abs_nonneg _
    linarith
  · have h2 : |stg rd mul A k₀ j (k₀+j) (k₀+j)|≤∑ l∈Ico (k₀+j) (k₀+N), |stg rd mul A k₀ j (k₀+j) l| :=
      single_le_sum (f := fun l => |stg rd mul A k₀ j (k₀+j) l|) (fun _ _ => abs_nonneg _) hk
    have h3 := hinvj.2 _ hk
    linarith [le_abs_self (stg rd mul A k₀ j (k₀+j) (k₀+j))]
  · exact ((single_le_sum (f := fun l => |stg rd mul A k₀ j i l|) (fun _ _ => abs_nonneg _)
      (hmem l hl1 hl2)).trans (hinvj.2 i (hmem i hi1 hi2))).trans hmj

end Stages

section Solve

variable {ι : Type*} [DecidableEq ι]

/-- **Sizes of the band solve.** The computed solution is at most `Xb` (the exact
bound plus the error bound), every forward value is at most `M Xb` plus the back
residual, and every pivot lies in `[μ/2, M]`. -/
theorem bandSolveG_sizes (rd : ℝ → ℝ) (mul : ℝ → ℝ → ℝ) (rec : ℝ → ℝ) (η θ : ℝ)
    (hrd : ∀ x, |rd x-x|≤η) (hrd0 : rd 0=0) (hmul : ∀ a b, |mul a b-a/b|≤η)
    (hmul0 : ∀ b, mul 0 b=0)
    (pos : ι → ℕ) (hpos : Function.Injective pos)
    (A : Matrix ι ι ℝ) (S : Finset ι) (μ m M n : ℝ) (hμ : 0<μ) (hM : 0≤M) (hm0 : 0≤m)
    (hinv : StageInv A S μ m) (hcard : (S.card : ℝ)≤n) (ks : List ι) (hks : ks.toFinset=S)
    (hsort : ks.Pairwise (fun a b => pos a<pos b))
    (hm : m+ks.length*(η*(n+M))≤M) (hmu : μ/2+2*ks.length*(η*(n+M))≤μ)
    (hrec : ∀ c, μ/2≤c → c≤M → |c*rec c-1|≤θ) (hθ : θ≤1/2)
    (x b : ι → ℝ) (hx : Solves A S x b) (X : ℝ) (hX : 0≤X) (hxX : ∀ j∈S, |x j|≤X)
    (hsmall : (n*(ks.length*(η*(1+M)))+(1+ks.length*(2*M/μ+η))*(2*θ*M))/μ≤1/2)
    (Xb : ℝ) (hXb : X+2*(((1+ks.length*(2*M/μ+η))*((n+M+2*θ*M)*η)+n*η)/μ+
        (n*(ks.length*(η*(1+M)))+(1+ks.length*(2*M/μ+η))*(2*θ*M))/μ*X)≤Xb) :
    (∀ j∈S, |bandSolveG rd mul rec A S ks b j|≤Xb) ∧
    (∀ k∈S, |fwdM rd (luLr rd mul A S ks) b ∅ (fun _ => 0) ks k|≤
      M*Xb+((n+M+2*θ*M)*η+2*θ*M*Xb)) ∧
    (∀ k∈S, μ/2≤luUr rd mul A S ks k k ∧ luUr rd mul A S ks k k≤M) := by
  have hη : 0≤η := le_trans (abs_nonneg _) (hrd 0)
  have hn : 0≤n := le_trans (Nat.cast_nonneg _) hcard
  have hsol : ∀ j∈S, |bandSolveG rd mul rec A S ks b j|≤Xb := fun j hj => by
    have h1 := bandSolveG_error rd mul rec η θ hrd hrd0 hmul hmul0 pos hpos A S μ m M n hμ hM hm0
      hinv hcard ks hks hsort hm hmu hrec hθ x b hx X hX hxX hsmall j hj
    have h2 := hxX j hj
    have := abs_sub_abs_le_abs_sub (bandSolveG rd mul rec A S ks b j) (x j)
    linarith
  obtain ⟨-, hU, -⟩ := lur_good rd mul η hrd hmul μ M n hμ hM hn ks A S μ m hinv hcard hm0 hm hmu
  obtain ⟨-, hUt⟩ := fill_support_r rd mul hrd0 hmul0 pos (fun _ _ => True)
    (fun _ _ _ _ _ _ _ => trivial) ks A S (by rw [hks]) hsort (fun _ _ _ _ _ => trivial)
  have hmem : ∀ k∈ks, k∈S := fun k hk => hks ▸ List.mem_toFinset.mpr hk
  have hdone : (∅ : Finset ι)=S\ks.toFinset := by rw [hks, sdiff_self]; rfl
  have hpiv : ∀ k∈S, μ/2≤luUr rd mul A S ks k k ∧ luUr rd mul A S ks k k≤M := by
    intro k hk
    obtain ⟨hd, hmass⟩ := hU k hk
    have h0 : 0≤∑ j∈S.erase k, |luUr rd mul A S ks k j| := sum_nonneg fun _ _ => abs_nonneg _
    have hle : |luUr rd mul A S ks k k|≤∑ j∈S, |luUr rd mul A S ks k j| :=
      single_le_sum (f := fun j => |luUr rd mul A S ks k j|) (fun _ _ => abs_nonneg _) hk
    exact ⟨by linarith, by linarith [le_abs_self (luUr rd mul A S ks k k)]⟩
  have hdiag : ∀ k∈S, |luUr rd mul A S ks k k|≤M ∧
      |luUr rd mul A S ks k k*rec (luUr rd mul A S ks k k)-1|≤θ := fun k hk => by
    have := hpiv k hk
    exact ⟨abs_le.mpr ⟨by linarith, this.2⟩, hrec _ this.1 this.2⟩
  have hb := bwdM_residual rd η M θ hrd pos hpos (luUr rd mul A S ks) _
    (fwdM rd (luLr rd mul A S ks) b ∅ (fun _ => 0) ks) S (fun k j h => (hUt k j h).2) hdiag hθ hM
    ks.reverse ∅ (fun _ => 0) (List.pairwise_reverse.mpr hsort)
    (fun k hk => hmem k (List.mem_reverse.mp hk)) (by rw [List.toFinset_reverse]; exact hdone)
  refine ⟨hsol, fun k hk => ?_, hpiv⟩
  have hXb0 : 0≤Xb := (abs_nonneg _).trans (hsol k hk)
  have h1 := hb Xb hsol k (List.mem_reverse.mpr (List.mem_toFinset.mp (hks ▸ hk)))
  have hsum : |∑ j∈S, luUr rd mul A S ks k j*bandSolveG rd mul rec A S ks b j|≤M*Xb :=
    calc _ ≤ ∑ j∈S, |luUr rd mul A S ks k j| * Xb :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hsol j hj) (abs_nonneg _))
      _=(∑ j∈S, |luUr rd mul A S ks k j|)*Xb := by rw [sum_mul]
      _≤M*Xb := mul_le_mul_of_nonneg_right (hU k hk).2 hXb0
  have hc : ((S.card : ℝ)+M+2*θ*M)*η≤(n+M+2*θ*M)*η := mul_le_mul_of_nonneg_right (by linarith) hη
  unfold bandSolveG at hsum
  have := abs_sub_abs_le_abs_sub (∑ j∈S, luUr rd mul A S ks k j*
    bwdM rd (luUr rd mul A S ks) (fun k => rec (luUr rd mul A S ks k k))
      (fwdM rd (luLr rd mul A S ks) b ∅ (fun _ => 0) ks) ∅ (fun _ => 0) ks.reverse j)
    (fwdM rd (luLr rd mul A S ks) b ∅ (fun _ => 0) ks k)
  rw [abs_sub_comm] at this
  have h2 := abs_sub_abs_le_abs_sub (fwdM rd (luLr rd mul A S ks) b ∅ (fun _ => 0) ks k)
    (∑ j∈S, luUr rd mul A S ks k j*
    bwdM rd (luUr rd mul A S ks) (fun k => rec (luUr rd mul A S ks k k))
      (fwdM rd (luLr rd mul A S ks) b ∅ (fun _ => 0) ks) ∅ (fun _ => 0) ks.reverse j)
  rw [abs_sub_comm] at h2
  linarith

end Solve

end IntegerMultBounds.NLogN.SchurDominance
