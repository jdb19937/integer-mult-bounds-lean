module

public import IntegerMultBounds.NLogN.ResamplingMultiNumeric

/-! The padded box of the tensor interface. On tape every axis keeps its
padded length `tᵢ`; a map from length `sᵢ` to `tᵢ` reads the first `sᵢ`
entries of each line (`restr`), and a map from `tᵢ` to `sᵢ` writes zeros after
its `sᵢ` outputs (`extd`). The tensor of the padded square maps equals the
rectangular tensor of the original maps on the restricted array
(`tensorZR_restr`) or extended by zeros (`tensorZR_extd`). -/

@[expose] public section

namespace IntegerMultBounds.Resampling.PaddedTensor

open IntegerMultBounds.NLogN

/-- The first `s` entries of a line of length `t`. -/
def restr (s t : ℕ) (v : ZMod t → ℂ) : ZMod s → ℂ := fun j => v (j.val : ZMod t)

/-- The restriction of a `d`-dimensional array to the first `Sᵢ` entries of each axis. -/
def restrD {d : ℕ} (S T : Fin d → ℕ) (v : ((i : Fin d) → ZMod (T i)) → ℂ) : ((i : Fin d) → ZMod (S i)) → ℂ :=
  fun j => v fun i => ((j i).val : ZMod (T i))

theorem tensorZR_restr : ∀ (d : ℕ) (S T : Fin d → ℕ) [∀ i, NeZero (S i)] [∀ i, NeZero (T i)]
    (A : (i : Fin d) → (ZMod (S i) → ℂ) → (ZMod (T i) → ℂ)) (v : ((i : Fin d) → ZMod (T i)) → ℂ),
    tensorZR d T T (fun i => A i ∘ restr (S i) (T i)) v = tensorZR d S T A (restrD S T v)
  | 0, _, _, _, _, _, v => by
    funext k; simp only [tensorZR, restrD]; congr 1; funext i; exact i.elim0
  | d + 1, S, T, _, _, A, v => by
    funext k
    simp only [tensorZR, Function.comp_apply, alongHeadZR, alongTailZR]
    unfold restr
    congr 1
    funext j₀
    have ih := tensorZR_restr d (fun i => S i.succ) (fun i => T i.succ) (fun i => A i.succ)
    unfold restr at ih
    beta_reduce
    erw [ih]
    congr 1
    funext j
    simp only [restrD]
    congr 1
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i => rfl

/-- A line of length `s` followed by zeros up to length `t`. -/
def extd (s t : ℕ) (u : ZMod s → ℂ) : ZMod t → ℂ := fun k => if k.val < s then u (k.val : ZMod s) else 0

/-- A `d`-dimensional array extended by zeros from `Sᵢ` to `Tᵢ` entries per axis. -/
def extdD {d : ℕ} (S T : Fin d → ℕ) (u : ((i : Fin d) → ZMod (S i)) → ℂ) : ((i : Fin d) → ZMod (T i)) → ℂ :=
  fun k => if ∀ i, (k i).val < S i then u (fun i => ((k i).val : ZMod (S i))) else 0

theorem tensorZR_extd : ∀ (d : ℕ) (S T : Fin d → ℕ) [∀ i, NeZero (S i)] [∀ i, NeZero (T i)]
    (B : (i : Fin d) → (ZMod (T i) → ℂ) → (ZMod (S i) → ℂ)), (∀ i, B i 0 = 0) →
    ∀ v : ((i : Fin d) → ZMod (T i)) → ℂ,
    tensorZR d T T (fun i => extd (S i) (T i) ∘ B i) v = extdD S T (tensorZR d T S B v)
  | 0, _, _, _, _, _, _, v => by
    funext k; simp only [tensorZR, extdD]; simp
  | d + 1, S, T, _, _, B, hB, v => by
    funext k
    have ih := tensorZR_extd d (fun i => S i.succ) (fun i => T i.succ) (fun i => B i.succ) (fun i => hB i.succ)
    simp only [tensorZR, Function.comp_apply, alongHeadZR, alongTailZR]
    unfold extd at ih ⊢
    simp only [extdD]
    have key : ∀ j₀ : ZMod (T 0), tensorZR d (fun i => T i.succ) (fun i => T i.succ)
        (fun i => (fun u k => if k.val < S i.succ then u (k.val : ZMod (S i.succ)) else 0) ∘ B i.succ)
        (fun j' => v (Fin.cons j₀ j')) (Fin.tail k) =
        if ∀ i : Fin d, (k i.succ).val < S i.succ then
          tensorZR d (fun i => T i.succ) (fun i => S i.succ) (fun i => B i.succ) (fun j' => v (Fin.cons j₀ j'))
            (fun i => ((k i.succ).val : ZMod (S i.succ)))
        else 0 := fun j₀ => by rw [ih]; rfl
    by_cases h0 : (k 0).val < S 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
      by_cases ht : ∀ i : Fin d, (k i.succ).val < S i.succ
      · have hall : ∀ i : Fin (d + 1), (k i).val < S i := by
          intro i; induction i using Fin.cases with
          | zero => exact h0
          | succ i => exact ht i
        rw [ite_eq_left_of_eq_true _ _ (eq_true hall)]
        simp only [alongHeadZR, alongTailZR]
        congr 1
        funext j₀
        have := key j₀
        rw [ite_eq_left_of_eq_true _ _ (eq_true ht)] at this
        exact this
      · have hall : ¬ ∀ i : Fin (d + 1), (k i).val < S i := fun h => ht fun i => h i.succ
        rw [ite_eq_right_of_eq_false _ _ (eq_false hall)]
        have : (fun j₀ : ZMod (T 0) => tensorZR d (fun i => T i.succ) (fun i => T i.succ)
            (fun i => (fun u k => if k.val < S i.succ then u (k.val : ZMod (S i.succ)) else 0) ∘ B i.succ)
            (fun j' => v (Fin.cons j₀ j')) (Fin.tail k)) = 0 := by
          funext j₀; rw [key j₀, ite_eq_right_of_eq_false _ _ (eq_false ht)]; rfl
        erw [this, hB 0]; rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
      have hall : ¬ ∀ i : Fin (d + 1), (k i).val < S i := fun h => h0 (h 0)
      rw [ite_eq_right_of_eq_false _ _ (eq_false hall)]

end IntegerMultBounds.Resampling.PaddedTensor
