module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryLoopData

/-!
# One fixed program executes a stream of elementary routing configurations

The loop is controlled by the raw configuration tape. Its code and tape bank do
not depend on the number of calls or their coordinate indices. Every iteration
executes the loader, elementary permutation and cleanup proved in ElementaryCall.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

structure ElementaryLoopReady {t₀ T A : ℕ} (rg : LayReg t₀ → Fin T)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (R : Fin T → List (Fin (A + 4))) (n rows B : ℕ) : Prop where
  shared : ElementarySharedCfg rg R n (rows * 2 ^ n) B 0
  empty : ∀ key, R (elementaryConfigTarget rg hd key) = []
  pay0 : R (rg (.sw (reg pay))) = []
  private0 : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → R (rg (.sw j)) = []
  other : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
    ∀ x ∈ R (rg (.sw (reg i))), x ≠ blank ∧ x.val < prime + 4

theorem ElementaryLoopReady.congr {t₀ T A : ℕ} {rg : LayReg t₀ → Fin T}
    {hd : Fin 5 → Fin t₀} {pay : Fin t₀} {R R' : Fin T → List (Fin (A + 4))} {n rows B : ℕ}
    (h : ElementaryLoopReady rg hd pay R n rows B)
    (hkeep : ∀ r, r ≠ .str → R' (rg r) = R (rg r)) :
    ElementaryLoopReady rg hd pay R' n rows B := by
  refine ⟨h.shared.congr (fun r hr _ _ => hkeep r hr), ?_, ?_, ?_, ?_⟩
  · intro key
    have hk := h.empty key
    rcases elementaryConfigTarget_role rg hd key with ⟨j, hj⟩ | hj
    · rw [hj] at hk ⊢
      rw [hkeep _ (by simp)]
      exact hk
    · rw [hj] at hk ⊢
      rw [hkeep _ (by simp)]
      exact hk
  · rw [hkeep _ (by simp)]
    exact h.pay0
  · intro j hj
    rw [hkeep _ (by simp)]
    exact h.private0 j hj
  · intro i hi hk
    rw [hkeep _ (by simp)]
    exact h.other i hi hk

variable {t₀ T Q K : ℕ} {U P : Type}

noncomputable def elementaryLoopBody (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T) (config saved : Fin T) :
    Pr P T Q (prime + K) U :=
  .seq (elementaryCallProgram rg hrg hd pay hhd hQ hT config saved) (.act (peekR config))

noncomputable def elementaryLoopProgram (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T) (config saved : Fin T) :
    Pr P T Q (prime + K) U :=
  .seq (.act (peekR config)) (.loop (·.flag) (elementaryLoopBody rg hrg hd pay hhd hQ hT config saved))

/-- The loop invariant includes all raw metadata, restored scratch and exact costs. -/
theorem elementaryLoop_loop_exec {n rows B : ℕ}
    (body : P → Pr P T Q (prime + K) U) (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ j, hd j ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q) (hT : swapT t₀ ≤ T)
    (config saved : Fin T) (hcs : config ≠ saved)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (hrows : 0 < rows) (hB : 1 ≤ B) (ds : List (ElementaryInstruction n))
    (hvalid : ∀ d ∈ ds, d.Valid rows B)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = []) (hready : ElementaryLoopReady rg hd pay S.R n rows B)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rows * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8)
    (hstream : S.R (rg .str) = l.flatten) (hinput : S.R config = elementaryFrames ds)
    (hflag : v.flag = (elementaryFrames (A := prime + K) ds).head?.isSome) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ elementaryLoopCost rg hd config saved rows B S ds l ∧
      Exec body (.loop (·.flag) (elementaryLoopBody rg hrg hd pay hhd hQ hT config saved)) (mk v S) m
        (mk v' { S with R := elementaryLoopBank S.R rg config saved rows ds l }) := by
  induction ds generalizing v S l with
  | nil =>
    refine ⟨v, 1, rfl, by simp [elementaryLoopCost], ?_⟩
    exact Exec.loop_false (by simpa only [elementaryFrames, List.head?_nil, Option.isSome_none, mk_var] using hflag)
  | cons d ds ih =>
    have hdv := hvalid d (by simp)
    let l₁ := moveRecs (d.rank rows) l
    let S₁ : Stacks T (prime + K) :=
      { S with R := elementaryStepBank S.R rg config saved d rows (elementaryFrames ds) l }
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := elementaryCall_exec body rg hrg hd pay hhd hpay hQ hT
      config saved hcs hconfig hsaved d.target d.source d.source_ne hrows hB d.headers hdv.1 hdv.2
      (elementaryFrames ds) v S hL hready.shared hready.empty hready.pay0 hready.private0 hready.other
      l hl hlB h8 hstream hinput
    have hinput₁ : S₁.R config = elementaryFrames ds := by
      simp [S₁, elementaryStepBank, Function.update_of_ne (hconfig .str), Function.update_of_ne hcs]
    let v₂ := { v₁ with flag := (elementaryFrames (A := prime + K) ds).head?.isSome }
    have hpeek : (peekR config : Act T Q (prime + K) U).run (mk v₁ S₁) = mk v₂ S₁ := by
      simp only [peekR_run, hinput₁]
      rfl
    have hready₁ : ElementaryLoopReady rg hd pay S₁.R n rows B :=
      hready.congr (elementaryStepBank_keep S.R rg hrg config saved hconfig hsaved d rows _ l)
    have hl₁ : l₁.length = rows * 2 ^ n := length_moveRecs _ _
    have hmem : ∀ r ∈ l₁, r ∈ l := fun r hr => mem_moveRecs _ hl hr
    obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := ih (fun d hd => hvalid d (by simp [hd])) v₂ S₁ hL hready₁
      l₁ hl₁ (fun r hr => hlB r (hmem r hr)) (fun r hr => h8 r (hmem r hr))
      (by simp [S₁, elementaryStepBank, l₁]) hinput₁ rfl
    have hf : v.flag = true := by
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (d.frame_ne_nil (A := prime + K))
      simpa only [elementaryFrames, hx, List.cons_append, List.head?_cons, Option.isSome_some] using hflag
    have hebody := Exec.seq he₁ (hpeek ▸ Exec.act (body := body) (peekR config) (mk v₁ S₁))
    have hex := Exec.loop_true (body := body) (f := (·.flag)) (by simpa only [mk_var] using hf) hebody he₃
    refine ⟨v₃, m₁ + m₃ + 2, hu₃.trans hu₁, ?_, Exec.cast hex (by omega) rfl⟩
    change ((m₁ + m₃ + 2 : ℕ) : ℝ) ≤
      elementaryStepPrice rg hd config saved rows B S d (elementaryFrames ds) + 2 +
        elementaryLoopCost rg hd config saved rows B S₁ ds l₁
    change (m₁ : ℝ) ≤ elementaryStepPrice rg hd config saved rows B S d (elementaryFrames ds) at hm₁
    rw [Nat.cast_add, Nat.cast_add]
    norm_num only [Nat.cast_ofNat]
    linarith only [hm₁, hm₃]

end IntegerMultBounds.MathlibTM2.Routing
