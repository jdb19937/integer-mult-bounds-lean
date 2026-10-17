module

public import IntegerMultBounds.Networks.Certificates.T16.Streams.Model

/-! Soundness of the eight-stream check: an accepted program is `M target` on every stream, for
every operator homomorphism `M` and every stream value. The invariant writes each current stream
as its frame operator applied to an integer combination of the inputs with their start frames
removed. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Streams

open Multiplicative

variable {S : Type*} [AddCommGroup S] [Module ℂ S]

theorem op_add (M : Op S) (a b : Fin 73 → ZMod 4) (y : S) :
    M (ofAdd (a + b)) y = M (ofAdd a) (M (ofAdd b) y) := by
  rw [ofAdd_add, map_mul, Module.End.mul_apply]

theorem op_zero (M : Op S) (y : S) : M (ofAdd 0) y = y := by
  rw [ofAdd_zero, map_one, Module.End.one_apply]

/-- Each stream as its frame operator on an integer combination of de-framed inputs. -/
def value (M : Op S) (start : Fin 8 → Vec) (σ : CState) (x₀ : Fin 8 → S) (i : Fin 8) : S :=
  M (ofAdd (σ.frame i).toFun) (∑ j, σ.chain i j • M (ofAdd (start j).neg.toFun) (x₀ j))

theorem value_init (M : Op S) (start : Fin 8 → Vec) (x₀ : Fin 8 → S) :
    value M start ⟨start, identityChain⟩ x₀ = x₀ := by
  funext i
  simp only [value, identityChain, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [← op_add, Vec.toFun_neg, add_neg_cancel, op_zero]

theorem value_phase (M : Op S) (start : Fin 8 → Vec) (σ : CState) (x₀ : Fin 8 → S)
    (s : Fin 8) (v : Vec) :
    (Event.phase s v).run M (value M start σ x₀) =
      value M start ⟨Function.update σ.frame s ((σ.frame s).add v), σ.chain⟩ x₀ := by
  funext i
  simp only [Event.run]
  by_cases h : i = s
  · subst h
    simp only [Function.update_self, value, Vec.toFun_add]
    rw [add_comm, op_add]
  · simp only [Function.update_of_ne h, value]

theorem value_shear (M : Op S) (start : Fin 8 → Vec) (σ : CState) (x₀ : Fin 8 → S)
    (d s : Fin 8) (c : ℤ) (hf : σ.frame d = σ.frame s) :
    (Event.shear d s c).run M (value M start σ x₀) =
      value M start ⟨σ.frame, Function.update σ.chain d
        (fun j => σ.chain d j + c * σ.chain s j)⟩ x₀ := by
  funext i
  simp only [Event.run]
  by_cases h : i = d
  · subst h
    simp only [Function.update_self, value]
    rw [hf]
    simp only [add_smul, mul_smul, Finset.sum_add_distrib, map_add, ← Finset.smul_sum, map_zsmul]
  · simp only [Function.update_of_ne h, value]

theorem value_exchange (M : Op S) (start : Fin 8 → Vec) (σ : CState) (x₀ : Fin 8 → S)
    (p : Fin 4) :
    (Event.exchange p).run M (value M start σ x₀) =
      value M start ⟨Function.update (Function.update σ.frame (pairX p) (σ.frame (pairY p)))
          (pairY p) (σ.frame (pairX p)),
        Function.update (Function.update σ.chain (pairX p) (σ.chain (pairY p))) (pairY p)
          (fun j => -σ.chain (pairX p) j)⟩ x₀ := by
  have hxy := pairX_ne_pairY p
  funext i
  simp only [Event.run]
  by_cases hy : i = pairY p
  · subst hy
    simp only [Function.update_self, value]
    simp only [neg_smul, Finset.sum_neg_distrib, map_neg]
  · by_cases hx : i = pairX p
    · subst hx
      simp only [Function.update_of_ne hxy, Function.update_self, value]
    · simp only [Function.update_of_ne hy, Function.update_of_ne hx, value]

theorem value_check (M : Op S) (start : Fin 8 → Vec) {σ σ' : CState} (x₀ : Fin 8 → S)
    {e : Event} (h : e.check σ = some σ') :
    e.run M (value M start σ x₀) = value M start σ' x₀ := by
  cases e with
  | phase s v =>
    simp only [Event.check, Option.some.injEq] at h
    subst h
    exact value_phase M start σ x₀ s v
  | shear d s c =>
    simp only [Event.check] at h
    split_ifs at h with hf
    simp only [Option.some.injEq] at h
    subst h
    exact value_shear M start σ x₀ d s c hf
  | exchange p =>
    simp only [Event.check, Option.some.injEq] at h
    subst h
    exact value_exchange M start σ x₀ p

theorem value_checkRun (M : Op S) (start : Fin 8 → Vec) (x₀ : Fin 8 → S) :
    ∀ {es : List Event} {σ σ' : CState}, checkRun es σ = some σ' →
      run M es (value M start σ x₀) = value M start σ' x₀
  | [], σ, σ', h => by
    simp only [checkRun, Option.some.injEq] at h
    subst h
    rfl
  | e :: es, σ, σ', h => by
    simp only [checkRun] at h
    cases hc : e.check σ with
    | none => simp [hc] at h
    | some τ =>
      rw [hc, Option.bind_some] at h
      simp only [run]
      rw [value_check M start x₀ hc]
      exact value_checkRun M start x₀ h

/-- **Soundness.** An accepted stream program is `M target` on every stream. -/
theorem run_of_accepts (M : Op S) {es : List Event} {start : Fin 8 → Vec} {target : Vec}
    (h : accepts es start target = true) (x₀ : Fin 8 → S) :
    run M es x₀ = fun i => M (ofAdd target.toFun) (x₀ i) := by
  unfold accepts at h
  split at h
  · rename_i σ hσ
    have hall := List.all_eq_true.mp h
    have hframe : ∀ i, σ.frame i = (start i).add target := fun i => by
      have := hall i (List.mem_finRange i)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    have hchain : σ.chain = identityChain := by
      funext i j
      have := hall i (List.mem_finRange i)
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
      exact this.2 j (List.mem_finRange j)
    rw [← value_init M start x₀, value_checkRun M start x₀ hσ]
    funext i
    simp only [value, hchain, hframe, identityChain, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Vec.toFun_add, Vec.toFun_neg, add_comm, op_add, ← op_add M (start i).toFun, add_neg_cancel,
      op_zero]
  · simp at h

end IntegerMultBounds.Networks.Certificates.T16.Streams
