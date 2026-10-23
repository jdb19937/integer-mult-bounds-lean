module

public import IntegerMultBounds.MathlibTM2.Routing.HeaderBankLayout

/-! Execute a finite canonical-header bank from live padded numeric operands.
All sources and shared scratch are restored; only the core outputs change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {N J Q A : ℕ} {P U : Type}

theorem headerBankJob_ready (dst : Fin J → Fin N) (L value : Fin J → ℕ) (j : Fin J)
    (bank : Fin (N + (J + 2)) → List (Fin (A + 4))) (hfit : value j < 2 ^ L j)
    (hsource : bank (headerAux ⟨j.val, by omega⟩) = binSyms (L j) (value j))
    (hdst : bank (headerCore (dst j)) = [])
    (htmp : bank (headerAux ⟨J, by omega⟩) = [])
    (hwork : bank (headerAux ⟨J + 1, by omega⟩) = []) :
    (headerBankJob dst L value j).Ready bank := by
  refine ⟨headerBankReg_injective dst j, hfit, hsource, ?_⟩
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  · exact hdst
  · exact htmp
  · exact hwork

theorem headerBank_exec (body : P → Pr P (N + (J + 2)) Q A U)
    (dst : Fin J → Fin N) (hdst : Function.Injective dst) (L value : Fin J → ℕ)
    (v : HS (N + (J + 2)) Q A U) (S : Stacks (N + (J + 2)) A)
    (hfit : ∀ j, value j < 2 ^ L j)
    (hsource : ∀ j, S.R (headerAux ⟨j.val, by omega⟩) = binSyms (L j) (value j))
    (hblank : ∀ j, S.R (headerCore (dst j)) = [])
    (htmp : S.R (headerAux ⟨J, by omega⟩) = [])
    (hwork : S.R (headerAux ⟨J + 1, by omega⟩) = []) :
    let jobs := List.ofFn (headerBankJob dst L value)
    ∃ v', v'.user = v.user ∧ Exec body (canonicalHeaderBatch jobs) (mk v S) (canonicalHeaderBatchCost jobs)
      (mk v' { S with R := canonicalHeadersGenerated S.R jobs }) := by
  apply canonicalHeaderBatch_exec
  · intro job hj other ho hne i
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ho
    apply headerBankReg_separate dst hdst j k
    intro he
    exact hne (congrArg (headerBankJob dst L value) he)
  · exact List.nodup_ofFn.mpr (headerBankJob_injective dst hdst L value)
  · intro job hj
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
    exact headerBankJob_ready dst L value j S.R (hfit j) (hsource j) (hblank j) htmp hwork

theorem headerBank_contents (dst : Fin J → Fin N) (hdst : Function.Injective dst) (L value : Fin J → ℕ)
    (bank : Fin (N + (J + 2)) → List (Fin (A + 4))) (j : Fin J) :
    canonicalHeadersGenerated bank (List.ofFn (headerBankJob dst L value)) (headerCore (dst j)) =
      (GrowingCounterData.advance (value j) []).map bitSymbol := by
  have hn : ((List.ofFn (headerBankJob dst L value)).map CanonicalHeaderJob.dst).Nodup := by
    rw [List.map_ofFn]
    apply List.nodup_ofFn.mpr
    intro i k he
    exact hdst (headerCore_injective he)
  exact canonicalHeadersGenerated_at bank _ hn (headerBankJob dst L value j) (List.mem_ofFn.mpr ⟨j, rfl⟩)

theorem headerBank_aux (dst : Fin J → Fin N) (L value : Fin J → ℕ)
    (bank : Fin (N + (J + 2)) → List (Fin (A + 4))) (i : Fin (J + 2)) :
    canonicalHeadersGenerated bank (List.ofFn (headerBankJob dst L value)) (headerAux i) = bank (headerAux i) := by
  apply canonicalHeadersGenerated_keep
  intro job hj
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hj
  exact (headerCore_aux (dst j) i).symm

end IntegerMultBounds.MathlibTM2.Routing
