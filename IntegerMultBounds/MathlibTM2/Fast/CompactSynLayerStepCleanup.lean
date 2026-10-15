module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisRefresh

/-! Restored legacy files commute with the compact bank, enabling actual final cleanup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- Updating a register outside the embedded image commutes with overwriting that image. -/
theorem compactEmbExt_update_off {T T' : ℕ} {β : Type} (e : Fin T → Fin T')
    (f : Fin T → β) (R : Fin T' → β) (x : Fin T') (v : β) (hx : ∀ i,e i≠x) :
    embExt e f (Function.update R x v)=Function.update (embExt e f R) x v := by
  funext y
  by_cases hy : y=x
  · subst y
    rw [embExt_off f _ hx,Function.update_self,Function.update_self]
  · simp only [Function.update_of_ne hy]
    cases h : embInv e y <;> simp only [embExt,h,Function.update_of_ne hy]

/-- Updating an embedded register is the same update in the replacement file. -/
theorem compactEmbExt_update_image {T T' : ℕ} {β : Type} (e : Fin T → Fin T')
    (he : Function.Injective e) (f : Fin T → β) (R : Fin T' → β) (i : Fin T) (v : β) :
    Function.update (embExt e f R) (e i) v=embExt e (Function.update f i v) R := by
  funext y
  by_cases hy : y=e i
  · subst y
    rw [Function.update_self,embExt_apply he,Function.update_self]
  · rw [Function.update_of_ne hy]
    cases h : embInv e y with
    | none => simp only [embExt,h]
    | some j =>
      have hj : j≠i := by intro hh; subst j; exact hy (embInv_some h).symm
      simp only [embExt,h,Function.update_of_ne hj]

/-- A second overwrite of the same image replaces the first one completely. -/
theorem compactEmbExt_overwrite {T T' : ℕ} {β : Type} (e : Fin T → Fin T')
    (f g : Fin T → β) (R : Fin T' → β) : embExt e f (embExt e g R)=embExt e f R := by
  funext y
  cases h : embInv e y <;> simp only [embExt,h]

/-- Seven disjoint private updates commute with an arbitrary embedded-file overwrite. -/
theorem compactEmbExt_setup7 {T T' : ℕ} (e : Fin T → Fin T')
    (f : Fin T → List (Fin (A+4))) (R : Fin T' → List (Fin (A+4)))
    (dst : Fin 7 → Fin T') (values : Fin 7 → ℕ) (hdisj : ∀ j i,e i≠dst j) :
    embExt e f (compactSetupUpdate7 R dst values)=compactSetupUpdate7 (embExt e f R) dst values := by
  have hupdate (R : Fin T' → List (Fin (A+4))) (j : Fin 7) (xs : List (Fin (A+4))) :=
    compactEmbExt_update_off e f R (dst j) xs (hdisj j)
  simp only [compactSetupUpdate7,hupdate]

lemma compactSynLayerCleanup_commute
    (f : Fin (nT SXReg) → List (Fin (A+4)))
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (values : Fin 7 → ℕ) :
    embExt compactLegacyReg f (compactSetupUpdate7 R compactBasisRefreshDst values)=
      compactSetupUpdate7 (embExt compactLegacyReg f R) compactBasisRefreshDst values :=
  compactEmbExt_setup7 compactLegacyReg f R compactBasisRefreshDst values
    (fun j i => compactLegacyReg_ne_compact_bc i (.work (compactBasisRefreshWork j)))

/-- Final cleanup restores the arbitrary background while keeping the restored legacy file. -/
theorem compactSynLayerCleanup_runs (body : P → Pr P (nT CompactHostBReg) Q A U)
    (f : Fin (nT SXReg) → List (Fin (A+4)))
    (R : Fin (nT CompactHostBReg) → List (Fin (A+4))) (values : Fin 7 → ℕ)
    (hblank : ∀ i,R (compactBasisRefreshDst i)=[]) :
    LayRuns body compactBasisRefreshCleanup
      (embExt compactLegacyReg f (compactSetupUpdate7 R compactBasisRefreshDst (compactZeroTail values)))
      (embExt compactLegacyReg f R) (compactClear7Cost (compactZeroTail values)) := by
  rw [compactSynLayerCleanup_commute]
  apply compactBasisRefreshCleanup_runs
  intro j
  have hoff : embExt compactLegacyReg f R (compactBasisRefreshDst j)=R (compactBasisRefreshDst j) :=
    embExt_off f R (fun i => compactLegacyReg_ne_compact_bc i (.work (compactBasisRefreshWork j)))
  exact hoff.trans (hblank j)

end
end IntegerMultBounds.MathlibTM2.Fast
