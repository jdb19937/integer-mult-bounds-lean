module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynHybridRound
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainBootstrapRuntime
public import IntegerMultBounds.MathlibTM2.Fast.SynFwd

/-! Stable runtime globals and the synthetic view on the expanded main machine. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
noncomputable section
variable {A : ℕ}

structure CompactSynReady (R : Fin compactMnT → List (Fin (A+4))) (M : ℕ) : Prop where
  blank : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 → R (compactMnLay (.bc (.inl z)))=[]
  depth : (R (compactMnLay (.bc (.inl (.work 13))))).length=Mult.Sizes.d M
  guard : (R (compactMnLay (.bc (.inl (.work 14))))).length=CompactReservationGrowth.guard M

theorem CompactSynReady.update_legacy {R : Fin compactMnT → List (Fin (A+4))} {M : ℕ}
    (h : CompactSynReady R M) (j : Fin mnT) (word : List (Fin (A+4))) :
    CompactSynReady (Function.update R (compactMnLegacyReg j) word) M where
  blank z h13 h14 := by
    rw [Function.update_of_ne (compactMnLegacyReg_ne_private j z).symm]
    exact h.blank z h13 h14
  depth := by rw [Function.update_of_ne (compactMnLegacyReg_ne_private j (.work 13)).symm]; exact h.depth
  guard := by rw [Function.update_of_ne (compactMnLegacyReg_ne_private j (.work 14)).symm]; exact h.guard

theorem CompactSynReady.update_io {R : Fin compactMnT → List (Fin (A+4))} {M : ℕ}
    (h : CompactSynReady R M) (word : List (Fin (A+4))) :
    CompactSynReady (Function.update R (compactMnRg (.src (.v .io))) word) M := by
  simpa only [compactMnLegacyReg_rg] using h.update_legacy (mnRg (.src (.v .io))) word

theorem CompactSynReady.update_wire {R : Fin compactMnT → List (Fin (A+4))} {M : ℕ}
    (h : CompactSynReady R M) (x : SynW) (word : List (Fin (A+4))) :
    CompactSynReady (Function.update R (compactSynDispatchReg x) word) M :=
  h.update_legacy (mnLayE (sreg x)) word

theorem compactSynReady_of_globals (M : ℕ) (hM : 2≤M)
    (R : Fin compactMnT → List (Fin (A+4)))
    (hg : CompactMainGlobals R (Mult.Sizes.p M) (Mult.Sizes.d M))
    (hb : ∀ z : CompactBReg,z≠.work 13 → z≠.work 14 → R (compactMnLay (.bc (.inl z)))=[]) :
    CompactSynReady R M := by
  obtain ⟨hd,hg⟩ := compactMainGlobals_runtime_lengths M hM R hg
  simp only [Function.comp_apply,compactMnLayerReg_private] at hd hg
  exact ⟨hb,hd,hg⟩

def compactSynView (R : Fin compactMnT → List (Fin (A+4))) :=
  (R ∘ compactMnLegacyReg) ∘ mnLayE

private theorem updateProjection {T T' : ℕ} (e : Fin T → Fin T') (he : Function.Injective e)
    (R : Fin T' → List (Fin (A+4))) (i : Fin T) (word : List (Fin (A+4))) :
    (Function.update R (e i) word) ∘ e=Function.update (R ∘ e) i word := by
  funext j
  by_cases hj : j=i
  · subst j; simp
  · simp [Function.update_of_ne,hj,he.ne hj]

theorem compactSynView_update_io (R : Fin compactMnT → List (Fin (A+4)))
    (word : List (Fin (A+4))) :
    compactSynView (Function.update R (compactMnRg (.src (.v .io))) word)=
      Function.update (compactSynView R) mnLio word := by
  have he := updateProjection (compactMnLegacyReg ∘ mnLayE)
    (compactMnLegacyReg_injective.comp mnLayE_inj) R mnLio word
  simpa only [Function.comp_apply,mnLayE_io,compactMnLegacyReg_rg,Function.comp_assoc,
    compactSynView] using he

theorem compactSynView_update_wire (R : Fin compactMnT → List (Fin (A+4)))
    (x : SynW) (word : List (Fin (A+4))) :
    compactSynView (Function.update R (compactSynDispatchReg x) word)=
      Function.update (compactSynView R) (sreg x) word :=
  updateProjection (compactMnLegacyReg ∘ mnLayE)
    (compactMnLegacyReg_injective.comp mnLayE_inj) R (sreg x) word

theorem compactSynView_io (R : Fin compactMnT → List (Fin (A+4)))
    (io io' park : List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (h : compactSynView R=synG (synIdle io park) v) :
    compactSynView (Function.update R (compactMnRg (.src (.v .io))) io')=
      synG (synIdle io' park) v := by
  rw [compactSynView_update_io,h,synG_update_out (lreg_out (by simp)),synIdle_update_io]

end
end IntegerMultBounds.MathlibTM2.Fast.Main
