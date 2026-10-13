module

public import IntegerMultBounds.Schoenhage.LayoutGenMain
public import IntegerMultBounds.Schoenhage.TransformGenRun
public import IntegerMultBounds.Schoenhage.AlphaLift

/-! The §6 layout-script writers on the word bank (`LayoutGen`): the 48-tape writer
(`LayoutGenMain.lgFwd`, `LayoutGenMain.lgUndo`) compiled to one primitive and placed on the
decoded parameters, named tape 7 for its output and free drivers' tapes for its scratch. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Spec.SignedRingProduct Resampling AxisDriver LayoutMachines TwistDescriptors
  LayoutGenRun LayoutGenMain

namespace LayoutGenWrap

/-- Where the writer's tape `i` sits among the drivers' tapes: the inputs on the decoded
`ℓ`, `K`, `w`, axis ticks, flags and `d - 1`, the output on named tape 7, scratch on free tapes. -/
def lslotV (i : ℕ) : ℕ :=
  if i < 6 then i else if i < 32 then i + 2 else if i = 32 then 135 else if i = 33 then 120 else
  if i = 34 then 136 else if i = 35 then 127 else if i = 36 then 126 else if i = 37 then 118 else
  if i = 38 then 7 else i - 5

theorem lslotV_lt : ∀ i : Fin 48, lslotV i.val < 160 := by decide

theorem lslotV_inj : ∀ i j : Fin 48, lslotV i.val = lslotV j.val → i = j := by decide

variable {A tL nL : ℕ}

/-- The writer's tapes in the word bank. -/
def lslot (tL nL : ℕ) (i : Fin 48) : Fin (4 + DB tL nL) :=
  drv tL nL ⟨lslotV i.val, by have := lslotV_lt i; unfold DB; omega⟩

theorem lslot_injective : Function.Injective (lslot tL nL) := fun i j h => by
  have := congrArg Fin.val (drv_injective h)
  exact lslotV_inj i j this

/-- A 48-tape writer as one primitive on the word bank. -/
noncomputable def lgOf (A tL nL : ℕ) (c : Cmd 0 48) : Cmd A (4 + DB tL nL) :=
  .prim (Prim.liftE (Nat.zero_le A) (Prim.ofHoare (compile (a := 0) (by decide) c).2 (by decide)))
    (lslot tL nL) lslot_injective

/-- The forward layout-script writer. -/
noncomputable def layoutGenFwd (A tL nL : ℕ) : Cmd A (4 + DB tL nL) := lgOf A tL nL lgFwd

/-- The undo layout-script writer. -/
noncomputable def layoutGenUndo (A tL nL : ℕ) : Cmd A (4 + DB tL nL) := lgOf A tL nL lgUndo

theorem lengthFlags_eq {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) :
    TransformParams.lengthFlags ℓ ts = pf ts ℓ := by
  have hℓ : 1 ≤ ℓ := hL.2.2.2
  have hts : ∀ t ∈ ts, t = 2 ^ (ℓ - 1) ∨ t = 2 ^ ℓ := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨a, ha, -⟩ := hL.1 _ ht
    have hax : axLen ts i = a := by
      simp only [axLen, List.getD_eq_getElem _ _ hi, ha, Nat.log_pow (by norm_num : 1 < 2)]
    rw [ha]
    rcases hL.2.1 i hi with h | h <;> rw [hax] at h <;> simp [h]
  exact TransformParams.flags_paper hℓ hts

set_option maxHeartbeats 16000000 in
/-- The decoded parameters, seen through the writer's slots, are the writer's start. -/
theorem decState_lslot {p d ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hD : ts.length = d - 1)
    (F : List Bool) (S6 : WTape) :
    Function.update (decState (tL := tL) (nL := nL) p d ℓ K w ts F) (drv tL nL (nm tL nL 6)) S6 ∘ lslot tL nL =
      lstart ℓ K w ts.length (pf ts ℓ) := by
  have hflags := lengthFlags_eq hL
  rw [decState_eq, update_wbank_nm]
  funext i
  fin_cases i <;> simp (config := {decide := true}) [lslot, lslotV, wbank, wst_drv, decoded, decStart,
    Function.update_apply, lstart, hflags, ← hD]

theorem upd_lslot (σ : Fin (4 + DB tL nL) → WTape) (v : WTape) :
    upd σ (lslot tL nL) (Function.update (σ ∘ lslot tL nL) 38 v) = Function.update σ (lslot tL nL 38) v := by
  refine upd_eq_of σ lslot_injective _ _ (fun i => ?_) (fun x hx => ?_)
  · by_cases hi : i = 38
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne (fun e => hi (lslot_injective e))]; rfl
  · rw [Function.update_of_ne (fun e => hx 38 e.symm)]

theorem lslot_out : lslot tL nL 38 = drv tL nL (nm tL nL 7) := rfl

theorem layoutGen_of {c : Cmd 0 48} {fwd : Bool} {ℓ K : ℕ} {ts : List ℕ} {p d w B : ℕ}
    (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hD : ts.length = d - 1)
    (hc : Runs c (lstart ℓ K w ts.length (pf ts ℓ))
      (· = Function.update (lstart ℓ K w ts.length (pf ts ℓ)) 38
        ⟨[], if fwd then layoutWords (2 ^ ℓ) w ts ℓ K else undoWords (2 ^ ℓ) w ts ℓ K⟩) B) :
    LayoutGen fwd (lgOf A tL nL c) ℓ K ts p d w B := by
  intro F S6
  obtain ⟨τ', k, hx, hq, hk⟩ := hc
  have hcomp := decState_lslot (tL := tL) (nL := nL) (p := p) (w := w) hL hD F S6
  have hT : HoareTo (compile (a := 0) (by decide) c).2
      (Function.update (decState (tL := tL) (nL := nL) p d ℓ K w ts F) (drv tL nL (nm tL nL 6)) S6 ∘ lslot tL nL)
      τ' k := by
    rw [hcomp]
    exact (compile_correct (by decide) hx).consequence (fun _ h => h) (fun _ h => h) le_rfl
  refine (runs_ofHoare_liftE (Nat.zero_le A) _ (by decide) lslot_injective hT).mono (fun τ h => ?_) hk
  rw [h, hq, ← hcomp, upd_lslot, lslot_out]

/-- `LayoutGen true`: the forward layout-script writer. -/
theorem layoutGen_fwd {ℓ K : ℕ} {ts : List ℕ} {p d w : ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hw : 1 ≤ w)
    (hD : ts.length = d - 1) :
    LayoutGen true (layoutGenFwd A tL nL) ℓ K ts p d w (lgFwdCost ℓ K w ts) :=
  layoutGen_of hL hD (by simpa using runs_lgFwd hL hw hL.2.2.1)

/-- `LayoutGen false`: the undo layout-script writer. -/
theorem layoutGen_undo {ℓ K : ℕ} {ts : List ℕ} {p d w : ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hw : 1 ≤ w)
    (hD : ts.length = d - 1) :
    LayoutGen false (layoutGenUndo A tL nL) ℓ K ts p d w (lgUndoCost ℓ K w ts) :=
  layoutGen_of hL hD (by simpa using runs_lgUndo hL hw hL.2.2.1)

end LayoutGenWrap

end IntegerMultBounds.Schoenhage
