module

public import IntegerMultBounds.MathlibTM2.Fast.DistPrim
public import IntegerMultBounds.MathlibTM2.Fast.SrcStage

/-!
# Register files of the converter into the source transform

The converter (`Fast/DistSrc.lean`) runs on the parameter layout `rg : TblR pmNV → Fin T`, the
registers of the source transform `sg : SrcR t₀ → Fin T` (`Fast/SrcRegs.lean`) and its own
registers `io : DsX → Fin T`. The last two form one family `DsY t₀` (`dsGY sg io`), and a register
file of the machine is `dsF rg g R X W wl σ`: the parameter layout carrying the variables `σ`
(words of `W` bits, `wl` on `wr` and `wn`), the family carrying `X : DsY t₀ → List _`, every other
register `R`.

The wrappers `dsF_*` restate the primitive contracts in this form: a register of the family
changes as an update of `X`, a table step as a change of `σ`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- The converter's own registers: the inputs `uW` (`Wt` symbols) and `uw` (`w` symbols), the
loop counter `uD`, spares, and the outputs for the synthetic transform and its layout. -/
inductive DsX
  | uW | uw | uD | tm | xT | xS | tR | uq | ut | tb | tx | rR | lN | lL | lK | lD | lB | lW | lE
  deriving DecidableEq

noncomputable section

/-- The registers of the source transform and of the converter. -/
inductive DsY (t₀ : ℕ)
  | s (x : SrcR t₀)
  | o (x : DsX)
  deriving DecidableEq

end

section File

variable {T A t₀ : ℕ}

/-- The register map of `DsY`. -/
def dsGY (sg : SrcR t₀ → Fin T) (io : DsX → Fin T) : DsY t₀ → Fin T
  | .s x => sg x
  | .o x => io x

/-- The register layouts: injective and pairwise disjoint. -/
structure DsLay (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) : Prop where
  irg : Function.Injective rg
  ig : Function.Injective g
  disj : ∀ r y, rg r ≠ g y

/-- The register file of the machine. -/
noncomputable def dsF (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) (R : Regs T A)
    (X : DsY t₀ → List (Fin (A + 4))) (W : ℕ) (wl : List (Fin (A + 4))) (σ : Fin pmNV → ℕ) :
    Regs T A :=
  dsOv rg (dsOv g R X) (tblRho W wl wl ⟨σ, []⟩)

variable {rg : TblR pmNV → Fin T} {g : DsY t₀ → Fin T}

theorem dsF_g (h : DsLay rg g) (R : Regs T A) (X : DsY t₀ → List (Fin (A + 4))) (W : ℕ) (wl)
    (σ : Fin pmNV → ℕ) (y : DsY t₀) : dsF rg g R X W wl σ (g y) = X y := by
  rw [dsF, dsOv_off _ _ (fun r => h.disj r y), dsOv_rg h.ig]

theorem dsF_upd (h : DsLay rg g) (R : Regs T A) (X : DsY t₀ → List (Fin (A + 4))) (W : ℕ) (wl)
    (σ : Fin pmNV → ℕ) (y : DsY t₀) (v : List (Fin (A + 4))) :
    Function.update (dsF rg g R X W wl σ) (g y) v = dsF rg g R (Function.update X y v) W wl σ := by
  rw [dsF, dsOv_update _ _ (fun r => h.disj r y), dsOv_update_on h.ig]
  rfl

end File

/-! ### Wrappers -/

section Wrap

variable {T Q A t₀ : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {g : DsY t₀ → Fin T} (h : DsLay rg g) (R : Regs T A) {W : ℕ} (wl : List (Fin (A + 4)))
  (X : DsY t₀ → List (Fin (A + 4))) (σ : Fin pmNV → ℕ)
include h

theorem dsF_un (x : Fin pmNV) (y : DsY t₀) (hx : σ x < 2 ^ W) {l : List (Fin (A + 4))}
    (hy : X y = l) :
    dsRuns body (dsUn rg x (g y)) (dsF rg g R X W wl σ)
      (dsF rg g R (Function.update X y (List.replicate (σ x) tick ++ l)) W wl σ)
      (W * (4 * σ x + 11) + 2 * σ x + 6) := by
  have s := ds_un (body := body) h.irg (fun r => h.disj r y) wl wl ⟨σ, []⟩ x hx (dsOv g R X)
  dsimp only at s
  rw [dsOv_rg h.ig, dsOv_update_on h.ig, hy] at s
  exact s

theorem dsF_code {c : TblCode pmNV} {σ' : Fin pmNV → ℕ} {K : ℕ}
    (hc : TblDo A W W c ⟨σ, []⟩ (· = ⟨σ', []⟩) K) (hσ : ∀ j, σ j < 2 ^ W)
    (hwl : wl.length = W) :
    dsRuns body (tblCompile rg c) (dsF rg g R X W wl σ) (dsF rg g R X W wl σ') (K * tblC W W) :=
  ds_code h.irg wl wl hwl hwl le_rfl hc hσ (dsOv g R X)

theorem dsF_load (y : DsY t₀) (x : Fin pmNV) (hwl : wl.length = W) :
    dsRuns body (dsLoad rg (g y) x) (dsF rg g R X W wl σ)
      (dsF rg g R X W wl (Function.update σ x (X y).length))
      (2 * W + 2 + ((X y).length * (4 * W + 10) + 4 * W + 8)) := by
  have s := ds_load (body := body) h.irg (fun r => h.disj r y) wl hwl σ x (dsOv g R X)
  rw [dsOv_rg h.ig] at s
  exact s

theorem dsF_step (y : DsY t₀) {c : TblCode pmNV} {x K : ℕ}
    (hc : TblDo A W W c ⟨σ, []⟩ (DsPost σ x) K)
    (hσ0 : ∀ j : Fin pmNV, 31 ≤ j.val → j.val < 38 → σ j = 0) (hσ : ∀ j, σ j < 2 ^ W)
    (hwl : wl.length = W) {l : List (Fin (A + 4))} (hy : X y = l) :
    dsRuns body (dsStep rg c (g y)) (dsF rg g R X W wl σ)
      (dsF rg g R (Function.update X y (List.replicate x tick ++ l)) W wl σ)
      (dsStepCost W K x) := by
  have s := ds_step (body := body) h.irg (fun r => h.disj r y) wl hwl hc hσ0 hσ (dsOv g R X)
  rw [dsOv_rg h.ig, dsOv_update_on h.ig, hy] at s
  exact s

theorem dsF_stepB (yE yL : DsY t₀) (hEL : yE ≠ yL) {c : TblCode pmNV} {x K : ℕ}
    (hc : TblDo A W W c ⟨σ, []⟩ (DsPost σ x) K)
    (hσ0 : ∀ j : Fin pmNV, 31 ≤ j.val → j.val < 38 → σ j = 0) (hσ : ∀ j, σ j < 2 ^ W)
    (hwl : wl.length = W) {WL : ℕ} (hWWL : W ≤ WL) (hE : X yE = []) (hL : (X yL).length = WL) :
    dsRuns body (dsStepB rg c (g yE) (g yL)) (dsF rg g R X W wl σ)
      (dsF rg g R (Function.update X yE (binSyms WL x)) W wl σ) (dsStepBCost W K WL) := by
  have s := ds_stepB (body := body) h.irg (fun r => h.disj r yE) (fun r => h.disj r yL)
    (h.ig.ne hEL) wl hwl hc hσ0 hσ hWWL (dsOv g R X) (by rw [dsOv_rg h.ig, hE])
    (by rw [dsOv_rg h.ig, hL])
  rw [dsOv_update_on h.ig] at s
  exact s

theorem dsF_ucopy (y₁ y₂ yt : DsY t₀) (h12 : y₁ ≠ y₂) (h1t : y₁ ≠ yt) (h2t : y₂ ≠ yt) {c : ℕ}
    (h1 : (X y₁).length = c) {l : List (Fin (A + 4))} (h2 : X y₂ = l) (ht : X yt = []) :
    dsRuns body (ucopy (g y₁) (g y₂) (g yt)) (dsF rg g R X W wl σ)
      (dsF rg g R (Function.update X y₂ (List.replicate c tick ++ l)) W wl σ) (4 * c + 4) := by
  have s := ds_ucopy (body := body) (h.ig.ne h12) (h.ig.ne h1t) (h.ig.ne h2t)
    (dsF rg g R X W wl σ) (by rw [dsF_g h, ht])
  rw [dsF_g h, dsF_g h, dsF_upd h, h1, h2] at s
  exact s

theorem dsF_umulSym (c : ℕ) (z : Fin (A + 4)) (y₁ y₂ yt : DsY t₀) (h12 : y₁ ≠ y₂) (h1t : y₁ ≠ yt)
    (h2t : y₂ ≠ yt) {k : ℕ} (h1 : (X y₁).length = k) {l : List (Fin (A + 4))} (h2 : X y₂ = l)
    (ht : X yt = []) :
    dsRuns body (umulSym c z (g y₁) (g y₂) (g yt)) (dsF rg g R X W wl σ)
      (dsF rg g R (Function.update X y₂ (List.replicate (c * k) z ++ l)) W wl σ) (4 * k + 4) := by
  have s := ds_umulSym (body := body) c z (h.ig.ne h12) (h.ig.ne h1t) (h.ig.ne h2t)
    (dsF rg g R X W wl σ) (by rw [dsF_g h, ht])
  rw [dsF_g h, dsF_g h, dsF_upd h, h1, h2] at s
  exact s

theorem dsF_umul (y₁ y₂ y₃ t₁ t₂ : DsY t₀) (hreg : [y₁, y₂, y₃, t₁, t₂].Nodup) {k₁ k₂ : ℕ}
    (h1 : (X y₁).length = k₁) (h2 : (X y₂).length = k₂) {l : List (Fin (A + 4))} (h3 : X y₃ = l)
    (ht₁ : X t₁ = []) (ht₂ : X t₂ = []) :
    dsRuns body (dsUMul (g y₁) (g y₂) (g y₃) (g t₁) (g t₂)) (dsF rg g R X W wl σ)
      (dsF rg g R (Function.update X y₃ (List.replicate (k₁ * k₂) tick ++ l)) W wl σ)
      (k₁ * (4 * k₂ + 7) + 2 * k₁ + 4) := by
  have s := ds_umul (body := body) (a := g y₁) (b := g y₂) (c := g y₃) (t₁ := g t₁) (t₂ := g t₂)
    (by simpa using hreg.map h.ig) (dsF rg g R X W wl σ) (by rw [dsF_g h, ht₁])
    (by rw [dsF_g h, ht₂])
  rw [dsF_g h, dsF_g h, dsF_g h, dsF_upd h, h1, h2, h3] at s
  exact s

theorem dsF_bcopy (y₁ y₂ : DsY t₀) (h12 : y₁ ≠ y₂) {l₁ l₂ : List (Fin (A + 4))}
    (h1 : X y₁ = l₁) (h2 : X y₂ = l₂) :
    dsRuns body (bcopy (g y₁) (g y₂) (rg (.z 0)) (rg (.z 1))) (dsF rg g R X W wl σ)
      (dsF rg g R (Function.update X y₂ (l₁ ++ l₂)) W wl σ) (6 * l₁.length + 6) := by
  have hreg : [g y₁, g y₂, rg (.z 0), rg (.z 1)].Nodup := by
    have h01 : rg (.z 0) ≠ rg (.z 1) := h.irg.ne (by simp)
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_,
      List.nodup_singleton _⟩⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h.ig.ne h12, fun e => h.disj _ _ e.symm, fun e => h.disj _ _ e.symm⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => h.disj _ _ e.symm, fun e => h.disj _ _ e.symm⟩
    · simpa using h01
  have s := ds_bcopy (body := body) hreg (dsF rg g R X W wl σ) (by rw [dsF, dsOv_rg h.irg]; rfl)
    (by rw [dsF, dsOv_rg h.irg]; rfl)
  rw [dsF_g h, dsF_g h, dsF_upd h, h1, h2] at s
  exact s

theorem dsF_bclear (y : DsY t₀) {c : ℕ} (hy : (X y).length = c) :
    dsRuns body (bclear (g y)) (dsF rg g R X W wl σ)
      (dsF rg g R (Function.update X y []) W wl σ) (2 * c + 2) := by
  have s := ds_bclear (body := body) (g y) (dsF rg g R X W wl σ)
  rw [dsF_g h, dsF_upd h, hy] at s
  exact s

theorem dsF_uclear (y : DsY t₀) {c : ℕ} (hy : (X y).length = c) :
    dsRuns body (uclear (g y)) (dsF rg g R X W wl σ)
      (dsF rg g R (Function.update X y []) W wl σ) (2 * c + 2) := by
  have s := ds_uclear (body := body) (g y) (dsF rg g R X W wl σ)
  rw [dsF_g h, dsF_upd h, hy] at s
  exact s

theorem dsF_moveR (y₁ y₂ : DsY t₀) (h12 : y₁ ≠ y₂) {l₁ l₂ : List (Fin (A + 4))}
    (h1 : X y₁ = l₁) (h2 : X y₂ = l₂) :
    dsRuns body (moveR (g y₁) (g y₂) id) (dsF rg g R X W wl σ)
      (dsF rg g R (Function.update (Function.update X y₁ []) y₂ (l₁.reverse ++ l₂)) W wl σ)
      (2 * l₁.length + 2) := by
  have s := ds_moveR (body := body) (h.ig.ne h12) (dsF rg g R X W wl σ)
  rw [dsF_g h, dsF_g h, dsF_upd h, dsF_upd h, h1, h2] at s
  exact s

theorem dsF_narrow (x : Fin pmNV) (yL ytm ytb ytx yo : DsY t₀) (hreg : [yL, ytm, ytb, ytx, yo].Nodup)
    (htm : X ytm = []) (htb : X ytb = []) (htx : X ytx = []) {L : ℕ} (hL : (X yL).length = L)
    (hLW : L ≤ W) {l : List (Fin (A + 4))} (ho : X yo = l) :
    dsRuns body (dsNarrow rg x (g yL) (g ytm) (g ytb) (g ytx) (g yo)) (dsF rg g R X W wl σ)
      (dsF rg g R (Function.update X yo (binSyms L (σ x) ++ l)) W wl σ) (14 * W + 14) := by
  have s := ds_narrow (body := body) h.irg (x := x) (W := W) (by simpa using hreg.map h.ig)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro k (rfl | rfl | rfl | rfl | rfl) r <;> exact h.disj r _)
    wl wl ⟨σ, []⟩ (dsOv g R X) (by rw [dsOv_rg h.ig, htm]) (by rw [dsOv_rg h.ig, htb])
    (by rw [dsOv_rg h.ig, htx]) (by rw [dsOv_rg h.ig, hL]; exact hLW)
  dsimp only at s
  rw [dsOv_rg h.ig, dsOv_rg h.ig, dsOv_update_on h.ig, hL, ho] at s
  exact s

end Wrap

end IntegerMultBounds.MathlibTM2.Fast.TableVM
