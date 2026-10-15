module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlAllFibers
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlWorkspace

/-! # All CRT fibers with a returned arithmetic workspace -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM
variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Allocate the arithmetic variables, execute all fibers, then return them. -/
def crtControlAllFibersWorkspace (rg : TblR 10 → Fin T) (e : Fin 14 → Fin T)
    (fwd : Bool) : Pr P T Q A U :=
  .seq (crtControlWorkspaceInit rg)
    (.seq (crtControlAllFibers rg e fwd) (crtControlWorkspaceClear rg))

theorem crtControlAllFibersWorkspace_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    (e : Fin 14 → Fin T) (he : Function.Injective e) (hrge : ∀ r j, rg r ≠ e j)
    {W w L : ℕ} (hW : 0 < W) (hL : L ≤ W)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (fs : List CrtControlField) (M S μ n k : ℕ) (fwd : Bool)
    (hfields : ∀ f ∈ fs, 0 < f.place ∧ f.place < 2 ^ W ∧ f.bound < 2 ^ W ∧
      f.weight < 2 ^ W ∧ f.weight ≤ M)
    (hbudget : ∀ F < 2 ^ L, F * M < 2 ^ W)
    (hS : 0 < S) (hSlt : S < 2 ^ W) (hμ : μ < 2 ^ W)
    (hprod : ∀ F < 2 ^ L, μ * crtControlValue fs F < 2 ^ W)
    (slots : ℕ → List (List (Fin (A + 4))))
    (hslots : ∀ F < 2 ^ L, (slots F).length = n ∧ ∀ x ∈ slots F, x.length = k)
    (R : Regs T A) (htape : R (e 0) = crtControlTape W fs) (hsave : R (e 1) = [])
    (hmod : R (e 2) = binSyms W S) (hmul : R (e 3) = binSyms W μ)
    (hpadding : n = S + (R (e 4)).length) (hslot : (R (e 5)).length = k)
    (hexponent : (R (e 8)).length = L)
    (hclean : ∀ j : Fin 14, 9 ≤ j.val → R (e j) = [])
    (hsource : R (e 6) = (List.range (2 ^ L)).flatMap (fun F => (slots F).flatten))
    (hacc : R (e 7) = [])
    (hwr : R (rg .wr) = wl) (hwn : R (rg .wn) = nl)
    (hv : ∀ i, R (rg (.v i)) = []) (hz : ∀ j, R (rg (.z j)) = [])
    (hbankacc : R (rg .acc) = []) :
    crtRuns body (crtControlAllFibersWorkspace rg e fwd) R
      (Function.update R (e 6) ((List.range (2 ^ L)).flatMap (crtControlAllOut fs S μ fwd slots)))
      ((10 * (4 * W + 4) + 1 + 10 * tblC W w) +
        crtControlAllCost fs.length W w L S n k + (10 * (2 * W + 2) + 1)) := by
  have hinit := crtControlWorkspaceInit_runs (body := body) hrg hW wl nl hwl hnl hw
    R hwr hwn hv hz
  rw [hbankacc] at hinit
  have hpass := crtControlAllFibers_runs (body := body) hrg e he hrge hW hL wl nl hwl hnl hw
    fs M S μ n k fwd hfields hbudget hS hSlt hμ hprod slots hslots R htape hsave hmod hmul
    hpadding hslot hexponent hclean hsource hacc
  let out := (List.range (2 ^ L)).flatMap (crtControlAllOut fs S μ fwd slots)
  let R' := Function.update R (e 6) out
  let st := crtControlState (crtControlBoundary fs (2 ^ L)) 0 true ([] : List (Fin (A + 4)))
  have hout : Function.update (Function.update (crtBankOverlay rg R (tblRho W wl nl st))
      (e 7) []) (e 6) out = crtBankOverlay rg R' (tblRho W wl nl st) := by
    funext j
    by_cases hj : ∃ r, rg r = j
    · obtain ⟨r, rfl⟩ := hj
      simp [crtBankOverlay_on hrg, hrge]
    · have hj' : ∀ r, rg r ≠ j := by simpa using hj
      simp only [crtBankOverlay_off _ _ _ _ hj', R', Function.update_apply]
      split_ifs <;> simp_all
  have hclear := crtControlWorkspace_restore (body := body) hrg W wl nl st R'
    (by intro i; simpa [R', hrge] using hv i)
    (by intro j; simpa [R', hrge] using hz j)
    (by simpa [R', hrge] using hwr) (by simpa [R', hrge] using hwn)
    (by simp [R', st, crtControlState, hrge, hbankacc])
  have hpass' := crtRuns_congr hpass hout
  exact crtRuns_mono (crtRuns_seq hinit (crtRuns_seq hpass' hclear)) (by omega)

end IntegerMultBounds.MathlibTM2.Fast
