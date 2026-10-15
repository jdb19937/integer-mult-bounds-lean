module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlReset

/-! # Initializing and returning the CRT arithmetic workspace

A fixed ten-variable bank is initialized from empty variable registers.
Width, auxiliary width, accumulator and external tapes are preserved.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def crtWorkspaceZeros (rg : TblR 10 → Fin T) : List (Fin 10) → Pr P T Q A U
  | [] => .act .done
  | i :: l => .seq (zeroBits (rg .wr) (rg (.v i)) (rg (.z 0))) (crtWorkspaceZeros rg l)

theorem crtWorkspaceZeros_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg) :
    ∀ (l : List (Fin 10)), l.Nodup → ∀ (R : Regs T A),
      (∀ i ∈ l, R (rg (.v i)) = []) → R (rg (.z 0)) = [] →
      crtRuns body (crtWorkspaceZeros rg l) R
        (fun k => if ∃ i ∈ l, rg (.v i) = k then binSyms (R (rg .wr)).length 0 else R k)
        (l.length * (4 * (R (rg .wr)).length + 4) + 1)
  | [], _, R, _, _ => by
      have h : crtRuns body (.act .done) R R 1 := by
        intro v S hS _
        subst R
        exact ⟨v, 1, rfl, le_rfl, Exec.act .done (mk v S)⟩
      simpa [crtWorkspaceZeros] using h
  | i :: l, hnd, R, hv, h0 => by
      have hnd' := List.nodup_cons.1 hnd
      have hz := crtZeroBits_runs (body := body)
        (hrg.ne (by simp : (TblR.wr : TblR 10) ≠ .v i))
        (hrg.ne (by decide : (TblR.wr : TblR 10) ≠ .z 0))
        (hrg.ne (by simp : (TblR.v i : TblR 10) ≠ .z 0)) R h0
      rw [hv i List.mem_cons_self, List.append_nil] at hz
      let R₁ := Function.update R (rg (.v i)) (binSyms (R (rg .wr)).length 0)
      have ih := crtWorkspaceZeros_runs hrg l hnd'.2 R₁ (fun j hj => by
        have hji : j ≠ i := fun h => hnd'.1 (h ▸ hj)
        simpa [R₁, hrg.eq_iff, hji] using hv j (List.mem_cons_of_mem _ hj))
        (by simpa [R₁, hrg.eq_iff] using h0)
      have hwr : R₁ (rg .wr) = R (rg .wr) := by simp [R₁, hrg.eq_iff]
      rw [hwr] at ih
      refine crtRuns_mono (crtRuns_congr (crtRuns_seq hz ih) ?_) (by simp; ring_nf; omega)
      funext k
      by_cases hk : ∃ j ∈ l, rg (.v j) = k
      · obtain ⟨j, hj, rfl⟩ := hk
        simp only [List.mem_cons, exists_eq_or_imp]
        rw [ite_eq_left (Or.inr ⟨j, hj, rfl⟩), ite_eq_left ⟨j, hj, rfl⟩]
      · rw [ite_eq_right hk]
        by_cases hki : rg (.v i) = k
        · subst k
          rw [ite_eq_left ⟨i, List.mem_cons_self, rfl⟩]
          simp [R₁]
        · have hne : ¬ ∃ j ∈ i :: l, rg (.v j) = k := by
            rintro ⟨j, hj, rfl⟩
            rcases List.mem_cons.1 hj with rfl | hj
            · exact hki rfl
            · exact hk ⟨j, hj, rfl⟩
          rw [ite_eq_right hne]
          simp [R₁, Ne.symm hki]

/-- Initialize every binary variable, then set the validity flag. -/
def crtControlWorkspaceInit (rg : TblR 10 → Fin T) : Pr P T Q A U :=
  .seq (crtWorkspaceZeros rg (List.finRange 10)) (tblCompile rg crtControlReset)

/-- Allocate the binary bank from empty variables and empty scratch. -/
theorem crtControlWorkspaceInit_runs {rg : TblR 10 → Fin T} (hrg : Function.Injective rg)
    {W w : ℕ} (hW : 0 < W) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W)
    (R : Regs T A) (hwr : R (rg .wr) = wl) (hwn : R (rg .wn) = nl)
    (hv : ∀ i, R (rg (.v i)) = []) (hz : ∀ j, R (rg (.z j)) = []) :
    crtRuns body (crtControlWorkspaceInit rg) R
      (crtBankOverlay rg R (tblRho W wl nl (crtControlState 0 0 true (R (rg .acc)))))
      (10 * (4 * W + 4) + 1 + 10 * tblC W w) := by
  have hinit := crtWorkspaceZeros_runs (body := body) hrg (List.finRange 10)
    (List.nodup_finRange _) R (fun i _ => hv i) (hz 0)
  rw [hwr, hwl] at hinit
  let R₀ : Regs T A := fun k => if ∃ i : Fin 10, rg (.v i) = k then binSyms W 0 else R k
  have hinit' : crtRuns body (crtWorkspaceZeros rg (List.finRange 10)) R R₀
      (10 * (4 * W + 4) + 1) := by simpa [R₀] using hinit
  let st : TblSt 10 A := ⟨fun _ => 0, R (rg .acc)⟩
  have hR₀ : ∀ r, R₀ (rg r) = tblRho W wl nl st r := by
    intro r
    cases r <;> simp [R₀, hrg.eq_iff, tblRho, st, hwr, hwn, hz]
  have hst : ∀ j, st.val j < 2 ^ W := by intro j; dsimp [st]; positivity
  have hreset := crtControlReset_runs (body := body) hrg hW wl nl hwl hnl hw st hst R₀ hR₀
  refine crtRuns_congr (crtRuns_seq hinit' hreset) ?_
  funext k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hk
    simp [crtBankOverlay_on hrg, st]
  · have hk' : ∀ r, rg r ≠ k := by simpa using hk
    simp [crtBankOverlay_off _ _ _ _ hk', R₀, show ¬∃ i, rg (.v i) = k from by
      rintro ⟨i, hi⟩; exact hk' (.v i) hi]

/-- Return a fixed list of physical registers to empty. -/
def crtWorkspaceClear : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | r :: rs => .seq (uclear r) (crtWorkspaceClear rs)

theorem crtWorkspaceClear_runs (W : ℕ) :
    ∀ (rs : List (Fin T)) (R : Regs T A), (∀ r ∈ rs, (R r).length ≤ W) →
      crtRuns body (crtWorkspaceClear rs) R (fun k => if k ∈ rs then [] else R k)
        (rs.length * (2 * W + 2) + 1)
  | [], R, _ => by
      have h : crtRuns body (.act .done) R R 1 := by
        intro v S hS _
        subst R
        exact ⟨v, 1, rfl, le_rfl, Exec.act .done (mk v S)⟩
      simpa [crtWorkspaceClear] using h
  | r :: rs, R, hlen => by
      have hc := crtClear_runs (body := body) r R
      let R₁ := Function.update R r []
      have ih := crtWorkspaceClear_runs W rs R₁ (fun j hj => by
        by_cases h : j = r
        · simp [R₁, h]
        · simpa [R₁, h] using hlen j (by simp [hj]))
      refine crtRuns_mono (crtRuns_congr (crtRuns_seq hc ih) ?_) ?_
      · funext k
        by_cases hk : k ∈ rs <;> by_cases hkr : k = r <;> simp [hk, hkr, R₁]
      · have := hlen r (by simp)
        simp only [List.length_cons]
        nlinarith

/-- Clearing the ten variables preserves width, accumulator, and spectators. -/
def crtControlWorkspaceClear (rg : TblR 10 → Fin T) : Pr P T Q A U :=
  crtWorkspaceClear ((List.finRange 10).map (fun i => rg (.v i)))

theorem crtControlWorkspaceClear_runs {rg : TblR 10 → Fin T} (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 10 A) (R : Regs T A)
    (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    crtRuns body (crtControlWorkspaceClear rg) R
      (fun k => if ∃ i : Fin 10, rg (.v i) = k then [] else R k)
      (10 * (2 * W + 2) + 1) := by
  have h := crtWorkspaceClear_runs (body := body) W
    ((List.finRange 10).map (fun i => rg (.v i))) R (by
      intro r hr
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
      simp [hR, tblRho, length_binSyms])
  simpa [crtControlWorkspaceClear] using h

/-- After a bank computation, clearing its variables restores the original
empty workspace, provided its accumulator and configuration were preserved. -/
theorem crtControlWorkspace_restore {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (W : ℕ) (wl nl : List (Fin (A + 4)))
    (st : TblSt 10 A) (R : Regs T A)
    (hv : ∀ i, R (rg (.v i)) = []) (hz : ∀ j, R (rg (.z j)) = [])
    (hwr : R (rg .wr) = wl) (hwn : R (rg .wn) = nl) (hacc : st.acc = R (rg .acc)) :
    crtRuns body (crtControlWorkspaceClear rg)
      (crtBankOverlay rg R (tblRho W wl nl st)) R (10 * (2 * W + 2) + 1) := by
  have h := crtControlWorkspaceClear_runs (body := body) W wl nl st
    (crtBankOverlay rg R (tblRho W wl nl st)) (crtBankOverlay_on hrg _ _)
  refine crtRuns_congr h ?_
  funext k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hk
    cases r <;> simp [hrg.eq_iff, crtBankOverlay_on hrg, tblRho, hv, hz, hwr, hwn, hacc]
  · have hk' : ∀ r, rg r ≠ k := by simpa using hk
    have hvar : ¬ ∃ i, rg (.v i) = k := by rintro ⟨i, hi⟩; exact hk' (.v i) hi
    simp [hvar, crtBankOverlay_off _ _ _ _ hk']

end IntegerMultBounds.MathlibTM2.Fast
