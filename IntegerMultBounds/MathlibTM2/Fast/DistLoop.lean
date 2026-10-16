module

public import IntegerMultBounds.MathlibTM2.Fast.DistBase

/-!
# A general axis loop

`dsGLoop rg uD tm c₁ c₂ L = scanP uD tm (c₁; pushes L; c₂)` on a table layout
`rg : TblR m → Fin T`: one iteration per symbol of `uD`. With the layout carrying `σ j` before
iteration `j`, `c₁` taking `σ j` to `τ j` and `c₂` taking `τ j` to `σ (j + 1)` (exact table
contracts), the loop ends with the layout carrying `σ N` and every register `k` off the layout
with `dsGAcc τ L N k` on top: the pushes of the iterations `N - 1, …, 0`, from the top
(`ds_gloop`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer


section GLoop

variable {T Q A m : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR m → Fin T}

/-- One iteration: `c₁`, the pushes `L`, `c₂`. -/
def dsGBody (rg : TblR m → Fin T) (c₁ c₂ : TblCode m) (L : List (Fin T × Fin m × DsMode)) :
    Pr P T Q A U :=
  .seq (tblCompile rg c₁) (.seq (dsPush rg L) (tblCompile rg c₂))

/-- The loop: one iteration per symbol of `uD`, through the spare `tm`. -/
def dsGLoop (rg : TblR m → Fin T) (uD tm : Fin T) (c₁ c₂ : TblCode m)
    (L : List (Fin T × Fin m × DsMode)) : Pr P T Q A U :=
  scanP uD tm (dsGBody rg c₁ c₂ L)

/-- What register `k` gains in the first `j` iterations, the latest on top. -/
def dsGAcc (τ : ℕ → Fin m → ℕ) (L : List (Fin T × Fin m × DsMode)) (j : ℕ) (k : Fin T) :
    List (Fin (A + 4)) :=
  ((List.range j).reverse).flatMap fun i => dsOut (τ i) L k

/-- The step bound of the loop. -/
def dsGCost (W w K : ℕ) (τ : ℕ → Fin m → ℕ) (L : List (Fin T × Fin m × DsMode)) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, (K * tblC W w + dsPushCost W (τ i) L + 3) + 2 * N + 4

theorem dsOut_none' (val : Fin m → ℕ) (L : List (Fin T × Fin m × DsMode)) {k : Fin T}
    (hk : ∀ e ∈ L, e.1 ≠ k) : dsOut (A := A) val L k = [] := by
  unfold dsOut
  rw [List.filter_eq_nil_iff.2 (fun e he => by simpa using hk e he)]
  rfl

theorem dsGAcc_succ (τ : ℕ → Fin m → ℕ) (L : List (Fin T × Fin m × DsMode)) (j : ℕ) (k : Fin T) :
    dsGAcc (A := A) τ L (j + 1) k = dsOut (τ j) L k ++ dsGAcc τ L j k := by
  simp [dsGAcc, List.range_succ, List.reverse_append]

theorem dsGAcc_none (τ : ℕ → Fin m → ℕ) (L : List (Fin T × Fin m × DsMode)) {k : Fin T}
    (hk : ∀ e ∈ L, e.1 ≠ k) (j : ℕ) : dsGAcc (A := A) τ L j k = [] := by
  simp [dsGAcc, dsOut_none' _ L hk]

/-- The register file of the loop after `j` iterations. -/
noncomputable def dsGPsi (rg : TblR m → Fin T) (R : Regs T A) (σ τ : ℕ → Fin m → ℕ)
    (L : List (Fin T × Fin m × DsMode)) (W : ℕ) (wl nl : List (Fin (A + 4))) (j : ℕ) :
    Regs T A :=
  dsOv rg (fun k => dsGAcc τ L j k ++ R k) (tblRho W wl nl ⟨σ j, []⟩)

variable (hrg : Function.Injective rg)
include hrg

/-- **The general loop.** -/
theorem ds_gloop {uD tm : Fin T} (huD : ∀ r, rg r ≠ uD) (htm : ∀ r, rg r ≠ tm) (hut : uD ≠ tm)
    {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w)
    (hw : w ≤ W) {c₁ c₂ : TblCode m} {K₁ K₂ N : ℕ} {σ τ : ℕ → Fin m → ℕ}
    (h₁ : ∀ j < N, TblDo A W w c₁ ⟨σ j, []⟩ (· = ⟨τ j, []⟩) K₁)
    (h₂ : ∀ j < N, TblDo A W w c₂ ⟨τ j, []⟩ (· = ⟨σ (j + 1), []⟩) K₂)
    (hσ : ∀ j < N, ∀ x, σ j x < 2 ^ W) (hτ : ∀ j < N, ∀ x, τ j x < 2 ^ W)
    (L : List (Fin T × Fin m × DsMode)) (hL : ∀ e ∈ L, ∀ r, rg r ≠ e.1)
    (hLu : ∀ e ∈ L, e.1 ≠ uD) (hLt : ∀ e ∈ L, e.1 ≠ tm)
    (R : Regs T A) (hRu : (R uD).length = N) (hRt : R tm = []) :
    dsRuns body (dsGLoop rg uD tm c₁ c₂ L) (dsOv rg R (tblRho W wl nl ⟨σ 0, []⟩))
      (dsGPsi rg R σ τ L W wl nl N) (dsGCost W w (K₁ + K₂) τ L N) := by
  have hbody : ∀ j < N, ∀ X : Regs T A,
      dsRuns body (dsGBody rg c₁ c₂ L) (dsOv rg X (tblRho W wl nl ⟨σ j, []⟩))
        (dsOv rg (dsGain (τ j) L X) (tblRho W wl nl ⟨σ (j + 1), []⟩))
        ((K₁ + K₂) * tblC W w + dsPushCost W (τ j) L) := by
    intro j hj X
    have s1 := ds_code (body := body) hrg wl nl hwl hnl hw (h₁ j hj) (hσ j hj) X
    have s2 := ds_push (body := body) hrg (W := W) wl nl ⟨τ j, []⟩ L hL
      (fun e _ => hτ j hj _) X
    have s3 := ds_code (body := body) hrg wl nl hwl hnl hw (h₂ j hj) (hτ j hj) (dsGain (τ j) L X)
    refine (s1.seq (s2.seq s3)).mono ?_
    rw [Nat.add_mul]
    dsimp only
    omega
  have hspec : IterSpec body (dsGBody rg c₁ c₂ L) uD tm (dsGPsi rg R σ τ L W wl nl)
      (fun j => (K₁ + K₂) * tblC W w + dsPushCost W (τ j) L) N := by
    intro j hj v S hS
    have hX : S.R = dsOv rg S.R (tblRho W wl nl ⟨σ j, []⟩) :=
      dsOv_eq_of hrg (fun r => by rw [hS (rg r) (huD r) (htm r), dsGPsi, dsOv_rg hrg])
        (fun _ _ => rfl)
    obtain ⟨v', m', hu, hm, he⟩ := hbody j hj S.R v S hX
    refine ⟨v', _, m', hu, hm, he, ?_, ?_, fun k hku hkt => ?_⟩
    · rw [dsOv_off _ _ huD, dsGain_eq, dsOut_none' _ L hLu, List.nil_append]
    · rw [dsOv_off _ _ htm, dsGain_eq, dsOut_none' _ L hLt, List.nil_append]
    · by_cases hk : ∃ r, rg r = k
      · obtain ⟨r, rfl⟩ := hk
        rw [dsOv_rg hrg, dsGPsi, dsOv_rg hrg]
      · push Not at hk
        rw [dsOv_off _ _ hk, dsGain_eq, hS k hku hkt, dsGPsi, dsGPsi, dsOv_off _ _ hk,
          dsOv_off _ _ hk, dsGAcc_succ, List.append_assoc]
  intro v S hS
  obtain ⟨v', R', m', hu, hm, he, hRu', hRt', hR'⟩ := scanP_exec body hut hspec 0 v S
    (by rw [hS, dsOv_off _ _ huD, hRu, Nat.zero_add])
    (fun k _ _ => by rw [hS, dsGPsi]; simp [dsGAcc])
  refine ⟨v', m', hu, ?_, ?_⟩
  · rw [hS, dsOv_off _ _ huD, dsOv_off _ _ htm, hRu, hRt] at hm
    unfold dsGCost
    simpa using hm
  · have e : R' = dsGPsi rg R σ τ L W wl nl N := by
      funext k
      by_cases hku : k = uD
      · subst hku
        rw [hRu', hS, dsOv_off _ _ htm, hRt, List.reverse_nil, List.nil_append, dsOv_off _ _ huD,
          dsGPsi, dsOv_off _ _ huD, dsGAcc_none τ L hLu, List.nil_append]
      by_cases hkt : k = tm
      · subst hkt
        rw [hRt', dsGPsi, dsOv_off _ _ htm, dsGAcc_none τ L hLt, List.nil_append, hRt]
      rw [hR' k hku hkt, Nat.zero_add, hS, dsOv_off _ _ huD, hRu]
    rw [e] at he
    exact he

end GLoop

end IntegerMultBounds.MathlibTM2.Fast.TableVM
