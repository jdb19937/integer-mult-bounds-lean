module

public import IntegerMultBounds.MathlibTM2.DFT.Unpack
public import IntegerMultBounds.MathlibTM2.DFT.PipeSetup
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The pipeline, first part: widths, the reciprocal and loop A

`M.pipeA B` (`pipeA_exec`): from the parsed instance (`rEnt = fieldSyms w as`, `rPw = p`,
`rWm = ω`, every other DFT register empty), `widths`, `recipProg` with `r = 2 w`, `prepA` and
loop A. The registers end as `chirpA … (pipeR1 …) n`: `rWR`, `rW3` of `2 w` and `3 w` symbols,
`μ = ⌊2 ^ (k + w) / p⌋` in `rAa` for some `2 w < k ≤ 4 w` with `k` symbols in `rWK`, and the
`n` chirps of loop A.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

open scoped IntegerMultBounds.MathlibTM2.DFT.Reg

namespace IntegerMultBounds.MathlibTM2.DFT

theorem length_fieldSyms' {A : ℕ} (w : ℕ) (l : List ℕ) :
    (fieldSyms w l : List (Fin (A + 4))).length = l.length * (w + 1) := by
  induction l with
  | nil => simp [fieldSyms]
  | cons x l ih => rw [fieldSyms_cons, List.length_append, List.length_cons, ih, length_binSyms,
      List.length_cons]; ring

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (B : Type)

/-- Widths, the reciprocal, and loop A. -/
def pipeA : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B) :=
  .seq (hostCode (widths (M.dreg 50 rPw) (M.dreg 50 rWR) (M.dreg 50 rW3) (M.dreg 50 rt1)
      (M.dreg 50 rt2)))
    (.seq (M.recipProg 50 B rPw rWR rCnt rDp rWK rW2K rWL rONE rSIX rB1 rDd rAa rB2 rB3 rY rYn
        rt1 rt2 rt3 rt4 rt5)
      (.seq (hostCode (prepA (M.dreg 50 rEnt) (M.dreg 50 rF) (M.dreg 50 rC) (M.dreg 50 rE)
          (M.dreg 50 rWinv) (M.dreg 50 rPw) (M.dreg 50 rt1) (M.dreg 50 rt2)))
        (M.countLoop 50 B (M.dreg 50 rF) (M.chirpRoundA B))))

/-- The registers before loop A. -/
def pipeR1 (w p k : ℕ) (as : List ℕ) (Kc : List (Fin (M.A + 4)))
    (R : Fin (M.T + 50) → List (Fin (M.A + 4))) : Fin (M.T + 50) → List (Fin (M.A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update R
    (M.dreg 50 rWR) (binSyms w p ++ binSyms w p))
    (M.dreg 50 rW3) (binSyms w p ++ (binSyms w p ++ binSyms w p))) (M.dreg 50 rWK) Kc)
    (M.dreg 50 rAa) (binSyms (k + k + 4) (2 ^ (k + w) / p))) (M.dreg 50 rF) (fieldSyms w as))
    (M.dreg 50 rC) (binSyms w 1)) (M.dreg 50 rE) (binSyms w 1)) (M.dreg 50 rWinv) (binSyms w 1)

theorem pipeA_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {w p ω : ℕ} (as : List ℕ) (hw : 1 ≤ w) (hp1 : 2 ^ (w - 1) ≤ p) (hp : p < 2 ^ w)
    (hp2 : 2 ≤ p) (hω : ω < p) (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ j, S.L j = [])
    (hR : ∀ i, S.R (M.emb 50 i) = []) (hEnt : S.R (M.dreg 50 rEnt) = fieldSyms w as)
    (hPw : S.R (M.dreg 50 rPw) = binSyms w p) (hWm : S.R (M.dreg 50 rWm) = binSyms w ω)
    (hclean : ∀ j : Fin 50, j ≠ rEnt → j ≠ rPw → j ≠ rWm → S.R (M.dreg 50 j) = [])
    (gi go : List Γ') :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ (Kc : List (Fin (M.A + 4))) (k n : ℕ),
      v'.user.2 = v.user.2 ∧ Kc.length = k ∧ 2 * w + 1 ≤ k ∧ k ≤ 2 * (2 * w) ∧
      n ≤ (7200 + 27 * H (4 * (2 * w) + 4)) * (2 * (2 * w) + 1) + 6 * (as.length * (w + 1)) +
        as.length * (chirpCost H k + 2) + 200 * w + 200 ∧
      Exec (M.tab 50 B main) (M.pipeA B) (dmk v S gi go) n
        (dmk v' { S with R := M.chirpA w p ω as (M.pipeR1 w p k as Kc S.R) as.length } gi go) := by
  have crIn := hclean rIn (by decide) (by decide) (by decide)
  have crT := hclean rT (by decide) (by decide) (by decide)
  have crWR := hclean rWR (by decide) (by decide) (by decide)
  have crW3 := hclean rW3 (by decide) (by decide) (by decide)
  have crCnt := hclean rCnt (by decide) (by decide) (by decide)
  have crDp := hclean rDp (by decide) (by decide) (by decide)
  have crWK := hclean rWK (by decide) (by decide) (by decide)
  have crW2K := hclean rW2K (by decide) (by decide) (by decide)
  have crWL := hclean rWL (by decide) (by decide) (by decide)
  have crONE := hclean rONE (by decide) (by decide) (by decide)
  have crSIX := hclean rSIX (by decide) (by decide) (by decide)
  have crB1 := hclean rB1 (by decide) (by decide) (by decide)
  have crDd := hclean rDd (by decide) (by decide) (by decide)
  have crAa := hclean rAa (by decide) (by decide) (by decide)
  have crB2 := hclean rB2 (by decide) (by decide) (by decide)
  have crB3 := hclean rB3 (by decide) (by decide) (by decide)
  have crY := hclean rY (by decide) (by decide) (by decide)
  have crYn := hclean rYn (by decide) (by decide) (by decide)
  have crt1 := hclean rt1 (by decide) (by decide) (by decide)
  have crt2 := hclean rt2 (by decide) (by decide) (by decide)
  have crt3 := hclean rt3 (by decide) (by decide) (by decide)
  have crt4 := hclean rt4 (by decide) (by decide) (by decide)
  have crt5 := hclean rt5 (by decide) (by decide) (by decide)
  have crZ := hclean rZ (by decide) (by decide) (by decide)
  have crQ1 := hclean rQ1 (by decide) (by decide) (by decide)
  have crQ2 := hclean rQ2 (by decide) (by decide) (by decide)
  have crP3 := hclean rP3 (by decide) (by decide) (by decide)
  have crO := hclean rO (by decide) (by decide) (by decide)
  have crF := hclean rF (by decide) (by decide) (by decide)
  have crFt := hclean rFt (by decide) (by decide) (by decide)
  have crFu := hclean rFu (by decide) (by decide) (by decide)
  have crC := hclean rC (by decide) (by decide) (by decide)
  have crE := hclean rE (by decide) (by decide) (by decide)
  have crWinv := hclean rWinv (by decide) (by decide) (by decide)
  have crV := hclean rV (by decide) (by decide) (by decide)
  have crCw := hclean rCw (by decide) (by decide) (by decide)
  have crWc := hclean rWc (by decide) (by decide) (by decide)
  -- widths
  obtain ⟨v₁, hu₁, e₁⟩ := widths_exec Empty.elim (Pw := M.dreg 50 rPw) (WR := M.dreg 50 rWR)
    (W3 := M.dreg 50 rW3) (t₁ := M.dreg 50 rt1) (t₂ := M.dreg 50 rt2) (by simp) (w := w) v S
    (by rw [hPw, length_binSyms]) crWR crW3 crt1 crt2
  rw [hPw] at e₁
  set S₁ : Stacks (M.T + 50) M.A := { S with
    R := Function.update (Function.update S.R (M.dreg 50 rWR) (binSyms w p ++ binSyms w p))
      (M.dreg 50 rW3) (binSyms w p ++ (binSyms w p ++ binSyms w p)) } with hS₁
  -- the reciprocal
  obtain ⟨v₂, Kc, k, n₂, hu₂, hKc, hk1, hk2, hn₂, e₂⟩ := M.recip_exec 50 B main H hH hT
    (Pw := rPw) (wR := rWR) (Cnt := rCnt) (Dp := rDp) (wK := rWK) (w2K := rW2K) (wL := rWL)
    (ONE := rONE) (SIX := rSIX) (B1 := rB1) (Dd := rDd) (Aa := rAa) (B2 := rB2) (B3 := rB3)
    (Y := rY) (Yn := rYn) (t₁ := rt1) (t₂ := rt2) (t₃ := rt3) (t₄ := rt4) (t₅ := rt5) (by decide)
    (r := 2 * w) hw (by omega) hp1 hp v₁ S₁ (by simp [hS₁, hinp]) (by simp [hS₁, hout])
    (by simp [hS₁, hL]) (by intro i; simp [hS₁, hR]) (by simp [hS₁, hPw])
    (by simp [hS₁, length_binSyms]; ring) (by simp [hS₁, crCnt]) (by simp [hS₁, crDp])
    (by simp [hS₁, crWK]) (by simp [hS₁, crW2K]) (by simp [hS₁, crWL]) (by simp [hS₁, crONE])
    (by simp [hS₁, crSIX]) (by simp [hS₁, crB1]) (by simp [hS₁, crDd]) (by simp [hS₁, crAa])
    (by simp [hS₁, crB2]) (by simp [hS₁, crB3]) (by simp [hS₁, crY]) (by simp [hS₁, crYn])
    (by simp [hS₁, crt1]) (by simp [hS₁, crt2]) (by simp [hS₁, crt3]) (by simp [hS₁, crt4])
    (by simp [hS₁, crt5]) gi go
  set S₂ : Stacks (M.T + 50) M.A := { S₁ with
    R := Function.update (Function.update S₁.R (M.dreg 50 rWK) Kc) (M.dreg 50 rAa)
      (binSyms (k + k + 4) (2 ^ (k + w) / p)) } with hS₂
  -- the registers of loop A
  obtain ⟨v₃, hu₃, e₃⟩ := prepA_exec Empty.elim (Ent := M.dreg 50 rEnt) (F := M.dreg 50 rF)
    (C := M.dreg 50 rC) (E := M.dreg 50 rE) (Wi := M.dreg 50 rWinv) (Pw := M.dreg 50 rPw)
    (t₁ := M.dreg 50 rt1) (t₂ := M.dreg 50 rt2) (by simp) hw v₂ S₂
    (by simp [hS₂, hS₁, hPw, length_binSyms]) (by simp [hS₂, hS₁, crF]) (by simp [hS₂, hS₁, crC])
    (by simp [hS₂, hS₁, crE]) (by simp [hS₂, hS₁, crWinv]) (by simp [hS₂, hS₁, crt1])
    (by simp [hS₂, hS₁, crt2])
  rw [show S₂.R (M.dreg 50 rEnt) = fieldSyms w as by simp [hS₂, hS₁, hEnt]] at e₃
  set S₃ : Stacks (M.T + 50) M.A := { S₂ with
    R := Function.update (Function.update (Function.update (Function.update S₂.R (M.dreg 50 rF)
      (fieldSyms w as)) (M.dreg 50 rC) (binSyms w 1)) (M.dreg 50 rE) (binSyms w 1))
      (M.dreg 50 rWinv) (binSyms w 1) } with hS₃
  -- loop A
  obtain ⟨v₄, n₄, hu₄, hn₄, e₄⟩ := M.chirpLoopA_exec B main H hH hT (k := k) as hw (by omega)
    hp1 hp hp2 hω v₃ S₃
    ⟨by simp [hS₃, hS₂, hS₁, hinp], by simp [hS₃, hS₂, hS₁, hout], by simp [hS₃, hS₂, hS₁, hL],
      by intro i; simp [hS₃, hS₂, hS₁, hR], by simp [hS₃, hS₂], by simp [hS₃, hS₂, hS₁, hPw],
      by simp [hS₃, hS₂, hKc], by simp [hS₃, hS₂, hS₁, crZ], by simp [hS₃, hS₂, hS₁, crQ1],
      by simp [hS₃, hS₂, hS₁, crQ2], by simp [hS₃, hS₂, hS₁, crP3], by simp [hS₃, hS₂, hS₁, crO],
      by simp [hS₃, hS₂, hS₁, crt1], by simp [hS₃, hS₂, hS₁, crt2], by simp [hS₃, hS₂, hS₁, crt3],
      by simp [hS₃, hS₂, hS₁, crt4], by simp [hS₃, hS₂, hS₁, crt5]⟩
    (by simp [hS₃]) (by simp [hS₃, hS₂, hS₁, crFt]) (by simp [hS₃, hS₂, hS₁, crFu])
    (by simp [hS₃]) (by simp [hS₃]) (by simp [hS₃]) (by simp [hS₃, hS₂, hS₁, crV])
    (by simp [hS₃, hS₂, hS₁, hWm]) (by simp [hS₃, hS₂, hS₁, length_binSyms]; ring)
    (by simp [hS₃, hS₂, hS₁, crCw]) (by simp [hS₃, hS₂, hS₁, crWc]) gi go
  refine ⟨v₄, Kc, k, _, by rw [hu₄, hu₃, hu₂, hu₁], hKc, hk1, hk2, ?_,
    Exec.cast (Exec.seq (exec_hostCode e₁ gi go) (Exec.seq e₂ (Exec.seq (exec_hostCode e₃ gi go)
      e₄))) rfl rfl⟩
  rw [length_fieldSyms'] at *
  omega

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
