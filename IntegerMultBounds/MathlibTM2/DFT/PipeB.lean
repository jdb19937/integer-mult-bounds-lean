module

public import IntegerMultBounds.MathlibTM2.DFT.PipeA
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The pipeline, second part: loop B and the input loop

`M.pipeB B` (`pipeB_exec`): `rF := rEnt`, loop B (`n` more chirps from `n`), `rV2 := rV` in order
(`moveR`), `rC`, `rE := 1` (`restartCE`), and the input loop with the inverse root `ω'` in
`rWinv`. The registers end as `inputR … (pipeR2 …) n`, with
`rV2 = binSyms (3 w (n + n)) (pack B (chirp p ω) (n + n))`.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

open scoped IntegerMultBounds.MathlibTM2.DFT.Reg

namespace IntegerMultBounds.MathlibTM2.DFT

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (B : Type)

/-- Loop B, the chirp pack in order, and the input loop. -/
def pipeB : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B) :=
  .seq (hostCode (bcopy (M.dreg 50 rEnt) (M.dreg 50 rF) (M.dreg 50 rt1) (M.dreg 50 rt2)))
    (.seq (M.countLoop 50 B (M.dreg 50 rF) (M.chirpRoundB B))
      (.seq (hostCode (moveR (M.dreg 50 rV) (M.dreg 50 rV2) id))
        (.seq (hostCode (restartCE (M.dreg 50 rC) (M.dreg 50 rE) (M.dreg 50 rPw) (M.dreg 50 rt1)))
          (M.countLoop 50 B (M.dreg 50 rEnt) (M.inputRound B)))))

/-- The registers before the input loop. -/
def pipeR2 (w p ω : ℕ) (as : List ℕ) (R : Fin (M.T + 50) → List (Fin (M.A + 4))) :
    Fin (M.T + 50) → List (Fin (M.A + 4)) :=
  Function.update (Function.update (Function.update (Function.update
    (M.chirpB w p ω as.length as (Function.update R (M.dreg 50 rF) (fieldSyms w as)) as.length)
    (M.dreg 50 rV) []) (M.dreg 50 rV2)
    (binSyms (3 * w * (as.length + as.length))
      (pack (2 ^ (3 * w)) (chirp p ω) (as.length + as.length))))
    (M.dreg 50 rC) (binSyms w 1)) (M.dreg 50 rE) (binSyms w 1)

theorem pipeB_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {k w p ω ω' : ℕ} (as : List ℕ) (hw : 1 ≤ w) (hwk : w ≤ k) (hp1 : 2 ^ (w - 1) ≤ p)
    (hp : p < 2 ^ w) (hp2 : 2 ≤ p) (hω : ω < p) (hω' : ω' < p) (has : ∀ a ∈ as, a < p)
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (henv : M.ModEnv k w p S) (hEnt : S.R (M.dreg 50 rEnt) = fieldSyms w as)
    (hF : S.R (M.dreg 50 rF) = []) (hFt : S.R (M.dreg 50 rFt) = [])
    (hFu : S.R (M.dreg 50 rFu) = [])
    (hC : S.R (M.dreg 50 rC) = binSyms w (chirp p ω as.length))
    (hE : S.R (M.dreg 50 rE) = binSyms w (ω ^ as.length % p))
    (hV : S.R (M.dreg 50 rV) =
      (binSyms (3 * w * as.length) (pack (2 ^ (3 * w)) (chirp p ω) as.length)).reverse)
    (hWm : S.R (M.dreg 50 rWm) = binSyms w ω) (hW3 : (S.R (M.dreg 50 rW3)).length = 3 * w)
    (hCw : S.R (M.dreg 50 rCw) = []) (hWc : S.R (M.dreg 50 rWc) = [])
    (hWinv : S.R (M.dreg 50 rWinv) = binSyms w ω') (hV2 : S.R (M.dreg 50 rV2) = [])
    (hXa : S.R (M.dreg 50 rXa) = []) (hUp : S.R (M.dreg 50 rUp) = [])
    (hNcnt : S.R (M.dreg 50 rNcnt) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ n, v'.user.2 = v.user.2 ∧
      n ≤ 6 * (as.length * (w + 1)) + as.length * (chirpCost H k + 2) +
        6 * w * (as.length + as.length) + as.length * (inputCost H k + 2) + 12 * w + 30 ∧
      Exec (M.tab 50 B main) (M.pipeB B) (dmk v S gi go) n
        (dmk v' { S with R := M.inputR w p ω' as (M.pipeR2 w p ω as S.R) as.length } gi go) := by
  obtain ⟨hinp, hout, hL, hR, hA, hPw, hK, hZ, hQ1, hQ2, hP3, hO, ht1, ht2, ht3, ht4, ht5⟩ :=
    henv
  have hp0 : 0 < p := by omega
  -- the counter of loop B
  obtain ⟨v₁, hu₁, e₁⟩ := bcopy_exec Empty.elim (a := M.dreg 50 rEnt) (c := M.dreg 50 rF)
    (t₁ := M.dreg 50 rt1) (t₂ := M.dreg 50 rt2) (by simp) v S ht1 ht2
  rw [hEnt, hF, List.append_nil, length_fieldSyms'] at e₁
  set S₁ : Stacks (M.T + 50) M.A :=
    { S with R := Function.update S.R (M.dreg 50 rF) (fieldSyms w as) } with hS₁
  -- loop B
  obtain ⟨v₂, n₂, hu₂, hn₂, e₂⟩ := M.chirpLoopB_exec B main H hH hT (k := k) (ω := ω)
    (m₀ := as.length) as hw hwk hp1 hp hω v₁ S₁
    ⟨by simp [hS₁, hinp], by simp [hS₁, hout], by simp [hS₁, hL], by intro i; simp [hS₁, hR],
      by simp [hS₁, hA], by simp [hS₁, hPw], by simp [hS₁, hK], by simp [hS₁, hZ],
      by simp [hS₁, hQ1], by simp [hS₁, hQ2], by simp [hS₁, hP3], by simp [hS₁, hO],
      by simp [hS₁, ht1], by simp [hS₁, ht2], by simp [hS₁, ht3], by simp [hS₁, ht4],
      by simp [hS₁, ht5]⟩
    (by simp [hS₁]) (by simp [hS₁, hFt]) (by simp [hS₁, hFu]) (by simp [hS₁, hC])
    (by simp [hS₁, hE]) (by simp [hS₁, hV]) (by simp [hS₁, hWm]) (by simp [hS₁, hW3])
    (by simp [hS₁, hCw]) (by simp [hS₁, hWc]) gi go
  set S₂ : Stacks (M.T + 50) M.A :=
    { S₁ with R := M.chirpB w p ω as.length as S₁.R as.length } with hS₂
  -- the chirp pack in order
  obtain ⟨v₃, hu₃, e₃⟩ := moveR_exec Empty.elim (M.dreg 50 rV) (M.dreg 50 rV2) (by simp) id v₂ S₂
  have hS₂V : S₂.R (M.dreg 50 rV) = (binSyms (3 * w * (as.length + as.length))
      (pack (2 ^ (3 * w)) (chirp p ω) (as.length + as.length))).reverse := by
    simp [hS₂, chirpB]
  rw [hS₂V, List.length_reverse, length_binSyms] at e₃
  set S₃ : Stacks (M.T + 50) M.A := { S₂ with
    R := movedR S₂.R (M.dreg 50 rV) (M.dreg 50 rV2) id (binSyms (3 * w * (as.length + as.length))
      (pack (2 ^ (3 * w)) (chirp p ω) (as.length + as.length))).reverse } with hS₃
  -- restart the chirp registers
  obtain ⟨v₄, hu₄, e₄⟩ := restartCE_exec Empty.elim (C := M.dreg 50 rC) (E := M.dreg 50 rE)
    (Pw := M.dreg 50 rPw) (t₁ := M.dreg 50 rt1) (by simp) hw v₃ S₃
    (by simp [hS₃, hS₂, hS₁, movedR, chirpB, hPw, length_binSyms])
    (by simp [hS₃, hS₂, hS₁, movedR, chirpB, length_binSyms])
    (by simp [hS₃, hS₂, hS₁, movedR, chirpB, length_binSyms])
    (by simp [hS₃, hS₂, hS₁, movedR, chirpB, ht1])
  set S₄ : Stacks (M.T + 50) M.A := { S₃ with
    R := Function.update (Function.update S₃.R (M.dreg 50 rC) (binSyms w 1)) (M.dreg 50 rE)
      (binSyms w 1) } with hS₄
  have hV2' : M.chirpB w p ω as.length as (Function.update S.R (M.dreg 50 rF) (fieldSyms w as))
      as.length (M.dreg 50 rV2) = [] := by simp [chirpB, hV2]
  have hS₄R : S₄.R = M.pipeR2 w p ω as S.R := by
    simp only [hS₄, hS₃, hS₂, hS₁, pipeR2, movedR, List.map_id, List.reverse_reverse, hV2',
      List.append_nil]
  -- the input loop
  obtain ⟨v₅, n₅, hu₅, hn₅, e₅⟩ := M.inputLoop_exec B main H hH hT (k := k) (ω' := ω') as hw hwk
    hp1 hp hp2 hω' has v₄ S₄
    ⟨by simp [hS₄, hS₃, hS₂, hS₁, hinp], by simp [hS₄, hS₃, hS₂, hS₁, hout],
      by simp [hS₄, hS₃, hS₂, hS₁, hL], by intro i; simp [hS₄, hS₃, hS₂, hS₁, movedR, chirpB, hR],
      by simp [hS₄R, pipeR2, chirpB, hA], by simp [hS₄R, pipeR2, chirpB, hPw],
      by simp [hS₄R, pipeR2, chirpB, hK], by simp [hS₄R, pipeR2, chirpB, hZ],
      by simp [hS₄R, pipeR2, chirpB, hQ1], by simp [hS₄R, pipeR2, chirpB, hQ2],
      by simp [hS₄R, pipeR2, chirpB, hP3], by simp [hS₄R, pipeR2, chirpB, hO],
      by simp [hS₄R, pipeR2, chirpB, ht1], by simp [hS₄R, pipeR2, chirpB, ht2],
      by simp [hS₄R, pipeR2, chirpB, ht3], by simp [hS₄R, pipeR2, chirpB, ht4],
      by simp [hS₄R, pipeR2, chirpB, ht5]⟩
    (by simp [hS₄R, pipeR2, chirpB, hEnt]) (by simp [hS₄R, pipeR2, chirpB, hXa])
    (by simp [hS₄R, pipeR2, chirpB, hFu]) (by simp [hS₄R, pipeR2]) (by simp [hS₄R, pipeR2])
    (by simp [hS₄R, pipeR2, chirpB, hUp]) (by simp [hS₄R, pipeR2, chirpB, hNcnt])
    (by simp [hS₄R, pipeR2, chirpB, hWinv]) (by simp [hS₄R, pipeR2, chirpB, hW3])
    (by simp [hS₄R, pipeR2, chirpB, hCw]) (by simp [hS₄R, pipeR2, chirpB, hWc]) gi go
  refine ⟨v₅, _, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq (exec_hostCode e₁ gi go) (Exec.seq e₂ (Exec.seq (exec_hostCode e₃ gi go)
      (Exec.seq (exec_hostCode e₄ gi go) e₅)))) rfl ?_⟩
  · have : 2 * (3 * w * (as.length + as.length)) = 6 * w * (as.length + as.length) := by ring
    omega
  · show dmk v₅ _ gi go = dmk v₅ _ gi go
    rw [hS₄R]

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
