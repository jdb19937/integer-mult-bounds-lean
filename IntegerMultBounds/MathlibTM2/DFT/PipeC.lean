module

public import IntegerMultBounds.MathlibTM2.DFT.PipeB
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The pipeline, third part: the product and the unpacking loop

`M.pipeC B` (`pipeC_exec`): from `rUp = binSyms (s n) X` and `rV2 = binSyms (s (n + n)) Y`,
`s = 3 w`: `rDw := rUp` and `s` zeros onto `rUp` (`prepP`, so `rUp = binSyms (s (n + 1)) (B X)`),
the product `rZp := B X Y` (`mulCall`), `rZp := B X Y / 2 ^ (s n)` (`usub` by `rDw`),
`rC`, `rE := 1`, and the unpacking loop. The registers end as `unpackR … (pipeR3 …) n`.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

open scoped IntegerMultBounds.MathlibTM2.DFT.Reg

namespace IntegerMultBounds.MathlibTM2.DFT

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (B : Type)

/-- The product and the unpacking loop. -/
def pipeC : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B) :=
  .seq (hostCode (prepP (M.dreg 50 rUp) (M.dreg 50 rDw) (M.dreg 50 rW3) (M.dreg 50 rt1)
      (M.dreg 50 rt2)))
    (.seq (M.mulCall 50 B (M.dreg 50 rUp) (M.dreg 50 rV2) (M.dreg 50 rZp) (M.dreg 50 rt1)
        (M.dreg 50 rt2) (M.dreg 50 rt3) (M.dreg 50 rt4) (M.dreg 50 rt5))
      (.seq (hostCode (usub (M.dreg 50 rDw) (M.dreg 50 rZp) (M.dreg 50 rt1)))
        (.seq (hostCode (restartCE (M.dreg 50 rC) (M.dreg 50 rE) (M.dreg 50 rPw) (M.dreg 50 rt1)))
          (M.countLoop 50 B (M.dreg 50 rNcnt) (M.unpackRound B)))))

/-- The registers before the unpacking loop. -/
def pipeR3 (w n X Y : ℕ) (R : Fin (M.T + 50) → List (Fin (M.A + 4))) :
    Fin (M.T + 50) → List (Fin (M.A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update R
    (M.dreg 50 rDw) (binSyms (3 * w * n) X))
    (M.dreg 50 rUp) (binSyms (3 * w * (n + 1)) (0 + 2 ^ (3 * w) * X)))
    (M.dreg 50 rZp) (binSyms (3 * w * (2 * n + 1)) ((0 + 2 ^ (3 * w) * X) * Y / 2 ^ (3 * w * n))))
    (M.dreg 50 rC) (binSyms w 1)) (M.dreg 50 rE) (binSyms w 1)

theorem pipeC_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {k w p ω' n X Y : ℕ} (hw : 1 ≤ w) (h2w : 2 * w ≤ k) (hp1 : 2 ^ (w - 1) ≤ p)
    (hp : p < 2 ^ w) (hp2 : 2 ≤ p) (hω' : ω' < p) (hX : X < 2 ^ (3 * w * n))
    (hY : Y < 2 ^ (3 * w * (n + n)))
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (henv : M.ModEnv k w p S) (hUp : S.R (M.dreg 50 rUp) = binSyms (3 * w * n) X)
    (hV2 : S.R (M.dreg 50 rV2) = binSyms (3 * w * (n + n)) Y) (hDw : S.R (M.dreg 50 rDw) = [])
    (hZp : S.R (M.dreg 50 rZp) = []) (hN : S.R (M.dreg 50 rNcnt) = List.replicate n tick)
    (hC : (S.R (M.dreg 50 rC)).length = w) (hE : (S.R (M.dreg 50 rE)).length = w)
    (hWinv : S.R (M.dreg 50 rWinv) = binSyms w ω') (hW3 : (S.R (M.dreg 50 rW3)).length = 3 * w)
    (hTk : S.R (M.dreg 50 rTk) = []) (hO2 : S.R (M.dreg 50 rO2) = [])
    (hOut : S.R (M.dreg 50 rOut) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ n', v'.user.2 = v.user.2 ∧
      n' ≤ (3 * w * (3 * n + 1) + 1) * H (3 * w * (3 * n + 1)) + n * (unpackCost H k + 2) +
        400 * w * (n + 1) + 100 ∧
      Exec (M.tab 50 B main) (M.pipeC B) (dmk v S gi go) n'
        (dmk v' { S with
          R := M.unpackR w p ω' n (2 * n + 1) ((0 + 2 ^ (3 * w) * X) * Y / 2 ^ (3 * w * n))
            (M.pipeR3 w n X Y S.R) n } gi go) := by
  obtain ⟨hinp, hout, hL, hR, hA, hPw, hK, hZ, hQ1, hQ2, hP3, hO, ht1, ht2, ht3, ht4, ht5⟩ :=
    henv
  -- `rDw := rUp`, `s` zeros onto `rUp`
  obtain ⟨v₁, hu₁, e₁⟩ := prepP_exec Empty.elim (Up := M.dreg 50 rUp) (Dw := M.dreg 50 rDw)
    (W3 := M.dreg 50 rW3) (t₁ := M.dreg 50 rt1) (t₂ := M.dreg 50 rt2) (by simp) v S hW3 hDw ht1
    ht2
  rw [hUp, binSyms_cons_block (show 0 < 2 ^ (3 * w) by positivity), length_binSyms] at e₁
  set S₁ : Stacks (M.T + 50) M.A := { S with
    R := Function.update (Function.update S.R (M.dreg 50 rDw) (binSyms (3 * w * n) X))
      (M.dreg 50 rUp) (binSyms (3 * w * (n + 1)) (0 + 2 ^ (3 * w) * X)) } with hS₁
  -- the product
  have hx : 0 + 2 ^ (3 * w) * X < 2 ^ (3 * w * (n + 1)) := by
    rw [Nat.zero_add, show 3 * w * (n + 1) = 3 * w + 3 * w * n by ring, pow_add]
    exact (Nat.mul_lt_mul_left (by positivity)).2 hX
  obtain ⟨v₂, m₂, hu₂, hm₂, e₂⟩ := M.mulCall_exec 50 B main (a := M.dreg 50 rUp)
    (b := M.dreg 50 rV2) (c := M.dreg 50 rZp) (t₁ := M.dreg 50 rt1) (t₂ := M.dreg 50 rt2)
    (t₃ := M.dreg 50 rt3) (t₄ := M.dreg 50 rt4) (t₅ := M.dreg 50 rt5) (by simp) hx hY v₁ S₁
    (by simp [hS₁, hinp]) (by simp [hS₁, hout]) (by simp [hS₁, hL]) (by intro i; simp [hS₁, hR])
    (by simp [hS₁]) (by simp [hS₁, hV2]) (by simp [hS₁, hZp]) (by simp [hS₁, ht1])
    (by simp [hS₁, ht2]) (by simp [hS₁, ht3]) (by simp [hS₁, ht4]) (by simp [hS₁, ht5]) gi go
  set P := (0 + 2 ^ (3 * w) * X) * Y with hP
  set S₂ : Stacks (M.T + 50) M.A := { S₁ with
    R := Function.update S₁.R (M.dreg 50 rZp) (binSyms (3 * w * (n + 1) + 3 * w * (n + n)) P) }
    with hS₂
  -- drop `s n` bits
  obtain ⟨v₃, hu₃, e₃⟩ := bhigh_exec Empty.elim (a := M.dreg 50 rZp) (wR := M.dreg 50 rDw)
    (t := M.dreg 50 rt1) (by simp) (r := 3 * w * n) (e := 3 * w * (2 * n + 1)) (X := P) v₂ S₂
    (by rw [show 3 * w * n + 3 * w * (2 * n + 1) = 3 * w * (n + 1) + 3 * w * (n + n) by ring];
        simp [hS₂])
    (by simp [hS₂, hS₁, length_binSyms]) (by simp [hS₂, hS₁, ht1])
  set S₃ : Stacks (M.T + 50) M.A := { S₂ with
    R := Function.update S₂.R (M.dreg 50 rZp) (binSyms (3 * w * (2 * n + 1)) (P / 2 ^ (3 * w * n))) }
    with hS₃
  -- restart the chirp registers
  obtain ⟨v₄, hu₄, e₄⟩ := restartCE_exec Empty.elim (C := M.dreg 50 rC) (E := M.dreg 50 rE)
    (Pw := M.dreg 50 rPw) (t₁ := M.dreg 50 rt1) (by simp) hw v₃ S₃
    (by simp [hS₃, hS₂, hS₁, hPw, length_binSyms]) (by simp [hS₃, hS₂, hS₁, hC])
    (by simp [hS₃, hS₂, hS₁, hE]) (by simp [hS₃, hS₂, hS₁, ht1])
  set S₄ : Stacks (M.T + 50) M.A := { S₃ with
    R := Function.update (Function.update S₃.R (M.dreg 50 rC) (binSyms w 1)) (M.dreg 50 rE)
      (binSyms w 1) } with hS₄
  have hS₄R : S₄.R = M.pipeR3 w n X Y S.R := by
    simp only [hS₄, hS₃, hS₂, hS₁, pipeR3]
    funext j
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  -- the unpacking loop
  obtain ⟨v₅, n₅, hu₅, hn₅, e₅⟩ := M.unpackLoop_exec B main H hH hT (k := k) (ω' := ω') (n := n)
    (m := 2 * n + 1) (Y := P / 2 ^ (3 * w * n)) hw h2w hp1 hp hp2 hω' (by omega) v₄ S₄
    ⟨by simp [hS₄, hS₃, hS₂, hS₁, hinp], by simp [hS₄, hS₃, hS₂, hS₁, hout],
      by simp [hS₄, hS₃, hS₂, hS₁, hL], by intro i; simp [hS₄R, pipeR3, hR],
      by simp [hS₄R, pipeR3, hA], by simp [hS₄R, pipeR3, hPw], by simp [hS₄R, pipeR3, hK],
      by simp [hS₄R, pipeR3, hZ], by simp [hS₄R, pipeR3, hQ1], by simp [hS₄R, pipeR3, hQ2],
      by simp [hS₄R, pipeR3, hP3], by simp [hS₄R, pipeR3, hO], by simp [hS₄R, pipeR3, ht1],
      by simp [hS₄R, pipeR3, ht2], by simp [hS₄R, pipeR3, ht3], by simp [hS₄R, pipeR3, ht4],
      by simp [hS₄R, pipeR3, ht5]⟩
    (by simp [hS₄R, pipeR3, hN]) (by simp [hS₄R, pipeR3, hP]) (by simp [hS₄R, pipeR3, hTk])
    (by simp [hS₄R, pipeR3, hO2]) (by simp [hS₄R, pipeR3, hOut]) (by simp [hS₄R, pipeR3])
    (by simp [hS₄R, pipeR3]) (by simp [hS₄R, pipeR3, hWinv]) (by simp [hS₄R, pipeR3, hW3]) gi go
  refine ⟨v₅, _, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq (exec_hostCode e₁ gi go) (Exec.seq e₂ (Exec.seq (exec_hostCode e₃ gi go)
      (Exec.seq (exec_hostCode e₄ gi go) e₅)))) rfl ?_⟩
  · -- the time
    have hsz : Nat.size (0 + 2 ^ (3 * w) * X) + Nat.size Y ≤ 3 * w * (3 * n + 1) := by
      have := Nat.size_le.2 hx
      have := Nat.size_le.2 hY
      have : 3 * w * (n + 1) + 3 * w * (n + n) = 3 * w * (3 * n + 1) := by ring
      omega
    have hm₂' : m₂ + 2 ≤ (3 * w * (3 * n + 1) + 1) * H (3 * w * (3 * n + 1)) :=
      hm₂.trans ((hT _).trans (Nat.mul_le_mul (by omega) (hH hsz)))
    have hPs : Nat.size P ≤ 3 * w * (n + 1) + 3 * w * (n + n) :=
      Nat.size_le.2 (by rw [hP, pow_add]; exact Nat.mul_lt_mul'' hx hY)
    have e1 : 3 * w * (n + 1) = 3 * (w * n) + 3 * w := by ring
    have e2 : 3 * w * (n + n) = 6 * (w * n) := by ring
    have e3 : 3 * w * n = 3 * (w * n) := by ring
    have e4 : 400 * w * (n + 1) = 400 * (w * n) + 400 * w := by ring
    omega
  · show dmk v₅ _ gi go = dmk v₅ _ gi go
    rw [hS₄R]

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
