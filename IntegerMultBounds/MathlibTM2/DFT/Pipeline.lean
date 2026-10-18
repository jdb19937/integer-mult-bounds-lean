module

public import IntegerMultBounds.MathlibTM2.DFT.PipeC
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The pipeline

`M.pipeline B = pipeA ; pipeB ; pipeC` (`pipeline_exec`): from the parsed instance, the registers
end as `pipeR w p ω k as Kc R`, whose output register holds the emitted values of the
unpacking loop (`pipeR_out`), with the inverse root `ω' = ω ^ (n - 1) mod p`, the chirped input
`X = revPack B (a j · chirp p ω' j mod p) n` and the chirp pack `Y = pack B (chirp p ω) (n + n)`.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

open scoped IntegerMultBounds.MathlibTM2.DFT.Reg

namespace IntegerMultBounds.MathlibTM2.DFT

/-- The chirped input as a packed number. -/
def pipeX (w p ω : ℕ) (as : List ℕ) : ℕ :=
  revPack (2 ^ (3 * w)) (fun j => as.getD j 0 * chirp p (ω ^ (as.length - 1) % p) j % p)
    as.length

/-- The chirp as a packed number. -/
def pipeY (w p ω : ℕ) (as : List ℕ) : ℕ :=
  pack (2 ^ (3 * w)) (chirp p ω) (as.length + as.length)

/-- The product after the low `n` digits are dropped. -/
def pipeZ (w p ω : ℕ) (as : List ℕ) : ℕ :=
  (0 + 2 ^ (3 * w) * pipeX w p ω as) * pipeY w p ω as / 2 ^ (3 * w * as.length)

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (B : Type)

/-- The three parts. -/
def pipeline : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B) :=
  .seq (M.pipeA B) (.seq (M.pipeB B) (M.pipeC B))

/-- The registers after the pipeline. -/
def pipeR (w p ω k : ℕ) (as : List ℕ) (Kc : List (Fin (M.A + 4)))
    (R : Fin (M.T + 50) → List (Fin (M.A + 4))) : Fin (M.T + 50) → List (Fin (M.A + 4)) :=
  M.unpackR w p (ω ^ (as.length - 1) % p) as.length (2 * as.length + 1) (pipeZ w p ω as)
    (M.pipeR3 w as.length (pipeX w p ω as) (pipeY w p ω as)
      (M.inputR w p (ω ^ (as.length - 1) % p) as
        (M.pipeR2 w p ω as (M.chirpA w p ω as (M.pipeR1 w p k as Kc R) as.length))
        as.length)) as.length

theorem pipeline_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {w p ω : ℕ} (as : List ℕ) (hw : 1 ≤ w) (hp1 : 2 ^ (w - 1) ≤ p) (hp : p < 2 ^ w)
    (hp2 : 2 ≤ p) (hω : ω < p) (has : ∀ a ∈ as, a < p)
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ j, S.L j = [])
    (hR : ∀ i, S.R (M.emb 50 i) = []) (hEnt : S.R (M.dreg 50 rEnt) = fieldSyms w as)
    (hPw : S.R (M.dreg 50 rPw) = binSyms w p) (hWm : S.R (M.dreg 50 rWm) = binSyms w ω)
    (hclean : ∀ j : Fin 50, j ≠ rEnt → j ≠ rPw → j ≠ rWm → S.R (M.dreg 50 j) = [])
    (gi go : List Γ') :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ (Kc : List (Fin (M.A + 4))) (k n : ℕ),
      v'.user.2 = v.user.2 ∧ Kc.length = k ∧ 2 * w + 1 ≤ k ∧ k ≤ 2 * (2 * w) ∧
      n ≤ (7200 + 27 * H (4 * (2 * w) + 4)) * (2 * (2 * w) + 1) + 6 * (as.length * (w + 1)) +
        as.length * (chirpCost H k + 2) + 200 * w + 200 +
        (6 * (as.length * (w + 1)) + as.length * (chirpCost H k + 2) +
          6 * w * (as.length + as.length) + as.length * (inputCost H k + 2) + 12 * w + 30) +
        ((3 * w * (3 * as.length + 1) + 1) * H (3 * w * (3 * as.length + 1)) +
          as.length * (unpackCost H k + 2) + 400 * w * (as.length + 1) + 100) ∧
      Exec (M.tab 50 B main) (M.pipeline B) (dmk v S gi go) n
        (dmk v' { S with R := M.pipeR w p ω k as Kc S.R } gi go) := by
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
  have crV2 := hclean rV2 (by decide) (by decide) (by decide)
  have crXa := hclean rXa (by decide) (by decide) (by decide)
  have crUp := hclean rUp (by decide) (by decide) (by decide)
  have crNcnt := hclean rNcnt (by decide) (by decide) (by decide)
  have crZp := hclean rZp (by decide) (by decide) (by decide)
  have crDw := hclean rDw (by decide) (by decide) (by decide)
  have crTk := hclean rTk (by decide) (by decide) (by decide)
  have crO2 := hclean rO2 (by decide) (by decide) (by decide)
  have crOut := hclean rOut (by decide) (by decide) (by decide)
  have hp0 : 0 < p := by omega
  -- the first part
  obtain ⟨v₁, Kc, k, n₁, hu₁, hKc, hk1, hk2, hn₁, e₁⟩ := M.pipeA_exec B main H hH hT as hw hp1
    hp hp2 hω v S hinp hout hL hR hEnt hPw hWm hclean gi go
  set SA : Stacks (M.T + 50) M.A :=
    { S with R := M.chirpA w p ω as (M.pipeR1 w p k as Kc S.R) as.length } with hSA
  -- the second part
  obtain ⟨v₂, n₂, hu₂, hn₂, e₂⟩ := M.pipeB_exec B main H hH hT (k := k)
    (ω' := ω ^ (as.length - 1) % p) as hw (by omega) hp1 hp hp2 hω (Nat.mod_lt _ hp0) has v₁ SA
    ⟨by simp [hSA, hinp],
      by simp [hSA, hout],
      by simp [hSA, hL],
      by intro i; simp [hSA, chirpA, pipeR1, hR],
      by simp [hSA, chirpA, pipeR1],
      by simp [hSA, chirpA, pipeR1, hPw],
      by simp [hSA, chirpA, pipeR1, hKc],
      by simp [hSA, chirpA, pipeR1, crZ],
      by simp [hSA, chirpA, pipeR1, crQ1],
      by simp [hSA, chirpA, pipeR1, crQ2],
      by simp [hSA, chirpA, pipeR1, crP3],
      by simp [hSA, chirpA, pipeR1, crO],
      by simp [hSA, chirpA, pipeR1, crt1],
      by simp [hSA, chirpA, pipeR1, crt2],
      by simp [hSA, chirpA, pipeR1, crt3],
      by simp [hSA, chirpA, pipeR1, crt4],
      by simp [hSA, chirpA, pipeR1, crt5]⟩
    (by simp [hSA, chirpA, pipeR1, hEnt]) (by simp [hSA, chirpA, fieldSyms])
    (by simp [hSA, chirpA, pipeR1, crFt]) (by simp [hSA, chirpA, pipeR1, crFu])
    (by simp [hSA, chirpA]) (by simp [hSA, chirpA]) (by simp [hSA, chirpA])
    (by simp [hSA, chirpA, pipeR1, hWm]) (by simp [hSA, chirpA, pipeR1, length_binSyms]; ring)
    (by simp [hSA, chirpA, pipeR1, crCw]) (by simp [hSA, chirpA, pipeR1, crWc])
    (by simp [hSA, chirpA]) (by simp [hSA, chirpA, pipeR1, crV2])
    (by simp [hSA, chirpA, pipeR1, crXa]) (by simp [hSA, chirpA, pipeR1, crUp])
    (by simp [hSA, chirpA, pipeR1, crNcnt]) gi go
  set SB : Stacks (M.T + 50) M.A := { SA with
    R := M.inputR w p (ω ^ (as.length - 1) % p) as (M.pipeR2 w p ω as SA.R) as.length } with hSB
  -- the third part
  have hdig : ∀ j, as.getD j 0 * chirp p (ω ^ (as.length - 1) % p) j % p < 2 ^ (3 * w) :=
    fun j => lt_of_lt_of_le ((Nat.mod_lt _ hp0).trans hp)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hcB : ∀ m, chirp p ω m < 2 ^ (3 * w) := fun m =>
    lt_of_lt_of_le ((Nat.mod_lt _ hp0).trans hp) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hX : pipeX w p ω as < 2 ^ (3 * w * as.length) := by
    rw [pipeX, pow_mul 2 (3 * w) as.length]; exact revPack_lt _ hdig _
  have hY : pipeY w p ω as < 2 ^ (3 * w * (as.length + as.length)) := by
    rw [pipeY, pow_mul 2 (3 * w) (as.length + as.length)]; exact pack_lt _ hcB _
  obtain ⟨v₃, n₃, hu₃, hn₃, e₃⟩ := M.pipeC_exec B main H hH hT (k := k)
    (ω' := ω ^ (as.length - 1) % p) (n := as.length) (X := pipeX w p ω as)
    (Y := pipeY w p ω as) hw (by omega) hp1 hp hp2 (Nat.mod_lt _ hp0) hX hY v₂ SB
    ⟨by simp [hSB, hSA, hinp],
      by simp [hSB, hSA, hout],
      by simp [hSB, hSA, hL],
      by intro i; simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, hR],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, hPw],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, hKc],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crZ],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crQ1],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crQ2],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crP3],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crO],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crt1],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crt2],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crt3],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crt4],
      by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crt5]⟩
    (by simp [hSB, hSA, inputR, pipeX]) (by simp [hSB, hSA, inputR, pipeR2, pipeY])
    (by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crDw])
    (by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crZp])
    (by simp [hSB, hSA, inputR]) (by simp [hSB, hSA, inputR, length_binSyms])
    (by simp [hSB, hSA, inputR, length_binSyms])
    (by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA])
    (by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, length_binSyms]; ring)
    (by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crTk])
    (by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crO2])
    (by simp [hSB, hSA, inputR, pipeR2, chirpB, chirpA, pipeR1, crOut]) gi go
  refine ⟨v₃, Kc, k, _, by rw [hu₃, hu₂, hu₁], hKc, hk1, hk2, ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₃)) rfl rfl⟩
  omega

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
