module

public import IntegerMultBounds.MathlibTM2.DFT.ChirpLoop
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The chirped input

* `inputMid Xa O Ow w3 Wc Up Nc t₁ t₂` (`inputMid_exec`, on the host): `Xa` cleared,
  `Up := binSyms s x ++ Up` from `O = binSyms w x` (`pushBlock`), `O` cleared, a tick onto `Nc`.
* `M.inputRound B` (`inputRound_exec`): the next entry `a` of `rEnt` onto `rXa` (`takeField`),
  `rO := a c' mod p` (`modMulProg` with `rC = c'`), `inputMid`, and `chirpStep` with
  `X = rWinv`.
* `inputLoop_exec`: `n = |as|` rounds from `rC = rE = 1`; after round `i` (`inputR`),
  `rUp = binSyms (3 w i) (revPack B x i)` for `x j = a j · chirp p ω' j mod p`, `rC = chirp p ω' j`,
  `rE = ω' ^ i mod p` and `rNcnt` holds `i` ticks.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

open scoped IntegerMultBounds.MathlibTM2.DFT.Reg

namespace IntegerMultBounds.MathlibTM2.DFT

section Mid

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- `Xa` cleared, `Up := binSyms s x ++ Up`, `O` cleared, a tick onto `Nc`. -/
def inputMid (Xa O Ow w3 Wc Up Nc t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bclear Xa) (.seq (pushBlock O Ow w3 Wc Up t₁ t₂) (.seq (bclear O) (pushS Nc tick)))

theorem inputMid_exec {Xa O Ow w3 Wc Up Nc t₁ t₂ : Fin T}
    (hreg : [Xa, O, Ow, w3, Wc, Up, Nc, t₁, t₂].Nodup) {w s x : ℕ} (hws : w ≤ s)
    (hx : x < 2 ^ w) (v : HS T Q A U) (S : Stacks T A) (hXa : (S.R Xa).length = w)
    (hO : S.R O = binSyms w x) (hw3 : (S.R w3).length = s) (hOw : S.R Ow = [])
    (hWc : S.R Wc = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (inputMid Xa O Ow w3 Wc Up Nc t₁ t₂) (mk v S) (10 * w + 20 * s + 37)
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update S.R Xa [])
            Up (binSyms s x ++ S.R Up)) O []) Nc (tick :: S.R Nc) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, -, e₁⟩ := bclear_exec body Xa v S
  rw [hXa] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R Xa [] } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := pushBlock_exec body (O := O) (Ow := Ow) (w3 := w3) (Wc := Wc)
    (Up := Up) (t₁ := t₁) (t₂ := t₂) (by regs_nodup) hws hx v₁ S₁ (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
  rw [show S₁.R Up = S.R Up by simp [hS₁, *, Ne.symm]] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R Up (binSyms s x ++ S.R Up) }
    with hS₂
  obtain ⟨v₃, hu₃, -, e₃⟩ := bclear_exec body O v₂ S₂
  rw [show (S₂.R O).length = w by simp [hS₂, hS₁, *, Ne.symm]] at e₃
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R O [] } with hS₃
  have e₄ := pushS_exec body Nc tick v₃ S₃
  rw [show S₃.R Nc = S.R Nc by simp [hS₃, hS₂, hS₁, *, Ne.symm]] at e₄
  refine ⟨v₃, by rw [hu₃, hu₂, hu₁], Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ e₄)))
    (by ring) ?_⟩
  rfl

end Mid

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (B : Type)

/-- One entry: `rO := a c' mod p`, pushed onto `rUp`, then `chirpStep` with `rWinv`. -/
def inputRound : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B) :=
  .seq (hostCode (takeField (M.dreg 50 rEnt) (M.dreg 50 rXa) (M.dreg 50 rFu)))
    (.seq (M.modMulProg 50 B rXa rC rZ rAa rPw rWK rQ1 rQ2 rP3 rO rt1 rt2 rt3 rt4 rt5)
      (.seq (hostCode (inputMid (M.dreg 50 rXa) (M.dreg 50 rO) (M.dreg 50 rCw) (M.dreg 50 rW3)
          (M.dreg 50 rWc) (M.dreg 50 rUp) (M.dreg 50 rNcnt) (M.dreg 50 rt1) (M.dreg 50 rt2)))
        (M.chirpStep 50 B rC rE rWinv rZ rAa rPw rWK rQ1 rQ2 rP3 rO rt1 rt2 rt3 rt4 rt5)))

/-- The cost bound of an input round. -/
def inputCost (H : ℕ → ℕ) (k : ℕ) : ℕ :=
  (1680 + 27 * H (3 * k + 3)) * k + 2200 + 36 * H (3 * k + 3)

theorem inputRound_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {k w p ω' c e a : ℕ} {l : List ℕ} (hw : 1 ≤ w) (hwk : w ≤ k) (hp1 : 2 ^ (w - 1) ≤ p)
    (hp : p < 2 ^ w) (hc : c < p) (he : e < p) (hω : ω' < p) (ha : a < p)
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (henv : M.ModEnv k w p S) (hEnt : S.R (M.dreg 50 rEnt) = fieldSyms w (a :: l))
    (hXa : S.R (M.dreg 50 rXa) = []) (hFu : S.R (M.dreg 50 rFu) = [])
    (hC : S.R (M.dreg 50 rC) = binSyms w c) (hE : S.R (M.dreg 50 rE) = binSyms w e)
    (hWinv : S.R (M.dreg 50 rWinv) = binSyms w ω') (hW3 : (S.R (M.dreg 50 rW3)).length = 3 * w)
    (hCw : S.R (M.dreg 50 rCw) = []) (hWc : S.R (M.dreg 50 rWc) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ n, v'.user.2 = v.user.2 ∧ n ≤ inputCost H k ∧
      Exec (M.tab 50 B main) (M.inputRound B) (dmk v S gi go) n
        (dmk v' { S with
          R := Function.update (Function.update (Function.update (Function.update
            (Function.update S.R (M.dreg 50 rEnt) (fieldSyms w l)) (M.dreg 50 rUp)
            (binSyms (3 * w) (a * c % p) ++ S.R (M.dreg 50 rUp))) (M.dreg 50 rNcnt)
            (tick :: S.R (M.dreg 50 rNcnt))) (M.dreg 50 rC) (binSyms w (c * e % p)))
            (M.dreg 50 rE) (binSyms w (e * ω' % p)) } gi go) := by
  obtain ⟨hinp, hout, hL, hR, hA, hPw, hK, hZ, hQ1, hQ2, hP3, hO, ht1, ht2, ht3, ht4, ht5⟩ :=
    henv
  -- the entry
  rw [fieldSyms_cons] at hEnt
  obtain ⟨v₁, hu₁, e₁⟩ := takeField_exec Empty.elim (i := M.dreg 50 rEnt) (j := M.dreg 50 rXa)
    (t := M.dreg 50 rFu) (by simp) (by simp) (by simp) (separator_not_mem_binSyms w a) v S hEnt
    hFu hXa
  rw [length_binSyms] at e₁
  set S₁ : Stacks (M.T + 50) M.A := { S with
    R := Function.update (Function.update S.R (M.dreg 50 rEnt) (fieldSyms w l)) (M.dreg 50 rXa)
      (binSyms w a) } with hS₁
  -- `rO := a c`
  obtain ⟨v₂, n₂, hu₂, hn₂, e₂⟩ := M.modMul_exec 50 B main H hH hT (Xa := rXa) (Yb := rC)
    (Z := rZ) (Aa := rAa) (Pw := rPw) (wK := rWK) (Q1 := rQ1) (Q2 := rQ2) (P3 := rP3) (O := rO)
    (t₁ := rt1) (t₂ := rt2) (t₃ := rt3) (t₄ := rt4) (t₅ := rt5) (by decide) hw hwk hp1 hp ha hc
    v₁ S₁ (by simp [hS₁, hinp]) (by simp [hS₁, hout]) (by simp [hS₁, hL])
    (by intro i; simp [hS₁, hR]) (by simp [hS₁]) (by simp [hS₁, hC]) (by simp [hS₁, hA])
    (by simp [hS₁, hPw]) (by simp [hS₁, hK]) (by simp [hS₁, hZ]) (by simp [hS₁, hQ1])
    (by simp [hS₁, hQ2]) (by simp [hS₁, hP3]) (by simp [hS₁, hO]) (by simp [hS₁, ht1])
    (by simp [hS₁, ht2]) (by simp [hS₁, ht3]) (by simp [hS₁, ht4]) (by simp [hS₁, ht5]) gi go
  set S₂ : Stacks (M.T + 50) M.A :=
    { S₁ with R := Function.update S₁.R (M.dreg 50 rO) (binSyms w (a * c % p)) } with hS₂
  -- push it
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp1
  obtain ⟨v₃, hu₃, e₃⟩ := inputMid_exec Empty.elim (Xa := M.dreg 50 rXa) (O := M.dreg 50 rO)
    (Ow := M.dreg 50 rCw) (w3 := M.dreg 50 rW3) (Wc := M.dreg 50 rWc) (Up := M.dreg 50 rUp)
    (Nc := M.dreg 50 rNcnt) (t₁ := M.dreg 50 rt1) (t₂ := M.dreg 50 rt2) (by simp) (w := w)
    (s := 3 * w) (x := a * c % p) (by omega) ((Nat.mod_lt _ hp0).trans hp) v₂ S₂
    (by simp [hS₂, hS₁, length_binSyms]) (by simp [hS₂]) (by simp [hS₂, hS₁, hW3]) (by simp [hS₂, hS₁, hCw]) (by simp [hS₂, hS₁, hWc])
    (by simp [hS₂, hS₁, ht1]) (by simp [hS₂, hS₁, ht2])
  rw [show S₂.R (M.dreg 50 rUp) = S.R (M.dreg 50 rUp) by simp [hS₂, hS₁],
    show S₂.R (M.dreg 50 rNcnt) = S.R (M.dreg 50 rNcnt) by simp [hS₂, hS₁]] at e₃
  set S₃ : Stacks (M.T + 50) M.A := { S₂ with
    R := Function.update (Function.update (Function.update (Function.update S₂.R (M.dreg 50 rXa)
      []) (M.dreg 50 rUp) (binSyms (3 * w) (a * c % p) ++ S.R (M.dreg 50 rUp))) (M.dreg 50 rO)
      []) (M.dreg 50 rNcnt) (tick :: S.R (M.dreg 50 rNcnt)) } with hS₃
  -- the inverse chirp step
  obtain ⟨v₄, n₄, hu₄, hn₄, e₄⟩ := M.chirpStep_exec 50 B main H hH hT (C := rC) (E := rE)
    (X := rWinv) (Z := rZ) (Aa := rAa) (Pw := rPw) (wK := rWK) (Q1 := rQ1) (Q2 := rQ2)
    (P3 := rP3) (O := rO) (t₁ := rt1) (t₂ := rt2) (t₃ := rt3) (t₄ := rt4) (t₅ := rt5) (by decide)
    hw hwk hp1 hp hc he hω v₃ S₃ (by simp [hS₃, hS₂, hS₁, hinp]) (by simp [hS₃, hS₂, hS₁, hout])
    (by simp [hS₃, hS₂, hS₁, hL]) (by intro i; simp [hS₃, hS₂, hS₁, hR])
    (by simp [hS₃, hS₂, hS₁, hC]) (by simp [hS₃, hS₂, hS₁, hE]) (by simp [hS₃, hS₂, hS₁, hWinv])
    (by simp [hS₃, hS₂, hS₁, hA]) (by simp [hS₃, hS₂, hS₁, hPw]) (by simp [hS₃, hS₂, hS₁, hK])
    (by simp [hS₃, hS₂, hS₁, hZ]) (by simp [hS₃, hS₂, hS₁, hQ1]) (by simp [hS₃, hS₂, hS₁, hQ2])
    (by simp [hS₃, hS₂, hS₁, hP3]) (by simp [hS₃]) (by simp [hS₃, hS₂, hS₁, ht1])
    (by simp [hS₃, hS₂, hS₁, ht2]) (by simp [hS₃, hS₂, hS₁, ht3]) (by simp [hS₃, hS₂, hS₁, ht4])
    (by simp [hS₃, hS₂, hS₁, ht5]) gi go
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq (exec_hostCode e₁ gi go)
    (Exec.seq e₂ (Exec.seq (exec_hostCode e₃ gi go) e₄))) rfl ?_⟩
  · have : (1680 + 27 * H (3 * k + 3)) * k =
        (520 + 9 * H (3 * k + 3)) * k + (1060 + 18 * H (3 * k + 3)) * k + 100 * k := by ring
    simp only [inputCost]
    omega
  · clear e₁ e₂ e₃ e₄
    show dmk v₄ _ gi go = dmk v₄ _ gi go
    congr 1
    simp only [hS₃, hS₂, hS₁]
    congr 1
    funext j
    by_cases hj1 : j = M.dreg 50 rE
    · subst hj1; simp
    by_cases hj2 : j = M.dreg 50 rC
    · subst hj2; simp
    by_cases hj3 : j = M.dreg 50 rNcnt
    · subst hj3; simp
    by_cases hj4 : j = M.dreg 50 rO
    · subst hj4; simp [hO]
    by_cases hj5 : j = M.dreg 50 rUp
    · subst hj5; simp
    by_cases hj6 : j = M.dreg 50 rXa
    · subst hj6; simp [hXa]
    by_cases hj7 : j = M.dreg 50 rEnt
    · subst hj7; simp
    simp [hj1, hj2, hj3, hj4, hj5, hj6, hj7]

/-- The registers after `i` input rounds. -/
def inputR (w p ω' : ℕ) (as : List ℕ) (R : Fin (M.T + 50) → List (Fin (M.A + 4))) (i : ℕ) :
    Fin (M.T + 50) → List (Fin (M.A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update R
    (M.dreg 50 rEnt) (fieldSyms w (as.drop i)))
    (M.dreg 50 rUp) (binSyms (3 * w * i)
      (revPack (2 ^ (3 * w)) (fun j => as.getD j 0 * chirp p ω' j % p) i)))
    (M.dreg 50 rNcnt) (List.replicate i tick)) (M.dreg 50 rC) (binSyms w (chirp p ω' i)))
    (M.dreg 50 rE) (binSyms w (ω' ^ i % p))

theorem modEnv_inputR {k w p ω' : ℕ} {as : List ℕ} {S : Stacks (M.T + 50) M.A}
    (h : M.ModEnv k w p S) (i : ℕ) :
    M.ModEnv k w p { S with R := M.inputR w p ω' as S.R i } :=
  M.modEnv_update (M.modEnv_update (M.modEnv_update (M.modEnv_update (M.modEnv_update h rEnt
    (by decide) _) rUp (by decide) _) rNcnt (by decide) _) rC (by decide) _) rE (by decide) _

/-- The input loop: `n = |as|` rounds. -/
theorem inputLoop_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {k w p ω' : ℕ} (as : List ℕ) (hw : 1 ≤ w) (hwk : w ≤ k) (hp1 : 2 ^ (w - 1) ≤ p)
    (hp : p < 2 ^ w) (hp2 : 2 ≤ p) (hω : ω' < p) (has : ∀ a ∈ as, a < p)
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (henv : M.ModEnv k w p S) (hEnt : S.R (M.dreg 50 rEnt) = fieldSyms w as)
    (hXa : S.R (M.dreg 50 rXa) = []) (hFu : S.R (M.dreg 50 rFu) = [])
    (hC : S.R (M.dreg 50 rC) = binSyms w 1) (hE : S.R (M.dreg 50 rE) = binSyms w 1)
    (hUp : S.R (M.dreg 50 rUp) = []) (hNcnt : S.R (M.dreg 50 rNcnt) = [])
    (hWinv : S.R (M.dreg 50 rWinv) = binSyms w ω') (hW3 : (S.R (M.dreg 50 rW3)).length = 3 * w)
    (hCw : S.R (M.dreg 50 rCw) = []) (hWc : S.R (M.dreg 50 rWc) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ n, v'.user.2 = v.user.2 ∧
      n ≤ as.length * (inputCost H k + 2) + 2 ∧
      Exec (M.tab 50 B main) (M.countLoop 50 B (M.dreg 50 rEnt) (M.inputRound B))
        (dmk v S gi go) n (dmk v' { S with R := M.inputR w p ω' as S.R as.length } gi go) := by
  have hp0 : 0 < p := by omega
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp2
  have hR0 : M.inputR w p ω' as S.R 0 = S.R := by
    funext j
    by_cases hj1 : j = M.dreg 50 rE
    · subst hj1; simp [inputR, hE, h1]
    by_cases hj2 : j = M.dreg 50 rC
    · subst hj2; simp [inputR, hC, chirp_zero, h1]
    by_cases hj3 : j = M.dreg 50 rNcnt
    · subst hj3; simp [inputR, hNcnt]
    by_cases hj4 : j = M.dreg 50 rUp
    · subst hj4; simp [inputR, hUp, binSyms]
    by_cases hj5 : j = M.dreg 50 rEnt
    · subst hj5; simp [inputR, hEnt]
    simp [inputR, hj1, hj2, hj3, hj4, hj5]
  obtain ⟨v', S', m, ⟨hu, hS'⟩, hm, e⟩ := M.countLoop_exec 50 B main (M.dreg 50 rEnt)
    (M.inputRound B)
    (fun i v' S' => v'.user.2 = v.user.2 ∧ S' = { S with R := M.inputR w p ω' as S.R i })
    as.length (inputCost H k) gi go (fun _ _ _ _ h => h)
    (fun i v' S' h => by
      rw [h.2]
      simp only [inputR, Function.update_of_ne (show M.dreg 50 rEnt ≠ M.dreg 50 rE by simp),
        Function.update_of_ne (show M.dreg 50 rEnt ≠ M.dreg 50 rC by simp),
        Function.update_of_ne (show M.dreg 50 rEnt ≠ M.dreg 50 rNcnt by simp),
        Function.update_of_ne (show M.dreg 50 rEnt ≠ M.dreg 50 rUp by simp),
        Function.update_self]
      rw [fieldSyms_head, Ne, List.drop_eq_nil_iff]
      omega)
    (fun i hi v' S' h => by
      obtain ⟨hu', rfl⟩ := h
      obtain ⟨v'', n, hu'', hn, e⟩ := M.inputRound_exec B main H hH hT
        (c := chirp p ω' i) (e := ω' ^ i % p) (a := as[i]) (l := as.drop (i + 1)) hw hwk hp1 hp
        (Nat.mod_lt _ hp0) (Nat.mod_lt _ hp0) hω (has _ (List.getElem_mem hi)) v' _
        (M.modEnv_inputR (ω' := ω') (as := as) henv i)
        (by rw [← List.drop_eq_getElem_cons hi]; simp [inputR])
        (by simp [inputR, hXa]) (by simp [inputR, hFu])
        (by simp only [inputR, Function.update_self,
          Function.update_of_ne (show M.dreg 50 rC ≠ M.dreg 50 rE by simp)])
        (by simp only [inputR, Function.update_self]) (by simp [inputR, hWinv])
        (by simp [inputR, hW3]) (by simp [inputR, hCw]) (by simp [inputR, hWc]) gi go
      refine ⟨v'', _, n, ⟨hu''.trans hu', ?_⟩, hn, e⟩
      congr 1
      funext j
      by_cases hj1 : j = M.dreg 50 rE
      · subst hj1
        simp only [inputR, Function.update_self]
        rw [powMod_succ, Nat.mod_eq_of_lt hω]
      by_cases hj2 : j = M.dreg 50 rC
      · subst hj2
        simp [inputR, chirp_succ]
      by_cases hj3 : j = M.dreg 50 rNcnt
      · subst hj3
        simp [inputR, List.replicate_succ]
      by_cases hj4 : j = M.dreg 50 rUp
      · subst hj4
        simp only [inputR, Function.update_of_ne (show M.dreg 50 rUp ≠ M.dreg 50 rE by simp),
          Function.update_of_ne (show M.dreg 50 rUp ≠ M.dreg 50 rC by simp),
          Function.update_of_ne (show M.dreg 50 rUp ≠ M.dreg 50 rNcnt by simp),
          Function.update_self]
        have hx : as.getD i 0 * chirp p ω' i % p < 2 ^ (3 * w) :=
          lt_of_lt_of_le ((Nat.mod_lt _ hp0).trans hp)
            (Nat.pow_le_pow_right (by norm_num) (by omega))
        rw [← binSyms_revPack_succ (fun j => as.getD j 0 * chirp p ω' j % p) hx,
          List.getD_eq_getElem _ _ hi]
      by_cases hj5 : j = M.dreg 50 rEnt
      · subst hj5
        simp [inputR]
      simp [inputR, hj1, hj2, hj3, hj4, hj5])
    v S ⟨rfl, by rw [hR0]⟩
  subst hS'
  exact ⟨v', m, hu, hm, e⟩

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
