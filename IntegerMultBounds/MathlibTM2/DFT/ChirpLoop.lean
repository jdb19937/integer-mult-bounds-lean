module

public import IntegerMultBounds.MathlibTM2.DFT.Chirp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The chirp loops on the pipeline registers

`ModEnv k w p S`: the multiplier's stacks are empty, `rAa` holds `μ = ⌊2 ^ (k + w) / p⌋`, `rPw`
holds `p`, `rWK` has `k` symbols and the scratch registers of `modMulProg` are empty
(`modEnv_update`: kept by updates of other registers).

* `chirpRoundA_exec`: one round of loop A (`dropField`, `copyOver`, `pushWide`, `chirpStep`).
* `chirpLoopA_exec`: loop A over the counter `rF = fieldSyms w l` from `rC = rE = rWinv = 1`,
  `rV = []`; after round `i`, `chirpA R i` holds `rC = chirp p ω i`, `rE = ω ^ i mod p`,
  `rWinv = ω ^ (i - 1) mod p` and `rV = (binSyms (3 w i) (pack B (chirp p ω) i)).reverse`.
* `chirpRoundB_exec`, `chirpLoopB_exec`: loop B, the same rounds without `rWinv`, continuing
  from `m₀` chirps (`chirpB`).
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

open scoped IntegerMultBounds.MathlibTM2.DFT.Reg

namespace IntegerMultBounds.MathlibTM2.DFT

theorem fieldSyms_head {A : ℕ} (w : ℕ) (l : List ℕ) :
    ((fieldSyms w l : List (Fin (A + 4))).head?.isSome = true) ↔ l ≠ [] := by
  cases l with
  | nil => simp [fieldSyms]
  | cons x l => simp [fieldSyms_cons]

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (B : Type)

/-- The registers of the reduction blocks. -/
def ModEnv (k w p : ℕ) (S : Stacks (M.T + 50) M.A) : Prop :=
  S.inp = [] ∧ S.out = [] ∧ (∀ j, S.L j = []) ∧ (∀ i, S.R (M.emb 50 i) = []) ∧
    S.R (M.dreg 50 rAa) = binSyms (k + k + 4) (2 ^ (k + w) / p) ∧
    S.R (M.dreg 50 rPw) = binSyms w p ∧ (S.R (M.dreg 50 rWK)).length = k ∧
    S.R (M.dreg 50 rZ) = [] ∧ S.R (M.dreg 50 rQ1) = [] ∧ S.R (M.dreg 50 rQ2) = [] ∧
    S.R (M.dreg 50 rP3) = [] ∧ S.R (M.dreg 50 rO) = [] ∧ S.R (M.dreg 50 rt1) = [] ∧
    S.R (M.dreg 50 rt2) = [] ∧ S.R (M.dreg 50 rt3) = [] ∧ S.R (M.dreg 50 rt4) = [] ∧
    S.R (M.dreg 50 rt5) = []

theorem modEnv_update {k w p : ℕ} {S : Stacks (M.T + 50) M.A} (h : M.ModEnv k w p S)
    (j : Fin 50) (hj : j ∉ [rAa, rPw, rWK, rZ, rQ1, rQ2, rP3, rO, rt1, rt2, rt3, rt4, rt5])
    (x : List (Fin (M.A + 4))) :
    M.ModEnv k w p { S with R := Function.update S.R (M.dreg 50 j) x } := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hj
  obtain ⟨hinp, hout, hL, hR, hA, hPw, hK, hZ, hQ1, hQ2, hP3, hO, ht1, ht2, ht3, ht4, ht5⟩ := h
  refine ⟨hinp, hout, hL, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [*, Ne.symm]

/-- The cost bound of a chirp round. -/
def chirpCost (H : ℕ → ℕ) (k : ℕ) : ℕ := (1130 + 18 * H (3 * k + 3)) * k + 1500 + 24 * H (3 * k + 3)

/-! ### Loop A -/

/-- Drop a field of `rF`, `rWinv := rE`, push `rC` widened onto `rV`, `chirpStep` with `ω`. -/
def chirpRoundA : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B) :=
  .seq (hostCode (dropField (M.dreg 50 rF) (M.dreg 50 rFt) (M.dreg 50 rFu)))
    (.seq (hostCode (copyOver (M.dreg 50 rE) (M.dreg 50 rWinv) (M.dreg 50 rt1) (M.dreg 50 rt2)))
      (.seq (hostCode (pushWide (M.dreg 50 rC) (M.dreg 50 rCw) (M.dreg 50 rW3) (M.dreg 50 rWc)
          (M.dreg 50 rV) (M.dreg 50 rt1) (M.dreg 50 rt2)))
        (M.chirpStep 50 B rC rE rWm rZ rAa rPw rWK rQ1 rQ2 rP3 rO rt1 rt2 rt3 rt4 rt5)))

theorem chirpRoundA_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {k w p ω c e x : ℕ} {l : List ℕ} (hw : 1 ≤ w) (hwk : w ≤ k) (hp1 : 2 ^ (w - 1) ≤ p)
    (hp : p < 2 ^ w) (hc : c < p) (he : e < p) (hω : ω < p)
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (henv : M.ModEnv k w p S) (hF : S.R (M.dreg 50 rF) = fieldSyms w (x :: l))
    (hFt : S.R (M.dreg 50 rFt) = []) (hFu : S.R (M.dreg 50 rFu) = [])
    (hWinv : (S.R (M.dreg 50 rWinv)).length = w) (hC : S.R (M.dreg 50 rC) = binSyms w c)
    (hE : S.R (M.dreg 50 rE) = binSyms w e) (hWm : S.R (M.dreg 50 rWm) = binSyms w ω)
    (hW3 : (S.R (M.dreg 50 rW3)).length = 3 * w) (hCw : S.R (M.dreg 50 rCw) = [])
    (hWc : S.R (M.dreg 50 rWc) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ n, v'.user.2 = v.user.2 ∧ n ≤ chirpCost H k ∧
      Exec (M.tab 50 B main) (M.chirpRoundA B) (dmk v S gi go) n
        (dmk v' { S with
          R := Function.update (Function.update (Function.update (Function.update
            (Function.update S.R (M.dreg 50 rF) (fieldSyms w l)) (M.dreg 50 rWinv)
            (binSyms w e)) (M.dreg 50 rV) ((binSyms (3 * w) c).reverse ++ S.R (M.dreg 50 rV)))
            (M.dreg 50 rC) (binSyms w (c * e % p))) (M.dreg 50 rE) (binSyms w (e * ω % p)) }
          gi go) := by
  obtain ⟨hinp, hout, hL, hR, hA, hPw, hK, hZ, hQ1, hQ2, hP3, hO, ht1, ht2, ht3, ht4, ht5⟩ :=
    henv
  -- drop a field
  obtain ⟨v₁, hu₁, e₁⟩ := dropField_exec Empty.elim (F := M.dreg 50 rF) (Ft := M.dreg 50 rFt)
    (Fu := M.dreg 50 rFu) (by simp) v S hF hFt hFu
  set S₁ : Stacks (M.T + 50) M.A :=
    { S with R := Function.update S.R (M.dreg 50 rF) (fieldSyms w l) } with hS₁
  -- `rWinv := rE`
  obtain ⟨v₂, hu₂, e₂⟩ := copyOver_exec Empty.elim (E := M.dreg 50 rE) (W := M.dreg 50 rWinv)
    (t₁ := M.dreg 50 rt1) (t₂ := M.dreg 50 rt2) (by simp) (w := w) (w' := w) v₁ S₁
    (by simp [hS₁, hWinv]) (by simp [hS₁, hE]) (by simp [hS₁, ht1]) (by simp [hS₁, ht2])
  rw [show S₁.R (M.dreg 50 rE) = binSyms w e by simp [hS₁, hE]] at e₂
  set S₂ : Stacks (M.T + 50) M.A :=
    { S₁ with R := Function.update S₁.R (M.dreg 50 rWinv) (binSyms w e) } with hS₂
  -- push the chirp
  obtain ⟨v₃, hu₃, e₃⟩ := pushWide_exec Empty.elim (C := M.dreg 50 rC) (Cw := M.dreg 50 rCw)
    (w3 := M.dreg 50 rW3) (Wc := M.dreg 50 rWc) (V := M.dreg 50 rV) (t₁ := M.dreg 50 rt1)
    (t₂ := M.dreg 50 rt2) (by simp) (w := w) (s := 3 * w) (c := c) (by omega) (hc.trans hp) v₂
    S₂ (by simp [hS₂, hS₁, hC]) (by simp [hS₂, hS₁, hW3]) (by simp [hS₂, hS₁, hCw])
    (by simp [hS₂, hS₁, hWc]) (by simp [hS₂, hS₁, ht1]) (by simp [hS₂, hS₁, ht2])
  rw [show S₂.R (M.dreg 50 rV) = S.R (M.dreg 50 rV) by simp [hS₂, hS₁]] at e₃
  set S₃ : Stacks (M.T + 50) M.A := { S₂ with
    R := Function.update S₂.R (M.dreg 50 rV) ((binSyms (3 * w) c).reverse ++ S.R (M.dreg 50 rV)) }
    with hS₃
  -- the chirp step
  obtain ⟨v₄, n₄, hu₄, hn₄, e₄⟩ := M.chirpStep_exec 50 B main H hH hT (C := rC) (E := rE)
    (X := rWm) (Z := rZ) (Aa := rAa) (Pw := rPw) (wK := rWK) (Q1 := rQ1) (Q2 := rQ2) (P3 := rP3)
    (O := rO) (t₁ := rt1) (t₂ := rt2) (t₃ := rt3) (t₄ := rt4) (t₅ := rt5) (by decide) hw hwk hp1
    hp hc he hω v₃ S₃ (by simp [hS₃, hS₂, hS₁, hinp]) (by simp [hS₃, hS₂, hS₁, hout])
    (by simp [hS₃, hS₂, hS₁, hL]) (by intro i; simp [hS₃, hS₂, hS₁, hR])
    (by simp [hS₃, hS₂, hS₁, hC]) (by simp [hS₃, hS₂, hS₁, hE]) (by simp [hS₃, hS₂, hS₁, hWm])
    (by simp [hS₃, hS₂, hS₁, hA]) (by simp [hS₃, hS₂, hS₁, hPw]) (by simp [hS₃, hS₂, hS₁, hK])
    (by simp [hS₃, hS₂, hS₁, hZ]) (by simp [hS₃, hS₂, hS₁, hQ1]) (by simp [hS₃, hS₂, hS₁, hQ2])
    (by simp [hS₃, hS₂, hS₁, hP3]) (by simp [hS₃, hS₂, hS₁, hO]) (by simp [hS₃, hS₂, hS₁, ht1])
    (by simp [hS₃, hS₂, hS₁, ht2]) (by simp [hS₃, hS₂, hS₁, ht3]) (by simp [hS₃, hS₂, hS₁, ht4])
    (by simp [hS₃, hS₂, hS₁, ht5]) gi go
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq (exec_hostCode e₁ gi go)
    (Exec.seq (exec_hostCode e₂ gi go) (Exec.seq (exec_hostCode e₃ gi go) e₄))) rfl ?_⟩
  · have : (1130 + 18 * H (3 * k + 3)) * k = (1060 + 18 * H (3 * k + 3)) * k + 70 * k := by ring
    simp only [chirpCost]
    omega
  · rfl

/-- The registers after `i` rounds of loop A. -/
def chirpA (w p ω : ℕ) (l : List ℕ) (R : Fin (M.T + 50) → List (Fin (M.A + 4))) (i : ℕ) :
    Fin (M.T + 50) → List (Fin (M.A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update R
    (M.dreg 50 rF) (fieldSyms w (l.drop i))) (M.dreg 50 rWinv) (binSyms w (ω ^ (i - 1) % p)))
    (M.dreg 50 rV) (binSyms (3 * w * i) (pack (2 ^ (3 * w)) (chirp p ω) i)).reverse)
    (M.dreg 50 rC) (binSyms w (chirp p ω i))) (M.dreg 50 rE) (binSyms w (ω ^ i % p))

theorem modEnv_chirpA {k w p ω : ℕ} {l : List ℕ} {S : Stacks (M.T + 50) M.A}
    (h : M.ModEnv k w p S) (i : ℕ) :
    M.ModEnv k w p { S with R := M.chirpA w p ω l S.R i } :=
  M.modEnv_update (M.modEnv_update (M.modEnv_update (M.modEnv_update (M.modEnv_update h rF
    (by decide) _) rWinv (by decide) _) rV (by decide) _) rC (by decide) _) rE (by decide) _

/-- Loop A: `n = |l|` rounds. -/
theorem chirpLoopA_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {k w p ω : ℕ} (l : List ℕ) (hw : 1 ≤ w) (hwk : w ≤ k) (hp1 : 2 ^ (w - 1) ≤ p)
    (hp : p < 2 ^ w) (hp2 : 2 ≤ p) (hω : ω < p)
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (henv : M.ModEnv k w p S) (hF : S.R (M.dreg 50 rF) = fieldSyms w l)
    (hFt : S.R (M.dreg 50 rFt) = []) (hFu : S.R (M.dreg 50 rFu) = [])
    (hWinv : S.R (M.dreg 50 rWinv) = binSyms w 1) (hC : S.R (M.dreg 50 rC) = binSyms w 1)
    (hE : S.R (M.dreg 50 rE) = binSyms w 1) (hV : S.R (M.dreg 50 rV) = [])
    (hWm : S.R (M.dreg 50 rWm) = binSyms w ω) (hW3 : (S.R (M.dreg 50 rW3)).length = 3 * w)
    (hCw : S.R (M.dreg 50 rCw) = []) (hWc : S.R (M.dreg 50 rWc) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ n, v'.user.2 = v.user.2 ∧
      n ≤ l.length * (chirpCost H k + 2) + 2 ∧
      Exec (M.tab 50 B main) (M.countLoop 50 B (M.dreg 50 rF) (M.chirpRoundA B))
        (dmk v S gi go) n (dmk v' { S with R := M.chirpA w p ω l S.R l.length } gi go) := by
  have hp0 : 0 < p := by omega
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp2
  have hcB : ∀ m, chirp p ω m < 2 ^ (3 * w) := fun m =>
    lt_of_lt_of_le ((Nat.mod_lt _ hp0).trans hp) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hR0 : M.chirpA w p ω l S.R 0 = S.R := by
    funext j
    by_cases hj1 : j = M.dreg 50 rE
    · subst hj1; simp [chirpA, hE, h1]
    by_cases hj2 : j = M.dreg 50 rC
    · subst hj2; simp [chirpA, hC, chirp_zero, h1]
    by_cases hj3 : j = M.dreg 50 rV
    · subst hj3; simp [chirpA, hV, binSyms]
    by_cases hj4 : j = M.dreg 50 rWinv
    · subst hj4; simp [chirpA, hWinv, h1]
    by_cases hj5 : j = M.dreg 50 rF
    · subst hj5; simp [chirpA, hF]
    simp [chirpA, hj1, hj2, hj3, hj4, hj5]
  obtain ⟨v', S', m, ⟨hu, hS'⟩, hm, e⟩ := M.countLoop_exec 50 B main (M.dreg 50 rF)
    (M.chirpRoundA B)
    (fun i v' S' => v'.user.2 = v.user.2 ∧ S' = { S with R := M.chirpA w p ω l S.R i })
    l.length (chirpCost H k) gi go (fun _ _ _ _ h => h)
    (fun i v' S' h => by
      rw [h.2]
      simp only [chirpA, Function.update_of_ne (show M.dreg 50 rF ≠ M.dreg 50 rE by simp),
        Function.update_of_ne (show M.dreg 50 rF ≠ M.dreg 50 rC by simp),
        Function.update_of_ne (show M.dreg 50 rF ≠ M.dreg 50 rV by simp),
        Function.update_of_ne (show M.dreg 50 rF ≠ M.dreg 50 rWinv by simp),
        Function.update_self]
      rw [fieldSyms_head, Ne, List.drop_eq_nil_iff]
      omega)
    (fun i hi v' S' h => by
      obtain ⟨hu', rfl⟩ := h
      obtain ⟨v'', n, hu'', hn, e⟩ := M.chirpRoundA_exec B main H hH hT (c := chirp p ω i)
        (e := ω ^ i % p) (x := l[i]) (l := l.drop (i + 1)) hw hwk hp1 hp (Nat.mod_lt _ hp0)
        (Nat.mod_lt _ hp0) hω v' _ (M.modEnv_chirpA (ω := ω) (l := l) henv i)
        (by rw [← List.drop_eq_getElem_cons hi]; simp [chirpA])
        (by simp [chirpA, hFt]) (by simp [chirpA, hFu]) (by simp [chirpA, length_binSyms])
        (by simp only [chirpA, Function.update_self,
          Function.update_of_ne (show M.dreg 50 rC ≠ M.dreg 50 rE by simp)])
        (by simp only [chirpA, Function.update_self]) (by simp [chirpA, hWm])
        (by simp [chirpA, hW3])
        (by simp [chirpA, hCw]) (by simp [chirpA, hWc]) gi go
      refine ⟨v'', _, n, ⟨hu''.trans hu', ?_⟩, hn, e⟩
      congr 1
      funext j
      by_cases hj1 : j = M.dreg 50 rE
      · subst hj1
        simp only [chirpA, Function.update_self]
        rw [powMod_succ, Nat.mod_eq_of_lt hω]
      by_cases hj2 : j = M.dreg 50 rC
      · subst hj2
        simp [chirpA, chirp_succ]
      by_cases hj3 : j = M.dreg 50 rV
      · subst hj3
        simp only [chirpA, Function.update_of_ne (show M.dreg 50 rV ≠ M.dreg 50 rE by simp),
          Function.update_of_ne (show M.dreg 50 rV ≠ M.dreg 50 rC by simp), Function.update_self]
        exact binSyms_pack_succ_reverse (chirp p ω) hcB i
      by_cases hj4 : j = M.dreg 50 rWinv
      · subst hj4
        simp [chirpA]
      by_cases hj5 : j = M.dreg 50 rF
      · subst hj5
        simp [chirpA]
      simp [chirpA, hj1, hj2, hj3, hj4, hj5])
    v S ⟨rfl, by rw [hR0]⟩
  subst hS'
  exact ⟨v', m, hu, hm, e⟩

/-! ### Loop B -/

/-- Drop a field of `rF`, push `rC` widened onto `rV`, `chirpStep` with `ω`. -/
def chirpRoundB : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B) :=
  .seq (hostCode (dropField (M.dreg 50 rF) (M.dreg 50 rFt) (M.dreg 50 rFu)))
    (.seq (hostCode (pushWide (M.dreg 50 rC) (M.dreg 50 rCw) (M.dreg 50 rW3) (M.dreg 50 rWc)
        (M.dreg 50 rV) (M.dreg 50 rt1) (M.dreg 50 rt2)))
      (M.chirpStep 50 B rC rE rWm rZ rAa rPw rWK rQ1 rQ2 rP3 rO rt1 rt2 rt3 rt4 rt5))

theorem chirpRoundB_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {k w p ω c e x : ℕ} {l : List ℕ} (hw : 1 ≤ w) (hwk : w ≤ k) (hp1 : 2 ^ (w - 1) ≤ p)
    (hp : p < 2 ^ w) (hc : c < p) (he : e < p) (hω : ω < p)
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (henv : M.ModEnv k w p S) (hF : S.R (M.dreg 50 rF) = fieldSyms w (x :: l))
    (hFt : S.R (M.dreg 50 rFt) = []) (hFu : S.R (M.dreg 50 rFu) = [])
    (hC : S.R (M.dreg 50 rC) = binSyms w c) (hE : S.R (M.dreg 50 rE) = binSyms w e)
    (hWm : S.R (M.dreg 50 rWm) = binSyms w ω) (hW3 : (S.R (M.dreg 50 rW3)).length = 3 * w)
    (hCw : S.R (M.dreg 50 rCw) = []) (hWc : S.R (M.dreg 50 rWc) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ n, v'.user.2 = v.user.2 ∧ n ≤ chirpCost H k ∧
      Exec (M.tab 50 B main) (M.chirpRoundB B) (dmk v S gi go) n
        (dmk v' { S with
          R := Function.update (Function.update (Function.update
            (Function.update S.R (M.dreg 50 rF) (fieldSyms w l))
            (M.dreg 50 rV) ((binSyms (3 * w) c).reverse ++ S.R (M.dreg 50 rV)))
            (M.dreg 50 rC) (binSyms w (c * e % p))) (M.dreg 50 rE) (binSyms w (e * ω % p)) }
          gi go) := by
  obtain ⟨hinp, hout, hL, hR, hA, hPw, hK, hZ, hQ1, hQ2, hP3, hO, ht1, ht2, ht3, ht4, ht5⟩ :=
    henv
  obtain ⟨v₁, hu₁, e₁⟩ := dropField_exec Empty.elim (F := M.dreg 50 rF) (Ft := M.dreg 50 rFt)
    (Fu := M.dreg 50 rFu) (by simp) v S hF hFt hFu
  set S₁ : Stacks (M.T + 50) M.A :=
    { S with R := Function.update S.R (M.dreg 50 rF) (fieldSyms w l) } with hS₁
  obtain ⟨v₃, hu₃, e₃⟩ := pushWide_exec Empty.elim (C := M.dreg 50 rC) (Cw := M.dreg 50 rCw)
    (w3 := M.dreg 50 rW3) (Wc := M.dreg 50 rWc) (V := M.dreg 50 rV) (t₁ := M.dreg 50 rt1)
    (t₂ := M.dreg 50 rt2) (by simp) (w := w) (s := 3 * w) (c := c) (by omega) (hc.trans hp) v₁
    S₁ (by simp [hS₁, hC]) (by simp [hS₁, hW3]) (by simp [hS₁, hCw])
    (by simp [hS₁, hWc]) (by simp [hS₁, ht1]) (by simp [hS₁, ht2])
  rw [show S₁.R (M.dreg 50 rV) = S.R (M.dreg 50 rV) by simp [hS₁]] at e₃
  set S₃ : Stacks (M.T + 50) M.A := { S₁ with
    R := Function.update S₁.R (M.dreg 50 rV) ((binSyms (3 * w) c).reverse ++ S.R (M.dreg 50 rV)) }
    with hS₃
  obtain ⟨v₄, n₄, hu₄, hn₄, e₄⟩ := M.chirpStep_exec 50 B main H hH hT (C := rC) (E := rE)
    (X := rWm) (Z := rZ) (Aa := rAa) (Pw := rPw) (wK := rWK) (Q1 := rQ1) (Q2 := rQ2) (P3 := rP3)
    (O := rO) (t₁ := rt1) (t₂ := rt2) (t₃ := rt3) (t₄ := rt4) (t₅ := rt5) (by decide) hw hwk hp1
    hp hc he hω v₃ S₃ (by simp [hS₃, hS₁, hinp]) (by simp [hS₃, hS₁, hout])
    (by simp [hS₃, hS₁, hL]) (by intro i; simp [hS₃, hS₁, hR])
    (by simp [hS₃, hS₁, hC]) (by simp [hS₃, hS₁, hE]) (by simp [hS₃, hS₁, hWm])
    (by simp [hS₃, hS₁, hA]) (by simp [hS₃, hS₁, hPw]) (by simp [hS₃, hS₁, hK])
    (by simp [hS₃, hS₁, hZ]) (by simp [hS₃, hS₁, hQ1]) (by simp [hS₃, hS₁, hQ2])
    (by simp [hS₃, hS₁, hP3]) (by simp [hS₃, hS₁, hO]) (by simp [hS₃, hS₁, ht1])
    (by simp [hS₃, hS₁, ht2]) (by simp [hS₃, hS₁, ht3]) (by simp [hS₃, hS₁, ht4])
    (by simp [hS₃, hS₁, ht5]) gi go
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₁], ?_, Exec.cast (Exec.seq (exec_hostCode e₁ gi go)
    (Exec.seq (exec_hostCode e₃ gi go) e₄)) rfl ?_⟩
  · have : (1130 + 18 * H (3 * k + 3)) * k = (1060 + 18 * H (3 * k + 3)) * k + 70 * k := by ring
    simp only [chirpCost]
    omega
  · rfl

/-- The registers after `i` rounds of loop B, from `m₀` chirps. -/
def chirpB (w p ω m₀ : ℕ) (l : List ℕ) (R : Fin (M.T + 50) → List (Fin (M.A + 4))) (i : ℕ) :
    Fin (M.T + 50) → List (Fin (M.A + 4)) :=
  Function.update (Function.update (Function.update (Function.update R
    (M.dreg 50 rF) (fieldSyms w (l.drop i)))
    (M.dreg 50 rV) (binSyms (3 * w * (m₀ + i)) (pack (2 ^ (3 * w)) (chirp p ω) (m₀ + i))).reverse)
    (M.dreg 50 rC) (binSyms w (chirp p ω (m₀ + i)))) (M.dreg 50 rE)
    (binSyms w (ω ^ (m₀ + i) % p))

theorem modEnv_chirpB {k w p ω m₀ : ℕ} {l : List ℕ} {S : Stacks (M.T + 50) M.A}
    (h : M.ModEnv k w p S) (i : ℕ) :
    M.ModEnv k w p { S with R := M.chirpB w p ω m₀ l S.R i } :=
  M.modEnv_update (M.modEnv_update (M.modEnv_update (M.modEnv_update h rF
    (by decide) _) rV (by decide) _) rC (by decide) _) rE (by decide) _

/-- Loop B: `n = |l|` rounds after `m₀` chirps. -/
theorem chirpLoopB_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {k w p ω m₀ : ℕ} (l : List ℕ) (hw : 1 ≤ w) (hwk : w ≤ k) (hp1 : 2 ^ (w - 1) ≤ p)
    (hp : p < 2 ^ w) (hω : ω < p)
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (henv : M.ModEnv k w p S) (hF : S.R (M.dreg 50 rF) = fieldSyms w l)
    (hFt : S.R (M.dreg 50 rFt) = []) (hFu : S.R (M.dreg 50 rFu) = [])
    (hC : S.R (M.dreg 50 rC) = binSyms w (chirp p ω m₀))
    (hE : S.R (M.dreg 50 rE) = binSyms w (ω ^ m₀ % p))
    (hV : S.R (M.dreg 50 rV) = (binSyms (3 * w * m₀) (pack (2 ^ (3 * w)) (chirp p ω) m₀)).reverse)
    (hWm : S.R (M.dreg 50 rWm) = binSyms w ω) (hW3 : (S.R (M.dreg 50 rW3)).length = 3 * w)
    (hCw : S.R (M.dreg 50 rCw) = []) (hWc : S.R (M.dreg 50 rWc) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ n, v'.user.2 = v.user.2 ∧
      n ≤ l.length * (chirpCost H k + 2) + 2 ∧
      Exec (M.tab 50 B main) (M.countLoop 50 B (M.dreg 50 rF) (M.chirpRoundB B))
        (dmk v S gi go) n (dmk v' { S with R := M.chirpB w p ω m₀ l S.R l.length } gi go) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp1
  have hcB : ∀ m, chirp p ω m < 2 ^ (3 * w) := fun m =>
    lt_of_lt_of_le ((Nat.mod_lt _ hp0).trans hp) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hR0 : M.chirpB w p ω m₀ l S.R 0 = S.R := by
    funext j
    by_cases hj1 : j = M.dreg 50 rE
    · subst hj1; simp [chirpB, hE]
    by_cases hj2 : j = M.dreg 50 rC
    · subst hj2; simp [chirpB, hC]
    by_cases hj3 : j = M.dreg 50 rV
    · subst hj3; simp [chirpB, hV]
    by_cases hj5 : j = M.dreg 50 rF
    · subst hj5; simp [chirpB, hF]
    simp [chirpB, hj1, hj2, hj3, hj5]
  obtain ⟨v', S', m, ⟨hu, hS'⟩, hm, e⟩ := M.countLoop_exec 50 B main (M.dreg 50 rF)
    (M.chirpRoundB B)
    (fun i v' S' => v'.user.2 = v.user.2 ∧ S' = { S with R := M.chirpB w p ω m₀ l S.R i })
    l.length (chirpCost H k) gi go (fun _ _ _ _ h => h)
    (fun i v' S' h => by
      rw [h.2]
      simp only [chirpB, Function.update_of_ne (show M.dreg 50 rF ≠ M.dreg 50 rE by simp),
        Function.update_of_ne (show M.dreg 50 rF ≠ M.dreg 50 rC by simp),
        Function.update_of_ne (show M.dreg 50 rF ≠ M.dreg 50 rV by simp),
        Function.update_self]
      rw [fieldSyms_head, Ne, List.drop_eq_nil_iff]
      omega)
    (fun i hi v' S' h => by
      obtain ⟨hu', rfl⟩ := h
      obtain ⟨v'', n, hu'', hn, e⟩ := M.chirpRoundB_exec B main H hH hT
        (c := chirp p ω (m₀ + i)) (e := ω ^ (m₀ + i) % p) (x := l[i]) (l := l.drop (i + 1)) hw hwk
        hp1 hp (Nat.mod_lt _ hp0) (Nat.mod_lt _ hp0) hω v' _
        (M.modEnv_chirpB (ω := ω) (m₀ := m₀) (l := l) henv i)
        (by rw [← List.drop_eq_getElem_cons hi]; simp [chirpB])
        (by simp [chirpB, hFt]) (by simp [chirpB, hFu])
        (by simp only [chirpB, Function.update_self,
          Function.update_of_ne (show M.dreg 50 rC ≠ M.dreg 50 rE by simp)])
        (by simp only [chirpB, Function.update_self]) (by simp [chirpB, hWm])
        (by simp [chirpB, hW3]) (by simp [chirpB, hCw]) (by simp [chirpB, hWc]) gi go
      refine ⟨v'', _, n, ⟨hu''.trans hu', ?_⟩, hn, e⟩
      congr 1
      funext j
      by_cases hj1 : j = M.dreg 50 rE
      · subst hj1
        simp only [chirpB, Function.update_self]
        rw [← Nat.add_assoc, powMod_succ, Nat.mod_eq_of_lt hω]
      by_cases hj2 : j = M.dreg 50 rC
      · subst hj2
        simp [chirpB, ← Nat.add_assoc, chirp_succ]
      by_cases hj3 : j = M.dreg 50 rV
      · subst hj3
        simp only [chirpB, Function.update_of_ne (show M.dreg 50 rV ≠ M.dreg 50 rE by simp),
          Function.update_of_ne (show M.dreg 50 rV ≠ M.dreg 50 rC by simp), Function.update_self]
        rw [← Nat.add_assoc]
        exact binSyms_pack_succ_reverse (chirp p ω) hcB (m₀ + i)
      by_cases hj5 : j = M.dreg 50 rF
      · subst hj5
        simp [chirpB]
      simp [chirpB, hj1, hj2, hj3, hj5])
    v S ⟨rfl, by rw [hR0]⟩
  subst hS'
  exact ⟨v', m, hu, hm, e⟩

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
