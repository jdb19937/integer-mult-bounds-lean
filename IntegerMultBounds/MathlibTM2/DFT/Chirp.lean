module

public import IntegerMultBounds.MathlibTM2.DFT.CountLoop
public import IntegerMultBounds.MathlibTM2.DFT.PipeHost
public import IntegerMultBounds.MathlibTM2.DFT.Regs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The chirp loops

* `M.chirpStep D B C E X …` (`chirpStep_exec`): `C := C E mod p`, `E := E X mod p` (two
  `modMulProg`, each result moved back by `moveBack`).
* `M.chirpRoundA B` (`chirpRoundA_exec`), on the registers of `DFT/Regs.lean`: drop a field of
  the counter `rF`, `rWinv := rE`, push `c` widened to `s = 3 w` bits, most significant bit
  first, onto `rV` (`pushWide`), and `chirpStep` with `X = ω`. `M.chirpRoundB B`: the same
  without `rWinv`.
* `chirpLoopA_exec`, `chirpLoopB_exec`: `n` rounds from the counter `fieldSyms w l`,
  `|l| = n`. From `c m₀ = chirp p ω m₀` and `e = ω ^ m₀ mod p`, round `i` pushes
  `chirp p ω (m₀ + i)`, so `rV` ends with `(binSyms (s (m₀ + n)) (pack B (chirp p ω) (m₀ + n))).reverse`
  (`binSyms_pack_succ_reverse`, `chirp_succ`, `powMod_succ`), and loop A leaves
  `rWinv = ω ^ (n - 1) mod p`.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

open scoped IntegerMultBounds.MathlibTM2.DFT.Reg

namespace IntegerMultBounds.MathlibTM2.DFT

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (D : ℕ) (B : Type)

/-! ### One step of a chirp -/

/-- `C := C E mod p`, `E := E X mod p`. -/
def chirpStep (C E X Z Aa Pw wK Q1 Q2 P3 O t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (M.modMulProg D B C E Z Aa Pw wK Q1 Q2 P3 O t₁ t₂ t₃ t₄ t₅)
    (.seq (hostCode (moveBack (M.dreg D O) (M.dreg D C) (M.dreg D t₁) (M.dreg D t₂)))
      (.seq (M.modMulProg D B E X Z Aa Pw wK Q1 Q2 P3 O t₁ t₂ t₃ t₄ t₅)
        (hostCode (moveBack (M.dreg D O) (M.dreg D E) (M.dreg D t₁) (M.dreg D t₂)))))

theorem chirpStep_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {C E X Z Aa Pw wK Q1 Q2 P3 O t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [C, E, X, Z, Aa, Pw, wK, Q1, Q2, P3, O, t₁, t₂, t₃, t₄, t₅].Nodup) {k w p c e x : ℕ}
    (hw : 1 ≤ w) (hwk : w ≤ k) (hp1 : 2 ^ (w - 1) ≤ p) (hp : p < 2 ^ w) (hc : c < p)
    (he : e < p) (hx : x < p) (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ j, S.L j = [])
    (hR : ∀ i, S.R (M.emb D i) = []) (hC : S.R (M.dreg D C) = binSyms w c)
    (hE : S.R (M.dreg D E) = binSyms w e) (hX : S.R (M.dreg D X) = binSyms w x)
    (hA : S.R (M.dreg D Aa) = binSyms (k + k + 4) (2 ^ (k + w) / p))
    (hPw : S.R (M.dreg D Pw) = binSyms w p) (hK : (S.R (M.dreg D wK)).length = k)
    (hZ : S.R (M.dreg D Z) = []) (hQ1 : S.R (M.dreg D Q1) = []) (hQ2 : S.R (M.dreg D Q2) = [])
    (hP3 : S.R (M.dreg D P3) = []) (hO : S.R (M.dreg D O) = []) (h₁ : S.R (M.dreg D t₁) = [])
    (h₂ : S.R (M.dreg D t₂) = []) (h₃ : S.R (M.dreg D t₃) = []) (h₄ : S.R (M.dreg D t₄) = [])
    (h₅ : S.R (M.dreg D t₅) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ n, v'.user.2 = v.user.2 ∧
      n ≤ (1060 + 18 * H (3 * k + 3)) * k + 1420 + 24 * H (3 * k + 3) ∧
      Exec (M.tab D B main) (M.chirpStep D B C E X Z Aa Pw wK Q1 Q2 P3 O t₁ t₂ t₃ t₄ t₅)
        (dmk v S gi go) n
        (dmk v' { S with
          R := Function.update (Function.update S.R (M.dreg D C) (binSyms w (c * e % p)))
            (M.dreg D E) (binSyms w (e * x % p)) } gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  have hnd : ∀ l : List (Fin D), l.Nodup → (l.map (M.dreg D)).Nodup := fun _ h => M.nodup_dreg D h
  have hnd₂ := hnd [O, C, t₁, t₂] (by regs_nodup)
  have hnd₄ := hnd [O, E, t₁, t₂] (by regs_nodup)
  -- `O := c e`
  obtain ⟨v₁, n₁, hu₁, hn₁, e₁⟩ := M.modMul_exec D B main H hH hT (Xa := C) (Yb := E) (Z := Z)
    (Aa := Aa) (Pw := Pw) (wK := wK) (Q1 := Q1) (Q2 := Q2) (P3 := P3) (O := O) (t₁ := t₁)
    (t₂ := t₂) (t₃ := t₃) (t₄ := t₄) (t₅ := t₅) (by regs_nodup) hw hwk hp1 hp hc he v S hinp
    hout hL hR hC hE hA hPw hK hZ hQ1 hQ2 hP3 hO h₁ h₂ h₃ h₄ h₅ gi go
  set S₁ : Stacks (M.T + D) M.A := { S with
    R := Function.update S.R (M.dreg D O) (binSyms w (c * e % p)) } with hS₁
  -- `C := O`
  obtain ⟨v₂, hu₂, e₂⟩ := moveBack_exec Empty.elim (O := M.dreg D O) (C := M.dreg D C)
    (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂) (by simpa only [List.map_cons, List.map_nil] using hnd₂)
    (w := w) v₁ S₁ (by simp [*]) (by simp [hS₁]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  rw [show S₁.R (M.dreg D O) = binSyms w (c * e % p) by simp [hS₁]] at e₂
  set S₂ : Stacks (M.T + D) M.A := { S₁ with
    R := Function.update (Function.update S₁.R (M.dreg D C) (binSyms w (c * e % p)))
      (M.dreg D O) [] } with hS₂
  -- `O := e x`
  obtain ⟨v₃, n₃, hu₃, hn₃, e₃⟩ := M.modMul_exec D B main H hH hT (Xa := E) (Yb := X) (Z := Z)
    (Aa := Aa) (Pw := Pw) (wK := wK) (Q1 := Q1) (Q2 := Q2) (P3 := P3) (O := O) (t₁ := t₁)
    (t₂ := t₂) (t₃ := t₃) (t₄ := t₄) (t₅ := t₅) (by regs_nodup) hw hwk hp1 hp he hx v₂ S₂
    (by simp [hS₂, hS₁, hinp]) (by simp [hS₂, hS₁, hout]) (by simp [hS₂, hS₁, hL])
    (by intro i; simp [hS₂, hS₁, hR]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm]) (by simp [hS₂])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) gi go
  set S₃ : Stacks (M.T + D) M.A := { S₂ with
    R := Function.update S₂.R (M.dreg D O) (binSyms w (e * x % p)) } with hS₃
  -- `E := O`
  obtain ⟨v₄, hu₄, e₄⟩ := moveBack_exec Empty.elim (O := M.dreg D O) (C := M.dreg D E)
    (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂) (by simpa only [List.map_cons, List.map_nil] using hnd₄)
    (w := w) v₃ S₃ (by simp [*, Ne.symm]) (by simp [hS₃])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
  rw [show S₃.R (M.dreg D O) = binSyms w (e * x % p) by simp [hS₃]] at e₄
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq e₁ (Exec.seq
    (exec_hostCode e₂ gi go) (Exec.seq e₃ (exec_hostCode e₄ gi go)))) rfl ?_⟩
  · have hc' : (1060 + 18 * H (3 * k + 3)) * k =
        2 * ((520 + 9 * H (3 * k + 3)) * k) + 20 * k := by ring
    omega
  · clear e₁ e₂ e₃ e₄
    show dmk v₄ _ gi go = dmk v₄ _ gi go
    congr 1
    simp only [hS₃, hS₂, hS₁]
    clear hS₃ hS₂ hS₁ hnd hnd₂ hnd₄ hn₁ hn₃
    congr 1
    funext j
    by_cases hj1 : j = M.dreg D O
    · subst hj1; simp [*, Ne.symm]
    by_cases hj2 : j = M.dreg D C
    · subst hj2; simp [*]
    by_cases hj3 : j = M.dreg D E
    · subst hj3; simp [*]
    simp [*]

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
