module

public import IntegerMultBounds.MathlibTM2.DFT.Input
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unpacking the product

* `M.unpackRound B` (`unpackRound_exec`): a tick off `rNcnt`, the low `s = 3 w` bits of the
  product `rZp` onto `rTk` (`splitLow`), `rO := T mod p` (`barrettProg`), `rO2 := (T mod p) c'
  mod p` (`modMulProg` with `rC = c'`), `emitNat` onto `rOut`, and `chirpStep` with `rWinv`.
* `unpackLoop_exec`: `n` rounds from `rZp = binSyms (s m) Y`, `n ≤ m`, `rC = rE = 1`, `rOut`
  empty; round `k` emits `unpackVal p ω' w Y k = ((Y / 2 ^ (s k)) mod 2 ^ s mod p) · chirp p ω' k
  mod p`, and `rOut` ends with `natSyms` of the `n` values, reversed (`unpackR`).
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

open scoped IntegerMultBounds.MathlibTM2.DFT.Reg

namespace IntegerMultBounds.MathlibTM2.DFT

theorem zeroTop_natSyms {A : ℕ} (l : List ℕ) :
    zeroTop ((natSyms l).reverse : List (Fin (A + 4))).head? = false := by
  rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
  · simp [natSyms, zeroTop]
  · rw [List.concat_eq_append, natSyms_concat]
    simp [zeroTop, (bitSymbol_ne_separator false).symm]

/-- The value emitted in round `k`. -/
def unpackVal (p ω' w Y k : ℕ) : ℕ :=
  Y / 2 ^ (3 * w * k) % 2 ^ (3 * w) % p * chirp p ω' k % p

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (B : Type)

/-- One digit: reduce it, times the inverse chirp, emitted; then `chirpStep` with `rWinv`. -/
def unpackRound : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B) :=
  .seq (hostCode (.act (dropR (M.dreg 50 rNcnt))))
    (.seq (hostCode (splitLow (M.dreg 50 rZp) (M.dreg 50 rW3) (M.dreg 50 rTk) (M.dreg 50 rt1)
        (M.dreg 50 rt2)))
      (.seq (M.barrettProg 50 B rTk rAa rPw rWK rQ1 rQ2 rP3 rO rt1 rt2 rt3 rt4 rt5)
        (.seq (hostCode (bclear (M.dreg 50 rTk)))
          (.seq (M.modMulProg 50 B rO rC rZ rAa rPw rWK rQ1 rQ2 rP3 rO2 rt1 rt2 rt3 rt4 rt5)
            (.seq (hostCode (.seq (bclear (M.dreg 50 rO)) (emitNat (M.dreg 50 rO2)
                (M.dreg 50 rOut))))
              (M.chirpStep 50 B rC rE rWinv rZ rAa rPw rWK rQ1 rQ2 rP3 rO rt1 rt2 rt3 rt4
                rt5))))))

/-- The cost bound of an unpacking round. -/
def unpackCost (H : ℕ → ℕ) (k : ℕ) : ℕ :=
  (2200 + 35 * H (4 * k + 3)) * k + 2800 + 44 * H (4 * k + 3)

theorem unpackRound_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {k w p ω' c e Y e' : ℕ} {rest : List (Fin (M.A + 4))} (hw : 1 ≤ w) (h2w : 2 * w ≤ k)
    (hp1 : 2 ^ (w - 1) ≤ p) (hp : p < 2 ^ w) (hc : c < p) (he : e < p) (hω : ω' < p)
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (henv : M.ModEnv k w p S) (hN : S.R (M.dreg 50 rNcnt) = tick :: rest)
    (hZp : S.R (M.dreg 50 rZp) = binSyms (3 * w + e') Y) (hTk : S.R (M.dreg 50 rTk) = [])
    (hO2 : S.R (M.dreg 50 rO2) = []) (hOut : zeroTop (S.R (M.dreg 50 rOut)).head? = false)
    (hC : S.R (M.dreg 50 rC) = binSyms w c) (hE : S.R (M.dreg 50 rE) = binSyms w e)
    (hWinv : S.R (M.dreg 50 rWinv) = binSyms w ω') (hW3 : (S.R (M.dreg 50 rW3)).length = 3 * w)
    (gi go : List Γ') :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ n, v'.user.2 = v.user.2 ∧ n ≤ unpackCost H k ∧
      Exec (M.tab 50 B main) (M.unpackRound B) (dmk v S gi go) n
        (dmk v' { S with
          R := Function.update (Function.update (Function.update (Function.update
            (Function.update S.R (M.dreg 50 rNcnt) rest) (M.dreg 50 rZp)
            (binSyms e' (Y / 2 ^ (3 * w)))) (M.dreg 50 rOut)
            (separator :: ((binSyms (Nat.size (Y % 2 ^ (3 * w) % p * c % p))
              (Y % 2 ^ (3 * w) % p * c % p)).reverse ++ S.R (M.dreg 50 rOut))))
            (M.dreg 50 rC) (binSyms w (c * e % p))) (M.dreg 50 rE) (binSyms w (e * ω' % p)) }
          gi go) := by
  obtain ⟨hinp, hout, hL, hR, hA, hPw, hK, hZ, hQ1, hQ2, hP3, hO, ht1, ht2, ht3, ht4, ht5⟩ :=
    henv
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp1
  have hwk : w ≤ k := by omega
  set T := Y % 2 ^ (3 * w) with hTdef
  have hT3 : T < 2 ^ (3 * w) := Nat.mod_lt _ (by positivity)
  have hTs : T < 2 ^ (k + w) := lt_of_lt_of_le hT3 (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- a tick
  have e₁ := Exec.act (body := (Empty.elim : Empty → Pr Empty (M.T + 50) M.Q M.A (M.U × B)))
    (dropR (M.dreg 50 rNcnt)) (Host.mk v S)
  rw [dropR_run, hN, List.tail_cons] at e₁
  set S₁ : Stacks (M.T + 50) M.A :=
    { S with R := Function.update S.R (M.dreg 50 rNcnt) rest } with hS₁
  -- the digit
  obtain ⟨v₂, hu₂, e₂⟩ := splitLow_exec Empty.elim (a := M.dreg 50 rZp) (wR := M.dreg 50 rW3)
    (d := M.dreg 50 rTk) (t₁ := M.dreg 50 rt1) (t₂ := M.dreg 50 rt2) (by simp) (r := 3 * w)
    (e := e') (X := Y) v S₁ (by simp [hS₁, hZp]) (by simp [hS₁, hW3]) (by simp [hS₁, hTk])
    (by simp [hS₁, ht1]) (by simp [hS₁, ht2])
  rw [← binSyms_mod (3 * w) Y, ← hTdef] at e₂
  set S₂ : Stacks (M.T + 50) M.A := { S₁ with
    R := Function.update (Function.update S₁.R (M.dreg 50 rZp) (binSyms e' (Y / 2 ^ (3 * w))))
      (M.dreg 50 rTk) (binSyms (3 * w) T) } with hS₂
  -- `rO := T mod p`
  obtain ⟨v₃, m₁, m₂, n₃, hu₃, hm₁, hm₂, hn₃, e₃⟩ := M.barrett_exec 50 B main (X := rTk)
    (Aa := rAa) (Pw := rPw) (wK := rWK) (Q1 := rQ1) (Q2 := rQ2) (P3 := rP3) (O := rO)
    (t₁ := rt1) (t₂ := rt2) (t₃ := rt3) (t₄ := rt4) (t₅ := rt5) (by decide) (L := 3 * w)
    (k := k) hw (by omega) hwk hp1 hp hT3 hTs v₂ S₂ (by simp [hS₂, hS₁, hinp])
    (by simp [hS₂, hS₁, hout]) (by simp [hS₂, hS₁, hL]) (by intro i; simp [hS₂, hS₁, hR])
    (by simp [hS₂]) (by simp [hS₂, hS₁, hA]) (by simp [hS₂, hS₁, hPw]) (by simp [hS₂, hS₁, hK])
    (by simp [hS₂, hS₁, hQ1]) (by simp [hS₂, hS₁, hQ2]) (by simp [hS₂, hS₁, hP3])
    (by simp [hS₂, hS₁, hO]) (by simp [hS₂, hS₁, ht1]) (by simp [hS₂, hS₁, ht2])
    (by simp [hS₂, hS₁, ht3]) (by simp [hS₂, hS₁, ht4]) (by simp [hS₂, hS₁, ht5]) gi go
  set S₃ : Stacks (M.T + 50) M.A :=
    { S₂ with R := Function.update S₂.R (M.dreg 50 rO) (binSyms w (T % p)) } with hS₃
  obtain ⟨v₄, hu₄, -, e₄⟩ := bclear_exec Empty.elim (M.dreg 50 rTk) v₃ S₃
  rw [show (S₃.R (M.dreg 50 rTk)).length = 3 * w by simp [hS₃, hS₂]] at e₄
  set S₄ : Stacks (M.T + 50) M.A := { S₃ with R := Function.update S₃.R (M.dreg 50 rTk) [] }
    with hS₄
  -- `rO2 := (T mod p) c`
  obtain ⟨v₅, n₅, hu₅, hn₅, e₅⟩ := M.modMul_exec 50 B main H hH hT (Xa := rO) (Yb := rC)
    (Z := rZ) (Aa := rAa) (Pw := rPw) (wK := rWK) (Q1 := rQ1) (Q2 := rQ2) (P3 := rP3)
    (O := rO2) (t₁ := rt1) (t₂ := rt2) (t₃ := rt3) (t₄ := rt4) (t₅ := rt5) (by decide)
    (x := T % p) (y := c) hw hwk hp1 hp (Nat.mod_lt _ hp0) hc v₄ S₄ (by simp [hS₄, hS₃, hS₂, hS₁, hinp])
    (by simp [hS₄, hS₃, hS₂, hS₁, hout]) (by simp [hS₄, hS₃, hS₂, hS₁, hL])
    (by intro i; simp [hS₄, hS₃, hS₂, hS₁, hR]) (by simp [hS₄, hS₃])
    (by simp [hS₄, hS₃, hS₂, hS₁, hC]) (by simp [hS₄, hS₃, hS₂, hS₁, hA])
    (by simp [hS₄, hS₃, hS₂, hS₁, hPw]) (by simp [hS₄, hS₃, hS₂, hS₁, hK])
    (by simp [hS₄, hS₃, hS₂, hS₁, hZ]) (by simp [hS₄, hS₃, hS₂, hS₁, hQ1])
    (by simp [hS₄, hS₃, hS₂, hS₁, hQ2]) (by simp [hS₄, hS₃, hS₂, hS₁, hP3])
    (by simp [hS₄, hS₃, hS₂, hS₁, hO2]) (by simp [hS₄, hS₃, hS₂, hS₁, ht1])
    (by simp [hS₄, hS₃, hS₂, hS₁, ht2]) (by simp [hS₄, hS₃, hS₂, hS₁, ht3])
    (by simp [hS₄, hS₃, hS₂, hS₁, ht4]) (by simp [hS₄, hS₃, hS₂, hS₁, ht5]) gi go
  set X := T % p * c % p with hX
  set S₅ : Stacks (M.T + 50) M.A :=
    { S₄ with R := Function.update S₄.R (M.dreg 50 rO2) (binSyms w X) } with hS₅
  -- clear `rO`, emit `X`
  obtain ⟨v₆, hu₆, -, e₆a⟩ := bclear_exec Empty.elim (M.dreg 50 rO) v₅ S₅
  rw [show (S₅.R (M.dreg 50 rO)).length = w by simp [hS₅, hS₄, hS₃]] at e₆a
  set S₆ : Stacks (M.T + 50) M.A := { S₅ with R := Function.update S₅.R (M.dreg 50 rO) [] }
    with hS₆
  obtain ⟨v₇, hu₇, e₆b⟩ := emitNat_exec Empty.elim (s := M.dreg 50 rO2) (o := M.dreg 50 rOut)
    (by simp) (w := w) (x := X) ((Nat.mod_lt _ hp0).trans hp) v₆ S₆ (by simp [hS₆, hS₅])
    (by simpa [hS₆, hS₅, hS₄, hS₃, hS₂, hS₁] using hOut)
  set S₇ : Stacks (M.T + 50) M.A := { S₆ with R := emitR S₆.R (M.dreg 50 rO2) (M.dreg 50 rOut) X }
    with hS₇
  -- the inverse chirp step
  obtain ⟨v₈, n₈, hu₈, hn₈, e₈⟩ := M.chirpStep_exec 50 B main H hH hT (C := rC) (E := rE)
    (X := rWinv) (Z := rZ) (Aa := rAa) (Pw := rPw) (wK := rWK) (Q1 := rQ1) (Q2 := rQ2)
    (P3 := rP3) (O := rO) (t₁ := rt1) (t₂ := rt2) (t₃ := rt3) (t₄ := rt4) (t₅ := rt5) (by decide)
    hw hwk hp1 hp hc he hω v₇ S₇ (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, hinp])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, hout])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, hL])
    (by intro i; simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, hR])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, hC])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, hE])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, hWinv])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, hA])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, hPw])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, hK])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, hZ])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, hQ1])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, hQ2])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, hP3])
    (by simp [hS₇, hS₆, emitR])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, ht1])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, ht2])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, ht3])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, ht4])
    (by simp [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, emitR, ht5]) gi go
  refine ⟨v₈, _, by rw [hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂], ?_, Exec.cast
    (Exec.seq (exec_hostCode e₁ gi go) (Exec.seq (exec_hostCode e₂ gi go) (Exec.seq e₃
      (Exec.seq (exec_hostCode e₄ gi go) (Exec.seq e₅ (Exec.seq
        (exec_hostCode (Exec.seq e₆a e₆b) gi go) e₈)))))) rfl ?_⟩
  · -- the time
    simp only [unpackCost]
    set h := H (4 * k + 3) with hh
    have hTs' : ∀ s, s ≤ 4 * k + 3 → M.time s ≤ 4 * (k * h) + 4 * h := fun s hs => by
      calc M.time s ≤ (s + 1) * H s := hT s
        _ ≤ (4 * k + 4) * h := Nat.mul_le_mul (by omega) (hH hs)
        _ = 4 * (k * h) + 4 * h := by ring
    have hμ : 2 ^ (k + w) / p < 2 ^ (k + 2) :=
      lt_of_le_of_lt (recip_le hw hp1) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hq : T * (2 ^ (k + w) / p) / 2 ^ (k + w) < 2 ^ (3 * w) :=
      lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_right _ hp0) (barrett2_le p (k + w) T)) hT3
    have := Nat.size_le.2 hT3
    have := Nat.size_le.2 hμ
    have := Nat.size_le.2 hq
    have := Nat.size_le.2 hp
    have hm₁' := hm₁.trans (hTs' _ (by omega))
    have hm₂' := hm₂.trans (hTs' _ (by omega))
    have hhh : H (3 * k + 3) ≤ h := hH (by omega)
    have e1 : (520 + 9 * H (3 * k + 3)) * k ≤ 520 * k + 9 * (k * h) := by
      have := Nat.mul_le_mul_right k (show 520 + 9 * H (3 * k + 3) ≤ 520 + 9 * h by omega)
      calc (520 + 9 * H (3 * k + 3)) * k ≤ (520 + 9 * h) * k := this
        _ = 520 * k + 9 * (k * h) := by ring
    have e2 : (1060 + 18 * H (3 * k + 3)) * k ≤ 1060 * k + 18 * (k * h) := by
      have := Nat.mul_le_mul_right k (show 1060 + 18 * H (3 * k + 3) ≤ 1060 + 18 * h by omega)
      calc (1060 + 18 * H (3 * k + 3)) * k ≤ (1060 + 18 * h) * k := this
        _ = 1060 * k + 18 * (k * h) := by ring
    have e3 : (2200 + 35 * h) * k = 2200 * k + 35 * (k * h) := by ring
    omega
  · clear e₁ e₂ e₃ e₄ e₅ e₆a e₆b e₈
    show dmk v₈ _ gi go = dmk v₈ _ gi go
    congr 1
    simp only [hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁]
    congr 1
    funext j
    by_cases hj1 : j = M.dreg 50 rE
    · subst hj1; simp [emitR]
    by_cases hj2 : j = M.dreg 50 rC
    · subst hj2; simp [emitR]
    by_cases hj3 : j = M.dreg 50 rOut
    · subst hj3; simp [emitR]
    by_cases hj4 : j = M.dreg 50 rO2
    · subst hj4; simp [emitR, hO2]
    by_cases hj5 : j = M.dreg 50 rO
    · subst hj5; simp [emitR, hO]
    by_cases hj6 : j = M.dreg 50 rTk
    · subst hj6; simp [emitR, hTk]
    by_cases hj7 : j = M.dreg 50 rZp
    · subst hj7; simp [emitR]
    by_cases hj8 : j = M.dreg 50 rNcnt
    · subst hj8; simp [emitR]
    simp [emitR, hj1, hj2, hj3, hj4, hj5, hj6, hj7, hj8]

/-- The registers after `i` unpacking rounds. -/
def unpackR (w p ω' n m Y : ℕ) (R : Fin (M.T + 50) → List (Fin (M.A + 4))) (i : ℕ) :
    Fin (M.T + 50) → List (Fin (M.A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update R
    (M.dreg 50 rNcnt) (List.replicate (n - i) tick))
    (M.dreg 50 rZp) (binSyms (3 * w * (m - i)) (Y / 2 ^ (3 * w * i))))
    (M.dreg 50 rOut) (natSyms ((List.range i).map (unpackVal p ω' w Y))).reverse)
    (M.dreg 50 rC) (binSyms w (chirp p ω' i))) (M.dreg 50 rE) (binSyms w (ω' ^ i % p))

theorem modEnv_unpackR {k w p ω' n m Y : ℕ} {S : Stacks (M.T + 50) M.A}
    (h : M.ModEnv k w p S) (i : ℕ) :
    M.ModEnv k w p { S with R := M.unpackR w p ω' n m Y S.R i } :=
  M.modEnv_update (M.modEnv_update (M.modEnv_update (M.modEnv_update (M.modEnv_update h rNcnt
    (by decide) _) rZp (by decide) _) rOut (by decide) _) rC (by decide) _) rE (by decide) _

/-- The unpacking loop: `n` rounds over `rNcnt`. -/
theorem unpackLoop_exec (main : DPr (Option M.P) (M.T + 50) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {k w p ω' n m Y : ℕ} (hw : 1 ≤ w) (h2w : 2 * w ≤ k) (hp1 : 2 ^ (w - 1) ≤ p)
    (hp : p < 2 ^ w) (hp2 : 2 ≤ p) (hω : ω' < p) (hnm : n ≤ m)
    (v : HS (M.T + 50) M.Q M.A (M.U × B)) (S : Stacks (M.T + 50) M.A)
    (henv : M.ModEnv k w p S) (hN : S.R (M.dreg 50 rNcnt) = List.replicate n tick)
    (hZp : S.R (M.dreg 50 rZp) = binSyms (3 * w * m) Y) (hTk : S.R (M.dreg 50 rTk) = [])
    (hO2 : S.R (M.dreg 50 rO2) = []) (hOut : S.R (M.dreg 50 rOut) = [])
    (hC : S.R (M.dreg 50 rC) = binSyms w 1) (hE : S.R (M.dreg 50 rE) = binSyms w 1)
    (hWinv : S.R (M.dreg 50 rWinv) = binSyms w ω') (hW3 : (S.R (M.dreg 50 rW3)).length = 3 * w)
    (gi go : List Γ') :
    ∃ v' : HS (M.T + 50) M.Q M.A (M.U × B), ∃ n', v'.user.2 = v.user.2 ∧
      n' ≤ n * (unpackCost H k + 2) + 2 ∧
      Exec (M.tab 50 B main) (M.countLoop 50 B (M.dreg 50 rNcnt) (M.unpackRound B))
        (dmk v S gi go) n' (dmk v' { S with R := M.unpackR w p ω' n m Y S.R n } gi go) := by
  have hp0 : 0 < p := by omega
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp2
  have hR0 : M.unpackR w p ω' n m Y S.R 0 = S.R := by
    funext j
    by_cases hj1 : j = M.dreg 50 rE
    · subst hj1; simp [unpackR, hE, h1]
    by_cases hj2 : j = M.dreg 50 rC
    · subst hj2; simp [unpackR, hC, chirp_zero, h1]
    by_cases hj3 : j = M.dreg 50 rOut
    · subst hj3; simp [unpackR, hOut, natSyms]
    by_cases hj4 : j = M.dreg 50 rZp
    · subst hj4; simp [unpackR, hZp]
    by_cases hj5 : j = M.dreg 50 rNcnt
    · subst hj5; simp [unpackR, hN]
    simp [unpackR, hj1, hj2, hj3, hj4, hj5]
  obtain ⟨v', S', n', ⟨hu, hS'⟩, hn', e⟩ := M.countLoop_exec 50 B main (M.dreg 50 rNcnt)
    (M.unpackRound B)
    (fun i v' S' => v'.user.2 = v.user.2 ∧ S' = { S with R := M.unpackR w p ω' n m Y S.R i })
    n (unpackCost H k) gi go (fun _ _ _ _ h => h)
    (fun i v' S' h => by
      rw [h.2]
      simp only [unpackR, Function.update_of_ne (show M.dreg 50 rNcnt ≠ M.dreg 50 rE by simp),
        Function.update_of_ne (show M.dreg 50 rNcnt ≠ M.dreg 50 rC by simp),
        Function.update_of_ne (show M.dreg 50 rNcnt ≠ M.dreg 50 rOut by simp),
        Function.update_of_ne (show M.dreg 50 rNcnt ≠ M.dreg 50 rZp by simp),
        Function.update_self]
      rcases Nat.eq_zero_or_pos (n - i) with h0 | h0
      · rw [h0]; simp; omega
      · obtain ⟨t, ht⟩ : ∃ t, n - i = t + 1 := ⟨n - i - 1, by omega⟩
        rw [ht]; simp; omega)
    (fun i hi v' S' h => by
      obtain ⟨hu', rfl⟩ := h
      have hwidth : 3 * w * (m - i) = 3 * w + 3 * w * (m - i - 1) := by
        obtain ⟨t, ht⟩ : ∃ t, m - i = t + 1 := ⟨m - i - 1, by omega⟩
        rw [ht, show t + 1 - 1 = t by omega]; ring
      obtain ⟨v'', n'', hu'', hn'', e⟩ := M.unpackRound_exec B main H hH hT
        (c := chirp p ω' i) (e := ω' ^ i % p) (Y := Y / 2 ^ (3 * w * i))
        (e' := 3 * w * (m - i - 1)) (rest := List.replicate (n - i - 1) tick) hw h2w hp1 hp
        (Nat.mod_lt _ hp0) (Nat.mod_lt _ hp0) hω v' _
        (M.modEnv_unpackR (ω' := ω') (n := n) (m := m) (Y := Y) henv i)
        (by
          obtain ⟨t, ht⟩ : ∃ t, n - i = t + 1 := ⟨n - i - 1, by omega⟩
          simp [unpackR, ht, List.replicate_succ])
        (by simp [unpackR, ← hwidth]) (by simp [unpackR, hTk]) (by simp [unpackR, hO2])
        (by simp only [unpackR, Function.update_self,
              Function.update_of_ne (show M.dreg 50 rOut ≠ M.dreg 50 rE by simp),
              Function.update_of_ne (show M.dreg 50 rOut ≠ M.dreg 50 rC by simp)]
            exact zeroTop_natSyms _)
        (by simp only [unpackR, Function.update_self,
          Function.update_of_ne (show M.dreg 50 rC ≠ M.dreg 50 rE by simp)])
        (by simp only [unpackR, Function.update_self]) (by simp [unpackR, hWinv])
        (by simp [unpackR, hW3]) gi go
      refine ⟨v'', _, n'', ⟨hu''.trans hu', ?_⟩, hn'', e⟩
      congr 1
      funext j
      by_cases hj1 : j = M.dreg 50 rE
      · subst hj1
        simp only [unpackR, Function.update_self]
        rw [powMod_succ, Nat.mod_eq_of_lt hω]
      by_cases hj2 : j = M.dreg 50 rC
      · subst hj2
        simp [unpackR, chirp_succ]
      by_cases hj3 : j = M.dreg 50 rOut
      · subst hj3
        simp only [unpackR, Function.update_of_ne (show M.dreg 50 rOut ≠ M.dreg 50 rE by simp),
          Function.update_of_ne (show M.dreg 50 rOut ≠ M.dreg 50 rC by simp),
          Function.update_self]
        rw [List.range_succ, List.map_append, List.map_singleton, natSyms_concat]
        rfl
      by_cases hj4 : j = M.dreg 50 rZp
      · subst hj4
        simp only [unpackR, Function.update_of_ne (show M.dreg 50 rZp ≠ M.dreg 50 rE by simp),
          Function.update_of_ne (show M.dreg 50 rZp ≠ M.dreg 50 rC by simp),
          Function.update_of_ne (show M.dreg 50 rZp ≠ M.dreg 50 rOut by simp),
          Function.update_self]
        rw [Nat.div_div_eq_div_mul, ← pow_add, show m - (i + 1) = m - i - 1 by omega,
          show 3 * w * i + 3 * w = 3 * w * (i + 1) by ring]
      by_cases hj5 : j = M.dreg 50 rNcnt
      · subst hj5
        simp [unpackR, show n - (i + 1) = n - i - 1 by omega]
      simp [unpackR, hj1, hj2, hj3, hj4, hj5])
    v S ⟨rfl, by rw [hR0]⟩
  subst hS'
  exact ⟨v', n', hu, hn', e⟩

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
