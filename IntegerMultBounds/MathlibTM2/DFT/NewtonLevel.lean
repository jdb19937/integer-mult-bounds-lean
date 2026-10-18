module

public import IntegerMultBounds.MathlibTM2.DFT.Newton
public import IntegerMultBounds.MathlibTM2.DFT.NewtonGuess
public import IntegerMultBounds.MathlibTM2.DFT.Redc
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A level of the Newton reciprocal

For a normalized divisor `2 ^ (N - 1) ≤ D < 2 ^ N` write `μ k = ⌊2 ^ (2k) / ⌊D / 2 ^ (N - k)⌋⌋`
for the reciprocal of its top `k` bits. A level computes `μ (2k)` from `a = μ k`: with
`d = ⌊D / 2 ^ (N - 2k)⌋` the guess `y = 2 ^ (k+1) a - (⌊d a² / 4 ^ k⌋ + 1)` satisfies
`y d ≤ 2 ^ (4k)` and `(2 ^ (4k) - y d) / d ≤ 8`, and `y + (2 ^ (4k) - y d) / d = μ (2k)`
(`newton_level_arith`, from `newton_step`).

`M.newtonLevel D B Cnt Dp wK … t₅` runs the level on the DFT registers, for `Dp` holding `D`
most significant bit first and `wK` holding `k` symbols: `newtonPrep`, `newtonLoad`, the product
`a · a`, `newtonSq`, the product `d · a²`, `newtonGuessProg`, the product `y · d` and
`newtonFinish`. `newtonLevel_exec`: `A` goes from `binSyms (2k + 4) (μ k)` to
`binSyms (4k + 4) (μ (2k))`, `wK` doubles, the counter `Cnt` loses `k` symbols, in at most
`(3200 + 12 h) k + 4000 + 15 h` steps for a time majorant `M.time n ≤ (n + 1) H n` and
`h = H (4k + 4)`.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

/-- The arithmetic of a level from `k` to `2 k` bits. -/
theorem newton_level_arith {N Dv k d a y : ℕ} (hk : 1 ≤ k) (hkN : k + k ≤ N)
    (hD1 : 2 ^ (N - 1) ≤ Dv) (hD : Dv < 2 ^ N) (hd : d = Dv / 2 ^ (N - (k + k)))
    (ha : a = 2 ^ (k + k) / (Dv / 2 ^ (N - k)))
    (hy : y = 2 ^ (k + 1) * a - (d * (a * a) / 2 ^ (k + k) + 1)) :
    0 < d ∧ d < 2 ^ (k + k) ∧ a ≤ 2 ^ (k + 1) ∧
      d * (a * a) / 2 ^ (k + k) + 1 ≤ 2 ^ (k + 1) * a ∧ y * d ≤ 2 ^ (4 * k) ∧
      (2 ^ (4 * k) - y * d) / d ≤ 8 ∧ y + (2 ^ (4 * k) - y * d) / d < 2 ^ (k + k + 2) ∧
      y + (2 ^ (4 * k) - y * d) / d = 2 ^ (k + k + (k + k)) / (Dv / 2 ^ (N - (k + k))) := by
  have h4 : (4 : ℕ) ^ k = 2 ^ (k + k) := by rw [← two_mul, pow_mul]; norm_num
  have h16 : (16 : ℕ) ^ k = 2 ^ (4 * k) := by rw [pow_mul]; norm_num
  -- the top `k` bits of `d`
  have hdk : d / 2 ^ k = Dv / 2 ^ (N - k) := by
    rw [hd, Nat.div_div_eq_div_mul, ← pow_add, show N - (k + k) + k = N - k by omega]
  have hdlo : 2 ^ (k + k) ≤ 2 * d := by
    have h1 : 2 ^ (N - 1) / 2 ^ (N - (k + k)) ≤ d := by
      rw [hd]; exact Nat.div_le_div_right hD1
    rw [Nat.pow_div (by omega) (by norm_num)] at h1
    calc 2 ^ (k + k) = 2 * 2 ^ (N - 1 - (N - (k + k))) := by
          rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * d := by omega
  have hdhi : d < 2 ^ (k + k) := by
    rw [hd, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show k + k + (N - (k + k)) = N by omega]
    exact hD
  have hd0 : 0 < d := by
    have : 0 < 2 ^ (k + k) := by positivity
    omega
  have hale : a ≤ 2 ^ (k + 1) := by
    have h1 : 2 ^ (N - 1) / 2 ^ (N - k) ≤ Dv / 2 ^ (N - k) := Nat.div_le_div_right hD1
    rw [Nat.pow_div (by omega) (by norm_num)] at h1
    rw [ha]
    calc 2 ^ (k + k) / (Dv / 2 ^ (N - k)) ≤ 2 ^ (k + k) / 2 ^ (N - 1 - (N - k)) :=
          Nat.div_le_div_left h1 (by positivity)
      _ = 2 ^ (k + 1) := by rw [Nat.pow_div (by omega) (by norm_num)]; congr 1; omega
  obtain ⟨s₁, s₂, s₃⟩ := newton_step hk (by rw [h4]; exact hdlo) (by rw [h4]; exact hdhi)
  have ha' : 4 ^ k / (d / 2 ^ k) = a := by rw [hdk, h4, ha]
  have hg : newtonGuess k d a = y := by rw [hy, newtonGuess, h4, pow_two]
  rw [ha', h4, pow_two] at s₁
  rw [ha', hg, h16] at s₂
  rw [ha', hg, h16] at s₃
  have hρ : (2 ^ (4 * k) - y * d) / d < 9 := by
    rw [Nat.div_lt_iff_lt_mul hd0]
    rw [Nat.add_mul] at s₃
    omega
  have hμ : y + (2 ^ (4 * k) - y * d) / d = 2 ^ (4 * k) / d := by
    conv_rhs => rw [← Nat.sub_add_cancel s₂.le]
    rw [Nat.add_mul_div_right _ _ hd0]
    exact Nat.add_comm _ _
  have hμlt : 2 ^ (4 * k) / d < 2 ^ (k + k + 2) := by
    rw [Nat.div_lt_iff_lt_mul hd0]
    have e : 2 ^ (k + k + 2) * d = 2 ^ (k + k) * (4 * d) := by rw [pow_add]; ring
    have e' : 2 ^ (4 * k) = 2 ^ (k + k) * 2 ^ (k + k) := by rw [← pow_add]; congr 1; ring
    rw [e, e']
    exact (Nat.mul_lt_mul_left (by positivity)).2 (by omega)
  refine ⟨hd0, hdhi, hale, s₁, s₂.le, by omega, by rw [hμ]; exact hμlt, ?_⟩
  rw [← hd, show k + k + (k + k) = 4 * k by ring]
  exact hμ


namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (D : ℕ) (B : Type)

/-! ### The first half: loading, `a²` and `d a²` -/

/-- `newtonPrep`, `newtonLoad`, `B3 := a · a`, `newtonSq`, `B2 := d · a²`. -/
def newtonLevelA (Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (hostCode (newtonPrep (M.dreg D Cnt) (M.dreg D wK) (M.dreg D w2K) (M.dreg D wL)
      (M.dreg D ONE) (M.dreg D SIX) (M.dreg D t₁) (M.dreg D t₂)))
    (.seq (hostCode (newtonLoad (M.dreg D Dp) (M.dreg D w2K) (M.dreg D wL) (M.dreg D B1)
        (M.dreg D Dd) (M.dreg D Aa) (M.dreg D B2) (M.dreg D t₁) (M.dreg D t₂)))
      (.seq (M.mulCall D B (M.dreg D Aa) (M.dreg D B2) (M.dreg D B3) (M.dreg D t₁)
          (M.dreg D t₂) (M.dreg D t₃) (M.dreg D t₄) (M.dreg D t₅))
        (.seq (hostCode (newtonSq (M.dreg D B2) (M.dreg D B3) (M.dreg D wL) (M.dreg D t₁)
            (M.dreg D t₂)))
          (M.mulCall D B (M.dreg D Dd) (M.dreg D B3) (M.dreg D B2) (M.dreg D t₁)
            (M.dreg D t₂) (M.dreg D t₃) (M.dreg D t₄) (M.dreg D t₅)))))

theorem newtonLevelA_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    {Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [Cnt, Dp, wK, w2K, wL, ONE, SIX, B1, Dd, Aa, B2, B3, t₁, t₂, t₃, t₄, t₅].Nodup)
    {N Dv k a : ℕ} (hkN : k + k ≤ N) (hD : Dv < 2 ^ N) (hale : a ≤ 2 ^ (k + 1))
    (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ j, S.L j = [])
    (hR : ∀ i, S.R (M.emb D i) = []) (hDp : S.R (M.dreg D Dp) = (binSyms N Dv).reverse)
    (hK : (S.R (M.dreg D wK)).length = k) (hA : S.R (M.dreg D Aa) = binSyms (k + k + 4) a)
    (h2 : S.R (M.dreg D w2K) = []) (hwL : S.R (M.dreg D wL) = []) (hO : S.R (M.dreg D ONE) = [])
    (hS6 : S.R (M.dreg D SIX) = []) (hB1 : S.R (M.dreg D B1) = []) (hDd : S.R (M.dreg D Dd) = [])
    (hB2 : S.R (M.dreg D B2) = []) (hB3 : S.R (M.dreg D B3) = [])
    (h₁ : S.R (M.dreg D t₁) = []) (h₂ : S.R (M.dreg D t₂) = []) (h₃ : S.R (M.dreg D t₃) = [])
    (h₄ : S.R (M.dreg D t₄) = []) (h₅ : S.R (M.dreg D t₅) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ m₁ m₂ n, v'.user.2 = v.user.2 ∧
      m₁ + 2 ≤ M.time (Nat.size a + Nat.size a) ∧
      m₂ + 2 ≤ M.time (Nat.size (Dv / 2 ^ (N - (k + k))) + Nat.size (a * a)) ∧
      n ≤ 850 * k + 1050 + m₁ + m₂ ∧
      Exec (M.tab D B main) (M.newtonLevelA D B Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 t₁ t₂ t₃
        t₄ t₅) (dmk v S gi go) n
        (dmk v' { S with
          R := Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update (Function.update
            (Function.update S.R (M.dreg D Cnt) ((S.R (M.dreg D Cnt)).drop k)) (M.dreg D w2K)
            (S.R (M.dreg D wK) ++ S.R (M.dreg D wK))) (M.dreg D wL)
            ([tick, tick, tick, tick] ++ (S.R (M.dreg D wK) ++ S.R (M.dreg D wK)) ++
              (S.R (M.dreg D wK) ++ S.R (M.dreg D wK))))
            (M.dreg D ONE) (binSyms (4 * k + 4) 1)) (M.dreg D SIX)
            (binSyms (4 * k + 4) (2 ^ (4 * k)))) (M.dreg D Dd)
            (binSyms (4 * k + 4) (Dv / 2 ^ (N - (k + k))))) (M.dreg D Aa)
            (binSyms (4 * k + 4) a)) (M.dreg D B3) (binSyms (4 * k + 4) (a * a))) (M.dreg D B2)
            (binSyms (4 * k + 4 + (4 * k + 4)) (Dv / 2 ^ (N - (k + k)) * (a * a))) } gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  have hnd : ∀ l : List (Fin D), l.Nodup → (l.map (M.dreg D)).Nodup := fun _ h => M.nodup_dreg D h
  set d := Dv / 2 ^ (N - (k + k)) with hd
  have hdlt : d < 2 ^ (k + k) := by
    rw [hd, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show k + k + (N - (k + k)) = N by omega]
    exact hD
  clear_value d
  have hL4 : ∀ e, e < 4 * k + 4 → 2 ^ e < 2 ^ (4 * k + 4) := fun e he =>
    Nat.pow_lt_pow_right (by norm_num) he
  have hk1 : a < 2 ^ (k + 2) := lt_of_le_of_lt hale (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have haW : a < 2 ^ (k + k + 4) := lt_trans hk1 (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have haa : a * a < 2 ^ (k + k + 3) := by
    calc a * a ≤ 2 ^ (k + 1) * 2 ^ (k + 1) := Nat.mul_le_mul hale hale
      _ < 2 ^ (k + k + 3) := by
          rw [← pow_add]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have haL : a < 2 ^ (4 * k + 4) := lt_trans hk1 (hL4 _ (by omega))
  have haaL : a * a < 2 ^ (4 * k + 4) := lt_trans haa (hL4 _ (by omega))
  have hdL : d < 2 ^ (4 * k + 4) := lt_trans hdlt (hL4 _ (by omega))
  have hX₂ : d * (a * a) < 2 ^ (4 * k + 4) := by
    calc d * (a * a) < 2 ^ (k + k) * 2 ^ (k + k + 3) := Nat.mul_lt_mul'' hdlt haa
      _ = 2 ^ (4 * k + 3) := by rw [← pow_add]; congr 1; ring
      _ < 2 ^ (4 * k + 4) := hL4 _ (by omega)
  -- `newtonPrep`
  obtain ⟨v₁, n₁, hu₁, hn₁, e₁⟩ := newtonPrep_exec Empty.elim (Cnt := M.dreg D Cnt)
    (wK := M.dreg D wK) (w2K := M.dreg D w2K) (wL := M.dreg D wL) (ONE := M.dreg D ONE)
    (SIX := M.dreg D SIX) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (by simpa only [List.map_cons, List.map_nil] using
      hnd [Cnt, wK, w2K, wL, ONE, SIX, t₁, t₂] (by regs_nodup)) v S hK h2 hwL hO hS6 h₁ h₂
  set S₁ : Stacks (M.T + D) M.A := { S with
    R := Function.update (Function.update (Function.update (Function.update
      (Function.update S.R (M.dreg D Cnt) ((S.R (M.dreg D Cnt)).drop k)) (M.dreg D w2K)
      (S.R (M.dreg D wK) ++ S.R (M.dreg D wK))) (M.dreg D wL)
      ([tick, tick, tick, tick] ++ (S.R (M.dreg D wK) ++ S.R (M.dreg D wK)) ++
        (S.R (M.dreg D wK) ++ S.R (M.dreg D wK))))
      (M.dreg D ONE) (binSyms (4 * k + 4) 1)) (M.dreg D SIX) (binSyms (4 * k + 4) (2 ^ (4 * k))) }
    with hS₁
  -- `newtonLoad`
  obtain ⟨v₂, n₂, hu₂, hn₂, e₂⟩ := newtonLoad_exec Empty.elim (Dp := M.dreg D Dp)
    (w2K := M.dreg D w2K) (wL := M.dreg D wL) (B1 := M.dreg D B1) (Dd := M.dreg D Dd)
    (Aa := M.dreg D Aa) (B2 := M.dreg D B2) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (by simpa only [List.map_cons, List.map_nil] using
      hnd [Dp, w2K, wL, B1, Dd, Aa, B2, t₁, t₂] (by regs_nodup)) hkN hD haW v₁ S₁
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm] <;> omega)
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
  rw [← hd] at e₂
  set S₂ : Stacks (M.T + D) M.A := { S₁ with
    R := Function.update (Function.update (Function.update S₁.R (M.dreg D Dd)
      (binSyms (4 * k + 4) d)) (M.dreg D Aa) (binSyms (4 * k + 4) a)) (M.dreg D B2)
      (binSyms (4 * k + 4) a) } with hS₂
  -- `B3 := a a`
  obtain ⟨v₃, m₁, hu₃, hm₁, e₃⟩ := M.mulCall_exec D B main (a := M.dreg D Aa)
    (b := M.dreg D B2) (c := M.dreg D B3) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (t₃ := M.dreg D t₃) (t₄ := M.dreg D t₄) (t₅ := M.dreg D t₅)
    (by simpa only [List.map_cons, List.map_nil] using
      hnd [B3, Aa, B2, t₁, t₂, t₃, t₄, t₅] (by regs_nodup)) haL haL v₂ S₂
    (by simp [hS₂, hS₁, hinp]) (by simp [hS₂, hS₁, hout]) (by simp [hS₂, hS₁, hL])
    (by intro i; simp [hS₂, hS₁, hR]) (by simp [hS₂, *, Ne.symm]) (by simp [hS₂])
    (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
    (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
    (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm]) gi go
  set S₃ : Stacks (M.T + D) M.A := { S₂ with
    R := Function.update S₂.R (M.dreg D B3) (binSyms (4 * k + 4 + (4 * k + 4)) (a * a)) }
    with hS₃
  -- `newtonSq`
  obtain ⟨v₄, hu₄, e₄⟩ := newtonSq_exec Empty.elim (B2 := M.dreg D B2) (B3 := M.dreg D B3)
    (wL := M.dreg D wL) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (by simpa only [List.map_cons, List.map_nil] using hnd [B2, B3, wL, t₁, t₂] (by regs_nodup))
    (L := 4 * k + 4) (X := a * a) v₃ S₃
    (by simp [hS₃, hS₂, *, Ne.symm]) (by simp [hS₃])
    (by simp [hS₃, hS₂, hS₁, *, Ne.symm] <;> omega) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
  set S₄ : Stacks (M.T + D) M.A := { S₃ with
    R := Function.update (Function.update S₃.R (M.dreg D B3) (binSyms (4 * k + 4) (a * a)))
      (M.dreg D B2) [] } with hS₄
  -- `B2 := d a²`
  obtain ⟨v₅, m₂, hu₅, hm₂, e₅⟩ := M.mulCall_exec D B main (a := M.dreg D Dd)
    (b := M.dreg D B3) (c := M.dreg D B2) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (t₃ := M.dreg D t₃) (t₄ := M.dreg D t₄) (t₅ := M.dreg D t₅)
    (by simpa only [List.map_cons, List.map_nil] using
      hnd [B2, Dd, B3, t₁, t₂, t₃, t₄, t₅] (by regs_nodup)) hdL haaL v₄ S₄
    (by simp [hS₄, hS₃, hS₂, hS₁, hinp]) (by simp [hS₄, hS₃, hS₂, hS₁, hout])
    (by simp [hS₄, hS₃, hS₂, hS₁, hL]) (by intro i; simp [hS₄, hS₃, hS₂, hS₁, hR])
    (by simp [hS₄, hS₃, hS₂, *, Ne.symm]) (by simp [hS₄, *, Ne.symm]) (by simp [hS₄])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm]) gi go
  refine ⟨v₅, m₁, m₂, _, ?_, hm₁, hm₂, ?_, Exec.cast (Exec.seq (exec_hostCode e₁ gi go)
    (Exec.seq (exec_hostCode e₂ gi go) (Exec.seq e₃ (Exec.seq (exec_hostCode e₄ gi go) e₅))))
    rfl ?_⟩
  · rw [hu₅, hu₄, hu₃, hu₂, hu₁]
  · have := Nat.size_le.2 haaL
    have := Nat.size_le.2 hX₂
    omega
  · clear e₁ e₂ e₃ e₄ e₅
    show dmk v₅ _ gi go = dmk v₅ _ gi go
    congr 1
    simp only [hS₄, hS₃, hS₂, hS₁]
    clear hS₄ hS₃ hS₂ hS₁ hnd hL4 hm₁ hm₂ hn₁ hn₂ hdlt hk1 haW haa haL haaL hdL hX₂ hd
    congr 1
    funext j
    by_cases hj1 : j = M.dreg D B2
    · subst hj1; simp [*, Ne.symm]
    by_cases hj2 : j = M.dreg D B3
    · subst hj2; simp [*, Ne.symm]
    by_cases hj3 : j = M.dreg D Aa
    · subst hj3; simp [*, Ne.symm]
    by_cases hj4 : j = M.dreg D Dd
    · subst hj4; simp [*, Ne.symm]
    by_cases hj5 : j = M.dreg D SIX
    · subst hj5; simp [*, Ne.symm]
    by_cases hj6 : j = M.dreg D ONE
    · subst hj6; simp [*, Ne.symm]
    by_cases hj7 : j = M.dreg D wL
    · subst hj7; simp [*, Ne.symm]
    by_cases hj8 : j = M.dreg D w2K
    · subst hj8; simp [*, Ne.symm]
    by_cases hj9 : j = M.dreg D Cnt
    · subst hj9; simp [*, Ne.symm]
    simp [*]

/-! ### The second half: the guess, `y d` and the correction -/

/-- `newtonGuessProg`, `B2 := y · d`, `newtonFinish`. -/
def newtonLevelB (SIX Dd Aa B1 B2 B3 ONE Y Yn wK w2K wL t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (hostCode (newtonGuessProg (M.dreg D B2) (M.dreg D B3) (M.dreg D ONE) (M.dreg D Aa)
      (M.dreg D Y) (M.dreg D B1) (M.dreg D Yn) (M.dreg D wK) (M.dreg D w2K) (M.dreg D wL)
      (M.dreg D t₁) (M.dreg D t₂) (M.dreg D t₃)))
    (.seq (M.mulCall D B (M.dreg D Y) (M.dreg D Dd) (M.dreg D B2) (M.dreg D t₁) (M.dreg D t₂)
        (M.dreg D t₃) (M.dreg D t₄) (M.dreg D t₅))
      (hostCode (newtonFinish (M.dreg D B2) (M.dreg D SIX) (M.dreg D B1) (M.dreg D Dd)
        (M.dreg D Y) (M.dreg D ONE) (M.dreg D B3) (M.dreg D Yn) (M.dreg D Aa) (M.dreg D wK)
        (M.dreg D w2K) (M.dreg D wL) (M.dreg D t₁) (M.dreg D t₂) (M.dreg D t₃))))

theorem newtonLevelB_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    {SIX Dd Aa B1 B2 B3 ONE Y Yn wK w2K wL t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [SIX, Dd, Aa, B1, B2, B3, ONE, Y, Yn, wK, w2K, wL, t₁, t₂, t₃, t₄, t₅].Nodup)
    {k d a y : ℕ} (hy : y = 2 ^ (k + 1) * a - (d * (a * a) / 2 ^ (k + k) + 1))
    (hX₂ : d * (a * a) < 2 ^ (4 * k + 4)) (h2a : 2 ^ (k + 1) * a < 2 ^ (4 * k + 4))
    (hz : d * (a * a) / 2 ^ (k + k) + 1 ≤ 2 ^ (k + 1) * a) (hyd : y * d ≤ 2 ^ (4 * k))
    (hd0 : 0 < d) (hdL : d < 2 ^ (4 * k + 4))
    (hμL : y + (2 ^ (4 * k) - y * d) / d < 2 ^ (4 * k + 4)) (hc : (2 ^ (4 * k) - y * d) / d ≤ 8)
    (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ j, S.L j = [])
    (hR : ∀ i, S.R (M.emb D i) = [])
    (hB2 : S.R (M.dreg D B2) = binSyms (4 * k + 4 + (4 * k + 4)) (d * (a * a)))
    (hB3 : (S.R (M.dreg D B3)).length = 4 * k + 4)
    (hO : S.R (M.dreg D ONE) = binSyms (4 * k + 4) 1)
    (hS6 : S.R (M.dreg D SIX) = binSyms (4 * k + 4) (2 ^ (4 * k)))
    (hDd : S.R (M.dreg D Dd) = binSyms (4 * k + 4) d)
    (hA : S.R (M.dreg D Aa) = binSyms (4 * k + 4) a) (hK : (S.R (M.dreg D wK)).length = k)
    (h2 : (S.R (M.dreg D w2K)).length = k + k) (hwL : (S.R (M.dreg D wL)).length = 4 * k + 4)
    (hY : S.R (M.dreg D Y) = []) (hB1 : S.R (M.dreg D B1) = []) (hYn : S.R (M.dreg D Yn) = [])
    (h₁ : S.R (M.dreg D t₁) = []) (h₂ : S.R (M.dreg D t₂) = []) (h₃ : S.R (M.dreg D t₃) = [])
    (h₄ : S.R (M.dreg D t₄) = []) (h₅ : S.R (M.dreg D t₅) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ m₃ n, v'.user.2 = v.user.2 ∧
      m₃ + 2 ≤ M.time (Nat.size y + Nat.size d) ∧ n ≤ 2300 * k + 2900 + m₃ ∧
      Exec (M.tab D B main) (M.newtonLevelB D B SIX Dd Aa B1 B2 B3 ONE Y Yn wK w2K wL t₁ t₂ t₃
        t₄ t₅) (dmk v S gi go) n
        (dmk v' { S with
          R := Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update S.R (M.dreg D B3) []) (M.dreg D B2) [])
            (M.dreg D SIX) []) (M.dreg D Dd) []) (M.dreg D Y) []) (M.dreg D ONE) [])
            (M.dreg D wL) []) (M.dreg D Aa) (binSyms (4 * k + 4) (y + (2 ^ (4 * k) - y * d) / d)))
            (M.dreg D wK) (S.R (M.dreg D w2K))) (M.dreg D w2K) [] } gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  have hnd : ∀ l : List (Fin D), l.Nodup → (l.map (M.dreg D)).Nodup := fun _ h => M.nodup_dreg D h
  have hyL : y < 2 ^ (4 * k + 4) := lt_of_le_of_lt (Nat.le_add_right _ _) hμL
  have hydL : y * d < 2 ^ (4 * k + 4) :=
    lt_of_le_of_lt hyd (Nat.pow_lt_pow_right (by norm_num) (by omega))
  -- the guess
  obtain ⟨v₁, n₁, hu₁, hn₁, e₁⟩ := newtonGuessProg_exec Empty.elim (B2 := M.dreg D B2)
    (B3 := M.dreg D B3) (ONE := M.dreg D ONE) (Aa := M.dreg D Aa) (Y := M.dreg D Y)
    (B1 := M.dreg D B1) (Yn := M.dreg D Yn) (wK := M.dreg D wK) (w2K := M.dreg D w2K)
    (wL := M.dreg D wL) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂) (t₃ := M.dreg D t₃)
    (by simpa only [List.map_cons, List.map_nil] using
      hnd [B2, B3, ONE, Aa, Y, B1, Yn, wK, w2K, wL, t₁, t₂, t₃] (by regs_nodup))
    (k := k) (a := a) (X₂ := d * (a * a)) hX₂ h2a hz v S hB2 hB3 hO hA hK h2 hwL hY hB1 hYn h₁
    h₂ h₃
  rw [← hy] at e₁
  set S₁ : Stacks (M.T + D) M.A := { S with
    R := Function.update (Function.update (Function.update S.R (M.dreg D Y)
      (binSyms (4 * k + 4) y)) (M.dreg D B2) []) (M.dreg D B3) [] } with hS₁
  -- `B2 := y d`
  obtain ⟨v₂, m₃, hu₂, hm₃, e₂⟩ := M.mulCall_exec D B main (a := M.dreg D Y)
    (b := M.dreg D Dd) (c := M.dreg D B2) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (t₃ := M.dreg D t₃) (t₄ := M.dreg D t₄) (t₅ := M.dreg D t₅)
    (by simpa only [List.map_cons, List.map_nil] using
      hnd [B2, Y, Dd, t₁, t₂, t₃, t₄, t₅] (by regs_nodup)) hyL hdL v₁ S₁
    (by simp [hS₁, hinp]) (by simp [hS₁, hout]) (by simp [hS₁, hL]) (by intro i; simp [hS₁, hR])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) gi go
  set S₂ : Stacks (M.T + D) M.A := { S₁ with
    R := Function.update S₁.R (M.dreg D B2) (binSyms (4 * k + 4 + (4 * k + 4)) (y * d)) }
    with hS₂
  -- the correction
  obtain ⟨v₃, n₃, hu₃, hn₃, e₃⟩ := newtonFinish_exec Empty.elim (B2 := M.dreg D B2)
    (SIX := M.dreg D SIX) (R := M.dreg D B1) (Dd := M.dreg D Dd) (Y := M.dreg D Y)
    (ONE := M.dreg D ONE) (Rn := M.dreg D B3) (Yn := M.dreg D Yn) (Aa := M.dreg D Aa)
    (wK := M.dreg D wK) (w2K := M.dreg D w2K) (wL := M.dreg D wL) (t₁ := M.dreg D t₁)
    (t₂ := M.dreg D t₂) (t₃ := M.dreg D t₃)
    (by simpa only [List.map_cons, List.map_nil] using
      hnd [B2, SIX, B1, Dd, Y, ONE, B3, Yn, Aa, wK, w2K, wL, t₁, t₂, t₃] (by regs_nodup))
    (k := k) (d := d) (y := y) hyd hd0 hdL hμL hc v₂ S₂
    (by simp [hS₂]) (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
    (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
    (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
    (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
    (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
    (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
    (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
  refine ⟨v₃, m₃, _, ?_, hm₃, ?_, Exec.cast (Exec.seq (exec_hostCode e₁ gi go)
    (Exec.seq e₂ (exec_hostCode e₃ gi go))) rfl ?_⟩
  · rw [hu₃, hu₂, hu₁]
  · have := Nat.size_le.2 hydL
    omega
  · clear e₁ e₂ e₃
    show dmk v₃ _ gi go = dmk v₃ _ gi go
    congr 1
    simp only [hS₂, hS₁]
    clear hS₂ hS₁ hnd hn₁ hn₃ hm₃ hyL hydL hy hX₂ h2a hz hyd hd0 hdL hμL hc
    congr 1
    funext j
    by_cases hj1 : j = M.dreg D B3
    · subst hj1; simp [*, Ne.symm]
    by_cases hj2 : j = M.dreg D B2
    · subst hj2; simp [*, Ne.symm]
    by_cases hj3 : j = M.dreg D SIX
    · subst hj3; simp [*, Ne.symm]
    by_cases hj4 : j = M.dreg D Dd
    · subst hj4; simp [*, Ne.symm]
    by_cases hj5 : j = M.dreg D Y
    · subst hj5; simp [*, Ne.symm]
    by_cases hj6 : j = M.dreg D ONE
    · subst hj6; simp [*, Ne.symm]
    by_cases hj7 : j = M.dreg D wL
    · subst hj7; simp [*, Ne.symm]
    by_cases hj8 : j = M.dreg D Aa
    · subst hj8; simp [*, Ne.symm]
    by_cases hj9 : j = M.dreg D wK
    · subst hj9; simp [*, Ne.symm]
    by_cases hj10 : j = M.dreg D w2K
    · subst hj10; simp [*, Ne.symm]
    simp [*]

/-! ### The level -/

/-- One Newton level on the DFT registers. -/
def newtonLevel (Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 Y Yn t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (M.newtonLevelA D B Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 t₁ t₂ t₃ t₄ t₅)
    (M.newtonLevelB D B SIX Dd Aa B1 B2 B3 ONE Y Yn wK w2K wL t₁ t₂ t₃ t₄ t₅)

/-- `newtonLevel`: `A := binSyms (4k + 4) (μ (2k))`, `wK := wK ++ wK`, `Cnt := Cnt.drop k`. -/
theorem newtonLevel_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 Y Yn t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [Cnt, Dp, wK, w2K, wL, ONE, SIX, B1, Dd, Aa, B2, B3, Y, Yn, t₁, t₂, t₃, t₄,
      t₅].Nodup)
    {N Dv k : ℕ} (hk : 1 ≤ k) (hkN : k + k ≤ N) (hD1 : 2 ^ (N - 1) ≤ Dv) (hD : Dv < 2 ^ N)
    (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ j, S.L j = [])
    (hR : ∀ i, S.R (M.emb D i) = []) (hDp : S.R (M.dreg D Dp) = (binSyms N Dv).reverse)
    (hK : (S.R (M.dreg D wK)).length = k)
    (hA : S.R (M.dreg D Aa) = binSyms (k + k + 4) (2 ^ (k + k) / (Dv / 2 ^ (N - k))))
    (h2 : S.R (M.dreg D w2K) = []) (hwL : S.R (M.dreg D wL) = []) (hO : S.R (M.dreg D ONE) = [])
    (hS6 : S.R (M.dreg D SIX) = []) (hB1 : S.R (M.dreg D B1) = []) (hDd : S.R (M.dreg D Dd) = [])
    (hB2 : S.R (M.dreg D B2) = []) (hB3 : S.R (M.dreg D B3) = []) (hY : S.R (M.dreg D Y) = [])
    (hYn : S.R (M.dreg D Yn) = []) (h₁ : S.R (M.dreg D t₁) = []) (h₂ : S.R (M.dreg D t₂) = [])
    (h₃ : S.R (M.dreg D t₃) = []) (h₄ : S.R (M.dreg D t₄) = []) (h₅ : S.R (M.dreg D t₅) = [])
    (gi go : List Γ') :
    ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ n, v'.user.2 = v.user.2 ∧
      n ≤ (3200 + 12 * H (4 * k + 4)) * k + 4000 + 15 * H (4 * k + 4) ∧
      Exec (M.tab D B main) (M.newtonLevel D B Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 Y Yn t₁
        t₂ t₃ t₄ t₅) (dmk v S gi go) n
        (dmk v' { S with
          R := Function.update (Function.update (Function.update S.R (M.dreg D Cnt)
            ((S.R (M.dreg D Cnt)).drop k)) (M.dreg D wK)
            (S.R (M.dreg D wK) ++ S.R (M.dreg D wK))) (M.dreg D Aa)
            (binSyms (4 * k + 4) (2 ^ (k + k + (k + k)) / (Dv / 2 ^ (N - (k + k))))) } gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  set d := Dv / 2 ^ (N - (k + k)) with hd
  set a := 2 ^ (k + k) / (Dv / 2 ^ (N - k)) with ha
  set y := 2 ^ (k + 1) * a - (d * (a * a) / 2 ^ (k + k) + 1) with hy
  obtain ⟨hd0, hdlt, hale, hz, hyd, hc, hμlt, hμ⟩ := newton_level_arith hk hkN hD1 hD hd ha hy
  rw [← hd] at hμ
  -- the first half
  obtain ⟨v₁, m₁, m₂, n₁, hu₁, hm₁, hm₂, hn₁, e₁⟩ := M.newtonLevelA_exec D B main (Cnt := Cnt)
    (Dp := Dp) (wK := wK) (w2K := w2K) (wL := wL) (ONE := ONE) (SIX := SIX) (B1 := B1)
    (Dd := Dd) (Aa := Aa) (B2 := B2) (B3 := B3) (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (t₄ := t₄)
    (t₅ := t₅) (by regs_nodup) hkN hD hale v S hinp hout hL hR hDp hK hA h2 hwL hO hS6 hB1 hDd
    hB2 hB3 h₁ h₂ h₃ h₄ h₅ gi go
  rw [← hd] at e₁ hm₂
  clear_value y a d
  clear hd ha
  set S₁ : Stacks (M.T + D) M.A := { S with
    R := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (Function.update S.R (M.dreg D Cnt) ((S.R (M.dreg D Cnt)).drop k)) (M.dreg D w2K)
      (S.R (M.dreg D wK) ++ S.R (M.dreg D wK))) (M.dreg D wL)
      ([tick, tick, tick, tick] ++ (S.R (M.dreg D wK) ++ S.R (M.dreg D wK)) ++
        (S.R (M.dreg D wK) ++ S.R (M.dreg D wK))))
      (M.dreg D ONE) (binSyms (4 * k + 4) 1)) (M.dreg D SIX)
      (binSyms (4 * k + 4) (2 ^ (4 * k)))) (M.dreg D Dd) (binSyms (4 * k + 4) d)) (M.dreg D Aa)
      (binSyms (4 * k + 4) a)) (M.dreg D B3) (binSyms (4 * k + 4) (a * a))) (M.dreg D B2)
      (binSyms (4 * k + 4 + (4 * k + 4)) (d * (a * a))) } with hS₁
  -- value bounds
  have hL4 : ∀ e, e < 4 * k + 4 → 2 ^ e < 2 ^ (4 * k + 4) := fun e he =>
    Nat.pow_lt_pow_right (by norm_num) he
  have hk1 : a < 2 ^ (k + 2) := lt_of_le_of_lt hale (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have haa : a * a < 2 ^ (k + k + 3) := by
    calc a * a ≤ 2 ^ (k + 1) * 2 ^ (k + 1) := Nat.mul_le_mul hale hale
      _ < 2 ^ (k + k + 3) := by
          rw [← pow_add]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hyle : y ≤ 2 ^ (k + 1) * a := by rw [hy]; exact Nat.sub_le _ _
  have hylt : y < 2 ^ (k + k + 3) := by
    calc y ≤ 2 ^ (k + 1) * 2 ^ (k + 1) := hyle.trans (Nat.mul_le_mul_left _ hale)
      _ < 2 ^ (k + k + 3) := by
          rw [← pow_add]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hdL : d < 2 ^ (4 * k + 4) := lt_trans hdlt (hL4 _ (by omega))
  have hμL : y + (2 ^ (4 * k) - y * d) / d < 2 ^ (4 * k + 4) := lt_trans hμlt (hL4 _ (by omega))
  have hX₂ : d * (a * a) < 2 ^ (4 * k + 4) := by
    calc d * (a * a) < 2 ^ (k + k) * 2 ^ (k + k + 3) := Nat.mul_lt_mul'' hdlt haa
      _ = 2 ^ (4 * k + 3) := by rw [← pow_add]; congr 1; ring
      _ < 2 ^ (4 * k + 4) := hL4 _ (by omega)
  have h2a : 2 ^ (k + 1) * a < 2 ^ (4 * k + 4) := by
    calc 2 ^ (k + 1) * a ≤ 2 ^ (k + 1) * 2 ^ (k + 1) := Nat.mul_le_mul_left _ hale
      _ = 2 ^ (k + k + 2) := by rw [← pow_add]; congr 1; ring
      _ < 2 ^ (4 * k + 4) := hL4 _ (by omega)
  -- the second half
  obtain ⟨v₂, m₃, n₂, hu₂, hm₃, hn₂, e₂⟩ := M.newtonLevelB_exec D B main (SIX := SIX)
    (Dd := Dd) (Aa := Aa) (B1 := B1) (B2 := B2) (B3 := B3) (ONE := ONE) (Y := Y) (Yn := Yn)
    (wK := wK) (w2K := w2K) (wL := wL) (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (t₄ := t₄) (t₅ := t₅)
    (by regs_nodup) hy hX₂ h2a hz hyd hd0 hdL hμL hc v₁ S₁ (by simp [hS₁, hinp])
    (by simp [hS₁, hout]) (by simp [hS₁, hL]) (by intro i; simp [hS₁, hR]) (by simp [hS₁])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm] <;> omega)
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) gi go
  rw [hμ] at e₂
  refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.cast (Exec.seq e₁ e₂) rfl ?_⟩
  · -- the time
    set h := H (4 * k + 4) with hh
    have hTs : ∀ s, s ≤ 4 * k + 4 → M.time s ≤ 4 * (k * h) + 5 * h := fun s hs => by
      calc M.time s ≤ (s + 1) * H s := hT s
        _ ≤ (4 * k + 5) * h := Nat.mul_le_mul (by omega) (hH hs)
        _ = 4 * (k * h) + 5 * h := by ring
    have hs₁ : Nat.size a + Nat.size a ≤ 4 * k + 4 := by
      have := Nat.size_le.2 hk1; omega
    have hs₂ : Nat.size d + Nat.size (a * a) ≤ 4 * k + 4 := by
      have := Nat.size_le.2 hdlt; have := Nat.size_le.2 haa; omega
    have hs₃ : Nat.size y + Nat.size d ≤ 4 * k + 4 := by
      have := Nat.size_le.2 hylt; have := Nat.size_le.2 hdlt; omega
    have hm₁' := hm₁.trans (hTs _ hs₁)
    have hm₂' := hm₂.trans (hTs _ hs₂)
    have hm₃' := hm₃.trans (hTs _ hs₃)
    have hc' : (3200 + 12 * h) * k = 3200 * k + 12 * (k * h) := by ring
    omega
  · -- the final store
    clear e₁ e₂
    show dmk v₂ _ gi go = dmk v₂ _ gi go
    congr 1
    simp only [hS₁]
    clear hS₁ hμ hL4 hm₁ hm₂ hm₃ hn₁ hn₂ hd0 hdlt hale hz hyd hc hμlt hk1 haa hyle hylt hdL hμL
      hX₂ h2a hy
    congr 1
    funext j
    by_cases hj1 : j = M.dreg D Cnt
    · subst hj1; simp [*, Ne.symm]
    by_cases hj2 : j = M.dreg D w2K
    · subst hj2; simp [*, Ne.symm]
    by_cases hj3 : j = M.dreg D wL
    · subst hj3; simp [*, Ne.symm]
    by_cases hj4 : j = M.dreg D ONE
    · subst hj4; simp [*, Ne.symm]
    by_cases hj5 : j = M.dreg D SIX
    · subst hj5; simp [*, Ne.symm]
    by_cases hj6 : j = M.dreg D Dd
    · subst hj6; simp [*, Ne.symm]
    by_cases hj7 : j = M.dreg D Aa
    · subst hj7; simp [*, Ne.symm]
    by_cases hj8 : j = M.dreg D B2
    · subst hj8; simp [*, Ne.symm]
    by_cases hj9 : j = M.dreg D B3
    · subst hj9; simp [*, Ne.symm]
    by_cases hj10 : j = M.dreg D Y
    · subst hj10; simp [*, Ne.symm]
    by_cases hj11 : j = M.dreg D wK
    · subst hj11; simp [*, Ne.symm]
    simp [*]

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
