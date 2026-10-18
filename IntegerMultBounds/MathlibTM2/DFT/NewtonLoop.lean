module

public import IntegerMultBounds.MathlibTM2.DFT.NewtonLevel
public import IntegerMultBounds.MathlibTM2.DFT.HostSteps
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Newton reciprocal

`M.recipProg D B Pw wR Cnt Dp wK … t₅` computes `⌊2 ^ (k' + w) / p⌋` for
`2 ^ (w - 1) ≤ p < 2 ^ w`, from `Pw = binSyms w p` and a width register `wR` of `r ≥ w`
symbols, for some `k'` with `r + 1 ≤ k' ≤ 2 r` left as the length of `wK` (`recip_exec`):

1. `recipSetup`: `Dp := (binSyms N D).reverse` for `N = 2 r + w` and `D = 2 ^ (2r) p`
   (`2 r` zeros by `bzero`, then `p` most significant bit on top by `bcopy` and `moveR`),
   `A := binSyms 6 4` (the reciprocal `μ 1 = 4` of the top bit), `wK := [tick]`, `Cnt := wR`;
2. while `Cnt` is nonempty, `newtonLevel` (`newtonLoop_aux`, with the potential `newtonPot`);
3. `Dp` cleared.

For `k' ≥ w` the top `k'` bits of `D` are `2 ^ (k' - w) p`, so
`μ k' = ⌊2 ^ (k' + w) / p⌋` (`recip_value`). As in the Hensel iteration the counter shrinks by
`k` while `k` doubles: a level starts only with `k ≤ r`, and the levels cost at most
`(7200 + 27 h) (2 r + 1)` steps in all, for `h = H (4 r + 4)`.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

/-- The top `k` bits of `2 ^ (2r) p` in `2 r + w` bits, for `w ≤ r < k ≤ 2 r`. -/
theorem recip_value {r w p k : ℕ} (hwr : w ≤ r) (hk1 : r + 1 ≤ k) (hk2 : k ≤ 2 * r) :
    2 ^ (k + k) / (2 ^ (r + r) * p / 2 ^ (r + r + w - k)) = 2 ^ (k + w) / p := by
  have e : 2 ^ (r + r) * p = 2 ^ (r + r + w - k) * (2 ^ (k - w) * p) := by
    rw [← mul_assoc, ← pow_add, show r + r + w - k + (k - w) = r + r by omega]
  rw [e, Nat.mul_div_cancel_left _ (by positivity), ← Nat.div_div_eq_div_mul,
    Nat.pow_div (by omega) (by norm_num), show k + k - (k - w) = k + w by omega]

/-! ### The setup on the host -/

section Setup

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- `binSyms 6 4` onto register `i`. -/
def pushFour (i : Fin T) : Pr P T Q A U :=
  .seq (pushS i (bitSymbol false)) (.seq (pushS i (bitSymbol false))
    (.seq (pushS i (bitSymbol false)) (.seq (pushS i (bitSymbol true))
      (.seq (pushS i (bitSymbol false)) (pushS i (bitSymbol false))))))

theorem binSyms_six_four : (binSyms 6 4 : List (Fin (A + 4))) =
    [bitSymbol false, bitSymbol false, bitSymbol true, bitSymbol false, bitSymbol false,
      bitSymbol false] := rfl

theorem pushFour_exec (i : Fin T) (v : HS T Q A U) (S : Stacks T A) (hi : S.R i = []) :
    Exec body (pushFour i) (mk v S) 6
      (mk v { S with R := Function.update S.R i (binSyms 6 4) }) := by
  refine Exec.cast (Exec.seq (pushS_exec body i (bitSymbol false) v S)
    (Exec.seq (pushS_exec body i (bitSymbol false) v _)
      (Exec.seq (pushS_exec body i (bitSymbol false) v _)
        (Exec.seq (pushS_exec body i (bitSymbol true) v _)
          (Exec.seq (pushS_exec body i (bitSymbol false) v _)
            (pushS_exec body i (bitSymbol false) v _)))))) rfl ?_
  rw [binSyms_six_four]
  congr 2
  funext j
  by_cases hj : j = i
  · subst hj; simp [hi]
  · simp [hj]

/-- `Dp := (binSyms (2r + w) (2 ^ (2r) p)).reverse`, `A := binSyms 6 4`, `wK := [tick]`,
`Cnt := wR`. -/
def recipSetup (Pw wR Cnt Dp wK Aa B1 t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bzero wR Dp t₁) (.seq (bzero wR Dp t₁) (.seq (bcopy Pw B1 t₁ t₂)
    (.seq (moveR B1 Dp id) (.seq (pushFour Aa) (.seq (pushS wK tick) (bcopy wR Cnt t₁ t₂))))))

theorem recipSetup_exec {Pw wR Cnt Dp wK Aa B1 t₁ t₂ : Fin T}
    (hreg : [Pw, wR, Cnt, Dp, wK, Aa, B1, t₁, t₂].Nodup) {r w p : ℕ} (v : HS T Q A U)
    (S : Stacks T A) (hwR : (S.R wR).length = r) (hPw : S.R Pw = binSyms w p)
    (hCnt : S.R Cnt = []) (hDp : S.R Dp = []) (hK : S.R wK = []) (hA : S.R Aa = [])
    (hB1 : S.R B1 = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (recipSetup Pw wR Cnt Dp wK Aa B1 t₁ t₂) (mk v S) (14 * r + 8 * w + 29)
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update S.R Dp
            (binSyms (r + r + w) (2 ^ (r + r) * p)).reverse) Aa (binSyms 6 4)) wK [tick]) Cnt
            (S.R wR) }) := by
  have hreg' := hreg
  regs_ne hreg'
  -- `2 r` zeros
  obtain ⟨v₁, hu₁, e₁⟩ := bzero_exec body (wR := wR) (c := Dp) (t := t₁) (by regs_nodup) v S h₁
  rw [hwR, hDp, List.append_nil] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R Dp (binSyms r 0) } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := bzero_exec body (wR := wR) (c := Dp) (t := t₁) (by regs_nodup) v₁ S₁
    (by simp [hS₁, *, Ne.symm])
  rw [show (S₁.R wR).length = r by simp [hS₁, *, Ne.symm],
    show S₁.R Dp = binSyms r 0 by simp [hS₁]] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R Dp (binSyms r 0 ++ binSyms r 0) }
    with hS₂
  -- `p`, most significant bit on top
  obtain ⟨v₃, hu₃, e₃⟩ := bcopy_exec body (a := Pw) (c := B1) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₂ S₂ (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
  rw [show S₂.R Pw = binSyms w p by simp [hS₂, hS₁, *, Ne.symm],
    show S₂.R B1 = [] by simp [hS₂, hS₁, *, Ne.symm], List.append_nil, length_binSyms] at e₃
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R B1 (binSyms w p) } with hS₃
  obtain ⟨v₄, hu₄, e₄⟩ := moveR_exec body B1 Dp (Ne.symm ‹Dp ≠ B1›) id v₃ S₃
  have hDpv : ((binSyms w p).map id).reverse ++ (binSyms r 0 ++ binSyms r 0) =
      ((binSyms (r + r + w) (2 ^ (r + r) * p)).reverse : List (Fin (A + 4))) := by
    rw [← binSyms_shift_pow, List.reverse_append, List.reverse_replicate, List.map_id,
      binSyms_zero_right, List.replicate_add]
  rw [show S₃.R B1 = binSyms w p by simp [hS₃], length_binSyms,
    show movedR S₃.R B1 Dp id (binSyms w p) = Function.update (Function.update S₃.R B1 []) Dp
      (binSyms (r + r + w) (2 ^ (r + r) * p)).reverse by
      rw [movedR, show S₃.R Dp = binSyms r 0 ++ binSyms r 0 by simp [hS₃, hS₂, ‹Dp ≠ B1›],
        hDpv]] at e₄
  set S₄ : Stacks T A := { S₃ with
    R := Function.update (Function.update S₃.R B1 []) Dp
      (binSyms (r + r + w) (2 ^ (r + r) * p)).reverse } with hS₄
  -- `A`, `wK`, `Cnt`
  have e₅ := pushFour_exec body Aa v₄ S₄ (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
  set S₅ : Stacks T A := { S₄ with R := Function.update S₄.R Aa (binSyms 6 4) } with hS₅
  have e₆ := pushS_exec body wK tick v₄ S₅
  rw [show S₅.R wK = [] by simp [hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm]] at e₆
  set S₆ : Stacks T A := { S₅ with R := Function.update S₅.R wK [tick] } with hS₆
  obtain ⟨v₇, hu₇, e₇⟩ := bcopy_exec body (a := wR) (c := Cnt) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₄ S₆ (by simp [hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
  rw [show S₆.R wR = S.R wR by simp [hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm],
    show S₆.R Cnt = [] by simp [hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm], List.append_nil,
    hwR] at e₇
  refine ⟨v₇, by rw [hu₇, hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃
    (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆ e₇)))))) (by ring) ?_⟩
  clear e₁ e₂ e₃ e₄ e₅ e₆ e₇
  simp only [hS₆, hS₅, hS₄, hS₃, hS₂, hS₁]
  clear hS₆ hS₅ hS₄ hS₃ hS₂ hS₁ hDpv
  congr 2
  funext j
  by_cases hj1 : j = Dp
  · subst hj1; simp [*, Ne.symm]
  by_cases hj2 : j = B1
  · subst hj2; simp [*, Ne.symm]
  by_cases hj3 : j = Aa
  · subst hj3; simp [*, Ne.symm]
  by_cases hj4 : j = wK
  · subst hj4; simp [*, Ne.symm]
  by_cases hj5 : j = Cnt
  · subst hj5; simp [*, Ne.symm]
  simp [*]

end Setup

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (D : ℕ) (B : Type)

/-! ### The iteration -/

/-- The loop body: a level, then the test of the counter. -/
def newtonBody (Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 Y Yn t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (M.newtonLevel D B Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 Y Yn t₁ t₂ t₃ t₄ t₅)
    (hostCode (.act (peekR (M.dreg D Cnt))))

/-- The cost bound of the iteration with `w` counter symbols and `k` bits. -/
def newtonPot (c w k : ℕ) : ℕ := if w = 0 then 1 else c * (2 * w + k) + 2 * w + 1

/-- The iteration, by strong induction on the counter. -/
theorem newtonLoop_aux (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 Y Yn t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [Cnt, Dp, wK, w2K, wL, ONE, SIX, B1, Dd, Aa, B2, B3, Y, Yn, t₁, t₂, t₃, t₄,
      t₅].Nodup)
    {r N Dv : ℕ} (hrN : r + r ≤ N) (hD1 : 2 ^ (N - 1) ≤ Dv) (hD : Dv < 2 ^ N)
    (gi go : List Γ') :
    ∀ w k (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A),
      (S.R (M.dreg D Cnt)).length = w → (S.R (M.dreg D wK)).length = k → 1 ≤ k →
      S.R (M.dreg D Aa) = binSyms (k + k + 4) (2 ^ (k + k) / (Dv / 2 ^ (N - k))) →
      ((w = 0 ∧ r + 1 ≤ k ∧ k ≤ 2 * r) ∨ (1 ≤ w ∧ w + k = r + 1)) →
      v.flag = (S.R (M.dreg D Cnt)).head?.isSome →
      S.inp = [] → S.out = [] → (∀ j, S.L j = []) → (∀ i, S.R (M.emb D i) = []) →
      S.R (M.dreg D Dp) = (binSyms N Dv).reverse →
      S.R (M.dreg D w2K) = [] → S.R (M.dreg D wL) = [] → S.R (M.dreg D ONE) = [] →
      S.R (M.dreg D SIX) = [] → S.R (M.dreg D B1) = [] → S.R (M.dreg D Dd) = [] →
      S.R (M.dreg D B2) = [] → S.R (M.dreg D B3) = [] → S.R (M.dreg D Y) = [] →
      S.R (M.dreg D Yn) = [] → S.R (M.dreg D t₁) = [] → S.R (M.dreg D t₂) = [] →
      S.R (M.dreg D t₃) = [] → S.R (M.dreg D t₄) = [] → S.R (M.dreg D t₅) = [] →
      ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ (Kc : List (Fin (M.A + 4))) (k' n : ℕ),
        v'.user.2 = v.user.2 ∧ Kc.length = k' ∧ r + 1 ≤ k' ∧ k' ≤ 2 * r ∧
        n ≤ newtonPot (7200 + 27 * H (4 * r + 4)) w k ∧
        Exec (M.tab D B main) (.loop (·.flag) (M.newtonBody D B Cnt Dp wK w2K wL ONE SIX B1 Dd
          Aa B2 B3 Y Yn t₁ t₂ t₃ t₄ t₅)) (dmk v S gi go) n
          (dmk v' { S with
            R := Function.update (Function.update (Function.update S.R (M.dreg D Cnt) [])
              (M.dreg D wK) Kc) (M.dreg D Aa)
              (binSyms (k' + k' + 4) (2 ^ (k' + k') / (Dv / 2 ^ (N - k')))) } gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro k v S hw hk hk1 hA hinv hf hinp hout hL hR hDp h2 hwL hO hS6 hB1 hDd hB2 hB3 hY hYn h₁
    h₂ h₃ h₄ h₅
  rcases Nat.eq_zero_or_pos w with rfl | hwpos
  · -- the counter is empty: the loop stops
    obtain ⟨-, hrk, hk2r⟩ := hinv.resolve_right (by omega)
    have hW : S.R (M.dreg D Cnt) = [] := List.length_eq_zero_iff.1 hw
    refine ⟨v, S.R (M.dreg D wK), k, 1, rfl, hk, hrk, hk2r, by simp [newtonPot],
      Exec.cast (Exec.loop_false (by show v.flag = false; rw [hf, hW]; rfl)) rfl ?_⟩
    congr 1
    rw [← hA, ← hW, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  · -- one level, then the rest of the loop
    have hwk : w + k = r + 1 := (hinv.resolve_left (by omega)).2
    have hkr : k ≤ r := by omega
    obtain ⟨v₁, n₁, hu₁, hn₁, e₁⟩ := M.newtonLevel_exec D B main H hH hT hreg hk1 (by omega) hD1
      hD v S hinp hout hL hR hDp hk hA h2 hwL hO hS6 hB1 hDd hB2 hB3 hY hYn h₁ h₂ h₃ h₄ h₅ gi go
    set S₁ : Stacks (M.T + D) M.A := { S with
      R := Function.update (Function.update (Function.update S.R (M.dreg D Cnt)
        ((S.R (M.dreg D Cnt)).drop k)) (M.dreg D wK) (S.R (M.dreg D wK) ++ S.R (M.dreg D wK)))
        (M.dreg D Aa) (binSyms (4 * k + 4) (2 ^ (k + k + (k + k)) / (Dv / 2 ^ (N - (k + k))))) }
      with hS₁
    have e₂ := M.peek_exec D B main (M.dreg D Cnt) v₁ S₁ gi go
    -- the next state
    have hS₁w : (S₁.R (M.dreg D Cnt)).length = w - k := by simp [hS₁, *, Ne.symm]
    have hA₁ : S₁.R (M.dreg D Aa) =
        binSyms (k + k + (k + k) + 4) (2 ^ (k + k + (k + k)) / (Dv / 2 ^ (N - (k + k)))) := by
      rw [show k + k + (k + k) + 4 = 4 * k + 4 by ring]
      simp [hS₁]
    obtain ⟨v₂, Kc, k', n₂, hu₂, hKc, hrk', hk2r', hn₂, e₃⟩ :=
      ih (w - k) (by omega) (k + k) { v₁ with flag := (S₁.R (M.dreg D Cnt)).head?.isSome } S₁
        hS₁w (by simp [hS₁, *, Ne.symm]) (by omega) hA₁
        (by
          by_cases hwk' : w ≤ k
          · exact Or.inl ⟨by omega, by omega, by omega⟩
          · exact Or.inr ⟨by omega, by omega⟩)
        rfl (by simp [hS₁, hinp]) (by simp [hS₁, hout]) (by simp [hS₁, hL])
        (by intro i; simp [hS₁, hR]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
        (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
        (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
        (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
        (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
        (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    -- the time of the level
    set h := H (4 * r + 4) with hh
    have hHk : H (4 * k + 4) ≤ h := hH (by omega)
    have hhk : h ≤ h * k := Nat.le_mul_of_pos_right h hk1
    have hn₁' : n₁ ≤ (7200 + 27 * h) * k := by
      have e1 : (3200 + 12 * H (4 * k + 4)) * k ≤ (3200 + 12 * h) * k :=
        Nat.mul_le_mul_right _ (by omega)
      have e2 : (3200 + 12 * h) * k = 3200 * k + 12 * (h * k) := by ring
      have e3 : (7200 + 27 * h) * k = 7200 * k + 27 * (h * k) := by ring
      omega
    refine ⟨v₂, Kc, k', n₁ + 1 + n₂ + 1, by rw [hu₂, hu₁], hKc, hrk', hk2r', ?_,
      Exec.loop_true (by
        show v.flag = true
        rw [hf]
        cases hc : S.R (M.dreg D Cnt) with
        | nil => simp [hc] at hw; omega
        | cons _ _ => rfl) (Exec.seq e₁ e₂) (e₃.cast rfl ?_)⟩
    · -- the potential
      have hpot : newtonPot (7200 + 27 * h) w k =
          (7200 + 27 * h) * (2 * w) + (7200 + 27 * h) * k + 2 * w + 1 := by
        simp only [newtonPot, if_neg (show w ≠ 0 by omega), Nat.mul_add]
      rw [hpot]
      by_cases hwk' : w ≤ k
      · have : newtonPot (7200 + 27 * h) (w - k) (k + k) = 1 := by
          simp [newtonPot, show w - k = 0 by omega]
        rw [this] at hn₂
        omega
      · have : newtonPot (7200 + 27 * h) (w - k) (k + k) =
            (7200 + 27 * h) * (2 * w) + 2 * (w - k) + 1 := by
          simp only [newtonPot, if_neg (show w - k ≠ 0 by omega),
            show 2 * (w - k) + (k + k) = 2 * w by omega]
        rw [this] at hn₂
        omega
    · -- the final store
      show dmk v₂ _ gi go = dmk v₂ _ gi go
      congr 1
      simp only [hS₁]
      congr 1
      exact update3_idem _ (by simpa using ‹Cnt ≠ wK›) (by simpa using ‹Cnt ≠ Aa›)
        (by simpa using ‹wK ≠ Aa›) _ _ _ _ _ _

/-! ### The reciprocal -/

/-- `⌊2 ^ (k' + w) / p⌋` into `A`, `k'` symbols into `wK`. -/
def recipProg (Pw wR Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 Y Yn t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (hostCode (recipSetup (M.dreg D Pw) (M.dreg D wR) (M.dreg D Cnt) (M.dreg D Dp)
      (M.dreg D wK) (M.dreg D Aa) (M.dreg D B1) (M.dreg D t₁) (M.dreg D t₂)))
    (.seq (hostCode (.act (peekR (M.dreg D Cnt))))
      (.seq (.loop (·.flag) (M.newtonBody D B Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 Y Yn t₁ t₂
          t₃ t₄ t₅))
        (hostCode (bclear (M.dreg D Dp)))))

/-- `recipProg`: `A := binSyms (2k' + 4) ⌊2 ^ (k' + w) / p⌋` and `wK` of length `k'`, for some
`r + 1 ≤ k' ≤ 2 r`. -/
theorem recip_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {Pw wR Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 Y Yn t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [Pw, wR, Cnt, Dp, wK, w2K, wL, ONE, SIX, B1, Dd, Aa, B2, B3, Y, Yn, t₁, t₂, t₃, t₄,
      t₅].Nodup)
    {r w p : ℕ} (hw : 1 ≤ w) (hwr : w ≤ r) (hp1 : 2 ^ (w - 1) ≤ p) (hp : p < 2 ^ w)
    (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ j, S.L j = [])
    (hR : ∀ i, S.R (M.emb D i) = []) (hPw : S.R (M.dreg D Pw) = binSyms w p)
    (hwR : (S.R (M.dreg D wR)).length = r) (hCnt : S.R (M.dreg D Cnt) = [])
    (hDp : S.R (M.dreg D Dp) = []) (hK : S.R (M.dreg D wK) = []) (h2 : S.R (M.dreg D w2K) = [])
    (hwL : S.R (M.dreg D wL) = []) (hO : S.R (M.dreg D ONE) = []) (hS6 : S.R (M.dreg D SIX) = [])
    (hB1 : S.R (M.dreg D B1) = []) (hDd : S.R (M.dreg D Dd) = []) (hA : S.R (M.dreg D Aa) = [])
    (hB2 : S.R (M.dreg D B2) = []) (hB3 : S.R (M.dreg D B3) = []) (hY : S.R (M.dreg D Y) = [])
    (hYn : S.R (M.dreg D Yn) = []) (h₁ : S.R (M.dreg D t₁) = []) (h₂ : S.R (M.dreg D t₂) = [])
    (h₃ : S.R (M.dreg D t₃) = []) (h₄ : S.R (M.dreg D t₄) = []) (h₅ : S.R (M.dreg D t₅) = [])
    (gi go : List Γ') :
    ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ (Kc : List (Fin (M.A + 4))) (k' n : ℕ),
      v'.user.2 = v.user.2 ∧ Kc.length = k' ∧ r + 1 ≤ k' ∧ k' ≤ 2 * r ∧
      n ≤ (7200 + 27 * H (4 * r + 4)) * (2 * r + 1) + 20 * r + 10 * w + 40 ∧
      Exec (M.tab D B main) (M.recipProg D B Pw wR Cnt Dp wK w2K wL ONE SIX B1 Dd Aa B2 B3 Y Yn
        t₁ t₂ t₃ t₄ t₅) (dmk v S gi go) n
        (dmk v' { S with
          R := Function.update (Function.update S.R (M.dreg D wK) Kc) (M.dreg D Aa)
            (binSyms (k' + k' + 4) (2 ^ (k' + w) / p)) } gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  have hnd : ∀ l : List (Fin D), l.Nodup → (l.map (M.dreg D)).Nodup := fun _ h => M.nodup_dreg D h
  have hr1 : 1 ≤ r := by omega
  have hD : 2 ^ (r + r) * p < 2 ^ (r + r + w) := by
    rw [pow_add 2 (r + r) w]; exact (Nat.mul_lt_mul_left (by positivity)).2 hp
  have hD1 : 2 ^ (r + r + w - 1) ≤ 2 ^ (r + r) * p := by
    rw [show r + r + w - 1 = r + r + (w - 1) by omega, pow_add]
    exact Nat.mul_le_mul_left _ hp1
  have h2N : 2 ^ (r + r + w) = 2 * 2 ^ (r + r + w - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hbase : 2 ^ (r + r) * p / 2 ^ (r + r + w - 1) = 1 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  -- the setup
  obtain ⟨v₁, hu₁, e₁⟩ := recipSetup_exec Empty.elim (Pw := M.dreg D Pw) (wR := M.dreg D wR)
    (Cnt := M.dreg D Cnt) (Dp := M.dreg D Dp) (wK := M.dreg D wK) (Aa := M.dreg D Aa)
    (B1 := M.dreg D B1) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (by simpa only [List.map_cons, List.map_nil] using
      hnd [Pw, wR, Cnt, Dp, wK, Aa, B1, t₁, t₂] (by regs_nodup)) v S hwR hPw hCnt hDp hK hA hB1
    h₁ h₂
  set S₁ : Stacks (M.T + D) M.A := { S with
    R := Function.update (Function.update (Function.update (Function.update S.R (M.dreg D Dp)
      (binSyms (r + r + w) (2 ^ (r + r) * p)).reverse) (M.dreg D Aa) (binSyms 6 4))
      (M.dreg D wK) [tick]) (M.dreg D Cnt) (S.R (M.dreg D wR)) } with hS₁
  have e₂ := M.peek_exec D B main (M.dreg D Cnt) v₁ S₁ gi go
  -- the iteration
  obtain ⟨v₃, Kc, k', n₃, hu₃, hKc, hrk', hk2r', hn₃, e₃⟩ := M.newtonLoop_aux D B main H hH hT
    (Cnt := Cnt) (Dp := Dp) (wK := wK) (w2K := w2K) (wL := wL) (ONE := ONE) (SIX := SIX)
    (B1 := B1) (Dd := Dd) (Aa := Aa) (B2 := B2) (B3 := B3) (Y := Y) (Yn := Yn) (t₁ := t₁)
    (t₂ := t₂) (t₃ := t₃) (t₄ := t₄) (t₅ := t₅) (by regs_nodup) (r := r) (N := r + r + w)
    (Dv := 2 ^ (r + r) * p) (by omega) hD1 hD gi go r 1
    { v₁ with flag := (S₁.R (M.dreg D Cnt)).head?.isSome } S₁ (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) le_rfl (by rw [hbase]; simp [hS₁, *, Ne.symm])
    (Or.inr ⟨hr1, rfl⟩) rfl (by simp [hS₁, hinp]) (by simp [hS₁, hout]) (by simp [hS₁, hL])
    (by intro i; simp [hS₁, hR]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
  rw [recip_value hwr hrk' hk2r'] at e₃
  set S₃ : Stacks (M.T + D) M.A := { S₁ with
    R := Function.update (Function.update (Function.update S₁.R (M.dreg D Cnt) [])
      (M.dreg D wK) Kc) (M.dreg D Aa) (binSyms (k' + k' + 4) (2 ^ (k' + w) / p)) } with hS₃
  -- clear `Dp`
  obtain ⟨v₄, hu₄, -, e₄⟩ := bclear_exec Empty.elim (M.dreg D Dp) v₃ S₃
  rw [show (S₃.R (M.dreg D Dp)).length = r + r + w by simp [hS₃, hS₁, *, Ne.symm]] at e₄
  refine ⟨v₄, Kc, k', _, by rw [hu₄, hu₃, hu₁], hKc, hrk', hk2r', ?_,
    Exec.cast (Exec.seq (exec_hostCode e₁ gi go) (Exec.seq e₂ (Exec.seq e₃
      (exec_hostCode e₄ gi go)))) rfl ?_⟩
  · simp only [newtonPot, if_neg (show r ≠ 0 by omega)] at hn₃
    omega
  · clear e₁ e₂ e₃ e₄
    show dmk v₄ _ gi go = dmk v₄ _ gi go
    congr 1
    simp only [hS₃, hS₁]
    clear hS₃ hS₁ hnd hn₃ hD hD1 h2N hbase
    congr 1
    funext j
    by_cases hj1 : j = M.dreg D Dp
    · subst hj1; simp [*, Ne.symm]
    by_cases hj2 : j = M.dreg D Aa
    · subst hj2; simp [*, Ne.symm]
    by_cases hj3 : j = M.dreg D wK
    · subst hj3; simp [*, Ne.symm]
    by_cases hj4 : j = M.dreg D Cnt
    · subst hj4; simp [*, Ne.symm]
    simp [*]

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
