module

public import IntegerMultBounds.MathlibTM2.DFT.Hensel
public import IntegerMultBounds.MathlibTM2.DFT.HostSteps
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Hensel iteration

`M.henselProg D B wR W K K2 pW P2 Y Z Ur Yn t₁ … t₅` computes `p'` with `2 ^ r ∣ p p' + 1` for an
odd `p`, from `pW = binSyms (r + r) p` and a width register `wR` of `r` symbols:

1. `W := wR` (a unary counter of `r` symbols), `K := [tick]`, `Y := binSyms 1 1`;
2. while `W` is nonempty, `henselRound` (`W` loses `|K|` symbols, `K` doubles, `Y` is lifted);
3. `Y := Y mod 2 ^ r` (`btrunc` by `wR`), `K` cleared.

The counter shrinks by `k` while `k` doubles, so a round starts only with `k ≤ r` and the sum of
the `k` over all rounds is at most `2 r + 1`: the iteration costs `O(r)` steps plus the products
(`henselLoop_aux`, with the potential `(400 + 8 h) (2 w + k) + 252 w + 1` for `w` symbols left in
`W`). With a time majorant `M.time n ≤ (n + 1) H n`, `H` monotone, and `h = H (3 r)`,
`hensel_exec` bounds the whole procedure by `(400 + 8 h) (2 r + 1) + 270 r + 20` steps.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (D : ℕ) (B : Type)

/-- The loop body: a round, then the test of the counter. -/
def henselBody (W K K2 pW P2 Y Z Ur Yn t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (M.henselRound D B W K K2 pW P2 Y Z Ur Yn t₁ t₂ t₃ t₄ t₅)
    (hostCode (.act (peekR (M.dreg D W))))

/-- The cost bound of the loop with `w` counter symbols and `k` bits. -/
def henselPot (c w k : ℕ) : ℕ := if w = 0 then 1 else c * (2 * w + k) + 252 * w + 1

/-- The loop, by strong induction on the counter. -/
theorem henselLoop_aux (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {W K K2 pW P2 Y Z Ur Yn t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [W, K, K2, pW, P2, Y, Z, Ur, Yn, t₁, t₂, t₃, t₄, t₅].Nodup) {r p : ℕ}
    (gi go : List Γ') :
    ∀ w k y (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A),
      (S.R (M.dreg D W)).length = w → (S.R (M.dreg D K)).length = k → 1 ≤ k →
      S.R (M.dreg D Y) = binSyms k y → y < 2 ^ k → 2 ^ k ∣ p * y + 1 →
      ((w = 0 ∧ r + 1 ≤ k ∧ k ≤ 2 * r) ∨ (1 ≤ w ∧ w + k = r + 1)) →
      v.flag = (S.R (M.dreg D W)).head?.isSome →
      S.inp = [] → S.out = [] → (∀ j, S.L j = []) → (∀ i, S.R (M.emb D i) = []) →
      S.R (M.dreg D pW) = binSyms (r + r) p →
      S.R (M.dreg D K2) = [] → S.R (M.dreg D P2) = [] → S.R (M.dreg D Z) = [] →
      S.R (M.dreg D Ur) = [] → S.R (M.dreg D Yn) = [] → S.R (M.dreg D t₁) = [] →
      S.R (M.dreg D t₂) = [] → S.R (M.dreg D t₃) = [] → S.R (M.dreg D t₄) = [] →
      S.R (M.dreg D t₅) = [] →
      ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ (Kc : List (Fin (M.A + 4))) (k' y' n : ℕ),
        v'.user.2 = v.user.2 ∧ Kc.length = k' ∧ y' < 2 ^ k' ∧ 2 ^ k' ∣ p * y' + 1 ∧
        r + 1 ≤ k' ∧ k' ≤ 2 * r ∧ n ≤ henselPot (400 + 8 * H (3 * r)) w k ∧
        Exec (M.tab D B main) (.loop (·.flag) (M.henselBody D B W K K2 pW P2 Y Z Ur Yn t₁ t₂ t₃
          t₄ t₅)) (dmk v S gi go) n
          (dmk v' { S with
            R := Function.update (Function.update (Function.update S.R (M.dreg D W) [])
              (M.dreg D K) Kc) (M.dreg D Y) (binSyms k' y') } gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro k y v S hw hk hk1 hY hy hdvd hinv hf hinp hout hL hR hpW hK2 hP2 hZ hU hYn h₁ h₂ h₃ h₄
    h₅
  rcases Nat.eq_zero_or_pos w with rfl | hwpos
  · -- the counter is empty: the loop stops
    obtain ⟨-, hrk, hk2r⟩ := hinv.resolve_right (by omega)
    have hW : S.R (M.dreg D W) = [] := List.length_eq_zero_iff.1 hw
    refine ⟨v, S.R (M.dreg D K), k, y, 1, rfl, hk, hy, hdvd, hrk, hk2r, by simp [henselPot],
      Exec.cast (Exec.loop_false (by show v.flag = false; rw [hf, hW]; rfl)) rfl ?_⟩
    congr 1
    rw [← hY, ← hW, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  · -- one round, then the rest of the loop
    have hwk : w + k = r + 1 := (hinv.resolve_left (by omega)).2
    have hkr : k ≤ r := by omega
    obtain ⟨v₁, m₁, m₂, n₁, hu₁, hm₁, hm₂, hn₁, e₁⟩ := M.henselRound_exec D B main hreg hk1 hkr
      hy v S hinp hout hL hR hk hpW hY hK2 hP2 hZ hU hYn h₁ h₂ h₃ h₄ h₅ gi go
    set S₁ : Stacks (M.T + D) M.A := { S with
      R := Function.update (Function.update (Function.update S.R (M.dreg D W)
        ((S.R (M.dreg D W)).drop k)) (M.dreg D K) (S.R (M.dreg D K) ++ S.R (M.dreg D K)))
        (M.dreg D Y) (binSyms (k + k) (henselNext p k y)) } with hS₁
    have e₂ := M.peek_exec D B main (M.dreg D W) v₁ S₁ gi go
    -- the next state
    have hS₁w : (S₁.R (M.dreg D W)).length = w - k := by simp [hS₁, *, Ne.symm]
    obtain ⟨v₂, Kc, k', y', n₂, hu₂, hKc, hy', hdvd', hrk', hk2r', hn₂, e₃⟩ :=
      ih (w - k) (by omega) (k + k) (henselNext p k y)
        { v₁ with flag := (S₁.R (M.dreg D W)).head?.isSome } S₁ hS₁w
        (by simp [hS₁, *, Ne.symm]) (by omega) (by simp [hS₁]) (henselNext_lt p k y)
        (hensel_round_dvd p k y hdvd)
        (by
          by_cases hwk' : w ≤ k
          · exact Or.inl ⟨by omega, by omega, by omega⟩
          · exact Or.inr ⟨by omega, by omega⟩)
        rfl (by simp [hS₁, hinp]) (by simp [hS₁, hout]) (by simp [hS₁, hL])
        (by intro i; simp [hS₁, hR]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
        (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
        (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
        (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    -- the time of the round
    set h := H (3 * r) with hh
    have hL₁ : Nat.size (p % 2 ^ (k + k)) + Nat.size y ≤ 3 * k := by
      have := Nat.size_le.2 (Nat.mod_lt p (show 0 < 2 ^ (k + k) by positivity))
      have := Nat.size_le.2 hy
      omega
    have hL₂ : Nat.size (p % 2 ^ (k + k) * y % 2 ^ (k + k)) + Nat.size y ≤ 3 * k := by
      have := Nat.size_le.2 (Nat.mod_lt (p % 2 ^ (k + k) * y)
        (show 0 < 2 ^ (k + k) by positivity))
      have := Nat.size_le.2 hy
      omega
    have hT₁ : ∀ L, L ≤ 3 * k → M.time L ≤ 3 * (k * h) + h := fun L hL => by
      calc M.time L ≤ (L + 1) * H L := hT L
        _ ≤ (3 * k + 1) * h := Nat.mul_le_mul (by omega) (hH (by omega))
        _ = 3 * (k * h) + h := by ring
    have hkh : h ≤ k * h := Nat.le_mul_of_pos_left h hk1
    have hm₁' := (hm₁.trans (hT₁ _ hL₁))
    have hm₂' := (hm₂.trans (hT₁ _ hL₂))
    have hc : (400 + 8 * h) * k = 400 * k + 8 * (k * h) := by ring
    refine ⟨v₂, Kc, k', y', n₁ + 1 + n₂ + 1, by rw [hu₂, hu₁], hKc, hy', hdvd', hrk', hk2r', ?_,
      Exec.loop_true (by
        show v.flag = true
        rw [hf]
        cases hc : S.R (M.dreg D W) with
        | nil => simp [hc] at hw; omega
        | cons _ _ => rfl) (Exec.seq e₁ e₂) (e₃.cast rfl ?_)⟩
    · -- the potential
      have hpot : henselPot (400 + 8 * h) w k = (400 + 8 * h) * (2 * w) + (400 + 8 * h) * k +
          252 * w + 1 := by
        simp only [henselPot, if_neg (show w ≠ 0 by omega), Nat.mul_add]
      rw [hpot]
      by_cases hwk' : w ≤ k
      · have : henselPot (400 + 8 * h) (w - k) (k + k) = 1 := by
          simp [henselPot, show w - k = 0 by omega]
        rw [this] at hn₂
        have : (400 + 8 * h) * (2 * w) ≥ 0 := Nat.zero_le _
        omega
      · have : henselPot (400 + 8 * h) (w - k) (k + k) =
            (400 + 8 * h) * (2 * w) + 252 * (w - k) + 1 := by
          simp only [henselPot, if_neg (show w - k ≠ 0 by omega),
            show 2 * (w - k) + (k + k) = 2 * w by omega]
        rw [this] at hn₂
        omega
    · -- the final store
      show dmk v₂ _ gi go = dmk v₂ _ gi go
      congr 1
      simp only [hS₁]
      congr 1
      exact update3_idem _ (by simpa using ‹W ≠ K›) (by simpa using ‹W ≠ Y›)
        (by simpa using ‹K ≠ Y›) _ _ _ _ _ _

/-- `-p⁻¹ mod 2 ^ r` by Hensel lifting, into `Y`. -/
def henselProg (wR W K K2 pW P2 Y Z Ur Yn t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (hostCode (bcopy (M.dreg D wR) (M.dreg D W) (M.dreg D t₁) (M.dreg D t₂)))
    (.seq (hostCode (.act (.push (.rt (M.dreg D K)) (fun _ => tick) .done)))
      (.seq (hostCode (.act (.push (.rt (M.dreg D Y)) (fun _ => bitSymbol true) .done)))
        (.seq (hostCode (.act (peekR (M.dreg D W))))
          (.seq (.loop (·.flag) (M.henselBody D B W K K2 pW P2 Y Z Ur Yn t₁ t₂ t₃ t₄ t₅))
            (.seq (hostCode (btrunc (M.dreg D Y) (M.dreg D wR) (M.dreg D t₁) (M.dreg D t₂)))
              (hostCode (bclear (M.dreg D K))))))))

/-- `henselProg`: `Y := binSyms r p'` with `2 ^ r ∣ p p' + 1`, for odd `p`. -/
theorem hensel_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {wR W K K2 pW P2 Y Z Ur Yn t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [wR, W, K, K2, pW, P2, Y, Z, Ur, Yn, t₁, t₂, t₃, t₄, t₅].Nodup) {r p : ℕ}
    (hr : 1 ≤ r) (hp : 2 ∣ p + 1) (v : HS (M.T + D) M.Q M.A (M.U × B))
    (S : Stacks (M.T + D) M.A) (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ j, S.L j = [])
    (hR : ∀ i, S.R (M.emb D i) = []) (hwR : (S.R (M.dreg D wR)).length = r)
    (hpW : S.R (M.dreg D pW) = binSyms (r + r) p) (hW : S.R (M.dreg D W) = [])
    (hK : S.R (M.dreg D K) = []) (hK2 : S.R (M.dreg D K2) = []) (hP2 : S.R (M.dreg D P2) = [])
    (hY : S.R (M.dreg D Y) = []) (hZ : S.R (M.dreg D Z) = []) (hU : S.R (M.dreg D Ur) = [])
    (hYn : S.R (M.dreg D Yn) = []) (h₁ : S.R (M.dreg D t₁) = []) (h₂ : S.R (M.dreg D t₂) = [])
    (h₃ : S.R (M.dreg D t₃) = []) (h₄ : S.R (M.dreg D t₄) = []) (h₅ : S.R (M.dreg D t₅) = [])
    (gi go : List Γ') :
    ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ p' n, v'.user.2 = v.user.2 ∧ p' < 2 ^ r ∧
      2 ^ r ∣ p * p' + 1 ∧ n ≤ (400 + 8 * H (3 * r)) * (2 * r + 1) + 270 * r + 20 ∧
      Exec (M.tab D B main) (M.henselProg D B wR W K K2 pW P2 Y Z Ur Yn t₁ t₂ t₃ t₄ t₅)
        (dmk v S gi go) n
        (dmk v' { S with R := Function.update S.R (M.dreg D Y) (binSyms r p') } gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  have hnd : ∀ l : List (Fin D), l.Nodup → (l.map (M.dreg D)).Nodup := fun _ h => M.nodup_dreg D h
  -- `W := wR`
  obtain ⟨v₁, hu₁, e₁⟩ := bcopy_exec Empty.elim (a := M.dreg D wR) (c := M.dreg D W)
    (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂) (by simpa using hnd [wR, W, t₁, t₂] (by regs_nodup))
    v S h₁ h₂
  rw [hW, List.append_nil, hwR] at e₁
  set S₁ : Stacks (M.T + D) M.A :=
    { S with R := Function.update S.R (M.dreg D W) (S.R (M.dreg D wR)) } with hS₁
  -- `K := [tick]`, `Y := binSyms 1 1`
  have e₂ := M.push_exec D B main (M.dreg D K) tick v₁ S₁ gi go
  rw [show S₁.R (M.dreg D K) = [] by simp [hS₁, *, Ne.symm]] at e₂
  set S₂ : Stacks (M.T + D) M.A :=
    { S₁ with R := Function.update S₁.R (M.dreg D K) [tick] } with hS₂
  have e₃ := M.push_exec D B main (M.dreg D Y) (bitSymbol true) v₁ S₂ gi go
  rw [show S₂.R (M.dreg D Y) = [] by simp [hS₂, hS₁, *, Ne.symm]] at e₃
  set S₃ : Stacks (M.T + D) M.A :=
    { S₂ with R := Function.update S₂.R (M.dreg D Y) [bitSymbol true] } with hS₃
  have e₄ := M.peek_exec D B main (M.dreg D W) v₁ S₃ gi go
  have hone : (binSyms 1 1 : List (Fin (M.A + 4))) = [bitSymbol true] := rfl
  -- the loop
  obtain ⟨v₅, Kc, k', y', n₅, hu₅, hKc, hy', hdvd', hrk', hk2r', hn₅, e₅⟩ :=
    M.henselLoop_aux D B main H hH hT (W := W) (K := K) (K2 := K2) (pW := pW) (P2 := P2)
      (Y := Y) (Z := Z) (Ur := Ur) (Yn := Yn) (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (t₄ := t₄)
      (t₅ := t₅) (by regs_nodup) (r := r) (p := p) gi go r 1 1
      { v₁ with flag := (S₃.R (M.dreg D W)).head?.isSome } S₃
      (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, *, Ne.symm]) le_rfl
      (by simp [hS₃, hone]) (by norm_num) (by simpa using hp) (Or.inr ⟨hr, rfl⟩) rfl
      (by simp [hS₃, hS₂, hS₁, hinp]) (by simp [hS₃, hS₂, hS₁, hout])
      (by simp [hS₃, hS₂, hS₁, hL]) (by intro i; simp [hS₃, hS₂, hS₁, hR])
      (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
      (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
      (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
      (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
      (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
      (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
  set S₅ : Stacks (M.T + D) M.A := { S₃ with
    R := Function.update (Function.update (Function.update S₃.R (M.dreg D W) [])
      (M.dreg D K) Kc) (M.dreg D Y) (binSyms k' y') } with hS₅
  -- `Y := y' mod 2 ^ r`
  obtain ⟨v₆, hu₆, e₆⟩ := btrunc_exec Empty.elim (a := M.dreg D Y) (wR := M.dreg D wR)
    (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂) (by simpa using hnd [Y, wR, t₁, t₂] (by regs_nodup))
    (r := r) (e := k' - r) (X := y') v₅ S₅
    (by rw [show r + (k' - r) = k' by omega]; simp [hS₅])
    (by simp [hS₅, hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₅, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₅, hS₃, hS₂, hS₁, *, Ne.symm])
  rw [← binSyms_mod r y'] at e₆
  set S₆ : Stacks (M.T + D) M.A :=
    { S₅ with R := Function.update S₅.R (M.dreg D Y) (binSyms r (y' % 2 ^ r)) } with hS₆
  -- clear `K`
  obtain ⟨v₇, hu₇, -, e₇⟩ := bclear_exec Empty.elim (M.dreg D K) v₆ S₆
  rw [show (S₆.R (M.dreg D K)).length = k' by simp [hS₆, hS₅, *, Ne.symm]] at e₇
  simp only [henselPot, if_neg (show r ≠ 0 by omega)] at hn₅
  refine ⟨v₇, y' % 2 ^ r, _, ?_, Nat.mod_lt _ (by positivity), dvd_low (by omega) hdvd', ?_,
    Exec.cast (Exec.seq (exec_hostCode e₁ gi go) (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄
      (Exec.seq e₅ (Exec.seq (exec_hostCode e₆ gi go) (exec_hostCode e₇ gi go))))))) rfl ?_⟩
  · rw [hu₇, hu₆, hu₅, hu₁]
  · omega
  · clear e₁ e₂ e₃ e₄ e₅ e₆ e₇
    show dmk v₇ _ gi go = dmk v₇ _ gi go
    congr 1
    simp only [hS₆, hS₅, hS₃, hS₂, hS₁]
    clear hS₆ hS₅ hS₃ hS₂ hS₁ hn₅ hnd
    congr 1
    funext j
    by_cases hjY : j = M.dreg D Y
    · subst hjY; simp [*, Ne.symm]
    by_cases hjK : j = M.dreg D K
    · subst hjK; simp [*, Ne.symm]
    by_cases hjW : j = M.dreg D W
    · subst hjW; simp [*, Ne.symm]
    simp [*]

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
