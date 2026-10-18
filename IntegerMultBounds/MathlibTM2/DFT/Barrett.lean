module

public import IntegerMultBounds.MathlibTM2.DFT.NewtonLoop
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Barrett reduction on the host

For `μ = ⌊2 ^ s / p⌋`, `s = k + w`, and `x < 2 ^ s`, the quotient `q = ⌊x μ / 2 ^ s⌋` has
`q p ≤ x < q p + 2 p` (`barrett2_le`, `barrett2_lt`), so `x mod p` is `x - q p` or
`x - q p - p` (`barrett_tail_val`).

* `barrettTail X Pw Q1 Q2 P3 O t₁ t₂ t₃` (`barrettTail_exec`): from `X = binSyms L x` and
  `Q2 = binSyms (L + e) z` with `z = q p`, `Q1 := x - z` (`btrunc`, `bsub`), `P3 := p` in `L`
  bits (`bcopy`, `bwiden`), one conditional subtraction into `O` (`blt`, then `bcopy` or
  `bsub`), and `O` cut to `w` bits; `Q1`, `Q2` and `P3` end empty.
* `M.barrettProg D B X Aa Pw wK Q1 Q2 P3 O t₁ … t₅` (`barrett_exec`): `mulCall` for `x μ` into
  `Q1`, `usub` by `wK` and by `Pw` (`q`), `mulCall` for `q p` into `Q2`, `barrettTail`:
  `O := binSyms w (x mod p)`, in `150 L + 120 k + 600` steps plus the two products.
* `M.modMulProg` (`modMul_exec`): `mulCall` for `x y`, `barrettProg`, the product cleared:
  `O := binSyms w (x y mod p)` for `x, y < p` and `w ≤ k`.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

/-- One conditional subtraction after `q p ≤ x < q p + 2 p` gives `x mod p`. -/
theorem barrett_tail_val {p x z : ℕ} (hpz : p ∣ z) (hz : z ≤ x) (hx : x < z + 2 * p) :
    (if x - z < p then x - z else x - z - p) = x % p := by
  obtain ⟨c, rfl⟩ := hpz
  have hmod : x % p = (x - p * c) % p := by
    conv_lhs => rw [← Nat.sub_add_cancel hz]
    rw [Nat.add_mul_mod_self_left]
  rw [hmod]
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The reciprocal is below `2 ^ (k + 1)`. -/
theorem recip_le {k w p : ℕ} (hw : 1 ≤ w) (hp1 : 2 ^ (w - 1) ≤ p) :
    2 ^ (k + w) / p ≤ 2 ^ (k + 1) := by
  calc 2 ^ (k + w) / p ≤ 2 ^ (k + w) / 2 ^ (w - 1) := Nat.div_le_div_left hp1 (by positivity)
    _ = 2 ^ (k + 1) := by rw [Nat.pow_div (by omega) (by norm_num)]; congr 1; omega

section Tail

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- `O := (x - z) mod p` in `w` bits, for `z = q p`. -/
def barrettTail (X Pw Q1 Q2 P3 O t₁ t₂ t₃ : Fin T) : Pr P T Q A U :=
  .seq (btrunc Q2 X t₁ t₂) (.seq (bclear Q1) (.seq (bsub X Q2 Q1 t₁ t₂ t₃ O) (.seq (bclear Q2)
    (.seq (bcopy Pw P3 t₁ t₂) (.seq (bwiden P3 X O t₁ t₂) (.seq (blt Q1 P3 t₁ t₂ t₃ O)
      (.seq (.cond (slotTrue O) (bcopy Q1 O t₁ t₂) (bsub Q1 P3 O t₁ t₂ t₃ O))
        (.seq (btrunc O Pw t₁ t₂) (.seq (bclear Q1) (bclear P3))))))))))

theorem barrettTail_exec {X Pw Q1 Q2 P3 O t₁ t₂ t₃ : Fin T}
    (hreg : [X, Pw, Q1, Q2, P3, O, t₁, t₂, t₃].Nodup) {L e w p x z : ℕ} (hwL : w ≤ L)
    (hp0 : 0 < p) (hp : p < 2 ^ w) (hx : x < 2 ^ L) (hpz : p ∣ z) (hz : z ≤ x)
    (hxz : x < z + 2 * p) (v : HS T Q A U) (S : Stacks T A) (hX : S.R X = binSyms L x)
    (hPw : S.R Pw = binSyms w p) (hQ2 : S.R Q2 = binSyms (L + e) z) (hP3 : S.R P3 = [])
    (hO : S.R O = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) (h₃ : S.R t₃ = []) :
    ∃ v' : HS T Q A U, ∃ n, v'.user = v.user ∧
      n ≤ 2 * (S.R Q1).length + 60 * L + 2 * e + 12 * w + 100 ∧
      Exec body (barrettTail X Pw Q1 Q2 P3 O t₁ t₂ t₃) (mk v S) n
        (mk v' { S with
          R := Function.update (Function.update (Function.update S.R Q1 []) Q2 []) O
            (binSyms w (x % p)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hzL : z < 2 ^ L := lt_of_le_of_lt hz hx
  have hpL : p < 2 ^ L := lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) hwL)
  have hdL : x - z < 2 ^ L := lt_of_le_of_lt (Nat.sub_le _ _) hx
  -- `Q2 := z` in `L` bits
  obtain ⟨v₁, hu₁, e₁⟩ := btrunc_exec body (a := Q2) (wR := X) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) (r := L) (e := e) (X := z) v S hQ2 (by rw [hX, length_binSyms]) h₁ h₂
  set S₁ : Stacks T A := { S with R := Function.update S.R Q2 (binSyms L z) } with hS₁
  obtain ⟨v₂, hu₂, -, e₂⟩ := bclear_exec body Q1 v₁ S₁
  rw [show (S₁.R Q1).length = (S.R Q1).length by simp [hS₁, ‹Q1 ≠ Q2›]] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R Q1 [] } with hS₂
  -- `Q1 := x - z`
  obtain ⟨v₃, hu₃, -, -, e₃⟩ := bsub_exec body (a := X) (b := Q2) (c := Q1) (tx := t₁) (ty := t₂)
    (tz := t₃) (cy := O) (by regs_nodup) ‹X ≠ O›.symm ‹Q2 ≠ O›.symm hx hzL v₂ S₂
    (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
    (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
    (by simp [hS₂, hS₁, *, Ne.symm])
  have hval : (x + 2 ^ L - z) % 2 ^ L = x - z := by
    rw [Nat.sub_add_comm hz, Nat.add_mod_right, Nat.mod_eq_of_lt hdL]
  rw [hval, show S₂.R Q1 = [] by simp [hS₂], List.append_nil] at e₃
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R Q1 (binSyms L (x - z)) } with hS₃
  obtain ⟨v₄, hu₄, -, e₄⟩ := bclear_exec body Q2 v₃ S₃
  rw [show (S₃.R Q2).length = L by simp [hS₃, hS₂, hS₁, *, Ne.symm]] at e₄
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R Q2 [] } with hS₄
  -- `P3 := p` in `L` bits
  obtain ⟨v₅, hu₅, e₅⟩ := bcopy_exec body (a := Pw) (c := P3) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₄ S₄ (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
  rw [show S₄.R Pw = binSyms w p by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm],
    show S₄.R P3 = [] by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm], List.append_nil,
    length_binSyms] at e₅
  set S₅ : Stacks T A := { S₄ with R := Function.update S₄.R P3 (binSyms w p) } with hS₅
  obtain ⟨v₆, hu₆, e₆⟩ := bwiden_exec body (a := P3) (wR := X) (cnt := O) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) hwL hp v₅ S₅ (by simp [hS₅])
    (by simp [hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
  set S₆ : Stacks T A := { S₅ with R := Function.update S₅.R P3 (binSyms L p) } with hS₆
  have hS₆Q : S₆.R Q1 = binSyms L (x - z) := by simp [hS₆, hS₅, hS₄, hS₃, *, Ne.symm]
  have hS₆P : S₆.R P3 = binSyms L p := by simp [hS₆]
  have hS₆O : S₆.R O = [] := by simp [hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm]
  have hS₆t₁ : S₆.R t₁ = [] := by simp [hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm]
  have hS₆t₂ : S₆.R t₂ = [] := by simp [hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm]
  have hS₆t₃ : S₆.R t₃ = [] := by simp [hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm]
  -- compare with `p`
  obtain ⟨v₇, hu₇, hsc₇, -, e₇⟩ := blt_exec body (a := Q1) (b := P3) (tx := t₁) (ty := t₂)
    (tz := t₃) (cy := O) (by regs_nodup) ‹Q1 ≠ O›.symm ‹P3 ≠ O›.symm hdL hpL v₆ S₆ hS₆Q hS₆P
    hS₆t₁ hS₆t₂ hS₆t₃
  -- the conditional subtraction
  have e₈ : ∃ v₈ : HS T Q A U, ∃ n₈, v₈.user = v₇.user ∧ n₈ ≤ 8 * L + 9 ∧
      Exec body (.cond (slotTrue O) (bcopy Q1 O t₁ t₂) (bsub Q1 P3 O t₁ t₂ t₃ O)) (mk v₇ S₆)
        n₈ (mk v₈ { S₆ with R := Function.update S₆.R O (binSyms L (x % p)) }) := by
    rw [← barrett_tail_val hpz hz hxz]
    by_cases hlt : x - z < p
    · have hf : slotTrue O v₇ = true := by simp [slotTrue, hsc₇, hlt]
      obtain ⟨v₈, hu₈, e⟩ := bcopy_exec body (a := Q1) (c := O) (t₁ := t₁) (t₂ := t₂)
        (by regs_nodup) v₇ S₆ hS₆t₁ hS₆t₂
      rw [hS₆Q, hS₆O, List.append_nil, length_binSyms] at e
      refine ⟨v₈, _, hu₈, by omega, Exec.cond_true hf (e.cast rfl ?_)⟩
      simp [hlt]
    · have hf : slotTrue O v₇ = false := by
        simp [slotTrue, hsc₇, hlt, bitSymbol_true_ne_false.symm]
      obtain ⟨v₈, hu₈, -, -, e⟩ := bsub_exec body (a := Q1) (b := P3) (c := O) (tx := t₁)
        (ty := t₂) (tz := t₃) (cy := O) (by regs_nodup) ‹Q1 ≠ O›.symm ‹P3 ≠ O›.symm hdL hpL v₇
        S₆ hS₆Q hS₆P hS₆t₁ hS₆t₂ hS₆t₃
      rw [hS₆O, List.append_nil] at e
      have hval' : (x - z + 2 ^ L - p) % 2 ^ L = x - z - p := by
        rw [show x - z + 2 ^ L - p = (x - z - p) + 2 ^ L by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [hval'] at e
      refine ⟨v₈, _, hu₈, by omega, Exec.cond_false hf (e.cast rfl ?_)⟩
      simp [hlt]
  obtain ⟨v₈, n₈, hu₈, hn₈, e₈⟩ := e₈
  set S₈ : Stacks T A := { S₆ with R := Function.update S₆.R O (binSyms L (x % p)) } with hS₈
  -- `O` in `w` bits, clear `Q1` and `P3`
  obtain ⟨v₉, hu₉, e₉⟩ := btrunc_exec body (a := O) (wR := Pw) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) (r := w) (e := L - w) (X := x % p) v₈ S₈
    (by rw [show w + (L - w) = L by omega]; simp [hS₈])
    (by simp [hS₈, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₈, hS₆t₁, ‹O ≠ t₁›.symm]) (by simp [hS₈, hS₆t₂, ‹O ≠ t₂›.symm])
  set S₉ : Stacks T A := { S₈ with R := Function.update S₈.R O (binSyms w (x % p)) } with hS₉
  obtain ⟨v₁₀, hu₁₀, -, e₁₀⟩ := bclear_exec body Q1 v₉ S₉
  rw [show (S₉.R Q1).length = L by simp [hS₉, hS₈, hS₆Q, ‹Q1 ≠ O›]] at e₁₀
  set S₁₀ : Stacks T A := { S₉ with R := Function.update S₉.R Q1 [] } with hS₁₀
  obtain ⟨v₁₁, hu₁₁, -, e₁₁⟩ := bclear_exec body P3 v₁₀ S₁₀
  rw [show (S₁₀.R P3).length = L by simp [hS₁₀, hS₉, hS₈, hS₆P, ‹Q1 ≠ P3›.symm, ‹P3 ≠ O›]]
    at e₁₁
  refine ⟨v₁₁, _, by rw [hu₁₁, hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ (Exec.seq e₈ (Exec.seq e₉ (Exec.seq e₁₀ e₁₁)))))))))) rfl ?_⟩
  · omega
  · clear e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁
    simp only [hS₁₀, hS₉, hS₈, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁]
    clear hS₁₀ hS₉ hS₈ hS₆ hS₅ hS₄ hS₃ hS₂ hS₁ hS₆Q hS₆P hS₆O hS₆t₁ hS₆t₂ hS₆t₃ hval
    congr 2
    funext j
    by_cases hj1 : j = Q1
    · subst hj1; simp [*, Ne.symm]
    by_cases hj2 : j = Q2
    · subst hj2; simp [*, Ne.symm]
    by_cases hj3 : j = P3
    · subst hj3; simp [*, Ne.symm]
    by_cases hj4 : j = O
    · subst hj4; simp [*, Ne.symm]
    simp [*]

end Tail

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (D : ℕ) (B : Type)

/-- `O := x mod p` by Barrett's method with `μ = ⌊2 ^ (k + w) / p⌋` in `A`. -/
def barrettProg (X Aa Pw wK Q1 Q2 P3 O t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (M.mulCall D B (M.dreg D X) (M.dreg D Aa) (M.dreg D Q1) (M.dreg D t₁) (M.dreg D t₂)
      (M.dreg D t₃) (M.dreg D t₄) (M.dreg D t₅))
    (.seq (hostCode (.seq (usub (M.dreg D wK) (M.dreg D Q1) (M.dreg D t₁))
        (usub (M.dreg D Pw) (M.dreg D Q1) (M.dreg D t₁))))
      (.seq (M.mulCall D B (M.dreg D Q1) (M.dreg D Pw) (M.dreg D Q2) (M.dreg D t₁)
          (M.dreg D t₂) (M.dreg D t₃) (M.dreg D t₄) (M.dreg D t₅))
        (hostCode (barrettTail (M.dreg D X) (M.dreg D Pw) (M.dreg D Q1) (M.dreg D Q2)
          (M.dreg D P3) (M.dreg D O) (M.dreg D t₁) (M.dreg D t₂) (M.dreg D t₃)))))

/-- `barrettProg`: `O := binSyms w (x mod p)` for `x < 2 ^ (k + w)`. -/
theorem barrett_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    {X Aa Pw wK Q1 Q2 P3 O t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [X, Aa, Pw, wK, Q1, Q2, P3, O, t₁, t₂, t₃, t₄, t₅].Nodup) {L k w p x : ℕ}
    (hw : 1 ≤ w) (hwL : w ≤ L) (hwk : w ≤ k) (hp1 : 2 ^ (w - 1) ≤ p) (hp : p < 2 ^ w)
    (hx : x < 2 ^ L) (hxs : x < 2 ^ (k + w)) (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ j, S.L j = [])
    (hR : ∀ i, S.R (M.emb D i) = []) (hX : S.R (M.dreg D X) = binSyms L x)
    (hA : S.R (M.dreg D Aa) = binSyms (k + k + 4) (2 ^ (k + w) / p))
    (hPw : S.R (M.dreg D Pw) = binSyms w p) (hK : (S.R (M.dreg D wK)).length = k)
    (hQ1 : S.R (M.dreg D Q1) = []) (hQ2 : S.R (M.dreg D Q2) = []) (hP3 : S.R (M.dreg D P3) = [])
    (hO : S.R (M.dreg D O) = []) (h₁ : S.R (M.dreg D t₁) = []) (h₂ : S.R (M.dreg D t₂) = [])
    (h₃ : S.R (M.dreg D t₃) = []) (h₄ : S.R (M.dreg D t₄) = []) (h₅ : S.R (M.dreg D t₅) = [])
    (gi go : List Γ') :
    ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ m₁ m₂ n, v'.user.2 = v.user.2 ∧
      m₁ + 2 ≤ M.time (Nat.size x + Nat.size (2 ^ (k + w) / p)) ∧
      m₂ + 2 ≤ M.time (Nat.size (x * (2 ^ (k + w) / p) / 2 ^ (k + w)) + Nat.size p) ∧
      n ≤ 150 * L + 120 * k + 600 + m₁ + m₂ ∧
      Exec (M.tab D B main) (M.barrettProg D B X Aa Pw wK Q1 Q2 P3 O t₁ t₂ t₃ t₄ t₅)
        (dmk v S gi go) n
        (dmk v' { S with R := Function.update S.R (M.dreg D O) (binSyms w (x % p)) } gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  have hnd : ∀ l : List (Fin D), l.Nodup → (l.map (M.dreg D)).Nodup := fun _ h => M.nodup_dreg D h
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp1
  set μ := 2 ^ (k + w) / p with hμ
  have hμlt : μ < 2 ^ (k + k + 4) :=
    lt_of_le_of_lt (recip_le hw hp1) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  set q := x * μ / 2 ^ (k + w) with hq
  have hqp : q * p ≤ x := barrett2_le p (k + w) x
  have hxq : x < q * p + 2 * p := barrett2_lt p (k + w) x hp0 hxs
  have hqx : q ≤ x := le_trans (Nat.le_mul_of_pos_right q hp0) hqp
  have hLw : L ≤ L + k + 4 - w := by omega
  have hqL : q < 2 ^ (L + k + 4 - w) :=
    lt_of_le_of_lt hqx (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hLw))
  have hnd₂ := hnd [Q1, wK, t₁] (by regs_nodup)
  have hnd₃ := hnd [Q1, Pw, t₁] (by regs_nodup)
  -- `Q1 := x μ`
  obtain ⟨v₁, m₁, hu₁, hm₁, e₁⟩ := M.mulCall_exec D B main (a := M.dreg D X) (b := M.dreg D Aa)
    (c := M.dreg D Q1) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂) (t₃ := M.dreg D t₃)
    (t₄ := M.dreg D t₄) (t₅ := M.dreg D t₅)
    (by simpa only [List.map_cons, List.map_nil] using
      hnd [Q1, X, Aa, t₁, t₂, t₃, t₄, t₅] (by regs_nodup)) hx hμlt v S hinp hout hL hR hX hA hQ1
    h₁ h₂ h₃ h₄ h₅ gi go
  set S₁ : Stacks (M.T + D) M.A := { S with
    R := Function.update S.R (M.dreg D Q1) (binSyms (L + (k + k + 4)) (x * μ)) } with hS₁
  -- `Q1 := q`
  obtain ⟨v₂, hu₂, e₂⟩ := bhigh_exec Empty.elim (a := M.dreg D Q1) (wR := M.dreg D wK)
    (t := M.dreg D t₁) (by simpa only [List.map_cons, List.map_nil] using hnd₂) (r := k) (e := L + k + 4) (X := x * μ) v₁ S₁
    (by rw [show k + (L + k + 4) = L + (k + k + 4) by ring]; simp [hS₁])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
  set S₂ : Stacks (M.T + D) M.A := { S₁ with
    R := Function.update S₁.R (M.dreg D Q1) (binSyms (L + k + 4) (x * μ / 2 ^ k)) } with hS₂
  obtain ⟨v₃, hu₃, e₃⟩ := bhigh_exec Empty.elim (a := M.dreg D Q1) (wR := M.dreg D Pw)
    (t := M.dreg D t₁) (by simpa only [List.map_cons, List.map_nil] using hnd₃) (r := w) (e := L + k + 4 - w) (X := x * μ / 2 ^ k) v₂ S₂
    (by rw [show w + (L + k + 4 - w) = L + k + 4 by omega]; simp [hS₂])
    (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
  rw [Nat.div_div_eq_div_mul, ← pow_add, ← hq] at e₃
  set S₃ : Stacks (M.T + D) M.A := { S₂ with
    R := Function.update S₂.R (M.dreg D Q1) (binSyms (L + k + 4 - w) q) } with hS₃
  -- `Q2 := q p`
  obtain ⟨v₄, m₂, hu₄, hm₂, e₄⟩ := M.mulCall_exec D B main (a := M.dreg D Q1)
    (b := M.dreg D Pw) (c := M.dreg D Q2) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (t₃ := M.dreg D t₃) (t₄ := M.dreg D t₄) (t₅ := M.dreg D t₅)
    (by simpa only [List.map_cons, List.map_nil] using
      hnd [Q2, Q1, Pw, t₁, t₂, t₃, t₄, t₅] (by regs_nodup)) hqL hp v₃ S₃
    (by simp [hS₃, hS₂, hS₁, hinp]) (by simp [hS₃, hS₂, hS₁, hout]) (by simp [hS₃, hS₂, hS₁, hL])
    (by intro i; simp [hS₃, hS₂, hS₁, hR]) (by simp [hS₃]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) gi go
  set S₄ : Stacks (M.T + D) M.A := { S₃ with
    R := Function.update S₃.R (M.dreg D Q2) (binSyms (L + k + 4 - w + w) (q * p)) } with hS₄
  -- the tail
  obtain ⟨v₅, n₅, hu₅, hn₅, e₅⟩ := barrettTail_exec Empty.elim (X := M.dreg D X)
    (Pw := M.dreg D Pw) (Q1 := M.dreg D Q1) (Q2 := M.dreg D Q2) (P3 := M.dreg D P3)
    (O := M.dreg D O) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂) (t₃ := M.dreg D t₃)
    (by simpa only [List.map_cons, List.map_nil] using
      hnd [X, Pw, Q1, Q2, P3, O, t₁, t₂, t₃] (by regs_nodup)) (L := L) (e := k + 4) hwL hp0 hp hx
    (Dvd.intro_left q rfl) hqp hxq v₄ S₄ (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by rw [show L + (k + 4) = L + k + 4 - w + w by omega]; simp [hS₄])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
  rw [show (S₄.R (M.dreg D Q1)).length = L + k + 4 - w by
    simp [hS₄, hS₃, *, Ne.symm]] at hn₅
  refine ⟨v₅, m₁, m₂, _, ?_, hm₁, hm₂, ?_, Exec.cast (Exec.seq e₁ (Exec.seq
    (exec_hostCode (Exec.seq e₂ e₃) gi go) (Exec.seq e₄ (exec_hostCode e₅ gi go)))) rfl ?_⟩
  · rw [hu₅, hu₄, hu₃, hu₂, hu₁]
  · have := Nat.size_le.2 (show x * μ < 2 ^ (L + (k + k + 4)) by
      rw [pow_add]; exact Nat.mul_lt_mul'' hx hμlt)
    have := Nat.size_le.2 (show q * p < 2 ^ (L + k + 4 - w + w) by
      rw [pow_add]; exact Nat.mul_lt_mul'' hqL hp)
    omega
  · clear e₁ e₂ e₃ e₄ e₅
    show dmk v₅ _ gi go = dmk v₅ _ gi go
    congr 1
    simp only [hS₄, hS₃, hS₂, hS₁]
    clear hS₄ hS₃ hS₂ hS₁ hnd hnd₂ hnd₃ hn₅ hm₁ hm₂
    congr 1
    funext j
    by_cases hj1 : j = M.dreg D Q1
    · subst hj1; simp [*, Ne.symm]
    by_cases hj2 : j = M.dreg D Q2
    · subst hj2; simp [*, Ne.symm]
    by_cases hj3 : j = M.dreg D O
    · subst hj3; simp [*, Ne.symm]
    simp [*]

/-- `O := x y mod p` for `x`, `y` in `w` bits. -/
def modMulProg (Xa Yb Z Aa Pw wK Q1 Q2 P3 O t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (M.mulCall D B (M.dreg D Xa) (M.dreg D Yb) (M.dreg D Z) (M.dreg D t₁) (M.dreg D t₂)
      (M.dreg D t₃) (M.dreg D t₄) (M.dreg D t₅))
    (.seq (M.barrettProg D B Z Aa Pw wK Q1 Q2 P3 O t₁ t₂ t₃ t₄ t₅)
      (hostCode (bclear (M.dreg D Z))))

/-- `modMulProg`: `O := binSyms w (x y mod p)` for `x, y < p`, in
`(520 + 9 h) k + 700 + 12 h` steps for `h = H (3k + 3)`. -/
theorem modMul_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    (H : ℕ → ℕ) (hH : Monotone H) (hT : ∀ n, M.time n ≤ (n + 1) * H n)
    {Xa Yb Z Aa Pw wK Q1 Q2 P3 O t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [Xa, Yb, Z, Aa, Pw, wK, Q1, Q2, P3, O, t₁, t₂, t₃, t₄, t₅].Nodup) {k w p x y : ℕ}
    (hw : 1 ≤ w) (hwk : w ≤ k) (hp1 : 2 ^ (w - 1) ≤ p) (hp : p < 2 ^ w) (hx : x < p)
    (hy : y < p) (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ j, S.L j = [])
    (hR : ∀ i, S.R (M.emb D i) = []) (hXa : S.R (M.dreg D Xa) = binSyms w x)
    (hYb : S.R (M.dreg D Yb) = binSyms w y)
    (hA : S.R (M.dreg D Aa) = binSyms (k + k + 4) (2 ^ (k + w) / p))
    (hPw : S.R (M.dreg D Pw) = binSyms w p) (hK : (S.R (M.dreg D wK)).length = k)
    (hZ : S.R (M.dreg D Z) = []) (hQ1 : S.R (M.dreg D Q1) = []) (hQ2 : S.R (M.dreg D Q2) = [])
    (hP3 : S.R (M.dreg D P3) = []) (hO : S.R (M.dreg D O) = []) (h₁ : S.R (M.dreg D t₁) = [])
    (h₂ : S.R (M.dreg D t₂) = []) (h₃ : S.R (M.dreg D t₃) = []) (h₄ : S.R (M.dreg D t₄) = [])
    (h₅ : S.R (M.dreg D t₅) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ n, v'.user.2 = v.user.2 ∧
      n ≤ (520 + 9 * H (3 * k + 3)) * k + 700 + 12 * H (3 * k + 3) ∧
      Exec (M.tab D B main) (M.modMulProg D B Xa Yb Z Aa Pw wK Q1 Q2 P3 O t₁ t₂ t₃ t₄ t₅)
        (dmk v S gi go) n
        (dmk v' { S with R := Function.update S.R (M.dreg D O) (binSyms w (x * y % p)) }
          gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  have hnd : ∀ l : List (Fin D), l.Nodup → (l.map (M.dreg D)).Nodup := fun _ h => M.nodup_dreg D h
  have hxw : x < 2 ^ w := hx.trans hp
  have hyw : y < 2 ^ w := hy.trans hp
  have hxy : x * y < 2 ^ (w + w) := by rw [pow_add]; exact Nat.mul_lt_mul'' hxw hyw
  have hxys : x * y < 2 ^ (k + w) :=
    lt_of_lt_of_le hxy (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- `Z := x y`
  obtain ⟨v₁, m₀, hu₁, hm₀, e₁⟩ := M.mulCall_exec D B main (a := M.dreg D Xa)
    (b := M.dreg D Yb) (c := M.dreg D Z) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (t₃ := M.dreg D t₃) (t₄ := M.dreg D t₄) (t₅ := M.dreg D t₅)
    (by simpa only [List.map_cons, List.map_nil] using
      hnd [Z, Xa, Yb, t₁, t₂, t₃, t₄, t₅] (by regs_nodup)) hxw hyw v S hinp hout hL hR hXa hYb
    hZ h₁ h₂ h₃ h₄ h₅ gi go
  set S₁ : Stacks (M.T + D) M.A := { S with
    R := Function.update S.R (M.dreg D Z) (binSyms (w + w) (x * y)) } with hS₁
  -- `O := x y mod p`
  obtain ⟨v₂, m₁, m₂, n₂, hu₂, hm₁, hm₂, hn₂, e₂⟩ := M.barrett_exec D B main (X := Z) (Aa := Aa)
    (Pw := Pw) (wK := wK) (Q1 := Q1) (Q2 := Q2) (P3 := P3) (O := O) (t₁ := t₁) (t₂ := t₂)
    (t₃ := t₃) (t₄ := t₄) (t₅ := t₅) (by regs_nodup) (L := w + w) (k := k) hw (by omega) hwk hp1
    hp hxy hxys v₁ S₁ (by simp [hS₁, hinp]) (by simp [hS₁, hout]) (by simp [hS₁, hL])
    (by intro i; simp [hS₁, hR]) (by simp [hS₁]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) gi go
  set S₂ : Stacks (M.T + D) M.A := { S₁ with
    R := Function.update S₁.R (M.dreg D O) (binSyms w (x * y % p)) } with hS₂
  -- clear `Z`
  obtain ⟨v₃, hu₃, -, e₃⟩ := bclear_exec Empty.elim (M.dreg D Z) v₂ S₂
  rw [show (S₂.R (M.dreg D Z)).length = w + w by simp [hS₂, hS₁, *, Ne.symm]] at e₃
  refine ⟨v₃, _, by rw [hu₃, hu₂, hu₁], ?_, Exec.cast (Exec.seq e₁ (Exec.seq e₂
    (exec_hostCode e₃ gi go))) rfl ?_⟩
  · -- the time
    set h := H (3 * k + 3) with hh
    have hTs : ∀ s, s ≤ 3 * k + 3 → M.time s ≤ 3 * (k * h) + 4 * h := fun s hs => by
      calc M.time s ≤ (s + 1) * H s := hT s
        _ ≤ (3 * k + 4) * h := Nat.mul_le_mul (by omega) (hH hs)
        _ = 3 * (k * h) + 4 * h := by ring
    have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp1
    have hμ : 2 ^ (k + w) / p < 2 ^ (k + 2) :=
      lt_of_le_of_lt (recip_le hw hp1) (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hq : x * y * (2 ^ (k + w) / p) / 2 ^ (k + w) < 2 ^ (w + w) :=
      lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_right _ hp0) (barrett2_le p (k + w) (x * y)))
        hxy
    have := Nat.size_le.2 hxw
    have := Nat.size_le.2 hyw
    have := Nat.size_le.2 hxy
    have := Nat.size_le.2 hμ
    have := Nat.size_le.2 hq
    have := Nat.size_le.2 hp
    have hm₀' := hm₀.trans (hTs _ (by omega))
    have hm₁' := hm₁.trans (hTs _ (by omega))
    have hm₂' := hm₂.trans (hTs _ (by omega))
    have hc : (520 + 9 * h) * k = 520 * k + 9 * (k * h) := by ring
    omega
  · clear e₁ e₂ e₃
    show dmk v₃ _ gi go = dmk v₃ _ gi go
    congr 1
    simp only [hS₂, hS₁]
    clear hS₂ hS₁ hnd hn₂ hm₀ hm₁ hm₂
    congr 1
    funext j
    by_cases hj1 : j = M.dreg D Z
    · subst hj1; simp [*, Ne.symm]
    by_cases hj2 : j = M.dreg D O
    · subst hj2; simp [*, Ne.symm]
    simp [*]

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
