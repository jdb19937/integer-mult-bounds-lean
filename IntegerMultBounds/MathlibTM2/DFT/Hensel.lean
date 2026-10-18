module

public import IntegerMultBounds.MathlibTM2.DFT.Redc
public import IntegerMultBounds.MathlibTM2.DFT.HenselHost
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Montgomery constant by Hensel lifting

`-p⁻¹` modulo `2 ^ r` (`2 ^ r ∣ p p' + 1`) is lifted from `y = 1` modulo `2` by rounds
`y ↦ (2 y + p y²) mod 2 ^ (2k)` from `k` to `2 k` bits (`hensel_round_dvd`).

`M.henselRound D B W K K2 pW P2 Y Z Ur Yn t₁ … t₅` is one round on the DFT registers, for
`pW = binSyms (r + r) p` and `k = |K| ≤ r`: `henselA` (`W` loses `k` symbols, `K2 := K ++ K`,
`P2 := p mod 2 ^ (2k)`), `mulCall` for `z₀ = P2 · Y`, `btrunc` to `z = z₀ mod 2 ^ (2k)`,
`mulCall` for `z · Y`, and `henselC`. `henselRound_exec`: `Y` ends with
`binSyms (k + k) (hensel value)`, `K` with `2 k` symbols, `W` with `k` symbols fewer, in at most
`400 k + 250 + m₁ + m₂` steps, `m₁`, `m₂` bounded by the multiplier's time on the two products.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

namespace IntegerMultBounds.MathlibTM2.DFT

/-- The value after one Hensel round from `k` bits. -/
def henselNext (p k y : ℕ) : ℕ :=
  (p % 2 ^ (k + k) * y % 2 ^ (k + k) * y % 2 ^ (k + k) + 2 * y) % 2 ^ (k + k)

/-- A Hensel round doubles the precision of `-p⁻¹`. -/
theorem hensel_round_dvd (p k y : ℕ) (h : 2 ^ k ∣ p * y + 1) :
    2 ^ (k + k) ∣ p * henselNext p k y + 1 := by
  have hsq : 2 ^ (k + k) ∣ (p * y + 1) ^ 2 := by
    rw [show 2 ^ (k + k) = (2 ^ k) ^ 2 by ring]
    exact pow_dvd_pow_of_dvd h 2
  rw [← ZMod.natCast_eq_zero_iff] at hsq ⊢
  simp only [henselNext, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_mod,
    Nat.cast_one, Nat.cast_ofNat] at hsq ⊢
  linear_combination hsq

theorem henselNext_lt (p k y : ℕ) : henselNext p k y < 2 ^ (k + k) :=
  Nat.mod_lt _ (by positivity)

/-- The low `r` bits of a lift to `k ≥ r` bits. -/
theorem dvd_low {p r k y : ℕ} (hrk : r ≤ k) (h : 2 ^ k ∣ p * y + 1) :
    2 ^ r ∣ p * (y % 2 ^ r) + 1 := by
  have h' := (pow_dvd_pow 2 hrk).trans h
  rw [← ZMod.natCast_eq_zero_iff] at h' ⊢
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_one] at h' ⊢
  exact h'

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (D : ℕ) (B : Type)

/-- One Hensel round on the DFT registers. -/
def henselRound (W K K2 pW P2 Y Z Ur Yn t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (hostCode (henselA (M.dreg D W) (M.dreg D K) (M.dreg D K2) (M.dreg D pW) (M.dreg D P2)
      (M.dreg D t₁) (M.dreg D t₂)))
    (.seq (M.mulCall D B (M.dreg D P2) (M.dreg D Y) (M.dreg D Z) (M.dreg D t₁) (M.dreg D t₂)
        (M.dreg D t₃) (M.dreg D t₄) (M.dreg D t₅))
      (.seq (hostCode (btrunc (M.dreg D Z) (M.dreg D K2) (M.dreg D t₁) (M.dreg D t₂)))
        (.seq (M.mulCall D B (M.dreg D Z) (M.dreg D Y) (M.dreg D Ur) (M.dreg D t₁)
            (M.dreg D t₂) (M.dreg D t₃) (M.dreg D t₄) (M.dreg D t₅))
          (hostCode (henselC (M.dreg D Y) (M.dreg D K) (M.dreg D K2) (M.dreg D P2)
            (M.dreg D Z) (M.dreg D Ur) (M.dreg D Yn) (M.dreg D t₃) (M.dreg D t₁)
            (M.dreg D t₂))))))

/-- `henselRound`: `Y := binSyms (k + k) (henselNext p k y)`, `K := K ++ K`, `W := W.drop k`. -/
theorem henselRound_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    {W K K2 pW P2 Y Z Ur Yn t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [W, K, K2, pW, P2, Y, Z, Ur, Yn, t₁, t₂, t₃, t₄, t₅].Nodup)
    {r p k y : ℕ} (hk : 1 ≤ k) (hkr : k ≤ r) (hy : y < 2 ^ k)
    (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ j, S.L j = [])
    (hR : ∀ i, S.R (M.emb D i) = []) (hK : (S.R (M.dreg D K)).length = k)
    (hpW : S.R (M.dreg D pW) = binSyms (r + r) p) (hY : S.R (M.dreg D Y) = binSyms k y)
    (hK2 : S.R (M.dreg D K2) = []) (hP2 : S.R (M.dreg D P2) = []) (hZ : S.R (M.dreg D Z) = [])
    (hU : S.R (M.dreg D Ur) = []) (hYn : S.R (M.dreg D Yn) = [])
    (h₁ : S.R (M.dreg D t₁) = []) (h₂ : S.R (M.dreg D t₂) = []) (h₃ : S.R (M.dreg D t₃) = [])
    (h₄ : S.R (M.dreg D t₄) = []) (h₅ : S.R (M.dreg D t₅) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ m₁ m₂ n, v'.user.2 = v.user.2 ∧
      m₁ + 2 ≤ M.time (Nat.size (p % 2 ^ (k + k)) + Nat.size y) ∧
      m₂ + 2 ≤ M.time (Nat.size (p % 2 ^ (k + k) * y % 2 ^ (k + k)) + Nat.size y) ∧
      n ≤ 400 * k + 250 + m₁ + m₂ ∧
      Exec (M.tab D B main) (M.henselRound D B W K K2 pW P2 Y Z Ur Yn t₁ t₂ t₃ t₄ t₅)
        (dmk v S gi go) n
        (dmk v' { S with
          R := Function.update (Function.update (Function.update S.R (M.dreg D W)
            ((S.R (M.dreg D W)).drop k)) (M.dreg D K) (S.R (M.dreg D K) ++ S.R (M.dreg D K)))
            (M.dreg D Y) (binSyms (k + k) (henselNext p k y)) } gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  have hnd : ∀ l : List (Fin D), l.Nodup → (l.map (M.dreg D)).Nodup := fun _ h => M.nodup_dreg D h
  have hM : (0 : ℕ) < 2 ^ (k + k) := by positivity
  set p₂ := p % 2 ^ (k + k) with hp₂
  have hp₂lt : p₂ < 2 ^ (k + k) := Nat.mod_lt _ hM
  -- `henselA`
  obtain ⟨v₁, hu₁, e₁⟩ := henselA_exec Empty.elim (W := M.dreg D W) (K := M.dreg D K)
    (K2 := M.dreg D K2) (pW := M.dreg D pW) (P2 := M.dreg D P2) (t₁ := M.dreg D t₁)
    (t₂ := M.dreg D t₂) (by simpa using hnd [W, K, K2, pW, P2, t₁, t₂] (by regs_nodup))
    (k := k) (e := r + r - (k + k)) (p := p) v S hK
    (by rw [show k + k + (r + r - (k + k)) = r + r by omega]; exact hpW) hK2 hP2 h₁ h₂
  rw [← binSyms_mod (k + k) p, ← hp₂] at e₁
  set KK := S.R (M.dreg D K) ++ S.R (M.dreg D K) with hKK
  set S₁ : Stacks (M.T + D) M.A := { S with
    R := Function.update (Function.update (Function.update S.R (M.dreg D W)
      ((S.R (M.dreg D W)).drop k)) (M.dreg D K2) KK) (M.dreg D P2) (binSyms (k + k) p₂) }
    with hS₁
  have hKKl : KK.length = k + k := by simp [hKK, hK]
  -- `Z := p₂ y`
  obtain ⟨v₂, m₁, hu₂, hm₁, e₂⟩ := M.mulCall_exec D B main (a := M.dreg D P2)
    (b := M.dreg D Y) (c := M.dreg D Z) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (t₃ := M.dreg D t₃) (t₄ := M.dreg D t₄) (t₅ := M.dreg D t₅)
    (by simpa using hnd [Z, P2, Y, t₁, t₂, t₃, t₄, t₅] (by regs_nodup)) hp₂lt hy v₁ S₁
    (by simp [hS₁, hinp]) (by simp [hS₁, hout]) (by simp [hS₁, hL]) (by intro i; simp [hS₁, hR])
    (by simp [hS₁]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) gi go
  set S₂ : Stacks (M.T + D) M.A :=
    { S₁ with R := Function.update S₁.R (M.dreg D Z) (binSyms (k + k + k) (p₂ * y)) } with hS₂
  -- `Z := p₂ y mod 2 ^ (2k)`
  obtain ⟨v₃, hu₃, e₃⟩ := btrunc_exec Empty.elim (a := M.dreg D Z) (wR := M.dreg D K2)
    (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (by simpa using hnd [Z, K2, t₁, t₂] (by regs_nodup)) (r := k + k) (e := k) (X := p₂ * y)
    v₂ S₂ (by simp [hS₂]) (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
    (by simp [hS₂, hS₁, *, Ne.symm])
  rw [← binSyms_mod (k + k) (p₂ * y)] at e₃
  set z := p₂ * y % 2 ^ (k + k) with hz
  have hzlt : z < 2 ^ (k + k) := Nat.mod_lt _ hM
  set S₃ : Stacks (M.T + D) M.A :=
    { S₂ with R := Function.update S₂.R (M.dreg D Z) (binSyms (k + k) z) } with hS₃
  -- `Ur := z y`
  obtain ⟨v₄, m₂, hu₄, hm₂, e₄⟩ := M.mulCall_exec D B main (a := M.dreg D Z)
    (b := M.dreg D Y) (c := M.dreg D Ur) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (t₃ := M.dreg D t₃) (t₄ := M.dreg D t₄) (t₅ := M.dreg D t₅)
    (by simpa using hnd [Ur, Z, Y, t₁, t₂, t₃, t₄, t₅] (by regs_nodup)) hzlt hy v₃ S₃
    (by simp [hS₃, hS₂, hS₁, hinp]) (by simp [hS₃, hS₂, hS₁, hout])
    (by simp [hS₃, hS₂, hS₁, hL]) (by intro i; simp [hS₃, hS₂, hS₁, hR]) (by simp [hS₃])
    (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₃, hS₂, hS₁, *, Ne.symm]) gi go
  set S₄ : Stacks (M.T + D) M.A :=
    { S₃ with R := Function.update S₃.R (M.dreg D Ur) (binSyms (k + k + k) (z * y)) } with hS₄
  -- `henselC`
  obtain ⟨v₅, n₅, hu₅, hn₅, e₅⟩ := henselC_exec Empty.elim (Y := M.dreg D Y) (K := M.dreg D K)
    (K2 := M.dreg D K2) (P2 := M.dreg D P2) (Z := M.dreg D Z) (Ur := M.dreg D Ur)
    (Yn := M.dreg D Yn) (cnt := M.dreg D t₃) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (by simpa using hnd [Y, K, K2, P2, Z, Ur, Yn, t₃, t₁, t₂] (by regs_nodup)) (k := k)
    (X := z * y) (y := y) (z := z) (q := p₂) hk hy v₄ S₄ (by simp [hS₄])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₄, hS₃, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm]) (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm])
  have hS₄K2 : S₄.R (M.dreg D K2) = KK := by simp [hS₄, hS₃, hS₂, hS₁, *, Ne.symm]
  rw [hS₄K2] at e₅
  have hsz₁ : Nat.size (p₂ * y) ≤ k + k + k :=
    Nat.size_le.2 (by rw [pow_add]; exact Nat.mul_lt_mul'' hp₂lt hy)
  have hsz₂ : Nat.size (z * y) ≤ k + k + k :=
    Nat.size_le.2 (by rw [pow_add]; exact Nat.mul_lt_mul'' hzlt hy)
  have hval : (z * y % 2 ^ (k + k) + 2 * y) % 2 ^ (k + k) = henselNext p k y := by
    simp only [henselNext, hz, hp₂]
  rw [hval] at e₅
  refine ⟨v₅, m₁, m₂, _, ?_, hm₁, hm₂, ?_, Exec.cast (Exec.seq (exec_hostCode e₁ gi go)
    (Exec.seq e₂ (Exec.seq (exec_hostCode e₃ gi go) (Exec.seq e₄ (exec_hostCode e₅ gi go)))))
    rfl ?_⟩
  · rw [hu₅, hu₄, hu₃, hu₂, hu₁]
  · omega
  · clear e₁ e₂ e₃ e₄ e₅
    show dmk v₅ _ gi go = dmk v₅ _ gi go
    congr 1
    simp only [hS₄, hS₃, hS₂, hS₁]
    clear hS₄ hS₃ hS₂ hS₁ hS₄K2 hval hm₁ hm₂ hn₅ hsz₁ hsz₂ hnd
    congr 1
    funext j
    by_cases hj : j = M.dreg D K2
    · subst hj; simp [*, Ne.symm]
    by_cases hj' : j = M.dreg D K
    · subst hj'; simp [*, Ne.symm]
    by_cases hjY : j = M.dreg D Y
    · subst hjY; simp [*, Ne.symm]
    by_cases hjU : j = M.dreg D Ur
    · subst hjU; simp [*, Ne.symm]
    by_cases hjZ : j = M.dreg D Z
    · subst hjZ; simp [*, Ne.symm]
    by_cases hjP : j = M.dreg D P2
    · subst hjP; simp [*, Ne.symm]
    simp [*]

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
