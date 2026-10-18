module

public import IntegerMultBounds.MathlibTM2.DFT.Redc
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Montgomery multiplication on the DFT registers

`M.montMulProg D B xR yR oR tT pR qR wR m1 m2 sR t₁ … t₅` multiplies `x` and `y` (registers
`xR`, `yR`, `r` bits each) with the fast multiplier into `tT` and reduces with `redcProg` into
`oR`; `tT` is cleared. `montMul_exec`: for `x, y < p`, register `oR` ends with
`binSyms r (redc p (2 ^ r) p' (x y))`, which is `x y R⁻¹` in `ZMod p` and below `p`
(`redc_cast`, `redc_lt`), in at most `330 r + 270 + m₀ + m₁ + m₂` steps, where `m₀ + 2`, `m₁ + 2`,
`m₂ + 2` are bounded by the multiplier's time on the three products.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

namespace IntegerMultBounds.MathlibTM2.DFT

namespace HostMultiplier

variable {κ : ℝ} (M : HostMultiplier κ) (D : ℕ) (B : Type)

/-- Montgomery multiplication: `oR := REDC (x y)`, through `tT`. -/
def montMulProg (xR yR oR tT pR qR wR m1 m2 sR t₁ t₂ t₃ t₄ t₅ : Fin D) :
    DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B) :=
  .seq (M.mulCall D B (M.dreg D xR) (M.dreg D yR) (M.dreg D tT) (M.dreg D t₁) (M.dreg D t₂)
      (M.dreg D t₃) (M.dreg D t₄) (M.dreg D t₅))
    (.seq (M.redcProg D B tT pR qR wR oR m1 m2 sR t₁ t₂ t₃ t₄ t₅)
      (hostCode (bclear (M.dreg D tT))))

/-- `montMulProg`: `oR := binSyms r (redc p (2 ^ r) p' (x y))`. -/
theorem montMul_exec (main : DPr (Option M.P) (M.T + D) M.Q M.A (M.U × B))
    {xR yR oR tT pR qR wR m1 m2 sR t₁ t₂ t₃ t₄ t₅ : Fin D}
    (hreg : [xR, yR, oR, tT, pR, qR, wR, m1, m2, sR, t₁, t₂, t₃, t₄, t₅].Nodup)
    {r p p' x y : ℕ} (hp : 0 < p) (hpr : 2 * p ≤ 2 ^ r) (hp'r : p' < 2 ^ r) (hx : x < p)
    (hy : y < p) (v : HS (M.T + D) M.Q M.A (M.U × B)) (S : Stacks (M.T + D) M.A)
    (hinp : S.inp = []) (hout : S.out = []) (hL : ∀ k, S.L k = [])
    (hR : ∀ i, S.R (M.emb D i) = [])
    (hxR : S.R (M.dreg D xR) = binSyms r x) (hyR : S.R (M.dreg D yR) = binSyms r y)
    (hpR : S.R (M.dreg D pR) = binSyms r p) (hqR : S.R (M.dreg D qR) = binSyms r p')
    (hwR : (S.R (M.dreg D wR)).length = r) (hoR : S.R (M.dreg D oR) = [])
    (htT : S.R (M.dreg D tT) = []) (hm1 : S.R (M.dreg D m1) = [])
    (hm2 : S.R (M.dreg D m2) = []) (hsR : S.R (M.dreg D sR) = [])
    (h₁ : S.R (M.dreg D t₁) = []) (h₂ : S.R (M.dreg D t₂) = []) (h₃ : S.R (M.dreg D t₃) = [])
    (h₄ : S.R (M.dreg D t₄) = []) (h₅ : S.R (M.dreg D t₅) = []) (gi go : List Γ') :
    ∃ v' : HS (M.T + D) M.Q M.A (M.U × B), ∃ m₀ m₁ m₂ n, v'.user.2 = v.user.2 ∧
      m₀ + 2 ≤ M.time (Nat.size x + Nat.size y) ∧
      m₁ + 2 ≤ M.time (Nat.size (x * y) + Nat.size p') ∧
      m₂ + 2 ≤ M.time (Nat.size (x * y * p' % 2 ^ r) + Nat.size p) ∧
      n ≤ 330 * r + 270 + m₀ + m₁ + m₂ ∧
      Exec (M.tab D B main) (M.montMulProg D B xR yR oR tT pR qR wR m1 m2 sR t₁ t₂ t₃ t₄ t₅)
        (dmk v S gi go) n
        (dmk v' { S with
          R := Function.update S.R (M.dreg D oR) (binSyms r (redc p (2 ^ r) p' (x * y))) }
          gi go) := by
  have hreg' := hreg
  regs_ne hreg'
  have hnd : ∀ l : List (Fin D), l.Nodup → (l.map (M.dreg D)).Nodup := fun _ h => M.nodup_dreg D h
  have hpr' : p < 2 ^ r := by omega
  have hx' : x < 2 ^ r := hx.trans hpr'
  have hy' : y < 2 ^ r := hy.trans hpr'
  have hxy : x * y < p * 2 ^ r :=
    (Nat.mul_lt_mul_of_lt_of_le hx hy.le hp).trans_le (Nat.mul_le_mul_left _ hpr'.le)
  -- `tT := x y`
  obtain ⟨v₁, m₀, hu₁, hm₀, e₁⟩ := M.mulCall_exec D B main (a := M.dreg D xR)
    (b := M.dreg D yR) (c := M.dreg D tT) (t₁ := M.dreg D t₁) (t₂ := M.dreg D t₂)
    (t₃ := M.dreg D t₃) (t₄ := M.dreg D t₄) (t₅ := M.dreg D t₅)
    (by simpa using hnd [tT, xR, yR, t₁, t₂, t₃, t₄, t₅] (by regs_nodup)) hx' hy' v S hinp hout
    hL hR hxR hyR htT h₁ h₂ h₃ h₄ h₅ gi go
  set S₁ : Stacks (M.T + D) M.A :=
    { S with R := Function.update S.R (M.dreg D tT) (binSyms (r + r) (x * y)) } with hS₁
  -- `oR := REDC (x y)`
  obtain ⟨v₂, m₁, m₂, n₂, hu₂, hm₁, hm₂, hn₂, e₂⟩ := M.redc_exec D B main (tR := tT) (pR := pR)
    (qR := qR) (wR := wR) (oR := oR) (m1 := m1) (m2 := m2) (sR := sR) (t₁ := t₁) (t₂ := t₂)
    (t₃ := t₃) (t₄ := t₄) (t₅ := t₅) (by regs_nodup) hp hpr hp'r hxy v₁ S₁
    (by simp [hS₁, hinp]) (by simp [hS₁, hout]) (by simp [hS₁, hL])
    (by intro i; simp [hS₁, hR]) (by simp [hS₁])
    (by simp [hS₁, ‹tT ≠ pR›.symm, hpR]) (by simp [hS₁, ‹tT ≠ qR›.symm, hqR])
    (by simp [hS₁, ‹tT ≠ wR›.symm, hwR]) (by simp [hS₁, ‹oR ≠ tT›, hoR])
    (by simp [hS₁, ‹tT ≠ m1›.symm, hm1]) (by simp [hS₁, ‹tT ≠ m2›.symm, hm2])
    (by simp [hS₁, ‹tT ≠ sR›.symm, hsR]) (by simp [hS₁, ‹tT ≠ t₁›.symm, h₁])
    (by simp [hS₁, ‹tT ≠ t₂›.symm, h₂]) (by simp [hS₁, ‹tT ≠ t₃›.symm, h₃])
    (by simp [hS₁, ‹tT ≠ t₄›.symm, h₄]) (by simp [hS₁, ‹tT ≠ t₅›.symm, h₅]) gi go
  set S₂ : Stacks (M.T + D) M.A := { S₁ with
    R := Function.update S₁.R (M.dreg D oR) (binSyms r (redc p (2 ^ r) p' (x * y))) } with hS₂
  -- clear `tT`
  obtain ⟨v₃, hu₃, -, e₃⟩ := bclear_exec Empty.elim (M.dreg D tT) v₂ S₂
  rw [show S₂.R (M.dreg D tT) = binSyms (r + r) (x * y) by simp [hS₂, hS₁, ‹oR ≠ tT›.symm],
    length_binSyms] at e₃
  have hsz : Nat.size (x * y) ≤ r + r :=
    Nat.size_le.2 (by rw [pow_add]; exact Nat.mul_lt_mul'' hx' hy')
  refine ⟨v₃, m₀, m₁, m₂, _, ?_, hm₀, hm₁, hm₂, ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (exec_hostCode e₃ gi go))) rfl ?_⟩
  · rw [hu₃, hu₂, hu₁]
  · omega
  · clear e₁ e₂ e₃
    show dmk v₃ _ gi go = dmk v₃ _ gi go
    congr 1
    simp only [hS₂, hS₁]
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

end HostMultiplier

end IntegerMultBounds.MathlibTM2.DFT
