module

public import IntegerMultBounds.MathlibTM2.DFT.NewtonSetup
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The host blocks of a Newton level

A level raises the precision of the reciprocal from `k` to `2 k` bits in `L = 4 k + 4` bits. The
divisor is kept most significant bit first in `Dp = (binSyms N D).reverse`; its top `2 k` bits
are `d = D / 2 ^ (N - 2k)` (`binSyms_reverse_top`). Between the three products of the level the
host runs:

* `newtonLoad` (`newtonLoad_exec`): `Dd := binSyms L d` (`bcopyTop`, `moveR`, `bwiden`),
  `A := binSyms L a` (`bwiden`) and its copy `B2`;
* `newtonSq` (`newtonSq_exec`): `B3 := a²` in `L` bits (`btrunc`), `B2` cleared;
* `newtonGuessProg` (`newtonGuessProg_exec`): from `B2 = d a²` in `2 L` bits,
  `Y := 2 ^ (k+1) a - (⌊d a² / 4 ^ k⌋ + 1)` in `L` bits (`btrunc`, `usub`, `bwiden`, `badd`,
  shifting `A` by `k + 1` zeros, `bsub`).
-/

@[expose] public section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- The top `m` bits of `binSyms N X`, most significant first. -/
theorem binSyms_reverse_top {N m : ℕ} (hm : m ≤ N) (X : ℕ) :
    (binSyms N X : List (Fin (A + 4))).reverse =
      (binSyms m (X / 2 ^ (N - m))).reverse ++ (binSyms (N - m) X).reverse := by
  conv_lhs => rw [show N = (N - m) + m by omega, binSyms_append]
  rw [List.reverse_append]

/-! ### Loading the divisor and the reciprocal -/

/-- `Dd := ` the top `2 k` bits of `Dp` in `L` bits, `A := A` in `L` bits, `B2 := A`. -/
def newtonLoad (Dp w2K wL B1 Dd Aa B2 t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bcopyLow Dp w2K B1 t₁ t₂) (.seq (moveR B1 Dd id) (.seq (bwiden Dd wL B1 t₁ t₂)
    (.seq (bwiden Aa wL B1 t₁ t₂) (bcopy Aa B2 t₁ t₂))))

theorem newtonLoad_exec {Dp w2K wL B1 Dd Aa B2 t₁ t₂ : Fin T}
    (hreg : [Dp, w2K, wL, B1, Dd, Aa, B2, t₁, t₂].Nodup) {k N D a : ℕ} (hN : k + k ≤ N)
    (hD : D < 2 ^ N) (ha : a < 2 ^ (k + k + 4)) (v : HS T Q A U) (S : Stacks T A)
    (hDp : S.R Dp = (binSyms N D).reverse) (h2 : (S.R w2K).length = k + k)
    (hL : (S.R wL).length = 4 * k + 4) (hA : S.R Aa = binSyms (k + k + 4) a)
    (hB1 : S.R B1 = []) (hDd : S.R Dd = []) (hB2 : S.R B2 = []) (h₁ : S.R t₁ = [])
    (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, ∃ n, v'.user = v.user ∧ n ≤ 150 * k + 200 ∧
      Exec body (newtonLoad Dp w2K wL B1 Dd Aa B2 t₁ t₂) (mk v S) n
        (mk v' { S with
          R := Function.update (Function.update (Function.update S.R Dd
            (binSyms (4 * k + 4) (D / 2 ^ (N - (k + k))))) Aa (binSyms (4 * k + 4) a)) B2
            (binSyms (4 * k + 4) a) }) := by
  have hreg' := hreg
  regs_ne hreg'
  set d := D / 2 ^ (N - (k + k)) with hd
  have hdlt : d < 2 ^ (k + k) := by
    rw [hd, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show k + k + (N - (k + k)) = N by omega]
    exact hD
  -- the top `2 k` bits, most significant first, onto `B1`
  obtain ⟨v₁, hu₁, e₁⟩ := bcopyTop_exec body (s := Dp) (wR := w2K) (d := B1) (t₁ := t₁)
    (t₂ := t₂) (by regs_nodup) (l₁ := (binSyms (k + k) d).reverse)
    (l₂ := (binSyms (N - (k + k)) D).reverse) v S (by rw [hDp, binSyms_reverse_top hN])
    (by simp [h2]) h₁ h₂
  rw [hB1, List.append_nil, List.length_reverse, length_binSyms] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R B1 (binSyms (k + k) d).reverse }
    with hS₁
  -- back onto `Dd`, least significant first
  obtain ⟨v₂, hu₂, e₂⟩ := moveR_exec body B1 Dd ‹B1 ≠ Dd› id v₁ S₁
  rw [show S₁.R B1 = (binSyms (k + k) d).reverse by simp [hS₁], List.length_reverse,
    length_binSyms] at e₂
  set S₂ : Stacks T A := { S₁ with R := movedR S₁.R B1 Dd id (binSyms (k + k) d).reverse }
    with hS₂
  have hS₂Dd : S₂.R Dd = binSyms (k + k) d := by simp [hS₂, hS₁, movedR, ‹B1 ≠ Dd›.symm, hDd]
  have hS₂B1 : S₂.R B1 = [] := by simp [hS₂, movedR, ‹B1 ≠ Dd›]
  -- widen `Dd` and `A`
  obtain ⟨v₃, hu₃, e₃⟩ := bwiden_exec body (a := Dd) (wR := wL) (cnt := B1) (t₁ := t₁)
    (t₂ := t₂) (by regs_nodup) (by omega : k + k ≤ 4 * k + 4) hdlt v₂ S₂ hS₂Dd
    (by simp [hS₂, hS₁, movedR, *, Ne.symm]) hS₂B1 (by simp [hS₂, hS₁, movedR, *, Ne.symm])
    (by simp [hS₂, hS₁, movedR, *, Ne.symm])
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R Dd (binSyms (4 * k + 4) d) }
    with hS₃
  obtain ⟨v₄, hu₄, e₄⟩ := bwiden_exec body (a := Aa) (wR := wL) (cnt := B1) (t₁ := t₁)
    (t₂ := t₂) (by regs_nodup) (by omega : k + k + 4 ≤ 4 * k + 4) ha v₃ S₃
    (by simp [hS₃, hS₂, hS₁, movedR, *, Ne.symm]) (by simp [hS₃, hS₂, hS₁, movedR, *, Ne.symm])
    (by simp [hS₃, hS₂B1, ‹B1 ≠ Dd›]) (by simp [hS₃, hS₂, hS₁, movedR, *, Ne.symm])
    (by simp [hS₃, hS₂, hS₁, movedR, *, Ne.symm])
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R Aa (binSyms (4 * k + 4) a) }
    with hS₄
  -- copy `A` onto `B2`
  obtain ⟨v₅, hu₅, e₅⟩ := bcopy_exec body (a := Aa) (c := B2) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₄ S₄ (by simp [hS₄, hS₃, hS₂, hS₁, movedR, *, Ne.symm])
    (by simp [hS₄, hS₃, hS₂, hS₁, movedR, *, Ne.symm])
  rw [show S₄.R Aa = binSyms (4 * k + 4) a by simp [hS₄], length_binSyms,
    show S₄.R B2 = [] by simp [hS₄, hS₃, hS₂, hS₁, movedR, *, Ne.symm], List.append_nil] at e₅
  refine ⟨v₅, _, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ e₅)))) rfl ?_⟩
  · omega
  · clear e₁ e₂ e₃ e₄ e₅
    simp only [hS₄, hS₃, hS₂, hS₁]
    clear hS₄ hS₃ hS₂ hS₁ hS₂Dd hS₂B1
    congr 2
    funext j
    by_cases hjD : j = Dd
    · subst hjD; simp [movedR, *, Ne.symm]
    by_cases hjA : j = Aa
    · subst hjA; simp [movedR, *, Ne.symm]
    by_cases hjB : j = B2
    · subst hjB; simp [movedR, *, Ne.symm]
    by_cases hjB1 : j = B1
    · subst hjB1; simp [movedR, *, Ne.symm]
    simp [movedR, *]

/-! ### The square -/

/-- `B3 := ` its low `L` bits, `B2` cleared. -/
def newtonSq (B2 B3 wL t₁ t₂ : Fin T) : Pr P T Q A U := .seq (btrunc B3 wL t₁ t₂) (bclear B2)

theorem newtonSq_exec {B2 B3 wL t₁ t₂ : Fin T} (hreg : [B2, B3, wL, t₁, t₂].Nodup) {L X : ℕ}
    (v : HS T Q A U) (S : Stacks T A) (hB2 : (S.R B2).length = L)
    (hB3 : S.R B3 = binSyms (L + L) X) (hL : (S.R wL).length = L) (h₁ : S.R t₁ = [])
    (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (newtonSq B2 B3 wL t₁ t₂) (mk v S) (10 * L + 10)
        (mk v' { S with R := Function.update (Function.update S.R B3 (binSyms L X)) B2 [] }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, e₁⟩ := btrunc_exec body (a := B3) (wR := wL) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) (r := L) (e := L) (X := X) v S hB3 hL h₁ h₂
  set S₁ : Stacks T A := { S with R := Function.update S.R B3 (binSyms L X) } with hS₁
  obtain ⟨v₂, hu₂, -, e₂⟩ := bclear_exec body B2 v₁ S₁
  rw [show (S₁.R B2).length = L by simp [hS₁, ‹B2 ≠ B3›, hB2]] at e₂
  exact ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq e₁ e₂) (by ring) rfl⟩

end IntegerMultBounds.MathlibTM2.DFT
