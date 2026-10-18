module

public import IntegerMultBounds.MathlibTM2.DFT.NewtonBlocks
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Newton guess and its correction on the host

In `L = 4 k + 4` bits:

* `newtonGuessProg` (`newtonGuessProg_exec`): from `B2 = d a²` in `2 L` bits and `A = a`,
  `Y := 2 ^ (k+1) a - (⌊d a² / 4 ^ k⌋ + 1)`. `B2` is truncated (`btrunc`) and shifted down by
  `2 k` bits (`usub` by `w2K`), widened, incremented by `ONE` (`badd`); `A` is copied and shifted up
  by `k + 1` zeros (`bzero` by `wK`, one more zero, `btrunc`); `bsub` gives the guess.
* `newtonFinish` (`newtonFinish_exec`): from `B2 = y d` in `2 L` bits,
  `R := 2 ^ (4k) - y d` (`bsub` from `SIX`), the correction loop (`corrLoop`) adds
  `(2 ^ (4k) - y d) / d` to `Y`, and `A := Y`, `wK := w2K`; every other work register is
  cleared.
-/

@[expose] public section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-! ### The guess -/

/-- `Y := 2 ^ (k+1) A - (⌊B2 / 4 ^ k⌋ + 1)`. -/
def newtonGuessProg (B2 B3 ONE Aa Y B1 Yn wK w2K wL t₁ t₂ t₃ : Fin T) : Pr P T Q A U :=
  .seq (btrunc B2 wL t₁ t₂) (.seq (usub w2K B2 t₁) (.seq (bwiden B2 wL B1 t₁ t₂)
    (.seq (badd B2 ONE B1 t₁ t₂ t₃ Yn) (.seq (bclear B2) (.seq (bclear B3) (.seq (bcopy Aa Y t₁ t₂)
      (.seq (bzero wK Y t₁) (.seq (pushS Y (bitSymbol false)) (.seq (btrunc Y wL t₁ t₂)
        (.seq (bsub Y B1 Yn t₁ t₂ t₃ B2) (.seq (bclear Y) (.seq (bclear B1)
          (.seq (bcopy Yn Y t₁ t₂) (bclear Yn))))))))))))))

theorem newtonGuessProg_exec {B2 B3 ONE Aa Y B1 Yn wK w2K wL t₁ t₂ t₃ : Fin T}
    (hreg : [B2, B3, ONE, Aa, Y, B1, Yn, wK, w2K, wL, t₁, t₂, t₃].Nodup) {k a X₂ : ℕ}
    (hX₂ : X₂ < 2 ^ (4 * k + 4)) (ha : 2 ^ (k + 1) * a < 2 ^ (4 * k + 4))
    (hz : X₂ / 2 ^ (k + k) + 1 ≤ 2 ^ (k + 1) * a) (v : HS T Q A U) (S : Stacks T A)
    (hB2 : S.R B2 = binSyms (4 * k + 4 + (4 * k + 4)) X₂)
    (hB3 : (S.R B3).length = 4 * k + 4) (hO : S.R ONE = binSyms (4 * k + 4) 1)
    (hA : S.R Aa = binSyms (4 * k + 4) a) (hK : (S.R wK).length = k)
    (h2 : (S.R w2K).length = k + k) (hL : (S.R wL).length = 4 * k + 4) (hY : S.R Y = [])
    (hB1 : S.R B1 = []) (hYn : S.R Yn = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = [])
    (h₃ : S.R t₃ = []) :
    ∃ v' : HS T Q A U, ∃ n, v'.user = v.user ∧ n ≤ 300 * k + 400 ∧
      Exec body (newtonGuessProg B2 B3 ONE Aa Y B1 Yn wK w2K wL t₁ t₂ t₃) (mk v S) n
        (mk v' { S with
          R := Function.update (Function.update (Function.update S.R Y
            (binSyms (4 * k + 4) (2 ^ (k + 1) * a - (X₂ / 2 ^ (k + k) + 1)))) B2 []) B3 [] }) := by
  have hreg' := hreg
  regs_ne hreg'
  set L := 4 * k + 4 with hLdef
  set z := X₂ / 2 ^ (k + k) with hzdef
  have hzlt : z < 2 ^ (k + k + 4) := by
    rw [hzdef, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
    calc X₂ < 2 ^ L := hX₂
      _ = 2 ^ (k + k + 4 + (k + k)) := by rw [hLdef]; ring_nf
  have hzL : z + 1 < 2 ^ L := by omega
  have h1L : 1 < 2 ^ L := by
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- `B2 := X₂ mod 2 ^ L`, then `z`
  obtain ⟨v₁, hu₁, e₁⟩ := btrunc_exec body (a := B2) (wR := wL) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) (r := L) (e := L) (X := X₂) v S hB2 hL h₁ h₂
  set S₁ : Stacks T A := { S with R := Function.update S.R B2 (binSyms L X₂) } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := bhigh_exec body (a := B2) (wR := w2K) (t := t₁) (by regs_nodup)
    (r := k + k) (e := k + k + 4) (X := X₂) v₁ S₁
    (by rw [show k + k + (k + k + 4) = L by omega]; simp [hS₁])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
  rw [← hzdef] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R B2 (binSyms (k + k + 4) z) }
    with hS₂
  obtain ⟨v₃, hu₃, e₃⟩ := bwiden_exec body (a := B2) (wR := wL) (cnt := B1) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) (by omega : k + k + 4 ≤ L) hzlt v₂ S₂ (by simp [hS₂])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R B2 (binSyms L z) } with hS₃
  -- `B1 := z + 1`
  obtain ⟨v₄, hu₄, -, -, e₄⟩ := badd_exec body (a := B2) (b := ONE) (c := B1) (tx := t₁)
    (ty := t₂) (tz := t₃) (cy := Yn) (by regs_nodup) ‹B2 ≠ Yn›.symm ‹ONE ≠ Yn›.symm (L := L)
    (x := z) (y := 1) (by omega) h1L v₃ S₃ (by simp [hS₃]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  rw [Nat.mod_eq_of_lt hzL, show S₃.R B1 = [] by simp [*, Ne.symm],
    List.append_nil] at e₄
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R B1 (binSyms L (z + 1)) } with hS₄
  -- clear `B2`, `B3`
  obtain ⟨v₅, hu₅, -, e₅⟩ := bclear_exec body B2 v₄ S₄
  rw [show (S₄.R B2).length = L by simp [hS₄, hS₃, ‹B2 ≠ B1›]] at e₅
  set S₅ : Stacks T A := { S₄ with R := Function.update S₄.R B2 [] } with hS₅
  obtain ⟨v₆, hu₆, -, e₆⟩ := bclear_exec body B3 v₅ S₅
  rw [show (S₅.R B3).length = L by simp [*, Ne.symm]] at e₆
  set S₆ : Stacks T A := { S₅ with R := Function.update S₅.R B3 [] } with hS₆
  -- `Y := 2 ^ (k+1) a`
  obtain ⟨v₇, hu₇, e₇⟩ := bcopy_exec body (a := Aa) (c := Y) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₆ S₆ (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  rw [show S₆.R Aa = binSyms L a by simp [*, Ne.symm],
    show S₆.R Y = [] by simp [*, Ne.symm], List.append_nil,
    length_binSyms] at e₇
  set S₇ : Stacks T A := { S₆ with R := Function.update S₆.R Y (binSyms L a) } with hS₇
  obtain ⟨v₈, hu₈, e₈⟩ := bzero_exec body (wR := wK) (c := Y) (t := t₁) (by regs_nodup) v₇ S₇
    (by simp [*, Ne.symm])
  rw [show (S₇.R wK).length = k by simp [*, Ne.symm],
    show S₇.R Y = binSyms L a by simp [hS₇]] at e₈
  set S₈ : Stacks T A := { S₇ with R := Function.update S₇.R Y (binSyms k 0 ++ binSyms L a) }
    with hS₈
  have e₉ := pushS_exec body Y (bitSymbol false) v₈ S₈
  have hshift : (bitSymbol false :: (binSyms k 0 ++ binSyms L a) : List (Fin (A + 4))) =
      binSyms (L + (k + 1)) (2 ^ (k + 1) * a) := by
    rw [binSyms_zero_right, ← List.cons_append, ← List.replicate_succ, binSyms_shift_pow,
      Nat.add_comm (k + 1) L]
  rw [show S₈.R Y = binSyms k 0 ++ binSyms L a by simp [hS₈], hshift] at e₉
  set S₉ : Stacks T A :=
    { S₈ with R := Function.update S₈.R Y (binSyms (L + (k + 1)) (2 ^ (k + 1) * a)) } with hS₉
  obtain ⟨v₁₀, hu₁₀, e₁₀⟩ := btrunc_exec body (a := Y) (wR := wL) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) (r := L) (e := k + 1) (X := 2 ^ (k + 1) * a) v₈ S₉ (by simp [hS₉])
    (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  set S₁₀ : Stacks T A := { S₉ with R := Function.update S₉.R Y (binSyms L (2 ^ (k + 1) * a)) }
    with hS₁₀
  -- `Yn := Y - B1`
  obtain ⟨v₁₁, hu₁₁, -, -, e₁₁⟩ := bsub_exec body (a := Y) (b := B1) (c := Yn) (tx := t₁)
    (ty := t₂) (tz := t₃) (cy := B2) (by regs_nodup) ‹B2 ≠ Y› ‹B2 ≠ B1› (L := L)
    (x := 2 ^ (k + 1) * a) (y := z + 1) ha hzL v₁₀ S₁₀ (by simp [hS₁₀])
    (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  have hval : (2 ^ (k + 1) * a + 2 ^ L - (z + 1)) % 2 ^ L = 2 ^ (k + 1) * a - (z + 1) := by
    rw [Nat.sub_add_comm hz, Nat.add_mod_right,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) ha)]
  rw [hval, show S₁₀.R Yn = [] by
    simp [*, Ne.symm], List.append_nil] at e₁₁
  set y := 2 ^ (k + 1) * a - (z + 1) with hy
  set S₁₁ : Stacks T A := { S₁₀ with R := Function.update S₁₀.R Yn (binSyms L y) } with hS₁₁
  -- `Y := Yn`, clear `B1`, `Yn`
  obtain ⟨v₁₂, hu₁₂, -, e₁₂⟩ := bclear_exec body Y v₁₁ S₁₁
  rw [show (S₁₁.R Y).length = L by simp [hS₁₁, hS₁₀, ‹Y ≠ Yn›]] at e₁₂
  set S₁₂ : Stacks T A := { S₁₁ with R := Function.update S₁₁.R Y [] } with hS₁₂
  obtain ⟨v₁₃, hu₁₃, -, e₁₃⟩ := bclear_exec body B1 v₁₂ S₁₂
  rw [show (S₁₂.R B1).length = L by
    simp [*, Ne.symm]] at e₁₃
  set S₁₃ : Stacks T A := { S₁₂ with R := Function.update S₁₂.R B1 [] } with hS₁₃
  obtain ⟨v₁₄, hu₁₄, e₁₄⟩ := bcopy_exec body (a := Yn) (c := Y) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₁₃ S₁₃
    (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  rw [show S₁₃.R Yn = binSyms L y by simp [*, Ne.symm],
    show S₁₃.R Y = [] by simp [*], List.append_nil, length_binSyms] at e₁₄
  set S₁₄ : Stacks T A := { S₁₃ with R := Function.update S₁₃.R Y (binSyms L y) } with hS₁₄
  obtain ⟨v₁₅, hu₁₅, -, e₁₅⟩ := bclear_exec body Yn v₁₄ S₁₄
  rw [show (S₁₄.R Yn).length = L by simp [*, Ne.symm]] at e₁₅
  refine ⟨v₁₅, _, by rw [hu₁₅, hu₁₄, hu₁₃, hu₁₂, hu₁₁, hu₁₀, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂,
    hu₁], ?_, Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅
      (Exec.seq e₆ (Exec.seq e₇ (Exec.seq e₈ (Exec.seq e₉ (Exec.seq e₁₀ (Exec.seq e₁₁
        (Exec.seq e₁₂ (Exec.seq e₁₃ (Exec.seq e₁₄ e₁₅)))))))))))))) rfl ?_⟩
  · omega
  · clear e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃ e₁₄ e₁₅
    simp only [hS₁₄, hS₁₃, hS₁₂, hS₁₁, hS₁₀, hS₉, hS₈, hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁]
    clear hS₁₄ hS₁₃ hS₁₂ hS₁₁ hS₁₀ hS₉ hS₈ hS₇ hS₆ hS₅ hS₄ hS₃ hS₂ hS₁ hval hshift
    congr 2
    funext j
    by_cases hjY : j = Y
    · subst hjY; simp [*, Ne.symm]
    by_cases hjB2 : j = B2
    · subst hjB2; simp [*]
    by_cases hjB3 : j = B3
    · subst hjB3; simp [*]
    by_cases hjB1 : j = B1
    · subst hjB1; simp [*, Ne.symm]
    by_cases hjYn : j = Yn
    · subst hjYn; simp [*, Ne.symm]
    simp [*]

/-! ### The correction and the next level -/

/-- `R := 2 ^ (4k) - B2`, correct `Y`, then `A := Y` and `wK := w2K`; clear the work registers. -/
def newtonFinish (B2 SIX R Dd Y ONE Rn Yn Aa wK w2K wL t₁ t₂ t₃ : Fin T) : Pr P T Q A U :=
  .seq (btrunc B2 wL t₁ t₂) (.seq (bsub SIX B2 R t₁ t₂ t₃ Rn) (.seq (bclear B2) (.seq (bclear SIX)
    (.seq (corrLoop R Dd Y ONE Rn Yn t₁ t₂ t₃) (.seq (bclear R) (.seq (bclear ONE)
      (.seq (bclear Dd) (.seq (bclear wL) (.seq (bclear Aa) (.seq (bcopy Y Aa t₁ t₂)
        (.seq (bclear Y) (.seq (bclear wK) (.seq (bcopy w2K wK t₁ t₂) (bclear w2K))))))))))))))

theorem newtonFinish_exec {B2 SIX R Dd Y ONE Rn Yn Aa wK w2K wL t₁ t₂ t₃ : Fin T}
    (hreg : [B2, SIX, R, Dd, Y, ONE, Rn, Yn, Aa, wK, w2K, wL, t₁, t₂, t₃].Nodup) {k P d y : ℕ}
    (hP : P ≤ 2 ^ (4 * k)) (hd0 : 0 < d) (hd : d < 2 ^ (4 * k + 4))
    (hy : y + (2 ^ (4 * k) - P) / d < 2 ^ (4 * k + 4)) (hc : (2 ^ (4 * k) - P) / d ≤ 8)
    (v : HS T Q A U) (S : Stacks T A) (hB2 : S.R B2 = binSyms (4 * k + 4 + (4 * k + 4)) P)
    (hS6 : S.R SIX = binSyms (4 * k + 4) (2 ^ (4 * k))) (hDd : S.R Dd = binSyms (4 * k + 4) d)
    (hY : S.R Y = binSyms (4 * k + 4) y) (hO : S.R ONE = binSyms (4 * k + 4) 1)
    (hA : (S.R Aa).length = 4 * k + 4) (hK : (S.R wK).length = k)
    (h2 : (S.R w2K).length = k + k) (hL : (S.R wL).length = 4 * k + 4) (hR : S.R R = [])
    (hRn : S.R Rn = []) (hYn : S.R Yn = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = [])
    (h₃ : S.R t₃ = []) :
    ∃ v' : HS T Q A U, ∃ n, v'.user = v.user ∧ n ≤ 1700 * k + 2100 ∧
      Exec body (newtonFinish B2 SIX R Dd Y ONE Rn Yn Aa wK w2K wL t₁ t₂ t₃) (mk v S) n
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update
            (Function.update (Function.update (Function.update (Function.update
              (Function.update S.R B2 []) SIX []) Dd []) Y []) ONE []) wL []) Aa
              (binSyms (4 * k + 4) (y + (2 ^ (4 * k) - P) / d))) wK (S.R w2K)) w2K [] }) := by
  have hreg' := hreg
  regs_ne hreg'
  set L := 4 * k + 4 with hLdef
  set ρ := 2 ^ (4 * k) - P with hρ
  have h4L : 2 ^ (4 * k) < 2 ^ L := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hPL : P < 2 ^ L := lt_of_le_of_lt hP h4L
  have hρL : ρ < 2 ^ L := lt_of_le_of_lt (Nat.sub_le _ _) h4L
  -- `B2 := P` in `L` bits
  obtain ⟨v₁, hu₁, e₁⟩ := btrunc_exec body (a := B2) (wR := wL) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) (r := L) (e := L) (X := P) v S hB2 hL h₁ h₂
  set S₁ : Stacks T A := { S with R := Function.update S.R B2 (binSyms L P) } with hS₁
  -- `R := 2 ^ (4k) - P`
  obtain ⟨v₂, hu₂, -, -, e₂⟩ := bsub_exec body (a := SIX) (b := B2) (c := R) (tx := t₁)
    (ty := t₂) (tz := t₃) (cy := Rn) (by regs_nodup) ‹SIX ≠ Rn›.symm ‹B2 ≠ Rn›.symm (L := L)
    (x := 2 ^ (4 * k)) (y := P) h4L hPL v₁ S₁ (by simp [*, Ne.symm]) (by simp [hS₁])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
  have hval : (2 ^ (4 * k) + 2 ^ L - P) % 2 ^ L = ρ := by
    rw [Nat.sub_add_comm hP, Nat.add_mod_right, Nat.mod_eq_of_lt hρL]
  rw [hval, show S₁.R R = [] by simp [*, Ne.symm], List.append_nil] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R R (binSyms L ρ) } with hS₂
  obtain ⟨v₃, hu₃, -, e₃⟩ := bclear_exec body B2 v₂ S₂
  rw [show (S₂.R B2).length = L by simp [hS₂, hS₁, ‹B2 ≠ R›]] at e₃
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R B2 [] } with hS₃
  obtain ⟨v₄, hu₄, -, e₄⟩ := bclear_exec body SIX v₃ S₃
  rw [show (S₃.R SIX).length = L by simp [*, Ne.symm]] at e₄
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R SIX [] } with hS₄
  -- the correction loop
  obtain ⟨v₅, n₅, hu₅, hn₅, e₅⟩ := corrLoop_exec body (R := R) (Dd := Dd) (Y := Y) (ONE := ONE)
    (Rn := Rn) (Yn := Yn) (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) (by regs_nodup) (L := L) (ρ := ρ)
    (d := d) (y := y) hd0 hd hρL hy v₄ S₄ (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
  set μ := y + ρ / d with hμ
  set S₅ : Stacks T A := { S₄ with
    R := Function.update (Function.update S₄.R R (binSyms L (ρ % d))) Y (binSyms L μ) }
    with hS₅
  -- clear `R`, `ONE`, `Dd`, `wL`
  obtain ⟨v₆, hu₆, -, e₆⟩ := bclear_exec body R v₅ S₅
  rw [show (S₅.R R).length = L by simp [hS₅, ‹R ≠ Y›]] at e₆
  set S₆ : Stacks T A := { S₅ with R := Function.update S₅.R R [] } with hS₆
  obtain ⟨v₇, hu₇, -, e₇⟩ := bclear_exec body ONE v₆ S₆
  rw [show (S₆.R ONE).length = L by simp [*, Ne.symm]] at e₇
  set S₇ : Stacks T A := { S₆ with R := Function.update S₆.R ONE [] } with hS₇
  obtain ⟨v₈, hu₈, -, e₈⟩ := bclear_exec body Dd v₇ S₇
  rw [show (S₇.R Dd).length = L by simp [*, Ne.symm]] at e₈
  set S₈ : Stacks T A := { S₇ with R := Function.update S₇.R Dd [] } with hS₈
  obtain ⟨v₉, hu₉, -, e₉⟩ := bclear_exec body wL v₈ S₈
  rw [show (S₈.R wL).length = L by
    simp [*, Ne.symm]] at e₉
  set S₉ : Stacks T A := { S₈ with R := Function.update S₈.R wL [] } with hS₉
  -- `A := Y`
  obtain ⟨v₁₀, hu₁₀, -, e₁₀⟩ := bclear_exec body Aa v₉ S₉
  rw [show (S₉.R Aa).length = L by
    simp [*, Ne.symm]] at e₁₀
  set S₁₀ : Stacks T A := { S₉ with R := Function.update S₉.R Aa [] } with hS₁₀
  obtain ⟨v₁₁, hu₁₁, e₁₁⟩ := bcopy_exec body (a := Y) (c := Aa) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₁₀ S₁₀
    (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  rw [show S₁₀.R Y = binSyms L μ by simp [*, Ne.symm],
    show S₁₀.R Aa = [] by simp [hS₁₀], List.append_nil, length_binSyms] at e₁₁
  set S₁₁ : Stacks T A := { S₁₀ with R := Function.update S₁₀.R Aa (binSyms L μ) } with hS₁₁
  obtain ⟨v₁₂, hu₁₂, -, e₁₂⟩ := bclear_exec body Y v₁₁ S₁₁
  rw [show (S₁₁.R Y).length = L by
    simp [*, Ne.symm]] at e₁₂
  set S₁₂ : Stacks T A := { S₁₁ with R := Function.update S₁₁.R Y [] } with hS₁₂
  -- `wK := w2K`
  obtain ⟨v₁₃, hu₁₃, -, e₁₃⟩ := bclear_exec body wK v₁₂ S₁₂
  rw [show (S₁₂.R wK).length = k by
    simp [*, Ne.symm]] at e₁₃
  set S₁₃ : Stacks T A := { S₁₂ with R := Function.update S₁₂.R wK [] } with hS₁₃
  have hW2 : S₁₃.R w2K = S.R w2K := by
    simp [*, Ne.symm]
  obtain ⟨v₁₄, hu₁₄, e₁₄⟩ := bcopy_exec body (a := w2K) (c := wK) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₁₃ S₁₃
    (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  rw [hW2, h2, show S₁₃.R wK = [] by simp [hS₁₃], List.append_nil] at e₁₄
  set S₁₄ : Stacks T A := { S₁₃ with R := Function.update S₁₃.R wK (S.R w2K) } with hS₁₄
  obtain ⟨v₁₅, hu₁₅, -, e₁₅⟩ := bclear_exec body w2K v₁₄ S₁₄
  rw [show (S₁₄.R w2K).length = k + k by simp [hS₁₄, ‹wK ≠ w2K›.symm, hW2, h2]] at e₁₅
  refine ⟨v₁₅, _, by rw [hu₁₅, hu₁₄, hu₁₃, hu₁₂, hu₁₁, hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃,
    hu₂, hu₁], ?_, Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅
      (Exec.seq e₆ (Exec.seq e₇ (Exec.seq e₈ (Exec.seq e₉ (Exec.seq e₁₀ (Exec.seq e₁₁
        (Exec.seq e₁₂ (Exec.seq e₁₃ (Exec.seq e₁₄ e₁₅)))))))))))))) rfl ?_⟩
  · have : ρ / d * (44 * L + 45) ≤ 8 * (44 * L + 45) := Nat.mul_le_mul_right _ hc
    omega
  · clear e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃ e₁₄ e₁₅
    simp only [hS₁₄, hS₁₃, hS₁₂, hS₁₁, hS₁₀, hS₉, hS₈, hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁]
    clear hS₁₄ hS₁₃ hS₁₂ hS₁₁ hS₁₀ hS₉ hS₈ hS₇ hS₆ hS₅ hS₄ hS₃ hS₂ hS₁ hval hW2 hn₅
    congr 2
    funext j
    by_cases hj1 : j = B2
    · subst hj1; simp [*]
    by_cases hj2 : j = SIX
    · subst hj2; simp [*]
    by_cases hj3 : j = R
    · subst hj3; simp [*, Ne.symm]
    by_cases hj4 : j = Dd
    · subst hj4; simp [*]
    by_cases hj5 : j = Y
    · subst hj5; simp [*]
    by_cases hj6 : j = ONE
    · subst hj6; simp [*, Ne.symm]
    by_cases hj7 : j = wL
    · subst hj7; simp [*, Ne.symm]
    by_cases hj8 : j = Aa
    · subst hj8; simp [*, Ne.symm]
    by_cases hj9 : j = wK
    · subst hj9; simp [*]
    by_cases hj10 : j = w2K
    · subst hj10; simp [*]
    simp [*]

end IntegerMultBounds.MathlibTM2.DFT
