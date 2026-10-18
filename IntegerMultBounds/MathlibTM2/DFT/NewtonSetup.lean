module

public import IntegerMultBounds.MathlibTM2.DFT.NewtonHost
public import IntegerMultBounds.MathlibTM2.DFT.Fields
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The registers of a Newton level

A level of the Newton iteration raises the precision from `k` to `2 k` bits and works in
`L = 4 k + 4` bits. `newtonPrep Cnt wK w2K wL ONE SIX t₁ t₂` prepares its registers
(`newtonPrep_exec`):

* the counter `Cnt` loses `k = |wK|` symbols (`usub`);
* `w2K := wK ++ wK` and `wL := w2K ++ w2K ++ [tick, tick, tick, tick]`, width registers of
  `2 k` and `L` symbols;
* `ONE := binSyms L 1` (`L` zeros, the top one replaced by `bitSymbol true`);
* `SIX := binSyms L (2 ^ (4k))` (`binSyms 4 1` under `4 k` zeros, `binSyms_shift_pow`).
-/

@[expose] public section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Push the symbol `x` onto register `i`. -/
def pushS (i : Fin T) (x : Fin (A + 4)) : Pr P T Q A U := .act (.push (.rt i) (fun _ => x) .done)

theorem pushS_exec (i : Fin T) (x : Fin (A + 4)) (v : HS T Q A U) (S : Stacks T A) :
    Exec body (pushS i x) (mk v S) 1
      (mk v { S with R := Function.update S.R i (x :: S.R i) }) := by
  have := Exec.act (body := body) (Action.push (.rt i) (fun _ => x) .done : Act T Q A U) (mk v S)
  simpa [pushS, Action.run, update_rt] using this

theorem dropR_exec (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    Exec body (.act (dropR i)) (mk v S) 1
      (mk v { S with R := Function.update S.R i (S.R i).tail }) := by
  have := Exec.act (body := body) (dropR i : Act T Q A U) (mk v S)
  rwa [dropR_run] at this

theorem binSyms_four_one : (binSyms 4 1 : List (Fin (A + 4))) =
    [bitSymbol true, bitSymbol false, bitSymbol false, bitSymbol false] := rfl

/-- The registers of a level: counter, width registers, `ONE`, `SIX`. -/
def newtonPrep (Cnt wK w2K wL ONE SIX t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (usub wK Cnt t₁) (.seq (bcopy wK w2K t₁ t₂) (.seq (bcopy wK w2K t₁ t₂)
    (.seq (bcopy w2K wL t₁ t₂) (.seq (bcopy w2K wL t₁ t₂) (.seq (pushS wL tick)
      (.seq (pushS wL tick) (.seq (pushS wL tick) (.seq (pushS wL tick)
        (.seq (bzero wL ONE t₁) (.seq (.act (dropR ONE)) (.seq (pushS ONE (bitSymbol true))
          (.seq (pushS SIX (bitSymbol false)) (.seq (pushS SIX (bitSymbol false))
            (.seq (pushS SIX (bitSymbol false)) (.seq (pushS SIX (bitSymbol true))
              (.seq (bzero w2K SIX t₁) (bzero w2K SIX t₁)))))))))))))))))

/-- `newtonPrep`: the counter loses `k` symbols; the width registers, `ONE` and `SIX` are set. -/
theorem newtonPrep_exec {Cnt wK w2K wL ONE SIX t₁ t₂ : Fin T}
    (hreg : [Cnt, wK, w2K, wL, ONE, SIX, t₁, t₂].Nodup) {k : ℕ} (v : HS T Q A U)
    (S : Stacks T A) (hK : (S.R wK).length = k) (h2 : S.R w2K = []) (hL : S.R wL = [])
    (hO : S.R ONE = []) (hS6 : S.R SIX = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, ∃ n, v'.user = v.user ∧ n ≤ 100 * k + 100 ∧
      Exec body (newtonPrep Cnt wK w2K wL ONE SIX t₁ t₂) (mk v S) n
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update
            (Function.update S.R Cnt ((S.R Cnt).drop k)) w2K (S.R wK ++ S.R wK))
            wL ([tick, tick, tick, tick] ++ (S.R wK ++ S.R wK) ++ (S.R wK ++ S.R wK)))
            ONE (binSyms (4 * k + 4) 1)) SIX (binSyms (4 * k + 4) (2 ^ (4 * k))) }) := by
  have hreg' := hreg
  regs_ne hreg'
  set KK := S.R wK ++ S.R wK with hKK
  have hKKl : KK.length = k + k := by simp [hKK, hK]
  set WL := [tick, tick, tick, tick] ++ KK ++ KK with hWL
  have hWLl : WL.length = 4 * k + 4 := by simp [hWL, hKKl]; ring
  -- the counter
  obtain ⟨v₁, hu₁, e₁⟩ := usub_exec body ‹Cnt ≠ wK›.symm ‹wK ≠ t₁› ‹Cnt ≠ t₁› v S h₁
  rw [hK] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R Cnt ((S.R Cnt).drop k) } with hS₁
  -- `w2K`
  obtain ⟨v₂, hu₂, e₂⟩ := bcopy_exec body (a := wK) (c := w2K) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₁ S₁ (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
  rw [show S₁.R wK = S.R wK by simp [*, Ne.symm], hK,
    show S₁.R w2K = [] by simp [*, Ne.symm], List.append_nil] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R w2K (S.R wK) } with hS₂
  obtain ⟨v₃, hu₃, e₃⟩ := bcopy_exec body (a := wK) (c := w2K) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₂ S₂ (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
  rw [show S₂.R wK = S.R wK by simp [*, Ne.symm], hK,
    show S₂.R w2K = S.R wK by simp [hS₂]] at e₃
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R w2K KK } with hS₃
  -- `wL`
  obtain ⟨v₄, hu₄, e₄⟩ := bcopy_exec body (a := w2K) (c := wL) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₃ S₃ (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  rw [show S₃.R w2K = KK by simp [hS₃], hKKl,
    show S₃.R wL = [] by simp [*, Ne.symm], List.append_nil] at e₄
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R wL KK } with hS₄
  obtain ⟨v₅, hu₅, e₅⟩ := bcopy_exec body (a := w2K) (c := wL) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₄ S₄ (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  rw [show S₄.R w2K = KK by simp [hS₄, hS₃, ‹w2K ≠ wL›], hKKl,
    show S₄.R wL = KK by simp [hS₄]] at e₅
  set S₅ : Stacks T A := { S₄ with R := Function.update S₄.R wL (KK ++ KK) } with hS₅
  have e₆ := pushS_exec body wL tick v₅ S₅
  rw [show S₅.R wL = KK ++ KK by simp [hS₅]] at e₆
  set S₆ : Stacks T A := { S₅ with R := Function.update S₅.R wL (tick :: (KK ++ KK)) } with hS₆
  have e₇ := pushS_exec body wL tick v₅ S₆
  rw [show S₆.R wL = tick :: (KK ++ KK) by simp [hS₆]] at e₇
  set S₇ : Stacks T A :=
    { S₆ with R := Function.update S₆.R wL (tick :: tick :: (KK ++ KK)) } with hS₇
  have e₈ := pushS_exec body wL tick v₅ S₇
  rw [show S₇.R wL = tick :: tick :: (KK ++ KK) by simp [hS₇]] at e₈
  set S₈ : Stacks T A :=
    { S₇ with R := Function.update S₇.R wL (tick :: tick :: tick :: (KK ++ KK)) } with hS₈
  have e₉ := pushS_exec body wL tick v₅ S₈
  rw [show S₈.R wL = tick :: tick :: tick :: (KK ++ KK) by simp [hS₈],
    show (tick :: tick :: tick :: tick :: (KK ++ KK) : List (Fin (A + 4))) = WL by
      simp [hWL]] at e₉
  set S₉ : Stacks T A := { S₈ with R := Function.update S₈.R wL WL } with hS₉
  -- `ONE`
  obtain ⟨v₁₀, hu₁₀, e₁₀⟩ := bzero_exec body (wR := wL) (c := ONE) (t := t₁) (by regs_nodup)
    v₅ S₉ (by simp [*, Ne.symm])
  rw [show S₉.R wL = WL by simp [hS₉], hWLl,
    show S₉.R ONE = [] by simp [*, Ne.symm],
    List.append_nil] at e₁₀
  set S₁₀ : Stacks T A := { S₉ with R := Function.update S₉.R ONE (binSyms (4 * k + 4) 0) }
    with hS₁₀
  have e₁₁ := dropR_exec body ONE v₁₀ S₁₀
  rw [show S₁₀.R ONE = binSyms (4 * k + 4) 0 by simp [hS₁₀]] at e₁₁
  set S₁₁ : Stacks T A :=
    { S₁₀ with R := Function.update S₁₀.R ONE (binSyms (4 * k + 4) 0).tail } with hS₁₁
  have e₁₂ := pushS_exec body ONE (bitSymbol true) v₁₀ S₁₁
  have hone : (bitSymbol true :: (binSyms (4 * k + 4) 0).tail : List (Fin (A + 4))) =
      binSyms (4 * k + 4) 1 := by
    rw [binSyms_one, binSyms_succ, List.tail_cons, Nat.zero_div]
  rw [show S₁₁.R ONE = (binSyms (4 * k + 4) 0).tail by simp [hS₁₁], hone] at e₁₂
  set S₁₂ : Stacks T A := { S₁₁ with R := Function.update S₁₁.R ONE (binSyms (4 * k + 4) 1) }
    with hS₁₂
  -- `SIX`
  have e₁₃ := pushS_exec body SIX (bitSymbol false) v₁₀ S₁₂
  rw [show S₁₂.R SIX = [] by
    simp [*, Ne.symm]] at e₁₃
  set S₁₃ : Stacks T A := { S₁₂ with R := Function.update S₁₂.R SIX [bitSymbol false] }
    with hS₁₃
  have e₁₄ := pushS_exec body SIX (bitSymbol false) v₁₀ S₁₃
  rw [show S₁₃.R SIX = [bitSymbol false] by simp [hS₁₃]] at e₁₄
  set S₁₄ : Stacks T A :=
    { S₁₃ with R := Function.update S₁₃.R SIX [bitSymbol false, bitSymbol false] } with hS₁₄
  have e₁₅ := pushS_exec body SIX (bitSymbol false) v₁₀ S₁₄
  rw [show S₁₄.R SIX = [bitSymbol false, bitSymbol false] by simp [hS₁₄]] at e₁₅
  set S₁₅ : Stacks T A := { S₁₄ with
    R := Function.update S₁₄.R SIX [bitSymbol false, bitSymbol false, bitSymbol false] }
    with hS₁₅
  have e₁₆ := pushS_exec body SIX (bitSymbol true) v₁₀ S₁₅
  rw [show S₁₅.R SIX = [bitSymbol false, bitSymbol false, bitSymbol false] by simp [hS₁₅],
    ← binSyms_four_one] at e₁₆
  set S₁₆ : Stacks T A := { S₁₅ with R := Function.update S₁₅.R SIX (binSyms 4 1) } with hS₁₆
  have hS₁₆w : (S₁₆.R w2K).length = k + k := by
    simp [*]
  have hS₁₆t : S₁₆.R t₁ = [] := by
    simp [*, Ne.symm]
  obtain ⟨v₁₇, hu₁₇, e₁₇⟩ := bzero_exec body (wR := w2K) (c := SIX) (t := t₁) (by regs_nodup)
    v₁₀ S₁₆ hS₁₆t
  rw [hS₁₆w, show S₁₆.R SIX = binSyms 4 1 by simp [hS₁₆]] at e₁₇
  set S₁₇ : Stacks T A :=
    { S₁₆ with R := Function.update S₁₆.R SIX (binSyms (k + k) 0 ++ binSyms 4 1) } with hS₁₇
  obtain ⟨v₁₈, hu₁₈, e₁₈⟩ := bzero_exec body (wR := w2K) (c := SIX) (t := t₁) (by regs_nodup)
    v₁₇ S₁₇ (by simp [hS₁₇, ‹SIX ≠ t₁›.symm, hS₁₆t])
  have hsix : (binSyms (k + k) 0 ++ (binSyms (k + k) 0 ++ binSyms 4 1) : List (Fin (A + 4))) =
      binSyms (4 * k + 4) (2 ^ (4 * k)) := by
    rw [binSyms_zero_right, ← List.append_assoc, ← List.replicate_add, binSyms_shift_pow,
      Nat.mul_one]
    congr 1 <;> ring
  rw [show (S₁₇.R w2K).length = k + k by simp [hS₁₇, ‹w2K ≠ SIX›, hS₁₆w],
    show S₁₇.R SIX = binSyms (k + k) 0 ++ binSyms 4 1 by simp [hS₁₇], hsix] at e₁₈
  refine ⟨v₁₈, _, by rw [hu₁₈, hu₁₇, hu₁₀, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ (Exec.seq e₈ (Exec.seq e₉ (Exec.seq e₁₀ (Exec.seq e₁₁ (Exec.seq e₁₂
        (Exec.seq e₁₃ (Exec.seq e₁₄ (Exec.seq e₁₅ (Exec.seq e₁₆ (Exec.seq e₁₇ e₁₈)))))))))))))))))
    rfl ?_⟩
  · omega
  · clear e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉ e₁₀ e₁₁ e₁₂ e₁₃ e₁₄ e₁₅ e₁₆ e₁₇ e₁₈
    simp only [hS₁₇, hS₁₆, hS₁₅, hS₁₄, hS₁₃, hS₁₂, hS₁₁, hS₁₀, hS₉, hS₈, hS₇, hS₆, hS₅, hS₄,
      hS₃, hS₂, hS₁]
    clear hS₁₇ hS₁₆ hS₁₅ hS₁₄ hS₁₃ hS₁₂ hS₁₁ hS₁₀ hS₉ hS₈ hS₇ hS₆ hS₅ hS₄ hS₃ hS₂ hS₁ hsix hone
      hS₁₆w hS₁₆t
    congr 2
    funext j
    by_cases hjC : j = Cnt
    · subst hjC; simp [*]
    by_cases hj2 : j = w2K
    · subst hj2; simp [*]
    by_cases hjL : j = wL
    · subst hjL; simp [*]
    by_cases hjO : j = ONE
    · subst hjO; simp [*]
    by_cases hj6 : j = SIX
    · subst hj6; simp [*]
    simp [*]

end IntegerMultBounds.MathlibTM2.DFT
