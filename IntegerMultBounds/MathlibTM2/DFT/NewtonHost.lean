module

public import IntegerMultBounds.MathlibTM2.DFT.HenselHost
public import IntegerMultBounds.MathlibTM2.DFT.RedcTail
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Host procedures for the Newton reciprocal

* `bcopyTop_exec`: `bcopyLow s wR d t₁ t₂` copies the top `|wR|` symbols of any register
  `s = l₁ ++ l₂` (`|l₁| = |wR|`) onto `d`, keeping `s`.
* `binSyms_shift_pow`: `|j|` zeros pushed on `binSyms L x` give `binSyms (j + L) (2 ^ j x)`;
  `binSyms_one`: `binSyms (m + 1) 1 = bitSymbol true :: binSyms m 0`.
* `corrLoop R Dd Y ONE Rn Yn t₁ t₂ t₃`: while `R ≥ Dd`, `R := R - Dd` and `Y := Y + 1`
  (`ONE = binSyms L 1`). `corrLoop_exec`: from `R = ρ`, `Dd = d > 0`, `Y = y` in `L` bits it ends
  with `R = ρ mod d` and `Y = y + ρ / d`, in at most `(ρ / d) (44 L + 45) + 8 L + 9` steps.
-/

@[expose] public section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-! ### Copying the top of a register -/

/-- `bcopyLow`: `d` gains the top `|wR|` symbols `l₁` of `s = l₁ ++ l₂`; `s` is kept. -/
theorem bcopyTop_exec {s wR d t₁ t₂ : Fin T} (hreg : [s, wR, d, t₁, t₂].Nodup)
    {l₁ l₂ : List (Fin (A + 4))} (v : HS T Q A U) (S : Stacks T A) (hs : S.R s = l₁ ++ l₂)
    (hw : (S.R wR).length = l₁.length) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (bcopyLow s wR d t₁ t₂) (mk v S) (6 * l₁.length + 6)
        (mk v' { S with R := Function.update S.R d (l₁ ++ S.R d) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, e₁⟩ := scanR_exec' body ‹wR ≠ t₂› (regFx_moveTop ‹s ≠ t₁›)
    (frame_moveTop ‹s ≠ wR›.symm ‹wR ≠ t₁›) (frame_moveTop ‹s ≠ t₂›.symm ‹t₁ ≠ t₂›.symm) v S h₂
  rw [foldl_moveTop ‹s ≠ t₁› _ _ (by rw [hs, hw]; simp), hw, hs, List.drop_left' rfl,
    List.take_left' rfl, h₁, List.append_nil] at e₁
  set S₁ : Stacks T A := { S with
    R := Function.update (Function.update S.R s l₂) t₁ l₁.reverse } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := drainR_exec body t₁ (regFx_dupTo ‹s ≠ d›)
    (frame_dupTo ‹s ≠ t₁›.symm ‹d ≠ t₁›.symm) v₁ S₁
  have hS₁t : S₁.R t₁ = l₁.reverse := by simp [hS₁]
  rw [hS₁t, foldl_dupTo ‹s ≠ d›, List.length_reverse, List.reverse_reverse] at e₂
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq e₁ e₂) (by ring) ?_⟩
  clear e₁ e₂
  simp only [hS₁]
  congr 2
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### Numerals -/

theorem binSyms_shift_pow (j L x : ℕ) :
    List.replicate j (bitSymbol false) ++ (binSyms L x : List (Fin (A + 4))) =
      binSyms (j + L) (2 ^ j * x) := by
  rw [binSyms_append, ← binSyms_mod j (2 ^ j * x), Nat.mul_mod_right, binSyms_zero_right,
    Nat.mul_div_cancel_left _ (by positivity)]

theorem binSyms_one (m : ℕ) :
    (binSyms (m + 1) 1 : List (Fin (A + 4))) = bitSymbol true :: binSyms m 0 := by
  rw [binSyms_succ]
  rfl

/-! ### The correction loop -/

/-- One correction: `R := R - Dd`, `Y := Y + 1`, then slot `Rn` records `R < Dd`. -/
def corrStep (R Dd Y ONE Rn Yn t₁ t₂ t₃ : Fin T) : Pr P T Q A U :=
  .seq (bsub R Dd Rn t₁ t₂ t₃ Rn) (.seq (bclear R) (.seq (bcopy Rn R t₁ t₂) (.seq (bclear Rn)
    (.seq (badd Y ONE Yn t₁ t₂ t₃ Rn) (.seq (bclear Y) (.seq (bcopy Yn Y t₁ t₂) (.seq (bclear Yn)
      (blt R Dd t₁ t₂ t₃ Rn))))))))

/-- Subtract `Dd` from `R` while `R ≥ Dd`, counting in `Y`. -/
def corrLoop (R Dd Y ONE Rn Yn t₁ t₂ t₃ : Fin T) : Pr P T Q A U :=
  .seq (blt R Dd t₁ t₂ t₃ Rn) (.loop (fun v => !slotTrue Rn v) (corrStep R Dd Y ONE Rn Yn t₁ t₂ t₃))

/-- One correction step. -/
theorem corrStep_exec {R Dd Y ONE Rn Yn t₁ t₂ t₃ : Fin T}
    (hreg : [R, Dd, Y, ONE, Rn, Yn, t₁, t₂, t₃].Nodup) {L ρ d y : ℕ} (hdρ : d ≤ ρ)
    (hρ : ρ < 2 ^ L) (hd : d < 2 ^ L) (hy : y + 1 < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hR : S.R R = binSyms L ρ) (hD : S.R Dd = binSyms L d) (hY : S.R Y = binSyms L y)
    (hO : S.R ONE = binSyms L 1) (hRn : S.R Rn = []) (hYn : S.R Yn = []) (h₁ : S.R t₁ = [])
    (h₂ : S.R t₂ = []) (h₃ : S.R t₃ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan Rn = bitSymbol (decide (ρ - d < d)) ∧
      Exec body (corrStep R Dd Y ONE Rn Yn t₁ t₂ t₃) (mk v S) (44 * L + 44)
        (mk v' { S with
          R := Function.update (Function.update S.R R (binSyms L (ρ - d))) Y
            (binSyms L (y + 1)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have h1L : 1 < 2 ^ L := by omega
  -- `Rn := R - Dd`
  obtain ⟨v₁, hu₁, -, -, e₁⟩ := bsub_exec body (a := R) (b := Dd) (c := Rn) (tx := t₁) (ty := t₂)
    (tz := t₃) (cy := Rn) (by regs_nodup) ‹R ≠ Rn›.symm ‹Dd ≠ Rn›.symm hρ hd v S hR hD h₁ h₂ h₃
  have hval : (ρ + 2 ^ L - d) % 2 ^ L = ρ - d := by
    rw [show ρ + 2 ^ L - d = (ρ - d) + 2 ^ L by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  rw [hval, hRn, List.append_nil] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R Rn (binSyms L (ρ - d)) } with hS₁
  obtain ⟨v₂, hu₂, -, e₂⟩ := bclear_exec body R v₁ S₁
  rw [show S₁.R R = binSyms L ρ by simp [hS₁, ‹R ≠ Rn›, hR], length_binSyms] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R R [] } with hS₂
  obtain ⟨v₃, hu₃, e₃⟩ := bcopy_exec body (a := Rn) (c := R) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₂ S₂ (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
  rw [show S₂.R Rn = binSyms L (ρ - d) by simp [hS₂, hS₁, ‹R ≠ Rn›.symm],
    show S₂.R R = [] by simp [hS₂], List.append_nil, length_binSyms] at e₃
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R R (binSyms L (ρ - d)) } with hS₃
  obtain ⟨v₄, hu₄, -, e₄⟩ := bclear_exec body Rn v₃ S₃
  rw [show S₃.R Rn = binSyms L (ρ - d) by simp [hS₃, hS₂, hS₁, ‹R ≠ Rn›.symm],
    length_binSyms] at e₄
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R Rn [] } with hS₄
  -- `Yn := Y + 1`
  obtain ⟨v₅, hu₅, -, -, e₅⟩ := badd_exec body (a := Y) (b := ONE) (c := Yn) (tx := t₁)
    (ty := t₂) (tz := t₃) (cy := Rn) (by regs_nodup) ‹Y ≠ Rn›.symm ‹ONE ≠ Rn›.symm
    (L := L) (x := y) (y := 1) (by omega) h1L v₄ S₄ (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
  rw [Nat.mod_eq_of_lt hy, show S₄.R Yn = [] by simp [*, Ne.symm],
    List.append_nil] at e₅
  set S₅ : Stacks T A := { S₄ with R := Function.update S₄.R Yn (binSyms L (y + 1)) } with hS₅
  obtain ⟨v₆, hu₆, -, e₆⟩ := bclear_exec body Y v₅ S₅
  rw [show S₅.R Y = binSyms L y by simp [*, Ne.symm],
    length_binSyms] at e₆
  set S₆ : Stacks T A := { S₅ with R := Function.update S₅.R Y [] } with hS₆
  obtain ⟨v₇, hu₇, e₇⟩ := bcopy_exec body (a := Yn) (c := Y) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₆ S₆ (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  rw [show S₆.R Yn = binSyms L (y + 1) by simp [hS₆, hS₅, ‹Y ≠ Yn›.symm],
    show S₆.R Y = [] by simp [hS₆], List.append_nil, length_binSyms] at e₇
  set S₇ : Stacks T A := { S₆ with R := Function.update S₆.R Y (binSyms L (y + 1)) } with hS₇
  obtain ⟨v₈, hu₈, -, e₈⟩ := bclear_exec body Yn v₇ S₇
  rw [show S₇.R Yn = binSyms L (y + 1) by simp [hS₇, hS₆, hS₅, ‹Y ≠ Yn›.symm],
    length_binSyms] at e₈
  set S₈ : Stacks T A := { S₇ with R := Function.update S₇.R Yn [] } with hS₈
  -- the test
  obtain ⟨v₉, hu₉, hsc₉, -, e₉⟩ := blt_exec body (a := R) (b := Dd) (tx := t₁) (ty := t₂)
    (tz := t₃) (cy := Rn) (by regs_nodup) ‹R ≠ Rn›.symm ‹Dd ≠ Rn›.symm (L := L) (x := ρ - d)
    (y := d) (by omega) hd v₈ S₈
    (by simp [*])
    (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  refine ⟨v₉, by rw [hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], hsc₉,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ (Exec.seq e₈ e₉)))))))) (by ring) ?_⟩
  clear e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ e₉
  simp only [hS₈, hS₇, hS₆, hS₅, hS₄, hS₃, hS₂, hS₁]
  clear hS₈ hS₇ hS₆ hS₅ hS₄ hS₃ hS₂ hS₁ hval hsc₉
  congr 2
  funext j
  by_cases hjR : j = R
  · subst hjR; simp [*]
  by_cases hjY : j = Y
  · subst hjY; simp [*]
  by_cases hjRn : j = Rn
  · subst hjRn; simp [*, Ne.symm]
  by_cases hjYn : j = Yn
  · subst hjYn; simp [*, Ne.symm]
  simp [*]

/-- The correction loop after its first test. -/
theorem corrLoop_aux {R Dd Y ONE Rn Yn t₁ t₂ t₃ : Fin T}
    (hreg : [R, Dd, Y, ONE, Rn, Yn, t₁, t₂, t₃].Nodup) {L d : ℕ} (hd0 : 0 < d)
    (hd : d < 2 ^ L) :
    ∀ (c ρ y : ℕ) (v : HS T Q A U) (S : Stacks T A), ρ / d = c → ρ < 2 ^ L → y + c < 2 ^ L →
      S.R R = binSyms L ρ → S.R Dd = binSyms L d → S.R Y = binSyms L y →
      S.R ONE = binSyms L 1 → S.R Rn = [] → S.R Yn = [] → S.R t₁ = [] → S.R t₂ = [] →
      S.R t₃ = [] → v.scan Rn = bitSymbol (decide (ρ < d)) →
      ∃ v' : HS T Q A U, ∃ n, v'.user = v.user ∧ n ≤ c * (44 * L + 45) + 1 ∧
        Exec body (.loop (fun v => !slotTrue Rn v) (corrStep R Dd Y ONE Rn Yn t₁ t₂ t₃))
          (mk v S) n
          (mk v' { S with
            R := Function.update (Function.update S.R R (binSyms L (ρ % d))) Y
              (binSyms L (y + c)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  intro c
  induction c with
  | zero =>
    intro ρ y v S hc hρ hy hR hD hY hO hRn hYn h₁ h₂ h₃ hsc
    have hlt : ρ < d := by
      by_contra h
      push Not at h
      have := Nat.div_pos h hd0
      omega
    refine ⟨v, 1, rfl, by omega, ?_⟩
    have hS : ({ S with
        R := Function.update (Function.update S.R R (binSyms L (ρ % d))) Y
          (binSyms L (y + 0)) } : Stacks T A) = S := by
      have hfun : Function.update (Function.update S.R R (binSyms L (ρ % d))) Y
          (binSyms L (y + 0)) = S.R := by
        funext j
        simp only [Function.update_apply, Nat.mod_eq_of_lt hlt, Nat.add_zero]
        split_ifs <;> simp_all
      rw [hfun]
    rw [hS]
    exact .loop_false (by show (!slotTrue Rn v) = false; simp [slotTrue, hsc, hlt])
  | succ c ih =>
    intro ρ y v S hc hρ hy hR hD hY hO hRn hYn h₁ h₂ h₃ hsc
    have hge : d ≤ ρ := by
      by_contra h
      push Not at h
      rw [Nat.div_eq_of_lt h] at hc
      omega
    have hdec : ρ = (ρ - d) + d := by omega
    have hc' : (ρ - d) / d = c := by
      have : ρ / d = (ρ - d) / d + 1 := by
        conv_lhs => rw [hdec]
        rw [Nat.add_div_right _ hd0]
      omega
    have hmod : (ρ - d) % d = ρ % d := by
      conv_rhs => rw [hdec]
      rw [Nat.add_mod_right]
    clear hdec
    obtain ⟨v₁, hu₁, hsc₁, e₁⟩ := corrStep_exec body hreg hge hρ hd (by omega) v S hR hD hY hO
      hRn hYn h₁ h₂ h₃
    set S₁ : Stacks T A := { S with
      R := Function.update (Function.update S.R R (binSyms L (ρ - d))) Y (binSyms L (y + 1)) }
      with hS₁
    obtain ⟨v₂, n₂, hu₂, hn₂, e₂⟩ := ih (ρ - d) (y + 1) v₁ S₁ hc' (by omega) (by omega)
      (by simp [hS₁, ‹R ≠ Y›]) (by simp [*, Ne.symm]) (by simp [hS₁])
      (by simp [*, Ne.symm]) (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
      (by simp [*, Ne.symm]) (by simp [*, Ne.symm]) (by simp [*, Ne.symm]) hsc₁
    have hf : (!slotTrue Rn v) = true := by
      simp [slotTrue, hsc, show ¬ ρ < d by omega, bitSymbol_true_ne_false.symm]
    refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.loop_true hf e₁ (e₂.cast rfl ?_)⟩
    · have : (c + 1) * (44 * L + 45) = c * (44 * L + 45) + (44 * L + 45) := by ring
      omega
    · clear e₁ e₂ ih
      simp only [hS₁, hmod, show y + 1 + c = y + (c + 1) by ring]
      congr 2
      funext j
      simp only [Function.update_apply]
      split_ifs <;> simp_all

/-- `corrLoop`: `R := ρ mod d`, `Y := y + ρ / d`. -/
theorem corrLoop_exec {R Dd Y ONE Rn Yn t₁ t₂ t₃ : Fin T}
    (hreg : [R, Dd, Y, ONE, Rn, Yn, t₁, t₂, t₃].Nodup) {L ρ d y : ℕ} (hd0 : 0 < d)
    (hd : d < 2 ^ L) (hρ : ρ < 2 ^ L) (hy : y + ρ / d < 2 ^ L) (v : HS T Q A U)
    (S : Stacks T A) (hR : S.R R = binSyms L ρ) (hD : S.R Dd = binSyms L d)
    (hY : S.R Y = binSyms L y) (hO : S.R ONE = binSyms L 1) (hRn : S.R Rn = [])
    (hYn : S.R Yn = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) (h₃ : S.R t₃ = []) :
    ∃ v' : HS T Q A U, ∃ n, v'.user = v.user ∧ n ≤ ρ / d * (44 * L + 45) + 8 * L + 9 ∧
      Exec body (corrLoop R Dd Y ONE Rn Yn t₁ t₂ t₃) (mk v S) n
        (mk v' { S with
          R := Function.update (Function.update S.R R (binSyms L (ρ % d))) Y
            (binSyms L (y + ρ / d)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, hsc₁, -, e₁⟩ := blt_exec body (a := R) (b := Dd) (tx := t₁) (ty := t₂)
    (tz := t₃) (cy := Rn) (by regs_nodup) ‹R ≠ Rn›.symm ‹Dd ≠ Rn›.symm hρ hd v S hR hD h₁ h₂ h₃
  obtain ⟨v₂, n₂, hu₂, hn₂, e₂⟩ := corrLoop_aux body hreg hd0 hd (ρ / d) ρ y v₁ S rfl hρ hy hR hD
    hY hO hRn hYn h₁ h₂ h₃ hsc₁
  exact ⟨v₂, _, by rw [hu₂, hu₁], by omega, Exec.seq e₁ e₂⟩

end IntegerMultBounds.MathlibTM2.DFT
