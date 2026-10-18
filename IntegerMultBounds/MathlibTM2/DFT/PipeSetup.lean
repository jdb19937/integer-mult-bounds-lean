module

public import IntegerMultBounds.MathlibTM2.DFT.PipeHost
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The host steps between the loops of the pipeline

* `widths Pw WR W3 t₁ t₂` (`widths_exec`): `WR := Pw ++ Pw`, `W3 := Pw ++ Pw ++ Pw`.
* `prepA Ent F C E Wi Pw t₁ t₂` (`prepA_exec`): `F := Ent`, `C`, `E`, `Wi := binSyms w 1`.
* `restartCE C E Pw t₁` (`restartCE_exec`): `C`, `E := binSyms w 1` over `w`-bit values.
* `prepP Up Dw W3 t₁ t₂` (`prepP_exec`): `Dw := Up`, then `s` zeros pushed onto `Up`.
-/

@[expose] public section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- `WR := Pw ++ Pw`, `W3 := Pw ++ Pw ++ Pw`. -/
def widths (Pw WR W3 t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bcopy Pw WR t₁ t₂) (.seq (bcopy Pw WR t₁ t₂) (.seq (bcopy Pw W3 t₁ t₂)
    (.seq (bcopy Pw W3 t₁ t₂) (bcopy Pw W3 t₁ t₂))))

theorem widths_exec {Pw WR W3 t₁ t₂ : Fin T} (hreg : [Pw, WR, W3, t₁, t₂].Nodup) {w : ℕ}
    (v : HS T Q A U) (S : Stacks T A) (hPw : (S.R Pw).length = w) (hWR : S.R WR = [])
    (hW3 : S.R W3 = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (widths Pw WR W3 t₁ t₂) (mk v S) (30 * w + 30)
        (mk v' { S with
          R := Function.update (Function.update S.R WR (S.R Pw ++ S.R Pw)) W3
            (S.R Pw ++ (S.R Pw ++ S.R Pw)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, e₁⟩ := bcopy_exec body (a := Pw) (c := WR) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v S h₁ h₂
  rw [hWR, List.append_nil, hPw] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R WR (S.R Pw) } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := bcopy_exec body (a := Pw) (c := WR) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₁ S₁ (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
  rw [show S₁.R Pw = S.R Pw by simp [*], show S₁.R WR = S.R Pw by simp [hS₁],
    hPw] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R WR (S.R Pw ++ S.R Pw) } with hS₂
  obtain ⟨v₃, hu₃, e₃⟩ := bcopy_exec body (a := Pw) (c := W3) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₂ S₂ (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
  rw [show S₂.R Pw = S.R Pw by simp [*],
    show S₂.R W3 = [] by simp [*, Ne.symm], List.append_nil, hPw] at e₃
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R W3 (S.R Pw) } with hS₃
  obtain ⟨v₄, hu₄, e₄⟩ := bcopy_exec body (a := Pw) (c := W3) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₃ S₃ (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  rw [show S₃.R Pw = S.R Pw by simp [*],
    show S₃.R W3 = S.R Pw by simp [hS₃], hPw] at e₄
  set S₄ : Stacks T A := { S₃ with R := Function.update S₃.R W3 (S.R Pw ++ S.R Pw) } with hS₄
  obtain ⟨v₅, hu₅, e₅⟩ := bcopy_exec body (a := Pw) (c := W3) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₄ S₄ (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  rw [show S₄.R Pw = S.R Pw by simp [*],
    show S₄.R W3 = S.R Pw ++ S.R Pw by simp [hS₄], hPw] at e₅
  refine ⟨v₅, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃
    (Exec.seq e₄ e₅)))) (by ring) ?_⟩
  clear e₁ e₂ e₃ e₄ e₅
  simp only [hS₄, hS₃, hS₂, hS₁]
  congr 2
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- `F := Ent`; `C`, `E`, `Wi := binSyms w 1`. -/
def prepA (Ent F C E Wi Pw t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bcopy Ent F t₁ t₂) (.seq (setOne C Pw t₁) (.seq (setOne E Pw t₁) (setOne Wi Pw t₁)))

theorem prepA_exec {Ent F C E Wi Pw t₁ t₂ : Fin T} (hreg : [Ent, F, C, E, Wi, Pw, t₁, t₂].Nodup)
    {w : ℕ} (hw : 1 ≤ w) (v : HS T Q A U) (S : Stacks T A) (hPw : (S.R Pw).length = w)
    (hF : S.R F = []) (hC : S.R C = []) (hE : S.R E = []) (hWi : S.R Wi = [])
    (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (prepA Ent F C E Wi Pw t₁ t₂) (mk v S) (6 * (S.R Ent).length + 12 * w + 24)
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update S.R F
            (S.R Ent)) C (binSyms w 1)) E (binSyms w 1)) Wi (binSyms w 1) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, e₁⟩ := bcopy_exec body (a := Ent) (c := F) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v S h₁ h₂
  rw [hF, List.append_nil] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R F (S.R Ent) } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := setOne_exec body (C := C) (Pw := Pw) (t := t₁) (by regs_nodup) hw v₁ S₁
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R C (binSyms w 1) } with hS₂
  obtain ⟨v₃, hu₃, e₃⟩ := setOne_exec body (C := E) (Pw := Pw) (t := t₁) (by regs_nodup) hw v₂ S₂
    (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R E (binSyms w 1) } with hS₃
  obtain ⟨v₄, hu₄, e₄⟩ := setOne_exec body (C := Wi) (Pw := Pw) (t := t₁) (by regs_nodup) hw v₃
    S₃ (by simp [*, Ne.symm]) (by simp [*, Ne.symm])
    (by simp [*, Ne.symm])
  exact ⟨v₄, by rw [hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ e₄)))
    (by ring) rfl⟩

/-- `C`, `E := binSyms w 1` over `w`-bit values. -/
def restartCE (C E Pw t₁ : Fin T) : Pr P T Q A U :=
  .seq (bclear C) (.seq (setOne C Pw t₁) (.seq (bclear E) (setOne E Pw t₁)))

theorem restartCE_exec {C E Pw t₁ : Fin T} (hreg : [C, E, Pw, t₁].Nodup) {w : ℕ} (hw : 1 ≤ w)
    (v : HS T Q A U) (S : Stacks T A) (hPw : (S.R Pw).length = w) (hC : (S.R C).length = w)
    (hE : (S.R E).length = w) (h₁ : S.R t₁ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (restartCE C E Pw t₁) (mk v S) (12 * w + 16)
        (mk v' { S with
          R := Function.update (Function.update S.R C (binSyms w 1)) E (binSyms w 1) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, -, e₁⟩ := bclear_exec body C v S
  rw [hC] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R C [] } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := setOne_exec body (C := C) (Pw := Pw) (t := t₁) (by regs_nodup) hw v₁ S₁
    (by simp [*, Ne.symm]) (by simp [hS₁]) (by simp [*, Ne.symm])
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R C (binSyms w 1) } with hS₂
  obtain ⟨v₃, hu₃, -, e₃⟩ := bclear_exec body E v₂ S₂
  rw [show (S₂.R E).length = w by simp [*, Ne.symm]] at e₃
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R E [] } with hS₃
  obtain ⟨v₄, hu₄, e₄⟩ := setOne_exec body (C := E) (Pw := Pw) (t := t₁) (by regs_nodup) hw v₃
    S₃ (by simp [*, Ne.symm]) (by simp [hS₃]) (by simp [*, Ne.symm])
  refine ⟨v₄, by rw [hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ e₄)))
    (by ring) ?_⟩
  clear e₁ e₂ e₃ e₄
  simp only [hS₃, hS₂, hS₁]
  congr 2
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- `Dw := Up`, then `|W3|` zeros onto `Up`. -/
def prepP (Up Dw W3 t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bcopy Up Dw t₁ t₂) (bzero W3 Up t₁)

theorem prepP_exec {Up Dw W3 t₁ t₂ : Fin T} (hreg : [Up, Dw, W3, t₁, t₂].Nodup) {s : ℕ}
    (v : HS T Q A U) (S : Stacks T A) (hW3 : (S.R W3).length = s) (hDw : S.R Dw = [])
    (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (prepP Up Dw W3 t₁ t₂) (mk v S) (6 * (S.R Up).length + 4 * s + 10)
        (mk v' { S with
          R := Function.update (Function.update S.R Dw (S.R Up)) Up
            (binSyms s 0 ++ S.R Up) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, e₁⟩ := bcopy_exec body (a := Up) (c := Dw) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v S h₁ h₂
  rw [hDw, List.append_nil] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R Dw (S.R Up) } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := bzero_exec body (wR := W3) (c := Up) (t := t₁) (by regs_nodup) v₁ S₁
    (by simp [*, Ne.symm])
  rw [show (S₁.R W3).length = s by simp [*, Ne.symm],
    show S₁.R Up = S.R Up by simp [*]] at e₂
  exact ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq e₁ e₂) (by ring) rfl⟩

end IntegerMultBounds.MathlibTM2.DFT
