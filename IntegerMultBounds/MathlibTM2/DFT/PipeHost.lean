module

public import IntegerMultBounds.MathlibTM2.DFT.Barrett
public import IntegerMultBounds.MathlibTM2.DFT.Parse
public import IntegerMultBounds.MathlibTM2.DFT.PipeMath
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Host blocks of the pipeline

* `dropField F Ft Fu` (`dropField_exec`): register `F` loses its first field.
* `pushWide C Cw w3 Wc V t₁ t₂` (`pushWide_exec`): `V := (binSyms s c).reverse ++ V` from
  `C = binSyms w c`, `|w3| = s` (`bcopy`, `bwiden`, `moveR`); `C` is kept.
* `pushBlock O Ow w3 Wc Up t₁ t₂` (`pushBlock_exec`): `Up := binSyms s x ++ Up` from
  `O = binSyms w x` (`bcopy`, `bwiden`, `bcopy`, `bclear`); `O` is kept.
* `moveBack O C t₁ t₂` (`moveBack_exec`): `C := O`, `O := []`.
* `copyOver E W t₁ t₂` (`copyOver_exec`): `W := E`.
* `setOne C Pw t` (`setOne_exec`): `C := binSyms w 1` for `|Pw| = w ≥ 1`.
* `splitLow a wR d t₁ t₂` (`splitLow_exec`): the low `|wR|` bits of `a` move onto the empty
  register `d`, in order.
-/

@[expose] public section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-! ### Fields -/

/-- Drop the first field of `F`. -/
def dropField (F Ft Fu : Fin T) : Pr P T Q A U := .seq (takeField F Ft Fu) (bclear Ft)

theorem dropField_exec {F Ft Fu : Fin T} (hreg : [F, Ft, Fu].Nodup) {w x : ℕ} {l : List ℕ}
    (v : HS T Q A U) (S : Stacks T A) (hF : S.R F = fieldSyms w (x :: l)) (hFt : S.R Ft = [])
    (hFu : S.R Fu = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (dropField F Ft Fu) (mk v S) (6 * w + 7)
        (mk v' { S with R := Function.update S.R F (fieldSyms w l) }) := by
  have hreg' := hreg
  regs_ne hreg'
  rw [fieldSyms_cons] at hF
  obtain ⟨v₁, hu₁, e₁⟩ := takeField_exec body ‹F ≠ Ft› ‹F ≠ Fu› ‹Ft ≠ Fu›
    (separator_not_mem_binSyms w x) v S hF hFu hFt
  rw [length_binSyms] at e₁
  set S₁ : Stacks T A := { S with
    R := Function.update (Function.update S.R F (fieldSyms w l)) Ft (binSyms w x) } with hS₁
  obtain ⟨v₂, hu₂, -, e₂⟩ := bclear_exec body Ft v₁ S₁
  rw [show (S₁.R Ft).length = w by simp [hS₁]] at e₂
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq e₁ e₂) (by ring) ?_⟩
  clear e₁ e₂
  simp only [hS₁]
  congr 2
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### Packed registers -/

/-- `V := (binSyms s c).reverse ++ V`; `C` is kept. -/
def pushWide (C Cw w3 Wc V t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bcopy C Cw t₁ t₂) (.seq (bwiden Cw w3 Wc t₁ t₂) (moveR Cw V id))

theorem pushWide_exec {C Cw w3 Wc V t₁ t₂ : Fin T} (hreg : [C, Cw, w3, Wc, V, t₁, t₂].Nodup)
    {w s c : ℕ} (hws : w ≤ s) (hc : c < 2 ^ w) (v : HS T Q A U) (S : Stacks T A)
    (hC : S.R C = binSyms w c) (hw3 : (S.R w3).length = s) (hCw : S.R Cw = [])
    (hWc : S.R Wc = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (pushWide C Cw w3 Wc V t₁ t₂) (mk v S) (6 * w + 14 * s + 26)
        (mk v' { S with R := Function.update S.R V ((binSyms s c).reverse ++ S.R V) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, e₁⟩ := bcopy_exec body (a := C) (c := Cw) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v S h₁ h₂
  rw [hC, hCw, List.append_nil, length_binSyms] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R Cw (binSyms w c) } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := bwiden_exec body (a := Cw) (wR := w3) (cnt := Wc) (t₁ := t₁)
    (t₂ := t₂) (by regs_nodup) hws hc v₁ S₁ (by simp [hS₁]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R Cw (binSyms s c) } with hS₂
  obtain ⟨v₃, hu₃, e₃⟩ := moveR_exec body Cw V ‹Cw ≠ V› id v₂ S₂
  rw [show S₂.R Cw = binSyms s c by simp [hS₂], length_binSyms] at e₃
  refine ⟨v₃, by rw [hu₃, hu₂, hu₁], Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₃)) (by ring) ?_⟩
  clear e₁ e₂ e₃
  simp only [hS₂, hS₁]
  congr 2
  funext j
  simp only [movedR, Function.update_apply, List.map_id]
  split_ifs <;> simp_all

/-- `Up := binSyms s x ++ Up`; `O` is kept. -/
def pushBlock (O Ow w3 Wc Up t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bcopy O Ow t₁ t₂) (.seq (bwiden Ow w3 Wc t₁ t₂) (.seq (bcopy Ow Up t₁ t₂) (bclear Ow)))

theorem pushBlock_exec {O Ow w3 Wc Up t₁ t₂ : Fin T} (hreg : [O, Ow, w3, Wc, Up, t₁, t₂].Nodup)
    {w s x : ℕ} (hws : w ≤ s) (hx : x < 2 ^ w) (v : HS T Q A U) (S : Stacks T A)
    (hO : S.R O = binSyms w x) (hw3 : (S.R w3).length = s) (hOw : S.R Ow = [])
    (hWc : S.R Wc = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (pushBlock O Ow w3 Wc Up t₁ t₂) (mk v S) (6 * w + 20 * s + 32)
        (mk v' { S with R := Function.update S.R Up (binSyms s x ++ S.R Up) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, e₁⟩ := bcopy_exec body (a := O) (c := Ow) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v S h₁ h₂
  rw [hO, hOw, List.append_nil, length_binSyms] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R Ow (binSyms w x) } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := bwiden_exec body (a := Ow) (wR := w3) (cnt := Wc) (t₁ := t₁)
    (t₂ := t₂) (by regs_nodup) hws hx v₁ S₁ (by simp [hS₁]) (by simp [hS₁, *, Ne.symm])
    (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R Ow (binSyms s x) } with hS₂
  obtain ⟨v₃, hu₃, e₃⟩ := bcopy_exec body (a := Ow) (c := Up) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₂ S₂ (by simp [hS₂, hS₁, *, Ne.symm]) (by simp [hS₂, hS₁, *, Ne.symm])
  rw [show S₂.R Ow = binSyms s x by simp [hS₂], show S₂.R Up = S.R Up by
    simp [hS₂, hS₁, *, Ne.symm], length_binSyms] at e₃
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R Up (binSyms s x ++ S.R Up) } with hS₃
  obtain ⟨v₄, hu₄, -, e₄⟩ := bclear_exec body Ow v₃ S₃
  rw [show (S₃.R Ow).length = s by simp [hS₃, hS₂, ‹Ow ≠ Up›]] at e₄
  refine ⟨v₄, by rw [hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ e₄)))
    (by ring) ?_⟩
  clear e₁ e₂ e₃ e₄
  simp only [hS₃, hS₂, hS₁]
  congr 2
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### Copies -/

/-- `C := O`, `O := []`. -/
def moveBack (O C t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (bclear C) (.seq (bcopy O C t₁ t₂) (bclear O))

theorem moveBack_exec {O C t₁ t₂ : Fin T} (hreg : [O, C, t₁, t₂].Nodup) {w : ℕ}
    (v : HS T Q A U) (S : Stacks T A) (hC : (S.R C).length = w) (hO : (S.R O).length = w)
    (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (moveBack O C t₁ t₂) (mk v S) (10 * w + 10)
        (mk v' { S with R := Function.update (Function.update S.R C (S.R O)) O [] }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, -, e₁⟩ := bclear_exec body C v S
  rw [hC] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R C [] } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := bcopy_exec body (a := O) (c := C) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₁ S₁ (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
  rw [show S₁.R O = S.R O by simp [hS₁, *, Ne.symm], show S₁.R C = [] by simp [hS₁], hO,
    List.append_nil] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R C (S.R O) } with hS₂
  obtain ⟨v₃, hu₃, -, e₃⟩ := bclear_exec body O v₂ S₂
  rw [show (S₂.R O).length = w by simp [hS₂, hS₁, *, Ne.symm]] at e₃
  refine ⟨v₃, by rw [hu₃, hu₂, hu₁], Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₃)) (by ring) ?_⟩
  clear e₁ e₂ e₃
  simp only [hS₂, hS₁]
  congr 2
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- `W := E`. -/
def copyOver (E W t₁ t₂ : Fin T) : Pr P T Q A U := .seq (bclear W) (bcopy E W t₁ t₂)

theorem copyOver_exec {E W t₁ t₂ : Fin T} (hreg : [E, W, t₁, t₂].Nodup) {w w' : ℕ}
    (v : HS T Q A U) (S : Stacks T A) (hW : (S.R W).length = w') (hE : (S.R E).length = w)
    (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (copyOver E W t₁ t₂) (mk v S) (2 * w' + 6 * w + 8)
        (mk v' { S with R := Function.update S.R W (S.R E) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, -, e₁⟩ := bclear_exec body W v S
  rw [hW] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R W [] } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := bcopy_exec body (a := E) (c := W) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) v₁ S₁ (by simp [hS₁, *, Ne.symm]) (by simp [hS₁, *, Ne.symm])
  rw [show S₁.R E = S.R E by simp [hS₁, *, Ne.symm], show S₁.R W = [] by simp [hS₁], hE,
    List.append_nil] at e₂
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq e₁ e₂) (by ring) ?_⟩
  clear e₁ e₂
  simp only [hS₁]
  congr 2
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- `C := binSyms w 1` for `|Pw| = w`. -/
def setOne (C Pw t : Fin T) : Pr P T Q A U :=
  .seq (bzero Pw C t) (.seq (.act (dropR C)) (pushS C (bitSymbol true)))

theorem setOne_exec {C Pw t : Fin T} (hreg : [C, Pw, t].Nodup) {w : ℕ} (hw : 1 ≤ w)
    (v : HS T Q A U) (S : Stacks T A) (hPw : (S.R Pw).length = w) (hC : S.R C = [])
    (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (setOne C Pw t) (mk v S) (4 * w + 6)
        (mk v' { S with R := Function.update S.R C (binSyms w 1) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, e₁⟩ := bzero_exec body (wR := Pw) (c := C) (t := t) (by regs_nodup) v S ht
  rw [hPw, hC, List.append_nil] at e₁
  set S₁ : Stacks T A := { S with R := Function.update S.R C (binSyms w 0) } with hS₁
  have e₂ := Exec.act (body := body) (dropR C) (mk v₁ S₁)
  rw [dropR_run, show S₁.R C = binSyms w 0 by simp [hS₁]] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R C (binSyms w 0).tail } with hS₂
  have e₃ := pushS_exec body C (bitSymbol true) v₁ S₂
  have hone : (bitSymbol true :: (binSyms w 0).tail : List (Fin (A + 4))) = binSyms w 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
    rw [binSyms_one, binSyms_zero_right, binSyms_zero_right, List.replicate_succ,
      List.tail_cons]
  rw [show S₂.R C = (binSyms w 0).tail by simp [hS₂], hone] at e₃
  refine ⟨v₁, hu₁, Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₃)) (by ring) ?_⟩
  clear e₁ e₂ e₃
  simp only [hS₂, hS₁]
  congr 2
  funext j
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### The low bits of a register -/

/-- The low `|wR|` bits of `a` onto `d`. -/
def splitLow (a wR d t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (scanR wR t₂ (moveTop a t₁)) (moveR t₁ d id)

theorem splitLow_exec {a wR d t₁ t₂ : Fin T} (hreg : [a, wR, d, t₁, t₂].Nodup) {r e X : ℕ}
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms (r + e) X)
    (hw : (S.R wR).length = r) (hd : S.R d = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (splitLow a wR d t₁ t₂) (mk v S) (6 * r + 6)
        (mk v' { S with
          R := Function.update (Function.update S.R a (binSyms e (X / 2 ^ r))) d
            (binSyms r X) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, e₁⟩ := scanR_exec' body ‹wR ≠ t₂› (regFx_moveTop ‹a ≠ t₁›)
    (frame_moveTop ‹a ≠ wR›.symm ‹wR ≠ t₁›) (frame_moveTop ‹a ≠ t₂›.symm ‹t₁ ≠ t₂›.symm) v S h₂
  rw [foldl_moveTop ‹a ≠ t₁› _ _ (by rw [ha, hw]; simp), hw, ha, binSyms_append r e X,
    List.drop_left' (length_binSyms r X), List.take_left' (length_binSyms r X), h₁,
    List.append_nil] at e₁
  set S₁ : Stacks T A := { S with
    R := Function.update (Function.update S.R a (binSyms e (X / 2 ^ r))) t₁
      (binSyms r X).reverse } with hS₁
  obtain ⟨v₂, hu₂, e₂⟩ := moveR_exec body t₁ d ‹d ≠ t₁›.symm id v₁ S₁
  rw [show S₁.R t₁ = (binSyms r X).reverse by simp [hS₁], List.length_reverse,
    length_binSyms] at e₂
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq e₁ e₂) (by ring) ?_⟩
  clear e₁ e₂
  simp only [hS₁]
  congr 2
  funext j
  simp only [movedR, Function.update_apply, List.map_id, List.reverse_reverse]
  split_ifs <;> simp_all

end IntegerMultBounds.MathlibTM2.DFT
