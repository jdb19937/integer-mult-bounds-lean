module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-!
# Low and high parts of a binary register

For a register holding `binSyms (r + e) X` and a width register of `r` symbols:

* `btrunc a wR t₁ t₂` keeps the low part: `a := binSyms r X` (`btrunc_exec`,
  `6 r + 2 e + 8` steps). The top `r` symbols of `a` move onto `t₁` (`moveTop`, one per symbol
  of `wR`, `scanR`), the rest of `a` is cleared, and `t₁` moves back.
* `usub wR a t` (`Node/Params.lean`) keeps the high part: `a := binSyms e (X / 2 ^ r)`
  (`bhigh_exec`).
-/

@[expose] public section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Pop register `b` onto register `c`, then continue with `k`. -/
def moveTop (b c : Fin T) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt b) (fun v o => { v with sym := o }) (.push (.rt c) (fun v => v.sym.getD blank) k)

/-- The effect of `moveTop b c` on the registers. -/
def moveTopFx (b c : Fin T) : Fin (A + 4) → (Fin T → List (Fin (A + 4))) →
    Fin T → List (Fin (A + 4)) :=
  fun _ R => Function.update (Function.update R b (R b).tail) c ((R b).head?.getD blank :: R c)

lemma regFx_moveTop {b c : Fin T} (hbc : b ≠ c) :
    RegFx (moveTop (T := T) (Q := Q) (A := A) (U := U) b c) (moveTopFx b c) := by
  intro x k v S _
  refine ⟨{ v with sym := (S.R b).head? }, rfl, ?_⟩
  simp [moveTop, moveTopFx, Action.run, update_rt, Function.update_of_ne hbc.symm]

lemma frame_moveTop {a b c : Fin T} (hab : a ≠ b) (hac : a ≠ c) :
    Frame a (moveTopFx (A := A) b c) := by
  intro x R l
  simp only [moveTopFx, Function.update_of_ne hab.symm, Function.update_of_ne hac.symm]
  rw [Function.update_comm hab, Function.update_comm hac]

lemma foldl_moveTop {b c : Fin T} (hbc : b ≠ c) :
    ∀ (l : List (Fin (A + 4))) (R : Fin T → List (Fin (A + 4))), l.length ≤ (R b).length →
      l.foldl (fun R x => moveTopFx b c x R) R =
        Function.update (Function.update R b ((R b).drop l.length)) c
          (((R b).take l.length).reverse ++ R c)
  | [], R, _ => by simp
  | x :: rest, R, hl => by
      obtain ⟨y, ys, hy⟩ : ∃ y ys, R b = y :: ys := by
        cases h : R b with
        | nil => simp [h] at hl
        | cons y ys => exact ⟨y, ys, rfl⟩
      have hR' : moveTopFx b c x R b = ys := by
        simp [moveTopFx, Function.update_of_ne hbc, hy]
      simp only [List.foldl_cons]
      rw [foldl_moveTop hbc rest _ (by rw [hR']; simp [hy] at hl; omega), hR']
      funext k
      simp only [moveTopFx, Function.update_apply, hy]
      split_ifs <;> simp_all

/-- Keep the low part: the top `|wR|` symbols of `a` move onto `t₁` through `t₂`, `a` is
cleared, and `t₁` moves back. -/
def btrunc (a wR t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (scanR wR t₂ (moveTop a t₁)) (.seq (bclear a) (moveR t₁ a id))

/-- `btrunc`: `a := binSyms r X` from `binSyms (r + e) X`, for `|wR| = r`. -/
theorem btrunc_exec {a wR t₁ t₂ : Fin T} (hreg : [a, wR, t₁, t₂].Nodup) {r e X : ℕ}
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms (r + e) X)
    (hw : (S.R wR).length = r) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (btrunc a wR t₁ t₂) (mk v S) (6 * r + 2 * e + 8)
        (mk v' { S with R := Function.update S.R a (binSyms r X) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, e₁⟩ := scanR_exec' body ‹wR ≠ t₂› (regFx_moveTop ‹a ≠ t₁›)
    (frame_moveTop ‹a ≠ wR›.symm ‹wR ≠ t₁›) (frame_moveTop ‹a ≠ t₂›.symm ‹t₁ ≠ t₂›.symm) v S h₂
  have hsplit : (binSyms (r + e) X : List (Fin (A + 4))) = binSyms r X ++ binSyms e (X / 2 ^ r) :=
    binSyms_append r e X
  rw [foldl_moveTop ‹a ≠ t₁› _ _ (by rw [ha, hw]; simp), hw, ha, hsplit,
    List.drop_left' (length_binSyms r X), List.take_left' (length_binSyms r X), h₁,
    List.append_nil] at e₁
  set S₁ : Stacks T A := { S with
    R := Function.update (Function.update S.R a (binSyms e (X / 2 ^ r))) t₁
      (binSyms r X).reverse } with hS₁
  obtain ⟨v₂, hu₂, -, e₂⟩ := bclear_exec body a v₁ S₁
  have hS₁a : S₁.R a = binSyms e (X / 2 ^ r) := by simp [hS₁, ‹a ≠ t₁›]
  rw [hS₁a, length_binSyms] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R a [] } with hS₂
  obtain ⟨v₃, hu₃, e₃⟩ := moveR_exec body t₁ a ‹a ≠ t₁›.symm id v₂ S₂
  have hS₂t : S₂.R t₁ = (binSyms r X).reverse := by simp [hS₂, hS₁, ‹a ≠ t₁›.symm]
  rw [hS₂t, List.length_reverse, length_binSyms] at e₃
  refine ⟨v₃, by rw [hu₃, hu₂, hu₁], Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₃)) (by ring) ?_⟩
  clear e₁ e₂ e₃
  simp only [hS₂, hS₁]
  congr 2
  funext k
  simp only [movedR, Function.update_apply, List.map_id, List.reverse_reverse]
  split_ifs <;> simp_all

/-- `usub wR a t` keeps the high part: `a := binSyms e (X / 2 ^ r)` from `binSyms (r + e) X`,
for `|wR| = r`. -/
theorem bhigh_exec {a wR t : Fin T} (hreg : [a, wR, t].Nodup) {r e X : ℕ} (v : HS T Q A U)
    (S : Stacks T A) (ha : S.R a = binSyms (r + e) X) (hw : (S.R wR).length = r)
    (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (usub wR a t) (mk v S) (4 * r + 4)
        (mk v' { S with R := Function.update S.R a (binSyms e (X / 2 ^ r)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v', hu, h⟩ := usub_exec body ‹a ≠ wR›.symm ‹wR ≠ t› ‹a ≠ t› v S ht
  rw [hw, ha, binSyms_append, List.drop_left' (length_binSyms r X)] at h
  exact ⟨v', hu, h⟩

end IntegerMultBounds.MathlibTM2.DFT
