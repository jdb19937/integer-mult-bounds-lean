module

public import IntegerMultBounds.MathlibTM2.Layer.PackedXor

/-!
# Record streams on the packed rectangle

A stream holds the records of the rectangle `[N₀] × [2^L] × [N₁] × [2^L] × [N₂] × [2^L] × [N₃]`
in rank order (`PackedXor.rank`). An instruction of the packed program (`PackedXor.Instr`) moves
the record at physical address `(s, c)` to `(s, run c)`; `rankPerm P` is the resulting map of
ranks for an instruction list and `moveRecs π l` is the stream after moving the record at rank
`a` to rank `π a`. Machine passes are specified by `moveRecs (rankPerm [i])`, and a program by
composing them (`moveRecs_rankPerm_append`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Layer.PackedXor

variable (N₀ N₁ N₂ N₃ L K ρ n : ℕ)

/-- One instruction as a permutation of slot triples. -/
noncomputable def instrPerm : Instr → Equiv.Perm (Tri L)
  | .swap a b => Equiv.arrowCongr (Equiv.swap a b) (Equiv.refl _)
  | .rot neg b => crotPerm L 2 0 1 (fun c₀ c₁ => sgn neg * offMag K ρ n b c₀ c₁) (by decide) (by decide)

theorem instrPerm_apply (i : Instr) (c : Tri L) : instrPerm L K ρ n i c = i.run L K ρ n c := by
  cases i with
  | swap a b =>
    funext k
    simp [instrPerm, Instr.run, Equiv.arrowCongr_apply]
  | rot neg b => rfl

/-- A program as a permutation of slot triples, head first. -/
noncomputable def progPerm : List Instr → Equiv.Perm (Tri L)
  | [] => Equiv.refl _
  | i :: P => (instrPerm L K ρ n i).trans (progPerm P)

theorem progPerm_apply (P : List Instr) (c : Tri L) : progPerm L K ρ n P c = runProg L K ρ n P c := by
  induction P generalizing c with
  | nil => rfl
  | cons i P ih =>
    simp only [progPerm, Equiv.trans_apply, ih, instrPerm_apply, runProg, List.foldl_cons]

/-- The map of ranks of a program on the rectangle. -/
noncomputable def rankPerm (P : List Instr) : Equiv.Perm (Fin (rectSize N₀ N₁ N₂ N₃ L)) :=
  (rankEquiv N₀ N₁ N₂ N₃ L).symm.trans
    ((liftA N₀ N₁ N₂ N₃ L (progPerm L K ρ n P)).trans (rankEquiv N₀ N₁ N₂ N₃ L))

/-- The stream after moving the record at rank `a` to rank `π a`. -/
def moveRecs {α : Type*} {M : ℕ} (π : Equiv.Perm (Fin M)) (l : List (List α)) : List (List α) :=
  List.ofFn fun j : Fin M => l.getD (π.symm j) []

theorem length_moveRecs {α : Type*} {M : ℕ} (π : Equiv.Perm (Fin M)) (l : List (List α)) :
    (moveRecs π l).length = M := by
  simp [moveRecs]

theorem moveRecs_trans {α : Type*} {M : ℕ} (π π' : Equiv.Perm (Fin M)) (l : List (List α))
    (hl : l.length = M) : moveRecs (π.trans π') l = moveRecs π' (moveRecs π l) := by
  subst hl
  apply List.ext_getElem (by simp [length_moveRecs])
  intro j h1 h2
  simp [moveRecs, List.getD_eq_getElem?_getD]

theorem rankPerm_append (P P' : List Instr) :
    rankPerm N₀ N₁ N₂ N₃ L K ρ n (P ++ P') =
      (rankPerm N₀ N₁ N₂ N₃ L K ρ n P).trans (rankPerm N₀ N₁ N₂ N₃ L K ρ n P') := by
  ext x
  simp only [rankPerm, Equiv.trans_apply, Equiv.symm_apply_apply, liftA,
    Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map, progPerm_apply, runProg_append]

theorem moveRecs_rankPerm_append {α : Type*} (P P' : List Instr) (l : List (List α))
    (hl : l.length = rectSize N₀ N₁ N₂ N₃ L) :
    moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ n (P ++ P')) l =
      moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ n P') (moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ n P) l) := by
  rw [rankPerm_append, moveRecs_trans _ _ _ hl]

/-- The packed program on ranks: the record at `enc σ a` moves to `enc σ (S₀ a)`. -/
theorem rankPerm_prog (f : ℕ) (σ : Equiv.Perm (Fin 3)) (a : Addr N₀ N₁ N₂ N₃ L) :
    rankPerm N₀ N₁ N₂ N₃ L K ρ (f - 1) (prog σ) (enc N₀ N₁ N₂ N₃ L σ a) =
      enc N₀ N₁ N₂ N₃ L σ (liftA N₀ N₁ N₂ N₃ L (packedS L K ρ f) a) := by
  rw [← prog_rank]
  simp only [rankPerm, enc, Equiv.trans_apply, Equiv.symm_apply_apply, liftA, runPhys,
    Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map, progPerm_apply]

end IntegerMultBounds.MathlibTM2.Node
