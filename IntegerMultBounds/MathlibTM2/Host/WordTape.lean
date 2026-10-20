module

public import IntegerMultBounds.Schoenhage.Words
public import IntegerMultBounds.MathlibTM2.Host.Stream

/-!
# Word tapes on host stacks

The stack layer under the host backend of word programs (`Schoenhage.Cmd`).

**Word tapes on registers.** A word tape `⟨left, right⟩` on host register `r` has the cells from
the head on (`cells right`) on the right stack and the cells left of the head on the left stack,
nearest on top (`lcells left`: each word as its separator and then its bits from the last).
`place S ι σ` puts the bank `σ` on the injective family of registers `ι`; every other stack keeps
its contents. `regs S j F` puts raw stacks `F x` on the registers `j x`.

**Straight-line code.** `actThen a b` runs the action `a` and then `b` in one host step; `actSeq`
chains a list. `mv1 x` moves the head of register `x` one cell to the right, `scan1 x` records the
cell under it in `scan x`; `moveLR`, `moveRL`, `dropR` and `copyLoop` are the loops over one or two
registers, each with an exact step count.

**Host implementations.** `HostSpec C n pre sem cost prog`: on any injective family of registers
of any host with at least `n` control states, the host program `prog` takes the placed tapes of a
primitive with precondition `pre` to those of its effect `sem` within `C (cost + 1)` steps, every
other stack and the `user` component unchanged. Rewind, back, clear and emit are implemented here
(`rewind_hostSpec`, `back_hostSpec`, `clear_hostSpec`, `emit_hostSpec`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Host.WordCmd

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.Schoenhage (WTape cells clen syms parse)

/-! ### Word tapes on stacks -/

section Cells

variable {A : ℕ}

/-- The cells left of a word tape's head, nearest first. -/
def lcells : List (List Bool) → List (Fin (A + 4))
  | [] => []
  | u :: L => separator :: (u.reverse.map bitSymbol ++ lcells L)

theorem cells_cons' (w : List Bool) (R : List (List Bool)) :
    cells (a := A) (w :: R) = w.map bitSymbol ++ separator :: cells R := by
  simp [cells, Schoenhage.syms_cons, Schoenhage.sym, Function.comp_def]

theorem cells_append' (ws vs : List (List Bool)) :
    cells (a := A) (ws ++ vs) = cells ws ++ cells vs := by
  simp [cells, Schoenhage.syms_append]

theorem lcells_append (L L' : List (List Bool)) :
    lcells (A := A) (L ++ L') = lcells L ++ lcells L' := by
  induction L with
  | nil => rfl
  | cons u L ih => simp [lcells, ih]

theorem lcells_reverse (ws : List (List Bool)) : lcells (A := A) ws.reverse = (cells ws).reverse := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.reverse_cons, lcells_append, ih, cells_cons']
    simp [lcells, List.map_reverse]

theorem reverse_lcells (L : List (List Bool)) : (lcells (A := A) L).reverse = cells L.reverse := by
  rw [← List.reverse_reverse (cells L.reverse), ← lcells_reverse, List.reverse_reverse]

theorem length_lcells (L : List (List Bool)) : (lcells (A := A) L).length = clen L := by
  induction L with
  | nil => rfl
  | cons u L ih => simp [lcells, ih]; ring

theorem cells_head_isSome (R : List (List Bool)) :
    (cells (a := A) R).head?.isSome = decide (R ≠ []) := by
  cases R with
  | nil => rfl
  | cons w R => rw [cells_cons']; cases w <;> simp

end Cells

section Place

variable {T A t : ℕ}

/-- The stacks `S` with the word tapes `σ` on the registers `ι`. -/
noncomputable def place (S : Stacks T A) (ι : Fin t → Fin T) (σ : Fin t → WTape) : Stacks T A :=
  { S with
    L := fun r => if h : ∃ x, ι x = r then lcells (σ h.choose).left else S.L r
    R := fun r => if h : ∃ x, ι x = r then cells (σ h.choose).right else S.R r }

variable {ι : Fin t → Fin T}

theorem place_L_at (hι : Function.Injective ι) (S : Stacks T A) (σ : Fin t → WTape) (x : Fin t) :
    (place S ι σ).L (ι x) = lcells (σ x).left := by
  have h : ∃ y, ι y = ι x := ⟨x, rfl⟩
  simp only [place, h, ↓reduceDIte]
  rw [hι h.choose_spec]

theorem place_R_at (hι : Function.Injective ι) (S : Stacks T A) (σ : Fin t → WTape) (x : Fin t) :
    (place S ι σ).R (ι x) = cells (σ x).right := by
  have h : ∃ y, ι y = ι x := ⟨x, rfl⟩
  simp only [place, h, ↓reduceDIte]
  rw [hι h.choose_spec]

theorem place_L_off (S : Stacks T A) (σ : Fin t → WTape) {r : Fin T} (hr : ∀ x, ι x ≠ r) :
    (place S ι σ).L r = S.L r := by
  have h : ¬ ∃ x, ι x = r := fun ⟨x, hx⟩ => hr x hx
  simp [place, h]

theorem place_R_off (S : Stacks T A) (σ : Fin t → WTape) {r : Fin T} (hr : ∀ x, ι x ≠ r) :
    (place S ι σ).R r = S.R r := by
  have h : ¬ ∃ x, ι x = r := fun ⟨x, hx⟩ => hr x hx
  simp [place, h]

/-- One placed tape. -/
theorem place_one (S : Stacks T A) (j : Fin 1 → Fin T) (τ : Fin 1 → WTape) :
    place S j τ = { S with
      L := Function.update S.L (j 0) (lcells (τ 0).left)
      R := Function.update S.R (j 0) (cells (τ 0).right) } := by
  have hj : Function.Injective j := Function.injective_of_subsingleton j
  have hoff : ∀ {r}, r ≠ j 0 → ∀ x, j x ≠ r := fun hr x h => hr (by rw [← h, Subsingleton.elim x 0])
  ext1
  · rfl
  · rfl
  · funext r
    by_cases hr : r = j 0
    · subst hr; rw [place_L_at hj]; simp
    · rw [place_L_off _ _ (hoff hr)]; simp [hr]
  · funext r
    by_cases hr : r = j 0
    · subst hr; rw [place_R_at hj]; simp
    · rw [place_R_off _ _ (hoff hr)]; simp [hr]

end Place

/-! ### Straight-line code -/

section Seq

variable {K : Type} {Γ : K → Type} {σ : Type}

/-- Run `a`, then `b`. -/
def actThen : Action Γ σ → Action Γ σ → Action Γ σ
  | .done, b => b
  | .push k f a, b => .push k f (actThen a b)
  | .peek k f a, b => .peek k f (actThen a b)
  | .pop k f a, b => .pop k f (actThen a b)
  | .load f a, b => .load f (actThen a b)
  | .branch t x y, b => .branch t (actThen x b) (actThen y b)

/-- Run a list of actions in order. -/
def actSeq : List (Action Γ σ) → Action Γ σ
  | [] => .done
  | a :: as => actThen a (actSeq as)

variable [DecidableEq K]

theorem run_actThen (a b : Action Γ σ) (s : Store Γ σ) : (actThen a b).run s = b.run (a.run s) := by
  induction a generalizing s with
  | done => rfl
  | push k f a ih => simp only [actThen, Action.run, ih]
  | peek k f a ih => simp only [actThen, Action.run, ih]
  | pop k f a ih => simp only [actThen, Action.run, ih]
  | load f a ih => simp only [actThen, Action.run, ih]
  | branch t x y ihx ihy => simp only [actThen, Action.run]; split <;> simp [ihx, ihy]

@[simp] theorem run_actSeq_nil (s : Store Γ σ) : (actSeq ([] : List (Action Γ σ))).run s = s := rfl

@[simp] theorem run_actSeq_cons (a : Action Γ σ) (as : List (Action Γ σ)) (s : Store Γ σ) :
    (actSeq (a :: as)).run s = (actSeq as).run (a.run s) := run_actThen _ _ _

theorem run_actSeq_append (as bs : List (Action Γ σ)) (s : Store Γ σ) :
    (actSeq (as ++ bs)).run s = (actSeq bs).run ((actSeq as).run s) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp [ih]

end Seq

/-! ### Raw registers -/

section Regs

variable {T A s : ℕ}

/-- A pair of stacks: left, right. -/
abbrev LR (A : ℕ) := List (Fin (A + 4)) × List (Fin (A + 4))

/-- The stacks `S` with the stacks `F x` on the registers `j x`. -/
noncomputable def regs (S : Stacks T A) (j : Fin s → Fin T) (F : Fin s → LR A) : Stacks T A :=
  { S with
    L := fun r => if h : ∃ x, j x = r then (F h.choose).1 else S.L r
    R := fun r => if h : ∃ x, j x = r then (F h.choose).2 else S.R r }

variable {j : Fin s → Fin T}

theorem regs_L_at (hj : Function.Injective j) (S : Stacks T A) (F : Fin s → LR A) (x : Fin s) :
    (regs S j F).L (j x) = (F x).1 := by
  have h : ∃ y, j y = j x := ⟨x, rfl⟩
  simp only [regs, h, ↓reduceDIte]
  rw [hj h.choose_spec]

theorem regs_R_at (hj : Function.Injective j) (S : Stacks T A) (F : Fin s → LR A) (x : Fin s) :
    (regs S j F).R (j x) = (F x).2 := by
  have h : ∃ y, j y = j x := ⟨x, rfl⟩
  simp only [regs, h, ↓reduceDIte]
  rw [hj h.choose_spec]

theorem regs_L_off (S : Stacks T A) (F : Fin s → LR A) {r : Fin T} (hr : ∀ x, j x ≠ r) :
    (regs S j F).L r = S.L r := by
  have h : ¬ ∃ x, j x = r := fun ⟨x, hx⟩ => hr x hx
  simp [regs, h]

theorem regs_R_off (S : Stacks T A) (F : Fin s → LR A) {r : Fin T} (hr : ∀ x, j x ≠ r) :
    (regs S j F).R r = S.R r := by
  have h : ¬ ∃ x, j x = r := fun ⟨x, hx⟩ => hr x hx
  simp [regs, h]

theorem place_eq_regs (S : Stacks T A) (σ : Fin s → WTape) :
    place S j σ = regs S j (fun x => (lcells (σ x).left, cells (σ x).right)) := rfl

/-- Changing the stacks of one register. -/
theorem regs_set (hj : Function.Injective j) (S : Stacks T A) (F : Fin s → LR A) (x : Fin s)
    (p : LR A) :
    ({ regs S j F with
        L := Function.update (regs S j F).L (j x) p.1
        R := Function.update (regs S j F).R (j x) p.2 } : Stacks T A) =
      regs S j (Function.update F x p) := by
  ext1
  · rfl
  · rfl
  all_goals
    funext r
    by_cases hr : ∃ y, j y = r
    · obtain ⟨y, rfl⟩ := hr
      by_cases hy : y = x
      · subst hy; simp [regs_L_at hj, regs_R_at hj]
      · have : j y ≠ j x := fun h => hy (hj h)
        simp [this, regs_L_at hj, regs_R_at hj, hy]
    · have hoff : ∀ y, j y ≠ r := fun y h => hr ⟨y, h⟩
      have hne : r ≠ j x := fun h => hoff x h.symm
      simp [hne, regs_L_off _ _ hoff, regs_R_off _ _ hoff]

end Regs

/-! ### Moves and peeks -/

section Moves

variable {T Q A : ℕ} {U : Type}

/-- Pop the right stack of `x` onto its left stack. -/
def mv1 (x : Fin T) : Act T Q A U :=
  .pop (.rt x) (fun v o => { v with sym := o }) (.push (.lt x) (fun v => v.sym.getD blank) .done)

/-- Record the top of the right stack of `x` in `scan x`. -/
def scan1 (x : Fin T) : Act T Q A U :=
  .peek (.rt x) (fun v o => { v with scan := Function.update v.scan x (o.getD blank) }) .done

/-- One cell to the right: the top of the right stack onto the left stack. -/
def adv (p : LR A) : LR A := (p.2.headD blank :: p.1, p.2.tail)

@[simp] theorem adv_cons (L : List (Fin (A + 4))) (e : Fin (A + 4)) (R : List (Fin (A + 4))) :
    adv (L, e :: R) = (e :: L, R) := rfl

variable {s : ℕ} {j : Fin s → Fin T}

theorem mv1_run (hj : Function.Injective j) (S : Stacks T A) (F : Fin s → LR A) (x : Fin s)
    (v : HS T Q A U) :
    (mv1 (j x)).run (mk v (regs S j F)) =
      mk { v with sym := (F x).2.head? } (regs S j (Function.update F x (adv (F x)))) := by
  rw [← regs_set hj]
  rcases hF : F x with ⟨L, _ | ⟨e, R⟩⟩
  · simp [mv1, Action.run, adv, regs_L_at hj, regs_R_at hj, hF, update_lt, update_rt]
  · simp [mv1, Action.run, adv, regs_L_at hj, regs_R_at hj, hF, update_lt, update_rt]

theorem scan1_run (S : Stacks T A) (x : Fin T) (v : HS T Q A U) :
    (scan1 x).run (mk v S) =
      mk { v with scan := Function.update v.scan x ((S.R x).head?.getD blank) } S := rfl

/-- Record the tops of the right stacks of `xs`. -/
def scanAll (xs : List (Fin T)) : Act T Q A U := actSeq (xs.map scan1)

theorem scanAll_run (S : Stacks T A) :
    ∀ (xs : List (Fin T)) (v : HS T Q A U), (scanAll xs).run (mk v S) =
      mk { v with scan := fun x => if x ∈ xs then (S.R x).head?.getD blank else v.scan x } S
  | [], v => by simp [scanAll]
  | x :: xs, v => by
    simp only [scanAll, List.map_cons, run_actSeq_cons, scan1_run] at *
    rw [show actSeq (xs.map scan1) = (scanAll xs : Act T Q A U) from rfl, scanAll_run S xs]
    congr 2
    funext y
    by_cases hy : y ∈ xs
    · simp [hy]
    · by_cases hyx : y = x
      · subst hyx; simp [hy]
      · simp [hy, hyx]

end Moves

section Regs

variable {T A s : ℕ} {j : Fin s → Fin T}

theorem regs_updL (hj : Function.Injective j) (S : Stacks T A) (F : Fin s → LR A) (x : Fin s)
    (l : List (Fin (A + 4))) :
    Function.update (regs S j F).get (.lt (j x)) l = (regs S j (Function.update F x (l, (F x).2))).get := by
  rw [update_lt, ← regs_set hj]
  congr 2
  rw [← regs_R_at hj S F x, Function.update_eq_self]

theorem regs_updR (hj : Function.Injective j) (S : Stacks T A) (F : Fin s → LR A) (x : Fin s)
    (l : List (Fin (A + 4))) :
    Function.update (regs S j F).get (.rt (j x)) l = (regs S j (Function.update F x ((F x).1, l))).get := by
  rw [update_rt, ← regs_set hj]
  congr 2
  rw [← regs_L_at hj S F x, Function.update_eq_self]

end Regs

/-! ### Moves on one register -/

section Moves

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Record in `flag` whether register `r`'s left stack has a top satisfying `p`. -/
def peekL (r : Fin T) (p : Fin (A + 4) → Bool) : Act T Q A U :=
  .peek (.lt r) (fun v o => { v with flag := (o.map p).getD false }) .done

/-- Pop the left stack of register `r` onto its right stack. -/
def lrStep (r : Fin T) (p : Fin (A + 4) → Bool) : Act T Q A U :=
  .pop (.lt r) (fun v o => { v with sym := o })
    (.push (.rt r) (fun v => v.sym.getD blank) (peekL r p))

/-- Move the left stack of register `r` onto its right stack while its top satisfies `p`. -/
def moveLR (r : Fin T) (p : Fin (A + 4) → Bool) : Pr P T Q A U :=
  .seq (.act (peekL r p)) (.loop (·.flag) (.act (lrStep r p)))

theorem moveLR_loop (r : Fin T) (p : Fin (A + 4) → Bool) :
    ∀ (l rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      (∀ x ∈ l, p x = true) → (rest.head?.map p).getD false = false → S.L r = l ++ rest →
      v.flag = ((l ++ rest).head?.map p).getD false →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (lrStep r p))) (mk v S) (2 * l.length + 1)
          (mk v' { S with
            L := Function.update S.L r rest
            R := Function.update S.R r (l.reverse ++ S.R r) }) := by
  intro l
  induction l with
  | nil =>
    intro rest v S _ hrest hS hf
    refine ⟨v, rfl, ?_⟩
    have : ({ S with
        L := Function.update S.L r rest
        R := Function.update S.R r (([] : List (Fin (A + 4))).reverse ++ S.R r) } : Stacks T A) = S := by
      simp only [List.nil_append] at hS
      subst hS
      simp
    rw [this]
    exact .loop_false (by simpa [hrest] using hf)
  | cons e l ih =>
    intro rest v S hl hrest hS hf
    have he : p e = true := hl e List.mem_cons_self
    obtain ⟨v', hu, hx⟩ := ih rest { v with sym := some e, flag := ((l ++ rest).head?.map p).getD false }
      { S with
        L := Function.update S.L r (l ++ rest)
        R := Function.update S.R r (e :: S.R r) }
      (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hrest (by simp) rfl
    refine ⟨v', hu, ?_⟩
    have hrun : (lrStep r p : Act T Q A U).run (mk v S) =
        mk { v with sym := some e, flag := ((l ++ rest).head?.map p).getD false }
          { S with
            L := Function.update S.L r (l ++ rest)
            R := Function.update S.R r (e :: S.R r) } := by
      simp [lrStep, peekL, Action.run, hS, update_lt, update_rt]
    refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa [hS, he] using hf)
      (hrun ▸ Exec.act (body := body) (lrStep r p) (mk v S)) hx) (by simp; ring) ?_
    congr 2 <;> simp

theorem moveLR_exec (r : Fin T) (p : Fin (A + 4) → Bool) (l rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A) (hl : ∀ x ∈ l, p x = true)
    (hrest : (rest.head?.map p).getD false = false) (hS : S.L r = l ++ rest) :
    ∃ v', v'.user = v.user ∧
      Exec body (moveLR r p) (mk v S) (2 * l.length + 2)
        (mk v' { S with
          L := Function.update S.L r rest
          R := Function.update S.R r (l.reverse ++ S.R r) }) := by
  obtain ⟨v', hu, he⟩ := moveLR_loop body r p l rest
    { v with flag := ((S.L r).head?.map p).getD false } S hl hrest hS (by rw [hS])
  exact ⟨v', hu, Exec.cast (Exec.seq (Exec.act (body := body) (peekL r p) (mk v S)) he) (by ring) rfl⟩

/-- Empty the right stack of register `r`. -/
def dropR (r : Fin T) : Pr P T Q A U :=
  whileR r (.pop (.rt r) (fun v _ => v) (peekR r))

theorem dropR_loop (r : Fin T) : ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
    S.R r = l → v.flag = l.head?.isSome →
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (.act (.pop (.rt r) (fun v _ => v) (peekR r)))) (mk v S)
        (2 * l.length + 1) (mk v' { S with R := Function.update S.R r [] }) := by
  intro l
  induction l with
  | nil =>
    intro v S hS hf
    refine ⟨v, rfl, ?_⟩
    have : ({ S with R := Function.update S.R r [] } : Stacks T A) = S := by rw [← hS]; simp
    rw [this]
    exact .loop_false (by simpa using hf)
  | cons e l ih =>
    intro v S hS hf
    obtain ⟨v', hu, hx⟩ := ih { v with flag := l.head?.isSome }
      { S with R := Function.update S.R r l } (by simp) rfl
    refine ⟨v', hu, ?_⟩
    have hrun : (Action.pop (.rt r) (fun v _ => v) (peekR r) : Act T Q A U).run (mk v S) =
        mk { v with flag := l.head?.isSome } { S with R := Function.update S.R r l } := by
      simp [peekR, Action.run, hS, update_rt]
    refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
      (hrun ▸ Exec.act (body := body) _ (mk v S)) hx) (by simp; ring) ?_
    congr 2; simp

theorem dropR_exec (r : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (dropR r) (mk v S) (2 * (S.R r).length + 2)
        (mk v' { S with R := Function.update S.R r [] }) := by
  obtain ⟨v', hu, he⟩ := dropR_loop body r (S.R r) { v with flag := (S.R r).head?.isSome } S rfl rfl
  exact ⟨v', hu, Exec.cast (Exec.seq (peekR_run r v S ▸ Exec.act (body := body) (peekR r) (mk v S)) he)
    (by ring) rfl⟩

/-- Push `l` onto the left stack of register `r`, its last symbol on top. -/
def pushL (r : Fin T) : List (Fin (A + 4)) → Act T Q A U
  | [] => .done
  | x :: xs => .push (.lt r) (fun _ => x) (pushL r xs)

theorem pushL_run (r : Fin T) : ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
    (pushL r l).run (mk v S) = mk v { S with L := Function.update S.L r (l.reverse ++ S.L r) }
  | [], v, S => by simp [pushL]
  | x :: xs, v, S => by
    simp only [pushL, Action.run, mk_var, mk_stk, get_lt, update_lt, store_mk]
    rw [pushL_run r xs]
    congr 2
    simp

/-- Pop the left stack of register `r` onto its right stack once. -/
def popLR (r : Fin T) : Act T Q A U :=
  .pop (.lt r) (fun v o => { v with sym := o }) (.push (.rt r) (fun v => v.sym.getD blank) .done)

end Moves

section Loops

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Record in `flag` whether register `x`'s right stack has a top satisfying `p`. -/
def peekRp (x : Fin T) (p : Fin (A + 4) → Bool) : Act T Q A U :=
  .peek (.rt x) (fun v o => { v with flag := (o.map p).getD false }) .done

/-- Pop the right stack of `x` onto its left stack, then test the new top. -/
def rlStep (x : Fin T) (p : Fin (A + 4) → Bool) : Act T Q A U := actThen (mv1 x) (peekRp x p)

/-- Move the right stack of `x` onto its left stack while its top satisfies `p`. -/
def moveRL (x : Fin T) (p : Fin (A + 4) → Bool) : Pr P T Q A U :=
  .seq (.act (peekRp x p)) (.loop (·.flag) (.act (rlStep x p)))

/-- Pop the left stack of `x` onto the left stack of `y` and the right stack of `x`. -/
def cpStep (x y : Fin T) (p : Fin (A + 4) → Bool) : Act T Q A U :=
  .pop (.lt x) (fun v o => { v with sym := o })
    (.push (.lt y) (fun v => v.sym.getD blank)
      (.push (.rt x) (fun v => v.sym.getD blank)
        (.peek (.lt x) (fun v o => { v with flag := (o.map p).getD false }) .done)))

/-- Copy the left stack of `x` while its top satisfies `p`, reversed, onto the left stack of `y`,
restoring it on the right stack of `x`. -/
def copyLoop (x y : Fin T) (p : Fin (A + 4) → Bool) : Pr P T Q A U :=
  .seq (.act (peekL x p)) (.loop (·.flag) (.act (cpStep x y p)))

variable {s : ℕ} {j : Fin s → Fin T}

theorem moveRL_exec (hj : Function.Injective j) (S : Stacks T A) (x : Fin s)
    (p : Fin (A + 4) → Bool) :
    ∀ (l rest : List (Fin (A + 4))) (F : Fin s → LR A) (v : HS T Q A U),
      (∀ e ∈ l, p e = true) → (rest.head?.map p).getD false = false → (F x).2 = l ++ rest →
      ∃ v', v'.user = v.user ∧
        Exec body (moveRL (j x) p) (mk v (regs S j F)) (2 * l.length + 2)
          (mk v' (regs S j (Function.update F x (l.reverse ++ (F x).1, rest)))) := by
  intro l rest F v hl hrest hF
  suffices h : ∀ (l : List (Fin (A + 4))) (F : Fin s → LR A) (v : HS T Q A U),
      (∀ e ∈ l, p e = true) → (F x).2 = l ++ rest → v.flag = ((l ++ rest).head?.map p).getD false →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (rlStep (j x) p))) (mk v (regs S j F)) (2 * l.length + 1)
          (mk v' (regs S j (Function.update F x (l.reverse ++ (F x).1, rest)))) by
    obtain ⟨v', hu, he⟩ := h l F { v with flag := ((F x).2.head?.map p).getD false } hl hF (by rw [hF])
    have hp : (peekRp (j x) p : Act T Q A U).run (mk v (regs S j F)) =
        mk { v with flag := ((F x).2.head?.map p).getD false } (regs S j F) := by
      simp [peekRp, Action.run, regs_R_at hj]
    refine ⟨v', hu, Exec.cast (Exec.seq (hp ▸ Exec.act (body := body) (peekRp (j x) p) _) he)
      (by ring) rfl⟩
  intro l
  induction l with
  | nil =>
    intro F v _ hF hf
    refine ⟨v, rfl, ?_⟩
    have : Function.update F x (([] : List (Fin (A + 4))).reverse ++ (F x).1, rest) = F := by
      simp only [List.nil_append] at hF
      rw [← hF]; simp
    rw [this]
    exact .loop_false (by simpa [hrest] using hf)
  | cons e l ih =>
    intro F v hl hF hf
    have he : p e = true := hl e List.mem_cons_self
    have hrun : (rlStep (j x) p : Act T Q A U).run (mk v (regs S j F)) =
        mk { v with sym := some e, flag := ((l ++ rest).head?.map p).getD false }
          (regs S j (Function.update F x (e :: (F x).1, l ++ rest))) := by
      have ha : adv (F x) = (e :: (F x).1, l ++ rest) := by simp [adv, hF]
      rw [rlStep, run_actThen, mv1_run hj, ha]
      simp [peekRp, Action.run, regs_R_at hj, hF]
    obtain ⟨v', hu, hx⟩ := ih (Function.update F x (e :: (F x).1, l ++ rest))
      { v with sym := some e, flag := ((l ++ rest).head?.map p).getD false }
      (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (by simp) rfl
    refine ⟨v', hu, ?_⟩
    refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa [hF, he] using hf)
      (hrun ▸ Exec.act (body := body) (rlStep (j x) p) _) hx) (by simp; ring) ?_
    simp

theorem copyLoop_exec (hj : Function.Injective j) (S : Stacks T A) {x y : Fin s} (hxy : x ≠ y)
    (p : Fin (A + 4) → Bool) :
    ∀ (l rest : List (Fin (A + 4))) (F : Fin s → LR A) (v : HS T Q A U),
      (∀ e ∈ l, p e = true) → (rest.head?.map p).getD false = false → (F x).1 = l ++ rest →
      ∃ v', v'.user = v.user ∧
        Exec body (copyLoop (j x) (j y) p) (mk v (regs S j F)) (2 * l.length + 2)
          (mk v' (regs S j (Function.update (Function.update F x (rest, l.reverse ++ (F x).2)) y
            (l.reverse ++ (F y).1, (F y).2)))) := by
  intro l rest F v hl hrest hF
  have hjxy : j x ≠ j y := fun h => hxy (hj h)
  suffices h : ∀ (l : List (Fin (A + 4))) (F : Fin s → LR A) (v : HS T Q A U),
      (∀ e ∈ l, p e = true) → (F x).1 = l ++ rest → v.flag = ((l ++ rest).head?.map p).getD false →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (cpStep (j x) (j y) p))) (mk v (regs S j F)) (2 * l.length + 1)
          (mk v' (regs S j (Function.update (Function.update F x (rest, l.reverse ++ (F x).2)) y
            (l.reverse ++ (F y).1, (F y).2)))) by
    obtain ⟨v', hu, he⟩ := h l F { v with flag := ((F x).1.head?.map p).getD false } hl hF (by rw [hF])
    have hp : (peekL (j x) p : Act T Q A U).run (mk v (regs S j F)) =
        mk { v with flag := ((F x).1.head?.map p).getD false } (regs S j F) := by
      simp [peekL, Action.run, regs_L_at hj]
    refine ⟨v', hu, Exec.cast (Exec.seq (hp ▸ Exec.act (body := body) (peekL (j x) p) _) he)
      (by ring) rfl⟩
  intro l
  induction l with
  | nil =>
    intro F v _ hF hf
    refine ⟨v, rfl, ?_⟩
    have : Function.update (Function.update F x (rest, ([] : List (Fin (A + 4))).reverse ++ (F x).2)) y
        (([] : List (Fin (A + 4))).reverse ++ (F y).1, (F y).2) = F := by
      funext z
      by_cases hz : z = y
      · subst hz; simp
      · by_cases hzx : z = x
        · subst hzx; simp only [List.nil_append] at hF; simp [hz, ← hF]
        · simp [hz, hzx]
    rw [this]
    exact .loop_false (by simpa [hrest] using hf)
  | cons e l ih =>
    intro F v hl hF hf
    have he : p e = true := hl e List.mem_cons_self
    set F₁ := Function.update (Function.update F x (l ++ rest, e :: (F x).2)) y (e :: (F y).1, (F y).2)
    have hrun : (cpStep (j x) (j y) p : Act T Q A U).run (mk v (regs S j F)) =
        mk { v with sym := some e, flag := ((l ++ rest).head?.map p).getD false } (regs S j F₁) := by
      simp only [cpStep, Action.run, mk_var, mk_stk, get_lt, get_rt, regs_L_at hj, hF,
        List.cons_append, List.head?_cons, List.tail_cons, Option.getD_some, regs_updL hj,
        regs_updR hj, store_mk, Function.update_self, Function.update_of_ne hxy.symm, regs_R_at hj]
      congr 2
      · simp [Function.update_of_ne hxy]
      · funext z
        by_cases hz : z = y
        · subst hz; simp [F₁, hxy.symm]
        · by_cases hzx : z = x
          · subst hzx; simp [F₁, hz]
          · simp [F₁, hz, hzx]
    obtain ⟨v', hu, hx⟩ := ih F₁ { v with sym := some e, flag := ((l ++ rest).head?.map p).getD false }
      (fun z hz => hl z (List.mem_cons_of_mem _ hz)) (by simp [F₁, hxy]) rfl
    refine ⟨v', hu, ?_⟩
    refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa [hF, he] using hf)
      (hrun ▸ Exec.act (body := body) (cpStep (j x) (j y) p) _) hx) (by simp; ring) ?_
    congr 2
    funext z
    by_cases hz : z = y
    · subst hz; simp [F₁]
    · by_cases hzx : z = x
      · subst hzx; simp [F₁, hz]
      · simp [F₁, hz, hzx]

end Loops

/-! ### Host implementations -/

section Spec

/-- A host program on `s` registers, in any host. -/
abbrev HProg (s : ℕ) : Type 1 :=
  {P : Type} → {T Q A : ℕ} → {U : Type} → (Fin s → Fin T) → Pr P T Q A U

/-- `prog` implements the word-tape primitive with precondition `pre`, effect `sem` and cost
`cost` with constant `C` on hosts with at least `n` control states. -/
def HostSpec (C n s : ℕ) (pre : (Fin s → WTape) → Prop) (sem : (Fin s → WTape) → Fin s → WTape)
    (cost : (Fin s → WTape) → ℕ) (prog : HProg s) : Prop :=
  ∀ {P : Type} {T Q A : ℕ} {U : Type} (body : P → Pr P T Q A U) (j : Fin s → Fin T),
    Function.Injective j → n ≤ Q → ∀ τ, pre τ → ∀ (v : HS T Q A U) (S : Stacks T A),
      ∃ v' m, v'.user = v.user ∧ m ≤ C * (cost τ + 1) ∧
        Exec body (prog j) (mk v (place S j τ)) m (mk v' (place S j (sem τ)))

/-- A program without procedure calls. -/
def NoCalls {K : Type} {Γ : K → Type} {σ P : Type} : Prog P Γ σ → Prop
  | .act _ => True
  | .seq p q => NoCalls p ∧ NoCalls q
  | .cond _ p q => NoCalls p ∧ NoCalls q
  | .loop _ p => NoCalls p
  | .call _ => False

/-- A host program without procedure calls on every placement. -/
def HNoCalls {s : ℕ} (prog : HProg s) : Prop :=
  ∀ {P : Type} {T Q A : ℕ} {U : Type} (j : Fin s → Fin T),
    NoCalls (prog (P := P) (T := T) (Q := Q) (A := A) (U := U) j)

end Spec

/-! ### Rewind, back, clear and emit -/

section Prims

theorem bitSymbol_ne_sep {A : ℕ} (b : Bool) : bitSymbol (a := A) b ≠ separator := by
  cases b <;> simp [bitSymbol, separator]

theorem two_le_mul {C x : ℕ} (hC : 2 ≤ C) : 2 * x ≤ C * x := Nat.mul_le_mul_right x hC

/-- Rewind: the left stack onto the right stack. -/
def rewindProg : HProg 1 := fun j => moveLR (j 0) (fun _ => true)

theorem rewind_hostSpec : HostSpec 3 0 1 (fun _ => True)
    (fun σ _ => ⟨[], (σ 0).left.reverse ++ (σ 0).right⟩) (fun σ => clen (σ 0).left + 2) rewindProg := by
  intro P T Q A U body j _ _ τ _ v S
  have hC : 2 ≤ 3 := by norm_num
  obtain ⟨v', hu, he⟩ := moveLR_exec body (j 0) (fun _ => true) (lcells (τ 0).left) [] v
    (place S j τ) (by simp) rfl (by rw [place_one]; simp)
  refine ⟨v', _, hu, ?_, he.cast rfl ?_⟩
  · have := two_le_mul (x := clen (τ 0).left + 2 + 1) hC
    simp only [length_lcells]
    omega
  · congr 1
    simp only [place_one]
    congr 1
    · simp [lcells]
    · simp [reverse_lcells, cells_append']

/-- Back: the separator and then the bits of the previous word onto the right stack. -/
def backProg : HProg 1 := fun j =>
  .seq (.act (popLR (j 0))) (moveLR (j 0) (fun x => decide (x ≠ separator)))

theorem back_hostSpec : HostSpec 3 0 1 (fun σ => (σ 0).left ≠ [])
    (fun σ _ => ⟨(σ 0).left.tail, (σ 0).left.headD [] :: (σ 0).right⟩)
    (fun σ => ((σ 0).left.headD []).length + 3) backProg := by
  intro P T Q A U body j _ _ τ hpre v S
  have hC : 2 ≤ 3 := by norm_num
  obtain ⟨u, L, hL⟩ : ∃ u L, (τ 0).left = u :: L := by
    rcases h : (τ 0).left with _ | ⟨u, L⟩
    · exact absurd h hpre
    · exact ⟨u, L, rfl⟩
  set S₀ := place S j τ
  have hrun : (popLR (j 0) : Act _ _ A _).run (mk v S₀) =
      mk { v with sym := some separator }
        { S₀ with
          L := Function.update S₀.L (j 0) (u.reverse.map bitSymbol ++ lcells L)
          R := Function.update S₀.R (j 0) (separator :: S₀.R (j 0)) } := by
    have : S₀.L (j 0) = separator :: (u.reverse.map bitSymbol ++ lcells L) := by
      simp [S₀, place_one, hL, lcells]
    simp [popLR, Action.run, this, update_lt, update_rt]
  obtain ⟨v', hu, he⟩ := moveLR_exec body (j 0) (fun x => decide (x ≠ separator))
    (u.reverse.map bitSymbol) (lcells L) { v with sym := some separator }
    { S₀ with
      L := Function.update S₀.L (j 0) (u.reverse.map bitSymbol ++ lcells L)
      R := Function.update S₀.R (j 0) (separator :: S₀.R (j 0)) }
    (fun x hx => by obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; simpa using bitSymbol_ne_sep b)
    (by cases L <;> simp [lcells]) (by simp)
  refine ⟨v', _, hu, ?_, (Exec.seq (hrun ▸ Exec.act _ _) he).cast rfl ?_⟩
  · have := two_le_mul (x := ((τ 0).left.headD []).length + 3 + 1) hC
    simp only [hL, List.headD_cons, List.length_map, List.length_reverse] at this ⊢
    omega
  · congr 1
    simp only [S₀, place_one]
    congr 1
    · simp [hL]
    · simp [hL, cells_cons', List.map_reverse]

/-- Clear: rewind, then empty the right stack. -/
def clearProg : HProg 1 := fun j => .seq (moveLR (j 0) (fun _ => true)) (dropR (j 0))

theorem clear_hostSpec : HostSpec 3 0 1 (fun _ => True) (fun _ _ => ⟨[], []⟩)
    (fun σ => 2 * clen (σ 0).words + 2) clearProg := by
  intro P T Q A U body j _ _ τ _ v S
  have hC : 2 ≤ 3 := by norm_num
  obtain ⟨v₁, hu₁, he₁⟩ := moveLR_exec body (j 0) (fun _ => true) (lcells (τ 0).left) [] v
    (place S j τ) (by simp) rfl (by rw [place_one]; simp)
  obtain ⟨v₂, hu₂, he₂⟩ := dropR_exec body (j 0) v₁
    { place S j τ with
      L := Function.update (place S j τ).L (j 0) []
      R := Function.update (place S j τ).R (j 0)
        ((lcells (τ 0).left).reverse ++ (place S j τ).R (j 0)) }
  refine ⟨v₂, _, hu₂.trans hu₁, ?_, (Exec.seq he₁ he₂).cast rfl ?_⟩
  · have := two_le_mul (x := 2 * clen (τ 0).words + 2 + 1) hC
    simp only [place_one, Function.update_self, length_lcells, List.length_append,
      List.length_reverse, Schoenhage.length_cells, WTape.words, Schoenhage.clen_append,
      Schoenhage.clen_reverse] at this ⊢
    omega
  · congr 1
    simp only [place_one]
    congr 1
    · simp [lcells]
    · simp [cells]

/-- Emit: the cells of the words onto the left stack, in one step. -/
def emitProg (ws : List (List Bool)) : HProg 1 := fun j => .act (pushL (j 0) (cells ws))

theorem emit_hostSpec (ws : List (List Bool)) :
    HostSpec 3 0 1 (fun σ => (σ 0).right = []) (fun σ _ => ⟨ws.reverse ++ (σ 0).left, []⟩)
      (fun _ => clen ws) (emitProg ws) := by
  intro P T Q A U body j _ _ τ hpre v S
  have hC : 2 ≤ 3 := by norm_num
  refine ⟨v, 1, rfl, Nat.mul_pos (by omega) (by omega), ?_⟩
  refine (Exec.act (body := body) _ _).cast rfl ?_
  rw [pushL_run]
  congr 1
  simp only [place_one]
  congr 1
  · simp [lcells_append, lcells_reverse]
  · have hr : (τ 0).right = [] := hpre
    simp [hr]

theorem rewindProg_noCalls : HNoCalls rewindProg := fun _ => ⟨trivial, trivial⟩
theorem backProg_noCalls : HNoCalls backProg := fun _ => ⟨trivial, trivial, trivial⟩
theorem clearProg_noCalls : HNoCalls clearProg := fun _ => ⟨⟨trivial, trivial⟩, trivial, trivial⟩
theorem emitProg_noCalls (ws : List (List Bool)) : HNoCalls (emitProg ws) := fun _ => trivial

end Prims

end IntegerMultBounds.MathlibTM2.Host.WordCmd
