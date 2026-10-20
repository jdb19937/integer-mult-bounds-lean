module

public import IntegerMultBounds.MathlibTM2.Host.WordCmd

/-!
# The streaming primitive on host stacks

A host implementation (`streamImpl`) of the streaming primitive `Schoenhage.streamPrim R ext` of
word programs: tape `drv` is the driver, tapes `oth i` the further inputs and tape `out` the
output (`Schoenhage.Strm`).

**Straight-line code.** `actThen a b` runs the action `a` and then `b` in one host step; `actSeq`
chains a list. Registers hold raw stacks: `regs S j F` has the left and right stacks `F x` on
register `j x`. `mv1 x` pops the right stack of `x` onto its left stack (the head moves one cell to
the right), `scan1 x` records its top in `scan x`; `moveIf test l` moves every further input
`i ∈ l` whose test holds, the tests reading only `st` and `scan` (`run_moveIf`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Host.WordCmd

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.Schoenhage (WTape Prim Cmd cells clen upd syms parse)

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

/-! ### Conditional moves of the further inputs -/

section MoveIf

variable {T Q A : ℕ} {U : Type} {r : ℕ} (j : Fin (r + 2) → Fin T)

open Schoenhage.Strm (oth)

/-- Move the further inputs `i ∈ l` whose test holds. -/
def moveIf (test : Fin Q → (Fin T → Fin (A + 4)) → Fin r → Bool) (l : List (Fin r)) :
    Act T Q A U :=
  actSeq (l.map fun i => .branch (fun v => test v.st v.scan i) (mv1 (j (oth i))) .done)

/-- The stacks after moving the further inputs of `l` passing `p`. -/
noncomputable def moved (F : Fin (r + 2) → LR A) (l : List (Fin r)) (p : Fin r → Bool) :
    Fin (r + 2) → LR A :=
  open Classical in fun x => if ∃ i ∈ l, oth i = x ∧ p i = true then adv (F x) else F x

@[simp] theorem moved_nil (F : Fin (r + 2) → LR A) (p : Fin r → Bool) : moved F [] p = F := by
  funext x; simp [moved]

theorem oth_injective : Function.Injective (oth (r := r)) := by
  intro i i' h; simpa [oth, Fin.ext_iff] using h

theorem run_moveIf (hj : Function.Injective j) (S : Stacks T A)
    (test : Fin Q → (Fin T → Fin (A + 4)) → Fin r → Bool) :
    ∀ (l : List (Fin r)) (F : Fin (r + 2) → LR A) (v : HS T Q A U), l.Nodup →
      ∃ o, (moveIf j test l).run (mk v (regs S j F)) =
        mk { v with sym := o } (regs S j (moved F l (test v.st v.scan)))
  | [], F, v, _ => ⟨v.sym, by rw [moved_nil]; rfl⟩
  | i :: l, F, v, hl => by
    rw [List.nodup_cons] at hl
    simp only [moveIf, List.map_cons, run_actSeq_cons, Action.run]
    rw [show actSeq (l.map fun i => .branch (fun v : HS T Q A U => test v.st v.scan i)
        (mv1 (j (oth i))) .done) = moveIf (U := U) j test l from rfl]
    by_cases ht : test v.st v.scan i = true
    · simp only [mk_var, ht, ↓reduceIte]
      rw [mv1_run hj]
      obtain ⟨o, ho⟩ := run_moveIf hj S test l _ { v with sym := (F (oth i)).2.head? } hl.2
      refine ⟨o, ho.trans ?_⟩
      congr 2
      funext x
      by_cases hx : x = oth i
      · subst hx
        have : ¬ ∃ i' ∈ l, oth i' = oth i ∧ test v.st v.scan i' = true :=
          fun ⟨i', hi', he, _⟩ => hl.1 (oth_injective he ▸ hi')
        simp [moved, this, ht]
      · have hne : ∀ i', oth i' = x → i' ≠ i := fun i' h hi => hx (hi ▸ h.symm)
        simp only [moved, Function.update_of_ne hx]
        congr 1
        apply propext
        constructor
        · rintro ⟨i', hi', he, hp⟩; exact ⟨i', List.mem_cons_of_mem _ hi', he, hp⟩
        · rintro ⟨i', hi', he, hp⟩
          rcases List.mem_cons.mp hi' with rfl | hi'
          · exact absurd he.symm hx
          · exact ⟨i', hi', he, hp⟩
    · have ht' : test v.st v.scan i = false := by simpa using ht
      simp only [mk_var, ht', Bool.false_eq_true, ↓reduceIte]
      obtain ⟨o, ho⟩ := run_moveIf hj S test l F v hl.2
      refine ⟨o, ho.trans ?_⟩
      congr 2
      funext x
      simp only [moved]
      congr 1
      apply propext
      constructor
      · rintro ⟨i', hi', he, hp⟩; exact ⟨i', List.mem_cons_of_mem _ hi', he, hp⟩
      · rintro ⟨i', hi', he, hp⟩
        rcases List.mem_cons.mp hi' with rfl | hi'
        · exact absurd hp ht
        · exact ⟨i', hi', he, hp⟩

end MoveIf

/-! ### Configurations of the streaming tapes -/

section Cfg

variable {A r : ℕ}

open Schoenhage.Strm (drv oth)

/-- The stacks of the driver, the further inputs and the output. -/
def cfg (d : LR A) (o : Fin r → LR A) (u : LR A) : Fin (r + 2) → LR A := Fin.cons d (Fin.snoc o u)

theorem drv_eq : (drv : Fin (r + 2)) = 0 := Fin.ext rfl
theorem oth_eq (i : Fin r) : oth i = (Fin.castSucc i).succ := Fin.ext rfl
theorem out_eq : (Schoenhage.Strm.out : Fin (r + 2)) = (Fin.last r).succ := Fin.ext rfl

@[simp] theorem cfg_drv (d : LR A) (o : Fin r → LR A) (u : LR A) : cfg d o u drv = d := by
  simp [cfg, drv_eq]

@[simp] theorem cfg_oth (d : LR A) (o : Fin r → LR A) (u : LR A) (i : Fin r) :
    cfg d o u (oth i) = o i := by
  simp [cfg, oth_eq]

@[simp] theorem cfg_out (d : LR A) (o : Fin r → LR A) (u : LR A) :
    cfg d o u Schoenhage.Strm.out = u := by
  simp [cfg, out_eq]

theorem cfg_ext {F G : Fin (r + 2) → LR A} (hd : F drv = G drv) (ho : ∀ i, F (oth i) = G (oth i))
    (hu : F Schoenhage.Strm.out = G Schoenhage.Strm.out) : F = G := by
  funext x
  rcases Schoenhage.Strm.cases_tape x with rfl | ⟨i, rfl⟩ | rfl
  · exact hd
  · exact ho i
  · exact hu

theorem update_cfg_drv (d d' : LR A) (o : Fin r → LR A) (u : LR A) :
    Function.update (cfg d o u) drv d' = cfg d' o u :=
  cfg_ext (by simp) (fun i => by simp [Function.update_of_ne (Schoenhage.Strm.oth_ne_drv i)])
    (by simp [Function.update_of_ne (Schoenhage.Strm.drv_ne_out).symm])

theorem update_cfg_out (d : LR A) (o : Fin r → LR A) (u u' : LR A) :
    Function.update (cfg d o u) Schoenhage.Strm.out u' = cfg d o u' :=
  cfg_ext (by simp [Function.update_of_ne Schoenhage.Strm.drv_ne_out])
    (fun i => by simp [Function.update_of_ne (Schoenhage.Strm.oth_ne_out i)]) (by simp)

theorem moved_cfg (d : LR A) (o : Fin r → LR A) (u : LR A) (l : List (Fin r)) (p : Fin r → Bool) :
    moved (cfg d o u) l p = cfg d (fun i => if i ∈ l ∧ p i = true then adv (o i) else o i) u := by
  refine cfg_ext ?_ (fun i => ?_) ?_
  · have : ¬ ∃ i ∈ l, oth i = drv ∧ p i = true :=
      fun ⟨i, _, h, _⟩ => Schoenhage.Strm.oth_ne_drv i h
    simp [moved, this]
  · have : (∃ i' ∈ l, oth i' = oth i ∧ p i' = true) ↔ i ∈ l ∧ p i = true :=
      ⟨fun ⟨i', hi', h, hp⟩ => oth_injective h ▸ ⟨hi', hp⟩, fun ⟨hi, hp⟩ => ⟨i, hi, rfl, hp⟩⟩
    simp only [moved, cfg_oth, this]
  · have : ¬ ∃ i ∈ l, oth i = Schoenhage.Strm.out ∧ p i = true :=
      fun ⟨i, _, h, _⟩ => Schoenhage.Strm.oth_ne_out i h
    simp [moved, this]

end Cfg

/-! ### The streaming program -/

section Stream

open Schoenhage.Strm (Rule go drv oth decode)

variable {T Q A : ℕ} {U P : Type} {r : ℕ} (R : Rule r) (ext : Bool) (j : Fin (r + 2) → Fin T)

/-- The rule state held in `st`. -/
noncomputable def qdec (st : Fin Q) : R.Q :=
  if h : st.val < Fintype.card R.Q then (Fintype.equivFin R.Q).symm ⟨st.val, h⟩ else R.q0

/-- Hold the rule state `q` in `st`. -/
noncomputable def qset (q : R.Q) (st : Fin Q) : Fin Q :=
  if h : ((Fintype.equivFin R.Q) q).val < Q then ⟨_, h⟩ else st

theorem qdec_qset (hQ : Fintype.card R.Q ≤ Q) (q : R.Q) (st : Fin Q) :
    qdec R (qset R q st) = q := by
  have h : ((Fintype.equivFin R.Q) q).val < Q := lt_of_lt_of_le ((Fintype.equivFin R.Q) q).isLt hQ
  simp [qset, qdec, h]

/-- Whether a cell holds a bit. -/
def isBit (x : Fin (A + 4)) : Bool := (decode x).isSome

theorem decode_head (l : List Bool) (X : List (Fin (A + 4))) :
    decode ((l.map bitSymbol ++ separator :: X).headD blank) = l.head? := by
  cases l <;> simp

theorem isBit_head (l : List Bool) (X : List (Fin (A + 4))) :
    isBit ((l.map bitSymbol ++ separator :: X).headD blank) = !l.isEmpty := by
  cases l <;> simp [isBit]

theorem flag_eq (l : List (Fin (A + 4))) : (l.head?.map isBit).getD false = isBit (l.headD blank) := by
  cases l <;> simp [isBit, decode, blank, bitSymbol]

theorem decide_bit (b : Bool) : decide (bitSymbol (a := A) b = bitSymbol true) = b := by
  cases b <;> simp [bitSymbol]

/-- The rule's step on the recorded tops. -/
noncomputable def res (st : Fin Q) (sc : Fin T → Fin (A + 4)) :=
  R.step (qdec R st) (decide (sc (j drv) = bitSymbol true)) (fun i => decode (sc (j (oth i))))

/-- Whether further input `i` moves in this step. -/
noncomputable def advT (st : Fin Q) (sc : Fin T → Fin (A + 4)) (i : Fin r) : Bool :=
  (res R j st sc).2.2 i && isBit (sc (j (oth i)))

/-- Emit the step's symbol, if any. -/
noncomputable def emitAct : Act T Q A U :=
  .branch (fun v => (res R j v.st v.scan).2.1.isSome)
    (.push (.lt (j Schoenhage.Strm.out)) (fun v => Schoenhage.sym ((res R j v.st v.scan).2.1.getD none))
      .done) .done

/-- Enter the step's next rule state. -/
noncomputable def setSt : Act T Q A U :=
  .load (fun v => { v with st := qset R (res R j v.st v.scan).1 v.st }) .done

/-- Record in `flag` whether register `x` has a bit on top. -/
def flagBit (x : Fin T) : Act T Q A U :=
  .peek (.rt x) (fun v o => { v with flag := (o.map isBit).getD false }) .done

/-- The registers of the further inputs. -/
def others : List (Fin T) := (List.finRange r).map fun i => j (oth i)

/-- One bit of the driver. -/
noncomputable def bitStep : Act T Q A U :=
  actSeq [scanAll (j drv :: others j), moveIf j (advT R j) (List.finRange r), emitAct R j,
    mv1 (j drv), setSt R j, flagBit (j drv)]

/-- Record in `flag` whether some further input has a bit on top. -/
def flagAny : Act T Q A U :=
  actThen (scanAll (others j))
    (.load (fun v => { v with flag := (List.finRange r).any fun i => isBit (v.scan (j (oth i))) }) .done)

/-- One cell of every further input still inside its word. -/
def skipStep : Act T Q A U :=
  actSeq [scanAll (others j), moveIf j (fun _ sc i => isBit (sc (j (oth i)))) (List.finRange r),
    flagAny j]

theorem mem_others (i : Fin r) : j (oth i) ∈ others j := by
  simp [others]

theorem drv_notMem_others (hj : Function.Injective j) : j drv ∉ others j := by
  simp only [others, List.mem_map, List.mem_finRange, true_and, not_exists]
  exact fun i h => Schoenhage.Strm.oth_ne_drv i (hj h)

variable {j}

theorem scanAll_cfg (hj : Function.Injective j) (S : Stacks T A) (d : LR A) (o : Fin r → LR A)
    (u : LR A) (v : HS T Q A U) (xs : List (Fin T)) {x : Fin (r + 2)} (hx : j x ∈ xs) :
    (((scanAll xs).run (mk v (regs S j (cfg d o u)))).var.scan (j x)) =
      ((cfg d o u x).2).headD blank := by
  rw [scanAll_run]
  simp [hx, regs_R_at hj, List.headD_eq_head?_getD]

theorem bitStep_run (hQ : Fintype.card R.Q ≤ Q) (hj : Function.Injective j) (S : Stacks T A)
    (b : Bool) (Ld Rd : List (Fin (A + 4))) (o : Fin r → LR A) (Lu Ru : List (Fin (A + 4)))
    (v : HS T Q A U) :
    let p := R.step (qdec R v.st) b (fun i => decode ((o i).2.headD blank))
    ∃ v', v'.user = v.user ∧ qdec R v'.st = p.1 ∧ v'.flag = isBit (Rd.headD blank) ∧
      (bitStep R j).run (mk v (regs S j (cfg (Ld, bitSymbol b :: Rd) o (Lu, Ru)))) =
        mk v' (regs S j (cfg (bitSymbol b :: Ld, Rd)
          (fun i => if p.2.2 i && isBit ((o i).2.headD blank) then adv (o i) else o i)
          ((p.2.1.toList.map Schoenhage.sym).reverse ++ Lu, Ru))) := by
  intro p
  set F := cfg (Ld, bitSymbol b :: Rd) o (Lu, Ru)
  set sc₁ : Fin T → Fin (A + 4) := fun x =>
    if x ∈ j drv :: others j then ((regs S j F).R x).head?.getD blank else v.scan x
  set v₁ : HS T Q A U := { v with scan := sc₁ }
  have e₁ : (scanAll (j drv :: others j)).run (mk v (regs S j F)) = mk v₁ (regs S j F) :=
    scanAll_run (regs S j F) _ v
  have hst : v₁.st = v.st := rfl
  have hd : v₁.scan (j drv) = bitSymbol b := by
    simp [v₁, sc₁, regs_R_at hj, F]
  have ho : ∀ i, v₁.scan (j (oth i)) = (o i).2.headD blank := fun i => by
    simp [v₁, sc₁, regs_R_at hj, F, mem_others j i, List.headD_eq_head?_getD]
  have hres : res R j v₁.st v₁.scan = p := by
    simp only [res, hst, hd, decide_bit, ho, p]
  have hadv : advT R j v₁.st v₁.scan = fun i => p.2.2 i && isBit ((o i).2.headD blank) := by
    funext i; simp only [advT, hres, ho]
  obtain ⟨o₂, e₂⟩ := run_moveIf j hj S (advT R j) (List.finRange r) F v₁ (List.nodup_finRange r)
  set v₂ : HS T Q A U := { v₁ with sym := o₂ }
  set o' := fun i => if p.2.2 i && isBit ((o i).2.headD blank) then adv (o i) else o i
  have hF₂ : moved F (List.finRange r) (advT R j v₁.st v₁.scan) = cfg (Ld, bitSymbol b :: Rd) o' (Lu, Ru) := by
    simp only [F, moved_cfg, hadv, List.mem_finRange, true_and, o']
  set Lu' := (p.2.1.toList.map Schoenhage.sym).reverse ++ Lu
  have e₃ : (emitAct R j).run (mk v₂ (regs S j (cfg (Ld, bitSymbol b :: Rd) o' (Lu, Ru)))) =
      mk v₂ (regs S j (cfg (Ld, bitSymbol b :: Rd) o' (Lu', Ru))) := by
    have hres₂ : res R j v₂.st v₂.scan = p := hres
    rcases he : p.2.1 with _ | e
    · simp [emitAct, Action.run, hres₂, he, Lu']
    · have := regs_set (A := A) hj S (cfg (Ld, bitSymbol b :: Rd) o' (Lu, Ru)) Schoenhage.Strm.out
        (Schoenhage.sym e :: Lu, Ru)
      simp only [update_cfg_out] at this
      simp only [emitAct, Action.run, mk_var, hres₂, he, Option.isSome_some, ↓reduceIte, mk_stk,
        get_lt, regs_L_at hj, cfg_out, Option.getD_some, update_lt, store_mk, Lu', Option.toList_some,
        List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append]
      rw [← this]
      congr 2
      simp [regs_R_at hj]
  have e₄ := mv1_run (Q := Q) (U := U) hj S (cfg (Ld, bitSymbol b :: Rd) o' (Lu', Ru)) drv v₂
  simp only [cfg_drv, adv_cons, update_cfg_drv] at e₄
  set v₃ : HS T Q A U :=
    { v₂ with sym := some (bitSymbol b), st := qset R p.1 v.st, flag := isBit (Rd.headD blank) }
  refine ⟨v₃, rfl, by simp [v₃, qdec_qset R hQ], rfl, ?_⟩
  simp only [bitStep, run_actSeq_cons, run_actSeq_nil, e₁, e₂, hF₂, e₃, e₄]
  simp only [setSt, flagBit, Action.run, mk_var, mk_stk, get_rt, regs_R_at hj, cfg_drv]
  have hres₂ : res R j v₂.st v₂.scan = p := hres
  simp only [hres₂, flag_eq]
  rfl

variable (body : P → Pr P T Q A U)

/-- The bit loop runs the rule over the driver's word. -/
theorem bitLoop (hQ : Fintype.card R.Q ≤ Q) (hj : Function.Injective j) (S : Stacks T A)
    (Xd : List (Fin (A + 4))) (X : Fin r → List (Fin (A + 4))) (Ru : List (Fin (A + 4))) :
    ∀ (bs : List Bool) (q : R.Q) (ws : Fin r → List Bool) (Ld : List (Fin (A + 4)))
      (Li : Fin r → List (Fin (A + 4))) (Lu : List (Fin (A + 4))) (v : HS T Q A U),
      qdec R v.st = q → v.flag = !bs.isEmpty →
      ∃ v', v'.user = v.user ∧ qdec R v'.st = (go R q bs ws).1 ∧
        ∃ pre : Fin r → List Bool, (∀ i, pre i ++ (go R q bs ws).2.2 i = ws i) ∧
        Exec body (.loop (·.flag) (.act (bitStep R j)))
          (mk v (regs S j (cfg (Ld, bs.map bitSymbol ++ separator :: Xd)
            (fun i => (Li i, (ws i).map bitSymbol ++ separator :: X i)) (Lu, Ru))))
          (2 * bs.length + 1)
          (mk v' (regs S j (cfg ((bs.map bitSymbol).reverse ++ Ld, separator :: Xd)
            (fun i => ((pre i).reverse.map bitSymbol ++ Li i,
              ((go R q bs ws).2.2 i).map bitSymbol ++ separator :: X i))
            (((go R q bs ws).2.1.map Schoenhage.sym).reverse ++ Lu, Ru)))) := by
  intro bs
  induction bs with
  | nil =>
    intro q ws Ld Li Lu v hq hf
    refine ⟨v, rfl, by simpa [go] using hq, fun _ => [], fun i => by simp [go], ?_⟩
    have := Exec.loop_false (body := body) (f := (·.flag)) (p := .act (bitStep R j))
      (s := mk v (regs S j (cfg (Ld, separator :: Xd)
        (fun i => (Li i, (ws i).map bitSymbol ++ separator :: X i)) (Lu, Ru)))) (by simpa using hf)
    simpa [go] using this
  | cons b bs ih =>
    intro q ws Ld Li Lu v hq hf
    obtain ⟨v₁, hu₁, hq₁, hf₁, e⟩ := bitStep_run R hQ hj S b Ld (bs.map bitSymbol ++ separator :: Xd)
      (fun i => (Li i, (ws i).map bitSymbol ++ separator :: X i)) Lu Ru v
    set p := R.step q b (fun i => (ws i).head?) with hp
    have hp' : R.step (qdec R v.st) b
        (fun i => decode (((fun i => (Li i, (ws i).map bitSymbol ++ separator :: X i)) i).2.headD blank)) =
          p := by
      simp only [hq, decode_head, p]
    rw [hp'] at hq₁ e
    set ws' : Fin r → List Bool := fun i => if p.2.2 i then (ws i).tail else ws i
    set Li' : Fin r → List (Fin (A + 4)) := fun i =>
      if p.2.2 i && !(ws i).isEmpty then bitSymbol ((ws i).headD false) :: Li i else Li i
    have ho : (fun i => if p.2.2 i && isBit (((fun i => (Li i, (ws i).map bitSymbol ++ separator :: X i)) i).2.headD blank)
        then adv ((fun i => (Li i, (ws i).map bitSymbol ++ separator :: X i)) i)
        else (fun i => (Li i, (ws i).map bitSymbol ++ separator :: X i)) i) =
          fun i => (Li' i, (ws' i).map bitSymbol ++ separator :: X i) := by
      funext i
      simp only [isBit_head]
      rcases hw : ws i with _ | ⟨c, t⟩ <;> cases hpi : p.2.2 i <;> simp [Li', ws', hw, hpi]
    rw [ho] at e
    obtain ⟨v', hu', hq', pre', hpre', he'⟩ := ih p.1 ws' (bitSymbol b :: Ld) Li'
      ((p.2.1.toList.map Schoenhage.sym).reverse ++ Lu) v₁ hq₁ (by rw [hf₁]; exact isBit_head bs Xd)
    have hgo : go R q (b :: bs) ws = ((go R p.1 bs ws').1, p.2.1.toList ++ (go R p.1 bs ws').2.1,
        (go R p.1 bs ws').2.2) := rfl
    refine ⟨v', hu'.trans hu₁, by rw [hgo]; exact hq',
      fun i => (if p.2.2 i && !(ws i).isEmpty then [(ws i).headD false] else []) ++ pre' i,
      fun i => ?_, ?_⟩
    · rw [hgo]
      simp only
      rw [List.append_assoc, hpre' i]
      simp only [ws']
      rcases hw : ws i with _ | ⟨c, t⟩ <;> cases hpi : p.2.2 i <;> simp
    · have hstep := Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (e ▸ Exec.act (body := body) (bitStep R j) _) he'
      refine hstep.cast (by simp; ring) ?_
      rw [hgo]
      congr 3
      · simp
      · funext i
        simp only [Li']
        rcases hw : ws i with _ | ⟨c, t⟩ <;> cases hpi : p.2.2 i <;> simp
      · simp

theorem regs_setL (hj : Function.Injective j) (S : Stacks T A) (F : Fin (r + 2) → LR A)
    (x : Fin (r + 2)) (l : List (Fin (A + 4))) :
    ({ regs S j F with L := Function.update (regs S j F).L (j x) l } : Stacks T A) =
      regs S j (Function.update F x (l, (F x).2)) := by
  rw [← regs_set hj]
  ext1
  · rfl
  · rfl
  · rfl
  · funext y
    by_cases hy : y = j x
    · subst hy; simp [regs_R_at hj]
    · simp [hy]

theorem flagAny_run (hj : Function.Injective j) (S : Stacks T A) (F : Fin (r + 2) → LR A)
    (v : HS T Q A U) :
    ∃ v', v'.user = v.user ∧ v'.st = v.st ∧
      v'.flag = (List.finRange r).any (fun i => isBit ((F (oth i)).2.headD blank)) ∧
      (flagAny j).run (mk v (regs S j F)) = mk v' (regs S j F) := by
  set sc : Fin T → Fin (A + 4) := fun x =>
    if x ∈ others j then ((regs S j F).R x).head?.getD blank else v.scan x
  refine ⟨{ v with scan := sc, flag := (List.finRange r).any fun i => isBit (sc (j (oth i))) },
    rfl, rfl, ?_, by rw [flagAny, run_actThen, scanAll_run]; rfl⟩
  simp [sc, mem_others, regs_R_at hj, List.headD_eq_head?_getD]

theorem skipStep_run (hj : Function.Injective j) (S : Stacks T A) (d u : LR A)
    (rem : Fin r → List Bool) (Li X : Fin r → List (Fin (A + 4))) (v : HS T Q A U) :
    ∃ v', v'.user = v.user ∧ v'.st = v.st ∧
      v'.flag = (List.finRange r).any (fun i => !(rem i).tail.isEmpty) ∧
      (skipStep j).run (mk v (regs S j (cfg d (fun i => (Li i, (rem i).map bitSymbol ++ separator :: X i)) u))) =
        mk v' (regs S j (cfg d (fun i =>
          ((if (rem i).isEmpty then [] else [bitSymbol ((rem i).headD false)]) ++ Li i,
            (rem i).tail.map bitSymbol ++ separator :: X i)) u)) := by
  set F := cfg d (fun i => (Li i, (rem i).map bitSymbol ++ separator :: X i)) u
  set sc₁ : Fin T → Fin (A + 4) := fun x =>
    if x ∈ others j then ((regs S j F).R x).head?.getD blank else v.scan x
  set v₁ : HS T Q A U := { v with scan := sc₁ }
  have e₁ : (scanAll (others j)).run (mk v (regs S j F)) = mk v₁ (regs S j F) :=
    scanAll_run (regs S j F) _ v
  have ho : ∀ i, isBit (v₁.scan (j (oth i))) = !(rem i).isEmpty := fun i => by
    simp only [v₁, sc₁, mem_others, ↓reduceIte, regs_R_at hj, F, cfg_oth]
    rw [← List.headD_eq_head?_getD, isBit_head]
  obtain ⟨o₂, e₂⟩ := run_moveIf j hj S (fun _ sc i => isBit (sc (j (oth i)))) (List.finRange r) F v₁
    (List.nodup_finRange r)
  have hF : moved F (List.finRange r) (fun i => isBit (v₁.scan (j (oth i)))) =
      cfg d (fun i => ((if (rem i).isEmpty then [] else [bitSymbol ((rem i).headD false)]) ++ Li i,
        (rem i).tail.map bitSymbol ++ separator :: X i)) u := by
    simp only [F, moved_cfg, List.mem_finRange, true_and, ho]
    congr 1
    funext i
    rcases rem i with _ | ⟨c, t⟩ <;> simp
  obtain ⟨v', hu, hst, hfl, e₃⟩ := flagAny_run hj S (cfg d (fun i =>
    ((if (rem i).isEmpty then [] else [bitSymbol ((rem i).headD false)]) ++ Li i,
      (rem i).tail.map bitSymbol ++ separator :: X i)) u) { v₁ with sym := o₂ }
  refine ⟨v', hu, hst, ?_, ?_⟩
  · rw [hfl]; simp only [cfg_oth, isBit_head]
  · simp only [skipStep, run_actSeq_cons, run_actSeq_nil, e₁, e₂, hF, e₃]

/-- The skip loop moves every further input to the end of its word. -/
theorem skipLoop (hj : Function.Injective j) (S : Stacks T A) (d u : LR A)
    (X : Fin r → List (Fin (A + 4))) :
    ∀ (N : ℕ) (rem : Fin r → List Bool) (Li : Fin r → List (Fin (A + 4))) (v : HS T Q A U),
      (∀ i, (rem i).length ≤ N) → v.flag = (List.finRange r).any (fun i => !(rem i).isEmpty) →
      ∃ v' m, v'.user = v.user ∧ v'.st = v.st ∧ m ≤ 2 * N + 1 ∧
        Exec body (.loop (·.flag) (.act (skipStep j)))
          (mk v (regs S j (cfg d (fun i => (Li i, (rem i).map bitSymbol ++ separator :: X i)) u))) m
          (mk v' (regs S j (cfg d (fun i => ((rem i).reverse.map bitSymbol ++ Li i, separator :: X i)) u))) := by
  intro N
  induction N with
  | zero =>
    intro rem Li v hN hf
    have hrem : ∀ i, rem i = [] := fun i => List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (hN i))
    refine ⟨v, 1, rfl, rfl, by omega, ?_⟩
    have := Exec.loop_false (body := body) (f := (·.flag)) (p := .act (skipStep j))
      (s := mk v (regs S j (cfg d (fun i => (Li i, (rem i).map bitSymbol ++ separator :: X i)) u)))
      (by simp [hf, hrem, List.any_eq_false])
    simpa [hrem] using this
  | succ N ih =>
    intro rem Li v hN hf
    by_cases hany : (List.finRange r).any (fun i => !(rem i).isEmpty) = true
    · obtain ⟨v₁, hu₁, hst₁, hf₁, e⟩ := skipStep_run hj S d u rem Li X v
      obtain ⟨v', m, hu', hst', hm, he'⟩ := ih (fun i => (rem i).tail)
        (fun i => (if (rem i).isEmpty then [] else [bitSymbol ((rem i).headD false)]) ++ Li i) v₁
        (fun i => by have := hN i; simp; omega) hf₁
      refine ⟨v', m + 1 + 1, hu'.trans hu₁, hst'.trans hst₁, by omega, ?_⟩
      refine (Exec.loop_true (body := body) (f := (·.flag)) (by simpa [hf] using hany)
        (e ▸ Exec.act (body := body) (skipStep j) _) he').cast (by ring) ?_
      congr 3
      funext i
      rcases rem i with _ | ⟨c, t⟩ <;> simp
    · have hrem : ∀ i, rem i = [] := fun i => by
        simpa using (by simpa using hany : ∀ i, (rem i).isEmpty = true) i
      refine ⟨v, 1, rfl, rfl, by omega, ?_⟩
      have := Exec.loop_false (body := body) (f := (·.flag)) (p := .act (skipStep j))
        (s := mk v (regs S j (cfg d (fun i => (Li i, (rem i).map bitSymbol ++ separator :: X i)) u)))
        (by simpa [hf] using hany)
      simpa [hrem] using this

variable (j)

/-- Enter the rule's start state; in extend mode drop the output's last separator. -/
noncomputable def initAct : Act T Q A U :=
  actSeq [.load (fun v => { v with st := qset R R.q0 v.st }) .done,
    if ext then .pop (.lt (j Schoenhage.Strm.out)) (fun v _ => v) .done else .done, flagBit (j drv)]

/-- Emit symbol `k` of the flush of the rule's state, if any. -/
noncomputable def flushBr (k : ℕ) : Act T Q A U :=
  .branch (fun v => decide (k < (R.flush (qdec R v.st)).length))
    (.push (.lt (j Schoenhage.Strm.out))
      (fun v => Schoenhage.sym ((R.flush (qdec R v.st)).getD k none)) .done) .done

/-- Emit the flush of the rule's state. -/
noncomputable def flushAct : Act T Q A U := actSeq ((List.range R.B).map (flushBr R j))

/-- Step every input past its separator. -/
def finAct : Act T Q A U := actThen (mv1 (j drv)) (moveIf j (fun _ _ _ => true) (List.finRange r))

/-- The streaming primitive as a host program. -/
noncomputable def streamProg : Pr P T Q A U :=
  .seq (.act (initAct R ext j)) (.seq (.loop (·.flag) (.act (bitStep R j)))
    (.seq (.act (flagAny j)) (.seq (.loop (·.flag) (.act (skipStep j)))
      (.act (actThen (flushAct R j) (finAct j))))))

variable {j}

theorem initAct_run (hQ : Fintype.card R.Q ≤ Q) (hj : Function.Injective j) (S : Stacks T A)
    (d : LR A) (o : Fin r → LR A) (Lu Ru : List (Fin (A + 4))) (v : HS T Q A U) :
    ∃ v', v'.user = v.user ∧ qdec R v'.st = R.q0 ∧ v'.flag = isBit (d.2.headD blank) ∧
      (initAct R ext j).run (mk v (regs S j (cfg d o (Lu, Ru)))) =
        mk v' (regs S j (cfg d o (if ext then Lu.tail else Lu, Ru))) := by
  refine ⟨{ v with st := qset R R.q0 v.st, flag := isBit (d.2.headD blank) }, rfl,
    qdec_qset R hQ _ _, rfl, ?_⟩
  cases ext
  · simp [initAct, flagBit, Action.run, regs_R_at hj, flag_eq]
  · have := regs_setL hj S (cfg d o (Lu, Ru)) Schoenhage.Strm.out Lu.tail
    simp only [cfg_out, update_cfg_out] at this
    simp [initAct, flagBit, Action.run, regs_R_at hj, regs_L_at hj, update_lt, this, flag_eq]

theorem take_succ_rev {α : Type} (l : List α) (m : ℕ) (hm : m < l.length) (L : List α) :
    l[m] :: ((l.take m).reverse ++ L) = (l.take (m + 1)).reverse ++ L := by
  rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some, List.reverse_append,
    List.reverse_singleton, List.singleton_append, List.cons_append]

theorem flush_take (hj : Function.Injective j) (S : Stacks T A) (d : LR A) (o : Fin r → LR A)
    (Lu Ru : List (Fin (A + 4))) (v : HS T Q A U) :
    ∀ m, (actSeq ((List.range m).map (flushBr R j))).run (mk v (regs S j (cfg d o (Lu, Ru)))) =
      mk v (regs S j (cfg d o
        ((((R.flush (qdec R v.st)).take m).map Schoenhage.sym).reverse ++ Lu, Ru)))
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, run_actSeq_append, flush_take hj S d o Lu Ru v m]
    simp only [List.map_cons, List.map_nil, run_actSeq_cons, run_actSeq_nil, flushBr, Action.run,
      mk_var]
    by_cases hm : m < (R.flush (qdec R v.st)).length
    · have := regs_setL hj S (cfg d o
        ((((R.flush (qdec R v.st)).take m).map Schoenhage.sym).reverse ++ Lu, Ru)) Schoenhage.Strm.out
        (Schoenhage.sym ((R.flush (qdec R v.st)).getD m none) ::
          ((((R.flush (qdec R v.st)).take m).map Schoenhage.sym).reverse ++ Lu))
      simp only [cfg_out, update_cfg_out] at this
      simp only [hm, decide_true, ↓reduceIte, mk_stk, get_lt, regs_L_at hj, cfg_out, update_lt,
        store_mk, this]
      congr 4
      rw [List.getD_eq_getElem _ _ hm]
      have := take_succ_rev ((R.flush (qdec R v.st)).map Schoenhage.sym) m (by simpa using hm) Lu
      rw [List.getElem_map] at this
      simpa using this
    · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

theorem flush_run (hj : Function.Injective j) (S : Stacks T A) (d : LR A) (o : Fin r → LR A)
    (Lu Ru : List (Fin (A + 4))) (v : HS T Q A U) :
    (flushAct R j).run (mk v (regs S j (cfg d o (Lu, Ru)))) =
      mk v (regs S j (cfg d o (((R.flush (qdec R v.st)).map Schoenhage.sym).reverse ++ Lu, Ru))) := by
  rw [flushAct, flush_take R hj, List.take_of_length_le (R.hB _)]

theorem finAct_run (hj : Function.Injective j) (S : Stacks T A) (d : LR A) (o : Fin r → LR A)
    (u : LR A) (v : HS T Q A U) :
    ∃ v', v'.user = v.user ∧
      (finAct j).run (mk v (regs S j (cfg d o u))) = mk v' (regs S j (cfg (adv d) (fun i => adv (o i)) u)) := by
  rw [finAct, run_actThen, mv1_run hj]
  simp only [cfg_drv, update_cfg_drv]
  obtain ⟨o', e⟩ := run_moveIf j hj S (fun _ _ _ => true) (List.finRange r) (cfg (adv d) o u)
    { v with sym := d.2.head? } (List.nodup_finRange r)
  refine ⟨{ v with sym := o' }, rfl, e.trans ?_⟩
  simp [moved_cfg]

end Stream

/-! ### The primitive -/

section Impl

open Schoenhage.Strm (Rule go drv oth)

variable {A r : ℕ} (R : Rule r) (ext : Bool)

theorem time_bound (w : List Bool) (ws : Fin r → List Bool) :
    w.length + Schoenhage.Strm.rest R w ws + 5 ≤ Schoenhage.Strm.time R w ws := by
  unfold Schoenhage.Strm.time; omega

/-- The streaming primitive on host stacks. -/
noncomputable def streamImpl (C n : ℕ) (hC : 2 ≤ C) (hn : Fintype.card R.Q ≤ n) :
    TImpl C n (Schoenhage.streamPrim (a := A) R ext) where
  prog j := streamProg R ext j
  spec body j hj hQ τ hpre v S := by
    have hQ' := hn.trans hQ
    obtain ⟨hdrv, hoth, hout, vs, hvs, hext⟩ := hpre
    obtain ⟨w, R0, hw⟩ := Schoenhage.exists_cons hdrv
    choose ws Rs hws using fun i => Schoenhage.exists_cons (hoth i)
    have hcur : (τ drv).cur = w := by simp [WTape.cur, hw]
    have hcurs : (fun i => (τ (oth i)).cur) = ws := funext fun i => by simp [WTape.cur, hws i]
    rw [hcur, hcurs] at hvs
    set g := go R R.q0 w ws
    set Lu0 := if ext then (lcells (A := A) (τ Schoenhage.Strm.out).left).tail
      else lcells (τ Schoenhage.Strm.out).left
    have h0 : place S j τ = regs S j (cfg (lcells (τ drv).left, w.map bitSymbol ++ separator :: cells R0)
        (fun i => (lcells (τ (oth i)).left, (ws i).map bitSymbol ++ separator :: cells (Rs i)))
        (lcells (τ Schoenhage.Strm.out).left, [])) := by
      rw [place_eq_regs]
      congr 1
      exact cfg_ext (by simp [hw, cells_cons']) (fun i => by simp [hws i, cells_cons'])
        (by simp [hout, cells])
    -- init
    obtain ⟨v₀, hu₀, hq₀, hf₀, e₀⟩ := initAct_run R ext hQ' hj S
      (lcells (τ drv).left, w.map bitSymbol ++ separator :: cells R0)
      (fun i => (lcells (τ (oth i)).left, (ws i).map bitSymbol ++ separator :: cells (Rs i)))
      (lcells (τ Schoenhage.Strm.out).left) [] v
    -- bits
    obtain ⟨v₁, hu₁, hq₁, pre, hpre, he₁⟩ := bitLoop R body hQ' hj S (cells R0) (fun i => cells (Rs i)) []
      w R.q0 ws (lcells (τ drv).left) (fun i => lcells (τ (oth i)).left) Lu0 v₀ hq₀
      (by rw [hf₀]; exact isBit_head w _)
    -- skip
    set d₁ : LR A := ((w.map bitSymbol).reverse ++ lcells (τ drv).left, separator :: cells R0)
    set u₁ : LR A := ((g.2.1.map Schoenhage.sym).reverse ++ Lu0, [])
    obtain ⟨v₂, hu₂, hst₂, hf₂, e₂⟩ := flagAny_run hj S (cfg d₁
      (fun i => ((pre i).reverse.map bitSymbol ++ lcells (τ (oth i)).left,
        (g.2.2 i).map bitSymbol ++ separator :: cells (Rs i))) u₁) v₁
    obtain ⟨v₃, m, hu₃, hst₃, hm, he₃⟩ := skipLoop body hj S d₁ u₁ (fun i => cells (Rs i))
      (Schoenhage.Strm.rest R w ws) g.2.2 (fun i => (pre i).reverse.map bitSymbol ++ lcells (τ (oth i)).left)
      v₂ (fun i => Finset.le_sup (f := fun i => (g.2.2 i).length) (Finset.mem_univ i))
      (by rw [hf₂]; simp only [cfg_oth, isBit_head])
    -- flush and step past the separators
    have hq₃ : qdec R v₃.st = g.1 := by rw [hst₃, hst₂]; exact hq₁
    have e₄ := flush_run R hj S d₁ (fun i => ((g.2.2 i).reverse.map bitSymbol ++
      ((pre i).reverse.map bitSymbol ++ lcells (τ (oth i)).left), separator :: cells (Rs i)))
      ((g.2.1.map Schoenhage.sym).reverse ++ Lu0) [] v₃
    rw [hq₃] at e₄
    obtain ⟨v₄, hu₄, e₅⟩ := finAct_run hj S d₁ (fun i => ((g.2.2 i).reverse.map bitSymbol ++
      ((pre i).reverse.map bitSymbol ++ lcells (τ (oth i)).left), separator :: cells (Rs i)))
      (((R.flush g.1).map Schoenhage.sym).reverse ++ ((g.2.1.map Schoenhage.sym).reverse ++ Lu0), []) v₃
    refine ⟨v₄, 1 + ((2 * w.length + 1) + (1 + (m + 1))), ?_, ?_, ?_⟩
    · rw [hu₄, hu₃, hu₂, hu₁, hu₀]
    · have ht := time_bound R w ws
      have h2 := Nat.mul_le_mul_right (Schoenhage.Strm.time R w ws + 1) hC
      simp only [hcur, hcurs]
      omega
    · rw [h0]
      refine Exec.seq ((Exec.act (body := body) _ _).cast rfl e₀) (Exec.seq he₁
        (Exec.seq ((Exec.act (body := body) _ _).cast rfl e₂) (Exec.seq he₃
          ((Exec.act (body := body) _ _).cast rfl ?_))))
      rw [run_actThen, e₄, e₅, place_eq_regs]
      congr 2
      refine cfg_ext ?_ (fun i => ?_) ?_
      · simp [d₁, Schoenhage.streamSem, Schoenhage.Strm.drv_ne_out, WTape.next, WTape.cur, hw, lcells,
          List.map_reverse]
      · have hp : pre i ++ g.2.2 i = ws i := hpre i
        simp only [cfg_oth, adv_cons, Schoenhage.streamSem, Schoenhage.Strm.oth_ne_out, ↓reduceIte,
          WTape.next, WTape.cur, hws i, List.headD_cons, List.tail_cons, lcells]
        rw [← hp]
        simp [List.map_reverse]
      · have hout' : g.2.1 ++ R.flush g.1 = syms vs := hvs
        have ecells : ((syms vs).map (Schoenhage.sym (a := A))) = cells vs := rfl
        simp only [cfg_out, Schoenhage.streamSem, ↓reduceIte]
        rw [hcur, hcurs, hvs, Schoenhage.parse_syms]
        rw [← List.append_assoc, ← List.reverse_append, ← List.map_append, hout', ecells]
        cases ext
        · simp [Lu0, WTape.put, lcells_append, lcells_reverse, cells]
        · obtain ⟨hL, hV⟩ := hext rfl
          obtain ⟨u, L, hl⟩ := Schoenhage.exists_cons hL
          obtain ⟨x, xs, hx⟩ := Schoenhage.exists_cons hV
          subst hx
          simp [Lu0, WTape.put, hl, lcells, lcells_append, lcells_reverse, cells,
            Schoenhage.syms_cons, Schoenhage.sym, Function.comp_def, List.map_reverse]

theorem allTM_op0 {C n t : ℕ} (hC : 2 ≤ C) (R : Rule 0) (hn : Fintype.card R.Q ≤ n) (ext : Bool)
    {d o : Fin t} (h : d ≠ o) : AllTM C n (Schoenhage.op0 (a := A) R ext d o h) :=
  .prim ⟨streamImpl R ext C n hC hn⟩

theorem allTM_op1 {C n t : ℕ} (hC : 2 ≤ C) (R : Rule 1) (hn : Fintype.card R.Q ≤ n) (ext : Bool)
    {d e o : Fin t} (h1 : d ≠ e) (h2 : d ≠ o) (h3 : e ≠ o) :
    AllTM C n (Schoenhage.op1 (a := A) R ext d e o h1 h2 h3) :=
  .prim ⟨streamImpl R ext C n hC hn⟩

end Impl

end IntegerMultBounds.MathlibTM2.Host.WordCmd
