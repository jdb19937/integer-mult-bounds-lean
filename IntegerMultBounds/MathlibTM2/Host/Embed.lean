module

public import IntegerMultBounds.MathlibTM2.Host.Core

/-!
# Host programs on a larger register file

A host program on `T` tapes runs unchanged inside a host with `T'` tapes along an injective
register map `e : Fin T → Fin T'`.

**Maps.** `embK e : HK T → HK T'` sends `inp`, `out` to themselves and the stacks of tape `i` to
those of tape `e i`; the alphabets agree along it (`embCast`, `embUncast`). `embInv e` is the
partial inverse of `e`, `embExt e f g` the function equal to `f ∘ e⁻¹` on the image of `e` and to
`g` off it. On local states, `embDn e : HS T' → HS T` precomposes `scan` and the actions of `nxt`
with `e`, and `embUp e v w` writes `v` back into `w` on the image of `e`, keeping `w` off it
(`embDn_up : embDn e (embUp e v w) = v`). On stacks, `embStk e S'` reads `S'` along `e`, and
`embOvr e f B` places the stack function `f` of the small file on the image of `e` over the
background `B`.

**Programs.** `embAct e` and `embProg e ι` run every test and every value of a program on
`embDn e` of the local state and write every update back through `embUp e`; `embProg` renames
the called procedures through `ι : P → P'`. A big table `body'` contains the embedded table when
`body' (ι f) = embProg e ι (body f)` (`embTab` for `ι = id`, `embTabExt` for an injective `ι`
next to other procedures).

**Simulation** (`exec_emb`). An execution of `p` from `mk v S` to `mk v₁ S₁` in `n` steps gives
an execution of `embProg e ι p` in exactly `n` steps from every `mk v' S'` with `embDn e v' = v`
and `embStk e S' = S`, ending at `mk v₁' S₁'` with `embDn e v₁' = v₁` (so `v₁'.user = v₁.user`),
`embStk e S₁' = S₁`, and `S₁'` equal to `S'` on every tape outside the image of `e`
(`exec_emb_ovr`: `S₁' = embOvr e S₁.get S'`). Every action of the host language reads the local
state only through its semantic functions, so the multitape simulation `foreign` (whose
`peekScan`, `tapeAct` read and write `scan` and `nxt`) is covered by the same proof.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack


variable {T T' Q A : ℕ} {U : Type}

/-! ### The maps -/

section Maps

variable (e : Fin T → Fin T')

/-- The stack map along `e`. -/
def embK : HK T → HK T'
  | .inp => .inp
  | .out => .out
  | .lt i => .lt (e i)
  | .rt i => .rt (e i)

/-- A symbol of stack `k` as a symbol of stack `embK e k`. -/
def embCast : (k : HK T) → HΓ A k → HΓ (T := T') A (embK e k)
  | .inp, x => x
  | .out, x => x
  | .lt _, x => x
  | .rt _, x => x

/-- A symbol of stack `embK e k` as a symbol of stack `k`. -/
def embUncast : (k : HK T) → HΓ (T := T') A (embK e k) → HΓ A k
  | .inp, x => x
  | .out, x => x
  | .lt _, x => x
  | .rt _, x => x

/-- The partial inverse of `e`. -/
def embInv (j : Fin T') : Option (Fin T) := (List.finRange T).find? fun i => e i = j

/-- `f` along the inverse of `e` on the image of `e`, `g` off it. -/
def embExt {β : Type} (f : Fin T → β) (g : Fin T' → β) (j : Fin T') : β :=
  match embInv e j with
  | some i => f i
  | none => g j

/-- The local state of the small file read from a state of the big file. -/
def embDn (w : HS T' Q A U) : HS T Q A U where
  flag := w.flag
  sym := w.sym
  st := w.st
  scan := w.scan ∘ e
  nxt := w.nxt.map fun p => (p.1, p.2 ∘ e)
  user := w.user

/-- The local state `v` of the small file written back into the state `w` of the big file. -/
def embUp (v : HS T Q A U) (w : HS T' Q A U) : HS T' Q A U where
  flag := v.flag
  sym := v.sym
  st := v.st
  scan := embExt e v.scan w.scan
  nxt := v.nxt.map fun p => (p.1, embExt e p.2 fun j =>
    (w.nxt.map fun q => q.2 j).getD ((⟨0, by omega⟩ : Fin (A + 4)), Move.stay))
  user := v.user

/-- The stacks of the big file read along `e`. -/
def embStk (S' : Stacks T' A) : Stacks T A := ⟨S'.inp, S'.out, S'.L ∘ e, S'.R ∘ e⟩

/-- The stack function `f` of the small file placed on the image of `e` over the background
`B`. -/
def embOvr (f : ∀ k : HK T, List (HΓ A k)) (B : Stacks T' A) : Stacks T' A :=
  ⟨f .inp, f .out, embExt e (fun i => f (.lt i)) B.L, embExt e (fun i => f (.rt i)) B.R⟩

end Maps

/-! ### Embedded programs -/

section Progs

variable (e : Fin T → Fin T')

/-- An action of the small file run on the big file. -/
def embAct : Act T Q A U → Act T' Q A U
  | .done => .done
  | .push k f a => .push (embK e k) (fun w => embCast e k (f (embDn e w))) (embAct a)
  | .peek k f a =>
      .peek (embK e k) (fun w o => embUp e (f (embDn e w) (o.map (embUncast e k))) w) (embAct a)
  | .pop k f a =>
      .pop (embK e k) (fun w o => embUp e (f (embDn e w) (o.map (embUncast e k))) w) (embAct a)
  | .load f a => .load (fun w => embUp e (f (embDn e w)) w) (embAct a)
  | .branch f a b => .branch (fun w => f (embDn e w)) (embAct a) (embAct b)

/-- A program of the small file run on the big file, calls renamed through `ι`. -/
def embProg {P P' : Type} (ι : P → P') : Pr P T Q A U → Pr P' T' Q A U
  | .act a => .act (embAct e a)
  | .seq p q => .seq (embProg ι p) (embProg ι q)
  | .cond f p q => .cond (fun w => f (embDn e w)) (embProg ι p) (embProg ι q)
  | .loop f p => .loop (fun w => f (embDn e w)) (embProg ι p)
  | .call f => .call (ι f)

/-- The embedded procedure table on the same procedure names. -/
def embTab {P : Type} (body : P → Pr P T Q A U) : P → Pr P T' Q A U :=
  fun f => embProg e id (body f)

/-- The embedded procedure table on the image of an injective `ι : P → P'`, the procedures
`other` elsewhere. -/
noncomputable def embTabExt {P P' : Type} (ι : P → P') (body : P → Pr P T Q A U)
    (other : P' → Pr P' T' Q A U) : P' → Pr P' T' Q A U :=
  Function.extend ι (fun f => embProg e ι (body f)) other

end Progs

/-! ### Lemmas on the maps -/

section Lemmas

variable {e : Fin T → Fin T'}

theorem embInv_some {j : Fin T'} {i : Fin T} (h : embInv e j = some i) : e i = j := by
  have := List.find?_some h
  simpa using this

theorem embInv_none {j : Fin T'} (h : embInv e j = none) (i : Fin T) : e i ≠ j := by
  have := List.find?_eq_none.1 h i (List.mem_finRange i)
  simpa using this

theorem embInv_apply (he : Function.Injective e) (i : Fin T) : embInv e (e i) = some i := by
  cases h : embInv e (e i) with
  | none => exact absurd rfl (embInv_none h i)
  | some i' => rw [he (embInv_some h)]

theorem embInv_eq_none {j : Fin T'} (h : ∀ i, e i ≠ j) : embInv e j = none := by
  cases hj : embInv e j with
  | none => rfl
  | some i => exact absurd (embInv_some hj) (h i)

theorem embExt_apply (he : Function.Injective e) {β : Type} (f : Fin T → β) (g : Fin T' → β)
    (i : Fin T) : embExt e f g (e i) = f i := by
  simp only [embExt, embInv_apply he]

theorem embExt_off {β : Type} (f : Fin T → β) (g : Fin T' → β) {j : Fin T'} (h : ∀ i, e i ≠ j) :
    embExt e f g j = g j := by
  simp only [embExt, embInv_eq_none h]

theorem embExt_comp {β : Type} (g : Fin T' → β) : embExt e (g ∘ e) g = g := by
  funext j
  unfold embExt
  cases h : embInv e j with
  | none => rfl
  | some i => simp [embInv_some h]

theorem embExt_comp_e (he : Function.Injective e) {β : Type} (f : Fin T → β) (g : Fin T' → β) :
    embExt e f g ∘ e = f := by
  funext i
  exact embExt_apply he f g i

theorem embDn_up (he : Function.Injective e) (v : HS T Q A U) (w : HS T' Q A U) :
    embDn e (embUp e v w) = v := by
  rcases v with ⟨fl, sy, st, sc, nx, us⟩
  simp only [embDn, embUp, embExt_comp_e he]
  congr 1
  cases nx with
  | none => rfl
  | some p => simp [embExt_comp_e he]

@[simp] theorem embDn_user (w : HS T' Q A U) : (embDn e w).user = w.user := rfl

theorem embUncast_comp (k : HK T) : embUncast (A := A) e k ∘ embCast e k = id := by
  cases k <;> rfl

theorem embOvr_get (he : Function.Injective e) (f : ∀ k : HK T, List (HΓ A k)) (B : Stacks T' A)
    (k : HK T) : (embOvr e f B).get (embK e k) = (f k).map (embCast e k) := by
  cases k <;> simp only [embOvr, embK, Stacks.get, embExt_apply he] <;> exact (List.map_id _).symm

theorem embOvr_update (he : Function.Injective e) (f : ∀ k : HK T, List (HΓ A k))
    (B : Stacks T' A) (k : HK T) (l : List (HΓ A k)) :
    Function.update (embOvr e f B).get (embK e k) (l.map (embCast e k)) =
      (embOvr e (Function.update f k l) B).get := by
  cases k with
  | inp =>
      rw [show l.map (embCast e .inp) = l from List.map_id l]
      show Function.update (embOvr e f B).get .inp l = _
      rw [update_inp]
      congr 1
  | out =>
      rw [show l.map (embCast e .out) = l from List.map_id l]
      show Function.update (embOvr e f B).get .out l = _
      rw [update_out]
      congr 1
  | lt i =>
      rw [show l.map (embCast e (.lt i)) = l from List.map_id l]
      show Function.update (embOvr e f B).get (.lt (e i)) l = _
      rw [update_lt]
      congr 1
      refine Stacks.ext ?_ ?_ ?_ ?_
      · simp [embOvr]
      · simp [embOvr]
      · funext j
        by_cases hj : j = e i
        · subst hj; simp [embOvr, embExt_apply he]
        · dsimp only
          rw [Function.update_of_ne hj]
          simp only [embOvr]
          unfold embExt
          cases h : embInv e j with
          | none => rfl
          | some i' =>
              have : i' ≠ i := fun h' => hj (by rw [← embInv_some h, h'])
              simp [Function.update_of_ne (show HK.lt i' ≠ HK.lt i by simpa using this)]
      · funext j; simp only [embOvr]; unfold embExt
        cases h : embInv e j with
        | none => rfl
        | some i' => simp
  | rt i =>
      rw [show l.map (embCast e (.rt i)) = l from List.map_id l]
      show Function.update (embOvr e f B).get (.rt (e i)) l = _
      rw [update_rt]
      congr 1
      refine Stacks.ext ?_ ?_ ?_ ?_
      · simp [embOvr]
      · simp [embOvr]
      · funext j; simp only [embOvr]; unfold embExt
        cases h : embInv e j with
        | none => rfl
        | some i' => simp
      · funext j
        by_cases hj : j = e i
        · subst hj; simp [embOvr, embExt_apply he]
        · dsimp only
          rw [Function.update_of_ne hj]
          simp only [embOvr]
          unfold embExt
          cases h : embInv e j with
          | none => rfl
          | some i' =>
              have : i' ≠ i := fun h' => hj (by rw [← embInv_some h, h'])
              simp [Function.update_of_ne (show HK.rt i' ≠ HK.rt i by simpa using this)]

theorem embStk_L (S' : Stacks T' A) (i : Fin T) : (embStk e S').L i = S'.L (e i) := rfl

theorem embStk_R (S' : Stacks T' A) (i : Fin T) : (embStk e S').R i = S'.R (e i) := rfl

/-- The big stacks over themselves. -/
theorem embOvr_stk (S' : Stacks T' A) : embOvr e (embStk e S').get S' = S' := by
  rcases S' with ⟨i, o, L, R⟩
  simp only [embOvr, embStk, Stacks.get]
  congr 1
  · exact embExt_comp L
  · exact embExt_comp R

/-- The small stacks read back from the big ones. -/
theorem embStk_ovr (he : Function.Injective e) (S : Stacks T A) (B : Stacks T' A) :
    embStk e (embOvr e S.get B) = S := by
  rcases S with ⟨i, o, L, R⟩
  simp only [embOvr, embStk, Stacks.get, embExt_comp_e he]

/-- Off the image of `e` the stacks are the background. -/
theorem embOvr_off (f : ∀ k : HK T, List (HΓ A k)) (B : Stacks T' A) {j : Fin T'}
    (hj : ∀ i, e i ≠ j) : (embOvr e f B).L j = B.L j ∧ (embOvr e f B).R j = B.R j :=
  ⟨embExt_off _ _ hj, embExt_off _ _ hj⟩

/-- A change of one register of the small file is a change of its image. -/
theorem embOvr_updR (he : Function.Injective e) (S : Stacks T A) (B : Stacks T' A) (x : Fin T)
    (l : List (Fin (A + 4))) :
    embOvr e ({ S with R := Function.update S.R x l } : Stacks T A).get B =
      { embOvr e S.get B with R := Function.update (embOvr e S.get B).R (e x) l } := by
  simp only [embOvr, Stacks.get]
  congr 1
  funext j
  by_cases hj : j = e x
  · subst hj; simp [embExt_apply he]
  · rw [Function.update_of_ne hj]
    unfold embExt
    cases h : embInv e j with
    | none => rfl
    | some i' =>
        have : i' ≠ x := fun h' => hj (by rw [← embInv_some h, h'])
        simp [Function.update_of_ne this]

end Lemmas

/-! ### Simulation -/

section Sim

variable {e : Fin T → Fin T'} (he : Function.Injective e)
include he

/-- One embedded action: the big store over the background `B` follows the small store. -/
theorem embAct_run (B : Stacks T' A) :
    ∀ (a : Act T Q A U) (s : Store (HΓ (T := T) A) (HS T Q A U)) (w : HS T' Q A U),
      embDn e w = s.var → ∃ w', embDn e w' = (a.run s).var ∧
        (embAct e a).run ⟨w, (embOvr e s.stk B).get⟩ = ⟨w', (embOvr e (a.run s).stk B).get⟩ := by
  intro a
  induction a with
  | done => intro s w hw; exact ⟨w, hw, rfl⟩
  | push k f a ih =>
      intro s w hw
      show ∃ w', _ ∧ Action.run (embAct e a) ⟨w, Function.update (embOvr e s.stk B).get (embK e k)
        (embCast e k (f (embDn e w)) :: (embOvr e s.stk B).get (embK e k))⟩ = _
      rw [embOvr_get he, hw, ← List.map_cons, embOvr_update he]
      exact ih ⟨s.var, Function.update s.stk k (f s.var :: s.stk k)⟩ w hw
  | peek k f a ih =>
      intro s w hw
      show ∃ w', _ ∧ Action.run (embAct e a) ⟨embUp e (f (embDn e w)
        (((embOvr e s.stk B).get (embK e k)).head?.map (embUncast e k))) w,
          (embOvr e s.stk B).get⟩ = _
      rw [embOvr_get he, hw, List.head?_map, Option.map_map, embUncast_comp, Option.map_id]
      exact ih ⟨f s.var (s.stk k).head?, s.stk⟩ _ (embDn_up he _ _)
  | pop k f a ih =>
      intro s w hw
      show ∃ w', _ ∧ Action.run (embAct e a) ⟨embUp e (f (embDn e w)
        (((embOvr e s.stk B).get (embK e k)).head?.map (embUncast e k))) w,
          Function.update (embOvr e s.stk B).get (embK e k)
            ((embOvr e s.stk B).get (embK e k)).tail⟩ = _
      rw [embOvr_get he, hw, List.head?_map, Option.map_map, embUncast_comp, Option.map_id,
        ← List.map_tail, embOvr_update he]
      exact ih ⟨f s.var (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩ _
        (embDn_up he _ _)
  | load f a ih =>
      intro s w hw
      show ∃ w', _ ∧ Action.run (embAct e a) ⟨embUp e (f (embDn e w)) w,
        (embOvr e s.stk B).get⟩ = _
      rw [hw]
      exact ih ⟨f s.var, s.stk⟩ _ (embDn_up he _ _)
  | branch f a b iha ihb =>
      intro s w hw
      have hw' : f (embDn e w) = f s.var := by rw [hw]
      cases hf : f s.var with
      | true =>
          have e1 : Action.run (.branch f a b) s = a.run s := by simp [Action.run, hf]
          have e2 : (embAct e (.branch f a b)).run ⟨w, (embOvr e s.stk B).get⟩ =
              (embAct e a).run ⟨w, (embOvr e s.stk B).get⟩ := by
            simp [embAct, Action.run, hw', hf]
          rw [e1, e2]
          exact iha s w hw
      | false =>
          have e1 : Action.run (.branch f a b) s = b.run s := by simp [Action.run, hf]
          have e2 : (embAct e (.branch f a b)).run ⟨w, (embOvr e s.stk B).get⟩ =
              (embAct e b).run ⟨w, (embOvr e s.stk B).get⟩ := by
            simp [embAct, Action.run, hw', hf]
          rw [e1, e2]
          exact ihb s w hw

variable {P P' : Type} {ι : P → P'} {body : P → Pr P T Q A U} {body' : P' → Pr P' T' Q A U}
  (hbody : ∀ f, body' (ι f) = embProg e ι (body f))
include hbody

/-- The simulation on stores, over a fixed background `B`. -/
theorem embProg_exec (B : Stacks T' A) {p : Pr P T Q A U}
    {s t : Store (HΓ (T := T) A) (HS T Q A U)} {n : ℕ} (h : Exec body p s n t) :
    ∀ w : HS T' Q A U, embDn e w = s.var → ∃ w', embDn e w' = t.var ∧
      Exec body' (embProg e ι p) ⟨w, (embOvr e s.stk B).get⟩ n ⟨w', (embOvr e t.stk B).get⟩ := by
  induction h with
  | act a s =>
      intro w hw
      obtain ⟨w', hw', hr⟩ := embAct_run he B a s w hw
      exact ⟨w', hw', hr ▸ Exec.act _ _⟩
  | seq _ _ ihp ihq =>
      intro w hw
      obtain ⟨w₁, hw₁, h₁⟩ := ihp w hw
      obtain ⟨w₂, hw₂, h₂⟩ := ihq w₁ hw₁
      exact ⟨w₂, hw₂, Exec.seq h₁ h₂⟩
  | @cond_true f p q s t n hf _ ih =>
      intro w hw
      obtain ⟨w', hw', h'⟩ := ih w hw
      exact ⟨w', hw', Exec.cond_true (f := fun w => f (embDn e w))
        (show f (embDn e w) = true by rw [hw]; exact hf) h'⟩
  | @cond_false f p q s t n hf _ ih =>
      intro w hw
      obtain ⟨w', hw', h'⟩ := ih w hw
      exact ⟨w', hw', Exec.cond_false (f := fun w => f (embDn e w))
        (show f (embDn e w) = false by rw [hw]; exact hf) h'⟩
  | @loop_false f p s hf =>
      intro w hw
      exact ⟨w, hw, Exec.loop_false (f := fun w => f (embDn e w))
        (show f (embDn e w) = false by rw [hw]; exact hf)⟩
  | @loop_true f p s t u m n hf _ _ ihp ihl =>
      intro w hw
      obtain ⟨w₁, hw₁, h₁⟩ := ihp w hw
      obtain ⟨w₂, hw₂, h₂⟩ := ihl w₁ hw₁
      exact ⟨w₂, hw₂, Exec.loop_true (f := fun w => f (embDn e w))
        (show f (embDn e w) = true by rw [hw]; exact hf) h₁ h₂⟩
  | @call f s t n _ ih =>
      intro w hw
      obtain ⟨w', hw', h'⟩ := ih w hw
      refine ⟨w', hw', Exec.call ?_⟩
      rw [hbody]
      exact h'

/-- **The simulation**, with the final stacks in closed form: the small final stacks on the image
of `e`, the initial big stacks off it. -/
theorem exec_emb_ovr {p : Pr P T Q A U} {v v₁ : HS T Q A U} {S S₁ : Stacks T A} {n : ℕ}
    (h : Exec body p (mk v S) n (mk v₁ S₁)) (v' : HS T' Q A U) (hv : embDn e v' = v)
    (S' : Stacks T' A) (hS : embStk e S' = S) :
    ∃ v₁', embDn e v₁' = v₁ ∧ v₁'.user = v₁.user ∧
      Exec body' (embProg e ι p) (mk v' S') n (mk v₁' (embOvr e S₁.get S')) := by
  obtain ⟨w', hw', h'⟩ := embProg_exec he hbody S' h v' hv
  have hw₁ : embDn e w' = v₁ := hw'
  refine ⟨w', hw₁, by rw [← hw₁]; rfl, ?_⟩
  have e1 : embOvr e (mk v S).stk S' = S' := by
    rw [mk_stk, ← hS]; exact embOvr_stk S'
  rw [e1] at h'
  exact h'

/-- **The simulation.** An execution of `p` on the small file from `mk v S` to `mk v₁ S₁` in
`n` steps gives an execution of `embProg e ι p` on the big file in `n` steps from every
`mk v' S'` with `embDn e v' = v` and `embStk e S' = S` (`S'` agrees with `S` on `inp`, `out`
and the image of `e`), to `mk v₁' S₁'` with `embDn e v₁' = v₁`, `v₁'.user = v₁.user`,
`embStk e S₁' = S₁`, and `S₁'` equal to `S'` off the image of `e`. -/
theorem exec_emb {p : Pr P T Q A U} {v v₁ : HS T Q A U} {S S₁ : Stacks T A} {n : ℕ}
    (h : Exec body p (mk v S) n (mk v₁ S₁)) (v' : HS T' Q A U) (hv : embDn e v' = v)
    (S' : Stacks T' A) (hS : embStk e S' = S) :
    ∃ v₁' S₁', Exec body' (embProg e ι p) (mk v' S') n (mk v₁' S₁') ∧ embDn e v₁' = v₁ ∧
      v₁'.user = v₁.user ∧ embStk e S₁' = S₁ ∧
      ∀ j, (∀ i, e i ≠ j) → S₁'.L j = S'.L j ∧ S₁'.R j = S'.R j := by
  obtain ⟨v₁', hv₁, hu, h'⟩ := exec_emb_ovr he hbody h v' hv S' hS
  exact ⟨v₁', _, h', hv₁, hu, embStk_ovr he S₁ S', fun j hj => embOvr_off _ _ hj⟩

end Sim

end IntegerMultBounds.MathlibTM2.Host
