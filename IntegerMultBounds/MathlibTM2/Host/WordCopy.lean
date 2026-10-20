module

public import IntegerMultBounds.MathlibTM2.Host.WordStream
public import IntegerMultBounds.Schoenhage.Reverse
public import IntegerMultBounds.Schoenhage.Chunk

/-!
# Reverse and chunk on host stacks

Host implementations of the word-program primitives `Schoenhage.Reverse.prim` (`reverseImpl`) and
`Schoenhage.Chunk.prim` (`chunkImpl`).

**Reverse.** The source's current word, reversed, becomes a new word of the destination, and the
source steps past it. On stacks: the source's head runs over its word (`moveRL`), then back, every
bit popped from the source's left stack onto the destination's left stack and back onto the
source's right stack (`copyLoop`), which reverses the word onto the destination; a separator ends
it, and the source's head runs over the word and its separator again. `6 n + 8` steps for an
`n`-bit word, against the primitive's cost `3 n + 10`; any `C ≥ 2`.

**Chunk.** The source's current word, cut into pieces of the width `W` of the unary register, as
new words of the destination. On stacks: each bit goes from the source onto the destination while
the register's head steps one cell (`chStep`); where the register runs out, a separator ends the
piece and the register is rewound (`endPiece`), and so for a final partial piece. The emitted
symbols are those of the pieces (`chunkPush_cut`). At most `12 n + 8` steps, against the cost
`4 n + 3`; any `C ≥ 3`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Host.WordCmd

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.Schoenhage (WTape Prim Cmd cells clen syms)

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

/-! ### Reverse -/

section Reverse

variable {A : ℕ}

theorem isBit_bits (w : List Bool) : ∀ e ∈ w.map (bitSymbol (a := A)), isBit e = true := by
  intro e he; obtain ⟨b, -, rfl⟩ := List.mem_map.mp he; simp [isBit]

theorem isBit_lcells (L : List (List Bool)) : ((lcells (A := A) L).head?.map isBit).getD false = false := by
  cases L <;> simp [lcells, isBit]

/-- Reverse on host stacks. -/
noncomputable def reverseImpl (C n : ℕ) (hC : 2 ≤ C) : TImpl C n (Schoenhage.Reverse.prim (a := A)) where
  prog j := .seq (moveRL (j 0) isBit) (.seq (copyLoop (j 0) (j 1) isBit)
    (.seq (.act (.push (.lt (j 1)) (fun _ => separator) .done))
      (.seq (moveRL (j 0) isBit) (.act (mv1 (j 0))))))
  spec body j hj _ τ hpre v S := by
    obtain ⟨h0, h1⟩ := hpre
    obtain ⟨w, R0, hw⟩ := Schoenhage.exists_cons h0
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    set F0 : Fin 2 → LR A := fun x => (lcells (τ x).left, cells (τ x).right)
    have hF0 : (F0 0).2 = w.map bitSymbol ++ separator :: cells R0 := by simp [F0, hw, cells_cons']
    obtain ⟨v₁, hu₁, e₁⟩ := moveRL_exec body hj S 0 isBit (w.map bitSymbol) (separator :: cells R0)
      F0 v (isBit_bits w) (by simp [isBit]) hF0
    set F1 := Function.update F0 0 ((w.map bitSymbol).reverse ++ (F0 0).1, separator :: cells R0)
    obtain ⟨v₂, hu₂, e₂⟩ := copyLoop_exec body hj S h01 isBit ((w.map bitSymbol).reverse)
      (lcells (τ 0).left) F1 v₁ (fun e he => isBit_bits w e (List.mem_reverse.mp he)) (isBit_lcells _)
      (by simp [F1, F0])
    set F2 := Function.update (Function.update F1 0 (lcells (τ 0).left,
      ((w.map bitSymbol).reverse).reverse ++ (F1 0).2)) 1
      (((w.map bitSymbol).reverse).reverse ++ (F1 1).1, (F1 1).2)
    set F3 := Function.update F2 1 (separator :: (F2 1).1, (F2 1).2)
    have e₃ : (Action.push (.lt (j 1)) (fun _ => separator) .done : Act _ _ A _).run (mk v₂ (regs S j F2)) =
        mk v₂ (regs S j F3) := by
      simp [Action.run, regs_L_at hj, regs_updL hj, F3]
    have hF3 : (F3 0).2 = w.map bitSymbol ++ separator :: cells R0 := by
      simp [F3, F2, F1]
    obtain ⟨v₄, hu₄, e₄⟩ := moveRL_exec body hj S 0 isBit (w.map bitSymbol) (separator :: cells R0)
      F3 v₂ (isBit_bits w) (by simp [isBit]) hF3
    have e₅ := mv1_run (Q := _) (U := _) hj S
      (Function.update F3 0 ((w.map bitSymbol).reverse ++ (F3 0).1, separator :: cells R0)) 0 v₄
    refine ⟨{ v₄ with sym := (separator :: cells R0).head? },
      (2 * w.length + 2) + ((2 * w.length + 2) + (1 + ((2 * w.length + 2) + 1))), ?_, ?_, ?_⟩
    · simp only; rw [hu₄, hu₂, hu₁]
    · have hcur : (τ 0).cur = w := by simp [WTape.cur, hw]
      have := two_le_mul (x := 3 * w.length + 10 + 1) hC
      simp only [hcur] at this ⊢
      omega
    · simp only [place_eq_regs]
      refine Exec.seq (by simpa using e₁) (Exec.seq (by simpa using e₂)
        (Exec.seq ((Exec.act (body := body) _ _).cast rfl e₃) (Exec.seq (e₄.cast (by simp) rfl)
          ((Exec.act (body := body) _ _).cast rfl (e₅.trans ?_)))))
      congr 2
      funext x
      fin_cases x
      · simp [F3, F2, F1, F0, WTape.next, WTape.cur, hw, lcells,
          List.map_reverse]
      · simp [F3, F2, F1, F0, h01, WTape.cur, hw, lcells, h1, cells]

theorem allTM_revw {C n t : ℕ} (hC : 2 ≤ C) {s d : Fin t} (h : s ≠ d) :
    AllTM C n (Schoenhage.revw (a := A) s d h) :=
  .prim ⟨reverseImpl C n hC⟩

end Reverse

/-! ### Chunk: the emitted symbols -/

section ChunkMath

open Schoenhage (cut cut_cons cut_nil)

/-- The symbols emitted for the bits `bs` from position `p` of a piece of width `W`: every bit,
and a separator after each completed piece. -/
def chunkPush (W : ℕ) : ℕ → List Bool → List (Option Bool)
  | _, [] => []
  | p, b :: bs => some b :: if p + 1 = W then none :: chunkPush W 0 bs else chunkPush W (p + 1) bs

theorem chunkPush_full (W : ℕ) (rest : List Bool) :
    ∀ (l : List Bool) (p : ℕ), l ≠ [] → p + l.length = W →
      chunkPush W p (l ++ rest) = l.map some ++ none :: chunkPush W 0 rest
  | [], _, h, _ => absurd rfl h
  | [b], p, _, hl => by simp at hl; simp [chunkPush, hl]
  | b :: c :: l, p, _, hl => by
    simp only [List.length_cons] at hl
    have hne : p + 1 ≠ W := by omega
    have ih := chunkPush_full W rest (c :: l) (p + 1) (by simp) (by simp; omega)
    rw [List.cons_append, chunkPush]
    simp only [hne, ↓reduceIte]
    rw [ih]
    simp

theorem chunkPush_part (W : ℕ) : ∀ (l : List Bool) (p : ℕ), p + l.length < W →
    chunkPush W p l = l.map some
  | [], _, _ => rfl
  | b :: l, p, hl => by
    simp only [List.length_cons] at hl
    have hne : p + 1 ≠ W := by omega
    simp only [chunkPush, hne, ↓reduceIte, List.map_cons]
    rw [chunkPush_part W l (p + 1) (by omega)]

/-- With a final separator after a partial piece, the emitted symbols are those of the pieces. -/
theorem chunkPush_cut (W : ℕ) (hW : 1 ≤ W) (x : List Bool) :
    chunkPush W 0 x ++ (if x.length % W = 0 then [] else [none]) = syms (cut W x) := by
  by_cases hx : x = []
  · subst hx; simp [chunkPush]
  rw [cut_cons hx (by omega)]
  by_cases hlen : W ≤ x.length
  · have htake : (x.take W).length = W := by simp; omega
    have hne : x.take W ≠ [] := by intro h; simp [h] at htake; omega
    conv_lhs => rw [← List.take_append_drop W x]
    rw [chunkPush_full W _ (x.take W) 0 hne (by simp [htake]), List.take_append_drop]
    have hmod : x.length % W = (x.drop W).length % W := by
      rw [List.length_drop]; exact Nat.mod_eq_sub_mod hlen
    rw [hmod, List.append_assoc, List.cons_append, chunkPush_cut W hW (x.drop W)]
    simp [Schoenhage.syms_cons]
  · have hlt : x.length < W := by omega
    have hx0 : x.length ≠ 0 := by simpa using hx
    rw [chunkPush_part W x 0 (by omega), Nat.mod_eq_of_lt hlt]
    simp only [hx0, ↓reduceIte]
    rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega), cut_nil]
    simp [Schoenhage.syms_cons]
termination_by x.length
decreasing_by
  have : 0 < x.length := List.length_pos_of_ne_nil hx
  simp; omega

end ChunkMath

/-! ### Chunk on host stacks -/

section Chunk

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- The stacks of the source, the width register and the destination. -/
def tri (a b c : LR A) : Fin 3 → LR A := ![a, b, c]

@[simp] theorem tri_0 (a b c : LR A) : tri a b c 0 = a := rfl
@[simp] theorem tri_1 (a b c : LR A) : tri a b c 1 = b := rfl
@[simp] theorem tri_2 (a b c : LR A) : tri a b c 2 = c := rfl

theorem tri_upd0 (a b c a' : LR A) : Function.update (tri a b c) 0 a' = tri a' b c := by
  funext x; fin_cases x <;> rfl
theorem tri_upd1 (a b c b' : LR A) : Function.update (tri a b c) 1 b' = tri a b' c := by
  funext x; fin_cases x <;> rfl
theorem tri_upd2 (a b c c' : LR A) : Function.update (tri a b c) 2 c' = tri a b c' := by
  funext x; fin_cases x <;> rfl

/-- The width register `W` cells wide with its head `p` cells in. -/
def regP (W p : ℕ) : LR A :=
  (List.replicate p (bitSymbol true), List.replicate (W - p) (bitSymbol true) ++ [separator])

theorem adv_regP {W p : ℕ} (hp : p < W) : adv (regP (A := A) W p) = regP W (p + 1) := by
  obtain ⟨k, hk⟩ : ∃ k, W - p = k + 1 := ⟨W - p - 1, by omega⟩
  simp [adv, regP, hk, show W - (p + 1) = k by omega, List.replicate_succ]

/-- One bit: the source's bit onto the destination, the register's head one cell on, its next
cell in `sym`. -/
def chStep (j : Fin 3 → Fin T) : Act T Q A U :=
  actSeq [mv1 (j 0), .push (.lt (j 2)) (fun v => v.sym.getD blank) .done, mv1 (j 1),
    .peek (.rt (j 1)) (fun v o => { v with sym := o }) .done]

/-- Push a separator onto the left stack of `x`. -/
def pushSep (x : Fin T) : Act T Q A U := .push (.lt x) (fun _ => separator) .done

/-- End a piece: a separator onto the destination, the register rewound. -/
def endPiece (j : Fin 3 → Fin T) : Pr P T Q A U :=
  .seq (.act (pushSep (j 2))) (moveLR (j 1) (fun _ => true))

/-- One bit and, at the end of a piece, its separator. -/
def chBody (j : Fin 3 → Fin T) : Pr P T Q A U :=
  .seq (.act (chStep j)) (.seq (.cond (fun v => decide (v.sym = some separator)) (endPiece j) (.act .done))
    (.act (flagBit (j 0))))

/-- Chunk as a host program. -/
def chunkProg (j : Fin 3 → Fin T) : Pr P T Q A U :=
  .seq (.act (flagBit (j 0))) (.seq (.loop (·.flag) (chBody j))
    (.seq (.act (peekL (j 1) (fun _ => true))) (.seq (.cond (·.flag) (endPiece j) (.act .done))
      (.act (mv1 (j 0))))))

variable {j : Fin 3 → Fin T}

theorem chStep_run (hj : Function.Injective j) (S : Stacks T A) (e : Fin (A + 4))
    (Ls Rs Ld Rd : List (Fin (A + 4))) (r : LR A) (v : HS T Q A U) :
    ∃ v', v'.user = v.user ∧ v'.sym = (adv r).2.head? ∧
      (chStep j).run (mk v (regs S j (tri (Ls, e :: Rs) r (Ld, Rd)))) =
        mk v' (regs S j (tri (e :: Ls, Rs) (adv r) (e :: Ld, Rd))) := by
  refine ⟨{ v with sym := (adv r).2.head? }, rfl, rfl, ?_⟩
  simp only [chStep, run_actSeq_cons, run_actSeq_nil]
  rw [mv1_run hj]
  simp only [tri_0, adv_cons, tri_upd0, Action.run, mk_var, mk_stk, get_lt, regs_L_at hj, tri_2,
    Option.getD_some, List.head?_cons, regs_updL hj, store_mk, tri_upd2]
  rw [mv1_run hj]
  simp [tri_upd1, regs_R_at hj]

theorem rewind_regs (hj : Function.Injective j) (S : Stacks T A) (F : Fin 3 → LR A) (x : Fin 3)
    (v : HS T Q A U) :
    ∃ v', v'.user = v.user ∧
      Exec body (moveLR (j x) (fun _ => true)) (mk v (regs S j F)) (2 * (F x).1.length + 2)
        (mk v' (regs S j (Function.update F x ([], (F x).1.reverse ++ (F x).2)))) := by
  obtain ⟨v', hu, he⟩ := moveLR_exec body (j x) (fun _ => true) (F x).1 [] v (regs S j F) (by simp) rfl
    (by simp [regs_L_at hj])
  refine ⟨v', hu, he.cast rfl ?_⟩
  rw [← regs_set hj]
  simp [regs_R_at hj]

theorem endPiece_exec (hj : Function.Injective j) (S : Stacks T A) (W : ℕ) (a : LR A)
    (Ld Rd : List (Fin (A + 4))) (v : HS T Q A U) {p : ℕ} (hp : p ≤ W) :
    ∃ v', v'.user = v.user ∧
      Exec body (endPiece j) (mk v (regs S j (tri a (regP W p) (Ld, Rd)))) (2 * p + 3)
        (mk v' (regs S j (tri a (regP W 0) (separator :: Ld, Rd)))) := by
  have e₁ : (pushSep (j 2) : Act T Q A U).run (mk v (regs S j (tri a (regP W p) (Ld, Rd)))) =
      mk v (regs S j (tri a (regP W p) (separator :: Ld, Rd))) := by
    simp [pushSep, Action.run, regs_L_at hj, regs_updL hj, tri_upd2]
  obtain ⟨v', hu, he⟩ := rewind_regs body hj S (tri a (regP W p) (separator :: Ld, Rd)) 1 v
  refine ⟨v', hu, (Exec.seq ((Exec.act (body := body) _ _).cast rfl e₁) he).cast
    (by simp [regP]; ring) ?_⟩
  rw [tri_upd1]
  congr 3
  simp only [tri_1, regP, List.reverse_replicate, Nat.sub_zero, List.replicate_zero, Prod.mk.injEq,
    true_and]
  rw [← List.append_assoc, List.replicate_append_replicate, show p + (W - p) = W by omega]

/-- The bit loop of chunk. -/
theorem chunkLoop (hj : Function.Injective j) (S : Stacks T A) (W : ℕ) (Xs : List (Fin (A + 4))) :
    ∀ (bs : List Bool) (p : ℕ), p < W → ∀ (Ls Ld : List (Fin (A + 4))) (v : HS T Q A U),
      v.flag = !bs.isEmpty →
      ∃ v' m, v'.user = v.user ∧ m ≤ 10 * bs.length + 2 * p + 1 ∧
        Exec body (.loop (·.flag) (chBody j))
          (mk v (regs S j (tri (Ls, bs.map bitSymbol ++ separator :: Xs) (regP W p) (Ld, [])))) m
          (mk v' (regs S j (tri ((bs.map bitSymbol).reverse ++ Ls, separator :: Xs)
            (regP W ((p + bs.length) % W)) (((chunkPush W p bs).map Schoenhage.sym).reverse ++ Ld, [])))) := by
  intro bs
  induction bs with
  | nil =>
    intro p hp Ls Ld v hf
    refine ⟨v, 1, rfl, by omega, ?_⟩
    have := Exec.loop_false (body := body) (f := (·.flag)) (p := chBody j)
      (s := mk v (regs S j (tri (Ls, separator :: Xs) (regP W p) (Ld, [])))) (by simpa using hf)
    simpa [chunkPush, Nat.mod_eq_of_lt hp] using this
  | cons b bs ih =>
    intro p hp Ls Ld v hf
    obtain ⟨v₁, hu₁, hs₁, e₁⟩ := chStep_run hj S (bitSymbol b) Ls (bs.map bitSymbol ++ separator :: Xs)
      Ld [] (regP W p) v
    rw [adv_regP hp] at hs₁ e₁
    have hflag : ∀ (v' : HS T Q A U) (F : Fin 3 → LR A), (F 0).2 = bs.map bitSymbol ++ separator :: Xs →
        (flagBit (j 0) : Act T Q A U).run (mk v' (regs S j F)) =
          mk { v' with flag := !bs.isEmpty } (regs S j F) := by
      intro v' F hF
      cases bs <;> simp [flagBit, Action.run, regs_R_at hj, hF, isBit]
    by_cases hW : p + 1 = W
    · -- the piece ends
      have hsep : v₁.sym = some separator := by
        rw [hs₁]; simp [regP, hW]
      obtain ⟨v₂, hu₂, e₂⟩ := endPiece_exec body hj S W (bitSymbol b :: Ls, bs.map bitSymbol ++ separator :: Xs)
        (bitSymbol b :: Ld) [] v₁ (p := p + 1) (by omega)
      obtain ⟨v', m, hu', hm, he'⟩ := ih 0 (by omega) (bitSymbol b :: Ls) (separator :: bitSymbol b :: Ld)
        { v₂ with flag := !bs.isEmpty } rfl
      refine ⟨v', 1 + ((2 * (p + 1) + 3 + 1) + 1) + m + 1, hu'.trans (hu₂.trans hu₁),
        by simp only [List.length_cons]; omega, ?_⟩
      have hbody := Exec.seq (body := body) ((Exec.act (body := body) _ _).cast rfl e₁)
        (Exec.seq (Exec.cond_true (f := fun v => decide (v.sym = some separator)) (q := .act .done)
          (by simp [hsep]) e₂)
          ((Exec.act (body := body) _ _).cast rfl (hflag v₂ _ rfl)))
      refine (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf) hbody he').cast rfl ?_
      have hmod : (p + (b :: bs).length) % W = (0 + bs.length) % W := by
        simp only [List.length_cons]
        rw [show p + (bs.length + 1) = W + bs.length by omega, Nat.add_mod_left, Nat.zero_add]
      have hpush : ((chunkPush W p (b :: bs)).map Schoenhage.sym).reverse ++ Ld =
          ((chunkPush W 0 bs).map Schoenhage.sym).reverse ++ separator :: bitSymbol b :: Ld := by
        simp [chunkPush, hW, Schoenhage.sym]
      rw [hmod, hpush]
      simp
    · -- the piece goes on
      have hsep : v₁.sym ≠ some separator := by
        rw [hs₁]
        obtain ⟨k, hk⟩ : ∃ k, W - (p + 1) = k + 1 := ⟨W - (p + 1) - 1, by omega⟩
        simp [regP, hk, List.replicate_succ, bitSymbol, separator]
      obtain ⟨v', m, hu', hm, he'⟩ := ih (p + 1) (by omega) (bitSymbol b :: Ls) (bitSymbol b :: Ld)
        { v₁ with flag := !bs.isEmpty } rfl
      refine ⟨v', 1 + ((1 + 1) + 1) + m + 1, hu'.trans hu₁, by simp only [List.length_cons]; omega, ?_⟩
      have hbody := Exec.seq (body := body) ((Exec.act (body := body) _ _).cast rfl e₁)
        (Exec.seq (Exec.cond_false (f := fun v => decide (v.sym = some separator)) (p := endPiece j)
          (by simp [hsep])
          (Exec.act (body := body) .done _))
          ((Exec.act (body := body) _ _).cast rfl (hflag v₁ _ rfl)))
      refine (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf) hbody he').cast rfl ?_
      have hmod : (p + (b :: bs).length) % W = (p + 1 + bs.length) % W := by
        simp only [List.length_cons]; ring_nf
      have hpush : ((chunkPush W p (b :: bs)).map Schoenhage.sym).reverse ++ Ld =
          ((chunkPush W (p + 1) bs).map Schoenhage.sym).reverse ++ bitSymbol b :: Ld := by
        simp [chunkPush, hW, Schoenhage.sym]
      rw [hmod, hpush]
      simp

end Chunk

section ChunkImpl

variable {A : ℕ}

open Schoenhage (cut ones reg)

theorem flag_replicate {α : Type} (k : ℕ) (e : α) :
    ((List.replicate k e).head?.map (fun _ => true)).getD false = decide (k ≠ 0) := by
  cases k <;> simp [List.replicate_succ]

theorem cells_ones (W : ℕ) : cells (a := A) [ones W] = List.replicate W (bitSymbol true) ++ [separator] := by
  simp [cells, ones, Schoenhage.syms_cons, Schoenhage.sym]

/-- Chunk on host stacks. -/
noncomputable def chunkImpl (C n : ℕ) (hC : 3 ≤ C) : TImpl C n (Schoenhage.Chunk.prim (a := A)) where
  prog j := chunkProg j
  spec body j hj _ τ hpre v S := by
    obtain ⟨h0, hW, hreg, h2⟩ := hpre
    set W := (τ 1).cur.length
    obtain ⟨x, R0, hx⟩ := Schoenhage.exists_cons h0
    have hcur : (τ 0).cur = x := by simp [WTape.cur, hx]
    set F0 := tri (lcells (A := A) (τ 0).left, x.map bitSymbol ++ separator :: cells R0) (regP W 0)
      (lcells (τ 2).left, [])
    have h0' : place S j τ = regs S j F0 := by
      rw [place_eq_regs]
      congr 1
      funext i
      fin_cases i
      · simp [F0, hx, cells_cons']
      · simp only [F0, Fin.mk_one, tri_1]
        rw [hreg]
        simp [regP, reg, lcells, cells_ones]
      · simp [F0, h2, cells]
    have e₀ : (flagBit (j 0) : Act _ _ A _).run (mk v (regs S j F0)) =
        mk { v with flag := !x.isEmpty } (regs S j F0) := by
      cases x <;> simp [flagBit, Action.run, regs_R_at hj, F0, isBit]
    obtain ⟨v₁, m, hu₁, hm, e₁⟩ := chunkLoop body hj S W (cells R0) x 0 (by omega) (lcells (τ 0).left)
      (lcells (τ 2).left) { v with flag := !x.isEmpty } rfl
    set q := (0 + x.length) % W
    have hqx : q ≤ x.length := by simp only [q, Nat.zero_add]; exact Nat.mod_le _ _
    have hqW : q < W := Nat.mod_lt _ (by omega)
    set a₁ : LR A := ((x.map bitSymbol).reverse ++ lcells (τ 0).left, separator :: cells R0)
    set D := ((chunkPush W 0 x).map Schoenhage.sym).reverse ++ lcells (τ 2).left
    have e₂ : (peekL (j 1) (fun _ => true) : Act _ _ A _).run
        (mk v₁ (regs S j (tri a₁ (regP W q) (D, [])))) =
          mk { v₁ with flag := decide (q ≠ 0) } (regs S j (tri a₁ (regP W q) (D, []))) := by
      simp [peekL, Action.run, regs_L_at hj, regP, flag_replicate]
    have hcut := chunkPush_cut W hW x
    -- the final piece
    obtain ⟨v₃, m₃, hu₃, hm₃, e₃⟩ : ∃ v₃ m₃, v₃.user = v₁.user ∧ m₃ ≤ 2 * q + 4 ∧
        Exec body (.cond (·.flag) (endPiece j) (.act .done))
          (mk { v₁ with flag := decide (q ≠ 0) } (regs S j (tri a₁ (regP W q) (D, [])))) m₃
          (mk v₃ (regs S j (tri a₁ (regP W 0) ((cells (cut W x)).reverse ++ lcells (τ 2).left, [])))) := by
      by_cases hq : q = 0
      · refine ⟨{ v₁ with flag := decide (q ≠ 0) }, 2, rfl, by omega, ?_⟩
        have hq' : x.length % W = 0 := by simpa [q] using hq
        have hcells : cells (a := A) (cut W x) = (chunkPush W 0 x).map Schoenhage.sym := by
          simp only [hq', ↓reduceIte, List.append_nil] at hcut
          simp [cells, ← hcut]
        have hD : D = (cells (cut W x)).reverse ++ lcells (τ 2).left := by
          simp [D, hcells]
        rw [← hD, ← hq]
        exact Exec.cond_false (by simp [hq]) (Exec.act _ _)
      · obtain ⟨v₃, hu₃, e⟩ := endPiece_exec body hj S W a₁ D [] { v₁ with flag := decide (q ≠ 0) }
          (p := q) (by omega)
        refine ⟨v₃, 2 * q + 3 + 1, hu₃, by omega, ?_⟩
        have hq' : x.length % W ≠ 0 := by simpa [q] using hq
        have hcells : cells (a := A) (cut W x) = (chunkPush W 0 x ++ [none]).map Schoenhage.sym := by
          simp only [hq', ↓reduceIte] at hcut
          simp [cells, ← hcut]
        have hD : separator :: D = (cells (cut W x)).reverse ++ lcells (τ 2).left := by
          simp [D, hcells, Schoenhage.sym]
        rw [← hD]
        exact Exec.cond_true (by simp [hq]) e
    have e₄ := mv1_run (Q := _) (U := _) hj S
      (tri a₁ (regP W 0) ((cells (cut W x)).reverse ++ lcells (τ 2).left, [])) 0 v₃
    refine ⟨{ v₃ with sym := (separator :: cells R0).head? }, 1 + (m + (1 + (m₃ + 1))), ?_, ?_, ?_⟩
    · simp only; rw [hu₃, hu₁]
    · have := Nat.mul_le_mul_right (4 * x.length + 3 + 1) hC
      simp only [hcur]
      omega
    · rw [h0']
      refine Exec.seq ((Exec.act (body := body) _ _).cast rfl e₀) (Exec.seq e₁
        (Exec.seq ((Exec.act (body := body) _ _).cast rfl e₂) (Exec.seq e₃
          ((Exec.act (body := body) _ _).cast rfl (e₄.trans ?_)))))
      rw [place_eq_regs]
      congr 2
      funext i
      fin_cases i
      · simp [a₁, Schoenhage.Chunk.prim, WTape.next, WTape.cur, hx, lcells, List.map_reverse]
      · simp only [Fin.mk_one, tri_upd0, tri_1, Schoenhage.Chunk.prim]
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
        rw [hreg]
        simp [regP, reg, lcells, cells_ones]
      · simp [Schoenhage.Chunk.prim, hcur, lcells_append, lcells_reverse, cells]
        rfl

variable {t : ℕ}

theorem allTM_chunkw {C n : ℕ} (hC : 3 ≤ C) {s r d : Fin t} (h1 : s ≠ r) (h2 : s ≠ d) (h3 : r ≠ d) :
    AllTM C n (Schoenhage.chunkw (a := A) s r d h1 h2 h3) :=
  .prim ⟨chunkImpl C n hC⟩

end ChunkImpl

end IntegerMultBounds.MathlibTM2.Host.WordCmd
