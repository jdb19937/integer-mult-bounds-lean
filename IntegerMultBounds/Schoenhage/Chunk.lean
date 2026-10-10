import IntegerMultBounds.Schoenhage.Reverse

/-! Cutting a word into pieces of a fixed width. A three-tape machine copies
the source's current word to the destination while stepping a unary width
register; when the register runs out it ends the piece with a separator and
rewinds the register. As a primitive (`Chunk.prim`, `chunkw`): the source
advances one word and the destination gains the pieces `cut w x`
(`runs_chunkw`). -/

namespace IntegerMultBounds.Schoenhage

open Machine

variable {a t : ℕ}

/-! ### Pieces -/

/-- Consecutive pieces of width `w` (the last may be shorter); empty for the empty word. -/
def cut (w : ℕ) (x : List Bool) : List (List Bool) :=
  if hx : x = [] then [] else if hw : w = 0 then [x] else x.take w :: cut w (x.drop w)
termination_by x.length
decreasing_by
  have : 0 < x.length := List.length_pos_of_ne_nil hx
  simp; omega

@[simp] theorem cut_nil (w : ℕ) : cut w [] = [] := by rw [cut]; simp

theorem cut_cons {w : ℕ} {x : List Bool} (hx : x ≠ []) (hw : w ≠ 0) :
    cut w x = x.take w :: cut w (x.drop w) := by
  rw [cut]; simp [hx, hw]

theorem cut_flatten (w : ℕ) (x : List Bool) : (cut w x).flatten = x := by
  by_cases hx : x = []
  · simp [hx]
  by_cases hw : w = 0
  · rw [cut]; simp [hx, hw]
  rw [cut_cons hx hw, List.flatten_cons, cut_flatten w (x.drop w), List.take_append_drop]
termination_by x.length
decreasing_by have := List.length_pos_of_ne_nil hx; simp; omega

theorem cut_lengths {w : ℕ} (hw : 1 ≤ w) (x : List Bool) (hx : w ∣ x.length) :
    ∀ c ∈ cut w x, c.length = w := by
  by_cases h0 : x = []
  · simp [h0]
  have hpos := List.length_pos_of_ne_nil h0
  have hle : w ≤ x.length := Nat.le_of_dvd hpos hx
  rw [cut_cons h0 (by omega)]
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · simp; omega
  · exact cut_lengths hw (x.drop w) (by rw [List.length_drop]; exact Nat.dvd_sub hx (dvd_refl w)) c hc
termination_by x.length
decreasing_by simp; omega

theorem length_cut {w : ℕ} (hw : 1 ≤ w) (x : List Bool) (hx : w ∣ x.length) :
    (cut w x).length = x.length / w := by
  by_cases h0 : x = []
  · simp [h0]
  have hpos := List.length_pos_of_ne_nil h0
  have hle : w ≤ x.length := Nat.le_of_dvd hpos hx
  rw [cut_cons h0 (by omega), List.length_cons,
    length_cut hw (x.drop w) (by rw [List.length_drop]; exact Nat.dvd_sub hx (dvd_refl w)), List.length_drop]
  obtain ⟨k, hk⟩ := hx
  rw [hk, show w * k - w = w * (k - 1) by rw [Nat.mul_sub, mul_one], Nat.mul_div_cancel_left _ (by omega),
    Nat.mul_div_cancel_left _ (by omega)]
  have : 1 ≤ k := Nat.pos_of_ne_zero (fun h => by subst h; rw [mul_zero] at hk; omega)
  omega
termination_by x.length
decreasing_by simp; omega

theorem cells_cons (c : List Bool) (cs : List (List Bool)) :
    cells (a := a) (c :: cs) = c.map bitSymbol ++ [separator] ++ cells cs := by
  simp [cells, syms_cons, sym, Function.comp_def]

/-! ### Three tapes -/

/-- A three-tape bank. -/
def three (h0 : ℤ) (f0 : ℤ → Fin (a + 4)) (h1 : ℤ) (f1 : ℤ → Fin (a + 4)) (h2 : ℤ) (f2 : ℤ → Fin (a + 4)) :
    Tapes 3 a :=
  ⟨fun i => if i.val = 0 then h0 else if i.val = 1 then h1 else h2,
    fun i => if i.val = 0 then f0 else if i.val = 1 then f1 else f2⟩

theorem enc_three (σ : Fin 3 → WTape) :
    enc (a := a) σ = three (σ 0).pos (σ 0).tape (σ 1).pos (σ 1).tape (σ 2).pos (σ 2).tape := by
  simp only [enc, three]
  congr 1 <;> funext x <;> fin_cases x <;> rfl

/-- The action writing `x0`, `x1`, `x2` and moving by `m0`, `m1`, `m2`. -/
def act3 (x0 : Fin (a + 4)) (m0 : Move) (x1 : Fin (a + 4)) (m1 : Move) (x2 : Fin (a + 4)) (m2 : Move) :
    Fin 3 → Fin (a + 4) × Move :=
  fun i => if i.val = 0 then (x0, m0) else if i.val = 1 then (x1, m1) else (x2, m2)

/-- The symbols read. -/
def rd3 (h0 : ℤ) (f0 : ℤ → Fin (a + 4)) (h1 : ℤ) (f1 : ℤ → Fin (a + 4)) (h2 : ℤ) (f2 : ℤ → Fin (a + 4)) :
    Fin 3 → Fin (a + 4) := fun i => if i.val = 0 then f0 h0 else if i.val = 1 then f1 h1 else f2 h2

@[simp] theorem rd3_0 (h0 : ℤ) (f0 : ℤ → Fin (a + 4)) (h1 : ℤ) (f1 : ℤ → Fin (a + 4)) (h2 : ℤ)
    (f2 : ℤ → Fin (a + 4)) : rd3 h0 f0 h1 f1 h2 f2 0 = f0 h0 := rfl
@[simp] theorem rd3_1 (h0 : ℤ) (f0 : ℤ → Fin (a + 4)) (h1 : ℤ) (f1 : ℤ → Fin (a + 4)) (h2 : ℤ)
    (f2 : ℤ → Fin (a + 4)) : rd3 h0 f0 h1 f1 h2 f2 1 = f1 h1 := rfl
@[simp] theorem rd3_2 (h0 : ℤ) (f0 : ℤ → Fin (a + 4)) (h1 : ℤ) (f1 : ℤ → Fin (a + 4)) (h2 : ℤ)
    (f2 : ℤ → Fin (a + 4)) : rd3 h0 f0 h1 f1 h2 f2 2 = f2 h2 := rfl

/-- One transition of a three-tape machine. -/
theorem step_three (M : FMachine 3 a) {s s' : M.S} {h0 h1 h2 : ℤ} {f0 f1 f2 : ℤ → Fin (a + 4)}
    (x0 : Fin (a + 4)) (m0 : Move) (x1 : Fin (a + 4)) (m1 : Move) (x2 : Fin (a + 4)) (m2 : Move)
    (hδ : M.δ s (rd3 h0 f0 h1 f1 h2 f2) = some (s', act3 x0 m0 x1 m1 x2 m2)) :
    M.fstep ⟨s, three h0 f0 h1 f1 h2 f2⟩ = some ⟨s', three (h0 + m0.offset) (Function.update f0 h0 x0)
      (h1 + m1.offset) (Function.update f1 h1 x1) (h2 + m2.offset) (Function.update f2 h2 x2)⟩ := by
  have hr : (fun i : Fin 3 => (three h0 f0 h1 f1 h2 f2 : Tapes 3 a).tape i
      ((three h0 f0 h1 f1 h2 f2 : Tapes 3 a).head i)) = rd3 h0 f0 h1 f1 h2 f2 := by
    funext i; simp only [three, rd3]; split_ifs <;> rfl
  simp only [FMachine.fstep, hr, hδ]
  congr 2
  simp only [three, act3, Tapes.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext i; split_ifs <;> rfl
  · funext i j; split_ifs <;> simp_all [Function.update_apply]

theorem halt_three (M : FMachine 3 a) {s : M.S} {v : Tapes 3 a}
    (hδ : ∀ syms, M.δ s syms = none) : M.fstep ⟨s, v⟩ = none := by
  simp [FMachine.fstep, hδ]

namespace Chunk

inductive St where
  | copy (st : Bool)
  | rew (fin : Bool)
  | done
  deriving DecidableEq

instance : Fintype St :=
  ⟨{.copy false, .copy true, .rew false, .rew true, .done}, by intro x; cases x <;> simp⟩

abbrev machine : FMachine 3 a where
  S := St
  start := .copy false
  δ s syms := match s with
    | .copy st => if syms 0 = separator then
          (if st then some (.rew true, act3 (syms 0) .right (syms 1) .left separator .right)
           else some (.done, act3 (syms 0) .right (syms 1) .stay (syms 2) .stay))
        else if syms 1 = separator then some (.rew false, act3 (syms 0) .stay (syms 1) .left separator .right)
        else some (.copy true, act3 (syms 0) .right (syms 1) .right (syms 0) .right)
    | .rew fin => if syms 1 = blank ∨ syms 1 = separator then
          some (if fin then .done else .copy false, act3 (syms 0) .stay (syms 1) .right (syms 2) .stay)
        else some (.rew fin, act3 (syms 0) .stay (syms 1) .left (syms 2) .stay)
    | .done => none

theorem bit_ne_sep (b : Bool) : bitSymbol (a := a) b ≠ separator := by
  cases b <;> simp [bitSymbol, separator, Fin.ext_iff]

theorem bit_ne_blank (b : Bool) : bitSymbol (a := a) b ≠ blank := by
  cases b <;> simp [bitSymbol, blank, Fin.ext_iff]

/-- Copy the bits `bs` while stepping the register over ones. -/
theorem copy_run (f0 f1 : ℤ → Fin (a + 4)) :
    ∀ (bs : List Bool) (st : Bool) (h0 h1 h2 : ℤ) (f2 : ℤ → Fin (a + 4)),
      (∀ c : ℕ, (hc : c < bs.length) → f0 (h0 + c) = bitSymbol bs[c]) →
      (∀ c : ℕ, c < bs.length → f1 (h1 + c) = bitSymbol true) →
      (machine (a := a)).frun bs.length ⟨.copy st, three h0 f0 h1 f1 h2 f2⟩ =
        some ⟨.copy (st || !bs.isEmpty), three (h0 + bs.length) f0 (h1 + bs.length) f1 (h2 + bs.length)
          (putWord f2 h2 (bs.map bitSymbol))⟩
  | [], st, h0, h1, h2, f2, _, _ => by simp [FMachine.frun, putWord]
  | b :: bs, st, h0, h1, h2, f2, hb, hr => by
    have e0 : f0 h0 = bitSymbol b := by
      have := hb 0 (by simp); simp only [List.getElem_cons_zero, Nat.cast_zero, add_zero] at this; exact this
    have e1 : f1 h1 = bitSymbol true := by
      have := hr 0 (by simp); simp only [Nat.cast_zero, add_zero] at this; exact this
    have ih := copy_run f0 f1 bs true (h0 + 1) (h1 + 1) (h2 + 1) (Function.update f2 h2 (bitSymbol b))
      (fun c hc => by
        have := hb (c + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this; push_cast at this
        rwa [show h0 + 1 + (c : ℤ) = h0 + ((c : ℤ) + 1) by ring])
      (fun c hc => by
        have := hr (c + 1) (by simp; omega); push_cast at this
        rwa [show h1 + 1 + (c : ℤ) = h1 + ((c : ℤ) + 1) by ring])
    rw [List.length_cons, show bs.length + 1 = 1 + bs.length by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_three machine (s' := .copy true) (f0 h0) .right (f1 h1) .right (f0 h0) .right
        (by simp [machine, e0, e1, bit_ne_sep]))) ?_
    simp only [Function.update_eq_self, Move.offset]
    rw [e0, ih]
    simp only [Bool.true_or, List.isEmpty_cons, Bool.not_false, Bool.or_true, List.map_cons, putWord_cons]
    congr 3 <;> push_cast <;> ring

/-- Rewind the register over `n` ones to the cell after the boundary. -/
theorem rew_run (f0 f2 : ℤ → Fin (a + 4)) (h0 h2 : ℤ) (f1 : ℤ → Fin (a + 4)) (fin : Bool) :
    ∀ (n : ℕ) (h1 : ℤ), (∀ c : ℕ, c < n → f1 (h1 - c) = bitSymbol true) →
      (f1 (h1 - n) = blank ∨ f1 (h1 - n) = separator) →
      (machine (a := a)).frun (n + 1) ⟨.rew fin, three h0 f0 h1 f1 h2 f2⟩ =
        some ⟨if fin then .done else .copy false, three h0 f0 (h1 - n + 1) f1 h2 f2⟩
  | 0, h1, _, hb => by
    simp only [Nat.cast_zero, sub_zero] at hb
    rw [FMachine.frun_one, step_three machine (s' := if fin then .done else .copy false)
      (f0 h0) .stay (f1 h1) .right (f2 h2) .stay (by simp [machine, hb])]
    simp [Move.offset]
  | n + 1, h1, hones, hb => by
    have e1 : f1 h1 = bitSymbol true := by simpa using hones 0 (by omega)
    have ih := rew_run f0 f2 h0 h2 f1 fin n (h1 - 1) (fun c hc => by
      have := hones (c + 1) (by omega); push_cast at this; rwa [show h1 - 1 - c = h1 - (c + 1) by ring])
      (by push_cast at hb; rwa [show h1 - 1 - n = h1 - (n + 1) by ring])
    rw [show n + 1 + 1 = 1 + (n + 1) by omega]
    refine FMachine.frun_trans _ (FMachine.frun_of_step _
      (step_three machine (s' := .rew fin) (f0 h0) .stay (f1 h1) .left (f2 h2) .stay
        (by simp [machine, e1, bit_ne_sep, bit_ne_blank]))) ?_
    simp only [Function.update_eq_self, Move.offset, add_zero]
    convert ih using 4
    all_goals (push_cast; ring)

theorem putWord_single (f : ℤ → Fin (a + 4)) (p : ℤ) (x : Fin (a + 4)) : putWord f p [x] = Function.update f p x := rfl

/-- The whole word: every piece, then step past the source word. -/
theorem main_run (f0 f1 : ℤ → Fin (a + 4)) {w : ℕ} (hw : 1 ≤ w)
    (R1 : ∀ c : ℕ, c < w → f1 c = bitSymbol true) (R2 : f1 w = separator) (R3 : f1 (-1) = blank)
    (x : List Bool) (h0 h2 : ℤ) (f2 : ℤ → Fin (a + 4))
    (hx : ∀ c : ℕ, (hc : c < x.length) → f0 (h0 + c) = bitSymbol x[c]) (hs : f0 (h0 + x.length) = separator) :
    ∃ k, k ≤ 4 * x.length + 3 ∧ (machine (a := a)).frun k ⟨.copy false, three h0 f0 0 f1 h2 f2⟩ =
      some ⟨.done, three (h0 + x.length + 1) f0 0 f1 (h2 + clen (cut w x)) (putWord f2 h2 (cells (cut w x)))⟩ := by
  by_cases h0x : x = []
  · subst h0x
    simp only [List.length_nil, Nat.cast_zero, add_zero] at hs
    refine ⟨1, by simp, ?_⟩
    rw [FMachine.frun_one, step_three machine (s' := .done) (f0 h0) .right (f1 0) .stay (f2 h2) .stay
      (by simp [machine, hs])]
    simp [Move.offset, cells, putWord]
  have hpos := List.length_pos_of_ne_nil h0x
  by_cases hle : x.length ≤ w
  · have hcut : cut w x = [x] := by
      rw [cut_cons h0x (by omega), List.take_of_length_le hle, List.drop_of_length_le hle, cut_nil]
    have s1 := copy_run f0 f1 x false h0 0 h2 f2 hx (fun c hc => by simpa using R1 c (by omega))
    simp only [Bool.false_or, zero_add] at s1
    have hne : x.isEmpty = false := by simp [h0x]
    simp only [hne, Bool.not_false] at s1
    have s2 := step_three (machine (a := a)) (s := .copy true) (s' := .rew true)
      (h0 := h0 + x.length) (h1 := x.length) (h2 := h2 + x.length) (f0 := f0) (f1 := f1)
      (f2 := putWord f2 h2 (x.map bitSymbol)) (f0 (h0 + x.length)) .right (f1 x.length) .left separator .right
      (by simp [machine, hs])
    have s3 := rew_run f0 (Function.update (putWord f2 h2 (x.map bitSymbol)) (h2 + x.length) separator)
      (h0 + x.length + 1) (h2 + x.length + 1) f1 true x.length (x.length - 1)
      (fun c hc => by
        rw [show (x.length : ℤ) - 1 - c = ((x.length - 1 - c : ℕ) : ℤ) by omega]; exact R1 _ (by omega))
      (by rw [show (x.length : ℤ) - 1 - x.length = -1 by ring]; left; exact R3)
    refine ⟨x.length + (1 + (x.length + 1)), by omega, FMachine.frun_trans _ s1
      (FMachine.frun_trans _ (FMachine.frun_of_step _ s2) ?_)⟩
    simp only [Move.offset, Function.update_eq_self] at s3 ⊢
    rw [show (x.length : ℤ) + -1 = x.length - 1 by ring]
    rw [s3, hcut]
    simp only [ite_true]
    have hc : cells (a := a) [x] = x.map bitSymbol ++ [separator] := by rw [cells_cons]; simp [cells]
    rw [hc, ← putWord_append_forward, List.length_map, putWord_single]
    congr 3
    · ring
    · simp [clen]; ring
  · push Not at hle
    set y := x.take w
    set z := x.drop w
    have hyl : y.length = w := by simp [y]; omega
    have hzl : z.length = x.length - w := by simp [z]
    have hz0 : z ≠ [] := by intro h; have := congrArg List.length h; simp [z] at this; omega
    have hcut : cut w x = y :: cut w z := cut_cons h0x (by omega)
    have s1 := copy_run f0 f1 y false h0 0 h2 f2
      (fun c hc => by rw [hx c (by omega)]; simp [y])
      (fun c hc => by simpa using R1 c (by omega))
    rw [hyl] at s1
    simp only [Bool.false_or, zero_add] at s1
    have hy0 : y ≠ [] := fun h => by have := congrArg List.length h; rw [hyl] at this; simp at this; omega
    have hne : y.isEmpty = false := by simp [hy0]
    simp only [hne, Bool.not_false] at s1
    have hxw : f0 (h0 + w) = bitSymbol x[w] := hx w hle
    have s2 := step_three (machine (a := a)) (s := .copy true) (s' := .rew false)
      (h0 := h0 + w) (h1 := w) (h2 := h2 + w) (f0 := f0) (f1 := f1)
      (f2 := putWord f2 h2 (y.map bitSymbol)) (f0 (h0 + w)) .stay (f1 w) .left separator .right
      (by simp [machine, hxw, bit_ne_sep, R2])
    have s3 := rew_run f0 (Function.update (putWord f2 h2 (y.map bitSymbol)) (h2 + w) separator)
      (h0 + w) (h2 + w + 1) f1 false w (w - 1)
      (fun c hc => by
        rw [show (w : ℤ) - 1 - c = ((w - 1 - c : ℕ) : ℤ) by omega]; exact R1 _ (by omega))
      (by rw [show (w : ℤ) - 1 - w = -1 by ring]; left; exact R3)
    obtain ⟨k, hk, s4⟩ := main_run f0 f1 hw R1 R2 R3 z (h0 + w) (h2 + w + 1)
      (Function.update (putWord f2 h2 (y.map bitSymbol)) (h2 + w) separator)
      (fun c hc => by
        rw [show h0 + w + (c : ℤ) = h0 + ((w + c : ℕ) : ℤ) by push_cast; ring, hx (w + c) (by omega)]
        simp [z])
      (by rw [hzl, show h0 + w + ((x.length - w : ℕ) : ℤ) = h0 + x.length by push_cast [hle.le]; ring]; exact hs)
    have e1 : h0 + w + (z.length : ℤ) + 1 = h0 + x.length + 1 := by rw [hzl]; push_cast [hle.le]; ring
    have e2 : h2 + w + 1 + (clen (cut w z) : ℤ) = h2 + clen (cut w x) := by
      rw [hcut, clen_cons, hyl]; push_cast; ring
    have e3 : putWord (Function.update (putWord f2 h2 (y.map bitSymbol)) (h2 + w) separator) (h2 + w + 1)
        (cells (cut w z)) = putWord f2 h2 (cells (a := a) (cut w x)) := by
      rw [hcut, cells_cons, ← putWord_single, ← putWord_append_forward f2 h2 (y.map bitSymbol ++ [separator]),
        ← putWord_append_forward f2 h2 (y.map bitSymbol) [separator]]
      simp only [List.length_append, List.length_map, List.length_singleton, hyl]
      push_cast; ring_nf
    rw [e1, e2, e3] at s4
    refine ⟨w + (1 + (w + 1 + k)), by omega, FMachine.frun_trans _ s1
      (FMachine.frun_trans _ (FMachine.frun_of_step _ s2) (FMachine.frun_trans _ ?_ s4))⟩
    simp only [Move.offset, Function.update_eq_self, add_zero] at s3 ⊢
    rw [show (w : ℤ) + -1 = w - 1 by ring, s3]
    simp only [Bool.false_eq_true, ite_false]
    congr 3; ring
termination_by x.length
decreasing_by simp [z]; omega

/-- Chunk: the source's current word, cut into pieces of the register's width, as new words of
the destination. -/
noncomputable abbrev prim : Prim a where
  s := 3
  hs := by omega
  M := machine
  pre σ := (σ 0).right ≠ [] ∧ 1 ≤ (σ 1).cur.length ∧ σ 1 = reg (ones (σ 1).cur.length) ∧ (σ 2).right = []
  sem σ := fun i => if i.val = 0 then (σ 0).next else if i.val = 1 then σ 1
    else ⟨(cut (σ 1).cur.length (σ 0).cur).reverse ++ (σ 2).left, []⟩
  cost σ := 4 * (σ 0).cur.length + 3
  spec σ hpre := by
    obtain ⟨h0, hw, hreg, h2⟩ := hpre
    apply FMachine.hoare
    intro v hv; subst hv
    rw [enc_three]
    set T0 := σ 0
    set T1 := σ 1
    set T2 := σ 2
    set W := T1.cur.length
    obtain ⟨x, R, hr⟩ : ∃ x R, T0.right = x :: R := by
      rcases h : T0.right with _ | ⟨x, R⟩
      · exact absurd h h0
      · exact ⟨x, R, rfl⟩
    have hcur : T0.cur = x := by simp [WTape.cur, hr]
    have h1r : T1.right = [ones W] := by rw [hreg]; rfl
    have h1p : T1.pos = 0 := by rw [hreg]; rfl
    have R1 : ∀ c : ℕ, c < W → T1.tape (a := a) c = bitSymbol true := fun c hc => by
      have := T1.tape_word (a := a) h1r c (by simpa using hc)
      rw [h1p, zero_add] at this; rw [this]; simp [ones]
    have R2 : T1.tape (a := a) W = separator := by
      have := T1.tape_sep (a := a) h1r; rwa [h1p, zero_add, length_ones] at this
    have R3 : T1.tape (a := a) (-1) = blank := T1.tape_neg _ (by norm_num)
    obtain ⟨k, hk, hrun⟩ := main_run (T0.tape (a := a)) (T1.tape (a := a)) hw R1 R2 R3 x T0.pos T2.pos T2.tape
      (fun c hc => T0.tape_word hr c hc) (T0.tape_sep hr)
    refine ⟨k, _, by rw [hcur]; omega, by rw [h1p]; exact hrun, halt_three machine (fun _ => rfl), ?_⟩
    rw [enc_three]
    have c0 : ((0 : Fin 3) : ℕ) = 0 := rfl
    have c1 : ((1 : Fin 3) : ℕ) = 1 := rfl
    have c2 : ((2 : Fin 3) : ℕ) = 2 := rfl
    simp only [c0, c1, c2, ↓reduceIte, one_ne_zero, OfNat.ofNat_ne_zero, hcur, T0.next_pos hr, T0.next_tape hr,
      show (2 : ℕ) ≠ 1 by decide, show (2 : ℕ) ≠ 0 by decide]
    have hput := T2.put_end (a := a) h2 (cut W x)
    rw [hput, h1p]
    simp [three, WTape.pos, clen_append, clen_reverse]
    ring

end Chunk

/-- Three slots: source, width register, destination. -/
def slot3 (s r d : Fin t) : Fin 3 → Fin t := fun i => if i.val = 0 then s else if i.val = 1 then r else d

theorem slot3_inj {s r d : Fin t} (h1 : s ≠ r) (h2 : s ≠ d) (h3 : r ≠ d) : Function.Injective (slot3 s r d) := by
  intro i j hij
  simp only [slot3] at hij
  apply Fin.ext
  have hi := i.isLt; have hj := j.isLt
  split_ifs at hij <;> first | omega | (exfalso; simp_all)

/-- Cut the current word of `s` into pieces of the width in `r`, appended to `d`. -/
noncomputable def chunkw (s r d : Fin t) (h1 : s ≠ r) (h2 : s ≠ d) (h3 : r ≠ d) : Cmd a t :=
  .prim Chunk.prim (slot3 s r d) (slot3_inj h1 h2 h3)

theorem upd_slot3 (σ : Fin t → WTape) {s r d : Fin t} (h1 : s ≠ r) (h2 : s ≠ d) (h3 : r ≠ d)
    (τ : Fin 3 → WTape) :
    upd σ (slot3 s r d) τ = Function.update (Function.update (Function.update σ s (τ 0)) r (τ 1)) d (τ 2) := by
  have hi := slot3_inj h1 h2 h3
  funext x
  by_cases hxd : x = d
  · subst hxd
    rw [Function.update_self]
    have := upd_slot σ hi τ 2
    rwa [show slot3 s r x 2 = x by simp [slot3]] at this
  · rw [Function.update_of_ne hxd]
    by_cases hxr : x = r
    · subst hxr
      rw [Function.update_self]
      have := upd_slot σ hi τ 1
      rwa [show slot3 s x d 1 = x by simp [slot3]] at this
    · rw [Function.update_of_ne hxr]
      by_cases hxs : x = s
      · subst hxs
        rw [Function.update_self]
        have := upd_slot σ hi τ 0
        rwa [show slot3 x r d 0 = x by simp [slot3]] at this
      · rw [Function.update_of_ne hxs]
        refine upd_other σ _ τ x (fun i hi => ?_)
        simp only [slot3] at hi; split_ifs at hi <;> simp_all

theorem runs_chunkw {s r d : Fin t} (h1 : s ≠ r) (h2 : s ≠ d) (h3 : r ≠ d) (σ : Fin t → WTape)
    {L R : List (List Bool)} {x : List Bool} {w : ℕ}
    (hs : σ s = ⟨L, x :: R⟩) (hr : σ r = reg (ones w)) (hw : 1 ≤ w) (hd : (σ d).right = []) :
    Runs (a := a) (chunkw s r d h1 h2 h3) σ
      (· = Function.update (Function.update σ s ⟨x :: L, R⟩) d ⟨(cut w x).reverse ++ (σ d).left, []⟩)
      (4 * x.length + 3) := by
  have ew : (σ r).cur.length = w := by rw [hr]; simp [WTape.cur, reg]
  have hpre : Chunk.prim.pre (a := a) (σ ∘ slot3 s r d) :=
    ⟨by simp [slot3, hs], by simp [slot3, ew, hw], by simp [slot3, hr], by simpa [slot3, h2.symm, h3.symm] using hd⟩
  refine ⟨_, _, Exec.prim (P := Chunk.prim) hpre, ?_, ?_⟩
  · rw [upd_slot3 σ h1 h2 h3]
    have c0 : ((0 : Fin 3) : ℕ) = 0 := rfl
    have c1 : ((1 : Fin 3) : ℕ) = 1 := rfl
    have c2 : ((2 : Fin 3) : ℕ) = 2 := rfl
    simp only [slot3, Function.comp_apply, c0, c1, c2, ↓reduceIte, one_ne_zero, hs, WTape.next, WTape.cur,
      List.headD_cons, List.tail_cons, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide]
    rw [show (σ r).right.headD [] = ones w by rw [hr]; rfl, length_ones]
    funext y
    by_cases hy : y = d
    · subst hy; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hy, Function.update_of_ne hy]
      by_cases hy2 : y = r
      · subst hy2; rw [Function.update_self, Function.update_of_ne h1.symm]
      · rw [Function.update_of_ne hy2]
  · simp [slot3, hs, WTape.cur]

end IntegerMultBounds.Schoenhage
