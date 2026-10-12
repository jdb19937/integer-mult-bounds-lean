module

public import IntegerMultBounds.MathlibTM2.Host.Stream
public import IntegerMultBounds.MathlibTM2.Layer.Format

/-!
# Multiplying a coefficient stream by a power of two

Multiplying a residue modulo `2^W` by `2^s` (`s ≤ W`) shifts its bits up by `s` places. On the
pair-symbol format of `coeffSyms`, the new word is `s` copies of `pairSym A false false` followed
by the first `W - s` symbols of the old word (`coeffSyms_shift`).

`shiftWords src dst cS cR tS tR z` applies this to every word of the stream in register `src`.

Register interface (all six registers distinct):

* `src`: the input stream, consumed word by word; the loop runs while `src` is nonempty;
* `dst`: receives the output stream, reversed, on top of its old contents;
* `cS`: a counter holding `s` symbols (any symbols), restored after each word;
* `cR`: a counter holding `W - s` symbols (any symbols), restored after each word;
* `tS`, `tR`: empty temporaries for `cS` and `cR`, empty again after each word.

For each word, `shiftWord`

1. pushes `z` onto `dst` once per symbol of `cS` (moving `cS` onto `tS`, then back);
2. moves one symbol from `src` onto `dst` per symbol of `cR` (moving `cR` onto `tR`, then back);
3. pops and discards one symbol of `src` per symbol of `cS` (moving `cS` onto `tS`, then back);
4. records in `flag` whether `src` is nonempty.

Only the scratch slots `flag` and `sym` of the local state change (`Shift.Scratch`). The step
actions, the counted-loop lemmas and `Shift.moveR_exec` (a `moveR_exec` that also keeps every
non-scratch slot) live in the namespace `IntegerMultBounds.MathlibTM2.Host.Shift`.

Step counts, for `s ≤ W`; the stream theorems also need `1 ≤ W`, since the loop detects the next
word by testing `src`:

* `shiftWord_exec`: one word in exactly `4 * W + 4 * s + 13` steps;
* `shiftWords_exec`: `n` words in exactly `n * (4 * W + 4 * s + 14) + 2` steps;
* `shiftInto_exec`: `shiftWords` followed by `moveR dst out id`, which puts the output in forward
  order onto `out`, in exactly `n * (6 * W + 4 * s + 14) + 4` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

/-- Bit `t < W` of `2^s * x` modulo `2^W`. -/
lemma testBit_val_two_pow_mul {W s : ℕ} (x : ZMod (2 ^ W)) {t : ℕ} (ht : t < W) :
    ((2 ^ s : ZMod (2 ^ W)) * x).val.testBit t = (decide (s ≤ t) && x.val.testBit (t - s)) := by
  have h2 : (2 ^ s : ZMod (2 ^ W)) = ((2 ^ s : ℕ) : ZMod (2 ^ W)) := by push_cast; rfl
  rw [ZMod.val_mul, h2, ZMod.val_natCast, Nat.mod_mul_mod, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_mul]
  simp [ht]

/-- Multiplying a coefficient by `2^s` shifts its pair symbols up by `s` places. -/
theorem coeffSyms_shift {A W s : ℕ} (hs : s ≤ W) (z : GR W) :
    coeffSyms A W ((2 ^ s : ZMod (2 ^ W)) * z.1, (2 ^ s : ZMod (2 ^ W)) * z.2) =
      List.replicate s (pairSym A false false) ++ (coeffSyms A W z).take (W - s) := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 _
    simp only [length_coeffSyms] at h1
    simp only [coeffSyms, List.getElem_ofFn]
    rw [testBit_val_two_pow_mul _ h1, testBit_val_two_pow_mul _ h1]
    by_cases hi : i < s
    · rw [List.getElem_append_left (by simpa using hi)]
      simp [show ¬ s ≤ i by omega]
    · rw [List.getElem_append_right (by simpa using hi)]
      simp [show s ≤ i by omega]

/-- A stream of `n` coefficients has `n * W` symbols. -/
lemma length_flatMap_coeffSyms (A W : ℕ) (zs : List (GR W)) :
    (zs.flatMap (coeffSyms A W)).length = zs.length * W := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
      rw [List.flatMap_cons, List.length_append, ih, length_coeffSyms, List.length_cons]
      ring

end IntegerMultBounds.MathlibTM2.Layer

namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Layer

set_option linter.unusedSimpArgs false

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

namespace Shift

/-! ### Scratch-only changes of the local state -/

/-- `v'` agrees with `v` outside the scratch slots `flag` and `sym`. -/
def Scratch (v v' : HS T Q A U) : Prop := ∃ fl sy, v' = { v with flag := fl, sym := sy }

lemma Scratch.refl (v : HS T Q A U) : Scratch v v := ⟨v.flag, v.sym, rfl⟩

lemma Scratch.set (v : HS T Q A U) (fl : Bool) (sy : Option (Fin (A + 4))) :
    Scratch v { v with flag := fl, sym := sy } := ⟨fl, sy, rfl⟩

lemma Scratch.setFlag (v : HS T Q A U) (fl : Bool) : Scratch v { v with flag := fl } :=
  ⟨fl, v.sym, rfl⟩

lemma Scratch.trans {v₁ v₂ v₃ : HS T Q A U} (h₁ : Scratch v₁ v₂) (h₂ : Scratch v₂ v₃) :
    Scratch v₁ v₃ := by
  obtain ⟨_, _, rfl⟩ := h₁
  obtain ⟨c, d, rfl⟩ := h₂
  exact ⟨c, d, rfl⟩

lemma Scratch.user {v v' : HS T Q A U} (h : Scratch v v') : v'.user = v.user := by
  obtain ⟨_, _, rfl⟩ := h; rfl

lemma Scratch.scan {v v' : HS T Q A U} (h : Scratch v v') : v'.scan = v.scan := by
  obtain ⟨_, _, rfl⟩ := h; rfl

/-! ### Moving a register, changing only the scratch slots -/

theorem moveR_loop (i j : Fin T) (hij : i ≠ j) (f : Fin (A + 4) → Fin (A + 4)) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.R i = l → v.flag = l.head?.isSome →
      ∃ v', Scratch v v' ∧
        Exec body (.loop (·.flag) (.act (moveStep i j f))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := movedR S.R i j f l }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, Scratch.refl v, ?_⟩
      have : ({ S with R := movedR S.R i j f [] } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          by_cases hk : k = j
          · subst hk; simp [movedR]
          · by_cases hk' : k = i
            · subst hk'; simp [movedR, hk, hS]
            · simp [movedR, hk, hk']
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hv, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
        { S with R := Function.update (Function.update S.R i rest) j (f e :: S.R j) }
        (by simp [Function.update_of_ne hij]) rfl
      refine ⟨v', (Scratch.set v _ _).trans hv, ?_⟩
      have hrun : (moveStep i j f : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, flag := rest.head?.isSome }
            { S with R := Function.update (Function.update S.R i rest) j (f e :: S.R j) } := by
        simp [moveStep, peekR, Action.run, hS, update_rt, Function.update_of_ne hij,
          Function.update_of_ne hij.symm]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (moveStep i j f) (mk v S)) he) (by simp; ring) ?_
      congr 2
      funext k
      by_cases hk : k = j
      · subst hk; simp [movedR, Function.update_of_ne hij.symm]
      · by_cases hk' : k = i
        · subst hk'; simp [movedR, hk]
        · simp [movedR, hk, hk']

theorem moveR_exec (i j : Fin T) (hij : i ≠ j) (f : Fin (A + 4) → Fin (A + 4)) (v : HS T Q A U)
    (S : Stacks T A) :
    ∃ v', Scratch v v' ∧
      Exec body (moveR i j f) (mk v S) (2 * (S.R i).length + 2)
        (mk v' { S with R := movedR S.R i j f (S.R i) }) := by
  obtain ⟨v', hv, he⟩ := moveR_loop body i j hij f (S.R i) { v with flag := (S.R i).head?.isSome } S
    rfl rfl
  exact ⟨v', (Scratch.setFlag v _).trans hv,
    Exec.cast (Exec.seq (peekR_run i v S ▸ Exec.act (body := body) (peekR i) (mk v S)) he)
    (by ring) rfl⟩

/-! ### Counted steps -/

/-- Pop counter `c` onto `t`, push `z` onto `dst`, and record whether `c` is nonempty. -/
def zeroStep (c t dst : Fin T) (z : Fin (A + 4)) : Act T Q A U :=
  .pop (.rt c) (fun v o => { v with sym := o })
    (.push (.rt t) (fun v => v.sym.getD blank)
      (.push (.rt dst) (fun _ => z) (peekR c)))

/-- Pop counter `c` onto `t`, move one symbol from `src` onto `dst`, and record whether `c` is
nonempty. -/
def copyStep (c t src dst : Fin T) : Act T Q A U :=
  .pop (.rt c) (fun v o => { v with sym := o })
    (.push (.rt t) (fun v => v.sym.getD blank)
      (.pop (.rt src) (fun v o => { v with sym := o })
        (.push (.rt dst) (fun v => v.sym.getD blank) (peekR c))))

/-- Pop counter `c` onto `t`, pop and discard one symbol of `src`, and record whether `c` is
nonempty. -/
def dropStep (c t src : Fin T) : Act T Q A U :=
  .pop (.rt c) (fun v o => { v with sym := o })
    (.push (.rt t) (fun v => v.sym.getD blank)
      (.pop (.rt src) (fun v o => { v with sym := o }) (peekR c)))

theorem zeroStep_loop (c t dst : Fin T) (z : Fin (A + 4)) (h1 : c ≠ t) (h2 : dst ≠ c)
    (h3 : dst ≠ t) :
    ∀ (cl : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.R c = cl → v.flag = cl.head?.isSome →
      ∃ v' R', Scratch v v' ∧
        Exec body (.loop (·.flag) (.act (zeroStep c t dst z))) (mk v S) (2 * cl.length + 1)
          (mk v' { S with R := R' }) ∧
        R' c = [] ∧ R' t = cl.reverse ++ S.R t ∧ R' dst = List.replicate cl.length z ++ S.R dst ∧
        ∀ k, k ≠ c → k ≠ t → k ≠ dst → R' k = S.R k := by
  intro cl
  induction cl with
  | nil =>
      intro v S hc hf
      exact ⟨v, S.R, Scratch.refl v, .loop_false (by simpa using hf), hc, rfl, rfl,
        fun _ _ _ _ => rfl⟩
  | cons e cl ih =>
      intro v S hc hf
      have hrun : (zeroStep c t dst z : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, flag := cl.head?.isSome } { S with
            R := Function.update (Function.update (Function.update S.R c cl) t (e :: S.R t)) dst
              (z :: S.R dst) } := by
        simp [zeroStep, peekR, Action.run, hc, update_rt, Function.update_of_ne h1,
          Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1.symm,
          Function.update_of_ne h2.symm, Function.update_of_ne h3.symm]
      obtain ⟨v', R', hv, he, hc', ht', hd', hoth⟩ :=
        ih { v with sym := some e, flag := cl.head?.isSome } { S with
          R := Function.update (Function.update (Function.update S.R c cl) t (e :: S.R t)) dst
            (z :: S.R dst) } (by simp [Function.update_of_ne h2.symm, Function.update_of_ne h1])
          rfl
      refine ⟨v', R', (Scratch.set v _ _).trans hv, ?_, hc', ?_, ?_, ?_⟩
      · exact Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
          (hrun ▸ Exec.act (body := body) _ (mk v S)) he) (by simp; ring) rfl
      · rw [ht']; simp [Function.update_of_ne h3.symm]
      · rw [hd']; simp [List.replicate_succ']
      · intro k hk1 hk2 hk3
        rw [hoth k hk1 hk2 hk3]
        simp [Function.update_of_ne hk1, Function.update_of_ne hk2, Function.update_of_ne hk3]

theorem copyStep_loop (c t src dst : Fin T) (h1 : c ≠ t) (h2 : src ≠ c) (h3 : src ≠ t)
    (h4 : dst ≠ c) (h5 : dst ≠ t) (h6 : dst ≠ src) :
    ∀ (cl ys rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      cl.length = ys.length → S.R c = cl → S.R src = ys ++ rest → v.flag = cl.head?.isSome →
      ∃ v' R', Scratch v v' ∧
        Exec body (.loop (·.flag) (.act (copyStep c t src dst))) (mk v S) (2 * cl.length + 1)
          (mk v' { S with R := R' }) ∧
        R' c = [] ∧ R' t = cl.reverse ++ S.R t ∧ R' src = rest ∧
        R' dst = ys.reverse ++ S.R dst ∧
        ∀ k, k ≠ c → k ≠ t → k ≠ src → k ≠ dst → R' k = S.R k := by
  intro cl
  induction cl with
  | nil =>
      intro ys rest v S hlen hc hs hf
      obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
      exact ⟨v, S.R, Scratch.refl v, .loop_false (by simpa using hf), hc, rfl, by simpa using hs,
        rfl, fun _ _ _ _ _ => rfl⟩
  | cons e cl ih =>
      intro ys rest v S hlen hc hs hf
      cases ys with
      | nil => simp at hlen
      | cons x ys =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        have hrun : (copyStep c t src dst : Act T Q A U).run (mk v S) =
            mk { v with sym := some x, flag := cl.head?.isSome } { S with
              R := Function.update (Function.update (Function.update (Function.update S.R c cl) t
                (e :: S.R t)) src (ys ++ rest)) dst (x :: S.R dst) } := by
          simp [copyStep, peekR, Action.run, hc, hs, update_rt,
            Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
            Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6,
            Function.update_of_ne h1.symm, Function.update_of_ne h2.symm,
            Function.update_of_ne h3.symm, Function.update_of_ne h4.symm,
            Function.update_of_ne h5.symm, Function.update_of_ne h6.symm]
        obtain ⟨v', R', hv, he, hc', ht', hs', hd', hoth⟩ := ih ys rest
          { v with sym := some x, flag := cl.head?.isSome } { S with
            R := Function.update (Function.update (Function.update (Function.update S.R c cl) t
              (e :: S.R t)) src (ys ++ rest)) dst (x :: S.R dst) } hlen
          (by simp [Function.update_of_ne h4.symm, Function.update_of_ne h2.symm,
            Function.update_of_ne h1])
          (by simp [Function.update_of_ne h6.symm]) rfl
        refine ⟨v', R', (Scratch.set v _ _).trans hv, ?_, hc', ?_, hs', ?_, ?_⟩
        · exact Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
            (hrun ▸ Exec.act (body := body) _ (mk v S)) he) (by simp; ring) rfl
        · rw [ht']; simp [Function.update_of_ne h5.symm, Function.update_of_ne h3.symm]
        · rw [hd']; simp
        · intro k hk1 hk2 hk3 hk4
          rw [hoth k hk1 hk2 hk3 hk4]
          simp [Function.update_of_ne hk1, Function.update_of_ne hk2, Function.update_of_ne hk3,
            Function.update_of_ne hk4]

theorem dropStep_loop (c t src : Fin T) (h1 : c ≠ t) (h2 : src ≠ c) (h3 : src ≠ t) :
    ∀ (cl ys rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      cl.length = ys.length → S.R c = cl → S.R src = ys ++ rest → v.flag = cl.head?.isSome →
      ∃ v' R', Scratch v v' ∧
        Exec body (.loop (·.flag) (.act (dropStep c t src))) (mk v S) (2 * cl.length + 1)
          (mk v' { S with R := R' }) ∧
        R' c = [] ∧ R' t = cl.reverse ++ S.R t ∧ R' src = rest ∧
        ∀ k, k ≠ c → k ≠ t → k ≠ src → R' k = S.R k := by
  intro cl
  induction cl with
  | nil =>
      intro ys rest v S hlen hc hs hf
      obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
      exact ⟨v, S.R, Scratch.refl v, .loop_false (by simpa using hf), hc, rfl, by simpa using hs,
        fun _ _ _ _ => rfl⟩
  | cons e cl ih =>
      intro ys rest v S hlen hc hs hf
      cases ys with
      | nil => simp at hlen
      | cons x ys =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        have hrun : (dropStep c t src : Act T Q A U).run (mk v S) =
            mk { v with sym := some x, flag := cl.head?.isSome } { S with
              R := Function.update (Function.update (Function.update S.R c cl) t
                (e :: S.R t)) src (ys ++ rest) } := by
          simp [dropStep, peekR, Action.run, hc, hs, update_rt,
            Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
            Function.update_of_ne h1.symm, Function.update_of_ne h2.symm,
            Function.update_of_ne h3.symm]
        obtain ⟨v', R', hv, he, hc', ht', hs', hoth⟩ := ih ys rest
          { v with sym := some x, flag := cl.head?.isSome } { S with
            R := Function.update (Function.update (Function.update S.R c cl) t
              (e :: S.R t)) src (ys ++ rest) } hlen
          (by simp [Function.update_of_ne h2.symm, Function.update_of_ne h1])
          (by simp) rfl
        refine ⟨v', R', (Scratch.set v _ _).trans hv, ?_, hc', ?_, hs', ?_⟩
        · exact Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
            (hrun ▸ Exec.act (body := body) _ (mk v S)) he) (by simp; ring) rfl
        · rw [ht']; simp [Function.update_of_ne h3.symm]
        · intro k hk1 hk2 hk3
          rw [hoth k hk1 hk2 hk3]
          simp [Function.update_of_ne hk1, Function.update_of_ne hk2, Function.update_of_ne hk3]

/-- Run `b` once per symbol of counter `c` (each run moves one symbol of `c` onto `t`), then move
`t` back onto `c`. -/
def counted (c t : Fin T) (b : Act T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR c)) (.seq (.loop (·.flag) (.act b)) (moveR t c id))

/-- A counted loop that empties `c` onto the empty register `t` is followed by restoring `c`, in
`4 * |c| + 4` steps in all. -/
theorem counted_exec (c t : Fin T) (hct : c ≠ t) (b : Act T Q A U) (v v₁ : HS T Q A U)
    (S : Stacks T A) (R₁ : Fin T → List (Fin (A + 4))) (ht : S.R t = [])
    (hv₁ : Scratch { v with flag := (S.R c).head?.isSome } v₁)
    (he : Exec body (.loop (·.flag) (.act b)) (mk { v with flag := (S.R c).head?.isSome } S)
      (2 * (S.R c).length + 1) (mk v₁ { S with R := R₁ }))
    (hc₁ : R₁ c = []) (ht₁ : R₁ t = (S.R c).reverse ++ S.R t) :
    ∃ v₂ R₂, Scratch v v₂ ∧
      Exec body (counted c t b) (mk v S) (4 * (S.R c).length + 4) (mk v₂ { S with R := R₂ }) ∧
      R₂ c = S.R c ∧ R₂ t = [] ∧ ∀ k, k ≠ c → k ≠ t → R₂ k = R₁ k := by
  obtain ⟨v₂, hv₂, he₂⟩ := moveR_exec body t c hct.symm id v₁ { S with R := R₁ }
  refine ⟨v₂, movedR R₁ t c id (R₁ t), ((Scratch.setFlag v _).trans hv₁).trans hv₂,
    Exec.cast (Exec.seq (peekR_run c v S ▸ Exec.act (body := body) (peekR c) (mk v S))
      (Exec.seq he he₂)) ?_ rfl, ?_, ?_, ?_⟩
  · simp [ht₁, ht]; ring
  · simp [movedR, ht₁, ht, hc₁]
  · simp [movedR, hct.symm]
  · intro k hk1 hk2
    simp [movedR, hk1, hk2]

/-! ### One word -/

/-- The shifted word: `s` copies of `z`, then the first `W - s` symbols of `w`. -/
def shiftW {α : Type} (s W : ℕ) (z : α) (w : List α) : List α :=
  List.replicate s z ++ w.take (W - s)

/-- Shift one word: push `|cS|` copies of `z` onto `dst`, move `|cR|` symbols from `src` onto
`dst`, discard `|cS|` symbols of `src`, and record in `flag` whether `src` is nonempty. -/
def shiftWord (src dst cS cR tS tR : Fin T) (z : Fin (A + 4)) : Pr P T Q A U :=
  .seq (counted cS tS (zeroStep cS tS dst z))
    (.seq (counted cR tR (copyStep cR tR src dst))
      (.seq (counted cS tS (dropStep cS tS src)) (.act (peekR src))))

/-- One word `w` of `W ≥ s` symbols on top of `src`, in `4 * W + 4 * s + 13` steps. -/
theorem shiftWord_exec (src dst cS cR tS tR : Fin T) (hreg : [src, dst, cS, cR, tS, tR].Nodup)
    (z : Fin (A + 4)) {W s : ℕ} (hs : s ≤ W) (w rest : List (Fin (A + 4))) (hw : w.length = W)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = w ++ rest) (hcS : (S.R cS).length = s)
    (hcR : (S.R cR).length = W - s) (htS : S.R tS = []) (htR : S.R tR = []) :
    ∃ v' R', Scratch v v' ∧ v'.flag = rest.head?.isSome ∧
      Exec body (shiftWord src dst cS cR tS tR z) (mk v S) (4 * W + 4 * s + 13)
        (mk v' { S with R := R' }) ∧
      R' src = rest ∧ R' dst = (shiftW s W z w).reverse ++ S.R dst ∧
      ∀ k, k ≠ src → k ≠ dst → R' k = S.R k := by
  have hdl : (w.drop (W - s)).length = s := by rw [List.length_drop, hw, Nat.sub_sub_self hs]
  have htl : (w.take (W - s)).length = W - s := by
    rw [List.length_take, hw]; exact Nat.min_eq_left (Nat.sub_le W s)
  have hcost : ∀ a b c, a = s → b = W - s → c = s →
      4 * a + 4 + (4 * b + 4 + (4 * c + 4 + 1)) = 4 * W + 4 * s + 13 := by
    intros; subst_vars; omega
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg
  -- `a`: src ≠ dst, cS, cR, tS, tR; `b`: dst ≠ cS, cR, tS, tR; `c`: cS ≠ cR, tS, tR;
  -- `d`: cR ≠ tS, tR; `e1`: tS ≠ tR
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, ⟨_, c2, _⟩, ⟨_, d2⟩, _⟩ := hreg
  -- phase 1: push `s` copies of `z`
  obtain ⟨v₁, R₁, hv₁, he₁, hc₁, ht₁, hd₁, hoth₁⟩ := zeroStep_loop body cS tS dst z c2 b1 b3
    (S.R cS) { v with flag := (S.R cS).head?.isSome } S rfl rfl
  obtain ⟨v₂, R₂, hv₂, he₂, hc₂, ht₂, hoth₂⟩ := counted_exec body cS tS c2 (zeroStep cS tS dst z) v v₁ S R₁ htS hv₁ he₁
    hc₁ ht₁
  have hfr₂ : ∀ k, k ≠ dst → R₂ k = S.R k := by
    intro k hk
    by_cases k1 : k = cS
    · subst k1; exact hc₂
    by_cases k2 : k = tS
    · subst k2; rw [ht₂, htS]
    rw [hoth₂ k k1 k2, hoth₁ k k1 k2 hk]
  have hd₂ : R₂ dst = List.replicate s z ++ S.R dst := by
    rw [hoth₂ dst b1 b3, hd₁, hcS]
  -- phase 2: move `W - s` symbols from `src` onto `dst`
  obtain ⟨v₃, R₃, hv₃, he₃, hc₃, ht₃, hs₃, hd₃, hoth₃⟩ := copyStep_loop body cR tR src dst d2
    a3 a5 b2 b4 (Ne.symm a1) (R₂ cR) (w.take (W - s)) (w.drop (W - s) ++ rest)
    { v₂ with flag := (R₂ cR).head?.isSome } { S with R := R₂ }
    (by rw [hfr₂ cR (Ne.symm b2), hcR, htl]) rfl
    (by simp only [hfr₂ src a1, hsrc, ← List.append_assoc, List.take_append_drop]) rfl
  obtain ⟨v₄, R₄, hv₄, he₄, hc₄, ht₄, hoth₄⟩ := counted_exec body cR tR d2 (copyStep cR tR src dst) v₂ v₃
    { S with R := R₂ } R₃ (by simp [hfr₂ tR (Ne.symm b4), htR]) hv₃ he₃ hc₃ ht₃
  have hfr₄ : ∀ k, k ≠ src → k ≠ dst → R₄ k = S.R k := by
    intro k hk hk'
    by_cases k1 : k = cR
    · subst k1; rw [hc₄]; exact hfr₂ _ hk'
    by_cases k2 : k = tR
    · subst k2; rw [ht₄, htR]
    rw [hoth₄ k k1 k2, hoth₃ k k1 k2 hk hk']
    exact hfr₂ _ hk'
  have hs₄ : R₄ src = w.drop (W - s) ++ rest := by rw [hoth₄ src a3 a5, hs₃]
  have hd₄ : R₄ dst = (w.take (W - s)).reverse ++ List.replicate s z ++ S.R dst := by
    rw [hoth₄ dst b2 b4, hd₃]; simp [hd₂]
  -- phase 3: discard `s` symbols of `src`
  obtain ⟨v₅, R₅, hv₅, he₅, hc₅, ht₅, hs₅, hoth₅⟩ := dropStep_loop body cS tS src c2 a2 a4
    (R₄ cS) (w.drop (W - s)) rest { v₄ with flag := (R₄ cS).head?.isSome } { S with R := R₄ }
    (by rw [hfr₄ cS (Ne.symm a2) (Ne.symm b1), hcS, hdl]) rfl hs₄ rfl
  obtain ⟨v₆, R₆, hv₆, he₆, hc₆, ht₆, hoth₆⟩ := counted_exec body cS tS c2 (dropStep cS tS src) v₄ v₅
    { S with R := R₄ } R₅ (by simp [hfr₄ tS (Ne.symm a4) (Ne.symm b3), htS]) hv₅ he₅ hc₅ ht₅
  have hs₆ : R₆ src = rest := by rw [hoth₆ src a2 a4, hs₅]
  -- phase 4: test `src`
  have he₇ := Exec.act (body := body) (peekR src) (mk v₆ { S with R := R₆ })
  rw [peekR_run] at he₇
  refine ⟨{ v₆ with flag := (R₆ src).head?.isSome }, R₆,
    ((((hv₂.trans hv₄).trans hv₆)).trans (Scratch.setFlag v₆ _)), by simp [hs₆],
    Exec.cast (Exec.seq he₂ (Exec.seq he₄ (Exec.seq he₆ he₇))) ?_ rfl, hs₆, ?_, ?_⟩
  · exact hcost _ _ _ hcS (by dsimp only; rw [hfr₂ cR (Ne.symm b2), hcR])
      (by dsimp only; rw [hfr₄ cS (Ne.symm a2) (Ne.symm b1), hcS])
  · rw [hoth₆ dst b1 b3, hoth₅ dst b1 b3 (Ne.symm a1)]
    dsimp only
    rw [hd₄]
    simp [shiftW]
  · intro k hk hk'
    by_cases k1 : k = cS
    · subst k1; rw [hc₆]; exact hfr₄ _ hk hk'
    by_cases k2 : k = tS
    · subst k2; rw [ht₆, htS]
    rw [hoth₆ k k1 k2, hoth₅ k k1 k2 hk]
    exact hfr₄ _ hk hk'

end Shift

open Shift

/-! ### The stream -/

/-- Multiply every coefficient of the stream in `src` by `2^s` modulo `2^W`, pushing the result
onto `dst` (reversed). `cS` holds `s` symbols, `cR` holds `W - s` symbols, `tS` and `tR` are
empty temporaries, and `z` is the zero pair symbol. -/
def shiftWords (src dst cS cR tS tR : Fin T) (z : Fin (A + 4)) : Pr P T Q A U :=
  .seq (.act (peekR src)) (.loop (·.flag) (shiftWord src dst cS cR tS tR z))

/-- The word loop of `shiftWords` over words `ws` of length `W ≥ 1`. -/
theorem shiftWords_loop (src dst cS cR tS tR : Fin T) (hreg : [src, dst, cS, cR, tS, tR].Nodup)
    (z : Fin (A + 4)) {W s : ℕ} (hW : 1 ≤ W) (hs : s ≤ W) :
    ∀ (ws : List (List (Fin (A + 4)))) (v : HS T Q A U) (S : Stacks T A),
      (∀ w ∈ ws, w.length = W) → S.R src = ws.flatten → (S.R cS).length = s →
      (S.R cR).length = W - s → S.R tS = [] → S.R tR = [] → v.flag = ws.flatten.head?.isSome →
      ∃ v' R', Scratch v v' ∧
        Exec body (.loop (·.flag) (shiftWord src dst cS cR tS tR z)) (mk v S)
          (ws.length * (4 * W + 4 * s + 14) + 1) (mk v' { S with R := R' }) ∧
        R' src = [] ∧ R' dst = (ws.map (shiftW s W z)).flatten.reverse ++ S.R dst ∧
        ∀ k, k ≠ src → k ≠ dst → R' k = S.R k := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg'
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, _, _, _⟩ := hreg'
  intro ws
  induction ws with
  | nil =>
      intro v S _ hsrc _ _ _ _ hf
      exact ⟨v, S.R, Scratch.refl v, Exec.cast (.loop_false (by simpa using hf)) (by simp) rfl,
        by simpa using hsrc, by simp, fun _ _ _ => rfl⟩
  | cons w ws ih =>
      intro v S hlen hsrc hcS hcR htS htR hf
      have hw : w.length = W := hlen w List.mem_cons_self
      obtain ⟨v₁, R₁, hv₁, hf₁, he₁, hs₁, hd₁, hoth₁⟩ := shiftWord_exec body src dst cS cR tS tR
        hreg z hs w ws.flatten hw v S (by simpa using hsrc) hcS hcR htS htR
      obtain ⟨v', R', hv, he, hs', hd', hoth⟩ := ih v₁ { S with R := R₁ }
        (fun w' hw' => hlen w' (List.mem_cons_of_mem _ hw')) hs₁
        (by simp [hoth₁ cS (Ne.symm a2) (Ne.symm b1), hcS])
        (by simp [hoth₁ cR (Ne.symm a3) (Ne.symm b2), hcR])
        (by simp [hoth₁ tS (Ne.symm a4) (Ne.symm b3), htS])
        (by simp [hoth₁ tR (Ne.symm a5) (Ne.symm b4), htR]) hf₁
      have hft : v.flag = true := by
        rw [hf]
        cases w with
        | nil => simp at hw; omega
        | cons x w' => simp
      refine ⟨v', R', hv₁.trans hv, Exec.cast (Exec.loop_true (body := body) (f := (·.flag))
        hft he₁ he) (by simp; ring) rfl, hs', ?_, ?_⟩
      · rw [hd']; simp [hd₁]
      · intro k hk hk'
        rw [hoth k hk hk']
        exact hoth₁ k hk hk'

/-- The coefficient stream of `zs` in `src` becomes, reversed on top of `dst`, the stream of the
coefficients `2^s * z`, for `1 ≤ W` and `s ≤ W`. `src` ends empty and every register other than
`src` and `dst` (in particular `cS`, `cR`, `tS`, `tR`) is unchanged. Exactly
`|zs| * (4 * W + 4 * s + 14) + 2` steps. -/
theorem shiftWords_exec (src dst cS cR tS tR : Fin T) (hreg : [src, dst, cS, cR, tS, tR].Nodup)
    {W s : ℕ} (hW : 1 ≤ W) (hs : s ≤ W) (zs : List (GR W)) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = zs.flatMap (coeffSyms A W)) (hcS : (S.R cS).length = s)
    (hcR : (S.R cR).length = W - s) (htS : S.R tS = []) (htR : S.R tR = []) :
    ∃ v' R', v'.user = v.user ∧ v'.scan = v.scan ∧
      Exec body (shiftWords src dst cS cR tS tR (pairSym A false false)) (mk v S)
        (zs.length * (4 * W + 4 * s + 14) + 2) (mk v' { S with R := R' }) ∧
      R' src = [] ∧
      R' dst = ((zs.map fun z => ((2 ^ s : ZMod (2 ^ W)) * z.1, (2 ^ s : ZMod (2 ^ W)) * z.2)).flatMap
        (coeffSyms A W)).reverse ++ S.R dst ∧
      ∀ k, k ≠ src → k ≠ dst → R' k = S.R k := by
  obtain ⟨v', R', hv, he, hs', hd', hoth⟩ := shiftWords_loop body src dst cS cR tS tR hreg
    (pairSym A false false) hW hs (zs.map (coeffSyms A W))
    { v with flag := (S.R src).head?.isSome } S
    (fun w hw => by obtain ⟨z, _, rfl⟩ := List.mem_map.1 hw; exact length_coeffSyms A W z)
    (by rw [hsrc, List.flatMap_def])
    hcS hcR htS htR (by rw [hsrc, List.flatMap_def])
  have hv' := (Scratch.setFlag v _).trans hv
  have hout : ((zs.map (coeffSyms A W)).map (shiftW s W (pairSym A false false))).flatten =
      (zs.map fun z => ((2 ^ s : ZMod (2 ^ W)) * z.1, (2 ^ s : ZMod (2 ^ W)) * z.2)).flatMap
        (coeffSyms A W) := by
    rw [List.flatMap_map, List.flatMap_def, List.map_map]
    congr 1
    apply List.map_congr_left
    intro z _
    rw [Function.comp_apply, coeffSyms_shift hs]
    rfl
  refine ⟨v', R', hv'.user, hv'.scan, Exec.cast (Exec.seq (peekR_run src v S ▸
    Exec.act (body := body) (peekR src) (mk v S)) he) (by simp; ring) rfl, hs', ?_, hoth⟩
  rw [hd', hout]

/-- Shift the stream in `src` onto `dst`, then move `dst` onto `out`, which restores forward
order. -/
def shiftInto (src dst out cS cR tS tR : Fin T) (z : Fin (A + 4)) : Pr P T Q A U :=
  .seq (shiftWords src dst cS cR tS tR z) (moveR dst out id)

/-- `shiftInto` with an empty `dst` puts the shifted stream in forward order on top of `out`
(`out = src` shifts in place); `dst` ends empty, `src` ends empty unless it is `out`, and every
other register is unchanged. Exactly `|zs| * (6 * W + 4 * s + 14) + 4` steps. -/
theorem shiftInto_exec (src dst out cS cR tS tR : Fin T) (hreg : [src, dst, cS, cR, tS, tR].Nodup)
    (hout : out ≠ dst) {W s : ℕ} (hW : 1 ≤ W) (hs : s ≤ W) (zs : List (GR W)) (v : HS T Q A U)
    (S : Stacks T A) (hsrc : S.R src = zs.flatMap (coeffSyms A W)) (hcS : (S.R cS).length = s)
    (hcR : (S.R cR).length = W - s) (htS : S.R tS = []) (htR : S.R tR = []) (hdst : S.R dst = []) :
    ∃ v' R', v'.user = v.user ∧ v'.scan = v.scan ∧
      Exec body (shiftInto src dst out cS cR tS tR (pairSym A false false)) (mk v S)
        (zs.length * (6 * W + 4 * s + 14) + 4) (mk v' { S with R := R' }) ∧
      R' out = (zs.map fun z => ((2 ^ s : ZMod (2 ^ W)) * z.1, (2 ^ s : ZMod (2 ^ W)) * z.2)).flatMap
        (coeffSyms A W) ++ (if out = src then [] else S.R out) ∧
      (out ≠ src → R' src = []) ∧
      ∀ k, k ≠ src → k ≠ out → R' k = S.R k := by
  have hsd : src ≠ dst := by
    intro h; rw [h] at hreg; simp at hreg
  obtain ⟨v₁, R₁, hu₁, hsc₁, he₁, hs₁, hd₁, hoth₁⟩ := shiftWords_exec body src dst cS cR tS tR hreg
    hW hs zs v S hsrc hcS hcR htS htR
  obtain ⟨v₂, hv₂, he₂⟩ := Shift.moveR_exec body dst out hout.symm id v₁ { S with R := R₁ }
  have hlen : ((zs.map fun z => ((2 ^ s : ZMod (2 ^ W)) * z.1,
      (2 ^ s : ZMod (2 ^ W)) * z.2)).flatMap (coeffSyms A W)).length = zs.length * W := by
    rw [length_flatMap_coeffSyms, List.length_map]
  have hR₁out : R₁ out = if out = src then [] else S.R out := by
    by_cases h : out = src
    · subst h; simp [hs₁]
    · simp [h, hoth₁ out h hout]
  refine ⟨v₂, _, hv₂.user.trans hu₁, hv₂.scan.trans hsc₁, Exec.cast (Exec.seq he₁ he₂) ?_ rfl,
    ?_, ?_, ?_⟩
  · simp only [hd₁, hdst, List.append_nil, List.length_reverse, hlen]
    ring
  · simp [movedR, hd₁, hdst, hR₁out]
  · intro h
    simp [movedR, Function.update_of_ne (Ne.symm h), Function.update_of_ne hsd, hs₁]
  · intro k hk hk'
    by_cases hkd : k = dst
    · subst hkd; simp [movedR, Function.update_of_ne hk', hdst]
    · simp [movedR, Function.update_of_ne hk', Function.update_of_ne hkd, hoth₁ k hk hkd]

end IntegerMultBounds.MathlibTM2.Host
