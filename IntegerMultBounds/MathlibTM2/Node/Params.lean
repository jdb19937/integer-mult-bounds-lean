module

public import IntegerMultBounds.MathlibTM2.Host.Index
public import Mathlib.Combinatorics.Colex

/-!
# Unary parameter registers and binary masks

Host utility programs on the registers `S.R i`. A unary value `k` on a register is any list of
length `k` (the register holds `k` symbols). The programs read only the lengths of their unary
inputs and restore those registers exactly; symbols they create are `tick = bitSymbol true`.
Every `_exec` theorem gives the final register file exactly, as a `Function.update` of the
initial one, so every other register ends as it started; it also gives `v'.user = v.user` and an
exact step count or a step bound linear in the lengths involved.

**Loops.** `drainR a f` pops `a` into `sym` once per symbol and runs a continuation transformer
`f` acting on the registers as `Φ x` (`RegFx`, `Frame`); `drainR_exec` folds `Φ` over the symbols.
`scanR a t f` also keeps each symbol on a spare `t` and moves the spare back onto `a`
(`scanR_exec`, `scanR_exec'`). `scanP a t p` runs a program `p` once per symbol, specified by the
register files `Ψ j` off `a` and `t` (`IterSpec`, `scanP_exec`).

**Unary arithmetic.** Spares start empty and end empty.
* `ucopy a b t`, `uadd a b t`: `b` gains `|a|` ticks, in `4 |a| + 4` steps.
* `umul c a b t`: `b` gains `c |a|` ticks, in `4 |a| + 4` steps (`c` pushes per symbol).
* `usub a b t`: `b` drops its top `min |a| |b|` symbols, in `4 |a| + 4` steps.
* `udiv c a b t`, `c ≥ 1`: `b` gains `|a| / c` ticks, in at most `4 |a| + 4` steps.
* `uclear a`: `a` is emptied, in `2 |a| + 2` steps.
* `zeroBits len z t`: `z` gains `binSyms |len| 0` on top, in `4 |len| + 4` steps.
* `upow2 a b t₁ t₂`: every symbol of `b` is repeated `2 ^ |a|` times, so `b` ends holding
  `2 ^ |a| · |b|` symbols, in at most `4 · 2 ^ |a| · |b| + 9 |a| + 4` steps. Spares: `t₁` keeps
  the scanned symbols of `a`, `t₂` holds `b` during each doubling (`udbl`).
* `expProg G F uR jR eR t₁ t₂ t₃`: the empty `eR` ends holding `expSeq G F |uR| |jR|` ticks, where
  `expSeq G F u` is `E₀ = u`, `E_{i+1} = G + F E_i` (`expSeq_eq_rec`, `eq_expSeq`), in at most
  `4 |uR| + 2 |jR| + 8 + ∑_{i < |jR|} (8 E_i + 12)` steps. Spares: `t₁` (the initial copy and the
  scanR of `jR`), `t₂` (the previous exponent), `t₃` (the scanR inside `umul`).

**Masks.** A mask is built least significant bit first on an accumulator `w`, against a position
counter `cnt` holding `n` ticks: `emit cnt w b` pops `cnt` and, when it held a symbol, pushes
`bitSymbol b` onto `w`, so positions at or past `n` are dropped. `maskRegs` describes `cnt` and
`w` after `p` positions (`emitFx_maskRegs`, `foldl_emitFx`); `maskFinish_exec` moves `w` onto the
output, bit `0` on top.
* `strideMask nR oR KR kR z cnt w t₁ t₂ M pred`, from unary `n`, `o`, `K ≥ 1`, `k`: `z` gains
  `binSyms n (maskVal o K k M pred)` on top, `maskVal o K k M pred` being
  `∑_{i < M k, pred (i / k)} 2 ^ (o + K i)` (`testBit_maskVal`), in at most
  `10 n + 4 o + M (k (4 K + 9) + 4) + 15` steps. Positions: `o` zeros; for each slot `m < M`
  (`strideSlots`, a static loop) and item `r < k` (`scanP` over `kR`), the bit `pred m` and
  `K - 1` zeros (`strideItem`); `n` zeros of padding. Spares: `cnt`, `w`; `t₁` for the scans of
  `nR`, `oR`, `kR`; `t₂` for the scanR of `KR`.
* `bitMask nR tR z cnt w t₁`, from unary `n`, `t`: `z` gains `binSyms n (2 ^ t)` on top, in
  `10 n + 4 t + 15` steps. Spares: `cnt`, `w`, `t₁`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host


/-- Register contents of a host: the right stacks. -/
abbrev Regs (T A : ℕ) := Fin T → List (Fin (A + 4))

/-- The symbol pushed for one unit of a unary value. -/
def tick {A : ℕ} : Fin (A + 4) := bitSymbol true

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-! ### Pushing constant blocks -/

/-- Push `c` copies of `g v` onto register `j`, then continue with `k`. -/
def pushN (j : Fin T) (g : HS T Q A U → Fin (A + 4)) : ℕ → Act T Q A U → Act T Q A U
  | 0, k => k
  | c + 1, k => .push (.rt j) g (pushN j g c k)

lemma pushN_run (j : Fin T) (g : HS T Q A U → Fin (A + 4)) (k : Act T Q A U) :
    ∀ (c : ℕ) (v : HS T Q A U) (S : Stacks T A), (pushN j g c k).run (mk v S) =
      k.run (mk v { S with R := Function.update S.R j (List.replicate c (g v) ++ S.R j) })
  | 0, v, S => by simp [pushN]
  | c + 1, v, S => by
      simp only [pushN, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk]
      rw [pushN_run j g k c v]
      congr 3
      funext i
      by_cases hi : i = j
      · subst hi; simp [List.replicate_succ']
      · simp [hi]

/-! ### Draining and scanning a register -/

/-- An effect of a continuation transformer `f` on the registers: run with `sym = some x`, `f k`
acts as `Φ x` on the registers, keeps `user`, and then runs `k`. -/
def RegFx (f : Act T Q A U → Act T Q A U) (Φ : Fin (A + 4) → Regs T A → Regs T A) : Prop :=
  ∀ (x : Fin (A + 4)) (k : Act T Q A U) (v : HS T Q A U) (S : Stacks T A), v.sym = some x →
    ∃ v' : HS T Q A U, v'.user = v.user ∧ (f k).run (mk v S) = k.run (mk v' { S with R := Φ x S.R })

/-- `Φ` neither reads nor writes register `a`. -/
def Frame (a : Fin T) (Φ : Fin (A + 4) → Regs T A → Regs T A) : Prop :=
  ∀ x (R : Regs T A) l, Φ x (Function.update R a l) = Function.update (Φ x R) a l

namespace Frame

variable {a : Fin T} {Φ : Fin (A + 4) → Regs T A → Regs T A}

lemma apply (h : Frame a Φ) (x : Fin (A + 4)) (R : Regs T A) : Φ x R a = R a := by
  have := congrFun (h x R (R a)) a
  simpa using this

lemma foldl (h : Frame a Φ) (l : List (Fin (A + 4))) (R : Regs T A) (l' : List (Fin (A + 4))) :
    l.foldl (fun R x => Φ x R) (Function.update R a l') =
      Function.update (l.foldl (fun R x => Φ x R) R) a l' := by
  induction l generalizing R with
  | nil => rfl
  | cons x rest ih => simp only [List.foldl_cons]; rw [h, ih]

lemma foldl_apply (h : Frame a Φ) (l : List (Fin (A + 4))) (R : Regs T A) :
    (l.foldl (fun R x => Φ x R) R) a = R a := by
  induction l generalizing R with
  | nil => rfl
  | cons x rest ih => simp only [List.foldl_cons]; rw [ih, h.apply]

end Frame

/-- Pop register `a` into `sym`, run `f`, and record in `flag` whether `a` is nonempty. -/
def popDo (a : Fin T) (f : Act T Q A U → Act T Q A U) : Act T Q A U :=
  .pop (.rt a) (fun v o => { v with sym := o }) (f (peekR a))

/-- Run `f` once per symbol of register `a`, with the symbol in `sym`; `a` ends empty. -/
def drainR (a : Fin T) (f : Act T Q A U → Act T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR a)) (.loop (·.flag) (.act (popDo a f)))

theorem drainR_loop (a : Fin T) {f : Act T Q A U → Act T Q A U}
    {Φ : Fin (A + 4) → Regs T A → Regs T A} (hf : RegFx f Φ) (ha : Frame a Φ) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A), S.R a = l →
      v.flag = l.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (popDo a f))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := Function.update (l.foldl (fun R x => Φ x R) S.R) a [] }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hfl
      refine ⟨v, rfl, ?_⟩
      have : ({ S with R := Function.update (([] : List (Fin (A + 4))).foldl
          (fun R x => Φ x R) S.R) a [] } : Stacks T A) = S := by
        rw [List.foldl_nil, ← hS, Function.update_eq_self]
      rw [this]
      exact .loop_false (by simpa using hfl)
  | cons x rest ih =>
      intro v S hS hfl
      obtain ⟨v₁, hu₁, hrun⟩ := hf x (peekR a) { v with sym := some x }
        { S with R := Function.update S.R a rest } rfl
      have hpop : (popDo a f : Act T Q A U).run (mk v S) =
          (f (peekR a)).run (mk { v with sym := some x } { S with R := Function.update S.R a rest }) := by
        simp [popDo, Action.run, hS, update_rt]
      rw [hrun, peekR_run] at hpop
      obtain ⟨v', hu, he⟩ := ih { v₁ with flag := (Φ x (Function.update S.R a rest) a).head?.isSome }
        { S with R := Φ x (Function.update S.R a rest) } (by simp [ha.apply]) (by simp [ha.apply])
      refine ⟨v', by rw [hu]; simpa using hu₁, ?_⟩
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hfl)
        (hpop ▸ Exec.act (body := body) (popDo a f) (mk v S)) he) (by simp; ring) ?_
      simp only [List.foldl_cons]
      rw [ha, ha.foldl, Function.update_idem]

/-- `drainR`: `2 |a| + 2` steps; the registers end as `Φ` folded over the symbols of `a`, top
first, with `a` empty. -/
theorem drainR_exec (a : Fin T) {f : Act T Q A U → Act T Q A U}
    {Φ : Fin (A + 4) → Regs T A → Regs T A} (hf : RegFx f Φ) (ha : Frame a Φ)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (drainR a f) (mk v S) (2 * (S.R a).length + 2)
        (mk v' { S with R := Function.update ((S.R a).foldl (fun R x => Φ x R) S.R) a [] }) := by
  obtain ⟨v', hu, he⟩ := drainR_loop body a hf ha (S.R a) { v with flag := (S.R a).head?.isSome } S
    rfl rfl
  exact ⟨v', hu, Exec.cast (Exec.seq (peekR_run a v S ▸ Exec.act (body := body) (peekR a) (mk v S))
    he) (by ring) rfl⟩

/-- Push `sym` onto register `t`, then run `f`. -/
def keepIn (t : Fin T) (f : Act T Q A U → Act T Q A U) (k : Act T Q A U) : Act T Q A U :=
  .push (.rt t) (fun v => v.sym.getD blank) (f k)

/-- Run `f` once per symbol of register `a`, keeping the symbols on `t` and moving them back onto
`a` at the end. -/
def scanR (a t : Fin T) (f : Act T Q A U → Act T Q A U) : Pr P T Q A U :=
  .seq (drainR a (keepIn t f)) (moveR t a id)

lemma regFx_keepIn (t : Fin T) {f : Act T Q A U → Act T Q A U}
    {Φ : Fin (A + 4) → Regs T A → Regs T A} (hf : RegFx f Φ) :
    RegFx (keepIn t f) (fun x R => Φ x (Function.update R t (x :: R t))) := by
  intro x k v S hx
  obtain ⟨v', hu, h⟩ := hf x k v { S with R := Function.update S.R t (x :: S.R t) } hx
  refine ⟨v', hu, ?_⟩
  simp only [keepIn, Action.run, mk_var, mk_stk, get_rt, hx, Option.getD_some, update_rt, store_mk]
  exact h

lemma frame_keepIn {a t : Fin T} (hat : a ≠ t) {Φ : Fin (A + 4) → Regs T A → Regs T A}
    (ha : Frame a Φ) : Frame a (fun x R => Φ x (Function.update R t (x :: R t))) := by
  intro x R l
  simp only
  rw [Function.update_of_ne hat.symm, Function.update_comm hat, ha]

lemma foldl_keepIn {t : Fin T} {Φ : Fin (A + 4) → Regs T A → Regs T A} (ht : Frame t Φ) :
    ∀ (l : List (Fin (A + 4))) (R : Regs T A),
      l.foldl (fun R x => Φ x (Function.update R t (x :: R t))) R =
        Function.update (l.foldl (fun R x => Φ x R) R) t (l.reverse ++ R t)
  | [], R => by simp
  | x :: rest, R => by
      simp only [List.foldl_cons]
      rw [foldl_keepIn ht rest, ht, ht.foldl, Function.update_idem]
      simp

/-- `scanR`: `4 |a| + 2 |t| + 4` steps. The registers end as `Φ` folded over the symbols of `a`,
top first, then `t` is emptied and `a` holds `t` reversed on top of its old contents. -/
theorem scanR_exec {a t : Fin T} (hat : a ≠ t) {f : Act T Q A U → Act T Q A U}
    {Φ : Fin (A + 4) → Regs T A → Regs T A} (hf : RegFx f Φ) (ha : Frame a Φ) (ht : Frame t Φ)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (scanR a t f) (mk v S) (4 * (S.R a).length + 2 * (S.R t).length + 4)
        (mk v' { S with
          R := Function.update (Function.update ((S.R a).foldl (fun R x => Φ x R) S.R) t []) a
            ((S.R t).reverse ++ S.R a) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := drainR_exec body a (regFx_keepIn t hf) (frame_keepIn hat ha) v S
  rw [foldl_keepIn ht] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body t a hat.symm id v₁
    { S with
      R := Function.update (Function.update ((S.R a).foldl (fun R x => Φ x R) S.R) t
        ((S.R a).reverse ++ S.R t)) a [] }
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
  · simp [Function.update_of_ne hat.symm]; ring
  · congr 2
    simp only [movedR, Function.update_of_ne hat.symm, Function.update_self, List.map_id,
      List.reverse_append, List.reverse_reverse, List.append_nil]
    rw [Function.update_comm hat.symm, Function.update_idem, Function.update_comm hat,
      Function.update_idem, Function.update_comm hat.symm]

/-- `scanR` with `t` empty: `4 |a| + 4` steps, and only `Φ` acts on the registers. -/
theorem scanR_exec' {a t : Fin T} (hat : a ≠ t) {f : Act T Q A U → Act T Q A U}
    {Φ : Fin (A + 4) → Regs T A → Regs T A} (hf : RegFx f Φ) (ha : Frame a Φ) (ht : Frame t Φ)
    (v : HS T Q A U) (S : Stacks T A) (ht0 : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (scanR a t f) (mk v S) (4 * (S.R a).length + 4)
        (mk v' { S with R := (S.R a).foldl (fun R x => Φ x R) S.R }) := by
  obtain ⟨v', hu, he⟩ := scanR_exec body hat hf ha ht v S
  refine ⟨v', hu, Exec.cast he (by simp [ht0]) ?_⟩
  congr 2
  funext k
  by_cases hk : k = a
  · subst hk; simp [ht0, ha.foldl_apply]
  · by_cases hk' : k = t
    · subst hk'; simp [hk, ht0, ht.foldl_apply]
    · simp [hk, hk']


/-! ### Pushing, popping, clearing -/

/-- The effect of pushing `c` copies of `h x` onto register `j`. -/
def pushFx (j : Fin T) (c : ℕ) (h : Fin (A + 4) → Fin (A + 4)) :
    Fin (A + 4) → Regs T A → Regs T A :=
  fun x R => Function.update R j (List.replicate c (h x) ++ R j)

lemma regFx_pushN (j : Fin T) (c : ℕ) (g : HS T Q A U → Fin (A + 4))
    (h : Fin (A + 4) → Fin (A + 4)) (hg : ∀ v x, v.sym = some x → g v = h x) :
    RegFx (pushN j g c) (pushFx j c h) := by
  intro x k v S hx
  exact ⟨v, rfl, by rw [pushN_run, hg v x hx]; rfl⟩

lemma frame_pushFx {a j : Fin T} (haj : a ≠ j) (c : ℕ) (h : Fin (A + 4) → Fin (A + 4)) :
    Frame a (pushFx (T := T) j c h) := by
  intro x R l
  simp only [pushFx]
  rw [Function.update_of_ne haj.symm, Function.update_comm haj]

lemma foldl_pushFx (j : Fin T) (c : ℕ) (h : Fin (A + 4) → Fin (A + 4)) :
    ∀ (l : List (Fin (A + 4))) (R : Regs T A), l.foldl (fun R x => pushFx j c h x R) R =
      Function.update R j ((l.reverse.flatMap fun x => List.replicate c (h x)) ++ R j)
  | [], R => by simp
  | x :: rest, R => by
      simp only [List.foldl_cons]
      rw [foldl_pushFx j c h rest]
      simp [pushFx]

lemma flatMap_replicate_const {α β : Type} (l : List α) (c : ℕ) (y : β) :
    (l.flatMap fun _ => List.replicate c y) = List.replicate (c * l.length) y := by
  induction l with
  | nil => simp
  | cons x rest ih =>
      rw [List.flatMap_cons, ih, List.replicate_append_replicate, List.length_cons]
      congr 1; ring

/-- Push `c` copies of `y` onto `b` per symbol of `a`, keeping `a` on the empty `t`. -/
def umulSym (c : ℕ) (y : Fin (A + 4)) (a b t : Fin T) : Pr P T Q A U :=
  scanR a t (pushN b (fun _ => y) c)

/-- `umulSym`: `b` gains `c |a|` copies of `y`; `4 |a| + 4` steps. -/
theorem umulSym_exec (c : ℕ) (y : Fin (A + 4)) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (v : HS T Q A U) (S : Stacks T A) (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (umulSym c y a b t) (mk v S) (4 * (S.R a).length + 4)
        (mk v' { S with
          R := Function.update S.R b (List.replicate (c * (S.R a).length) y ++ S.R b) }) := by
  obtain ⟨v', hu, he⟩ := scanR_exec' body hat
    (regFx_pushN b c (fun _ => y) (fun _ => y) (fun _ _ _ => rfl))
    (frame_pushFx hab c _) (frame_pushFx hbt.symm c _) v S ht
  refine ⟨v', hu, Exec.cast he rfl ?_⟩
  rw [foldl_pushFx, flatMap_replicate_const, List.length_reverse]

/-- `b` gains `c |a|` ticks; `a` is restored through the empty `t`. -/
def umul (c : ℕ) (a b t : Fin T) : Pr P T Q A U := umulSym c tick a b t

/-- `b` gains `|a|` ticks; `a` is restored through the empty `t`. -/
def ucopy (a b t : Fin T) : Pr P T Q A U := umulSym 1 tick a b t

/-- Unary addition `b += a`: the same program as `ucopy`. -/
abbrev uadd (a b t : Fin T) : Pr P T Q A U := ucopy a b t

/-- `umul`: `b` gains `c |a|` ticks in `4 |a| + 4` steps. -/
theorem umul_exec (c : ℕ) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (v : HS T Q A U) (S : Stacks T A) (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (umul c a b t) (mk v S) (4 * (S.R a).length + 4)
        (mk v' { S with
          R := Function.update S.R b (List.replicate (c * (S.R a).length) tick ++ S.R b) }) :=
  umulSym_exec body c tick hab hat hbt v S ht

/-- `ucopy`: `b` gains `|a|` ticks in `4 |a| + 4` steps. -/
theorem ucopy_exec {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (v : HS T Q A U) (S : Stacks T A) (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (ucopy a b t) (mk v S) (4 * (S.R a).length + 4)
        (mk v' { S with
          R := Function.update S.R b (List.replicate (S.R a).length tick ++ S.R b) }) := by
  simpa [ucopy] using umulSym_exec body 1 tick hab hat hbt v S ht

/-- `uadd`: `b` gains `|a|` ticks in `4 |a| + 4` steps. -/
theorem uadd_exec {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (v : HS T Q A U) (S : Stacks T A) (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (uadd a b t) (mk v S) (4 * (S.R a).length + 4)
        (mk v' { S with
          R := Function.update S.R b (List.replicate (S.R a).length tick ++ S.R b) }) :=
  ucopy_exec body hab hat hbt v S ht

lemma binSyms_zero_right (L : ℕ) :
    (binSyms L 0 : List (Fin (A + 4))) = List.replicate L (bitSymbol false) := by
  simp [binSyms, List.ofFn_const]

/-- Push `binSyms |len| 0` (all `bitSymbol false`) onto `z`, through the empty `t`. -/
def zeroBits (len z t : Fin T) : Pr P T Q A U := umulSym 1 (bitSymbol false) len z t

/-- `zeroBits`: `4 |len| + 4` steps. -/
theorem zeroBits_exec {len z t : Fin T} (hlz : len ≠ z) (hlt : len ≠ t) (hzt : z ≠ t)
    (v : HS T Q A U) (S : Stacks T A) (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (zeroBits len z t) (mk v S) (4 * (S.R len).length + 4)
        (mk v' { S with R := Function.update S.R z (binSyms (S.R len).length 0 ++ S.R z) }) := by
  simpa [zeroBits, binSyms_zero_right] using umulSym_exec body 1 (bitSymbol false) hlz hlt hzt v S ht

/-- Pop register `j`, discarding the symbol, then continue with `k`. -/
def dropTop (j : Fin T) (k : Act T Q A U) : Act T Q A U := .pop (.rt j) (fun v _ => v) k

/-- The effect of `dropTop j`. -/
def popFx (j : Fin T) : Fin (A + 4) → Regs T A → Regs T A :=
  fun _ R => Function.update R j (R j).tail

lemma regFx_dropTop (j : Fin T) : RegFx (dropTop (T := T) (Q := Q) (A := A) (U := U) j) (popFx j) := by
  intro x k v S _
  exact ⟨v, rfl, by simp [dropTop, Action.run, update_rt, popFx]⟩

lemma frame_popFx {a j : Fin T} (haj : a ≠ j) : Frame a (popFx (T := T) (A := A) j) := by
  intro x R l
  simp only [popFx]
  rw [Function.update_of_ne haj.symm, Function.update_comm haj]

lemma foldl_popFx (j : Fin T) :
    ∀ (l : List (Fin (A + 4))) (R : Regs T A), l.foldl (fun R x => popFx j x R) R =
      Function.update R j ((R j).drop l.length)
  | [], R => by simp
  | x :: rest, R => by
      simp only [List.foldl_cons]
      rw [foldl_popFx j rest]
      simp [popFx, List.drop_tail, Nat.add_comm]

/-- Unary subtraction: `b` loses `min |a| |b|` symbols; `a` is restored through the empty `t`. -/
def usub (a b t : Fin T) : Pr P T Q A U := scanR a t (dropTop b)

/-- `usub`: `b` drops its top `|a|` symbols in `4 |a| + 4` steps. -/
theorem usub_exec {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (v : HS T Q A U) (S : Stacks T A) (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (usub a b t) (mk v S) (4 * (S.R a).length + 4)
        (mk v' { S with R := Function.update S.R b ((S.R b).drop (S.R a).length) }) := by
  obtain ⟨v', hu, he⟩ := scanR_exec' body hat (regFx_dropTop b) (frame_popFx hab)
    (frame_popFx hbt.symm) v S ht
  exact ⟨v', hu, Exec.cast he rfl (by rw [foldl_popFx])⟩

/-- Empty register `a`. -/
def uclear (a : Fin T) : Pr P T Q A U := drainR a id

/-- `uclear`: `2 |a| + 2` steps. -/
theorem uclear_exec (a : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (uclear a) (mk v S) (2 * (S.R a).length + 2)
        (mk v' { S with R := Function.update S.R a [] }) := by
  have hf : RegFx (id : Act T Q A U → Act T Q A U) (fun _ R => R) :=
    fun x k v S _ => ⟨v, rfl, rfl⟩
  obtain ⟨v', hu, he⟩ := drainR_exec body a hf (fun _ _ _ => rfl) v S
  refine ⟨v', hu, Exec.cast he rfl ?_⟩
  have : ∀ (l : List (Fin (A + 4))) (R : Regs T A), l.foldl (fun R _ => R) R = R := by
    intro l; induction l with
    | nil => intro R; rfl
    | cons x rest ih => intro R; exact ih R
  rw [this]

/-! ### Division by a constant -/

/-- Up to `c` pops of `a` onto `t`; if all `c` succeed, one tick onto `b`. Ends by recording in
`flag` whether `a` is nonempty. -/
def divChain (a t b : Fin T) : ℕ → Act T Q A U
  | 0 => .push (.rt b) (fun _ => tick) (peekR a)
  | c + 1 => .pop (.rt a) (fun v o => { v with sym := o })
      (.branch (fun v => v.sym.isSome)
        (.push (.rt t) (fun v => v.sym.getD blank) (divChain a t b c)) (peekR a))

/-- `b` gains `|a| / c` ticks: each loop iteration moves up to `c` symbols of `a` onto `t` and
pushes a tick when it moved `c`; then `a` is restored from `t`. -/
def udiv (c : ℕ) (a b t : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR a)) (.seq (.loop (·.flag) (.act (divChain a t b c))) (moveR t a id))

lemma divChain_run {a t b : Fin T} (hat : a ≠ t) (hab : a ≠ b) (htb : t ≠ b) :
    ∀ (c : ℕ) (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A), S.R a = l →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        (c ≤ l.length → v'.flag = (l.drop c).head?.isSome ∧
          (divChain a t b c).run (mk v S) = mk v' { S with
            R := Function.update (Function.update (Function.update S.R a (l.drop c)) t
              ((l.take c).reverse ++ S.R t)) b (tick :: S.R b) }) ∧
        (l.length < c → v'.flag = false ∧
          (divChain a t b c).run (mk v S) = mk v' { S with
            R := Function.update (Function.update S.R a []) t (l.reverse ++ S.R t) })
  | 0, l, v, S, hS => by
      refine ⟨{ v with flag := l.head?.isSome }, rfl, fun _ => ⟨rfl, ?_⟩,
        fun h => absurd h (Nat.not_lt_zero _)⟩
      simp only [divChain, Action.run, peekR, mk_var, mk_stk, update_rt, store_mk, get_rt,
        Function.update_of_ne hab, hS, List.drop_zero, List.take_zero, List.reverse_nil,
        List.nil_append]
      congr 3
      rw [← hS, Function.update_eq_self, Function.update_eq_self]
  | c + 1, [], v, S, hS => by
      refine ⟨{ v with sym := none, flag := false }, rfl, fun h => absurd h (by simp),
        fun _ => ⟨rfl, ?_⟩⟩
      simp [divChain, Action.run, peekR, update_rt, hS]
      congr 2
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all
  | c + 1, x :: rest, v, S, hS => by
      obtain ⟨v', hu, hfull, hpart⟩ := divChain_run hat hab htb c rest { v with sym := some x }
        { S with R := Function.update (Function.update S.R a rest) t (x :: S.R t) }
        (by simp [Function.update_of_ne hat])
      have hrun : (divChain a t b (c + 1)).run (mk v S) = (divChain a t b c).run
          (mk { v with sym := some x }
            { S with R := Function.update (Function.update S.R a rest) t (x :: S.R t) }) := by
        simp [divChain, Action.run, hS, update_rt, Function.update_of_ne hat.symm]
      refine ⟨v', hu, fun h => ?_, fun h => ?_⟩
      · obtain ⟨hf, he⟩ := hfull (by simpa using h)
        refine ⟨by simpa using hf, ?_⟩
        rw [hrun, he]
        congr 2
        funext k
        dsimp only
        simp only [Function.update_apply, List.drop_succ_cons, List.take_succ_cons,
          List.reverse_cons, List.append_assoc, List.singleton_append]
        split_ifs <;> simp_all
      · obtain ⟨hf, he⟩ := hpart (by simpa using h)
        refine ⟨hf, ?_⟩
        rw [hrun, he]
        congr 2
        funext k
        dsimp only
        simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
          List.singleton_append]
        split_ifs <;> simp_all

lemma udiv_nil {a t b : Fin T} {c : ℕ} (v : HS T Q A U) (S : Stacks T A) (hS : S.R a = [])
    (hfl : v.flag = false) :
    Exec body (.loop (·.flag) (.act (divChain a t b c))) (mk v S) 1
      (mk v { S with
        R := Function.update (Function.update (Function.update S.R a []) t
          (([] : List (Fin (A + 4))).reverse ++ S.R t)) b
          (List.replicate (([] : List (Fin (A + 4))).length / c) tick ++ S.R b) }) := by
  have : ({ S with
      R := Function.update (Function.update (Function.update S.R a []) t
        (([] : List (Fin (A + 4))).reverse ++ S.R t)) b
        (List.replicate (([] : List (Fin (A + 4))).length / c) tick ++ S.R b) } : Stacks T A) =
      S := by
    simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_div,
      List.replicate_zero]
    rw [← hS, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
  rw [this]
  exact .loop_false (by simpa using hfl)

theorem udiv_loop {a t b : Fin T} (hat : a ≠ t) (hab : a ≠ b) (htb : t ≠ b) {c : ℕ}
    (hc : 1 ≤ c) :
    ∀ (N : ℕ) (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A), l.length ≤ N →
      S.R a = l → v.flag = l.head?.isSome →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 2 * l.length + 1 ∧
        Exec body (.loop (·.flag) (.act (divChain a t b c))) (mk v S) m
          (mk v' { S with
            R := Function.update (Function.update (Function.update S.R a []) t
              (l.reverse ++ S.R t)) b (List.replicate (l.length / c) tick ++ S.R b) }) := by
  intro N
  induction N with
  | zero =>
      intro l v S hl hS hfl
      obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact ⟨v, 1, rfl, by simp, udiv_nil body v S hS (by simpa using hfl)⟩
  | succ N ih =>
      intro l v S hl hS hfl
      by_cases hnil : l = []
      · subst hnil
        exact ⟨v, 1, rfl, by simp, udiv_nil body v S hS (by simpa using hfl)⟩
      have hpos : 0 < l.length := List.length_pos_iff.2 hnil
      have hflt : v.flag = true := by
        rw [hfl]; cases l with
        | nil => exact absurd rfl hnil
        | cons _ _ => rfl
      obtain ⟨v₁, hu₁, hfull, hpart⟩ := divChain_run hat hab htb c l v S hS
      by_cases hcl : c ≤ l.length
      · obtain ⟨hf₁, he₁⟩ := hfull hcl
        obtain ⟨v', m, hu, hm, he⟩ := ih (l.drop c) v₁
          { S with
            R := Function.update (Function.update (Function.update S.R a (l.drop c)) t
              ((l.take c).reverse ++ S.R t)) b (tick :: S.R b) }
          (by rw [List.length_drop]; omega)
          (by simp [Function.update_of_ne hat, Function.update_of_ne hab]) hf₁
        refine ⟨v', 1 + m + 1, by rw [hu, hu₁], ?_, ?_⟩
        · rw [List.length_drop] at hm; omega
        · refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hflt
            (he₁ ▸ Exec.act (body := body) (divChain a t b c) (mk v S)) he) rfl ?_
          have hdiv : l.length / c = (l.length - c) / c + 1 :=
            Nat.div_eq_sub_div (by omega) hcl
          have hrev : l.reverse = (l.drop c).reverse ++ (l.take c).reverse := by
            conv_lhs => rw [← List.take_append_drop c l]
            rw [List.reverse_append]
          rw [hdiv, List.replicate_succ', List.append_assoc, List.singleton_append, hrev,
            List.length_drop]
          congr 2
          funext k
          dsimp only
          simp only [Function.update_apply]
          split_ifs <;> simp_all
      · obtain ⟨hf₁, he₁⟩ := hpart (by omega)
        refine ⟨v₁, 1 + 1 + 1, hu₁, by omega, ?_⟩
        refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hflt
          (he₁ ▸ Exec.act (body := body) (divChain a t b c) (mk v S))
          (.loop_false (by simpa using hf₁))) rfl ?_
        rw [Nat.div_eq_of_lt (by omega), List.replicate_zero, List.nil_append]
        congr 2
        funext k
        simp only [Function.update_apply]
        split_ifs <;> simp_all

/-- `udiv` for `c ≥ 1`: `b` gains `|a| / c` ticks in at most `4 |a| + 4` steps. -/
theorem udiv_exec {c : ℕ} (hc : 1 ≤ c) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (v : HS T Q A U) (S : Stacks T A) (ht : S.R t = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 4 * (S.R a).length + 4 ∧
      Exec body (udiv c a b t) (mk v S) m
        (mk v' { S with
          R := Function.update S.R b (List.replicate ((S.R a).length / c) tick ++ S.R b) }) := by
  obtain ⟨v₁, m, hu₁, hm, he₁⟩ := udiv_loop body hat hab hbt.symm hc (S.R a).length (S.R a)
    { v with flag := (S.R a).head?.isSome } S le_rfl rfl rfl
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body t a hat.symm id v₁
    { S with
      R := Function.update (Function.update (Function.update S.R a []) t
        ((S.R a).reverse ++ S.R t)) b (List.replicate ((S.R a).length / c) tick ++ S.R b) }
  refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.cast (Exec.seq (peekR_run a v S ▸
    Exec.act (body := body) (peekR a) (mk v S)) (Exec.seq he₁ he₂)) rfl ?_⟩
  · simp [Function.update_of_ne hbt.symm, ht]; omega
  · congr 2
    funext k
    simp only [movedR, Function.update_apply, List.map_id, ht, List.append_nil,
      ]
    split_ifs <;> simp_all

/-! ### Scanning with a program body -/

/-- Pop register `a` into `sym` and push the symbol onto `t`. -/
def popPush (a t : Fin T) : Act T Q A U :=
  .pop (.rt a) (fun v o => { v with sym := o }) (.push (.rt t) (fun v => v.sym.getD blank) .done)

/-- Run the program `p` once per symbol of register `a`, keeping the symbols on `t` and moving
them back onto `a` at the end. -/
def scanP (a t : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR a))
    (.seq (.loop (·.flag) (.seq (.act (popPush a t)) (.seq p (.act (peekR a))))) (moveR t a id))

/-- Iteration `j < N` of `p` takes registers equal to `Ψ j` off `a` and `t` to registers equal
to `Ψ (j + 1)` off `a` and `t`, in at most `c j` steps, leaving `a`, `t` and `user` alone. -/
def IterSpec (p : Pr P T Q A U) (a t : Fin T) (Ψ : ℕ → Regs T A) (c : ℕ → ℕ) (N : ℕ) : Prop :=
  ∀ j < N, ∀ (v : HS T Q A U) (S : Stacks T A), (∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) →
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧ m ≤ c j ∧
      Exec body p (mk v S) m (mk v' { S with R := R' }) ∧ R' a = S.R a ∧ R' t = S.R t ∧
      ∀ k, k ≠ a → k ≠ t → R' k = Ψ (j + 1) k

theorem scanP_loop {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U} {Ψ : ℕ → Regs T A}
    {c : ℕ → ℕ} {N : ℕ} (hp : IterSpec body p a t Ψ c N) :
    ∀ (l : List (Fin (A + 4))) (j : ℕ) (v : HS T Q A U) (S : Stacks T A), S.R a = l →
      j + l.length ≤ N → (∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) → v.flag = l.head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧
        m ≤ ∑ i ∈ Finset.range l.length, (c (j + i) + 3) + 1 ∧
        Exec body (.loop (·.flag) (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))))
          (mk v S) m (mk v' { S with R := R' }) ∧
        R' a = [] ∧ R' t = l.reverse ++ S.R t ∧
        ∀ k, k ≠ a → k ≠ t → R' k = Ψ (j + l.length) k
  | [], j, v, S, hS, _, hΨ, hfl =>
      ⟨v, S.R, 1, rfl, by simp, .loop_false (by simpa using hfl), hS, by simp,
        by simpa using hΨ⟩
  | x :: rest, j, v, S, hS, hN, hΨ, hfl => by
      have hrun : (popPush a t : Act T Q A U).run (mk v S) = mk { v with sym := some x }
          { S with R := Function.update (Function.update S.R a rest) t (x :: S.R t) } := by
        simp [popPush, Action.run, hS, update_rt, Function.update_of_ne hat.symm]
      obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, ha₁, ht₁, hΨ₁⟩ := hp j (by simp at hN; omega)
        { v with sym := some x }
        { S with R := Function.update (Function.update S.R a rest) t (x :: S.R t) }
        (fun k hka hkt => by
          simpa [Function.update_of_ne hka, Function.update_of_ne hkt] using hΨ k hka hkt)
      have ha₁' : R₁ a = rest := by rw [ha₁]; simp [Function.update_of_ne hat]
      have he₂ := Exec.act (body := body) (peekR a) (mk v₁ { S with R := R₁ })
      rw [peekR_run] at he₂
      obtain ⟨v', R', m', hu', hm', he', ha', ht', hΨ'⟩ := scanP_loop hat hp rest (j + 1)
        { v₁ with flag := (R₁ a).head?.isSome } { S with R := R₁ } ha₁' (by simp at hN; omega) hΨ₁
        (by rw [ha₁'])
      refine ⟨v', R', 1 + (m₁ + 1) + m' + 1, by rw [hu', ← hu₁], ?_,
        Exec.loop_true (by simpa using hfl) (Exec.seq (hrun ▸ Exec.act (body := body) _ (mk v S))
          (Exec.seq he₁ he₂)) he', ha', ?_, ?_⟩
      · rw [List.length_cons, Finset.sum_range_succ']
        have : ∑ i ∈ Finset.range rest.length, (c (j + 1 + i) + 3) =
            ∑ i ∈ Finset.range rest.length, (c (j + (i + 1)) + 3) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Nat.add_assoc, Nat.add_comm 1 i]
        rw [← this]
        simp only [Nat.add_zero]
        omega
      · rw [ht']; dsimp only; rw [ht₁]; simp
      · intro k hka hkt
        rw [hΨ' k hka hkt, List.length_cons, Nat.add_assoc, Nat.add_comm 1]

/-- `scanP`: registers off `a` and `t` go from `Ψ j` to `Ψ (j + |a|)`; `t` is emptied and `a`
holds `t` reversed on top of its old contents. -/
theorem scanP_exec {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U} {Ψ : ℕ → Regs T A}
    {c : ℕ → ℕ} {N : ℕ} (hp : IterSpec body p a t Ψ c N) (j : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hN : j + (S.R a).length ≤ N) (hΨ : ∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) :
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧
      m ≤ ∑ i ∈ Finset.range (S.R a).length, (c (j + i) + 3) + 2 * (S.R a).length +
        2 * (S.R t).length + 4 ∧
      Exec body (scanP a t p) (mk v S) m (mk v' { S with R := R' }) ∧
      R' a = (S.R t).reverse ++ S.R a ∧ R' t = [] ∧
      ∀ k, k ≠ a → k ≠ t → R' k = Ψ (j + (S.R a).length) k := by
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, ha₁, ht₁, hΨ₁⟩ := scanP_loop body hat hp (S.R a) j
    { v with flag := (S.R a).head?.isSome } S rfl hN hΨ rfl
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body t a hat.symm id v₁ { S with R := R₁ }
  refine ⟨v₂, movedR R₁ t a id (R₁ t), _, by rw [hu₂, hu₁],
    ?_, Exec.seq (peekR_run a v S ▸ Exec.act (body := body) (peekR a) (mk v S))
      (Exec.seq he₁ he₂), ?_, ?_, ?_⟩
  · dsimp only; rw [ht₁]; simp; omega
  · simp [movedR, ht₁, ha₁]
  · simp [movedR, Function.update_of_ne hat.symm]
  · intro k hka hkt
    simp [movedR, Function.update_of_ne hka, Function.update_of_ne hkt, hΨ₁ k hka hkt]

/-! ### Powers of two -/

lemma flatMap_replicate_one {α : Type} (l : List α) : l.flatMap (List.replicate 1) = l := by
  induction l with
  | nil => rfl
  | cons x rest ih => simp [ih]

lemma flatMap_replicate_of_replicate {α : Type} (n m : ℕ) (x : α) :
    (List.replicate m x).flatMap (List.replicate n) = List.replicate (m * n) x := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ, List.flatMap_cons, ih, List.replicate_append_replicate]
      congr 1; ring

lemma flatMap_replicate_replicate {α : Type} (l : List α) (m n : ℕ) :
    (l.flatMap (List.replicate m)).flatMap (List.replicate n) =
      l.flatMap (List.replicate (m * n)) := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      rw [List.flatMap_cons, List.flatMap_append, ih, List.flatMap_cons,
        flatMap_replicate_of_replicate]

lemma length_flatMap_replicate {α : Type} (l : List α) (n : ℕ) :
    (l.flatMap (List.replicate n)).length = n * l.length := by
  induction l with
  | nil => rfl
  | cons x rest ih => simp [ih]; ring

/-- Double register `b` in place: move it onto the empty `t₂`, then pop `t₂` pushing each symbol
twice onto `b`. -/
def udbl (b t₂ : Fin T) : Pr P T Q A U :=
  .seq (moveR b t₂ id) (drainR t₂ (pushN b (fun v => v.sym.getD blank) 2))

/-- `udbl`: `b` becomes `b.flatMap (replicate 2)` in `4 |b| + 4` steps. -/
theorem udbl_exec {b t₂ : Fin T} (hbt : b ≠ t₂) (v : HS T Q A U) (S : Stacks T A)
    (ht : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (udbl b t₂) (mk v S) (4 * (S.R b).length + 4)
        (mk v' { S with R := Function.update S.R b ((S.R b).flatMap (List.replicate 2)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body b t₂ hbt id v S
  obtain ⟨v₂, hu₂, he₂⟩ := drainR_exec body t₂
    (regFx_pushN b 2 (fun v => v.sym.getD blank) id (fun v x hx => by simp [hx]))
    (frame_pushFx hbt.symm 2 id) v₁ { S with R := movedR S.R b t₂ id (S.R b) }
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
  · simp [movedR, ht]; ring
  · congr 2
    rw [foldl_pushFx]
    funext k
    simp only [movedR, Function.update_apply, List.map_id, ht, List.append_nil, id,
      ]
    split_ifs <;> simp_all [List.replicate]

/-- Make `b` hold `2 ^ |a|` copies of each of its symbols: double `b` once per symbol of `a`
(kept on the empty `t₁`), through the empty `t₂`. -/
def upow2 (a b t₁ t₂ : Fin T) : Pr P T Q A U := scanP a t₁ (udbl b t₂)

lemma sum_pow_two_le (x : ℕ) : ∀ e : ℕ,
    ∑ i ∈ Finset.range e, (4 * (2 ^ i * x) + 4 + 3) + 4 * x ≤ 4 * (2 ^ e * x) + 7 * e
  | 0 => by simp
  | e + 1 => by
      have ih := sum_pow_two_le x e
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [Nat.zero_le (2 ^ e * x)]

/-- `upow2`: with `|a| = e` and `|b| = x`, `b` ends holding `2 ^ e * x` symbols, namely each
symbol of `b` repeated `2 ^ e` times, in at most `4 · 2 ^ e x + 9 e + 4` steps. -/
theorem upow2_exec {a b t₁ t₂ : Fin T} (hreg : [a, b, t₁, t₂].Nodup) (v : HS T Q A U)
    (S : Stacks T A) (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 4 * (2 ^ (S.R a).length * (S.R b).length) + 9 * (S.R a).length + 4 ∧
      Exec body (upow2 a b t₁ t₂) (mk v S) m
        (mk v' { S with
          R := Function.update S.R b ((S.R b).flatMap (List.replicate (2 ^ (S.R a).length))) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨hab, hat₁, hat₂⟩, ⟨hbt₁, hbt₂⟩, ht₁t₂⟩ := hreg
  set x := (S.R b).length with hx
  let Ψ : ℕ → Regs T A := fun i => Function.update S.R b ((S.R b).flatMap (List.replicate (2 ^ i)))
  have hp : IterSpec body (udbl b t₂) a t₁ Ψ (fun i => 4 * (2 ^ i * x) + 4) (S.R a).length := by
    intro i _ v S' hS'
    have hb' : S'.R b = (S.R b).flatMap (List.replicate (2 ^ i)) := by
      rw [hS' b hab.symm hbt₁]; simp [Ψ]
    have ht₂' : S'.R t₂ = [] := by
      rw [hS' t₂ hat₂.symm ht₁t₂.symm]; simp [Ψ, Function.update_of_ne hbt₂.symm, ht₂]
    obtain ⟨v', hu, he⟩ := udbl_exec body hbt₂ v S' ht₂'
    refine ⟨v', _, _, hu, le_of_eq ?_, he, ?_, ?_, ?_⟩
    · rw [hb', length_flatMap_replicate]
    · simp [Function.update_of_ne hab]
    · simp [Function.update_of_ne hbt₁.symm]
    · intro k hka hkt
      by_cases hk : k = b
      · subst hk
        simp [Ψ, hb', flatMap_replicate_replicate, pow_succ]
      · simp [Ψ, Function.update_of_ne hk, hS' k hka hkt]
  obtain ⟨v', R', m, hu, hm, he, ha', ht', hΨ'⟩ := scanP_exec body hat₁ hp 0 v S (by simp)
    (fun k _ _ => by simp [Ψ, flatMap_replicate_one])
  refine ⟨v', m, hu, ?_, Exec.cast he rfl ?_⟩
  · have := sum_pow_two_le x (S.R a).length
    simp only [Nat.zero_add, ht₁, List.length_nil, Nat.mul_zero, Nat.add_zero] at hm
    omega
  · congr 2
    funext k
    by_cases hka : k = a
    · subst hka; simp [ha', ht₁, Function.update_of_ne hab]
    · by_cases hkt : k = t₁
      · subst hkt; simp [ht', ht₁, Function.update_of_ne hbt₁.symm]
      · rw [hΨ' k hka hkt]; simp [Ψ]

/-! ### The exponent recursion -/

/-- The exponents `E₀ = u`, `E_{i+1} = G + F E_i`. -/
def expSeq (G F u : ℕ) : ℕ → ℕ
  | 0 => u
  | i + 1 => G + F * expSeq G F u i

theorem expSeq_eq_rec (G F u j : ℕ) : expSeq G F u j = Nat.rec u (fun _ E => G + F * E) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [expSeq, ih]

/-- Any sequence with `e 0 = u` and `e (i + 1) = G + F e i` is `expSeq G F u`. -/
theorem eq_expSeq {G F u : ℕ} {e : ℕ → ℕ} (h0 : e 0 = u) (hs : ∀ i, e (i + 1) = G + F * e i) :
    ∀ j, e j = expSeq G F u j
  | 0 => h0
  | j + 1 => by rw [hs, eq_expSeq h0 hs j, expSeq]

/-- One level of the recursion on register `e`: move `e` onto the empty `t₂`, push `G` ticks
onto `e`, add `F` ticks per symbol of `t₂` (`umul` through the empty `t₃`), and empty `t₂`. -/
def expStep (G F : ℕ) (e t₂ t₃ : Fin T) : Pr P T Q A U :=
  .seq (moveR e t₂ id) (.seq (.act (pushN e (fun _ => tick) G .done))
    (.seq (umul F t₂ e t₃) (uclear t₂)))

/-- `expStep`: `e` ends holding `G + F |e|` ticks, in `8 |e| + 9` steps. -/
theorem expStep_exec (G F : ℕ) {e t₂ t₃ : Fin T} (hreg : [e, t₂, t₃].Nodup) (v : HS T Q A U)
    (S : Stacks T A) (ht₂ : S.R t₂ = []) (ht₃ : S.R t₃ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (expStep G F e t₂ t₃) (mk v S) (8 * (S.R e).length + 9)
        (mk v' { S with
          R := Function.update S.R e (List.replicate (G + F * (S.R e).length) tick) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨he2, he3⟩, h23⟩ := hreg
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body e t₂ he2 id v S
  set S₁ : Stacks T A := { S with R := movedR S.R e t₂ id (S.R e) } with hS₁
  have he₂ := Exec.act (body := body) (pushN e (fun _ => tick) G .done) (mk v₁ S₁)
  rw [pushN_run, run_done] at he₂
  set S₂ : Stacks T A :=
    { S₁ with R := Function.update S₁.R e (List.replicate G tick ++ S₁.R e) } with hS₂
  obtain ⟨v₃, hu₃, he₃⟩ := umul_exec body F he2.symm h23 he3 v₁ S₂
    (by simp [hS₂, hS₁, movedR, Function.update_of_ne he3.symm, Function.update_of_ne h23.symm,
      ht₃])
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body t₂ v₃ { S₂ with
    R := Function.update S₂.R e (List.replicate (F * (S₂.R t₂).length) tick ++ S₂.R e) }
  refine ⟨v₄, by rw [hu₄, hu₃, hu₁], Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)))
    ?_ ?_⟩
  · simp [hS₂, hS₁, movedR, Function.update_of_ne he2.symm, ht₂]; ring
  · congr 2
    funext k
    simp only [hS₂, hS₁, movedR, Function.update_apply, List.map_id, ht₂, List.append_nil,
      ]
    split_ifs <;> simp_all [List.replicate_append_replicate, Nat.add_comm]

/-- The exponent program: copy `|uR|` ticks onto the empty `eR` (through `t₁`), then run
`expStep G F` once per symbol of `jR` (kept on `t₁`), with spares `t₂`, `t₃`. -/
def expProg (G F : ℕ) (uR jR eR t₁ t₂ t₃ : Fin T) : Pr P T Q A U :=
  .seq (ucopy uR eR t₁) (scanP jR t₁ (expStep G F eR t₂ t₃))

/-- `expProg`: `eR` ends holding `expSeq G F |uR| |jR|` ticks; every other register ends as it
started. -/
theorem expProg_exec (G F : ℕ) {uR jR eR t₁ t₂ t₃ : Fin T} (hreg : [uR, jR, eR, t₁, t₂, t₃].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (he : S.R eR = []) (ht₁ : S.R t₁ = [])
    (ht₂ : S.R t₂ = []) (ht₃ : S.R t₃ = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 4 * (S.R uR).length + 2 * (S.R jR).length + 8 +
        ∑ i ∈ Finset.range (S.R jR).length, (8 * expSeq G F (S.R uR).length i + 12) ∧
      Exec body (expProg G F uR jR eR t₁ t₂ t₃) (mk v S) m
        (mk v' { S with
          R := Function.update S.R eR
            (List.replicate (expSeq G F (S.R uR).length (S.R jR).length) tick) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨hu1, hu2, hu3, hu4, hu5⟩, ⟨hj1, hj2, hj3, hj4⟩, ⟨he1, he2, he3⟩, ⟨h12, h13⟩, h23⟩ := hreg
  set u := (S.R uR).length with hu
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body hu2 hu3 he1 v S ht₁
  let Ψ : ℕ → Regs T A := fun i => Function.update S.R eR (List.replicate (expSeq G F u i) tick)
  have hp : IterSpec body (expStep G F eR t₂ t₃) jR t₁ Ψ (fun i => 8 * expSeq G F u i + 9)
      (S.R jR).length := by
    intro i _ w S' hS'
    have hreg' : [eR, t₂, t₃].Nodup := by simp [he2, he3, h23]
    obtain ⟨w', hw, hx⟩ := expStep_exec body G F hreg' w S'
      (by rw [hS' t₂ hj3.symm h12.symm]; simp [Ψ, Function.update_of_ne he2.symm, ht₂])
      (by rw [hS' t₃ hj4.symm h13.symm]; simp [Ψ, Function.update_of_ne he3.symm, ht₃])
    have hE : S'.R eR = List.replicate (expSeq G F u i) tick := by
      rw [hS' eR hj1.symm he1]; simp [Ψ]
    refine ⟨w', _, _, hw, le_of_eq ?_, hx, ?_, ?_, ?_⟩
    · rw [hE, List.length_replicate]
    · simp [Function.update_of_ne hj1]
    · simp [Function.update_of_ne he1.symm]
    · intro k hka hkt
      by_cases hk : k = eR
      · subst hk; simp [Ψ, hE, expSeq]
      · simp [Ψ, Function.update_of_ne hk, hS' k hka hkt]
  obtain ⟨v₂, R', m, hu₂, hm, he₂, ha', ht', hΨ'⟩ := scanP_exec body hj2 hp 0 v₁
    { S with R := Function.update S.R eR (List.replicate u tick ++ S.R eR) }
    (by simp [Function.update_of_ne hj1]) (fun k _ _ => by simp [Ψ, he, expSeq])
  refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ he₂) rfl ?_⟩
  · simp only [Function.update_of_ne hj1, Function.update_of_ne he1.symm, ht₁, List.length_nil,
      Nat.mul_zero, Nat.add_zero, Nat.zero_add] at hm
    have : ∑ i ∈ Finset.range (S.R jR).length, (8 * expSeq G F u i + 9 + 3) =
        ∑ i ∈ Finset.range (S.R jR).length, (8 * expSeq G F u i + 12) := rfl
    omega
  · congr 2
    funext k
    by_cases hka : k = jR
    · subst hka; simp [ha', Function.update_of_ne hj1, Function.update_of_ne he1.symm, ht₁]
    · by_cases hkt : k = t₁
      · subst hkt; simp [ht', Function.update_of_ne he1.symm, ht₁]
      · rw [hΨ' k hka hkt]; simp [Ψ, Function.update_of_ne hj1]

/-! ### Mask values -/

/-- A sum of distinct powers of two has bit `t` set exactly when `t ∈ s`. -/
lemma testBit_sum_two_pow (s : Finset ℕ) (t : ℕ) :
    (∑ i ∈ s, 2 ^ i).testBit t = true ↔ t ∈ s := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]

/-- The strided mask `∑_{i < M k, pred (i / k)} 2 ^ (o + K i)`. -/
def maskVal (o K k M : ℕ) (pred : ℕ → Bool) : ℕ :=
  ∑ i ∈ (Finset.range (M * k)).filter (fun i => pred (i / k) = true), 2 ^ (o + K * i)

theorem testBit_maskVal {o K k M : ℕ} (hK : 1 ≤ K) (pred : ℕ → Bool) (t : ℕ) :
    (maskVal o K k M pred).testBit t = true ↔
      ∃ i < M * k, pred (i / k) = true ∧ t = o + K * i := by
  have hinj : Set.InjOn (fun i => o + K * i)
      ↑((Finset.range (M * k)).filter (fun i => pred (i / k) = true)) := by
    intro i _ j _ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_left (by omega) (by omega : K * i = K * j)
  rw [maskVal, ← Finset.sum_image (f := fun q => 2 ^ q) hinj, testBit_sum_two_pow]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨i, ⟨hi, hp⟩, rfl⟩
    exact ⟨i, hi, hp, rfl⟩
  · rintro ⟨i, hi, hp, rfl⟩
    exact ⟨i, ⟨hi, hp⟩, rfl⟩

lemma maskVal_testBit_item {o K k M : ℕ} (hK : 1 ≤ K) (pred : ℕ → Bool) {i : ℕ}
    (hi : i < M * k) : (maskVal o K k M pred).testBit (o + K * i) = pred (i / k) := by
  rw [Bool.eq_iff_iff, testBit_maskVal hK]
  constructor
  · rintro ⟨i', _, hp, h⟩
    obtain rfl : i' = i := Nat.eq_of_mul_eq_mul_left (by omega) (by omega : K * i' = K * i)
    exact hp
  · intro hp
    exact ⟨i, hi, hp, rfl⟩

lemma maskVal_testBit_false {o K k M q : ℕ} (hK : 1 ≤ K) (pred : ℕ → Bool)
    (hq : ∀ i < M * k, q ≠ o + K * i) : (maskVal o K k M pred).testBit q = false := by
  rw [← Bool.not_eq_true, testBit_maskVal hK]
  rintro ⟨i, hi, _, rfl⟩
  exact hq i hi rfl

lemma ne_stride {o K i i' s : ℕ} (hs : 0 < s) (hsK : s < K) : o + K * i + s ≠ o + K * i' := by
  intro h
  rcases Nat.lt_or_ge i' (i + 1) with h' | h'
  · have : K * i' ≤ K * i := Nat.mul_le_mul_left K (by omega)
    omega
  · have : K * (i + 1) ≤ K * i' := Nat.mul_le_mul_left K h'
    rw [Nat.mul_succ] at this
    omega

/-! ### Emitting mask bits -/

/-- Emit one mask position: pop the position counter `cnt`; if it held a symbol, push the bit
`b` onto the accumulator `w`. -/
def emit (cnt w : Fin T) (b : Bool) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt cnt) (fun v o => { v with flag := o.isSome })
    (.branch (·.flag) (.push (.rt w) (fun _ => bitSymbol b) k) k)

/-- The effect of `emit`. -/
def emitFx (cnt w : Fin T) (b : Bool) (R : Regs T A) : Regs T A :=
  if R cnt = [] then R
  else Function.update (Function.update R cnt (R cnt).tail) w (bitSymbol b :: R w)

lemma emit_run {cnt w : Fin T} (hcw : cnt ≠ w) (b : Bool) (k : Act T Q A U) (v : HS T Q A U)
    (S : Stacks T A) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      (emit cnt w b k).run (mk v S) = k.run (mk v' { S with R := emitFx cnt w b S.R }) := by
  by_cases h : S.R cnt = []
  · refine ⟨{ v with flag := false }, rfl, ?_⟩
    have h' : Function.update S.R cnt [] = S.R := by rw [← h, Function.update_eq_self]
    simp [emit, Action.run, h, update_rt, emitFx, h']
  · obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil h
    refine ⟨{ v with flag := true }, rfl, ?_⟩
    simp [emit, Action.run, hy, update_rt, emitFx, Function.update_of_ne hcw.symm]

lemma regFx_emit {cnt w : Fin T} (hcw : cnt ≠ w) (b : Bool) :
    RegFx (emit (T := T) (Q := Q) (A := A) (U := U) cnt w b) (fun _ R => emitFx cnt w b R) :=
  fun _ k v S _ => emit_run hcw b k v S

lemma frame_emitFx {a cnt w : Fin T} (hac : a ≠ cnt) (haw : a ≠ w) (b : Bool) :
    Frame a (fun _ R => emitFx (A := A) cnt w b R) := by
  intro x R l
  simp only [emitFx, Function.update_of_ne hac.symm, Function.update_of_ne haw.symm]
  split_ifs
  · rfl
  · rw [Function.update_comm hac, Function.update_comm haw]

/-- Registers of a mask build after `p` positions: the counter `cnt` holds the `n - p`
positions left and the accumulator `w` the bits `0, …, min p n - 1` of `X`, the last on top. -/
def maskRegs (cnt w : Fin T) (n X : ℕ) (R : Regs T A) (p : ℕ) : Regs T A :=
  Function.update (Function.update R cnt (List.replicate (n - p) tick)) w
    (binSyms (min p n) X).reverse

section MaskRegs

variable {cnt w : Fin T} {n X : ℕ}

lemma maskRegs_cnt (hcw : cnt ≠ w) (R : Regs T A) (p : ℕ) :
    maskRegs cnt w n X R p cnt = List.replicate (n - p) tick := by
  simp [maskRegs, Function.update_of_ne hcw]

lemma maskRegs_w (R : Regs T A) (p : ℕ) :
    maskRegs cnt w n X R p w = (binSyms (min p n) X).reverse := by
  simp [maskRegs]

lemma maskRegs_of_ne {k : Fin T} (h1 : k ≠ cnt) (h2 : k ≠ w) (R : Regs T A) (p : ℕ) :
    maskRegs cnt w n X R p k = R k := by
  simp [maskRegs, Function.update_of_ne h1, Function.update_of_ne h2]

lemma maskRegs_maskRegs (R : Regs T A) (p q : ℕ) :
    maskRegs cnt w n X (maskRegs cnt w n X R p) q = maskRegs cnt w n X R q := by
  funext k
  simp only [maskRegs, Function.update_apply]
  split_ifs <;> simp_all

lemma maskRegs_self {R : Regs T A} {p : ℕ}
    (h1 : R cnt = List.replicate (n - p) tick) (h2 : R w = (binSyms (min p n) X).reverse) :
    maskRegs cnt w n X R p = R := by
  simp only [maskRegs]
  rw [← h1, Function.update_eq_self, ← h2, Function.update_eq_self]

end MaskRegs

lemma binSyms_succ' (L a : ℕ) :
    (binSyms (L + 1) a : List (Fin (A + 4))) = binSyms L a ++ [bitSymbol (a.testBit L)] := by
  rw [binSyms, List.ofFn_succ', List.concat_eq_append]
  rfl

lemma emitFx_maskRegs {cnt w : Fin T} (hcw : cnt ≠ w) {n X p : ℕ} {b : Bool}
    (hb : p < n → X.testBit p = b) (R : Regs T A) :
    emitFx cnt w b (maskRegs cnt w n X R p) = maskRegs cnt w n X R (p + 1) := by
  by_cases hp : p < n
  · have hc : maskRegs cnt w n X R p cnt = tick :: List.replicate (n - (p + 1)) tick := by
      rw [maskRegs_cnt hcw, show n - p = n - (p + 1) + 1 by omega, List.replicate_succ]
    simp only [emitFx, hc, reduceCtorEq, ↓reduceIte, List.tail_cons, maskRegs_w]
    funext k
    simp only [maskRegs, Function.update_apply]
    rw [show min (p + 1) n = p + 1 by omega, show min p n = p by omega, binSyms_succ', hb hp]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    split_ifs <;> simp_all
  · have hc : maskRegs cnt w n X R p cnt = [] := by
      rw [maskRegs_cnt hcw, show n - p = 0 by omega, List.replicate_zero]
    simp only [emitFx, hc, ↓reduceIte]
    simp only [maskRegs, show n - p = n - (p + 1) by omega, show min p n = min (p + 1) n by omega]

lemma foldl_emitFx {cnt w : Fin T} (hcw : cnt ≠ w) {n X : ℕ} {b : Bool} (R : Regs T A) :
    ∀ (l : List (Fin (A + 4))) (p : ℕ),
      (∀ q, p ≤ q → q < p + l.length → q < n → X.testBit q = b) →
      l.foldl (fun R _ => emitFx cnt w b R) (maskRegs cnt w n X R p) =
        maskRegs cnt w n X R (p + l.length)
  | [], p, _ => by simp
  | x :: rest, p, h => by
      simp only [List.foldl_cons]
      rw [emitFx_maskRegs hcw (fun hp => h p le_rfl (by simp) hp),
        foldl_emitFx hcw R rest (p + 1) (fun q h1 h2 h3 => h q (by omega) (by simp; omega) h3)]
      simp [Nat.add_assoc, Nat.add_comm 1]

/-- Emit one position per symbol of `a` (kept on `t`), all with bit `b`. -/
theorem scanEmit_exec {a t cnt w : Fin T} (hreg : [a, t, cnt, w].Nodup) {n X p : ℕ} (b : Bool)
    (R₀ : Regs T A) (v : HS T Q A U) (S : Stacks T A) (hS : S.R = maskRegs cnt w n X R₀ p)
    (ht : R₀ t = []) (hX : ∀ q, p ≤ q → q < p + (R₀ a).length → q < n → X.testBit q = b) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (scanR a t (emit cnt w b)) (mk v S) (4 * (R₀ a).length + 4)
        (mk v' { S with R := maskRegs cnt w n X R₀ (p + (R₀ a).length) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨hat, hac, haw⟩, ⟨htc, htw⟩, hcw⟩ := hreg
  have hSa : S.R a = R₀ a := by rw [hS, maskRegs_of_ne hac haw]
  obtain ⟨v', hu, he⟩ := scanR_exec' body hat (regFx_emit hcw b) (frame_emitFx hac haw b)
    (frame_emitFx htc htw b) v S (by rw [hS, maskRegs_of_ne htc htw, ht])
  refine ⟨v', hu, Exec.cast he (by rw [hSa]) ?_⟩
  rw [hSa]
  conv_lhs => rw [hS]
  rw [foldl_emitFx hcw R₀ (R₀ a) p hX]

/-! ### The strided mask -/

/-- One stride item: emit the bit `b`, then `K - 1` zeros, scanning the `K` symbols of `KR`
through the empty `t₂` after moving its top symbol to `t₂`. -/
def strideItem (KR cnt w t₂ : Fin T) (b : Bool) : Pr P T Q A U :=
  .seq (.act (emit cnt w b .done)) (.seq (.act (popPush KR t₂)) (scanR KR t₂ (emit cnt w false)))

theorem strideItem_exec {KR t₂ cnt w : Fin T} (hreg : [KR, t₂, cnt, w].Nodup) {n X p : ℕ}
    {b : Bool} (R₀ : Regs T A) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = maskRegs cnt w n X R₀ p) (hK : 1 ≤ (R₀ KR).length) (ht₂ : R₀ t₂ = [])
    (hb : p < n → X.testBit p = b)
    (hz : ∀ q, p < q → q < p + (R₀ KR).length → q < n → X.testBit q = false) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (strideItem KR cnt w t₂ b) (mk v S) (4 * (R₀ KR).length + 4)
        (mk v' { S with R := maskRegs cnt w n X R₀ (p + (R₀ KR).length) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hKt, hKc, hKw⟩, ⟨htc, htw⟩, hcw⟩ := hreg'
  obtain ⟨x, rest, hx⟩ := List.exists_cons_of_length_pos hK
  obtain ⟨v₁, hu₁, hr₁⟩ := emit_run hcw b (.done) v S
  have he₁ := Exec.act (body := body) (emit cnt w b .done) (mk v S)
  rw [hr₁, run_done, hS, emitFx_maskRegs hcw hb] at he₁
  set M₁ := maskRegs cnt w n X R₀ (p + 1) with hM₁
  have hrun : (popPush KR t₂ : Act T Q A U).run (mk v₁ { S with R := M₁ }) =
      mk { v₁ with sym := some x }
        { S with R := Function.update (Function.update M₁ KR rest) t₂ [x] } := by
    have h1 : M₁ KR = x :: rest := by rw [hM₁, maskRegs_of_ne hKc hKw, hx]
    have h2 : M₁ t₂ = [] := by rw [hM₁, maskRegs_of_ne htc htw, ht₂]
    simp [popPush, Action.run, h1, h2, update_rt, Function.update_of_ne hKt.symm]
  have he₂ := Exec.act (body := body) (popPush KR t₂) (mk v₁ { S with R := M₁ })
  rw [hrun] at he₂
  obtain ⟨v₃, hu₃, he₃⟩ := scanR_exec body hKt (regFx_emit hcw false) (frame_emitFx hKc hKw false)
    (frame_emitFx htc htw false) { v₁ with sym := some x }
    { S with R := Function.update (Function.update M₁ KR rest) t₂ [x] }
  refine ⟨v₃, by rw [hu₃]; simpa using hu₁, Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) ?_ ?_⟩
  · simp [Function.update_of_ne hKt, hx]; ring
  · congr 2
    dsimp only
    rw [Function.update_of_ne hKt, Function.update_self, Function.update_self,
      (frame_emitFx htc htw false).foldl, (frame_emitFx hKc hKw false).foldl, hM₁,
      foldl_emitFx hcw R₀ rest (p + 1) (fun q h1 h2 h3 => hz q (by omega) (by rw [hx]; simp; omega) h3)]
    funext k
    by_cases hk1 : k = KR
    · subst hk1; simp [maskRegs_of_ne hKc hKw, hx]
    · by_cases hk2 : k = t₂
      · subst hk2; simp [hk1, maskRegs_of_ne htc htw, ht₂]
      · simp only [Function.update_of_ne hk1, Function.update_of_ne hk2]
        rw [hx]; simp [Nat.add_assoc, Nat.add_comm 1]

lemma maskRegs_congr {cnt w : Fin T} {n X : ℕ} {R R' : Regs T A} (p : ℕ) {k : Fin T}
    (h : k ≠ cnt → k ≠ w → R k = R' k) :
    maskRegs cnt w n X R p k = maskRegs cnt w n X R' p k := by
  simp only [maskRegs, Function.update_apply]
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact h h2 h1

lemma div_slot {M k j : ℕ} (hj : j < k) : (M * k + j) / k = M := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < k), Nat.div_eq_of_lt hj, zero_add]

/-- One slot: `|kR|` stride items with bit `b`, scanning `kR` through the empty `t₁`. -/
theorem strideSlot_exec {kR KR cnt w t₁ t₂ : Fin T} (hreg : [kR, KR, cnt, w, t₁, t₂].Nodup)
    {n X p₀ K : ℕ} (b : Bool) (R₀ : Regs T A) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = maskRegs cnt w n X R₀ p₀) (hKl : (R₀ KR).length = K) (hK : 1 ≤ K)
    (ht₁ : R₀ t₁ = []) (ht₂ : R₀ t₂ = [])
    (hb : ∀ j < (R₀ kR).length, p₀ + K * j < n → X.testBit (p₀ + K * j) = b)
    (hz : ∀ j < (R₀ kR).length, ∀ s, 0 < s → s < K → p₀ + K * j + s < n →
      X.testBit (p₀ + K * j + s) = false) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ (R₀ kR).length * (4 * K + 9) + 4 ∧
      Exec body (scanP kR t₁ (strideItem KR cnt w t₂ b)) (mk v S) m
        (mk v' { S with R := maskRegs cnt w n X R₀ (p₀ + K * (R₀ kR).length) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hkK, hkc, hkw, hk1, hk2⟩, ⟨hKc, hKw, hK1, hK2⟩, ⟨hcw, hc1, hc2⟩, ⟨hw1, hw2⟩, h12⟩ :=
    hreg'
  have hregI : [KR, t₂, cnt, w].Nodup := by
    simp [hKc, hKw, hK2, hc2.symm, hw2.symm, hcw]
  let Ψ : ℕ → Regs T A := fun j => maskRegs cnt w n X R₀ (p₀ + K * j)
  have hp : IterSpec body (strideItem KR cnt w t₂ b) kR t₁ Ψ (fun _ => 4 * K + 4)
      (R₀ kR).length := by
    intro j hj v' S' hS'
    have hc' : S'.R cnt = List.replicate (n - (p₀ + K * j)) tick :=
      (hS' cnt hkc.symm hc1).trans (maskRegs_cnt hcw _ _)
    have hw' : S'.R w = (binSyms (min (p₀ + K * j) n) X).reverse :=
      (hS' w hkw.symm hw1).trans (maskRegs_w _ _)
    have hKR : S'.R KR = R₀ KR := (hS' KR hkK.symm hK1).trans (maskRegs_of_ne hKc hKw _ _)
    have ht₂' : S'.R t₂ = [] :=
      (hS' t₂ hk2.symm h12.symm).trans ((maskRegs_of_ne hc2.symm hw2.symm _ _).trans ht₂)
    obtain ⟨v'', hu, he⟩ := strideItem_exec body hregI (S'.R) v' S' (maskRegs_self hc' hw').symm
      (by rw [hKR, hKl]; exact hK) ht₂' (hb j hj)
      (fun q h1 h2 h3 => by
        rw [hKR, hKl] at h2
        have := hz j hj (q - (p₀ + K * j)) (by omega) (by omega) (by omega)
        rwa [show p₀ + K * j + (q - (p₀ + K * j)) = q by omega] at this)
    have hpos : p₀ + K * j + (S'.R KR).length = p₀ + K * (j + 1) := by
      rw [hKR, hKl, Nat.mul_succ, Nat.add_assoc]
    rw [hpos] at he
    refine ⟨v'', _, _, hu, le_of_eq (by rw [hKR, hKl]), he, maskRegs_of_ne hkc hkw _ _,
      maskRegs_of_ne hc1.symm hw1.symm _ _, fun k hka hkt => ?_⟩
    exact maskRegs_congr _ fun h1 h2 => by
      rw [hS' k hka hkt]; exact maskRegs_of_ne h1 h2 _ _
  obtain ⟨v', R', m, hu, hm, he, ha', ht', hΨ'⟩ := scanP_exec body hk1 hp 0 v S
    (by rw [hS, maskRegs_of_ne hkc hkw]; simp)
    (fun k hka hkt => by rw [hS]; simp [Ψ])
  have hSk : S.R kR = R₀ kR := by rw [hS, maskRegs_of_ne hkc hkw]
  have hSt : S.R t₁ = [] := by rw [hS, maskRegs_of_ne hc1.symm hw1.symm, ht₁]
  refine ⟨v', m, hu, ?_, Exec.cast he rfl ?_⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, hSk, hSt,
      List.length_nil, Nat.mul_zero, Nat.add_zero] at hm
    nlinarith
  · congr 2
    funext k
    by_cases hka : k = kR
    · subst hka; rw [ha', hSt, maskRegs_of_ne hkc hkw, hSk]; rfl
    · by_cases hkt : k = t₁
      · subst hkt; rw [ht', maskRegs_of_ne hc1.symm hw1.symm, ht₁]
      · rw [hΨ' k hka hkt, hSk]; simp [Ψ]

/-- `M` slots; slot `m` runs `k` stride items with bit `pred m`, scanning `kR` through `t₁`. -/
def strideSlots (kR KR cnt w t₁ t₂ : Fin T) (pred : ℕ → Bool) : ℕ → Pr P T Q A U
  | 0 => .act .done
  | m + 1 => .seq (strideSlots kR KR cnt w t₁ t₂ pred m)
      (scanP kR t₁ (strideItem KR cnt w t₂ (pred m)))

theorem strideSlots_exec {kR KR cnt w t₁ t₂ : Fin T} (hreg : [kR, KR, cnt, w, t₁, t₂].Nodup)
    {n X o K k : ℕ} (pred : ℕ → Bool) (R₀ : Regs T A) (hKl : (R₀ KR).length = K) (hK : 1 ≤ K)
    (hkl : (R₀ kR).length = k) (ht₁ : R₀ t₁ = []) (ht₂ : R₀ t₂ = []) :
    ∀ (M : ℕ) (v : HS T Q A U) (S : Stacks T A), S.R = maskRegs cnt w n X R₀ o →
      (∀ i < M * k, o + K * i < n → X.testBit (o + K * i) = pred (i / k)) →
      (∀ i < M * k, ∀ s, 0 < s → s < K → o + K * i + s < n →
        X.testBit (o + K * i + s) = false) →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ M * (k * (4 * K + 9) + 4) + 1 ∧
        Exec body (strideSlots kR KR cnt w t₁ t₂ pred M) (mk v S) m
          (mk v' { S with R := maskRegs cnt w n X R₀ (o + K * (M * k)) })
  | 0, v, S, hS, _, _ => by
      refine ⟨v, 1, rfl, by simp, Exec.cast (Exec.act (body := body) .done (mk v S)) rfl ?_⟩
      have : maskRegs cnt w n X R₀ (o + K * (0 * k)) = S.R := by rw [hS]; simp
      rw [run_done, this]
  | M + 1, v, S, hS, hb, hz => by
      have hMk : ∀ j < k, M * k + j < (M + 1) * k := fun j hj => by rw [Nat.add_one_mul]; omega
      obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := strideSlots_exec hreg pred R₀ hKl hK hkl ht₁ ht₂ M v S hS
        (fun i hi => hb i (lt_of_lt_of_le hi (Nat.mul_le_mul_right k (by omega))))
        (fun i hi => hz i (lt_of_lt_of_le hi (Nat.mul_le_mul_right k (by omega))))
      obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := strideSlot_exec body hreg (pred M) R₀ v₁
        { S with R := maskRegs cnt w n X R₀ (o + K * (M * k)) } rfl hKl hK ht₁ ht₂
        (fun j hj hlt => by
          rw [hkl] at hj
          have := hb (M * k + j) (hMk j hj)
            (by rw [Nat.mul_add, ← Nat.add_assoc]; exact hlt)
          rwa [div_slot hj, Nat.mul_add, ← Nat.add_assoc] at this)
        (fun j hj s hs hsK hlt => by
          rw [hkl] at hj
          have := hz (M * k + j) (hMk j hj) s hs hsK
            (by rw [Nat.mul_add, ← Nat.add_assoc]; exact hlt)
          rwa [Nat.mul_add, ← Nat.add_assoc] at this)
      refine ⟨v₂, m₁ + m₂, by rw [hu₂, hu₁], ?_, Exec.cast (Exec.seq he₁ he₂) rfl ?_⟩
      · rw [hkl] at hm₂
        rw [Nat.add_one_mul]
        omega
      · rw [hkl, Nat.add_one_mul, Nat.mul_add, Nat.add_assoc]

/-! ### Mask programs -/

lemma maskRegs_start {cnt w : Fin T} (hcw : cnt ≠ w) {n X : ℕ} (R : Regs T A) (hc : R cnt = [])
    (hw : R w = []) :
    Function.update R cnt (List.replicate n tick ++ R cnt) = maskRegs cnt w n X R 0 := by
  have h0 : (binSyms (min 0 n) X : List (Fin (A + 4))) = [] := by simp [binSyms]
  simp only [maskRegs, Nat.sub_zero, h0, List.reverse_nil, hc, List.append_nil]
  exact (Function.update_eq_self_iff.2 (by rw [Function.update_of_ne hcw.symm, hw])).symm

/-- The last phase of a mask build: move the accumulator `w` (forward order) onto `z`. -/
theorem maskFinish_exec {z cnt w : Fin T} (hzc : z ≠ cnt) (hzw : z ≠ w) (hcw : cnt ≠ w)
    {n X p : ℕ} (hp : n ≤ p) (R₀ : Regs T A) (hc : R₀ cnt = []) (hw : R₀ w = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : S.R = maskRegs cnt w n X R₀ p) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (moveR w z id) (mk v S) (2 * n + 2)
        (mk v' { S with R := Function.update R₀ z (binSyms n X ++ R₀ z) }) := by
  have hSw : S.R w = (binSyms n X).reverse := by
    rw [hS, maskRegs_w, show min p n = n by omega]
  obtain ⟨v', hu, he⟩ := moveR_exec body w z hzw.symm id v S
  refine ⟨v', hu, Exec.cast he (by rw [hSw]; simp) ?_⟩
  congr 2
  funext k
  rw [hSw]
  simp only [movedR, List.map_id, List.reverse_reverse, Function.update_apply]
  split_ifs with h1 h2
  · subst h1; rw [hS, maskRegs_of_ne hzc hzw]
  · subst h2; rw [hw]
  · rw [hS]
    by_cases h3 : k = cnt
    · subst h3; rw [maskRegs_cnt hcw, hc, show n - p = 0 by omega]; rfl
    · exact maskRegs_of_ne h3 h2 _ _

/-- The strided mask builder. Registers: unary inputs `nR` (`n`), `oR` (`o`), `KR` (`K ≥ 1`),
`kR` (`k`); output `z`; empty spares `cnt` (positions left), `w` (bits, reversed), `t₁`, `t₂`.
Phases: `cnt := n` ticks; `o` zeros; `M` slots of `k` items, each the bit `pred m` and `K - 1`
zeros; `n` zeros of padding (positions past `n` are dropped); `w` moved onto `z`. -/
def strideMask (nR oR KR kR z cnt w t₁ t₂ : Fin T) (M : ℕ) (pred : ℕ → Bool) : Pr P T Q A U :=
  .seq (ucopy nR cnt t₁)
    (.seq (scanR oR t₁ (emit cnt w false))
      (.seq (strideSlots kR KR cnt w t₁ t₂ pred M)
        (.seq (scanR nR t₁ (emit cnt w false)) (moveR w z id))))

/-- `strideMask`: `z` gains `binSyms n (maskVal o K k M pred)` on top; every other register ends
as it started. No fit hypothesis is needed: positions at or past `n` are dropped. -/
theorem strideMask_exec {nR oR KR kR z cnt w t₁ t₂ : Fin T}
    (hreg : [nR, oR, KR, kR, z, cnt, w, t₁, t₂].Nodup) (M : ℕ) (pred : ℕ → Bool)
    {n o K k : ℕ} (v : HS T Q A U) (S : Stacks T A) (hn : (S.R nR).length = n)
    (ho : (S.R oR).length = o) (hKl : (S.R KR).length = K) (hkl : (S.R kR).length = k)
    (hK : 1 ≤ K) (hc : S.R cnt = []) (hw : S.R w = []) (ht₁ : S.R t₁ = [])
    (ht₂ : S.R t₂ = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 10 * n + 4 * o + M * (k * (4 * K + 9) + 4) + 15 ∧
      Exec body (strideMask nR oR KR kR z cnt w t₁ t₂ M pred) (mk v S) m
        (mk v' { S with
          R := Function.update S.R z (binSyms n (maskVal o K k M pred) ++ S.R z) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hno, hnK, hnk, hnz, hnc, hnw, hn1, hn2⟩, ⟨hoK, hok, hoz, hoc, how, ho1, ho2⟩,
    ⟨hKk, hKz, hKc, hKw, hK1, hK2⟩, ⟨hkz, hkc, hkw, hk1, hk2⟩, ⟨hzc, hzw, hz1, hz2⟩,
    ⟨hcw, hc1, hc2⟩, ⟨hw1, hw2⟩, h12⟩ := hreg'
  set X := maskVal o K k M pred with hX
  -- `cnt := n` ticks
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body hnc hn1 hc1 v S ht₁
  rw [maskRegs_start (X := X) hcw S.R hc hw, hn] at he₁
  -- `o` zeros
  obtain ⟨v₂, hu₂, he₂⟩ := scanEmit_exec body (a := oR) (t := t₁) (cnt := cnt) (w := w)
    (by simp [ho1, hoc, how, hc1.symm, hw1.symm, hcw])
    false S.R v₁ { S with R := maskRegs cnt w n X S.R 0 } rfl ht₁
    (fun q _ h2 _ => maskVal_testBit_false hK pred fun i _ h => by rw [ho] at h2; omega)
  rw [ho, Nat.zero_add] at he₂
  -- the slots
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := strideSlots_exec body (kR := kR) (KR := KR) (cnt := cnt)
    (w := w) (t₁ := t₁) (t₂ := t₂)
    (by simp [hKk.symm, hkc, hkw, hk1, hk2, hKc, hKw, hK1, hK2, hcw, hc1, hc2, hw1, hw2, h12])
    pred S.R hKl hK hkl ht₁ ht₂ M v₂ { S with R := maskRegs cnt w n X S.R o } rfl
    (fun i hi _ => maskVal_testBit_item hK pred hi)
    (fun i _ s hs hsK _ => maskVal_testBit_false hK pred fun i' _ => ne_stride hs hsK)
  -- `n` zeros of padding
  obtain ⟨v₄, hu₄, he₄⟩ := scanEmit_exec body (a := nR) (t := t₁) (cnt := cnt) (w := w)
    (by simp [hn1, hnc, hnw, hc1.symm, hw1.symm, hcw])
    false S.R v₃ { S with R := maskRegs cnt w n X S.R (o + K * (M * k)) } rfl ht₁
    (fun q h1 _ _ => maskVal_testBit_false hK pred fun i hi h => by
      have : K * i < K * (M * k) := Nat.mul_lt_mul_of_pos_left hi (by omega)
      omega)
  rw [hn] at he₄
  -- move the bits onto `z`
  obtain ⟨v₅, hu₅, he₅⟩ := maskFinish_exec body hzc hzw hcw (p := o + K * (M * k) + n)
    (by omega) S.R hc hw v₄ { S with R := maskRegs cnt w n X S.R (o + K * (M * k) + n) } rfl
  refine ⟨v₅, _, by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))⟩
  rw [hn, ho] at *
  omega

/-- The single-bit mask builder. Registers: unary inputs `nR` (`n`), `tR` (`t`); output `z`;
empty spares `cnt`, `w`, `t₁`. Phases: `cnt := n` ticks; `t` zeros; a one; `n` zeros of padding;
`w` moved onto `z`. -/
def bitMask (nR tR z cnt w t₁ : Fin T) : Pr P T Q A U :=
  .seq (ucopy nR cnt t₁)
    (.seq (scanR tR t₁ (emit cnt w false))
      (.seq (.act (emit cnt w true .done))
        (.seq (scanR nR t₁ (emit cnt w false)) (moveR w z id))))

/-- `bitMask`: `z` gains `binSyms n (2 ^ t)` on top in `10 n + 4 t + 15` steps (all zeros when
`n ≤ t`); every other register ends as it started. -/
theorem bitMask_exec {nR tR z cnt w t₁ : Fin T} (hreg : [nR, tR, z, cnt, w, t₁].Nodup)
    {n t : ℕ} (v : HS T Q A U) (S : Stacks T A) (hn : (S.R nR).length = n)
    (ht : (S.R tR).length = t) (hc : S.R cnt = []) (hw : S.R w = []) (ht₁ : S.R t₁ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (bitMask nR tR z cnt w t₁) (mk v S) (10 * n + 4 * t + 15)
        (mk v' { S with R := Function.update S.R z (binSyms n (2 ^ t) ++ S.R z) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hnt, hnz, hnc, hnw, hn1⟩, ⟨htz, htc, htw, ht1⟩, ⟨hzc, hzw, hz1⟩, ⟨hcw, hc1⟩, hw1⟩ :=
    hreg'
  have hbit : ∀ q, (2 ^ t).testBit q = decide (t = q) := fun q => Nat.testBit_two_pow
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body hnc hn1 hc1 v S ht₁
  rw [maskRegs_start (X := 2 ^ t) hcw S.R hc hw, hn] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := scanEmit_exec body (a := tR) (t := t₁) (cnt := cnt) (w := w)
    (by simp [ht1, htc, htw, hc1.symm, hw1.symm, hcw])
    false S.R v₁ { S with R := maskRegs cnt w n (2 ^ t) S.R 0 } rfl ht₁
    (fun q _ h2 _ => by rw [hbit]; rw [ht] at h2; simp; omega)
  rw [ht, Nat.zero_add] at he₂
  obtain ⟨v₃, hu₃, hr₃⟩ := emit_run hcw true (.done) v₂
    { S with R := maskRegs cnt w n (2 ^ t) S.R t }
  have he₃ := Exec.act (body := body) (emit cnt w true .done) (mk v₂
    { S with R := maskRegs cnt w n (2 ^ t) S.R t })
  rw [hr₃, run_done] at he₃
  dsimp only at he₃
  rw [emitFx_maskRegs hcw (fun _ => by rw [hbit]; simp)] at he₃
  obtain ⟨v₄, hu₄, he₄⟩ := scanEmit_exec body (a := nR) (t := t₁) (cnt := cnt) (w := w)
    (by simp [hn1, hnc, hnw, hc1.symm, hw1.symm, hcw])
    false S.R v₃ { S with R := maskRegs cnt w n (2 ^ t) S.R (t + 1) } rfl ht₁
    (fun q h1 _ _ => by rw [hbit]; simp; omega)
  rw [hn] at he₄
  obtain ⟨v₅, hu₅, he₅⟩ := maskFinish_exec body hzc hzw hcw (p := t + 1 + n) (by omega) S.R hc hw
    v₄ { S with R := maskRegs cnt w n (2 ^ t) S.R (t + 1 + n) } rfl
  refine ⟨v₅, by rw [hu₅, hu₄, hu₃, hu₂, hu₁],
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))) ?_ rfl⟩
  ring

end IntegerMultBounds.MathlibTM2.Node
