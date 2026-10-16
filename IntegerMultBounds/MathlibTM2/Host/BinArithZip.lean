module

public import IntegerMultBounds.MathlibTM2.Host.BinArithBits
public import Mathlib.Tactic.CasesM

/-!
# Binary registers: zip passes, copies, padding, addition, subtraction, comparison

A natural number `a` held in width `L` is the register contents `binSyms L a` (`a < 2 ^ L`),
least significant bit on top. Every `_exec` theorem gives the final register file exactly, as a
`Function.update` of the initial one (every other register ends as it started), `v'.user =
v.user`, and an exact step count or an explicit step bound. Spare registers start empty and end
empty. Operands of a binary operation have one common width `L`.

**Zip pass.** `zipPass x y tx ty tz cy f s₀` runs the transducer `f : BitFn` over the bits of `x`
and `y` in parallel, least significant first, from state `s₀` held in scan slot `cy`; the bits of
`x`, `y` move reversed onto `tx`, `ty` and the outputs reversed onto `tz` (`zipPass_exec`,
`2 L + 2` steps). The popped bits pass through the scan slots `x` and `y`, so `cy ∉ {x, y}`; every
other scan slot is kept. `zipKeep` also moves the operands back (`6 L + 6` steps).

**Programs.**
* `bclear a`: `a := []`, keeping every scan slot; `2 |a| + 2` steps.
* `bcopy a c t₁ t₂`: `c` gains the contents of `a` on top; `6 |a| + 6` steps.
* `bzero wR c t`: `c` gains `binSyms |wR| 0` on top; `4 |wR| + 4` steps.
* `bpad a eR t₁ t₂`: `a := binSyms (L + |eR|) x`; `4 L + 6 |eR| + 8` steps. `bpad1 a t`: one high
  zero, `4 L + 7` steps. `bwiden a wR cnt t₁ t₂`: `a := binSyms W x` for `W = |wR| ≥ L`;
  `12 W + 18` steps.
* `bmoveLow s t d`: `d` gains `s` without its top bit (the last symbol) and `s` is emptied;
  `2 |s| + 2 (|s| - 1) + 5` steps. `bshift s t g`: `s := (g v :: s).dropLast`, which is
  `y ↦ (2 y + b) mod 2 ^ W` in width `W` for `g v = bitSymbol b` (`binSyms_shift`); `4 W + 8`
  steps.
* `badd a b c tx ty tz cy`: `c` gains `binSyms L ((x + y) % 2 ^ L)`, slot `cy` holds the carry
  `2 ^ L ≤ x + y`; `8 L + 8` steps. `baddTo a b tx ty tz cy`: `a := (x + y) % 2 ^ L` in place,
  `8 L + 8` steps.
* `bsub a b c tx ty tz cy`: `c` gains `binSyms L ((x + 2 ^ L - y) % 2 ^ L)` (`x - y` modulo
  `2 ^ L`), slot `cy` holds the borrow `x < y`; `8 L + 8` steps.
* `blt`, `beq`: slot `cy` holds `x < y`, `x = y`; `8 L + 8` steps. `bcmp a b tx ty tz clt ceq`:
  both, `16 L + 16` steps.

**Symbol loops.** `eachSym a t p` runs `p` once per symbol of `a` with the symbol in `sym`,
moving the symbols onto `t`; `SymSpec` specifies `p` by register files `Ψ j` off `a` and `t`, as
`IterSpec` does for `scanP`, with the symbol at hand (`eachSym_exec`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node


/-- Split the hypothesis that a register list is duplicate-free into pairwise inequalities. -/
macro "regs_ne " h:ident : tactic =>
  `(tactic| (
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at $h:ident
    casesm* _ ∧ _))

/-- Prove that a register list is duplicate-free from pairwise inequalities in the context. -/
macro "regs_nodup" : tactic =>
  `(tactic| (
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] <;>
    and_intros <;> first | assumption | exact Ne.symm (by assumption)))

/-- Close a pointwise equation of register files built from `Function.update`. -/
macro "regs_ext" : tactic =>
  `(tactic| (
    funext k
    simp only [Function.update_apply, movedR, List.map_id]
    split_ifs <;> simp_all))

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-! ### Zip passes -/

/-- The step of `f` on the state slot `cy` and the operand slots `x`, `y`. -/
def zipNext (x y cy : Fin T) (f : BitFn) (v : HS T Q A U) : Bool × Bool :=
  f (symBit (v.scan cy)) (symBit (v.scan x)) (symBit (v.scan y))

/-- One column of a zip pass: pop `x` and `y` into their scan slots, push them onto `tx`, `ty`,
push the output bit of `f` onto `tz`, store the new state in slot `cy`, and record in `flag`
whether `x` is nonempty. -/
def zipStep (x y tx ty tz cy : Fin T) (f : BitFn) : Act T Q A U :=
  .pop (.rt x) (fun v o => { v with scan := Function.update v.scan x (o.getD blank) })
    (.pop (.rt y) (fun v o => { v with scan := Function.update v.scan y (o.getD blank) })
      (.push (.rt tx) (fun v => v.scan x)
        (.push (.rt ty) (fun v => v.scan y)
          (.push (.rt tz) (fun v => bitSymbol (zipNext x y cy f v).2)
            (.load (fun v => { v with
                scan := Function.update v.scan cy (bitSymbol (zipNext x y cy f v).1) })
              (peekR x))))))

/-- Set the state slot `cy` to `s₀` and test register `x`. -/
def zipInit (x cy : Fin T) (s₀ : Bool) : Act T Q A U :=
  .load (fun v => { v with scan := Function.update v.scan cy (bitSymbol s₀) }) (peekR x)

/-- A zip pass of `f` over `x` and `y` from state `s₀`. -/
def zipPass (x y tx ty tz cy : Fin T) (f : BitFn) (s₀ : Bool) : Pr P T Q A U :=
  .seq (.act (zipInit x cy s₀)) (.loop (·.flag) (.act (zipStep x y tx ty tz cy f)))

/-- Registers after a zip pass over the bits `xs`, `ys` with outputs `zs`. -/
def zipRegs (R : Regs T A) (x y tx ty tz : Fin T) (xs ys zs : List Bool) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update R x []) y [])
    tx ((xs.map bitSymbol).reverse ++ R tx)) ty ((ys.map bitSymbol).reverse ++ R ty)) tz
    ((zs.map bitSymbol).reverse ++ R tz)

theorem zipStep_run {x y tx ty tz cy : Fin T} (hreg : [x, y, tx, ty, tz].Nodup) (hcx : cy ≠ x)
    (hcy : cy ≠ y) (f : BitFn) (p q s : Bool) (xs ys : List (Fin (A + 4))) (v : HS T Q A U)
    (S : Stacks T A) (hx : S.R x = bitSymbol p :: xs) (hy : S.R y = bitSymbol q :: ys)
    (hs : v.scan cy = bitSymbol s) :
    (zipStep x y tx ty tz cy f : Act T Q A U).run (mk v S) =
      mk { v with
          scan := Function.update (Function.update (Function.update v.scan x (bitSymbol p)) y
            (bitSymbol q)) cy (bitSymbol (f s p q).1)
          flag := xs.head?.isSome }
        { S with
          R := Function.update (Function.update (Function.update (Function.update
            (Function.update S.R x xs) y ys) tx (bitSymbol p :: S.R tx)) ty (bitSymbol q :: S.R ty))
            tz (bitSymbol (f s p q).2 :: S.R tz) } := by
  regs_ne hreg
  simp [zipStep, zipNext, peekR, Action.run, update_rt, Function.update_of_ne, *,
    Ne.symm, ne_comm]

theorem zipLoop {x y tx ty tz cy : Fin T} (hreg : [x, y, tx, ty, tz].Nodup) (hcx : cy ≠ x)
    (hcy : cy ≠ y) (f : BitFn) :
    ∀ (xs ys : List Bool) (s : Bool) (v : HS T Q A U) (S : Stacks T A), xs.length = ys.length →
      S.R x = xs.map bitSymbol → S.R y = ys.map bitSymbol → v.scan cy = bitSymbol s →
      v.flag = (S.R x).head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan cy = bitSymbol (zipFin f s xs ys) ∧
        (∀ k, k ≠ x → k ≠ y → k ≠ cy → v'.scan k = v.scan k) ∧
        Exec body (.loop (·.flag) (.act (zipStep x y tx ty tz cy f))) (mk v S) (2 * xs.length + 1)
          (mk v' { S with R := zipRegs S.R x y tx ty tz xs ys (zipOut f s xs ys) })
  | [], ys, s, v, S, hl, hx, hy, hs, hf => by
      obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hl.symm
      refine ⟨v, rfl, hs, fun _ _ _ _ => rfl, ?_⟩
      have : ({ S with R := zipRegs S.R x y tx ty tz [] [] (zipOut f s [] []) } : Stacks T A) =
          S := by
        cases S with
        | mk inp out L R =>
          simp only [List.map_nil] at hx hy ⊢
          congr 1
          funext k
          simp only [zipRegs, zipOut, List.map_nil, List.reverse_nil, List.nil_append,
            Function.update_apply]
          split_ifs <;> simp_all
      rw [this]
      exact .loop_false (by simpa [hx] using hf)
  | _ :: _, [], _, _, _, hl, _, _, _, _ => by simp at hl
  | p :: xs, q :: ys, s, v, S, hl, hx, hy, hs, hf => by
      have hreg' := hreg
      regs_ne hreg'
      have hrun := zipStep_run hreg hcx hcy f p q s (xs.map bitSymbol) (ys.map bitSymbol) v S
        (by simpa using hx) (by simpa using hy) hs
      set v₁ : HS T Q A U := { v with
          scan := Function.update (Function.update (Function.update v.scan x (bitSymbol p)) y
            (bitSymbol q)) cy (bitSymbol (f s p q).1)
          flag := (xs.map bitSymbol).head?.isSome } with hv₁
      set S₁ : Stacks T A := { S with
          R := Function.update (Function.update (Function.update (Function.update
            (Function.update S.R x (xs.map bitSymbol)) y (ys.map bitSymbol)) tx
            (bitSymbol p :: S.R tx)) ty (bitSymbol q :: S.R ty))
            tz (bitSymbol (f s p q).2 :: S.R tz) } with hS₁
      have h1x : S₁.R x = xs.map bitSymbol := by
        simp [Function.update_of_ne, *]
      obtain ⟨v', hu, hc, hsc, he⟩ := zipLoop hreg hcx hcy f xs ys (f s p q).1 v₁ S₁
        (by simpa using hl) h1x (by simp [Function.update_of_ne, *])
        (by simp [hv₁]) (by rw [h1x])
      refine ⟨v', hu, hc, fun k h1 h2 h3 => ?_, ?_⟩
      · rw [hsc k h1 h2 h3]
        simp [hv₁, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
      · refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa [hx] using hf)
          (hrun ▸ Exec.act (body := body) (zipStep x y tx ty tz cy f) (mk v S)) he)
          (by simp only [List.length_cons]; ring) ?_
        congr 2
        funext k
        simp only [hS₁, zipRegs, zipOut, List.map_cons, List.reverse_cons, List.append_assoc,
          List.singleton_append, Function.update_apply]
        split_ifs <;> simp_all

/-- `zipPass`: exactly `2 L + 2` steps on two `L`-bit operands. Slot `cy` ends holding the final
state, the operand slots `x`, `y` are scratch, every other scan slot is kept. -/
theorem zipPass_exec {x y tx ty tz cy : Fin T} (hreg : [x, y, tx, ty, tz].Nodup) (hcx : cy ≠ x)
    (hcy : cy ≠ y) (f : BitFn) (s₀ : Bool) {L a b : ℕ} (v : HS T Q A U) (S : Stacks T A)
    (ha : S.R x = binSyms L a) (hb : S.R y = binSyms L b) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      v'.scan cy = bitSymbol (zipFin f s₀ (binBits L a) (binBits L b)) ∧
      (∀ k, k ≠ x → k ≠ y → k ≠ cy → v'.scan k = v.scan k) ∧
      Exec body (zipPass x y tx ty tz cy f s₀) (mk v S) (2 * L + 2)
        (mk v' { S with
          R := zipRegs S.R x y tx ty tz (binBits L a) (binBits L b)
            (zipOut f s₀ (binBits L a) (binBits L b)) }) := by
  obtain ⟨v', hu, hc, hsc, he⟩ := zipLoop body hreg hcx hcy f (binBits L a) (binBits L b) s₀
    { v with
      scan := Function.update v.scan cy (bitSymbol s₀)
      flag := (S.R x).head?.isSome } S (by simp) (by rw [ha, binSyms_eq])
    (by rw [hb, binSyms_eq]) (by simp) rfl
  refine ⟨v', hu, hc, fun k h1 h2 h3 => by rw [hsc k h1 h2 h3]; simp [Function.update_of_ne h3], ?_⟩
  refine Exec.cast (Exec.seq (Exec.act (body := body) (zipInit x cy s₀) (mk v S)) he) ?_ rfl
  simp; ring

/-! ### Clearing a register, keeping the scan slots -/

/-- Empty register `a`. -/
def bclear (a : Fin T) : Pr P T Q A U := uclear a

theorem bclear_loop (a : Fin T) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A), S.R a = l →
      v.flag = l.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan = v.scan ∧
        Exec body (.loop (·.flag) (.act (popDo a id))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := Function.update S.R a [] })
  | [], v, S, hS, hf => by
      refine ⟨v, rfl, rfl, ?_⟩
      have : ({ S with R := Function.update S.R a [] } : Stacks T A) = S := by
        rw [← hS, Function.update_eq_self]
      rw [this]
      exact .loop_false (by simpa using hf)
  | x :: rest, v, S, hS, hf => by
      obtain ⟨v', hu, hsc, he⟩ := bclear_loop a rest { v with sym := some x, flag := rest.head?.isSome }
        { S with R := Function.update S.R a rest } (by simp) rfl
      refine ⟨v', hu, hsc, ?_⟩
      have hrun : (popDo a id : Act T Q A U).run (mk v S) =
          mk { v with sym := some x, flag := rest.head?.isSome }
            { S with R := Function.update S.R a rest } := by
        simp [popDo, peekR, Action.run, hS, update_rt]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (popDo a id) (mk v S)) he) (by simp; ring) ?_
      simp

/-- `bclear`: `a` emptied in `2 |a| + 2` steps; every scan slot is kept. -/
theorem bclear_exec (a : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan = v.scan ∧
      Exec body (bclear a) (mk v S) (2 * (S.R a).length + 2)
        (mk v' { S with R := Function.update S.R a [] }) := by
  obtain ⟨v', hu, hsc, he⟩ := bclear_loop body a (S.R a) { v with flag := (S.R a).head?.isSome } S
    rfl rfl
  exact ⟨v', hu, hsc, Exec.cast (Exec.seq (peekR_run a v S ▸ Exec.act (body := body) (peekR a)
    (mk v S)) he) (by ring) rfl⟩

/-! ### Operations on two operands -/

/-- A zip pass that moves the operands back: `x` and `y` keep their values and `tz` gains the
outputs, reversed. -/
def zipKeep (x y tx ty tz cy : Fin T) (f : BitFn) (s₀ : Bool) : Pr P T Q A U :=
  .seq (zipPass x y tx ty tz cy f s₀) (.seq (moveR tx x id) (moveR ty y id))

/-- `zipKeep`: exactly `6 L + 6` steps on two `L`-bit operands, with empty `tx`, `ty`. -/
theorem zipKeep_exec {x y tx ty tz cy : Fin T} (hreg : [x, y, tx, ty, tz].Nodup) (hcx : cy ≠ x)
    (hcy : cy ≠ y) (f : BitFn) (s₀ : Bool) {L a b : ℕ} (v : HS T Q A U) (S : Stacks T A)
    (ha : S.R x = binSyms L a) (hb : S.R y = binSyms L b) (htx : S.R tx = [])
    (hty : S.R ty = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      v'.scan cy = bitSymbol (zipFin f s₀ (binBits L a) (binBits L b)) ∧
      (∀ k, k ≠ x → k ≠ y → k ≠ cy → v'.scan k = v.scan k) ∧
      Exec body (zipKeep x y tx ty tz cy f s₀) (mk v S) (6 * L + 6)
        (mk v' { S with
          R := Function.update S.R tz
            (((zipOut f s₀ (binBits L a) (binBits L b)).map bitSymbol).reverse ++ S.R tz) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, hc₁, hsc₁, he₁⟩ := zipPass_exec body hreg hcx hcy f s₀ v S ha hb
  rw [binSyms_eq] at ha hb
  set R₁ := zipRegs S.R x y tx ty tz (binBits L a) (binBits L b)
    (zipOut f s₀ (binBits L a) (binBits L b)) with hR₁
  obtain ⟨v₂, hu₂, hsc₂, he₂⟩ := moveR_exec_scan body tx x (Ne.symm ‹x ≠ tx›) id v₁
    { S with R := R₁ }
  obtain ⟨v₃, hu₃, hsc₃, he₃⟩ := moveR_exec_scan body ty y (Ne.symm ‹y ≠ ty›) id v₂
    { S with R := movedR R₁ tx x id (R₁ tx) }
  refine ⟨v₃, by rw [hu₃, hu₂, hu₁], by rw [hsc₃, hsc₂, hc₁],
    fun k h1 h2 h3 => by rw [hsc₃, hsc₂, hsc₁ k h1 h2 h3],
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) ?_ ?_⟩
  · simp [zipRegs, movedR, Function.update_of_ne, *, Ne.symm]; ring
  · congr 2
    simp only [hR₁, zipRegs]
    regs_ext

/-- Addition: `c` gains `(a + b) mod 2 ^ L` on top; the carry goes to slot `cy`. -/
def badd (a b c tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (zipKeep a b tx ty tz cy addF false) (moveR tz c id)

/-- Subtraction: `c` gains `(a - b) mod 2 ^ L` on top; the borrow goes to slot `cy`. -/
def bsub (a b c tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (zipKeep a b tx ty tz cy subF false) (moveR tz c id)

/-- A zip pass whose outputs go on top of `c`. -/
theorem zipTo_exec {a b c tx ty tz cy : Fin T} (hreg : [a, b, c, tx, ty, tz].Nodup)
    (hca : cy ≠ a) (hcb : cy ≠ b) (f : BitFn) (s₀ : Bool) {L x y : ℕ} (v : HS T Q A U)
    (S : Stacks T A) (ha : S.R a = binSyms L x) (hb : S.R b = binSyms L y) (htx : S.R tx = [])
    (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      v'.scan cy = bitSymbol (zipFin f s₀ (binBits L x) (binBits L y)) ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ cy → v'.scan k = v.scan k) ∧
      Exec body (.seq (zipKeep a b tx ty tz cy f s₀) (moveR tz c id)) (mk v S) (8 * L + 8)
        (mk v' { S with
          R := Function.update S.R c
            ((zipOut f s₀ (binBits L x) (binBits L y)).map bitSymbol ++ S.R c) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, hc₁, hsc₁, he₁⟩ := zipKeep_exec body (x := a) (y := b) (tx := tx) (ty := ty)
    (tz := tz) (by regs_nodup) hca hcb f s₀ v S ha hb htx hty
  obtain ⟨v₂, hu₂, hsc₂, he₂⟩ := moveR_exec_scan body tz c (Ne.symm ‹c ≠ tz›) id v₁
    { S with
      R := Function.update S.R tz
        (((zipOut f s₀ (binBits L x) (binBits L y)).map bitSymbol).reverse ++ S.R tz) }
  refine ⟨v₂, by rw [hu₂, hu₁], by rw [hsc₂, hc₁], fun k h1 h2 h3 => by rw [hsc₂, hsc₁ k h1 h2 h3],
    Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
  · simp [htz, length_zipOut]; ring
  · congr 2
    regs_ext

/-- `badd` on `L`-bit operands: `c` gains `binSyms L ((x + y) % 2 ^ L)` and slot `cy` holds the
carry `2 ^ L ≤ x + y`, in `8 L + 8` steps. -/
theorem badd_exec {a b c tx ty tz cy : Fin T} (hreg : [a, b, c, tx, ty, tz].Nodup)
    (hca : cy ≠ a) (hcb : cy ≠ b) {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms L x) (hb : S.R b = binSyms L y)
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan cy = bitSymbol (decide (2 ^ L ≤ x + y)) ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ cy → v'.scan k = v.scan k) ∧
      Exec body (badd a b c tx ty tz cy) (mk v S) (8 * L + 8)
        (mk v' { S with R := Function.update S.R c (binSyms L ((x + y) % 2 ^ L) ++ S.R c) }) := by
  obtain ⟨v', hu, hc, hsc, he⟩ := zipTo_exec body hreg hca hcb addF false v S ha hb htx hty htz
  refine ⟨v', hu, ?_, hsc, ?_⟩
  · rw [hc, zipFin_addF_lt false L x y hx hy]; simp
  · rw [zipOut_addF, ← binSyms_eq] at he
    rw [binSyms_mod]
    simp only [Bool.toNat_false, Nat.add_zero] at he
    exact he

/-- `bsub` on `L`-bit operands: `c` gains `binSyms L ((x + 2 ^ L - y) % 2 ^ L)` (`x - y` modulo
`2 ^ L`) and slot `cy` holds the borrow `x < y`, in `8 L + 8` steps. -/
theorem bsub_exec {a b c tx ty tz cy : Fin T} (hreg : [a, b, c, tx, ty, tz].Nodup)
    (hca : cy ≠ a) (hcb : cy ≠ b) {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms L x) (hb : S.R b = binSyms L y)
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan cy = bitSymbol (decide (x < y)) ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ cy → v'.scan k = v.scan k) ∧
      Exec body (bsub a b c tx ty tz cy) (mk v S) (8 * L + 8)
        (mk v' { S with
          R := Function.update S.R c (binSyms L ((x + 2 ^ L - y) % 2 ^ L) ++ S.R c) }) := by
  obtain ⟨v', hu, hc, hsc, he⟩ := zipTo_exec body hreg hca hcb subF false v S ha hb htx hty htz
  refine ⟨v', hu, ?_, hsc, ?_⟩
  · rw [hc, zipFin_subF_binBits L x y hx hy]
  · rw [zipOut_subF_binBits L x y hy, ← binSyms_eq] at he
    rw [binSyms_mod]
    exact he

/-- In-place addition `a := (a + b) mod 2 ^ L`; the carry goes to slot `cy`. -/
def baddTo (a b tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (zipPass a b tx ty tz cy addF false) (.seq (bclear tx) (.seq (moveR ty b id) (moveR tz a id)))

/-- `baddTo` on `L`-bit operands: `a := (x + y) % 2 ^ L` and slot `cy` holds the carry, in
`8 L + 8` steps. -/
theorem baddTo_exec {a b tx ty tz cy : Fin T} (hreg : [a, b, tx, ty, tz].Nodup)
    (hca : cy ≠ a) (hcb : cy ≠ b) {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms L x) (hb : S.R b = binSyms L y)
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan cy = bitSymbol (decide (2 ^ L ≤ x + y)) ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ cy → v'.scan k = v.scan k) ∧
      Exec body (baddTo a b tx ty tz cy) (mk v S) (8 * L + 8)
        (mk v' { S with R := Function.update S.R a (binSyms L ((x + y) % 2 ^ L)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, hc₁, hsc₁, he₁⟩ := zipPass_exec body hreg hca hcb addF false v S ha hb
  rw [zipOut_addF] at he₁
  rw [binSyms_eq] at hb
  set R₁ := zipRegs S.R a b tx ty tz (binBits L x) (binBits L y)
    (binBits L (x + y + false.toNat)) with hR₁
  obtain ⟨v₂, hu₂, hsc₂, he₂⟩ := bclear_exec body tx v₁ { S with R := R₁ }
  obtain ⟨v₃, hu₃, hsc₃, he₃⟩ := moveR_exec_scan body ty b (Ne.symm ‹b ≠ ty›) id v₂
    { S with R := Function.update R₁ tx [] }
  obtain ⟨v₄, hu₄, hsc₄, he₄⟩ := moveR_exec_scan body tz a (Ne.symm ‹a ≠ tz›) id v₃
    { S with R := movedR (Function.update R₁ tx []) ty b id (Function.update R₁ tx [] ty) }
  refine ⟨v₄, by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    fun k h1 h2 h3 => by rw [hsc₄, hsc₃, hsc₂, hsc₁ k h1 h2 h3],
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))) ?_ ?_⟩
  · rw [hsc₄, hsc₃, hsc₂, hc₁, zipFin_addF_lt false L x y hx hy]; simp
  · simp [zipRegs, movedR, Function.update_of_ne, *, Ne.symm]; ring
  · congr 2
    rw [binSyms_mod, binSyms_eq]
    simp only [hR₁, zipRegs, Bool.toNat_false, Nat.add_zero]
    regs_ext

/-- Comparison `a < b` into slot `cy`. -/
def blt (a b tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (zipKeep a b tx ty tz cy ltF false) (bclear tz)

/-- Equality `a = b` into slot `cy`. -/
def beq (a b tx ty tz cy : Fin T) : Pr P T Q A U :=
  .seq (zipKeep a b tx ty tz cy eqF true) (bclear tz)

/-- Both comparisons: `a < b` into slot `clt`, `a = b` into slot `ceq`. -/
def bcmp (a b tx ty tz clt ceq : Fin T) : Pr P T Q A U :=
  .seq (blt a b tx ty tz clt) (beq a b tx ty tz ceq)

/-- A zip pass whose outputs are discarded: the registers end as they started. -/
theorem zipTest_exec {a b tx ty tz cy : Fin T} (hreg : [a, b, tx, ty, tz].Nodup)
    (hca : cy ≠ a) (hcb : cy ≠ b) (f : BitFn) (s₀ : Bool) {L x y : ℕ} (v : HS T Q A U)
    (S : Stacks T A) (ha : S.R a = binSyms L x) (hb : S.R b = binSyms L y) (htx : S.R tx = [])
    (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      v'.scan cy = bitSymbol (zipFin f s₀ (binBits L x) (binBits L y)) ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ cy → v'.scan k = v.scan k) ∧
      Exec body (.seq (zipKeep a b tx ty tz cy f s₀) (bclear tz)) (mk v S) (8 * L + 8) (mk v' S) := by
  obtain ⟨v₁, hu₁, hc₁, hsc₁, he₁⟩ := zipKeep_exec body hreg hca hcb f s₀ v S ha hb htx hty
  obtain ⟨v₂, hu₂, hsc₂, he₂⟩ := bclear_exec body tz v₁
    { S with
      R := Function.update S.R tz
        (((zipOut f s₀ (binBits L x) (binBits L y)).map bitSymbol).reverse ++ S.R tz) }
  refine ⟨v₂, by rw [hu₂, hu₁], by rw [hsc₂, hc₁], fun k h1 h2 h3 => by rw [hsc₂, hsc₁ k h1 h2 h3],
    Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
  · simp [htz, length_zipOut]; ring
  · rw [Function.update_idem, ← htz, Function.update_eq_self]

/-- `blt` on `L`-bit operands: slot `cy` holds `x < y`; `8 L + 8` steps, registers unchanged. -/
theorem blt_exec {a b tx ty tz cy : Fin T} (hreg : [a, b, tx, ty, tz].Nodup)
    (hca : cy ≠ a) (hcb : cy ≠ b) {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms L x) (hb : S.R b = binSyms L y)
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan cy = bitSymbol (decide (x < y)) ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ cy → v'.scan k = v.scan k) ∧
      Exec body (blt a b tx ty tz cy) (mk v S) (8 * L + 8) (mk v' S) := by
  obtain ⟨v', hu, hc, hsc, he⟩ := zipTest_exec body hreg hca hcb ltF false v S ha hb htx hty htz
  refine ⟨v', hu, ?_, hsc, he⟩
  rw [hc, zipFin_ltF, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  simp

/-- `beq` on `L`-bit operands: slot `cy` holds `x = y`; `8 L + 8` steps, registers unchanged. -/
theorem beq_exec {a b tx ty tz cy : Fin T} (hreg : [a, b, tx, ty, tz].Nodup)
    (hca : cy ≠ a) (hcb : cy ≠ b) {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms L x) (hb : S.R b = binSyms L y)
    (htx : S.R tx = []) (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan cy = bitSymbol (decide (x = y)) ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ cy → v'.scan k = v.scan k) ∧
      Exec body (beq a b tx ty tz cy) (mk v S) (8 * L + 8) (mk v' S) := by
  obtain ⟨v', hu, hc, hsc, he⟩ := zipTest_exec body hreg hca hcb eqF true v S ha hb htx hty htz
  refine ⟨v', hu, ?_, hsc, he⟩
  rw [hc, zipFin_eqF, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  simp

/-- `bcmp` on `L`-bit operands: slot `clt` holds `x < y` and slot `ceq` holds `x = y`;
`16 L + 16` steps, registers unchanged. -/
theorem bcmp_exec {a b tx ty tz clt ceq : Fin T} (hreg : [a, b, tx, ty, tz].Nodup)
    (hla : clt ≠ a) (hlb : clt ≠ b) (hea : ceq ≠ a) (heb : ceq ≠ b) (hle : clt ≠ ceq)
    {L x y : ℕ} (hx : x < 2 ^ L) (hy : y < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (ha : S.R a = binSyms L x) (hb : S.R b = binSyms L y) (htx : S.R tx = [])
    (hty : S.R ty = []) (htz : S.R tz = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan clt = bitSymbol (decide (x < y)) ∧
      v'.scan ceq = bitSymbol (decide (x = y)) ∧
      (∀ k, k ≠ a → k ≠ b → k ≠ clt → k ≠ ceq → v'.scan k = v.scan k) ∧
      Exec body (bcmp a b tx ty tz clt ceq) (mk v S) (16 * L + 16) (mk v' S) := by
  obtain ⟨v₁, hu₁, hc₁, hsc₁, he₁⟩ := blt_exec body hreg hla hlb hx hy v S ha hb htx hty htz
  obtain ⟨v₂, hu₂, hc₂, hsc₂, he₂⟩ := beq_exec body hreg hea heb hx hy v₁ S ha hb htx hty htz
  refine ⟨v₂, by rw [hu₂, hu₁], by rw [hsc₂ clt hla hlb hle, hc₁], hc₂,
    fun k h1 h2 h3 h4 => by rw [hsc₂ k h1 h2 h4, hsc₁ k h1 h2 h3],
    Exec.cast (Exec.seq he₁ he₂) (by ring) rfl⟩

/-! ### Copying, zeros, padding, shifting -/

/-- Copy: `c` gains the contents of `a` on top. `a` is scanned through `t₁` and the copy built on
`t₂`. -/
def bcopy (a c t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (scanR a t₁ (pushN t₂ (fun v => v.sym.getD blank) 1)) (moveR t₂ c id)

/-- `bcopy`: `c` gains the contents of `a` on top, in `6 |a| + 6` steps. -/
theorem bcopy_exec {a c t₁ t₂ : Fin T} (hreg : [a, c, t₁, t₂].Nodup) (v : HS T Q A U)
    (S : Stacks T A) (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (bcopy a c t₁ t₂) (mk v S) (6 * (S.R a).length + 6)
        (mk v' { S with R := Function.update S.R c (S.R a ++ S.R c) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := scanR_exec' body (a := a) (t := t₁) ‹a ≠ t₁›
    (regFx_pushN t₂ 1 (fun v => v.sym.getD blank) id (fun v x hx => by simp [hx]))
    (frame_pushFx ‹a ≠ t₂› 1 id) (frame_pushFx ‹t₁ ≠ t₂› 1 id) v S ht₁
  rw [foldl_pushFx] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body t₂ c (Ne.symm ‹c ≠ t₂›) id v₁
    { S with
      R := Function.update S.R t₂
        (((S.R a).reverse.flatMap fun x => List.replicate 1 (id x)) ++ S.R t₂) }
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
  · simp [ht₂]; ring
  · congr 2
    regs_ext

/-- Zeros: `c` gains `binSyms |wR| 0` on top; `wR` is scanned through `t`. -/
def bzero (wR c t : Fin T) : Pr P T Q A U := zeroBits wR c t

/-- `bzero`: `4 |wR| + 4` steps. -/
theorem bzero_exec {wR c t : Fin T} (hreg : [wR, c, t].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (bzero wR c t) (mk v S) (4 * (S.R wR).length + 4)
        (mk v' { S with R := Function.update S.R c (binSyms (S.R wR).length 0 ++ S.R c) }) := by
  have hreg' := hreg
  regs_ne hreg'
  exact zeroBits_exec body ‹wR ≠ c› ‹wR ≠ t› ‹c ≠ t› v S ht

/-- Padding with `|eR|` high zeros: `a` moves reversed onto `t₁`, the zeros go on top (`eR` is
scanned through `t₂`), and `t₁` moves back. -/
def bpad (a eR t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (moveR a t₁ id) (.seq (umulSym 1 (bitSymbol false) eR t₁ t₂) (moveR t₁ a id))

/-- `bpad`: `a := binSyms (L + |eR|) x`, in `4 L + 6 |eR| + 8` steps. -/
theorem bpad_exec {a eR t₁ t₂ : Fin T} (hreg : [a, eR, t₁, t₂].Nodup) {L x : ℕ} (hx : x < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms L x) (ht₁ : S.R t₁ = [])
    (ht₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (bpad a eR t₁ t₂) (mk v S) (4 * L + 6 * (S.R eR).length + 8)
        (mk v' { S with R := Function.update S.R a (binSyms (L + (S.R eR).length) x) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body a t₁ ‹a ≠ t₁› id v S
  obtain ⟨v₂, hu₂, he₂⟩ := umulSym_exec body 1 (bitSymbol false) (a := eR) (b := t₁) (t := t₂)
    ‹eR ≠ t₁› ‹eR ≠ t₂› ‹t₁ ≠ t₂› v₁ { S with R := movedR S.R a t₁ id (S.R a) }
    (by simp [movedR, Function.update_of_ne, *, Ne.symm])
  set S₂ : Stacks T A := { { S with R := movedR S.R a t₁ id (S.R a) } with
    R := Function.update (movedR S.R a t₁ id (S.R a)) t₁
      (List.replicate (1 * ((movedR S.R a t₁ id (S.R a)) eR).length) (bitSymbol false) ++
        (movedR S.R a t₁ id (S.R a)) t₁) } with hS₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body t₁ a (Ne.symm ‹a ≠ t₁›) id v₂ S₂
  refine ⟨v₃, by rw [hu₃, hu₂, hu₁], Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) ?_ ?_⟩
  · simp [movedR, Function.update_of_ne, *, Ne.symm]; ring
  · congr 2
    rw [binSyms_pad L _ x hx]
    simp only [hS₂, ← ha]
    regs_ext

/-- One high zero: `a` moves reversed onto `t`, a zero goes on top, and `t` moves back. -/
def bpad1 (a t : Fin T) : Pr P T Q A U :=
  .seq (moveR a t id) (.seq (.act (.push (.rt t) (fun _ => bitSymbol false) .done)) (moveR t a id))

/-- `bpad1`: `a := binSyms (L + 1) x`, in `4 L + 7` steps. -/
theorem bpad1_exec {a t : Fin T} (hat : a ≠ t) {L x : ℕ} (hx : x < 2 ^ L) (v : HS T Q A U)
    (S : Stacks T A) (ha : S.R a = binSyms L x) (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (bpad1 a t) (mk v S) (4 * L + 7)
        (mk v' { S with R := Function.update S.R a (binSyms (L + 1) x) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body a t hat id v S
  have he₂ := Exec.act (body := body) (.push (.rt t) (fun _ => bitSymbol false) .done)
    (mk v₁ { S with R := movedR S.R a t id (S.R a) })
  simp only [Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk] at he₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body t a hat.symm id v₁
    { S with
      R := Function.update (movedR S.R a t id (S.R a)) t
        (bitSymbol false :: movedR S.R a t id (S.R a) t) }
  refine ⟨v₃, by rw [hu₃, hu₁], Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) ?_ ?_⟩
  · simp [movedR, ht, ha]; ring
  · congr 2
    rw [binSyms_pad L 1 x hx]
    regs_ext

/-- Widening to the width `|wR|`: `cnt := |wR| - L` ticks, pad by `cnt`, clear `cnt`. -/
def bwiden (a wR cnt t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (ucopy wR cnt t₁) (.seq (usub a cnt t₁) (.seq (bpad a cnt t₁ t₂) (uclear cnt)))

/-- `bwiden`: for `L ≤ W = |wR|`, `a := binSyms W x`, in `12 W + 18` steps. -/
theorem bwiden_exec {a wR cnt t₁ t₂ : Fin T} (hreg : [a, wR, cnt, t₁, t₂].Nodup) {L W x : ℕ}
    (hLW : L ≤ W) (hx : x < 2 ^ L) (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms L x)
    (hw : (S.R wR).length = W) (hc : S.R cnt = []) (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (bwiden a wR cnt t₁ t₂) (mk v S) (12 * W + 18)
        (mk v' { S with R := Function.update S.R a (binSyms W x) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body (a := wR) (b := cnt) (t := t₁) ‹wR ≠ cnt› ‹wR ≠ t₁›
    ‹cnt ≠ t₁› v S ht₁
  set R₁ := Function.update S.R cnt (List.replicate (S.R wR).length tick ++ S.R cnt) with hR₁
  obtain ⟨v₂, hu₂, he₂⟩ := usub_exec body (a := a) (b := cnt) (t := t₁) ‹a ≠ cnt› ‹a ≠ t₁›
    ‹cnt ≠ t₁› v₁ { S with R := R₁ } (by simp [Function.update_of_ne, *, Ne.symm])
  set R₂ := Function.update R₁ cnt ((R₁ cnt).drop (R₁ a).length) with hR₂
  have h2c : R₂ cnt = List.replicate (W - L) tick := by
    simp [Function.update_of_ne, *, List.drop_replicate]
  obtain ⟨v₃, hu₃, he₃⟩ := bpad_exec body (a := a) (eR := cnt) (t₁ := t₁) (t₂ := t₂)
    (by regs_nodup) hx v₂ { S with R := R₂ } (by simp [Function.update_of_ne, *])
    (by simp [Function.update_of_ne, *, Ne.symm])
    (by simp [Function.update_of_ne, *, Ne.symm])
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body cnt v₃
    { S with R := Function.update R₂ a (binSyms (L + (R₂ cnt).length) x) }
  refine ⟨v₄, by rw [hu₄, hu₃, hu₂, hu₁], Exec.cast (Exec.seq he₁ (Exec.seq he₂
    (Exec.seq he₃ he₄))) ?_ ?_⟩
  · simp only [h2c, List.length_replicate, Function.update_of_ne ‹a ≠ cnt›.symm,
      ]
    simp [Function.update_of_ne, *]
    omega
  · congr 2
    rw [h2c, List.length_replicate, show L + (W - L) = W by omega]
    simp only [hR₂, hR₁]
    regs_ext

/-- `d` gains `s` without its last symbol (the top bit of a numeral); `s` is emptied through
`t`. -/
def bmoveLow (s t d : Fin T) : Pr P T Q A U :=
  .seq (moveR s t id) (.seq (.act (dropTop t .done)) (moveR t d id))

/-- `bmoveLow`: `2 |s| + 2 (|s| - 1) + 5` steps; `d` may be `s`. -/
theorem bmoveLow_exec {s t d : Fin T} (hst : s ≠ t) (hdt : d ≠ t) (v : HS T Q A U)
    (S : Stacks T A) (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (bmoveLow s t d) (mk v S) (2 * (S.R s).length + 2 * ((S.R s).length - 1) + 5)
        (mk v' { S with
          R := Function.update (Function.update S.R s []) d
            ((S.R s).dropLast ++ Function.update S.R s [] d) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body s t hst id v S
  have he₂ := Exec.act (body := body) (dropTop t .done)
    (mk v₁ { S with R := movedR S.R s t id (S.R s) })
  simp only [dropTop, Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk] at he₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body t d hdt.symm id v₁
    { S with
      R := Function.update (movedR S.R s t id (S.R s)) t (movedR S.R s t id (S.R s) t).tail }
  refine ⟨v₃, by rw [hu₃, hu₁], Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) ?_ ?_⟩
  · simp [movedR, ht, List.tail_reverse]; ring
  · congr 2
    funext k
    simp only [Function.update_apply, movedR, List.map_id, ht, List.append_nil, 
      ]
    split_ifs <;> simp_all

/-- Shift: push `g v` onto `s`, then drop the last symbol of `s` through `t`. On a numeral of
width `W` with `g v = bitSymbol b` this is `y ↦ (2 y + b) mod 2 ^ W` (`binSyms_shift`). -/
def bshift (s t : Fin T) (g : HS T Q A U → Fin (A + 4)) : Pr P T Q A U :=
  .seq (.act (.push (.rt s) g .done)) (bmoveLow s t s)

/-- `bshift`: `s := (g v :: s).dropLast`, in `4 |s| + 8` steps. -/
theorem bshift_exec {s t : Fin T} (hst : s ≠ t) (g : HS T Q A U → Fin (A + 4)) (v : HS T Q A U)
    (S : Stacks T A) (ht : S.R t = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (bshift s t g) (mk v S) (4 * (S.R s).length + 8)
        (mk v' { S with R := Function.update S.R s (g v :: S.R s).dropLast }) := by
  have he₁ := Exec.act (body := body) (.push (.rt s) g .done) (mk v S)
  simp only [Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := bmoveLow_exec body hst hst v
    { S with R := Function.update S.R s (g v :: S.R s) } (by simp [Function.update_of_ne hst.symm, ht])
  refine ⟨v₂, hu₂, Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
  · simp; omega
  · congr 2
    simp

/-! ### Symbol loops -/

/-- Run `p` once per symbol of register `a`, popping the symbol into `sym` and pushing it onto
`t`; `a` ends empty and `t` holds its symbols reversed on top. -/
def eachSym (a t : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR a)) (.loop (·.flag) (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))))

/-- Iteration `j` of `p`, run with symbol `l[j]` in `sym`, takes registers equal to `Ψ j` off
`a` and `t` to registers equal to `Ψ (j + 1)` off `a` and `t`, in at most `c` steps, leaving
`a`, `t` and `user` alone. -/
def SymSpec (p : Pr P T Q A U) (a t : Fin T) (l : List (Fin (A + 4))) (Ψ : ℕ → Regs T A)
    (c : ℕ) : Prop :=
  ∀ j (hj : j < l.length) (v : HS T Q A U) (S : Stacks T A), v.sym = some l[j] →
    (∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) →
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧ m ≤ c ∧
      Exec body p (mk v S) m (mk v' { S with R := R' }) ∧ R' a = S.R a ∧ R' t = S.R t ∧
      ∀ k, k ≠ a → k ≠ t → R' k = Ψ (j + 1) k

theorem eachSym_loop {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U} {l : List (Fin (A + 4))}
    {Ψ : ℕ → Regs T A} {c : ℕ} (hp : SymSpec body p a t l Ψ c) :
    ∀ (n j : ℕ) (v : HS T Q A U) (S : Stacks T A), j + n = l.length → S.R a = l.drop j →
      (∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) → v.flag = (S.R a).head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧ m ≤ n * (c + 3) + 1 ∧
        Exec body (.loop (·.flag) (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))))
          (mk v S) m (mk v' { S with R := R' }) ∧
        R' a = [] ∧ R' t = (l.drop j).reverse ++ S.R t ∧
        ∀ k, k ≠ a → k ≠ t → R' k = Ψ (j + n) k
  | 0, j, v, S, hn, hS, hΨ, hfl => by
      have hd : l.drop j = [] := List.drop_eq_nil_of_le (by omega)
      rw [hd] at hS
      exact ⟨v, S.R, 1, rfl, by simp, .loop_false (by simpa [hS] using hfl), hS, by simp [hd],
        by simpa using hΨ⟩
  | n + 1, j, v, S, hn, hS, hΨ, hfl => by
      have hj : j < l.length := by omega
      have hS' : S.R a = l[j] :: l.drop (j + 1) := by rw [hS, List.drop_eq_getElem_cons hj]
      have hrun : (popPush a t : Act T Q A U).run (mk v S) = mk { v with sym := some l[j] }
          { S with
            R := Function.update (Function.update S.R a (l.drop (j + 1))) t (l[j] :: S.R t) } := by
        simp only [popPush, Action.run, mk_var, mk_stk, get_rt, hS', List.head?_cons,
          List.tail_cons, Option.getD_some, update_rt, store_mk]
        rw [Function.update_of_ne hat.symm]
      obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, ha₁, ht₁, hΨ₁⟩ := hp j hj { v with sym := some l[j] }
        { S with
          R := Function.update (Function.update S.R a (l.drop (j + 1))) t (l[j] :: S.R t) } rfl
        (fun k hka hkt => by
          simpa [Function.update_of_ne hka, Function.update_of_ne hkt] using hΨ k hka hkt)
      have ha₁' : R₁ a = l.drop (j + 1) := by rw [ha₁]; simp [Function.update_of_ne hat]
      have he₂ := Exec.act (body := body) (peekR a) (mk v₁ { S with R := R₁ })
      rw [peekR_run] at he₂
      obtain ⟨v', R', m', hu', hm', he', ha', ht', hΨ'⟩ := eachSym_loop hat hp n (j + 1)
        { v₁ with flag := (R₁ a).head?.isSome } { S with R := R₁ } (by omega) ha₁' hΨ₁ rfl
      refine ⟨v', R', 1 + (m₁ + 1) + m' + 1, by rw [hu', ← hu₁], ?_,
        Exec.loop_true (by show v.flag = true; rw [hfl, hS']; rfl) (Exec.seq (hrun ▸ Exec.act (body := body) _ (mk v S))
          (Exec.seq he₁ he₂)) he', ha', ?_, ?_⟩
      · rw [Nat.add_mul]; omega
      · rw [ht']; dsimp only
        rw [ht₁]; dsimp only
        rw [Function.update_self, List.drop_eq_getElem_cons hj, List.reverse_cons,
          List.append_assoc]
        rfl
      · intro k hka hkt
        rw [hΨ' k hka hkt, Nat.add_assoc, Nat.add_comm 1]

/-- `eachSym`: registers off `a` and `t` go from `Ψ 0` to `Ψ |a|`; `a` is emptied and `t`
gains the symbols of `a` reversed on top; at most `|a| (c + 3) + 2` steps. -/
theorem eachSym_exec {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U} {Ψ : ℕ → Regs T A} {c : ℕ}
    (v : HS T Q A U) (S : Stacks T A) (hp : SymSpec body p a t (S.R a) Ψ c)
    (hΨ : ∀ k, k ≠ a → k ≠ t → S.R k = Ψ 0 k) :
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧
      m ≤ (S.R a).length * (c + 3) + 2 ∧
      Exec body (eachSym a t p) (mk v S) m (mk v' { S with R := R' }) ∧
      R' a = [] ∧ R' t = (S.R a).reverse ++ S.R t ∧
      ∀ k, k ≠ a → k ≠ t → R' k = Ψ (S.R a).length k := by
  obtain ⟨v', R', m, hu, hm, he, ha', ht', hΨ'⟩ := eachSym_loop body hat hp (S.R a).length 0
    { v with flag := (S.R a).head?.isSome } S (by simp) (by simp) hΨ rfl
  refine ⟨v', R', 1 + m, hu, by omega, Exec.seq (peekR_run a v S ▸
    Exec.act (body := body) (peekR a) (mk v S)) he, ha', by simpa using ht', ?_⟩
  simpa using hΨ'

end IntegerMultBounds.MathlibTM2.Host
