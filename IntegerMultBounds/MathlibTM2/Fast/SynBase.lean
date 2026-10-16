module

public import IntegerMultBounds.MathlibTM2.Node.TopProc
public import IntegerMultBounds.MathlibTM2.Fast.Layout
public import IntegerMultBounds.MathlibTM2.Fast.TwiddleL
public import IntegerMultBounds.MathlibTM2.Fast.RingProd
public import IntegerMultBounds.MathlibTM2.Cost.Branching

/-!
# Registers and run contracts of the synthetic transform machines

Paper §6, the computed transforms of `lem:synthetic-transform-cost`. The machines run on the
register file of the layer machine (`nT SXReg` registers, `IntegerMultBounds.MathlibTM2.LayerMachine.reg`), because the
layer (`topProg`) is a fixed program on that file.

## Registers

`SynW` names the registers of the transform machines: the twiddle registers `tw x` (`TwReg`), the
layout registers `ly i`, the persistent parameters `p x` (`SynP`) and the scratch registers
`s i`. Each lives on a wire register of the layer machine, `sreg x = reg (.wire (synWire x))`
(`synWire` injective). The wires are empty whenever the layer runs, so the transform machines
park their persistent registers on `park` around it (`synStash`, `synUnstash`).

## Run contracts

Contracts are `LayRuns body p R₀ R₁ c` (`Fast/Layout.lean`): from every store with empty left
stacks and register file `R₀`, `p` reaches register file `R₁` within `c` steps, keeping `user`.
`lr_*` restate the host utilities of `Node/Params.lean`, `Host/Stream.lean` and
`Node/TopRec.lean` in this form. New programs:

* `synPush x s`, `synPop x`: push the symbol `s`, drop the top symbol;
* `synIfNE x p q`: `p` if register `x` is nonempty, else `q`;
* `synMulR a b c t₁ t₂`: `c` gains `|a| |b|` ticks (`lr_synMulR`);
* `synMulIn k x t t'`: `x` becomes `k |x|` ticks (`lr_synMulIn`);
* `synDivModR x k q r t₁ t₂ t₃`: `q` gains `|x| / |k|` ticks and the empty `r` ends with
  `|x| mod |k|` ticks, for `|k| ≥ 1` (`lr_synDivModR`);
* `synFieldR x c t`, `synFieldF x c t`: push a unary field of `|x|` ticks with its separator
  `topSep`, reversed (ticks below the separator) or in record order;
* `synMoveUntil src dst mk`: move the symbols of `src` above the first `mk` onto `dst`;
  `synStash pk mk xs`, `synUnstash pk mk xs`: park the registers `xs` on `pk`, each followed by
  the marker `mk`, and restore them (`lr_synStash`, `lr_synUnstash`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg

set_option maxHeartbeats 1000000

/-! ### Registers -/

instance : Fintype TwReg :=
  Fintype.ofList [.src, .dst, .acc, .wn, .rwn, .ad, .rl, .hn, .lh, .x, .tl, .hd, .c, .v, .vp, .f,
    .g, .z, .sg, .as, .t1, .t2, .t3, .t4, .t5, .cy, .st, .pa, .pz, .ps, .pv, .nn, .nm]
    (by intro x; cases x <;> simp)

/-- The persistent registers: the round counter `c` and its spare `t`, the named position `h`,
the parameters `K`, `ℓ`, `b`, `D`, `Lg` (long axes), `N`, `w`, `r`, `lr` (`log₂ r`), the axis
exponents `es`, and the per-round outputs of the record builder: the working width `w2`, the
configuration record `cf` (reversed), the bit stride `kh`, the offset `rh` and the piece record
`pr`. -/
inductive SynP
  | h | c | t | K | ℓ | b | D | Lg | N | w | r | lr | es | w2 | cf | kh | rh | pr
  deriving DecidableEq

instance : Fintype SynP :=
  Fintype.ofList [.h, .c, .t, .K, .ℓ, .b, .D, .Lg, .N, .w, .r, .lr, .es, .w2, .cf, .kh, .rh, .pr]
    (by intro x; cases x <;> simp)

/-- The registers of the transform machines. -/
inductive SynW
  | tw (x : TwReg)
  | ly (i : Fin 24)
  | p (x : SynP)
  | s (i : Fin 32)
  deriving DecidableEq, Fintype

theorem synW_card : Fintype.card SynW ≤ NW := by
  rw [IntegerMultBounds.MathlibTM2.Cost.br_NW_eq]
  exact le_trans (by decide : Fintype.card SynW ≤ 200) (by norm_num)

/-- The wire holding a transform register. -/
noncomputable def synWire (x : SynW) : NWire :=
  wireOf (Fin.castLE synW_card (Fintype.equivFin SynW x))

theorem synWire_inj : Function.Injective synWire := by
  intro x y h
  have h1 := wireOf.injective h
  have h2 := Fin.castLE_injective synW_card h1
  exact (Fintype.equivFin SynW).injective h2

@[simp] theorem synWire_eq_iff {x y : SynW} : synWire x = synWire y ↔ x = y :=
  synWire_inj.eq_iff

/-- The host register of a transform register. -/
noncomputable def sreg (x : SynW) : Fin (nT SXReg) := reg (BReg := SXReg) (.wire (synWire x))

theorem sreg_eq (x : SynW) : sreg x = reg (BReg := SXReg) (.wire (synWire x)) := rfl

theorem sreg_injective : Function.Injective sreg := by
  intro x y h
  simpa [sreg_eq] using h

/-- The twiddle registers. -/
noncomputable def synTg (x : TwReg) : Fin (nT SXReg) := sreg (.tw x)

theorem synTg_injective : Function.Injective synTg := by
  intro x y h
  simpa [synTg, sreg_eq] using h

/-- The layout registers: the interchange bank on the bank `swp 0` of the layer machine, the
others on wires. -/
noncomputable def synLayRg : LayReg 6 → Fin (nT SXReg)
  | .str => sreg (.ly 0)
  | .r0 => sreg (.ly 1)
  | .r1 => sreg (.ly 2)
  | .r2 => sreg (.ly 3)
  | .r3 => sreg (.ly 4)
  | .q0 => sreg (.ly 5)
  | .q1 => sreg (.ly 6)
  | .q2 => sreg (.ly 7)
  | .q3 => sreg (.ly 8)
  | .ctrB => sreg (.ly 9)
  | .cnt => sreg (.ly 10)
  | .tmp => sreg (.ly 11)
  | .st => sreg (.ly 12)
  | .fld => sreg (.ly 13)
  | .mA => sreg (.ly 14)
  | .mB => sreg (.ly 15)
  | .us r => sreg (.ly ⟨16 + r.val, by omega⟩)
  | .sw j => reg (BReg := SXReg) (.bc (.swp 0 j))
  | .cM => sreg (.ly 19)
  | .tM => sreg (.ly 20)
  | .cX => sreg (.ly 21)
  | .tX => sreg (.ly 22)

theorem synLayRg_injective : Function.Injective synLayRg := by
  intro x y h
  cases x <;> cases y <;> simp only [synLayRg, sreg_eq, reg_inj, LReg.wire.injEq,
    synWire_eq_iff, SynW.ly.injEq, LReg.bc.injEq, SXReg.swp.injEq, reduceCtorEq, true_and,
    LayReg.us.injEq, LayReg.sw.injEq] at h ⊢ <;>
    first
    | rfl
    | exact h
    | (simp only [Fin.ext_iff] at h; omega)

theorem synLayRg_sw_injective : Function.Injective fun j => synLayRg (.sw j) :=
  fun _ _ h => by simpa using synLayRg_injective h

/-- Evaluate register updates at register names. -/
macro "synupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj,
  reduceCtorEq, ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.ph.injEq, LReg.lf.injEq,
  LReg.wire.injEq, LReg.bc.injEq, synWire_eq_iff, sreg_eq, SynW.tw.injEq, SynW.ly.injEq, SynW.p.injEq,
  SynW.s.injEq, IntegerMultBounds.MathlibTM2.Node.LReg.k.injEq, Fin.reduceEq, Fin.isValue, synTg, ite_false,
  ite_true]))

/-! ### Run contracts of the host utilities -/

section Kit

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

theorem lr_weaken {p : Pr P T Q A U} {R₀ R₁ R₁' : Fin T → List (Fin (A + 4))} {c c' : ℕ}
    (h : LayRuns body p R₀ R₁ c) (hR : R₁ = R₁') (hc : c ≤ c') : LayRuns body p R₀ R₁' c' :=
  hR ▸ h.mono hc

theorem lr_congr_left {p : Pr P T Q A U} {R₀ R₀' R₁ : Fin T → List (Fin (A + 4))} {c : ℕ}
    (h : LayRuns body p R₀ R₁ c) (hR : R₀' = R₀) : LayRuns body p R₀' R₁ c := hR ▸ h

theorem lr_of_exec {p : Pr P T Q A U} {R₀ R₁ : Fin T → List (Fin (A + 4))} {c : ℕ}
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R₀ → ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body p (mk v S) c (mk v' { S with R := R₁ })) : LayRuns body p R₀ R₁ c := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := h v S hS
  exact ⟨v', c, hu, le_rfl, he⟩

theorem lr_of_exec_le {p : Pr P T Q A U} {R₀ R₁ : Fin T → List (Fin (A + 4))} {c : ℕ}
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R₀ → ∃ (v' : HS T Q A U) (m : ℕ),
      v'.user = v.user ∧ m ≤ c ∧ Exec body p (mk v S) m (mk v' { S with R := R₁ })) :
    LayRuns body p R₀ R₁ c := by
  intro v S _ hS
  exact h v S hS

/-- The empty program. -/
def synSkip : Pr P T Q A U := .act .done

theorem lr_skip (R : Fin T → List (Fin (A + 4))) : LayRuns body synSkip R R 1 :=
  lr_of_exec body fun v S hS => ⟨v, rfl, by
    have := Exec.act (body := body) (Action.done : Act T Q A U) (mk v S)
    rw [run_done] at this
    have hS' : ({ S with R := R } : Stacks T A) = S := by cases S; simp_all
    rw [hS']
    exact this⟩

variable {R : Fin T → List (Fin (A + 4))}

theorem lr_ucopy {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : R t = []) :
    LayRuns body (ucopy a b t) R
      (Function.update R b (List.replicate (R a).length tick ++ R b)) (4 * (R a).length + 4) :=
  lr_of_exec body fun v S hS => by subst hS; exact ucopy_exec body hab hat hbt v S ht

theorem lr_umul (c : ℕ) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ht : R t = []) :
    LayRuns body (umul c a b t) R
      (Function.update R b (List.replicate (c * (R a).length) tick ++ R b))
      (4 * (R a).length + 4) :=
  lr_of_exec body fun v S hS => by subst hS; exact umul_exec body c hab hat hbt v S ht

theorem lr_umulSym (c : ℕ) (y : Fin (A + 4)) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (ht : R t = []) :
    LayRuns body (umulSym c y a b t) R
      (Function.update R b (List.replicate (c * (R a).length) y ++ R b))
      (4 * (R a).length + 4) :=
  lr_of_exec body fun v S hS => by subst hS; exact umulSym_exec body c y hab hat hbt v S ht

theorem lr_usub {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : R t = []) :
    LayRuns body (usub a b t) R (Function.update R b ((R b).drop (R a).length))
      (4 * (R a).length + 4) :=
  lr_of_exec body fun v S hS => by subst hS; exact usub_exec body hab hat hbt v S ht

theorem lr_uclear (a : Fin T) :
    LayRuns body (uclear a) R (Function.update R a []) (2 * (R a).length + 2) :=
  lr_of_exec body fun v S hS => by subst hS; exact uclear_exec body a v S

theorem lr_udiv {c : ℕ} (hc : 1 ≤ c) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ht : R t = []) :
    LayRuns body (udiv c a b t) R
      (Function.update R b (List.replicate ((R a).length / c) tick ++ R b))
      (4 * (R a).length + 4) :=
  lr_of_exec_le body fun v S hS => by subst hS; exact udiv_exec body hc hab hat hbt v S ht

theorem lr_moveR (i j : Fin T) (hij : i ≠ j) (f : Fin (A + 4) → Fin (A + 4)) :
    LayRuns body (moveR i j f) R (movedR R i j f (R i)) (2 * (R i).length + 2) :=
  lr_of_exec body fun v S hS => by subst hS; exact moveR_exec body i j hij f v S

theorem lr_moveR_id {i j : Fin T} (hij : i ≠ j) :
    LayRuns body (moveR i j id) R
      (Function.update (Function.update R i []) j ((R i).reverse ++ R j))
      (2 * (R i).length + 2) := by
  have := lr_moveR body (R := R) i j hij id
  simpa [movedR] using this

theorem lr_upow2 {a b t₁ t₂ : Fin T} (hreg : [a, b, t₁, t₂].Nodup) (ht₁ : R t₁ = [])
    (ht₂ : R t₂ = []) :
    LayRuns body (upow2 a b t₁ t₂) R
      (Function.update R b ((R b).flatMap (List.replicate (2 ^ (R a).length))))
      (4 * (2 ^ (R a).length * (R b).length) + 9 * (R a).length + 4) :=
  lr_of_exec_le body fun v S hS => by subst hS; exact upow2_exec body hreg v S ht₁ ht₂

theorem lr_expProg (G F : ℕ) {uR jR eR t₁ t₂ t₃ : Fin T}
    (hreg : [uR, jR, eR, t₁, t₂, t₃].Nodup) (he : R eR = []) (ht₁ : R t₁ = [])
    (ht₂ : R t₂ = []) (ht₃ : R t₃ = []) :
    LayRuns body (expProg G F uR jR eR t₁ t₂ t₃) R
      (Function.update R eR (List.replicate (expSeq G F (R uR).length (R jR).length) tick))
      (4 * (R uR).length + 2 * (R jR).length + 8 +
        ∑ i ∈ Finset.range (R jR).length, (8 * expSeq G F (R uR).length i + 12)) :=
  lr_of_exec_le body fun v S hS => by subst hS; exact expProg_exec body G F hreg v S he ht₁ ht₂ ht₃

theorem lr_zeroBits {len z t : Fin T} (hlz : len ≠ z) (hlt : len ≠ t) (hzt : z ≠ t)
    (ht : R t = []) :
    LayRuns body (zeroBits len z t) R
      (Function.update R z (binSyms (R len).length 0 ++ R z)) (4 * (R len).length + 4) :=
  lr_of_exec body fun v S hS => by subst hS; exact zeroBits_exec body hlz hlt hzt v S ht

theorem lr_topField {src bk dst : Fin T} (hsb : src ≠ bk) (hsd : src ≠ dst) (hbd : bk ≠ dst)
    (b : Bool) (k : ℕ) (rest : List (Fin (A + 4)))
    (hs : R src = List.replicate k tick ++ topSep :: rest) :
    LayRuns body (topField src bk dst b) R
      (Function.update (Function.update (Function.update R src rest) bk
        (topSep :: List.replicate k tick ++ R bk)) dst
          (if b then List.replicate k tick ++ R dst else R dst)) (2 * k + 3) :=
  lr_of_exec body fun v S hS => by subst hS; exact topField_exec body hsb hsd hbd b k rest v S hs

theorem lr_topSkips {src bk dst : Fin T} (hsb : src ≠ bk) (hsd : src ≠ dst) (hbd : bk ≠ dst)
    (i : ℕ) (l : List ℕ) (rest : List (Fin (A + 4))) (hi : i ≤ l.length)
    (hs : R src = topRec l ++ rest) :
    LayRuns body (topSkips src bk dst i) R
      (Function.update (Function.update R src (topRec (l.drop i) ++ rest)) bk
        ((topRec (l.take i)).reverse ++ R bk))
      (2 * (topRec (l.take i) : List (Fin (A + 4))).length + i + 1) :=
  lr_of_exec body fun v S hS => by subst hS; exact topSkips_exec body hsb hsd hbd i l rest v S hi hs

/-! ### Single actions and branches -/

/-- Push the symbol `s` onto register `x`. -/
def synPush (x : Fin T) (s : Fin (A + 4)) : Pr P T Q A U :=
  .act (.push (.rt x) (fun _ => s) .done)

/-- Drop the top symbol of register `x`. -/
def synPop (x : Fin T) : Pr P T Q A U := .act (.pop (.rt x) (fun v _ => v) .done)

theorem lr_push (x : Fin T) (s : Fin (A + 4)) :
    LayRuns body (synPush x s) R (Function.update R x (s :: R x)) 1 :=
  lr_of_exec body fun v S hS => by
    subst hS
    refine ⟨v, rfl, ?_⟩
    have := Exec.act (body := body) (Action.push (.rt x) (fun _ => s) .done : Act T Q A U)
      (mk v S)
    simp only [Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk] at this
    exact this

theorem lr_pop (x : Fin T) :
    LayRuns body (synPop x) R (Function.update R x (R x).tail) 1 :=
  lr_of_exec body fun v S hS => by
    subst hS
    refine ⟨v, rfl, ?_⟩
    have := Exec.act (body := body) (Action.pop (.rt x) (fun v _ => v) .done : Act T Q A U)
      (mk v S)
    simp only [Action.run, mk_var, mk_stk, get_rt, update_rt, store_mk] at this
    exact this

/-- `p` if register `x` is nonempty, else `q`. -/
def synIfNE (x : Fin T) (p q : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR x)) (.cond (·.flag) p q)

theorem lr_ifNE_pos {x : Fin T} {p q : Pr P T Q A U} {R' : Fin T → List (Fin (A + 4))} {c : ℕ}
    (hx : R x ≠ []) (hp : LayRuns body p R R' c) : LayRuns body (synIfNE x p q) R R' (c + 2) := by
  intro v S hL hS
  have he₁ := Exec.act (body := body) (peekR x : Act T Q A U) (mk v S)
  rw [peekR_run] at he₁
  obtain ⟨v', m, hu, hm, he⟩ := hp { v with flag := (S.R x).head?.isSome } S hL hS
  refine ⟨v', 1 + (m + 1), hu, by omega, Exec.seq he₁ (Exec.cond_true ?_ he)⟩
  rw [hS]
  cases h : R x with
  | nil => exact absurd h hx
  | cons y l => simp

theorem lr_ifNE_neg {x : Fin T} {p q : Pr P T Q A U} {R' : Fin T → List (Fin (A + 4))} {c : ℕ}
    (hx : R x = []) (hq : LayRuns body q R R' c) : LayRuns body (synIfNE x p q) R R' (c + 2) := by
  intro v S hL hS
  have he₁ := Exec.act (body := body) (peekR x : Act T Q A U) (mk v S)
  rw [peekR_run] at he₁
  obtain ⟨v', m, hu, hm, he⟩ := hq { v with flag := (S.R x).head?.isSome } S hL hS
  refine ⟨v', 1 + (m + 1), hu, by omega, Exec.seq he₁ (Exec.cond_false ?_ he)⟩
  rw [hS, hx]
  rfl

/-! ### Compound programs -/

/-- `c` gains `|a| |b|` ticks: `|b|` ticks per symbol of `a` (kept on `t₁`), through `t₂`. -/
def synMulR (a b c t₁ t₂ : Fin T) : Pr P T Q A U := scanP a t₁ (ucopy b c t₂)

/-- The step bound of `synMulR`. -/
def synMulRCost (x y : ℕ) : ℕ := x * (4 * y + 7) + 2 * x + 4

theorem lr_synMulR {a b c t₁ t₂ : Fin T} (hreg : [a, b, c, t₁, t₂].Nodup) (ht₁ : R t₁ = [])
    (ht₂ : R t₂ = []) :
    LayRuns body (synMulR a b c t₁ t₂) R
      (Function.update R c (List.replicate ((R a).length * (R b).length) tick ++ R c))
      (synMulRCost (R a).length (R b).length) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨hab, hac, hat₁, hat₂⟩, ⟨hbc, hbt₁, hbt₂⟩, ⟨hct₁, hct₂⟩, ht₁t₂⟩ := hreg
  set cs := R a with hcs
  set y := (R b).length with hy
  let Φ : ℕ → Fin T → List (Fin (A + 4)) := fun j =>
    Function.update R c (List.replicate (j * y) tick ++ R c)
  have hstep : ∀ j < cs.length, LayRuns body (ucopy b c t₂)
      (Function.update (Function.update (Φ j) a (cs.drop (j + 1))) t₁ (cs.take (j + 1)).reverse)
      (Function.update (Function.update (Φ (j + 1)) a (cs.drop (j + 1))) t₁
        (cs.take (j + 1)).reverse) (4 * y + 4) := by
    intro j _
    refine lr_weaken body (lr_ucopy body hbc hbt₂ hct₂ (by
      simp [Φ, Function.update_of_ne hat₂.symm, Function.update_of_ne ht₁t₂.symm,
        Function.update_of_ne hct₂.symm, ht₂])) ?_ (by
      simp [Φ, Function.update_of_ne hab.symm, Function.update_of_ne hbt₁, Function.update_of_ne hbc,
        hy])
    have e : List.replicate y tick ++ (List.replicate (j * y) tick ++ R c) =
        List.replicate ((j + 1) * y) tick ++ R c := by
      rw [← List.append_assoc, List.replicate_append_replicate]
      congr 2
      ring
    funext k
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all
  have h := layScan_exec hat₁ Φ cs (fun _ => 4 * y + 4) hstep
  refine lr_weaken body (lr_congr_left body h ?_) ?_ ?_
  · funext k
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all
  · funext k
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all
  · simp [synMulRCost]

/-- `x` becomes `k |x|` ticks, through the empty `t` and `t'`. -/
def synMulIn (k : ℕ) (x t t' : Fin T) : Pr P T Q A U :=
  .seq (moveR x t id) (.seq (umul k t x t') (uclear t))

theorem lr_synMulIn (k : ℕ) {x t t' : Fin T} (hreg : [x, t, t'].Nodup) (ht : R t = [])
    (ht' : R t' = []) :
    LayRuns body (synMulIn k x t t') R
      (Function.update R x (List.replicate (k * (R x).length) tick)) (8 * (R x).length + 8) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨hxt, hxt'⟩, htt'⟩ := hreg
  refine lr_weaken body ((lr_moveR_id body (R := R) hxt).seq
    ((lr_umul body k hxt.symm htt' hxt' (by simp [Function.update_of_ne htt'.symm,
      Function.update_of_ne hxt'.symm, ht'])).seq (lr_uclear body t))) ?_ ?_
  · funext j
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simp [Function.update_of_ne hxt.symm, ht]
    omega

/-- One symbol of the dividend: `r` gains a tick; if it reaches `|k|` ticks, `r` is emptied and
`q` gains a tick. -/
def synDivStep (k q r t₂ t₃ : Fin T) : Pr P T Q A U :=
  .seq (synPush r tick) (.seq (ucopy k t₂ t₃) (.seq (usub r t₂ t₃)
    (synIfNE t₂ (uclear t₂) (.seq (uclear r) (synPush q tick)))))

/-- `q` gains `|x| / |k|` ticks and the empty `r` ends with `|x| mod |k|` ticks; `x` is kept on
`t₁` and restored. -/
def synDivModR (x k q r t₁ t₂ t₃ : Fin T) : Pr P T Q A U := scanP x t₁ (synDivStep k q r t₂ t₃)

/-- The step bound of `synDivModR`. -/
def synDivModCost (x K : ℕ) : ℕ := x * (10 * K + 17) + 2 * x + 4

theorem lr_synDivModR {x k q r t₁ t₂ t₃ : Fin T} (hreg : [x, k, q, r, t₁, t₂, t₃].Nodup)
    (hk : 1 ≤ (R k).length) (hr : R r = []) (ht₁ : R t₁ = []) (ht₂ : R t₂ = [])
    (ht₃ : R t₃ = []) :
    LayRuns body (synDivModR x k q r t₁ t₂ t₃) R
      (Function.update (Function.update R r (List.replicate ((R x).length % (R k).length) tick)) q
        (List.replicate ((R x).length / (R k).length) tick ++ R q))
      (synDivModCost (R x).length (R k).length) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg
  obtain ⟨⟨hxk, hxq, hxr, hxt₁, hxt₂, hxt₃⟩, ⟨hkq, hkr, hkt₁, hkt₂, hkt₃⟩, ⟨hqr, hqt₁, hqt₂, hqt₃⟩,
    ⟨hrt₁, hrt₂, hrt₃⟩, ⟨ht₁t₂, ht₁t₃⟩, ht₂t₃⟩ := hreg
  set cs := R x with hcs
  set K := (R k).length with hK
  let Φ : ℕ → Fin T → List (Fin (A + 4)) := fun j =>
    Function.update (Function.update R r (List.replicate (j % K) tick)) q
      (List.replicate (j / K) tick ++ R q)
  have hstep : ∀ j < cs.length, LayRuns body (synDivStep k q r t₂ t₃)
      (Function.update (Function.update (Φ j) x (cs.drop (j + 1))) t₁ (cs.take (j + 1)).reverse)
      (Function.update (Function.update (Φ (j + 1)) x (cs.drop (j + 1))) t₁
        (cs.take (j + 1)).reverse) (10 * K + 14) := by
    intro j _
    set R₀ := Function.update (Function.update (Φ j) x (cs.drop (j + 1))) t₁
      (cs.take (j + 1)).reverse with hR₀
    have hjK : j % K < K := Nat.mod_lt _ (by omega)
    have e0 : R₀ r = List.replicate (j % K) tick := by
      simp [hR₀, Φ, Function.update_of_ne hrt₁, Function.update_of_ne hxr.symm,
        Function.update_of_ne hqr.symm]
    have ek : R₀ k = R k := by
      simp [hR₀, Φ, Function.update_of_ne hkt₁, Function.update_of_ne hxk.symm,
        Function.update_of_ne hkq, Function.update_of_ne hkr]
    have et₂ : R₀ t₂ = [] := by
      simp [hR₀, Φ, Function.update_of_ne ht₁t₂.symm, Function.update_of_ne hxt₂.symm,
        Function.update_of_ne hqt₂.symm, Function.update_of_ne hrt₂.symm, ht₂]
    have et₃ : R₀ t₃ = [] := by
      simp [hR₀, Φ, Function.update_of_ne ht₁t₃.symm, Function.update_of_ne hxt₃.symm,
        Function.update_of_ne hqt₃.symm, Function.update_of_ne hrt₃.symm, ht₃]
    have h1 := lr_push body (R := R₀) r tick
    set R₁ := Function.update R₀ r (tick :: R₀ r) with hR₁
    have h2 := lr_ucopy body (R := R₁) hkt₂ hkt₃ ht₂t₃ (by
      simp [hR₁, Function.update_of_ne hrt₃.symm, et₃])
    have ek₁ : R₁ k = R k := by simp [hR₁, Function.update_of_ne hkr, ek]
    rw [ek₁] at h2
    set R₂ := Function.update R₁ t₂ (List.replicate K tick ++ R₁ t₂) with hR₂
    have h3 := lr_usub body (R := R₂) hrt₂ hrt₃ ht₂t₃ (by
      simp [hR₂, hR₁, Function.update_of_ne ht₂t₃.symm, Function.update_of_ne hrt₃.symm, et₃])
    have er₂ : R₂ r = List.replicate (j % K + 1) tick := by
      simp [hR₂, hR₁, Function.update_apply, hrt₂, e0, List.replicate_succ]
    have et₂' : R₂ t₂ = List.replicate K tick := by
      simp [hR₂, hR₁, hrt₂.symm, et₂]
    rw [er₂, et₂', List.length_replicate, List.drop_replicate] at h3
    set R₃ := Function.update R₂ t₂ (List.replicate (K - (j % K + 1)) tick) with hR₃
    by_cases hlt : j % K + 1 < K
    · have hne : R₃ t₂ ≠ [] := by
        simp [hR₃]; omega
      have h4 := lr_ifNE_pos body (q := .seq (uclear r) (synPush q tick)) hne
        (lr_uclear body (R := R₃) t₂)
      refine lr_weaken body (h1.seq (h2.seq (h3.seq h4))) ?_ ?_
      · have hm : (j + 1) % K = j % K + 1 := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < K by omega)]
          exact Nat.mod_eq_of_lt hlt
        have hd : (j + 1) / K = j / K := by
          have h1 := Nat.div_add_mod j K
          have h2 := Nat.div_add_mod (j + 1) K
          rw [hm] at h2
          have : K * ((j + 1) / K) = K * (j / K) := by omega
          exact Nat.eq_of_mul_eq_mul_left (by omega) this
        clear h1 h2 h3 h4
        funext z
        simp only [hR₃, hR₂, hR₁, hR₀, Φ, Function.update_apply, hm, hd]
        clear hm hd hlt hne hjK
        split_ifs <;> simp_all [List.replicate_succ]
      · simp only [hR₃, Function.update_self, List.length_replicate, 
          ]
        omega
    · have hKe : j % K + 1 = K := by omega
      have he : R₃ t₂ = [] := by simp [hR₃]; omega
      have h4 := lr_ifNE_neg body (p := uclear t₂) he
        ((lr_uclear body (R := R₃) r).seq (lr_push body q tick))
      refine lr_weaken body (h1.seq (h2.seq (h3.seq h4))) ?_ ?_
      · have hm : (j + 1) % K = 0 := by
          have := Nat.div_add_mod j K
          rw [show j + 1 = K * (j / K + 1) by rw [Nat.mul_add, Nat.mul_one]; omega]
          exact Nat.mul_mod_right _ _
        have hd : (j + 1) / K = j / K + 1 := by
          rw [show j + 1 = K * (j / K + 1) by
            have := Nat.div_add_mod j K
            rw [Nat.mul_add, Nat.mul_one]; omega]
          exact Nat.mul_div_cancel_left _ (by omega)
        have hK0 : K - (j % K + 1) = 0 := by omega
        clear h1 h2 h3 h4
        funext z
        simp only [hR₃, hR₂, hR₁, hR₀, Φ, Function.update_apply, hm, hd, hK0]
        clear hm hd hlt he hjK hKe hK0
        split_ifs <;> simp_all [List.replicate_succ]
      · have er₃ : (R₃ r).length = j % K + 1 := by
          rw [hR₃, Function.update_of_ne hrt₂, er₂, List.length_replicate]
        rw [er₃]
        omega
  have h := layScan_exec hxt₁ Φ cs (fun _ => 10 * K + 14) hstep
  refine lr_weaken body (lr_congr_left body h ?_) ?_ ?_
  · funext z
    simp only [Φ, Function.update_apply, Nat.zero_mod, Nat.zero_div]
    split_ifs <;> simp_all
  · funext z
    simp only [Φ, Function.update_apply]
    split_ifs <;> simp_all
  · simp [synDivModCost]

/-- Push a unary field of `|x|` ticks and then its separator onto `c` (the field reversed). -/
def synFieldR (x c t : Fin T) : Pr P T Q A U := .seq (ucopy x c t) (synPush c topSep)

/-- Push a separator and then a unary field of `|x|` ticks onto `c` (record order). -/
def synFieldF (x c t : Fin T) : Pr P T Q A U := .seq (synPush c topSep) (ucopy x c t)

theorem lr_synFieldR {x c t : Fin T} (hxc : x ≠ c) (hxt : x ≠ t) (hct : c ≠ t) (ht : R t = []) :
    LayRuns body (synFieldR x c t) R
      (Function.update R c (topSep :: (List.replicate (R x).length tick ++ R c)))
      (4 * (R x).length + 5) :=
  lr_weaken body ((lr_ucopy body hxc hxt hct ht).seq (lr_push body c topSep))
    (by funext z; simp only [Function.update_apply]; split_ifs <;> simp_all) (by simp)

theorem lr_synFieldF {x c t : Fin T} (hxc : x ≠ c) (hxt : x ≠ t) (hct : c ≠ t) (ht : R t = []) :
    LayRuns body (synFieldF x c t) R
      (Function.update R c (List.replicate (R x).length tick ++ topSep :: R c))
      (4 * (R x).length + 5) :=
  lr_weaken body ((lr_push body c topSep).seq (lr_ucopy body hxc hxt hct
      (by simp [Function.update_of_ne hct.symm, ht])))
    (by funext z; simp only [Function.update_apply]; split_ifs <;> simp_all)
    (by simp [Function.update_of_ne hxc]; omega)

/-! ### Moving up to a marker; parking registers -/

/-- Record in `flag` whether `src` has a top symbol other than `mkr`. -/
def synPeekNe (src : Fin T) (mkr : Fin (A + 4)) : Act T Q A U :=
  .peek (.rt src) (fun v o => { v with flag := decide (o ≠ none ∧ o ≠ some mkr) }) .done

/-- Move the top symbol of `src` onto `dst`, then test the next one. -/
def synMvStep (src dst : Fin T) (mkr : Fin (A + 4)) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.push (.rt dst) (fun v => v.sym.getD blank) (synPeekNe src mkr))

/-- Move the symbols of `src` above the first `mkr` onto `dst` (reversing them). -/
def synMoveUntil (src dst : Fin T) (mkr : Fin (A + 4)) : Pr P T Q A U :=
  .seq (.act (synPeekNe src mkr)) (.loop (·.flag) (.act (synMvStep src dst mkr)))

lemma syn_flag_top (mkr : Fin (A + 4)) (l rest : List (Fin (A + 4))) (hl : mkr ∉ l) :
    decide ((l ++ mkr :: rest).head? ≠ none ∧ (l ++ mkr :: rest).head? ≠ some mkr) =
      decide (l ≠ []) := by
  cases l with
  | nil => simp
  | cons y l =>
      have : y ≠ mkr := fun h => hl (by simp [h])
      simp [this]

theorem synMoveUntil_loop {src dst : Fin T} (hsd : src ≠ dst) (mkr : Fin (A + 4))
    (rest : List (Fin (A + 4))) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.R src = l ++ mkr :: rest → mkr ∉ l → v.flag = decide (l ≠ []) →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (synMvStep src dst mkr))) (mk v S) (2 * l.length + 1)
          (mk v' { S with
            R := Function.update (Function.update S.R src (mkr :: rest)) dst
              (l.reverse ++ S.R dst) }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS _ hf
      refine ⟨v, rfl, ?_⟩
      have hR : ({ S with
          R := Function.update (Function.update S.R src (mkr :: rest)) dst
            ([].reverse ++ S.R dst) } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS ⊢
          congr 1
          funext j
          simp only [Function.update_apply, List.reverse_nil, List.nil_append]
          split_ifs with h1 h2 <;> simp_all
      rw [hR]
      exact .loop_false (by simpa using hf)
  | cons x l ih =>
      intro v S hS hm hf
      have hx : x ≠ mkr := fun h => hm (by simp [h])
      have hm' : mkr ∉ l := fun h => hm (by simp [h])
      have hrun : (synMvStep src dst mkr : Act T Q A U).run (mk v S) =
          mk { v with sym := some x, flag := decide (l ≠ []) }
            { S with
              R := Function.update (Function.update S.R src (l ++ mkr :: rest)) dst
                (x :: S.R dst) } := by
        have := syn_flag_top mkr l rest hm'
        simp only [synMvStep, synPeekNe, Action.run, mk_var, mk_stk, get_rt, hS,
          List.cons_append, List.head?_cons, List.tail_cons, update_rt, store_mk,
          Function.update_of_ne hsd.symm, Option.getD_some]
        simp only [Function.update_apply, ite_eq_right hsd, ↓reduceIte] at this ⊢
        rw [this]
      obtain ⟨v', hu, he⟩ := ih { v with sym := some x, flag := decide (l ≠ []) }
        { S with
          R := Function.update (Function.update S.R src (l ++ mkr :: rest)) dst
            (x :: S.R dst) }
        (by simp [Function.update_of_ne hsd]) hm' rfl
      refine ⟨v', hu, ?_⟩
      have he₁ := Exec.act (body := body) (synMvStep src dst mkr : Act T Q A U) (mk v S)
      rw [hrun] at he₁
      have := Exec.loop_true (f := (·.flag)) (by simpa using hf) he₁ he
      refine Exec.cast this (by simp; ring) ?_
      congr 2
      funext j
      simp only [Function.update_apply]
      split_ifs <;> simp_all

theorem lr_synMoveUntil {src dst : Fin T} (hsd : src ≠ dst) (mkr : Fin (A + 4))
    (l rest : List (Fin (A + 4))) (hS : R src = l ++ mkr :: rest) (hm : mkr ∉ l) :
    LayRuns body (synMoveUntil src dst mkr) R
      (Function.update (Function.update R src (mkr :: rest)) dst (l.reverse ++ R dst))
      (2 * l.length + 2) :=
  lr_of_exec body fun v S hR => by
    subst hR
    have he₁ := Exec.act (body := body) (synPeekNe src mkr : Act T Q A U) (mk v S)
    have hrun : (synPeekNe src mkr : Act T Q A U).run (mk v S) =
        mk { v with flag := decide (l ≠ []) } S := by
      simp only [synPeekNe, Action.run, mk_var, mk_stk, get_rt, hS]
      rw [syn_flag_top mkr l rest hm]
      rfl
    rw [hrun] at he₁
    obtain ⟨v', hu, he⟩ := synMoveUntil_loop body hsd mkr rest l
      { v with flag := decide (l ≠ []) } S hS hm rfl
    exact ⟨v', hu, Exec.cast (Exec.seq he₁ he) (by ring) rfl⟩

/-- Park the registers `xs` on `pk`, in order, each followed by the marker `mkr`. -/
def synStashL (pk : Fin T) (mkr : Fin (A + 4)) : List (Fin T) → Pr P T Q A U
  | [] => synSkip
  | x :: xs => .seq (moveR x pk id) (.seq (synPush pk mkr) (synStashL pk mkr xs))

/-- Push the marker `mkr` and park the registers `xs`. -/
def synStash (pk : Fin T) (mkr : Fin (A + 4)) (xs : List (Fin T)) : Pr P T Q A U :=
  .seq (synPush pk mkr) (synStashL pk mkr xs)

/-- Restore the registers `xs` parked by `synStashL`, the last one first. -/
def synUnstashL (pk : Fin T) (mkr : Fin (A + 4)) : List (Fin T) → Pr P T Q A U
  | [] => synSkip
  | x :: xs => .seq (synUnstashL pk mkr xs) (.seq (synPop pk) (synMoveUntil pk x mkr))

/-- Restore the registers parked by `synStash` and drop the first marker. -/
def synUnstash (pk : Fin T) (mkr : Fin (A + 4)) (xs : List (Fin T)) : Pr P T Q A U :=
  .seq (synUnstashL pk mkr xs) (synPop pk)

/-- The parked contents of the registers `xs` of the file `R`, the last register on top. -/
def synStk (R : Fin T → List (Fin (A + 4))) (mkr : Fin (A + 4)) : List (Fin T) → List (Fin (A + 4))
  | [] => []
  | x :: xs => synStk R mkr xs ++ mkr :: (R x).reverse

/-- The file `R` with the registers `xs` emptied. -/
def synClr (R : Fin T → List (Fin (A + 4))) (xs : List (Fin T)) : Fin T → List (Fin (A + 4)) :=
  fun k => if k ∈ xs then [] else R k

/-- The step bound of parking or restoring `xs`. -/
def synStashCost (R : Fin T → List (Fin (A + 4))) : List (Fin T) → ℕ
  | [] => 1
  | x :: xs => 2 * (R x).length + 3 + synStashCost R xs

lemma synStk_congr {R R' : Fin T → List (Fin (A + 4))} (mkr : Fin (A + 4)) :
    ∀ xs : List (Fin T), (∀ x ∈ xs, R' x = R x) → synStk R' mkr xs = synStk R mkr xs
  | [], _ => rfl
  | x :: xs, h => by
      simp only [synStk, h x (by simp), synStk_congr mkr xs fun y hy => h y (by simp [hy])]

lemma synStashCost_congr {R R' : Fin T → List (Fin (A + 4))} :
    ∀ xs : List (Fin T), (∀ x ∈ xs, R' x = R x) → synStashCost R' xs = synStashCost R xs
  | [], _ => rfl
  | x :: xs, h => by
      simp only [synStashCost, h x (by simp), synStashCost_congr xs fun y hy => h y (by simp [hy])]

theorem lr_synStashL {pk : Fin T} (mkr : Fin (A + 4)) :
    ∀ (xs : List (Fin T)) (R : Fin T → List (Fin (A + 4))), xs.Nodup → pk ∉ xs →
      LayRuns body (synStashL pk mkr xs) R
        (Function.update (synClr R xs) pk (synStk R mkr xs ++ R pk)) (synStashCost R xs)
  | [], R, _, _ => lr_weaken body (lr_skip body R)
      (by funext k; simp [synClr, synStk, Function.update_apply]; intro h; rw [h]) le_rfl
  | x :: xs, R, hd, hpk => by
      rw [List.nodup_cons] at hd
      have hxp : x ≠ pk := fun h => hpk (by simp [h])
      have hpk' : pk ∉ xs := fun h => hpk (by simp [h])
      have h1 := lr_moveR_id body (R := R) hxp
      have h2 := lr_push body (R := Function.update (Function.update R x []) pk
        ((R x).reverse ++ R pk)) pk mkr
      have h3 := lr_synStashL mkr xs (Function.update (Function.update (Function.update R x []) pk
        ((R x).reverse ++ R pk)) pk (mkr :: Function.update (Function.update R x []) pk
          ((R x).reverse ++ R pk) pk)) hd.2 hpk'
      have hag : ∀ y ∈ xs, Function.update (Function.update (Function.update R x []) pk
          ((R x).reverse ++ R pk)) pk (mkr :: Function.update (Function.update R x []) pk
            ((R x).reverse ++ R pk) pk) y = R y := by
        intro y hy
        have hyx : y ≠ x := fun h => hd.1 (h ▸ hy)
        have hyp : y ≠ pk := fun h => hpk' (h ▸ hy)
        simp [hyx, hyp]
      rw [synStk_congr mkr xs hag, synStashCost_congr xs hag] at h3
      refine lr_weaken body (h1.seq (h2.seq h3)) ?_ ?_
      · funext k
        simp only [synClr, synStk, Function.update_apply, List.mem_cons]
        by_cases hk : k = pk
        · subst hk; simp
        · by_cases hkx : k = x
          · subst hkx; simp [hk]
          · simp [hk, hkx]
      · simp [synStashCost]; omega

theorem lr_synStash {pk : Fin T} (mkr : Fin (A + 4)) (xs : List (Fin T)) (hd : xs.Nodup)
    (hpk : pk ∉ xs) :
    LayRuns body (synStash pk mkr xs) R
      (Function.update (synClr R xs) pk (synStk R mkr xs ++ mkr :: R pk))
      (synStashCost R xs + 1) := by
  have h2 := lr_synStashL body mkr xs (Function.update R pk (mkr :: R pk)) hd hpk
  have hag : ∀ y ∈ xs, Function.update R pk (mkr :: R pk) y = R y := by
    intro y hy
    have hyp : y ≠ pk := fun h => hpk (h ▸ hy)
    simp [hyp]
  rw [synStk_congr mkr xs hag, synStashCost_congr xs hag] at h2
  refine lr_weaken body ((lr_push body pk mkr).seq h2) ?_ (by omega)
  funext k
  simp only [synClr, Function.update_apply]
  split_ifs <;> simp_all

theorem lr_synUnstashL {pk : Fin T} (mkr : Fin (A + 4)) :
    ∀ (xs : List (Fin T)) (R : Fin T → List (Fin (A + 4))) (P₀ : List (Fin (A + 4))),
      xs.Nodup → pk ∉ xs → (∀ x ∈ xs, mkr ∉ R x) →
      LayRuns body (synUnstashL pk mkr xs)
        (Function.update (synClr R xs) pk (synStk R mkr xs ++ mkr :: P₀))
        (Function.update R pk (mkr :: P₀)) (synStashCost R xs)
  | [], R, P₀, _, _, _ => lr_weaken body (lr_skip body _)
      (by funext k; simp [synClr, synStk, Function.update_apply]) le_rfl
  | x :: xs, R, P₀, hd, hpk, hmk => by
      rw [List.nodup_cons] at hd
      have hxp : x ≠ pk := fun h => hpk (by simp [h])
      have hpk' : pk ∉ xs := fun h => hpk (by simp [h])
      have hmx : mkr ∉ R x := hmk x (by simp)
      have h1 := lr_synUnstashL mkr xs (Function.update R x []) ((R x).reverse ++ mkr :: P₀)
        hd.2 hpk' (fun y hy => by
          have hyx : y ≠ x := fun h => hd.1 (h ▸ hy)
          simp only [Function.update_of_ne hyx]
          exact hmk y (by simp [hy]))
      have hag : ∀ y ∈ xs, Function.update R x [] y = R y := by
        intro y hy
        have hyx : y ≠ x := fun h => hd.1 (h ▸ hy)
        simp [Function.update_of_ne hyx]
      rw [synStk_congr mkr xs hag, synStashCost_congr xs hag] at h1
      have h2 := lr_pop body (R := Function.update (Function.update R x []) pk
        (mkr :: ((R x).reverse ++ mkr :: P₀))) pk
      have h3 := lr_synMoveUntil body (R := Function.update (Function.update
        (Function.update R x []) pk (mkr :: ((R x).reverse ++ mkr :: P₀))) pk
          (Function.update (Function.update R x []) pk (mkr :: ((R x).reverse ++ mkr :: P₀))
            pk).tail) hxp.symm mkr (R x).reverse P₀ (by simp) (by simpa using hmx)
      have hstart : Function.update (synClr R (x :: xs)) pk (synStk R mkr (x :: xs) ++ mkr :: P₀) =
          Function.update (synClr (Function.update R x []) xs) pk
            (synStk R mkr xs ++ mkr :: ((R x).reverse ++ mkr :: P₀)) := by
        funext k
        simp only [synClr, synStk, Function.update_apply, List.mem_cons, List.append_assoc,
          List.cons_append]
        by_cases hk : k = pk
        · simp [hk]
        · by_cases hkx : k = x
          · subst hkx; simp [hk]
          · simp [hk, hkx]
      refine lr_weaken body (lr_congr_left body (h1.seq (h2.seq h3)) hstart) ?_ ?_
      · funext k
        simp only [Function.update_apply]
        by_cases hk : k = pk
        · subst hk; simp [hxp.symm]
        · by_cases hkx : k = x
          · subst hkx; simp [hk]
          · simp [hk, hkx]
      · simp [synStashCost]; omega

theorem lr_synUnstash {pk : Fin T} (mkr : Fin (A + 4)) (xs : List (Fin T))
    (P₀ : List (Fin (A + 4))) (hd : xs.Nodup) (hpk : pk ∉ xs) (hmk : ∀ x ∈ xs, mkr ∉ R x) :
    LayRuns body (synUnstash pk mkr xs)
      (Function.update (synClr R xs) pk (synStk R mkr xs ++ mkr :: P₀))
      (Function.update R pk P₀) (synStashCost R xs + 1) :=
  lr_weaken body ((lr_synUnstashL body mkr xs R P₀ hd hpk hmk).seq (lr_pop body pk))
    (by funext k; simp only [Function.update_apply]; split_ifs <;> simp_all) le_rfl

end Kit

/-! ### Register files with the transform wires as a function of their names -/

section Wires

variable {Q A : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q A U)

/-- The file `R` with every transform wire `sreg x` replaced by `v x`. -/
noncomputable def synG (R : Fin (nT SXReg) → List (Fin (A + 4))) (v : SynW → List (Fin (A + 4))) :
    Fin (nT SXReg) → List (Fin (A + 4)) :=
  fun z => if h : ∃ x, sreg x = z then v h.choose else R z

variable {R : Fin (nT SXReg) → List (Fin (A + 4))} {v : SynW → List (Fin (A + 4))}

@[simp] theorem synG_sreg (x : SynW) : synG R v (sreg x) = v x := by
  have h : ∃ y, sreg y = sreg x := ⟨x, rfl⟩
  simp only [synG, dite_eq_left h]
  congr
  exact sreg_injective h.choose_spec

theorem synG_of_ne {z : Fin (nT SXReg)} (hz : ∀ x, sreg x ≠ z) : synG R v z = R z := by
  have : ¬ ∃ x, sreg x = z := fun ⟨x, hx⟩ => hz x hx
  simp only [synG, dite_eq_right this]

theorem synG_update (x : SynW) (l : List (Fin (A + 4))) :
    Function.update (synG R v) (sreg x) l = synG R (Function.update v x l) := by
  funext z
  by_cases hz : ∃ y, sreg y = z
  · obtain ⟨y, rfl⟩ := hz
    simp only [synG_sreg, Function.update_apply, sreg_injective.eq_iff]
  · have hz' : ∀ y, sreg y ≠ z := fun y hy => hz ⟨y, hy⟩
    rw [synG_of_ne hz', Function.update_of_ne (hz' x).symm, synG_of_ne hz']

theorem synG_update_out {z : Fin (nT SXReg)} (hz : ∀ x, sreg x ≠ z) (l : List (Fin (A + 4))) :
    Function.update (synG R v) z l = synG (Function.update R z l) v := by
  funext y
  by_cases hy : ∃ x, sreg x = y
  · obtain ⟨x, rfl⟩ := hy
    rw [Function.update_of_ne (hz x), synG_sreg, synG_sreg]
  · have hy' : ∀ x, sreg x ≠ y := fun x hx => hy ⟨x, hx⟩
    rw [synG_of_ne hy']
    by_cases hyz : y = z
    · subst hyz; simp
    · rw [Function.update_of_ne hyz, Function.update_of_ne hyz, synG_of_ne hy']

theorem sreg_ne_reg {x : SynW} {y : LReg SXReg} (hy : ∀ v, y ≠ .wire v) : sreg x ≠ reg y := by
  rw [sreg_eq]; intro h; exact hy _ (reg_injective h).symm

/-! Contracts on the transform wires. -/

variable {a b c t t₁ t₂ t₃ : SynW}

theorem sg_ucopy (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : v t = []) :
    LayRuns body (ucopy (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (List.replicate (v a).length tick ++ v b)))
      (4 * (v a).length + 4) :=
  lr_weaken body (lr_ucopy body (sreg_injective.ne hab) (sreg_injective.ne hat)
    (sreg_injective.ne hbt) (by simpa using ht)) (by rw [synG_update, synG_sreg, synG_sreg])
    (by simp)

theorem sg_umul (k : ℕ) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : v t = []) :
    LayRuns body (umul k (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (List.replicate (k * (v a).length) tick ++ v b)))
      (4 * (v a).length + 4) :=
  lr_weaken body (lr_umul body k (sreg_injective.ne hab) (sreg_injective.ne hat)
    (sreg_injective.ne hbt) (by simpa using ht)) (by rw [synG_update, synG_sreg, synG_sreg])
    (by simp)

theorem sg_umulSym (k : ℕ) (y : Fin (A + 4)) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ht : v t = []) :
    LayRuns body (umulSym k y (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (List.replicate (k * (v a).length) y ++ v b)))
      (4 * (v a).length + 4) :=
  lr_weaken body (lr_umulSym body k y (sreg_injective.ne hab) (sreg_injective.ne hat)
    (sreg_injective.ne hbt) (by simpa using ht)) (by rw [synG_update, synG_sreg, synG_sreg])
    (by simp)

theorem sg_usub (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : v t = []) :
    LayRuns body (usub (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b ((v b).drop (v a).length))) (4 * (v a).length + 4) :=
  lr_weaken body (lr_usub body (sreg_injective.ne hab) (sreg_injective.ne hat)
    (sreg_injective.ne hbt) (by simpa using ht)) (by rw [synG_update, synG_sreg, synG_sreg])
    (by simp)

theorem sg_uclear (a : SynW) :
    LayRuns body (uclear (sreg a)) (synG R v) (synG R (Function.update v a []))
      (2 * (v a).length + 2) :=
  lr_weaken body (lr_uclear body (sreg a)) (by rw [synG_update]) (by simp)

theorem sg_udiv {k : ℕ} (hk : 1 ≤ k) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : v t = []) :
    LayRuns body (udiv k (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (List.replicate ((v a).length / k) tick ++ v b)))
      (4 * (v a).length + 4) :=
  lr_weaken body (lr_udiv body hk (sreg_injective.ne hab) (sreg_injective.ne hat)
    (sreg_injective.ne hbt) (by simpa using ht)) (by rw [synG_update, synG_sreg, synG_sreg])
    (by simp)

theorem sg_moveR (hab : a ≠ b) :
    LayRuns body (moveR (sreg a) (sreg b) id) (synG R v)
      (synG R (Function.update (Function.update v a []) b ((v a).reverse ++ v b)))
      (2 * (v a).length + 2) :=
  lr_weaken body (lr_moveR_id body (sreg_injective.ne hab))
    (by rw [synG_update, synG_sreg, synG_update, synG_sreg])
    (by simp)

theorem sg_push (a : SynW) (y : Fin (A + 4)) :
    LayRuns body (synPush (sreg a) y) (synG R v) (synG R (Function.update v a (y :: v a))) 1 :=
  lr_weaken body (lr_push body (sreg a) y) (by rw [synG_update, synG_sreg]) le_rfl

theorem sg_pop (a : SynW) :
    LayRuns body (synPop (sreg a)) (synG R v) (synG R (Function.update v a (v a).tail)) 1 :=
  lr_weaken body (lr_pop body (sreg a)) (by rw [synG_update, synG_sreg]) le_rfl

theorem sg_upow2 (hreg : [a, b, t₁, t₂].Nodup) (ht₁ : v t₁ = []) (ht₂ : v t₂ = []) :
    LayRuns body (upow2 (sreg a) (sreg b) (sreg t₁) (sreg t₂)) (synG R v)
      (synG R (Function.update v b ((v b).flatMap (List.replicate (2 ^ (v a).length)))))
      (4 * (2 ^ (v a).length * (v b).length) + 9 * (v a).length + 4) := by
  have hreg' : [sreg a, sreg b, sreg t₁, sreg t₂].Nodup := by
    simpa [List.nodup_cons, sreg_injective.eq_iff] using hreg
  exact lr_weaken body (lr_upow2 body hreg' (by simpa using ht₁) (by simpa using ht₂))
    (by rw [synG_update, synG_sreg, synG_sreg]) (by simp)

theorem sg_expProg (G F : ℕ) {uR jR eR : SynW} (hreg : [uR, jR, eR, t₁, t₂, t₃].Nodup)
    (he : v eR = []) (ht₁ : v t₁ = []) (ht₂ : v t₂ = []) (ht₃ : v t₃ = []) :
    LayRuns body (expProg G F (sreg uR) (sreg jR) (sreg eR) (sreg t₁) (sreg t₂) (sreg t₃))
      (synG R v)
      (synG R (Function.update v eR
        (List.replicate (expSeq G F (v uR).length (v jR).length) tick)))
      (4 * (v uR).length + 2 * (v jR).length + 8 +
        ∑ i ∈ Finset.range (v jR).length, (8 * expSeq G F (v uR).length i + 12)) := by
  have hreg' : [sreg uR, sreg jR, sreg eR, sreg t₁, sreg t₂, sreg t₃].Nodup := by
    simpa [List.nodup_cons, sreg_injective.eq_iff] using hreg
  exact lr_weaken body (lr_expProg body G F hreg' (by simpa using he) (by simpa using ht₁)
    (by simpa using ht₂) (by simpa using ht₃)) (by rw [synG_update, synG_sreg, synG_sreg])
    (by simp)

theorem sg_zeroBits (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : v t = []) :
    LayRuns body (zeroBits (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (binSyms (v a).length 0 ++ v b))) (4 * (v a).length + 4) :=
  lr_weaken body (lr_zeroBits body (sreg_injective.ne hab) (sreg_injective.ne hat)
    (sreg_injective.ne hbt) (by simpa using ht)) (by rw [synG_update, synG_sreg, synG_sreg])
    (by simp)

theorem sg_synMulR (hreg : [a, b, c, t₁, t₂].Nodup) (ht₁ : v t₁ = []) (ht₂ : v t₂ = []) :
    LayRuns body (synMulR (sreg a) (sreg b) (sreg c) (sreg t₁) (sreg t₂)) (synG R v)
      (synG R (Function.update v c (List.replicate ((v a).length * (v b).length) tick ++ v c)))
      (synMulRCost (v a).length (v b).length) := by
  have hreg' : [sreg a, sreg b, sreg c, sreg t₁, sreg t₂].Nodup := by
    simpa [List.nodup_cons, sreg_injective.eq_iff] using hreg
  exact lr_weaken body (lr_synMulR body hreg' (by simpa using ht₁) (by simpa using ht₂))
    (by rw [synG_update, synG_sreg, synG_sreg, synG_sreg]) (by simp)

theorem sg_synMulIn (k : ℕ) (hreg : [a, t, t₁].Nodup) (ht : v t = []) (ht₁ : v t₁ = []) :
    LayRuns body (synMulIn k (sreg a) (sreg t) (sreg t₁)) (synG R v)
      (synG R (Function.update v a (List.replicate (k * (v a).length) tick)))
      (8 * (v a).length + 8) := by
  have hreg' : [sreg a, sreg t, sreg t₁].Nodup := by
    simpa [List.nodup_cons, sreg_injective.eq_iff] using hreg
  exact lr_weaken body (lr_synMulIn body k hreg' (by simpa using ht) (by simpa using ht₁))
    (by rw [synG_update, synG_sreg]) (by simp)

theorem sg_synDivModR {x k q r : SynW} (hreg : [x, k, q, r, t₁, t₂, t₃].Nodup)
    (hk : 1 ≤ (v k).length) (hr : v r = []) (ht₁ : v t₁ = []) (ht₂ : v t₂ = [])
    (ht₃ : v t₃ = []) :
    LayRuns body (synDivModR (sreg x) (sreg k) (sreg q) (sreg r) (sreg t₁) (sreg t₂) (sreg t₃))
      (synG R v)
      (synG R (Function.update (Function.update v r
        (List.replicate ((v x).length % (v k).length) tick)) q
          (List.replicate ((v x).length / (v k).length) tick ++ v q)))
      (synDivModCost (v x).length (v k).length) := by
  have hreg' : [sreg x, sreg k, sreg q, sreg r, sreg t₁, sreg t₂, sreg t₃].Nodup := by
    simpa [List.nodup_cons, sreg_injective.eq_iff] using hreg
  exact lr_weaken body (lr_synDivModR body hreg' (by simpa using hk) (by simpa using hr)
    (by simpa using ht₁) (by simpa using ht₂) (by simpa using ht₃))
    (by rw [synG_update, synG_update, synG_sreg, synG_sreg, synG_sreg]) (by simp)

theorem sg_synFieldR (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : v t = []) :
    LayRuns body (synFieldR (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (topSep :: (List.replicate (v a).length tick ++ v b))))
      (4 * (v a).length + 5) :=
  lr_weaken body (lr_synFieldR body (sreg_injective.ne hab) (sreg_injective.ne hat)
    (sreg_injective.ne hbt) (by simpa using ht)) (by rw [synG_update, synG_sreg, synG_sreg])
    (by simp)

theorem sg_synFieldF (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : v t = []) :
    LayRuns body (synFieldF (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (List.replicate (v a).length tick ++ topSep :: v b)))
      (4 * (v a).length + 5) :=
  lr_weaken body (lr_synFieldF body (sreg_injective.ne hab) (sreg_injective.ne hat)
    (sreg_injective.ne hbt) (by simpa using ht)) (by rw [synG_update, synG_sreg, synG_sreg])
    (by simp)

theorem sg_ifNE_pos {x : SynW} {p q : Pr P (nT SXReg) Q A U}
    {R' : Fin (nT SXReg) → List (Fin (A + 4))} {k : ℕ} (hx : v x ≠ [])
    (hp : LayRuns body p (synG R v) R' k) :
    LayRuns body (synIfNE (sreg x) p q) (synG R v) R' (k + 2) :=
  lr_ifNE_pos body (by simpa using hx) hp

theorem sg_ifNE_neg {x : SynW} {p q : Pr P (nT SXReg) Q A U}
    {R' : Fin (nT SXReg) → List (Fin (A + 4))} {k : ℕ} (hx : v x = [])
    (hq : LayRuns body q (synG R v) R' k) :
    LayRuns body (synIfNE (sreg x) p q) (synG R v) R' (k + 2) :=
  lr_ifNE_neg body (by simpa using hx) hq

/-- The scan loop on a transform wire: iteration `j` of `p` takes the wires `Φ j` to `Φ (j + 1)`
(the counter `a` and its spare `t` as in `layScan_exec`). -/
theorem sg_scan (hat : a ≠ t) {p : Pr P (nT SXReg) Q A U} (Φ : ℕ → SynW → List (Fin (A + 4)))
    (cs : List (Fin (A + 4))) (bnd : ℕ → ℕ)
    (hstep : ∀ j < cs.length, LayRuns body p
      (synG R (Function.update (Function.update (Φ j) a (cs.drop (j + 1))) t
        (cs.take (j + 1)).reverse))
      (synG R (Function.update (Function.update (Φ (j + 1)) a (cs.drop (j + 1))) t
        (cs.take (j + 1)).reverse)) (bnd j)) :
    LayRuns body (scanP (sreg a) (sreg t) p)
      (synG R (Function.update (Function.update (Φ 0) a cs) t []))
      (synG R (Function.update (Function.update (Φ cs.length) a cs) t []))
      (∑ j ∈ Finset.range cs.length, (bnd j + 3) + 2 * cs.length + 4) := by
  have h := layScan_exec (body := body) (sreg_injective.ne hat) (fun j => synG R (Φ j)) cs bnd
    (fun j hj => by
      have := hstep j hj
      simpa only [← synG_update] using this)
  simpa only [← synG_update] using h

theorem sg_skip : LayRuns body synSkip (synG R v) (synG R v) 1 := lr_skip body _

/-! Contracts with explicit unary values: the result wire file is an update of `v` by values
given as arguments, so that chains of contracts stay small. -/

theorem sgU_copy {x y : ℕ} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : v t = [])
    (ha : (v a).length = x) (hb : v b = List.replicate y tick) :
    LayRuns body (ucopy (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (List.replicate (x + y) tick))) (4 * x + 4) :=
  lr_weaken body (sg_ucopy body hab hat hbt ht)
    (by rw [ha, hb, List.replicate_append_replicate]) (by rw [ha])

theorem sgU_umul (k : ℕ) {x y : ℕ} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : v t = [])
    (ha : (v a).length = x) (hb : v b = List.replicate y tick) :
    LayRuns body (umul k (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (List.replicate (k * x + y) tick))) (4 * x + 4) :=
  lr_weaken body (sg_umul body k hab hat hbt ht)
    (by rw [ha, hb, List.replicate_append_replicate]) (by rw [ha])

theorem sgU_sub {x y : ℕ} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (ht : v t = [])
    (ha : (v a).length = x) (hb : v b = List.replicate y tick) :
    LayRuns body (usub (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (List.replicate (y - x) tick))) (4 * x + 4) :=
  lr_weaken body (sg_usub body hab hat hbt ht) (by rw [ha, hb, List.drop_replicate]) (by rw [ha])

theorem sgU_div {k x y : ℕ} (hk : 1 ≤ k) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ht : v t = []) (ha : (v a).length = x) (hb : v b = List.replicate y tick) :
    LayRuns body (udiv k (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (List.replicate (x / k + y) tick))) (4 * x + 4) :=
  lr_weaken body (sg_udiv body hk hab hat hbt ht)
    (by rw [ha, hb, List.replicate_append_replicate]) (by rw [ha])

theorem sgU_clear {x : ℕ} (ha : (v a).length = x) :
    LayRuns body (uclear (sreg a)) (synG R v) (synG R (Function.update v a [])) (2 * x + 2) :=
  lr_weaken body (sg_uclear body a) rfl (by rw [ha])

theorem sgU_push {y : ℕ} (hb : v a = List.replicate y tick) :
    LayRuns body (synPush (sreg a) tick) (synG R v)
      (synG R (Function.update v a (List.replicate (y + 1) tick))) 1 :=
  lr_weaken body (sg_push body a tick) (by rw [hb, List.replicate_succ]) le_rfl

theorem sgU_pop {y : ℕ} (hb : v a = List.replicate y tick) :
    LayRuns body (synPop (sreg a)) (synG R v)
      (synG R (Function.update v a (List.replicate (y - 1) tick))) 1 :=
  lr_weaken body (sg_pop body a) (by rw [hb, List.tail_replicate]) le_rfl

theorem sgU_mulR {x y z : ℕ} (hreg : [a, b, c, t₁, t₂].Nodup) (ht₁ : v t₁ = [])
    (ht₂ : v t₂ = []) (ha : (v a).length = x) (hb : (v b).length = y)
    (hc : v c = List.replicate z tick) :
    LayRuns body (synMulR (sreg a) (sreg b) (sreg c) (sreg t₁) (sreg t₂)) (synG R v)
      (synG R (Function.update v c (List.replicate (x * y + z) tick))) (synMulRCost x y) :=
  lr_weaken body (sg_synMulR body hreg ht₁ ht₂)
    (by rw [ha, hb, hc, List.replicate_append_replicate]) (by rw [ha, hb])

theorem sgU_mulIn (k : ℕ) {x : ℕ} (hreg : [a, t, t₁].Nodup) (ht : v t = []) (ht₁ : v t₁ = [])
    (ha : (v a).length = x) :
    LayRuns body (synMulIn k (sreg a) (sreg t) (sreg t₁)) (synG R v)
      (synG R (Function.update v a (List.replicate (k * x) tick))) (8 * x + 8) :=
  lr_weaken body (sg_synMulIn body k hreg ht ht₁) (by rw [ha]) (by rw [ha])

theorem sgU_pow2 {x y : ℕ} (hreg : [a, b, t₁, t₂].Nodup) (ht₁ : v t₁ = []) (ht₂ : v t₂ = [])
    (ha : (v a).length = x) (hb : v b = List.replicate y tick) :
    LayRuns body (upow2 (sreg a) (sreg b) (sreg t₁) (sreg t₂)) (synG R v)
      (synG R (Function.update v b (List.replicate (2 ^ x * y) tick)))
      (4 * (2 ^ x * y) + 9 * x + 4) :=
  lr_weaken body (sg_upow2 body hreg ht₁ ht₂)
    (by rw [ha, hb, flatMap_replicate_of_replicate, Nat.mul_comm]) (by rw [ha, hb]; simp)

theorem sgU_divMod {x k q r : SynW} {X Kv z : ℕ} (hreg : [x, k, q, r, t₁, t₂, t₃].Nodup)
    (hk : 1 ≤ Kv) (hkv : (v k).length = Kv) (hx : (v x).length = X) (hr : v r = [])
    (hq : v q = List.replicate z tick) (ht₁ : v t₁ = []) (ht₂ : v t₂ = []) (ht₃ : v t₃ = []) :
    LayRuns body (synDivModR (sreg x) (sreg k) (sreg q) (sreg r) (sreg t₁) (sreg t₂) (sreg t₃))
      (synG R v)
      (synG R (Function.update (Function.update v r (List.replicate (X % Kv) tick)) q
        (List.replicate (X / Kv + z) tick)))
      (synDivModCost X Kv) :=
  lr_weaken body (sg_synDivModR body hreg (by rw [hkv]; exact hk) hr ht₁ ht₂ ht₃)
    (by rw [hkv, hx, hq, List.replicate_append_replicate]) (by rw [hkv, hx])

theorem sgU_exp (G F : ℕ) {uR jR eR : SynW} {x y : ℕ} (hreg : [uR, jR, eR, t₁, t₂, t₃].Nodup)
    (he : v eR = []) (ht₁ : v t₁ = []) (ht₂ : v t₂ = []) (ht₃ : v t₃ = [])
    (hu : (v uR).length = x) (hj : (v jR).length = y) :
    LayRuns body (expProg G F (sreg uR) (sreg jR) (sreg eR) (sreg t₁) (sreg t₂) (sreg t₃))
      (synG R v)
      (synG R (Function.update v eR (List.replicate (expSeq G F x y) tick)))
      (4 * x + 2 * y + 8 + ∑ i ∈ Finset.range y, (8 * expSeq G F x i + 12)) :=
  lr_weaken body (sg_expProg body G F hreg he ht₁ ht₂ ht₃) (by rw [hu, hj]) (by rw [hu, hj])

theorem sgU_move {x : ℕ} (hab : a ≠ b) (ha : v a = List.replicate x tick) (hb : v b = []) :
    LayRuns body (moveR (sreg a) (sreg b) id) (synG R v)
      (synG R (Function.update (Function.update v a []) b (List.replicate x tick)))
      (2 * x + 2) :=
  lr_weaken body (sg_moveR body hab) (by rw [ha, hb]; simp) (by rw [ha]; simp)

theorem sgR_fieldR {x : ℕ} {l : List (Fin (A + 4))} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ht : v t = []) (ha : (v a).length = x) (hb : v b = l) :
    LayRuns body (synFieldR (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (topSep :: (List.replicate x tick ++ l)))) (4 * x + 5) :=
  lr_weaken body (sg_synFieldR body hab hat hbt ht) (by rw [ha, hb]) (by rw [ha])

theorem sgR_fieldF {x : ℕ} {l : List (Fin (A + 4))} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ht : v t = []) (ha : (v a).length = x) (hb : v b = l) :
    LayRuns body (synFieldF (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (List.replicate x tick ++ topSep :: l))) (4 * x + 5) :=
  lr_weaken body (sg_synFieldF body hab hat hbt ht) (by rw [ha, hb]) (by rw [ha])

theorem sgR_umulSym (k : ℕ) (y : Fin (A + 4)) {x : ℕ} {l : List (Fin (A + 4))} (hab : a ≠ b)
    (hat : a ≠ t) (hbt : b ≠ t) (ht : v t = []) (ha : (v a).length = x) (hb : v b = l) :
    LayRuns body (umulSym k y (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (List.replicate (k * x) y ++ l))) (4 * x + 4) :=
  lr_weaken body (sg_umulSym body k y hab hat hbt ht) (by rw [ha, hb]) (by rw [ha])

theorem sgR_topField {src bk dst : SynW} (hsb : src ≠ bk) (hsd : src ≠ dst) (hbd : bk ≠ dst)
    (bb : Bool) (k : ℕ) {rest l₁ l₂ : List (Fin (A + 4))}
    (hs : v src = List.replicate k tick ++ topSep :: rest) (hbk : v bk = l₁) (hdst : v dst = l₂) :
    LayRuns body (topField (sreg src) (sreg bk) (sreg dst) bb) (synG R v)
      (synG R (Function.update (Function.update (Function.update v src rest) bk
        (topSep :: List.replicate k tick ++ l₁)) dst
          (if bb then List.replicate k tick ++ l₂ else l₂))) (2 * k + 3) :=
  lr_weaken body (lr_topField body (sreg_injective.ne hsb) (sreg_injective.ne hsd)
    (sreg_injective.ne hbd) bb k rest (by rw [synG_sreg, hs]))
    (by rw [synG_sreg, synG_sreg, hbk, hdst, synG_update, synG_update, synG_update]) le_rfl

theorem sgR_zeroBits {x : ℕ} {l : List (Fin (A + 4))} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ht : v t = []) (ha : (v a).length = x) (hb : v b = l) :
    LayRuns body (zeroBits (sreg a) (sreg b) (sreg t)) (synG R v)
      (synG R (Function.update v b (binSyms x 0 ++ l))) (4 * x + 4) :=
  lr_weaken body (sg_zeroBits body hab hat hbt ht) (by rw [ha, hb]) (by rw [ha])

theorem sgR_push (y : Fin (A + 4)) {l : List (Fin (A + 4))} (hb : v a = l) :
    LayRuns body (synPush (sreg a) y) (synG R v) (synG R (Function.update v a (y :: l))) 1 :=
  lr_weaken body (sg_push body a y) (by rw [hb]) le_rfl

/-! Contracts mixing transform wires and other registers (`b` with `∀ x, sreg x ≠ b`). -/

variable {o : Fin (nT SXReg)}

theorem so_copy {x y : ℕ} (ho : ∀ z, sreg z ≠ o) (hat : a ≠ t) (ht : v t = [])
    (ha : (v a).length = x) (hb : R o = List.replicate y tick) :
    LayRuns body (ucopy (sreg a) o (sreg t)) (synG R v)
      (synG (Function.update R o (List.replicate (x + y) tick)) v) (4 * x + 4) :=
  lr_weaken body (lr_ucopy body (ho a) (sreg_injective.ne hat) (ho t).symm (by simpa using ht))
    (by rw [synG_sreg, synG_of_ne ho, ha, hb, List.replicate_append_replicate, synG_update_out ho])
    (by rw [synG_sreg, ha])

theorem so_push (ho : ∀ z, sreg z ≠ o) (y : Fin (A + 4)) :
    LayRuns body (synPush o y) (synG R v) (synG (Function.update R o (y :: R o)) v) 1 :=
  lr_weaken body (lr_push body o y) (by rw [synG_of_ne ho, synG_update_out ho]) le_rfl

theorem so_pop (ho : ∀ z, sreg z ≠ o) :
    LayRuns body (synPop o) (synG R v) (synG (Function.update R o (R o).tail) v) 1 :=
  lr_weaken body (lr_pop body o) (by rw [synG_of_ne ho, synG_update_out ho]) le_rfl

theorem so_clear (ho : ∀ z, sreg z ≠ o) {x : ℕ} (hx : (R o).length = x) :
    LayRuns body (uclear o) (synG R v) (synG (Function.update R o []) v) (2 * x + 2) :=
  lr_weaken body (lr_uclear body o) (by rw [synG_update_out ho]) (by rw [synG_of_ne ho, hx])

theorem so_mulR {x y z : ℕ} (ho : ∀ z, sreg z ≠ o) (hreg : [a, b, t₁, t₂].Nodup)
    (ht₁ : v t₁ = []) (ht₂ : v t₂ = []) (ha : (v a).length = x) (hb : (v b).length = y)
    (hc : R o = List.replicate z tick) :
    LayRuns body (synMulR (sreg a) (sreg b) o (sreg t₁) (sreg t₂)) (synG R v)
      (synG (Function.update R o (List.replicate (x * y + z) tick)) v) (synMulRCost x y) := by
  have hreg' : [sreg a, sreg b, o, sreg t₁, sreg t₂].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hreg ⊢
    refine ⟨⟨sreg_injective.ne hreg.1.1, ho a, sreg_injective.ne hreg.1.2.1,
      sreg_injective.ne hreg.1.2.2⟩, ⟨ho b, sreg_injective.ne hreg.2.1.1,
        sreg_injective.ne hreg.2.1.2⟩, ⟨(ho t₁).symm, (ho t₂).symm⟩,
        ⟨sreg_injective.ne hreg.2.2.1, not_false⟩⟩
  exact lr_weaken body (lr_synMulR body hreg' (by simpa using ht₁) (by simpa using ht₂))
    (by rw [synG_sreg, synG_sreg, synG_of_ne ho, ha, hb, hc, List.replicate_append_replicate,
      synG_update_out ho])
    (by rw [synG_sreg, synG_sreg, ha, hb])

theorem so_zeroBits (ho : ∀ z, sreg z ≠ o) (hat : a ≠ t) (ht : v t = []) {x : ℕ}
    (ha : (v a).length = x) (hb : R o = []) :
    LayRuns body (zeroBits (sreg a) o (sreg t)) (synG R v)
      (synG (Function.update R o (binSyms x 0)) v) (4 * x + 4) :=
  lr_weaken body (lr_zeroBits body (ho a) (sreg_injective.ne hat) (ho t).symm (by simpa using ht))
    (by rw [synG_sreg, synG_of_ne ho, ha, hb, List.append_nil, synG_update_out ho])
    (by rw [synG_sreg, ha])

theorem so_pow2 (ho : ∀ z, sreg z ≠ o) (hreg : [a, t₁, t₂].Nodup) (ht₁ : v t₁ = [])
    (ht₂ : v t₂ = []) {x y : ℕ} (ha : (v a).length = x) (hb : R o = List.replicate y tick) :
    LayRuns body (upow2 (sreg a) o (sreg t₁) (sreg t₂)) (synG R v)
      (synG (Function.update R o (List.replicate (2 ^ x * y) tick)) v)
      (4 * (2 ^ x * y) + 9 * x + 4) := by
  have hreg' : [sreg a, o, sreg t₁, sreg t₂].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hreg ⊢
    exact ⟨⟨ho a, sreg_injective.ne hreg.1.1, sreg_injective.ne hreg.1.2⟩,
      ⟨(ho t₁).symm, (ho t₂).symm⟩, ⟨sreg_injective.ne hreg.2.1, not_false⟩⟩
  exact lr_weaken body (lr_upow2 body hreg' (by simpa using ht₁) (by simpa using ht₂))
    (by rw [synG_sreg, synG_of_ne ho, ha, hb, flatMap_replicate_of_replicate, Nat.mul_comm,
      synG_update_out ho])
    (by rw [synG_sreg, synG_of_ne ho, ha, hb]; simp)

theorem so_moveWO (ho : ∀ z, sreg z ≠ o) :
    LayRuns body (moveR (sreg a) o id) (synG R v)
      (synG (Function.update R o ((v a).reverse ++ R o)) (Function.update v a []))
      (2 * (v a).length + 2) :=
  lr_weaken body (lr_moveR_id body (ho a))
    (by rw [synG_sreg, synG_of_ne ho, synG_update, synG_update_out (fun z => ho z)])
    (by rw [synG_sreg])

theorem so_moveOW (ho : ∀ z, sreg z ≠ o) :
    LayRuns body (moveR o (sreg a) id) (synG R v)
      (synG (Function.update R o []) (Function.update v a ((R o).reverse ++ v a)))
      (2 * (R o).length + 2) :=
  lr_weaken body (lr_moveR_id body (ho a).symm)
    (by rw [synG_sreg, synG_of_ne ho, synG_update_out ho, synG_update])
    (by rw [synG_of_ne ho])

theorem so_pushV (ho : ∀ z, sreg z ≠ o) (y : Fin (A + 4)) {l : List (Fin (A + 4))}
    (hb : R o = l) :
    LayRuns body (synPush o y) (synG R v) (synG (Function.update R o (y :: l)) v) 1 :=
  lr_weaken body (so_push body ho y) (by rw [hb]) le_rfl

theorem so_popV (ho : ∀ z, sreg z ≠ o) {y : ℕ} (hb : R o = List.replicate y tick) :
    LayRuns body (synPop o) (synG R v)
      (synG (Function.update R o (List.replicate (y - 1) tick)) v) 1 :=
  lr_weaken body (so_pop body ho) (by rw [hb, List.tail_replicate]) le_rfl

theorem so_moveWOV (ho : ∀ z, sreg z ≠ o) {l l' : List (Fin (A + 4))} (ha : v a = l)
    (hb : R o = l') :
    LayRuns body (moveR (sreg a) o id) (synG R v)
      (synG (Function.update R o (l.reverse ++ l')) (Function.update v a []))
      (2 * l.length + 2) :=
  lr_weaken body (so_moveWO body ho) (by rw [ha, hb]) (by rw [ha])

theorem so_moveOWV (ho : ∀ z, sreg z ≠ o) {l l' : List (Fin (A + 4))} (ha : R o = l)
    (hb : v a = l') :
    LayRuns body (moveR o (sreg a) id) (synG R v)
      (synG (Function.update R o []) (Function.update v a (l.reverse ++ l')))
      (2 * l.length + 2) :=
  lr_weaken body (so_moveOW body ho) (by rw [ha, hb]) (by rw [ha])

theorem sgR_move {l l' : List (Fin (A + 4))} (hab : a ≠ b) (ha : v a = l) (hb : v b = l') :
    LayRuns body (moveR (sreg a) (sreg b) id) (synG R v)
      (synG R (Function.update (Function.update v a []) b (l.reverse ++ l')))
      (2 * l.length + 2) :=
  lr_weaken body (sg_moveR body hab) (by rw [ha, hb]) (by rw [ha])

theorem so_topSkips (ho : ∀ z, sreg z ≠ o) (hbd : b ≠ c) (i : ℕ) (l : List ℕ)
    (rest : List (Fin (A + 4))) (hi : i ≤ l.length) (hs : R o = topRec l ++ rest) :
    LayRuns body (topSkips o (sreg b) (sreg c) i) (synG R v)
      (synG (Function.update R o (topRec (l.drop i) ++ rest))
        (Function.update v b ((topRec (l.take i)).reverse ++ v b)))
      (2 * (topRec (l.take i) : List (Fin (A + 4))).length + i + 1) :=
  lr_weaken body (lr_topSkips body (ho b).symm (ho c).symm (sreg_injective.ne hbd) i l rest hi
    (by rw [synG_of_ne ho, hs]))
    (by rw [synG_sreg, synG_update_out ho, synG_update]) le_rfl

/-! Parking transform wires. -/

/-- The parked contents of the wires `xs`, the last one on top. -/
def synStkW (v : SynW → List (Fin (A + 4))) (mkr : Fin (A + 4)) : List SynW → List (Fin (A + 4))
  | [] => []
  | x :: xs => synStkW v mkr xs ++ mkr :: (v x).reverse

/-- The wire file `v` with the wires `xs` emptied. -/
def synClrW (v : SynW → List (Fin (A + 4))) (xs : List SynW) : SynW → List (Fin (A + 4)) :=
  fun y => if y ∈ xs then [] else v y

/-- The step bound of parking or restoring the wires `xs`. -/
def synStashCostW (v : SynW → List (Fin (A + 4))) : List SynW → ℕ
  | [] => 1
  | x :: xs => 2 * (v x).length + 3 + synStashCostW v xs

theorem synStkW_congr {v v' : SynW → List (Fin (A + 4))} (mkr : Fin (A + 4)) :
    ∀ xs : List SynW, (∀ x ∈ xs, v' x = v x) → synStkW v' mkr xs = synStkW v mkr xs
  | [], _ => rfl
  | x :: xs, h => by
      simp only [synStkW, h x (by simp), synStkW_congr mkr xs fun y hy => h y (by simp [hy])]

theorem synStashCostW_congr {v v' : SynW → List (Fin (A + 4))} :
    ∀ xs : List SynW, (∀ x ∈ xs, v' x = v x) → synStashCostW v' xs = synStashCostW v xs
  | [], _ => rfl
  | x :: xs, h => by
      simp only [synStashCostW, h x (by simp), synStashCostW_congr xs fun y hy => h y (by simp [hy])]

theorem synStk_synG (mkr : Fin (A + 4)) :
    ∀ xs : List SynW, synStk (synG R v) mkr (xs.map sreg) = synStkW v mkr xs
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, synStk, synStkW, synStk_synG mkr xs, synG_sreg]

theorem synStashCost_synG :
    ∀ xs : List SynW, synStashCost (synG R v) (xs.map sreg) = synStashCostW v xs
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, synStashCost, synStashCostW, synStashCost_synG xs, synG_sreg]

theorem synClr_synG (xs : List SynW) : synClr (synG R v) (xs.map sreg) = synG R (synClrW v xs) := by
  funext z
  by_cases hz : ∃ y, sreg y = z
  · obtain ⟨y, rfl⟩ := hz
    simp [synClr, synClrW, sreg_injective.eq_iff]
  · have hz' : ∀ y, sreg y ≠ z := fun y hy => hz ⟨y, hy⟩
    have : z ∉ xs.map sreg := by
      simp only [List.mem_map, not_exists, not_and]; exact fun y _ => hz' y
    simp only [synClr, this, ite_false]
    rw [synG_of_ne hz', synG_of_ne hz']

theorem sg_synStash {pk : Fin (nT SXReg)} (hpk : ∀ z, sreg z ≠ pk) (mkr : Fin (A + 4))
    (xs : List SynW) (hd : xs.Nodup) :
    LayRuns body (synStash pk mkr (xs.map sreg)) (synG R v)
      (synG (Function.update R pk (synStkW v mkr xs ++ mkr :: R pk)) (synClrW v xs))
      (synStashCostW v xs + 1) := by
  have h := lr_synStash body (R := synG R v) mkr (xs.map sreg) (hd.map sreg_injective)
    (by simp only [List.mem_map, not_exists, not_and]; exact fun y _ => hpk y)
  rw [synStk_synG, synStashCost_synG, synClr_synG, synG_of_ne hpk, synG_update_out hpk] at h
  exact h

theorem sg_synUnstash {pk : Fin (nT SXReg)} (hpk : ∀ z, sreg z ≠ pk) (mkr : Fin (A + 4))
    (xs : List SynW) (P₀ : List (Fin (A + 4))) (hd : xs.Nodup) (hmk : ∀ x ∈ xs, mkr ∉ v x) :
    LayRuns body (synUnstash pk mkr (xs.map sreg))
      (synG (Function.update R pk (synStkW v mkr xs ++ mkr :: P₀)) (synClrW v xs))
      (synG (Function.update R pk P₀) v) (synStashCostW v xs + 1) := by
  have h := lr_synUnstash body (R := synG R v) mkr (xs.map sreg) P₀ (hd.map sreg_injective)
    (by simp only [List.mem_map, not_exists, not_and]; exact fun y _ => hpk y)
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      rw [synG_sreg]; exact hmk y hy)
  rw [synStk_synG, synStashCost_synG, synClr_synG, synG_update_out hpk,
    synG_update_out hpk] at h
  exact h

end Wires

/-- Equality of files given by updates at concrete names. -/
macro "vext" : tactic => `(tactic| (refine congrArg (synG _) ?_; funext y; simp only [Function.update_apply]; split_ifs <;> (try simp_all) <;> omega))

end IntegerMultBounds.MathlibTM2.Fast
