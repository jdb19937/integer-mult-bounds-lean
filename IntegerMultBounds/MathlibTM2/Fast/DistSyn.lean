module

public import IntegerMultBounds.MathlibTM2.Fast.DistSynHost
public import IntegerMultBounds.MathlibTM2.Fast.DistSrcBase
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The parameter wires of the synthetic transforms: the machine

`dsySyn rg io oPark oB oLg oL oNr oRec oPos` is one fixed program running on the registers
`io : DsX → Fin T` of the distribution machine (`Fast/DistMain.lean`): the unary `lN = N`,
`lL = ℓ`, `lK = K`, `lD = D`, `lW = W_L` and the binary axis word `lE = binSyms W_L E`, on a
table layout `rg : TblR 40 → Fin T` (empty before and after) and the output registers:

* `oPark`: the park record `dsyParkL (W_L + ℓ + D) E` of the layout programs
  (`blank :: (binSyms W E).reverse ++ blank :: replicate W tick ++ blank :: []`);
* `oB`: `(ℓ - 1) mod K` ticks (`layB ℓ K`); `oLg`: `|layLongs es ℓ|` ticks (the long axes);
  `oL`: `ℓ` ticks; `oNr`: `dsyNr N D ℓ` ticks (`ℓ` if some axis is long, else `ℓ - 1`);
* `oRec`: the axis record `topRec es`;
* `oPos`: the position table `twPosReg A N (twPosL (layPerm es ℓ K))` of the layout.

The inputs are not consumed. **Program**: the park record (unary copies of `lW`, `lL`, `lD`,
`lE` widened by `bpad`); the table word width `W = dsyW N ℓ = N² + N + ℓ + 4` built in unary
on `wr` (`dsyWidth`, a unary product); the variables zeroed, `N, ℓ, K, D` loaded (`tblLoad1`)
and the low `W` bits of `lE` copied into the variable `vE` (`dsyLoadE`); the prefix moves of
the layout (`ldw1Code`, its emissions discarded); then the six phases `dsyPhase` emitting the
wires (`Fast/DistSynTbl.lean`); finally the layout cleared.

* `dsySyn_runs`: the contract for any `es ℓ K E W_L` with `LayHyp es ℓ K`, the axis word,
  `E < 2^D`, `dsyW N ℓ ≤ W_L`, `E < 2^W_L`, within `dsySynCostG N ℓ K D W_L` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.Rounds


variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-! ### The park record -/

/-- The park record of the layout programs: `W` and `E` above the empty rest. -/
def dsyParkL (A : ℕ) (W E : ℕ) : List (Fin (A + 4)) :=
  blank :: (binSyms W E).reverse ++ blank :: List.replicate W tick ++ blank :: []

/-- The park record from `lW`, `lL`, `lD` (the ticks) and `lE` (widened by `|lL| + |lD|`). -/
def dsyParkP (rg : TblR 40 → Fin T) (io : DsX → Fin T) (o : Fin T) : Pr P T Q A U :=
  .seq (dsyPush o blank 1) <| .seq (ucopy (io .lD) o (rg (.z 7))) <|
  .seq (ucopy (io .lL) o (rg (.z 7))) <| .seq (ucopy (io .lW) o (rg (.z 7))) <|
  .seq (dsyPush o blank 1) <| .seq (bcopy (io .lE) (rg (.z 9)) (rg (.z 7)) (rg (.z 8))) <|
  .seq (bpad (rg (.z 9)) (io .lL) (rg (.z 7)) (rg (.z 8))) <|
  .seq (bpad (rg (.z 9)) (io .lD) (rg (.z 7)) (rg (.z 8))) <|
  .seq (moveR (rg (.z 9)) o id) (dsyPush o blank 1)

/-- The step bound of `dsyParkP`. -/
def dsyParkCost (WL ℓ D : ℕ) : ℕ := 20 * WL + 16 * ℓ + 16 * D + 39

theorem dsy_rep3 {α : Type} (a b c : ℕ) (x : α) (l : List α) :
    List.replicate a x ++ (List.replicate b x ++ (List.replicate c x ++ l)) =
      List.replicate (a + b + c) x ++ l := by
  rw [← List.append_assoc, ← List.append_assoc, List.replicate_append_replicate,
    List.replicate_append_replicate]

theorem dsyParkP_runs {rg : TblR 40 → Fin T} {io : DsX → Fin T} (hrg : Function.Injective rg)
    (hdisj : ∀ r x, rg r ≠ io x) {o : Fin T} (ho : ∀ r, rg r ≠ o) (hoi : ∀ x, io x ≠ o)
    (R : Regs T A) {WL ℓ D E : ℕ} (hEW : E < 2 ^ WL) (hW : (R (io .lW)).length = WL)
    (hL : (R (io .lL)).length = ℓ) (hD : (R (io .lD)).length = D) (hE : R (io .lE) = binSyms WL E)
    (h7 : R (rg (.z 7)) = []) (h8 : R (rg (.z 8)) = []) (h9 : R (rg (.z 9)) = []) :
    dsyRuns body (dsyParkP rg io o) R
      (Function.update R o (dsyParkL A (WL + ℓ + D) E ++ R o)) (dsyParkCost WL ℓ D) := by
  have n79 : rg (.z 7) ≠ rg (.z 9) := hrg.ne (by decide)
  have n89 : rg (.z 8) ≠ rg (.z 9) := hrg.ne (by decide)
  have n78 : rg (.z 7) ≠ rg (.z 8) := hrg.ne (by decide)
  -- 1: blank
  have s1 := dsyRuns_push (body := body) o blank 1 R
  set R₁ := Function.update R o (List.replicate 1 blank ++ R o) with hR₁
  have l1 : ∀ k, k ≠ o → R₁ k = R k := fun k hk => by rw [hR₁, Function.update_of_ne hk]
  -- 2: D ticks
  have s2 := dsyRuns_ucopy (body := body) (hoi .lD) (hdisj _ _).symm (ho _).symm R₁
    (by rw [l1 _ (ho _)]; exact h7)
  rw [l1 _ (hoi _), hD] at s2
  set R₂ := Function.update R₁ o (List.replicate D tick ++ R₁ o) with hR₂
  have l2 : ∀ k, k ≠ o → R₂ k = R k := fun k hk => by rw [hR₂, Function.update_of_ne hk, l1 k hk]
  -- 3: ℓ ticks
  have s3 := dsyRuns_ucopy (body := body) (hoi .lL) (hdisj _ _).symm (ho _).symm R₂
    (by rw [l2 _ (ho _)]; exact h7)
  rw [l2 _ (hoi _), hL] at s3
  set R₃ := Function.update R₂ o (List.replicate ℓ tick ++ R₂ o) with hR₃
  have l3 : ∀ k, k ≠ o → R₃ k = R k := fun k hk => by rw [hR₃, Function.update_of_ne hk, l2 k hk]
  -- 4: WL ticks
  have s4 := dsyRuns_ucopy (body := body) (hoi .lW) (hdisj _ _).symm (ho _).symm R₃
    (by rw [l3 _ (ho _)]; exact h7)
  rw [l3 _ (hoi _), hW] at s4
  set R₄ := Function.update R₃ o (List.replicate WL tick ++ R₃ o) with hR₄
  have l4 : ∀ k, k ≠ o → R₄ k = R k := fun k hk => by rw [hR₄, Function.update_of_ne hk, l3 k hk]
  -- 5: blank
  have s5 := dsyRuns_push (body := body) o blank 1 R₄
  set R₅ := Function.update R₄ o (List.replicate 1 blank ++ R₄ o) with hR₅
  have l5 : ∀ k, k ≠ o → R₅ k = R k := fun k hk => by rw [hR₅, Function.update_of_ne hk, l4 k hk]
  -- 6: copy E
  have s6 := dsyRuns_bcopy (body := body) (a := io .lE) (c := rg (.z 9)) (t₁ := rg (.z 7))
    (t₂ := rg (.z 8)) (by
      have := (hdisj (.z 9) .lE).symm; have := (hdisj (.z 7) .lE).symm
      have := (hdisj (.z 8) .lE).symm
      regs_nodup) R₅ (by rw [l5 _ (ho _)]; exact h7) (by rw [l5 _ (ho _)]; exact h8)
  rw [l5 _ (hoi _), l5 _ (ho _), hE, h9, List.append_nil] at s6
  set R₆ := Function.update R₅ (rg (.z 9)) (binSyms WL E) with hR₆
  have l6 : ∀ k, k ≠ o → k ≠ rg (.z 9) → R₆ k = R k := fun k hk hk9 => by
    rw [hR₆, Function.update_of_ne hk9, l5 k hk]
  -- 7, 8: widen
  have s7 := dsyRuns_bpad (body := body) (a := rg (.z 9)) (eR := io .lL) (t₁ := rg (.z 7))
    (t₂ := rg (.z 8)) (by
      have := hdisj (.z 9) .lL; have := (hdisj (.z 7) .lL).symm; have := (hdisj (.z 8) .lL).symm
      have := n79.symm; have := n89.symm
      regs_nodup) hEW R₆ (by rw [hR₆, Function.update_self])
    (by rw [l6 _ (ho _) n79]; exact h7) (by rw [l6 _ (ho _) n89]; exact h8)
  rw [l6 _ (hoi _) (hdisj _ _).symm, hL] at s7
  set R₇ := Function.update R₆ (rg (.z 9)) (binSyms (WL + ℓ) E) with hR₇
  have l7 : ∀ k, k ≠ o → k ≠ rg (.z 9) → R₇ k = R k := fun k hk hk9 => by
    rw [hR₇, Function.update_of_ne hk9, l6 k hk hk9]
  have hEW' : E < 2 ^ (WL + ℓ) :=
    lt_of_lt_of_le hEW (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _))
  have s8 := dsyRuns_bpad (body := body) (a := rg (.z 9)) (eR := io .lD) (t₁ := rg (.z 7))
    (t₂ := rg (.z 8)) (by
      have := hdisj (.z 9) .lD; have := (hdisj (.z 7) .lD).symm; have := (hdisj (.z 8) .lD).symm
      have := n79.symm; have := n89.symm
      regs_nodup) hEW' R₇ (by rw [hR₇, Function.update_self])
    (by rw [l7 _ (ho _) n79]; exact h7) (by rw [l7 _ (ho _) n89]; exact h8)
  rw [l7 _ (hoi _) (hdisj _ _).symm, hD] at s8
  set R₈ := Function.update R₇ (rg (.z 9)) (binSyms (WL + ℓ + D) E) with hR₈
  -- 9: move onto the park
  have s9 := dsyRuns_moveR (body := body) (ho (.z 9)) R₈
  set R₉ := Function.update (Function.update R₈ (rg (.z 9)) []) o ((R₈ (rg (.z 9))).reverse ++ R₈ o)
    with hR₉
  -- 10: blank
  have s10 := dsyRuns_push (body := body) o blank 1 R₉
  refine ((s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq
    (s9.seq s10))))))))).congr ?_).mono ?_
  · have e8z : R₈ (rg (.z 9)) = binSyms (WL + ℓ + D) E := by rw [hR₈, Function.update_self]
    have e8o : R₈ o = List.replicate 1 blank ++ (List.replicate WL tick ++ (List.replicate ℓ tick ++
        (List.replicate D tick ++ (List.replicate 1 blank ++ R o)))) := by
      rw [hR₈, Function.update_of_ne (ho _).symm, hR₇, Function.update_of_ne (ho _).symm, hR₆,
        Function.update_of_ne (ho _).symm, hR₅, Function.update_self, hR₄, Function.update_self,
        hR₃, Function.update_self, hR₂, Function.update_self, hR₁, Function.update_self]
    funext k
    by_cases hk : k = o
    · subst hk
      rw [Function.update_self, Function.update_self, hR₉, Function.update_self, e8z, e8o,
        dsy_rep3, dsyParkL]
      simp only [List.replicate_one, List.cons_append, List.append_assoc,
        List.nil_append]
    · rw [Function.update_of_ne hk, Function.update_of_ne hk, hR₉, Function.update_of_ne hk]
      by_cases hk9 : k = rg (.z 9)
      · rw [hk9, Function.update_self, h9]
      · rw [Function.update_of_ne hk9, hR₈, Function.update_of_ne hk9, l7 k hk hk9]
  · simp only [hR₈, Function.update_self, length_binSyms]
    unfold dsyParkCost; omega

/-! ### The word width -/

/-- The table word width `N² + N + ℓ + 4`. -/
def dsyW (N ℓ : ℕ) : ℕ := N * N + N + ℓ + 4

theorem dsyW_ok {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) :
    (es.sum + 1) ^ es.sum < 2 ^ dsyW es.sum ℓ ∧ es.sum < dsyW es.sum ℓ ∧ 2 ≤ dsyW es.sum ℓ ∧
      ℓ < 2 ^ dsyW es.sum ℓ ∧ es.length < 2 ^ dsyW es.sum ℓ ∧ K < 2 ^ dsyW es.sum ℓ := by
  have hDN := ldw_length_le_sum H
  have hK := H.K_le
  have hℓ := H.ℓ_ge
  have h1 : es.sum + 1 ≤ 2 ^ es.sum := Nat.lt_two_pow_self
  have h2 : (es.sum + 1) ^ es.sum ≤ 2 ^ (es.sum * es.sum) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h1 _
  have hW : es.sum * es.sum < dsyW es.sum ℓ := by unfold dsyW; omega
  have hNW : es.sum < dsyW es.sum ℓ := by unfold dsyW; omega
  have hℓW : ℓ < dsyW es.sum ℓ := by unfold dsyW; omega
  refine ⟨lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by norm_num) hW), hNW, by unfold dsyW; omega,
    lt_trans hℓW Nat.lt_two_pow_self, lt_trans (lt_of_le_of_lt hDN hNW) Nat.lt_two_pow_self,
    lt_trans (lt_of_lt_of_le (by omega) hℓW.le) Nat.lt_two_pow_self⟩

/-- `wr := N² + N + ℓ + 4` ticks (`N = |lN|`, `ℓ = |lL|`), `wn := [tick]`. -/
def dsyWidth (rg : TblR 40 → Fin T) (io : DsX → Fin T) : Pr P T Q A U :=
  .seq (ucopy (io .lN) (rg (.z 9)) (rg (.z 7))) <| .seq (ucopy (io .lN) (rg .wr) (rg (.z 7))) <|
  .seq (dsyMulU (rg (.z 9)) (io .lN) (rg .wr) (rg (.z 8)) (rg (.z 7))) <|
  .seq (uclear (rg (.z 9))) <| .seq (ucopy (io .lL) (rg .wr) (rg (.z 7))) <|
  .seq (dsyPush (rg .wr) tick 4) (dsyPush (rg .wn) tick 1)

/-- The step bound of `dsyWidth`. -/
def dsyWidthCost (N ℓ : ℕ) : ℕ := 4 * N * N + 19 * N + 4 * ℓ + 20

theorem dsyWidth_runs {rg : TblR 40 → Fin T} {io : DsX → Fin T} (hrg : Function.Injective rg)
    (hdisj : ∀ r x, rg r ≠ io x) (R : Regs T A) {N ℓ : ℕ} (hN : (R (io .lN)).length = N)
    (hL : (R (io .lL)).length = ℓ) (hwr : R (rg .wr) = []) (hwn : R (rg .wn) = [])
    (h7 : R (rg (.z 7)) = []) (h8 : R (rg (.z 8)) = []) (h9 : R (rg (.z 9)) = []) :
    dsyRuns body (dsyWidth rg io) R
      (Function.update (Function.update R (rg .wr) (List.replicate (dsyW N ℓ) tick)) (rg .wn)
        [tick]) (dsyWidthCost N ℓ) := by
  have n79 : rg (.z 7) ≠ rg (.z 9) := hrg.ne (by decide)
  have n89 : rg (.z 8) ≠ rg (.z 9) := hrg.ne (by decide)
  have n78 : rg (.z 7) ≠ rg (.z 8) := hrg.ne (by decide)
  have nw7 : rg .wr ≠ rg (.z 7) := hrg.ne (by decide)
  have nw8 : rg .wr ≠ rg (.z 8) := hrg.ne (by decide)
  have nw9 : rg .wr ≠ rg (.z 9) := hrg.ne (by decide)
  have nwn : rg .wr ≠ rg .wn := hrg.ne (by decide)
  have n9N : rg (.z 9) ≠ io .lN := hdisj _ _
  have n7N : rg (.z 7) ≠ io .lN := hdisj _ _
  have n8N : rg (.z 8) ≠ io .lN := hdisj _ _
  have nwN : rg .wr ≠ io .lN := hdisj _ _
  -- 1
  have s1 := dsyRuns_ucopy (body := body) n9N.symm n7N.symm n79.symm R h7
  rw [hN, h9, List.append_nil] at s1
  set R₁ := Function.update R (rg (.z 9)) (List.replicate N tick) with hR₁
  have l1 : ∀ k, k ≠ rg (.z 9) → R₁ k = R k := fun k hk => by rw [hR₁, Function.update_of_ne hk]
  -- 2
  have s2 := dsyRuns_ucopy (body := body) nwN.symm n7N.symm nw7 R₁ (by rw [l1 _ n79]; exact h7)
  rw [l1 _ n9N.symm, hN, l1 _ nw9, hwr, List.append_nil] at s2
  set R₂ := Function.update R₁ (rg .wr) (List.replicate N tick) with hR₂
  have l2 : ∀ k, k ≠ rg (.z 9) → k ≠ rg .wr → R₂ k = R k := fun k hk hkw => by
    rw [hR₂, Function.update_of_ne hkw, l1 k hk]
  -- 3: the product
  have s3 := dsyRuns_mulU (body := body) (a := rg (.z 9)) (b := io .lN) (dst := rg .wr)
    (t := rg (.z 8)) (t' := rg (.z 7)) (by
      have := nw8.symm; have := nw7.symm; have := n9N
      regs_nodup) R₂ (by rw [l2 _ n89 nw8.symm]; exact h8) (by rw [l2 _ n79 nw7.symm]; exact h7)
  have e3 : R₂ (rg (.z 9)) = List.replicate N tick := by
    rw [hR₂, Function.update_of_ne nw9.symm, hR₁, Function.update_self]
  have e3' : R₂ (rg .wr) = List.replicate N tick := by rw [hR₂, Function.update_self]
  rw [l2 _ n9N.symm nwN.symm, hN, e3, e3', List.length_replicate] at s3
  set R₃ := Function.update R₂ (rg .wr) (List.replicate (N * N) tick ++ List.replicate N tick)
    with hR₃
  have l3 : ∀ k, k ≠ rg (.z 9) → k ≠ rg .wr → R₃ k = R k := fun k hk hkw => by
    rw [hR₃, Function.update_of_ne hkw, l2 k hk hkw]
  -- 4
  have s4 := dsyRuns_uclear (body := body) (rg (.z 9)) R₃
  set R₄ := Function.update R₃ (rg (.z 9)) [] with hR₄
  have l4 : ∀ k, k ≠ rg (.z 9) → k ≠ rg .wr → R₄ k = R k := fun k hk hkw => by
    rw [hR₄, Function.update_of_ne hk, l3 k hk hkw]
  -- 5
  have e4 : R₃ (rg (.z 9)) = List.replicate N tick := by
    rw [hR₃, Function.update_of_ne nw9.symm, e3]
  rw [e4, List.length_replicate] at s4
  have s5 := dsyRuns_ucopy (body := body) (hdisj .wr .lL).symm (hdisj (.z 7) .lL).symm nw7 R₄
    (by rw [l4 _ n79 nw7.symm]; exact h7)
  have e5 : R₄ (rg .wr) = List.replicate (N * N) tick ++ List.replicate N tick := by
    rw [hR₄, Function.update_of_ne nw9, hR₃, Function.update_self]
  rw [l4 _ (hdisj _ _).symm (hdisj _ _).symm, hL, e5] at s5
  set R₅ := Function.update R₄ (rg .wr) (List.replicate ℓ tick ++
    (List.replicate (N * N) tick ++ List.replicate N tick)) with hR₅
  -- 6, 7
  have s6 := dsyRuns_push (body := body) (rg .wr) tick 4 R₅
  set R₆ := Function.update R₅ (rg .wr) (List.replicate 4 tick ++ R₅ (rg .wr)) with hR₆
  have s7 := dsyRuns_push (body := body) (rg .wn) tick 1 R₆
  refine ((s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq s7)))))).congr ?_).mono ?_
  · funext k
    by_cases hkn : k = rg .wn
    · subst hkn
      rw [Function.update_self, Function.update_self, hR₆, Function.update_of_ne nwn.symm, hR₅,
        Function.update_of_ne nwn.symm, l4 _ (hrg.ne (by decide)) nwn.symm, hwn]
      rfl
    rw [Function.update_of_ne hkn, Function.update_of_ne hkn]
    by_cases hkw : k = rg .wr
    · subst hkw
      rw [Function.update_self, hR₆, Function.update_self, hR₅, Function.update_self, dsy_rep3,
        List.replicate_append_replicate, dsyW]
      congr 1; ring
    · rw [Function.update_of_ne hkw, hR₆, Function.update_of_ne hkw, hR₅,
        Function.update_of_ne hkw]
      by_cases hk9 : k = rg (.z 9)
      · rw [hk9, hR₄, Function.update_self, h9]
      · exact l4 k hk9 hkw
  · unfold dsyWidthCost; nlinarith

/-! ### The variables and their loads -/

/-- The initial variable values: `N, ℓ, K, D, E` in the variables `0 … 4`. -/
def dsyInit (N ℓ K D E : ℕ) : Fin 40 → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (fun _ => 0) 0 N) 1 ℓ) 2 K) 3 D) 4 E

/-- The zeroing of all variables, from the file after `dsyWidth`, as a layout file. -/
theorem dsyZeroAll_runs {rg : TblR 40 → Fin T} (hrg : Function.Injective rg) (R : Regs T A)
    (hrg0 : ∀ r, R (rg r) = []) (W : ℕ) :
    dsyRuns body (dsyZeroVars rg (List.finRange 40))
      (Function.update (Function.update R (rg .wr) (List.replicate W tick)) (rg .wn) [tick])
      (dsOv rg R (tblRho W (List.replicate W tick) [tick] ⟨fun _ => 0, []⟩))
      (40 * (4 * W + 4) + 1) := by
  set R₀ := Function.update (Function.update R (rg .wr) (List.replicate W tick)) (rg .wn) [tick]
    with hR₀
  have l0 : ∀ r, r ≠ .wr → r ≠ .wn → R₀ (rg r) = [] := fun r h1 h2 => by
    rw [hR₀, Function.update_of_ne (hrg.ne h2), Function.update_of_ne (hrg.ne h1), hrg0]
  have hwr : R₀ (rg .wr) = List.replicate W tick := by
    rw [hR₀, Function.update_of_ne (hrg.ne (by decide)), Function.update_self]
  have h := dsyZeroVars_runs (body := body) hrg (List.finRange 40) (List.nodup_finRange 40) R₀
    (fun i _ => l0 _ (fun h => by cases h) (fun h => by cases h)) (l0 _ (by decide) (by decide))
  rw [hwr, List.length_replicate, List.length_finRange] at h
  refine h.congr ?_
  funext k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hk
    rw [dsOv_rg hrg]
    rcases r with i | _ | _ | _ | j
    · rw [ite_eq_left ⟨i, List.mem_finRange i, rfl⟩]; rfl
    · rw [ite_eq_right (by rintro ⟨i, -, h⟩; cases hrg h), hwr]; rfl
    · rw [ite_eq_right (by rintro ⟨i, -, h⟩; cases hrg h), hR₀, Function.update_self]; rfl
    · rw [ite_eq_right (by rintro ⟨i, -, h⟩; cases hrg h), l0 _ (by decide) (by decide)]; rfl
    · rw [ite_eq_right (by rintro ⟨i, -, h⟩; cases hrg h), l0 _ (fun h => by cases h)
        (fun h => by cases h)]; rfl
  · push Not at hk
    rw [dsOv_off _ _ hk, ite_eq_right (by rintro ⟨i, -, h⟩; exact hk _ h), hR₀,
      Function.update_of_ne (hk _).symm, Function.update_of_ne (hk _).symm]

/-- The loads of `N, ℓ, K, D` into the variables `0 … 3`. -/
def dsyLoads (rg : TblR 40 → Fin T) (io : DsX → Fin T) : Pr P T Q A U :=
  .seq (tblLoad1 rg (io .lN) 0) <| .seq (tblLoad1 rg (io .lL) 1) <|
  .seq (tblLoad1 rg (io .lK) 2) (tblLoad1 rg (io .lD) 3)

/-- The step bound of `dsyLoads`. -/
def dsyLoadsCost (N ℓ K D W : ℕ) : ℕ := (N + ℓ + K + D) * (4 * W + 10) + 4 * (6 * W + 10)

theorem dsyLoads_runs {rg : TblR 40 → Fin T} {io : DsX → Fin T} (hrg : Function.Injective rg)
    (hdisj : ∀ r x, rg r ≠ io x) (R : Regs T A) {N ℓ K D W : ℕ} (hN : (R (io .lN)).length = N)
    (hL : (R (io .lL)).length = ℓ) (hK : (R (io .lK)).length = K) (hD : (R (io .lD)).length = D)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) :
    dsyRuns body (dsyLoads rg io) (dsOv rg R (tblRho W wl nl ⟨fun _ => 0, []⟩))
      (dsOv rg R (tblRho W wl nl ⟨Function.update (Function.update (Function.update
        (Function.update (fun _ => 0) 0 N) 1 ℓ) 2 K) 3 D, []⟩)) (dsyLoadsCost N ℓ K D W) := by
  have hoff : ∀ (ρ : TblR 40 → List (Fin (A + 4))) (x : DsX), dsOv rg R ρ (io x) = R (io x) :=
    fun ρ x => dsOv_off _ _ (fun r => hdisj r x)
  have s1 := dsyRuns_load1 (body := body) hrg wl nl hwl (fun r => hdisj r .lN) 0
    ⟨fun _ => 0, []⟩ (dsOv rg R (tblRho W wl nl ⟨fun _ => 0, []⟩)) (fun r => dsOv_rg hrg _ _ r)
  rw [hoff, hN, dsOv_dsOv] at s1
  have s2 := dsyRuns_load1 (body := body) hrg wl nl hwl (fun r => hdisj r .lL) 1
    ⟨Function.update (fun _ => 0) 0 N, []⟩
    (dsOv rg R (tblRho W wl nl ⟨Function.update (fun _ => 0) 0 N, []⟩))
    (fun r => dsOv_rg hrg _ _ r)
  rw [hoff, hL, dsOv_dsOv] at s2
  have s3 := dsyRuns_load1 (body := body) hrg wl nl hwl (fun r => hdisj r .lK) 2
    ⟨Function.update (Function.update (fun _ => 0) 0 N) 1 ℓ, []⟩
    (dsOv rg R (tblRho W wl nl ⟨Function.update (Function.update (fun _ => 0) 0 N) 1 ℓ, []⟩))
    (fun r => dsOv_rg hrg _ _ r)
  rw [hoff, hK, dsOv_dsOv] at s3
  have s4 := dsyRuns_load1 (body := body) hrg wl nl hwl (fun r => hdisj r .lD) 3
    ⟨Function.update (Function.update (Function.update (fun _ => 0) 0 N) 1 ℓ) 2 K, []⟩
    (dsOv rg R (tblRho W wl nl
      ⟨Function.update (Function.update (Function.update (fun _ => 0) 0 N) 1 ℓ) 2 K, []⟩))
    (fun r => dsOv_rg hrg _ _ r)
  rw [hoff, hD, dsOv_dsOv] at s4
  refine (s1.seq (s2.seq (s3.seq s4))).mono ?_
  unfold dsyLoadsCost; nlinarith

/-- The low `|wr|` bits of `lE` into the variable `4` (`lE` restored). -/
def dsyLoadE (rg : TblR 40 → Fin T) (io : DsX → Fin T) : Pr P T Q A U :=
  .seq (dsyXfer (rg .wr) (rg (.z 8)) (io .lE) (rg (.z 9))) <|
  .seq (bcopy (rg (.z 9)) (rg (.z 10)) (rg (.z 7)) (rg (.z 8))) <|
  .seq (moveR (rg (.z 9)) (io .lE) id) <| .seq (bclear (rg (.v 4))) (moveR (rg (.z 10)) (rg (.v 4)) id)

theorem dsyLoadE_runs {rg : TblR 40 → Fin T} {io : DsX → Fin T} (hrg : Function.Injective rg)
    (hdisj : ∀ r x, rg r ≠ io x) (R : Regs T A) {W e E : ℕ} (hE : R (io .lE) = binSyms (W + e) E)
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (σ : Fin 40 → ℕ) :
    dsyRuns body (dsyLoadE rg io) (dsOv rg R (tblRho W wl nl ⟨σ, []⟩))
      (dsOv rg R (tblRho W wl nl ⟨Function.update σ 4 E, []⟩)) (18 * W + 16) := by
  set R₀ := dsOv rg R (tblRho W wl nl ⟨σ, []⟩) with hR₀
  have lr : ∀ r, R₀ (rg r) = tblRho W wl nl ⟨σ, []⟩ r := fun r => dsOv_rg hrg _ _ r
  have li : ∀ x, R₀ (io x) = R (io x) := fun x => dsOv_off _ _ (fun r => hdisj r x)
  have hE0 : R₀ (io .lE) = binSyms (W + e) E := by rw [li, hE]
  have n89 : rg (.z 8) ≠ rg (.z 9) := hrg.ne (by decide)
  have n79 : rg (.z 7) ≠ rg (.z 9) := hrg.ne (by decide)
  have n78 : rg (.z 7) ≠ rg (.z 8) := hrg.ne (by decide)
  have n910 : rg (.z 9) ≠ rg (.z 10) := hrg.ne (by decide)
  have n710 : rg (.z 7) ≠ rg (.z 10) := hrg.ne (by decide)
  have n810 : rg (.z 8) ≠ rg (.z 10) := hrg.ne (by decide)
  have nw8 : rg .wr ≠ rg (.z 8) := hrg.ne (by decide)
  have nw9 : rg .wr ≠ rg (.z 9) := hrg.ne (by decide)
  have n4_10 : rg (.v 4) ≠ rg (.z 10) := hrg.ne (by decide)
  -- 1: the transfer
  have s1 := dsyRuns_xfer (body := body) (cnt := rg .wr) (t := rg (.z 8)) (src := io .lE)
    (dst := rg (.z 9)) (by
      have := hdisj .wr .lE; have := hdisj (.z 8) .lE; have := hdisj (.z 9) .lE
      regs_nodup) R₀ (by rw [lr]; rfl) (by rw [lr, hE0]; simp [hwl])
  rw [lr .wr, tblRho_wr, hwl, hE0, lr (.z 9), tblRho_z, List.append_nil] at s1
  set R₁ := Function.update (Function.update R₀ (io .lE) ((binSyms (W + e) E).drop W)) (rg (.z 9))
    (((binSyms (W + e) E).take W).reverse) with hR₁
  have l1 : ∀ k, k ≠ io .lE → k ≠ rg (.z 9) → R₁ k = R₀ k := fun k h1 h2 => by
    rw [hR₁, Function.update_of_ne h2, Function.update_of_ne h1]
  -- 2: the copy
  have s2 := dsyRuns_bcopy (body := body) (a := rg (.z 9)) (c := rg (.z 10)) (t₁ := rg (.z 7))
    (t₂ := rg (.z 8)) (by regs_nodup) R₁ (by rw [l1 _ (hdisj _ _) n79, lr]; rfl)
    (by rw [l1 _ (hdisj _ _) n89, lr]; rfl)
  have e1z : R₁ (rg (.z 9)) = ((binSyms (W + e) E).take W).reverse := by
    rw [hR₁, Function.update_self]
  have e1t : R₁ (rg (.z 10)) = [] := by rw [l1 _ (hdisj _ _) n910.symm, lr]; rfl
  rw [e1z, e1t, List.append_nil] at s2
  set R₂ := Function.update R₁ (rg (.z 10)) (((binSyms (W + e) E).take W).reverse) with hR₂
  -- 3: restore lE
  have s3 := dsyRuns_moveR (body := body) (hdisj (.z 9) .lE) R₂
  have e2z : R₂ (rg (.z 9)) = ((binSyms (W + e) E).take W).reverse := by
    rw [hR₂, Function.update_of_ne n910, e1z]
  have e2E : R₂ (io .lE) = (binSyms (W + e) E).drop W := by
    rw [hR₂, Function.update_of_ne (hdisj _ _).symm, hR₁, Function.update_of_ne (hdisj _ _).symm,
      Function.update_self]
  rw [e2z, e2E, List.reverse_reverse, List.take_append_drop] at s3
  set R₃ := Function.update (Function.update R₂ (rg (.z 9)) []) (io .lE) (binSyms (W + e) E)
    with hR₃
  -- 4: clear the variable
  have s4 := dsyRuns_bclear (body := body) (rg (.v 4)) R₃
  set R₄ := Function.update R₃ (rg (.v 4)) [] with hR₄
  -- 5: move the bits in
  have s5 := dsyRuns_moveR (body := body) n4_10.symm R₄
  have e4t : R₄ (rg (.z 10)) = ((binSyms (W + e) E).take W).reverse := by
    rw [hR₄, Function.update_of_ne n4_10.symm, hR₃, Function.update_of_ne (hdisj _ _),
      Function.update_of_ne n910.symm, hR₂, Function.update_self]
  have e4v : R₄ (rg (.v 4)) = [] := by rw [hR₄, Function.update_self]
  rw [e4t, e4v, List.reverse_reverse, List.append_nil, tbl_take_binSyms] at s5
  refine ((s1.seq (s2.seq (s3.seq (s4.seq s5)))).congr ?_).mono ?_
  · funext k
    by_cases hk : ∃ r, rg r = k
    · obtain ⟨r, rfl⟩ := hk
      rw [dsOv_rg hrg]
      by_cases hr4 : r = .v 4
      · subst hr4
        rw [Function.update_self]; rfl
      rw [Function.update_of_ne (hrg.ne hr4)]
      by_cases hr10 : r = .z 10
      · subst hr10
        rw [Function.update_self]; rfl
      rw [Function.update_of_ne (hrg.ne hr10), hR₄, Function.update_of_ne (hrg.ne hr4), hR₃,
        Function.update_of_ne (hdisj _ _)]
      by_cases hr9 : r = .z 9
      · subst hr9
        rw [Function.update_self]; rfl
      rw [Function.update_of_ne (hrg.ne hr9), hR₂, Function.update_of_ne (hrg.ne hr10),
        l1 _ (hdisj _ _) (hrg.ne hr9), lr]
      rcases r with i | _ | _ | _ | j
      · have hi : i ≠ 4 := fun h => hr4 (by rw [h])
        simp [tblRho, Function.update_of_ne hi]
      · rfl
      · rfl
      · rfl
      · rfl
    · push Not at hk
      rw [dsOv_off _ _ hk, Function.update_of_ne (hk _).symm, Function.update_of_ne (hk _).symm,
        hR₄, Function.update_of_ne (hk _).symm, hR₃]
      by_cases hkE : k = io .lE
      · rw [hkE, Function.update_self, ← hE, ← li]
      rw [Function.update_of_ne hkE, Function.update_of_ne (hk _).symm, hR₂,
        Function.update_of_ne (hk _).symm, l1 _ hkE (hk _).symm, hR₀, dsOv_off _ _ hk]
  · have e3v : R₃ (rg (.v 4)) = binSyms W (σ 4) := by
      rw [hR₃, Function.update_of_ne (hdisj _ _), Function.update_of_ne (hrg.ne (by decide)), hR₂,
        Function.update_of_ne (hrg.ne (by decide)), l1 _ (hdisj _ _) (hrg.ne (by decide)), lr]
      rfl
    rw [e3v]
    simp only [List.length_reverse, List.length_take, length_binSyms, min_eq_left
      (Nat.le_add_right W e)]
    omega

/-! ### The prefix moves, with the emissions discarded -/

/-- The prefix moves of the layout; their emissions are discarded. -/
def dsyPhase0 (rg : TblR 40 → Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg ldw1Code) (bclear (rg .acc))

theorem dsyPhase0_runs {rg : TblR 40 → Fin T} (hrg : Function.Injective rg) {W : ℕ}
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = 1) (h1W : 1 ≤ W)
    {es : List ℕ} {ℓ K E : ℕ} (H : LayHyp es ℓ K)
    (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2) (st : TblSt 40 A)
    (hN : st.val 0 = es.sum) (hL : st.val 1 = ℓ) (hK : st.val 2 = K)
    (hD : st.val 3 = es.length) (hEv : st.val 4 = E) (hacc : st.acc = [])
    (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hNW : es.sum < W) (h2W : 2 ≤ W) (hℓW : ℓ < 2 ^ W)
    (hst : ∀ j, st.val j < 2 ^ W) (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    ∃ st' : TblSt 40 A, DsyInv st' es ℓ K E ∧ (∀ j, st'.val j < 2 ^ W) ∧
      dsyRuns body (dsyPhase0 rg) R (dsOv rg R (tblRho W wl nl ⟨st'.val, []⟩))
        (ldw1Atoms es.sum es.length (layB ℓ K) * tblC W 1 + (2 * es.sum + 2)) := by
  obtain ⟨st', ⟨hinv, hlen⟩, hlt, hr⟩ := dsyRuns_host (body := body) hrg wl nl hwl hnl h1W
    (dsyLay_do (W := W) H hE st hN hL hK hD hEv hW hNW h2W hℓW) hst R hR
  refine ⟨st', hinv, hlt, ?_⟩
  have hc := dsyRuns_bclear (body := body) (rg .acc) (dsOv rg R (tblRho W wl nl st'))
  rw [dsOv_rg hrg, tblRho_acc] at hc
  refine ((hr.seq hc).congr ?_).mono ?_
  · rw [dsOv_update_on hrg, tblRho_acc_nil]
  · rw [hlen, hacc, List.length_nil]
    have := layPre_length_le H
    omega

/-! ### The whole machine -/

/-- The registers of the layout cleared at the end: the variables, `wr`, `wn`. -/
def dsyAllRegs : List (TblR 40) := (List.finRange 40).map TblR.v ++ [.wr, .wn]

theorem dsyClearAll_runs {rg : TblR 40 → Fin T} (hrg : Function.Injective rg) (R : Regs T A)
    {W : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = 1)
    (h1W : 1 ≤ W) (σ : Fin 40 → ℕ) :
    dsyRuns body (dsyClearL rg dsyAllRegs) (dsOv rg R (tblRho W wl nl ⟨σ, []⟩))
      (dsOv rg R fun _ => []) (42 * (2 * W + 2) + 1) := by
  have h := dsyClearL_runs (body := body) hrg W dsyAllRegs (dsOv rg R (tblRho W wl nl ⟨σ, []⟩))
    (fun r hr => by
      rw [dsOv_rg hrg]
      rcases r with i | _ | _ | _ | j
      · simp
      · simp [hwl]
      · simp [hnl, h1W]
      · simp
      · simp)
  rw [show dsyAllRegs.length = 42 by rfl] at h
  refine h.congr ?_
  funext k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hk
    simp only [dsOv_rg hrg]
    rcases r with i | _ | _ | _ | j
    · rw [ite_eq_left ⟨.v i, by simp [dsyAllRegs], rfl⟩]
    · rw [ite_eq_left ⟨.wr, by simp [dsyAllRegs], rfl⟩]
    · rw [ite_eq_left ⟨.wn, by simp [dsyAllRegs], rfl⟩]
    · rw [ite_eq_right (by rintro ⟨r, hr, h⟩; have := hrg h; subst this; simp [dsyAllRegs] at hr)]; rfl
    · rw [ite_eq_right (by rintro ⟨r, hr, h⟩; have := hrg h; subst this; simp [dsyAllRegs] at hr)]; rfl
  · push Not at hk
    rw [dsOv_off _ _ hk, ite_eq_right (by rintro ⟨r, -, h⟩; exact hk _ h), dsOv_off _ _ hk]

/-- **The wire machine.** -/
def dsySyn (rg : TblR 40 → Fin T) (io : DsX → Fin T) (oPark oB oLg oL oNr oRec oPos : Fin T) :
    Pr P T Q A U :=
  .seq (dsyParkP rg io oPark) <| .seq (dsyWidth rg io) <|
  .seq (dsyZeroVars rg (List.finRange 40)) <| .seq (dsyLoads rg io) <| .seq (dsyLoadE rg io) <|
  .seq (dsyPhase0 rg) <| .seq (dsyPhase rg dsyCodeB oB) <| .seq (dsyPhase rg dsyCodeLg oLg) <|
  .seq (dsyPhase rg dsyCodeL oL) <| .seq (dsyPhase rg dsyCodeNr oNr) <|
  .seq (dsyPhase rg dsyCodeRec oRec) <| .seq (dsyPhase rg dsyCodePos oPos) <|
  dsyClearL rg dsyAllRegs

/-- The atoms of the table phases. -/
def dsyAtoms (N ℓ K D : ℕ) : ℕ :=
  ldw1Atoms N D (layB ℓ K) + dsyLoopAtoms (layB ℓ K) + dsyLgAtoms N + dsyLoopAtoms ℓ +
    dsyNrAtoms ℓ + dsyRecAtoms D ℓ + dsyPosAtoms N

/-- The step bound of `dsySyn`, for `N = es.sum`, `D = es.length`, the word width
`W = dsyW N ℓ`. -/
def dsySynCostG (N ℓ K D WL : ℕ) : ℕ :=
  dsyParkCost WL ℓ D + dsyWidthCost N ℓ + (40 * (4 * dsyW N ℓ + 4) + 1) +
    dsyLoadsCost N ℓ K D (dsyW N ℓ) + (18 * dsyW N ℓ + 16) +
    dsyAtoms N ℓ K D * tblC (dsyW N ℓ) 1 +
    (2 * (N + K + N + ℓ + ℓ + D * (ℓ + 1) + N * N) + 14) + (42 * (2 * dsyW N ℓ + 2) + 1)

theorem dsy_mem_replicate_tick (n : ℕ) :
    ∀ x ∈ (List.replicate n tick : List (Fin (A + 4))), x = tick ∨ x = bitSymbol false := by
  intro x hx
  exact Or.inl (List.eq_of_mem_replicate hx)

theorem dsy_mem_topRec (es : List ℕ) :
    ∀ x ∈ (topRec es : List (Fin (A + 4))), x = tick ∨ x = bitSymbol false := by
  intro x hx
  simp only [topRec, List.mem_flatMap, List.mem_append, List.mem_replicate, List.mem_singleton]
    at hx
  obtain ⟨a, -, h | h⟩ := hx
  · exact Or.inl h.2
  · exact Or.inr h

theorem dsy_mem_twPosReg (N : ℕ) (P : ℕ → ℕ) :
    ∀ x ∈ (twPosReg A N P : List (Fin (A + 4))), x = tick ∨ x = bitSymbol false := by
  intro x hx
  simp only [twPosReg, twBlock, List.mem_flatMap, List.mem_append, List.mem_replicate] at hx
  obtain ⟨a, -, h | h⟩ := hx
  · exact Or.inl h.2
  · exact Or.inr h.2

theorem dsy_length_topRec_le {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) :
    (topRec es : List (Fin (A + 4))).length ≤ es.length * (ℓ + 1) := by
  rw [length_topRec]
  have : ∀ x ∈ es.map (· + 1), x ≤ ℓ + 1 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    rcases H.widths e he with h | h <;> omega
  calc (es.map (· + 1)).sum ≤ (es.map (· + 1)).length * (ℓ + 1) := List.sum_le_length_nsmul _ _ this
    _ = es.length * (ℓ + 1) := by rw [List.length_map]

theorem dsy_length_twPosReg (N : ℕ) (P : ℕ → ℕ) (hP : ∀ k < N, P k ≤ N) :
    (twPosReg A N P : List (Fin (A + 4))).length = N * N := by
  rw [twPosReg, tw_length_flatMap_const _ _ N (fun k hk => twBlock_length (hP k (by simpa using hk))),
    List.length_reverse, List.length_range]

/-- **The wire machine.** From the unary `N, ℓ, K, D, W_L` and the word `binSyms W_L E` on
`io`, the layout `rg` empty, `dsySyn` leaves the park record on `oPark`, the unary wires on
`oB`, `oLg`, `oL`, `oNr`, the axis record on `oRec`, the position table on `oPos` (each on top
of the register's old contents), the layout empty, every other register as it started. -/
theorem dsySyn_runs (hA : 4 ≤ A) {rg : TblR 40 → Fin T} (hrg : Function.Injective rg)
    {io : DsX → Fin T} (hdisj : ∀ r x, rg r ≠ io x) {oPark oB oLg oL oNr oRec oPos : Fin T}
    (hnd : [oPark, oB, oLg, oL, oNr, oRec, oPos].Nodup)
    (hor : ∀ o ∈ [oPark, oB, oLg, oL, oNr, oRec, oPos], ∀ r, rg r ≠ o)
    (hoi : ∀ o ∈ [oPark, oB, oLg, oL, oNr, oRec, oPos], ∀ x, io x ≠ o)
    {es : List ℕ} {ℓ K E WL : ℕ} (H : LayHyp es ℓ K)
    (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2) (hED : E < 2 ^ es.length)
    (hWL : dsyW es.sum ℓ ≤ WL) (hEW : E < 2 ^ WL) (R : Regs T A) (hrg0 : ∀ r, R (rg r) = [])
    (hN : R (io .lN) = List.replicate es.sum tick) (hL : R (io .lL) = List.replicate ℓ tick)
    (hK : R (io .lK) = List.replicate K tick) (hD : R (io .lD) = List.replicate es.length tick)
    (hlE : R (io .lE) = binSyms WL E) (hlW : R (io .lW) = List.replicate WL tick) :
    dsyRuns body (dsySyn rg io oPark oB oLg oL oNr oRec oPos) R
      (dsOv rg (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update R
          oPark (dsyParkL A (WL + ℓ + es.length) E ++ R oPark))
          oB (List.replicate (layB ℓ K) tick ++ R oB))
          oLg (List.replicate (layLongs es ℓ).length tick ++ R oLg))
          oL (List.replicate ℓ tick ++ R oL))
          oNr (List.replicate (dsyNr es.sum es.length ℓ) tick ++ R oNr))
          oRec (topRec es ++ R oRec))
          oPos (twPosReg A es.sum (twPosL (layPerm es ℓ K)) ++ R oPos)) fun _ => [])
      (dsySynCostG es.sum ℓ K es.length WL) := by
  have hnd' := hnd
  regs_ne hnd'
  obtain ⟨hW1, hNW, h2W, hℓW, hDW, hKW⟩ := dsyW_ok H
  set N := es.sum with hNdef
  set D := es.length with hDdef
  set W := dsyW N ℓ with hWdef
  have hDN := ldw_length_le_sum H
  have hℓ := H.ℓ_ge
  have hNW2 : N < 2 ^ W := lt_trans hNW Nat.lt_two_pow_self
  have hEWW : E < 2 ^ W :=
    lt_of_lt_of_le hED (Nat.pow_le_pow_right (by norm_num) (le_trans hDN hNW.le))
  have h1W : 1 ≤ W := by omega
  set wl : List (Fin (A + 4)) := List.replicate W tick with hwl
  set nl : List (Fin (A + 4)) := [tick] with hnl
  have hwll : wl.length = W := by simp [hwl]
  have hnll : nl.length = 1 := by simp [hnl]
  have hPk := hor oPark (by simp)
  have hPi := hoi oPark (by simp)
  -- the park
  have sP := dsyParkP_runs (body := body) hrg hdisj hPk hPi R (WL := WL) (ℓ := ℓ) (D := D)
    (E := E) hEW (by simp [hlW]) (by simp [hL]) (by simp [hD]) hlE (hrg0 _) (hrg0 _) (hrg0 _)
  set R₀ := Function.update R oPark (dsyParkL A (WL + ℓ + D) E ++ R oPark) with hR₀
  have l0 : ∀ k, k ≠ oPark → R₀ k = R k := fun k hk => by rw [hR₀, Function.update_of_ne hk]
  have hrg1 : ∀ r, R₀ (rg r) = [] := fun r => by rw [l0 _ (hPk r), hrg0]
  have li : ∀ x, R₀ (io x) = R (io x) := fun x => l0 _ (hPi x)
  -- the width
  have sW := dsyWidth_runs (body := body) hrg hdisj R₀ (N := N) (ℓ := ℓ) (by simp [li, hN])
    (by simp [li, hL]) (hrg1 _) (hrg1 _) (hrg1 _) (hrg1 _) (hrg1 _)
  -- the variables
  have sZ := dsyZeroAll_runs (body := body) hrg R₀ hrg1 W
  -- the loads
  have sL := dsyLoads_runs (body := body) hrg hdisj R₀ (N := N) (ℓ := ℓ) (K := K) (D := D)
    (by simp [li, hN]) (by simp [li, hL]) (by simp [li, hK]) (by simp [li, hD]) wl nl hwll
  set σ₄ : Fin 40 → ℕ := Function.update (Function.update (Function.update (Function.update
    (fun _ => 0) 0 N) 1 ℓ) 2 K) 3 D with hσ₄
  have sE := dsyLoadE_runs (body := body) hrg hdisj R₀ (W := W) (e := WL - W) (E := E)
    (by rw [li, hlE, Nat.add_sub_cancel' hWL]) wl nl hwll σ₄
  -- the prefix moves
  set σ₅ : Fin 40 → ℕ := Function.update σ₄ 4 E with hσ₅
  have hst₅ : ∀ j, σ₅ j < 2 ^ W := by
    intro j
    simp only [hσ₅, hσ₄, Function.update_apply]
    split_ifs <;> first | assumption | exact Nat.two_pow_pos W
  obtain ⟨st₀, hinv₀, hlt₀, s0⟩ := dsyPhase0_runs (body := body) hrg wl nl hwll hnll h1W H hE
    ⟨σ₅, []⟩ (by simp [hσ₅, hσ₄, hNdef]) (by simp [hσ₅, hσ₄]) (by simp [hσ₅, hσ₄])
    (by simp [hσ₅, hσ₄, hDdef]) (by simp [hσ₅]) rfl hW1 hNW h2W hℓW hst₅ (dsOv rg R₀ (tblRho W wl nl ⟨σ₅, []⟩))
    (fun r => dsOv_rg hrg _ _ r)
  rw [dsOv_dsOv] at s0
  -- the phases
  have hDL : D * (ℓ - 1) ≤ N := by rw [hNdef, hDdef]; have := lay_sum H; omega
  have hLg : N - D * (ℓ - 1) = (layLongs es ℓ).length := by
    rw [hNdef, hDdef]; have := lay_sum H; omega
  have hrep : ∀ n, (List.replicate n (dsyT A)).reverse.map (dsyH A) = List.replicate n tick := by
    intro n
    rw [List.reverse_replicate, List.map_replicate, ← dsyEnc_tick, dsyH_enc hA (Or.inl rfl)]
  have hlist : ∀ l : List (Fin (A + 4)), (∀ x ∈ l, x = tick ∨ x = bitSymbol false) →
      ((l.map (dsyEnc A)).reverse).reverse.map (dsyH A) = l := fun l hl => by
    rw [List.reverse_reverse, dsyH_map hA l hl]
  -- B
  obtain ⟨st₁, ⟨hinv₁, hacc₁⟩, hlt₁, s1⟩ := dsyPhase_runs (body := body) hrg (hor oB (by simp only [List.mem_cons, true_or, or_true]))
    wl nl hwll hnll h1W (dsyCodeB_do (W := W) ⟨st₀.val, []⟩ (hinv₀.reacc []) hℓW (by omega)) hlt₀
    (dsOv rg R₀ (tblRho W wl nl ⟨st₀.val, []⟩)) (fun r => dsOv_rg hrg _ _ r)
  simp only [List.append_nil] at hacc₁
  rw [hacc₁, hrep, dsOv_off _ _ (hor oB (by simp only [List.mem_cons, true_or, or_true])), l0 _ ‹oPark ≠ oB›.symm,
    dsOv_update _ _ (hor oB (by simp only [List.mem_cons, true_or, or_true])), dsOv_dsOv] at s1
  set R₁ := Function.update R₀ oB (List.replicate (layB ℓ K) tick ++ R oB) with hR₁
  have l1 : ∀ k, k ≠ oPark → k ≠ oB → R₁ k = R k := fun k h0 h1 => by
    rw [hR₁, Function.update_of_ne h1, l0 _ h0]
  have hc₁ : st₁.acc.length ≤ K := by rw [hacc₁, List.length_replicate]; exact H.b_lt.le
  -- Lg
  obtain ⟨st₂, ⟨hinv₂, hacc₂⟩, hlt₂, s2⟩ := dsyPhase_runs (body := body) hrg (hor oLg (by simp only [List.mem_cons, true_or, or_true]))
    wl nl hwll hnll h1W (dsyCodeLg_do (W := W) ⟨st₁.val, []⟩ (hinv₁.reacc []) hNW2 hDL) hlt₁
    (dsOv rg R₁ (tblRho W wl nl ⟨st₁.val, []⟩)) (fun r => dsOv_rg hrg _ _ r)
  simp only [List.append_nil] at hacc₂
  rw [hacc₂, hrep, hLg, dsOv_off _ _ (hor oLg (by simp only [List.mem_cons, true_or, or_true])), l1 _ ‹oPark ≠ oLg›.symm ‹oB ≠ oLg›.symm,
    dsOv_update _ _ (hor oLg (by simp only [List.mem_cons, true_or, or_true])), dsOv_dsOv] at s2
  set R₂ := Function.update R₁ oLg (List.replicate (layLongs es ℓ).length tick ++ R oLg) with hR₂
  have l2 : ∀ k, k ≠ oPark → k ≠ oB → k ≠ oLg → R₂ k = R k := fun k h0 h1 h2 => by
    rw [hR₂, Function.update_of_ne h2, l1 _ h0 h1]
  have hc₂ : st₂.acc.length ≤ N := by rw [hacc₂, List.length_replicate]; omega
  -- L
  obtain ⟨st₃, ⟨hinv₃, hacc₃⟩, hlt₃, s3⟩ := dsyPhase_runs (body := body) hrg (hor oL (by simp only [List.mem_cons, true_or, or_true]))
    wl nl hwll hnll h1W (dsyCodeL_do (W := W) ⟨st₂.val, []⟩ (hinv₂.reacc []) hℓW) hlt₂
    (dsOv rg R₂ (tblRho W wl nl ⟨st₂.val, []⟩)) (fun r => dsOv_rg hrg _ _ r)
  simp only [List.append_nil] at hacc₃
  rw [hacc₃, hrep, dsOv_off _ _ (hor oL (by simp only [List.mem_cons, true_or, or_true])),
    l2 _ ‹oPark ≠ oL›.symm ‹oB ≠ oL›.symm ‹oLg ≠ oL›.symm,
    dsOv_update _ _ (hor oL (by simp only [List.mem_cons, true_or, or_true])), dsOv_dsOv] at s3
  set R₃ := Function.update R₂ oL (List.replicate ℓ tick ++ R oL) with hR₃
  have l3 : ∀ k, k ≠ oPark → k ≠ oB → k ≠ oLg → k ≠ oL → R₃ k = R k := fun k h0 h1 h2 h3 => by
    rw [hR₃, Function.update_of_ne h3, l2 _ h0 h1 h2]
  have hc₃ : st₃.acc.length ≤ ℓ := by rw [hacc₃, List.length_replicate]
  -- Nr
  obtain ⟨st₄, ⟨hinv₄, hacc₄⟩, hlt₄, s4⟩ := dsyPhase_runs (body := body) hrg (hor oNr (by simp only [List.mem_cons, true_or, or_true]))
    wl nl hwll hnll h1W (dsyCodeNr_do (W := W) ⟨st₃.val, []⟩ (hinv₃.reacc []) hNW2 hℓW hDL) hlt₃
    (dsOv rg R₃ (tblRho W wl nl ⟨st₃.val, []⟩)) (fun r => dsOv_rg hrg _ _ r)
  simp only [List.append_nil] at hacc₄
  rw [hacc₄, hrep, dsOv_off _ _ (hor oNr (by simp only [List.mem_cons, true_or, or_true])),
    l3 _ ‹oPark ≠ oNr›.symm ‹oB ≠ oNr›.symm ‹oLg ≠ oNr›.symm ‹oL ≠ oNr›.symm,
    dsOv_update _ _ (hor oNr (by simp only [List.mem_cons, true_or, or_true])), dsOv_dsOv] at s4
  set R₄ := Function.update R₃ oNr (List.replicate (dsyNr N D ℓ) tick ++ R oNr) with hR₄
  have l4 : ∀ k, k ≠ oPark → k ≠ oB → k ≠ oLg → k ≠ oL → k ≠ oNr → R₄ k = R k :=
    fun k h0 h1 h2 h3 h4 => by rw [hR₄, Function.update_of_ne h4, l3 _ h0 h1 h2 h3]
  have hc₄ : st₄.acc.length ≤ ℓ := by
    rw [hacc₄, List.length_replicate]; unfold dsyNr; split_ifs <;> omega
  -- the record
  obtain ⟨st₅, ⟨hinv₅, hacc₅⟩, hlt₅, s5⟩ := dsyPhase_runs (body := body) hrg (hor oRec (by simp only [List.mem_cons, true_or, or_true]))
    wl nl hwll hnll h1W (dsyCodeRec_do (W := W) H hE ⟨st₄.val, []⟩ (hinv₄.reacc []) hNW hℓW) hlt₄
    (dsOv rg R₄ (tblRho W wl nl ⟨st₄.val, []⟩)) (fun r => dsOv_rg hrg _ _ r)
  simp only [List.append_nil] at hacc₅
  rw [hacc₅, hlist _ (dsy_mem_topRec es), dsOv_off _ _ (hor oRec (by simp only [List.mem_cons, true_or, or_true])),
    l4 _ ‹oPark ≠ oRec›.symm ‹oB ≠ oRec›.symm ‹oLg ≠ oRec›.symm ‹oL ≠ oRec›.symm
      ‹oNr ≠ oRec›.symm,
    dsOv_update _ _ (hor oRec (by simp only [List.mem_cons, true_or, or_true])), dsOv_dsOv] at s5
  set R₅ := Function.update R₄ oRec (topRec es ++ R oRec) with hR₅
  have l5 : ∀ k, k ≠ oPark → k ≠ oB → k ≠ oLg → k ≠ oL → k ≠ oNr → k ≠ oRec → R₅ k = R k :=
    fun k h0 h1 h2 h3 h4 h5 => by rw [hR₅, Function.update_of_ne h5, l4 _ h0 h1 h2 h3 h4]
  have hc₅ : st₅.acc.length ≤ D * (ℓ + 1) := by
    rw [hacc₅, List.length_reverse, List.length_map]; exact dsy_length_topRec_le H
  -- the positions
  obtain ⟨st₆, ⟨hinv₆, hacc₆⟩, hlt₆, s6⟩ := dsyPhase_runs (body := body) hrg (hor oPos (by simp only [List.mem_cons, true_or, or_true]))
    wl nl hwll hnll h1W (dsyCodePos_do (W := W) H ⟨st₅.val, []⟩ (hinv₅.reacc []) hW1 hNW) hlt₅
    (dsOv rg R₅ (tblRho W wl nl ⟨st₅.val, []⟩)) (fun r => dsOv_rg hrg _ _ r)
  simp only [List.append_nil] at hacc₆
  have hposeq : twPosReg A N (dsyPos es ℓ K) = twPosReg A N (twPosL (layPerm es ℓ K)) :=
    dsyPosReg_congr N _ _ fun k hk => dsyPos_eq H hk
  rw [hacc₆, hlist _ (dsy_mem_twPosReg _ _), hposeq, dsOv_off _ _ (hor oPos (by simp only [List.mem_cons, true_or, or_true])),
    l5 _ ‹oPark ≠ oPos›.symm ‹oB ≠ oPos›.symm ‹oLg ≠ oPos›.symm ‹oL ≠ oPos›.symm
      ‹oNr ≠ oPos›.symm ‹oRec ≠ oPos›.symm,
    dsOv_update _ _ (hor oPos (by simp only [List.mem_cons, true_or, or_true])), dsOv_dsOv] at s6
  have hc₆ : st₆.acc.length ≤ N * N := by
    rw [hacc₆, List.length_reverse, List.length_map, hposeq,
      dsy_length_twPosReg N _ (fun k hk => (twPosL_lt _ k hk).le)]
  -- the clearing
  have sC := dsyClearAll_runs (body := body) hrg
    (Function.update R₅ oPos (twPosReg A N (twPosL (layPerm es ℓ K)) ++ R oPos)) wl nl hwll hnll
    h1W st₆.val
  have hall := sP.seq (sW.seq (sZ.seq (sL.seq (sE.seq (s0.seq (s1.seq (s2.seq (s3.seq (s4.seq
    (s5.seq (s6.seq sC)))))))))))
  refine (hall.congr rfl).mono ?_
  have hb : layB ℓ K ≤ K := H.b_lt.le
  have hLgN : (layLongs es ℓ).length ≤ N := by rw [hNdef]; have := lay_sum H; omega
  have hrec := dsy_length_topRec_le (A := A) H
  have hpos := dsy_length_twPosReg (A := A) N (twPosL (layPerm es ℓ K))
    (fun k hk => (twPosL_lt _ k hk).le)
  have hnr : dsyNr N D ℓ ≤ ℓ := by unfold dsyNr; split_ifs <;> omega
  unfold dsySynCostG dsyAtoms
  simp only [Nat.add_mul, List.length_replicate, List.length_reverse, List.length_map, ← hNdef,
    ← hDdef]
  rw [hpos]
  linarith

end IntegerMultBounds.MathlibTM2.Fast.TableVM
