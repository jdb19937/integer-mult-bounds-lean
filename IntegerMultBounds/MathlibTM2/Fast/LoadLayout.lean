module

public import IntegerMultBounds.MathlibTM2.Fast.Layout
public import IntegerMultBounds.MathlibTM2.Fast.TableVM

/-!
# The loaders of the layout machine

Paper §6, proof of `lem:synthetic-transform-cost`: the per-move parameter loaders `prepM`,
`prepX` that `IntegerMultBounds.MathlibTM2.Fast.layApply` takes as hypotheses, reading the moves from description
streams in registers, and the layout stage without loader hypotheses.

## Registers

`lr : LdlReg → Fin T`, injective and disjoint from the layout registers `rg`: the description
streams `dM` (single-bit moves) and `dX` (chunk exchanges), the word counters `cN` (`n`
symbols) and `cW` (`wX` symbols), the bit buffers `tA`, `tB` and the counter spare `tS` (empty).

## Stream formats

Words are the pair symbols `tblPairs A w x y` of the table machine (`IntegerMultBounds.MathlibTM2.Fast.TableVM`):
symbol `t < w` is `pairSym A (x.testBit t) (y.testBit t)`, least significant first.
* Single-bit move `(a, b)`: one word `tblPairs A n (2 ^ a) (2 ^ b)` (`ldlBitRec`); the stream
  `ldlBitStream A n bs` is the records of the moves `bs` in order, the first on top.
* Exchange with header counters `hs`: five words `tblPairs A wX (value (hs k)) 0`, `k < 5`
  (`ldlXcRec`); the stream `ldlXcStream A wX xs` lists the exchanges in order.

## Loaders

* `ldlWord src cnt sp a b`: per symbol of the counter `cnt`, pop a pair symbol of `src` and push
  its real bit onto `a` and its imaginary bit onto `b` (`ldl_word_runs`, `6 |cnt| + 4` steps).
* `ldlStrip a`: pop the symbols `bitSymbol false` from the top of `a` (`ldl_strip_runs`).
* `ldlPrepM rg lr`: clear the masks `mA`, `mB`, read one word of `n` symbols of `dM`, and move
  its real bits onto `mA` and its imaginary bits onto `mB`: the masks `binSyms n (2 ^ a)`,
  `binSyms n (2 ^ b)` of the move (`ldl_prepM_runs`, `2 |mA| + 2 |mB| + 10 n + 12` steps).
* `ldlPrepX hd rg lr`: for each header register `sw (reg (hd k))`: clear it, read one word of
  `wX` symbols of `dX`, strip the zero bits above the highest one, and write
  `separator :: (hs k).map bitSymbol` (`ldl_hdr_runs`; at most `2 |old| + 12 wX + 13` steps per
  header).

## The layout stage

`ldlW`: the register files before each move (masks of the previous move, the remaining
streams); `ldl_prepM_loads`, `ldl_prepX_loads`: the loader contracts `LayLoads` of
`layApply_exec_gen`. `ldLayStage_exec`: from the description streams of `layBits es ℓ K` and
`layXcs es ℓ K B` the layout machine `layApply … (ldlPrepM rg lr) (ldlPrepX hd rg lr)` moves the
stream by `layPerm es ℓ K` with the explicit cost of `layApply_exec`, loaders of at most
`14 n + 12` and `70 wX + 75` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ### Runs of the basic programs -/

section Basic

variable {T Q A : ℕ} {U F : Type} {body : F → Pr F T Q A U}

theorem ldl_uclear_runs (a : Fin T) (R : Fin T → List (Fin (A + 4))) :
    LayRuns body (uclear a) R (Function.update R a []) (2 * (R a).length + 2) := by
  intro v S hL hS
  obtain ⟨v', hu, he⟩ := uclear_exec body a v S
  rw [hS] at he
  exact ⟨v', _, hu, le_rfl, he⟩

theorem ldl_moveR_runs {i j : Fin T} (hij : i ≠ j) (R : Fin T → List (Fin (A + 4))) :
    LayRuns body (moveR i j id) R (Function.update (Function.update R i []) j ((R i).reverse ++ R j))
      (2 * (R i).length + 2) := by
  intro v S hL hS
  obtain ⟨v', hu, he⟩ := moveR_exec body i j hij id v S
  rw [hS] at he
  refine ⟨v', _, hu, le_rfl, ?_⟩
  simpa [movedR] using he

theorem ldl_push_runs (d : Fin T) (x : Fin (A + 4)) (R : Fin T → List (Fin (A + 4))) :
    LayRuns body (.act (.push (.rt d) (fun _ => x) .done)) R (Function.update R d (x :: R d)) 1 := by
  intro v S hL hS
  refine ⟨v, 1, rfl, le_rfl, ?_⟩
  have h := Exec.act (body := body) (.push (.rt d) (fun _ => x) .done) (mk v S)
  have e : (Action.push (.rt d) (fun _ => x) .done : Act T Q A U).run (mk v S) =
      mk v { S with R := Function.update R d (x :: R d) } := by
    simp [Action.run, update_rt, hS]
  rwa [e] at h

theorem LayRuns.congr {p : Pr F T Q A U} {R₀ R₁ R₁' : Fin T → List (Fin (A + 4))} {c : ℕ}
    (h : LayRuns body p R₀ R₁ c) (e : R₁ = R₁') : LayRuns body p R₀ R₁' c := e ▸ h

end Basic

/-! ### Reading a word -/

section Word

variable {T Q A : ℕ} {U F : Type} {body : F → Pr F T Q A U}

/-- Pop a pair symbol of `src`; push its real bit onto `a` and its imaginary bit onto `b`. -/
def ldlSplit (src a b : Fin T) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.push (.rt a) (fun v => bitSymbol (pairRe (v.sym.getD blank)))
      (.push (.rt b) (fun v => bitSymbol (pairIm (v.sym.getD blank))) .done))

/-- Read one word of `|cnt|` pair symbols of `src` onto `a`, `b`, the last symbol on top. -/
def ldlWord (src cnt sp a b : Fin T) : Pr F T Q A U := scanP cnt sp (.act (ldlSplit src a b))

/-- The real bits of a list of pair symbols as bit symbols. -/
def ldlRe (l : List (Fin (A + 4))) : List (Fin (A + 4)) := l.map fun x => bitSymbol (pairRe x)

/-- The imaginary bits of a list of pair symbols as bit symbols. -/
def ldlIm (l : List (Fin (A + 4))) : List (Fin (A + 4)) := l.map fun x => bitSymbol (pairIm x)

/-- The register file after reading the first `i` symbols of the word `ws`. -/
def ldlWordFile (src a b : Fin T) (R : Fin T → List (Fin (A + 4))) (ws rest : List (Fin (A + 4)))
    (i : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update R src (ws.drop i ++ rest)) a
    ((ldlRe (ws.take i)).reverse ++ R a)) b ((ldlIm (ws.take i)).reverse ++ R b)

theorem ldl_split_run {src a b : Fin T} (hsa : src ≠ a) (hsb : src ≠ b) (hab : a ≠ b)
    (x : Fin (A + 4)) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R src = x :: rest) :
    (ldlSplit src a b : Act T Q A U).run (mk v S) = mk { v with sym := some x }
      { S with R := Function.update (Function.update (Function.update S.R src rest) a
        (bitSymbol (pairRe x) :: S.R a)) b (bitSymbol (pairIm x) :: S.R b) } := by
  simp [ldlSplit, Action.run, hS, update_rt, Function.update_of_ne hsa.symm,
    Function.update_of_ne hsb.symm, Function.update_of_ne hab.symm]

/-- **Reading a word.** With `cnt` holding `L` symbols, `sp` empty and `src` holding the word `ws`
of `L` symbols on top of `rest`, `ldlWord` leaves `rest` on `src`, pushes the real bits of `ws`
onto `a` and the imaginary bits onto `b` (the last on top), and restores `cnt`; `6 L + 4`
steps. -/
theorem ldl_word_runs {src cnt sp a b : Fin T} (hreg : [src, cnt, sp, a, b].Nodup)
    (R : Fin T → List (Fin (A + 4))) (ws rest : List (Fin (A + 4)))
    (hsrc : R src = ws ++ rest) (hcnt : (R cnt).length = ws.length) (hsp : R sp = []) :
    LayRuns body (ldlWord src cnt sp a b) R (ldlWordFile src a b R ws rest ws.length)
      (6 * ws.length + 4) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hreg
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7⟩, ⟨h8, h9⟩, h10⟩ := hreg
  have hit : IterSpec body (.act (ldlSplit src a b)) cnt sp (ldlWordFile src a b R ws rest)
      (fun _ => 1) ws.length := by
    intro i hi v S hS
    have hsrcS : S.R src = ws[i] :: (ws.drop (i + 1) ++ rest) := by
      rw [hS src h1 h2]
      simp only [ldlWordFile, Function.update_of_ne h3, Function.update_of_ne h4,
        Function.update_self]
      rw [List.drop_eq_getElem_cons hi]
      rfl
    refine ⟨{ v with sym := some ws[i] }, Function.update (Function.update (Function.update S.R src
      (ws.drop (i + 1) ++ rest)) a (bitSymbol (pairRe ws[i]) :: S.R a)) b
      (bitSymbol (pairIm ws[i]) :: S.R b), 1, rfl, le_rfl, ?_, ?_, ?_, ?_⟩
    · have h := Exec.act (body := body) (ldlSplit src a b) (mk v S)
      rw [ldl_split_run h3 h4 h10 _ _ v S hsrcS] at h
      exact h
    · simp [Function.update_of_ne (Ne.symm h1), Function.update_of_ne h6, Function.update_of_ne h7]
    · simp [Function.update_of_ne (Ne.symm h2), Function.update_of_ne h8, Function.update_of_ne h9]
    · intro k hk1 hk2
      have htake : ws.take (i + 1) = ws.take i ++ [ws[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
      by_cases hkb : k = b
      · rw [hkb, Function.update_self, hS b (Ne.symm h7) (Ne.symm h9)]
        simp only [ldlWordFile, Function.update_self, htake, ldlIm, List.map_append,
          List.map_singleton, List.reverse_append, List.reverse_singleton, List.singleton_append,
          List.cons_append, List.nil_append, List.append_assoc]
      · by_cases hka : k = a
        · rw [hka, Function.update_of_ne h10, Function.update_self, hS a (Ne.symm h6) (Ne.symm h8)]
          simp only [ldlWordFile, Function.update_of_ne h10, Function.update_self, htake, ldlRe,
            List.map_append, List.map_singleton, List.reverse_append, List.reverse_singleton,
            List.singleton_append, List.cons_append, List.nil_append, List.append_assoc]
        · by_cases hks : k = src
          · rw [hks, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_self]
            simp only [ldlWordFile, Function.update_of_ne h4, Function.update_of_ne h3,
              Function.update_self]
          · rw [Function.update_of_ne hkb, Function.update_of_ne hka, Function.update_of_ne hks,
              hS k hk1 hk2]
            simp only [ldlWordFile, Function.update_of_ne hkb, Function.update_of_ne hka,
              Function.update_of_ne hks]
  intro v S hL hS
  have hΨ0 : ∀ k, k ≠ cnt → k ≠ sp → S.R k = ldlWordFile src a b R ws rest 0 k := by
    intro k _ _
    rw [hS]
    simp only [ldlWordFile, List.drop_zero, List.take_zero]
    by_cases hkb : k = b
    · subst hkb; simp [ldlIm]
    · by_cases hka : k = a
      · subst hka; simp [Function.update_of_ne hkb, ldlRe]
      · by_cases hks : k = src
        · subst hks; simp [Function.update_of_ne hkb, Function.update_of_ne hka, hsrc]
        · simp [Function.update_of_ne hkb, Function.update_of_ne hka, Function.update_of_ne hks]
  obtain ⟨v', R', m, hu, hm, he, ha, ht, hk⟩ :=
    scanP_exec body h5 hit 0 v S (by rw [hS, hcnt]; omega) hΨ0
  refine ⟨v', m, hu, ?_, ?_⟩
  · rw [hS, hcnt, hsp] at hm
    refine hm.trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_nil]
    ring
  · have hR' : R' = ldlWordFile src a b R ws rest ws.length := by
      funext k
      by_cases hkc : k = cnt
      · subst hkc
        rw [ha, hS, hsp]
        simp [ldlWordFile, Function.update_of_ne (Ne.symm h1), Function.update_of_ne h6,
          Function.update_of_ne h7]
      · by_cases hks : k = sp
        · subst hks
          rw [ht]
          simp [ldlWordFile, Function.update_of_ne (Ne.symm h2), Function.update_of_ne h8,
            Function.update_of_ne h9, hsp]
        · rw [hk k hkc hks, hS, hcnt]
          simp
    rw [← hR']
    exact he

end Word

/-! ### Stripping zero bits -/

section Strip

variable {T Q A : ℕ} {U F : Type} {body : F → Pr F T Q A U}

/-- Record in `flag` whether the top of `a` is `bitSymbol false`. -/
def ldlPeekF (a : Fin T) : Act T Q A U :=
  .peek (.rt a) (fun v o => { v with flag := decide (o = some (bitSymbol false)) }) .done

/-- Pop the symbols `bitSymbol false` from the top of `a`. -/
def ldlStrip (a : Fin T) : Pr F T Q A U :=
  .seq (.act (ldlPeekF a)) (.loop (·.flag) (.act (.pop (.rt a) (fun v _ => v) (ldlPeekF a))))

/-- A list without its leading symbols `bitSymbol false`. -/
def ldlDropF : List (Fin (A + 4)) → List (Fin (A + 4))
  | [] => []
  | x :: l => if x = bitSymbol false then ldlDropF l else x :: l

/-- The number of leading symbols `bitSymbol false`. -/
def ldlNF : List (Fin (A + 4)) → ℕ
  | [] => 0
  | x :: l => if x = bitSymbol false then ldlNF l + 1 else 0

theorem ldl_strip_loop (a : Fin T) : ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
    S.R a = l → v.flag = decide (l.head? = some (bitSymbol false)) →
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (.loop (·.flag) (.act (.pop (.rt a) (fun v _ => v) (ldlPeekF a)))) (mk v S)
        (2 * ldlNF l + 1) (mk v' { S with R := Function.update S.R a (ldlDropF l) })
  | [], v, S, hS, hf => by
      refine ⟨v, rfl, ?_⟩
      have e : ({ S with R := Function.update S.R a (ldlDropF []) } : Stacks T A) = S := by
        rw [ldlDropF, ← hS, Function.update_eq_self]
      rw [e]
      exact .loop_false (by simpa using hf)
  | x :: l, v, S, hS, hf => by
      by_cases hx : x = bitSymbol false
      · have hrun : (Action.pop (.rt a) (fun v _ => v) (ldlPeekF a) : Act T Q A U).run (mk v S) =
            mk { v with flag := decide (l.head? = some (bitSymbol false)) }
              { S with R := Function.update S.R a l } := by
          simp [Action.run, ldlPeekF, hS, update_rt]
        obtain ⟨v', hu, he⟩ := ldl_strip_loop a l
          { v with flag := decide (l.head? = some (bitSymbol false)) }
          { S with R := Function.update S.R a l } (by simp) rfl
        refine ⟨v', hu, ?_⟩
        have h := Exec.loop_true (body := body) (f := (·.flag)) (by simpa [hx] using hf)
          (hrun ▸ Exec.act (body := body) _ (mk v S)) he
        refine Exec.cast h (by simp [ldlNF, hx]; ring) ?_
        simp [ldlDropF, hx]
      · refine ⟨v, rfl, ?_⟩
        have e : ({ S with R := Function.update S.R a (ldlDropF (x :: l)) } : Stacks T A) = S := by
          rw [ldlDropF, if_neg hx, ← hS, Function.update_eq_self]
        have e2 : 2 * ldlNF (x :: l) + 1 = 1 := by simp [ldlNF, hx]
        rw [e, e2]
        exact .loop_false (by simpa [hx] using hf)

/-- `ldlStrip`: `a` loses its leading symbols `bitSymbol false`; `2 ldlNF + 2` steps. -/
theorem ldl_strip_runs (a : Fin T) (R : Fin T → List (Fin (A + 4))) :
    LayRuns body (ldlStrip a) R (Function.update R a (ldlDropF (R a))) (2 * ldlNF (R a) + 2) := by
  intro v S hL hS
  have h1 := Exec.act (body := body) (ldlPeekF a) (mk v S)
  have e : (ldlPeekF a : Act T Q A U).run (mk v S) =
      mk { v with flag := decide ((S.R a).head? = some (bitSymbol false)) } S := rfl
  rw [e] at h1
  obtain ⟨v', hu, he⟩ := ldl_strip_loop (body := body) a (S.R a)
    { v with flag := decide ((S.R a).head? = some (bitSymbol false)) } S rfl rfl
  refine ⟨v', 1 + (2 * ldlNF (S.R a) + 1), hu, by rw [hS]; omega, ?_⟩
  rw [← hS]
  exact Exec.seq h1 he

theorem ldlDropF_replicate (k : ℕ) (l : List (Fin (A + 4))) :
    ldlDropF (List.replicate k (bitSymbol false) ++ l) = ldlDropF l := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.cons_append, ldlDropF, if_pos rfl, ih]

theorem ldlNF_replicate (k : ℕ) (l : List (Fin (A + 4))) :
    ldlNF (List.replicate k (bitSymbol false) ++ l) = k + ldlNF l := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, ldlNF, if_pos rfl, ih]; ring

end Strip

/-! ### Words of the table machine -/

section Words

variable {A : ℕ}

theorem ldl_testBit_value : ∀ (bs : List Bool) (t : ℕ), (Counter.value bs).testBit t = bs.getD t false
  | [], t => by simp [Counter.value]
  | b :: bs, 0 => by
      cases b <;> simp [Counter.value, Nat.testBit_zero, Nat.add_mod]
  | b :: bs, t + 1 => by
      rw [Nat.testBit_succ, show Counter.value (b :: bs) / 2 = Counter.value bs by
        cases b <;> (simp [Counter.value]; try omega), ldl_testBit_value bs t]
      simp

theorem ldlRe_tblPairs (hA : 4 ≤ A) (w x y : ℕ) :
    ldlRe (tblPairs A w x y) = (binSyms w x : List (Fin (A + 4))) := by
  simp only [ldlRe, tblPairs, coeffSyms, binSyms, List.map_ofFn]
  congr 1
  funext t
  simp [pairRe_pairSym hA, ZMod.val_natCast, Nat.testBit_mod_two_pow, t.isLt]

theorem ldlIm_tblPairs (hA : 4 ≤ A) (w x y : ℕ) :
    ldlIm (tblPairs A w x y) = (binSyms w y : List (Fin (A + 4))) := by
  simp only [ldlIm, tblPairs, coeffSyms, binSyms, List.map_ofFn]
  congr 1
  funext t
  simp [pairIm_pairSym hA, ZMod.val_natCast, Nat.testBit_mod_two_pow, t.isLt]

@[simp] theorem length_tblPairs (w x y : ℕ) : (tblPairs A w x y).length = w := by
  simp [tblPairs]

/-- The `w`-bit word of a canonical counter `bs` of at most `w` bits is `bs` padded with zeros. -/
theorem ldl_binSyms_value {bs : List Bool} (w : ℕ) (hw : bs.length ≤ w) :
    (binSyms w (Counter.value bs) : List (Fin (A + 4))) =
      bs.map bitSymbol ++ List.replicate (w - bs.length) (bitSymbol false) := by
  apply List.ext_getElem (by simp; omega)
  intro t h1 h2
  simp only [binSyms, List.getElem_ofFn, ldl_testBit_value]
  rw [List.getElem_append]
  split_ifs with ht
  · have ht' : t < bs.length := by simpa using ht
    simp [List.getElem?_eq_getElem ht']
  · simp only [List.getElem_replicate]
    rw [List.getD_eq_default _ _ (by simp at ht ⊢; omega)]

theorem ldl_strip_value {bs : List Bool} (hc : GrowingCounterData.Canonical bs) (w : ℕ)
    (hw : bs.length ≤ w) :
    ldlDropF (binSyms w (Counter.value bs) : List (Fin (A + 4))).reverse =
      (bs.map bitSymbol).reverse ∧
    ldlNF (binSyms w (Counter.value bs) : List (Fin (A + 4))).reverse = w - bs.length := by
  rw [ldl_binSyms_value w hw, List.reverse_append, List.reverse_replicate, ldlDropF_replicate,
    ldlNF_replicate]
  rcases hc with rfl | hlast
  · simp [ldlDropF, ldlNF]
  · obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    have hne : (bitSymbol true : Fin (A + 4)) ≠ bitSymbol false := by
      simp [bitSymbol]
    simp [ldlDropF, ldlNF, hne]

end Words

/-! ### The loaders -/

/-- The registers of the loaders. -/
inductive LdlReg
  | dM | dX | cN | cW | tA | tB | tS
  deriving DecidableEq

section Loaders

variable {T Q A t₀ : ℕ} {U F : Type} {body : F → Pr F T Q A U}

/-- The register maps of the layout and of the loaders: injective, with disjoint images. -/
structure LdlRegs (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) : Prop where
  rg_inj : Function.Injective rg
  lr_inj : Function.Injective lr
  disj : ∀ x y, rg x ≠ lr y

variable {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}

theorem LdlRegs.rl (h : LdlRegs rg lr) (x : LayReg t₀) (y : LdlReg) : (rg x = lr y) ↔ False :=
  ⟨h.disj x y, False.elim⟩

theorem LdlRegs.lr' (h : LdlRegs rg lr) (x : LayReg t₀) (y : LdlReg) : (lr y = rg x) ↔ False :=
  ⟨fun e => h.disj x y e.symm, False.elim⟩

/-- **The loader of a single-bit move**: clear the masks, read one word of `|cN| = n` symbols of
`dM`, and move its real bits onto `mA` and its imaginary bits onto `mB`. -/
def ldlPrepM (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) : Pr F T Q A U :=
  .seq (uclear (rg .mA)) (.seq (uclear (rg .mB))
    (.seq (ldlWord (lr .dM) (lr .cN) (lr .tS) (lr .tA) (lr .tB))
      (.seq (moveR (lr .tA) (rg .mA) id) (moveR (lr .tB) (rg .mB) id))))

theorem ldl_nodup5 (h : LdlRegs rg lr) :
    [lr .dM, lr .cN, lr .tS, lr .tA, lr .tB].Nodup ∧ [lr .dX, lr .cW, lr .tS, lr .tA, lr .tB].Nodup := by
  constructor <;>
  · simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      List.nodup_nil, h.lr_inj.eq_iff]
    decide

/-- `ldlPrepM`: with the word `tblPairs A n (2 ^ a) (2 ^ b)` on top of `dM`, `n` symbols on `cN`
and empty buffers, the masks become `binSyms n (2 ^ a)` and `binSyms n (2 ^ b)` and `dM` loses
the word; `2 |mA| + 2 |mB| + 10 n + 12` steps. -/
theorem ldl_prepM_runs (hA : 4 ≤ A) (h : LdlRegs rg lr) (R : Fin T → List (Fin (A + 4)))
    {n a b : ℕ} (rest : List (Fin (A + 4)))
    (hdM : R (lr .dM) = tblPairs A n (2 ^ a) (2 ^ b) ++ rest) (hcN : (R (lr .cN)).length = n)
    (htA : R (lr .tA) = []) (htB : R (lr .tB) = []) (htS : R (lr .tS) = []) :
    LayRuns body (ldlPrepM rg lr) R
      (Function.update (Function.update (Function.update R (rg .mA) (binSyms n (2 ^ a)))
        (rg .mB) (binSyms n (2 ^ b))) (lr .dM) rest)
      (2 * (R (rg .mA)).length + 2 * (R (rg .mB)).length + 10 * n + 12) := by
  have rl := h.rl
  have lr' := h.lr'
  have ri : ∀ x y, rg x = rg y ↔ x = y := fun x y => h.rg_inj.eq_iff
  have li : ∀ x y, lr x = lr y ↔ x = y := fun x y => h.lr_inj.eq_iff
  set ws := tblPairs A n (2 ^ a) (2 ^ b) with hws
  have hwl : ws.length = n := length_tblPairs _ _ _
  have s1 := ldl_uclear_runs (body := body) (rg .mA) R
  set R1 := Function.update R (rg .mA) [] with hR1
  have s2 := ldl_uclear_runs (body := body) (rg .mB) R1
  set R2 := Function.update R1 (rg .mB) [] with hR2
  have s3 := ldl_word_runs (body := body) (ldl_nodup5 h).1 R2 ws rest
    (by simp [Function.update_apply, rl, lr', li, ri, hR2, hR1, rl, hdM]) (by simp [Function.update_apply, rl, lr', li, ri, hR2, hR1, rl, hcN, hwl]) (by simp [Function.update_apply, rl, lr', li, ri, hR2, hR1, rl, htS])
  set R3 := ldlWordFile (lr .dM) (lr .tA) (lr .tB) R2 ws rest ws.length with hR3
  have s4 := ldl_moveR_runs (body := body) (show lr .tA ≠ rg .mA from fun e => h.disj _ _ e.symm) R3
  set R4 := Function.update (Function.update R3 (lr .tA) []) (rg .mA)
    ((R3 (lr .tA)).reverse ++ R3 (rg .mA)) with hR4
  have s5 := ldl_moveR_runs (body := body) (show lr .tB ≠ rg .mB from fun e => h.disj _ _ e.symm) R4
  have e3A : R3 (lr .tA) = (binSyms n (2 ^ a) : List (Fin (A + 4))).reverse := by
    simp [Function.update_apply, rl, lr', li, ri, hR3, ldlWordFile, li, hR2, hR1, lr', htA, hws, ldlRe_tblPairs hA,
      List.take_of_length_le]
  have e3B : R3 (lr .tB) = (binSyms n (2 ^ b) : List (Fin (A + 4))).reverse := by
    simp [Function.update_apply, rl, lr', li, ri, hR3, ldlWordFile, li, hR2, hR1, lr', htB, hws, ldlIm_tblPairs hA,
      List.take_of_length_le]
  refine ((s1.seq (s2.seq (s3.seq (s4.seq s5)))).mono ?_).congr ?_
  · have l1 : (R1 (rg .mB)).length = (R (rg .mB)).length := by simp [Function.update_apply, rl, lr', li, ri, hR1, ri]
    have l3 : (R3 (lr .tA)).length = n := by simp [e3A]
    have l4 : (R4 (lr .tB)).length = n := by
      simp [Function.update_apply, rl, lr', li, ri, hR4, li, lr', e3B]
    rw [l1, l3, l4, hwl]
    omega
  · have e4B : R4 (lr .tB) = (binSyms n (2 ^ b) : List (Fin (A + 4))).reverse := by
      simp [Function.update_apply, rl, lr', li, hR4, e3B]
    have e4mB : R4 (rg .mB) = [] := by
      simp [Function.update_apply, rl, lr', li, ri, hR4, hR3, ldlWordFile, hR2]
    have e3mA : R3 (rg .mA) = [] := by
      simp [Function.update_apply, rl, lr', li, ri, hR3, ldlWordFile, hR2, hR1]
    funext y
    rw [e4B, e4mB, List.reverse_reverse, List.append_nil]
    by_cases y1 : y = rg .mB
    · subst y1; simp [Function.update_apply, rl, lr', ri]
    by_cases y2 : y = lr .tB
    · subst y2; simp [Function.update_apply, rl, lr', li, htB]
    rw [Function.update_of_ne y1, Function.update_of_ne y2, hR4, e3A, e3mA, List.reverse_reverse,
      List.append_nil]
    by_cases y3 : y = rg .mA
    · subst y3; simp [Function.update_apply, rl, lr', ri]
    by_cases y4 : y = lr .tA
    · subst y4; simp [Function.update_apply, rl, lr', li, htA]
    rw [Function.update_of_ne y3, Function.update_of_ne y4, hR3]
    simp only [ldlWordFile]
    rw [Function.update_of_ne y2, Function.update_of_ne y4]
    by_cases y5 : y = lr .dM
    · subst y5; simp [Function.update_apply, rl, lr', li]
    rw [Function.update_of_ne y5, hR2, hR1, Function.update_of_ne y1, Function.update_of_ne y3]
    simp [Function.update_apply, y1, y3, y5]

/-- The words of one header: the five counters `hs k` as `w`-bit words. -/
def ldlXcRec (A w : ℕ) (hs : Fin 5 → List Bool) : List (Fin (A + 4)) :=
  tblPairs A w (Counter.value (hs 0)) 0 ++ (tblPairs A w (Counter.value (hs 1)) 0 ++
    (tblPairs A w (Counter.value (hs 2)) 0 ++ (tblPairs A w (Counter.value (hs 3)) 0 ++
      tblPairs A w (Counter.value (hs 4)) 0)))

/-- **The loader of one header register** `dst`: clear it, read one word of `|cW| = w` symbols of
`dX`, strip the zero bits above the highest one, and write `separator` followed by the bits,
least significant first. -/
def ldlHdr (dst : Fin T) (lr : LdlReg → Fin T) : Pr F T Q A U :=
  .seq (uclear dst) (.seq (ldlWord (lr .dX) (lr .cW) (lr .tS) (lr .tA) (lr .tB))
    (.seq (uclear (lr .tB)) (.seq (ldlStrip (lr .tA))
      (.seq (moveR (lr .tA) dst id) (.act (.push (.rt dst) (fun _ => separator) .done))))))

/-- `ldlHdr`: with the word of a canonical counter `bs` of at most `w` bits on top of `dX`, `w`
symbols on `cW` and empty buffers, `dst` becomes `separator :: bs.map bitSymbol` and `dX` loses
the word; `2 |dst| + 10 w + 13` steps. -/
theorem ldl_hdr_runs (hA : 4 ≤ A) (hlr : Function.Injective lr) {dst : Fin T}
    (hdst : ∀ y, lr y ≠ dst) (R : Fin T → List (Fin (A + 4))) {w : ℕ} (bs : List Bool)
    (hc : GrowingCounterData.Canonical bs) (hw : bs.length ≤ w) (rest : List (Fin (A + 4)))
    (hdX : R (lr .dX) = tblPairs A w (Counter.value bs) 0 ++ rest) (hcW : (R (lr .cW)).length = w)
    (htA : R (lr .tA) = []) (htB : R (lr .tB) = []) (htS : R (lr .tS) = []) :
    LayRuns body (ldlHdr dst lr) R
      (Function.update (Function.update R dst (separator :: bs.map bitSymbol)) (lr .dX) rest)
      (2 * (R dst).length + 10 * w + 13) := by
  have li : ∀ x y, lr x = lr y ↔ x = y := fun x y => hlr.eq_iff
  have hd' : ∀ y, (lr y = dst) ↔ False := fun y => ⟨hdst y, False.elim⟩
  have hd'' : ∀ y, (dst = lr y) ↔ False := fun y => ⟨fun e => hdst y e.symm, False.elim⟩
  set ws := tblPairs A w (Counter.value bs) 0 with hws
  have hwl : ws.length = w := length_tblPairs _ _ _
  have hnd : [lr .dX, lr .cW, lr .tS, lr .tA, lr .tB].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      List.nodup_nil, li]
    decide
  have s1 := ldl_uclear_runs (body := body) dst R
  set R1 := Function.update R dst [] with hR1
  have s2 := ldl_word_runs (body := body) hnd R1 ws rest (by simp [Function.update_apply, li, hd', hd'', hR1, hd', hdX])
    (by simp [Function.update_apply, li, hd', hd'', hR1, hd', hcW, hwl]) (by simp [Function.update_apply, li, hd', hd'', hR1, hd', htS])
  set R2 := ldlWordFile (lr .dX) (lr .tA) (lr .tB) R1 ws rest ws.length with hR2
  have s3 := ldl_uclear_runs (body := body) (lr .tB) R2
  set R3 := Function.update R2 (lr .tB) [] with hR3
  have s4 := ldl_strip_runs (body := body) (lr .tA) R3
  have e3A : R3 (lr .tA) = (binSyms w (Counter.value bs) : List (Fin (A + 4))).reverse := by
    simp [Function.update_apply, li, hd', hd'', hR3, hR2, hR1, ldlWordFile, li, hd', htA, hws, ldlRe_tblPairs hA,
      List.take_of_length_le]
  obtain ⟨hdrop, hnf⟩ := ldl_strip_value (A := A) hc w hw
  set R4 := Function.update R3 (lr .tA) (ldlDropF (R3 (lr .tA))) with hR4
  have e4A : R4 (lr .tA) = (bs.map bitSymbol).reverse := by simp [Function.update_apply, li, hd', hd'', hR4, e3A, hdrop]
  have s5 := ldl_moveR_runs (body := body) (hdst .tA) R4
  set R5 := Function.update (Function.update R4 (lr .tA) []) dst ((R4 (lr .tA)).reverse ++ R4 dst)
    with hR5
  have s6 := ldl_push_runs (body := body) dst separator R5
  refine ((s1.seq (s2.seq (s3.seq (s4.seq (s5.seq s6))))).mono ?_).congr ?_
  · have l2 : (R2 (lr .tB)).length = w := by
      simp [Function.update_apply, li, hd', hd'', hR2, ldlWordFile, hR1, hd', htB, hws, ldlIm_tblPairs hA,
        List.take_of_length_le]
    have l3 : ldlNF (R3 (lr .tA)) = w - bs.length := by rw [e3A, hnf]
    have l4 : (R4 (lr .tA)).length = bs.length := by simp [e4A]
    rw [l2, l3, l4, hwl]
    omega
  · funext y
    have e4d : R4 dst = [] := by
      simp [Function.update_apply, li, hd', hd'', hR4, hR3, hR2, hR1, ldlWordFile, hd'']
    simp only [hR5, Function.update_apply, e4A, e4d]
    simp only [hR4, hR3, hR2, hR1, ldlWordFile, Function.update_apply]
    split_ifs <;> simp_all

/-- The five header registers of the bank. -/
noncomputable def ldlH (rg : LayReg t₀ → Fin T) (hd : Fin 5 → Fin t₀) (k : Fin 5) : Fin T := rg (.sw (reg (hd k)))

/-- **The loader of an exchange**: the five header registers, each by `ldlHdr`. -/
noncomputable def ldlPrepX (hd : Fin 5 → Fin t₀) (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) :
    Pr F T Q A U :=
  .seq (ldlHdr (ldlH rg hd 0) lr) (.seq (ldlHdr (ldlH rg hd 1) lr) (.seq (ldlHdr (ldlH rg hd 2) lr)
    (.seq (ldlHdr (ldlH rg hd 3) lr) (ldlHdr (ldlH rg hd 4) lr))))

/-- The register file `R` with the header registers set to `h`. -/
noncomputable def ldlSetH (rg : LayReg t₀ → Fin T) (hd : Fin 5 → Fin t₀) (R : Fin T → List (Fin (A + 4)))
    (h : Fin 5 → List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update R
    (ldlH rg hd 0) (h 0)) (ldlH rg hd 1) (h 1)) (ldlH rg hd 2) (h 2)) (ldlH rg hd 3) (h 3))
    (ldlH rg hd 4) (h 4)

theorem ldlH_injective (hrg : Function.Injective rg) {hd : Fin 5 → Fin t₀}
    (hi : Function.Injective hd) : Function.Injective (ldlH rg hd) := by
  intro k k' e
  have e1 := hrg e
  simp only [LayReg.sw.injEq] at e1
  exact hi (BinaryInterchangeRun.slot_injective e1)

theorem ldlSetH_apply (hrg : Function.Injective rg) {hd : Fin 5 → Fin t₀}
    (hi : Function.Injective hd) (R : Fin T → List (Fin (A + 4))) (h : Fin 5 → List (Fin (A + 4)))
    (y : Fin T) : ldlSetH rg hd R h y = if hy : ∃ k, ldlH rg hd k = y then h hy.choose else R y := by
  have hinj := ldlH_injective hrg hi
  split_ifs with hy
  · have hk := hy.choose_spec
    generalize hy.choose = k at hk
    subst hk
    fin_cases k <;>
      simp [ldlSetH, Function.update_apply, hinj.eq_iff]
  · simp only [not_exists] at hy
    simp [ldlSetH, Function.update_apply, Ne.symm (hy _)]

theorem ldlSetH_H (hrg : Function.Injective rg) {hd : Fin 5 → Fin t₀}
    (hi : Function.Injective hd) (R : Fin T → List (Fin (A + 4))) (h : Fin 5 → List (Fin (A + 4)))
    (k : Fin 5) : ldlSetH rg hd R h (ldlH rg hd k) = h k := by
  rw [ldlSetH_apply hrg hi]
  have hy : ∃ k', ldlH rg hd k' = ldlH rg hd k := ⟨k, rfl⟩
  rw [dif_pos hy]
  exact congrArg h (ldlH_injective hrg hi hy.choose_spec)

theorem ldlSetH_of_ne (hrg : Function.Injective rg) {hd : Fin 5 → Fin t₀}
    (hi : Function.Injective hd) (R : Fin T → List (Fin (A + 4))) (h : Fin 5 → List (Fin (A + 4)))
    {y : Fin T} (hy : ∀ k, ldlH rg hd k ≠ y) : ldlSetH rg hd R h y = R y := by
  rw [ldlSetH_apply hrg hi, dif_neg (fun ⟨k, hk⟩ => hy k hk)]

theorem ldl_prepX_runs (hA : 4 ≤ A) (h : LdlRegs rg lr) {hd : Fin 5 → Fin t₀}
    (hi : Function.Injective hd) (R : Fin T → List (Fin (A + 4))) {w : ℕ} (hs : Fin 5 → List Bool)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hw : ∀ k, (hs k).length ≤ w)
    (rest : List (Fin (A + 4))) (hdX : R (lr .dX) = ldlXcRec A w hs ++ rest)
    (hcW : (R (lr .cW)).length = w) (htA : R (lr .tA) = []) (htB : R (lr .tB) = [])
    (htS : R (lr .tS) = []) :
    LayRuns body (ldlPrepX hd rg lr) R
      (Function.update (ldlSetH rg hd R fun k => separator :: (hs k).map bitSymbol) (lr .dX) rest)
      (∑ k : Fin 5, (2 * (R (ldlH rg hd k)).length + 10 * w + 13)) := by
  have hinj := ldlH_injective h.rg_inj hi
  have li : ∀ x y, lr x = lr y ↔ x = y := fun x y => h.lr_inj.eq_iff
  have hH : ∀ k y, lr y ≠ ldlH rg hd k := fun k y e => h.disj _ _ e.symm
  have hH' : ∀ k y, (ldlH rg hd k = lr y) ↔ False := fun k y => ⟨h.disj _ _, False.elim⟩
  have hH'' : ∀ k y, (lr y = ldlH rg hd k) ↔ False := fun k y => ⟨hH k y, False.elim⟩
  have hHH : ∀ k k', ldlH rg hd k = ldlH rg hd k' ↔ k = k' := fun k k' => hinj.eq_iff
  set hdr : Fin 5 → List (Fin (A + 4)) := fun k => separator :: (hs k).map bitSymbol with hhdr
  set w1 := tblPairs A w (Counter.value (hs 1)) 0
  set w2 := tblPairs A w (Counter.value (hs 2)) 0
  set w3 := tblPairs A w (Counter.value (hs 3)) 0
  set w4 := tblPairs A w (Counter.value (hs 4)) 0
  have s0 := ldl_hdr_runs (body := body) hA h.lr_inj (hH 0) R (hs 0) (hc 0) (hw 0)
    (w1 ++ (w2 ++ (w3 ++ (w4 ++ rest)))) (by rw [hdX]; simp [ldlXcRec, w1, w2, w3, w4]) hcW htA
    htB htS
  set R1 := Function.update (Function.update R (ldlH rg hd 0) (hdr 0)) (lr .dX)
    (w1 ++ (w2 ++ (w3 ++ (w4 ++ rest)))) with hR1
  have s1 := ldl_hdr_runs (body := body) hA h.lr_inj (hH 1) R1 (hs 1) (hc 1) (hw 1)
    (w2 ++ (w3 ++ (w4 ++ rest))) (by simp [hR1, w1])
    (by simp [hR1, Function.update_apply, li, hH'', hcW]) (by simp [hR1, Function.update_apply, li, hH'', htA])
    (by simp [hR1, Function.update_apply, li, hH'', htB]) (by simp [hR1, Function.update_apply, li, hH'', htS])
  set R2 := Function.update (Function.update R1 (ldlH rg hd 1) (hdr 1)) (lr .dX)
    (w2 ++ (w3 ++ (w4 ++ rest))) with hR2
  have s2 := ldl_hdr_runs (body := body) hA h.lr_inj (hH 2) R2 (hs 2) (hc 2) (hw 2)
    (w3 ++ (w4 ++ rest)) (by simp [hR2, w2])
    (by simp [hR2, hR1, Function.update_apply, li, hH'', hcW])
    (by simp [hR2, hR1, Function.update_apply, li, hH'', htA])
    (by simp [hR2, hR1, Function.update_apply, li, hH'', htB])
    (by simp [hR2, hR1, Function.update_apply, li, hH'', htS])
  set R3 := Function.update (Function.update R2 (ldlH rg hd 2) (hdr 2)) (lr .dX)
    (w3 ++ (w4 ++ rest)) with hR3
  have s3 := ldl_hdr_runs (body := body) hA h.lr_inj (hH 3) R3 (hs 3) (hc 3) (hw 3)
    (w4 ++ rest) (by simp [hR3, w3])
    (by simp [hR3, hR2, hR1, Function.update_apply, li, hH'', hcW])
    (by simp [hR3, hR2, hR1, Function.update_apply, li, hH'', htA])
    (by simp [hR3, hR2, hR1, Function.update_apply, li, hH'', htB])
    (by simp [hR3, hR2, hR1, Function.update_apply, li, hH'', htS])
  set R4 := Function.update (Function.update R3 (ldlH rg hd 3) (hdr 3)) (lr .dX)
    (w4 ++ rest) with hR4
  have s4 := ldl_hdr_runs (body := body) hA h.lr_inj (hH 4) R4 (hs 4) (hc 4) (hw 4)
    rest (by simp [hR4, w4])
    (by simp [hR4, hR3, hR2, hR1, Function.update_apply, li, hH'', hcW])
    (by simp [hR4, hR3, hR2, hR1, Function.update_apply, li, hH'', htA])
    (by simp [hR4, hR3, hR2, hR1, Function.update_apply, li, hH'', htB])
    (by simp [hR4, hR3, hR2, hR1, Function.update_apply, li, hH'', htS])
  refine ((s0.seq (s1.seq (s2.seq (s3.seq s4)))).mono (le_of_eq ?_)).congr ?_
  · simp only [Fin.sum_univ_five]
    simp [hR4, hR3, hR2, hR1, Function.update_apply, hH', hHH]
    ring
  · funext y
    by_cases hy : y = lr .dX
    · subst hy; simp [Function.update_apply]
    by_cases hk : ∃ k, ldlH rg hd k = y
    · obtain ⟨k, rfl⟩ := hk
      rw [Function.update_of_ne hy, Function.update_of_ne hy, ldlSetH_H h.rg_inj hi]
      fin_cases k <;> simp [hR4, hR3, hR2, hR1, Function.update_apply, hH', hHH, hhdr]
    · simp only [not_exists] at hk
      rw [Function.update_of_ne hy, Function.update_of_ne hy, ldlSetH_of_ne h.rg_inj hi _ _ hk]
      simp [hR4, hR3, hR2, hR1, Function.update_apply, hy, Ne.symm (hk _)]

end Loaders

/-! ### Description streams and register files -/

section Files

variable {T A t₀ : ℕ}

/-- The record of the single-bit move `e = (a, b)`: the word `tblPairs A n (2 ^ a) (2 ^ b)`. -/
def ldlBitRec (A n : ℕ) (e : ℕ × ℕ) : List (Fin (A + 4)) := tblPairs A n (2 ^ e.1) (2 ^ e.2)

/-- The description stream of the single-bit moves `bs`, the first on top. -/
def ldlBitStream (A n : ℕ) (bs : List (ℕ × ℕ)) : List (Fin (A + 4)) := bs.flatMap (ldlBitRec A n)

/-- The description stream of the exchanges `xs`, the first on top. -/
def ldlXcStream (A w : ℕ) (xs : List LayXcD) : List (Fin (A + 4)) :=
  xs.flatMap fun d => ldlXcRec A w d.hs

theorem ldlBitStream_drop {n : ℕ} {bs : List (ℕ × ℕ)} {j : ℕ} (hj : j < bs.length) :
    ldlBitStream A n (bs.drop j) = ldlBitRec A n bs[j] ++ ldlBitStream A n (bs.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons hj, ldlBitStream, List.flatMap_cons]
  rfl

theorem ldlXcStream_drop {w : ℕ} {xs : List LayXcD} {j : ℕ} (hj : j < xs.length) :
    ldlXcStream A w (xs.drop j) = ldlXcRec A w xs[j].hs ++ ldlXcStream A w (xs.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons hj, ldlXcStream, List.flatMap_cons]
  rfl

/-- The register files of the bit phase: before move `j`, the masks of move `j - 1` and the
records of the moves from `j` on. -/
def ldlWM (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) (A n : ℕ)
    (R₀ : Fin T → List (Fin (A + 4))) (bs : List (ℕ × ℕ)) : ℕ → Fin T → List (Fin (A + 4))
  | 0 => R₀
  | j + 1 => Function.update (Function.update (Function.update R₀ (rg .mA)
      (binSyms n (2 ^ (bs.getD j (0, 0)).1))) (rg .mB) (binSyms n (2 ^ (bs.getD j (0, 0)).2)))
      (lr .dM) (ldlBitStream A n (bs.drop (j + 1)))

/-- The register files of the exchange phase, from the file `R₁` after the bit phase: before
exchange `j`, the headers of exchange `j - 1` and the records of the exchanges from `j` on. -/
noncomputable def ldlWX (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) (hd : Fin 5 → Fin t₀)
    (A w : ℕ) (R₁ : Fin T → List (Fin (A + 4))) (xs : List LayXcD) : ℕ → Fin T → List (Fin (A + 4))
  | 0 => R₁
  | j + 1 => Function.update
      (ldlSetH rg hd R₁ fun k => separator :: ((xs.getD j default).hs k).map bitSymbol) (lr .dX)
      (ldlXcStream A w (xs.drop (j + 1)))

/-- The register files of the layout: `ldlWM` up to `|bs|`, then `ldlWX`. -/
noncomputable def ldlW (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) (hd : Fin 5 → Fin t₀)
    (A n w : ℕ) (R₀ : Fin T → List (Fin (A + 4))) (bs : List (ℕ × ℕ)) (xs : List LayXcD) (i : ℕ) :
    Fin T → List (Fin (A + 4)) :=
  if i ≤ bs.length then ldlWM rg lr A n R₀ bs i
  else ldlWX rg lr hd A w (ldlWM rg lr A n R₀ bs bs.length) xs (i - bs.length)

theorem ldlW_X (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) (hd : Fin 5 → Fin t₀)
    (A n w : ℕ) (R₀ : Fin T → List (Fin (A + 4))) (bs : List (ℕ × ℕ)) (xs : List LayXcD) (j : ℕ) :
    ldlW rg lr hd A n w R₀ bs xs (bs.length + j) =
      ldlWX rg lr hd A w (ldlWM rg lr A n R₀ bs bs.length) xs j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [ldlW, ldlWX]
  · rw [ldlW, if_neg (by omega), Nat.add_sub_cancel_left]

theorem ldlW_M (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) (hd : Fin 5 → Fin t₀)
    (A n w : ℕ) (R₀ : Fin T → List (Fin (A + 4))) (bs : List (ℕ × ℕ)) (xs : List LayXcD) {j : ℕ}
    (hj : j ≤ bs.length) : ldlW rg lr hd A n w R₀ bs xs j = ldlWM rg lr A n R₀ bs j := by
  rw [ldlW, if_pos hj]

variable {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}

theorem ldlWM_lr (n : ℕ) (R₀ : Fin T → List (Fin (A + 4))) (bs : List (ℕ × ℕ)) (j : ℕ)
    (h : LdlRegs rg lr) {y : LdlReg} (hy : y ≠ .dM) : ldlWM rg lr A n R₀ bs j (lr y) = R₀ (lr y) := by
  cases j with
  | zero => rfl
  | succ j =>
      simp [ldlWM, Function.update_apply, h.lr', (h.lr_inj.ne hy)]

theorem ldlWM_rg (n : ℕ) (R₀ : Fin T → List (Fin (A + 4))) (bs : List (ℕ × ℕ)) (j : ℕ)
    (h : LdlRegs rg lr) {x : LayReg t₀} (h1 : x ≠ .mA) (h2 : x ≠ .mB) :
    ldlWM rg lr A n R₀ bs j (rg x) = R₀ (rg x) := by
  cases j with
  | zero => rfl
  | succ j =>
      simp [ldlWM, Function.update_apply, h.rl, h.rg_inj.ne h1, h.rg_inj.ne h2]

theorem ldlWM_dM {n : ℕ} {R₀ : Fin T → List (Fin (A + 4))} {bs : List (ℕ × ℕ)}
    (hdM : R₀ (lr .dM) = ldlBitStream A n bs) (j : ℕ) :
    ldlWM rg lr A n R₀ bs j (lr .dM) = ldlBitStream A n (bs.drop j) := by
  cases j with
  | zero => simp only [ldlWM, List.drop_zero]; exact hdM
  | succ j => simp [ldlWM]

theorem ldlWM_step {n : ℕ} {R₀ : Fin T → List (Fin (A + 4))}
    {bs : List (ℕ × ℕ)} {j : ℕ} (hj : j < bs.length) :
    Function.update (Function.update (Function.update (ldlWM rg lr A n R₀ bs j) (rg .mA)
      (binSyms n (2 ^ bs[j].1))) (rg .mB) (binSyms n (2 ^ bs[j].2))) (lr .dM)
      (ldlBitStream A n (bs.drop (j + 1))) = ldlWM rg lr A n R₀ bs (j + 1) := by
  have hg : bs.getD j (0, 0) = bs[j] := by rw [List.getD_eq_getElem _ _ hj]
  cases j with
  | zero => simp only [ldlWM]; rw [hg]
  | succ j =>
      funext y
      simp only [ldlWM, Function.update_apply, hg]
      split_ifs <;> rfl

theorem ldlWX_lr (hd : Fin 5 → Fin t₀) (hi : Function.Injective hd) (w : ℕ)
    (R₁ : Fin T → List (Fin (A + 4))) (xs : List LayXcD) (j : ℕ) (h : LdlRegs rg lr) {y : LdlReg}
    (hy : y ≠ .dX) : ldlWX rg lr hd A w R₁ xs j (lr y) = R₁ (lr y) := by
  cases j with
  | zero => rfl
  | succ j =>
      rw [ldlWX, Function.update_of_ne (h.lr_inj.ne hy),
        ldlSetH_of_ne h.rg_inj hi _ _ (fun k => h.disj _ _)]

theorem ldlWX_rg (hd : Fin 5 → Fin t₀) (hi : Function.Injective hd) (w : ℕ)
    (R₁ : Fin T → List (Fin (A + 4))) (xs : List LayXcD) (j : ℕ) (h : LdlRegs rg lr)
    {x : LayReg t₀} (hx : ∀ k, ldlH rg hd k ≠ rg x) :
    ldlWX rg lr hd A w R₁ xs j (rg x) = R₁ (rg x) := by
  cases j with
  | zero => rfl
  | succ j =>
      rw [ldlWX, Function.update_of_ne (h.disj _ _), ldlSetH_of_ne h.rg_inj hi _ _ hx]

theorem ldlWX_dX (hd : Fin 5 → Fin t₀) {w : ℕ}
    {R₁ : Fin T → List (Fin (A + 4))} {xs : List LayXcD} (hdX : R₁ (lr .dX) = ldlXcStream A w xs)
    (j : ℕ) : ldlWX rg lr hd A w R₁ xs j (lr .dX) = ldlXcStream A w (xs.drop j) := by
  cases j with
  | zero => simp only [ldlWX, List.drop_zero]; exact hdX
  | succ j => simp [ldlWX]

theorem ldlWX_H (hd : Fin 5 → Fin t₀) (hi : Function.Injective hd) (w : ℕ)
    (R₁ : Fin T → List (Fin (A + 4))) (xs : List LayXcD) (j : ℕ) (h : LdlRegs rg lr) (k : Fin 5) :
    ldlWX rg lr hd A w R₁ xs (j + 1) (ldlH rg hd k) =
      separator :: ((xs.getD j default).hs k).map bitSymbol := by
  rw [ldlWX, Function.update_of_ne (show ldlH rg hd k ≠ lr .dX from h.disj _ _),
    ldlSetH_H h.rg_inj hi]

theorem ldlWX_step (h : LdlRegs rg lr) {hd : Fin 5 → Fin t₀} (hi : Function.Injective hd)
    {w : ℕ} {R₁ : Fin T → List (Fin (A + 4))} {xs : List LayXcD} {j : ℕ} (hj : j < xs.length) :
    Function.update (ldlSetH rg hd (ldlWX rg lr hd A w R₁ xs j)
      fun k => separator :: (xs[j].hs k).map bitSymbol) (lr .dX)
      (ldlXcStream A w (xs.drop (j + 1))) = ldlWX rg lr hd A w R₁ xs (j + 1) := by
  have hg : xs.getD j default = xs[j] := by rw [List.getD_eq_getElem _ _ hj]
  cases j with
  | zero => simp only [ldlWX]; rw [hg]
  | succ j =>
      funext y
      simp only [ldlWX, hg]
      by_cases hy : y = lr .dX
      · subst hy; simp
      rw [Function.update_of_ne hy, Function.update_of_ne hy]
      by_cases hk : ∃ k, ldlH rg hd k = y
      · obtain ⟨k, rfl⟩ := hk
        rw [ldlSetH_H h.rg_inj hi, ldlSetH_H h.rg_inj hi]
      · simp only [not_exists] at hk
        rw [ldlSetH_of_ne h.rg_inj hi _ _ hk, ldlSetH_of_ne h.rg_inj hi _ _ hk,
          Function.update_of_ne hy, ldlSetH_of_ne h.rg_inj hi _ _ hk]

end Files

/-! ### The loader contracts -/

section Contracts

variable {T Q A t₀ : ℕ} {U F : Type} {body : F → Pr F T Q A U} {rg : LayReg t₀ → Fin T}
  {lr : LdlReg → Fin T}

theorem ldl_layDyn_lr (h : LdlRegs rg lr) (R : Fin T → List (Fin (A + 4)))
    (s dm tm dx tx : List (Fin (A + 4))) (y : LdlReg) : layDyn rg R s dm tm dx tx (lr y) = R (lr y) := by
  simp [layDyn, Function.update_apply, h.lr']

theorem ldl_layDyn_upd (R : Fin T → List (Fin (A + 4))) (s dm tm dx tx : List (Fin (A + 4)))
    {y : Fin T} (h1 : y ≠ rg .str) (h2 : y ≠ rg .cM) (h3 : y ≠ rg .tM) (h4 : y ≠ rg .cX)
    (h5 : y ≠ rg .tX) (v : List (Fin (A + 4))) :
    layDyn rg (Function.update R y v) s dm tm dx tx =
      Function.update (layDyn rg R s dm tm dx tx) y v := by
  funext z
  simp only [layDyn, Function.update_apply]
  by_cases hz : z = y
  · subst hz; simp [h1, h2, h3, h4, h5]
  · simp only [hz, if_false]

theorem ldl_layDyn_setH (h : LdlRegs rg lr) (hd : Fin 5 → Fin t₀)
    (R : Fin T → List (Fin (A + 4))) (s dm tm dx tx : List (Fin (A + 4)))
    (g : Fin 5 → List (Fin (A + 4))) :
    layDyn rg (ldlSetH rg hd R g) s dm tm dx tx = ldlSetH rg hd (layDyn rg R s dm tm dx tx) g := by
  have ri : ∀ x y, rg x = rg y ↔ x = y := fun x y => h.rg_inj.eq_iff
  simp only [ldlSetH]
  rw [ldl_layDyn_upd, ldl_layDyn_upd, ldl_layDyn_upd, ldl_layDyn_upd, ldl_layDyn_upd] <;>
    simp [ldlH, ri]

/-- **The bit-move loader contract**: `ldlPrepM` takes `ldlWM … j` to `ldlWM … (j + 1)` within
`14 n + 12` steps, whatever the stream and the loop counters. -/
theorem ldl_prepM_loads (hA : 4 ≤ A) (h : LdlRegs rg lr) {n : ℕ} {R₀ : Fin T → List (Fin (A + 4))}
    {bs : List (ℕ × ℕ)} (hdM : R₀ (lr .dM) = ldlBitStream A n bs) (hcN : (R₀ (lr .cN)).length = n)
    (htA : R₀ (lr .tA) = []) (htB : R₀ (lr .tB) = []) (htS : R₀ (lr .tS) = [])
    (hmA : (R₀ (rg .mA)).length ≤ n) (hmB : (R₀ (rg .mB)).length ≤ n) {j : ℕ}
    (hj : j < bs.length) :
    LayLoads body rg (ldlPrepM rg lr) (ldlWM rg lr A n R₀ bs j) (ldlWM rg lr A n R₀ bs (j + 1))
      (14 * n + 12) := by
  intro s dm tm dx tx
  set X := ldlWM rg lr A n R₀ bs j with hX
  have hdM' : layDyn rg X s dm tm dx tx (lr .dM) =
      tblPairs A n (2 ^ bs[j].1) (2 ^ bs[j].2) ++ ldlBitStream A n (bs.drop (j + 1)) := by
    rw [ldl_layDyn_lr h, hX, ldlWM_dM hdM, ldlBitStream_drop hj]
    rfl
  have hr := ldl_prepM_runs (body := body) hA h (layDyn rg X s dm tm dx tx) _ hdM'
    (by rw [ldl_layDyn_lr h, hX, ldlWM_lr n R₀ bs j h (by simp), hcN])
    (by rw [ldl_layDyn_lr h, hX, ldlWM_lr n R₀ bs j h (by simp), htA])
    (by rw [ldl_layDyn_lr h, hX, ldlWM_lr n R₀ bs j h (by simp), htB])
    (by rw [ldl_layDyn_lr h, hX, ldlWM_lr n R₀ bs j h (by simp), htS])
  refine (hr.mono ?_).congr ?_
  · rw [layDyn_other h.rg_inj _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
      layDyn_other h.rg_inj _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
    have l1 : (X (rg .mA)).length ≤ n := by
      rw [hX]; cases j with
      | zero => exact hmA
      | succ j => simp [ldlWM, Function.update_apply, h.rl, h.rg_inj.eq_iff]
    have l2 : (X (rg .mB)).length ≤ n := by
      rw [hX]; cases j with
      | zero => exact hmB
      | succ j => simp [ldlWM, Function.update_apply, h.rl, h.rg_inj.eq_iff]
    omega
  · rw [← ldlWM_step hj, ldl_layDyn_upd, ldl_layDyn_upd, ldl_layDyn_upd] <;>
      simp [h.rg_inj.eq_iff, h.lr']

/-- **The exchange loader contract**: `ldlPrepX` takes `ldlWX … j` to `ldlWX … (j + 1)` within
`60 w + 75` steps, whatever the stream and the loop counters. -/
theorem ldl_prepX_loads (hA : 4 ≤ A) (h : LdlRegs rg lr) {hd : Fin 5 → Fin t₀}
    (hi : Function.Injective hd) {w : ℕ} {R₁ : Fin T → List (Fin (A + 4))} {xs : List LayXcD}
    (hdX : R₁ (lr .dX) = ldlXcStream A w xs) (hcW : (R₁ (lr .cW)).length = w)
    (htA : R₁ (lr .tA) = []) (htB : R₁ (lr .tB) = []) (htS : R₁ (lr .tS) = [])
    (hc : ∀ d ∈ xs, ∀ k, GrowingCounterData.Canonical (d.hs k))
    (hw : ∀ d ∈ xs, ∀ k, (d.hs k).length ≤ w) (hH : ∀ k, (R₁ (ldlH rg hd k)).length ≤ w + 1)
    {j : ℕ} (hj : j < xs.length) :
    LayLoads body rg (ldlPrepX hd rg lr) (ldlWX rg lr hd A w R₁ xs j)
      (ldlWX rg lr hd A w R₁ xs (j + 1)) (60 * w + 75) := by
  intro s dm tm dx tx
  set X := ldlWX rg lr hd A w R₁ xs j with hX
  have hdX' : layDyn rg X s dm tm dx tx (lr .dX) =
      ldlXcRec A w xs[j].hs ++ ldlXcStream A w (xs.drop (j + 1)) := by
    rw [ldl_layDyn_lr h, hX, ldlWX_dX hd hdX, ldlXcStream_drop hj]
  have hmem : xs[j] ∈ xs := List.getElem_mem hj
  have hr := ldl_prepX_runs (body := body) hA h hi (layDyn rg X s dm tm dx tx) xs[j].hs
    (hc _ hmem) (hw _ hmem) _ hdX'
    (by rw [ldl_layDyn_lr h, hX, ldlWX_lr hd hi w R₁ xs j h (by simp), hcW])
    (by rw [ldl_layDyn_lr h, hX, ldlWX_lr hd hi w R₁ xs j h (by simp), htA])
    (by rw [ldl_layDyn_lr h, hX, ldlWX_lr hd hi w R₁ xs j h (by simp), htB])
    (by rw [ldl_layDyn_lr h, hX, ldlWX_lr hd hi w R₁ xs j h (by simp), htS])
  refine (hr.mono ?_).congr ?_
  · have hk : ∀ k, (layDyn rg X s dm tm dx tx (ldlH rg hd k)).length ≤ w + 1 := by
      intro k
      rw [show ldlH rg hd k = rg (.sw (reg (hd k))) from rfl,
        layDyn_other h.rg_inj _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp),
        show rg (.sw (reg (hd k))) = ldlH rg hd k from rfl, hX]
      cases j with
      | zero => exact hH k
      | succ j =>
          rw [ldlWX_H hd hi w R₁ xs j h k]
          have hj' : j < xs.length := by omega
          rw [List.getD_eq_getElem _ _ hj']
          simpa using hw _ (List.getElem_mem hj') k
    simp only [Fin.sum_univ_five]
    have := hk 0; have := hk 1; have := hk 2; have := hk 3; have := hk 4
    omega
  · rw [← ldlWX_step h hi hj, ldl_layDyn_upd, ldl_layDyn_setH h hd]
    all_goals simp [h.lr']

end Contracts

/-! ### The layout stage -/

section Stage

variable {T Q t₀ Ka : ℕ} {U F : Type} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}

/-- The register file before the layout stage: the registers of a single-bit move as in
`LayMvCfg` (masks of at most `n` symbols), the bank of the interchange with empty payload and
private registers, header registers of at most `wX + 1` symbols, the description streams of the
moves `bs` and the exchanges `xs`, the word counters (`n` and `wX` symbols) and empty buffers. -/
structure LdlBase (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) (hd : Fin 5 → Fin t₀)
    (pay : Fin t₀) (R₀ : Fin T → List (Fin (prime + Ka + 4))) (n B wX : ℕ) (bs : List (ℕ × ℕ))
    (xs : List LayXcD) : Prop where
  r0 : R₀ (rg .r0) = []
  r1 : R₀ (rg .r1) = []
  r2 : R₀ (rg .r2) = []
  r3 : R₀ (rg .r3) = []
  q0 : R₀ (rg .q0) = []
  q1 : R₀ (rg .q1) = []
  q2 : R₀ (rg .q2) = []
  q3 : R₀ (rg .q3) = []
  tmp : R₀ (rg .tmp) = []
  ctrB : (R₀ (rg .ctrB)).length = B
  cnt : (R₀ (rg .cnt)).length = 2 ^ n
  fld : R₀ (rg .fld) = binSyms n 0
  us : ∀ r, R₀ (rg (.us r)) = []
  mA : (R₀ (rg .mA)).length ≤ n
  mB : (R₀ (rg .mB)).length ≤ n
  bpay : R₀ (rg (.sw (reg pay))) = []
  bpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → R₀ (rg (.sw j)) = []
  bother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
    ∀ s ∈ R₀ (rg (.sw (reg i))), s ≠ blank ∧ s.val < prime + 4
  hdr : ∀ k, (R₀ (ldlH rg hd k)).length ≤ wX + 1
  dM : R₀ (lr .dM) = ldlBitStream (prime + Ka) n bs
  dX : R₀ (lr .dX) = ldlXcStream (prime + Ka) wX xs
  cN : (R₀ (lr .cN)).length = n
  cW : (R₀ (lr .cW)).length = wX
  tA : R₀ (lr .tA) = []
  tB : R₀ (lr .tB) = []
  tS : R₀ (lr .tS) = []

theorem ldl_reg_val (i : Fin t₀) : (reg i : Fin (swapT t₀)).val = i.val := rfl

/-- **The layout machine on description streams.** From a base register file (`LdlBase`) holding
the description streams of the single-bit moves `bs` and the exchanges `xs`, the layout machine
`layApply` with the loaders `ldlPrepM`, `ldlPrepX` moves the stream of `2^n` records by the moves
`bs` and then `xs`; the register files follow `ldlW`; the cost is that of `layApply_exec_gen`
with loaders of `14 n + 12` and `60 wX + 75` steps. -/
theorem ldl_stage_gen (body : F → Pr F T Q (prime + Ka) U) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q) (h : LdlRegs rg lr)
    (hT : swapT t₀ ≤ T) (hA : 4 ≤ prime + Ka) (hpay : ∀ k, hd k ≠ pay) {n K B wX : ℕ}
    (hB : 1 ≤ B) (bs : List (ℕ × ℕ)) (xs : List LayXcD) (hbs : ∀ e ∈ bs, e.1 < n ∧ e.2 < n)
    (hxs : ∀ d ∈ xs, d.OK n K B) (hwX : ∀ d ∈ xs, ∀ k, (d.hs k).length ≤ wX)
    (R₀ : Fin T → List (Fin (prime + Ka + 4))) (hb : LdlBase rg lr hd pay R₀ n B wX bs xs)
    (l : List (List (Fin (prime + Ka + 4)))) (hl : l.length = 2 ^ n)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8)
    (csM csX : List (Fin (prime + Ka + 4))) (hcsM : csM.length = bs.length)
    (hcsX : csX.length = xs.length) :
    LayRuns body (layApply hd pay hi hQ rg (fun _ _ e => by simpa using h.rg_inj e) hT
        (ldlPrepM rg lr) (ldlPrepX hd rg lr))
      (layDyn rg R₀ l.flatten csM [] csX [])
      (layDyn rg (ldlW rg lr hd (prime + Ka) n wX R₀ bs xs (bs.length + xs.length))
        (layStream K n (layBitMoves bs ++ xs.map LayXcD.move) l).flatten csM [] csX [])
      (layBitCost n B (fun _ => 14 * n + 12) bs.length +
        layXcLoopCost T t₀ n K B rg (fun j => ldlW rg lr hd (prime + Ka) n wX R₀ bs xs (bs.length + j))
          (fun _ => 60 * wX + 75) xs) := by
  set W := ldlW rg lr hd (prime + Ka) n wX R₀ bs xs with hW
  set R₁ := ldlWM rg lr (prime + Ka) n R₀ bs bs.length with hR₁
  have hW0 : W 0 = R₀ := by rw [hW, ldlW_M _ _ _ _ _ _ _ _ _ (Nat.zero_le _)]; rfl
  have hHne : ∀ k (x : LayReg t₀), x = .mA ∨ x = .mB → ldlH rg hd k ≠ rg x := by
    intro k x hx e
    have := h.rg_inj e
    rcases hx with rfl | rfl <;> simp at this
  have hR₁rg : ∀ x : LayReg t₀, x ≠ .mA → x ≠ .mB → R₁ (rg x) = R₀ (rg x) := fun x h1 h2 =>
    ldlWM_rg n R₀ bs _ h h1 h2
  have hR₁lr : ∀ y : LdlReg, y ≠ .dM → R₁ (lr y) = R₀ (lr y) := fun y hy => ldlWM_lr n R₀ bs _ h hy
  have hHk : ∀ k (i : Fin t₀), hd k ≠ i → ldlH rg hd k ≠ rg (.sw (reg i)) := by
    intro k i hki e
    have e1 := h.rg_inj e
    simp only [LayReg.sw.injEq] at e1
    exact hki (BinaryInterchangeRun.slot_injective e1)
  have hWX1 : ∀ j, W (bs.length + (j + 1)) = ldlWX rg lr hd (prime + Ka) wX R₁ xs (j + 1) :=
    fun j => ldlW_X _ _ _ _ _ _ _ _ _ _
  have h := layApply_exec_gen body hd pay hi hQ h.rg_inj hT (ldlPrepM rg lr) (ldlPrepX hd rg lr)
    (n := n) (K := K) hB bs xs hbs hxs W
    (fun j hj => by
      rw [hW, ldlW_M _ _ _ _ _ _ _ _ _ (by omega : j + 1 ≤ bs.length)]
      have hg : bs.getD j (0, 0) = bs[j] := by rw [List.getD_eq_getElem _ _ hj]
      have e : ∀ x : LayReg t₀, x ≠ .mA → x ≠ .mB →
          ldlWM rg lr (prime + Ka) n R₀ bs (j + 1) (rg x) = R₀ (rg x) := fun x h1 h2 =>
        ldlWM_rg n R₀ bs _ h h1 h2
      exact ⟨by rw [e _ (by simp) (by simp)]; exact hb.r0, by rw [e _ (by simp) (by simp)]; exact hb.r1,
        by rw [e _ (by simp) (by simp)]; exact hb.r2, by rw [e _ (by simp) (by simp)]; exact hb.r3,
        by rw [e _ (by simp) (by simp)]; exact hb.q0, by rw [e _ (by simp) (by simp)]; exact hb.q1,
        by rw [e _ (by simp) (by simp)]; exact hb.q2, by rw [e _ (by simp) (by simp)]; exact hb.q3,
        by rw [e _ (by simp) (by simp)]; exact hb.tmp, by rw [e _ (by simp) (by simp)]; exact hb.ctrB,
        by rw [e _ (by simp) (by simp)]; exact hb.cnt, by rw [e _ (by simp) (by simp)]; exact hb.fld,
        by simp only [ldlWM]; rw [hg]; simp [Function.update_apply, h.rl, h.rg_inj.eq_iff],
        by simp only [ldlWM]; rw [hg]; simp [Function.update_apply, h.rl, h.rg_inj.eq_iff],
        fun r => by rw [e _ (by simp) (by simp)]; exact hb.us r⟩)
    (fun j hj => by
      rw [hWX1]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [ldlWX_rg hd hi wX R₁ xs _ h (fun k => hHk k pay (hpay k)), hR₁rg _ (by simp) (by simp)]
        exact hb.bpay
      · intro j' hj'
        have hne : ∀ k, ldlH rg hd k ≠ rg (.sw j') := by
          intro k e
          have e1 := h.rg_inj e
          simp only [LayReg.sw.injEq] at e1
          have := (hd k).isLt
          rw [← e1, ldl_reg_val] at hj'
          omega
        rw [ldlWX_rg hd hi wX R₁ xs _ h hne, hR₁rg _ (by simp) (by simp)]
        exact hb.bpriv j' hj'
      · intro k
        rw [show rg (.sw (reg (hd k))) = ldlH rg hd k from rfl, ldlWX_H hd hi wX R₁ xs j h k,
          List.getD_eq_getElem _ _ hj]
      · intro i hip hik
        rw [ldlWX_rg hd hi wX R₁ xs _ h (fun k => hHk k i (hik k)), hR₁rg _ (by simp) (by simp)]
        exact hb.bother i hip hik
      · rw [ldlWX_rg hd hi wX R₁ xs _ h (fun k e => by have := h.rg_inj e; simp at this),
          hR₁rg _ (by simp) (by simp)]
        exact hb.tmp)
    (fun _ => 14 * n + 12) (fun _ => 60 * wX + 75)
    (fun j hj => by
      rw [hW, ldlW_M _ _ _ _ _ _ _ _ _ (by omega : j ≤ bs.length),
        ldlW_M _ _ _ _ _ _ _ _ _ (by omega : j + 1 ≤ bs.length)]
      exact ldl_prepM_loads hA h hb.dM hb.cN hb.tA hb.tB hb.tS hb.mA hb.mB hj)
    (fun j hj => by
      rw [hW, ldlW_X, ldlW_X]
      refine ldl_prepX_loads hA h hi ?_ ?_ ?_ ?_ ?_ ?_ hwX ?_ hj
      · rw [ldlWM_lr n R₀ bs _ h (by simp)]; exact hb.dX
      · rw [ldlWM_lr n R₀ bs _ h (by simp)]; exact hb.cW
      · rw [ldlWM_lr n R₀ bs _ h (by simp)]; exact hb.tA
      · rw [ldlWM_lr n R₀ bs _ h (by simp)]; exact hb.tB
      · rw [ldlWM_lr n R₀ bs _ h (by simp)]; exact hb.tS
      · intro d hd' k
        exact (hxs d hd').2.2.2 k
      · intro k
        rw [show ldlH rg hd k = rg (.sw (reg (hd k))) from rfl, ldlWM_rg n R₀ bs _ h (by simp)
          (by simp)]
        exact hb.hdr k)
    l hl hlB h8 csM csX hcsM hcsX
  rw [hW0] at h
  exact h

end Stage

/-! ### Header lengths and the layout of the synthetic transforms -/

section Layout

open IntegerMultBounds.MathlibTM2.Layer.PackedXor (rectSize)

theorem ldl_swapDims_le {N₀ N₁ N₂ N₃ : ℕ} (L : ℕ) (h0 : 0 < N₀) (h1 : 0 < N₁) (h2 : 0 < N₂)
    (h3 : 0 < N₃) (a b : Fin 3) :
    (swapDims N₀ N₁ N₂ N₃ L a b).1 ≤ rectSize N₀ N₁ N₂ N₃ L ∧
      (swapDims N₀ N₁ N₂ N₃ L a b).2.1 ≤ rectSize N₀ N₁ N₂ N₃ L ∧
      (swapDims N₀ N₁ N₂ N₃ L a b).2.2 ≤ rectSize N₀ N₁ N₂ N₃ L := by
  have hp : 0 < rectSize N₀ N₁ N₂ N₃ L := by unfold rectSize; positivity
  have d : ∀ x y : ℕ, x * y = rectSize N₀ N₁ N₂ N₃ L → x ≤ rectSize N₀ N₁ N₂ N₃ L :=
    fun x y e => Nat.le_of_dvd hp ⟨y, e.symm⟩
  unfold swapDims
  split_ifs
  · exact ⟨d _ (2 ^ L * N₁ * 2 ^ L * N₂ * 2 ^ L * N₃) (by unfold rectSize; ring),
      d _ (N₀ * 2 ^ L * 2 ^ L * N₂ * 2 ^ L * N₃) (by unfold rectSize; ring),
      d _ (N₀ * 2 ^ L * N₁ * 2 ^ L) (by unfold rectSize; ring)⟩
  · exact ⟨d _ (2 ^ L * N₂ * 2 ^ L * N₃) (by unfold rectSize; ring),
      d _ (N₀ * 2 ^ L * N₁ * 2 ^ L * 2 ^ L * N₃) (by unfold rectSize; ring),
      d _ (N₀ * 2 ^ L * N₁ * 2 ^ L * N₂ * 2 ^ L) (by unfold rectSize; ring)⟩
  · exact ⟨d _ (2 ^ L * N₁ * 2 ^ L * N₂ * 2 ^ L * N₃) (by unfold rectSize; ring),
      d _ (N₀ * 2 ^ L * 2 ^ L * N₃) (by unfold rectSize; ring),
      d _ (N₀ * 2 ^ L * N₁ * 2 ^ L * N₂ * 2 ^ L) (by unfold rectSize; ring)⟩

/-- A canonical counter of a value below `2 ^ m` has at most `m` bits. -/
theorem ldl_canonical_length {bs : List Bool} (hc : GrowingCounterData.Canonical bs) {m : ℕ}
    (hm : Counter.value bs < 2 ^ m) : bs.length ≤ m := by
  have hw := GrowingCounterData.canonical_width bs hc
  rcases Nat.eq_zero_or_pos (Counter.value bs) with h0 | hpos
  · rcases hc with rfl | hlast
    · simp
    · obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
      have key : ∀ init : List Bool, 2 ^ init.length ≤ Counter.value (init ++ [true]) := by
        intro init
        induction init with
        | nil => simp [Counter.value]
        | cons b bs ih =>
            rw [List.cons_append, Counter.value, List.length_cons, pow_succ]
            cases b <;> simp <;> omega
      have := key init
      have := Nat.two_pow_pos init.length
      omega
  · have := (Nat.log2_lt (Nat.pos_iff_ne_zero.1 hpos)).2 hm
    omega

variable {es : List ℕ} {ℓ K : ℕ}

/-- The header counters of the exchanges of the layout have at most `N + B + 2` bits
(`N = es.sum`): the values are `P, G ≤ 2^N`, `B' ≤ 3 B 2^N` and `K < 2^N`. -/
theorem ldl_layXcs_hs_le (H : LayHyp es ℓ K) (B wX : ℕ) (hwX : es.sum + B + 2 ≤ wX) :
    ∀ d ∈ layXcs es ℓ K B, ∀ k, (d.hs k).length ≤ wX := by
  intro d hd k
  obtain ⟨hO, hab, hh⟩ := layXcs_OK B H d hd
  refine ldl_canonical_length (hh.2 k) (lt_of_lt_of_le ?_ (Nat.pow_le_pow_right (by norm_num) hwX))
  rw [hh.1 k]
  have hp : ∀ e : ℕ, 0 < 2 ^ e := fun e => Nat.two_pow_pos e
  obtain ⟨b1, b2, b3⟩ := ldl_swapDims_le (N₀ := layN0 es.sum K d.o) (N₁ := layN1 K d.o)
    (N₂ := layN2 K d.o) (N₃ := layN3 d.o) K (hp _) (hp _) (hp _) (hp _) d.a d.b
  rw [lay_rectSize hO] at b1 b2 b3
  have hK : K < 2 ^ es.sum := lt_of_le_of_lt (by have := hO.h0; omega) Nat.lt_two_pow_self
  have h3B : 3 * B < 2 ^ (B + 2) := by
    have := Nat.lt_two_pow_self (n := B)
    rw [pow_add]; omega
  have e3 : 2 ^ (es.sum + B + 2) = 2 ^ es.sum * 2 ^ (B + 2) := by rw [← pow_add]; ring_nf
  have hlt : 2 ^ es.sum < 2 ^ (es.sum + B + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  fin_cases k
  · show (swapDims (layN0 es.sum K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K d.a d.b).1 <
      2 ^ (es.sum + B + 2)
    omega
  · show (swapDims (layN0 es.sum K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K d.a d.b).2.1 <
      2 ^ (es.sum + B + 2)
    omega
  · show (swapDims (layN0 es.sum K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K d.a d.b).2.2 *
      (3 * B) < 2 ^ (es.sum + B + 2)
    rw [e3]
    have hpos : 0 < 2 ^ es.sum := hp _
    calc _ ≤ 2 ^ es.sum * (3 * B) := Nat.mul_le_mul_right _ b3
      _ < 2 ^ es.sum * 2 ^ (B + 2) := Nat.mul_lt_mul_of_pos_left h3B hpos
  · show K < 2 ^ (es.sum + B + 2)
    omega
  · show K < 2 ^ (es.sum + B + 2)
    omega

variable {T Q t₀ Ka : ℕ} {U F : Type} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T} {B : ℕ}

/-- **The layout stage.** From a base register file (`LdlBase`) holding the description streams
of the prefix moves `layBits es ℓ K` (records of `n = es.sum` symbols) and of the chunk
exchanges `layXcs es ℓ K B` (records of five words of `wX ≥ n + B + 2` symbols), and the loop
counters `cM`, `cX` holding one symbol per move, the layout machine with the loaders `ldlPrepM`,
`ldlPrepX` leaves `(moveRecs (layRec (layPerm es ℓ K)) l).flatten` on the stream register: the
record at address `x` moves to the address whose bit `layPerm es ℓ K j` is bit `j` of `x`. The
other registers follow the files `ldlW` (the streams consumed, the masks and headers of the last
moves); within the cost of `layApply_exec` with loaders of `14 n + 12` and `60 wX + 75` steps. -/
theorem ldLayStage_exec (H : LayHyp es ℓ K) (body : F → Pr F T Q (prime + Ka) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q) (h : LdlRegs rg lr) (hT : swapT t₀ ≤ T) (hA : 4 ≤ prime + Ka)
    (hpay : ∀ k, hd k ≠ pay) (hB : 1 ≤ B) {wX : ℕ} (hwX : es.sum + B + 2 ≤ wX)
    (R₀ : Fin T → List (Fin (prime + Ka + 4)))
    (hb : LdlBase rg lr hd pay R₀ es.sum B wX (layBits es ℓ K) (layXcs es ℓ K B))
    (l : List (List (Fin (prime + Ka + 4)))) (hl : l.length = 2 ^ es.sum)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8)
    (csM csX : List (Fin (prime + Ka + 4))) (hcsM : csM.length = (layBits es ℓ K).length)
    (hcsX : csX.length = (layXcs es ℓ K B).length) :
    LayRuns body (layApply hd pay hi hQ rg (fun _ _ e => by simpa using h.rg_inj e) hT
        (ldlPrepM rg lr) (ldlPrepX hd rg lr))
      (layDyn rg R₀ l.flatten csM [] csX [])
      (layDyn rg (ldlW rg lr hd (prime + Ka) es.sum wX R₀ (layBits es ℓ K) (layXcs es ℓ K B)
          ((layBits es ℓ K).length + (layXcs es ℓ K B).length))
        (moveRecs (layRec (layPerm es ℓ K)) l).flatten csM [] csX [])
      (layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es ℓ K).length +
        layXcLoopCost T t₀ es.sum K B rg
          (fun j => ldlW rg lr hd (prime + Ka) es.sum wX R₀ (layBits es ℓ K) (layXcs es ℓ K B)
            ((layBits es ℓ K).length + j)) (fun _ => 60 * wX + 75) (layXcs es ℓ K B)) := by
  have hs := ldl_stage_gen body hd pay hi hQ h hT hA hpay hB (layBits es ℓ K) (layXcs es ℓ K B)
    (layBits_valid H) (layXcs_OK B H) (ldl_layXcs_hs_le H B wX hwX) R₀ hb l hl hlB h8 csM csX
    hcsM hcsX
  rw [layStream, layMovesPerm_layApply B H] at hs
  exact hs

/-- **The cost of the layout stage**: with exchanges of at most `X` steps each, at most
`D (b + 1) (14 N + layMvCost N B + 17) + (D q - 1) (60 wX + X + 80) + 8` steps
(`D = |es|`, `N = es.sum`, `b = layB ℓ K`, `q = layQ ℓ K`). -/
theorem ldLayStage_cost_le (R₀ : Fin T → List (Fin (prime + Ka + 4))) (hd : Fin 5 → Fin t₀)
    (wX X : ℕ)
    (hXs : ∀ j < (layXcs es ℓ K B).length,
      layXcStep T t₀ es.sum K B rg
        (ldlW rg lr hd (prime + Ka) es.sum wX R₀ (layBits es ℓ K) (layXcs es ℓ K B)
          ((layBits es ℓ K).length + (j + 1))) ((layXcs es ℓ K B).getD j default) ≤ X) :
    layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es ℓ K).length +
        layXcLoopCost T t₀ es.sum K B rg
          (fun j => ldlW rg lr hd (prime + Ka) es.sum wX R₀ (layBits es ℓ K) (layXcs es ℓ K B)
            ((layBits es ℓ K).length + j)) (fun _ => 60 * wX + 75) (layXcs es ℓ K B) ≤
      es.length * (layB ℓ K + 1) * (14 * es.sum + 12 + layMvCost es.sum B + 5) +
        (es.length * layQ ℓ K - 1) * (60 * wX + 75 + X + 5) + 8 :=
  layApply_cost_le T t₀ rg _ _ _ (14 * es.sum + 12) (60 * wX + 75) X (fun _ => le_rfl)
    (fun _ => le_rfl) hXs

end Layout

end IntegerMultBounds.MathlibTM2.Fast
