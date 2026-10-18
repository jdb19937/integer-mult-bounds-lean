module

public import IntegerMultBounds.MathlibTM2.Host.Index

/-!
# Fields on host registers

The DFT machine keeps lists of numbers on one host register, each number followed by a
`separator` (the comma of the `Γ'` input and output, `DFT/IO.lean`).

* `takeField i j t` moves the first field of register `i`, up to its separator, onto the empty
  register `j` (through the empty register `t`) and drops the separator: for
  `S.R i = l ++ separator :: rest` with no separator in `l`, register `i` ends as `rest` and `j`
  as `l` (`takeField_exec`, `4 |l| + 5` steps). Binary numbers contain no separator
  (`separator_not_mem_binSyms`).
* `stripZeros i` pops the `bitSymbol false` symbols on top of register `i`
  (`stripZeros_exec`).
* `emitNat s o` moves `binSyms w x` from register `s` onto register `o` with its high zeros
  removed and a separator on top: `o` gains `separator :: (binSyms (Nat.size x) x).reverse`
  (`emitNat_exec`). Emitting `x₀, …, x_(n-1)` in order leaves the shortest-form list
  `natSyms` reversed on `o`, which `writeOut` prints (`DFT/IO.lean`). It uses
  `binSyms_size_pad`: `binSyms w x = binSyms (Nat.size x) x ++ replicate (w - Nat.size x) 0` for
  `x < 2 ^ w`.

Every `_exec` theorem keeps `user` and gives the final register file exactly.
-/

@[expose] public section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host

namespace IntegerMultBounds.MathlibTM2.DFT

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-! ### Symbols and binary numbers -/

theorem bitSymbol_ne_separator (b : Bool) : bitSymbol (a := A) b ≠ separator := by
  cases b <;> simp [bitSymbol, separator]

theorem separator_not_mem_binSyms (L x : ℕ) : (separator : Fin (A + 4)) ∉ binSyms L x := by
  rw [binSyms_eq]
  intro h
  obtain ⟨b, _, hb⟩ := List.mem_map.1 h
  exact bitSymbol_ne_separator b hb

theorem binBits_size_pad {w x : ℕ} (hx : x < 2 ^ w) :
    binBits w x = binBits (Nat.size x) x ++ List.replicate (w - Nat.size x) false := by
  have hs : Nat.size x ≤ w := Nat.size_le.2 hx
  refine List.ext_getElem
    (by simp only [binBits, List.length_append, List.length_ofFn, List.length_replicate]; omega)
    fun i h₁ h₂ => ?_
  by_cases hi : i < Nat.size x
  · rw [List.getElem_append_left (by simpa [binBits] using hi)]
    simp [binBits]
  · rw [List.getElem_append_right (by simpa [binBits] using hi), List.getElem_replicate]
    simp only [binBits, List.getElem_ofFn]
    exact Nat.testBit_lt_two_pow
      ((Nat.size_le.1 le_rfl).trans_le (Nat.pow_le_pow_right (by omega) (by omega)))

/-- High zeros of a binary number. -/
theorem binSyms_size_pad {w x : ℕ} (hx : x < 2 ^ w) :
    (binSyms w x : List (Fin (A + 4))) =
      binSyms (Nat.size x) x ++ List.replicate (w - Nat.size x) (bitSymbol false) := by
  rw [binSyms_eq, binSyms_eq, binBits_size_pad hx, List.map_append, List.map_replicate]

/-! ### Taking a field -/

/-- `true` for a symbol other than `separator`; `false` for `separator` and for nothing. -/
def notSep : Option (Fin (A + 4)) → Bool
  | some x => !decide (x = separator)
  | none => false

/-- Record in `flag` whether register `i` starts with a symbol other than `separator`. -/
def peekField (i : Fin T) : Act T Q A U :=
  .peek (.rt i) (fun v o => { v with flag := notSep o }) .done

/-- Pop register `i` onto register `j` and test register `i` again. -/
def fieldStep (i j : Fin T) : Act T Q A U :=
  .pop (.rt i) (fun v o => { v with sym := o })
    (.push (.rt j) (fun v => v.sym.getD blank) (peekField i))

/-- Pop register `i`, discarding the symbol. -/
def dropR (i : Fin T) : Act T Q A U := .pop (.rt i) (fun v _ => v) .done

/-- Move the first field of register `i` onto register `j` through `t` and drop its
separator. -/
def takeField (i j t : Fin T) : Pr P T Q A U :=
  .seq (.act (peekField i)) (.seq (.loop (·.flag) (.act (fieldStep i t)))
    (.seq (.act (dropR i)) (moveR t j id)))

lemma peekField_run (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (peekField i : Act T Q A U).run (mk v S) = mk { v with flag := notSep (S.R i).head? } S :=
  rfl

lemma dropR_run (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (dropR i : Act T Q A U).run (mk v S) =
      mk v { S with R := Function.update S.R i (S.R i).tail } := by
  simp [dropR, Action.run, update_rt]

/-- Registers after the field loop: register `i` holds `separator :: rest` and `j` gains `l`,
reversed. -/
def fieldR (R : Fin T → List (Fin (A + 4))) (i j : Fin T) (l rest : List (Fin (A + 4))) :
    Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update R i (separator :: rest)) j (l.reverse ++ R j)

theorem fieldLoop (i j : Fin T) (hij : i ≠ j) :
    ∀ (l rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A), separator ∉ l →
      S.R i = l ++ separator :: rest → v.flag = notSep (S.R i).head? →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (fieldStep i j))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := fieldR S.R i j l rest })
  | [], rest, v, S, _, hS, hf => by
      refine ⟨v, rfl, ?_⟩
      have hR : fieldR S.R i j [] rest = S.R := by
        funext k
        simp only [fieldR]
        by_cases hkj : k = j
        · subst hkj
          simp
        · by_cases hki : k = i
          · subst hki
            simp [hkj, hS]
          · simp [hkj, hki]
      rw [hR]
      exact .loop_false (by show v.flag = false; rw [hf, hS]; simp [notSep])
  | x :: l, rest, v, S, hsep, hS, hf => by
      have hx : x ≠ separator := fun h => hsep (by simp [h])
      have hsep' : separator ∉ l := fun h => hsep (by simp [h])
      obtain ⟨v', hu, he⟩ := fieldLoop i j hij l rest
        { v with sym := some x, flag := notSep (l ++ separator :: rest).head? }
        { S with
          R := Function.update (Function.update S.R i (l ++ separator :: rest)) j (x :: S.R j) }
        hsep' (by simp [Function.update_of_ne hij]) (by simp [Function.update_of_ne hij])
      refine ⟨v', hu, ?_⟩
      have hrun : (fieldStep i j : Act T Q A U).run (mk v S) =
          mk { v with sym := some x, flag := notSep (l ++ separator :: rest).head? }
            { S with
              R := Function.update (Function.update S.R i (l ++ separator :: rest)) j
                (x :: S.R j) } := by
        simp [fieldStep, peekField, Action.run, hS, update_rt, Function.update_of_ne hij,
          Function.update_of_ne hij.symm]
      have hact : Exec body (.act (fieldStep i j)) (mk v S) 1
          (mk { v with sym := some x, flag := notSep (l ++ separator :: rest).head? }
            { S with
              R := Function.update (Function.update S.R i (l ++ separator :: rest)) j
                (x :: S.R j) }) := by
        rw [← hrun]
        exact .act _ _
      refine Exec.cast (Exec.loop_true (f := (·.flag))
        (by show v.flag = true; rw [hf, hS]; simp [notSep, hx]) hact he)
        (by simp only [List.length_cons]; ring) ?_
      congr 2
      funext k
      simp only [fieldR]
      by_cases hkj : k = j
      · subst hkj
        simp
      · by_cases hki : k = i
        · subst hki
          simp [hkj]
        · simp [hkj, hki]

/-- `takeField i j t`: register `i` loses its first field `l` and the separator after it, and the
empty register `j` gains `l`. -/
theorem takeField_exec {i j t : Fin T} (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    {l rest : List (Fin (A + 4))} (hsep : separator ∉ l) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R i = l ++ separator :: rest) (ht : S.R t = []) (hj : S.R j = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (takeField i j t) (mk v S) (4 * l.length + 5)
        (mk v' { S with R := Function.update (Function.update S.R i rest) j l }) := by
  have hpeek : Exec body (.act (peekField i)) (mk v S) 1
      (mk { v with flag := notSep (S.R i).head? } S) := by
    rw [← peekField_run]
    exact .act _ _
  obtain ⟨v₂, hu₂, hloop⟩ :=
    fieldLoop body i t hit l rest { v with flag := notSep (S.R i).head? } S hsep hS rfl
  set S₂ : Stacks T A := { S with R := fieldR S.R i t l rest } with hS₂
  have hS₂i : S₂.R i = separator :: rest := by simp [hS₂, fieldR, Function.update_of_ne hit]
  have hdrop := Exec.act (body := body) (dropR i) (mk v₂ S₂)
  rw [dropR_run, hS₂i, List.tail_cons] at hdrop
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R i rest } with hS₃
  have hS₃t : S₃.R t = l.reverse := by
    simp [hS₃, hS₂, fieldR, Function.update_of_ne hit.symm, ht]
  obtain ⟨v₄, hu₄, hmove⟩ := moveR_exec body t j hjt.symm id v₂ S₃
  rw [hS₃t] at hmove
  refine ⟨v₄, hu₄.trans hu₂, Exec.cast (Exec.seq hpeek (Exec.seq hloop (Exec.seq hdrop hmove)))
    (by rw [List.length_reverse]; ring) ?_⟩
  rw [hS₃, hS₂]
  congr 2
  funext k
  simp only [fieldR]
  by_cases hkj : k = j
  · subst hkj
    simp [movedR, hij, hij.symm, hit, hit.symm, hjt, hjt.symm, ht, hj]
  · by_cases hkt : k = t
    · subst hkt
      simp [movedR, hkj, hij, hij.symm, hit, hit.symm, hjt, hjt.symm, ht, hj]
    · by_cases hki : k = i
      · subst hki
        simp [movedR, hkj, hkt, hij, hij.symm, hit, hit.symm, hjt, hjt.symm]
      · simp [movedR, hkj, hkt, hki]

/-! ### Emitting a number in shortest form -/

/-- `true` exactly when a register top is `bitSymbol false`. -/
def zeroTop : Option (Fin (A + 4)) → Bool
  | some x => decide (x = bitSymbol false)
  | none => false

/-- Record in `flag` whether register `i` starts with `bitSymbol false`. -/
def peekZero (i : Fin T) : Act T Q A U :=
  .peek (.rt i) (fun v o => { v with flag := zeroTop o }) .done

/-- Pop register `i` and test it again. -/
def zeroStep (i : Fin T) : Act T Q A U := .pop (.rt i) (fun v _ => v) (peekZero i)

/-- Pop the `bitSymbol false` symbols on top of register `i`. -/
def stripZeros (i : Fin T) : Pr P T Q A U :=
  .seq (.act (peekZero i)) (.loop (·.flag) (.act (zeroStep i)))

/-- Push a separator onto register `i`. -/
def pushSep (i : Fin T) : Act T Q A U := .push (.rt i) (fun _ => separator) .done

/-- Move `binSyms w x` from register `s` onto register `o` without its high zeros, then push a
separator. -/
def emitNat (s o : Fin T) : Pr P T Q A U :=
  .seq (moveR s o id) (.seq (stripZeros o) (.act (pushSep o)))

lemma peekZero_run (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (peekZero i : Act T Q A U).run (mk v S) = mk { v with flag := zeroTop (S.R i).head? } S :=
  rfl

lemma pushSep_run (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (pushSep i : Act T Q A U).run (mk v S) =
      mk v { S with R := Function.update S.R i (separator :: S.R i) } := by
  simp [pushSep, Action.run, update_rt]

theorem stripZeros_loop (i : Fin T) (l : List (Fin (A + 4))) (hl : zeroTop l.head? = false) :
    ∀ (k : ℕ) (v : HS T Q A U) (S : Stacks T A),
      S.R i = List.replicate k (bitSymbol false) ++ l → v.flag = zeroTop (S.R i).head? →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (zeroStep i))) (mk v S) (2 * k + 1)
          (mk v' { S with R := Function.update S.R i l })
  | 0, v, S, hS, hf => by
      refine ⟨v, rfl, ?_⟩
      have hR : ({ S with R := Function.update S.R i l } : Stacks T A) = S := by
        rw [show l = S.R i by simpa using hS.symm, Function.update_eq_self]
      rw [hR]
      exact .loop_false (by show v.flag = false; rw [hf, hS]; simpa using hl)
  | k + 1, v, S, hS, hf => by
      obtain ⟨v', hu, he⟩ := stripZeros_loop i l hl k
        { v with flag := zeroTop (List.replicate k (bitSymbol false) ++ l).head? }
        { S with R := Function.update S.R i (List.replicate k (bitSymbol false) ++ l) }
        (by simp) (by simp)
      refine ⟨v', hu, ?_⟩
      have hrun : (zeroStep i : Act T Q A U).run (mk v S) =
          mk { v with flag := zeroTop (List.replicate k (bitSymbol false) ++ l).head? }
            { S with R := Function.update S.R i (List.replicate k (bitSymbol false) ++ l) } := by
        simp [zeroStep, peekZero, Action.run, hS, update_rt, List.replicate_succ]
      have hact : Exec body (.act (zeroStep i)) (mk v S) 1
          (mk { v with flag := zeroTop (List.replicate k (bitSymbol false) ++ l).head? }
            { S with R := Function.update S.R i (List.replicate k (bitSymbol false) ++ l) }) := by
        rw [← hrun]
        exact .act _ _
      refine Exec.cast (Exec.loop_true (f := (·.flag))
        (by show v.flag = true; rw [hf, hS]; simp [zeroTop, List.replicate_succ]) hact he)
        (by ring) ?_
      simp [Function.update_idem]

/-- `stripZeros i`: register `i` loses the `k` zeros on top of `l`. -/
theorem stripZeros_exec (i : Fin T) (k : ℕ) (l : List (Fin (A + 4)))
    (hl : zeroTop l.head? = false) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R i = List.replicate k (bitSymbol false) ++ l) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (stripZeros i) (mk v S) (2 * k + 2)
        (mk v' { S with R := Function.update S.R i l }) := by
  obtain ⟨v', hu, he⟩ :=
    stripZeros_loop body i l hl k { v with flag := zeroTop (S.R i).head? } S hS rfl
  have hpeek : Exec body (.act (peekZero i)) (mk v S) 1
      (mk { v with flag := zeroTop (S.R i).head? } S) := by
    rw [← peekZero_run]
    exact .act _ _
  exact ⟨v', hu, Exec.cast (Exec.seq hpeek he) (by ring) rfl⟩

/-- The most significant bit of a positive number is set, so the shortest form reversed starts
with `bitSymbol true`. -/
theorem zeroTop_binSyms_reverse (x : ℕ) (old : List (Fin (A + 4)))
    (hold : zeroTop old.head? = false) :
    zeroTop ((binSyms (Nat.size x) x).reverse ++ old).head? = false := by
  rcases hs : Nat.size x with _ | s
  · simpa [binSyms] using hold
  · have hbit : x.testBit s = true :=
      Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (Nat.lt_size.1 (by omega))
        (Nat.size_le.1 (by omega))
    rw [binSyms, List.ofFn_succ_last, List.reverse_append]
    simp [zeroTop, hbit, bitSymbol]

/-- Registers after `emitNat s o` on `binSyms w x`. -/
def emitR (R : Fin T → List (Fin (A + 4))) (s o : Fin T) (x : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update R s []) o
    (separator :: ((binSyms (Nat.size x) x).reverse ++ R o))

/-- `emitNat s o`: register `s` empties and `o` gains `x` in shortest form, most significant bit
first, under a separator. -/
theorem emitNat_exec {s o : Fin T} (hso : s ≠ o) {w x : ℕ} (hx : x < 2 ^ w) (v : HS T Q A U)
    (S : Stacks T A) (hS : S.R s = binSyms w x) (ho : zeroTop (S.R o).head? = false) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (emitNat s o) (mk v S) (2 * w + 2 * (w - Nat.size x) + 5)
        (mk v' { S with R := emitR S.R s o x }) := by
  obtain ⟨v₁, hu₁, hmove⟩ := moveR_exec body s o hso id v S
  rw [hS] at hmove
  have hS₁ : ({ S with R := movedR S.R s o id (binSyms w x) } : Stacks T A).R o =
      List.replicate (w - Nat.size x) (bitSymbol false) ++
        ((binSyms (Nat.size x) x).reverse ++ S.R o) := by
    simp [movedR, binSyms_size_pad hx]
  obtain ⟨v₂, hu₂, hstrip⟩ := stripZeros_exec body o (w - Nat.size x) _
    (zeroTop_binSyms_reverse x _ ho) v₁ _ hS₁
  have hpush := Exec.act (body := body) (pushSep o) (mk v₂
    { ({ S with R := movedR S.R s o id (binSyms w x) } : Stacks T A) with
      R := Function.update (movedR S.R s o id (binSyms w x)) o
        ((binSyms (Nat.size x) x).reverse ++ S.R o) })
  rw [pushSep_run] at hpush
  refine ⟨v₂, hu₂.trans hu₁, Exec.cast (Exec.seq hmove (Exec.seq hstrip hpush))
    (by simp only [binSyms, List.length_ofFn]; ring) ?_⟩
  congr 2
  simp [emitR, movedR, Function.update_idem]

end IntegerMultBounds.MathlibTM2.DFT
