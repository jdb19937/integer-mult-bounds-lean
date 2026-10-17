module

public import IntegerMultBounds.MathlibTM2.Host.Stream
public import IntegerMultBounds.MathlibTM2.Host.Lift
public import IntegerMultBounds.Machine.BinaryInterchangeRun

/-!
# Rectangular interchange on host registers

`swapProg` runs the vendored binary rectangular interchange machine
(`BinaryInterchangeRun.program`, contract `BinaryInterchangeRun.runs`) on host registers. The host
has `swapT t₀ = bankCount t₀ + 1` tapes over `Fin (prime + K + 4)`: register `i < t₀` is caller
tape `i`, the others are the machine's private tapes. The machine runs through the
initial-segment alphabet encoding `Alphabet.widen prime K`, which fixes blank, bits and separator.

The program
1. moves the first symbol (`separator`) of each of the five header registers to its left stack,
   so the represented header tapes have their heads at cell `1`;
2. runs the machine with `foreign`;
3. normalizes every tape: moves the left stack onto the right one, then drops every blank.

The contract fixes only the represented tapes, so after the run a stack may carry blank padding at
either end; step 3 removes it. This recovers a register exactly when its content is blank-free,
which `swapProg_exec` assumes for the caller registers it does not interpret. Step 3 costs time
linear in all stack lengths, so the time bound has a term for the total length of all registers.

`swapList` states the interchange on lists with explicit index arithmetic (`swapList_getElem?`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2


section Tape

variable {a : ℕ}

lemma wordTape_nil : wordTape (a := a) [] = fun _ => blank := by
  funext z; simp [wordTape]

lemma readAt_nil_left (r : List (Fin (a + 4))) (z : ℤ) : readAt blank [] r z = wordTape r z := by
  rcases int_cases z with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [readAt_nonneg]; simp [wordTape]
  · rw [readAt_neg]; simp [wordTape]; omega

lemma readAt_single (x : Fin (a + 4)) (r : List (Fin (a + 4))) (z : ℤ) :
    readAt blank [x] r (z - 1) = wordTape (x :: r) z := by
  rcases int_cases (z - 1) with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, readAt_nonneg, show z = ((k + 1 : ℕ) : ℤ) by omega]
    simp [wordTape]
    intro h; omega
  · rw [hk, readAt_neg]
    rcases k with _ | k
    · have : z = 0 := by omega
      subst this; simp [wordTape]
    · simp [wordTape]; omega

lemma putWord_blank_zero (xs : List (Fin (a + 4))) :
    putWord (fun _ => blank) 0 xs = wordTape xs := by
  funext j
  simpa using putWord_blank 0 j xs

lemma encode_putBits (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (putBits f p bs z)) =
      putWord (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (f z)) p
        (bs.map bitSymbol) := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih =>
      funext z
      simp only [putBits, putWord, List.map_cons]
      rw [← ih]
      by_cases hz : z = p
      · subst hz; simp only [Function.update_self]; cases b <;> rfl
      · simp only [Function.update_of_ne hz]

/-- The encoded binary header is the word `separator :: bits` from cell `0`. -/
theorem encodedBinary_eq (bs : List Bool) :
    RadixZeroFill.encodedBinary (q := a) bs = wordTape (separator :: bs.map bitSymbol) := by
  unfold RadixZeroFill.encodedBinary CountedCopyReuse.binary
  rw [encode_putBits]
  have he : (fun z => (RadixToBinary.binaryEncoding (q := a)).encode (CountedCopyReuse.empty z)) =
      Function.update (fun _ => blank) 0 separator := by
    funext z
    by_cases hz : z = 0
    · subst hz; rfl
    · simp only [CountedCopyReuse.empty, ite_eq_right hz, Function.update_of_ne hz]; rfl
  rw [he, ← putWord_blank_zero, putWord_cons]
  norm_num

/-- Dropping the blanks from the cells stored on two stacks recovers a blank-free word. -/
theorem filter_window (L R : List (Fin (a + 4))) (h : ℤ) (w : List (Fin (a + 4)))
    (hw : blank ∉ w) (hT : ∀ z, wordTape w z = readAt blank L R (z - h)) :
    (L.reverse ++ R).filter (· ≠ blank) = w := by
  rw [window_eq blank L R h _ hT]
  by_cases hne : w = []
  · subst hne
    rw [List.filter_eq_nil_iff]
    intro x hx
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    simp [wordTape_nil]
  set lo : ℤ := h - L.length
  set len := L.length + R.length
  have hbit : ∀ j : ℕ, j < w.length → wordTape w j ≠ (blank : Fin (a + 4)) := by
    intro j hj
    simp only [wordTape, Nat.cast_nonneg, ite_true, Int.toNat_natCast, List.getElem?_eq_getElem hj,
      Option.getD_some]
    intro hb
    exact hw (hb ▸ List.getElem_mem hj)
  have hlen : 0 < w.length := List.length_pos_iff.2 hne
  have hlo : lo ≤ 0 := by
    by_contra hc
    apply hbit 0 hlen
    rw [hT, show ((0 : ℕ) : ℤ) - h = -((h - 1 - L.length).toNat + L.length + 1 : ℕ) by omega,
      readAt_neg, List.getElem?_eq_none (by omega)]
    rfl
  have hlo' : lo = h - L.length := rfl
  have hlen' : len = L.length + R.length := rfl
  have hhi : (w.length : ℤ) ≤ lo + len := by
    by_contra hc
    apply hbit (w.length - 1) (by omega)
    rw [hT, show (((w.length - 1 : ℕ)) : ℤ) - h = ((((w.length - 1 : ℕ) : ℤ) - h).toNat : ℕ) by
        omega, readAt_nonneg, List.getElem?_eq_none (by omega)]
    rfl
  have hsplit : (List.range len).map (fun i : ℕ => wordTape w (lo + (i : ℤ))) =
      List.replicate (-lo).toNat blank ++ w ++
        List.replicate (len - (-lo).toNat - w.length) blank := by
    apply List.ext_getElem (by simp; omega)
    intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    by_cases hi : i < (-lo).toNat
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_replicate]
      simp only [wordTape]
      rw [ite_eq_right (by omega)]
    · by_cases hi' : i < (-lo).toNat + w.length
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp only [wordTape, List.length_replicate]
        rw [ite_eq_left (by omega), show (lo + i).toNat = i - (-lo).toNat by omega,
          List.getElem?_eq_getElem (by omega)]
        rfl
      · rw [List.getElem_append_right (by simp; omega), List.getElem_replicate]
        simp only [wordTape]
        split_ifs with h0
        · rw [List.getElem?_eq_none (by omega)]
          rfl
        · rfl
  rw [hsplit]
  have hw' : w.filter (· ≠ blank) = w := List.filter_eq_self.2 (fun x hx => by
    simp only [ne_eq, decide_eq_true_eq]; rintro rfl; exact hw hx)
  simp [List.filter_append]
  exact fun x hx hb => hw (hb ▸ hx)

end Tape

section Loops

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- Record in `flag` whether the left stack of tape `i` is nonempty. -/
def peekL (i : Fin T) : Act T Q A U :=
  .peek (.lt i) (fun v o => { v with flag := o.isSome }) .done

lemma peekL_run (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (peekL i : Act T Q A U).run (mk v S) = mk { v with flag := (S.L i).head?.isSome } S := rfl

/-- One step of `unload`: pop the left stack of tape `i` onto its right stack. -/
def unloadStep (i : Fin T) : Act T Q A U :=
  .pop (.lt i) (fun v o => { v with sym := o })
    (.push (.rt i) (fun v => v.sym.getD blank) (peekL i))

/-- Move the whole left stack of tape `i` onto its right stack. -/
def unload (i : Fin T) : Pr P T Q A U :=
  .seq (.act (peekL i)) (.loop (·.flag) (.act (unloadStep i)))

theorem unload_loop (i : Fin T) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.L i = l → v.flag = l.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (unloadStep i))) (mk v S) (2 * l.length + 1)
          (mk v' { S with
            L := Function.update S.L i []
            R := Function.update S.R i (l.reverse ++ S.R i) }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          L := Function.update S.L i []
          R := Function.update S.R i (([] : List (Fin (A + 4))).reverse ++ S.R i) } :
            Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          · funext k; by_cases hk : k = i
            · subst hk; simp [hS]
            · simp [hk]
          · funext k; by_cases hk : k = i
            · subst hk; simp
            · simp [hk]
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hu, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
        { S with
          L := Function.update S.L i rest
          R := Function.update S.R i (e :: S.R i) }
        (by simp) rfl
      refine ⟨v', hu, ?_⟩
      have hrun : (unloadStep i : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, flag := rest.head?.isSome }
            { S with
              L := Function.update S.L i rest
              R := Function.update S.R i (e :: S.R i) } := by
        simp [unloadStep, peekL, Action.run, hS, update_rt, update_lt]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (unloadStep i) (mk v S)) he) (by simp; ring) ?_
      congr 2
      · funext k; by_cases hk : k = i
        · subst hk; simp
        · simp [hk]
      · funext k; by_cases hk : k = i
        · subst hk; simp
        · simp [hk]

theorem unload_exec (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (unload i) (mk v S) (2 * (S.L i).length + 2)
        (mk v' { S with
          L := Function.update S.L i []
          R := Function.update S.R i ((S.L i).reverse ++ S.R i) }) := by
  obtain ⟨v', hu, he⟩ := unload_loop body i (S.L i) { v with flag := (S.L i).head?.isSome } S
    rfl rfl
  exact ⟨v', hu, Exec.cast
    (Exec.seq (peekL_run i v S ▸ Exec.act (body := body) (peekL i) (mk v S)) he) (by ring) rfl⟩

/-- One step of `sieve`: pop the right stack of tape `i`, keeping non-blank symbols on its left
stack. -/
def sieveStep (i : Fin T) : Act T Q A U :=
  .pop (.rt i) (fun v o => { v with sym := o })
    (.branch (fun v => decide (v.sym.getD blank ≠ blank))
      (.push (.lt i) (fun v => v.sym.getD blank) (peekR i))
      (peekR i))

/-- Move the right stack of tape `i` onto its left stack, dropping blanks. -/
def sieve (i : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR i)) (.loop (·.flag) (.act (sieveStep i)))

theorem sieve_loop (i : Fin T) :
    ∀ (r : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      S.R i = r → v.flag = r.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (sieveStep i))) (mk v S) (2 * r.length + 1)
          (mk v' { S with
            L := Function.update S.L i ((r.filter (· ≠ blank)).reverse ++ S.L i)
            R := Function.update S.R i [] }) := by
  intro r
  induction r with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          L := Function.update S.L i
            ((([] : List (Fin (A + 4))).filter (· ≠ blank)).reverse ++ S.L i)
          R := Function.update S.R i [] } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          · funext k; by_cases hk : k = i
            · subst hk; simp
            · simp [hk]
          · funext k; by_cases hk : k = i
            · subst hk; simp [hS]
            · simp [hk]
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      by_cases he : e = blank
      · obtain ⟨v', hu, hx⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
          { S with R := Function.update S.R i rest } (by simp) rfl
        refine ⟨v', hu, ?_⟩
        have hrun : (sieveStep i : Act T Q A U).run (mk v S) =
            mk { v with sym := some e, flag := rest.head?.isSome }
              { S with R := Function.update S.R i rest } := by
          simp [sieveStep, peekR, Action.run, hS, update_rt, he]
        refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
          (hrun ▸ Exec.act (body := body) (sieveStep i) (mk v S)) hx) (by simp; ring) ?_
        congr 2
        · funext k; by_cases hk : k = i
          · subst hk; simp [he]
          · simp [hk]
        · funext k; by_cases hk : k = i
          · subst hk; simp
          · simp [hk]
      · obtain ⟨v', hu, hx⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
          { S with
            L := Function.update S.L i (e :: S.L i)
            R := Function.update S.R i rest }
          (by simp) rfl
        refine ⟨v', hu, ?_⟩
        have hrun : (sieveStep i : Act T Q A U).run (mk v S) =
            mk { v with sym := some e, flag := rest.head?.isSome }
              { S with
                L := Function.update S.L i (e :: S.L i)
                R := Function.update S.R i rest } := by
          simp [sieveStep, peekR, Action.run, hS, update_rt, update_lt, he]
        refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
          (hrun ▸ Exec.act (body := body) (sieveStep i) (mk v S)) hx) (by simp; ring) ?_
        congr 2
        · funext k; by_cases hk : k = i
          · subst hk; simp [he]
          · simp [hk]
        · funext k; by_cases hk : k = i
          · subst hk; simp
          · simp [hk]

theorem sieve_exec (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (sieve i) (mk v S) (2 * (S.R i).length + 2)
        (mk v' { S with
          L := Function.update S.L i (((S.R i).filter (· ≠ blank)).reverse ++ S.L i)
          R := Function.update S.R i [] }) := by
  obtain ⟨v', hu, he⟩ := sieve_loop body i (S.R i) { v with flag := (S.R i).head?.isSome } S
    rfl rfl
  exact ⟨v', hu, Exec.cast
    (Exec.seq (peekR_run i v S ▸ Exec.act (body := body) (peekR i) (mk v S)) he) (by ring) rfl⟩

/-- The blank-free content of a tape stored as stacks `L`, `R`. -/
def sweep (L R : List (Fin (A + 4))) : List (Fin (A + 4)) := (L.reverse ++ R).filter (· ≠ blank)

/-- Normalize tape `i`: its blank-free content ends on the right stack, the left stack empty. -/
def normTape (i : Fin T) : Pr P T Q A U := .seq (unload i) (.seq (sieve i) (unload i))

theorem normTape_exec (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6 * ((S.L i).length + (S.R i).length) + 6 ∧
      Exec body (normTape i) (mk v S) n
        (mk v' { S with
          L := Function.update S.L i []
          R := Function.update S.R i (sweep (S.L i) (S.R i)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := unload_exec body i v S
  obtain ⟨v₂, hu₂, he₂⟩ := sieve_exec body i v₁ _
  obtain ⟨v₃, hu₃, he₃⟩ := unload_exec body i v₂ _
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · simp only [Function.update_self, List.length_append, List.length_reverse, List.append_nil]
    have := List.length_filter_le (fun x => decide (x ≠ (blank : Fin (A + 4))))
      ((S.L i).reverse ++ S.R i)
    simp only [List.length_append, List.length_reverse] at this
    omega
  · congr 2
    · funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    · funext k; by_cases hk : k = i
      · subst hk; simp [sweep]
      · simp [hk]

/-- Normalize every tape of a list. -/
def normList (l : List (Fin T)) : Pr P T Q A U := Prog.seqList (l.map normTape)

theorem normList_exec : ∀ (l : List (Fin T)), l.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A),
    ∃ v' n, v'.user = v.user ∧
      n ≤ (l.map fun i => 6 * ((S.L i).length + (S.R i).length) + 6).sum + 1 ∧
      Exec body (normList l) (mk v S) n
        (mk v' { S with
          L := fun i => if i ∈ l then [] else S.L i
          R := fun i => if i ∈ l then sweep (S.L i) (S.R i) else S.R i }) := by
  intro l
  induction l with
  | nil =>
      intro _ v S
      refine ⟨v, 1, rfl, by simp, ?_⟩
      have : ({ S with
          L := fun i => if i ∈ ([] : List (Fin T)) then [] else S.L i
          R := fun i => if i ∈ ([] : List (Fin T)) then sweep (S.L i) (S.R i) else S.R i } :
            Stacks T A) = S := by cases S; simp
      rw [this]
      exact Exec.act .done (mk v S)
  | cons i rest ih =>
      intro hnd v S
      rw [List.nodup_cons] at hnd
      obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := normTape_exec body i v S
      obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := ih hnd.2 v₁ _
      refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, ?_, Exec.cast (Exec.seq he₁ he₂) rfl ?_⟩
      · have hsum : (rest.map fun j => 6 * ((Function.update S.L i [] j).length +
            (Function.update S.R i (sweep (S.L i) (S.R i)) j).length) + 6) =
            rest.map fun j => 6 * ((S.L j).length + (S.R j).length) + 6 := by
          apply List.map_congr_left
          intro j hj
          have hji : j ≠ i := fun h => hnd.1 (h ▸ hj)
          simp [Function.update_of_ne hji]
        simp only [hsum] at hn₂
        simp only [List.map_cons, List.sum_cons]
        omega
      · congr 2
        · funext j
          by_cases hj : j = i
          · subst hj; simp [hnd.1]
          · simp [hj]
        · funext j
          by_cases hj : j = i
          · subst hj; simp [hnd.1]
          · simp [hj]

/-- Move the top of the right stack of tape `i` to its left stack. -/
def shiftStep (i : Fin T) : Act T Q A U :=
  .pop (.rt i) (fun v o => { v with sym := o }) (.push (.lt i) (fun v => v.sym.getD blank) .done)

/-- Shift every tape of a list one cell to the right. -/
def shiftList (l : List (Fin T)) : Pr P T Q A U :=
  Prog.seqList (l.map fun i => .act (shiftStep i))

theorem shiftList_exec : ∀ (l : List (Fin T)), l.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A),
    ∃ v', v'.user = v.user ∧
      Exec body (shiftList l) (mk v S) (l.length + 1)
        (mk v' { S with
          L := fun i => if i ∈ l then (S.R i).head?.getD blank :: S.L i else S.L i
          R := fun i => if i ∈ l then (S.R i).tail else S.R i }) := by
  intro l
  induction l with
  | nil =>
      intro _ v S
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          L := fun i =>
            if i ∈ ([] : List (Fin T)) then (S.R i).head?.getD blank :: S.L i else S.L i
          R := fun i => if i ∈ ([] : List (Fin T)) then (S.R i).tail else S.R i } :
            Stacks T A) = S := by cases S; simp
      rw [this]
      exact Exec.act .done (mk v S)
  | cons i rest ih =>
      intro hnd v S
      rw [List.nodup_cons] at hnd
      have hrun : (shiftStep i : Act T Q A U).run (mk v S) =
          mk { v with sym := (S.R i).head? } { S with
            L := Function.update S.L i ((S.R i).head?.getD blank :: S.L i)
            R := Function.update S.R i (S.R i).tail } := by
        simp [shiftStep, Action.run, update_rt, update_lt]
      obtain ⟨v₂, hu₂, he₂⟩ := ih hnd.2 { v with sym := (S.R i).head? } _
      refine ⟨v₂, hu₂, Exec.cast
        (Exec.seq (hrun ▸ Exec.act (body := body) (shiftStep i) (mk v S)) he₂) (by simp; ring) ?_⟩
      congr 2
      · funext j
        by_cases hj : j = i
        · subst hj; simp [hnd.1]
        · simp [hj]
      · funext j
        by_cases hj : j = i
        · subst hj; simp [hnd.1]
        · simp [hj]

end Loops

/-! ### The interchange machine's tape bank -/

section Bank

variable {t n s a : ℕ}

/-- `v` is the caller bank `c` followed by blank tapes with heads at `0`. -/
def Ext (c : Tapes t a) (v : Tapes n a) : Prop :=
  ∀ j : Fin n, v.head j = (if h : j.val < t then c.head ⟨j, h⟩ else 0) ∧
    v.tape j = (if h : j.val < t then c.tape ⟨j, h⟩ else fun _ => blank)

lemma Ext.refl (c : Tapes t a) : Ext c c := fun j => by simp [j.isLt]

lemma Ext.append {c : Tapes t a} {v : Tapes n a} (hv : Ext c v) (htn : t ≤ n) (e : Tapes s a)
    (he : ∀ j, e.head j = 0 ∧ e.tape j = fun _ => blank) : Ext c (v.append e) := by
  intro j
  induction j using Fin.addCases with
  | left j => simpa [Tapes.append] using hv j
  | right j =>
      simp only [Tapes.append, Fin.addCases_right, Fin.val_natAdd]
      rw [dite_eq_right (by omega), dite_eq_right (by omega)]
      exact he j

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
/-- The interchange machine's input bank: the caller's tapes, then blank private tapes. -/
lemma input_ext (c : Tapes t prime) : Ext c (BinaryInterchangeRun.input c) := by
  unfold BinaryInterchangeRun.input BinaryInterchangeRun.bankInput BinaryInterchangeRun.middle
    BinaryAdjacentWidthMovementShared.input BinaryRadixEqualShared.input
    BinaryAdjacentWidthPrefixShared.input BinaryAdjacentWidthHeadersShared.input
  refine Ext.append ?_ (by omega) _ (fun _ => ⟨rfl, rfl⟩)
  refine Ext.append ?_ (by omega) _ (fun _ => ⟨rfl, rfl⟩)
  refine Ext.append ?_ (by omega) _ (fun _ => ⟨rfl, rfl⟩)
  refine Ext.append ?_ (by omega) _ (fun _ => ⟨rfl, rfl⟩)
  refine Ext.append ?_ (by omega) _ (fun _ => ⟨rfl, rfl⟩)
  refine Ext.append ?_ (by omega) _ (fun _ => ⟨rfl, rfl⟩)
  refine Ext.append ?_ (by omega) _ (fun _ => ⟨rfl, rfl⟩)
  exact Ext.refl c

end Bank

/-! ### List-level interchange -/

section Interchange

open BinaryAdjacentWidthInterchange

/-- Source offset of the cell at target offset `z` when `[P]×[H]×[G]×[D]×[B]` (row-major, `P`
outermost) is interchanged into `[P]×[D]×[G]×[H]×[B]`. -/
def swapSrc (H G D B z : ℕ) : ℕ :=
  (((z / B / H / G / D * H + z / B % H) * G + z / B / H % G) * D + z / B / H / G % D) * B + z % B

/-- The interchange of a list laid out as `[P]×[H]×[G]×[D]×[B]` into `[P]×[D]×[G]×[H]×[B]`;
`dflt` fills offsets beyond the list. -/
def swapList {α : Type*} (P H G D B : ℕ) (dflt : α) (l : List α) : List α :=
  (List.range (P * D * G * H * B)).map fun z => l.getD (swapSrc H G D B z) dflt

theorem ofFn_transpose {α : Type*} {P H G D B : ℕ} (x : Fin (volume P H G D B) → α) (dflt : α) :
    List.ofFn (transpose x) = swapList P H G D B dflt (List.ofFn x) := by
  apply List.ext_getElem
  · rw [List.length_ofFn, swapList, List.length_map, List.length_range]; rfl
  · intro z h₁ h₂
    simp only [List.getElem_ofFn, swapList, List.getElem_map, List.getElem_range]
    set c := coordinates (⟨z, by simpa using h₁⟩ : Fin (volume P D G H B))
    have hidx : (index c.1 c.2.2.2.1 c.2.2.1 c.2.1 c.2.2.2.2 : Fin (volume P H G D B)).val =
        swapSrc H G D B z := by
      simp [c, index, coordinates, RecursiveInterchangeRows.pack_val, finProdFinEquiv,
        Fin.divNat, Fin.modNat, swapSrc]
    rw [← hidx, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      dite_eq_left (index c.1 c.2.2.2.1 c.2.2.1 c.2.1 c.2.2.2.2).isLt]
    rfl

lemma div_mod_mix {a b n : ℕ} (hb : b < n) : (a * n + b) / n = a ∧ (a * n + b) % n = b := by
  have hn : 0 < n := by omega
  constructor
  · rw [add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, zero_add]
  · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

lemma mix_lt {a b A n : ℕ} (ha : a < A) (hb : b < n) : a * n + b < A * n := by
  have : (a + 1) * n ≤ A * n := Nat.mul_le_mul_right _ ha
  nlinarith

/-- Entry of the interchanged list: target cell `(p, d, g, h, b)` holds source cell
`(p, h, g, d, b)`. -/
theorem swapList_getElem? {α : Type*} {P H G D B : ℕ} (dflt : α) (l : List α)
    (hl : l.length = P * H * G * D * B) {p h g d b : ℕ}
    (hp : p < P) (hh : h < H) (hg : g < G) (hd : d < D) (hb : b < B) :
    (swapList P H G D B dflt l)[(((p * D + d) * G + g) * H + h) * B + b]? =
      l[(((p * H + h) * G + g) * D + d) * B + b]? := by
  have hz : (((p * D + d) * G + g) * H + h) * B + b < P * D * G * H * B :=
    mix_lt (mix_lt (mix_lt (mix_lt hp hd) hg) hh) hb
  have hs : (((p * H + h) * G + g) * D + d) * B + b < l.length :=
    hl ▸ mix_lt (mix_lt (mix_lt (mix_lt hp hh) hg) hd) hb
  rw [swapList, List.getElem?_map, List.getElem?_range hz, Option.map_some]
  have hsrc : swapSrc H G D B ((((p * D + d) * G + g) * H + h) * B + b) =
      (((p * H + h) * G + g) * D + d) * B + b := by
    unfold swapSrc
    rw [(div_mod_mix hb).1, (div_mod_mix hb).2, (div_mod_mix hh).1, (div_mod_mix hh).2,
      (div_mod_mix hg).1, (div_mod_mix hg).2, (div_mod_mix hd).1, (div_mod_mix hd).2]
  rw [hsrc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs]
  rfl

/-- The interchanged payload bits as a list. -/
lemma transpose_bits_eq_swapList {P H G D B a : ℕ} (x : Fin (volume P H G D B) → Bool) :
    (List.ofFn fun z => (bitSymbol (transpose x z) : Fin (a + 4))) =
      swapList P H G D B blank (List.ofFn fun i => bitSymbol (x i)) :=
  ofFn_transpose (fun i => bitSymbol (x i)) blank

end Interchange

/-! ### The host subprogram -/

noncomputable section

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Host tape count for a caller bank of `t₀` registers: the caller registers, then the
interchange machine's private tapes. -/
abbrev swapT (t₀ : ℕ) : ℕ := BinaryInterchangeRun.bankCount t₀ + 1

/-- The host register holding caller tape `i`; its index is `i`. -/
abbrev reg {t₀ : ℕ} (i : Fin t₀) : Fin (swapT t₀) := BinaryInterchangeRun.slot i

lemma reg_val {t₀ : ℕ} (i : Fin t₀) : (reg i).val = i.val := rfl

/-- The state count of a program. -/
def stateCount {t q a : ℕ} (_ : Program t q a) : ℕ := q

/-- The state count of the interchange machine. -/
abbrev swapStates {t₀ : ℕ} (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd) :
    ℕ :=
  stateCount (BinaryInterchangeRun.program hd pay hi)

/-- The state count does not depend on the chosen tapes. -/
lemma swapStates_eq {t₀ : ℕ} (hd hd' : Fin 5 → Fin t₀) (pay pay' : Fin t₀)
    (hi : Function.Injective hd) (hi' : Function.Injective hd') :
    swapStates hd pay hi = swapStates hd' pay' hi' := by
  unfold swapStates stateCount; rfl

/-- The interchange machine over the host alphabet `Fin (prime + K + 4)`. -/
def swapMachine {t₀ : ℕ} (K : ℕ) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) :=
  Alphabet.program (Alphabet.widen prime K) (BinaryInterchangeRun.program hd pay hi)

/-- Interchange on host registers: shift each header register one cell, run the interchange
machine, then normalize every tape. -/
def swapProg {t₀ Q K : ℕ} {U F : Type} (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q) :
    Pr F (swapT t₀) Q (prime + K) U :=
  .seq (shiftList (List.ofFn fun k => reg (hd k)))
    (.seq (foreign (liftQ (swapMachine K hd pay hi) hQ)) (normList (List.finRange _)))

section Symbols

variable {K : ℕ}

@[simp] lemma widen_decode_bitSymbol (b : Bool) :
    (Alphabet.widen prime K).decode (bitSymbol b) = bitSymbol b :=
  (Alphabet.widen prime K).decode_encode (bitSymbol b)

@[simp] lemma widen_decode_separator :
    (Alphabet.widen prime K).decode separator = separator :=
  (Alphabet.widen prime K).decode_encode separator

lemma bitSymbol_good (b : Bool) :
    (bitSymbol b : Fin (prime + K + 4)) ≠ blank ∧
      (bitSymbol b : Fin (prime + K + 4)).val < prime + 4 := by
  cases b <;> simp [bitSymbol, blank, Fin.ext_iff]

lemma separator_good :
    (separator : Fin (prime + K + 4)) ≠ blank ∧
      (separator : Fin (prime + K + 4)).val < prime + 4 := by
  simp [separator, blank, Fin.ext_iff]

/-- Encoding the decoded word of an initial-segment list gives the list back. -/
lemma encode_wordTape_decode (l : List (Fin (prime + K + 4))) (hl : ∀ s ∈ l, s.val < prime + 4)
    (z : ℤ) :
    (Alphabet.widen prime K).encode (wordTape (l.map (Alphabet.widen prime K).decode) z) =
      wordTape l z := by
  unfold wordTape
  split_ifs
  · rw [List.getElem?_map]
    cases hz : l[z.toNat]? with
    | none => rfl
    | some s =>
        have hs := hl s (List.mem_of_getElem? hz)
        simp only [Option.map_some, Option.getD_some]
        apply Fin.ext
        simp [Alphabet.widen, hs]
  · rfl

lemma encode_wordTape (l : List (Fin (prime + 4))) (z : ℤ) :
    (Alphabet.widen prime K).encode (wordTape l z) =
      wordTape (l.map (Alphabet.widen prime K).encode) z := by
  unfold wordTape
  split_ifs
  · rw [List.getElem?_map]
    cases l[z.toNat]? <;> rfl
  · rfl

end Symbols

/-- Running the interchange on host registers. Register `pay` holds the payload bits, register
`hd k` the encoded header `separator :: bits` of `hs k`; every left stack and every private
register is empty; every other caller register holds non-blank symbols of the vendored alphabet.
Afterwards the payload register holds the interchanged bits, every left stack is empty, and every
other register is unchanged. -/
theorem swapProg_exec {t₀ Q K : ℕ} {U F : Type} (body : F → Pr F (swapT t₀) Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (P G B h d : ℕ) (hs : Fin 5 → List Bool) (hhd : h ≤ d + 1) (hdh : d ≤ h + 1)
    (hv : ∀ k, Counter.value (hs k) = BinaryInterchangeRun.values P G B h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) B) → Bool)
    (v : HS (swapT t₀) Q (prime + K) U) (S : Stacks (swapT t₀) (prime + K))
    (hL : ∀ j, S.L j = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R j = [])
    (hhdr : ∀ k, S.R (reg (hd k)) = separator :: (hs k).map bitSymbol)
    (hpay : S.R (reg pay) = List.ofFn fun i => bitSymbol (x i))
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) → ∀ s ∈ S.R (reg i), s ≠ blank ∧ s.val < prime + 4) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (13 * swapT t₀ + 5) * BinaryInterchangeRun.cost P G B h d hs +
        6 * ∑ j, (S.R j).length + 6 * swapT t₀ + 13 ∧
      Exec body (swapProg hd pay hi hQ) (mk v S) m
        (mk v' { S with
          L := fun _ => []
          R := Function.update S.R (reg pay)
            (List.ofFn fun z => bitSymbol (BinaryAdjacentWidthInterchange.transpose x z)) }) := by
  classical
  set e := Alphabet.widen prime K with he_def
  -- every register holds non-blank symbols of the vendored alphabet
  have hgood : ∀ j, ∀ s ∈ S.R j, s ≠ blank ∧ s.val < prime + 4 := by
    intro j s hs'
    by_cases hj : j.val < t₀
    · have hji : j = reg (⟨j.val, hj⟩ : Fin t₀) := Fin.ext rfl
      rw [hji] at hs'
      by_cases hip : (⟨j.val, hj⟩ : Fin t₀) = pay
      · rw [hip, hpay, List.mem_ofFn] at hs'
        obtain ⟨z, rfl⟩ := hs'
        exact bitSymbol_good _
      · by_cases hk : ∃ k, hd k = ⟨j.val, hj⟩
        · obtain ⟨k, hk⟩ := hk
          rw [← hk, hhdr k] at hs'
          simp only [List.mem_cons, List.mem_map] at hs'
          rcases hs' with rfl | ⟨b, _, rfl⟩
          · exact separator_good
          · exact bitSymbol_good _
        · exact hother _ hip (fun k hk' => hk ⟨k, hk'⟩) s hs'
    · rw [hpriv j (by omega)] at hs'
      simp at hs'
  -- the payload register is not a header register
  have hpay_hd : ∀ k, hd k ≠ pay := by
    intro k hk
    have hvol : 0 < BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) B := by
      unfold BinaryAdjacentWidthInterchange.volume; positivity
    have h1 := congrArg (fun l => l[0]?) (hhdr k)
    rw [hk, hpay] at h1
    simp only [List.getElem?_ofFn, hvol, dite_true, List.getElem?_cons_zero,
      Option.some.injEq] at h1
    have h2 := congrArg Fin.val h1
    revert h2
    cases x ⟨0, hvol⟩ <;> simp [bitSymbol, separator]
  -- the caller bank seen by the interchange machine
  let caller : Tapes t₀ prime :=
    ⟨fun i => if ∃ k, hd k = i then 1 else 0, fun i => wordTape ((S.R (reg i)).map e.decode)⟩
  have htapes : ∀ k, caller.tape (hd k) = RadixZeroFill.encodedBinary (hs k) := by
    intro k
    show wordTape ((S.R (reg (hd k))).map e.decode) = _
    rw [hhdr k, encodedBinary_eq]
    simp [e, Function.comp_def]
  have hheads : ∀ k, caller.head (hd k) = 1 := fun k => by
    show (if ∃ k', hd k' = hd k then (1 : ℤ) else 0) = 1
    rw [ite_eq_left ⟨k, rfl⟩]
  have ht :
      caller.tape pay = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)) := by
    show wordTape ((S.R (reg pay)).map e.decode) = _
    rw [BinaryRadixRangePrepareAlphabet.word, putWord_blank_zero, hpay, List.map_ofFn]
    simp [e, Function.comp_def]
  have hh : caller.head pay = 0 := by
    show (if ∃ k, hd k = pay then (1 : ℤ) else 0) = 0
    rw [ite_eq_right (fun ⟨k, hk⟩ => hpay_hd k hk)]
  have hrun := BinaryInterchangeRun.runs caller hd pay hi P G B h d hs hhd hdh hv hc hP hG hB
    htapes hheads x ht hh
  have hM := HoareTime.liftQ hQ (Alphabet.map_hoare e hrun)
  -- step 1: shift the header registers
  set l₀ : List (Fin (swapT t₀)) := List.ofFn fun k => reg (hd k) with hl₀
  have hnd₀ : l₀.Nodup := by
    rw [hl₀, List.nodup_ofFn]
    intro a b hab
    exact hi (BinaryInterchangeRun.slot_injective hab)
  have hmem : ∀ j, j ∈ l₀ ↔ ∃ k, reg (hd k) = j := fun j => List.mem_ofFn
  obtain ⟨v₁, hu₁, he₁⟩ := shiftList_exec body l₀ hnd₀ v S
  set S₁ : Stacks (swapT t₀) (prime + K) := { S with
    L := fun i => if i ∈ l₀ then (S.R i).head?.getD blank :: S.L i else S.L i
    R := fun i => if i ∈ l₀ then (S.R i).tail else S.R i } with hS₁
  have hS₁len : ∀ i, (S₁.L i).length + (S₁.R i).length = (S.R i).length := by
    intro i
    by_cases hm : i ∈ l₀
    · obtain ⟨k, rfl⟩ := (hmem i).1 hm
      simp [S₁, hm, hL, hhdr k]
      omega
    · simp [S₁, hm, hL]
  have hrep : RepT (Alphabet.mapTapes e (BinaryInterchangeRun.input caller)) S₁.L S₁.R := by
    intro j z
    obtain ⟨hhead, htape⟩ := input_ext caller j
    show e.encode ((BinaryInterchangeRun.input caller).tape j z) =
      readAt blank (S₁.L j) (S₁.R j) (z - (BinaryInterchangeRun.input caller).head j)
    rw [hhead, htape]
    by_cases hj : j.val < t₀
    · rw [dite_eq_left hj, dite_eq_left hj]
      obtain ⟨i, rfl⟩ : ∃ i : Fin t₀, j = reg i := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
      change e.encode (wordTape ((S.R (reg i)).map e.decode) z) =
        readAt blank (S₁.L (reg i)) (S₁.R (reg i)) (z - caller.head i)
      rw [encode_wordTape_decode _ (fun s hs => (hgood _ s hs).2) z]
      by_cases hk : ∃ k, hd k = i
      · obtain ⟨k, rfl⟩ := hk
        have hm : reg (hd k) ∈ l₀ := (hmem _).2 ⟨k, rfl⟩
        simp only [S₁, hm, ite_true, hL, hhdr k, hheads k, List.head?_cons, Option.getD_some,
          List.tail_cons]
        rw [readAt_single]
      · have hm : reg i ∉ l₀ := fun hm => by
          obtain ⟨k, hk'⟩ := (hmem _).1 hm
          exact hk ⟨k, BinaryInterchangeRun.slot_injective hk'⟩
        have hc0 : caller.head i = 0 := ite_eq_right hk
        simp only [S₁, hm, ite_false, hL, hc0, sub_zero]
        rw [readAt_nil_left]
    · rw [dite_eq_right hj, dite_eq_right hj]
      have hm : j ∉ l₀ := fun hm => by
        obtain ⟨k, rfl⟩ := (hmem _).1 hm
        exact hj (hd k).isLt
      simp only [S₁, hm, ite_false, hL, hpriv j (by omega), readAt_nil_left, wordTape_nil]
      rfl
  -- step 2: run the interchange machine
  obtain ⟨v₂, S₂, w', ⟨orig, horig, rfl⟩, hrep', hu₂, hinp₂, hout₂, hlen₂, m₂, hm₂, he₂⟩ :=
    foreign_exec body _ hM v₁ S₁ _ ⟨_, rfl, rfl⟩ hrep
  subst horig
  -- the tapes after the run
  set out : List (Fin (prime + K + 4)) :=
    List.ofFn fun z => bitSymbol (BinaryAdjacentWidthInterchange.transpose x z) with hout
  have hfinal : ∀ j z, (Alphabet.mapTapes e (BinaryInterchangeRun.input
      (SharedPlacementAlphabet.setTape caller pay (BinaryRadixRangePrepareAlphabet.word
        (BinaryAdjacentWidthInterchange.transpose fun i => bitSymbol (x i))) 0))).tape j z =
      wordTape (Function.update S.R (reg pay) out j) z := by
    intro j z
    obtain ⟨_, htape⟩ := input_ext (SharedPlacementAlphabet.setTape caller pay
      (BinaryRadixRangePrepareAlphabet.word
        (BinaryAdjacentWidthInterchange.transpose fun i => bitSymbol (x i))) 0) j
    show e.encode ((BinaryInterchangeRun.input _).tape j z) = _
    rw [htape]
    by_cases hj : j.val < t₀
    · rw [dite_eq_left hj]
      obtain ⟨i, rfl⟩ : ∃ i : Fin t₀, j = reg i := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
      change e.encode (Function.update caller.tape pay (BinaryRadixRangePrepareAlphabet.word
        (BinaryAdjacentWidthInterchange.transpose fun i => bitSymbol (x i))) i z) = _
      by_cases hip : i = pay
      · subst hip
        rw [Function.update_self, Function.update_self, BinaryRadixRangePrepareAlphabet.word,
          putWord_blank_zero, encode_wordTape, List.map_ofFn]
        rfl
      · have hr : reg i ≠ reg pay := fun h' => hip (BinaryInterchangeRun.slot_injective h')
        rw [Function.update_of_ne hip, Function.update_of_ne hr]
        exact encode_wordTape_decode _ (fun s hs => (hgood _ s hs).2) z
    · rw [dite_eq_right hj]
      have hr : j ≠ reg pay := fun h' => hj (h' ▸ pay.isLt)
      rw [Function.update_of_ne hr, hpriv j (by omega), wordTape_nil]
      rfl
  have hfree : ∀ j, blank ∉ Function.update S.R (reg pay) out j := by
    intro j hb
    by_cases hj : j = reg pay
    · subst hj
      rw [Function.update_self, hout, List.mem_ofFn] at hb
      obtain ⟨z, hz⟩ := hb
      exact (bitSymbol_good _).1 hz
    · rw [Function.update_of_ne hj] at hb
      exact (hgood j blank hb).1 rfl
  -- step 3: normalize every tape
  obtain ⟨v₃, n₃, hu₃, hn₃, he₃⟩ :=
    normList_exec body (List.finRange _) (List.nodup_finRange _) v₂ S₂
  refine ⟨v₃, l₀.length + 1 + (m₂ + n₃), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ he₃)) rfl ?_⟩
  · rw [← Fin.sum_univ_def] at hn₃
    set k := BinaryInterchangeRun.cost P G B h d hs
    have hsum : ∑ i, (6 * ((S₂.L i).length + (S₂.R i).length) + 6) ≤
        ∑ i, (6 * (S.R i).length + (12 * k + 6)) := by
      apply Finset.sum_le_sum
      intro i _
      have h1 := hlen₂ i
      rw [hS₁len] at h1
      omega
    have hR : ∑ i : Fin (swapT t₀), (6 * (S.R i).length + (12 * k + 6)) =
        6 * ∑ i, (S.R i).length + swapT t₀ * (12 * k + 6) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    have key : k * (swapT t₀ + 5) + swapT t₀ * (12 * k + 6) =
        (13 * swapT t₀ + 5) * k + 6 * swapT t₀ := by ring
    have hl : l₀.length = 5 := by simp [hl₀]
    rw [hl]
    omega
  · congr 1
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact hinp₂
    · exact hout₂
    · funext j; simp [List.mem_finRange]
    · funext j
      simp only [List.mem_finRange, ite_true]
      exact filter_window (S₂.L j) (S₂.R j) _ _ (hfree j)
        (fun z => by rw [← hfinal j z]; exact hrep' j z)

/-- `swapProg_exec` with the payload output as a list function of the payload input. -/
theorem swapProg_exec_list {t₀ Q K : ℕ} {U F : Type} (body : F → Pr F (swapT t₀) Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (P G B h d : ℕ) (hs : Fin 5 → List Bool) (hhd : h ≤ d + 1) (hdh : d ≤ h + 1)
    (hv : ∀ k, Counter.value (hs k) = BinaryInterchangeRun.values P G B h d k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) B) → Bool)
    (v : HS (swapT t₀) Q (prime + K) U) (S : Stacks (swapT t₀) (prime + K))
    (hL : ∀ j, S.L j = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R j = [])
    (hhdr : ∀ k, S.R (reg (hd k)) = separator :: (hs k).map bitSymbol)
    (hpay : S.R (reg pay) = List.ofFn fun i => bitSymbol (x i))
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) → ∀ s ∈ S.R (reg i), s ≠ blank ∧ s.val < prime + 4) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (13 * swapT t₀ + 5) * BinaryInterchangeRun.cost P G B h d hs +
        6 * ∑ j, (S.R j).length + 6 * swapT t₀ + 13 ∧
      Exec body (swapProg hd pay hi hQ) (mk v S) m
        (mk v' { S with
          L := fun _ => []
          R := Function.update S.R (reg pay)
            (swapList P (2 ^ h) G (2 ^ d) B blank (S.R (reg pay))) }) := by
  obtain ⟨v', m, hu, hm, he⟩ := swapProg_exec body hd pay hi hQ P G B h d hs hhd hdh hv hc
    hP hG hB x v S hL hpriv hhdr hpay hother
  refine ⟨v', m, hu, hm, ?_⟩
  rw [hpay, ← transpose_bits_eq_swapList]
  exact he

end

end IntegerMultBounds.MathlibTM2.Host
