module

public import IntegerMultBounds.MathlibTM2.DFT.Keys
public import IntegerMultBounds.MathlibTM2.Host.Index
import Mathlib.Data.Num.Lemmas

/-!
# Reading and writing `Γ'` on a host register

The DFT machine runs host code on the keys `.host k` of `DK (HK T)` (`DFT/Keys.lean`). Its `Γ'`
input and output pass through one host register each.

**Symbols.** `gamCode` writes a `Γ'` bit as `bitSymbol` and the comma as `separator`;
`gamDecode` inverts it on bits and separators (`gamDecode_bitSymbol`, `gamDecode_separator`).

**Loops.** On `dmk v S gi go` (host local state `v`, host stacks `S`, `gi` on `gin`, `go` on
`gout`):
* `readIn r` moves `gin` onto register `r`, coding each symbol: `r` gains `(gi.map gamCode)`
  reversed on top and `gin` ends empty (`readIn_exec`, `2 |gi| + 2` steps);
* `writeOut r` moves register `r` onto `gout`, decoding each symbol: `gout` gains the decoded
  register reversed on top and `r` ends empty (`writeOut_exec`, `2 |r| + 2` steps).
Both keep `user` and the scan slots, and every other stack.

**Encodings.** `encodeFixedList_map`: the input `encodeFixedList w l` codes to `fieldSyms w l`,
each number as `binSyms w x` followed by a separator. `natSyms_map`: `natSyms l`, each number as
`binSyms (Nat.size x) x` followed by a separator, decodes to `encodeNatList l`, because
`encodeNat x = binBits (Nat.size x) x` (`encodeNat_eq_binBits`). `only_gin`, `only_gout`: the
stores of `ComputesWithin` are `dmk` stores with all host stacks empty.
-/

@[expose] public section

open Computability IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host

namespace IntegerMultBounds.MathlibTM2.DFT

/-! ### Stores over `DK (HK T)` -/

section Stores

variable {K : Type} [DecidableEq K] {Γ : K → Type}

theorem hostStk_update_gin (S : ∀ k, List (Γ k)) (gi go l : List Γ') :
    Function.update (hostStk S gi go) .gin l = hostStk S l go := by
  funext j
  cases j with
  | gin => exact Function.update_self _ _ _
  | gout => exact Function.update_of_ne (show (DK.gout : DK K) ≠ .gin from nofun) _ _
  | host k => exact Function.update_of_ne (show (DK.host k : DK K) ≠ .gin from nofun) _ _

theorem hostStk_update_gout (S : ∀ k, List (Γ k)) (gi go l : List Γ') :
    Function.update (hostStk S gi go) .gout l = hostStk S gi l := by
  funext j
  cases j with
  | gin => exact Function.update_of_ne (show (DK.gin : DK K) ≠ .gout from nofun) _ _
  | gout => exact Function.update_self _ _ _
  | host k => exact Function.update_of_ne (show (DK.host k : DK K) ≠ .gout from nofun) _ _

@[simp] lemma hostStk_gin (S : ∀ k, List (Γ k)) (gi go : List Γ') : hostStk S gi go .gin = gi :=
  rfl

@[simp] lemma hostStk_gout (S : ∀ k, List (Γ k)) (gi go : List Γ') :
    hostStk S gi go .gout = go := rfl

@[simp] lemma hostStk_host (S : ∀ k, List (Γ k)) (gi go : List Γ') (k : K) :
    hostStk S gi go (.host k) = S k := rfl

end Stores

variable {T Q A : ℕ} {U P : Type}

/-- Straight-line code and programs over the host keys and the `Γ'` stacks. -/
abbrev DAct (T Q A : ℕ) (U : Type) := Action (DΓ (HΓ (T := T) A)) (HS T Q A U)
abbrev DPr (P : Type) (T Q A : ℕ) (U : Type) := Prog P (DΓ (HΓ (T := T) A)) (HS T Q A U)

/-- The store with host local state `v`, host stacks `S`, `gi` on `gin` and `go` on `gout`. -/
def dmk (v : HS T Q A U) (S : Stacks T A) (gi go : List Γ') :
    Store (DΓ (HΓ (T := T) A)) (HS T Q A U) :=
  ⟨v, hostStk S.get gi go⟩

theorem dmk_eq_hostExt (v : HS T Q A U) (S : Stacks T A) (gi go : List Γ') :
    dmk v S gi go = hostExt (mk v S) gi go := rfl

@[simp] lemma dmk_var (v : HS T Q A U) (S : Stacks T A) (gi go : List Γ') :
    (dmk v S gi go).var = v := rfl

@[simp] lemma dmk_stk (v : HS T Q A U) (S : Stacks T A) (gi go : List Γ') :
    (dmk v S gi go).stk = hostStk S.get gi go := rfl

@[simp] lemma store_dmk (v : HS T Q A U) (S : Stacks T A) (gi go : List Γ') :
    (⟨v, hostStk S.get gi go⟩ : Store (DΓ (HΓ (T := T) A)) (HS T Q A U)) = dmk v S gi go := rfl

theorem hostStk_update_rt (S : Stacks T A) (gi go : List Γ') (i : Fin T)
    (l : List (Fin (A + 4))) :
    Function.update (hostStk S.get gi go) (.host (.rt i)) l =
      hostStk (Stacks.get { S with R := Function.update S.R i l }) gi go := by
  rw [hostStk_update, update_rt]

/-- No host stack holds anything. -/
def emptyStacks : Stacks T A := ⟨[], [], fun _ => [], fun _ => []⟩

theorem only_gin (v : HS T Q A U) (gi : List Γ') :
    Store.only (Γ := DΓ (HΓ (T := T) A)) v .gin gi = dmk v emptyStacks gi [] :=
  Store.ext rfl (funext fun j => by rcases j with _ | _ | (_ | _ | i | i) <;> rfl)

theorem only_gout (v : HS T Q A U) (go : List Γ') :
    Store.only (Γ := DΓ (HΓ (T := T) A)) v .gout go = dmk v emptyStacks [] go :=
  Store.ext rfl (funext fun j => by rcases j with _ | _ | (_ | _ | i | i) <;> rfl)

/-! ### Symbols -/

/-- A `Γ'` symbol on a host register: a bit as `bitSymbol`, the comma as `separator`. -/
def gamCode : Γ' → Fin (A + 4)
  | .bit b => bitSymbol b
  | .comma => separator
  | _ => blank

/-- A register symbol as `Γ'`: `separator` as the comma, every other symbol as a bit. -/
def gamDecode (x : Fin (A + 4)) : Γ' :=
  if x = separator then .comma else .bit (decide (x = bitSymbol true))

theorem gamDecode_bitSymbol (b : Bool) : gamDecode (bitSymbol (a := A) b) = .bit b := by
  cases b <;> simp [gamDecode, bitSymbol, separator]

theorem gamDecode_separator : gamDecode (separator (a := A)) = .comma := by
  rw [gamDecode, ite_eq_left rfl]

/-! ### Reading `gin` -/

/-- Record in `flag` whether `gin` is nonempty. -/
def peekIn : DAct T Q A U := .peek .gin (fun v o => { v with flag := o.isSome }) .done

/-- Pop `gin`, push its code onto register `r`, and record whether `gin` is nonempty. -/
def readStep (r : Fin T) : DAct T Q A U :=
  .pop .gin (fun v o => { v with sym := o.map gamCode })
    (.push (.host (.rt r)) (fun v => v.sym.getD blank) peekIn)

/-- Move `gin` onto register `r`, coding each symbol. -/
def readIn (r : Fin T) : DPr P T Q A U := .seq (.act peekIn) (.loop (·.flag) (.act (readStep r)))

theorem peekIn_run (v : HS T Q A U) (S : Stacks T A) (gi go : List Γ') :
    (peekIn : DAct T Q A U).run (dmk v S gi go) = dmk { v with flag := gi.head?.isSome } S gi go :=
  rfl

theorem readStep_run (r : Fin T) (g : Γ') (rest go : List Γ') (v : HS T Q A U)
    (S : Stacks T A) :
    (readStep r : DAct T Q A U).run (dmk v S (g :: rest) go) =
      dmk { v with sym := some (gamCode g), flag := rest.head?.isSome }
        { S with R := Function.update S.R r (gamCode g :: S.R r) } rest go := by
  simp [readStep, peekIn, Action.run, hostStk_update_gin, hostStk_update_rt]

variable (body : P → DPr P T Q A U)

theorem readIn_loop (r : Fin T) :
    ∀ (gi go : List Γ') (v : HS T Q A U) (S : Stacks T A), v.flag = gi.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan = v.scan ∧
        Exec body (.loop (·.flag) (.act (readStep r))) (dmk v S gi go) (2 * gi.length + 1)
          (dmk v' { S with R := Function.update S.R r ((gi.map gamCode).reverse ++ S.R r) } [] go)
  | [], go, v, S, hf => by
      refine ⟨v, rfl, rfl, ?_⟩
      have hS : ({ S with R := Function.update S.R r ((([] : List Γ').map gamCode).reverse ++
          S.R r) } : Stacks T A) = S := by
        rw [List.map_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
      rw [hS]
      exact .loop_false (by simpa using hf)
  | g :: rest, go, v, S, hf => by
      obtain ⟨v', hu, hsc, he⟩ := readIn_loop r rest go
        { v with sym := some (gamCode g), flag := rest.head?.isSome }
        { S with R := Function.update S.R r (gamCode g :: S.R r) } rfl
      refine ⟨v', hu, hsc, ?_⟩
      have hact : Exec body (.act (readStep r)) (dmk v S (g :: rest) go) 1
          (dmk { v with sym := some (gamCode g), flag := rest.head?.isSome }
            { S with R := Function.update S.R r (gamCode g :: S.R r) } rest go) := by
        rw [← readStep_run]
        exact .act _ _
      refine Exec.cast (Exec.loop_true (f := (·.flag)) (by simpa using hf) hact he)
        (by simp only [List.length_cons]; ring) ?_
      simp [Function.update_idem]

/-- `readIn r`: `gin` moves onto register `r`, coded and reversed, in `2 |gi| + 2` steps. -/
theorem readIn_exec (r : Fin T) (gi go : List Γ') (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan = v.scan ∧
      Exec body (readIn r) (dmk v S gi go) (2 * gi.length + 2)
        (dmk v' { S with R := Function.update S.R r ((gi.map gamCode).reverse ++ S.R r) }
          [] go) := by
  obtain ⟨v', hu, hsc, he⟩ := readIn_loop body r gi go { v with flag := gi.head?.isSome } S rfl
  have hpeek : Exec body (.act peekIn) (dmk v S gi go) 1
      (dmk { v with flag := gi.head?.isSome } S gi go) := by
    rw [← peekIn_run]
    exact .act _ _
  exact ⟨v', hu, hsc, Exec.cast (Exec.seq hpeek he) (by ring) rfl⟩

/-! ### Writing `gout` -/

/-- Record in `flag` whether register `r` is nonempty. -/
def peekOut (r : Fin T) : DAct T Q A U :=
  .peek (.host (.rt r)) (fun v o => { v with flag := o.isSome }) .done

/-- Pop register `r`, push its decoding onto `gout`, and record whether `r` is nonempty. -/
def writeStep (r : Fin T) : DAct T Q A U :=
  .pop (.host (.rt r)) (fun v o => { v with sym := o })
    (.push .gout (fun v => gamDecode (v.sym.getD blank)) (peekOut r))

/-- Move register `r` onto `gout`, decoding each symbol. -/
def writeOut (r : Fin T) : DPr P T Q A U :=
  .seq (.act (peekOut r)) (.loop (·.flag) (.act (writeStep r)))

theorem peekOut_run (r : Fin T) (v : HS T Q A U) (S : Stacks T A) (gi go : List Γ') :
    (peekOut r : DAct T Q A U).run (dmk v S gi go) =
      dmk { v with flag := (S.R r).head?.isSome } S gi go :=
  rfl

theorem writeStep_run (r : Fin T) (x : Fin (A + 4)) (rest : List (Fin (A + 4)))
    (gi go : List Γ') (v : HS T Q A U) (S : Stacks T A) (hS : S.R r = x :: rest) :
    (writeStep r : DAct T Q A U).run (dmk v S gi go) =
      dmk { v with sym := some x, flag := rest.head?.isSome }
        { S with R := Function.update S.R r rest } gi (gamDecode x :: go) := by
  simp [writeStep, peekOut, Action.run, hS, hostStk_update_rt, hostStk_update_gout]

theorem writeOut_loop (r : Fin T) :
    ∀ (l : List (Fin (A + 4))) (gi go : List Γ') (v : HS T Q A U) (S : Stacks T A),
      S.R r = l → v.flag = l.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan = v.scan ∧
        Exec body (.loop (·.flag) (.act (writeStep r))) (dmk v S gi go) (2 * l.length + 1)
          (dmk v' { S with R := Function.update S.R r [] } gi ((l.map gamDecode).reverse ++ go))
  | [], gi, go, v, S, hS, hf => by
      refine ⟨v, rfl, rfl, ?_⟩
      have hS' : ({ S with R := Function.update S.R r [] } : Stacks T A) = S := by
        rw [← hS, Function.update_eq_self]
      rw [hS', List.map_nil, List.reverse_nil, List.nil_append]
      exact .loop_false (by simpa using hf)
  | x :: rest, gi, go, v, S, hS, hf => by
      obtain ⟨v', hu, hsc, he⟩ := writeOut_loop r rest gi (gamDecode x :: go)
        { v with sym := some x, flag := rest.head?.isSome }
        { S with R := Function.update S.R r rest } (by simp) rfl
      refine ⟨v', hu, hsc, ?_⟩
      have hact : Exec body (.act (writeStep r)) (dmk v S gi go) 1
          (dmk { v with sym := some x, flag := rest.head?.isSome }
            { S with R := Function.update S.R r rest } gi (gamDecode x :: go)) := by
        rw [← writeStep_run r x rest gi go v S hS]
        exact .act _ _
      refine Exec.cast (Exec.loop_true (f := (·.flag)) (by simpa using hf) hact he)
        (by simp only [List.length_cons]; ring) ?_
      simp [Function.update_idem]

/-- `writeOut r`: register `r` moves onto `gout`, decoded and reversed, in `2 |r| + 2` steps. -/
theorem writeOut_exec (r : Fin T) (gi go : List Γ') (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧ v'.scan = v.scan ∧
      Exec body (writeOut r) (dmk v S gi go) (2 * (S.R r).length + 2)
        (dmk v' { S with R := Function.update S.R r [] } gi
          (((S.R r).map gamDecode).reverse ++ go)) := by
  obtain ⟨v', hu, hsc, he⟩ :=
    writeOut_loop body r (S.R r) gi go { v with flag := (S.R r).head?.isSome } S rfl rfl
  have hpeek : Exec body (.act (peekOut r)) (dmk v S gi go) 1
      (dmk { v with flag := (S.R r).head?.isSome } S gi go) := by
    rw [← peekOut_run]
    exact .act _ _
  exact ⟨v', hu, hsc, Exec.cast (Exec.seq hpeek he) (by ring) rfl⟩

/-! ### The encodings on registers -/

/-- Numbers in `w` binary digits each, least significant first, each followed by a separator. -/
def fieldSyms (w : ℕ) (l : List ℕ) : List (Fin (A + 4)) :=
  l.flatMap fun x => binSyms w x ++ [separator]

/-- Numbers in shortest binary form, least significant first, each followed by a separator. -/
def natSyms (l : List ℕ) : List (Fin (A + 4)) :=
  l.flatMap fun x => binSyms (Nat.size x) x ++ [separator]

theorem encodeFixed_map (w x : ℕ) : (encodeFixed w x).map (gamCode (A := A)) = binSyms w x := by
  rw [encodeFixed, binSyms, List.map_ofFn]
  rfl

theorem encodeFixedList_map (w : ℕ) (l : List ℕ) :
    (encodeFixedList w l).map (gamCode (A := A)) = fieldSyms w l := by
  rw [encodeFixedList, fieldSyms, List.map_flatMap]
  congr 1
  funext x
  rw [List.map_append, encodeFixed_map]
  rfl

theorem encodePosNum_eq_bits : ∀ m : PosNum, encodePosNum m = (m : ℕ).bits
  | .one => by rw [encodePosNum, PosNum.cast_one', Nat.one_bits]
  | .bit0 m => by
      rw [encodePosNum, PosNum.cast_bit0, ← two_mul, Nat.bit0_bits _ (PosNum.cast_pos m).ne',
        encodePosNum_eq_bits m]
  | .bit1 m => by
      rw [encodePosNum, PosNum.cast_bit1, ← two_mul, Nat.bit1_bits, encodePosNum_eq_bits m]

theorem encodeNat_eq_bits (n : ℕ) : encodeNat n = n.bits := by
  rw [encodeNat]
  conv_rhs => rw [← Num.to_of_nat n]
  cases (n : Num) with
  | zero => exact Nat.zero_bits.symm
  | pos m => rw [encodeNum, Num.cast_pos, encodePosNum_eq_bits]

theorem bits_eq_ofFn (n : ℕ) : n.bits = List.ofFn fun i : Fin (Nat.size n) => n.testBit i := by
  refine List.ext_getElem (by rw [List.length_ofFn, Nat.size_eq_bits_len]) fun i h₁ _ => ?_
  rw [List.getElem_ofFn, Nat.testBit_eq_inth, List.getI_eq_getElem _ h₁]

theorem bits_eq_binBits (n : ℕ) : n.bits = binBits (Nat.size n) n := bits_eq_ofFn n

/-- `encodeNat n` is the shortest binary form of `n`, least significant bit first. -/
theorem encodeNat_eq_binBits (n : ℕ) : encodeNat n = binBits (Nat.size n) n :=
  (encodeNat_eq_bits n).trans (bits_eq_binBits n)

theorem natSyms_map (l : List ℕ) : (natSyms (A := A) l).map gamDecode = encodeNatList l := by
  rw [natSyms, encodeNatList, List.map_flatMap]
  congr 1
  funext x
  rw [List.map_append, binSyms_eq, List.map_map, encodeNat_eq_binBits]
  congr 1
  exact List.map_congr_left fun b _ => gamDecode_bitSymbol b

end IntegerMultBounds.MathlibTM2.DFT
