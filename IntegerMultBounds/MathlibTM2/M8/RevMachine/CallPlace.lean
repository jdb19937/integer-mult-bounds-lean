module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Enter
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Blocks

/-!
# The call bank on the common bank

The call boundaries of stage 1 run on the forty-tape bank of `RecursiveChildCallSetup`: the six
headers at `3..8`, the descriptor and PC stacks at `38, 39`, every other tape blank. A program on
that bank with `e` more counter tapes is placed on the common bank (`place`): the headers on the
headers, the stacks on the call stacks, the counter tapes on chosen counters and everything else
private. `call_runs`: a run between two such banks is a run of the common bank that changes only
the headers and the call stacks.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.CallPlace

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs)
open CommonBank (bank K headerSlot auxSlot)
open CounterDimensions (descriptorHead descriptorTape)

variable {T e : ℕ}

/-- The return stack slots of the common bank. -/
abbrev ret (i : Fin 2) : Fin (CommonBank.count T) := Shared50RecursiveBank.returnSlot (u := K) i

theorem ret_val (i : Fin 2) : (ret (T := T) i).val = T + 36 + i.val := by
  simp [ret, Shared50RecursiveBank.returnSlot, K]; omega

/-- Where a tape of the forty-tape bank lives. -/
def slot40 (i : Fin 40) : Fin (CommonBank.count T + (40+e)) :=
  if h : 3 ≤ i.val ∧ i.val < 9 then Fin.castAdd _ (headerSlot ⟨i.val - 3, by omega⟩)
  else if i.val = 38 then Fin.castAdd _ (ret 0)
  else if i.val = 39 then Fin.castAdd _ (ret 1)
  else Fin.natAdd (CommonBank.count T) (Fin.castAdd e i)

/-- The placement of a call-bank program with counters `aux`. -/
def slot (aux : Fin e → Fin K) : Fin (40+e) → Fin (CommonBank.count T + (40+e)) :=
  Fin.addCases slot40 (fun j => Fin.castAdd _ (auxSlot (aux j)))

theorem count_val : CommonBank.count T = T + 38 := rfl

theorem slot40_val (i : Fin 40) : (slot40 (T := T) (e := e) i).val =
    if 3 ≤ i.val ∧ i.val < 9 then T + 1 + (i.val - 3) else if i.val = 38 then T + 36
    else if i.val = 39 then T + 37 else T + 38 + i.val := by
  unfold slot40
  split_ifs <;> simp [CommonBank.headerSlot_val, ret_val, count_val]

theorem slot_left_val (aux : Fin e → Fin K) (i : Fin 40) :
    (slot (T := T) aux (Fin.castAdd e i)).val =
      if 3 ≤ i.val ∧ i.val < 9 then T + 1 + (i.val - 3) else if i.val = 38 then T + 36
      else if i.val = 39 then T + 37 else T + 38 + i.val := by
  rw [slot, Fin.addCases_left, slot40_val]

theorem slot_right_val (aux : Fin e → Fin K) (j : Fin e) :
    (slot (T := T) aux (Fin.natAdd 40 j)).val = T + 12 + (aux j).val := by
  rw [slot, Fin.addCases_right, Fin.val_castAdd, CommonBank.auxSlot_val]

theorem slot_injective {aux : Fin e → Fin K} (ha : Function.Injective aux) :
    Function.Injective (slot (T := T) aux) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hK : K = 24 := rfl
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      rw [slot_left_val, slot_left_val] at hv
      have := i.isLt; have := j.isLt
      congr 1; apply Fin.ext
      split_ifs at hv <;> omega
    | right j =>
      rw [slot_left_val, slot_right_val] at hv
      have := (aux j).isLt
      split_ifs at hv <;> omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      rw [slot_left_val, slot_right_val] at hv
      have := (aux i).isLt
      split_ifs at hv <;> omega
    | right j =>
      rw [slot_right_val, slot_right_val] at hv
      exact congrArg _ (ha (Fin.ext (by omega)))

/-- A call-bank program placed on the common bank. -/
def place {q : ℕ} (M : Program (40+e) q prime) {aux : Fin e → Fin K} (ha : Function.Injective aux) :
    Graph.Block (CommonBank.count T) prime :=
  Embed.place (u := CommonBank.count T) M (slot aux) (slot_injective ha) (Nat.add_comm _ _)

theorem place_leading {q : ℕ} (M : Program (40+e) q prime) {aux : Fin e → Fin K}
    (ha : Function.Injective aux) : Blocks.Leading (place (T := T) M ha) := Blocks.place_leading _ _ _ _

/-- The counter tapes of the call bank. -/
def cnt (cs : Fin e → ℕ) : Tapes e prime := ⟨fun _ => 1, fun j => RadixZeroFill.encodedBinary (bits (cs j))⟩

/-- The forty-tape bank, slot by slot. -/
theorem bank40 (hs : Fin 6 → List Bool) (st : Tapes 2 prime) (i : Fin 40) :
    ((RecursiveChildCallSetup.bank hs st).head i, (RecursiveChildCallSetup.bank hs st).tape i) =
      if h : 3 ≤ i.val ∧ i.val < 9 then (1, RadixZeroFill.encodedBinary (hs ⟨i.val - 3, by omega⟩))
      else if i.val = 38 then (st.head 0, st.tape 0)
      else if i.val = 39 then (st.head 1, st.tape 1) else (0, fun _ => blank) := by
  have hv := Enter.view_split (q := prime) hs st (Enter.counters [] [] [] [])
  have hl : ∀ z : Fin 40, (RecursiveChildCallSetup.bank hs st).head z =
        (Enter.viewBank hs st (Enter.counters [] [] [] [])).head (Fin.castAdd 4 z) ∧
      (RecursiveChildCallSetup.bank hs st).tape z =
        (Enter.viewBank hs st (Enter.counters [] [] [] [])).tape (Fin.castAdd 4 z) := by
    intro z; simp [Enter.viewBank, Tapes.append]
  rw [(hl i).1, (hl i).2, hv]
  fin_cases i <;> first
    | (simp [Tapes.append, Headers.bank, Enter.base, Enter.rest, descriptorHead, descriptorTape]; done)
    | rfl

theorem bank40_st (hs : Fin 6 → List Bool) (st : Tapes 2 prime) (i : Fin 2) :
    (RecursiveChildCallSetup.bank hs st).head (Fin.natAdd 38 i) = st.head i ∧
      (RecursiveChildCallSetup.bank hs st).tape (Fin.natAdd 38 i) = st.tape i := by
  simp [RecursiveChildCallSetup.bank, Tapes.append]

theorem bank_ret (roles : Tapes T prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (c : Fin K → Option ℕ) (st : Tapes 2 prime) (i : Fin 2) :
    (bank roles hs f p node scalar c st).head (ret i) = st.head i ∧
      (bank roles hs f p node scalar c st).tape (ret i) = st.tape i := by
  fin_cases i <;> simp [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common,
    ret, Shared50RecursiveBank.returnSlot, Tapes.append]

/-- Two banks that differ only in headers and call stacks agree at every other tape. -/
theorem bank_other (roles : Tapes T prime) (hs hs' : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node scalar : Tapes 1 prime) (c : Fin K → Option ℕ) (st st' : Tapes 2 prime) (z : Fin (CommonBank.count T))
    (hh : ∀ j, headerSlot j ≠ z) (hr : ∀ i, ret i ≠ z) :
    (bank roles hs' f p node scalar c st').head z = (bank roles hs f p node scalar c st).head z ∧
      (bank roles hs' f p node scalar c st').tape z = (bank roles hs f p node scalar c st).tape z := by
  revert hh hr
  simp only [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common]
  induction z using Fin.addCases with
  | left z => intro _ _; simp [Tapes.append]
  | right z =>
    induction z using Fin.addCases with
    | left z =>
      change Fin (1+6) at z
      induction z using Fin.addCases with
      | left z => intro _ _; simp [Tapes.append]
      | right z => intro hh _; exact absurd rfl (hh z)
    | right z =>
      induction z using Fin.addCases with
      | left z => intro _ _; simp [Tapes.append]
      | right z => intro _ hr; exact absurd rfl (hr z)

variable {roles : Tapes T prime} {f : ℤ → Fin (prime+4)} {p : ℤ} {node scalar : Tapes 1 prime}
  {c : Fin K → Option ℕ}

theorem read40 (hs : Fin 6 → List Bool) (st : Tapes 2 prime) (aux : Fin e → Fin K) (i : Fin 40) :
    (raw (bank roles hs f p node scalar c st) (CommonBank.count T + (40+e))).head (slot aux (Fin.castAdd e i)) =
        (RecursiveChildCallSetup.bank hs st).head i ∧
      (raw (bank roles hs f p node scalar c st) (CommonBank.count T + (40+e))).tape (slot aux (Fin.castAdd e i)) =
        (RecursiveChildCallSetup.bank hs st).tape i := by
  have hb := bank40 hs st i
  simp only [slot, Fin.addCases_left, slot40] at hb ⊢
  split_ifs at hb ⊢ with h₁ h₂ h₃
  · rw [(Embed.raw_left _ _).1, (Embed.raw_left _ _).2, (CommonBank.bank_header ..).1,
      (CommonBank.bank_header ..).2]
    simp only [Prod.mk.injEq] at hb
    exact ⟨hb.1.symm, hb.2.symm⟩
  · rw [(Embed.raw_left _ _).1, (Embed.raw_left _ _).2, (bank_ret ..).1, (bank_ret ..).2]
    simp only [Prod.mk.injEq] at hb
    exact ⟨hb.1.symm, hb.2.symm⟩
  · rw [(Embed.raw_left _ _).1, (Embed.raw_left _ _).2, (bank_ret ..).1, (bank_ret ..).2]
    simp only [Prod.mk.injEq] at hb
    exact ⟨hb.1.symm, hb.2.symm⟩
  · rw [(Embed.raw_right _ _).1, (Embed.raw_right _ _).2]
    simp only [Prod.mk.injEq] at hb
    exact ⟨hb.1.symm, hb.2.symm⟩

/-- **A placed call-bank program**: its run from the call bank of `hs, st` to that of `hs', st'`,
with the same counters, is a run of the common bank that changes only the headers and the call
stacks. -/
theorem call_runs {q B : ℕ} {M : Program (40+e) q prime} {aux : Fin e → Fin K}
    (ha : Function.Injective aux) {cs : Fin e → ℕ} (hc : ∀ j, c (aux j) = some (cs j))
    {hs hs' : Fin 6 → List Bool} {st st' : Tapes 2 prime}
    (h : HoareTime M (fun w => w = (RecursiveChildCallSetup.bank hs st).append (cnt cs))
      (fun w => w = (RecursiveChildCallSetup.bank hs' st').append (cnt cs)) B) :
    Runs (place (T := T) M ha) (bank roles hs f p node scalar c st) (bank roles hs' f p node scalar c st') B := by
  refine Embed.place_runs h _ _ _ _ _ (fun i => ?_) (fun i => ?_) (fun z hz => ?_)
  · induction i using Fin.addCases with
    | left i =>
      rw [(read40 hs st aux i).1, (read40 hs st aux i).2]
      simp [Tapes.append]
    | right j =>
      simp only [slot, Fin.addCases_right, (Embed.raw_left _ _).1, (Embed.raw_left _ _).2,
        (CommonBank.bank_aux ..).1, (CommonBank.bank_aux ..).2, hc j]
      simp [Tapes.append, cnt, CommonBank.word, descriptorHead, descriptorTape]
  · induction i using Fin.addCases with
    | left i =>
      rw [(read40 hs' st' aux i).1, (read40 hs' st' aux i).2]
      simp [Tapes.append]
    | right j =>
      simp only [slot, Fin.addCases_right, (Embed.raw_left _ _).1, (Embed.raw_left _ _).2,
        (CommonBank.bank_aux ..).1, (CommonBank.bank_aux ..).2, hc j]
      simp [Tapes.append, cnt, CommonBank.word, descriptorHead, descriptorTape]
  · have hh : ∀ j, headerSlot j ≠ z := fun j he => by
      apply hz (Fin.castAdd e ⟨j.val + 3, by omega⟩)
      apply Fin.ext
      rw [slot_left_val, ← he, Fin.val_castAdd, CommonBank.headerSlot_val]
      have := j.isLt
      split_ifs with hc <;> simp at hc ⊢ <;> omega
    have hr : ∀ i, ret i ≠ z := fun i he => by
      fin_cases i
      · apply hz (Fin.castAdd e 38); apply Fin.ext
        rw [slot_left_val, ← he, Fin.val_castAdd, ret_val]; simp
      · apply hz (Fin.castAdd e 39); apply Fin.ext
        rw [slot_left_val, ← he, Fin.val_castAdd, ret_val]; simp
    exact bank_other roles hs hs' f p node scalar c st st' z hh hr

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.CallPlace
