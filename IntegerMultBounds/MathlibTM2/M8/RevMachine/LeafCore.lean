module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Family
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthOriginalTotalRun

/-!
# The leaf core: the stage-1 interchange on a one-atom view

A leaf of the reversed family is an ordinary interchange of one head atom with its partner tail
atom, a view `u` of width `b` (`Views`). Stage 1 supplies it: the fixed original-descriptor
machine `ArbitraryWidthOriginalTotalRun.program` transposes the bit array of any positive view,
of any width, read from six header tapes and one source tape, and restores its private tapes.

The core (`core io`) places that machine on the common bank: its six headers on the bank's
headers, its source on the I/O role `io`, and everything else on private blank tapes (`slot`).
The role streams are good (`Good io`) when the view is positive and the I/O role holds the source
word of a bit array at head zero. `leafCore97`: the core runs from good role streams to good role
streams, with the transposed array of the leaf view on `io` (`core_runs`), within the stage-1
bound `C V max(1, b)^τ` (`coreCost`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafCore

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open SharedBankStageInput (raw)
open SharedPlacementAlphabet (setTape)
open RecursiveInterchangeLayout (Descriptor volume)
open GraphContract (Runs)
open CommonBank (bank)
open Routines (hdr)
open Family (count LeafCore)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)

variable [M8.Machine.Net] {T : ℕ}

/-! ### Appending blank tapes -/

omit [M8.Machine.Net] in
theorem raw_self {k a : ℕ} (x : Tapes k a) : raw x k = x := by
  cases x
  apply congrArg₂ Tapes.mk <;> funext i <;> simp [i.isLt]

omit [M8.Machine.Net] in
theorem raw_append {k n m a : ℕ} (x : Tapes k a) (hk : k ≤ n) (e : Tapes m a)
    (hh : ∀ i, e.head i = 0) (ht : ∀ i, e.tape i = fun _ => blank) :
    (raw x n).append e = raw x (n+m) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i => simp [raw]
  | right i =>
    have : ¬ n + i.val < k := by omega
    simp [raw, this, hh, ht]

/-- The stage-1 machine's input bank is its caller followed by blank tapes. -/
theorem input_eq {t : ℕ} (caller : Tapes t prime) :
    M8.Machine.ArbitraryWidthOriginalTotalRun.input caller =
      raw caller (M8.Machine.ArbitraryWidthOriginalZeroBranch.count t) := by
  conv_lhs => rw [← raw_self caller]
  simp only [M8.Machine.ArbitraryWidthOriginalTotalRun.input, M8.Machine.ArbitraryWidthOriginalZeroBranch.input,
    M8.Machine.ArbitraryWidthHighPreparedRun.input, M8.Machine.ArbitraryWidthHighCommonPrepare.input,
    M8.Machine.ArbitraryWidthHighExecutionInitialize.input, M8.Machine.ArbitraryWidthHighBranchPrepare.input]
  rw [raw_append _ (by omega) _ (fun _ => rfl) (fun _ => rfl), raw_append _ (by omega) _ (fun _ => rfl) (fun _ => rfl),
    raw_append _ (by omega) _ (fun _ => rfl) (fun _ => rfl), raw_append _ (by omega) _ (fun _ => rfl) (fun _ => rfl),
    raw_append _ (by omega) _ (fun _ => rfl) (fun _ => rfl), raw_append _ (by omega) _ (fun _ => rfl) (fun _ => rfl),
    raw_append _ (by omega) _ (fun _ => rfl) (fun _ => rfl), raw_append _ (by omega) _ (fun _ => rfl) (fun _ => rfl),
    raw_append _ (by omega) _ (fun _ => rfl) (fun _ => rfl)]

/-! ### The placement -/

/-- The I/O role on the common bank. -/
def roleSlot (io : Fin T) : Fin (count T) := Fin.castAdd _ io

/-- The six headers and the I/O role: the caller bank of the stage-1 machine. -/
def sel (io : Fin T) : Fin 7 → Fin (count T) := Fin.lastCases (roleSlot io) CommonBank.headerSlot

omit [M8.Machine.Net] in
theorem sel_injective (io : Fin T) : Function.Injective (sel io) := by
  have hr : (roleSlot io).val < T := io.isLt
  intro i j h
  have hv := congrArg Fin.val h
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [sel, Fin.lastCases_last, Fin.lastCases_castSucc, CommonBank.headerSlot_val] at hv
  · rfl
  · omega
  · omega
  · exact congrArg _ (Fin.ext (by omega))

/-- The caller bank read off the common bank. -/
def caller (io : Fin T) (x : Tapes (count T) prime) : Tapes 7 prime :=
  ⟨fun i => x.head (sel io i), fun i => x.tape (sel io i)⟩

abbrev small : ℕ := M8.Machine.ArbitraryWidthOriginalZeroBranch.count 7

/-- The caller's tapes go to their common slots, the stage-1 private tapes to private tapes. -/
def slot (io : Fin T) (i : Fin small) : Fin (count T + small) :=
  if h : i.val < 7 then Fin.castAdd small (sel io ⟨i.val, h⟩) else Fin.natAdd (count T) i

theorem slot_injective (io : Fin T) : Function.Injective (slot io) := by
  intro i j h
  unfold slot at h
  split_ifs at h with hi hj hj
  · have := congrArg Fin.val (sel_injective io (Fin.castAdd_inj.mp h))
    exact Fin.ext (by simpa using this)
  · have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  · have := congrArg Fin.val h; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  · exact Fin.ext (by have := congrArg Fin.val h; simpa using this)

/-- The stage-1 machine. -/
def stage1 := M8.Machine.ArbitraryWidthOriginalTotalRun.program (t := 7) Fin.castSucc (Fin.last 6)

/-- **The leaf core.** -/
def core (io : Fin T) : Graph.Block (count T) prime :=
  Embed.place stage1 (slot io) (slot_injective io) (Nat.add_comm small (count T))

/-! ### The common bank at the caller slots -/

variable (roles : Tapes T prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
  (node scalar : Tapes 1 prime) (c : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime)

omit [M8.Machine.Net] in
theorem bank_role (j : Fin T) :
    (bank roles hs f p node scalar c st).head (roleSlot j) = roles.head j ∧
      (bank roles hs f p node scalar c st).tape (roleSlot j) = roles.tape j := by
  simp [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common,
    roleSlot, Tapes.append]

omit [M8.Machine.Net] in
/-- Changing one role stream changes the common bank at that role only. -/
theorem bank_set (io : Fin T) (w : ℤ → Fin (prime+4)) (z : Fin (count T)) (hz : z ≠ roleSlot io) :
    (bank (setTape roles io w 0) hs f p node scalar c st).head z = (bank roles hs f p node scalar c st).head z ∧
      (bank (setTape roles io w 0) hs f p node scalar c st).tape z = (bank roles hs f p node scalar c st).tape z := by
  revert hz
  induction z using Fin.addCases with
  | left j =>
    intro hz
    have hj : j ≠ io := fun h => hz (by rw [h]; rfl)
    simp [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common,
      Tapes.append, setTape, hj]
  | right j =>
    intro _
    simp [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common,
      Tapes.append]

/-! ### Source words of equal volumes -/

omit [M8.Machine.Net] in
theorem pair_cast {n m : ℕ} (h : n = m) (a : Fin m → Fin 4) :
    (FlatRepeatedControlArray.pair (radix := prime) (fun i : Fin n => a (Fin.cast h i))).tape 0 =
      (FlatRepeatedControlArray.pair (radix := prime) a).tape 0 := by
  subst h; rfl

omit [M8.Machine.Net] in
theorem sourceWord_cast {u v : Descriptor} (h : volume prime u = volume prime v)
    (x : Fin (volume prime v) → ZMod 2) :
    sourceWord (v := u) (fun i => x (Fin.cast h i)) = sourceWord (v := v) x := by
  unfold sourceWord RecursiveShiftRoleBank.source Shared50RecursiveNodeSemantics.encoded
  exact pair_cast h (fun i => SparseRoleCircuit.encode (x i))

/-! ### The leaf core's run -/

/-- Good role streams: a positive view, and the source word of a bit array on the I/O role. -/
def Good (io : Fin T) (v : Descriptor) (roles : Tapes T prime) : Prop :=
  v.Positive ∧ roles.head io = 0 ∧ ∃ x : Fin (volume prime v) → ZMod 2, roles.tape io = sourceWord x

omit [M8.Machine.Net] in
theorem positive_of_volume {u : Descriptor} (h : 0 < volume prime u) : u.Positive := by
  unfold volume at h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> apply Nat.pos_of_ne_zero <;> intro h0 <;> simp [h0] at h

theorem seven_le : 7 ≤ small := by
  simp only [small, M8.Machine.ArbitraryWidthOriginalZeroBranch.count,
    M8.Machine.ArbitraryWidthOriginalZeroBranch.highCount]
  omega

/-- The common bank at the placed slots is the stage-1 input of its caller bank. -/
theorem slot_read (io : Fin T) (Z : Tapes (count T) prime) (i : Fin small) :
    (raw Z (count T + small)).head (slot io i) = (raw (caller io Z) small).head i ∧
      (raw Z (count T + small)).tape (slot io i) = (raw (caller io Z) small).tape i := by
  unfold slot
  split_ifs with h
  · rw [(Embed.raw_left _ _).1, (Embed.raw_left _ _).2]
    simp [raw, h, caller]
  · rw [(Embed.raw_right _ _).1, (Embed.raw_right _ _).2]
    simp [raw, h]

omit [M8.Machine.Net] in
theorem caller_set (io : Fin T) (w : ℤ → Fin (prime+4)) :
    caller io (bank (setTape roles io w 0) hs f p node scalar c st) =
      setTape (caller io (bank roles hs f p node scalar c st)) (Fin.last 6) w 0 := by
  have hY := bank_role (setTape roles io w 0) hs f p node scalar c st io
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.lastCases with
  | last =>
    simp only [caller, sel, Fin.lastCases_last]
    first | (rw [hY.1]; simp [setTape]) | (rw [hY.2]; simp [setTape])
  | cast j =>
    have hne : CommonBank.headerSlot j ≠ roleSlot io := by
      intro h
      have := congrArg Fin.val h
      rw [CommonBank.headerSlot_val] at this
      have : (roleSlot io).val < T := io.isLt
      omega
    have hb := bank_set roles hs f p node scalar c st io w _ hne
    simp only [caller, sel, Fin.lastCases_castSucc]
    first | rw [hb.1] | rw [hb.2]
    rw [Function.update_of_ne (Fin.castSucc_ne_last j)]
    simp only [Fin.lastCases_castSucc]

/-- **The leaf core's run.** On a positive view `u` with its headers, the core transposes the bit
array on the I/O role and keeps every other tape, at the stage-1 machine's cost. -/
theorem core_runs (io : Fin T) {u : Descriptor} (hpos : u.Positive) (x : Fin (volume prime u) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x) :
    Runs (core io) (bank roles (hdr u) f p node scalar c st)
      (bank (setTape roles io (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd u.rows) x)) 0)
        (hdr u) f p node scalar c st)
      (M8.Machine.ArbitraryWidthOriginalTotalRun.cost u (hdr u)) := by
  set X := bank roles (hdr u) f p node scalar c st
  set w := sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd u.rows) x)
  have hX := bank_role roles (hdr u) f p node scalar c st io
  have hrun := M8.Machine.ArbitraryWidthOriginalTotalRun.runs (caller io X) Fin.castSucc (Fin.last 6) u (hdr u)
    hpos (Routines.hdr_headers u)
    (fun i => by simp [caller, sel, X, CommonBank.bank_header, CounterDimensions.descriptorTape])
    (fun i => by simp [caller, sel, X, CommonBank.bank_header, CounterDimensions.descriptorHead])
    x (by simp only [caller, sel, Fin.lastCases_last]; rw [hX.2, hx])
    (by simp only [caller, sel, Fin.lastCases_last]; rw [hX.1, hh])
  rw [input_eq, input_eq, ← caller_set] at hrun
  refine Embed.place_runs hrun (slot io) (slot_injective io) (Nat.add_comm small (count T)) _ _
    (fun i => slot_read io _ i) (fun i => slot_read io _ i) (fun j hj => ?_)
  have hne : j ≠ roleSlot io := by
    rintro rfl
    refine hj ⟨6, lt_of_lt_of_le (by decide) seven_le⟩ ?_
    simp only [slot, show (6 : ℕ) < 7 by decide, dite_true]
    rfl
  exact bank_set roles (hdr u) f p node scalar c st io w j hne

/-- The stage-1 machine's constant (`ArbitraryWidthOriginalTotalRun.uniform_bound`). -/
def C : ℝ := Classical.choose M8.Machine.ArbitraryWidthOriginalTotalRun.uniform_bound

/-- The leaf core's cost on volume `V` and atom width `b`. -/
def coreCost (V b : ℕ) : ℕ := ⌊C * V * ((max 1 b : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau⌋₊

theorem cost_le {u : Descriptor} (hpos : u.Positive) :
    M8.Machine.ArbitraryWidthOriginalTotalRun.cost u (hdr u) ≤ coreCost (volume prime u) u.width :=
  Nat.le_floor ((Classical.choose_spec M8.Machine.ArbitraryWidthOriginalTotalRun.uniform_bound).2 u (hdr u)
    hpos (Routines.hdr_headers u))

/-- **The leaf core of the stage-2 family**: the stage-1 interchange on the I/O role. -/
theorem leafCore97 (io : Fin T) : LeafCore (core io) (Good io) coreCost := by
  refine ⟨Blocks.place_leading _ _ _ _, ?_⟩
  intro v u b _ hub hvol hs hhs roles f p node scalar c st hg
  obtain ⟨hpos, hh, x, hx⟩ := hg
  subst hhs hub
  have hupos : u.Positive := positive_of_volume
    (hvol ▸ RecursiveAffinePrepare.volume_positive Networks.Shared50ModularControl.prime_prime.two_le v hpos)
  set y : Fin (volume prime u) → ZMod 2 := fun i => x (Fin.cast hvol i)
  have hy : roles.tape io = sourceWord y := hx.trans (sourceWord_cast hvol x).symm
  set z := Shared50RecursiveNodeRows.transpose (one_dvd u.rows) y
  refine ⟨setTape roles io (sourceWord z) 0, ⟨hpos, by simp [setTape], fun i => z (Fin.cast hvol.symm i), ?_⟩,
    Blocks.runs_mono (core_runs roles f p node scalar c st io hupos y hh hy) ?_⟩
  · simp only [setTape, Function.update_self]
    rw [← sourceWord_cast hvol]
    congr
  · rw [← hvol]
    exact cost_le hupos

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafCore
