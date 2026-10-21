module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodePark
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Counters
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.CallPlace
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Prepare

/-!
# A block call of the reversed node

A node holds its role data on the role view `v` of its `m f` atoms, with the node's counters
(`nodeC`: the segment counters `0..8`, the cutoff and the constant one). A call of rank `r` on
wire `w` enters (`enterB`): it parks every other wire and moves `w` to `io`, writes the child's
offset `(m - r) f`, count `r f` and rest `0`, saves the headers and the return code and installs
the child's headers (`Enter.enterView`), and erases the offsets. The child is the sub-view of
`r f` atoms with the child's role tapes and the call's counters (`enter_runs`).

Recovery (`recoverB`) restores the parent headers from the descriptor stack, recomputes the
node's counters from the width header, and moves the child's output back to `w` and unparks the
other wires (`recover_runs`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeCall

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs)
open CommonBank (bank K)
open Blocks (seqB seq_runs runs_mono Leading)
open Routines (hdr)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRoleSerialization (roles)
open RecursiveCallBank (role role_injective rolePart controlSlot)
open NodeBank (tapes io wireSlot)
open NodePark (parked childRoles)

variable (N : RevNetwork)

/-! ### Counters -/

/-- The node's counters, with `f` atoms per coordinate. -/
def nodeC (b f : ℕ) : Fin K → Option ℕ :=
  Function.update (Function.update (Prepare.rest b N.width) 5 (some f)) 8 (some (f - 1))

/-- The counters of a call of rank `r`: offset, count and rest of the child. -/
def callC (b r f : ℕ) : Fin K → Option ℕ :=
  Function.update (Function.update (Function.update (Prepare.rest b N.width) 12 (some ((N.width - r) * f)))
    13 (some (r * f))) 14 (some 0)

/-! ### The blocks -/

/-- Park every wire but `w` and move `w` to `io`. -/
def payloadB (w : N.World ⊕ N.Temp) : Graph.Block (CommonBank.count (tapes N)) prime :=
  RecursiveCallProtocol.payloadEntry (u := 1+(1+K)) (parked N w) (wireSlot N w) (io N) (NodeBank.wireSlot_ne_io N w)

/-- Move `io` back to `w` and unpark every other wire. -/
def recoverPayB (w : N.World ⊕ N.Temp) : Graph.Block (CommonBank.count (tapes N)) prime :=
  RecursiveCallProtocol.recover (u := 1+(1+K)) (parked N w) (wireSlot N w) (io N) (NodeBank.wireSlot_ne_io N w)

/-- The call's counters from the node's. -/
def countersB (r : ℕ) : Graph.Block (CommonBank.count (tapes N)) prime :=
  seqB (Counters.zero 13) (seqB (Counters.advs 13 5 (by decide) (r - 1)) (seqB (Counters.zero 12)
    (seqB (Counters.advs 12 5 (by decide) (N.width - r - 1)) (seqB (Counters.zero 14)
      (seqB (Counters.erase 5) (Counters.erase 8))))))

/-- The counters of the child view: width, offset, count, rest. -/
def viewAux : Fin 4 → Fin K := ![0, 12, 13, 14]

theorem viewAux_injective : Function.Injective viewAux := by decide

/-- Save the headers and the return code and install the child's headers. -/
def viewB {k : ℕ} (code : FiniteReturnStack.Code k) : Graph.Block (CommonBank.count (tapes N)) prime :=
  CallPlace.place (Enter.enterView Networks.Shared50ModularControl.prime_prime.two_le code) viewAux_injective

/-- Erase the child view's offset, count and rest. -/
def eraseB : Graph.Block (CommonBank.count (tapes N)) prime :=
  seqB (Counters.erase 12) (seqB (Counters.erase 13) (Counters.erase 14))

/-- **The entry of a call** of rank `r` on wire `w`. -/
def enterB (w : N.World ⊕ N.Temp) (r : ℕ) {k : ℕ} (code : FiniteReturnStack.Code k) :
    Graph.Block (CommonBank.count (tapes N)) prime :=
  seqB (payloadB N w) (seqB (countersB N r) (seqB (viewB N code) (eraseB N)))

/-- Restore the parent headers. -/
def restoreB : Graph.Block (CommonBank.count (tapes N)) prime :=
  CallPlace.place (e := 0) (RecursiveChildCallReturn.program (q := prime)) (aux := Fin.elim0)
    (fun i => i.elim0)

/-- The node's counters from the call's. -/
def recCountersB : Graph.Block (CommonBank.count (tapes N)) prime :=
  seqB Prepare.atoms (seqB Prepare.divide (seqB (Counters.diff 5 15 8 (by decide) (by decide) (by decide))
    (seqB (Counters.erase 9) (Counters.erase 11))))

/-- **The recovery of a call** on wire `w`. -/
def recoverB (w : N.World ⊕ N.Temp) : Graph.Block (CommonBank.count (tapes N)) prime :=
  seqB (restoreB N) (seqB (recCountersB N) (recoverPayB N w))

/-! ### Runs -/

theorem payloadB_leading (w : N.World ⊕ N.Temp) : Leading (payloadB N w) := fun _ => rfl
theorem recoverPayB_leading (w : N.World ⊕ N.Temp) : Leading (recoverPayB N w) := fun _ => rfl

variable {N}
variable {rr : Tapes (tapes N) prime} {hs : Fin 6 → List Bool} {fs : ℤ → Fin (prime+4)} {p : ℤ}
  {node scalar : Tapes 1 prime} {st : Tapes 2 prime}

/-- The cost of the call's counters. -/
def countersCost (r f m : ℕ) : ℕ :=
  6 + Counters.advsCost 0 f (r - 1) + 6 + Counters.advsCost 0 f (m - r - 1) + 6 +
    (2*(bits f).length+4) + (2*(bits (f-1)).length+4) + 6

theorem counters_runs {b f r : ℕ} (hr : 1 ≤ r) (hrm : r < N.width) :
    Runs (countersB N r) (bank rr hs fs p node scalar (nodeC N b f) st)
      (bank rr hs fs p node scalar (callC N b r f) st) (countersCost r f N.width) := by
  set c₀ := nodeC N b f
  have h₁ := Counters.zero_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₀) (j := 13) (by simp [c₀, nodeC, Prepare.rest])
  set c₁ := Function.update c₀ 13 (some 0)
  have h₂ := Counters.advs_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₁) (x := 13) (k := 5) (by decide) (X := 0) (Y := f) (by simp [c₁])
    (by simp [c₁, c₀, nodeC]) (r - 1)
  set c₂ := Function.update c₁ 13 (some (0 + (r - 1 + 1) * f))
  have h₃ := Counters.zero_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₂) (j := 12) (by simp [c₂, c₁, c₀, nodeC, Prepare.rest])
  set c₃ := Function.update c₂ 12 (some 0)
  have h₄ := Counters.advs_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₃) (x := 12) (k := 5) (by decide) (X := 0) (Y := f) (by simp [c₃])
    (by simp [c₃, c₂, c₁, c₀, nodeC]) (N.width - r - 1)
  set c₄ := Function.update c₃ 12 (some (0 + (N.width - r - 1 + 1) * f))
  have h₅ := Counters.zero_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₄) (j := 14) (by simp [c₄, c₃, c₂, c₁, c₀, nodeC, Prepare.rest])
  set c₅ := Function.update c₄ 14 (some 0)
  have h₆ := Counters.erase_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₅) (j := 5) (x := f) (by simp [c₅, c₄, c₃, c₂, c₁, c₀, nodeC])
  set c₆ := Function.update c₅ 5 none
  have h₇ := Counters.erase_runs (roles := rr) (hs := hs) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₆) (j := 8) (x := f - 1) (by simp [c₆, c₅, c₄, c₃, c₂, c₁, c₀, nodeC])
  have he : Function.update c₆ 8 none = callC N b r f := by
    have e1 : 0 + (r - 1 + 1) * f = r * f := by rw [Nat.sub_add_cancel hr]; ring
    have e2 : 0 + (N.width - r - 1 + 1) * f = (N.width - r) * f := by
      rw [Nat.sub_add_cancel (by omega)]; ring
    funext j
    fin_cases j <;> simp [c₆, c₅, c₄, c₃, c₂, c₁, c₀, nodeC, callC, Prepare.rest, Function.update, e1, e2, Fin.ext_iff, CommonBank.K]
  rw [he] at h₇
  have L₆ := seq_runs (Counters.blk_leading _ _ _) (Counters.blk_leading _ _ _) h₆ h₇
  have L₅ := seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₅ L₆
  have L₄ := seq_runs (Counters.advs_leading _ _ _ _) (Blocks.seq_leading _ _) h₄ L₅
  have L₃ := seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₃ L₄
  have L₂ := seq_runs (Counters.advs_leading _ _ _ _) (Blocks.seq_leading _ _) h₂ L₃
  have L₁ := seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₁ L₂
  exact runs_mono L₁ (by unfold countersCost; omega)

/-! ### Entry -/

theorem width_le_volume (v : Descriptor) (hp : v.Positive) : v.width ≤ volume prime v := by
  have h1 : v.width < prime ^ v.width := Nat.lt_pow_self Networks.Shared50ModularControl.prime_prime.one_lt
  obtain ⟨hA, hR, hB, hC, hE⟩ := hp
  have h2 : prime ^ v.width ≤ volume prime v := by
    unfold volume
    have hq : 0 < prime ^ v.width := pow_pos Networks.Shared50ModularControl.prime_prime.pos _
    calc prime ^ v.width ≤ v.beforeRows * v.rows * v.beforeH * prime ^ v.width :=
          Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos hA hR) hB)
      _ ≤ v.beforeRows * v.rows * v.beforeH * prime ^ v.width * v.between * prime ^ v.width * v.afterD := by
          apply Nat.le_mul_of_pos_right _ hE |>.trans' ?_
          apply Nat.le_mul_of_pos_right _ hq |>.trans' ?_
          exact Nat.le_mul_of_pos_right _ hC
  omega

/-- The child view of a call of rank `r`. -/
def childView (b f r : ℕ) (v : Descriptor) : Descriptor :=
  RevMachine.sub prime b (N.width * f) ((N.width - r) * f) (r * f) v

/-- The cost of a call's entry. -/
def enterCost (w : N.World ⊕ N.Temp) (f r k : ℕ) (V : ℕ) : ℕ :=
  (88 * (parked N w).length + 51883) * V + countersCost r f N.width + (1700 * V + k) +
    ((2*(bits ((N.width - r) * f)).length+4) + (2*(bits (r * f)).length+4) + (2*(bits 0).length+4) + 2) + 3

theorem counters_eq (b s c e : ℕ) :
    Enter.counters (q := prime) (bits b) (bits s) (bits c) (bits e) = CallPlace.cnt ![b, s, c, e] := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext j; fin_cases j <;> rfl

/-- **Entering a call** of rank `r` on wire `w`. -/
theorem enter_runs (w : N.World ⊕ N.Temp) {k : ℕ} (code : FiniteReturnStack.Code k) {v : Descriptor}
    {b f r : ℕ} (hpos : v.Positive) (hb : 0 < b) (hf : 0 < f) (hw : v.width = (N.width * f) * b) (hr : 1 ≤ r)
    (hrm : r < N.width) (data : RecursiveMixedSchedule.Data (tapes N) v) (hio : data (io N) = fun _ => blank) :
    Runs (enterB N w r code) (bank (roles data) (hdr v) fs p node scalar (nodeC N b f) st)
      (bank (childRoles N (RecursiveShiftRoleBank.source (data (wireSlot N w)))) (hdr (childView (N := N) b f r v))
        ((RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) (volume prime v)
          (bank (roles data) (hdr v) fs p node scalar (nodeC N b f) st)).tape (controlSlot 2))
        ((RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) (volume prime v)
          (bank (roles data) (hdr v) fs p node scalar (nodeC N b f) st)).head (controlSlot 2))
        node scalar (Prepare.rest b N.width) (RecursiveChildCallSetup.savedStacks (hdr v) st code))
      (enterCost (N := N) w f r k (volume prime v)) := by
  set E := RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) (volume prime v)
    (bank (roles data) (hdr v) fs p node scalar (nodeC N b f) st)
  have hV := RecursiveAffinePrepare.volume_positive Networks.Shared50ModularControl.prime_prime.two_le v hpos
  -- parking
  have h₁ := RecursiveCallProtocol.payload_entry_hoare (u := 1+(1+K)) (parked N w) (NodePark.parked_nodup N w)
    (wireSlot N w) (io N) (NodeBank.wireSlot_ne_io N w) (NodePark.active_not_parked N w) (NodePark.io_not_parked N w)
    v (roles data) (hdr v) fs p (node.append (scalar.append (CommonBank.counters (nodeC N b f)))) st
    (Routines.hdr_headers v) hpos (fun z _ => NodePark.roles_supported N data z) (NodePark.roles_supported N data _)
    ⟨rfl, by change RecursiveShiftRoleBank.source (data (io N)) = _; rw [hio]; exact RecursiveRowsSerialization.source_blank v⟩
  have hE := NodePark.entered_eq N (u := 1+(1+K)) w (volume prime v) (roles data) (hdr v) fs p
    (node.append (scalar.append (CommonBank.counters (nodeC N b f)))) st
  have h₁' : Runs (payloadB N w) (bank (roles data) (hdr v) fs p node scalar (nodeC N b f) st)
      (bank (childRoles N (RecursiveShiftRoleBank.source (data (wireSlot N w)))) (hdr v) (E.tape (controlSlot 2))
        (E.head (controlSlot 2)) node scalar (nodeC N b f) st) ((88 * (parked N w).length + 51883) * volume prime v) := by
    have : E = bank (childRoles N (RecursiveShiftRoleBank.source (data (wireSlot N w)))) (hdr v) (E.tape (controlSlot 2))
        (E.head (controlSlot 2)) node scalar (nodeC N b f) st := hE
    rw [← this]
    exact h₁
  -- counters
  have h₂ := counters_runs (rr := childRoles N (RecursiveShiftRoleBank.source (data (wireSlot N w))))
    (hs := hdr v) (fs := E.tape (controlSlot 2)) (p := E.head (controlSlot 2)) (node := node) (scalar := scalar)
    (st := st) (N := N) (b := b) (f := f) hr hrm
  -- view
  have hsum : (N.width - r) * f + r * f = N.width * f := by rw [← Nat.add_mul, Nat.sub_add_cancel hrm.le]
  have hsc : (N.width - r) * f + r * f ≤ N.width * f := hsum.le
  have he : 0 = N.width * f - (N.width - r) * f - r * f := by omega
  have hwv : v.width ≤ volume prime v := width_le_volume v hpos
  have hbw : b ≤ v.width := by rw [hw]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hf)
  have hmw : N.width * f ≤ v.width := by rw [hw]; exact Nat.le_mul_of_pos_right _ hb
  have hview := Enter.enters_volume (q := prime) Networks.Shared50ModularControl.prime_prime.two_le code st
    (Routines.hdr_headers v) hpos hb (n := N.width * f) (s := (N.width - r) * f) (c := r * f) (e := 0) hw hsc he
    (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
    (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_canonical _)
    (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
    (FlatCoordinateSchedule.bits_canonical _) ⟨by omega, by omega, by omega, by omega⟩
  have hch : Headers.childHeaders (q := prime) v (hdr v) b ((N.width - r) * f) (r * f) 0 = hdr (childView (N := N) b f r v) :=
    Routines.hdr_eq (Headers.child_headers (Routines.hdr_headers v) he)
  rw [hch, counters_eq] at hview
  have h₃ := CallPlace.call_runs (T := tapes N) (roles := childRoles N (RecursiveShiftRoleBank.source (data (wireSlot N w))))
    (f := E.tape (controlSlot 2)) (p := E.head (controlSlot 2)) (node := node) (scalar := scalar)
    (c := callC N b r f) viewAux_injective (cs := ![b, (N.width - r) * f, r * f, 0])
    (by intro j; fin_cases j <;> simp [viewAux, callC, Prepare.rest, Function.update, Fin.ext_iff, CommonBank.K])
    hview
  have h₄₁ := Counters.erase_runs (roles := childRoles N (RecursiveShiftRoleBank.source (data (wireSlot N w))))
    (hs := hdr (childView (N := N) b f r v)) (f := E.tape (controlSlot 2)) (p := E.head (controlSlot 2))
    (node := node) (scalar := scalar) (st := RecursiveChildCallSetup.savedStacks (hdr v) st code)
    (c := callC N b r f) (j := 12) (x := (N.width - r) * f) (by simp [callC])
  have h₄₂ := Counters.erase_runs (roles := childRoles N (RecursiveShiftRoleBank.source (data (wireSlot N w))))
    (hs := hdr (childView (N := N) b f r v)) (f := E.tape (controlSlot 2)) (p := E.head (controlSlot 2))
    (node := node) (scalar := scalar) (st := RecursiveChildCallSetup.savedStacks (hdr v) st code)
    (c := Function.update (callC N b r f) 12 none) (j := 13) (x := r * f) (by simp [callC])
  have h₄₃ := Counters.erase_runs (roles := childRoles N (RecursiveShiftRoleBank.source (data (wireSlot N w))))
    (hs := hdr (childView (N := N) b f r v)) (f := E.tape (controlSlot 2)) (p := E.head (controlSlot 2))
    (node := node) (scalar := scalar) (st := RecursiveChildCallSetup.savedStacks (hdr v) st code)
    (c := Function.update (Function.update (callC N b r f) 12 none) 13 none) (j := 14) (x := 0) (by simp [callC])
  have hrest : Function.update (Function.update (Function.update (callC N b r f) 12 none) 13 none) 14 none =
      Prepare.rest b N.width := by
    funext j; fin_cases j <;> simp [callC, Prepare.rest, Function.update, Fin.ext_iff, CommonBank.K]
  rw [hrest] at h₄₃
  have L₄ := seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₄₁
    (seq_runs (Counters.blk_leading _ _ _) (Counters.blk_leading _ _ _) h₄₂ h₄₃)
  have L₃ := seq_runs (CallPlace.place_leading _ _) (Blocks.seq_leading _ _) h₃ L₄
  have L₂ := seq_runs (Blocks.seq_leading _ _) (Blocks.seq_leading _ _) h₂ L₃
  have L₁ := seq_runs (payloadB_leading N w) (Blocks.seq_leading _ _) h₁' L₂
  exact runs_mono L₁ (by unfold enterCost; omega)

/-! ### Recovery -/

/-- The empty return code. -/
def code0 : FiniteReturnStack.Code 0 := fun i => i.elim0

theorem append_zero {n a : ℕ} (x : Tapes n a) (y : Tapes 0 a) : x.append y = x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i => exact Fin.addCases_left (motive := fun _ => _) i
  | right i => exact i.elim0

theorem pending_zero (st : Tapes 2 prime) : RecursiveChildCallReturn.pending st code0 = st := by
  unfold RecursiveChildCallReturn.pending FiniteReturnStackAt.pushed
  rw [FiniteReturnStack.prefix_zero, Nat.cast_zero, add_zero, SharedPlacementAlphabet.setTape_self]

/-- The cost of the node's counters after a call. -/
def recCountersCost (b f m : ℕ) : ℕ :=
  (BinaryDescriptorDivMod.linearConstant (bits b) * (m * f * b + 1) + 2 * b + 6) +
    BinaryDescriptorDivMod.linearConstant (bits m) * (m * f + 1) + (6 * f + 27) +
    (2*(bits (m * f)).length+4) + (2*(bits 0).length+4) + 4

theorem recCounters_runs {v : Descriptor} {b f : ℕ} (hb : 0 < b) (hf : 0 < f) (hw : v.width = (N.width * f) * b) :
    Runs (recCountersB N) (bank rr (hdr v) fs p node scalar (Prepare.rest b N.width) st)
      (bank rr (hdr v) fs p node scalar (nodeC N b f) st) (recCountersCost b f N.width) := by
  have hm : 0 < N.width := by have := N.two_le_width; omega
  obtain ⟨B₁, hB₁, h₁⟩ := Prepare.atoms_runs (roles := rr) (f := fs) (p := p) (node := node)
    (scalar := scalar) (st := st) (c := Prepare.rest b N.width) (hs := hdr v) hb
    (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_canonical _) rfl rfl
  have hwb : (RecursiveDimensionBank.values v 3) / b = N.width * f := by
    change v.width / b = _; rw [hw, Nat.mul_div_cancel _ hb]
  rw [hwb] at h₁
  obtain ⟨B₂, hB₂, h₂⟩ := Prepare.divide_runs (roles := rr) (f := fs) (p := p) (node := node)
    (scalar := scalar) (st := st) (hs := hdr v) (c := Function.update (Prepare.rest b N.width) 9 (some (N.width * f)))
    (n := N.width * f) (m := N.width) hm (by simp) (by simp [Prepare.rest]) (by simp [Prepare.rest]) (by simp [Prepare.rest])
  rw [Nat.mul_div_cancel_left _ hm, Nat.mul_mod_right] at h₂
  set c₂ := Function.update (Function.update (Function.update (Prepare.rest b N.width) 9 (some (N.width * f))) 5
    (some f)) 11 (some 0)
  have h₃ := Counters.diff_runs (roles := rr) (hs := hdr v) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := c₂) (x := 5) (y := 15) (o := 8) (by decide) (by decide) (by decide) (X := f) (Y := 1) hf
    (by simp [c₂]) (by simp [c₂, Prepare.rest]) (by simp [c₂, Prepare.rest])
  have h₄ := Counters.erase_runs (roles := rr) (hs := hdr v) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := Function.update c₂ 8 (some (f - 1))) (j := 9) (x := N.width * f) (by simp [c₂])
  have h₅ := Counters.erase_runs (roles := rr) (hs := hdr v) (f := fs) (p := p) (node := node) (scalar := scalar)
    (st := st) (c := Function.update (Function.update c₂ 8 (some (f - 1))) 9 none) (j := 11) (x := 0) (by simp [c₂])
  have he : Function.update (Function.update (Function.update c₂ 8 (some (f - 1))) 9 none) 11 none = nodeC N b f := by
    funext j; fin_cases j <;> simp [c₂, nodeC, Prepare.rest, Function.update, Fin.ext_iff, CommonBank.K]
  rw [he] at h₅
  have hw' : (RecursiveDimensionBank.values v 3) = N.width * f * b := hw
  rw [hw'] at hB₁
  have L₄ := seq_runs (Counters.blk_leading _ _ _) (Counters.blk_leading _ _ _) h₄ h₅
  have L₃ := seq_runs (Counters.blk_leading _ _ _) (Blocks.seq_leading _ _) h₃ L₄
  have L₂ := seq_runs (fun _ => rfl) (Blocks.seq_leading _ _) h₂ L₃
  have L₁ := seq_runs (fun _ => rfl) (Blocks.seq_leading _ _) h₁ L₂
  exact runs_mono L₁ (by unfold recCountersCost; omega)

/-- The cost of a call's recovery. -/
def recoverCost (w : N.World ⊕ N.Temp) (old hs : Fin 6 → List Bool) (b f V : ℕ) : ℕ :=
  RecursiveChildCallReturn.cost old hs + recCountersCost b f N.width + (92 * (parked N w).length + 51883) * V + 2

/-- **Recovering from a call** of rank `r` on wire `w`: the child's output `out` on `io` goes
back to `w`. -/
theorem recover_runs (w : N.World ⊕ N.Temp) {v : Descriptor} {b f r : ℕ} (hpos : v.Positive) (hb : 0 < b)
    (hf : 0 < f) (hw : v.width = (N.width * f) * b) (data : RecursiveMixedSchedule.Data (tapes N) v)
    (hio : data (io N) = fun _ => blank) (hpay : ∀ z, p ≤ z → fs z = blank)
    (hdesc : RecursiveStackAllocation.Available 0 st) (out : Fin (volume prime v) → Fin 4) :
    Runs (recoverB N w)
      (bank (childRoles N (RecursiveShiftRoleBank.source out)) (hdr (childView (N := N) b f r v))
        ((RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) (volume prime v)
          (bank (roles data) (hdr v) fs p node scalar (nodeC N b f) st)).tape (controlSlot 2))
        ((RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) (volume prime v)
          (bank (roles data) (hdr v) fs p node scalar (nodeC N b f) st)).head (controlSlot 2))
        node scalar (Prepare.rest b N.width) (RecursiveChildCallSetup.savedStacks (hdr v) st code0))
      (bank (roles (Function.update data (wireSlot N w) out)) (hdr v) fs p node scalar (nodeC N b f) st)
      (recoverCost (N := N) w (hdr v) (hdr (childView (N := N) b f r v)) b f (volume prime v)) := by
  set E := RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) (volume prime v)
    (bank (roles data) (hdr v) fs p node scalar (nodeC N b f) st)
  -- the headers
  have hres := RecursiveChildCallReturn.restores (q := prime) (hdr v) (hdr (childView (N := N) b f r v)) st code0 hdesc
  rw [pending_zero] at hres
  have hres' : HoareTime (RecursiveChildCallReturn.program (q := prime))
      (fun w => w = (RecursiveChildCallSetup.bank (hdr (childView (N := N) b f r v))
        (RecursiveChildCallSetup.savedStacks (hdr v) st code0)).append (CallPlace.cnt (e := 0) Fin.elim0))
      (fun w => w = (RecursiveChildCallSetup.bank (hdr v) st).append (CallPlace.cnt (e := 0) Fin.elim0))
      (RecursiveChildCallReturn.cost (hdr v) (hdr (childView (N := N) b f r v))) := by
    rw [append_zero, append_zero]; exact hres
  have h₁ := CallPlace.call_runs (T := tapes N) (roles := childRoles N (RecursiveShiftRoleBank.source out))
    (f := E.tape (controlSlot 2)) (p := E.head (controlSlot 2)) (node := node) (scalar := scalar)
    (c := Prepare.rest b N.width) (aux := Fin.elim0) (fun i => i.elim0) (cs := Fin.elim0) (fun j => j.elim0) hres'
  -- the counters
  have h₂ := recCounters_runs (N := N) (rr := childRoles N (RecursiveShiftRoleBank.source out))
    (fs := E.tape (controlSlot 2)) (p := E.head (controlSlot 2)) (node := node) (scalar := scalar) (st := st) hb hf hw
  -- the payload
  set aux := node.append (scalar.append (CommonBank.counters (nodeC N b f)))
  set rN := setTape (roles data) (wireSlot N w) (RecursiveShiftRoleBank.source out) 0
  have hrec := RecursiveCallProtocol.recovers (u := 1+(1+K)) (parked N w) (NodePark.parked_nodup N w)
    (wireSlot N w) (io N) (NodeBank.wireSlot_ne_io N w) (NodePark.active_not_parked N w) (NodePark.io_not_parked N w)
    v rN (hdr v) fs p aux st (Routines.hdr_headers v) hpos
    (fun z hz => by
      have hzw : z ≠ wireSlot N w := ((NodePark.mem_parked N w z).mp hz).1
      simp only [rN, setTape, Function.update_of_ne hzw]
      exact NodePark.roles_supported N data z)
    (fun z hz _ => hpay z hz)
    (by
      simp only [rN, setTape, Function.update_self]
      refine ⟨trivial, ?_⟩
      rw [RecursiveRoleSerialization.source_eq_word]
      exact RoleArrayStack.supported_word _ _ (by simp [List.length_ofFn]))
    (by
      have hne : io N ≠ wireSlot N w := (NodeBank.wireSlot_ne_io N w).symm
      simp only [rN, setTape, Function.update_of_ne hne]
      refine ⟨rfl, ?_⟩
      change RecursiveShiftRoleBank.source (data (io N)) = _
      rw [hio]; exact RecursiveRowsSerialization.source_blank v)
  have hin : RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) (volume prime v)
      (RecursiveCallBank.bank rN (hdr v) fs p aux st) =
      bank (childRoles N (RecursiveShiftRoleBank.source out)) (hdr v) (E.tape (controlSlot 2))
        (E.head (controlSlot 2)) node scalar (nodeC N b f) st := by
    rw [NodePark.entered_updated]
    have hE : E = RecursiveCallBank.bank (childRoles N ((roles data).tape (wireSlot N w))) (hdr v)
        (E.tape (controlSlot 2)) (E.head (controlSlot 2)) aux st :=
      NodePark.entered_eq N w (volume prime v) (roles data) (hdr v) fs p aux st
    change setTape E _ _ 0 = _
    conv_lhs => rw [hE]
    rw [← NodePark.bank_setTape]
    simp only [childRoles, SharedPlacementAlphabet.setTape_setTape]
    rfl
  have hout : RecursiveCallBank.bank rN (hdr v) fs p aux st =
      bank (roles (Function.update data (wireSlot N w) out)) (hdr v) fs p node scalar (nodeC N b f) st := by
    change RecursiveCallBank.bank (RecursiveShiftRoleBank.updated (roles data) (wireSlot N w) out) (hdr v) fs p aux st = _
    rw [RecursiveRoleSerialization.roles_update]
    rfl
  rw [hin, hout] at hrec
  have L₂ := seq_runs (Blocks.seq_leading _ _) (recoverPayB_leading N w) h₂ hrec
  have L₁ := seq_runs (CallPlace.place_leading _ _) (Blocks.seq_leading _ _) h₁ L₂
  exact runs_mono L₁ (by unfold recoverCost; omega)

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeCall
