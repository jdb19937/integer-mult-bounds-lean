module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Arith
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Routines

/-!
# Straight-line descriptor programs

A list of powers, products, divisions, differences, erasures and copies on the `22` optional
descriptors of `Headers.bank` (`Instr`) is one program (`prog`). The bank is read as a state of
optional values (`words`); each instruction updates the state (`exec`) when its operands are
present, its outputs and scratch blank and its divisor positive (`Pres`). `runs`: the program runs
from the state to its final state at the sum of the instruction costs, and `costs_le` bounds that
sum by the operand values (`weights`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Straight

noncomputable section
open IntegerMultBounds.Machine
open IntegerMultBounds.Machine.CounterDimensions (descriptorHead descriptorTape)
open FlatCoordinateSchedule (bits)
open RevMachine
open Headers (bank powerSlots productSlots powerAt productAt eraseAt copyAt)
open Arith (divSlots splitAt diffSlots diffAt)

/-- Optional values on the `22` slots. -/
abbrev State := Fin 22 → Option ℕ

/-- The canonical words of a state. -/
def words (s : State) : Fin 22 → Option (List Bool) := fun i => (s i).map bits

theorem words_update (s : State) (j : Fin 22) (x : Option ℕ) :
    words (Function.update s j x) = Function.update (words s) j (x.map bits) := by
  funext i
  by_cases h : i = j
  · subst h; simp [words]
  · simp [words, h]

/-- One instruction. -/
inductive Instr where
  | pow (e o : Fin 22) (h : Function.Injective (powerSlots e o))
  | prod (w o m : Fin 22) (h : Function.Injective (productSlots w o m))
  | div (y d z r : Fin 22) (h : Function.Injective (divSlots y d z r))
  | diff (x y o : Fin 22) (h : Function.Injective (diffSlots x y o))
  | erase (j : Fin 22)
  | copy (src dst : Fin 22) (h : src ≠ dst)

/-- The value of a slot. -/
def val (s : State) (i : Fin 22) : ℕ := (s i).getD 0

variable (q : ℕ)

/-- The state after an instruction. -/
def exec1 : Instr → State → State
  | .pow e o _, s => Function.update s o (some (q ^ val s e))
  | .prod w o m _, s => Function.update s o (some (val s m * val s w))
  | .div y d z r _, s =>
    Function.update (Function.update s z (some (val s y / val s d))) r (some (val s y % val s d))
  | .diff x y o _, s => Function.update s o (some (val s x - val s y))
  | .erase j, s => Function.update s j none
  | .copy src dst _, s => Function.update s dst (s src)

/-- What an instruction needs. -/
def Pre : Instr → State → Prop
  | .pow e o _, s => (s e).isSome ∧ s 0 = none ∧ s 1 = none ∧ s o = none
  | .prod w o m _, s => (s w).isSome ∧ (s m).isSome ∧ 0 < val s w ∧ s 0 = none ∧ s 1 = none ∧
      s 2 = none ∧ s o = none
  | .div y d z r _, s => (s y).isSome ∧ (s d).isSome ∧ 0 < val s d ∧ s z = none ∧ s r = none ∧
      s 0 = none ∧ s 1 = none ∧ s 2 = none ∧ s 13 = none ∧ s 14 = none ∧ s 15 = none ∧
      s 16 = none ∧ s 17 = none ∧ s 18 = none ∧ s 19 = none
  | .diff x y o _, s => (s x).isSome ∧ (s y).isSome ∧ val s y ≤ val s x ∧ s o = none
  | .erase j, s => (s j).isSome
  | .copy src dst _, s => (s src).isSome ∧ s dst = none

/-- The cost of an instruction. -/
def cost1 : Instr → State → ℕ
  | .pow e _ _, s => 99 * q ^ val s e
  | .prod w _ m _, s => 53 * (val s m * val s w) + 28
  | .div y d _ _ _, s => BinaryDescriptorDivMod.cost (bits (val s y)) (bits (val s d))
  | .diff x _ _ _, s => 6 * val s x + 27
  | .erase j, s => 2 * (bits (val s j)).length + 4
  | .copy src _ _, s => 2 * (bits (val s src)).length + 5

/-- The operand size of an instruction. -/
def weight : Instr → State → ℕ
  | .pow e _ _, s => q ^ val s e
  | .prod w _ m _, s => val s m * val s w
  | .div y d _ _ _, s => val s y + val s d
  | .diff x _ _ _, s => val s x
  | .erase j, s => val s j
  | .copy src _ _, s => val s src

/-- The final state. -/
def execs : List Instr → State → State
  | [], s => s
  | i :: l, s => execs l (exec1 q i s)

/-- Every instruction's needs, in order. -/
def Pres : List Instr → State → Prop
  | [], _ => True
  | i :: l, s => Pre i s ∧ Pres l (exec1 q i s)

def costs : List Instr → State → ℕ
  | [], _ => 0
  | i :: l, s => cost1 q i s + 1 + costs l (exec1 q i s)

def weights : List Instr → State → ℕ
  | [], _ => 0
  | i :: l, s => (weight q i s + 1) + weights l (exec1 q i s)

variable {q} (hq : 2 ≤ q)

/-- One instruction's program. -/
def prog1 : Instr → (n : ℕ) × Program 22 n q
  | .pow e o h => ⟨_, powerAt hq e o h⟩
  | .prod w o m h => ⟨_, productAt (q := q) w o m h⟩
  | .div y d z r h => ⟨_, splitAt (q := q) y d z r h⟩
  | .diff x y o h => ⟨_, diffAt (q := q) x y o h⟩
  | .erase j => ⟨_, eraseAt (q := q) j⟩
  | .copy src dst h => ⟨_, copyAt (q := q) src dst h⟩

/-- **The straight-line program.** -/
def prog : List Instr → (n : ℕ) × Program 22 n q
  | [] => ⟨1, skip 22 q (by omega)⟩
  | i :: l => ⟨_, seq (prog1 hq i).2 (prog l).2⟩

/-! ### Runs -/

theorem canon_eq {xs : List Bool} {x : ℕ} (hc : GrowingCounterData.Canonical xs) (hv : Counter.value xs = x) :
    xs = bits x := by rw [Routines.canon hc, hv]

theorem some_words {s : State} {i : Fin 22} (h : (s i).isSome) : words s i = some (bits (val s i)) := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  simp [words, val, hx]

theorem none_words {s : State} {i : Fin 22} (h : s i = none) : words s i = none := by simp [words, h]

/-- The divmod routine on any slots. -/
theorem div_step {d : Fin 22 → Option (List Bool)} {y dv z r : Fin 22}
    (hinj : Function.Injective (divSlots y dv z r)) {ys ds : List Bool}
    (hd0 : 0 < Counter.value ds) (hy : d y = some ys) (hdv : d dv = some ds)
    (hz : d z = none) (hr : d r = none)
    (s0 : d 0 = none) (s1 : d 1 = none) (s2 : d 2 = none) (s13 : d 13 = none) (s14 : d 14 = none)
    (s15 : d 15 = none) (s16 : d 16 = none) (s17 : d 17 = none) (s18 : d 18 = none) (s19 : d 19 = none) :
    ∃ zs rs : List Bool, GrowingCounterData.Canonical zs ∧ GrowingCounterData.Canonical rs ∧
      Counter.value zs = Counter.value ys / Counter.value ds ∧
      Counter.value rs = Counter.value ys % Counter.value ds ∧
      HoareTime (splitAt (q := q) y dv z r hinj) (fun v => v = bank d)
        (fun v => v = bank (Function.update (Function.update d z (some zs)) r (some rs)))
        (BinaryDescriptorDivMod.cost ys ds) := by
  obtain ⟨zs, rs, cz, cr, vz, vr, -, -, h⟩ := BinaryDescriptorDivMod.divmod_hoare (a := q) ys ds hd0
  refine ⟨zs, rs, cz, cr, vz, vr, ?_⟩
  have hvec : d ∘ divSlots y dv z r =
      ![some ys, some ds, none, none, none, none, none, none, none, none, none, none, none, none] := by
    funext i; fin_cases i <;> simp [divSlots, hy, hdv, hz, hr, s0, s1, s2, s13, s14, s15, s16, s17, s18, s19]
  have hvec' : Function.update (Function.update d z (some zs)) r (some rs) ∘ divSlots y dv z r =
      ![some ys, some ds, none, none, none, some zs, some rs, none, none, none, none, none, none, none] := by
    funext i
    have e := congrFun hvec i
    simp only [Function.comp_apply] at e ⊢
    rw [Function.update_apply, Function.update_apply]
    by_cases h6 : i = 6
    · subst h6; simp only [show divSlots y dv z r 6 = r from rfl, ↓reduceIte]; rfl
    have n6 : divSlots y dv z r i ≠ r := fun h => h6 (hinj (h.trans (rfl : r = divSlots y dv z r 6)))
    by_cases h5 : i = 5
    · subst h5
      have : z ≠ r := fun h => by
        have := hinj (show divSlots y dv z r 5 = divSlots y dv z r 6 from h)
        exact absurd this (by decide)
      simp only [show divSlots y dv z r 5 = z from rfl, this, ↓reduceIte]; rfl
    have n5 : divSlots y dv z r i ≠ z := fun h => h5 (hinj (h.trans (rfl : z = divSlots y dv z r 5)))
    simp only [n6, n5, ↓reduceIte]; rw [e]
    fin_cases i <;> simp_all
  refine Headers.placed_bank _ _ _ ?_ ?_ ?_ h
  · rw [Arith.divmod_input]
    have := congrFun hvec
    apply congrArg₂ Tapes.mk <;> funext i <;> rw [show d (divSlots y dv z r i) = _ from this i] <;>
      fin_cases i <;> simp [descriptorHead, descriptorTape]
  · rw [Arith.divmod_output]
    have := congrFun hvec'
    apply congrArg₂ Tapes.mk <;> funext i <;> rw [show (Function.update (Function.update d z (some zs)) r
      (some rs)) (divSlots y dv z r i) = _ from this i] <;> fin_cases i <;> simp [descriptorHead, descriptorTape]
  · intro j hj
    have h5 : z ≠ j := fun h => hj 5 (by simp [divSlots, h])
    have h6 : r ≠ j := fun h => hj 6 (by simp [divSlots, h])
    rw [Function.update_of_ne h6.symm, Function.update_of_ne h5.symm]

theorem run1 : ∀ (i : Instr) (s : State), Pre i s →
    HoareTime (prog1 hq i).2 (fun v => v = bank (words s)) (fun v => v = bank (words (exec1 q i s)))
      (cost1 q i s)
  | .pow e o h, s, ⟨he, h0, h1, ho⟩ => by
    have hs := Headers.power_step hq h (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_canonical _)
      (some_words he) (none_words h0) (none_words h1) (none_words ho)
    refine hs.consequence (fun _ h => h) (fun _ hv => hv.trans ?_) le_rfl
    rw [exec1, words_update, Option.map_some,
      canon_eq (RadixPowerDescriptor.bits_canonical hq _) (RadixPowerDescriptor.bits_value hq _)]
  | .prod w o m h, s, ⟨hw, hm, hpos, h0, h1, h2, ho⟩ => by
    have hs := Headers.product_step (q := q) h hpos (FlatCoordinateSchedule.bits_value _)
      (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_value _)
      (FlatCoordinateSchedule.bits_canonical _) (some_words hw) (some_words hm) (none_words h0) (none_words h1)
      (none_words h2) (none_words ho)
    refine hs.consequence (fun _ h => h) (fun _ hv => hv.trans ?_) le_rfl
    rw [exec1, words_update, Option.map_some,
      canon_eq (DimensionProductDescriptor.bits_canonical _ _) (DimensionProductDescriptor.bits_value _ _)]
  | .div y d z r h, s, ⟨hy, hd, hpos, hz, hr, s0, s1, s2, s13, s14, s15, s16, s17, s18, s19⟩ => by
    obtain ⟨zs, rs, cz, cr, vz, vr, hs⟩ := div_step (q := q) h (by rw [FlatCoordinateSchedule.bits_value]; exact hpos)
      (some_words hy) (some_words hd) (none_words hz) (none_words hr) (none_words s0) (none_words s1)
      (none_words s2) (none_words s13) (none_words s14) (none_words s15) (none_words s16) (none_words s17)
      (none_words s18) (none_words s19)
    refine hs.consequence (fun _ h => h) (fun _ hv => hv.trans ?_) le_rfl
    rw [FlatCoordinateSchedule.bits_value, FlatCoordinateSchedule.bits_value] at vz vr
    rw [exec1, words_update, words_update, Option.map_some, Option.map_some, canon_eq cz vz, canon_eq cr vr]
  | .diff x y o h, s, ⟨hx, hy, hle, ho⟩ => by
    have hs := Arith.difference_hoare (q := q) h
      (by rw [FlatCoordinateSchedule.bits_value, FlatCoordinateSchedule.bits_value]; exact hle)
      (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
      (some_words hx) (some_words hy) (none_words ho)
    refine hs.consequence (fun _ h => h) (fun _ hv => hv.trans ?_) (by simp [cost1])
    rw [exec1, words_update, Option.map_some, FlatCoordinateSchedule.bits_value, FlatCoordinateSchedule.bits_value,
      canon_eq (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_value _)]
  | .erase j, s, hj => by
    have hs := Headers.erase_step (q := q) (some_words hj)
    refine hs.consequence (fun _ h => h) (fun _ hv => hv.trans ?_) le_rfl
    rw [exec1, words_update]; rfl
  | .copy src dst h, s, ⟨hsrc, hdst⟩ => by
    have hs := Headers.copy_step (q := q) h (some_words hsrc) (none_words hdst)
    refine hs.consequence (fun _ h => h) (fun _ hv => hv.trans ?_) le_rfl
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsrc
    rw [exec1, words_update, hx]
    simp [val, hx]

/-- **A straight-line program runs** from its state to its final state. -/
theorem runs : ∀ (l : List Instr) (s : State), Pres q l s →
    HoareTime (prog hq l).2 (fun v => v = bank (words s)) (fun v => v = bank (words (execs q l s)))
      (costs q l s)
  | [], _, _ => skip_hoare _ _
  | i :: l, s, ⟨hi, hl⟩ => (run1 hq i s hi).seq (runs l _ hl)

/-! ### Costs -/

theorem length_le (x : ℕ) : (bits x).length ≤ x + 1 := by
  have hw := GrowingCounterData.canonical_width _ (FlatCoordinateSchedule.bits_canonical x)
  have hl := Nat.log2_le_self (Counter.value (bits x))
  rw [FlatCoordinateSchedule.bits_value] at hw hl
  omega

theorem cost1_le (i : Instr) (s : State) : cost1 q i s ≤ 10000 * (weight q i s + 1) := by
  cases i with
  | pow => simp only [cost1, weight]; omega
  | prod => simp only [cost1, weight]; omega
  | div y d z r h =>
    simp only [cost1, weight]
    have hb := BinaryDescriptorDivMod.cost_le (bits (val s y)) (bits (val s d))
    have hy := BinaryDescriptorDivMod.descriptor_square _ (FlatCoordinateSchedule.bits_canonical (val s y))
    have hd := BinaryDescriptorDivMod.descriptor_square _ (FlatCoordinateSchedule.bits_canonical (val s d))
    rw [FlatCoordinateSchedule.bits_value] at hy hd
    have hy' := length_le (val s y)
    have hd' := length_le (val s d)
    nlinarith
  | diff => simp only [cost1, weight]; omega
  | erase j => simp only [cost1, weight]; have := length_le (val s j); omega
  | copy src => simp only [cost1, weight]; have := length_le (val s src); omega

theorem costs_le : ∀ (l : List Instr) (s : State), costs q l s ≤ 10001 * weights q l s
  | [], _ => le_rfl
  | i :: l, s => by
    have h1 := cost1_le (q := q) i s
    have h2 := costs_le l (exec1 q i s)
    simp only [costs, weights]
    omega

/-! ### Bounded values -/

/-- Every value of the state is at most `M`. -/
def Bnd (M : ℕ) (s : State) : Prop := ∀ i x, s i = some x → x ≤ M

/-- The new values of powers and products are at most `M`. -/
def Ok (M : ℕ) : Instr → State → Prop
  | .pow e _ _, s => q ^ val s e ≤ M
  | .prod w _ m _, s => val s m * val s w ≤ M
  | _, _ => True

def OkAll (M : ℕ) : List Instr → State → Prop
  | [], _ => True
  | i :: l, s => Ok (q := q) M i s ∧ OkAll M l (exec1 q i s)

theorem val_le {M : ℕ} {s : State} (h : Bnd M s) (i : Fin 22) : val s i ≤ M := by
  unfold val
  cases hs : s i with
  | none => simp
  | some x => exact h i x hs

theorem bnd_update {M : ℕ} {s : State} (h : Bnd M s) (j : Fin 22) {x : Option ℕ}
    (hx : ∀ y, x = some y → y ≤ M) : Bnd M (Function.update s j x) := by
  intro i y hy
  by_cases hij : i = j
  · subst hij; simp at hy; exact hx y hy
  · rw [Function.update_of_ne hij] at hy; exact h i y hy

theorem bnd_exec {M : ℕ} {s : State} (h : Bnd M s) (i : Instr) (hok : Ok (q := q) M i s) :
    Bnd M (exec1 q i s) ∧ weight q i s ≤ 2 * M := by
  have hv := val_le h
  cases i with
  | pow e o _ =>
    have hok : q ^ val s e ≤ M := hok
    exact ⟨bnd_update h _ (by simpa using hok), hok.trans (by omega)⟩
  | prod w o m _ =>
    have hok : val s m * val s w ≤ M := hok
    exact ⟨bnd_update h _ (by simpa using hok), hok.trans (by omega)⟩
  | div y d z r _ =>
    refine ⟨bnd_update (bnd_update h _ (by simpa using (Nat.div_le_self _ _).trans (hv y))) _
      (by simpa using (Nat.mod_le _ _).trans (hv y)), ?_⟩
    simp only [weight]; have := hv y; have := hv d; omega
  | diff x y o _ =>
    exact ⟨bnd_update h _ (by simpa using (Nat.sub_le _ _).trans (hv x)), (hv x).trans (by omega)⟩
  | erase j => exact ⟨bnd_update h _ (by simp), (hv j).trans (by omega)⟩
  | copy src dst _ =>
    refine ⟨bnd_update h _ (fun y hy => h src y hy), (hv src).trans (by omega)⟩

/-- **The operand sizes of a bounded run.** -/
theorem weights_le {M : ℕ} : ∀ (l : List Instr) (s : State), Bnd M s → OkAll (q := q) M l s →
    weights q l s ≤ (2 * M + 1) * l.length
  | [], _, _, _ => by simp [weights]
  | i :: l, s, h, ⟨hi, hl⟩ => by
    obtain ⟨h', hw⟩ := bnd_exec h i hi
    have := weights_le l _ h' hl
    simp only [weights, List.length_cons]
    nlinarith

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Straight
