module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Leaf
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Place
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Straight

/-!
# Switching the headers of the core's bank

The core's bank at a view `u` (`Leaf.leafBank` with the memo `e` on the scalar tape) holds the
headers of `u`. A straight-line program placed on the headers, the counters and the memo switches
them to the headers of another view `u'` of the same volume, the array kept (`switch_phase`).

The core's three switches (`toTop`, `toLow`, `back`): from `v` to its top `e - r` digits, from
there to its low `r` digits, and back to `v`, with `e` the width of `v`, `w` the atom width on
counter `0` and `r = e mod w`. Each costs a constant times the volume of `v`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Switch

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
open SharedBankFamily (padProgram)
open FlatCoordinateSchedule (bits)
open Stage2Wrapper (top low)
open RevMachine
open CommonBank (count)
open Core (Phase)
open Place (memo Slot sel)
open Straight (Instr State words execs Pres costs)

/-! ### Views of the same volume -/

theorem top_volume {q r : ℕ} {v : Descriptor} (hr : r ≤ v.width) : volume q (top q r v) = volume q v := by
  have he : q ^ v.width = q ^ (v.width - r) * q ^ r := by rw [← pow_add, Nat.sub_add_cancel hr]
  simp only [volume, top, he]
  ring

theorem low_volume {q r : ℕ} {v : Descriptor} (hr : r ≤ v.width) : volume q (low q r v) = volume q v := by
  have he : q ^ v.width = q ^ (v.width - r) * q ^ r := by rw [← pow_add, Nat.sub_add_cancel hr]
  simp only [volume, low, he]
  ring

theorem rolesAt_congr {u u' : Descriptor} (h : volume prime u = volume prime u') (X : ℕ → ZMod 2) :
    FamilyStep.rolesAt u X = FamilyStep.rolesAt u' X := by
  have key : ∀ N N' : ℕ, N = N' →
      FlatRepeatedControlArray.pair (radix := prime) (fun i : Fin N => SparseRoleCircuit.encode (a := 0) (X i)) =
        FlatRepeatedControlArray.pair (radix := prime) (fun i : Fin N' => SparseRoleCircuit.encode (a := 0) (X i)) := by
    rintro _ _ rfl; rfl
  unfold FamilyStep.rolesAt FamilyRoot.rolesOf RecursiveShiftRoleBank.source Shared50RecursiveNodeSemantics.encoded
  rw [key _ _ h]

/-! ### A switch -/

variable (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (E : ℕ) (c : Fin CommonBank.K → Option ℕ)
  (st : Tapes 2 prime)

/-- The core's bank with the memo. -/
abbrev B (N : ℕ) (u : Descriptor) (X : ℕ → ZMod 2) : Tapes N prime :=
  raw (Leaf.leafBank f p node (memo E) c st u X) N

/-- A straight-line program placed by the routing `a`. -/
def placed (l : List Instr) (a : Fin 22 → Option Slot) (ha : Function.Injective (sel a)) :=
  Embed.place (t := count (NodeBank.tapes rev97m)) (Straight.prog (Nat.Prime.two_le
    Networks.Shared50ModularControl.prime_prime) l).2 (fun i => (sel a i).pos) (Place.pos_injective.comp ha)
    (Nat.add_comm _ _)

variable {f p node E c st}

/-- **A header switch.** -/
theorem switch_phase {N : ℕ} (hN : count (NodeBank.tapes rev97m) + 22 ≤ N) {u u' : Descriptor}
    (hvol : volume prime u = volume prime u') (l : List Instr) (a : Fin 22 → Option Slot)
    (ha : Function.Injective (sel a)) {s₀ s₁ : State} (hp : Pres prime l s₀) (hs : execs prime l s₀ = s₁)
    (hin : ∀ i, words s₀ i = (sel a i).value (Routines.hdr u) c E)
    (hout : ∀ i, words s₁ i = (sel a i).value (Routines.hdr u') c E)
    (hh : ∀ j, (∀ i, sel a i ≠ .header j) → Routines.hdr u' j = Routines.hdr u j) :
    Phase (padProgram (placed l a ha).program hN) (B f p node E c st N) u u' Eq (costs prime l s₀) := by
  intro X
  have hr := Place.memo_runs (roles := FamilyStep.rolesAt u X) (f := f) (p := p) (node := node) (st := st) a ha
    (Straight.runs (Nat.Prime.two_le Networks.Shared50ModularControl.prime_prime) l s₀ hp) (Routines.hdr u') c
    hin (fun i => by rw [hs]; exact hout i) hh (fun _ _ => rfl)
  have hpad := SharedBankFamily.pad_realizes hN (Nat.le_add_right _ _) _ _ _ hr
  refine hpad.consequence (fun _ h => h) (fun z hz => ⟨X, rfl, ?_⟩) le_rfl
  rw [hz, B, Leaf.leafBank, rolesAt_congr hvol]

/-! ### Volume bounds -/

section Bounds

variable {v : Descriptor} (hp : v.Positive)
include hp

theorem dvd_le {x : ℕ} (h : x ∣ volume prime v) : x ≤ volume prime v :=
  Nat.le_of_dvd (RecursiveAffinePrepare.volume_positive
    (Nat.Prime.two_le Networks.Shared50ModularControl.prime_prime) v hp) h

theorem width_le : v.width ≤ volume prime v :=
  (Nat.lt_pow_self Networks.Shared50ModularControl.prime_prime.one_lt).le.trans
    (dvd_le hp (Dvd.intro (v.beforeRows*v.rows*v.beforeH*v.between*prime^v.width*v.afterD)
      (by unfold volume; ring)))

theorem beforeH_le : v.beforeH ≤ volume prime v :=
  dvd_le hp (Dvd.intro (v.beforeRows*v.rows*prime^v.width*v.between*prime^v.width*v.afterD)
    (by unfold volume; ring))

theorem between_le : v.between ≤ volume prime v :=
  dvd_le hp (Dvd.intro (v.beforeRows*v.rows*v.beforeH*prime^v.width*prime^v.width*v.afterD)
    (by unfold volume; ring))

theorem afterD_le : v.afterD ≤ volume prime v :=
  dvd_le hp (Dvd.intro (v.beforeRows*v.rows*v.beforeH*prime^v.width*v.between*prime^v.width)
    (by unfold volume; ring))

theorem pow_le {r : ℕ} (hr : r ≤ v.width) : prime ^ r ≤ volume prime v :=
  dvd_le hp ((pow_dvd_pow prime hr).trans (Dvd.intro (v.beforeRows*v.rows*v.beforeH*v.between*prime^v.width*v.afterD)
    (by unfold volume; ring)))

theorem beforeH_pow_le {r : ℕ} (hr : r ≤ v.width) : v.beforeH * prime ^ r ≤ volume prime v :=
  dvd_le hp ((mul_dvd_mul_left _ (pow_dvd_pow prime hr)).trans
    (Dvd.intro (v.beforeRows*v.rows*v.between*prime^v.width*v.afterD) (by unfold volume; ring)))

theorem between_pow_le {r : ℕ} (hr : r ≤ v.width) : v.between * prime ^ r ≤ volume prime v :=
  dvd_le hp ((mul_dvd_mul_left _ (pow_dvd_pow prime hr)).trans
    (Dvd.intro (v.beforeRows*v.rows*v.beforeH*prime^v.width*v.afterD) (by unfold volume; ring)))

theorem afterD_pow_le {r : ℕ} (hr : r ≤ v.width) : v.afterD * prime ^ r ≤ volume prime v :=
  dvd_le hp ((mul_dvd_mul_left _ (pow_dvd_pow prime hr)).trans
    (Dvd.intro (v.beforeRows*v.rows*v.beforeH*prime^v.width*v.between) (by unfold volume; ring)))

end Bounds

theorem prime_pow_pos (r : ℕ) : 0 < prime ^ r := pow_pos Networks.Shared50ModularControl.prime_prime.pos r

/-- The cost of a bounded straight-line program. -/
theorem costs_le {l : List Instr} {s : State} {M : ℕ} (hb : Straight.Bnd M s)
    (hok : Straight.OkAll (q := prime) M l s) :
    costs prime l s ≤ 10001 * ((2 * M + 1) * l.length) :=
  (Straight.costs_le l s).trans (Nat.mul_le_mul_left _ (Straight.weights_le l s hb hok))

/-! ### To the top digits -/

/-- From the width `e`, `between` and `afterD` at slots `3..5` and the atom width `w` at slot `6`:
`r = e mod w`, then `e - r`, `between · q^r` and `afterD · q^r` replace the three headers. -/
def topList : List Instr :=
  [.div 3 6 7 8 (by decide), .erase 7, .diff 3 8 9 (by decide), .pow 8 10 (by decide),
   .prod 10 11 4 (by decide), .prod 10 12 5 (by decide), .erase 3, .erase 4, .erase 5,
   .copy 9 3 (by decide), .copy 11 4 (by decide), .copy 12 5 (by decide),
   .erase 8, .erase 9, .erase 10, .erase 11, .erase 12]

def topRoute : Fin 22 → Option Slot :=
  ![none, none, none, some (.header 3), some (.header 4), some (.header 5), some (.aux 0), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]

theorem topRoute_inj : Function.Injective (sel topRoute) := by decide

def topIn (e bt af w : ℕ) : State :=
  ![none, none, none, some e, some bt, some af, some w, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]

def topOut (e bt af w r : ℕ) : State :=
  ![none, none, none, some (e - r), some (bt * prime ^ r), some (af * prime ^ r), some w, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]

theorem top_exec (e bt af w : ℕ) : execs prime topList (topIn e bt af w) = topOut e bt af w (e % w) := by
  funext i
  fin_cases i <;> simp [execs, Straight.exec1, Straight.val, topList, topIn, topOut]

theorem top_pres {e bt af w : ℕ} (hw : 0 < w) : Pres prime topList (topIn e bt af w) := by
  simp [Pres, Straight.Pre, Straight.exec1, Straight.val, topList, topIn, hw,
    prime_pow_pos, Nat.mod_le]

/-- **To the top digits.** -/
theorem toTop_phase {N : ℕ} (hN : count (NodeBank.tapes rev97m) + 22 ≤ N) (v : Descriptor) {w : ℕ}
    (hw : 0 < w) :
    Phase (padProgram (placed topList topRoute topRoute_inj).program hN)
      (B f p node E (Prepare.rest w 529) st N) v (top prime (v.width % w) v) Eq
      (costs prime topList (topIn v.width v.between v.afterD w)) := by
  refine switch_phase hN (top_volume (Nat.mod_le _ _)).symm _ _ _ (top_pres hw) (top_exec _ _ _ _)
    (fun i => ?_) (fun i => ?_) (fun j hj => ?_)
  · fin_cases i <;> simp [words, topIn, sel, topRoute, Slot.value, Routines.hdr, RecursiveDimensionBank.values,
      CommonBank.word, Prepare.rest]
  · fin_cases i <;> simp [words, topOut, sel, topRoute, Slot.value, Routines.hdr, RecursiveDimensionBank.values,
      CommonBank.word, Prepare.rest, top, mul_comm]
  · fin_cases j
    · simp [Routines.hdr, RecursiveDimensionBank.values, top]
    · simp [Routines.hdr, RecursiveDimensionBank.values, top]
    · simp [Routines.hdr, RecursiveDimensionBank.values, top]
    · exact absurd rfl (hj 3)
    · exact absurd rfl (hj 4)
    · exact absurd rfl (hj 5)

theorem toTop_cost {v : Descriptor} (hp : v.Positive) {w : ℕ} (hwe : w ≤ v.width) :
    costs prime topList (topIn v.width v.between v.afterD w) ≤ 10001 * 51 * volume prime v := by
  have hV := RecursiveAffinePrepare.volume_positive (Nat.Prime.two_le Networks.Shared50ModularControl.prime_prime) v hp
  have hr : v.width % w ≤ v.width := Nat.mod_le _ _
  have h := costs_le (l := topList) (M := volume prime v) (s := topIn v.width v.between v.afterD w) (by
      intro i x hx
      fin_cases i <;> simp [topIn] at hx <;> subst hx
      · exact width_le hp
      · exact between_le hp
      · exact afterD_le hp
      · exact hwe.trans (width_le hp))
    (by simp [Straight.OkAll, Straight.Ok, Straight.exec1, Straight.val, topList, topIn,
      pow_le hp hr, between_pow_le hp hr, afterD_pow_le hp hr])
  rw [show topList.length = 17 from rfl] at h
  nlinarith

/-! ### To the low digits -/

/-- From the top headers `beforeH`, `e - r`, `q^r · between`, `q^r · afterD` at slots `3..6` and
the memo `e` at slot `7`: `r = e - (e - r)`, then `beforeH · q^(e-r)`, `r`, `between · q^(e-r)`
and `afterD` replace the four headers. -/
def lowList : List Instr :=
  [.diff 7 4 8 (by decide), .pow 8 9 (by decide), .pow 4 10 (by decide), .div 5 9 11 12 (by decide),
   .erase 12, .div 6 9 12 20 (by decide), .erase 20, .prod 10 20 3 (by decide), .prod 10 21 11 (by decide),
   .erase 3, .erase 4, .erase 5, .erase 6,
   .copy 20 3 (by decide), .copy 8 4 (by decide), .copy 21 5 (by decide), .copy 12 6 (by decide),
   .erase 8, .erase 9, .erase 10, .erase 11, .erase 12, .erase 20, .erase 21]

def lowRoute : Fin 22 → Option Slot :=
  ![none, none, none, some (.header 2), some (.header 3), some (.header 4), some (.header 5), some .scalar,
    none, none, none, none, none, none, none, none, none, none, none, none, none, none]

theorem lowRoute_inj : Function.Injective (sel lowRoute) := by decide

def lowIn (v : Descriptor) (r : ℕ) : State :=
  ![none, none, none, some v.beforeH, some (v.width - r), some (prime ^ r * v.between),
    some (prime ^ r * v.afterD), some v.width, none, none, none, none, none, none, none, none, none, none, none, none, none, none]

def lowOut (v : Descriptor) (r : ℕ) : State :=
  ![none, none, none, some (v.beforeH * prime ^ (v.width - r)), some r,
    some (v.between * prime ^ (v.width - r)), some v.afterD, some v.width, none, none, none, none, none, none, none, none, none, none, none, none, none, none]

theorem low_exec (v : Descriptor) {r : ℕ} (hr : r ≤ v.width) :
    execs prime lowList (lowIn v r) = lowOut v r := by
  funext i
  fin_cases i <;> simp [execs, Straight.exec1, Straight.val, lowList, lowIn, lowOut, Nat.sub_sub_self hr,
    Nat.mul_div_cancel_left _ (prime_pow_pos r)]

theorem low_pres (v : Descriptor) {r : ℕ} (hr : r ≤ v.width) : Pres prime lowList (lowIn v r) := by
  simp [Pres, Straight.Pre, Straight.exec1, Straight.val, lowList, lowIn, Nat.sub_sub_self hr,
    Nat.mul_div_cancel_left _ (prime_pow_pos r), prime_pow_pos]

/-- **To the low digits.** -/
theorem toLow_phase {N : ℕ} (hN : count (NodeBank.tapes rev97m) + 22 ≤ N) (v : Descriptor) {r : ℕ}
    (hr : r ≤ v.width) :
    Phase (padProgram (placed lowList lowRoute lowRoute_inj).program hN)
      (B f p node v.width c st N) (top prime r v) (low prime r v) Eq (costs prime lowList (lowIn v r)) := by
  refine switch_phase hN ((top_volume hr).trans (low_volume hr).symm) _ _ _ (low_pres v hr) (low_exec v hr)
    (fun i => ?_) (fun i => ?_) (fun j hj => ?_)
  · fin_cases i <;> simp [words, lowIn, sel, lowRoute, Slot.value, Routines.hdr, RecursiveDimensionBank.values,
      top]
  · fin_cases i <;> simp [words, lowOut, sel, lowRoute, Slot.value, Routines.hdr, RecursiveDimensionBank.values,
      low]
  · fin_cases j
    · simp [Routines.hdr, RecursiveDimensionBank.values, top, low]
    · simp [Routines.hdr, RecursiveDimensionBank.values, top, low]
    · exact absurd rfl (hj 3)
    · exact absurd rfl (hj 4)
    · exact absurd rfl (hj 5)
    · exact absurd rfl (hj 6)

theorem toLow_cost {v : Descriptor} (hp : v.Positive) {r : ℕ} (hr : r ≤ v.width) :
    costs prime lowList (lowIn v r) ≤ 10001 * 72 * volume prime v := by
  have hV := RecursiveAffinePrepare.volume_positive (Nat.Prime.two_le Networks.Shared50ModularControl.prime_prime) v hp
  have hm : v.width - r ≤ v.width := Nat.sub_le _ _
  have h := costs_le (l := lowList) (M := volume prime v) (s := lowIn v r) (by
      intro i x hx
      fin_cases i <;> simp [lowIn] at hx <;> subst hx
      · exact beforeH_le hp
      · exact hm.trans (width_le hp)
      · rw [mul_comm]; exact between_pow_le hp hr
      · rw [mul_comm]; exact afterD_pow_le hp hr
      · exact width_le hp)
    (by simp [Straight.OkAll, Straight.Ok, Straight.exec1, Straight.val, lowList, lowIn, Nat.sub_sub_self hr,
      Nat.mul_div_cancel_left _ (prime_pow_pos r), pow_le hp hr, pow_le hp hm, beforeH_pow_le hp hm,
      between_pow_le hp hm])
  rw [show lowList.length = 24 from rfl] at h
  nlinarith

/-! ### Back to the view -/

/-- From the low headers `beforeH · q^m`, `r`, `between · q^m` at slots `3..5` and the memo `e` at
slot `6`: `m = e - r`, then `beforeH`, `e` and `between` replace the three headers. -/
def backList : List Instr :=
  [.diff 6 4 7 (by decide), .pow 7 8 (by decide), .div 3 8 9 10 (by decide), .erase 10,
   .div 5 8 10 11 (by decide), .erase 11, .erase 3, .erase 4, .erase 5,
   .copy 9 3 (by decide), .copy 6 4 (by decide), .copy 10 5 (by decide),
   .erase 7, .erase 8, .erase 9, .erase 10]

def backRoute : Fin 22 → Option Slot :=
  ![none, none, none, some (.header 2), some (.header 3), some (.header 4), some .scalar, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]

theorem backRoute_inj : Function.Injective (sel backRoute) := by decide

def backIn (v : Descriptor) (r : ℕ) : State :=
  ![none, none, none, some (v.beforeH * prime ^ (v.width - r)), some r,
    some (v.between * prime ^ (v.width - r)), some v.width, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]

def backOut (v : Descriptor) : State :=
  ![none, none, none, some v.beforeH, some v.width, some v.between, some v.width, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]

theorem back_exec (v : Descriptor) (r : ℕ) : execs prime backList (backIn v r) = backOut v := by
  funext i
  fin_cases i <;> simp [execs, Straight.exec1, Straight.val, backList, backIn, backOut,
    Nat.mul_div_cancel _ (prime_pow_pos _)]

theorem back_pres (v : Descriptor) {r : ℕ} (hr : r ≤ v.width) : Pres prime backList (backIn v r) := by
  simp [Pres, Straight.Pre, Straight.exec1, Straight.val, backList, backIn, hr,
    Nat.mul_div_cancel _ (prime_pow_pos _), prime_pow_pos]

/-- **Back to the view.** -/
theorem back_phase {N : ℕ} (hN : count (NodeBank.tapes rev97m) + 22 ≤ N) (v : Descriptor) {r : ℕ}
    (hr : r ≤ v.width) :
    Phase (padProgram (placed backList backRoute backRoute_inj).program hN)
      (B f p node v.width c st N) (low prime r v) v Eq (costs prime backList (backIn v r)) := by
  refine switch_phase hN (low_volume hr) _ _ _ (back_pres v hr) (back_exec v r)
    (fun i => ?_) (fun i => ?_) (fun j hj => ?_)
  · fin_cases i <;> simp [words, backIn, sel, backRoute, Slot.value, Routines.hdr, RecursiveDimensionBank.values,
      low]
  · fin_cases i <;> simp [words, backOut, sel, backRoute, Slot.value, Routines.hdr, RecursiveDimensionBank.values]
  · fin_cases j
    · simp [Routines.hdr, RecursiveDimensionBank.values, low]
    · simp [Routines.hdr, RecursiveDimensionBank.values, low]
    · exact absurd rfl (hj 3)
    · exact absurd rfl (hj 4)
    · exact absurd rfl (hj 5)
    · simp [Routines.hdr, RecursiveDimensionBank.values, low]

theorem back_cost {v : Descriptor} (hp : v.Positive) {r : ℕ} (hr : r ≤ v.width) :
    costs prime backList (backIn v r) ≤ 10001 * 48 * volume prime v := by
  have hV := RecursiveAffinePrepare.volume_positive (Nat.Prime.two_le Networks.Shared50ModularControl.prime_prime) v hp
  have hm : v.width - r ≤ v.width := Nat.sub_le _ _
  have h := costs_le (l := backList) (M := volume prime v) (s := backIn v r) (by
      intro i x hx
      fin_cases i <;> simp [backIn] at hx <;> subst hx
      · exact beforeH_pow_le hp hm
      · exact hr.trans (width_le hp)
      · exact between_pow_le hp hm
      · exact width_le hp)
    (by simp [Straight.OkAll, Straight.Ok, Straight.exec1, Straight.val, backList, backIn,
      pow_le hp hm])
  rw [show backList.length = 16 from rfl] at h
  nlinarith

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Switch
