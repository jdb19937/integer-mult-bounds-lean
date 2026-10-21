module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Prepare

/-!
# The counters of a leaf and the headers of a sub-view

A leaf runs on the view `sub s 1` of the last remaining leaf pair: before it, the counters get
its offset `s = r - 1` (with `r` leaves remaining), count `1` and rest `e = n - s - 1`
(`offsets_runs`); after it, `r - 1` leaves remain and the three are erased (`advance_runs`).
`view_runs` installs the headers of the view `sub s c` with `Headers.program`, reading the atom
width and the three counters.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafRoutines

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs)
open CommonBank (bank Target word K)
open Routines (sel routine_runs canon)
open RecursiveInterchangeLayout (Descriptor volume)

variable {t : ℕ}

theorem quot_bits (n : ℕ) : RecursiveChildQuotientsConstant.bits n = bits n :=
  RecursiveChildQuotientsConstant.bits_eq_advance n

/-! ### The leaf's offsets -/

def offsetsRoute : Fin 22 → Option (Target 22) :=
  ![none, none, none, some (.aux 9), some (.aux 11), some (.aux 15), some (.aux 12), some (.aux 13),
    none, none, none, none, some (.aux 14), none, none, none, none, none, none, none, none, none]

theorem offsetsRoute_inj : Function.Injective (sel offsetsRoute) := by decide

def offsetsProgram :=
  seq (seq (seq (Arith.diffAt (q := prime) 4 5 6 (by decide)) (Headers.copyAt (q := prime) 5 7 (by decide)))
    (Arith.rest (q := prime))) (Headers.eraseAt (q := prime) 11)

def offsets : Graph.Block (CommonBank.count t) prime :=
  Embed.place (u := CommonBank.count t) offsetsProgram (fun i => (sel offsetsRoute i).slot (t := t))
    ((Routines.slot_injective 22).comp offsetsRoute_inj) (Nat.add_comm _ _)

variable {roles : Tapes t prime} {hs : Fin 6 → List Bool} {f : ℤ → Fin (prime+4)} {p : ℤ}
  {node scalar : Tapes 1 prime} {c : Fin K → Option ℕ} {st : Tapes 2 prime}

/-- **The leaf's offsets**: `s = r - 1`, `c = 1` and `e = n - s - 1`. -/
theorem offsets_runs {n r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) (h9 : c 9 = some n) (h11 : c 11 = some r)
    (h15 : c 15 = some 1) (h12 : c 12 = none) (h13 : c 13 = none) (h14 : c 14 = none) :
    ∃ B ≤ 30 * n + 130, Runs offsets (bank roles hs f p node scalar c st)
      (bank roles hs f p node scalar (Function.update (Function.update (Function.update c 12 (some (r - 1)))
        13 (some 1)) 14 (some (n - (r - 1) - 1))) st) B := by
  set d := fun i => (sel offsetsRoute i).value hs c
  have d3 : d 3 = some (bits n) := by simp [d, sel, offsetsRoute, Target.value, h9, word]
  have d4 : d 4 = some (bits r) := by simp [d, sel, offsetsRoute, Target.value, h11, word]
  have d5 : d 5 = some (bits 1) := by simp [d, sel, offsetsRoute, Target.value, h15, word]
  have d6 : d 6 = none := by simp [d, sel, offsetsRoute, Target.value, h12, word]
  have d7 : d 7 = none := by simp [d, sel, offsetsRoute, Target.value, h13, word]
  have d11 : d 11 = none := rfl
  have d12 : d 12 = none := by simp [d, sel, offsetsRoute, Target.value, h14, word]
  have hv (x : ℕ) := FlatCoordinateSchedule.bits_value x
  have hcb (x : ℕ) := FlatCoordinateSchedule.bits_canonical x
  have s1 := Arith.difference_hoare (q := prime) (d := d) (x := 4) (y := 5) (o := 6) (by decide)
    (xs := bits r) (ys := bits 1) (by rw [hv, hv]; exact hr) (hcb r) (hcb 1) d4 d5 d6
  rw [hv, hv, quot_bits] at s1
  have s2 := Headers.copy_step (q := prime) (d := Function.update d 6 (some (bits (r - 1))))
    (src := 5) (dst := 7) (by decide) (xs := bits 1) (by simp [Function.update, d5])
    (by simp [Function.update, d7])
  have s3 := Arith.rest_hoare (q := prime)
    (d := Function.update (Function.update d 6 (some (bits (r - 1)))) 7 (some (bits 1)))
    (ns := bits n) (ss := bits (r - 1)) (cs := bits 1) (n := n) (s := r - 1) (c := 1)
    (by omega) (hv n) (hv _) (hv 1) (hcb n) (hcb _) (hcb 1)
    (by simp [Function.update, d3]) (by simp [Function.update]) (by simp [Function.update])
    (by simp [Function.update, d11]) (by simp [Function.update, d12])
  rw [quot_bits, quot_bits] at s3
  have s4 := Headers.erase_step (q := prime)
    (d := Function.update (Function.update (Function.update (Function.update d 6 (some (bits (r - 1)))) 7
      (some (bits 1))) 11 (some (bits (n - (r - 1))))) 12 (some (bits (n - (r - 1) - 1))))
    (j := 11) (xs := bits (n - (r - 1))) (by simp [Function.update])
  refine ⟨_, ?_, routine_runs offsetsRoute offsetsRoute_inj (((s1.seq s2).seq s3).seq s4) hs _
    (fun i => ?_) (fun j _ => rfl) (fun j hj => ?_)⟩
  · have hl := GrowingCounterData.canonical_width _ (hcb (n - (r - 1)))
    have hl2 := Nat.log2_le_self (Counter.value (bits (n - (r - 1))))
    have hl1 : (bits 1).length = 1 := rfl
    rw [hv] at hl hl2
    omega
  · fin_cases i <;> simp [d, sel, offsetsRoute, Target.value, word, Function.update, h9, h11, h15]
  · have h₁ : j ≠ 12 := fun h => hj 6 (by rw [h]; rfl)
    have h₂ : j ≠ 13 := fun h => hj 7 (by rw [h]; rfl)
    have h₃ : j ≠ 14 := fun h => hj 12 (by rw [h]; rfl)
    rw [Function.update_of_ne h₃, Function.update_of_ne h₂, Function.update_of_ne h₁]

/-! ### One leaf fewer -/

def advanceRoute : Fin 22 → Option (Target 22) :=
  ![some (.aux 11), some (.aux 12), some (.aux 13), some (.aux 14), none, none, none, none, none, none,
    none, none, none, none, none, none, none, none, none, none, none, none]

theorem advanceRoute_inj : Function.Injective (sel advanceRoute) := by decide

def advanceProgram :=
  seq (seq (seq (seq (Headers.eraseAt (q := prime) 0) (Headers.copyAt (q := prime) 1 0 (by decide)))
    (Headers.eraseAt (q := prime) 1)) (Headers.eraseAt (q := prime) 2)) (Headers.eraseAt (q := prime) 3)

def advance : Graph.Block (CommonBank.count t) prime :=
  Embed.place (u := CommonBank.count t) advanceProgram (fun i => (sel advanceRoute i).slot (t := t))
    ((Routines.slot_injective 22).comp advanceRoute_inj) (Nat.add_comm _ _)

/-- **One leaf fewer**: the offset becomes the remaining leaves; the offsets are erased. -/
theorem advance_runs {r s cc e : ℕ} (hsr : s ≤ r) (hcr : cc ≤ r) (her : e ≤ r)
    (h11 : c 11 = some r) (h12 : c 12 = some s) (h13 : c 13 = some cc) (h14 : c 14 = some e) :
    ∃ B ≤ 20 * r + 40, Runs advance (bank roles hs f p node scalar c st)
      (bank roles hs f p node scalar (Function.update (Function.update (Function.update
        (Function.update c 11 (some s)) 12 none) 13 none) 14 none) st) B := by
  set d := fun i => (sel advanceRoute i).value hs c
  have e0 := Headers.erase_step (q := prime) (d := d) (j := 0) (xs := bits r)
    (by simp [d, sel, advanceRoute, Target.value, h11, word])
  have e1 := Headers.copy_step (q := prime) (d := Function.update d 0 none) (src := 1) (dst := 0) (by decide)
    (xs := bits s) (by simp [d, sel, advanceRoute, Target.value, h12, word, Function.update]) (by simp)
  have e2 := Headers.erase_step (q := prime) (d := Function.update (Function.update d 0 none) 0 (some (bits s)))
    (j := 1) (xs := bits s) (by simp [d, sel, advanceRoute, Target.value, h12, word, Function.update])
  have e3 := Headers.erase_step (q := prime)
    (d := Function.update (Function.update (Function.update d 0 none) 0 (some (bits s))) 1 none)
    (j := 2) (xs := bits cc) (by simp [d, sel, advanceRoute, Target.value, h13, word, Function.update])
  have e4 := Headers.erase_step (q := prime)
    (d := Function.update (Function.update (Function.update (Function.update d 0 none) 0 (some (bits s))) 1 none)
      2 none)
    (j := 3) (xs := bits e) (by simp [d, sel, advanceRoute, Target.value, h14, word, Function.update])
  have hl (x : ℕ) : (bits x).length ≤ x + 1 := by
    have h1 := GrowingCounterData.canonical_width _ (FlatCoordinateSchedule.bits_canonical x)
    have h2 := Nat.log2_le_self (Counter.value (bits x))
    rw [FlatCoordinateSchedule.bits_value] at h1 h2
    omega
  refine ⟨_, ?_, routine_runs advanceRoute advanceRoute_inj ((((e0.seq e1).seq e2).seq e3).seq e4) hs _
    (fun i => ?_) (fun j _ => rfl) (fun j hj => ?_)⟩
  · have := hl r; have := hl s; have := hl cc; have := hl e
    omega
  · fin_cases i <;> simp [d, sel, advanceRoute, Target.value, word, Function.update]
  · have h₁ : j ≠ 11 := fun h => hj 0 (by rw [h]; rfl)
    have h₂ : j ≠ 12 := fun h => hj 1 (by rw [h]; rfl)
    have h₃ : j ≠ 13 := fun h => hj 2 (by rw [h]; rfl)
    have h₄ : j ≠ 14 := fun h => hj 3 (by rw [h]; rfl)
    rw [Function.update_of_ne h₄, Function.update_of_ne h₃, Function.update_of_ne h₂, Function.update_of_ne h₁]

/-! ### The headers of a sub-view -/

def viewRoute : Fin 22 → Option (Target 22) :=
  ![none, none, none, some (.header 0), some (.header 1), some (.header 2), some (.header 3),
    some (.header 4), some (.header 5), some (.aux 0), some (.aux 12), some (.aux 13), some (.aux 14),
    none, none, none, none, none, none, none, none, none]

theorem viewRoute_inj : Function.Injective (sel viewRoute) := by decide

def view : Graph.Block (CommonBank.count t) prime :=
  Embed.place (u := CommonBank.count t) (Headers.program Networks.Shared50ModularControl.prime_prime.two_le)
    (fun i => (sel viewRoute i).slot (t := t)) ((Routines.slot_injective 22).comp viewRoute_inj) (Nat.add_comm _ _)

/-- **A sub-view's headers**, from the atom width and the offset, count and rest counters. -/
theorem view_runs {v : Descriptor} {b n s cc e : ℕ} (hv : RecursiveDimensionBank.Headers v hs)
    (hpos : v.Positive) (hb : 0 < b) (hw : v.width = n * b) (hsc : s + cc ≤ n) (he : e = n - s - cc)
    (h0 : c 0 = some b) (h12 : c 12 = some s) (h13 : c 13 = some cc) (h14 : c 14 = some e) :
    Runs view (bank roles hs f p node scalar c st)
      (bank roles (Headers.childHeaders (q := prime) v hs b s cc e) f p node scalar c st) (1500 * volume prime v) := by
  have hcb (x : ℕ) := FlatCoordinateSchedule.bits_canonical x
  have hv' (x : ℕ) := FlatCoordinateSchedule.bits_value x
  have h := Headers.prepares Networks.Shared50ModularControl.prime_prime.two_le hv hpos hb hw hsc he
    (hv' b) (hv' s) (hv' cc) (hv' e) (hcb b) (hcb s) (hcb cc) (hcb e)
  have hin : (fun i => (sel viewRoute i).value hs c) = Headers.inputs hs (bits b) (bits s) (bits cc) (bits e) := by
    funext i; fin_cases i <;> simp [sel, viewRoute, Target.value, word, Headers.inputs, h0, h12, h13, h14]
  rw [← hin] at h
  refine routine_runs viewRoute viewRoute_inj h _ c (fun i => ?_) (fun j hj => ?_) (fun j _ => rfl)
  · fin_cases i <;> simp [sel, viewRoute, Target.value, word, Headers.inputs, h0, h12, h13, h14]
  · exact absurd (by fin_cases j <;> decide) (fun h : ∃ i, sel viewRoute i = .header j => by
      obtain ⟨i, hi⟩ := h; exact hj i hi)

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.LeafRoutines
