module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Routines

/-!
# The preparation of a call

A call of the family enters with the view's headers, the atom width `b`, the cutoff `m` and the
constant one on its counters (`rest`). The preparation divides the width header by `b` into the
atom count `n` (`atoms_runs`), then `n` by `m` into the atoms per coordinate `f = ⌊n/m⌋` and the
remaining leaves `δ = n mod m` (`split_runs`).

Counters: `0` the atom width, `1..4` the atom positions, `5` the atoms per coordinate, `6` the
clock, `7` the loop clock, `8` the loop count, `9` the atom count, `10` the cutoff, `11` the
remaining leaves, `12, 13, 14` a view's offset, count and rest, `15` the constant one.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Prepare

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs)
open CommonBank (bank Target word K)
open Routines (sel routine_runs canon)

variable {t : ℕ}

/-- The counters at a call's entry. -/
def rest (b m : ℕ) : Fin K → Option ℕ :=
  ![some b, some 0, some 0, some 0, some 0, none, none, some 0, none, none, some m, none, none, none,
    none, some 1, none, none, none, none, none, none, none, none]

/-! ### The atom count -/

def atomsRoute : Fin 22 → Option (Target 22) :=
  ![none, none, none, some (.header 3), some (.aux 0), none, none, none, some (.aux 9), none, none,
    none, none, none, none, none, none, none, none, none, none, none]

theorem atomsRoute_inj : Function.Injective (sel atomsRoute) := by decide

def atomsProgram := seq (Arith.split (q := prime)) (Headers.eraseAt (q := prime) 9)

/-- The atom-count block. -/
def atoms : Graph.Block (CommonBank.count t) prime :=
  Embed.place (u := CommonBank.count t) atomsProgram (fun i => (sel atomsRoute i).slot (t := t))
    ((Routines.slot_injective 22).comp atomsRoute_inj) (Nat.add_comm _ _)

variable {roles : Tapes t prime} {hs : Fin 6 → List Bool} {f : ℤ → Fin (prime+4)} {p : ℤ}
  {node scalar : Tapes 1 prime} {c : Fin K → Option ℕ} {st : Tapes 2 prime}

/-- **The atom count**: `n = w / b` from the width header `w` and the atom width `b`. -/
theorem atoms_runs {w b : ℕ} (hb : 0 < b) (hw : Counter.value (hs 3) = w)
    (hcw : GrowingCounterData.Canonical (hs 3)) (h0 : c 0 = some b) (h9 : c 9 = none) :
    ∃ B ≤ BinaryDescriptorDivMod.linearConstant (bits b) * (w + 1) + 2 * b + 6,
      Runs atoms (bank roles hs f p node scalar c st)
        (bank roles hs f p node scalar (Function.update c 9 (some (w / b))) st) B := by
  have hd0 : 0 < Counter.value (bits b) := by rw [FlatCoordinateSchedule.bits_value]; exact hb
  obtain ⟨zs, rs, cz, cr, vz, vr, h⟩ := Arith.split_hoare (q := prime)
    (d := fun i => (sel atomsRoute i).value hs c) hd0 rfl (by simp [sel, atomsRoute, Target.value, h0, word])
    (by simp [sel, atomsRoute, Target.value, h9, word]) rfl
    (by intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have he := Headers.erase_step (q := prime)
    (d := Function.update (Function.update (fun i => (sel atomsRoute i).value hs c) 8 (some zs)) 9 (some rs))
    (j := 9) (xs := rs) (by simp)
  refine ⟨_, ?_, routine_runs atomsRoute atomsRoute_inj (h.seq he) hs _ (fun i => ?_) (fun j _ => rfl)
    (fun j hj => ?_)⟩
  · have h1 := BinaryDescriptorDivMod.cost_linear (hs 3) (bits b) hcw
    have h2 := GrowingCounterData.canonical_width rs cr
    have h3 : Counter.value rs < b := by
      rw [vr, FlatCoordinateSchedule.bits_value]; exact Nat.mod_lt _ hb
    have h4 := Nat.log2_le_self (Counter.value rs)
    rw [hw] at h1
    omega
  · have hz : zs = bits (w / b) := (canon cz).trans (by rw [vz, hw, FlatCoordinateSchedule.bits_value])
    rw [hz]
    fin_cases i <;> simp [sel, atomsRoute, Target.value, word, Function.update]
  · have : j ≠ 9 := fun h => hj 8 (by rw [h]; rfl)
    exact Function.update_of_ne this _ _

/-! ### The atoms per coordinate and the remaining leaves -/

def divideRoute : Fin 22 → Option (Target 22) :=
  ![none, none, none, some (.aux 9), some (.aux 10), none, none, none, some (.aux 5), some (.aux 11),
    none, none, none, none, none, none, none, none, none, none, none, none]

theorem divideRoute_inj : Function.Injective (sel divideRoute) := by decide

/-- The division block. -/
def divide : Graph.Block (CommonBank.count t) prime :=
  Embed.place (u := CommonBank.count t) (Arith.split (q := prime)) (fun i => (sel divideRoute i).slot (t := t))
    ((Routines.slot_injective 22).comp divideRoute_inj) (Nat.add_comm _ _)

/-- **The division**: `f = ⌊n/m⌋` and `δ = n mod m`. -/
theorem divide_runs {n m : ℕ} (hm : 0 < m) (h9 : c 9 = some n) (h10 : c 10 = some m)
    (h5 : c 5 = none) (h11 : c 11 = none) :
    ∃ B ≤ BinaryDescriptorDivMod.linearConstant (bits m) * (n + 1),
      Runs divide (bank roles hs f p node scalar c st)
        (bank roles hs f p node scalar (Function.update (Function.update c 5 (some (n / m))) 11
          (some (n % m))) st) B := by
  have hd0 : 0 < Counter.value (bits m) := by rw [FlatCoordinateSchedule.bits_value]; exact hm
  obtain ⟨zs, rs, cz, cr, vz, vr, h⟩ := Arith.split_hoare (q := prime)
    (d := fun i => (sel divideRoute i).value hs c) (ys := bits n) hd0
    (by simp [sel, divideRoute, Target.value, h9, word]) (by simp [sel, divideRoute, Target.value, h10, word])
    (by simp [sel, divideRoute, Target.value, h5, word]) (by simp [sel, divideRoute, Target.value, h11, word])
    (by intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine ⟨_, ?_, routine_runs divideRoute divideRoute_inj h hs _ (fun i => ?_) (fun j _ => rfl)
    (fun j hj => ?_)⟩
  · have h1 := BinaryDescriptorDivMod.cost_linear (bits n) (bits m) (FlatCoordinateSchedule.bits_canonical n)
    rwa [FlatCoordinateSchedule.bits_value] at h1
  · have hz : zs = bits (n / m) := (canon cz).trans (by simp only [vz, FlatCoordinateSchedule.bits_value])
    have hr : rs = bits (n % m) := (canon cr).trans (by simp only [vr, FlatCoordinateSchedule.bits_value])
    rw [hz, hr]
    fin_cases i <;> simp [sel, divideRoute, Target.value, word, Function.update]
  · have h₁ : j ≠ 5 := fun h => hj 8 (by rw [h]; rfl)
    have h₂ : j ≠ 11 := fun h => hj 9 (by rw [h]; rfl)
    rw [Function.update_of_ne h₂, Function.update_of_ne h₁]

/-! ### The finish -/

def finishRoute : Fin 22 → Option (Target 22) :=
  ![some (.aux 5), some (.aux 9), some (.aux 11), none, none, none, none, none, none, none, none,
    none, none, none, none, none, none, none, none, none, none, none]

theorem finishRoute_inj : Function.Injective (sel finishRoute) := by decide

def finishProgram :=
  seq (seq (Headers.eraseAt (q := prime) 0) (Headers.eraseAt (q := prime) 1)) (Headers.eraseAt (q := prime) 2)

/-- The finish block: erase the atoms per coordinate, the atom count and the remaining leaves. -/
def finish : Graph.Block (CommonBank.count t) prime :=
  Embed.place (u := CommonBank.count t) finishProgram (fun i => (sel finishRoute i).slot (t := t))
    ((Routines.slot_injective 22).comp finishRoute_inj) (Nat.add_comm _ _)

theorem finish_runs {f' n r : ℕ} (h5 : c 5 = some f') (h9 : c 9 = some n) (h11 : c 11 = some r) :
    Runs finish (bank roles hs f p node scalar c st)
      (bank roles hs f p node scalar (Function.update (Function.update (Function.update c 5 none) 9 none)
        11 none) st)
      ((2*(bits f').length+4) + (2*(bits n).length+4) + 1 + (2*(bits r).length+4) + 1) := by
  have e0 := Headers.erase_step (q := prime) (d := fun i => (sel finishRoute i).value hs c) (j := 0)
    (xs := bits f') (by simp [sel, finishRoute, Target.value, h5, word])
  have e1 := Headers.erase_step (q := prime)
    (d := Function.update (fun i => (sel finishRoute i).value hs c) 0 none) (j := 1)
    (xs := bits n) (by simp [sel, finishRoute, Target.value, h9, word])
  have e2 := Headers.erase_step (q := prime)
    (d := Function.update (Function.update (fun i => (sel finishRoute i).value hs c) 0 none) 1 none) (j := 2)
    (xs := bits r) (by simp [sel, finishRoute, Target.value, h11, word])
  refine (routine_runs finishRoute finishRoute_inj ((e0.seq e1).seq e2) hs _ (fun i => ?_) (fun j _ => rfl)
    (fun j hj => ?_)).consequence (fun _ h => h) (fun _ h => h) (by omega)
  · fin_cases i <;> simp [sel, finishRoute, Target.value, word, Function.update]
  · have h₁ : j ≠ 5 := fun h => hj 0 (by rw [h]; rfl)
    have h₂ : j ≠ 9 := fun h => hj 1 (by rw [h]; rfl)
    have h₃ : j ≠ 11 := fun h => hj 2 (by rw [h]; rfl)
    rw [Function.update_of_ne h₃, Function.update_of_ne h₂, Function.update_of_ne h₁]

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Prepare
