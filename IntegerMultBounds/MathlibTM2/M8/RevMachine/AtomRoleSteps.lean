module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleLoop
public import IntegerMultBounds.Machine.CounterSteps

/-!
# Counter steps between atom levels

The five position counters sit on the role bank's first auxiliary tapes. An increment or a
decrement changes one counter in place (`inc_level`, `dec_level`), the decrement using two private
tapes of the machine as scratch, which are blank at every level. Three fixed step programs move the
counters of the three level families to the next level:
* cross selections whose two positions both advance (`crossSteps`): scalings and cross shifts;
* within-field selections whose two positions both advance (`withinSteps`);
* cross selections whose head position retreats while the tail position advances (`revSteps`),
  the reversed head read of the twisted shift.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSteps

open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewRoleBank (Selection)
open RecursiveViewFrameRoleBank (count bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
open SharedPlacementAlphabet (setTape)
open FlatCoordinateSchedule (bits)
open AtomRoleLoop (levelBank)
variable {t u : ℕ}
noncomputable section

theorem raw_setTape {k T : ℕ} (c : Tapes k prime) (i : Fin T) (hi : i.val < k) (f : ℤ → Fin (prime+4))
    (p : ℤ) : setTape (raw c T) i f p = raw (setTape c ⟨i.val, hi⟩ f p) T := by
  unfold raw setTape
  apply congrArg₂ Tapes.mk <;> funext j <;> by_cases hj : j = i
  · subst hj; simp [hi]
  · have hne : ∀ h : j.val < k, (⟨j.val, h⟩ : Fin k) ≠ ⟨i.val, hi⟩ := fun h he =>
      hj (Fin.ext (by simpa using congrArg Fin.val he))
    by_cases hjk : j.val < k <;> simp [Function.update_of_ne hj, hjk, Function.update_of_ne (hne _)]
  · subst hj; simp [hi]
  · have hne : ∀ h : j.val < k, (⟨j.val, h⟩ : Fin k) ≠ ⟨i.val, hi⟩ := fun h he =>
      hj (Fin.ext (by simpa using congrArg Fin.val he))
    by_cases hjk : j.val < k <;> simp [Function.update_of_ne hj, hjk, Function.update_of_ne (hne _)]

section Slots

variable (T : ℕ) (hT : count t (5+u) + 2 ≤ T)
include hT

/-- Counter `z` on the machine's tapes. -/
def cslot (z : Fin 5) : Fin T := ⟨t+8+z.val, by unfold count at hT; omega⟩
/-- The two scratch tapes of a decrement: private, hence blank. -/
def oslot : Fin T := ⟨count t (5+u), by omega⟩
def zslot : Fin T := ⟨count t (5+u)+1, by omega⟩

omit hT in
theorem port_val (z : Fin 5) :
    (Fin.natAdd t (Fin.natAdd 7 (Fin.natAdd 1 (Fin.castAdd u z))) : Fin (count t (5+u))).val =
      t+8+z.val := by
  simp only [Fin.val_natAdd, Fin.val_castAdd]; omega

theorem bank_port (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (data : RecursiveViewedAction.Data t v) (ws : Fin 5 → List Bool) (z : Fin 5) :
    (levelBank T hs aux data ws).head (cslot T hT z) = 1 ∧
      (levelBank T hs aux data ws).tape (cslot T hT z) = RadixZeroFill.encodedBinary (ws z) := by
  have hk : t+8+z.val < count t (5+u) := by unfold count; omega
  have he : (⟨t+8+z.val, hk⟩ : Fin (count t (5+u))) =
      Fin.natAdd t (Fin.natAdd 7 (Fin.natAdd 1 (Fin.castAdd u z))) := Fin.ext (port_val z).symm
  simp only [levelBank, raw, cslot, hk, dite_true]
  rw [he]
  simp [bank, RecursiveShiftRoleBank.common, Tapes.append, Fin.addCases_left, Fin.addCases_right,
    AtomView.counters]

theorem bank_scratch (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (data : RecursiveViewedAction.Data t v) (ws : Fin 5 → List Bool) :
    (levelBank T hs aux data ws).head (oslot T hT) = 0 ∧
      (levelBank T hs aux data ws).tape (oslot T hT) = (fun _ => blank) ∧
      (levelBank T hs aux data ws).head (zslot T hT) = 0 ∧
      (levelBank T hs aux data ws).tape (zslot T hT) = (fun _ => blank) := by
  simp [levelBank, raw, oslot, zslot]

theorem bank_set (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (data : RecursiveViewedAction.Data t v) (ws : Fin 5 → List Bool) (z : Fin 5) (w : List Bool) :
    setTape (levelBank T hs aux data ws) (cslot T hT z) (RadixZeroFill.encodedBinary w) 1 =
      levelBank T hs aux data (Function.update ws z w) := by
  have hk : t+8+z.val < count t (5+u) := by unfold count; omega
  have he : (⟨t+8+z.val, hk⟩ : Fin (count t (5+u))) =
      Fin.natAdd t (Fin.natAdd 7 (Fin.natAdd 1 (Fin.castAdd u z))) := Fin.ext (port_val z).symm
  have hc : setTape (bank (roles data) hs (SharedBank.empty 1 prime) ((AtomView.counters ws).append aux))
      ⟨t+8+z.val, hk⟩ (RadixZeroFill.encodedBinary w) 1 =
      bank (roles data) hs (SharedBank.empty 1 prime)
        ((AtomView.counters (Function.update ws z w)).append aux) := by
    rw [he]
    unfold bank RecursiveShiftRoleBank.common
    rw [SharedPlacementAlphabet.setTape_append_right, SharedPlacementAlphabet.setTape_append_right,
      SharedPlacementAlphabet.setTape_append_right, SharedPlacementAlphabet.setTape_append_left]
    congr 4
    unfold AtomView.counters setTape
    apply congrArg₂ Tapes.mk <;> funext y <;> by_cases hy : y = z
    · subst hy; simp
    · simp [Function.update_of_ne hy]
    · subst hy; simp
    · simp [Function.update_of_ne hy]
  unfold levelBank
  rw [raw_setTape _ _ hk, ← hc]
  rfl

theorem cslot_ne_o (z : Fin 5) : cslot T hT z ≠ oslot T hT := by
  intro h; have := congrArg Fin.val h; simp [cslot, oslot, count] at this; omega

theorem cslot_ne_z (z : Fin 5) : cslot T hT z ≠ zslot T hT := by
  intro h; have := congrArg Fin.val h; simp [cslot, zslot, count] at this; omega

theorem o_ne_z : oslot T hT ≠ zslot T hT := by
  intro h; have := congrArg Fin.val h; simp [oslot, zslot] at this

theorem inc_level (hs : Fin 6 → List Bool) (aux : Tapes u prime) (data : RecursiveViewedAction.Data t v)
    (ws : Fin 5 → List Bool) (z : Fin 5) (n : ℕ) (hz : ws z = bits n) :
    HoareTime (CounterSteps.incProgram (a := prime) (cslot T hT z))
      (fun x => x = levelBank T hs aux data ws)
      (fun x => x = levelBank T hs aux data (Function.update ws z (bits (n+1)))) (2*n+4) := by
  have hp := bank_port T hT hs aux data ws z
  rw [hz] at hp
  rw [← bank_set T hT]
  exact CounterSteps.inc_hoare _ _ n hp.2 hp.1

theorem dec_level (hs : Fin 6 → List Bool) (aux : Tapes u prime) (data : RecursiveViewedAction.Data t v)
    (ws : Fin 5 → List Bool) (z : Fin 5) (n : ℕ) (hn : 1 ≤ n) (hz : ws z = bits n) :
    HoareTime (CounterSteps.decProgram (a := prime) (cslot T hT z) (oslot T hT) (zslot T hT)
        (cslot_ne_o T hT z) (cslot_ne_z T hT z) (o_ne_z T hT))
      (fun x => x = levelBank T hs aux data ws)
      (fun x => x = levelBank T hs aux data (Function.update ws z (bits (n-1)))) (20*n+80) := by
  have hp := bank_port T hT hs aux data ws z
  rw [hz] at hp
  have hsc := bank_scratch T hT hs aux data ws
  rw [← bank_set T hT]
  exact CounterSteps.dec_hoare _ _ _ _ n hn hp.2 hp.1 hsc.2.1 hsc.1 hsc.2.2.2 hsc.2.2.1

/-! ### The three step programs -/

/-- Both positions of a cross selection advance. -/
def crossSteps :=
  seq (seq (seq (CounterSteps.incProgram (a := prime) (cslot T hT 1))
    (CounterSteps.decProgram (a := prime) (cslot T hT 2) (oslot T hT) (zslot T hT)
      (cslot_ne_o T hT 2) (cslot_ne_z T hT 2) (o_ne_z T hT)))
    (CounterSteps.incProgram (a := prime) (cslot T hT 3)))
    (CounterSteps.decProgram (a := prime) (cslot T hT 4) (oslot T hT) (zslot T hT)
      (cslot_ne_o T hT 4) (cslot_ne_z T hT 4) (o_ne_z T hT))

/-- Both positions of a within-field selection advance. -/
def withinSteps :=
  seq (CounterSteps.incProgram (a := prime) (cslot T hT 1))
    (CounterSteps.decProgram (a := prime) (cslot T hT 3) (oslot T hT) (zslot T hT)
      (cslot_ne_o T hT 3) (cslot_ne_z T hT 3) (o_ne_z T hT))

/-- The head position of a cross selection retreats, the tail position advances. -/
def revSteps :=
  seq (seq (seq (CounterSteps.decProgram (a := prime) (cslot T hT 1) (oslot T hT) (zslot T hT)
      (cslot_ne_o T hT 1) (cslot_ne_z T hT 1) (o_ne_z T hT))
    (CounterSteps.incProgram (a := prime) (cslot T hT 2)))
    (CounterSteps.incProgram (a := prime) (cslot T hT 3)))
    (CounterSteps.decProgram (a := prime) (cslot T hT 4) (oslot T hT) (zslot T hT)
      (cslot_ne_o T hT 4) (cslot_ne_z T hT 4) (o_ne_z T hT))

variable {N : ℕ} (b : ℕ) (hs : Fin 6 → List Bool) (aux : Tapes u prime)
  (data : RecursiveViewedAction.Data t v)

/-- The step cost bound. -/
def stepCost (N : ℕ) : ℕ := 50*N+400

theorem cross_steps (i j : ℕ) (hi : i+1 < N) (hj : j+1 < N) :
    HoareTime (crossSteps T hT)
      (fun x => x = levelBank T hs aux data
        (AtomStep.words b (.cross (⟨i, by omega⟩ : Fin N) (⟨j, by omega⟩ : Fin N))))
      (fun x => x = levelBank T hs aux data
        (AtomStep.words b (.cross (⟨i+1, hi⟩ : Fin N) (⟨j+1, hj⟩ : Fin N))))
      (stepCost N) := by
  let w0 := AtomStep.words b (.cross (⟨i, by omega⟩ : Fin N) (⟨j, by omega⟩ : Fin N))
  let w1 := Function.update w0 1 (bits (i+1))
  let w2 := Function.update w1 2 (bits (N-1-i-1))
  let w3 := Function.update w2 3 (bits (j+1))
  have s1 := inc_level T hT hs aux data w0 1 i (by simp [w0, AtomStep.words])
  have s2 := dec_level T hT hs aux data w1 2 (N-1-i) (by omega) (by simp [w1, w0, AtomStep.words])
  have s3 := inc_level T hT hs aux data w2 3 j (by simp [w2, w1, w0, AtomStep.words, Function.update])
  have s4 := dec_level T hT hs aux data w3 4 (N-1-j) (by omega)
    (by simp [w3, w2, w1, w0, AtomStep.words, Function.update])
  refine (((s1.seq s2).seq s3).seq s4).consequence (fun _ h => h) (fun x hx => hx.trans ?_) ?_
  · congr 1
    funext z; fin_cases z <;> simp [w3, w2, w1, w0, AtomStep.words, Function.update]
    all_goals congr 1
  · unfold stepCost; omega

theorem within_steps (g : RecursiveAffineDimensions.Group) (j i : ℕ) (hji : j < i) (hi : i+1 < N) :
    HoareTime (withinSteps T hT)
      (fun x => x = levelBank T hs aux data (AtomStep.words b
        (.within g (⟨j, by omega⟩ : Fin N) (⟨i, by omega⟩ : Fin N) (by simpa using hji))))
      (fun x => x = levelBank T hs aux data (AtomStep.words b
        (.within g (⟨j+1, by omega⟩ : Fin N) (⟨i+1, hi⟩ : Fin N) (by simpa using hji))))
      (stepCost N) := by
  let w0 := AtomStep.words b (.within g (⟨j, by omega⟩ : Fin N) (⟨i, by omega⟩ : Fin N) (by simpa using hji))
  let w1 := Function.update w0 1 (bits (j+1))
  have s1 := inc_level T hT hs aux data w0 1 j (by simp [w0, AtomStep.words])
  have s2 := dec_level T hT hs aux data w1 3 (N-1-i) (by omega) (by simp [w1, w0, AtomStep.words])
  refine (s1.seq s2).consequence (fun _ h => h) (fun x hx => hx.trans ?_) ?_
  · congr 1
    funext z; fin_cases z <;> simp [w1, w0, AtomStep.words, Function.update]
    all_goals congr 1
  · unfold stepCost; omega

theorem rev_steps (i j : ℕ) (hi0 : 1 ≤ i) (hi : i < N) (hj : j+1 < N) :
    HoareTime (revSteps T hT)
      (fun x => x = levelBank T hs aux data
        (AtomStep.words b (.cross (⟨i, hi⟩ : Fin N) (⟨j, by omega⟩ : Fin N))))
      (fun x => x = levelBank T hs aux data
        (AtomStep.words b (.cross (⟨i-1, by omega⟩ : Fin N) (⟨j+1, hj⟩ : Fin N))))
      (stepCost N) := by
  let w0 := AtomStep.words b (.cross (⟨i, hi⟩ : Fin N) (⟨j, by omega⟩ : Fin N))
  let w1 := Function.update w0 1 (bits (i-1))
  let w2 := Function.update w1 2 (bits (N-1-i+1))
  let w3 := Function.update w2 3 (bits (j+1))
  have s1 := dec_level T hT hs aux data w0 1 i hi0 (by simp [w0, AtomStep.words])
  have s2 := inc_level T hT hs aux data w1 2 (N-1-i) (by simp [w1, w0, AtomStep.words])
  have s3 := inc_level T hT hs aux data w2 3 j (by simp [w2, w1, w0, AtomStep.words, Function.update])
  have s4 := dec_level T hT hs aux data w3 4 (N-1-j) (by omega)
    (by simp [w3, w2, w1, w0, AtomStep.words, Function.update])
  refine (((s1.seq s2).seq s3).seq s4).consequence (fun _ h => h) (fun x hx => hx.trans ?_) ?_
  · congr 1
    funext z; fin_cases z <;> simp [w3, w2, w1, w0, AtomStep.words, Function.update]
    all_goals (congr 1; all_goals omega)
  · unfold stepCost; omega

end Slots

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRoleSteps
