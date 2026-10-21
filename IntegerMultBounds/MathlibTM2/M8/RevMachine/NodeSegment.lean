module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SegmentBits
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.CommonBank
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Blocks

/-!
# Atom segments on the common bank

The chain of an atom segment runs on the role bank padded to `T'` tapes, with its counters and
loop count after the roles (`AtomRoleRun.common`). Its counters are the node's counters
`0..8` on the common bank: the atom width, four zero positions, the atoms per coordinate, a
blank clock, the zero loop clock and the loop count `f - 1` (`SegCounters`). `place` puts the
segment's tapes there, its other tapes on private blank tapes. `seg_runs`: a run of the
segment's bank is a run of the common bank that changes only the role tapes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSegment

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open SharedBankStageInput (raw)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs)
open CommonBank (bank K auxSlot)
open CounterDimensions (descriptorHead descriptorTape)
open RecursiveInterchangeLayout (Descriptor volume)
open CounterAdvance (addCases_val)

variable {t T' : ℕ}

/-! ### The placement -/

theorem count_val : CommonBank.count t = t + 38 := rfl

/-- Where a tape of the segment bank lives: the roles, the empty tape and the headers in place,
the counters and the atom count on counters `0..6`, the loop clock and count on `7, 8`, the rest
private. -/
def segSlot (t T' : ℕ) (i : Fin (T'+2)) : Fin (CommonBank.count t + (T'+2)) :=
  if h : i.val < t + 7 then Fin.castAdd _ ⟨i.val, by rw [count_val]; omega⟩
  else if h₂ : t + 8 ≤ i.val ∧ i.val < t + 15 then
    Fin.castAdd _ (auxSlot ⟨i.val - (t+8), by have : K = 24 := rfl; omega⟩)
  else if i.val = T' then Fin.castAdd _ (auxSlot 7)
  else if i.val = T' + 1 then Fin.castAdd _ (auxSlot 8)
  else Fin.natAdd _ i

theorem aux_val (j : ℕ) (hj : j < K) : (auxSlot (t := t) ⟨j, hj⟩).val = t + 12 + j := by
  rw [CommonBank.auxSlot_val]

theorem segSlot_val (i : Fin (T'+2)) : (segSlot t T' i).val =
    if i.val < t + 7 then i.val else if t + 8 ≤ i.val ∧ i.val < t + 15 then t + 12 + (i.val - (t+8))
    else if i.val = T' then t + 19 else if i.val = T' + 1 then t + 20 else t + 38 + i.val := by
  unfold segSlot
  split_ifs <;> simp only [Fin.val_castAdd, Fin.val_natAdd, CommonBank.auxSlot_val, count_val] <;> rfl

theorem segSlot_injective (hT : t + 15 ≤ T') : Function.Injective (segSlot t T') := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [segSlot_val, segSlot_val] at hv
  apply Fin.ext
  have := i.isLt; have := j.isLt
  split_ifs at hv <;> omega

/-- A segment program placed on the common bank. -/
def place {q : ℕ} (M : Program (T'+2) q prime) (hT : t + 15 ≤ T') : Graph.Block (CommonBank.count t) prime :=
  Embed.place (u := CommonBank.count t) M (segSlot t T') (segSlot_injective hT) (Nat.add_comm _ _)

theorem place_leading {q : ℕ} (M : Program (T'+2) q prime) (hT : t + 15 ≤ T') :
    Blocks.Leading (place M hT) := Blocks.place_leading _ _ _ _

/-- The node's counters `0..8` hold the segment's counters. -/
structure SegCounters (c : Fin K → Option ℕ) (b f : ℕ) : Prop where
  c0 : c 0 = some b
  c1 : c 1 = some 0
  c2 : c 2 = some 0
  c3 : c 3 = some 0
  c4 : c 4 = some 0
  c5 : c 5 = some f
  c6 : c 6 = none
  c7 : c 7 = some 0
  c8 : c 8 = some (f - 1)

variable {roles : Tapes t prime} {fs : ℤ → Fin (prime+4)} {p : ℤ} {node scalar : Tapes 1 prime}
  {c : Fin K → Option ℕ} {st : Tapes 2 prime}

/-- The common bank at a segment slot is the segment bank. -/
theorem seg_read {v : Descriptor} (hT : t + 15 ≤ T') (hs : Fin 6 → List Bool) {f b : ℕ}
    (hc : SegCounters c b f) (data : RecursiveViewedAction.Data t v) (i : Fin (T'+2)) :
    (raw (bank (RecursiveRoleSerialization.roles data) hs fs p node scalar c st)
        (CommonBank.count t + (T'+2))).head (segSlot t T' i) = (AtomRoleRun.common T' hs f b data).head i ∧
      (raw (bank (RecursiveRoleSerialization.roles data) hs fs p node scalar c st)
        (CommonBank.count t + (T'+2))).tape (segSlot t T' i) = (AtomRoleRun.common T' hs f b data).tape i := by
  have hb0 : CountedLoopReuseAlphabet.empty (a := prime) = RadixZeroFill.encodedBinary (bits 0) := by
    rw [← CounterAdvance.binary_encoded]; rfl
  have aux (j : Fin K) (x : ℕ) (hj : c j = some x) :
      (raw (bank (RecursiveRoleSerialization.roles data) hs fs p node scalar c st)
        (CommonBank.count t + (T'+2))).head (Fin.castAdd _ (auxSlot j)) = 1 ∧
      (raw (bank (RecursiveRoleSerialization.roles data) hs fs p node scalar c st)
        (CommonBank.count t + (T'+2))).tape (Fin.castAdd _ (auxSlot j)) = RadixZeroFill.encodedBinary (bits x) := by
    rw [(Embed.raw_left _ _).1, (Embed.raw_left _ _).2, (CommonBank.bank_aux ..).1, (CommonBank.bank_aux ..).2, hj]
    exact ⟨rfl, rfl⟩
  have hle : t + (7 + (1 + (5 + 2))) ≤ T' := by omega
  induction i using Fin.addCases with
  | right j =>
    rcases (show j = 0 ∨ j = 1 by fin_cases j <;> simp) with rfl | rfl
    · have hs : segSlot t T' (Fin.natAdd T' (0 : Fin 2)) = Fin.castAdd _ (auxSlot 7) := by
        apply Fin.ext; rw [segSlot_val, Fin.val_castAdd, show (7 : Fin K) = ⟨7, by decide⟩ from rfl, aux_val]
        simp; split_ifs <;> omega
      rw [hs, (aux 7 0 hc.c7).1, (aux 7 0 hc.c7).2]
      simp [AtomRoleRun.common, LevelLoop.bank, CountedLoopReuseAlphabet.bank, Tapes.append,
        CountedLoopReuseAlphabet.controls, hb0]
    · have hs : segSlot t T' (Fin.natAdd T' (1 : Fin 2)) = Fin.castAdd _ (auxSlot 8) := by
        apply Fin.ext; rw [segSlot_val, Fin.val_castAdd, show (8 : Fin K) = ⟨8, by decide⟩ from rfl, aux_val]
        simp; split_ifs <;> omega
      rw [hs, (aux 8 (f-1) hc.c8).1, (aux 8 (f-1) hc.c8).2]
      simp [AtomRoleRun.common, LevelLoop.bank, CountedLoopReuseAlphabet.bank, Tapes.append,
        CountedLoopReuseAlphabet.controls, CounterAdvance.binary_encoded]
  | left i =>
    have hX : ∀ k : Fin T', (AtomRoleRun.common T' hs f b data).head (Fin.castAdd 2 k) =
          (AtomRoleLoop.levelBank T' hs (AtomRoleInstall.fAux f) data (AtomRoleInstall.rest b)).head k ∧
        (AtomRoleRun.common T' hs f b data).tape (Fin.castAdd 2 k) =
          (AtomRoleLoop.levelBank T' hs (AtomRoleInstall.fAux f) data (AtomRoleInstall.rest b)).tape k := by
      intro k
      simp [AtomRoleRun.common, LevelLoop.bank, CountedLoopReuseAlphabet.bank, Tapes.append]
    rw [(hX i).1, (hX i).2]
    by_cases hi : i.val < t + 15
    · obtain ⟨j, rfl⟩ : ∃ j : Fin (t + (7 + (1 + (5 + 2)))), Fin.castLE hle j = i :=
        ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
      have hY : (AtomRoleLoop.levelBank T' hs (AtomRoleInstall.fAux f) data (AtomRoleInstall.rest b)).head
            (Fin.castLE hle j) =
          (RecursiveViewFrameRoleBank.bank (RecursiveRoleSerialization.roles data) hs (SharedBank.empty 1 prime)
            ((AtomView.counters (AtomRoleInstall.rest b)).append (AtomRoleInstall.fAux f))).head j ∧
          (AtomRoleLoop.levelBank T' hs (AtomRoleInstall.fAux f) data (AtomRoleInstall.rest b)).tape
            (Fin.castLE hle j) =
          (RecursiveViewFrameRoleBank.bank (RecursiveRoleSerialization.roles data) hs (SharedBank.empty 1 prime)
            ((AtomView.counters (AtomRoleInstall.rest b)).append (AtomRoleInstall.fAux f))).tape j := by
        simp [AtomRoleLoop.levelBank, raw, j.isLt]
      rw [hY.1, hY.2]
      induction j using Fin.addCases with
      | left r =>
        have hs' : segSlot t T' (Fin.castAdd 2 (Fin.castLE hle (Fin.castAdd _ r))) =
            Fin.castAdd _ (Fin.castAdd _ r) := by
          apply Fin.ext; rw [segSlot_val]; simp; omega
        rw [hs', (Embed.raw_left _ _).1, (Embed.raw_left _ _).2]
        simp [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common,
          RecursiveViewFrameRoleBank.bank, Tapes.append]
      | right k =>
        induction k using Fin.addCases with
        | left k =>
          have hs' : segSlot t T' (Fin.castAdd 2 (Fin.castLE hle (Fin.natAdd t (Fin.castAdd _ k)))) =
              Fin.castAdd _ (Fin.natAdd t (Fin.castAdd _ k)) := by
            apply Fin.ext; rw [segSlot_val]; simp
          rw [hs', (Embed.raw_left _ _).1, (Embed.raw_left _ _).2]
          simp [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common,
            RecursiveViewFrameRoleBank.bank, Tapes.append]
        | right k =>
          induction k using Fin.addCases with
          | left k =>
            have hs' : segSlot t T' (Fin.castAdd 2 (Fin.castLE hle (Fin.natAdd t (Fin.natAdd 7
                (Fin.castAdd _ k))))) = Fin.natAdd _ (Fin.castAdd 2 (Fin.castLE hle
                  (Fin.natAdd t (Fin.natAdd 7 (Fin.castAdd _ k))))) := by
              apply Fin.ext; rw [segSlot_val]; simp [count_val]; split_ifs <;> omega
            rw [hs', (Embed.raw_right _ _).1, (Embed.raw_right _ _).2]
            simp [RecursiveViewFrameRoleBank.bank, RecursiveShiftRoleBank.common, Tapes.append, SharedBank.empty]
          | right k =>
            induction k using Fin.addCases with
            | left z =>
              have hs' : segSlot t T' (Fin.castAdd 2 (Fin.castLE hle (Fin.natAdd t (Fin.natAdd 7
                  (Fin.natAdd 1 (Fin.castAdd _ z)))))) = Fin.castAdd _ (auxSlot ⟨z.val, by have : K = 24 := rfl; omega⟩) := by
                apply Fin.ext; rw [segSlot_val]; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_castLE, CommonBank.auxSlot_val]; split_ifs <;> omega
              have hc' : ∀ z : Fin 5, c ⟨z.val, by have : K = 24 := rfl; omega⟩ =
                  some (if z.val = 0 then b else 0) := by
                intro z
                fin_cases z
                · exact hc.c0
                · exact hc.c1
                · exact hc.c2
                · exact hc.c3
                · exact hc.c4
              have hr : AtomRoleInstall.rest b z = bits (if z.val = 0 then b else 0) := by
                fin_cases z <;> rfl
              rw [hs', (aux _ _ (hc' z)).1, (aux _ _ (hc' z)).2]
              simp [RecursiveViewFrameRoleBank.bank, RecursiveShiftRoleBank.common, Tapes.append,
                AtomView.counters, hr]
            | right z =>
              have hs' : segSlot t T' (Fin.castAdd 2 (Fin.castLE hle (Fin.natAdd t (Fin.natAdd 7
                  (Fin.natAdd 1 (Fin.natAdd 5 z)))))) = Fin.castAdd _ (auxSlot ⟨5 + z.val, by have : K = 24 := rfl; omega⟩) := by
                apply Fin.ext; rw [segSlot_val]; simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_castLE, CommonBank.auxSlot_val]; split_ifs <;> omega
              have hc' : ∀ z : Fin 2, c ⟨5 + z.val, by have : K = 24 := rfl; omega⟩ =
                  if z.val = 0 then some f else none := by
                intro z
                fin_cases z
                · exact hc.c5
                · exact hc.c6
              rw [hs', (Embed.raw_left _ _).1, (Embed.raw_left _ _).2, (CommonBank.bank_aux ..).1,
                (CommonBank.bank_aux ..).2, hc' z]
              simp only [RecursiveViewFrameRoleBank.bank, RecursiveShiftRoleBank.common, Tapes.append,
                Fin.addCases_right]
              fin_cases z <;> simp [AtomRoleInstall.fAux, CommonBank.word, descriptorHead, descriptorTape]
    · have hs' : segSlot t T' (Fin.castAdd 2 i) = Fin.natAdd _ (Fin.castAdd 2 i) := by
        apply Fin.ext; rw [segSlot_val]; simp only [Fin.val_castAdd, Fin.val_natAdd, count_val]; split_ifs <;> omega
      rw [hs', (Embed.raw_right _ _).1, (Embed.raw_right _ _).2]
      simp [AtomRoleLoop.levelBank, raw, show ¬ i.val < t + (7 + (1 + (5 + 2))) by omega]

/-- **A placed segment program**: a run of the segment bank from `data` to `data'` is a run of the
common bank that changes only the role tapes. -/
theorem seg_runs {v : Descriptor} (hT : t + 15 ≤ T') {q B : ℕ} {M : Program (T'+2) q prime}
    (hs : Fin 6 → List Bool) {f b : ℕ} (hc : SegCounters c b f) {data data' : RecursiveViewedAction.Data t v}
    (h : HoareTime M (fun w => w = AtomRoleRun.common T' hs f b data)
      (fun w => w = AtomRoleRun.common T' hs f b data') B) :
    Runs (place M hT) (bank (RecursiveRoleSerialization.roles data) hs fs p node scalar c st)
      (bank (RecursiveRoleSerialization.roles data') hs fs p node scalar c st) B := by
  refine Embed.place_runs h _ _ _ _ _ (fun i => seg_read hT hs hc data i) (fun i => seg_read hT hs hc data' i)
    (fun z hz => ?_)
  have hzt : t ≤ z.val := by
    by_contra hlt
    push Not at hlt
    apply hz (Fin.castAdd 2 ⟨z.val, by omega⟩)
    apply Fin.ext
    rw [segSlot_val]
    simp only [Fin.val_castAdd]
    split_ifs <;> omega
  revert hzt
  simp only [bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank, RecursiveShiftRoleBank.common]
  induction z using Fin.addCases with
  | left z => intro h; have := z.isLt; simp at h; omega
  | right z => intro _; simp [Tapes.append]

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSegment
