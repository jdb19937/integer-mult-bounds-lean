module

public import IntegerMultBounds.MathlibTM2.Node.CompactRotStage
public import IntegerMultBounds.Machine.ActivePrefixStageRuntimeEndpoint

/-! # Runtime compact stages on normalized host banks

The native width and order selectors cover every positive width, including
singleton slots. Only packed widths require the repair density conditions.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
open ActiveRepairLayoutRecordsData (Array)
noncomputable section
variable {s : Shape} {T Q K : ℕ} {U F : Type}

/-- Original descriptors and raw data in a bank with any sufficient tape count. -/
def compactRawWords {N : ℕ} (d : Inputs s) (x : Array s d.rows) (j : Fin N) : List (Fin (K+4)) :=
  compactStageWords (k := N) d x ⟨j.val, by omega⟩

def compactRawHeader {N : ℕ} (hN : 66 ≤ N) (i : Fin 13) : Fin N :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- The normalized host adapter also accepts the native raw-bank presentation. -/
theorem compactRaw_exec {N q : ℕ} (hN : 66 ≤ N)
    (body : F → Pr F T Q (prime+K) U) (M : Program N q prime) (hQ : q ≤ Q)
    (ι : Fin N → Fin T) (hι : Function.Injective ι) (hT : N ≤ T)
    (d : Inputs s) (x y : Array s d.rows) (cost : ℕ)
    (hM : HoareTime M (fun w => w=SharedBankStageInput.raw (original d x) N)
      (fun w => w=SharedBankStageInput.raw (original d y) N) cost)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j, S.L (ι j)=[]) (hR : ∀ j, S.R (ι j)=compactRawWords d x j) :
    ∃ v' m, v'.user=v.user ∧
      m ≤ (T+12*N+5)*cost + 6*(∑ j : Fin N, (compactRawWords (K := prime+K) d x j).length) +
        2*T+6*N+23 ∧
      Exec body (compactNativeProg (liftQ (Alphabet.program (Alphabet.widen prime K) M) hQ)
        (compactRawHeader hN) ι hι hT) (mk v S) m
        (mk v' { S with L := fun z => if z ∈ Set.range ι then [] else S.L z
                        R := fun z => if h : z ∈ Set.range ι then
                          compactRawWords d y (Classical.choose h) else S.R z }) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hm : HoareTime M (fun w => w=CleanSubbank.bank (s := k) (original d x))
      (fun w => w=CleanSubbank.bank (s := k) (original d y)) cost := by
    simpa only [SharedBankRawCompose.bank_eq_raw] using hM
  exact compactStageWiden_exec body M hQ ι hι hT d x y cost hm v S hL hR

abbrev compactRuntimeStates := stateCount ActivePrefixStageRuntimeProgram.program
lemma compactRuntimeCount : 66 ≤ ActivePrefixStageRuntimeProgram.count := by
  have := ActivePrefixStageRuntimeProgram.public_le
  unfold ActivePrefixStageRuntimeProgram.count
  omega

def compactRuntimeProg (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T) : Pr F T Q (prime+K) U :=
  compactNativeProg (liftQ (Alphabet.program (Alphabet.widen prime K)
    ActivePrefixStageRuntimeProgram.program) hQ) (compactRawHeader compactRuntimeCount) ι hι hT

/-- Actual execution of both physical selectors and the selected complete native stage. -/
theorem compactRuntimeProg_exec (body : F → Pr F T Q (prime+K) U)
    (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (D : ℕ) (d : Inputs s) (x : Array s d.rows)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j, S.L (ι j)=[])
    (hR : ∀ j, S.R (ι j)=compactRawWords d x j) :
    ∃ v' m, v'.user=v.user ∧
      m ≤ (T+12*ActivePrefixStageRuntimeProgram.count+5)*(ActivePrefixStageRuntimeData.cost D d hp) +
        6*(∑ j : Fin ActivePrefixStageRuntimeProgram.count,
          (compactRawWords (K := prime+K) d x j).length) +
        2*T+6*ActivePrefixStageRuntimeProgram.count+23 ∧
      Exec body (compactRuntimeProg hQ ι hι hT) (mk v S) m
        (mk v' { S with
          L := fun z => if z ∈ Set.range ι then [] else S.L z
          R := fun z => if h : z ∈ Set.range ι then
            compactRawWords d
              (ActivePrefixStageRuntimeData.result d x) (Classical.choose h) else S.R z }) := by
  have hm := ActivePrefixStageRuntimeRun.runs D d x hp
  simp only [ActivePrefixStageRuntimeEndpoint.bank_eq_original] at hm
  exact compactRaw_exec compactRuntimeCount body
    ActivePrefixStageRuntimeProgram.program hQ ι hι hT d x _ _ hm v S hL hR

end
end IntegerMultBounds.MathlibTM2.Node
