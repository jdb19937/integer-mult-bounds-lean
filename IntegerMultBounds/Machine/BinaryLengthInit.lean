module

public import IntegerMultBounds.Machine.BinaryLength

/-! Length-descriptor bootstrap directly from a genuinely blank work tape.
One literal transition writes its sentinel and advances its head; one genuine
sequence join enters the fixed length scanner. No marked-clock setup is assumed. -/

@[expose] public section

namespace IntegerMultBounds.Machine.BinaryLengthInit

open Placement (ExactRun)

def blankBank (source : ℤ → Fin 4) (p : ℤ) : Tapes 2 0 :=
  ⟨fun i => if i = 0 then p else 0,fun i => if i = 0 then source else fun _ => blank⟩

/-- Write the counter's sentinel and move its head to its first, still blank digit. -/
def initProgram : Program 2 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun state symbols => if state = 0 then
    some (1,fun i => if i = 1 then (separator,.right) else (symbols i,.stay)) else none

theorem init_exact (source : ℤ → Fin 4) (p : ℤ) :
    ExactRun initProgram 1 (blankBank source p) (BinaryLength.bank source p []) := by
  let c : Config 2 2 0 :=
    ⟨1,(BinaryLength.bank source p []).head,(BinaryLength.bank source p []).tape⟩
  refine ⟨c,?_,?_,rfl⟩
  · simp only [run_one,step,initProgram,Tapes.start,blankBank,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [BinaryLength.bank,Move.offset]
    · funext i j
      fin_cases i <;> simp [BinaryLength.bank,putBits,GrowingCounter.emptyTape,eq_comm]
      intro hj
      rw [hj]
  · simp [c,step,initProgram]

def program : Program 2 8 0 := seq initProgram BinaryLength.program

def runtime (n : ℕ) : ℕ := BinaryLength.runtime n []+2

theorem runtime_le (n : ℕ) : runtime n ≤ 8*n+2 := by
  have h := BinaryLength.runtime_le n []
  simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at h
  dsimp only [runtime]
  omega

/-- Exact initialized scan, preserving the entire source and returning the
counter head to one with its complete canonical binary descriptor. -/
theorem length_exact (n : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (hsource : ∀ j : ℕ, j < n → source (p+j) ≠ blank) (hend : source (p+n) = blank) :
    ExactRun program (runtime n) (blankBank source p)
      (BinaryLength.bank source (p+n) (GrowingCounterData.advance n [])) := by
  obtain ⟨hr,hh⟩ := BinaryLength.scan_exact n source p [] hsource hend
  have hs : ExactRun BinaryLength.program (BinaryLength.runtime n [])
      (BinaryLength.bank source p [])
      (BinaryLength.bank source (p+n) (GrowingCounterData.advance n [])) := ⟨_,hr,hh,rfl⟩
  simpa only [program,runtime,show 1+1+BinaryLength.runtime n [] =
    BinaryLength.runtime n []+2 by omega] using Placement.exact_seq (init_exact source p) hs

theorem length_hoare (n : ℕ) (source : ℤ → Fin 4) (p : ℤ)
    (hsource : ∀ j : ℕ, j < n → source (p+j) ≠ blank) (hend : source (p+n) = blank) :
    HoareTime program (fun v => v = blankBank source p)
      (fun v => ∃ bs : List Bool, Counter.value bs = n ∧ GrowingCounterData.Canonical bs ∧
        bs.length ≤ n.log2+1 ∧ v = BinaryLength.bank source (p+n) bs) (8*n+2) := by
  intro v hv
  subst v
  obtain ⟨c,hr,hh,hc⟩ := length_exact n source p hsource hend
  exact ⟨runtime n,c,runtime_le n,hr,hh,GrowingCounterData.advance n [],
    GrowingCounterData.empty_value n,GrowingCounterData.advance_canonical n [] (Or.inl rfl),
    GrowingCounterData.empty_width n,hc⟩

def inputWord (x y : List Bool) : List (Fin 4) :=
  x.map bitSymbol ++ [separator] ++ y.map bitSymbol

@[simp] theorem inputWord_length (x y : List Bool) : (inputWord x y).length = x.length+y.length+1 := by
  simp [inputWord]
  omega

theorem input_bank (x y : List Bool) :
    input program x y = (blankBank (wordTape (inputWord x y)) 0).start program := by
  unfold input Tapes.start blankBank inputWord
  congr 1
  · apply List.ofFn_injective; rfl
  · apply List.ofFn_injective; rfl

end IntegerMultBounds.Machine.BinaryLengthInit
