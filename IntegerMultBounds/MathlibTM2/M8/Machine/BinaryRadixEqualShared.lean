module

public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualRun
public import IntegerMultBounds.Machine.BinaryRadixRootHeadersShared
public import IntegerMultBounds.Machine.BinaryAdjacentWidthHeadersShared

/-! Equal binary interchange on a shared caller tape. The sole four original
headers are physically copied into the blank private bank and erased again. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualShared
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FixedHeaderSparseBankCopy (headerBank)
open SharedPlacementAlphabet (setTape)
open BinaryAdjacentWidthHeadersShared (Sources)
open IntegerMultBounds.MathlibTM2.M8.Stage2Machine (Padded Total.Capacity)
open IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Total (tau tau_range empty_blank)
variable [Total.Capacity]
variable {t : ℕ}

abbrev count := Stage2Machine.Total.count 26

omit [Total.Capacity] in
/-- The root headers' banks pad the prepared bank. -/
theorem root_pad : Padded (BinaryRadixRootHeadersShared.input (a := prime) (t := 19))
    (fun i => Fin.castAdd 6 (Fin.castAdd 1 i)) :=
  (Padded.append (FixedHeaderBankCopy.empty 1) empty_blank).comp
    (Padded.append (FixedHeaderBankCopy.empty 6) empty_blank)

def liftBank (v : Tapes 19 prime) : Tapes count prime :=
  Stage2Machine.Total.input (BinaryRadixRootHeadersShared.input v)

def liftSlot (i : Fin 19) : Fin count := Stage2Machine.Total.slot (Fin.castAdd 6 (Fin.castAdd 1 i))

theorem lift_pad : Padded liftBank liftSlot := root_pad.comp Stage2Machine.Total.input_pad

def lowDestination : Fin 4 → Fin 19 := ![2,3,4,5]
def destination (i : Fin 4) := liftSlot (lowDestination i)
def sourceSlot := liftSlot 0

omit [Total.Capacity] in
theorem lowDestination_injective : Function.Injective lowDestination := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [lowDestination] at h

theorem liftSlot_injective : Function.Injective liftSlot := lift_pad.inj

theorem destination_injective : Function.Injective destination :=
  liftSlot_injective.comp lowDestination_injective

theorem liftBank_sparse (hs : Fin 4 → List Bool) :
    liftBank (headerBank lowDestination hs) = headerBank destination hs :=
  lift_pad.headerBank_eq lowDestination lowDestination_injective hs

omit [Total.Capacity] in
theorem low_sparse (hs : Fin 4 → List Bool) :
    BinaryRadixRangePrepareAlphabet.input (a := prime) (fun _ => blank) (fun _ => blank) hs =
      headerBank lowDestination hs := by
  apply FixedHeaderSparseBankCopy.headerBank_eq lowDestination lowDestination_injective
  · intro i; fin_cases i <;> exact ⟨rfl,rfl⟩
  · intro j hj
    fin_cases j <;> first | exact ⟨rfl,rfl⟩ | exact (hj 0 rfl).elim | exact (hj 1 rfl).elim |
      exact (hj 2 rfl).elim | exact (hj 3 rfl).elim

def bank (source : ℤ → Fin (prime+4)) (hs : Fin 4 → List Bool) :=
  liftBank (BinaryRadixRangePrepareAlphabet.input source (fun _ => blank) hs)

theorem private_bank (hs : Fin 4 → List Bool) :
    bank (fun _ => blank) hs = headerBank destination hs := by
  rw [bank,low_sparse,liftBank_sparse]

theorem liftBank_cells (v : Tapes 19 prime) (i : Fin 19) :
    (liftBank v).head (liftSlot i) = v.head i ∧ (liftBank v).tape (liftSlot i) = v.tape i :=
  ⟨lift_pad.head v i, lift_pad.tape v i⟩

theorem bank_source (source : ℤ → Fin (prime+4)) (hs : Fin 4 → List Bool) :
    (bank source hs).head sourceSlot = 0 ∧ (bank source hs).tape sourceSlot = source :=
  liftBank_cells _ _

theorem bank_set_source (source spare : ℤ → Fin (prime+4)) (hs : Fin 4 → List Bool) :
    setTape (bank source hs) sourceSlot spare 0 = bank spare hs := by
  have hl : setTape (BinaryRadixRangePrepareAlphabet.input source (fun _ => blank) hs) 0 spare 0 =
      BinaryRadixRangePrepareAlphabet.input spare (fun _ => blank) hs := by
    apply congrArg₂ Tapes.mk <;> apply List.ofFn_injective <;> rfl
  rw [bank, bank, ← hl]
  exact (lift_pad.set _ 0 spare 0).symm

theorem destination_room : 4 ≤ count := by
  have h := Fintype.card_le_of_injective destination destination_injective
  simpa only [Fintype.card_fin] using h

def copyProgram (focus : Fin 4 → Fin t) := FixedHeaderSparseBankCopy.program
  (a := prime) (by omega : 0 < t+4) focus destination destination_injective destination_room
def eraseProgram := FixedHeaderSparseBankCopy.cleanup
  (a := prime) (by omega : 0 < t+4) destination destination_injective destination_room

omit [Total.Capacity] in
theorem header_bounds (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i) :
    0 < RadixRangePadding.volume P (2^u) G B ∧
      ∀ i, Counter.value (hs i) ≤ RadixRangePadding.volume P (2^u) G B := by
  have he : ArbitraryWidthHighDimensions.dataVolume 2 P G B u = RadixRangePadding.volume P (2^u) G B := by
    have hp : 2^(2*u) = (2^u)^2 := by rw [Nat.mul_comm 2 u,pow_mul]
    simp only [ArbitraryWidthHighDimensions.dataVolume,RadixRangePadding.volume,hp]
    ring
  obtain ⟨hV,hb⟩ := ArbitraryWidthHighDimensionsShared.original_bounds 2 P G B u 0
    (by omega) (by omega) hP hG hB
  rw [he] at hV hb
  refine ⟨hV,?_⟩
  intro i
  rw [hv]
  fin_cases i
  · exact hb 0
  · exact hb 1
  · exact hb 2
  · exact hb 3

theorem bank_eq (source : ℤ → Fin (prime+4)) (hs : Fin 4 → List Bool) :
    bank source hs = BinaryRadixEqualRun.input source hs := rfl

def runProgram (payload : Fin t) := Placement.placed BinaryRadixEqualRun.program
  (SharedPlacementAlphabet.sharedPlacement payload sourceSlot)
def program (focus : Fin 4 → Fin t) (payload : Fin t) :=
  seq (seq (copyProgram focus) (runProgram payload)) (eraseProgram (t := t))
def cost (P G B u : ℕ) (hs : Fin 4 → List Bool) :=
  40*RadixRangePadding.volume P (2^u) G B+BinaryRadixEqualRun.cost P G B u hs+
    36*RadixRangePadding.volume P (2^u) G B+2

def input (caller : Tapes t prime) := caller.append (FixedHeaderBankCopy.empty count)

private theorem shared_runs (caller : Tapes t prime) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) :
    HoareTime (runProgram payload)
      (fun v => v = caller.append (bank (fun _ => blank) hs))
      (fun v => v = (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) 0).append
          (bank (fun _ => blank) hs)) (BinaryRadixEqualRun.cost P G B u hs) := by
  have h := BinaryRadixEqualRun.runs P G B u hs hv hc hP hG hB x
  rw [← bank_eq,← bank_eq] at h
  have hw := SharedPlacementAlphabet.shared_hoare h caller payload sourceSlot (fun _ => blank) 0
    (ht.trans (bank_source _ hs).2.symm) (hh.trans (bank_source _ hs).1.symm)
  simp only [bank_set_source,(bank_source _ hs).1,(bank_source _ hs).2] at hw
  exact hw

/-- Original caller headers are the only initialized metadata. All local
copies, arithmetic, padding, root execution and inverse cleanup are paid. -/
theorem runs (caller : Tapes t prime) (focus : Fin 4 → Fin t) (payload : Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hsrc : Sources caller focus hs)
    (x : Fin (RadixRangePadding.volume P (2^u) G B) → Bool)
    (ht : caller.tape payload = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head payload = 0) :
    HoareTime (program focus payload) (fun v => v = input caller)
      (fun v => v = input (setTape caller payload
        (BinaryRadixRangePrepareAlphabet.word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) 0))
      (cost P G B u hs) := by
  obtain ⟨hV,hbounds⟩ := header_bounds P G B u hs hP hG hB hv
  have h1 := FixedHeaderSparseBankCopy.constructs_linear (a := prime) (by omega : 0 < t+4)
    focus destination destination_injective destination_room caller hs hsrc.tape hsrc.head
    (RadixRangePadding.volume P (2^u) G B) hV hc hbounds
  rw [← private_bank] at h1
  have h2 := shared_runs caller payload P G B u hs hv hc hP hG hB x ht hh
  have h3 := FixedHeaderSparseBankCopy.cleans_linear (a := prime) (by omega : 0 < t+4)
    destination destination_injective destination_room
    (setTape caller payload
      (BinaryRadixRangePrepareAlphabet.word (RadixRangePadding.transpose (fun i => bitSymbol (x i)))) 0)
    hs (RadixRangePadding.volume P (2^u) G B) hV hc hbounds
  rw [← private_bank] at h3
  apply ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
  unfold cost
  omega

/-- Physical copying and erasure add only linear cost to the certified
uniform binary-width bound, including the zero-width case. -/
theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P G B u : ℕ) (hs : Fin 4 → List Bool),
    0 < P → 0 < G → 0 < B →
    (∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    (cost P G B u hs : ℝ) ≤ C*(RadixRangePadding.volume P (2^u) G B : ℝ)*
      ((max 1 u : ℕ) : ℝ)^Stage2Machine.Total.tau := by
  obtain ⟨C,hC,hbound⟩ := BinaryRadixEqualRun.uniform_bound
  refine ⟨C+78,by linarith,?_⟩
  intro P G B u hs hP hG hB hv hc
  have hb := hbound P G B u hs hP hG hB hv hc
  have hVnat := (header_bounds P G B u hs hP hG hB hv).1
  have hV : 1 ≤ (RadixRangePadding.volume P (2^u) G B : ℝ) := by exact_mod_cast hVnat
  have hp : 1 ≤ ((max 1 u : ℕ) : ℝ)^Stage2Machine.Total.tau := Real.one_le_rpow
    (by exact_mod_cast le_max_left 1 u) Stage2Machine.Total.tau_range.1.le
  have hlin := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (RadixRangePadding.volume P (2^u) G B : ℝ) by positivity)
  unfold cost
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [hb,hV,hlin]

end
end IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualShared
