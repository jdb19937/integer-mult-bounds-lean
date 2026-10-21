module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreSparse
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighCost
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExecutionInitializeCleanup

/-!
# The stage-2 high body with its banks filled and erased

After stage 1's `ArbitraryWidthHighInitializedRun`: three sparse copies fill the exchange bank,
the movement bank and the padded core's bank from words on the caller's tapes (`fill`), the high
body runs (`HighBody.program`), and three sparse erasures blank the banks again (`erase`). All
private banks start and finish blank (`runs`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Init

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighLayout
open SharedPlacementAlphabet (setTape)
open FixedHeaderSparseBankCopy (headerBank)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open M8.Machine.ArbitraryWidthExecutionPrivateHeadersCore (blankTape emptyOne emptyTwo)
open M8.Machine.ArbitraryWidthExecutionPrivateHeadersRoot (exchangeSlots exchangeWords exchange_injective)
open M8.Machine.ArbitraryWidthExecutionPrivateHeadersMovement (movementSlots movementWords movement_injective)
open M8.Machine.ArbitraryWidthHighExecutionInitialize (Sources Bounded exchangePrivate movementPrivate
  exchangeCopy movementCopy movementFocus exchange_room movement_room)
open RevMachine
open FamilyRoot (FamilySpec)
open HighBody (Exponents tau₂ padCount)
open CoreSparse (paddedSlots paddedWords paddedSlots_injective)
open Params (r padded view threshold)

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)
variable {t : ℕ}

theorem padding_room : 4 + 15 ≤ padCount capacity := by
  show 4 + 15 ≤ 12 + Assembly.tW capacity
  have := CoreSparse.count_le capacity
  simp only [CommonBank.count, Shared50RecursiveBank.Count, RecursiveCallBank.TapeCount] at this
  omega

/-- The private banks, blank. -/
def input (caller : Tapes t prime) :=
  ((caller.append (SharedBank.empty exchangeCount prime)).append
    (SharedBank.empty movementCount prime)).append (SharedBank.empty (padCount capacity) prime)

/-- The private banks, filled. -/
def output (caller : Tapes t prime) (hs : Fin 6 → List Bool) (rs ss op oe : List Bool) (pw : Fin (4+15) → List Bool) :=
  ((caller.append (exchangePrivate hs rs)).append (movementPrivate ss op oe rs)).append
    (headerBank (paddedSlots capacity) pw)

/-- The padding sources among the private banks. -/
def paddingFocus (padding : Fin (4+15) → Fin t) : Fin (4+15) → Fin ((t+exchangeCount)+movementCount) :=
  fun i => Fin.castAdd movementCount (Fin.castAdd exchangeCount (padding i))

/-- Fill the padded core's bank. -/
def paddingCopy (padding : Fin (4+15) → Fin t) :=
  FixedHeaderSparseBankCopy.program (a := prime) (by omega : 0 < ((t+exchangeCount)+movementCount)+(4+15))
    (paddingFocus padding) (paddedSlots capacity) (paddedSlots_injective capacity) (padding_room capacity)

/-- Erase the padded core's bank. -/
def paddingCleanup :=
  FixedHeaderSparseBankCopy.cleanup (a := prime) (by omega : 0 < ((t+exchangeCount)+movementCount)+(4+15))
    (paddedSlots capacity) (paddedSlots_injective capacity) (padding_room capacity)

/-- Fill the three banks. -/
def fill (exchange : Fin 7 → Fin t) (movement : Fin 5 → Fin t) (padding : Fin (4+15) → Fin t) :=
  seq (seq (extend (extend (exchangeCopy exchange) movementCount) (padCount capacity))
    (extend (movementCopy movement) (padCount capacity))) (paddingCopy capacity padding)

/-- Erase the three banks. -/
def erase := seq (seq (paddingCleanup capacity (t := t))
    (extend M8.Machine.ArbitraryWidthHighExecutionInitializeCleanup.movementCleanup (padCount capacity)))
  (extend (extend M8.Machine.ArbitraryWidthHighExecutionInitializeCleanup.exchangeCleanup movementCount)
    (padCount capacity))

theorem fills (caller : Tapes t prime) (exchange : Fin 7 → Fin t) (movement : Fin 5 → Fin t)
    (padding : Fin (4+15) → Fin t) (hs : Fin 6 → List Bool) (rs ss op oe : List Bool)
    (pw : Fin (4+15) → List Bool) (V : ℕ) (hV : 0 < V)
    (he : Sources caller exchange (exchangeWords hs rs)) (hm : Sources caller movement (movementWords ss op oe rs))
    (hp : Sources caller padding pw)
    (be : Bounded (exchangeWords hs rs) V) (bm : Bounded (movementWords ss op oe rs) V) (bp : Bounded pw V) :
    HoareTime (fill capacity exchange movement padding) (fun w => w = input capacity caller)
      (fun w => w = output capacity caller hs rs ss op oe pw) (400*V) := by
  have h1 := FixedHeaderSparseBankCopy.constructs_linear (by omega : 0 < t+7) exchange
    exchangeSlots exchange_injective exchange_room caller (exchangeWords hs rs)
    he.tape he.head V hV be.canonical be.value
  rw [← M8.Machine.ArbitraryWidthExecutionPrivateHeadersRoot.exchange_sparse] at h1
  have h1' := hoare_extend_eq (hoare_extend_eq h1 (SharedBank.empty movementCount prime))
    (SharedBank.empty (padCount capacity) prime)
  have h2 := FixedHeaderSparseBankCopy.constructs_linear (by omega : 0 < (t+exchangeCount)+5)
    (movementFocus movement) (movementSlots (q := prime)) movement_injective movement_room
    (caller.append (exchangePrivate hs rs)) (movementWords ss op oe rs)
    (by intro i; simpa only [movementFocus, Tapes.append, Fin.addCases_left] using hm.tape i)
    (by intro i; simpa only [movementFocus, Tapes.append, Fin.addCases_left] using hm.head i)
    V hV bm.canonical bm.value
  rw [← M8.Machine.ArbitraryWidthExecutionPrivateHeadersMovement.movement_sparse] at h2
  have h2' := hoare_extend_eq h2 (SharedBank.empty (padCount capacity) prime)
  have h3 := FixedHeaderSparseBankCopy.constructs_linear
    (by omega : 0 < ((t+exchangeCount)+movementCount)+(4+15))
    (paddingFocus padding) (paddedSlots capacity) (paddedSlots_injective capacity) (padding_room capacity)
    ((caller.append (exchangePrivate hs rs)).append (movementPrivate ss op oe rs)) pw
    (by intro i; simpa only [paddingFocus, Tapes.append, Fin.addCases_left] using hp.tape i)
    (by intro i; simpa only [paddingFocus, Tapes.append, Fin.addCases_left] using hp.head i)
    V hV bp.canonical bp.value
  exact ((h1'.seq h2').seq h3).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem erases (caller : Tapes t prime) (hs : Fin 6 → List Bool) (rs ss op oe : List Bool)
    (pw : Fin (4+15) → List Bool) (V : ℕ) (hV : 0 < V)
    (be : Bounded (exchangeWords hs rs) V) (bm : Bounded (movementWords ss op oe rs) V) (bp : Bounded pw V) :
    HoareTime (erase capacity (t := t)) (fun w => w = output capacity caller hs rs ss op oe pw)
      (fun w => w = input capacity caller) (400*V) := by
  have h1 := FixedHeaderSparseBankCopy.cleans_linear (by omega : 0 < ((t+exchangeCount)+movementCount)+(4+15))
    (paddedSlots capacity) (paddedSlots_injective capacity) (padding_room capacity)
    ((caller.append (exchangePrivate hs rs)).append (movementPrivate ss op oe rs)) pw V hV bp.canonical bp.value
  have h2 := FixedHeaderSparseBankCopy.cleans_linear (by omega : 0 < (t+exchangeCount)+5)
    (movementSlots (q := prime)) movement_injective movement_room
    (caller.append (exchangePrivate hs rs)) (movementWords ss op oe rs) V hV bm.canonical bm.value
  rw [← M8.Machine.ArbitraryWidthExecutionPrivateHeadersMovement.movement_sparse] at h2
  have h2' := hoare_extend_eq h2 (SharedBank.empty (padCount capacity) prime)
  have h3 := FixedHeaderSparseBankCopy.cleans_linear (by omega : 0 < t+7)
    exchangeSlots exchange_injective exchange_room caller (exchangeWords hs rs) V hV be.canonical be.value
  rw [← M8.Machine.ArbitraryWidthExecutionPrivateHeadersRoot.exchange_sparse] at h3
  have h3' := hoare_extend_eq (hoare_extend_eq h3 (SharedBank.empty movementCount prime))
    (SharedBank.empty (padCount capacity) prime)
  exact ((h1.seq h2').seq h3').consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- **The high body with its banks.** -/
def program (focus : Fin t) (exchange : Fin 7 → Fin t) (movement : Fin 5 → Fin t)
    (padding : Fin (4+15) → Fin t) :=
  seq (seq (fill capacity exchange movement padding) (HighBody.program capacity focus)) (erase capacity (t := t))

/-- The padded core's words at width `e`. -/
abbrev coreWords (b : ℕ) (ph : Fin 4 → List Bool) (P e G B : ℕ) :=
  paddedWords ph (Assembly.wOf HighCost.K (view b P e G B)) (view b P e G B)

/-- **The high body with its banks**: from blank banks to blank banks, the caller's source
transposed, within a constant times `V e^τ₂` plus the linear filling and erasing. -/
theorem runs (hspec : FamilySpec capacity) (hτ : Exponents HighCost.K) {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, ∀ P e G B : ℕ, threshold b ≤ e → 0 < P → 0 < G → 0 < B →
      ∀ (hs : Fin 6 → List Bool) (rs ss op oe : List Bool),
      RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs →
      HighBody.JoinCounters P e (r b e) G B rs ss op oe →
      ∀ ph : Fin 4 → List Bool,
      M8.Machine.ArbitraryWidthPaddedPiecePadding.Headers (joinedDescriptor prime P e (r b e) G B) (padded b e) ph →
      ∀ {t : ℕ} (caller : Tapes t prime) (focus : Fin t) (exchange : Fin 7 → Fin t) (movement : Fin 5 → Fin t)
        (padding : Fin (4+15) → Fin t) (V : ℕ), 0 < V →
      Sources caller exchange (exchangeWords hs rs) → Sources caller movement (movementWords ss op oe rs) →
      Sources caller padding (coreWords b ph P e G B) →
      Bounded (exchangeWords hs rs) V → Bounded (movementWords ss op oe rs) V →
      Bounded (coreWords b ph P e G B) V →
      ∀ x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2,
      caller.tape focus = sourceWord x → caller.head focus = 0 → ∃ c : ℕ,
        (c : ℝ) ≤ C * volume prime (originalDescriptor P e G B) * (e : ℝ) ^ tau₂ HighCost.K + 802 * V ∧
        HoareTime (program capacity focus exchange movement padding) (fun w => w = input capacity caller)
          (fun w => w = input capacity
            (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)) c := by
  obtain ⟨C, hC⟩ := HighCost.runs capacity hspec hτ hb
  refine ⟨C, fun P e G B he hP hG hB hs rs ss op oe hv hj ph hph _ caller focus exchange movement padding V hV
    sx sm sp bx bm bp x hf hh => ?_⟩
  have h1 := fills capacity caller exchange movement padding hs rs ss op oe _ V hV sx sm sp bx bm bp
  obtain ⟨c, hc, h2⟩ := hC P e G B he hP hG hB hs rs ss op oe hv hj ph hph blankTape 0 emptyOne emptyOne emptyTwo
    M8.Machine.RootExecution.blank_ready blankTape 0 emptyOne emptyTwo
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ caller focus x hf hh
  rw [show HighBody.privateBanks capacity HighCost.K hs rs ss op oe blankTape 0 emptyOne emptyOne emptyTwo ph
      (view b P e G B) blankTape 0 emptyOne emptyTwo caller = output capacity caller hs rs ss op oe
        (coreWords b ph P e G B) by
      unfold HighBody.privateBanks output
      rw [CoreSparse.padded_sparse]; rfl,
    show ∀ c', HighBody.privateBanks capacity HighCost.K hs rs ss op oe blankTape 0 emptyOne emptyOne emptyTwo ph
      (view b P e G B) blankTape 0 emptyOne emptyTwo c' = output capacity c' hs rs ss op oe
        (coreWords b ph P e G B) from fun c' => by
      unfold HighBody.privateBanks output
      rw [CoreSparse.padded_sparse]; rfl] at h2
  have h3 := erases capacity (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)
    hs rs ss op oe _ V hV bx bm bp
  refine ⟨_, ?_, ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) le_rfl⟩
  have hV1 : (1 : ℝ) ≤ V := by exact_mod_cast hV
  push_cast
  linarith

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Init
