module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Common
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Prepared
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighOriginalEncoding

/-!
# The stage-2 high path on a caller's six headers

After stage 1's `ArbitraryWidthHighCommonHighBody` and `ArbitraryWidthOriginalRun`: from the six
shape headers on the caller, the common preparation (`Common`) folds the headers and builds the
stage-2 row metadata, the prepared high body (`Prepared`) transposes the folded source, and the
preparation is erased. At every width past `Params.threshold 2` the caller's source is transposed
from blank private banks to blank private banks within `C V e^τ₂ + D V` (`runs`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.High

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open RevMachine
open FamilyRoot (FamilySpec)
open HighBody (Exponents tau₂ padCount)
open Params (threshold)

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)
variable {t : ℕ}

/-- The caller's slot among the common preparation's banks. -/
def callerSlot (focus : Fin t) : Fin (Common.count t) := Fin.castAdd 19 (Fin.castAdd 16 focus)

/-- The common preparation's banks, extended by the prepared body's. -/
def extendBanks {states : ℕ} (M : Program (Common.count t) states prime) :=
  extend (extend (extend (extend (extend (extend (extend M 17) 12) 1) 22) exchangeCount) movementCount)
    (padCount capacity)

/-- **The stage-2 high path.** -/
def program (headers : Fin 6 → Fin t) (source : Fin t) :=
  seq (seq (extendBanks capacity (Common.program (a := prime) headers prime))
    (Prepared.program capacity (callerSlot source) Common.dimensionsFocus Common.joinedFocus Common.exchangeFocus
      Common.rowFocus Common.roundedFocus))
    (extendBanks capacity (Common.cleanup (a := prime) headers))

/-- The blank private banks. -/
def input (caller : Tapes t prime) := Prepared.input capacity (Common.input caller)

theorem extend_banks_hoare {states budget : ℕ} {M : Program (Common.count t) states prime}
    {v w : Tapes (Common.count t) prime}
    (h : HoareTime M (fun z => z = v) (fun z => z = w) budget) :
    HoareTime (extendBanks capacity M) (fun z => z = Prepared.input capacity v)
      (fun z => z = Prepared.input capacity w) budget :=
  hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (hoare_extend_eq (hoare_extend_eq h (FixedHeaderBankCopy.empty 17)) (FixedHeaderBankCopy.empty 12))
    ArbitraryWidthZeroHeaderShared.empty) (Width.privateIn (q := prime))) (SharedBank.empty exchangeCount prime))
    (SharedBank.empty movementCount prime)) (SharedBank.empty (padCount capacity) prime)

omit [M8.Machine.Net] in
theorem changed_common (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool)
    (focus : Fin t) (word : ℤ → Fin (prime+4)) :
    setTape (Common.output caller d hs prime) (callerSlot focus) word 0 =
      Common.output (setTape caller focus word 0) d hs prime := by
  unfold callerSlot Common.output
  rw [SharedPlacementAlphabet.setTape_append_left, SharedPlacementAlphabet.setTape_append_left]

omit [M8.Machine.Net] in
theorem cost_arith {s cl c V K : ℕ} {X D : ℝ} (h : s + cl ≤ K * V) (hV : 0 < V) (hc : (c : ℝ) ≤ X + D * V) :
    ((s + 1 + c + 1 + cl : ℕ) : ℝ) ≤ X + (D + ((K + 2 : ℕ) : ℝ)) * V := by
  have h' : s + 1 + 1 + cl ≤ (K + 2) * V := by nlinarith
  have h'' : ((s + 1 + 1 + cl : ℕ) : ℝ) ≤ ((K + 2 : ℕ) : ℝ) * V := by exact_mod_cast h'
  have hseq : s + 1 + c + 1 + cl = (s + 1 + 1 + cl) + c := by ring
  rw [hseq, Nat.cast_add]
  nlinarith

/-- **The stage-2 high path**: past the threshold, the caller's source is transposed. -/
theorem runs (hspec : FamilySpec capacity) (hτ : Exponents HighCost.K) :
    ∃ C D : ℝ, ∀ {t : ℕ} (caller : Tapes t prime) (headers : Fin 6 → Fin t) (source : Fin t)
      (d : Descriptor) (hs : Fin 6 → List Bool), d.Positive → threshold 2 ≤ d.width →
      RecursiveDimensionBank.Headers d hs →
      (∀ i, caller.tape (headers i) = RadixZeroFill.encodedBinary (hs i)) → (∀ i, caller.head (headers i) = 1) →
      ∀ x : Fin (volume prime d) → ZMod 2, caller.tape source = sourceWord x → caller.head source = 0 →
      ∃ c : ℕ, (c : ℝ) ≤ C * volume prime d * (d.width : ℝ) ^ tau₂ HighCost.K + D * volume prime d ∧
        HoareTime (program capacity headers source) (fun z => z = input capacity caller)
          (fun z => z = input capacity (setTape caller source
            (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)) c := by
  obtain ⟨C, D, hCD⟩ := Prepared.runs capacity hspec hτ
  refine ⟨C, D + ((2 * MetaPrepare.constant prime + 486 + 2 : ℕ) : ℝ),
    fun {t} caller headers source d hs hp he hv ht hh x hf hhead => ?_⟩
  have hfit := Params.fit_of_threshold (le_refl 2) he
  have hd : 0 < d.width := by omega
  have hs' := extend_banks_hoare capacity (Common.constructs headers caller prime d hs Params.prime_two hp hd hv ht hh)
  have hfold := Common.folded_headers d hs hv
  have hbase : (Common.output caller d hs prime).head (callerSlot source) = caller.head source ∧
      (Common.output caller d hs prime).tape (callerSlot source) = caller.tape source := by
    simp only [callerSlot, Common.output, Tapes.append, Fin.addCases_left]
    exact ⟨trivial, trivial⟩
  obtain ⟨c, hc, hb⟩ := hCD (Common.output caller d hs prime) (callerSlot source)
    Common.dimensionsFocus Common.joinedFocus Common.exchangeFocus Common.rowFocus Common.roundedFocus
    (Common.foldedPrefix d) d.width d.between d.afterD he (Common.foldedPrefix_positive d hp)
    hp.2.2.2.1 hp.2.2.2.2
    (Common.dimensionsWords d hs) (Common.joinedWords d hs) (ArbitraryWidthHighFoldHeaders.words d hs)
    (Common.rhoWord d) (Common.rowWord d) (Common.roundedWord d)
    (Common.dimensions_values d hs hv) (Common.dimensions_canonical d hs hv)
    (Common.joined_values d hs hv) (Common.joined_canonical d hs hv)
    (Common.dimensions_sources caller d hs) (Common.joined_sources caller d hs) (Common.exchange_sources caller d hs)
    hfold (Common.rho_value d) (Common.rho_canonical d) (Common.row_value d) (Common.row_canonical d)
    (Common.rounded_value d) (Common.rounded_canonical d) (Common.row_cells caller d hs).2
    (Common.row_cells caller d hs).1 (Common.rounded_cells caller d hs).2 (Common.rounded_cells caller d hs).1
    (ArbitraryWidthHighFoldSemantics.foldArray x)
    (hbase.2.trans (hf.trans (M8.Machine.ArbitraryWidthHighOriginalEncoding.source_fold x).symm))
    (hbase.1.trans hhead)
  have hword : sourceWord (Shared50RecursiveNodeRows.transpose
      (v := ArbitraryWidthHighLayout.originalDescriptor (Common.foldedPrefix d) d.width d.between d.afterD)
      (one_dvd _) (ArbitraryWidthHighFoldSemantics.foldArray x)) =
      sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x) :=
    M8.Machine.ArbitraryWidthHighOriginalEncoding.source_transpose_fold (by decide : 0 < 1) (one_dvd d.rows) x
  rw [hword, changed_common] at hb
  have hn : headers 3 ≠ source := by
    intro h
    have hh3 := hh 3
    rw [h, hhead] at hh3
    omega
  have hcl := extend_banks_hoare capacity (Common.cleans headers
    (setTape caller source (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x)) 0)
    prime d hs Params.prime_two hp hv
    (by simpa only [setTape, Function.update_of_ne hn] using ht 3)
    (by simpa only [setTape, Function.update_of_ne hn] using hh 3))
  refine ⟨_, ?_, ((hs'.seq hb).seq hcl).consequence (fun _ h => h) (fun _ h => h) le_rfl⟩
  have hvol : volume prime d = volume prime
      (ArbitraryWidthHighLayout.originalDescriptor (Common.foldedPrefix d) d.width d.between d.afterD) :=
    ArbitraryWidthHighFoldSemantics.folded_volume prime d
  rw [← hvol] at hc
  have hlin := Common.costs_le d hp (by omega)
  have hV := RecursiveAffinePrepare.volume_positive Params.prime_two d hp
  exact cost_arith hlin hV hc

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.High
