module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.CoreShared
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthPaddedPieceShared
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighRun

/-!
# The stage-2 high body on supplied metadata

Stage 1's high body (`ArbitraryWidthHighRun`) joins the low `r` digits of `h` and `d` into the
rows, pads the rows, runs its piece dispatcher, crops and separates. The stage-2 high body
(`program`) keeps every step but the inner one, which is the stage-2 core on the padded view
(`CoreShared`). Its metadata (the counters of `r`, the padding and the core's own bank) are
supplied on private banks, which it restores.

* `padded_runs`: pad the rows to `R'`, run the core, crop (after `ArbitraryWidthPaddedPieceRun`);
* `shared_runs`: the same with the source on a caller's tape (after `ArbitraryWidthPaddedPieceShared`);
* `runs`: exchange and join, the padded core, separate (after `ArbitraryWidthHighRun`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighBody

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRowPadding
open ArbitraryWidthHighLayout
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open M8.Machine.ArbitraryWidthHighExchangeJoin (exchangeCount movementCount)
open Stage2Width (tau2)
open RevMachine
open FamilyRoot (FamilySpec)
open Assembly (tW wOf nOf)

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

/-! ### Pad, core, crop -/

/-- The tapes of the padded core: the padding bank and the core's tapes. -/
abbrev padCount := 12 + tW capacity

/-- **Pad the rows, run the core, crop.** -/
def padded := seq
  (seq (extend (RowPaddingConstructedAlphabet.program (a := prime)) (tW capacity))
    (CoreShared.program capacity (1 : Fin 12)))
  (extend M8.Machine.ArbitraryWidthPaddedPiecePadding.cropProgram (tW capacity))

/-- The exponent of the core. -/
abbrev tau₂ (K : ℕ) : ℝ := tau2 (K : ℝ)⁻¹ Cost.tauS M8.Machine.BudgetBound.tau

/-- The core's conditions on a view `u`: positive, of width at least two, and rows splitting over
the family's depth. -/
structure Fits (K : ℕ) (u : Descriptor) : Prop where
  pos : u.Positive
  width : 2 ≤ u.width
  rows : rev97m.roleCount ^ RevNode.depth rev97m.width (RevHalf.Rk rev97m) (nOf K u) ∣ u.rows

/-- The core's own state: a blank payload past `p`, a free node tape and available stacks. -/
structure Ready (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime) : Prop where
  pay : ∀ z, p ≤ z → f z = blank
  node : Family.NodeFree node
  desc : RecursiveStackAllocation.Available 0 st
  pc : RecursiveStackAllocation.Available 1 st

/-- The τ hypotheses of the core. -/
structure Exponents (K : ℕ) : Prop where
  hK : 2 ≤ K
  s1 : Cost.tauS ≤ M8.Machine.BudgetBound.tau
  le1 : M8.Machine.BudgetBound.tau ≤ 1
  half : 1 / 2 ≤ M8.Machine.BudgetBound.tau
  two : 1 / 2 ≤ tau₂ K
  lin : 1 - (K : ℝ)⁻¹ ≤ tau₂ K

/-- The core's private bank at the padded view. -/
abbrev corePrivate (K : ℕ) (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)
    (u : Descriptor) := CoreShared.privateBank capacity f p node st (wOf K u) u

/-- The bank of the padded core. -/
def bank (K : ℕ) {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) (ph : Fin 4 → List Bool) (R' : ℕ)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime) :=
  (M8.Machine.ArbitraryWidthPaddedPiecePadding.input x ph).append (corePrivate capacity K f p node st (withRows v R'))

theorem padded_runs (hspec : FamilySpec capacity) {K : ℕ} (hτ : Exponents K) :
    ∃ C' : ℝ, ∀ (v : Descriptor) (R' : ℕ) (ph : Fin 4 → List Bool), v.Positive → v.rows ≤ R' →
      M8.Machine.ArbitraryWidthPaddedPiecePadding.Headers v R' ph → Fits K (withRows v R') →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime), Ready f p node st →
      ∀ x : Fin (volume prime v) → ZMod 2, ∃ c : ℕ,
        (c : ℝ) ≤ 826 * volume prime (withRows v R') + 2 +
          C' * volume prime (withRows v R') * (v.width : ℝ) ^ tau₂ K ∧
        HoareTime (padded capacity) (· = bank capacity K x ph R' f p node st)
          (· = bank capacity K (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x) ph R' f p node st) c := by
  obtain ⟨C', hC'⟩ := CoreShared.runs capacity hspec hτ.hK hτ.s1 hτ.le1 hτ.half hτ.two hτ.lin
  refine ⟨C', fun v R' ph hp hR hph hfit f p node st hready x => ?_⟩
  have hpad := hoare_extend_eq (M8.Machine.ArbitraryWidthPaddedPiecePadding.pad_hoare v R' ph hp hR hph x)
    (corePrivate capacity K f p node st (withRows v R'))
  obtain ⟨c, hc, hcore⟩ := hC' (withRows v R') hfit.pos hfit.width hfit.rows f p hready.pay node hready.node st
    hready.desc hready.pc (M8.Machine.ArbitraryWidthPaddedPiecePadding.middle (padArray R' 0 x) ph) (1 : Fin 12)
    (padArray R' 0 x) rfl rfl
  rw [M8.Machine.ArbitraryWidthPaddedPiecePadding.middle_source] at hcore
  have hcrop := hoare_extend_eq (M8.Machine.ArbitraryWidthPaddedPiecePadding.crop_hoare v R' ph hp hR hph
    (Shared50RecursiveNodeRows.transpose (one_dvd R') (padArray R' 0 x)))
    (corePrivate capacity K f p node st (withRows v R'))
  rw [cropArray_transpose_padArray] at hcrop
  refine ⟨_, ?_, ((hpad.seq hcore).seq hcrop).consequence (fun _ h => h) (fun _ h => h) le_rfl⟩
  have hw : (withRows v R').width = v.width := rfl
  rw [hw] at hc
  push_cast
  linarith

/-! ### On a caller's tape -/

/-- The source tape of the padded core. -/
def sourceSlot : Fin (padCount capacity) := Fin.castAdd (tW capacity) (0 : Fin 12)

/-- The padded core's bank with the source stream `src`. -/
def bankWith (K : ℕ) (src : ℤ → Fin (prime+4)) (ph : Fin 4 → List Bool) (u : Descriptor)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime) :=
  (M8.Machine.ArbitraryWidthPaddedPiecePadding.bank src (fun _ => blank) ph).append (corePrivate capacity K f p node st u)

/-- The padded core's own bank. -/
def privateBank (K : ℕ) (ph : Fin 4 → List Bool) (u : Descriptor) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (node : Tapes 1 prime) (st : Tapes 2 prime) :=
  bankWith capacity K (fun _ => blank) ph u f p node st

theorem bankWith_source (K : ℕ) (src target : ℤ → Fin (prime+4)) (ph : Fin 4 → List Bool) (u : Descriptor)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime) :
    setTape (bankWith capacity K src ph u f p node st) (sourceSlot capacity) target 0 =
      bankWith capacity K target ph u f p node st := by
  unfold bankWith sourceSlot
  rw [SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun w : Tapes 12 prime => w.append (corePrivate capacity K f p node st u))
  apply congrArg₂ Tapes.mk <;> apply List.ofFn_injective <;> rfl

theorem bankWith_head (K : ℕ) (src : ℤ → Fin (prime+4)) (ph : Fin 4 → List Bool) (u : Descriptor)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime) :
    (bankWith capacity K src ph u f p node st).head (sourceSlot capacity) = 0 := by
  simp only [bankWith, sourceSlot, Tapes.append, Fin.addCases_left]
  rfl

theorem bankWith_tape (K : ℕ) (src : ℤ → Fin (prime+4)) (ph : Fin 4 → List Bool) (u : Descriptor)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime) :
    (bankWith capacity K src ph u f p node st).tape (sourceSlot capacity) = src := by
  simp only [bankWith, sourceSlot, Tapes.append, Fin.addCases_left]
  rfl

/-- The padded core on the caller's tape `focus`. -/
def shared {t : ℕ} (focus : Fin t) :=
  Placement.placed (padded capacity) (SharedPlacementAlphabet.sharedPlacement focus (sourceSlot capacity))

theorem shared_runs (hspec : FamilySpec capacity) {K : ℕ} (hτ : Exponents K) :
    ∃ C' : ℝ, ∀ (v : Descriptor) (R' : ℕ) (ph : Fin 4 → List Bool), v.Positive → v.rows ≤ R' →
      M8.Machine.ArbitraryWidthPaddedPiecePadding.Headers v R' ph → Fits K (withRows v R') →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime), Ready f p node st →
      ∀ {t : ℕ} (caller : Tapes t prime) (focus : Fin t) (x : Fin (volume prime v) → ZMod 2),
      caller.tape focus = sourceWord x → caller.head focus = 0 → ∃ c : ℕ,
        (c : ℝ) ≤ 826 * volume prime (withRows v R') + 2 +
          C' * volume prime (withRows v R') * (v.width : ℝ) ^ tau₂ K ∧
        HoareTime (shared capacity focus)
          (· = caller.append (privateBank capacity K ph (withRows v R') f p node st))
          (· = (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x)) 0).append
            (privateBank capacity K ph (withRows v R') f p node st)) c := by
  obtain ⟨C', hC'⟩ := padded_runs capacity hspec hτ
  refine ⟨C', fun v R' ph hp hR hph hfit f p node st hready t caller focus x hf hh => ?_⟩
  obtain ⟨c, hc, hrun⟩ := hC' v R' ph hp hR hph hfit f p node st hready x
  refine ⟨c, hc, ?_⟩
  change HoareTime _ (fun w => w = bankWith capacity K (sourceWord x) ph (withRows v R') f p node st)
    (fun w => w = bankWith capacity K (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x))
      ph (withRows v R') f p node st) _ at hrun
  have h := SharedPlacementAlphabet.shared_hoare hrun caller focus (sourceSlot capacity) (fun _ => blank) 0
    (by rw [bankWith_tape]; exact hf) (by rw [bankWith_head]; exact hh)
  simpa only [shared, bankWith_tape, bankWith_head, bankWith_source, privateBank] using h

/-! ### Exchange, the padded core, separate -/

/-- **The stage-2 high body.** -/
def program {t : ℕ} (focus : Fin t) := seq
  (seq (extend (M8.Machine.ArbitraryWidthHighExchangeJoin.program focus) (padCount capacity))
    (shared capacity (Fin.castAdd movementCount (Fin.castAdd exchangeCount focus))))
  (extend (M8.Machine.ArbitraryWidthHighSeparateShared.program (Fin.castAdd exchangeCount focus)) (padCount capacity))

/-- The counters of the join: `r`, `q^(e-r) G`, `P q^r` and `q^(e-r) B`. -/
structure JoinCounters (P e r G B : ℕ) (rs ss op oe : List Bool) : Prop where
  hr : Counter.value rs = r
  cr : GrowingCounterData.Canonical rs
  hss : Counter.value ss = prime^(e-r)*G
  css : GrowingCounterData.Canonical ss
  hop : Counter.value op = P*prime^r
  cop : GrowingCounterData.Canonical op
  hoe : Counter.value oe = prime^(e-r)*B
  coe : GrowingCounterData.Canonical oe

/-- The private banks of the high body. -/
def privateBanks (K : ℕ) (hs : Fin 6 → List Bool) (rs ss op oe : List Bool) (f₀ : ℤ → Fin (prime+4)) (p₀ : ℤ)
    (node₀ scalar₀ : Tapes 1 prime) (st₀ : Tapes 2 prime) (ph : Fin 4 → List Bool) (u : Descriptor)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime) {t : ℕ} (caller : Tapes t prime) :=
  ((caller.append (M8.Machine.ArbitraryWidthHighExchangeShared.privateBank hs rs f₀ p₀ node₀ scalar₀ st₀)).append
    (M8.Machine.ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs)).append
    (privateBank capacity K ph u f p node st)

/-- **The stage-2 high body on supplied metadata.** -/
theorem runs (hspec : FamilySpec capacity) {K : ℕ} (hτ : Exponents K) :
    ∃ C' : ℝ, ∀ P e r G B : ℕ, r ≤ e → 0 < P → 0 < G → 0 < B →
      ∀ (hs : Fin 6 → List Bool) (rs ss op oe : List Bool),
      RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs → JoinCounters P e r G B rs ss op oe →
      ∀ (R' : ℕ) (ph : Fin 4 → List Bool), prime^(2*r) ≤ R' →
      M8.Machine.ArbitraryWidthPaddedPiecePadding.Headers (joinedDescriptor prime P e r G B) R' ph →
      Fits K (withRows (joinedDescriptor prime P e r G B) R') →
      ∀ (f₀ : ℤ → Fin (prime+4)) (p₀ : ℤ) (node₀ scalar₀ : Tapes 1 prime) (st₀ : Tapes 2 prime),
      M8.Machine.CallReady.Ready f₀ p₀ node₀ scalar₀ st₀ →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime), Ready f p node st →
      ∀ {t : ℕ} (caller : Tapes t prime) (focus : Fin t)
        (x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2),
      caller.tape focus = sourceWord x → caller.head focus = 0 → ∃ c : ℕ,
        (c : ℝ) ≤ ((M8.Machine.ArbitraryWidthHighExchangeJoin.coefficient +
            M8.Machine.RadixHighBlockSeparateRun.coefficient prime : ℕ) : ℝ) * (r + 1) *
              volume prime (originalDescriptor P e G B) +
          826 * volume prime (withRows (joinedDescriptor prime P e r G B) R') + 5 +
          C' * volume prime (withRows (joinedDescriptor prime P e r G B) R') * ((e - r : ℕ) : ℝ) ^ tau₂ K ∧
        HoareTime (program capacity focus)
          (· = privateBanks capacity K hs rs ss op oe f₀ p₀ node₀ scalar₀ st₀ ph
            (withRows (joinedDescriptor prime P e r G B) R') f p node st caller)
          (· = privateBanks capacity K hs rs ss op oe f₀ p₀ node₀ scalar₀ st₀ ph
            (withRows (joinedDescriptor prime P e r G B) R') f p node st
            (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)) c := by
  obtain ⟨C', hC'⟩ := shared_runs capacity hspec hτ
  refine ⟨C', fun P e r G B hfit hP hG hB hs rs ss op oe hv hj R' ph hR hph hfits f₀ p₀ node₀ scalar₀ st₀ ready₀
    f p node st hready t caller focus x hf hh => ?_⟩
  let v := joinedDescriptor prime P e r G B
  let u := withRows v R'
  let ex := M8.Machine.ArbitraryWidthHighExchangeShared.privateBank hs rs f₀ p₀ node₀ scalar₀ st₀
  let mv := M8.Machine.ArbitraryWidthHighMovementPlacement.privateBank (q := prime) (a := prime) ss op oe rs
  let pd := privateBank capacity K ph u f p node st
  have hp : (originalDescriptor P e G B).Positive :=
    ⟨hP, (by change 0 < 1; decide), (by change 0 < 1; decide), hG, hB⟩
  have h1 := hoare_extend_eq
    (M8.Machine.ArbitraryWidthHighExchangeJoin.realizes_hoare caller focus P e r G B hfit hP hG hB
      hs rs ss op oe hp hv hj.hr hj.cr hj.hss hj.css hj.hop hj.cop hj.hoe hj.coe f₀ p₀ node₀ scalar₀ st₀ ready₀ x hf hh) pd
  let joined := exchangeJoin P e r G B hfit x
  let mid := ((setTape caller focus (sourceWord joined) 0).append ex).append mv
  have hvp : v.Positive := ⟨hP, pow_pos Networks.Shared50ModularControl.prime_prime.pos _,
    (by change 0 < 1; decide), hG, hB⟩
  obtain ⟨c₂, hc₂, h2⟩ := hC' v R' ph hvp hR hph hfits f p node st hready mid
    (Fin.castAdd movementCount (Fin.castAdd exchangeCount focus)) joined
    (by simp only [mid, Tapes.append, Fin.addCases_left, setTape, Function.update_self])
    (by simp only [mid, Tapes.append, Fin.addCases_left, setTape, Function.update_self])
  have hout2 : setTape mid (Fin.castAdd movementCount (Fin.castAdd exchangeCount focus))
      (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) joined)) 0 =
      ((setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) joined)) 0).append ex).append mv := by
    dsimp only [mid]
    rw [SharedPlacementAlphabet.setTape_append_left, SharedPlacementAlphabet.setTape_append_left,
      SharedPlacementAlphabet.setTape_setTape]
  rw [hout2] at h2
  let low := Shared50RecursiveNodeRows.transpose (one_dvd v.rows) joined
  let sepCaller := (setTape caller focus (sourceWord low) 0).append ex
  have h3 := hoare_extend_eq
    (M8.Machine.ArbitraryWidthHighSeparateShared.realizes_hoare sepCaller (Fin.castAdd exchangeCount focus)
      P e r G B hfit hP hG hB rs ss op oe hj.hr hj.cr hj.hss hj.css hj.hop hj.cop hj.hoe hj.coe low
      (by simp only [sepCaller, Tapes.append, Fin.addCases_left, setTape, Function.update_self])
      (by simp only [sepCaller, Tapes.append, Fin.addCases_left, setTape, Function.update_self])) pd
  have hout3 : setTape sepCaller (Fin.castAdd exchangeCount focus)
      (sourceWord (separateExchange P e r G B hfit low)) 0 =
      (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0).append ex := by
    dsimp only [sepCaller, low, joined, v]
    rw [SharedPlacementAlphabet.setTape_append_left, SharedPlacementAlphabet.setTape_setTape,
      exchange_transpose_separate]
  rw [hout3] at h3
  refine ⟨_, ?_, ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) le_rfl⟩
  have hw : v.width = e - r := rfl
  rw [hw] at hc₂
  push_cast
  nlinarith

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighBody
