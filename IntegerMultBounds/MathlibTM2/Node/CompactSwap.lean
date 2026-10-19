module

public import IntegerMultBounds.MathlibTM2.Node.SwapPass
import Mathlib.Tactic.Positivity.Finset

/-! # Prepared compact-field interchange on the live host machine

A compact field has `h` bits. This adapter transports two complete fields, including arbitrary
dirty values, through the existing host interchange. Outer rows, the intervening gap and
the inner bit payload are spectators. The stream is explicitly encoded as bit symbols. Canonical interchange headers are inputs and are restored;
header generation and compact controlled rotations are separate obligations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Layer.PackedXor
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Compact's canonical integer residues are exactly the complete `h`-bit field. -/
def compactFieldEquiv (h : ℕ) : Fin (2 ^ h) ≃ Compact.Field ((2 : ℤ) ^ h) where
  toFun x := ⟨x.val, by constructor; omega; exact_mod_cast x.isLt⟩
  invFun x := ⟨x.val.toNat, by
    have hx := x.property
    have hp : (((2 : ℕ) ^ h : ℕ) : ℤ) = (2 : ℤ) ^ h := by simp
    omega⟩
  left_inv x := by apply Fin.ext; simp
  right_inv x := by apply Subtype.ext; exact Int.toNat_of_nonneg x.property.1

/-- Complete two-field geometry; `R` includes all inner coordinates and payload bits. -/
abbrev CompactSwapAddr (P G R h : ℕ) :=
  Fin P × Compact.Field ((2 : ℤ) ^ h) × Fin G × Compact.Field ((2 : ℤ) ^ h) × Fin R

/-- Swap the front and back fields, retaining every spectator coordinate. -/
def compactSwapPerm (P G R h : ℕ) : Equiv.Perm (CompactSwapAddr P G R h) where
  toFun x := (x.1, x.2.2.2.1, x.2.2.1, x.2.1, x.2.2.2.2)
  invFun x := (x.1, x.2.2.2.1, x.2.2.1, x.2.1, x.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A bijection onto the entire bit-stream volume, with no extra field or zero restriction. -/
def compactSwapRank (P G R h : ℕ) :
    CompactSwapAddr P G R h ≃ Fin (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ h) R) where
  toFun x := BinaryAdjacentWidthInterchange.index x.1 ((compactFieldEquiv h).symm x.2.1)
    x.2.2.1 ((compactFieldEquiv h).symm x.2.2.2.1) x.2.2.2.2
  invFun i :=
    let x := BinaryAdjacentWidthInterchange.coordinates i
    (x.1, compactFieldEquiv h x.2.1, x.2.2.1, compactFieldEquiv h x.2.2.2.1, x.2.2.2.2)
  left_inv x := by simp
  right_inv i := by simp only [Equiv.symm_apply_apply]; exact BinaryAdjacentWidthInterchange.index_coordinates i

/-- The native interchange's rank action is exactly the compact front/back swap. -/
lemma compactSwap_transpose (P G R h : ℕ) (data : CompactSwapAddr P G R h → Bool) :
    BinaryAdjacentWidthInterchange.transpose (data ∘ (compactSwapRank P G R h).symm) =
      data ∘ compactSwapPerm P G R h ∘ (compactSwapRank P G R h).symm := by
  funext i
  simp [BinaryAdjacentWidthInterchange.transpose, compactSwapRank, compactSwapPerm, Function.comp_def]

/-- The boundary is bit-symbol encoded, with arbitrary payload values on all addresses. -/
def compactSwapBits {A : ℕ} (P G R h : ℕ) (data : CompactSwapAddr P G R h → Bool) : List (Fin (A + 4)) :=
  List.ofFn fun i => bitSymbol (data ((compactSwapRank P G R h).symm i))

lemma compactSwapBits_swap {A : ℕ} (P G R h : ℕ) (data : CompactSwapAddr P G R h → Bool) :
    swapList P (2 ^ h) G (2 ^ h) R (blank : Fin (A + 4)) (compactSwapBits P G R h data) =
      compactSwapBits P G R h (data ∘ compactSwapPerm P G R h) := by
  rw [compactSwapBits, ← transpose_bits_eq_swapList]
  change List.ofFn (fun i => bitSymbol (BinaryAdjacentWidthInterchange.transpose
    (data ∘ (compactSwapRank P G R h).symm) i)) = _
  rw [compactSwap_transpose]
  rfl

/-- The fixed host program consumes prepared headers; there is no dimension-specialized code. -/
noncomputable def compactSwapProg {t₀ T Q K : ℕ} {U F : Type}
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q) (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι)
    (hT : swapT t₀ ≤ T) : Pr F T Q (prime + K) U :=
  placedSwapProg hd pay hi hQ ι hι hT

/-- A uniform envelope for the prepared pass. `volume` counts bits, and `bankSize` includes
all initial placed-register symbols. The wider envelope also leaves room for future adapters. -/
noncomputable def compactSwapCost (T t₀ volume h bankSize : ℕ) : ℝ :=
  3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (volume : ℝ) *
      ((max 1 h : ℕ) : ℝ) ^ Parameters.tau +
    (6 * bankSize + 34 * volume + 2 * T + 6 * swapT t₀ + 23 : ℕ)

/-- Actual prepared two-field host execution, including all dirty field values. Only the
bit-stream payload register changes; the entire remaining register file and user state are
restored. No header-generation or symbol-to-bit conversion cost is hidden in the contract. -/
theorem compactSwap_exec {t₀ T Q K : ℕ} {U F : Type}
    (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (P G R h : ℕ) (hP : 0 < P) (hG : 0 < G) (hR : 0 < R)
    (data : CompactSwapAddr P G R h → Bool) (hs : Fin 5 → List Bool)
    (hv : ∀ k, Counter.value (hs k) = BinaryInterchangeRun.values P G R h h k)
    (hc : ∀ k, GrowingCounterData.Canonical (hs k))
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = separator :: (hs k).map bitSymbol)
    (hpay : S.R (ι (reg pay)) = compactSwapBits P G R h data)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime + 4) :
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ compactSwapCost T t₀ (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ h) R) h
        (∑ j, (S.R (ι j)).length) ∧
      Exec body (compactSwapProg hd pay hi hQ ι hι hT) (mk v S) steps
        (mk v' { S with
          R := Function.update S.R (ι (reg pay)) (compactSwapBits P G R h (data ∘ compactSwapPerm P G R h)) }) := by
  obtain ⟨v', steps, hu, hsteps, hexec⟩ := placedSwapProg_exec body hd pay hi hQ ι hι hT
    P G R h h hs (Nat.le_succ h) (Nat.le_succ h) hv hc hP hG hR
    (data ∘ (compactSwapRank P G R h).symm) v S hL hpriv hhdr hpay hother
  have hC := (Classical.choose_spec BinaryInterchangeRun.uniform_bound).2
    P G R h h hs hP hG hR (Nat.le_succ h) (Nat.le_succ h) hv hc
  rw [max_self] at hC
  have hC' : (BinaryInterchangeRun.cost P G R h h hs : ℝ) ≤
      swapConst * (3 * (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ h) R : ℕ)) *
        ((max 1 h : ℕ) : ℝ) ^ Parameters.tau := by
    have hnonneg : 0 ≤ swapConst * (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ h) R : ℕ) *
        ((max 1 h : ℕ) : ℝ) ^ Parameters.tau := by
      have := swapConst_pos
      positivity
    change (BinaryInterchangeRun.cost P G R h h hs : ℝ) ≤
      swapConst * (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ h) R : ℕ) *
        ((max 1 h : ℕ) : ℝ) ^ Parameters.tau at hC
    nlinarith
  have hsteps' : steps ≤ (T + 12 * swapT t₀ + 5) * BinaryInterchangeRun.cost P G R h h hs +
      (6 * ∑ j, (S.R (ι j)).length + 2 * T + 6 * swapT t₀ + 15) := by
    simpa only [Nat.add_assoc] using hsteps
  have hb := cast_time_bound hsteps' hC'
  refine ⟨v', steps, hu, hb.trans ?_, ?_⟩
  · unfold compactSwapCost
    push_cast
    nlinarith
  · have hLeq : (fun _ => ([] : List (Fin (prime + K + 4)))) = S.L := funext fun j => (hL j).symm
    simpa only [compactSwapProg, hpay, compactSwapBits_swap, hLeq] using hexec

end IntegerMultBounds.MathlibTM2.Node
