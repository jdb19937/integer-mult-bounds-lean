module
public import IntegerMultBounds.MathlibTM2.Fast.ResampBAll
public import IntegerMultBounds.MathlibTM2.Fast.TableVM
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.MathlibTM2.Fast.TwiddleRuns
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd


/-!
# The table machine with `60` variables on the `B̃₀` stage

The folded-row program `tblFoldStreamCode` has `60` variables; with the width, word and
accumulator registers and the `12` scratch registers it needs `75` registers, more than the `64`
multiplier registers `ι`. `bandLay` places variables `48 … 59` on the spare registers `vx j` of
the stage bank and everything else on `ι` as `preLay` does. `band_toRuns` turns a contract on
this layout, with the table registers empty before and after, into a stage contract on
`Sum.elim rg rgx` whose spares `vx` stay empty.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast.TableVM


noncomputable section

/-- Where a register of the `60`-variable table machine lives: a multiplier register or a spare. -/
def bandIdx : TblR 60 → Fin 64 ⊕ Fin 12
  | .v i => if h : i.val < 48 then .inl ⟨i.val, by omega⟩ else .inr ⟨i.val - 48, by omega⟩
  | .wr => .inl 48
  | .wn => .inl 49
  | .acc => .inl 50
  | .z j => .inl ⟨51 + j.val, by omega⟩

lemma bandIdx_inj : Function.Injective bandIdx := by
  intro a b h
  rcases a with i | _ | _ | _ | j <;> rcases b with i' | _ | _ | _ | j' <;> revert h <;>
    simp only [bandIdx] <;> (try split_ifs) <;> simp [Fin.ext_iff] <;> omega

variable {t₀ T Q A : ℕ} {U P : Type}

/-- The layout of the `60`-variable table machine on the stage. -/
def bandLay (rg : RsbR → Fin T) (rgx : RsbX t₀ → Fin T) (ι : Fin 64 → Fin T) :
    RsbR ⊕ TblR 60 → Fin T :=
  Sum.elim rg fun x => Sum.elim ι (fun j => rgx (.vx j)) (bandIdx x)

variable {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T} {ι : Fin 64 → Fin T}

lemma bandLay_inj (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hι : Function.Injective ι)
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) : Function.Injective (bandLay rg rgx ι) := by
  have hne : ∀ r j, rg r ≠ rgx (.vx j) := fun r j h => by
    have := hrg₂ (a₁ := .inl r) (a₂ := .inr (.vx j)) h; cases this
  have hvx : ∀ j j', rgx (.vx j) = rgx (.vx j') → j = j' := fun j j' h => by
    have := hrg₂ (a₁ := .inr (.vx j)) (a₂ := .inr (.vx j')) h
    simpa using this
  have hrg : Function.Injective rg := fun a b h => Sum.inl_injective (hrg₂ (a₁ := .inl a) h)
  have hx : Function.Injective fun x : TblR 60 => Sum.elim ι (fun j => rgx (.vx j)) (bandIdx x) := by
    intro a b h
    apply bandIdx_inj
    simp only at h
    cases ha : bandIdx a <;> cases hb : bandIdx b <;> rw [ha, hb] at h <;> simp only [Sum.elim_inl,
      Sum.elim_inr] at h
    · rw [hι h]
    · exact absurd h.symm (hdisj₂ (.inr (.vx _)) _)
    · exact absurd h (hdisj₂ (.inr (.vx _)) _)
    · rw [hvx _ _ h]
  rintro (a | a) (b | b) h <;> simp only [bandLay, Sum.elim_inl, Sum.elim_inr] at h
  · rw [hrg h]
  · exfalso
    cases hb : bandIdx b <;> rw [hb] at h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact hdisj₂ (.inl a) _ h
    · exact hne a _ h
  · exfalso
    cases ha : bandIdx a <;> rw [ha] at h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact hdisj₂ (.inl b) _ h.symm
    · exact hne b _ h.symm
  · rw [hx h]

variable {body : P → Pr P T Q A U}

/-- **A table-machine contract on `bandLay` is a stage contract.** -/
theorem band_toRuns (hrg₂ : Function.Injective (Sum.elim rg rgx))
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) {p : Pr P T Q A U}
    {ρ ρ' : RsbR → List (Fin (A + 4))} {b : ℕ}
    (h : TwRuns body (bandLay rg rgx ι) p (Sum.elim ρ fun _ => []) (Sum.elim ρ' fun _ => []) b)
    (ξ : RsbX t₀ → List (Fin (A + 4))) (hξ : ∀ j, ξ (.vx j) = []) :
    RsbRuns body (Sum.elim rg rgx) ι p (Sum.elim ρ ξ) (Sum.elim ρ' ξ) b := by
  intro v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := h v S (fun r => by
    rcases r with r | x
    · exact hS (.inl r)
    · simp only [bandLay, Sum.elim_inr]
      cases bandIdx x with
      | inl i => exact hc.2 i
      | inr j => exact (hS (.inr (.vx j))).trans (hξ j))
  refine ⟨v', S', n, hu, hn, he, fun r => ?_, ⟨hf.1, hf.2.1, hf.2.2.1, fun k hk => ?_⟩⟩
  · rcases r with r | x
    · exact hS' (.inl r)
    · by_cases hx : ∃ j, x = .vx j
      · obtain ⟨j, rfl⟩ := hx
        have hidx : ∃ y : TblR 60, bandIdx y = .inr j :=
          ⟨.v ⟨j.val + 48, by omega⟩, by simp [bandIdx]⟩
        obtain ⟨y, hy⟩ := hidx
        have := hS' (.inr y)
        simp only [bandLay, Sum.elim_inr, hy, Sum.elim_inr] at this
        simp only [Sum.elim_inr, hξ]
        exact this
      · simp only [not_exists] at hx
        rw [hf.2.2.2 _ (fun r => ?_)]
        · exact hS (.inr x)
        · rcases r with r | y
          · exact fun e => by
              have := hrg₂ (a₁ := .inl r) (a₂ := .inr x) e; cases this
          · simp only [bandLay, Sum.elim_inr]
            cases hy : bandIdx y with
            | inl i => exact fun e => hdisj₂ (.inr x) i e.symm
            | inr j => exact fun e => hx j (by
                have := hrg₂ (a₁ := .inr (.vx j)) (a₂ := .inr x) e
                simpa using this.symm)
  · by_cases hk' : ∃ i y, bandIdx y = .inl i ∧ ι i = k
    · obtain ⟨i, y, hy, rfl⟩ := hk'
      have := hS' (.inr y)
      simp only [bandLay, Sum.elim_inr, hy, Sum.elim_inl] at this
      rw [this, hc.2 i]
    · exact hf.2.2.2 k (fun r => by
        rcases r with r | y
        · exact hk (.inl r)
        · simp only [bandLay, Sum.elim_inr]
          cases hy : bandIdx y with
          | inl i => exact fun e => hk' ⟨i, y, hy, e⟩
          | inr j => exact hk (.inr (.vx j)))

end

end IntegerMultBounds.MathlibTM2.Fast
