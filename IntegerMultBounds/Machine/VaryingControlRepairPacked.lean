module

public import IntegerMultBounds.Machine.VaryingControlRepairFiber
public import IntegerMultBounds.Compact.LatePowerTwoRank
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

/-! Actual early and later packed permutations with a source word selected
from the retained address coordinate. The finite local rank range depends on
its length only, while every inverse and ideal operation reads that source. -/

@[expose] public section

namespace IntegerMultBounds.Machine.VaryingControlRepairPacked
noncomputable section
open Compact Compact.PowerTwo

abbrev Early (q b : ℕ) {C : Type*} (Z : C → List Bool) (S : Type*) :=
  VaryingControlRepairFiber.Address C (fun x => EarlyAddress (Bi b) (Li q) (controls (Z x)).length) S
abbrev Late (q b : ℕ) {C : Type*} (Z : C → List Bool) (S : Type*) :=
  VaryingControlRepairFiber.Address C (fun x => LateAddress (Bi b) (Li q) (controls (Z x)).length) S

def earlySize (q b n : ℕ) := 2^(n*q+n*b)
def lateSize (q b n : ℕ) := 2^(n*q+n*b+n*b)

theorem early_size (q b n : ℕ) (hq : 1≤q) (Z : List Bool) (hZ : Z.length=n) :
    Mi q b Z=earlySize q b n := by
  rw [Mi_eq q b Z hq,hZ,earlySize,pow_add]
  ring

theorem late_size (q b n : ℕ) (hq : 1≤q) (Z : List Bool) (hZ : Z.length=n) :
    lateMi q b Z=lateSize q b n := by rw [lateMi_eq q b Z hq,hZ]; rfl

def earlyLocalRank (q b n : ℕ) (hq : 1≤q) {C : Type*} (Z : C → List Bool)
    (hZ : ∀ x, (Z x).length=n) (x : C) :=
  (Compact.PowerTwo.rankEquiv q b (Z x)).trans (finCongr (early_size q b n hq (Z x) (hZ x)))
def lateLocalRank (q b n : ℕ) (hq : 1≤q) {C : Type*} (Z : C → List Bool)
    (hZ : ∀ x, (Z x).length=n) (x : C) :=
  (lateRankEquiv q b (Z x)).trans (finCongr (late_size q b n hq (Z x) (hZ x)))

abbrev earlyActual (q b : ℕ) {C S : Type*} (Z : C → List Bool) : Equiv.Perm (Early q b Z S) :=
  VaryingControlRepairFiber.perm (fun x => Sperm q b (Z x))
abbrev earlyIdeal (q b : ℕ) {C S : Type*} (Z : C → List Bool) : Equiv.Perm (Early q b Z S) :=
  VaryingControlRepairFiber.perm (fun x => Tperm q b (Z x))
abbrev lateActual (q b : ℕ) {C S : Type*} (Z : C → List Bool) : Equiv.Perm (Late q b Z S) :=
  VaryingControlRepairFiber.perm (fun x => lateSperm q b (Z x))
abbrev lateIdeal (q b : ℕ) {C S : Type*} (Z : C → List Bool) : Equiv.Perm (Late q b Z S) :=
  VaryingControlRepairFiber.perm (fun x => lateTperm q b (Z x))

abbrev earlyBad (q b : ℕ) {C S : Type*} (Z : C → List Bool) (a : Early q b Z S) :=
  badSet q b (Z a.1) a.2.1
abbrev lateBad (q b : ℕ) {C S : Type*} (Z : C → List Bool) (a : Late q b Z S) :=
  lateBadSet q b (Z a.1) a.2.1

abbrev earlyDestination (q b : ℕ) {C S : Type*} (Z : C → List Bool) : Equiv.Perm (Early q b Z S) :=
  VaryingControlRepairFiber.destination (fun x => Sperm q b (Z x)) (fun x => Tperm q b (Z x))
abbrev lateDestination (q b : ℕ) {C S : Type*} (Z : C → List Bool) : Equiv.Perm (Late q b Z S) :=
  VaryingControlRepairFiber.destination (fun x => lateSperm q b (Z x)) (fun x => lateTperm q b (Z x))

end
end IntegerMultBounds.Machine.VaryingControlRepairPacked
