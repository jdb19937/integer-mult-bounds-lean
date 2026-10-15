module

public import IntegerMultBounds.MathlibTM2.Fast.CompactDistWires

/-! Actual eighth-root layout bundle, with its own permutation and charged costs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.Networks
  IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Fast.TableVM (dsW)
open Filter

noncomputable section

structure CompactMnLay (w : ℕ → ℕ) where
  layP : Pr LProc (nT SXReg) mnQ (prime + mnKa) Unit
  layQ : Pr LProc (nT SXReg) mnQ (prime + mnKa) Unit
  Pk : ℕ → List (Fin (prime + mnKa + 4)) → Prop
  P₀ : ℕ → List (Fin (prime + mnKa + 4))
  v₀ : ℕ → SynW → List (Fin (prime + mnKa + 4))
  cL : ℕ → ℕ
  cL' : ℕ → ℕ
  pk : ∀ᶠ n in atTop, Pk n (P₀ n)
  wires : ∀ᶠ n in atTop,
    SynV (v₀ n) (List.ofFn (cvAx (t n))) (ℓ n) (CompactSizes.K n) (w n) (ℓ n) 0
        (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (CompactSizes.K n)) ∧
      v₀ n (.p .h) = [] ∧ v₀ n (.p .t) = [] ∧ (v₀ n (.p .c)).length = nRounds (cvAx (t n)) ∧
      blank ∉ v₀ n (.p .c)
  layF : ∀ᶠ n in atTop, ∀ (P₀ : List (Fin (prime + mnKa + 4))), Pk n P₀ →
    ∀ (Z : ℕ → Fin (2 ^ ℓ n) → GaussianInt),
      LayRuns (layerTable (Ka := mnKa) (U := Unit) mnQ_layer Cost.brDirs) layP
        (synG (synIdle (cstream (prime + mnKa) (w n) (rpStream (cvM (cvAx (t n))) Z)) P₀) (v₀ n))
        (synG (synIdle (cstream (prime + mnKa) (w n) (rpStream (cvM (cvAx (t n)))
          (fun m => Z (synPi (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (CompactSizes.K n)) m)))) P₀) (v₀ n))
        (cL n)
  layO : ∀ᶠ n in atTop, ∀ (P₀ : List (Fin (prime + mnKa + 4))), Pk n P₀ →
    ∀ (Y : ℕ → Fin (2 ^ ℓ n) → GaussianInt),
      LayRuns (layerTable (Ka := mnKa) (U := Unit) mnQ_layer Cost.brDirs) layQ
        (synG (synIdle (cstream (prime + mnKa) (w n) (rpStream (cvM (cvAx (t n))) Y)) P₀) (v₀ n))
        (synG (synIdle (cstream (prime + mnKa) (w n) (rpStream (cvM (cvAx (t n)))
          (fun x => Y ((layRec (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (CompactSizes.K n)))
            ⟨x % 2 ^ (List.ofFn (cvAx (t n))).sum, Nat.mod_lt _ (by positivity)⟩)))) P₀) (v₀ n))
        (cL' n)

/-- Actual forward layout cost with the compact chunk. -/
def compactBlCL (n : ℕ) : ℕ :=
  slyFwdCost mnKa (dsyEs n) (ℓ n) (CompactSizes.K n) (ℓ n) (dsW n)
    (blW dsW n) (blE n) (compactDsyV₀ n)

def compactBlCL' (n : ℕ) : ℕ :=
  slyOppCost mnKa (dsyEs n) (ℓ n) (CompactSizes.K n) (ℓ n) (dsW n)
    (blW dsW n) (blE n) (compactDsyV₀ n)

/-- The same layout machines satisfy the new chunk's actual permutation contracts.
The analytic aggregate envelope is deliberately a separate obligation. -/
def compactBlLay : CompactMnLay dsW where
  layP := slyFwd mnQ_layer
  layQ := slyOpp mnQ_layer
  Pk n := slyPk (blW dsW n) (blE n)
  P₀ := blP₀ dsW
  v₀ := compactDsyV₀
  cL := compactBlCL
  cL' := compactBlCL'
  pk := Eventually.of_forall (blP₀_pk dsW)
  wires := compactDsyV₀_wires
  layF := by
    filter_upwards [eventually_big,compactDsyV₀_wires] with n hbig hv
    have hℓ : 1≤ℓ n := by have := hbig.K_succ_le_ℓ; omega
    have hw : 1≤dsW n := by unfold TableVM.dsW; omega
    obtain ⟨h1,h2,h3,h4⟩ := blW_ok dsW n
    exact slyFwd_lay mnQ_layer Cost.brDirs (cvAx (t n)) (compactDs_layHyp hbig)
      (compactDsyV₀ n) hv.1 bl_hA hw (blW dsW n) (blE n) (bl_ax hℓ) h4 h1 h2 h3
  layO := by
    filter_upwards [eventually_big,compactDsyV₀_wires] with n hbig hv
    have hℓ : 1≤ℓ n := by have := hbig.K_succ_le_ℓ; omega
    have hw : 1≤dsW n := by unfold TableVM.dsW; omega
    obtain ⟨h1,h2,h3,h4⟩ := blW_ok dsW n
    exact slyOpp_lay mnQ_layer Cost.brDirs (cvAx (t n)) (compactDs_layHyp hbig)
      (compactDsyV₀ n) hv.1 bl_hA hw (blW dsW n) (blE n) (bl_ax hℓ) h4 h1 h2 h3

end
end IntegerMultBounds.MathlibTM2.Fast.Main
