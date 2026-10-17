module

import IntegerMultBounds.MathlibTM2.Fast.CompactTopReady
import IntegerMultBounds.MathlibTM2.Fast.SynMath
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSelection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! The original input precision pays the computed compact top working width.
The pre-shift array fits exactly the width emitted by the runtime constructor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open CompactGadgetReservationCapacity
noncomputable section

/-- No additional intermediate-overflow premise is needed once the original
numerators satisfy the existing precision bound. -/
theorem compactTopPre_fits (ds : ComplexFramedExecution.Directions)
    (hd : ComplexPhaseBudget.Realizes ds)
    {d g K D oS n a W R R₂ r ρ p : ℕ} (h : CompactReservationFits d g K D) (hρ : ρ<K)
    (hR₂ : R*2^a≤R₂) (hW : p+2≤W)
    (hfitT : ∀ i<compactTopKernelCount d g K,
      compactTopKernelOffset d g K D oS+ρ+K*i<n+a)
    (Z : ZArr (Fin R × Fin r) (n+a))
    (hZ : ∀ q, ‖GaussianInt.toComplex (Z q)‖≤2^p) :
    let shift := (D+1)/2+compactTopKernelCount d g K+
      (backChunks d g K+synE (gateCount (program ds)) (factorCount (program ds))
        (compactReservationActive d g K D) (compactReservationActive d g K D))
    let w' := W+shift+D
    ∀ hpcs : ∀ pc∈compactTopPcs d g K D oS R₂,pc.Ok ds K n w' R₂,
    let Ps := topPieces hρ (compactTopPcs d g K D oS R₂) hpcs
    let low := Ps.flatMap Piece.bitsList
    let top := topTop (compactTopKernelOffset d g K D oS) ρ K
      (compactTopKernelCount d g K) (n+a) hfitT
    ∀ q, TopFitsZ w' (topPre ds a low top hR₂ Ps Z q) := by
  dsimp only
  intro hpcs
  apply topPre_fits ds hd
  · exact compactTopPieces_injective ds hρ _ hpcs
  · exact List.Perm.refl _
  · exact compactSelection_nodup (by omega) (compactTopSelection_vals ds h hρ hpcs hfitT)
  · simpa [topTop] using compactTop_shift ds h hρ hpcs hfitT
  · exact hZ
  · omega

/-- Original numerator records already fit before the runtime widening pass. -/
theorem compactTopInput_fits {R r n p W : ℕ} (Z : ZArr (Fin R × Fin r) n)
    (hW : p+2≤W) (hZ : ∀ q, ‖GaussianInt.toComplex (Z q)‖≤2^p) :
    ∀ q, TopFitsZ W (Z q) := fun q => topFitsZ_of_norm (hZ q) hW

end
end IntegerMultBounds.MathlibTM2.Fast
