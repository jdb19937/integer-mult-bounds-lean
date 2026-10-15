module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynUniformLayerContract
public import IntegerMultBounds.MathlibTM2.Fast.CompactDistWires
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRetunedCapacity

/-! The actual distributed transform supplies the compact caller geometry.
Its axis count is d-1; its precision and coefficient count are the original
runtime values. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Cost Filter
noncomputable section

theorem compactSynRetunedGeometry_eventually : ∀ᶠ M : ℕ in atTop,
    CompactSynUniformGeometry M (Mult.CompactSizes.K M) (dsyEs M) (Mult.Sizes.ℓ M) (dsW M) (Mult.Sizes.ℓ M) (Mult.Sizes.p M) := by
  filter_upwards [Mult.Sizes.eventually_big,compactCaller_retuned_eventually_full_dimension] with M hbig hfit
  have hlen : (dsyEs M).length=Mult.Sizes.d M-1 := ds_length_cvAx M
  have hsum : (dsyEs M).sum=Mult.Sizes.logT M-Mult.Sizes.ℓ M := ds_sum_cvAx hbig.1
  have hb : Mult.Sizes.b M≤Mult.Sizes.p M := Nat.le_mul_of_pos_left _ (by decide : 0<6)
  have hwidth := ds_w_B M
  refine ⟨Mult.CompactSizes.old_K_le_K M,Mult.CompactSizes.K_le_d M,by have := hbig.one_le_d; omega,compactDs_layHyp hbig,?_,?_,?_,?_,by omega,hwidth⟩
  · rw [hlen]
    exact hfit.1
  · rw [hlen]
    omega
  · rw [hsum]
    have := hbig.logT_bounds.2
    omega
  · exact Nat.le_refl _

end
end IntegerMultBounds.MathlibTM2.Fast.Main
