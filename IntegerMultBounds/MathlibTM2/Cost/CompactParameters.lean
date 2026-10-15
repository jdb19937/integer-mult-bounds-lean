module

public import IntegerMultBounds.MathlibTM2.Cost.CompactRuntime
public import IntegerMultBounds.Machine.ActiveRepairLayoutDensityArithmetic

/-! # A uniform repair allowance for compact host stages

The dyadic guard choice proves the packed execution premises with repair
constant one. The remaining caller obligations are size inequalities, including
the full row-address width; no probabilistic or supplied density bound remains.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
noncomputable section

theorem compactEarlyAddress_le {s : Shape} (d : Inputs s) :
    (ActiveRepairLayoutRecordsHeadersData.repair (descriptors .early d)).geom.addressBits + 1 ≤
      s.bits + d.rows.log2 + 2 := by
  change s.bits + ActiveRepairLayoutRecordsHeadersData.rowBits (descriptors .early d) + 1 ≤ _
  have := ActiveRepairLayoutRecordsHeadersData.row_log (descriptors .early d)
  omega

theorem compactLateAddress_le {s : Shape} (d : Inputs s) :
    (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair (descriptors .late d)).geom.addressBits + 1 ≤
      s.bits + d.rows.log2 + 2 := by
  change s.bits + ActiveRepairLayoutRecordsHeadersData.rowBits (descriptors .late d) + 1 ≤ _
  have := ActiveRepairLayoutRecordsHeadersData.row_log (descriptors .late d)
  omega

/-- A logarithmic guard pays every actual repair address with the fixed allowance `1`. -/
theorem compactRuntimePacked_of_dyadic {s : Shape} (d : Inputs s) (p : ℝ) (ell : ℕ)
    (hp : 0 < p) (hf : ((d.stage.f - 1 : ℕ) : ℝ) ≤ p) (hell : p ≤ (2 : ℝ) ^ ell)
    (hchunk : 8*ell + 16 ≤ s.chunk) (hguard : s.guard = 4*ell + 6)
    (hrecord : s.bits + d.rows.log2 + 2 ≤ s.payload)
    (hcube : ((s.bits + d.rows.log2 + 2 : ℕ) : ℝ) ≤ p^3) :
    ActivePrefixStageRuntimeData.Packed d 1 := by
  have he := compactEarlyAddress_le d
  have hl := compactLateAddress_le d
  have heR : ((ActiveRepairLayoutRecordsHeadersData.repair
      (descriptors .early d)).geom.addressBits : ℝ) + 1 ≤ p^3 := by
    have h : (((ActiveRepairLayoutRecordsHeadersData.repair
        (descriptors .early d)).geom.addressBits + 1 : ℕ) : ℝ) ≤
        ((s.bits + d.rows.log2 + 2 : ℕ) : ℝ) := by exact_mod_cast he
    exact_mod_cast h.trans hcube
  have hlR : ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair
      (descriptors .late d)).geom.addressBits : ℝ) + 1 ≤ p^3 := by
    have h : (((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair
        (descriptors .late d)).geom.addressBits + 1 : ℕ) : ℝ) ≤
        ((s.bits + d.rows.log2 + 2 : ℕ) : ℝ) := by exact_mod_cast hl
    exact_mod_cast h.trans hcube
  refine ⟨by omega, by omega, he.trans hrecord, hl.trans hrecord, ?_, ?_⟩
  · rw [hguard]
    simpa only [Nat.cast_one] using (ActiveRepairLayoutDensityArithmetic.dyadic_early_paid p (d.stage.f-1) ell s.chunk _
      hp hf hell hchunk heR)
  · rw [hguard]
    simpa only [Nat.cast_one] using (ActiveRepairLayoutDensityArithmetic.dyadic_late_paid p (d.stage.f-1) ell s.chunk _
      hp hf hell hchunk hlR)

end
end IntegerMultBounds.MathlibTM2.Cost
