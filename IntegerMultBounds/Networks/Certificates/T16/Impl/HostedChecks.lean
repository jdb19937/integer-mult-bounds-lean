module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallChecks

/-! The global hosting checks, evaluated by the kernel: every hosted slice lies on a helper of
its slot, and the literal slot bitmasks are those of the role lists. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

theorem hosted_covered : hostedCovered = true := by decide +kernel

theorem bits_agree : bitsAgree = true := by decide +kernel

end IntegerMultBounds.Networks.Certificates.T16.Impl
