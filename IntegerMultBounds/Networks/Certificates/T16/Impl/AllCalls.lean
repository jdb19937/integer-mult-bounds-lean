module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Checks0
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Checks1
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Checks2
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Checks3
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Checks4
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Checks5
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Checks6
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Checks7
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Checks8
public import IntegerMultBounds.Networks.Certificates.T16.Impl.HostedChecks

/-! Every local invocation satisfies its facts, so every local invocation is correct. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open Streams

theorem all_checks {s r : ℕ} (hs : s < 9) (hr : r < 16) : callCheck s r = true := by
  interval_cases s
  exacts [stage0_check r hr, stage1_check r hr, stage2_check r hr, stage3_check r hr,
    stage4_check r hr, stage5_check r hr, stage6_check r hr, stage7_check r hr, stage8_check r hr]

theorem all_callFacts {s r : ℕ} (hs : s < 9) (hr : r < 16) : CallFacts s r :=
  callFacts_of_check hosted_covered bits_agree hs hr (all_checks hs hr)

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S] [IsScalarTower ℚ ℂ S]
variable (ρ : Module.End ℂ (BinaryWalsh.Arrays 73) →* Module.End ℂ S)

/-- **Every local invocation is correct.** -/
theorem local_correct {s r : ℕ} (hs : s < 9) (hr : r < 16) (y : NodeUnit → S) (j : Fin 14336) :
    runT ρ (callProgram s r) y (.inl j) =
      runUnits (portRep ρ) (eventOps (.local s r)) y (.inl j) :=
  call_correct ρ hr (all_callFacts hs hr) y j

end IntegerMultBounds.Networks.Certificates.T16.Impl
