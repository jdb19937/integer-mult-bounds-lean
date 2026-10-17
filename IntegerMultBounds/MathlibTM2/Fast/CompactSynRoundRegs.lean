module

public import IntegerMultBounds.MathlibTM2.Node.CompactLayerPlaced
public import IntegerMultBounds.MathlibTM2.Node.CompactTopProcRegs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import IntegerMultBounds.MathlibTM2.Node.TopProc

/-! Combine legacy round workspace and persistent compact bank contracts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
noncomputable section
variable {Q A : ℕ} {U P : Type}

theorem compactSynRest_of_legacy
    {shape : CompactGadgetReservationShape.Shape} {o N r w : ℕ}
    {R : Fin (nT CompactHostBReg) → List (Fin (A+4))}
    (h : Rest bcEmpty N r w (R ∘ compactLegacyReg))
    (hb : ∀ z,compactBasisRest shape o r z (R (reg (BReg := CompactHostBReg) (.bc (.inl z))))) :
    Rest (compactHostBasisRest shape o r) N r w R := by
  intro x
  cases x with
  | io =>
    trivial

  | wire x =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.wire x)
  | wtmp x =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.wtmp x)
  | park =>
    trivial

  | ctr =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.ctr)
  | tmp =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.tmp)
  | cS =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.cS)
  | cR =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.cR)
  | tS =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.tS)
  | tR =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.tR)
  | ph x =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.ph x)
  | lf x =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.lf x)
  | rowctr =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.rowctr)
  | rowtmp =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.rowtmp)
  | rctmp =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.rctmp)
  | racc =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.racc)
  | lenctr =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.lenctr)
  | lev =>
    trivial

  | u =>
    trivial

  | K =>
    trivial

  | ρ =>
    trivial

  | a₀ =>
    trivial

  | L =>
    trivial

  | rows =>
    trivial

  | n =>
    trivial

  | w =>
    trivial

  | rw =>
    trivial

  | Tc =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.Tc)
  | sc x =>
    simpa only [restSpec,Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName]
      using h (.sc x)
  | bc z =>
    cases z with
    | inl z => exact hb z
    | inr z => trivial
  | st =>
    trivial

  | cs =>
    trivial


theorem compactSynTopRegs_of_legacy
    {shape : CompactGadgetReservationShape.Shape} {o N r w K ρ : ℕ}
    {R : Fin (nT CompactHostBReg) → List (Fin (A+4))}
    (h : TopRegs (R ∘ compactLegacyReg) N r w K ρ)
    (hb : ∀ z,compactBasisRest shape o r z (R (reg (BReg := CompactHostBReg) (.bc (.inl z))))) :
    CompactTopRegs (compactHostBasisRest shape o r) R N r w K ρ where
  rest := compactSynRest_of_legacy h.rest hb
  hlev := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.hlev
  hu := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.hu
  ha₀ := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.ha₀
  hL := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.hL
  hrows := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.hrows
  hn := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.hn
  hw := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.hw
  hrw := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.hrw
  hK := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.hK
  hρ := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.hρ

theorem compactSynTopIn_of_legacy
    {R : Fin (nT CompactHostBReg) → List (Fin (A+4))} {cfg pfs : List ℕ}
    (h : TopIn (R ∘ compactLegacyReg) cfg pfs) :
    CompactTopIn (BReg := CompactHostBReg) R cfg pfs where
  cf := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.cf
  pl := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.pl
  pb := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.pb
  x := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.x
  y := by simpa only [Function.comp_apply,compactLegacyReg,compactMapReg_reg,compactMapRegName] using h.y

end
end IntegerMultBounds.MathlibTM2.Fast
