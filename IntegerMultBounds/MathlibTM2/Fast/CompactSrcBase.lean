module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSrcFrame
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynMainEntry

/-! Concrete forward and opposite transforms with original layout programs and complete frame restoration. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
open IntegerMultBounds.MathlibTM2.Fast.Src
open IntegerMultBounds.MathlibTM2.Fast.ResampA
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Pipeline
open Filter
open Mult.Sizes
open IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- The distributed source file is independent of the host register and state counts. -/
lemma compactSrcBase_of_legacy {n w W : ℕ} {hd0 : 0<d n}
    {E : SrcF 6 (prime+mnKa)} {V₀ : RsaV (RsaX 6) (prime+mnKa)}
    {σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime+mnKa+4))}
    {restA restB axsA axsB : List (Fin (prime+mnKa+4))}
    (h : SrcBase mnM E n w W hd0 V₀ σ₀ restA restB axsA axsB) :
    SrcBase compactSrcM E n w W hd0 V₀ σ₀ restA restB axsA axsB :=
  ⟨h.a,h.aBase,h.aOut,h.aAx,h.b,h.bBase,h.bOut,h.bAx,h.k,h.v,h.m,h.x⟩

end
end IntegerMultBounds.MathlibTM2.Fast.Main
