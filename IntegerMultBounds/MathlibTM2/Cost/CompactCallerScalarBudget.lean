module
public import IntegerMultBounds.MathlibTM2.Cost.CompactCallerRuntimeParameters
public import IntegerMultBounds.MathlibTM2.Cost.MatchSynOver
public import IntegerMultBounds.MathlibTM2.Fast.CompactTopSelection

/-! One explicit polynomial scalar budget for the actual compact caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Fast CompactGadgetReservationCapacity Filter
noncomputable section

def compactCallerScalarBudget (c p : ℕ) := 2^(c+2)*(p+1)^2

/-- Field-size facts only; no execution or cost premise is stored here. -/
structure CompactCallerScalarBounds
    (N d g K D o W h b qrow f back active E working B : ℕ) : Prop where
  hB : 1≤B
  hN : N≤B
  hd : d≤B
  hg : g≤B
  hK : K≤B
  hD : D≤B
  ho : o≤B
  hW : W≤B
  hdg : d*g≤B
  hh : h≤B
  hb : b≤B
  hqrow : qrow≤B
  hf : f≤B
  hback : back≤B
  hactive : active≤B
  hoffset : o+K*back≤B
  hE : E≤B
  hq : qrow+f≤B
  haT : o+K*(back+active)≤B
  hKq : K*(qrow+f)≤B
  hworking : working≤B

/-- Enlarging the common scalar budget preserves every field bound. -/
theorem CompactCallerScalarBounds.mono
    {N d g K D o W h b qrow f back active E working B B' : ℕ}
    (hs : CompactCallerScalarBounds N d g K D o W h b qrow f back active E working B)
    (hBB' : B≤B') :
    CompactCallerScalarBounds N d g K D o W h b qrow f back active E working B' := by
  rcases hs with ⟨hB,hN,hd,hg,hK,hD,ho,hW,hdg,hh,hb,hqrow,hf,hback,hactive,hoffset,hE,hq,haT,hKq,hworking⟩
  exact ⟨hB.trans hBB',hN.trans hBB',hd.trans hBB',hg.trans hBB',hK.trans hBB',hD.trans hBB',ho.trans hBB',hW.trans hBB',hdg.trans hBB',hh.trans hBB',hb.trans hBB',hqrow.trans hBB',hf.trans hBB',hback.trans hBB',hactive.trans hBB',hoffset.trans hBB',hE.trans hBB',hq.trans hBB',haT.trans hBB',hKq.trans hBB',hworking.trans hBB'⟩

end
end IntegerMultBounds.MathlibTM2.Cost
