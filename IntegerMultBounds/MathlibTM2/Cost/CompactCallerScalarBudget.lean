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

private theorem scalarFields (N d g K D o W h b qrow f back active E working c p : ℕ)
    (hN : N≤p) (hd : d≤p) (hg : g≤p) (hK : K≤p) (hD : D≤d)
    (hfit : qrow+f+back≤D) (haddress : o+K*D≤N)
    (hactive : active=D-qrow-f-back) (hE : E≤W)
    (hwork : working≤2*W) (hW : W≤2^c*(p+1)) (hh : h≤p) (hb : b≤p) :
    CompactCallerScalarBounds N d g K D o W h b qrow f back active E working
      (compactCallerScalarBudget c p) := by
  have hB : 1≤compactCallerScalarBudget c p :=
    Nat.mul_pos (pow_pos (by decide : 0<2) _) (pow_pos (Nat.succ_pos p) _)
  have hp2 : p^2≤compactCallerScalarBudget c p :=
    (Nat.pow_le_pow_left (Nat.le_succ p) 2).trans
      (Nat.le_mul_of_pos_left _ (pow_pos (by decide : 0<2) _))
  have hp : p≤compactCallerScalarBudget c p := (Nat.le_self_pow (by decide : 2≠0) p).trans hp2
  have h2W : 2*W≤compactCallerScalarBudget c p := by
    calc
      2*W≤2*(2^c*(p+1)) := Nat.mul_le_mul_left _ hW
      _ = 2^(c+1)*(p+1) := by rw [pow_succ]; ring
      _ ≤ 2^(c+2)*(p+1)^2 := Nat.mul_le_mul
        (Nat.pow_le_pow_right (by decide : 0<2) (by omega : c+1≤c+2))
        (Nat.le_self_pow (by decide : 2≠0) _)
  have hWB : W≤compactCallerScalarBudget c p := (by omega : W≤2*W).trans h2W
  have hDp : D≤p := hD.trans hd
  have hbackD : back≤D := by omega
  have hqD : qrow+f≤D := by omega
  have hbaD : back+active≤D := by omega
  have hoff : o+K*back≤p :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left K hbackD) o).trans (haddress.trans hN)
  have haT : o+K*(back+active)≤p :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left K hbaD) o).trans (haddress.trans hN)
  have hKq : K*(qrow+f)≤p := (Nat.mul_le_mul_left K hqD).trans (by omega)
  refine ⟨hB,hN.trans hp,hd.trans hp,hg.trans hp,hK.trans hp,hDp.trans hp,
    (by omega : o≤p).trans hp,hWB,?_,hh.trans hp,hb.trans hp,
    (by omega : qrow≤p).trans hp,(by omega : f≤p).trans hp,
    (by omega : back≤p).trans hp,(by omega : active≤p).trans hp,
    hoff.trans hp,hE.trans hWB,hqD.trans (hDp.trans hp),haT.trans hp,hKq.trans hp,hwork.trans h2W⟩
  have hprod : d*g≤p^2 := by simpa only [pow_two] using Nat.mul_le_mul hd hg
  exact hprod.trans hp2

end
end IntegerMultBounds.MathlibTM2.Cost
