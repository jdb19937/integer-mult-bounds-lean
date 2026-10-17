module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRec
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecRows
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! # Original-parameter compact root piece records

This fixed host program derives the row, front, and back reservations from the
original axis/guard/chunk parameters, builds the shifted active descriptors and
optional back leaf, and restores all input and scratch registers. It produces
the piece record and exponent sum; assembling the surrounding top configuration
and checking the nonfallback branch remain explicit caller obligations.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {Q A : ℕ} {U P : Type}

noncomputable def compactSynRoot (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq compactRowReserve (.seq (compactSynRec G F) (uclear (sreg (.s 8))))

noncomputable def compactSynRootCost (G F d g k D o : ℕ) : ℕ :=
  compactRowReserveCost d+(compactSynRecCost G F d g k D (CompactGlobalRowPadding.rowAxes NW m d) o+
    (2*CompactGlobalRowPadding.rowAxes NW m d+2))

theorem sg_compactSynRootOfRows (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (G F d g k D o a J q rowCost : ℕ)
    (rowProg : Pr P (nT SXReg) Q A U) (hk : 1≤k)
    (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=k) (hD : (v (.p .D)).length=D)
    (ho : (v (.s 7)).length=o) (hpr : v (.p .pr)=[])
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → v (.s i)=[])
    (hr : LayRuns body rowProg (synG R v)
      (synG R (Function.update v (.s 8) (List.replicate q tick))) rowCost) :
    let f := frontChunks d g k
    let b := backChunks d g k
    let active := D-q-f-b
    let offset := o+k*b
    LayRuns body (.seq rowProg (.seq (compactSynRec G F) (uclear (sreg (.s 8))))) (synG R v)
      (synG R (Function.update (Function.update v (.s 16)
        (List.replicate (b+synE G F active active) tick)) (.p .pr)
        (topRec (topPcRec k (compactReservedPcs k a o b offset J active)))))
      (rowCost+(compactSynRecCost G F d g k D q o+(2*q+2))) := by
  have h8 := hs 8 (by decide) (by decide) (by decide)
  have hc := sg_compactSynRec body R (Function.update v (.s 8) (List.replicate q tick))
    G F d g k D q o a J hk
    (by simp [hd]) (by simp [hg]) (by simp [hK]) (by simp [hD]) (by simp) (by simp [ho])
    (by simp [hpr]) (by intro i h0 h1 h7 hi; simp [hi,hs i h0 h1 h7])
  let b := backChunks d g k
  let active := D-q-frontChunks d g k-b
  let out : List (Fin (A+4)) := topRec (topPcRec k (compactReservedPcs k a o b (o+k*b) J active))
  let E := b+synE G F active active
  let v2 := Function.update (Function.update
    (Function.update v (.s 8) (List.replicate q tick)) (.s 16) (List.replicate E tick)) (.p .pr) out
  have hclear := sgU_clear body (R := R) (v := v2) (a := .s 8) (x := q)
    (by simp only [v2, Function.update_of_ne (by decide : (SynW.s 8) ≠ .p .pr),
      Function.update_of_ne (by decide : (SynW.s 8) ≠ .s 16),
      Function.update_self,List.length_replicate])
  have hrun := hr.seq (hc.seq hclear)
  refine lr_weaken body hrun ?_ ?_
  · apply congrArg (synG R)
    change Function.update v2 (.s 8) [] = _
    dsimp only [v2,E,out,active,b]
    funext z
    by_cases h8z : z=.s 8
    · subst z; simp [h8]
    · by_cases h16z : z=.s 16
      · subst z; rfl
      · by_cases hpz : z=.p .pr
        · subst z; rfl
        · simp [Function.update_of_ne,h8z,h16z,hpz]
  · exact Nat.le_refl _

theorem sg_compactSynRoot (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (G F d g k D o a J : ℕ) (hdpos : 0<d) (hk : 1≤k)
    (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=k) (hD : (v (.p .D)).length=D)
    (ho : (v (.s 7)).length=o) (hpr : v (.p .pr)=[])
    (hs : ∀ i : Fin 32, i≠0 → i≠1 → i≠7 → v (.s i)=[]) :
    let q := CompactGlobalRowPadding.rowAxes NW m d
    let f := frontChunks d g k
    let b := backChunks d g k
    let active := D-q-f-b
    let offset := o+k*b
    LayRuns body (compactSynRoot G F) (synG R v)
      (synG R (Function.update (Function.update v (.s 16)
        (List.replicate (b+synE G F active active) tick)) (.p .pr)
        (topRec (topPcRec k (compactReservedPcs k a o b offset J active)))))
      (compactSynRootCost G F d g k D o) := by
  exact sg_compactSynRootOfRows body R v G F d g k D o a J
    (CompactGlobalRowPadding.rowAxes NW m d) (compactRowReserveCost d)
    compactRowReserve hk hd hg hK hD ho hpr hs
    (sg_compactRowReserve body R v d hdpos hd
      (by intro i hi; apply hs i <;> intro hh <;> subst i <;> simp at hi))

end
end IntegerMultBounds.MathlibTM2.Fast
