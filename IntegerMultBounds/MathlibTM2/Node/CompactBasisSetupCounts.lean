module

public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRec
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecRows
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Call-free synthesis of the seven persistent compact basis counters from original inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open CompactGadgetReservationCapacity
noncomputable section
variable {Q A : ℕ} {U P : Type}

/-- The output roles are s15=o, s6=back bits, s26=active axes, s11=total bits,
s16=coefficient count, s18=original axes, and s19=original guard. -/
def compactBasisCountsAfter : Pr P (nT SXReg) Q A U :=
  .seq (usub (sreg (.s 7)) (sreg (.s 6)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.p .D)) (sreg (.s 10)) (sreg (.s 2))) <|
  .seq (usub (sreg (.s 8)) (sreg (.s 10)) (sreg (.s 2))) <|
  .seq (synMulR (sreg (.p .K)) (sreg (.s 10)) (sreg (.s 11)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (ucopy (sreg (.s 7)) (sreg (.s 15)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.p .r)) (sreg (.s 16)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.s 0)) (sreg (.s 18)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.s 1)) (sreg (.s 19)) (sreg (.s 2))) <|
  .seq (uclear (sreg (.s 8))) <|
  .seq (uclear (sreg (.s 9))) <|
  .seq (uclear (sreg (.s 5))) (uclear (sreg (.s 10)))

def compactBasisCountsOutput (v : SynW → List (Fin (A+4))) (d g K D q o r : ℕ) :=
  let active := D-q-frontChunks d g K-backChunks d g K
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update v (.s 15) (List.replicate o tick))
      (.s 6) (List.replicate (K*backChunks d g K) tick))
      (.s 26) (List.replicate active tick)) (.s 11) (List.replicate (K*(D-q)) tick))
      (.s 16) (List.replicate r tick)) (.s 18) (List.replicate d tick))
      (.s 19) (List.replicate g tick)

def compactBasisCountsAfterCost (d g K D q o r : ℕ) :=
  (4*o+4)+(4*D+4)+(4*q+4)+synMulRCost K (D-q)+
    (4*o+4)+(4*r+4)+(4*d+4)+(4*g+4)+(2*q+2)+
    (2*frontChunks d g K+2)+(2*backChunks d g K+2)+(2*(D-q)+2)

private theorem sg_compactBasisCountsAfter (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (d g K D q o r : ℕ)
    (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D)
    (ho : (v (.s 7)).length=o) (hr : (v (.p .r)).length=r)
    (hs : ∀ i : Fin 32,i≠0 → i≠1 → i≠7 → v (.s i)=[]) :
    let vc := Function.update (Function.update (Function.update (Function.update (Function.update v
      (.s 8) (List.replicate q tick)) (.s 9) (List.replicate (frontChunks d g K) tick))
      (.s 5) (List.replicate (backChunks d g K) tick))
      (.s 26) (List.replicate (D-q-frontChunks d g K-backChunks d g K) tick))
      (.s 6) (List.replicate (o+K*backChunks d g K) tick)
    LayRuns body compactBasisCountsAfter (synG R vc)
      (synG R (compactBasisCountsOutput v d g K D q o r))
      (compactBasisCountsAfterCost d g K D q o r) := by
  dsimp only
  have h2 := hs 2 (by decide) (by decide) (by decide)
  have h3 := hs 3 (by decide) (by decide) (by decide)
  have h10 := hs 10 (by decide) (by decide) (by decide)
  have h11 := hs 11 (by decide) (by decide) (by decide)
  have h15 := hs 15 (by decide) (by decide) (by decide)
  have h16 := hs 16 (by decide) (by decide) (by decide)
  have h18 := hs 18 (by decide) (by decide) (by decide)
  have h19 := hs 19 (by decide) (by decide) (by decide)
  refine lr_weaken body
    ((sgU_sub body (a:=.s 7) (b:=.s 6) (t:=.s 2) (x:=o) (y:=o+K*backChunks d g K)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [ho]) (by simp)).seq <|
    (sgU_copy body (a:=.p .D) (b:=.s 10) (t:=.s 2) (x:=D) (y:=0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hD]) (by simp [h10])).seq <|
    (sgU_sub body (a:=.s 8) (b:=.s 10) (t:=.s 2) (x:=q) (y:=D)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp) (by simp)).seq <|
    (sgU_mulR body (a:=.p .K) (b:=.s 10) (c:=.s 11) (t₁:=.s 2) (t₂:=.s 3)
      (x:=K) (y:=D-q) (z:=0)
      (by decide)
      (by simp [h2]) (by simp [h3]) (by simp [hK]) (by simp) (by simp [h11])).seq <|
    (sgU_copy body (a:=.s 7) (b:=.s 15) (t:=.s 2) (x:=o) (y:=0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [ho]) (by simp [h15])).seq <|
    (sgU_copy body (a:=.p .r) (b:=.s 16) (t:=.s 2) (x:=r) (y:=0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hr]) (by simp [h16])).seq <|
    (sgU_copy body (a:=.s 0) (b:=.s 18) (t:=.s 2) (x:=d) (y:=0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hd]) (by simp [h18])).seq <|
    (sgU_copy body (a:=.s 1) (b:=.s 19) (t:=.s 2) (x:=g) (y:=0)
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hg]) (by simp [h19])).seq <|
    (sgU_clear body (a:=.s 8) (x:=q) (by simp)).seq <|
    (sgU_clear body (a:=.s 9) (x:=frontChunks d g K) (by simp)).seq <|
    (sgU_clear body (a:=.s 5) (x:=backChunks d g K) (by simp)).seq <|
    sgU_clear body (a:=.s 10) (x:=D-q) (by simp)) ?_ ?_
  · apply congrArg (synG R)
    funext z
    by_cases hz15 : z=.s 15
    · subst z; simp [compactBasisCountsOutput]
    by_cases hz6 : z=.s 6
    · subst z; simp [compactBasisCountsOutput]
    by_cases hz26 : z=.s 26
    · subst z; simp [compactBasisCountsOutput]
    by_cases hz11 : z=.s 11
    · subst z; simp [compactBasisCountsOutput]
    by_cases hz16 : z=.s 16
    · subst z; simp [compactBasisCountsOutput]
    by_cases hz18 : z=.s 18
    · subst z; simp [compactBasisCountsOutput]
    by_cases hz19 : z=.s 19
    · subst z; simp [compactBasisCountsOutput]
    by_cases hz8 : z=.s 8
    · subst z; simp [compactBasisCountsOutput,hs]
    by_cases hz9 : z=.s 9
    · subst z; simp [compactBasisCountsOutput,hs]
    by_cases hz5 : z=.s 5
    · subst z; simp [compactBasisCountsOutput,hs]
    by_cases hz10 : z=.s 10
    · subst z; simp [compactBasisCountsOutput,hs]
    simp [compactBasisCountsOutput,Function.update_of_ne,hz15,hz6,hz26,hz11,hz16,hz18,hz19,hz8,hz9,hz5,hz10]
  · simp only [compactBasisCountsAfterCost]
    omega

/-- Recompute reservations, synthesize the persistent counters, and restore all scratch. -/
def compactBasisCounts : Pr P (nT SXReg) Q A U :=
  .seq compactRowReserve (.seq (compactReserveCounts compactReserveWires) compactBasisCountsAfter)

def compactBasisCountsCost (d g K D o r : ℕ) :=
  let q := CompactGlobalRowPadding.rowAxes NW m d
  compactRowReserveCost d+compactReserveCountsCost d g K D q o+compactBasisCountsAfterCost d g K D q o r

 theorem sg_compactBasisCounts (body : P → Pr P (nT SXReg) Q A U)
    (R : Fin (nT SXReg) → List (Fin (A+4))) (v : SynW → List (Fin (A+4)))
    (d g K D o r : ℕ) (hdpos : 0<d) (hk : 1≤K)
    (hd : (v (.s 0)).length=d) (hg : (v (.s 1)).length=g)
    (hK : (v (.p .K)).length=K) (hD : (v (.p .D)).length=D)
    (ho : (v (.s 7)).length=o) (hr : (v (.p .r)).length=r)
    (hs : ∀ i : Fin 32,i≠0 → i≠1 → i≠7 → v (.s i)=[]) :
    LayRuns body compactBasisCounts (synG R v)
      (synG R (compactBasisCountsOutput v d g K D (CompactGlobalRowPadding.rowAxes NW m d) o r))
      (compactBasisCountsCost d g K D o r) := by
  let q := CompactGlobalRowPadding.rowAxes NW m d
  have hrow := sg_compactRowReserve body R v d hdpos hd
    (by
      intro i hi
      have hh : ∀ i : Fin 32, i∈[2,8,9,10,11,17,23] → i≠0 ∧ i≠1 ∧ i≠7 := by decide
      exact hs i (hh i hi).1 (hh i hi).2.1 (hh i hi).2.2)
  let vr := Function.update v (.s 8) (List.replicate q tick)
  have hcounts := sg_compactReserveCounts body compactReserveWires compactReserveWires_injective
    R vr d g K D q o hk
    (by intro i; fin_cases i <;> simp [vr,compactReserveWires,hd,hg,hK,hD,ho])
    (by intro i hi; fin_cases i <;> simp at hi <;> simp [vr,compactReserveWires,hs])
  have hafter := sg_compactBasisCountsAfter body R v d g K D q o r hd hg hK hD ho hr hs
  exact lr_weaken body (hrow.seq (hcounts.seq hafter)) rfl (by change compactRowReserveCost d+(compactReserveCountsCost d g K D q o+compactBasisCountsAfterCost d g K D q o r) ≤ compactRowReserveCost d+compactReserveCountsCost d g K D q o+compactBasisCountsAfterCost d g K D q o r; omega)

end
end IntegerMultBounds.MathlibTM2.Fast
