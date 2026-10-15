module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedCutoff

/-!
# Executed threshold-to-stopped-record pipeline

The cutoff is computed from the supplied threshold, consumed by the actual
scanner, then cleared. The caller supplies neither a cutoff nor an execution
oracle. The source threshold itself, its relation to global dimension, stopped
precision, and absorption of the explicit preparation/scanner cost remain
separate obligations.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
variable {Q A : ℕ} {U P : Type}
variable (body : P → Pr P (nT SXReg) Q A U) {R : Fin (nT SXReg) → List (Fin (A+4))}

noncomputable def compactStoppedPipeline (source : SynW) (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq (compactStoppedCutoff source) <|
  .seq (compactStoppedDigits G F) (uclear (sreg (.s 22)))

def compactStoppedPipelineCost (G F K oS D T : ℕ) : ℕ :=
  compactStoppedCutoffCost T + compactStoppedDigitsCost G F (Nat.log m T) K oS D +
    (2*Nat.log m T+2)

/-- Actual composed execution produces the semantic stopped records and their
`expZ` sum, with no supplied-cutoff hypothesis. Only depth, exponent and record
output change; s22 and every other scratch wire are restored. -/
theorem sg_compactStoppedPipeline (ds : Networks.ComplexFramedExecution.Directions)
    (source : SynW) (v : SynW → List (Fin (A+4))) (K X oS J D T : ℕ)
    (hTpos : 0 < T) (hT : (v source).length=T)
    (hsource2 : source ≠ .s 2) (hsource17 : source ≠ .s 17)
    (hsource22 : source ≠ .s 22) (hsource23 : source ≠ .s 23) (hsource29 : source ≠ .s 29)
    (hoS : v (.s 6)=List.replicate oS tick) (hK : (v (.p .K)).length=K)
    (hD : (v (.s 26)).length=D) (hpr : v (.p .pr)=[])
    (hs : ∀ i, 12 ≤ i → i ≤ 24 → v (.s i)=[])
    (h29 : v (.s 29)=[]) (h30 : v (.s 30)=[]) (h31 : v (.s 31)=[])
    (h2 : v (.s 2)=[]) (h3 : v (.s 3)=[]) (h4 : v (.s 4)=[]) :
    let pcs := (synPcs K X D oS J D).map (compactStoppedPiece (Nat.log m T))
    LayRuns body (compactStoppedPipeline source (gateCount (program ds)) (factorCount (program ds)))
      (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.s 14)
        (List.replicate (synJ D D) tick)) (.s 16)
        (List.replicate ((pcs.map (fun pc => expZ pc.u ds pc.j)).sum) tick))
        (.p .pr) (topRec (topPcRec K pcs))))
      (compactStoppedPipelineCost (gateCount (program ds)) (factorCount (program ds)) K oS D T) := by
  dsimp only
  have h17 := hs 17 (by decide) (by decide)
  have h22 := hs 22 (by decide) (by decide)
  have h23 := hs 23 (by decide) (by decide)
  refine lr_weaken body
    ((sg_compactStoppedCutoff body source v T hTpos hT hsource2 hsource17 hsource22 hsource23
      hsource29 h2 h17 h22 h23 h29).seq <|
    (sg_compactStoppedDigits_expZ body ds _ (Nat.log m T) K X oS J D
      (by simp [hoS]) (by simp [hK]) (by simp [hD]) (by simp [hpr])
      (by intro i hi12 hi24 hi22; simp [hi22, hs i hi12 hi24])
      (by simp) (by simp [h29]) (by simp [h30]) (by simp [h31])
      (by simp [h2]) (by simp [h3]) (by simp [h4])).seq <|
    sgU_clear body (a:=.s 22) (x:=Nat.log m T) (by simp)) ?_ ?_
  · apply congrArg (synG R)
    funext z
    by_cases hz : z = .s 22
    · subst z
      simp [h22]
    · simp [Function.update_apply, hz]
  · simp only [compactStoppedPipelineCost]
    omega

/-- The input threshold cannot occupy an output wire because those wires are
initially empty. Consequently the full-frame theorem also preserves its source. -/
theorem compactStoppedPipeline_source_preserved
    (v : SynW → List (Fin (A+4))) (source : SynW) (T depth exponent : ℕ)
    (records : List (Fin (A+4))) (hTpos : 0 < T) (hT : (v source).length=T)
    (h14 : v (.s 14)=[]) (h16 : v (.s 16)=[]) (hpr : v (.p .pr)=[]) :
    (Function.update (Function.update (Function.update v (.s 14)
      (List.replicate depth tick)) (.s 16) (List.replicate exponent tick)) (.p .pr) records)
      source = v source := by
  have hne14 : source ≠ .s 14 := by intro h; subst source; simp [h14] at hT; omega
  have hne16 : source ≠ .s 16 := by intro h; subst source; simp [h16] at hT; omega
  have hnepr : source ≠ .p .pr := by intro h; subst source; simp [hpr] at hT; omega
  simp [hne14, hne16, hnepr]

end IntegerMultBounds.MathlibTM2.Fast
