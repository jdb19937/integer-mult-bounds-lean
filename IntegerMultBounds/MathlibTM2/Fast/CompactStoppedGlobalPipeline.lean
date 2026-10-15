module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedGlobalCutoff

/-! # Executed selected-beta global-dimension stopped scanner
The cutoff comes from preserved p.D, independently of the chunk length on s26.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg
variable {Q A : ℕ} {U P : Type}
variable (body : P → Pr P (nT SXReg) Q A U) {R : Fin (nT SXReg) → List (Fin (A+4))}

noncomputable def compactStoppedGlobalPipeline (G F : ℕ) : Pr P (nT SXReg) Q A U :=
  .seq compactStoppedGlobalCutoff <|
  .seq (compactStoppedDigits G F) (uclear (sreg (.s 22)))

def compactStoppedGlobalPipelineCost (G F K oS D globalD : ℕ) : ℕ :=
  compactStoppedGlobalCutoffCost globalD + compactStoppedDigitsCost G F (compactGlobalCutoff globalD) K oS D +
    (2*compactGlobalCutoff globalD+2)

/-- Actual composed execution produces the semantic stopped records and their
`expZ` sum, with no supplied-cutoff hypothesis. Only depth, exponent and record
output change; s22 and every other scratch wire are restored. -/
theorem sg_compactStoppedGlobalPipeline (ds : Networks.ComplexFramedExecution.Directions)
    (v : SynW → List (Fin (A+4))) (K X oS J D globalD : ℕ)
    (hglobalDpos : 0 < globalD) (hglobalD : (v (.p .D)).length=globalD)
    (hoS : v (.s 6)=List.replicate oS tick) (hK : (v (.p .K)).length=K)
    (hD : (v (.s 26)).length=D) (hpr : v (.p .pr)=[])
    (hs : ∀ i, 12 ≤ i → i ≤ 24 → v (.s i)=[])
    (h29 : v (.s 29)=[]) (h30 : v (.s 30)=[]) (h31 : v (.s 31)=[])
    (h2 : v (.s 2)=[]) (h3 : v (.s 3)=[]) (h4 : v (.s 4)=[]) :
    let pcs := (synPcs K X D oS J D).map (compactStoppedPiece (compactGlobalCutoff globalD))
    LayRuns body (compactStoppedGlobalPipeline (gateCount (program ds)) (factorCount (program ds)))
      (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.s 14)
        (List.replicate (synJ D D) tick)) (.s 16)
        (List.replicate ((pcs.map (fun pc => expZ pc.u ds pc.j)).sum) tick))
        (.p .pr) (topRec (topPcRec K pcs))))
      (compactStoppedGlobalPipelineCost (gateCount (program ds)) (factorCount (program ds)) K oS D globalD) := by
  dsimp only
  have h17 := hs 17 (by decide) (by decide)
  have h22 := hs 22 (by decide) (by decide)
  have h23 := hs 23 (by decide) (by decide)
  refine lr_weaken body
    ((sg_compactStoppedGlobalCutoff body v globalD hglobalDpos hglobalD
      h2 h17 h22 h23 h29).seq <|
    (sg_compactStoppedDigits_expZ body ds _ (compactGlobalCutoff globalD) K X oS J D
      (by simp [hoS]) (by simp [hK]) (by simp [hD]) (by simp [hpr])
      (by intro i hi12 hi24 hi22; simp [hi22, hs i hi12 hi24])
      (by simp) (by simp [h29]) (by simp [h30]) (by simp [h31])
      (by simp [h2]) (by simp [h3]) (by simp [h4])).seq <|
    sgU_clear body (a:=.s 22) (x:=compactGlobalCutoff globalD) (by simp)) ?_ ?_
  · apply congrArg (synG R)
    funext z
    by_cases hz : z = .s 22
    · subst z
      simp [h22]
    · simp [Function.update_apply, hz]
  · simp only [compactStoppedGlobalPipelineCost]
    omega

/-- Every actual emitted stopped record satisfies the selected integer leaf budget. -/
theorem compactStoppedGlobalPipeline_leaf_bound (K X oS J D globalD t : ℕ)
    (hglobalD : 0 < globalD) (hlarge : selectedStopDen ≤ Nat.log m globalD)
    (pc : TopPc)
    (hpc : pc ∈ (synPcs K X D oS J t).map (compactStoppedPiece (compactGlobalCutoff globalD))) :
    pc.u^selectedStopDen ≤ globalD := by
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hpc
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp horiginal
  by_cases hz : synDg D j = 0
  · simp [hz] at hj
  · simp only [hz, ↓reduceIte, Option.some.injEq] at hj
    subst original
    exact compactGlobalCutoff_leaf_bound globalD (synDg D j) j hglobalD hlarge
      (Nat.mod_lt _ m_pos)

end IntegerMultBounds.MathlibTM2.Fast
