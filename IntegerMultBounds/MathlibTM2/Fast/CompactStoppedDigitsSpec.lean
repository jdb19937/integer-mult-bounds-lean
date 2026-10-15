module

public import IntegerMultBounds.MathlibTM2.Fast.CompactStoppedDigits

/-!
# Semantic stopped-piece records from the executed digit scanner

The scanner's recursive fields and exponent accumulator are exactly those of
`compactStoppedPiece` mapped over the existing ordered digit pieces. Row
metadata is retained in the semantic list; it is absent from serialized fields.
This correspondence neither assumes precision for the stopped pieces nor claims
that their later layer execution has zero cost.
-/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node hiding LReg

/-- The exact serialized stopped digit fields, independent of row metadata. -/
theorem compactStoppedFields_eq (cutoff K X D oS J t : ℕ) :
    compactStoppedFields cutoff K oS D t =
      topPcRec K ((synPcs K X D oS J t).map (compactStoppedPiece cutoff)) := by
  induction t with
  | zero => simp [compactStoppedFields, synPcs, topPcRec]
  | succ t ih =>
    rw [compactStoppedFields, synPcs_succ]
    split_ifs with h
    · simpa using ih
    · simp only [List.map_cons, List.cons_append,
        List.nil_append, topPcRec, List.flatMap_cons]
      rw [← topPcRec, ← ih, compactStoppedPiece_fields]
      simp [synPc, bits_eq_mul]

/-- The executed exponent accumulator is the sum of the newly rebased piece
exponents, without identifying them with the original piece exponents. -/
theorem compactStoppedE_eq_expSeq (G F cutoff K X D oS J t : ℕ) :
    compactStoppedE G F cutoff D t =
      (((synPcs K X D oS J t).map (compactStoppedPiece cutoff)).map
        (fun pc => expSeq G F pc.u pc.j)).sum := by
  induction t with
  | zero => simp [compactStoppedE, synPcs]
  | succ t ih =>
    rw [compactStoppedE, synPcs_succ]
    split_ifs with h
    · simpa using ih
    · simp only [List.map_cons, List.cons_append,
        List.nil_append, List.sum_cons]
      rw [← ih, compactStoppedPiece_depth]
      rfl

/-- For the actual node program counts this is exactly the sum of `expZ` over
its stopped semantic pieces, so subsequent precision obligations use new depths. -/
theorem compactStoppedE_eq_expZ (ds : Networks.ComplexFramedExecution.Directions)
    (cutoff K X D oS J t : ℕ) :
    compactStoppedE (gateCount (program ds)) (factorCount (program ds)) cutoff D t =
      (((synPcs K X D oS J t).map (compactStoppedPiece cutoff)).map
        (fun pc => expZ pc.u ds pc.j)).sum := by
  simp_rw [expZ_eq_expSeq]
  exact compactStoppedE_eq_expSeq _ _ cutoff K X D oS J t

variable {Q A : ℕ} {U P : Type}
variable (body : P → Pr P (nT SXReg) Q A U) {R : Fin (nT SXReg) → List (Fin (A+4))}

/-- The actual charged scanner returns the semantic stopped-piece record list
and summed stopped exponents with exactly the same full frame and cost. -/
theorem sg_compactStoppedDigits_spec (G F : ℕ) (v : SynW → List (Fin (A+4)))
    (cutoff K X oS J D : ℕ)
    (hoS : v (.s 6)=List.replicate oS tick) (hK : (v (.p .K)).length=K)
    (hD : (v (.s 26)).length=D) (hpr : v (.p .pr)=[])
    (hs : ∀ i, 12 ≤ i → i ≤ 24 → i ≠ 22 → v (.s i)=[])
    (hc : (v (.s 22)).length=cutoff)
    (h29 : v (.s 29)=[]) (h30 : v (.s 30)=[]) (h31 : v (.s 31)=[])
    (h2 : v (.s 2)=[]) (h3 : v (.s 3)=[]) (h4 : v (.s 4)=[]) :
    let pcs := (synPcs K X D oS J D).map (compactStoppedPiece cutoff)
    LayRuns body (compactStoppedDigits G F) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.s 14)
        (List.replicate (synJ D D) tick)) (.s 16)
        (List.replicate ((pcs.map (fun pc => expSeq G F pc.u pc.j)).sum) tick))
        (.p .pr) (topRec (topPcRec K pcs))))
      (compactStoppedDigitsCost G F cutoff K oS D) := by
  dsimp only
  have h := sg_compactStoppedDigits body (R := R) G F v cutoff K oS D hoS hK hD hpr hs hc
    h29 h30 h31 h2 h3 h4
  rw [compactStoppedFields_eq cutoff K X D oS J D,
    compactStoppedE_eq_expSeq G F cutoff K X D oS J D] at h
  exact h

/-- Node-program specialization writes exactly the sum of semantic `expZ`s. -/
theorem sg_compactStoppedDigits_expZ (ds : Networks.ComplexFramedExecution.Directions)
    (v : SynW → List (Fin (A+4))) (cutoff K X oS J D : ℕ)
    (hoS : v (.s 6)=List.replicate oS tick) (hK : (v (.p .K)).length=K)
    (hD : (v (.s 26)).length=D) (hpr : v (.p .pr)=[])
    (hs : ∀ i, 12 ≤ i → i ≤ 24 → i ≠ 22 → v (.s i)=[])
    (hc : (v (.s 22)).length=cutoff)
    (h29 : v (.s 29)=[]) (h30 : v (.s 30)=[]) (h31 : v (.s 31)=[])
    (h2 : v (.s 2)=[]) (h3 : v (.s 3)=[]) (h4 : v (.s 4)=[]) :
    let pcs := (synPcs K X D oS J D).map (compactStoppedPiece cutoff)
    LayRuns body (compactStoppedDigits (gateCount (program ds)) (factorCount (program ds))) (synG R v)
      (synG R (Function.update (Function.update (Function.update v (.s 14)
        (List.replicate (synJ D D) tick)) (.s 16)
        (List.replicate ((pcs.map (fun pc => expZ pc.u ds pc.j)).sum) tick))
        (.p .pr) (topRec (topPcRec K pcs))))
      (compactStoppedDigitsCost (gateCount (program ds)) (factorCount (program ds)) cutoff K oS D) := by
  dsimp only
  simp_rw [expZ_eq_expSeq]
  exact sg_compactStoppedDigits_spec body _ _ v cutoff K X oS J D hoS hK hD hpr hs hc
    h29 h30 h31 h2 h3 h4

end IntegerMultBounds.MathlibTM2.Fast
