module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallDef

/-! **Correctness of a local invocation.** Under facts that are checked on the data (distinct
registers, pure hosted slices of matching widths, every hosted slice of the slot on a helper, and
data frames agreeing off the chart), the program of the local invocation at stage `s`, replica
`r` acts on every family exactly as the stream events of that template event. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh Streams Pauli Multiplicative

variable {S : Type*} [AddCommGroup S] [Module ℂ S] [Module ℚ S] [IsScalarTower ℚ ℂ S]
variable (ρ : Module.End ℂ (Arrays 73) →* Module.End ℂ S)

/-- The stream operators of the ports, through `ρ`. -/
noncomputable def portRep (a : ℕ) : Op S := ρ.comp (portOp a)

theorem portRep_apply (a : ℕ) (c : Fin 73 → ZMod 4) (z : S) :
    portRep ρ a (ofAdd c) z = ρ (basisOp (portBasis (portData a)) (ofAdd c)) z := rfl

/-- The source frame of port `a` at stage `s`, and the others. -/
def frameX (s a : ℕ) : Fin 73 → ZMod 4 := (frameVec (portData a) s 0).toFun
def frameY (s a : ℕ) : Fin 73 → ZMod 4 := (frameVec (portData a) s 1).toFun

/-- The facts a local invocation needs, all checked on the data. -/
structure CallFacts (s r : ℕ) : Prop where
  inj : ∀ w < 712, ∀ w' < 712, callReg s r w = callReg s r w' → w = w'
  helper_lt : ∀ h < 480, helperFamily s r h < 14336
  pure : ∀ h < 480, (hostAcc (groupData (famReplica (helperFamily s r h))
    (famPort (helperFamily s r h))) (slotOf s r) (famStream (helperFamily s r h))).2 = 0
  width : ∀ h < 480, (maskIndices (helperMask (slotOf s r) (helperFamily s r h))).length ≤ 9
  rank : ∀ h < 480, Module.finrank Geometry.F (Tableau.xRange (edgeRealization
    (entryLabel (localReverse s) (224 + h)) (exitLabel (localReverse s) (224 + h))).binary) =
      (maskIndices (helperMask (slotOf s r) (helperFamily s r h))).length
  complete : ∀ r' < 16, ∀ a' < 112, ∀ i : Fin 8,
    hostAcc (groupData r' a') (slotOf s r) i ≠ Vec.zero →
      ∃ h < 480, helperFamily s r h = famIdx r' a' i
  ext : ∀ a < 112, SameExterior s (frameX s a) (frameX (s + 1) a) ∧
    SameExterior s (frameY s a) (frameY (s + 1) a) ∧
    SameExterior s (frameX s a) (frameY (s + 1) a) ∧
    SameExterior s (frameY s a) (frameX (s + 1) a)

/-! ### Registers -/

theorem callIn_X {s r a : ℕ} (ha : a < 112) :
    callIn s r a = dataIn s a (frameX s a) (entryLabel (localReverse s) a) := by
  simp [callIn, ha, frameX]

theorem callIn_Y {s r a : ℕ} (ha : a < 112) :
    callIn s r (a + 112) = dataIn s a (frameY s a) (entryLabel (localReverse s) (a + 112)) := by
  simp [callIn, show ¬ a + 112 < 112 by omega, show a + 112 < 224 by omega, frameY]

theorem callOut_X {s r a : ℕ} (ha : a < 112) :
    callOut s r a = dataOut s a (frameX (s + 1) a) (exitLabel (localReverse s) a) := by
  simp [callOut, ha, frameX]

theorem callOut_Y {s r a : ℕ} (ha : a < 112) :
    callOut s r (a + 112) = dataOut s a (frameY (s + 1) a) (exitLabel (localReverse s) (a + 112)) := by
  simp [callOut, show ¬ a + 112 < 112 by omega, show a + 112 < 224 by omega, frameY]

theorem callIn_helper {s r h : ℕ} (hh : h < 480) :
    callIn s r (224 + h) = hostIn (slotOf s r) (helperFamily s r h)
      (entryLabel (localReverse s) (224 + h)) (exitLabel (localReverse s) (224 + h)) := by
  simp [callIn, show ¬ 224 + h < 112 by omega, show ¬ 224 + h < 224 by omega,
    show 224 + h < 704 by omega]

theorem callOut_helper {s r h : ℕ} (hh : h < 480) :
    callOut s r (224 + h) = hostOut (slotOf s r) (helperFamily s r h)
      (entryLabel (localReverse s) (224 + h)) (exitLabel (localReverse s) (224 + h)) := by
  simp [callOut, show ¬ 224 + h < 112 by omega, show ¬ 224 + h < 224 by omega,
    show 224 + h < 704 by omega]

theorem callReg_X {s r a : ℕ} (ha : a < 112) :
    callReg s r a = streamUnit r a (toStream (2 * localPair s)) := by
  simp [callReg, ha]

theorem callReg_Y {s r a : ℕ} (ha : a < 112) :
    callReg s r (a + 112) = streamUnit r a (toStream (2 * localPair s + 1)) := by
  simp [callReg, show ¬ a + 112 < 112 by omega, show a + 112 < 224 by omega]

theorem callReg_helper {s r h : ℕ} (hh : h < 480) :
    callReg s r (224 + h) = famUnit (helperFamily s r h) := by
  simp [callReg, show ¬ 224 + h < 112 by omega, show ¬ 224 + h < 224 by omega,
    show 224 + h < 704 by omega]

/-- A frame change through the data wrappers of two registers of the same port. -/
theorem data_change {s r a : ℕ} (ha : a < 112) {win wout : ℕ} {f f' : Fin 73 → ZMod 4}
    (hin : callIn s r win = dataIn s a f (entryLabel (localReverse s) win))
    (hout : callOut s r wout = dataOut s a f' (exitLabel (localReverse s) wout))
    (he : SameExterior s f f') (z : S) :
    ρ (throughOp (callOut s r wout) (callIn s r win) (entryLabel (localReverse s) win)
        (exitLabel (localReverse s) wout)) z =
      portRep ρ a (ofAdd f') (portRep ρ a (ofAdd (-f)) z) := by
  rw [hin, hout, dataOut_dataIn ha he, map_mul, Module.End.mul_apply]
  rfl

/-! ### Families -/

theorem famIdx_decomp (j : ℕ) (hj : j < 14336) :
    famIdx (j / 896) (j % 112) (toStream ((j % 896) / 112)) = j := by
  simp only [famIdx, toStream]
  omega

theorem streamUnit_decomp (j : Fin 14336) :
    streamUnit (j.val / 896) (j.val % 112) (toStream ((j.val % 896) / 112)) = .inl j := by
  simp only [streamUnit, famIdx_decomp j.val j.isLt]
  congr
  exact Nat.mod_eq_of_lt j.isLt

theorem famUnit_eq (f : ℕ) (hf : f < 14336) :
    famUnit f = streamUnit (famReplica f) (famPort f) (famStream f) := by
  rw [famReplica, famPort, famStream, streamUnit_decomp ⟨f, hf⟩, famUnit]
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt hf)

/-! ### The stream side -/

theorem hostAcc_zero_apply {a : ℕ} {G : GroupData} {slot : ℕ} {i : Fin 8}
    (h : hostAcc G slot i = Vec.zero) (z : S) :
    portRep ρ a (ofAdd (hostAcc G slot i).toFun) z = z := by
  rw [h, Vec.toFun_zero, op_zero]

/-- The stream side of a local event at one group. -/
theorem local_rhs (s r : ℕ) {r' a' : ℕ} (hr' : r' < 16) (ha' : a' < 112) (y : NodeUnit → S)
    (i : Fin 8) :
    runUnits (portRep ρ) (eventOps (.local s r)) y (streamUnit r' a' i) =
      run (portRep ρ a') (if r = r' then dataEvents (portData a') s (localPair s) (localReverse s)
          else [])
        (fun i => portRep ρ a' (ofAdd (hostAcc (groupData r' a') (slotOf s r) i).toFun)
          (y (streamUnit r' a' i))) i := by
  have h := congrFun (view_eventOps (portRep ρ) hr' ha' (.local s r) y) i
  rw [h]
  simp only [expand]
  rw [run_append, run_hosted]
  rfl

end IntegerMultBounds.Networks.Certificates.T16.Impl
