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

/-! ### The program side -/

theorem callProgram_forward {s r : ℕ} (h : localReverse s = false) :
    callProgram s r = invocation (callReg s r) (callIn s r) (callOut s r) forwardWord := by
  simp [callProgram, h]

theorem callProgram_backward {s r : ℕ} (h : localReverse s = true) :
    callProgram s r = invocation (callReg s r) (callIn s r) (callOut s r) backwardWord := by
  simp [callProgram, h]

theorem entry_forward {s : ℕ} (h : localReverse s = false) (w : ℕ) :
    Trace.forwardInitial.label w = entryLabel (localReverse s) w := by simp [entryLabel, h]

theorem exit_forward {s : ℕ} (h : localReverse s = false) (w : ℕ) :
    Trace.forwardFinal.label w = exitLabel (localReverse s) w := by simp [exitLabel, h]

theorem entry_backward {s : ℕ} (h : localReverse s = true) (w : ℕ) :
    Trace.backwardInitial.label w = entryLabel (localReverse s) w := by simp [entryLabel, h]

theorem exit_backward {s : ℕ} (h : localReverse s = true) (w : ℕ) :
    Trace.backwardFinal.label w = exitLabel (localReverse s) w := by simp [exitLabel, h]

/-- A source register. -/
theorem lhs_X {s r a : ℕ} (F : CallFacts s r) (ha : a < 112) (y : NodeUnit → S) :
    runT ρ (callProgram s r) y (callReg s r a) =
      if localReverse s then
        portRep ρ a (ofAdd (frameX (s + 1) a)) (portRep ρ a (ofAdd (-frameX s a)) (y (callReg s r a)) +
          (-1 : ℤ) • portRep ρ a (ofAdd (-frameY s a)) (y (callReg s r (a + 112))))
      else portRep ρ a (ofAdd (frameX (s + 1) a))
        (portRep ρ a (ofAdd (-frameX s a)) (y (callReg s r a))) := by
  obtain ⟨e1, -, -, e4⟩ := F.ext a ha
  cases hrev : localReverse s
  · rw [callProgram_forward hrev, (forward_invocation ρ _ F.inj _ _ y).1 a ha,
      entry_forward hrev, exit_forward hrev,
      data_change ρ ha (callIn_X ha) (callOut_X ha) e1]
    rfl
  · rw [callProgram_backward hrev, (backward_invocation ρ _ F.inj _ _ y).1 a ha,
      entry_backward hrev, exit_backward hrev, entry_backward hrev,
      data_change ρ ha (callIn_X ha) (callOut_X ha) e1,
      data_change ρ ha (callIn_Y ha) (callOut_X ha) e4]
    simp only [ite_true, neg_one_smul, map_add, map_neg, sub_eq_add_neg]

/-- A target register. -/
theorem lhs_Y {s r a : ℕ} (F : CallFacts s r) (ha : a < 112) (y : NodeUnit → S) :
    runT ρ (callProgram s r) y (callReg s r (a + 112)) =
      if localReverse s then
        portRep ρ a (ofAdd (frameY (s + 1) a))
          (portRep ρ a (ofAdd (-frameY s a)) (y (callReg s r (a + 112))))
      else portRep ρ a (ofAdd (frameY (s + 1) a))
        (portRep ρ a (ofAdd (-frameY s a)) (y (callReg s r (a + 112))) +
          (1 : ℤ) • portRep ρ a (ofAdd (-frameX s a)) (y (callReg s r a))) := by
  obtain ⟨-, e2, e3, -⟩ := F.ext a ha
  cases hrev : localReverse s
  · have h2 := (forward_invocation ρ _ F.inj (callIn s r) (callOut s r) y).2.1 (a + 112)
      (by omega) (by omega)
    rw [callProgram_forward hrev, h2, show a + 112 - 112 = a by omega,
      entry_forward hrev, exit_forward hrev, entry_forward hrev,
      data_change ρ ha (callIn_X ha) (callOut_Y ha) e3,
      data_change ρ ha (callIn_Y ha) (callOut_Y ha) e2]
    simp only [Bool.false_eq_true, ite_false, one_smul, map_add, add_comm]
  · have h2 := (backward_invocation ρ _ F.inj (callIn s r) (callOut s r) y).2.1 (a + 112)
      (by omega) (by omega)
    rw [callProgram_backward hrev, h2, entry_backward hrev, exit_backward hrev,
      data_change ρ ha (callIn_Y ha) (callOut_Y ha) e2]
    rfl

/-- A helper register. -/
theorem lhs_helper {s r h : ℕ} (F : CallFacts s r) (hh : h < 480) (y : NodeUnit → S) :
    runT ρ (callProgram s r) y (callReg s r (224 + h)) =
      portRep ρ (famPort (helperFamily s r h))
        (ofAdd (maskFrame (helperMask (slotOf s r) (helperFamily s r h))))
        (y (callReg s r (224 + h))) := by
  have key : ρ (throughOp (callOut s r (224 + h)) (callIn s r (224 + h))
      (entryLabel (localReverse s) (224 + h)) (exitLabel (localReverse s) (224 + h))) =
        ρ (basisOp (portBasis (portData (famPort (helperFamily s r h))))
          (ofAdd (maskFrame (helperMask (slotOf s r) (helperFamily s r h))))) := by
    rw [callIn_helper hh, callOut_helper hh, hostIn, hostOut,
      helper_through _ _ (F.width h hh) _ _ (F.rank h hh)]
    rfl
  cases hrev : localReverse s
  · rw [callProgram_forward hrev, (forward_invocation ρ _ F.inj _ _ y).2.2.1 (224 + h)
      (by omega) (by omega), entry_forward hrev, exit_forward hrev, key]
    rfl
  · rw [callProgram_backward hrev, (backward_invocation ρ _ F.inj _ _ y).2.1 (224 + h)
      (by omega) (by omega), entry_backward hrev, exit_backward hrev, key]
    rfl

/-- Any other unit is unchanged. -/
theorem lhs_other {s r : ℕ} (F : CallFacts s r) (v : NodeUnit) (hv : ∀ w < 712, callReg s r w ≠ v)
    (y : NodeUnit → S) : runT ρ (callProgram s r) y v = y v := by
  cases hrev : localReverse s
  · rw [callProgram_forward hrev]
    exact (forward_invocation ρ _ F.inj _ _ y).2.2.2 v hv
  · rw [callProgram_backward hrev]
    exact (backward_invocation ρ _ F.inj _ _ y).2.2 v hv

/-! ### Correctness -/

theorem famUnit_inl {f : ℕ} (hf : f < 14336) : famUnit f = .inl ⟨f, hf⟩ := by
  simp only [famUnit, Sum.inl.injEq]
  exact Fin.ext (Nat.mod_eq_of_lt hf)

theorem not_helper_hostAcc {s r : ℕ} (F : CallFacts s r) {r' a' : ℕ} (hr' : r' < 16)
    (ha' : a' < 112) (i : Fin 8) (hn : ∀ h < 480, helperFamily s r h ≠ famIdx r' a' i) :
    hostAcc (groupData r' a') (slotOf s r) i = Vec.zero := by
  by_contra hne
  obtain ⟨h, hh, he⟩ := F.complete r' hr' a' ha' i hne
  exact hn h hh he

theorem streamUnit_val {r a : ℕ} (hr : r < 16) (ha : a < 112) (i : Fin 8) :
    streamUnit r a i = .inl ⟨famIdx r a i, famIdx_lt hr ha i⟩ := by
  simp only [streamUnit, Sum.inl.injEq]
  exact Fin.ext (Nat.mod_eq_of_lt (famIdx_lt hr ha i))

/-- Data units of the invocation are not helper families. -/
theorem data_not_helper {s r : ℕ} (F : CallFacts s r) (hr : r < 16) {a : ℕ} (ha : a < 112)
    (side : ℕ) (hside : side < 2) (h : ℕ) (hh : h < 480) :
    helperFamily s r h ≠ famIdx r a (toStream (2 * localPair s + side)) := by
  intro e
  have hw : callReg s r (a + 112 * side) = callReg s r (224 + h) := by
    rw [callReg_helper hh, famUnit_inl (F.helper_lt h hh)]
    interval_cases side
    · rw [show a + 112 * 0 = a by omega, callReg_X ha, streamUnit_val hr ha]
      simp only [Sum.inl.injEq, Fin.mk.injEq]
      rw [e]
      rfl
    · rw [show a + 112 * 1 = a + 112 by omega, callReg_Y ha, streamUnit_val hr ha]
      simp only [Sum.inl.injEq, Fin.mk.injEq]
      rw [e]
  have := F.inj _ (by omega) _ (by omega) hw
  omega

theorem toStream_two_mul_ne (n : ℕ) : toStream (2 * n) ≠ toStream (2 * n + 1) := by
  simp only [toStream, ne_eq, Fin.mk.injEq]
  omega

/-- A family that is neither a data unit of the invocation nor a helper family is no register. -/
theorem not_register {s r : ℕ} (hr : r < 16) (F : CallFacts s r) {r' a' : ℕ} (hr' : r' < 16)
    (ha' : a' < 112) {i : Fin 8} {j : Fin 14336} (hv : streamUnit r' a' i = .inl j)
    (hX : ¬ (r = r' ∧ i = toStream (2 * localPair s)))
    (hY : ¬ (r = r' ∧ i = toStream (2 * localPair s + 1)))
    (hhelp : ∀ h, h < 480 → ¬ helperFamily s r h = j.val) :
    ∀ w < 712, callReg s r w ≠ .inl j := by
  intro w hw e
  rw [← hv] at e
  by_cases h1 : w < 112
  · rw [callReg_X h1] at e
    obtain ⟨e1, -, e3⟩ := streamUnit_inj hr h1 hr' ha' e
    exact hX ⟨e1, e3.symm⟩
  · by_cases h2 : w < 224
    · have e' : callReg s r ((w - 112) + 112) = streamUnit r' a' i := by
        rw [show w - 112 + 112 = w by omega]; exact e
      rw [callReg_Y (by omega)] at e'
      obtain ⟨e1, -, e3⟩ := streamUnit_inj hr (by omega) hr' ha' e'
      exact hY ⟨e1, e3.symm⟩
    · by_cases h3 : w < 704
      · have e' : callReg s r (224 + (w - 224)) = streamUnit r' a' i := by
          rw [show 224 + (w - 224) = w by omega]; exact e
        rw [callReg_helper (by omega), famUnit_inl (F.helper_lt _ (by omega)), hv] at e'
        exact hhelp (w - 224) (by omega) (congrArg Fin.val (Sum.inl_injective e'))
      · simp [callReg, h1, h2, h3, hv] at e

/-- **A local invocation.** On every family, the program of the invocation at stage `s`,
replica `r` acts exactly as the stream events of that template event. -/
theorem call_correct {s r : ℕ} (hr : r < 16) (F : CallFacts s r) (y : NodeUnit → S)
    (j : Fin 14336) :
    runT ρ (callProgram s r) y (.inl j) = runUnits (portRep ρ) (eventOps (.local s r)) y (.inl j) := by
  set r' := j.val / 896
  set a' := j.val % 112
  set i := toStream ((j.val % 896) / 112)
  have hr' : r' < 16 := by omega
  have ha' : a' < 112 := Nat.mod_lt _ (by decide)
  have hv : streamUnit r' a' i = .inl j := streamUnit_decomp j
  have hfam : famIdx r' a' i = j.val := famIdx_decomp j.val j.isLt
  rw [← hv, local_rhs ρ s r hr' ha' y i]
  set Xs := toStream (2 * localPair s)
  set Ys := toStream (2 * localPair s + 1)
  set x : Fin 8 → S := fun i => portRep ρ a' (ofAdd (hostAcc (groupData r' a') (slotOf s r) i).toFun)
    (y (streamUnit r' a' i))
  by_cases hhelp : ∃ h < 480, helperFamily s r h = j.val
  · -- a helper
    obtain ⟨h, hh, he⟩ := hhelp
    have hreg : callReg s r (224 + h) = streamUnit r' a' i := by
      rw [callReg_helper hh, famUnit_inl (F.helper_lt h hh), hv]
      exact congrArg Sum.inl (Fin.ext he)
    rw [← hreg, lhs_helper ρ F hh y, hreg]
    have hdata : (if r = r' then dataEvents (portData a') s (localPair s) (localReverse s) else []).length = 0 ∨
        (i ≠ Xs ∧ i ≠ Ys) := by
      by_cases hrr : r = r'
      · right
        constructor
        · intro hi
          exact data_not_helper F hr (a := a') ha' 0 (by omega) h hh (by
            rw [he, ← hfam, hi, hrr]; rfl)
        · intro hi
          exact data_not_helper F hr (a := a') ha' 1 (by omega) h hh (by
            rw [he, ← hfam, hi, hrr])
      · left
        simp [hrr]
    have hrun : run (portRep ρ a') (if r = r' then dataEvents (portData a') s (localPair s)
        (localReverse s) else []) x i = x i := by
      by_cases hrr : r = r'
      · rcases hdata with hl | ⟨h1, h2⟩
        · simp [hrr, dataEvents] at hl
        · rw [if_pos hrr, run_data]
          simp only [Xs, Ys] at h1 h2
          simp [h1, h2]
      · rw [if_neg hrr]
        rfl
    rw [hrun]
    have hf : helperFamily s r h = j.val := he
    have hrep : famReplica (helperFamily s r h) = r' := by rw [hf]; rfl
    have hport : famPort (helperFamily s r h) = a' := by rw [hf]; rfl
    have hstr : famStream (helperFamily s r h) = i := by rw [hf]; rfl
    have hpure := F.pure h hh
    rw [hrep, hport, hstr] at hpure
    change _ = portRep ρ a' (ofAdd (hostAcc (groupData r' a') (slotOf s r) i).toFun)
      (y (streamUnit r' a' i))
    have hv' : ((hostAcc (groupData r' a') (slotOf s r) i).1, 0) =
        hostAcc (groupData r' a') (slotOf s r) i := Prod.ext rfl hpure.symm
    rw [hport, helperMask, hrep, hport, hstr, maskFrame_eq, hv']
  · simp only [not_exists, not_and] at hhelp
    have hacc : ∀ i', famIdx r' a' i' = j.val →
        hostAcc (groupData r' a') (slotOf s r) i' = Vec.zero := by
      intro i' hi'
      exact not_helper_hostAcc F hr' ha' i' (fun h hh e => hhelp h hh (e.trans hi'))
    have hxi : x i = y (streamUnit r' a' i) := by
      change portRep ρ a' _ _ = _
      rw [hacc i hfam, Vec.toFun_zero, op_zero]
    by_cases hrr : r = r'
    · -- the data streams of this replica are not hosted here
      have hxX : x Xs = y (streamUnit r' a' Xs) := by
        change portRep ρ a' _ _ = _
        rw [not_helper_hostAcc F hr' ha' Xs (fun h hh e => data_not_helper F hr ha' 0 (by omega) h hh
          (by rw [e, hrr]; rfl)), Vec.toFun_zero, op_zero]
      have hxY : x Ys = y (streamUnit r' a' Ys) := by
        change portRep ρ a' _ _ = _
        rw [not_helper_hostAcc F hr' ha' Ys (fun h hh e => data_not_helper F hr ha' 1 (by omega) h hh
          (by rw [e, hrr])), Vec.toFun_zero, op_zero]
      have hXY := toStream_two_mul_ne (localPair s)
      rw [if_pos hrr, run_data]
      by_cases hiX : i = Xs
      · -- a source
        have hreg : callReg s r a' = streamUnit r' a' i := by rw [callReg_X ha', hrr, hiX]
        rw [← hreg, lhs_X ρ F ha' y, hreg, if_pos hiX, hxi,
          show x (toStream (2 * localPair s + 1)) = y (callReg s r (a' + 112)) by
            rw [callReg_Y ha', hrr]; exact hxY]
        simp only [frameX, frameY, Vec.toFun_neg]
      · by_cases hiY : i = Ys
        · -- a target
          have hreg : callReg s r (a' + 112) = streamUnit r' a' i := by rw [callReg_Y ha', hrr, hiY]
          rw [← hreg, lhs_Y ρ F ha' y, hreg, if_neg hiX, if_pos hiY, hxi,
            show x (toStream (2 * localPair s)) = y (callReg s r a') by
              rw [callReg_X ha', hrr]; exact hxX]
          simp only [frameX, frameY, Vec.toFun_neg]
        · -- neither
          rw [if_neg hiX, if_neg hiY, hxi]
          exact lhs_other ρ F _ (by
            rw [hv]
            exact not_register hr F hr' ha' hv (fun h => hiX h.2) (fun h => hiY h.2) hhelp) y
    · rw [if_neg hrr]
      change _ = x i
      rw [hxi]
      exact lhs_other ρ F _ (by
        rw [hv]
        exact not_register hr F hr' ha' hv (fun h => hrr h.1) (fun h => hrr h.1) hhelp) y

end IntegerMultBounds.Networks.Certificates.T16.Impl
