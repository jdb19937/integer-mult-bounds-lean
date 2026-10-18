module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.CallCheckDefs
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Wrappers
public import IntegerMultBounds.Networks.Certificates.T16.Impl.DataChart
public import IntegerMultBounds.Networks.Certificates.T16.Impl.StreamLocal
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Roles

/-! The program of the local invocation at stage `s`, replica `r`. Sources `0..111` and targets
`112..223` are the active pair's two streams of the 112 ports of replica `r`; helpers
`224..703` are the families of the role assignment; the eight private centres are the private
units. Data registers are wrapped by the adapters of their stream frames through the stage's
data chart, helpers by the inverse halves of their split transitions through their slice charts.
The word is forward or backward as the stage's orientation. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh Streams Pauli

/-- The family unit with index `f`. -/
def famUnit (f : ℕ) : NodeUnit := .inl ⟨f % 14336, Nat.mod_lt _ (by decide)⟩

/-- The registers of the invocation at stage `s`, replica `r`. -/
def callReg (s r w : ℕ) : NodeUnit :=
  if w < 112 then streamUnit r w (toStream (2 * localPair s))
  else if w < 224 then streamUnit r (w - 112) (toStream (2 * localPair s + 1))
  else if w < 704 then famUnit (helperFamily s r (w - 224))
  else .inr ⟨(w - 704) % 8, Nat.mod_lt _ (by decide)⟩

theorem portData_check {a : ℕ} (ha : a < 112) : portCheck (portData a) = true :=
  List.all_eq_true.mp ports_check _ (portData_mem ha)

/-! ### Data wrappers -/

/-- The pre-wrapper of a data register of port `a` with stream frame `f` and entry label `l`. -/
noncomputable def dataIn (s a : ℕ) (f : Fin 73 → ZMod 4) (l : ℕ) : List Prim :=
  if ha : a < 112 then
    if hs : 1 ≤ s ∧ s ≤ 8 then
      adapterIn (stageChart (portData_check ha) s hs) (splitStage (portData_check ha) s hs f).gs l
    else adapterIn (LinearEquiv.refl _ _) (split0 (portData_check ha) f).gs l
  else []

/-- The post-wrapper of a data register of port `a` with stream frame `f` and exit label `l`. -/
noncomputable def dataOut (s a : ℕ) (f : Fin 73 → ZMod 4) (l : ℕ) : List Prim :=
  if ha : a < 112 then
    if hs : 1 ≤ s ∧ s ≤ 8 then
      adapterOut (stageChart (portData_check ha) s hs) (splitStage (portData_check ha) s hs f).gs l
    else adapterOut (LinearEquiv.refl _ _) (split0 (portData_check ha) f).gs l
  else []

/-- Two frames agree off the local indices of the data chart. -/
def SameExterior (s : ℕ) (f f' : Fin 73 → ZMod 4) : Prop :=
  ∀ k, k ∉ dataIndices s → f k = f' k

/-- **Data registers through a word.** -/
theorem dataOut_dataIn {s a : ℕ} (ha : a < 112) {f f' : Fin 73 → ZMod 4} (he : SameExterior s f f')
    (l l' : ℕ) :
    throughOp (dataOut s a f' l') (dataIn s a f l) l l' =
      basisOp (portBasis (portData a)) (Multiplicative.ofAdd f') *
        basisOp (portBasis (portData a)) (Multiplicative.ofAdd (-f)) := by
  unfold dataOut dataIn
  simp only [ha, ↓reduceDIte]
  by_cases hs : 1 ≤ s ∧ s ≤ 8
  · simp only [hs, ↓reduceDIte]
    refine data_through _ _ ?_ l l'
    funext k
    change (if k ∈ stageIndices s hs then 0 else f k) = (if k ∈ stageIndices s hs then 0 else f' k)
    split_ifs with hk
    · rfl
    · exact he k (by simp [dataIndices, hs, hk])
  · simp only [hs, ↓reduceDIte]
    refine data_through _ _ ?_ l l'
    funext k
    change (if k ∈ lowIndices then 0 else f k) = (if k ∈ lowIndices then 0 else f' k)
    split_ifs with hk
    · rfl
    · exact he k (by simp [dataIndices, hs, hk])

/-! ### Helper wrappers -/

/-- The pre-wrapper of a helper register hosting family `f` between labels `l` and `l'`. -/
noncomputable def hostIn (slot f l l' : ℕ) : List Prim :=
  helperIn (portData_check (Nat.mod_lt f (by decide) : famPort f < 112)) (helperMask slot f) l l'

/-- The post-wrapper of a helper register. -/
noncomputable def hostOut (slot f l l' : ℕ) : List Prim :=
  helperOut (portData_check (Nat.mod_lt f (by decide) : famPort f < 112)) (helperMask slot f) l l'

/-! ### The invocation -/

/-- The pre-wrapper of register `w` of the invocation at stage `s`, replica `r`. -/
noncomputable def callIn (s r w : ℕ) : List Prim :=
  let rev := localReverse s
  if w < 112 then dataIn s w (frameVec (portData w) s 0).toFun (entryLabel rev w)
  else if w < 224 then dataIn s (w - 112) (frameVec (portData (w - 112)) s 1).toFun (entryLabel rev w)
  else if w < 704 then
    hostIn (slotOf s r) (helperFamily s r (w - 224)) (entryLabel rev w) (exitLabel rev w)
  else []

/-- The post-wrapper of register `w`. -/
noncomputable def callOut (s r w : ℕ) : List Prim :=
  let rev := localReverse s
  if w < 112 then dataOut s w (frameVec (portData w) (s + 1) 0).toFun (exitLabel rev w)
  else if w < 224 then
    dataOut s (w - 112) (frameVec (portData (w - 112)) (s + 1) 1).toFun (exitLabel rev w)
  else if w < 704 then
    hostOut (slotOf s r) (helperFamily s r (w - 224)) (entryLabel rev w) (exitLabel rev w)
  else []

/-- **The local invocation at stage `s`, replica `r`.** -/
noncomputable def callProgram (s r : ℕ) : List (TInstr NodeUnit) :=
  invocation (callReg s r) (callIn s r) (callOut s r)
    (if localReverse s then backwardWord else forwardWord)

end IntegerMultBounds.Networks.Certificates.T16.Impl
