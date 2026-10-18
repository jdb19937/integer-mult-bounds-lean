module

public import IntegerMultBounds.MathlibTM2.Layer.Columns

/-!
# A network node on arrays with spectators

At a node the spectator carries the data family, so an array on `Y × DWire` with `m · k` active
bits is a bank of arrays on `Y`; the private centres start at zero. The node runs the network
program with each factor `(q, v)` implemented by `facImpl` — a change of basis, the forward
child on one slot (conjugated for `q = -1`), and the change of basis again —, translations and
slot XORs as pullbacks of the columns and slot phases as multiplications. On column arrays every
instruction is the T16 operator in every column (`slice_runWith`), so the node applies `C` to
every active bit (`nodeA_correct`, from `Impl.layerProgram_cAll`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks BinaryWalsh BinaryPhase BinaryColumns ComplexEndpoints
  ComplexFramedExecution
open IntegerMultBounds.Networks.Certificates.T16


variable {Y : Type} {k : ℕ}

/-- The product of forward kernels on the bits of slot `j`: what a child call computes. -/
noncomputable def slotProd (j : Fin m) : Arr Y (m * k) →ₗ[ℂ] Arr Y (m * k) :=
  ((List.finRange k).map fun c => kBit 1 (bitIdx j c)).prod

/-- Complex conjugation of an array. -/
def conjArr (u : Arr Y (m * k)) : Arr Y (m * k) := fun p => star (u p)

/-- Pull an array back along a change of basis applied in every column. -/
def pullArr (L : BinaryWalsh.Address m → BinaryWalsh.Address m) (u : Arr Y (m * k)) :
    Arr Y (m * k) :=
  fun p => u (p.1, ofCols (fun c => L (toCols p.2 c)))

/-- The machine's implementation of a factor: the slot is the first coordinate where the
direction is one. -/
noncomputable def facImpl (g : ZMod 4 × BinaryWalsh.Address m) (u : Arr Y (m * k)) : Arr Y (m * k) :=
  if h : ∃ j, g.2 j = 1 then
    pullArr (basisMap g.2 (Fin.find _ h))
      (if g.1 = 1 then slotProd (Fin.find _ h) (pullArr (basisMap g.2 (Fin.find _ h)) u)
        else conjArr (slotProd (Fin.find _ h) (conjArr (pullArr (basisMap g.2 (Fin.find _ h)) u))))
  else u

lemma lift_pullCols (L : BinaryWalsh.Address m → BinaryWalsh.Address m) (u : Arr Y (m * k)) :
    lift (pullCols L) u = pullArr L u := rfl

lemma lift_conjA (u : Arr Y (m * k)) : lift conjA u = conjArr u := by
  funext p; simp [lift, conjA, conjArr]

lemma lift_vf_single' (j : Fin m) (u : Arr Y (m * k)) :
    lift (fun g => BinaryColumns.vectorFactor k (1, Pi.single j 1) g) u = slotProd j u := by
  rw [lift_vf_single, slotProd, List.ofFn_eq_map]

lemma vectorFactor_zero (q : ZMod 4) (f : BinaryColumns.Arrays m k) :
    BinaryColumns.vectorFactor k (q, 0) f = f := by
  unfold BinaryColumns.vectorFactor
  have key : ∀ (cs : List (Fin k)) (f : BinaryColumns.Arrays m k),
      (cs.map fun c => columnKernel c q 0).prod f = f := by
    intro cs
    induction cs with
    | nil => intro f; rfl
    | cons c cs ih =>
        intro f
        simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
        funext x
        have : shift c (0 : BinaryWalsh.Address m) x = x := by simp [shift]
        simp only [columnKernel_apply, this]
        ring
  have h1 : (List.ofFn fun c : Fin k => columnKernel c q (0 : BinaryWalsh.Address m)) =
      (List.ofFn fun c : Fin k => c).map fun c => columnKernel c q 0 := by
    rw [List.map_ofFn]; rfl
  rw [h1]
  exact key _ f

/-- The machine's factor is the vendored factor, for the phases `±1` of the network. -/
lemma lift_vf_neg_single (j : Fin m) (u : Arr Y (m * k)) :
    lift (fun g => BinaryColumns.vectorFactor k (-1, Pi.single j 1) g) u =
      conjArr (slotProd j (conjArr u)) := by
  have hn : (fun f : BinaryColumns.Arrays m k =>
      BinaryColumns.vectorFactor k (-1, Pi.single j 1) f) =
      fun f => conjA (BinaryColumns.vectorFactor k (1, Pi.single j 1) (conjA f)) :=
    funext fun f => vectorFactor_neg _ f
  rw [hn, ← lift_vf_single']
  rfl

theorem facImpl_eq (g : ZMod 4 × BinaryWalsh.Address m) (hq : g.1 = 1 ∨ g.1 = -1)
    (u : Arr Y (m * k)) : facImpl g u = lift (vf k g) u := by
  obtain ⟨q, v⟩ := g
  unfold facImpl
  by_cases hp : ∃ j, v j = 1
  · rw [dite_eq_left hp]
    set j := Fin.find _ hp
    have hvj : v j = 1 := Fin.find_spec hp
    have hb : vf k (q, v) = fun f => pullCols (basisMap v j)
        (BinaryColumns.vectorFactor k (q, Pi.single j 1) (pullCols (basisMap v j) f)) :=
      funext fun f => vectorFactor_basis q v j hvj f
    rw [hb, lift_comp, lift_pullCols, lift_comp, lift_pullCols]
    dsimp only
    congr 1
    rcases hq with hq | hq
    · simp only at hq
      subst hq
      simp only [↓reduceIte, lift_vf_single']
    · simp only at hq
      subst hq
      rw [ite_eq_right (by decide), lift_vf_neg_single]
  · rw [dite_eq_right hp]
    have hv : v = 0 := by
      funext i
      have hi : v i ≠ 1 := fun h => hp ⟨i, h⟩
      have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      rcases h01 (v i) with h | h
      · exact h
      · exact absurd h hi
    subst hv
    funext p
    simp [lift, vf, vectorFactor_zero]

/-! ### Instructions on banks -/

/-- The slot phase `i^{c x_i}` in every column. -/
noncomputable def phaseArr (i : Fin m) (c : ZMod 4) (u : Arr Y (m * k)) : Arr Y (m * k) :=
  fun p => (∏ col : Fin k, BinaryPhase.phase (c * bitLift (toCols p.2 col i))) * u p

/-- Execute one instruction on a bank of spectator arrays, with factors implemented by `fac`. -/
noncomputable def execWith (fac : ZMod 4 × BinaryWalsh.Address m → Arr Y (m * k) → Arr Y (m * k)) :
    Instr → (NWire → Arr Y (m * k)) → (NWire → Arr Y (m * k))
  | .factor w g, x => Function.update x w (fac g (x w))
  | .gate g, x => FramedCircuit.moduleGate g x
  | .trans w v, x => Function.update x w (pullArr (· + v) (x w))
  | .xor w i j, x => Function.update x w (pullArr (Impl.xorMap i j) (x w))
  | .phase w i c, x => Function.update x w (phaseArr i c (x w))

/-- Execute a program on a bank, with factors implemented by `fac`. -/
noncomputable def runWith (fac : ZMod 4 × BinaryWalsh.Address m → Arr Y (m * k) → Arr Y (m * k)) :
    List Instr → (NWire → Arr Y (m * k)) → (NWire → Arr Y (m * k))
  | [], x => x
  | i :: rest, x => runWith fac rest (execWith fac i x)

lemma runWith_append (fac : ZMod 4 × BinaryWalsh.Address m → Arr Y (m * k) → Arr Y (m * k))
    (p q : List Instr) (x : NWire → Arr Y (m * k)) :
    runWith fac (p ++ q) x = runWith fac q (runWith fac p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons i rest ih => exact ih _

/-! ### The node -/

variable (k)

/-- The array of each wire: the data families, and zero on the private centres. -/
def bankOf (f : Arr (Y × DWire) (m * k)) : NWire → Arr Y (m * k)
  | .inl j => fun p => f ((p.1, j), p.2)
  | .inr _ => 0

/-- Reassemble an array from the arrays of the data families. -/
def unbank (B : NWire → Arr Y (m * k)) : Arr (Y × DWire) (m * k) := fun p => B (.inl p.1.2) (p.1.1, p.2)

/-- One node of the layer recursion. -/
noncomputable def nodeA (ds : Directions) (f : Arr (Y × DWire) (m * k)) : Arr (Y × DWire) (m * k) :=
  unbank k (runWith facImpl (program ds) (bankOf k f))

variable {k}

/-- The column array of a spectator value. -/
def slice (y : Y) (u : Arr Y (m * k)) : BinaryColumns.Arrays m k := fun x => u (y, ofCols x)

lemma slice_lift (y : Y) (T : BinaryColumns.Arrays m k → BinaryColumns.Arrays m k) (u : Arr Y (m * k)) :
    slice y (lift T u) = T (slice y u) := by
  funext x; simp only [slice, lift, toCols_ofCols]; rfl

lemma slice_add (y : Y) (u v : Arr Y (m * k)) : slice y (u + v) = slice y u + slice y v := rfl
lemma slice_smul (y : Y) (c : ℚ) (u : Arr Y (m * k)) : slice y (c • u) = c • slice y u := rfl
lemma slice_neg (y : Y) (u : Arr Y (m * k)) : slice y (-u) = -slice y u := rfl
lemma slice_csmul (y : Y) (c : ℂ) (u : Arr Y (m * k)) : slice y (c • u) = c • slice y u := rfl

lemma slice_sum (y : Y) (l : List (Arr Y (m * k))) : slice y l.sum = (l.map (slice y)).sum := by
  induction l with
  | nil => rfl
  | cons u l ih => simp [List.sum_cons, slice_add, ih]

lemma slice_moduleGate (y : Y) (g : Circuit.Gate NWire ℚ) (B : NWire → Arr Y (m * k)) :
    (fun w => slice y (FramedCircuit.moduleGate g B w)) =
      FramedCircuit.moduleGate g (fun w => slice y (B w)) := by
  funext w
  simp only [FramedCircuit.moduleGate]
  by_cases hw : w = g.target
  · subst hw
    simp only [Function.update_self, slice_add, slice_sum, List.map_map]
    rfl
  · simp [Function.update_of_ne hw]

/-! ### The column representation -/

/-- The T16 operators in every column. -/
noncomputable def ρcols (k : ℕ) :
    Module.End ℂ (BinaryWalsh.Arrays 73) →* Module.End ℂ (BinaryColumns.Arrays 73 k) where
  toFun := BinaryColumns.tensorColumns k
  map_one' := BinaryColumns.tensorColumns_one
  map_mul' := BinaryColumns.tensorColumns_mul

lemma liftColumns_pull (T : Module.End ℂ (BinaryWalsh.Arrays 73))
    (σ : BinaryWalsh.Address 73 → BinaryWalsh.Address 73) (hT : ∀ f x, T f x = f (σ x)) :
    ∀ (l : List (Fin k)), l.Nodup → ∀ (f : BinaryColumns.Arrays 73 k) x,
      (l.map fun j => BinaryColumns.liftColumn j T).prod f x =
        f (fun c => if c ∈ l then σ (x c) else x c) := by
  intro l hl
  induction l with
  | nil => intro f x; simp
  | cons j l ih =>
    intro f x
    obtain ⟨hj, hl⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    change T (fun y => _) (x j) = _
    rw [hT]
    simp only [ih hl]
    congr 1
    funext c
    by_cases hc : c = j
    · subst hc; simp [hj]
    · simp [hc, Function.update_of_ne hc]

lemma ρcols_pull (T : Module.End ℂ (BinaryWalsh.Arrays 73))
    (σ : BinaryWalsh.Address 73 → BinaryWalsh.Address 73) (hT : ∀ f x, T f x = f (σ x))
    (f : BinaryColumns.Arrays 73 k) (x : BinaryColumns.Address 73 k) :
    ρcols k T f x = f (fun c => σ (x c)) := by
  change (List.ofFn fun j : Fin k => BinaryColumns.liftColumn j T).prod f x = _
  rw [List.ofFn_eq_map, liftColumns_pull T σ hT _ (List.nodup_finRange k)]
  simp

lemma liftColumns_mul (T : Module.End ℂ (BinaryWalsh.Arrays 73))
    (φ : BinaryWalsh.Address 73 → ℂ) (hT : ∀ f x, T f x = φ x * f x) :
    ∀ (l : List (Fin k)), l.Nodup → ∀ (f : BinaryColumns.Arrays 73 k) x,
      (l.map fun j => BinaryColumns.liftColumn j T).prod f x = (l.map fun c => φ (x c)).prod * f x := by
  intro l hl
  induction l with
  | nil => intro f x; simp
  | cons j l ih =>
    intro f x
    obtain ⟨hj, hl⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    change T (fun y => _) (x j) = _
    rw [hT]
    simp only [ih hl, Function.update_eq_self]
    ring

lemma ρcols_mul (T : Module.End ℂ (BinaryWalsh.Arrays 73)) (φ : BinaryWalsh.Address 73 → ℂ)
    (hT : ∀ f x, T f x = φ x * f x) (f : BinaryColumns.Arrays 73 k) (x : BinaryColumns.Address 73 k) :
    ρcols k T f x = (∏ c : Fin k, φ (x c)) * f x := by
  change (List.ofFn fun j : Fin k => BinaryColumns.liftColumn j T).prod f x = _
  rw [List.ofFn_eq_map, liftColumns_mul T φ hT _ (List.nodup_finRange k), ← List.ofFn_eq_map,
    List.prod_ofFn]

lemma ρcols_kernel (g : ZMod 4 × BinaryWalsh.Address m) :
    ρcols k (BinaryWalsh.kernel g.1 g.2) = BinaryColumns.vectorFactor k g := by
  have h := BinaryColumns.tensorColumns_kernel_prod (k := k) [g]
  change BinaryColumns.tensorColumns k _ = _
  simpa using h

/-- On column arrays, an instruction is its T16 operator in every column. -/
lemma slice_execWith (y : Y) (i : Impl.KInstr NWire) (hi : i.Fit) (B : NWire → Arr Y (m * k)) :
    (fun w => slice y (execWith facImpl (ofK i) B w)) =
      i.run (ρcols k) (fun w => slice y (B w)) := by
  cases i with
  | factor w g =>
    funext w'
    simp only [ofK, execWith, Impl.KInstr.run]
    by_cases hw : w' = w
    · subst hw
      simp only [Function.update_self]
      rw [facImpl_eq g hi, slice_lift, ρcols_kernel]
      rfl
    · simp [Function.update_of_ne hw]
  | gate g => exact slice_moduleGate y g B
  | trans w v =>
    funext w'
    simp only [ofK, execWith, Impl.KInstr.run]
    by_cases hw : w' = w
    · subst hw
      simp only [Function.update_self]
      funext x
      rw [ρcols_pull _ (· + v) (fun f x => Impl.kernel_two_apply v f x)]
      simp [slice, pullArr]
    · simp [Function.update_of_ne hw]
  | xor w i j =>
    funext w'
    simp only [ofK, execWith, Impl.KInstr.run]
    by_cases hw : w' = w
    · subst hw
      simp only [Function.update_self]
      funext x
      rw [ρcols_pull _ (Impl.xorMap i j) (fun f x => rfl)]
      simp [slice, pullArr]
    · simp [Function.update_of_ne hw]
  | phase w i c =>
    funext w'
    simp only [ofK, execWith, Impl.KInstr.run]
    by_cases hw : w' = w
    · subst hw
      simp only [Function.update_self]
      funext x
      rw [ρcols_mul _ (fun x => BinaryPhase.phase (c * bitLift (x i))) (fun f x => rfl)]
      simp [slice, phaseArr]
    · simp [Function.update_of_ne hw]

/-- **Slicing a run.** On column arrays the node program is the T16 layer program in every
column. -/
lemma slice_runWith (y : Y) (l : List (Impl.KInstr NWire)) (hl : ∀ i ∈ l, i.Fit)
    (B : NWire → Arr Y (m * k)) :
    (fun w => slice y (runWith facImpl (l.map ofK) B w)) =
      Impl.runK (ρcols k) l (fun w => slice y (B w)) := by
  induction l generalizing B with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, runWith, Impl.runK]
    rw [ih (fun i' h' => hl i' (List.mem_cons_of_mem _ h')),
      slice_execWith y i (hl i List.mem_cons_self)]

/-- `C_all` is the product of the coordinate kernels. -/
lemma cAll_eq : Streams.cAll =
    ((coordinateKernels 73).map fun g => BinaryWalsh.kernel g.1 g.2).prod := by
  have h1 : (Multiplicative.ofAdd fun _ : Fin 73 => (1 : ZMod 4)) =
      ((List.finRange 73).map fun i => Multiplicative.ofAdd (Pi.single i (1 : ZMod 4))).prod := by
    rw [show ((List.finRange 73).map fun i => Multiplicative.ofAdd (Pi.single i (1 : ZMod 4))) =
      (((List.finRange 73).map fun i => Pi.single i (1 : ZMod 4)).map Multiplicative.ofAdd) by
        rw [List.map_map]; rfl, ← ofAdd_list_prod, ← Fin.sum_univ_def, Finset.univ_sum_single]
  rw [Streams.cAll, h1, map_list_prod, coordinateKernels, List.ofFn_eq_map, List.map_map,
    List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  simp [Streams.basisOp_single, Streams.stdBasis]

lemma ρcols_cAll : ρcols k Streams.cAll = (fullFrame (h := 73) k).toLinearMap := by
  rw [fullFrame_coordinate_product, cAll_eq]
  exact BinaryColumns.tensorColumns_kernel_prod (coordinateKernels 73)

/-- Every family is a stream unit of some replica, port and stream. -/
lemma family_streamUnit (j : DWire) :
    ∃ r a : ℕ, r < 16 ∧ a < 112 ∧ ∃ i : Fin 8, Streams.streamUnit r a i = Sum.inl j := by
  refine ⟨j.val / 896, j.val % 112, by omega, by omega, ⟨(j.val % 896) / 112, by omega⟩, ?_⟩
  simp only [Streams.streamUnit, Streams.famIdx, Sum.inl.injEq]
  ext
  simp only
  omega

/-- **A node of the layer recursion applies `C` to every active bit.** -/
theorem nodeA_correct (ds : Directions) (_hd : ComplexPhaseBudget.Realizes ds)
    (f : Arr (Y × DWire) (m * k)) : nodeA k ds f = Cfull (Y × DWire) (m * k) f := by
  funext ⟨⟨y, j⟩, b⟩
  obtain ⟨r, a, hr, ha, i, hj⟩ := family_streamUnit j
  have key := congrFun (congrFun (slice_runWith y Impl.layerProgram Impl.layerProgram_fit
    (bankOf k f)) (Sum.inl j)) (toCols b)
  rw [← program_eq ds] at key
  rw [← hj, Impl.layerProgram_cAll (ρcols k) _ hr ha i, hj, ρcols_cAll] at key
  have hb : b = ofCols (toCols b) := (ofCols_toCols b).symm
  calc nodeA k ds f ((y, j), b)
      = slice y (runWith facImpl (program ds) (bankOf k f) (Sum.inl j)) (toCols b) := by
        simp [nodeA, unbank, slice]
    _ = fullFrame k (slice y (bankOf k f (Sum.inl j))) (toCols b) := key
    _ = lift (fun g => fullFrame k g) (bankOf k f (Sum.inl j)) (y, b) := rfl
    _ = Cfull Y (m * k) (bankOf k f (Sum.inl j)) (y, b) := by rw [lift_fullFrame]
    _ = Cfull (Y × DWire) (m * k) f ((y, j), b) := by
        rw [Cfull_respec (fun y : Y => (y, j)) f y b]; rfl

end IntegerMultBounds.MathlibTM2.Layer
