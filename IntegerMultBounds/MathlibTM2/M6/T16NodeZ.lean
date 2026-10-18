module

public import IntegerMultBounds.MathlibTM2.M6.T16Arr

/-!
# The scaled T16 node on Gaussian-integer arrays

The T16 counterpart of `Layer.NodeZ`. The machine stores Gaussian integers, so it runs a scaled
node: every gate is doubled (the fitted program's coefficients are halves of integers), a child
returns `2^Tc` times its result and the other wires are multiplied by `2^Tc`, and the other
primitives run as their tape passes (`T16Arr.tapeZ`), unscaled. The node's bank holds the data
families of its input and zero arrays on the eight private centres.

* `facImplH`, `facImplH_eq`: at any width, the machine's factor (a change of basis to a pivot, the
  child on that slot, the change of basis again) is `lift (vectorFactor k g)` for the phases `±1`.
* `view_runT`: the views of a scaled run are `2^(progExpT Tc l)` times the run through
  `T16Arr.liftRep` on the views.
* `nodeT_correct`: if the child computes `2^Tc` times `C` on the bits of a slot, the scaled T16
  node computes `2^(progExpT Tc fittedProgram)` times `C` on every active bit, in the form of
  `NodeZ.nodeM_correct`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M6.T16NodeZ

open IntegerMultBounds.Networks BinaryPhase IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Certificates.T16 Streams
open IntegerMultBounds.MathlibTM2.M6.T16Node IntegerMultBounds.MathlibTM2.M6.T16Arr

/-! ### The machine's factor on decoded arrays, at any width -/

section FacArr

variable {Y : Type} {h k : ℕ}

/-- Complex conjugation of an array. -/
def conjArrH (u : Arr Y (h * k)) : Arr Y (h * k) := fun p => star (u p)

/-- Pull an array back along a change of basis applied in every column. -/
def pullArrH (L : BinaryWalsh.Address h → BinaryWalsh.Address h) (u : Arr Y (h * k)) :
    Arr Y (h * k) :=
  fun p => u (p.1, ofCols (fun c => L (toCols p.2 c)))

/-- The product of forward kernels on the bits of slot `j`: what a child call computes. -/
noncomputable def slotProdH (j : Fin h) : Arr Y (h * k) →ₗ[ℂ] Arr Y (h * k) :=
  ((List.finRange k).map fun c => kBit 1 (bitIdx j c)).prod

/-- The machine's implementation of a factor: the slot is the first coordinate where the
direction is one. -/
noncomputable def facImplH (g : ZMod 4 × BinaryWalsh.Address h) (u : Arr Y (h * k)) :
    Arr Y (h * k) :=
  if hp : ∃ j, g.2 j = 1 then
    pullArrH (basisMap g.2 (Fin.find _ hp))
      (if g.1 = 1 then slotProdH (Fin.find _ hp) (pullArrH (basisMap g.2 (Fin.find _ hp)) u)
        else conjArrH (slotProdH (Fin.find _ hp)
          (conjArrH (pullArrH (basisMap g.2 (Fin.find _ hp)) u))))
  else u

lemma lift_pullColsH (L : BinaryWalsh.Address h → BinaryWalsh.Address h) (u : Arr Y (h * k)) :
    lift (pullCols L) u = pullArrH L u := rfl

lemma lift_conjAH (u : Arr Y (h * k)) : lift conjA u = conjArrH u := by
  funext p; simp [lift, conjA, conjArrH]

lemma lift_vf_singleH (j : Fin h) (u : Arr Y (h * k)) :
    lift (fun g => BinaryColumns.vectorFactor k (1, Pi.single j 1) g) u = slotProdH j u := by
  rw [lift_vf_single, slotProdH, List.ofFn_eq_map]

lemma vectorFactor_zeroH (q : ZMod 4) (f : BinaryColumns.Arrays h k) :
    BinaryColumns.vectorFactor k (q, 0) f = f := by
  unfold BinaryColumns.vectorFactor
  have key : ∀ (cs : List (Fin k)) (f : BinaryColumns.Arrays h k),
      (cs.map fun c => BinaryColumns.columnKernel c q 0).prod f = f := by
    intro cs
    induction cs with
    | nil => intro f; rfl
    | cons c cs ih =>
        intro f
        simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
        funext x
        have : BinaryColumns.shift c (0 : BinaryWalsh.Address h) x = x := by
          simp [BinaryColumns.shift]
        simp only [BinaryColumns.columnKernel_apply, this]
        ring
  have h1 : (List.ofFn fun c : Fin k => BinaryColumns.columnKernel c q (0 : BinaryWalsh.Address h)) =
      (List.ofFn fun c : Fin k => c).map fun c => BinaryColumns.columnKernel c q 0 := by
    rw [List.map_ofFn]; rfl
  rw [h1]
  exact key _ f

lemma lift_vf_neg_singleH (j : Fin h) (u : Arr Y (h * k)) :
    lift (fun g => BinaryColumns.vectorFactor k (-1, Pi.single j 1) g) u =
      conjArrH (slotProdH j (conjArrH u)) := by
  have hn : (fun f : BinaryColumns.Arrays h k =>
      BinaryColumns.vectorFactor k (-1, Pi.single j 1) f) =
      fun f => conjA (BinaryColumns.vectorFactor k (1, Pi.single j 1) (conjA f)) :=
    funext fun f => vectorFactor_neg _ f
  rw [hn, ← lift_vf_singleH, ← lift_conjAH, ← lift_conjAH, ← lift_comp, ← lift_comp]

/-- **The machine's factor** is the vendored factor, for the phases `±1`. -/
theorem facImplH_eq (g : ZMod 4 × BinaryWalsh.Address h) (hq : g.1 = 1 ∨ g.1 = -1)
    (u : Arr Y (h * k)) :
    facImplH g u = lift (fun f => BinaryColumns.vectorFactor k g f) u := by
  obtain ⟨q, v⟩ := g
  unfold facImplH
  by_cases hp : ∃ j, v j = 1
  · rw [dite_eq_left hp]
    set j := Fin.find _ hp
    have hvj : v j = 1 := Fin.find_spec hp
    have hb : (fun f => BinaryColumns.vectorFactor k (q, v) f) = fun f => pullCols (basisMap v j)
        (BinaryColumns.vectorFactor k (q, Pi.single j 1) (pullCols (basisMap v j) f)) :=
      funext fun f => vectorFactor_basis q v j hvj f
    rw [hb, lift_comp, lift_pullColsH, lift_comp, lift_pullColsH]
    dsimp only
    congr 1
    rcases hq with hq | hq
    · simp only at hq
      subst hq
      simp only [↓reduceIte, lift_vf_singleH]
    · simp only at hq
      subst hq
      rw [ite_eq_right (by decide), lift_vf_neg_singleH]
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
    simp [lift, vectorFactor_zeroH]

lemma pullArrH_smul (L : BinaryWalsh.Address h → BinaryWalsh.Address h) (c : ℂ)
    (u : Arr Y (h * k)) : pullArrH L (c • u) = c • pullArrH L u := rfl

lemma conjArrH_two_pow_smul (s : ℕ) (u : Arr Y (h * k)) :
    conjArrH ((2 : ℂ) ^ s • u) = (2 : ℂ) ^ s • conjArrH u := by
  funext p; simp [conjArrH]

end FacArr

/-! ### The scaled tape semantics at width 73 -/

section Z

variable {Y : Type} {k n : ℕ} (e : Fin (73 * k) → Fin n)

/-- A factor `(q, v)` with child `child j` on slot `j` (scaled by `2^Tc`), as `NodeZ.facM`. -/
noncomputable def facMH (child : Fin 73 → ZArr Y n → ZArr Y n) (Tc : ℕ)
    (g : ZMod 4 × BinaryWalsh.Address 73) (f : ZArr Y n) : ZArr Y n :=
  if hp : ∃ j, g.2 j = 1 then
    pullMH e (basisMap g.2 (Fin.find _ hp))
      (if g.1 = 1 then child (Fin.find _ hp) (pullMH e (basisMap g.2 (Fin.find _ hp)) f)
        else conjZ (child (Fin.find _ hp) (conjZ (pullMH e (basisMap g.2 (Fin.find _ hp)) f))))
  else (2 ^ Tc : GaussianInt) • f

/-- A doubled gate on any wire type, as `NodeZ.gateZ`. -/
def gateZT {ι : Type} [DecidableEq ι] (g : Circuit.Gate ι ℚ) (B : ι → ZArr Y n) : ι → ZArr Y n :=
  fun v p => if v = g.target then
      2 * B g.target p + (g.terms.map fun t => dbl t.2 * B t.1 p).sum
    else 2 * B v p

/-- One scaled instruction of the T16 program: a child updates its wire and multiplies the others
by `2^Tc`; every other primitive runs its tape pass on its wire; a gate is doubled. -/
noncomputable def execT (child : Fin 73 → ZArr Y n → ZArr Y n) (Tc : ℕ) :
    Impl.MInstr NodeUnit → (NodeUnit → ZArr Y n) → (NodeUnit → ZArr Y n)
  | .gate g, B => gateZT g B
  | .prim w p, B => if p.isChild then
      (match p with
        | .factor q v => fun u => if u = w then facMH e child Tc (q, v) (B w)
            else (2 ^ Tc : GaussianInt) • B u
        | _ => B)
    else Function.update B w (tapeZ e p (B w))

/-- Run a scaled T16 program. -/
noncomputable def runT (child : Fin 73 → ZArr Y n → ZArr Y n) (Tc : ℕ) :
    List (Impl.MInstr NodeUnit) → (NodeUnit → ZArr Y n) → (NodeUnit → ZArr Y n)
  | [], B => B
  | i :: rest, B => runT child Tc rest (execT e child Tc i B)

/-- The exponent of a scaled program: one per gate, `Tc` per child. -/
def progExpT (Tc : ℕ) : List (Impl.MInstr NodeUnit) → ℕ
  | [] => 0
  | .gate _ :: rest => 1 + progExpT Tc rest
  | .prim _ p :: rest => (if p.isChild then Tc else 0) + progExpT Tc rest

variable {e}

lemma view_smulZH (c : GaussianInt) (u : ZArr Y n) :
    view e (toC (c • u)) = GaussianInt.toComplex c • view e (toC u) := by
  funext p; simp [view, toC, map_mul]

lemma view_conjZH (u : ZArr Y n) : view e (toC (conjZ u)) = conjArrH (view e (toC u)) := by
  funext p; simp [view, toC, conjZ, conjArrH, GaussianInt.toComplex_star]

lemma view_pullMH' (he : Function.Injective e) (L : BinaryWalsh.Address 73 → BinaryWalsh.Address 73)
    (u : ZArr Y n) : view e (toC (pullMH e L u)) = pullArrH L (view e (toC u)) :=
  view_pullMH he L u

lemma view_childH (he : Function.Injective e) (child : Fin 73 → ZArr Y n → ZArr Y n) (Tc : ℕ)
    (hchild : ∀ (j : Fin 73) (f : ZArr Y n), toC (child j f) =
      (2 : ℂ) ^ Tc • ((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC f))
    (j : Fin 73) (u : ZArr Y n) :
    view e (toC (child j u)) = (2 : ℂ) ^ Tc • slotProdH j (view e (toC u)) := by
  have h1 : slotProdH j (view e (toC u)) =
      view e (((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC u)) := by
    have := prod_view e he 1 ((List.finRange k).map (bitIdx j)) (toC u)
    simp only [List.map_map, Function.comp_def] at this
    exact this
  rw [h1, hchild]
  rfl

/-- The view of a scaled factor is `2^Tc` times `facImplH` on the view. -/
lemma view_facMH (he : Function.Injective e) (child : Fin 73 → ZArr Y n → ZArr Y n) (Tc : ℕ)
    (hchild : ∀ (j : Fin 73) (f : ZArr Y n), toC (child j f) =
      (2 : ℂ) ^ Tc • ((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC f))
    (g : ZMod 4 × BinaryWalsh.Address 73) (u : ZArr Y n) :
    view e (toC (facMH e child Tc g u)) = (2 : ℂ) ^ Tc • facImplH g (view e (toC u)) := by
  unfold facMH facImplH
  split_ifs with hp hq
  · rw [view_pullMH' he, view_childH he child Tc hchild, view_pullMH' he, pullArrH_smul]
  · rw [view_pullMH' he, view_conjZH, view_childH he child Tc hchild, view_conjZH,
      view_pullMH' he, conjArrH_two_pow_smul, pullArrH_smul]
  · rw [view_smulZH, map_pow, toComplex_two]

lemma gate_sum_viewT {ι : Type} (B : ι → ZArr Y n) (terms : List (ι × ℚ))
    (hterms : ∀ t ∈ terms, (2 * t.2).den = 1) (y : Y) (r : Fin n → ZMod 2)
    (a : Fin (73 * k) → ZMod 2) :
    GaussianInt.toComplex ((terms.map fun t => dbl t.2 * B t.1 (y, merge e r a)).sum) =
      2 * (terms.map fun t => t.2 • view e (toC (B t.1))).sum ((y, r), a) := by
  induction terms with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons, map_add, map_mul, Pi.add_apply, Pi.smul_apply]
      rw [ih (fun t ht => hterms t (List.mem_cons_of_mem _ ht)),
        toComplex_dbl _ (hterms t List.mem_cons_self)]
      simp only [view, toC, Rat.smul_def]
      ring

/-- The view of a doubled gate is twice the rational gate on the views. -/
lemma view_gateZT {ι : Type} [DecidableEq ι] (g : Circuit.Gate ι ℚ)
    (hg : ∀ t ∈ g.terms, (2 * t.2).den = 1) (B : ι → ZArr Y n) (v : ι) :
    view e (toC (gateZT g B v)) =
      (2 : ℂ) • FramedCircuit.moduleGate g (fun w => view e (toC (B w))) v := by
  funext ⟨⟨y, r⟩, a⟩
  simp only [FramedCircuit.moduleGate, Pi.smul_apply, smul_eq_mul]
  by_cases hv : v = g.target
  · subst hv
    have hs := gate_sum_viewT (e := e) B g.terms hg y r a
    simp only [Function.update_self, Pi.add_apply]
    change GaussianInt.toComplex (gateZT g B g.target (y, merge e r a)) = _
    simp only [gateZT, ↓reduceIte, map_add, map_mul, hs, toComplex_two]
    simp only [view, toC]
    ring
  · simp only [Function.update_of_ne hv]
    change GaussianInt.toComplex (gateZT g B v (y, merge e r a)) = _
    simp only [gateZT, hv, ↓reduceIte, map_mul, view, toC, toComplex_two]

end Z

/-! ### Transport through the program -/

section Transport

variable {Y : Type} {k n : ℕ} {e : Fin (73 * k) → Fin n}

lemma moduleGate_smulT {ι Z : Type} [DecidableEq ι] (g : Circuit.Gate ι ℚ) (c : ℂ)
    (X : ι → Arr Z (73 * k)) :
    FramedCircuit.moduleGate g (c • X) = c • FramedCircuit.moduleGate g X := by
  funext w
  simp only [FramedCircuit.moduleGate]
  by_cases hw : w = g.target
  · subst hw
    simp only [Function.update_self, Pi.smul_apply, smul_add]
    congr 1
    induction g.terms with
    | nil => simp
    | cons t ts ih => simp only [List.map_cons, List.sum_cons, smul_add, ih, smul_comm c t.2]
  · simp [Function.update_of_ne hw]

/-- The complex run is homogeneous. -/
lemma runM_smul {Z : Type} (l : List (Impl.MInstr NodeUnit)) (c : ℂ)
    (X : NodeUnit → Arr Z (73 * k)) :
    Impl.runM (liftRep Z k) l (c • X) = c • Impl.runM (liftRep Z k) l X := by
  induction l generalizing X with
  | nil => rfl
  | cons i rest ih =>
      simp only [Impl.runM]
      rw [← ih]
      congr 1
      cases i with
      | gate g => exact moduleGate_smulT g c X
      | prim w p =>
          funext u
          simp only [Impl.MInstr.run, Pi.smul_apply]
          by_cases hu : u = w
          · subst hu
            simp only [Function.update_self, Pi.smul_apply, map_smul]
          · simp only [Function.update_of_ne hu, Pi.smul_apply]

lemma isChild_factor (q : ZMod 4) (v : BinaryWalsh.Address 73) :
    (Impl.MPrim.factor q v).isChild = true ↔ q = 1 ∨ q = -1 := by
  have key : ∀ q : ZMod 4, (q.val % 2 == 1) = true ↔ q = 1 ∨ q = -1 := by decide
  exact key q

/-- **Transport.** The views of a scaled run are `2^(progExpT Tc l)` times the run through
`liftRep` on the views. -/
theorem view_runT (he : Function.Injective e) (child : Fin 73 → ZArr Y n → ZArr Y n) (Tc : ℕ)
    (hchild : ∀ (j : Fin 73) (f : ZArr Y n), toC (child j f) =
      (2 : ℂ) ^ Tc • ((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC f))
    (l : List (Impl.MInstr NodeUnit)) (hl : ∀ g, Impl.MInstr.gate g ∈ l → Impl.HalfGate g)
    (B : NodeUnit → ZArr Y n) :
    (fun u => view e (toC (runT e child Tc l B u))) =
      (2 : ℂ) ^ progExpT Tc l •
        Impl.runM (liftRep (Y × (Fin n → ZMod 2)) k) l (fun u => view e (toC (B u))) := by
  induction l generalizing B with
  | nil => funext u; simp [runT, progExpT, Impl.runM]
  | cons i rest ih =>
      have hrest : ∀ g, Impl.MInstr.gate g ∈ rest → Impl.HalfGate g :=
        fun g hg => hl g (List.mem_cons_of_mem _ hg)
      simp only [runT, Impl.runM]
      rw [ih hrest]
      cases i with
      | gate g =>
          have hx : (fun u => view e (toC (execT e child Tc (.gate g) B u))) =
              (2 : ℂ) ^ 1 • Impl.MInstr.run (liftRep (Y × (Fin n → ZMod 2)) k) (.gate g)
                (fun u => view e (toC (B u))) := by
            funext u
            rw [pow_one]
            exact view_gateZT g (hl g List.mem_cons_self) B u
          rw [hx, runM_smul, smul_smul, ← pow_add, Nat.add_comm]
          rfl
      | prim w p =>
          by_cases hp : p.isChild = true
          · cases p with
            | factor q v =>
                have hq := (isChild_factor q v).1 hp
                have hx : (fun u => view e (toC (execT e child Tc (.prim w (.factor q v)) B u))) =
                    (2 : ℂ) ^ Tc • Impl.MInstr.run (liftRep (Y × (Fin n → ZMod 2)) k)
                      (.prim w (.factor q v)) (fun u => view e (toC (B u))) := by
                  funext u
                  simp only [execT, hp, ↓reduceIte, Impl.MInstr.run, Pi.smul_apply]
                  by_cases hu : u = w
                  · subst hu
                    simp only [↓reduceIte, Function.update_self]
                    rw [view_facMH he child Tc hchild, facImplH_eq _ hq, Impl.MPrim.lin,
                      liftRep_apply, colRep_kernel]
                  · simp only [hu, ↓reduceIte, Function.update_of_ne hu, view_smulZH, map_pow,
                      toComplex_two]
                rw [hx, runM_smul, smul_smul, ← pow_add, progExpT, if_pos hp, Nat.add_comm]
            | trans v => simp [Impl.MPrim.isChild] at hp
            | xor i j => simp [Impl.MPrim.isChild] at hp
            | phase i c => simp [Impl.MPrim.isChild] at hp
            | unit c => simp [Impl.MPrim.isChild] at hp
          · have hp' : p.isChild = false := by simpa using hp
            have hx : (fun u => view e (toC (execT e child Tc (.prim w p) B u))) =
                Impl.MInstr.run (liftRep (Y × (Fin n → ZMod 2)) k) (.prim w p)
                  (fun u => view e (toC (B u))) := by
              funext u
              simp only [execT, hp', Bool.false_eq_true, ↓reduceIte, Impl.MInstr.run]
              by_cases hu : u = w
              · subst hu
                simp only [Function.update_self]
                exact view_tapeZ he p hp' (B u)
              · simp only [Function.update_of_ne hu]
            rw [hx, progExpT, if_neg hp, Nat.zero_add]

end Transport

/-! ### The node -/

section NodeT

variable {Y : Type} {k n : ℕ} (e : Fin (73 * k) → Fin n)

/-- The bank of a T16 node: the data families of its input, zero arrays on the centres. -/
def bankT (f : ZArr (Y × Fin 14336) n) : NodeUnit → ZArr Y n
  | .inl j => fun p => f ((p.1, j), p.2)
  | .inr _ => 0

/-- The scaled T16 node. -/
noncomputable def nodeT (child : Fin 73 → ZArr Y n → ZArr Y n) (Tc : ℕ)
    (f : ZArr (Y × Fin 14336) n) : ZArr (Y × Fin 14336) n :=
  fun p => runT e child Tc Impl.fittedProgram (bankT f) (.inl p.1.2) (p.1.1, p.2)

/-- **The scaled T16 node** computes `2^(progExpT Tc fittedProgram)` times `C` on every active
bit, if the child computes `2^Tc` times `C` on the bits of a slot. -/
theorem nodeT_correct (he : Function.Injective e) (child : Fin 73 → ZArr Y n → ZArr Y n) (Tc : ℕ)
    (hchild : ∀ (j : Fin 73) (f : ZArr Y n), toC (child j f) =
      (2 : ℂ) ^ Tc • ((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC f))
    (f : ZArr (Y × Fin 14336) n) :
    toC (nodeT e child Tc f) =
      (2 : ℂ) ^ progExpT Tc Impl.fittedProgram •
        ((List.finRange (73 * k)).map fun i => kBit 1 (e i)).prod (toC f) := by
  have hrun := view_runT he child Tc hchild Impl.fittedProgram Impl.fittedProgram_half (bankT f)
  funext ⟨⟨y, j⟩, r⟩
  have h1 : toC (nodeT e child Tc f) ((y, j), r) =
      view e (toC (runT e child Tc Impl.fittedProgram (bankT f) (.inl j)))
        ((y, r), fun i => r (e i)) := by
    simp only [view, merge_extract]
    rfl
  have h2 := congrFun (congrFun hrun (.inl j)) ((y, r), fun i => r (e i))
  rw [h1, h2, Pi.smul_apply, Pi.smul_apply, fittedArr_cfull, Pi.smul_apply]
  congr 1
  have h3 : view e (toC (bankT f (.inl j))) =
      view e (toC (fun p : Y × (Fin n → ZMod 2) => f ((p.1, j), p.2))) := rfl
  rw [h3, view_Cfull e he _ y r]
  have h4 := congrFun (prod_respec (fun y' : Y => (y', j)) 1 ((List.finRange (73 * k)).map e)
    (toC f)) (y, r)
  simp only [List.map_map, Function.comp_def] at h4
  exact h4.symm

end NodeT

end IntegerMultBounds.MathlibTM2.M6.T16NodeZ
