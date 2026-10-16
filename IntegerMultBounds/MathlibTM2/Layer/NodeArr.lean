module

public import IntegerMultBounds.MathlibTM2.Layer.Columns

/-!
# A network node on arrays with spectators

At a node the spectator carries the wire role, so an array on `Y × NWire` with `m · k` active
bits is a bank of arrays on `Y`. The node applies the source correction, runs the network
program with each factor `(q, v)` implemented by `facImpl` — a change of basis, the forward
child on one slot (conjugated for `q = -1`), and the change of basis again — and applies the
sink correction. `nodeA_correct`: the node applies `C` to every active bit.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks BinaryWalsh BinaryPhase BinaryColumns ComplexEndpoints
  ComplexFramedExecution

set_option linter.unusedSimpArgs false

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

/-! ### The node -/

variable (k)

/-- The array of each wire. -/
def bankOf (f : Arr (Y × NWire) (m * k)) : NWire → Arr Y (m * k) := fun w p => f ((p.1, w), p.2)

/-- Reassemble an array from the arrays of the wires. -/
def unbank (B : NWire → Arr Y (m * k)) : Arr (Y × NWire) (m * k) := fun p => B p.1.2 (p.1.1, p.2)

/-- Source correction: the sign character of each X terminal in every column. -/
noncomputable def correctInputA (B : NWire → Arr Y (m * k)) : NWire → Arr Y (m * k)
  | Sum.inl b => lift (fun g => signColumns k (terminalVector b) g) (B (Sum.inl b))
  | Sum.inr i => B (Sum.inr i)

/-- Sink correction and the undoing of the signed bank exchange. -/
noncomputable def correctOutputA (B : NWire → Arr Y (m * k)) : NWire → Arr Y (m * k)
  | Sum.inl b => Complex.I ^ (27 * k) • lift (fun g => signColumns k (terminalVector b) g) (B (Sum.inr (Sum.inl b)))
  | Sum.inr (Sum.inl b) => -B (Sum.inl b)
  | Sum.inr (Sum.inr s) => B (Sum.inr (Sum.inr s))

/-- One node of the layer recursion. -/
noncomputable def nodeA (ds : Directions) (f : Arr (Y × NWire) (m * k)) : Arr (Y × NWire) (m * k) :=
  unbank k (correctOutputA k (runWith facImpl (program ds) (correctInputA k (bankOf k f))))

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

lemma forall₂_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, b, hb => by simp at hb
  | _, _, .cons hab rest, b, hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨_, List.mem_cons_self .., hab⟩
      · obtain ⟨a, ha, h⟩ := forall₂_right rest b hb
        exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

/-- Every factor of the program comes from the direction lists. -/
lemma factor_mem_lowerSkel (sk : List Skel) (ds : Directions) (w : NWire)
    (g : ZMod 4 × BinaryWalsh.Address m) (h : Instr.factor w g ∈ lowerSkel sk ds) :
    ∃ gs ∈ ds, g ∈ gs := by
  induction sk generalizing ds with
  | nil => simp [lowerSkel] at h
  | cons s rest ih =>
      cases s with
      | edge w' =>
          simp only [lowerSkel, List.mem_append, List.mem_map, List.mem_reverse] at h
          rcases h with ⟨g', hg', he⟩ | h
          · cases he
            cases ds with
            | nil => simp at hg'
            | cons gs ds => exact ⟨gs, List.mem_cons_self .., hg'⟩
          · obtain ⟨gs, hgs, hg⟩ := ih ds.tail h
            exact ⟨gs, List.mem_of_mem_tail hgs, hg⟩
      | gate g' =>
          simp only [lowerSkel, List.mem_cons, reduceCtorEq, false_or] at h
          exact ih ds h

/-- Slicing commutes with running the program when the factors are the lifted vendored ones. -/
lemma slice_runWith (y : Y) (p : List Instr)
    (hp : ∀ w g, Instr.factor w g ∈ p → g.1 = 1 ∨ g.1 = -1) (B : NWire → Arr Y (m * k)) :
    (fun w => slice y (runWith facImpl p B w)) = runWith (vf k) p (fun w => slice y (B w)) := by
  induction p generalizing B with
  | nil => rfl
  | cons i rest ih =>
      have hrest : ∀ w g, Instr.factor w g ∈ rest → g.1 = 1 ∨ g.1 = -1 :=
        fun w g hg => hp w g (List.mem_cons_of_mem _ hg)
      simp only [runWith]
      rw [ih hrest]
      congr 1
      cases i with
      | factor w g =>
          funext w'
          simp only [execWith]
          by_cases hw : w' = w
          · subst hw
            simp only [Function.update_self]
            rw [facImpl_eq g (hp w' g (List.mem_cons_self ..)), slice_lift]
          · simp [Function.update_of_ne hw]
      | gate g => exact slice_moduleGate y g B

/-- A node of the layer recursion applies `C` to every active bit. -/
theorem nodeA_correct (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (f : Arr (Y × NWire) (m * k)) : nodeA k ds f = Cfull (Y × NWire) (m * k) f := by
  have hq : ∀ w g, Instr.factor w g ∈ program ds → g.1 = 1 ∨ g.1 = -1 := by
    intro w g hg
    obtain ⟨gs, hgs, hg⟩ := factor_mem_lowerSkel _ ds w g hg
    obtain ⟨_, -, he⟩ := forall₂_right hd gs hgs
    exact he.1 g hg
  funext ⟨⟨y, w⟩, b⟩
  have hin : (fun v => slice y (correctInputA k (bankOf k f) v)) =
      correctInput k (fun v => slice y (bankOf k f v)) := by
    funext v; rcases v with v | v <;> simp [correctInputA, correctInput, slice_lift]
  have hout : ∀ B : NWire → Arr Y (m * k), (fun v => slice y (correctOutputA k B v)) =
      correctOutput k (fun v => slice y (B v)) := by
    intro B; funext v
    rcases v with v | v | v
    · change slice y (Complex.I ^ (27 * k) • lift _ (B _)) = _
      rw [slice_csmul, slice_lift]; rfl
    · change slice y (-B _) = _
      rw [slice_neg]; rfl
    · rfl
  have key := congrFun (congrArg (fun F => F w) (hout (runWith facImpl (program ds)
    (correctInputA k (bankOf k f))))) (toCols b)
  simp only at key
  rw [slice_runWith y _ hq, hin, node_correct k ds hd] at key
  have hb : b = ofCols (toCols b) := (ofCols_toCols b).symm
  calc nodeA k ds f ((y, w), b)
      = slice y (correctOutputA k (runWith facImpl (program ds) (correctInputA k (bankOf k f))) w)
          (toCols b) := by simp [nodeA, unbank, slice]
    _ = fullFrame k (slice y (bankOf k f w)) (toCols b) := key
    _ = lift (fun g => fullFrame k g) (bankOf k f w) (y, b) := rfl
    _ = Cfull Y (m * k) (bankOf k f w) (y, b) := by rw [lift_fullFrame]
    _ = Cfull (Y × NWire) (m * k) f ((y, w), b) := by
        rw [Cfull_respec (fun y : Y => (y, w)) f y b]; rfl

end IntegerMultBounds.MathlibTM2.Layer
