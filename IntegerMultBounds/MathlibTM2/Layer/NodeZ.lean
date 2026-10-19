module

public import IntegerMultBounds.MathlibTM2.Layer.NodeArr
public import IntegerMultBounds.Machine.CompactFramedScalarGrid
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# The node on Gaussian-integer arrays

The machine stores Gaussian integers modulo `2^W`. To keep every operation a ring operation it
runs a scaled node: every gate is doubled (its coefficients are halves of integers) and the wires
it does not write are doubled with it; a factor's child returns `2^Tc` times its result and the
other wires are multiplied by `2^Tc`. The node acts on the full address of `n` bits; its active
bits are `e : Fin (m * k) → Fin n`, column `c` of slot `j` at `e (bitIdx j c)`.

`nodeM_correct`: if the child computes `2^Tc` times `C` on the bits of a slot, the scaled node
computes `2^(nodeExp ds Tc)` times `C` on every active bit. The proof views each wire array on the
active bits (`view e (toC u)`), where every scaled operation is a power of two times the matching
operation of the complex node `nodeA` (`view_runM`), and concludes with `nodeA_correct`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks BinaryWalsh BinaryPhase BinaryColumns ComplexEndpoints
  ComplexFramedExecution


/-- Gaussian-integer arrays. -/
abbrev ZArr (Y : Type) (n : ℕ) := Y × (Fin n → ZMod 2) → GaussianInt

variable {Y : Type} {n k : ℕ}

/-- The complex array of a Gaussian-integer array. -/
def toC (f : ZArr Y n) : Arr Y n := fun p => GaussianInt.toComplex (f p)

/-- The doubled forward kernel on bit `t`: `(1 + i) f + (1 - i) f ∘ flip t`. -/
def k2 (t : Fin n) (f : ZArr Y n) : ZArr Y n :=
  fun p => ⟨1, 1⟩ * f p + ⟨1, -1⟩ * f (p.1, flip t p.2)

/-! ### Operations on the full address -/

variable (e : Fin (m * k) → Fin n)

/-- Column `c` of the active bits: the bit of slot `j` is at `e (bitIdx j c)`. -/
def colBits (c : Fin k) (b : Fin n → ZMod 2) : BinaryWalsh.Address m := fun j => b (e (bitIdx j c))

/-- Pull back along a change of basis applied in every column of the active bits. -/
noncomputable def pullM (L : BinaryWalsh.Address m → BinaryWalsh.Address m) (f : ZArr Y n) :
    ZArr Y n :=
  fun p => f (p.1, merge e p.2 (ofCols fun c => L (colBits e c p.2)))

/-- Complex conjugation. -/
def conjZ (f : ZArr Y n) : ZArr Y n := fun p => star (f p)

/-- The sign `±1` of a bit. -/
def signZ (a : ZMod 2) : GaussianInt := if a = 0 then 1 else -1

/-- Multiplication by the product over columns of the characters `chi u (column)`. -/
noncomputable def signM (u : BinaryWalsh.Address m) (f : ZArr Y n) : ZArr Y n :=
  fun p => (∏ c : Fin k, signZ (Labels.binary m u (colBits e c p.2))) * f p

/-- A factor `(q, v)` with child `child j` on slot `j` (scaled by `2^Tc`): change of basis to the
pivot `j`, the child (conjugated unless `q = 1`), and the change of basis again. Without a pivot
the factor is the identity, scaled by `2^Tc`. -/
noncomputable def facM (child : Fin m → ZArr Y n → ZArr Y n) (Tc : ℕ)
    (g : ZMod 4 × BinaryWalsh.Address m) (f : ZArr Y n) : ZArr Y n :=
  if h : ∃ j, g.2 j = 1 then
    pullM e (basisMap g.2 (Fin.find _ h))
      (if g.1 = 1 then child (Fin.find _ h) (pullM e (basisMap g.2 (Fin.find _ h)) f)
        else conjZ (child (Fin.find _ h) (conjZ (pullM e (basisMap g.2 (Fin.find _ h)) f))))
  else (2 ^ Tc : GaussianInt) • f

/-- The doubled integer coefficient of a rational gate coefficient. -/
def dbl (c : ℚ) : GaussianInt := ((2 * c).num : GaussianInt)

/-- A doubled gate: the target becomes `2 x_t + Σ (2 c) x_s`, every other wire is doubled. -/
def gateZ (g : Circuit.Gate NWire ℚ) (B : NWire → ZArr Y n) : NWire → ZArr Y n :=
  fun v p => if v = g.target then
      2 * B g.target p + (g.terms.map fun t => dbl t.2 * B t.1 p).sum
    else 2 * B v p

/-- The slot phase `i^{c x_i}` in every column of the active bits. -/
def phaseM (i : Fin m) (c : ZMod 4) (f : ZArr Y n) : ZArr Y n :=
  fun p => (∏ col : Fin k, (⟨0, 1⟩ : GaussianInt) ^ (c * BinaryPhase.bitLift (colBits e col p.2 i)).val) * f p

/-- One scaled instruction. A factor updates its wire and multiplies the others by `2^Tc`; the
translations, slot XORs and slot phases are exact. -/
noncomputable def execM (child : Fin m → ZArr Y n → ZArr Y n) (Tc : ℕ) :
    Instr → (NWire → ZArr Y n) → (NWire → ZArr Y n)
  | .factor w g, B => fun v => if v = w then facM e child Tc g (B w) else (2 ^ Tc : GaussianInt) • B v
  | .gate g, B => gateZ g B
  | .trans w v, B => Function.update B w (pullM e (· + v) (B w))
  | .xor w i j, B => Function.update B w (pullM e (Networks.Certificates.T16.Impl.xorMap i j) (B w))
  | .phase w i c, B => Function.update B w (phaseM e i c (B w))

/-- Run a scaled program. -/
noncomputable def runM (child : Fin m → ZArr Y n → ZArr Y n) (Tc : ℕ) :
    List Instr → (NWire → ZArr Y n) → (NWire → ZArr Y n)
  | [], B => B
  | i :: rest, B => runM child Tc rest (execM e child Tc i B)

/-- The exponent of a scaled program: one per gate, `Tc` per factor. -/
def progExp (Tc : ℕ) : List Instr → ℕ
  | [] => 0
  | .gate _ :: rest => 1 + progExp Tc rest
  | .factor _ _ :: rest => Tc + progExp Tc rest
  | .trans _ _ :: rest => progExp Tc rest
  | .xor _ _ _ :: rest => progExp Tc rest
  | .phase _ _ _ :: rest => progExp Tc rest

/-- The exponent of the scaled node. -/
noncomputable def nodeExp (ds : Directions) (Tc : ℕ) : ℕ := progExp Tc (program ds)

/-- The bank of wire arrays: the data families, and zero on the private centres. -/
def bankZ (f : ZArr (Y × DWire) n) : NWire → ZArr Y n
  | .inl j => fun p => f ((p.1, j), p.2)
  | .inr _ => 0

/-- Reassemble an array from its data families. -/
def unbankZ (B : NWire → ZArr Y n) : ZArr (Y × DWire) n := fun p => B (.inl p.1.2) (p.1.1, p.2)

/-- The scaled node. -/
noncomputable def nodeM (child : Fin m → ZArr Y n → ZArr Y n) (Tc : ℕ) (ds : Directions)
    (f : ZArr (Y × DWire) n) : ZArr (Y × DWire) n :=
  unbankZ (runM e child Tc (program ds) (bankZ f))

/-! ### Correctness -/

/-- The doubled kernel. -/
theorem toC_k2 (t : Fin n) (f : ZArr Y n) : toC (k2 t f) = (2 : ℂ) • kBit 1 t (toC f) := by
  funext p
  simp only [toC, k2, map_add, map_mul, GaussianInt.toComplex_def', kBit_apply, phase_one,
    Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-! #### Views of the wires -/

lemma merge_apply_of_inj {k' : ℕ} {e : Fin k' → Fin n} (he : Function.Injective e)
    (r : Fin n → ZMod 2) (a : Fin k' → ZMod 2) (i : Fin k') : merge e r a (e i) = a i := by
  have h : ∃ i', e i' = e i := ⟨i, rfl⟩
  unfold merge
  split_ifs
  exact congrArg a (he h.choose_spec)

/-- Merging twice keeps only the second overwrite of the bits `e`. -/
lemma merge_merge {k' : ℕ} (e : Fin k' → Fin n) (r : Fin n → ZMod 2) (a b : Fin k' → ZMod 2) :
    merge e (merge e r a) b = merge e r b := by
  funext t
  unfold merge
  split_ifs <;> rfl

variable {e}

lemma colBits_merge (he : Function.Injective e) (r : Fin n → ZMod 2) (a : Fin (m * k) → ZMod 2)
    (c : Fin k) : colBits e c (merge e r a) = toCols a c := by
  funext j
  simp only [colBits, toCols, merge_apply_of_inj he]

lemma view_smulZ (c : GaussianInt) (u : ZArr Y n) :
    view e (toC (c • u)) = GaussianInt.toComplex c • view e (toC u) := by
  funext p; simp [view, toC, map_mul]

lemma view_pullM (he : Function.Injective e) (L : BinaryWalsh.Address m → BinaryWalsh.Address m)
    (u : ZArr Y n) : view e (toC (pullM e L u)) = pullArr L (view e (toC u)) := by
  funext ⟨⟨y, r⟩, a⟩
  simp only [view, toC, pullM, pullArr, colBits_merge he, merge_merge]

lemma view_conjZ (u : ZArr Y n) : view e (toC (conjZ u)) = conjArr (view e (toC u)) := by
  funext p; simp [view, toC, conjZ, conjArr, GaussianInt.toComplex_star]

lemma view_child (he : Function.Injective e) (child : Fin m → ZArr Y n → ZArr Y n) (Tc : ℕ)
    (hchild : ∀ (j : Fin m) (f : ZArr Y n), toC (child j f) =
      (2 : ℂ) ^ Tc • ((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC f))
    (j : Fin m) (u : ZArr Y n) :
    view e (toC (child j u)) = (2 : ℂ) ^ Tc • slotProd j (view e (toC u)) := by
  have h1 : slotProd j (view e (toC u)) =
      view e (((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC u)) := by
    have := prod_view e he 1 ((List.finRange k).map (bitIdx j)) (toC u)
    simp only [List.map_map, Function.comp_def] at this
    exact this
  rw [h1, hchild]
  rfl

lemma toComplex_two : GaussianInt.toComplex 2 = 2 := map_ofNat _ 2

lemma toComplex_dbl (c : ℚ) (hc : (2 * c).den = 1) : GaussianInt.toComplex (dbl c) = 2 * (c : ℂ) := by
  have h : ((2 * c).num : ℚ) = 2 * c := Rat.coe_int_num_of_den_eq_one hc
  have h' : (((2 * c).num : ℚ) : ℂ) = ((2 * c : ℚ) : ℂ) := by rw [h]
  simp only [dbl, map_intCast]
  push_cast at h'
  exact h'

lemma gate_sum_view (B : NWire → ZArr Y n) (terms : List (NWire × ℚ))
    (h : ∀ t ∈ terms, (2 * t.2).den = 1) (y : Y) (r : Fin n → ZMod 2) (a : Fin (m * k) → ZMod 2) :
    GaussianInt.toComplex ((terms.map fun t => dbl t.2 * B t.1 (y, merge e r a)).sum) =
      2 * (terms.map fun t => t.2 • view e (toC (B t.1))).sum ((y, r), a) := by
  induction terms with
  | nil => simp
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons, map_add, map_mul, Pi.add_apply, Pi.smul_apply]
      rw [ih (fun t ht => h t (List.mem_cons_of_mem _ ht)), toComplex_dbl _ (h t List.mem_cons_self)]
      simp only [view, toC, Rat.smul_def]
      ring

/-- The view of a doubled gate is twice the rational gate on the views. -/
lemma view_gateZ (g : Circuit.Gate NWire ℚ) (hg : ∀ t ∈ g.terms, (2 * t.2).den = 1)
    (B : NWire → ZArr Y n) (v : NWire) :
    view e (toC (gateZ g B v)) =
      (2 : ℂ) • FramedCircuit.moduleGate g (fun w => view e (toC (B w))) v := by
  funext ⟨⟨y, r⟩, a⟩
  simp only [FramedCircuit.moduleGate, Pi.smul_apply, smul_eq_mul]
  by_cases hv : v = g.target
  · subst hv
    have hs := gate_sum_view (e := e) B g.terms hg y r a
    simp only [Function.update_self, Pi.add_apply]
    change GaussianInt.toComplex (gateZ g B g.target (y, merge e r a)) = _
    simp only [gateZ, ↓reduceIte, map_add, map_mul, hs, toComplex_two]
    simp only [view, toC]
    ring
  · simp only [Function.update_of_ne hv]
    change GaussianInt.toComplex (gateZ g B v (y, merge e r a)) = _
    simp only [gateZ, hv, ↓reduceIte, map_mul, view, toC, toComplex_two]

/-! #### Homogeneity of the complex node -/

lemma pullArr_smul (L : BinaryWalsh.Address m → BinaryWalsh.Address m) (c : ℂ)
    (u : Arr Y (m * k)) : pullArr L (c • u) = c • pullArr L u := rfl

lemma conjArr_two_pow_smul (s : ℕ) (u : Arr Y (m * k)) :
    conjArr ((2 : ℂ) ^ s • u) = (2 : ℂ) ^ s • conjArr u := by
  funext p; simp [conjArr]

lemma facImpl_two_pow_smul (g : ZMod 4 × BinaryWalsh.Address m) (s : ℕ) (u : Arr Y (m * k)) :
    facImpl g ((2 : ℂ) ^ s • u) = (2 : ℂ) ^ s • facImpl g u := by
  unfold facImpl
  split_ifs <;> simp only [pullArr_smul, map_smul, conjArr_two_pow_smul]

lemma moduleGate_smul (g : Circuit.Gate NWire ℚ) (c : ℂ) (X : NWire → Arr Y (m * k)) :
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

lemma phaseArr_smul (i : Fin m) (c : ZMod 4) (a : ℂ) (u : Arr Y (m * k)) :
    phaseArr i c (a • u) = a • phaseArr i c u := by
  funext p; simp only [phaseArr, Pi.smul_apply, smul_eq_mul]; ring

lemma update_two_pow_smul (X : NWire → Arr Y (m * k)) (w : NWire) (T : Arr Y (m * k) → Arr Y (m * k))
    (hT : ∀ (a : ℂ) u, T (a • u) = a • T u) (s : ℕ) :
    Function.update ((2 : ℂ) ^ s • X) w (T (((2 : ℂ) ^ s • X) w)) =
      (2 : ℂ) ^ s • Function.update X w (T (X w)) := by
  funext v
  by_cases hv : v = w
  · subst hv; simp [Function.update_self, hT]
  · simp [Function.update_of_ne hv]

lemma execWith_two_pow_smul (i : Instr) (s : ℕ) (X : NWire → Arr Y (m * k)) :
    execWith facImpl i ((2 : ℂ) ^ s • X) = (2 : ℂ) ^ s • execWith facImpl i X := by
  cases i with
  | factor w g =>
      funext v
      simp only [execWith, Pi.smul_apply]
      by_cases hv : v = w
      · subst hv; simp [Function.update_self, facImpl_two_pow_smul]
      · simp [Function.update_of_ne hv]
  | gate g => exact moduleGate_smul g _ X
  | trans w v => exact update_two_pow_smul X w _ (fun a u => pullArr_smul _ a u) s
  | xor w i j => exact update_two_pow_smul X w _ (fun a u => pullArr_smul _ a u) s
  | phase w i c => exact update_two_pow_smul X w _ (fun a u => phaseArr_smul i c a u) s

lemma runWith_two_pow_smul (l : List Instr) (s : ℕ) (X : NWire → Arr Y (m * k)) :
    runWith facImpl l ((2 : ℂ) ^ s • X) = (2 : ℂ) ^ s • runWith facImpl l X := by
  induction l generalizing X with
  | nil => rfl
  | cons i rest ih => simp only [runWith, execWith_two_pow_smul, ih]

/-! #### Transport through the program -/

/-- The view of a scaled factor is `2^Tc` times `facImpl` on the view. -/
lemma view_facM (he : Function.Injective e) (child : Fin m → ZArr Y n → ZArr Y n) (Tc : ℕ)
    (hchild : ∀ (j : Fin m) (f : ZArr Y n), toC (child j f) =
      (2 : ℂ) ^ Tc • ((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC f))
    (g : ZMod 4 × BinaryWalsh.Address m) (u : ZArr Y n) :
    view e (toC (facM e child Tc g u)) = (2 : ℂ) ^ Tc • facImpl g (view e (toC u)) := by
  unfold facM facImpl
  split_ifs with h hq
  · rw [view_pullM he, view_child he child Tc hchild, view_pullM he, pullArr_smul]
  · rw [view_pullM he, view_conjZ, view_child he child Tc hchild, view_conjZ, view_pullM he,
      conjArr_two_pow_smul, pullArr_smul]
  · rw [view_smulZ, map_pow, toComplex_two]

lemma view_phaseM (he : Function.Injective e) (i : Fin m) (c : ZMod 4) (u : ZArr Y n) :
    view e (toC (phaseM e i c u)) = phaseArr i c (view e (toC u)) := by
  funext ⟨⟨y, r⟩, a⟩
  simp only [view, toC, phaseM, phaseArr, map_mul, map_prod, map_pow, colBits_merge he]
  congr 1
  refine Finset.prod_congr rfl fun col _ => ?_
  simp [BinaryPhase.phase, GaussianInt.toComplex_def']

lemma view_update (B : NWire → ZArr Y n) (w : NWire) (u : ZArr Y n) :
    (fun v => view e (toC (Function.update B w u v))) =
      Function.update (fun v => view e (toC (B v))) w (view e (toC u)) := by
  funext v
  by_cases hv : v = w
  · subst hv; simp
  · simp [Function.update_of_ne hv]

/-- The views of a scaled run are `2^(progExp Tc l)` times the complex run on the views. -/
lemma view_runM (he : Function.Injective e) (child : Fin m → ZArr Y n → ZArr Y n) (Tc : ℕ)
    (hchild : ∀ (j : Fin m) (f : ZArr Y n), toC (child j f) =
      (2 : ℂ) ^ Tc • ((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC f))
    (l : List Instr) (hl : ∀ g, Instr.gate g ∈ l → ∀ t ∈ g.terms, (2 * t.2).den = 1)
    (B : NWire → ZArr Y n) :
    (fun w => view e (toC (runM e child Tc l B w))) =
      (2 : ℂ) ^ progExp Tc l • runWith facImpl l (fun w => view e (toC (B w))) := by
  induction l generalizing B with
  | nil => funext w; simp [runM, progExp, runWith]
  | cons i rest ih =>
      have hrest : ∀ g, Instr.gate g ∈ rest → ∀ t ∈ g.terms, (2 * t.2).den = 1 :=
        fun g hg => hl g (List.mem_cons_of_mem _ hg)
      simp only [runM, runWith]
      rw [ih hrest]
      cases i with
      | factor w g =>
          have hx : (fun v => view e (toC (execM e child Tc (.factor w g) B v))) =
              (2 : ℂ) ^ Tc • execWith facImpl (.factor w g) (fun v => view e (toC (B v))) := by
            funext v
            simp only [execM, execWith, Pi.smul_apply]
            by_cases hv : v = w
            · subst hv
              simp only [↓reduceIte, Function.update_self]
              exact view_facM he child Tc hchild g (B v)
            · simp only [hv, ↓reduceIte, Function.update_of_ne hv, view_smulZ, map_pow, toComplex_two]
          rw [hx, runWith_two_pow_smul, smul_smul, ← pow_add, Nat.add_comm]
          rfl
      | gate g =>
          have hx : (fun v => view e (toC (execM e child Tc (.gate g) B v))) =
              (2 : ℂ) ^ 1 • execWith facImpl (.gate g) (fun v => view e (toC (B v))) := by
            funext v
            rw [pow_one]
            exact view_gateZ g (hl g List.mem_cons_self) B v
          rw [hx, runWith_two_pow_smul, smul_smul, ← pow_add, Nat.add_comm]
          rfl
      | trans w v =>
          change (2 : ℂ) ^ progExp Tc rest • runWith facImpl rest
              (fun u => view e (toC (Function.update B w (pullM e (· + v) (B w)) u))) = _
          rw [view_update, view_pullM he]
          rfl
      | xor w i j =>
          change (2 : ℂ) ^ progExp Tc rest • runWith facImpl rest
              (fun u => view e (toC (Function.update B w
                (pullM e (Networks.Certificates.T16.Impl.xorMap i j) (B w)) u))) = _
          rw [view_update, view_pullM he]
          rfl
      | phase w i c =>
          change (2 : ℂ) ^ progExp Tc rest • runWith facImpl rest
              (fun u => view e (toC (Function.update B w (phaseM e i c (B w)) u))) = _
          rw [view_update, view_phaseM he]
          rfl

variable (e)

/-- The scaled node computes `2^(nodeExp ds Tc)` times `C` on every active bit. -/
theorem nodeM_correct (he : Function.Injective e) (ds : Directions)
    (hd : ComplexPhaseBudget.Realizes ds) (child : Fin m → ZArr Y n → ZArr Y n) (Tc : ℕ)
    (hchild : ∀ (j : Fin m) (f : ZArr Y n), toC (child j f) =
      (2 : ℂ) ^ Tc • ((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC f))
    (f : ZArr (Y × DWire) n) :
    toC (nodeM e child Tc ds f) =
      (2 : ℂ) ^ nodeExp ds Tc • ((List.finRange (m * k)).map fun i => kBit 1 (e i)).prod (toC f) := by
  -- the array on the active bits, with spectators the original spectator and the bit vector
  let F : Arr ((Y × (Fin n → ZMod 2)) × DWire) (m * k) :=
    fun p => toC f ((p.1.1.1, p.1.2), merge e p.1.1.2 p.2)
  have hrun := view_runM he child Tc hchild (program ds) (program_gate_coeff ds) (bankZ f)
  have hbank : (fun w => view e (toC (bankZ f w))) = bankOf k F := by
    funext w
    rcases w with j | c
    · rfl
    · funext p; simp [bankZ, bankOf, view, toC]
  rw [hbank] at hrun
  have hA := nodeA_correct (Y := Y × (Fin n → ZMod 2)) ds hd F
  funext ⟨⟨y, j⟩, r⟩
  have h1 : toC (nodeM e child Tc ds f) ((y, j), r) =
      view e (toC (runM e child Tc (program ds) (bankZ f) (.inl j))) ((y, r), fun i => r (e i)) := by
    simp only [view, merge_extract]
    rfl
  have h2 := congrFun (congrFun hrun (.inl j)) ((y, r), fun i => r (e i))
  rw [h1, h2]
  have h3 : runWith facImpl (program ds) (bankOf k F) (.inl j) ((y, r), fun i => r (e i)) =
      nodeA k ds F (((y, r), j), fun i => r (e i)) := rfl
  rw [Pi.smul_apply, Pi.smul_apply, h3, hA, Pi.smul_apply, ← view_Cfull e he (toC f) (y, j) r]
  congr 1
  exact (Cfull_respec (fun z : (Y × (Fin n → ZMod 2)) × DWire => ((z.1.1, z.2), z.1.2))
    (view e (toC f)) ((y, r), j) (fun i => r (e i))).symm

end IntegerMultBounds.MathlibTM2.Layer
