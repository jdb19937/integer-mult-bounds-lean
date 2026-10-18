module

public import IntegerMultBounds.MathlibTM2.Layer.L2
public import IntegerMultBounds.MathlibTM2.Layer.NodeZ

/-!
# The node with rounded children

The scaled node `nodeM` keeps one common scale: a factor's child returns `2^Tc` times its result
and the other wires are multiplied by `2^Tc`, so the exponent compounds over the levels. With
rounded children the factor instead divides its child's result by the child's scale (truncating)
and leaves the other wires alone: this is `nodeM` with `Tc = 0` and children that are already
rounded. Its exponent is the number of gates at every level.

This file bounds the error of such a node in the `ℓ²` norm. The factors of the complex node are
isometries (`l2_facImpl_sub`), a gate is Lipschitz with constant `1 + Σ |c|` on the bank norm
`bl2` (`bl2_moduleGate_sub_le`), so a child error `δ` in every factor adds at most `δ` in the
view, and every gate multiplies the accumulated error by at most twice its constant
(`view_runM_err`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks BinaryWalsh BinaryPhase BinaryColumns ComplexEndpoints
  ComplexFramedExecution

/-! ### Isometries of the complex node -/

section Iso

variable {Y : Type} [Fintype Y] {k : ℕ}

lemma l2_congr_norm' {X : Type} [Fintype X] (f g : X → ℂ) (h : ∀ x, ‖f x‖ = ‖g x‖) :
    l2 f = l2 g := by
  unfold l2; simp only [h]

/-- Pulling back along an involutive change of basis of the columns preserves the norm. -/
lemma l2_pullArr (L : BinaryWalsh.Address m → BinaryWalsh.Address m) (hL : ∀ a, L (L a) = a)
    (u : Arr Y (m * k)) : l2 (pullArr L u) = l2 u := by
  let σ : Y × (Fin (m * k) → ZMod 2) ≃ Y × (Fin (m * k) → ZMod 2) :=
    ⟨fun p => (p.1, ofCols fun c => L (toCols p.2 c)),
      fun p => (p.1, ofCols fun c => L (toCols p.2 c)),
      fun p => by simp [hL], fun p => by simp [hL]⟩
  exact l2_comp_equiv σ u

lemma l2_conjArr (u : Arr Y (m * k)) : l2 (conjArr u) = l2 u := l2_star u

lemma l2_slotProd (j : Fin m) (u : Arr Y (m * k)) : l2 (slotProd j u) = l2 u := by
  unfold slotProd
  have := l2_prod_kBit (Y := Y) ((List.finRange k).map (bitIdx j)) u
  simpa [List.map_map, Function.comp_def] using this

omit [Fintype Y] in
lemma pullArr_sub (L : BinaryWalsh.Address m → BinaryWalsh.Address m) (u v : Arr Y (m * k)) :
    pullArr L (u - v) = pullArr L u - pullArr L v := rfl

omit [Fintype Y] in
lemma conjArr_sub (u v : Arr Y (m * k)) : conjArr (u - v) = conjArr u - conjArr v := by
  funext p; simp [conjArr]

omit [Fintype Y] in
lemma facImpl_sub (g : ZMod 4 × BinaryWalsh.Address m) (u v : Arr Y (m * k)) :
    facImpl g (u - v) = facImpl g u - facImpl g v := by
  unfold facImpl
  split_ifs <;> simp only [pullArr_sub, map_sub, conjArr_sub]

/-- The factors of the complex node are isometries. -/
lemma l2_facImpl (g : ZMod 4 × BinaryWalsh.Address m) (u : Arr Y (m * k)) :
    l2 (facImpl g u) = l2 u := by
  unfold facImpl
  split_ifs with h hq
  · have hv := Fin.find_spec h
    rw [l2_pullArr _ (basisMap_invol _ _ hv), l2_slotProd, l2_pullArr _ (basisMap_invol _ _ hv)]
  · have hv := Fin.find_spec h
    rw [l2_pullArr _ (basisMap_invol _ _ hv), l2_conjArr, l2_slotProd, l2_conjArr,
      l2_pullArr _ (basisMap_invol _ _ hv)]
  · rfl

lemma l2_facImpl_sub (g : ZMod 4 × BinaryWalsh.Address m) (u v : Arr Y (m * k)) :
    l2 (facImpl g u - facImpl g v) = l2 (u - v) := by
  rw [← facImpl_sub, l2_facImpl]

end Iso

/-! ### The bank norm -/

section Bank

variable {W Z : Type} [Fintype W] [Fintype Z]

/-- The `ℓ²` norm of a bank of wire arrays. -/
noncomputable def bl2 (B : W → Z → ℂ) : ℝ := l2 (fun q : W × Z => B q.1 q.2)

lemma bl2_nonneg (B : W → Z → ℂ) : 0 ≤ bl2 B := l2_nonneg _

lemma bl2_add_le (B C : W → Z → ℂ) : bl2 (B + C) ≤ bl2 B + bl2 C :=
  l2_add_le (fun q : W × Z => B q.1 q.2) (fun q => C q.1 q.2)

lemma bl2_smul (c : ℂ) (B : W → Z → ℂ) : bl2 (c • B) = ‖c‖ * bl2 B :=
  l2_smul c (fun q : W × Z => B q.1 q.2)

lemma bl2_sq (B : W → Z → ℂ) : bl2 B ^ 2 = ∑ w, l2 (B w) ^ 2 := by
  unfold bl2 l2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]

lemma l2_le_bl2 (B : W → Z → ℂ) (w : W) : l2 (B w) ≤ bl2 B := by
  have h := bl2_sq B
  have h1 : l2 (B w) ^ 2 ≤ bl2 B ^ 2 := by
    rw [h]; exact Finset.single_le_sum (f := fun w => l2 (B w) ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ w)
  exact (pow_le_pow_iff_left₀ (l2_nonneg _) (bl2_nonneg _) (by norm_num)).1 h1

/-- Replacing one wire by an array of at most its norm plus `δ` adds at most `δ`. -/
lemma bl2_update_le [DecidableEq W] (B : W → Z → ℂ) (w : W) (x : Z → ℂ) {δ : ℝ}
    (hx : l2 x ≤ l2 (B w) + δ) (hδ : 0 ≤ δ) : bl2 (Function.update B w x) ≤ bl2 B + δ := by
  have hB := bl2_nonneg B
  have hsplit : ∀ C : W → Z → ℂ, bl2 C ^ 2 =
      l2 (C w) ^ 2 + ∑ v ∈ Finset.univ.erase w, l2 (C v) ^ 2 := fun C => by
    rw [bl2_sq, ← Finset.add_sum_erase _ (fun v => l2 (C v) ^ 2) (Finset.mem_univ w)]
  have hrest : ∑ v ∈ Finset.univ.erase w, l2 (Function.update B w x v) ^ 2 =
      ∑ v ∈ Finset.univ.erase w, l2 (B v) ^ 2 :=
    Finset.sum_congr rfl fun v hv => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
  have h2 : bl2 (Function.update B w x) ^ 2 ≤ (bl2 B + δ) ^ 2 := by
    rw [hsplit, Function.update_self, hrest]
    have hs := hsplit B
    have hw := l2_le_bl2 B w
    have hx0 := l2_nonneg x
    have hx2 : l2 x ^ 2 ≤ (l2 (B w) + δ) ^ 2 := pow_le_pow_left₀ hx0 hx 2
    nlinarith [l2_nonneg (B w)]
  exact (pow_le_pow_iff_left₀ (bl2_nonneg _) (by linarith) (by norm_num)).1 h2

/-- The Lipschitz constant of a gate on the bank norm. -/
noncomputable def gateLip (g : Circuit.Gate W ℚ) : ℝ := 1 + (g.terms.map fun t => |(t.2 : ℝ)|).sum

omit [Fintype W] [Fintype Z] in
lemma one_le_gateLip (g : Circuit.Gate W ℚ) : 1 ≤ gateLip g := by
  unfold gateLip
  have : 0 ≤ (g.terms.map fun t => |(t.2 : ℝ)|).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _
  linarith

lemma l2_terms_le [DecidableEq W] (terms : List (W × ℚ)) (D : W → Z → ℂ) :
    l2 ((terms.map fun t => t.2 • D t.1).sum) ≤ (terms.map fun t => |(t.2 : ℝ)|).sum * bl2 D := by
  induction terms with
  | nil =>
    simp only [List.map_nil, List.sum_nil, zero_mul]
    unfold l2; simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (l2_add_le _ _).trans ?_
    have h1 : l2 (t.2 • D t.1) = |(t.2 : ℝ)| * l2 (D t.1) := by
      rw [show t.2 • D t.1 = ((t.2 : ℂ)) • D t.1 by funext z; simp [Rat.smul_def], l2_smul]
      congr 1
      rw [show ((t.2 : ℚ) : ℂ) = ((t.2 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs]
    rw [h1]
    have := l2_le_bl2 D t.1
    nlinarith [abs_nonneg (t.2 : ℝ)]

omit [Fintype W] [Fintype Z] in
lemma terms_sub [DecidableEq W] (terms : List (W × ℚ)) (X X' : W → Z → ℂ) :
    (terms.map fun p => p.2 • X p.1).sum - (terms.map fun p => p.2 • X' p.1).sum =
      (terms.map fun p => p.2 • (X - X') p.1).sum := by
  induction terms with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, Pi.sub_apply, smul_sub] at ih ⊢
    rw [← ih]; abel

omit [Fintype W] [Fintype Z] in
lemma moduleGate_sub [DecidableEq W] (g : Circuit.Gate W ℚ) (X X' : W → Z → ℂ) :
    FramedCircuit.moduleGate g X - FramedCircuit.moduleGate g X' =
      FramedCircuit.moduleGate g (X - X') := by
  funext w
  simp only [FramedCircuit.moduleGate, Pi.sub_apply]
  by_cases hw : w = g.target
  · subst hw
    simp only [Function.update_self]
    have h := terms_sub g.terms X X'
    simp only [Pi.sub_apply] at h
    rw [← h]; abel
  · simp [Function.update_of_ne hw]

/-- A gate is Lipschitz on the bank norm with constant `gateLip g`. -/
lemma bl2_moduleGate_le [DecidableEq W] (g : Circuit.Gate W ℚ) (D : W → Z → ℂ) :
    bl2 (FramedCircuit.moduleGate g D) ≤ gateLip g * bl2 D := by
  have e : FramedCircuit.moduleGate g D =
      D + Function.update (0 : W → Z → ℂ) g.target ((g.terms.map fun p => p.2 • D p.1).sum) := by
    funext w z
    simp only [FramedCircuit.moduleGate, Pi.add_apply]
    by_cases hw : w = g.target
    · subst hw; simp
    · simp [Function.update_of_ne hw]
  rw [e]
  refine (bl2_add_le _ _).trans ?_
  have h2 : bl2 (Function.update (0 : W → Z → ℂ) g.target
      ((g.terms.map fun p => p.2 • D p.1).sum)) ≤ (g.terms.map fun t => |(t.2 : ℝ)|).sum * bl2 D := by
    have h := bl2_update_le (0 : W → Z → ℂ) g.target
      ((g.terms.map fun p => p.2 • D p.1).sum) (δ := (g.terms.map fun t => |(t.2 : ℝ)|).sum * bl2 D)
      (by
        have : l2 ((0 : W → Z → ℂ) g.target) = 0 := by unfold l2; simp
        rw [this, zero_add]; exact l2_terms_le _ D)
      (mul_nonneg (by
        exact List.sum_nonneg fun x hx => by
          obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx; exact abs_nonneg _) (bl2_nonneg _))
    have h0 : bl2 (0 : W → Z → ℂ) = 0 := by unfold bl2 l2; simp
    rw [h0, zero_add] at h
    exact h
  unfold gateLip
  linarith

lemma bl2_moduleGate_sub_le [DecidableEq W] (g : Circuit.Gate W ℚ) (X X' : W → Z → ℂ) :
    bl2 (FramedCircuit.moduleGate g X - FramedCircuit.moduleGate g X') ≤
      gateLip g * bl2 (X - X') := by
  rw [moduleGate_sub]; exact bl2_moduleGate_le g _

end Bank

/-! ### The view and the norm -/

section View

variable {Y : Type} [Fintype Y] {n k : ℕ}

/-- A view duplicates every entry `2^k` times: `‖view e f‖ = √(2^k) ‖f‖`. -/
lemma l2_view {e : Fin k → Fin n} (he : Function.Injective e) (f : Arr Y n) :
    l2 (view e f) = √(2 ^ k) * l2 f := by
  let τ : (Y × (Fin n → ZMod 2)) × (Fin k → ZMod 2) ≃ (Y × (Fin n → ZMod 2)) × (Fin k → ZMod 2) :=
    ⟨fun p => ((p.1.1, merge e p.1.2 p.2), fun i => p.1.2 (e i)),
      fun p => ((p.1.1, merge e p.1.2 p.2), fun i => p.1.2 (e i)),
      fun p => by
        obtain ⟨⟨y, r⟩, a⟩ := p
        simp only [merge_merge, merge_extract]
        congr 2
        funext i; exact merge_apply_of_inj he r a i,
      fun p => by
        obtain ⟨⟨y, r⟩, a⟩ := p
        simp only [merge_merge, merge_extract]
        congr 2
        funext i; exact merge_apply_of_inj he r a i⟩
  rw [← l2_comp_equiv τ]
  have e1 : (view e f ∘ τ) = fun p => f p.1 := by
    funext ⟨⟨y, r⟩, a⟩
    simp only [Function.comp_apply, view, τ, Equiv.coe_fn_mk, merge_merge, merge_extract]
  rw [e1]
  unfold l2
  rw [Fintype.sum_prod_type, ← Real.sqrt_mul (by positivity)]
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Finset.mul_sum]
  push_cast; rfl

omit [Fintype Y] in
lemma view_sub (e : Fin k → Fin n) (f g : Arr Y n) : view e (f - g) = view e f - view e g := rfl

end View

lemma l2_phaseArr {Y : Type} [Fintype Y] {k : ℕ} (i : Fin m) (c : ZMod 4) (u : Arr Y (m * k)) :
    l2 (phaseArr i c u) = l2 u := by
  apply l2_congr_norm'
  intro p
  simp only [phaseArr, norm_mul, norm_prod]
  have : ∀ col : Fin k, ‖BinaryPhase.phase (c * BinaryPhase.bitLift (toCols p.2 col i))‖ = 1 :=
    fun col => by simp [BinaryPhase.phase]
  simp [this]

/-! ### A run with rounded children -/

section Run

variable {Y : Type} [Fintype Y] {n k : ℕ} {e : Fin (m * k) → Fin n}

/-- The error bound of a run: `δ` per factor, twice the gate constant per gate. -/
noncomputable def errRun (δ : ℝ) : List Instr → ℝ → ℝ
  | [], E => E
  | .gate g :: rest, E => errRun δ rest (2 * gateLip g * E)
  | .factor _ _ :: rest, E => errRun δ rest (E + δ)
  | .trans _ _ :: rest, E => errRun δ rest E
  | .xor _ _ _ :: rest, E => errRun δ rest E
  | .phase _ _ _ :: rest, E => errRun δ rest E

lemma errRun_mono (δ : ℝ) (l : List Instr) {E E' : ℝ} (h : E ≤ E') : errRun δ l E ≤ errRun δ l E' := by
  induction l generalizing E E' with
  | nil => exact h
  | cons i rest ih =>
    cases i with
    | factor w g => exact ih (by linarith)
    | gate g => exact ih (mul_le_mul_of_nonneg_left h (by have := one_le_gateLip g; linarith))
    | trans w v => exact ih h
    | xor w i j => exact ih h
    | phase w i c => exact ih h

/-- The product of twice the gate constants of a program. -/
noncomputable def lipProd : List Instr → ℝ
  | [] => 1
  | .gate g :: rest => 2 * gateLip g * lipProd rest
  | .factor _ _ :: rest => lipProd rest
  | .trans _ _ :: rest => lipProd rest
  | .xor _ _ _ :: rest => lipProd rest
  | .phase _ _ _ :: rest => lipProd rest

/-- The number of factors of a program. -/
def facCount : List Instr → ℕ
  | [] => 0
  | .gate _ :: rest => facCount rest
  | .factor _ _ :: rest => 1 + facCount rest
  | .trans _ _ :: rest => facCount rest
  | .xor _ _ _ :: rest => facCount rest
  | .phase _ _ _ :: rest => facCount rest

lemma one_le_lipProd : ∀ l : List Instr, 1 ≤ lipProd l
  | [] => le_rfl
  | .gate g :: rest => by
    have h1 := one_le_gateLip g
    have h2 := one_le_lipProd rest
    simp only [lipProd]; nlinarith
  | .factor _ _ :: rest => one_le_lipProd rest
  | .trans _ _ :: rest => one_le_lipProd rest
  | .xor _ _ _ :: rest => one_le_lipProd rest
  | .phase _ _ _ :: rest => one_le_lipProd rest

/-- **The closed form of the run error**: `errRun δ l E ≤ lipProd l (E + facCount l δ)`. -/
lemma errRun_le {δ : ℝ} (hδ : 0 ≤ δ) (l : List Instr) {E : ℝ} (hE : 0 ≤ E) :
    errRun δ l E ≤ lipProd l * (E + facCount l * δ) := by
  induction l generalizing E with
  | nil => simp [errRun, lipProd, facCount]
  | cons i rest ih =>
    cases i with
    | factor w g =>
      simp only [errRun, lipProd, facCount]
      refine (ih (by linarith)).trans (le_of_eq ?_)
      push_cast; ring
    | gate g =>
      simp only [errRun, lipProd, facCount]
      have hL := one_le_gateLip g
      have hP := one_le_lipProd rest
      refine (ih (mul_nonneg (by linarith) hE)).trans ?_
      have h1 : 2 * gateLip g * E + facCount rest * δ ≤ 2 * gateLip g * (E + facCount rest * δ) := by
        have : (0 : ℝ) ≤ facCount rest * δ := by positivity
        nlinarith
      calc lipProd rest * (2 * gateLip g * E + facCount rest * δ) ≤
          lipProd rest * (2 * gateLip g * (E + facCount rest * δ)) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = 2 * gateLip g * lipProd rest * (E + facCount rest * δ) := by ring
    | trans w v => simp only [errRun, lipProd, facCount]; exact ih hE
    | xor w i j => simp only [errRun, lipProd, facCount]; exact ih hE
    | phase w i c => simp only [errRun, lipProd, facCount]; exact ih hE

/-- An isometric linear update of one wire does not change the bank error. -/
lemma bl2_iso_update {Z : Type} [Fintype Z] (V X : NWire → Z → ℂ) (w : NWire) (T : (Z → ℂ) → Z → ℂ)
    (hT : ∀ (a : ℂ) u, T (a • u) = a • T u) (hsub : ∀ u u', T (u - u') = T u - T u')
    (hiso : ∀ u, l2 (T u) = l2 u) (s : ℕ) :
    bl2 (Function.update V w (T (V w)) - (2 : ℂ) ^ s • Function.update X w (T (X w))) =
      bl2 (V - (2 : ℂ) ^ s • X) := by
  have h : Function.update V w (T (V w)) - (2 : ℂ) ^ s • Function.update X w (T (X w)) =
      Function.update (V - (2 : ℂ) ^ s • X) w (T ((V - (2 : ℂ) ^ s • X) w)) := by
    funext v
    by_cases hv : v = w
    · subst hv; simp [hsub, hT]
    · simp [Function.update_of_ne hv]
  rw [h]
  generalize V - (2 : ℂ) ^ s • X = D
  refine le_antisymm ?_ ?_
  · have h := bl2_update_le D w (T (D w)) (δ := 0) (by rw [hiso, add_zero]) le_rfl
    rw [add_zero] at h
    exact h
  · have h := bl2_update_le (Function.update D w (T (D w))) w (D w) (δ := 0)
      (by rw [Function.update_self, hiso, add_zero]) le_rfl
    rw [Function.update_idem, Function.update_eq_self, add_zero] at h
    exact h

/-- A factor with a rounded child, against the complex factor: the child's error `δ` in the view. -/
lemma view_facM_err (he : Function.Injective e) (child : Fin m → ZArr Y n → ZArr Y n) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hchild : ∀ (j : Fin m) (u : ZArr Y n),
      l2 (view e (toC (child j u)) - slotProd j (view e (toC u))) ≤ δ)
    (g : ZMod 4 × BinaryWalsh.Address m) (u : ZArr Y n) :
    l2 (view e (toC (facM e child 0 g u)) - facImpl g (view e (toC u))) ≤ δ := by
  unfold facM facImpl
  split_ifs with h hq
  · have hv := Fin.find_spec h
    rw [view_pullM he, ← pullArr_sub, l2_pullArr _ (basisMap_invol _ _ hv), ← view_pullM he]
    exact hchild _ _
  · have hv := Fin.find_spec h
    rw [view_pullM he, ← pullArr_sub, l2_pullArr _ (basisMap_invol _ _ hv), view_conjZ,
      ← conjArr_sub, l2_conjArr, ← view_pullM he, ← view_conjZ]
    exact hchild _ _
  · rw [pow_zero, one_smul, sub_self]
    unfold l2; simpa using hδ

/-- **A run with rounded children against the complex run.** If every child is within `δ` of
the slot product in the view, then the views of the run are within `errRun δ l E` of `2^gates`
times the complex run, starting from an error `E` at scale `2^s`. -/
lemma view_runM_err (he : Function.Injective e) (child : Fin m → ZArr Y n → ZArr Y n) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hchild : ∀ (j : Fin m) (u : ZArr Y n),
      l2 (view e (toC (child j u)) - slotProd j (view e (toC u))) ≤ δ)
    (l : List Instr) (hl : ∀ g, Instr.gate g ∈ l → ∀ t ∈ g.terms, (2 * t.2).den = 1)
    (s : ℕ) (B : NWire → ZArr Y n) (X : NWire → Arr (Y × (Fin n → ZMod 2)) (m * k)) {E : ℝ}
    (hE : bl2 ((fun w => view e (toC (B w))) - (2 : ℂ) ^ s • X) ≤ E) :
    bl2 ((fun w => view e (toC (runM e child 0 l B w))) -
      (2 : ℂ) ^ (s + progExp 0 l) • runWith facImpl l X) ≤ errRun δ l E := by
  induction l generalizing s B X E with
  | nil => simpa [runM, progExp, runWith, errRun] using hE
  | cons i rest ih =>
    have hrest : ∀ g, Instr.gate g ∈ rest → ∀ t ∈ g.terms, (2 * t.2).den = 1 :=
      fun g hg => hl g (List.mem_cons_of_mem _ hg)
    cases i with
    | factor w g =>
      simp only [runM, runWith, progExp, errRun, zero_add]
      refine ih hrest s _ _ ?_
      have hupd : ((fun v => view e (toC (execM e child 0 (.factor w g) B v))) -
          (2 : ℂ) ^ s • execWith facImpl (.factor w g) X) =
          Function.update ((fun v => view e (toC (B v))) - (2 : ℂ) ^ s • X) w
            (view e (toC (facM e child 0 g (B w))) - (2 : ℂ) ^ s • facImpl g (X w)) := by
        funext v
        simp only [execM, execWith, Pi.sub_apply, Pi.smul_apply]
        by_cases hv : v = w
        · subst hv; simp
        · simp [hv]
      rw [hupd]
      refine bl2_update_le _ w _ ?_ hδ |>.trans (by linarith)
      have e2 : view e (toC (facM e child 0 g (B w))) - (2 : ℂ) ^ s • facImpl g (X w) =
          (view e (toC (facM e child 0 g (B w))) - facImpl g (view e (toC (B w)))) +
            (facImpl g (view e (toC (B w))) - facImpl g ((2 : ℂ) ^ s • X w)) := by
        have : facImpl g ((2 : ℂ) ^ s • X w) = (2 : ℂ) ^ s • facImpl g (X w) :=
          facImpl_two_pow_smul g s (X w)
        rw [this]; abel
      rw [e2]
      refine (l2_add_le _ _).trans ?_
      rw [l2_facImpl_sub]
      have h1 := view_facM_err he child hδ hchild g (B w)
      simp only [Pi.sub_apply, Pi.smul_apply]
      linarith
    | gate g =>
      simp only [runM, runWith, progExp, errRun]
      have hs : s + (1 + progExp 0 rest) = (s + 1) + progExp 0 rest := by ring
      rw [hs]
      refine ih hrest (s + 1) _ _ ?_
      have hg : ((fun v => view e (toC (execM e child 0 (.gate g) B v))) -
          (2 : ℂ) ^ (s + 1) • execWith facImpl (.gate g) X) =
          (2 : ℂ) • FramedCircuit.moduleGate g ((fun v => view e (toC (B v))) - (2 : ℂ) ^ s • X) := by
        funext v
        have h1 := view_gateZ (e := e) g (hl g List.mem_cons_self) B v
        simp only [execM, execWith, Pi.sub_apply, Pi.smul_apply] at h1 ⊢
        rw [h1, ← moduleGate_sub, moduleGate_smul, pow_succ]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_sub, smul_smul]
        ring_nf
      rw [hg, bl2_smul]
      have h2 := bl2_moduleGate_le g ((fun v => view e (toC (B v))) - (2 : ℂ) ^ s • X)
      have h3 := one_le_gateLip g
      have hn : ‖(2 : ℂ)‖ = 2 := by simp
      rw [hn]
      calc 2 * bl2 (FramedCircuit.moduleGate g _) ≤ 2 * (gateLip g * bl2 _) := by gcongr
        _ ≤ 2 * gateLip g * E := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hE (by linarith)
    | trans w v =>
      simp only [runM, runWith, progExp, errRun]
      refine ih hrest s _ _ ?_
      change bl2 ((fun u => view e (toC (Function.update B w (pullM e (· + v) (B w)) u))) -
        (2 : ℂ) ^ s • Function.update X w (pullArr (· + v) (X w))) ≤ E
      rw [view_update, view_pullM he]
      exact (bl2_iso_update _ _ _ (pullArr (· + v)) (fun a u => pullArr_smul _ a u)
        (fun u u' => pullArr_sub _ u u') (fun u => l2_pullArr _ (fun a => by
          funext t; simp only [Pi.add_apply]; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]) u)
          s).trans_le hE
    | xor w i j =>
      simp only [runM, runWith, progExp, errRun]
      refine ih hrest s _ _ ?_
      change bl2 ((fun u => view e (toC (Function.update B w
        (pullM e (Networks.Certificates.T16.Impl.xorMap i j) (B w)) u))) -
        (2 : ℂ) ^ s • Function.update X w (pullArr (Networks.Certificates.T16.Impl.xorMap i j) (X w))) ≤ E
      rw [view_update, view_pullM he]
      exact (bl2_iso_update _ _ _ _ (fun a u => pullArr_smul _ a u)
        (fun u u' => pullArr_sub _ u u') (fun u => l2_pullArr _
          (Networks.Certificates.T16.Impl.xorMap_involutive i j) u) s).trans_le hE
    | phase w i c =>
      simp only [runM, runWith, progExp, errRun]
      refine ih hrest s _ _ ?_
      change bl2 ((fun u => view e (toC (Function.update B w (phaseM e i c (B w)) u))) -
        (2 : ℂ) ^ s • Function.update X w (phaseArr i c (X w))) ≤ E
      rw [view_update, view_phaseM he]
      exact (bl2_iso_update _ _ _ (phaseArr i c) (fun a u => phaseArr_smul i c a u)
        (fun u u' => by funext p; simp only [phaseArr, Pi.sub_apply]; ring)
        (fun u => l2_phaseArr i c u) s).trans_le hE

end Run

/-! ### The node -/

section Node

variable {Y : Type} [Fintype Y] {n k : ℕ}

omit [Fintype Y] in
lemma l2_le_of_injective {X X' : Type} [Fintype X] [Fintype X'] (f : X → ℂ) (ι : X' → X)
    (hι : Function.Injective ι) : l2 (f ∘ ι) ≤ l2 f := by
  unfold l2
  apply Real.sqrt_le_sqrt
  classical
  calc ∑ x', ‖(f ∘ ι) x'‖ ^ 2 = ∑ x ∈ Finset.univ.image ι, ‖f x‖ ^ 2 := by
        rw [Finset.sum_image (fun a _ b _ h => hι h)]; rfl
    _ ≤ ∑ x, ‖f x‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity

omit [Fintype Y] in
lemma l2_congr_norm {X : Type} [Fintype X] (f g : X → ℂ) (h : ∀ x, ‖f x‖ = ‖g x‖) :
    l2 f = l2 g := l2_congr_norm' f g h

variable (e : Fin (m * k) → Fin n)

end Node

end IntegerMultBounds.MathlibTM2.Layer
