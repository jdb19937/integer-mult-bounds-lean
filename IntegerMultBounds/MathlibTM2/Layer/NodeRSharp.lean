module

public import IntegerMultBounds.MathlibTM2.Layer.NodeR

/-!
# The node error without the view factor

`nodeM_err` measures the child error in the view, which duplicates every entry `2^(mk)` times,
and reads the output as a sub-array of the view, so it loses a factor `√(2^(mk))` per level.
Every array of the complex run ignores the spectator bits at the active positions
(`SpecInv`): the input is a view, and the factors and gates act on the active address only
(`facImpl_reidx`, `moduleGate_breidx`). For such an array the diagonal sub-array that the output
reads has exactly `1/√(2^(mk))` of its norm (`sqrt_mul_l2_diag`), and the factor cancels:
`nodeM_err_sharp` bounds the node error by `errRun δ (program ds) 0`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks BinaryWalsh BinaryPhase BinaryColumns ComplexEndpoints
  ComplexFramedExecution

/-! ### Reindexing the spectator -/

section Respec

variable {X Z : Type} {k : ℕ}

/-- Reindex the spectator of an array. -/
def reidx {N : ℕ} (φ : Z → X) (u : Arr X N) : Arr Z N := fun p => u (φ p.1, p.2)

/-- Reindex the spectator of every wire of a bank. -/
def breidx {W : Type} {N : ℕ} (φ : Z → X) (B : W → Arr X N) : W → Arr Z N :=
  fun w => reidx φ (B w)

lemma pullArr_reidx (φ : Z → X) (L : BinaryWalsh.Address m → BinaryWalsh.Address m)
    (u : Arr X (m * k)) : reidx φ (pullArr L u) = pullArr L (reidx φ u) := rfl

lemma conjArr_reidx (φ : Z → X) (u : Arr X (m * k)) :
    reidx φ (conjArr u) = conjArr (reidx φ u) := rfl

lemma slotProd_reidx (φ : Z → X) (j : Fin m) (u : Arr X (m * k)) :
    reidx φ (slotProd j u) = slotProd j (reidx φ u) := by
  have := prod_respec φ 1 ((List.finRange k).map (bitIdx j)) u
  simp only [List.map_map, Function.comp_def] at this
  exact this

lemma facImpl_reidx (φ : Z → X) (g : ZMod 4 × BinaryWalsh.Address m) (u : Arr X (m * k)) :
    reidx φ (facImpl g u) = facImpl g (reidx φ u) := by
  unfold facImpl
  split_ifs <;> simp only [pullArr_reidx, conjArr_reidx, slotProd_reidx]

lemma terms_sum_apply {W : Type} {N : ℕ} (terms : List (W × ℚ)) (x : W → Arr X N)
    (p : X × (Fin N → ZMod 2)) :
    (terms.map fun t => t.2 • x t.1).sum p = (terms.map fun t => t.2 • x t.1 p).sum := by
  induction terms with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, List.sum_cons, Pi.add_apply, ih]; rfl

lemma breidx_update {W : Type} [DecidableEq W] {N : ℕ} (φ : Z → X) (B : W → Arr X N) (w : W)
    (x : Arr X N) : breidx φ (Function.update B w x) = Function.update (breidx φ B) w (reidx φ x) := by
  funext v
  by_cases hv : v = w
  · subst hv; simp [breidx]
  · simp [breidx, Function.update_of_ne hv]

lemma moduleGate_breidx {W : Type} [DecidableEq W] {N : ℕ} (φ : Z → X) (g : Circuit.Gate W ℚ)
    (B : W → Arr X N) :
    breidx φ (FramedCircuit.moduleGate g B) = FramedCircuit.moduleGate g (breidx φ B) := by
  unfold FramedCircuit.moduleGate
  rw [breidx_update]
  congr 1
  funext p
  simp only [reidx, Pi.add_apply, terms_sum_apply]
  rfl

lemma runWith_breidx (φ : Z → X) :
    ∀ (l : List Instr) (B : NWire → Arr X (m * k)),
      breidx φ (runWith facImpl l B) = runWith facImpl l (breidx φ B)
  | [], _ => rfl
  | .factor w g :: rest, B => by
    simp only [runWith, execWith]
    rw [runWith_breidx φ rest, breidx_update, facImpl_reidx]
    rfl
  | .gate g :: rest, B => by
    simp only [runWith, execWith]
    rw [runWith_breidx φ rest, moduleGate_breidx]
  | .trans w v :: rest, B => by
    simp only [runWith, execWith]
    rw [runWith_breidx φ rest, breidx_update, pullArr_reidx]
    rfl
  | .xor w i j :: rest, B => by
    simp only [runWith, execWith]
    rw [runWith_breidx φ rest, breidx_update, pullArr_reidx]
    rfl
  | .phase w i c :: rest, B => by
    simp only [runWith, execWith]
    rw [runWith_breidx φ rest, breidx_update]
    rfl

end Respec

/-! ### Arrays that ignore the spectator bits at the active positions -/

section Inv

variable {Y : Type} {n k : ℕ}

/-- Overwrite the spectator bits at the positions `e`. -/
noncomputable def specSet (e : Fin k → Fin n) (b : Fin k → ZMod 2) : Y × (Fin n → ZMod 2) → Y × (Fin n → ZMod 2) :=
  fun q => (q.1, merge e q.2 b)

/-- The array ignores the spectator bits at the positions `e`. -/
def SpecInv {N : ℕ} (e : Fin k → Fin n) (A : Arr (Y × (Fin n → ZMod 2)) N) : Prop :=
  ∀ b, reidx (specSet e b) A = A

lemma specInv_view {k' : ℕ} (e : Fin k' → Fin n) (f : Arr Y n) : SpecInv e (view e f) := by
  intro b; funext p
  simp only [reidx, specSet, view, merge_merge]

lemma specInv_runWith {k' : ℕ} (e : Fin k' → Fin n) (l : List Instr)
    (B : NWire → Arr (Y × (Fin n → ZMod 2)) (m * k)) (hB : ∀ w, SpecInv e (B w)) :
    ∀ w, SpecInv e (runWith facImpl l B w) := by
  intro w b
  have h := congrFun (runWith_breidx (specSet e b) l B) w
  simp only [breidx] at h
  rw [h]
  congr 1
  funext v
  exact hB v b

lemma specInv_sub {N : ℕ} {e : Fin k → Fin n} {A A' : Arr (Y × (Fin n → ZMod 2)) N}
    (hA : SpecInv e A) (hA' : SpecInv e A') : SpecInv e (A - A') := by
  intro b
  have h1 := hA b
  have h2 := hA' b
  funext p
  have e1 := congrFun h1 p
  have e2 := congrFun h2 p
  simp only [reidx, Pi.sub_apply] at e1 e2 ⊢
  rw [e1, e2]

lemma specInv_smul {N : ℕ} {e : Fin k → Fin n} (c : ℂ) {A : Arr (Y × (Fin n → ZMod 2)) N}
    (hA : SpecInv e A) : SpecInv e (c • A) := by
  intro b
  funext p
  have e1 := congrFun (hA b) p
  simp only [reidx, Pi.smul_apply] at e1 ⊢
  rw [e1]

/-- **The diagonal sub-array.** For an array that ignores the spectator bits at the positions
`e`, the entries whose address equals those spectator bits carry `1/√(2^k)` of its norm. -/
lemma sqrt_mul_l2_diag [Fintype Y] {e : Fin k → Fin n} (he : Function.Injective e)
    (A : Arr (Y × (Fin n → ZMod 2)) k) (hA : SpecInv e A) :
    √(2 ^ k) * l2 (fun q : Y × (Fin n → ZMod 2) => A (q, fun i => q.2 (e i))) = l2 A := by
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
  rw [← l2_comp_equiv τ A]
  have e1 : (A ∘ τ) = fun p => A (p.1, fun i => p.1.2 (e i)) := by
    funext ⟨⟨y, r⟩, a⟩
    have := congrFun (hA a) ((y, r), fun i => r (e i))
    simp only [reidx, specSet] at this
    simp only [Function.comp_apply, τ, Equiv.coe_fn_mk]
    exact this
  rw [e1]
  unfold l2
  have hs : ∑ p : (Y × (Fin n → ZMod 2)) × (Fin k → ZMod 2), ‖A (p.1, fun i => p.1.2 (e i))‖ ^ 2 =
      2 ^ k * ∑ q : Y × (Fin n → ZMod 2), ‖A (q, fun i => q.2 (e i))‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [Finset.sum_const, Finset.card_univ]
  rw [hs, Real.sqrt_mul (by positivity)]

end Inv

/-! ### The bank diagonal and the scaling of the run error -/

lemma errRun_smul {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) :
    ∀ (l : List Instr) (E : ℝ), errRun (c * δ) l (c * E) = c * errRun δ l E
  | [], _ => rfl
  | .factor _ _ :: rest, E => by
    simp only [errRun]; rw [← errRun_smul hc hδ rest]; congr 1; ring
  | .gate g :: rest, E => by
    simp only [errRun]; rw [← errRun_smul hc hδ rest]; congr 1; ring
  | .trans _ _ :: rest, E => by simp only [errRun]; exact errRun_smul hc hδ rest E
  | .xor _ _ _ :: rest, E => by simp only [errRun]; exact errRun_smul hc hδ rest E
  | .phase _ _ _ :: rest, E => by simp only [errRun]; exact errRun_smul hc hδ rest E

lemma sqrt_mul_l2_bank_diag {Y W : Type} [Fintype Y] [Fintype W] {n k : ℕ}
    {e : Fin k → Fin n} (he : Function.Injective e) (σ : W → W) (hσ : ∀ w, σ (σ w) = w)
    (D : W → Arr (Y × (Fin n → ZMod 2)) k) (hD : ∀ w, SpecInv e (D w)) :
    √(2 ^ k) * l2 (fun p : (Y × W) × (Fin n → ZMod 2) =>
      D (σ p.1.2) ((p.1.1, p.2), fun i => p.2 (e i))) = bl2 D := by
  let σe : W ≃ W := ⟨σ, σ, hσ, hσ⟩
  have hw : ∀ w, √(2 ^ k) * l2 (fun q : Y × (Fin n → ZMod 2) => D w (q, fun i => q.2 (e i))) =
      l2 (D w) := fun w => sqrt_mul_l2_diag he (D w) (hD w)
  have hsq : ∀ x : ℝ, 0 ≤ x → √(2 ^ k) * x = √(2 ^ k * x ^ 2) := fun x hx => by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hx]
  rw [hsq _ (l2_nonneg _), ← Real.sqrt_sq (bl2_nonneg D), bl2_sq]
  congr 1
  have h1 : l2 (fun p : (Y × W) × (Fin n → ZMod 2) =>
      D (σ p.1.2) ((p.1.1, p.2), fun i => p.2 (e i))) ^ 2 =
      ∑ w, l2 (fun q : Y × (Fin n → ZMod 2) => D w (q, fun i => q.2 (e i))) ^ 2 := by
    unfold l2
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
    rw [← Equiv.sum_comp σe]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fintype.sum_prod_type, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    simp [σe, hσ]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← hw w, mul_pow, Real.sq_sqrt (by positivity)]

/-- **The diagonal of a sub-bank.** Along an injective choice of wires, the diagonal carries at
most the bank norm. -/
lemma sqrt_mul_l2_subbank_diag {Y V W : Type} [Fintype Y] [Fintype V] [Fintype W] [DecidableEq W] {n k : ℕ}
    {e : Fin k → Fin n} (he : Function.Injective e) (τ : V → W) (hτ : Function.Injective τ)
    (D : W → Arr (Y × (Fin n → ZMod 2)) k) (hD : ∀ w, SpecInv e (D w)) :
    √(2 ^ k) * l2 (fun p : (Y × V) × (Fin n → ZMod 2) =>
      D (τ p.1.2) ((p.1.1, p.2), fun i => p.2 (e i))) ≤ bl2 D := by
  have hw : ∀ w, √(2 ^ k) * l2 (fun q : Y × (Fin n → ZMod 2) => D w (q, fun i => q.2 (e i))) =
      l2 (D w) := fun w => sqrt_mul_l2_diag he (D w) (hD w)
  have hsq : ∀ x : ℝ, 0 ≤ x → √(2 ^ k) * x = √(2 ^ k * x ^ 2) := fun x hx => by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hx]
  rw [hsq _ (l2_nonneg _), ← Real.sqrt_sq (bl2_nonneg D), bl2_sq]
  apply Real.sqrt_le_sqrt
  have h1 : l2 (fun p : (Y × V) × (Fin n → ZMod 2) =>
      D (τ p.1.2) ((p.1.1, p.2), fun i => p.2 (e i))) ^ 2 =
      ∑ v, l2 (fun q : Y × (Fin n → ZMod 2) => D (τ v) (q, fun i => q.2 (e i))) ^ 2 := by
    unfold l2
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Fintype.sum_prod_type, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  rw [h1, Finset.mul_sum]
  calc ∑ v, 2 ^ k * l2 (fun q : Y × (Fin n → ZMod 2) => D (τ v) (q, fun i => q.2 (e i))) ^ 2
      = ∑ v, l2 (D (τ v)) ^ 2 := Finset.sum_congr rfl fun v _ => by
        rw [← hw (τ v), mul_pow, Real.sq_sqrt (by positivity)]
    _ = ∑ w ∈ Finset.univ.image τ, l2 (D w) ^ 2 := by
        rw [Finset.sum_image (fun a _ b _ h => hτ h)]
    _ ≤ ∑ w, l2 (D w) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity

/-! ### The node -/

section Node

variable {Y : Type} [Fintype Y] {n k : ℕ}

omit [Fintype Y] in
variable (e : Fin (m * k) → Fin n)

/-- **The node with rounded children, sharp form.** If every child is within `δ` of the kernels
on its slot, the node with `Tc = 0` is within `errRun δ (program ds) 0` of `2^(nodeExp ds 0)`
times the kernels on every active bit. -/
theorem nodeM_err_sharp (he : Function.Injective e) (ds : Directions)
    (hd : ComplexPhaseBudget.Realizes ds) (child : Fin m → ZArr Y n → ZArr Y n) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hchild : ∀ (j : Fin m) (u : ZArr Y n), l2 (toC (child j u) -
      ((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC u)) ≤ δ)
    (f : ZArr (Y × DWire) n) :
    l2 (toC (nodeM e child 0 ds f) -
      (2 : ℂ) ^ nodeExp ds 0 • ((List.finRange (m * k)).map fun i => kBit 1 (e i)).prod (toC f)) ≤
      errRun δ (program ds) 0 := by
  -- the child in the view
  have hchildV : ∀ (j : Fin m) (u : ZArr Y n),
      l2 (view e (toC (child j u)) - slotProd j (view e (toC u))) ≤ √(2 ^ (m * k)) * δ := by
    intro j u
    have h1 : slotProd j (view e (toC u)) =
        view e (((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC u)) := by
      have := prod_view e he 1 ((List.finRange k).map (bitIdx j)) (toC u)
      simp only [List.map_map, Function.comp_def] at this
      exact this
    rw [h1, ← view_sub, l2_view he]
    exact mul_le_mul_of_nonneg_left (hchild j u) (Real.sqrt_nonneg _)
  let F : Arr ((Y × (Fin n → ZMod 2)) × DWire) (m * k) :=
    fun p => toC f ((p.1.1.1, p.1.2), merge e p.1.1.2 p.2)
  have hbank : (fun w => view e (toC (bankZ f w))) = bankOf k F := by
    funext w
    rcases w with j | c
    · rfl
    · funext p; simp [bankZ, bankOf, view, toC]
  have hrun := view_runM_err he child (by positivity) hchildV (program ds) (program_gate_coeff ds) 0
    (bankZ f) (bankOf k F) (E := 0) (by
      rw [hbank, pow_zero, one_smul, sub_self]
      unfold bl2 l2; simp)
  rw [zero_add] at hrun
  set Vr := fun w => view e (toC (runM e child 0 (program ds) (bankZ f) w))
  set S := runWith facImpl (program ds) (bankOf k F)
  have hA := nodeA_correct (Y := Y × (Fin n → ZMod 2)) ds hd F
  set D := Vr - (2 : ℂ) ^ progExp 0 (program ds) • S
  -- the entries of the difference are entries of the view difference on the families
  have hentry : ∀ y j r, (toC (nodeM e child 0 ds f) -
      (2 : ℂ) ^ nodeExp ds 0 • ((List.finRange (m * k)).map fun i => kBit 1 (e i)).prod (toC f))
      ((y, j), r) = D (.inl j) ((y, r), fun i => r (e i)) := by
    intro y j r
    have h1 : toC (nodeM e child 0 ds f) ((y, j), r) = Vr (.inl j) ((y, r), fun i => r (e i)) := by
      simp only [Vr, view, merge_extract]
      rfl
    have h3 : S (.inl j) ((y, r), fun i => r (e i)) = nodeA k ds F (((y, r), j), fun i => r (e i)) := by
      simp only [nodeA, unbank, S]
    simp only [D, Pi.sub_apply, Pi.smul_apply]
    rw [h1, h3, hA, ← view_Cfull e he (toC f) (y, j) r]
    congr 2
    exact Cfull_respec (fun z : (Y × (Fin n → ZMod 2)) × DWire => ((z.1.1, z.2), z.1.2))
      (view e (toC f)) ((y, r), j) (fun i => r (e i))
  have heq : l2 (toC (nodeM e child 0 ds f) -
      (2 : ℂ) ^ nodeExp ds 0 • ((List.finRange (m * k)).map fun i => kBit 1 (e i)).prod (toC f)) =
      l2 (fun p : (Y × DWire) × (Fin n → ZMod 2) =>
        D (Sum.inl p.1.2) ((p.1.1, p.2), fun i => p.2 (e i))) := by
    apply l2_congr_norm
    rintro ⟨⟨y, j⟩, r⟩
    rw [hentry]
  rw [heq]
  have hX0 : ∀ v, SpecInv e (bankOf k F v) := fun v => by
    have h := congrFun hbank v
    exact h ▸ specInv_view e (toC (bankZ f v))
  have hS : ∀ v, SpecInv e (S v) := specInv_runWith e (program ds) _ hX0
  have hV : ∀ v, SpecInv e (Vr v) := fun v => specInv_view e _
  have hD : ∀ w, SpecInv e (D w) := fun w => specInv_sub (hV w) (specInv_smul _ (hS w))
  have hdiag := sqrt_mul_l2_subbank_diag he Sum.inl Sum.inl_injective D hD
  have h0 := errRun_smul (c := √(2 ^ (m * k))) (Real.sqrt_nonneg _) hδ (program ds) 0
  rw [mul_zero] at h0
  rw [h0] at hrun
  have hpos : 0 < √(2 ^ (m * k)) := Real.sqrt_pos.2 (by positivity)
  have : √(2 ^ (m * k)) * l2 (fun p : (Y × DWire) × (Fin n → ZMod 2) =>
        D (Sum.inl p.1.2) ((p.1.1, p.2), fun i => p.2 (e i))) ≤
      √(2 ^ (m * k)) * errRun δ (program ds) 0 := hdiag.trans hrun
  exact le_of_mul_le_mul_left this hpos

end Node

end IntegerMultBounds.MathlibTM2.Layer
