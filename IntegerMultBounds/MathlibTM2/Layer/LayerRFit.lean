module

import IntegerMultBounds.MathlibTM2.Layer.LayerRBounds
public import IntegerMultBounds.MathlibTM2.Node.CompactLayerProcR
import IntegerMultBounds.MathlibTM2.Layer.NodeRSharp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The size of the inputs of the rounded children

A child of the rounded node is only ever called on arrays reached by the run. `runM_congr`:
along a run whose children are within `δ` of the slot products, every input of a factor has view
norm at most `2^s lipProd l ‖X‖ + errRun δ l E`, so two children that agree on inputs of this
size give the same run. `nodeM_congr` is the node form: children agreeing on inputs of norm at
most `lipProd ‖f‖₂ + errRun δ (program ds) 0` give the same node.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.Networks BinaryWalsh BinaryPhase BinaryColumns ComplexEndpoints
  ComplexFramedExecution

lemma le_errRun {δ : ℝ} (hδ : 0 ≤ δ) : ∀ (l : List Instr) {E : ℝ}, 0 ≤ E → E ≤ errRun δ l E
  | [], _, _ => le_rfl
  | .factor _ _ :: rest, E, hE => by
    simp only [errRun]
    exact (by linarith : E ≤ E + δ).trans (le_errRun hδ rest (by linarith))
  | .gate g :: rest, E, hE => by
    simp only [errRun]
    have h := one_le_gateLip g
    have h1 : E ≤ 2 * gateLip g * E := by nlinarith
    exact h1.trans (le_errRun hδ rest (by positivity))
  | .trans _ _ :: rest, E, hE => by simp only [errRun]; exact le_errRun hδ rest hE
  | .xor _ _ _ :: rest, E, hE => by simp only [errRun]; exact le_errRun hδ rest hE
  | .phase _ _ _ :: rest, E, hE => by simp only [errRun]; exact le_errRun hδ rest hE

section Run

variable {Y : Type} [Fintype Y] {n k : ℕ} {e : Fin (m * k) → Fin n}

lemma bl2_update_eq [DecidableEq NWire] (B : NWire → Arr Y (m * k)) (w : NWire)
    (x : Arr Y (m * k)) (hx : l2 x = l2 (B w)) : bl2 (Function.update B w x) = bl2 B := by
  apply le_antisymm
  · simpa using bl2_update_le B w x (by rw [hx]; linarith) le_rfl
  · have h := bl2_update_le (Function.update B w x) w (B w) (by simp [hx]) le_rfl
    simpa using h

/-- **Children that agree on the reached inputs give the same run.** -/
lemma runM_congr (he : Function.Injective e) (child child' : Fin m → ZArr Y n → ZArr Y n)
    {δ β : ℝ} (hδ : 0 ≤ δ)
    (hchild : ∀ (j : Fin m) (u : ZArr Y n),
      l2 (view e (toC (child j u)) - slotProd j (view e (toC u))) ≤ δ)
    (hagree : ∀ (j : Fin m) (u : ZArr Y n), l2 (view e (toC u)) ≤ β → child j u = child' j u)
    (l : List Instr) (hl : ∀ g, Instr.gate g ∈ l → ∀ t ∈ g.terms, (2 * t.2).den = 1)
    (s : ℕ) (B : NWire → ZArr Y n) (X : NWire → Arr (Y × (Fin n → ZMod 2)) (m * k)) {E : ℝ}
    (hE : bl2 ((fun w => view e (toC (B w))) - (2 : ℂ) ^ s • X) ≤ E)
    (hβ : 2 ^ s * lipProd l * bl2 X + errRun δ l E ≤ β) :
    runM e child 0 l B = runM e child' 0 l B := by
  induction l generalizing s B X E with
  | nil => rfl
  | cons i rest ih =>
    have hrest : ∀ g, Instr.gate g ∈ rest → ∀ t ∈ g.terms, (2 * t.2).den = 1 :=
      fun g hg => hl g (List.mem_cons_of_mem _ hg)
    have hE0 : 0 ≤ E := (bl2_nonneg _).trans hE
    have hX0 := bl2_nonneg X
    cases i with
    | factor w g =>
      simp only [runM]
      have hL := one_le_lipProd rest
      -- the input of the factor is small
      have hin : l2 (view e (toC (B w))) ≤ β := by
        have h1 : l2 (view e (toC (B w))) ≤ bl2 (fun w => view e (toC (B w))) :=
          l2_le_bl2 (fun w => view e (toC (B w))) w
        have h2 : bl2 (fun w => view e (toC (B w))) ≤ E + 2 ^ s * bl2 X := by
          have := bl2_add_le ((fun w => view e (toC (B w))) - (2 : ℂ) ^ s • X) ((2 : ℂ) ^ s • X)
          rw [sub_add_cancel, bl2_smul, norm_pow, RCLike.norm_two] at this
          linarith
        have h3 : E ≤ errRun δ (Instr.factor w g :: rest) E := le_errRun hδ _ hE0
        have h4 : 2 ^ s * bl2 X ≤ 2 ^ s * lipProd (Instr.factor w g :: rest) * bl2 X := by
          simp only [lipProd]
          have : (0 : ℝ) ≤ 2 ^ s * bl2 X := mul_nonneg (by positivity) hX0
          nlinarith
        linarith
      have hfac : facM e child 0 g (B w) = facM e child' 0 g (B w) := by
        unfold facM
        split_ifs with h hq
        · rw [hagree]
          rw [view_pullM he, l2_pullArr _ (basisMap_invol _ _ (Fin.find_spec h))]
          exact hin
        · rw [hagree]
          rw [view_conjZ, l2_conjArr, view_pullM he,
            l2_pullArr _ (basisMap_invol _ _ (Fin.find_spec h))]
          exact hin
        · rfl
      have hex : execM e child 0 (.factor w g) B = execM e child' 0 (.factor w g) B := by
        funext v
        by_cases hv : v = w
        · subst hv; simp [execM, hfac]
        · simp [execM, hv]
      rw [← hex]
      refine ih hrest s _ (execWith facImpl (.factor w g) X) (E := E + δ) ?_ ?_
      · -- the error after the factor, as in `view_runM_err`
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
      · have hX' : bl2 (execWith facImpl (.factor w g) X) = bl2 X := by
          simp only [execWith]
          exact bl2_update_eq X w _ (l2_facImpl g (X w))
        rw [hX']
        simpa [lipProd, errRun] using hβ
    | gate g =>
      simp only [runM]
      have hex : execM e child 0 (.gate g) B = execM e child' 0 (.gate g) B := rfl
      rw [← hex]
      refine ih hrest (s + 1) _ (execWith facImpl (.gate g) X) (E := 2 * gateLip g * E) ?_ ?_
      · have hg : ((fun v => view e (toC (execM e child 0 (.gate g) B v))) -
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
      · have h2 : bl2 (execWith facImpl (.gate g) X) ≤ gateLip g * bl2 X :=
          bl2_moduleGate_le g X
        have hL := one_le_lipProd rest
        have h3 : (2 : ℝ) ^ (s + 1) * lipProd rest * bl2 (execWith facImpl (.gate g) X) ≤
            2 ^ s * lipProd (Instr.gate g :: rest) * bl2 X := by
          simp only [lipProd]
          have hp : (0 : ℝ) ≤ 2 ^ (s + 1) * lipProd rest := by positivity
          calc (2 : ℝ) ^ (s + 1) * lipProd rest * bl2 (execWith facImpl (.gate g) X)
              ≤ 2 ^ (s + 1) * lipProd rest * (gateLip g * bl2 X) :=
                mul_le_mul_of_nonneg_left h2 hp
            _ = 2 ^ s * (2 * gateLip g * lipProd rest) * bl2 X := by ring
        simp only [errRun] at hβ
        linarith
    | trans w v =>
      simp only [runM]
      have hex : execM e child 0 (.trans w v) B = execM e child' 0 (.trans w v) B := rfl
      rw [← hex]
      have hinv : ∀ a : BinaryWalsh.Address m, a + v + v = a := fun a => by
        funext t; simp only [Pi.add_apply]; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      refine ih hrest s _ (execWith facImpl (.trans w v) X) (E := E) ?_ ?_
      · change bl2 ((fun u => view e (toC (Function.update B w (pullM e (· + v) (B w)) u))) -
          (2 : ℂ) ^ s • Function.update X w (pullArr (· + v) (X w))) ≤ E
        rw [view_update, view_pullM he]
        exact (bl2_iso_update _ _ _ (pullArr (· + v)) (fun a u => pullArr_smul _ a u)
          (fun u u' => pullArr_sub _ u u') (fun u => l2_pullArr _ hinv u) s).trans_le hE
      · have hX' : bl2 (execWith facImpl (.trans w v) X) = bl2 X :=
          bl2_update_eq X w _ (l2_pullArr _ hinv (X w))
        rw [hX']
        simpa [lipProd, errRun] using hβ
    | xor w i j =>
      simp only [runM]
      have hex : execM e child 0 (.xor w i j) B = execM e child' 0 (.xor w i j) B := rfl
      rw [← hex]
      have hinv := Networks.Certificates.T16.Impl.xorMap_involutive i j
      refine ih hrest s _ (execWith facImpl (.xor w i j) X) (E := E) ?_ ?_
      · change bl2 ((fun u => view e (toC (Function.update B w
          (pullM e (Networks.Certificates.T16.Impl.xorMap i j) (B w)) u))) -
          (2 : ℂ) ^ s • Function.update X w
            (pullArr (Networks.Certificates.T16.Impl.xorMap i j) (X w))) ≤ E
        rw [view_update, view_pullM he]
        exact (bl2_iso_update _ _ _ _ (fun a u => pullArr_smul _ a u)
          (fun u u' => pullArr_sub _ u u') (fun u => l2_pullArr _ hinv u) s).trans_le hE
      · have hX' : bl2 (execWith facImpl (.xor w i j) X) = bl2 X :=
          bl2_update_eq X w _ (l2_pullArr _ hinv (X w))
        rw [hX']
        simpa [lipProd, errRun] using hβ
    | phase w i c =>
      simp only [runM]
      have hex : execM e child 0 (.phase w i c) B = execM e child' 0 (.phase w i c) B := rfl
      rw [← hex]
      refine ih hrest s _ (execWith facImpl (.phase w i c) X) (E := E) ?_ ?_
      · change bl2 ((fun u => view e (toC (Function.update B w (phaseM e i c (B w)) u))) -
          (2 : ℂ) ^ s • Function.update X w (phaseArr i c (X w))) ≤ E
        rw [view_update, view_phaseM he]
        exact (bl2_iso_update _ _ _ (phaseArr i c) (fun a u => phaseArr_smul i c a u)
          (fun u u' => by funext p; simp only [phaseArr, Pi.sub_apply]; ring)
          (fun u => l2_phaseArr i c u) s).trans_le hE
      · have hX' : bl2 (execWith facImpl (.phase w i c) X) = bl2 X :=
          bl2_update_eq X w _ (l2_phaseArr i c (X w))
        rw [hX']
        simpa [lipProd, errRun] using hβ

end Run

/-! ### The node -/

section Node

variable {Y : Type} [Fintype Y] {n k : ℕ}

lemma bl2_view (e : Fin (m * k) → Fin n) (he : Function.Injective e) (B : NWire → ZArr Y n) :
    bl2 (fun w => view e (toC (B w))) = √(2 ^ (m * k)) * bl2 (fun w => toC (B w)) := by
  have h1 := bl2_sq (fun w => view e (toC (B w)))
  have h2 := bl2_sq (fun w => toC (B w))
  simp only [l2_view he, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 ^ (m * k)),
    ← Finset.mul_sum] at h1
  rw [← h2] at h1
  have h3 : bl2 (fun w => view e (toC (B w))) ^ 2 = (√(2 ^ (m * k)) * bl2 (fun w => toC (B w))) ^ 2 := by
    rw [h1, mul_pow, Real.sq_sqrt (by positivity)]
  exact (pow_left_inj₀ (bl2_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (bl2_nonneg _)) two_ne_zero).1 h3

omit [Fintype Y] in
lemma l2_swap_bank {Y W : Type} [Fintype Y] [Fintype W] (F : Arr (Y × W) n) :
    bl2 (fun (w : W) (p : Y × (Fin n → ZMod 2)) => F ((p.1, w), p.2)) = l2 F := by
  let σ : W × (Y × (Fin n → ZMod 2)) ≃ (Y × W) × (Fin n → ZMod 2) :=
    ⟨fun q => ((q.2.1, q.1), q.2.2), fun p => (p.1.2, (p.1.1, p.2)), fun _ => rfl, fun _ => rfl⟩
  unfold bl2 l2
  congr 1
  exact Equiv.sum_comp σ (fun p => ‖F p‖ ^ 2)

lemma bl2_bankZ (f : ZArr (Y × DWire) n) :
    bl2 (fun w => toC (bankZ f w)) = l2 (toC f) := by
  have hs := bl2_sq (fun w => toC (bankZ f w))
  have hs' := bl2_sq (fun (j : DWire) (p : Y × (Fin n → ZMod 2)) => toC f ((p.1, j), p.2))
  rw [l2_swap_bank (toC f)] at hs'
  have h0 : ∀ c : Fin 8, l2 (toC (bankZ f (.inr c))) = 0 := by
    intro c; unfold l2 toC; simp [bankZ]
  rw [Fintype.sum_sum_type] at hs
  simp only [h0, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    add_zero] at hs
  have h : bl2 (fun w => toC (bankZ f w)) ^ 2 = l2 (toC f) ^ 2 := by rw [hs, hs']; rfl
  exact (pow_left_inj₀ (bl2_nonneg _) (l2_nonneg _) two_ne_zero).1 h

variable (e : Fin (m * k) → Fin n)

/-- **Children that agree on small inputs give the same node.** If every child is within `δ`
of the kernels on its slot and two children agree on inputs of norm at most `β`, with
`lipProd ‖f‖₂ + errRun δ (program ds) 0 ≤ β`, the nodes agree on `f`. -/
theorem nodeM_congr (he : Function.Injective e) (ds : Directions)
    (child child' : Fin m → ZArr Y n → ZArr Y n) {δ β : ℝ} (hδ : 0 ≤ δ)
    (hchild : ∀ (j : Fin m) (u : ZArr Y n), l2 (toC (child j u) -
      ((List.finRange k).map fun c => kBit 1 (e (bitIdx j c))).prod (toC u)) ≤ δ)
    (hagree : ∀ (j : Fin m) (u : ZArr Y n), l2 (toC u) ≤ β → child j u = child' j u)
    (f : ZArr (Y × DWire) n)
    (hβ : lipProd (program ds) * l2 (toC f) + errRun δ (program ds) 0 ≤ β) :
    nodeM e child 0 ds f = nodeM e child' 0 ds f := by
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
  have hpos : 0 < √(2 ^ (m * k)) := Real.sqrt_pos.2 (by positivity)
  have hagreeV : ∀ (j : Fin m) (u : ZArr Y n), l2 (view e (toC u)) ≤ √(2 ^ (m * k)) * β →
      child j u = child' j u := by
    intro j u hu
    rw [l2_view he] at hu
    exact hagree j u (le_of_mul_le_mul_left hu hpos)
  set B := bankZ f
  have hrun := runM_congr he child child' (by positivity) hchildV hagreeV (program ds)
    (program_gate_coeff ds) 0 B (fun w => view e (toC (B w))) (E := 0)
    (by rw [pow_zero, one_smul, sub_self]; unfold bl2 l2; simp) (by
      have h0 := errRun_smul (c := √(2 ^ (m * k))) (Real.sqrt_nonneg _) hδ (program ds) 0
      rw [mul_zero] at h0
      rw [h0, pow_zero, one_mul, bl2_view e he, bl2_bankZ]
      have := mul_le_mul_of_nonneg_left hβ (Real.sqrt_nonneg (2 ^ (m * k)))
      linarith)
  unfold nodeM
  rw [hrun]

end Node

/-! ### The tape layer equals the rounded layer on small inputs -/

section Layer

open IntegerMultBounds.MathlibTM2.LayerMachine (layerRW symArr symZ symZ_eq)
open IntegerMultBounds.MathlibTM2.Node (TopFitsZ TopFits)

variable {r n : ℕ}

lemma l2_toBank_le (R' : ℕ) (f : ZArr (Fin (NW * R') × Fin r) n) :
    l2 (toC (toBank R' f)) ≤ l2 (toC f) := by
  let χ : ((Fin R' × Fin r) × DWire) × (Fin n → ZMod 2) → (Fin (NW * R') × Fin r) × (Fin n → ZMod 2) :=
    fun p => ((⟨NW * p.1.1.1 + wireOf.symm p.1.2, role_lt p.1.1.1.2 (wireOf.symm p.1.2).2⟩,
      p.1.1.2), p.2)
  have hχ : Function.Injective χ := by
    rintro ⟨⟨⟨g, c⟩, v⟩, b⟩ ⟨⟨⟨g', c'⟩, v'⟩, b'⟩ h
    simp only [χ, Prod.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hpos := Nat.pos_of_neZero NW
    have hi := (wireOf.symm v).2
    have hi' := (wireOf.symm v').2
    have hg : (g : ℕ) = g' := by
      have := congrArg (· / NW) h1
      simp only [Nat.mul_add_div hpos, Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hi'] at this
      exact this
    have hv : wireOf.symm v = wireOf.symm v' := by
      have := congrArg (· % NW) h1
      simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at this
      exact Fin.ext this
    rw [Fin.ext hg, h2, h3, wireOf.symm.injective hv]
  have : toC (toBank R' f) = toC f ∘ χ := rfl
  rw [this]
  exact l2_le_of_injective _ χ hχ

/-- One truncation by `2^S` after an array within `E` of `2^S P`: within `√2 √N + E/2^S` of `P`. -/
lemma tdivArr_err {Y : Type} [Fintype Y] (S : ℕ) (X : ZArr Y n) (P : Arr Y n) {E : ℝ}
    (hX : l2 (toC X - (2 : ℂ) ^ S • P) ≤ E) :
    l2 (toC (tdivArr S X) - P) ≤
      √2 * √(Fintype.card (Y × (Fin n → ZMod 2))) + E / 2 ^ S := by
  have hT := l2_tdivArr_sub_le S X
  have hsplit : toC (tdivArr S X) - P =
      (toC (tdivArr S X) - ((2 : ℂ) ^ S)⁻¹ • toC X) + ((2 : ℂ) ^ S)⁻¹ • (toC X - (2 : ℂ) ^ S • P) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]; abel
  rw [hsplit]
  refine (l2_add_le _ _).trans ?_
  rw [l2_smul]
  have hn : ‖((2 : ℂ) ^ S)⁻¹‖ = 1 / 2 ^ S := by
    rw [norm_inv, norm_pow, RCLike.norm_two, one_div]
  rw [hn]
  have hpos : (0 : ℝ) < 2 ^ S := by positivity
  have : 1 / 2 ^ S * l2 (toC X - (2 : ℂ) ^ S • P) ≤ E / 2 ^ S := by
    rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hX hpos.le
  linarith

lemma topFitsZ_of_norm_lt {w : ℕ} {z : GaussianInt} (h : ‖GaussianInt.toComplex z‖ < 2 ^ (w - 1)) :
    TopFitsZ w z := by
  have hre : |(z.re : ℝ)| < 2 ^ (w - 1) := by
    have := Complex.abs_re_le_norm (GaussianInt.toComplex z)
    have e : (GaussianInt.toComplex z).re = z.re := by simp
    rw [e] at this; linarith
  have him : |(z.im : ℝ)| < 2 ^ (w - 1) := by
    have := Complex.abs_im_le_norm (GaussianInt.toComplex z)
    have e : (GaussianInt.toComplex z).im = z.im := by simp
    rw [e] at this; linarith
  rw [abs_lt] at hre him
  have c1 : ((2 : ℤ) ^ (w - 1) : ℝ) = 2 ^ (w - 1) := by push_cast; rfl
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : (-(2 : ℤ) ^ (w - 1) : ℝ) < z.re := by push_cast; linarith
    exact_mod_cast this.le
  · have : (z.re : ℝ) < ((2 : ℤ) ^ (w - 1) : ℤ) := by push_cast; linarith
    exact_mod_cast this
  · have : (-(2 : ℤ) ^ (w - 1) : ℝ) < z.im := by push_cast; linarith
    exact_mod_cast this.le
  · have : (z.im : ℝ) < ((2 : ℤ) ^ (w - 1) : ℤ) := by push_cast; linarith
    exact_mod_cast this

/-- **The tape layer is the rounded layer on small inputs.** With input norms `β j` at level `j`
that cover the children (`lipProd β(i+1) + errL(i+1) ≤ β i`) and child results that fit `w`
signed bits (`2^scaleR i β i + errL i < 2^(w-1)`), the layer modulo `2^w` is `layerR`. -/
theorem layerRW_eq_layerR (w u : ℕ) (ds : Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (R₀ : ℕ) (hw : 1 ≤ w) (β : ℕ → ℝ) :
    ∀ j, (∀ i < j, lipProd (program ds) * β (i + 1) + errL u ds R₀ r n (i + 1) ≤ β i) →
      (∀ i < j, 2 ^ scaleR u ds i * β i + errL u ds R₀ r n i < 2 ^ (w - 1)) →
      ∀ (e : Fin (bits u j) → Fin n), Function.Injective e →
      ∀ f : ZArr (Fin (rowsAt R₀ j) × Fin r) n, l2 (toC f) ≤ β j →
        layerRW w u ds R₀ j e f = layerR u ds R₀ j e f := by
  intro j
  induction j with
  | zero => intro _ _ _ _ _ _; rfl
  | succ j ih =>
    intro hstep hfit e he f hf
    simp only [layerRW, layerR]
    refine congrArg (ofBank (rowsAt R₀ j)) ?_
    have hN : Fintype.card ((Fin (rowsAt R₀ j) × Fin r) × (Fin n → ZMod 2)) =
        rowsAt R₀ j * r * 2 ^ n := by simp
    set δ := √2 * √(rowsAt R₀ j * r * 2 ^ n) + errL u ds R₀ r n j / 2 ^ scaleR u ds j with hδ
    have hδ0 : 0 ≤ δ := add_nonneg (by positivity)
      (div_nonneg (errL_nonneg u ds R₀ r n j) (by positivity))
    have hinj : ∀ s : Fin m, Function.Injective fun c => e (bitIdx s c) :=
      fun s => he.comp fun c c' h => (bitIdx_inj.1 h).2
    refine (nodeM_congr (k := bits u j) e he ds _ _ (δ := δ) (β := β j) hδ0 (fun s g => ?_)
      (fun s g hg => ?_) _ ?_).symm
    · -- the rounded child against the kernels on its slot
      have hX := layerR_err u ds hd R₀ j (fun c => e (bitIdx s c)) (hinj s) g
      have := tdivArr_err (scaleR u ds j) _ _ hX
      rw [hN] at this
      push_cast at this
      exact this
    · -- the children agree on small inputs
      have hIH := ih (fun i hi => hstep i (by omega))
        (fun i hi => hfit i (by omega)) (fun c => e (bitIdx s c)) (hinj s) g hg
      show tdivArr _ (layerR u ds R₀ j _ g) = tdivArr _ (symArr w (layerRW w u ds R₀ j _ g))
      rw [hIH]
      congr 1
      funext q
      refine (symZ_eq hw (topFitsZ_of_norm_lt ?_)).symm
      have h1 := layerR_entry_le u ds hd R₀ j (fun c => e (bitIdx s c)) (hinj s) g q
      have h2 := hfit j (by omega)
      have h3 : 2 ^ scaleR u ds j * l2 (toC g) ≤ 2 ^ scaleR u ds j * β j :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      linarith
    · -- the input bound of the children
      have h1 := l2_toBank_le (rowsAt R₀ j) f
      have h2 := hstep j (by omega)
      have hL := one_le_lipProd (program ds)
      have h3 : lipProd (program ds) * l2 (toC (toBank (rowsAt R₀ j) f)) ≤
          lipProd (program ds) * β (j + 1) :=
        mul_le_mul_of_nonneg_left (h1.trans hf) (by linarith)
      have h4 : errRun δ (program ds) 0 = errL u ds R₀ r n (j + 1) := rfl
      linarith

end Layer

end IntegerMultBounds.MathlibTM2.Layer
