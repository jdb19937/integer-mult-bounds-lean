module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControlProducer
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlRouting
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlExposeRotation
import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerateLayout
import IntegerMultBounds.MathlibTM2.Fast.CRTControlGenerateTraversal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! # A complete nonzero target from unary parameters -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section
variable {T Q K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- Shared external allocation. Slots 0--12 are immutable inputs (except data0);
13--18 are disposable outputs; 19--30 are shared transient scratch. -/
def crtControlTargetParameters : Fin 10 → Fin 31 := ![9, 10, 4, 8, 14, 15, 16, 17, 19, 20]
def crtControlTargetSetup : Fin 5 → Fin 31 := ![3, 4, 5, 6, 19]
def crtControlTargetProducer : Fin 14 → Fin 31 := ![1, 2, 20, 21, 22, 23, 24, 25, 26, 27, 28, 13, 29, 30]
def crtControlTargetRotation : Fin 14 → Fin 31 := ![13, 19, 14, 15, 16, 11, 0, 20, 17, 21, 22, 23, 24, 25]
def crtControlTargetRouting : Fin 10 → Fin 31 := ![19, 7, 18, 26, 4, 5, 12, 20, 21, 22]

theorem crtControlTargetParameters_injective : Function.Injective crtControlTargetParameters := by decide
theorem crtControlTargetSetup_injective : Function.Injective crtControlTargetSetup := by decide
theorem crtControlTargetProducer_injective : Function.Injective crtControlTargetProducer := by decide
theorem crtControlTargetRotation_injective : Function.Injective crtControlTargetRotation := by decide
theorem crtControlTargetRouting_injective : Function.Injective crtControlTargetRouting := by decide

/-- Prepare all target data, expose and rotate, then erase the six produced tapes. -/
def crtControlTarget
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (e : Fin 31 → Fin T) (fwd : Bool) : Pr P T Q (prime + K) U :=
  .seq (crtControlParameters rg (e ∘ crtControlTargetParameters)) <|
  .seq (crtControlProducer rg (e ∘ crtControlTargetSetup) (e ∘ crtControlTargetProducer)) <|
  .seq (crtControlPrefixWidth (e 6) (e 5) (e 18) (e 19)) <|
  .seq (crtControlExposeRotation hQ ι hι hT (e ∘ crtControlTargetRouting) rg
    (e ∘ crtControlTargetRotation) fwd)
    (crtWorkspaceClear [e 13, e 14, e 15, e 16, e 17, e 18])

def crtControlTargetClearBound {d : ℕ} (B : ℕ) (a s : Fin (d + 1) → ℕ) (i : Fin (d + 1)) : ℕ :=
  (crtControlTape (A := prime + K) (3 * B + 1) (crtControlFields a s i.val (crtExposePrefix i))).length +
    (3 * B + 1) + 2 ^ a i + crtPre a (d + 1)

def crtControlTargetCost {d : ℕ} (T B w c : ℕ) (a s : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) (μ : ℕ) : ℕ :=
  crtControlParametersSetupCost (3 * B + 1) w (s i) μ (a i) (crtPre a (d + 1)) +
  crtControlProducerCost (3 * B + 1) w i.val (a i) (a 0) (crtPre a i.val)
    (crtEnts (A := prime + K) (List.ofFn a)).length (crtEnts (A := prime + K) (List.ofFn s)).length
    (List.ofFn a).sum (d + 1) (crtControlProducerAxisBudget (3 * B + 1) w a s) +
  (4 * crtPre a i.val + 4 * a 0 + 8) +
  (crtControlDistantCost T (crtW a (crtControlRoutingPre i)) (crtW a (crtControlRoutingGap i)) (a i) (a 0) c +
    crtControlExposedCost (crtControlFields a s i.val (crtExposePrefix i)).length B w
      (crtW a (crtExposePrefix i)) (a i) (s i) c +
    crtControlDistantCost T (crtW a (crtControlRoutingPre i)) (crtW a (crtControlRoutingGap i)) (a 0) (a i) c) +
  (6 * (2 * crtControlTargetClearBound (K := K) B a s i + 2) + 1)

/-- Erase all six produced tapes after the data operation. -/
theorem crtControlTarget_clear_runs {d B : ℕ} (e : Fin 31 → Fin T) (he : Function.Injective e)
    (a s : Fin (d + 1) → ℕ) (i : Fin (d + 1)) (hi : i ≠ 0) (μ : ℕ)
    (R : Regs T (prime + K)) (output : List (Fin (prime + K + 4)))
    (hempty : ∀ j : Fin 31, 13 ≤ j.val → R (e j) = []) :
    let R₁ := crtControlParametersRegs (e ∘ crtControlTargetParameters)
      (3 * B + 1) (s i) μ (a i) (crtPre a (d + 1)) R
    let R₂ := Function.update R₁ (e 13)
      (crtControlTape (3 * B + 1) (crtControlFields a s i.val (crtExposePrefix i)))
    let R₃ := Function.update R₂ (e 18) (List.replicate (crtW a (crtControlRoutingGap i)) tick)
    crtRuns body (crtWorkspaceClear [e 13, e 14, e 15, e 16, e 17, e 18])
      (Function.update R₃ (e 0) output) (Function.update R (e 0) output)
      (6 * (2 * crtControlTargetClearBound (K := K) B a s i + 2) + 1) := by
  let W := 3 * B + 1
  let p := e ∘ crtControlTargetParameters
  let tape := crtControlTape (A := prime + K) W (crtControlFields a s i.val (crtExposePrefix i))
  let R₁ := crtControlParametersRegs p W (s i) μ (a i) (crtPre a (d + 1)) R
  let R₂ := Function.update R₁ (e 13) tape
  let R₃ := Function.update R₂ (e 18) (List.replicate (crtW a (crtControlRoutingGap i)) tick)
  let R₄ := Function.update R₃ (e 0) output
  let M := crtControlTargetClearBound (K := K) B a s i
  have hpow : 0 < (2 : ℕ) ^ a i := by positivity
  have hclear := crtWorkspaceClear_runs (body := body) M [e 13, e 14, e 15, e 16, e 17, e 18] R₄ (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [R₄, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff]
    all_goals dsimp [M, crtControlTargetClearBound, tape, W]
    all_goals simp only [crtControlTape_length]
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [crtControlRoutingGap_width a i hi]
      have hpre := crtPre_mono a i.isLt.le
      omega)
  have hfinal : (fun k => if k ∈ [e 13, e 14, e 15, e 16, e 17, e 18] then [] else R₄ k) =
      Function.update R (e 0) output := by
    funext k
    by_cases hk : ∃ j, e j = k
    · obtain ⟨j, rfl⟩ := hk
      by_cases hj : j = 0
      · subst j; simp [R₄, he.eq_iff]
      · by_cases hclean : j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18
        · rcases hclean with rfl | rfl | rfl | rfl | rfl | rfl
          all_goals simp [he.eq_iff, hempty]
        · simp only [List.mem_cons, List.not_mem_nil, or_false, he.eq_iff]
          rw [ite_eq_right hclean]
          simp only [R₄, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, Function.comp_apply]
          simp only [Function.update_apply, he.eq_iff]
          split_ifs <;> simp_all
    · have hk' : ∀ j, k ≠ e j := by intro j h; exact hk ⟨j, h.symm⟩
      simp [R₄, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, hk']
  simpa only [List.length_cons, List.length_nil] using crtRuns_congr hclear hfinal

/-- Full target contract: no descriptors, binary constants, padding or gap are
assumed prebuilt. All temporary tapes are released and only data changes. -/
theorem crtControlTarget_runs
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (rg : TblR 10 → Fin T) (hrg : Function.Injective rg)
    (e : Fin 31 → Fin T) (he : Function.Injective e)
    (hrge : ∀ r j, rg r ≠ e j) (hιe : ∀ j k, ι j ≠ e k)
    {d B w : ℕ} (a s : Fin (d + 1) → ℕ) (i : Fin (d + 1)) (hi : i ≠ 0)
    (hwidth : a i ≤ a 0 + 1 ∧ a 0 ≤ a i + 1)
    (hs : ∀ j, s j ≤ 2 ^ a j) (hsi : 0 < s i) (μ : ℕ) (hμ : μ ≤ s i) (fwd : Bool)
    (hB : (∑ j, a j) ≤ B) (hd : d + 1 ≤ B) (c : ℕ) (hc : 0 < c)
    (wl nl : List (Fin (prime + K + 4))) (hwl : wl.length = 3 * B + 1)
    (hnl : nl.length = w) (hw : w ≤ 3 * B + 1)
    (C : (Fin (d + 1) → ℕ) → List (Fin (prime + K + 4)))
    (hC : ∀ x, (C x).length = c) (h8 : ∀ x, ∀ z ∈ C x, z.val < 8)
    (R : Regs T (prime + K))
    (hsource : R (e 0) = (crtBox a (crtRevAx (d := d + 1) (d + 1)) C 0).flatten)
    (hwidths : R (e 1) = crtEnts (List.ofFn a)) (hmoduli : R (e 2) = crtEnts (List.ofFn s))
    (hindex : (R (e 3)).length = i.val) (hai : (R (e 4)).length = a i)
    (ha0 : (R (e 5)).length = a 0) (hlower : (R (e 6)).length = crtPre a i.val)
    (hupper : (R (e 7)).length = crtW a (crtControlRoutingPre i))
    (htotal : (R (e 8)).length = crtPre a (d + 1))
    (hmod : (R (e 9)).length = s i) (hmul : (R (e 10)).length = μ)
    (hslot : (R (e 11)).length = c)
    (hthree : R (e 12) = (GrowingCounterData.advance (3 * c) []).map bitSymbol)
    (hempty : ∀ j : Fin 31, 13 ≤ j.val → R (e j) = [])
    (hwr : R (rg .wr) = wl) (hwn : R (rg .wn) = nl)
    (hvars : ∀ j, R (rg (.v j)) = []) (hz : ∀ j, R (rg (.z j)) = [])
    (hacc : R (rg .acc) = []) (hι0 : ∀ j, R (ι j) = []) :
    crtRuns body (crtControlTarget hQ ι hι hT rg e fwd) R
      (Function.update R (e 0)
        (crtBox a (crtRevAx (d := d + 1) (d + 1)) (crtRotC s i.val i.isLt μ fwd C) 0).flatten)
      (crtControlTargetCost (K := K) T B w c a s i μ) := by
  let W := 3 * B + 1
  let p := e ∘ crtControlTargetParameters
  let u := e ∘ crtControlTargetSetup
  let v := e ∘ crtControlTargetProducer
  let r := e ∘ crtControlTargetRotation
  let g := e ∘ crtControlTargetRouting
  let tape := crtControlTape (A := prime + K) W (crtControlFields a s i.val (crtExposePrefix i))
  let R₁ := crtControlParametersRegs p W (s i) μ (a i) (crtPre a (d + 1)) R
  let R₂ := Function.update R₁ (e 13) tape
  let R₃ := Function.update R₂ (e 18) (List.replicate (crtW a (crtControlRoutingGap i)) tick)
  let output := (crtBox a (crtRevAx (d := d + 1) (d + 1)) (crtRotC s i.val i.isLt μ fwd C) 0).flatten
  let R₄ := Function.update R₃ (e 0) output
  have hp : Function.Injective p := he.comp crtControlTargetParameters_injective
  have hu : Function.Injective u := he.comp crtControlTargetSetup_injective
  have hv : Function.Injective v := he.comp crtControlTargetProducer_injective
  have hr : Function.Injective r := he.comp crtControlTargetRotation_injective
  have hg : Function.Injective g := he.comp crtControlTargetRouting_injective
  have haiB : a i ≤ B := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hB
  have hSB : s i < 2 ^ W := (hs i).trans_lt (Nat.pow_lt_pow_right (by decide) (by dsimp [W]; omega))
  have hμB : μ < 2 ^ W := hμ.trans_lt hSB
  have hprefix : crtW a (crtExposePrefix i) = crtPre a (d + 1) - a i := by
    have h := crtControlGeneratedAxes_width a i (d + 1) le_rfl
    rw [crtControlGeneratedAxes_full] at h
    simpa only [ite_eq_right (show ¬d + 1 ≤ i.val by omega)] using h
  have hpreB : crtW a (crtExposePrefix i) ≤ B := by
    rw [hprefix]
    exact (Nat.sub_le _ _).trans ((crtControl_pre_le_sum a (d + 1)).trans hB)
  have hparameters := crtControlParameters_runs (body := body) hrg p hp (fun x j => hrge x _)
    (show 0 < W by dsimp [W]; omega) hSB hμB wl nl hwl hnl hw R hwr hwn hvars hz
    (by simpa [p, crtControlTargetParameters] using hmod)
    (by simpa [p, crtControlTargetParameters] using hmul)
    (by simpa [p, crtControlTargetParameters] using hai)
    (by simpa [p, crtControlTargetParameters] using htotal)
    (by intro j hj; fin_cases j <;> simp [p, crtControlTargetParameters, hempty] at hj ⊢)
  have hR₁bank : ∀ k, R₁ (rg k) = R (rg k) := by
    intro k; simp [R₁, crtControlParametersRegs, p, crtControlTargetParameters, hrge]
  have hproducer := crtControlProducer_runs (body := body) hrg u hu v hv
    (fun x j => hrge x _) (fun x j => hrge x _)
    (by intro j k; apply he.ne; fin_cases j <;> fin_cases k <;> decide)
    a s i hs hB hd wl nl hwl hnl hw R₁
    (by rw [hR₁bank]; exact hwr) (by rw [hR₁bank]; exact hwn)
    (by intro j; rw [hR₁bank]; exact hvars j) (by intro j; rw [hR₁bank]; exact hz j)
    (by simpa [R₁, crtControlParametersRegs, p, u, crtControlTargetParameters, crtControlTargetSetup, he.eq_iff] using hindex)
    (by simpa [R₁, crtControlParametersRegs, p, u, crtControlTargetParameters, crtControlTargetSetup, he.eq_iff] using hai)
    (by simpa [R₁, crtControlParametersRegs, p, u, crtControlTargetParameters, crtControlTargetSetup, he.eq_iff] using ha0)
    (by simpa [R₁, crtControlParametersRegs, p, u, crtControlTargetParameters, crtControlTargetSetup, he.eq_iff] using hlower)
    (by simp [R₁, crtControlParametersRegs, p, u, crtControlTargetParameters, crtControlTargetSetup, he.eq_iff, hempty])
    (by simpa [R₁, crtControlParametersRegs, p, v, crtControlTargetParameters, crtControlTargetProducer, he.eq_iff] using hwidths)
    (by simpa [R₁, crtControlParametersRegs, p, v, crtControlTargetParameters, crtControlTargetProducer, he.eq_iff] using hmoduli)
    (by intro j h0 h1 h11; fin_cases j <;> simp [R₁, crtControlParametersRegs, p, v,
      crtControlTargetParameters, crtControlTargetProducer, he.eq_iff, hempty] at h0 h1 h11 ⊢)
  have hproducer' : crtRuns body (crtControlProducer rg u v) R₁ R₂
      (crtControlProducerCost W w i.val (a i) (a 0) (crtPre a i.val)
        (crtEnts (A := prime + K) (List.ofFn a)).length (crtEnts (A := prime + K) (List.ofFn s)).length
        (List.ofFn a).sum (d + 1) (crtControlProducerAxisBudget W w a s)) := by
    simpa [v, crtControlTargetProducer, R₂, R₁, crtControlParametersRegs, p,
      crtControlTargetParameters, he.eq_iff, hempty, tape, W] using hproducer
  have hgap := crtControlRoutingGap_runs (body := body) (lower := e 6) (zeroWidth := e 5)
    (gap := e 18) (tmp := e 19) (by simp [List.nodup_cons, he.eq_iff]) a i hi R₂
    (by simpa [R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff] using hlower)
    (by simpa [R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff] using ha0)
    (by simp [R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, hempty])
    (by simp [R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, hempty])
  have hR₃bank : ∀ k, R₃ (rg k) = R (rg k) := by
    intro k; simp [R₃, R₂, hrge, hR₁bank]
  have hrotation := crtControlExposeRotation_runs (body := body) hQ ι hι hT g hg rg hrg r hr
    (fun x j => hrge x _)
    (by intro j; apply he.ne; fin_cases j <;> decide)
    (fun j => hιe j 0) (fun j k => hιe j _)
    a s i hi (crtControlRoutingPre i) (crtControlRoutingGap i) (crtControlRouting_split i hi)
    hwidth hs hsi μ hμ fwd B c w hc hB hpreB wl nl hwl hnl hw C hC h8 R₃
    (by simpa [r, crtControlTargetRotation, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff] using hsource)
    (by simpa [g, crtControlTargetRouting, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff] using hupper)
    (by simp [g, crtControlTargetRouting, R₃])
    (by simp [g, crtControlTargetRouting, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, hempty])
    (by simpa [g, crtControlTargetRouting, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff] using hai)
    (by simpa [g, crtControlTargetRouting, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff] using ha0)
    (by simpa [g, crtControlTargetRouting, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff] using hthree)
    (by simp [g, crtControlTargetRouting, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, hempty])
    (by simp [g, crtControlTargetRouting, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, hempty])
    (by simp [g, crtControlTargetRouting, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, hempty])
    (by simp [g, crtControlTargetRouting, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, hempty])
    (by intro j; simp [R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, hιe, hι0])
    (by simp [r, crtControlTargetRotation, R₃, R₂, he.eq_iff, tape, W])
    (by simp [r, crtControlTargetRotation, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, hempty])
    (by simp [r, crtControlTargetRotation, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, W])
    (by simp [r, crtControlTargetRotation, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, W])
    (by simp [r, crtControlTargetRotation, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff])
    (by simpa [r, crtControlTargetRotation, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff] using hslot)
    (by simp [r, crtControlTargetRotation, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, hprefix])
    (by intro j hj; fin_cases j <;> simp [r, crtControlTargetRotation, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, hempty] at hj ⊢)
    (by simp [r, crtControlTargetRotation, R₃, R₂, R₁, crtControlParametersRegs, p, crtControlTargetParameters, he.eq_iff, hempty])
    (by rw [hR₃bank]; exact hwr) (by rw [hR₃bank]; exact hwn)
    (by intro j; rw [hR₃bank]; exact hvars j) (by intro j; rw [hR₃bank]; exact hz j)
    (by rw [hR₃bank]; exact hacc)
  have hclear := crtControlTarget_clear_runs (body := body) (B := B) e he a s i hi μ R output hempty
  apply crtRuns_mono (crtRuns_seq hparameters (crtRuns_seq hproducer' (crtRuns_seq hgap
    (crtRuns_seq hrotation hclear))))
  simp only [crtControlTargetCost, W]
  omega

end
end IntegerMultBounds.MathlibTM2.Fast
