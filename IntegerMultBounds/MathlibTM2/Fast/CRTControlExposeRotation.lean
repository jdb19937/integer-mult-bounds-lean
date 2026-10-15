module

public import IntegerMultBounds.MathlibTM2.Fast.CRTLinear
public import IntegerMultBounds.MathlibTM2.Fast.CRTControlRotation

/-! # Expose, directly rotate, and restore one nonzero CRT target

The distant-routing and arithmetic banks need no common register allocation:
each checked stage modifies only the shared data source. Routing parameters,
descriptor tape, arithmetic widths and all scratch are therefore preserved
through the complete round trip. Target-specific parameters are prepared inputs.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable section

variable {T Q K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- Header preparation, one distant exchange, and header cleanup. -/
def crtControlDistantCost (T u g h w c : ℕ) : ℕ :=
  (T + 12 * swapT 6 + 5) * crtSwapCostN (3 * (2 ^ (u + (h + (g + w))) * c)) h w +
    (6 * swapT 6 + 10) * (u + g + 3 * c + h + w + 2) +
    34 * (2 ^ (u + (h + (g + w))) * c) + 2 * T + 6 * swapT 6 +
    4 * u + 4 * g + 18 * c + h * (4 * h + 11) + w * (4 * w + 11) + 88

/-- Arithmetic workspace initialization, exposed rotation, and restoration. -/
def crtControlExposedCost (D B w L ai S c : ℕ) : ℕ :=
  (10 * (4 * (3 * B + 1) + 4) + 1 + 10 * tblC (3 * B + 1) w) +
    crtControlAllCost D (3 * B + 1) w L S (2 ^ ai) c +
    (10 * (2 * (3 * B + 1) + 2) + 1)

/-- Routing register map: swap scratch, outer width, gap width, zero post width,
target width, zero-axis width, encoded three-record width, and three scratch
registers. Unexposure exchanges the two axis-width roles. -/
def crtControlExposeRotation
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (g : Fin 10 → Fin T) (rg : TblR 10 → Fin T) (e : Fin 14 → Fin T) (fwd : Bool) :
    Pr P T Q (prime + K) U :=
  .seq (crtGapSwapStep hQ ι hι hT (e 6) (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6)
    (g 7) (g 8) (g 9))
    (.seq (.seq (crtControlWorkspaceInit rg)
      (.seq (crtControlAllFibers rg e fwd) (crtControlWorkspaceClear rg)))
      (crtGapSwapStep hQ ι hι hT (e 6) (g 0) (g 1) (g 2) (g 3) (g 5) (g 4) (g 6)
        (g 7) (g 8) (g 9)))

/-- A complete nonzero triangular target step on the fixed full reverse
layout. No stage's machine execution is assumed; all three are composed from
checked host contracts and the sole modified register is the data source. -/
theorem crtControlExposeRotation_runs
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q)
    (ι : Fin (swapT 6) → Fin T) (hι : Function.Injective ι) (hT : swapT 6 ≤ T)
    (g : Fin 10 → Fin T) (hg : Function.Injective g)
    (rg : TblR 10 → Fin T) (hrg : Function.Injective rg)
    (e : Fin 14 → Fin T) (he : Function.Injective e) (hrge : ∀ r j, rg r ≠ e j)
    (hgsrc : ∀ j, g j ≠ e 6) (hιsrc : ∀ j, ι j ≠ e 6) (hιg : ∀ j k, ι j ≠ g k)
    {d : ℕ} (a s : Fin (d + 1) → ℕ) (i : Fin (d + 1)) (hi : i ≠ 0)
    (pre gap : List (Fin (d + 1))) (hsplit : crtOuterAxes d = pre ++ i :: gap)
    (hwidth : a i ≤ a 0 + 1 ∧ a 0 ≤ a i + 1)
    (hs : ∀ j, s j ≤ 2 ^ a j) (hsi : 0 < s i) (μ : ℕ) (hμ : μ ≤ s i) (fwd : Bool)
    (B c w : ℕ) (hc : 0 < c) (hB : (∑ j, a j) ≤ B)
    (hpre : crtW a (crtExposePrefix i) ≤ B)
    (wl nl : List (Fin (prime + K + 4))) (hwl : wl.length = 3 * B + 1)
    (hnl : nl.length = w) (hw : w ≤ 3 * B + 1)
    (C : (Fin (d + 1) → ℕ) → List (Fin (prime + K + 4)))
    (hC : ∀ x, (C x).length = c) (h8 : ∀ x, ∀ z ∈ C x, z.val < 8)
    (R : Regs T (prime + K))
    (hsource : R (e 6) = (crtBox a (crtRevAx (d := d + 1) (d + 1)) C 0).flatten)
    (hu : (R (g 1)).length = crtW a pre) (hgap : (R (g 2)).length = crtW a gap)
    (hv : (R (g 3)).length = 0) (haj : (R (g 4)).length = a i) (hak : (R (g 5)).length = a 0)
    (he3 : R (g 6) = (GrowingCounterData.advance (3 * c) []).map bitSymbol)
    (hstmp : R (g 0) = []) (htu : R (g 7) = []) (ht1 : R (g 8) = []) (ht2 : R (g 9) = [])
    (hι0 : ∀ j, R (ι j) = [])
    (htape : R (e 0) = crtControlTape (3 * B + 1) (crtControlFields a s i.val (crtExposePrefix i)))
    (hsave : R (e 1) = [])
    (hmod : R (e 2) = binSyms (3 * B + 1) (s i)) (hmul : R (e 3) = binSyms (3 * B + 1) μ)
    (hpadding : (R (e 4)).length = 2 ^ a i - s i) (hslot : (R (e 5)).length = c)
    (hexponent : (R (e 8)).length = crtW a (crtExposePrefix i))
    (hclean : ∀ j : Fin 14, 9 ≤ j.val → R (e j) = []) (hacc : R (e 7) = [])
    (hwr : R (rg .wr) = wl) (hwn : R (rg .wn) = nl)
    (hvars : ∀ j, R (rg (.v j)) = []) (hz : ∀ j, R (rg (.z j)) = [])
    (hbankacc : R (rg .acc) = []) :
    crtRuns body (crtControlExposeRotation hQ ι hι hT g rg e fwd) R
      (Function.update R (e 6)
        (crtBox a (crtRevAx (d := d + 1) (d + 1)) (crtRotC s i.val i.isLt μ fwd C) 0).flatten)
      (crtControlDistantCost T (crtW a pre) (crtW a gap) (a i) (a 0) c +
        crtControlExposedCost (crtControlFields a s i.val (crtExposePrefix i)).length
          B w (crtW a (crtExposePrefix i)) (a i) (s i) c +
        crtControlDistantCost T (crtW a pre) (crtW a gap) (a 0) (a i) c) := by
  have hreg : [e 6, g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9].Nodup := by
    simp [List.nodup_cons, hg.eq_iff, hgsrc, Ne.symm]
  have hbank : ∀ r ∈ [e 6, g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7, g 8, g 9],
      ∀ j, ι j ≠ r := by
    intro r hr j
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hιsrc j
    all_goals exact hιg _ _
  have hexpose := crtExposeStep_runs (body := body) a hQ ι hι hT hreg hbank i hi pre gap hsplit
    hwidth.1 hwidth.2 C c hc hC h8 0 R hsource hu hgap hv haj hak he3 hstmp htu ht1 ht2 hι0
  let R₁ := Function.update R (e 6) (crtBox a (crtExposePrefix i ++ [i]) C 0).flatten
  have hR₁e : ∀ j : Fin 14, j ≠ 6 → R₁ (e j) = R (e j) := by
    intro j hj; exact Function.update_of_ne (fun h => hj (he h)) _ _
  have hR₁r : ∀ r, R₁ (rg r) = R (rg r) := fun r => Function.update_of_ne (hrge r 6) _ _
  have hrotation := crtControlRotationWorkspace_runs (body := body) hrg e he hrge a s
    (crtExposePrefix i) i [] (crtExpose_nodup i) (crtExposePrefix_controls i) hs hsi μ hμ fwd
    B c w hB hpre wl nl hwl hnl hw C hC R₁
    (by rw [hR₁e 0 (by decide)]; exact htape)
    (by rw [hR₁e 1 (by decide)]; exact hsave)
    (by rw [hR₁e 2 (by decide)]; exact hmod)
    (by rw [hR₁e 3 (by decide)]; exact hmul)
    (by rw [hR₁e 4 (by decide)]; exact hpadding)
    (by rw [hR₁e 5 (by decide)]; simpa using hslot)
    (by rw [hR₁e 8 (by decide)]; exact hexponent)
    (by intro j hj; rw [hR₁e j (by intro h; subst j; contradiction)]; exact hclean j hj)
    (by simp [R₁]) (by rw [hR₁e 7 (by decide)]; exact hacc)
    (by rw [hR₁r]; exact hwr) (by rw [hR₁r]; exact hwn)
    (by intro j; rw [hR₁r]; exact hvars j) (by intro j; rw [hR₁r]; exact hz j)
    (by rw [hR₁r]; exact hbankacc)
  let C' := crtRotC s i.val i.isLt μ fwd C
  let R₂ := Function.update R (e 6) (crtBox a (crtExposePrefix i ++ [i]) C' 0).flatten
  have hrotout : Function.update R₁ (e 6)
      (crtBox a (crtExposePrefix i ++ i :: []) C' 0).flatten = R₂ := by
    simp [R₁, R₂]
  have hR₂g : ∀ j, R₂ (g j) = R (g j) := fun j => Function.update_of_ne (hgsrc j) _ _
  have hC' : ∀ x, (C' x).length = c := by
    intro x; unfold C' crtRotC; split_ifs <;> exact hC _
  have h8' : ∀ x, ∀ z ∈ C' x, z.val < 8 := by
    intro x z hz'; unfold C' crtRotC at hz'; split_ifs at hz' <;> exact h8 _ z hz'
  have hreg' : [e 6, g 0, g 1, g 2, g 3, g 5, g 4, g 6, g 7, g 8, g 9].Nodup := by
    simp [List.nodup_cons, hg.eq_iff, hgsrc, Ne.symm]
  have hbank' : ∀ r ∈ [e 6, g 0, g 1, g 2, g 3, g 5, g 4, g 6, g 7, g 8, g 9],
      ∀ j, ι j ≠ r := by
    intro r hr j
    apply hbank r ?_ j
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_left_comm, or_assoc, or_comm] using hr
  have hunexpose := crtUnexposeStep_runs (body := body) a hQ ι hι hT hreg' hbank' i hi pre gap hsplit
    hwidth.2 hwidth.1 C' c hc hC' h8' 0 R₂ (by simp [R₂])
    (by rw [hR₂g]; exact hu) (by rw [hR₂g]; exact hgap) (by rw [hR₂g]; exact hv)
    (by rw [hR₂g]; exact hak) (by rw [hR₂g]; exact haj) (by rw [hR₂g]; exact he3)
    (by rw [hR₂g]; exact hstmp) (by rw [hR₂g]; exact htu)
    (by rw [hR₂g]; exact ht1) (by rw [hR₂g]; exact ht2)
    (by intro j; simpa only [R₂, Function.update_of_ne (hιsrc j)] using hι0 j)
  have hrun := crtRuns_seq hexpose (crtRuns_seq (crtRuns_congr hrotation hrotout) hunexpose)
  apply crtRuns_mono (crtRuns_congr hrun (by simp [R₂, C']))
  simp only [crtControlDistantCost, crtControlExposedCost, crtW_append, crtW_cons,
    crtW_nil, Nat.add_zero, pow_zero, Nat.one_mul]
  omega

end
end IntegerMultBounds.MathlibTM2.Fast
