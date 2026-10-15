module

public import IntegerMultBounds.MathlibTM2.Fast.MainProg
public import IntegerMultBounds.MathlibTM2.Fast.SynFrame

/-!
# The synthetic transforms of the fast multiplier from the layer machine

The host program `mnFast` (`Fast/MainProg`) takes its transforms as a bundle `MnSyn`: programs
meeting `SynFwdSpec`/`SynOppSpec` on `src (.v .io)` under the precondition `mnSynPre σ`. This file
builds that bundle from the layer machine.

**The layer procedures.** `mnLb f` is `layerTable mnQ_layer Cost.brDirs f` (`Node/LayerProc`)
embedded along `mnLayE` (`Fast/MainRegs`) with calls renamed through `MnProc.lay`
(`Host/Embed`). The layer file's `lreg .io` is `src (.v .io)`, every other layer register is in
the reserved block `mnLay`.

**The transforms.** `embProg mnLayE MnProc.lay (synFwd Cost.brDirs layP)` and
`embProg mnLayE MnProc.lay (synOpp Cost.brDirs layQ)` for layout programs `layP`, `layQ` of the
layer machine; `embSynFwd_spec`, `embSynOpp_spec` (`Fast/SynFrame`) give their contracts under
`embPre mnLayE Pk v₀`, which `mnSynPre (mnσ P₀ v₀)` implies when `Pk P₀`
(`mn_synPre_embPre`): the reserved block holds the parameter wires `v₀` of the transforms and
the parking contents `P₀`, everything else of the layer file empty (`mnσ`).

**The remaining hypotheses** (`MnLay w`): the layout programs `layP`, `layQ`, parking predicates
`Pk n` with contents `P₀ n`, parameter wires `v₀ n` with `SynV`, the layout contracts `layF`,
`layO` of `Fast/SynFwd` in the form of `Fast/SynFrame`, and the cost bound
`cL + synLoopFCost + synLoopOCost + cL' = O(totConv)`. The parameter conditions `LayHyp`
(`mn_layHyp`), `nRounds ≤ ℓ + 1` and the bound `synPi < cvM` (`mn_synPi_lt`) are discharged from
`Sizes`.

`mnSynOfLay L hw : MnSyn mnKa mnLb w (mnσL L)` is the bundle, at the alphabet
`prime + mnKa`, `mnKa = embKa` (`Fast/SynFrame`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.Networks
  IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter

noncomputable section

/-! ### The alphabet and the layer procedures -/

/-- The alphabet offset: `embKa` of `Fast/SynFrame`. -/
def mnKa : ℕ := embKa

lemma mnKa_le : embKa ≤ mnKa := le_rfl

lemma mnKa_alpha : 96 ≤ prime + mnKa := by
  have : 9 ^ 4 ≤ embKa := (le_max_left _ _).trans (le_max_left _ _)
  unfold mnKa; omega

/-- The layer procedures of the host: `layerTable mnQ_layer Cost.brDirs f` embedded along
`mnLayE`, calls renamed through `MnProc.lay`. -/
def mnLb (f : LProc) : MnPr (prime + mnKa) :=
  embProg mnLayE MnProc.lay (layerTable (Ka := mnKa) (U := Unit) mnQ_layer Cost.brDirs f)

lemma mn_body_lay (mainP : MnPr (prime + mnKa)) (f : LProc) :
    mnBody mnLb mainP (MnProc.lay f) =
      embProg mnLayE MnProc.lay (layerTable (Ka := mnKa) (U := Unit) mnQ_layer Cost.brDirs f) :=
  rfl

/-- The forward transform of the host for a layout program `layP`. -/
def mnFwdP (layP : Pr LProc (nT SXReg) mnQ (prime + mnKa) Unit) : MnPr (prime + mnKa) :=
  embProg mnLayE MnProc.lay (synFwd Cost.brDirs layP)

/-- The opposite transform of the host for a layout program `layQ`. -/
def mnOppP (layQ : Pr LProc (nT SXReg) mnQ (prime + mnKa) Unit) : MnPr (prime + mnKa) :=
  embProg mnLayE MnProc.lay (synOpp Cost.brDirs layQ)

/-! ### The transforms' parameter registers -/

/-- The contents of the reserved block: the file `synG (synIdle [] P₀) v₀` of the layer machine
(parking `P₀`, wires `v₀`, everything else empty) read on the register names. -/
def mnσ (P₀ : List (Fin (prime + mnKa + 4))) (v₀ : SynW → List (Fin (prime + mnKa + 4)))
    (x : LReg SXReg) : List (Fin (prime + mnKa + 4)) :=
  synG (synIdle [] P₀) v₀ (reg (BReg := SXReg) x)

section Sigma

variable (P₀ : List (Fin (prime + mnKa + 4))) (v₀ : SynW → List (Fin (prime + mnKa + 4)))

/-- The wire of a transform register holds `v₀`. -/
lemma mnσ_wire (x : SynW) : mnσ P₀ v₀ (.wire (synWire x)) = v₀ x := synG_sreg x

/-- A register that is not a wire is as in the idle file. -/
lemma mnσ_of_not_wire {y : LReg SXReg} (hy : ∀ v, y ≠ .wire v) :
    mnσ P₀ v₀ y = synIdle [] P₀ (reg (BReg := SXReg) y) :=
  synG_of_ne (lreg_out hy)

/-- The parking register holds `P₀`. -/
lemma mnσ_park : mnσ P₀ v₀ .park = P₀ := by
  rw [mnσ_of_not_wire _ _ (by simp)]
  simp [synIdle]

/-- The (unused) copy of `lreg .io` is empty. -/
lemma mnσ_io : mnσ P₀ v₀ .io = [] := by
  rw [mnσ_of_not_wire _ _ (by simp)]
  simp [synIdle]

/-- Every other register is empty. -/
lemma mnσ_eq_nil {y : LReg SXReg} (hy : ∀ v, y ≠ .wire v) (hp : y ≠ .park) :
    mnσ P₀ v₀ y = [] := by
  rw [mnσ_of_not_wire _ _ hy]
  simp [synIdle, hp]

end Sigma

/-- `mnSynPre (mnσ P₀ v₀)` implies the embedded precondition `embPre mnLayE Pk v₀` when
`Pk P₀`. -/
lemma mn_synPre_embPre (Pk : List (Fin (prime + mnKa + 4)) → Prop)
    {P₀ : List (Fin (prime + mnKa + 4))} (hPk : Pk P₀)
    (v₀ : SynW → List (Fin (prime + mnKa + 4))) (S : Stacks mnT (prime + mnKa))
    (h : mnSynPre (mnσ P₀ v₀) S) : embPre mnLayE Pk v₀ S := by
  obtain ⟨hL, -, hR⟩ := h
  refine ⟨fun y => by rw [embStk_L]; exact hL _, P₀, hPk, fun k hk => ?_⟩
  rw [embStk_R, mnLayE_of_ne hk, hR]
  simp only [mnσ, IntegerMultBounds.MathlibTM2.LayerMachine.reg, Equiv.apply_symm_apply]

/-! ### The parameter conditions from `Sizes` -/

/-- `LayHyp` of the synthetic transforms at `n`: every axis has `ℓ - 1` or `ℓ` bits and
`1 ≤ K ≤ ℓ - 1`. -/
theorem mn_layHyp {n : ℕ} (hbig : Big n) : LayHyp (List.ofFn (cvAx (t n))) (ℓ n) (K n) := by
  refine ⟨fun e he => ?_, one_le_iroot cExp_ne hbig.one_le_d, ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    show Nat.log 2 (t n _) = _ ∨ Nat.log 2 (t n _) = _
    unfold t
    split_ifs <;> simp [Nat.log_pow]
  · have := hbig.K_succ_le_ℓ; omega

/-- The layout order stays below `cvM`. -/
theorem mn_synPi_lt (n m : ℕ) :
    synPi (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (K n)) m < cvM (cvAx (t n)) :=
  synPi_lt _ m

/-- `SynFwdSpec` is monotone in the precondition. -/
lemma mn_synFwd_mono {T Q A : ℕ} {U P : Type} {d : ℕ} {body : P → Pr P T Q A U}
    {fwdP : Pr P T Q A U} {io : Fin T} {Pre Pre' : Stacks T A → Prop} {w p l : ℕ}
    {a : Fin d → ℕ} {π : ℕ → ℕ} {cF : ℕ} (hP : ∀ S, Pre' S → Pre S)
    (h : SynFwdSpec body fwdP io Pre w p l a π cF) : SynFwdSpec body fwdP io Pre' w p l a π cF :=
  fun Z v S hS => h Z v S (hP S hS)

/-- `SynOppSpec` is monotone in the precondition. -/
lemma mn_synOpp_mono {T Q A : ℕ} {U P : Type} {d : ℕ} {body : P → Pr P T Q A U}
    {oppP : Pr P T Q A U} {io : Fin T} {Pre Pre' : Stacks T A → Prop} {w p l : ℕ}
    {a : Fin d → ℕ} {π : ℕ → ℕ} {cO : ℕ} (hP : ∀ S, Pre' S → Pre S)
    (h : SynOppSpec body oppP io Pre w p l a π cO) : SynOppSpec body oppP io Pre' w p l a π cO :=
  fun V v S hS => h V v S (hP S hS)

/-! ### The remaining hypotheses -/

/-- The step bound of the forward transform at `n`, coefficient width `w`, layout bound `cL`,
wires `v₀`. -/
def mnCF (n w cL : ℕ) (v₀ : SynW → List (Fin (prime + mnKa + 4))) : ℕ :=
  cL + synLoopFCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) w (ℓ n)
    (nRounds (cvAx (t n))) (synStashCostW v₀ synXS + 6 * nRounds (cvAx (t n)) + 6)

/-- The step bound of the opposite transform at `n`, coefficient width `w`, layout bound `cL'`,
wires `v₀`. -/
def mnCO (n w cL' : ℕ) (v₀ : SynW → List (Fin (prime + mnKa + 4))) : ℕ :=
  synLoopOCost Cost.brDirs (List.ofFn (cvAx (t n))) (ℓ n) (K n) w (ℓ n)
    (nRounds (cvAx (t n))) (synStashCostW v₀ synXS + 6 * nRounds (cvAx (t n)) + 6) + cL'

/-- **The layout hypotheses**: the layout programs `layP`, `layQ` of the layer machine, their
parking predicates `Pk n` with contents `P₀ n`, the parameter wires `v₀ n` (`SynV` at the axes
`cvAx (t n)`, `ℓ n`, `K n`, width `w n`), the layout contracts `layF`, `layO` within `cL n`,
`cL' n` steps, and the cost bound `cF + cO = O(totConv)`. -/
structure MnLay (w : ℕ → ℕ) where
  layP : Pr LProc (nT SXReg) mnQ (prime + mnKa) Unit
  layQ : Pr LProc (nT SXReg) mnQ (prime + mnKa) Unit
  Pk : ℕ → List (Fin (prime + mnKa + 4)) → Prop
  P₀ : ℕ → List (Fin (prime + mnKa + 4))
  v₀ : ℕ → SynW → List (Fin (prime + mnKa + 4))
  cL : ℕ → ℕ
  cL' : ℕ → ℕ
  pk : ∀ᶠ n in atTop, Pk n (P₀ n)
  wires : ∀ᶠ n in atTop,
    SynV (v₀ n) (List.ofFn (cvAx (t n))) (ℓ n) (K n) (w n) (ℓ n) 0
        (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (K n)) ∧
      v₀ n (.p .h) = [] ∧ v₀ n (.p .t) = [] ∧ (v₀ n (.p .c)).length = nRounds (cvAx (t n)) ∧
      blank ∉ v₀ n (.p .c)
  layF : ∀ᶠ n in atTop, ∀ (P₀ : List (Fin (prime + mnKa + 4))), Pk n P₀ →
    ∀ (Z : ℕ → Fin (2 ^ ℓ n) → GaussianInt),
      LayRuns (layerTable (Ka := mnKa) (U := Unit) mnQ_layer Cost.brDirs) layP
        (synG (synIdle (cstream (prime + mnKa) (w n) (rpStream (cvM (cvAx (t n))) Z)) P₀) (v₀ n))
        (synG (synIdle (cstream (prime + mnKa) (w n) (rpStream (cvM (cvAx (t n)))
          (fun m => Z (synPi (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (K n)) m)))) P₀) (v₀ n))
        (cL n)
  layO : ∀ᶠ n in atTop, ∀ (P₀ : List (Fin (prime + mnKa + 4))), Pk n P₀ →
    ∀ (Y : ℕ → Fin (2 ^ ℓ n) → GaussianInt),
      LayRuns (layerTable (Ka := mnKa) (U := Unit) mnQ_layer Cost.brDirs) layQ
        (synG (synIdle (cstream (prime + mnKa) (w n) (rpStream (cvM (cvAx (t n))) Y)) P₀) (v₀ n))
        (synG (synIdle (cstream (prime + mnKa) (w n) (rpStream (cvM (cvAx (t n)))
          (fun x => Y ((layRec (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (K n)))
            ⟨x % 2 ^ (List.ofFn (cvAx (t n))).sum, Nat.mod_lt _ (by positivity)⟩)))) P₀) (v₀ n))
        (cL' n)
  cost : ∃ C : ℝ, ∀ᶠ n in atTop,
    ((mnCF n (w n) (cL n) (v₀ n) + mnCO n (w n) (cL' n) (v₀ n) : ℕ) : ℝ) ≤
      C * IntegerMultBounds.MathlibTM2.Cost.totConv n

/-- The transforms' parameter registers of a layout bundle. -/
def mnσL {w : ℕ → ℕ} (L : MnLay w) (n : ℕ) : LReg SXReg → List (Fin (prime + mnKa + 4)) :=
  mnσ (L.P₀ n) (L.v₀ n)

/-! ### The bundle -/

/-- **The synthetic transforms of the host from the layout hypotheses.** -/
def mnSynOfLay {w : ℕ → ℕ} (L : MnLay w) (hw : ∀ᶠ n in atTop, p n + 2 ≤ w n) :
    MnSyn mnKa mnLb w (mnσL L) where
  fwdP := mnFwdP L.layP
  oppP := mnOppP L.layQ
  π n := synPi (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (K n))
  cF n := mnCF n (w n) (L.cL n) (L.v₀ n)
  cO n := mnCO n (w n) (L.cL' n) (L.v₀ n)
  spec := by
    filter_upwards [eventually_big, hw, L.pk, L.wires, L.layF, L.layO]
      with n hbig hw hpk ⟨hv₀, hvh, hvt, hvc, hcb⟩ hF hO
    intro mainP
    have H := mn_layHyp hbig
    have hAl : nRounds (cvAx (t n)) ≤ ℓ n + 1 := (nRounds_le H).trans (Nat.le_succ _)
    have hbody := mn_body_lay mainP
    refine ⟨?_, ?_, fun m _ => mn_synPi_lt n m⟩
    · have h := embSynFwd_spec mnQ_layer mnKa_le mnLayE_inj hbody (cvAx (t n)) H hAl hw (L.v₀ n)
        hv₀ hvh hvt hvc hcb (L.Pk n) L.layP (L.cL n) hF
      rw [mnLayE_io] at h
      exact mn_synFwd_mono (fun S hS => mn_synPre_embPre (L.Pk n) hpk (L.v₀ n) S hS) h
    · have h := embSynOpp_spec mnQ_layer mnKa_le mnLayE_inj hbody (cvAx (t n)) H hAl hw (L.v₀ n)
        hv₀ hvh hvt hvc hcb (L.Pk n) L.layQ (L.cL' n) hO
      rw [mnLayE_io] at h
      exact mn_synOpp_mono (fun S hS => mn_synPre_embPre (L.Pk n) hpk (L.v₀ n) S hS) h
  cost := L.cost
  alpha := mnKa_alpha

end

end IntegerMultBounds.MathlibTM2.Fast.Main
