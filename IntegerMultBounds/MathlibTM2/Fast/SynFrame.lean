module

public import IntegerMultBounds.MathlibTM2.Host.Embed
public import IntegerMultBounds.MathlibTM2.Fast.SynFwd
public import IntegerMultBounds.MathlibTM2.Fast.ConvSynth

/-!
# The synthetic transforms in a larger register file

`synFwd_spec_br`, `synOpp_spec_br` (`Fast/SynFwd`) hold on the register file `nT SXReg` of the
layer machine. The convolution stage (`Fast/ConvSynth`, `cvSynth_runs`) runs both transforms in
a host of `T'` tapes next to its own registers. This file places the layer machine's file in the
big one along an injective `e : Fin (nT SXReg) → Fin T'` (`Host/Embed`) and restates both
contracts there.

**Programs.** `embProg e ι (synFwd Cost.brDirs layP)` and `embProg e ι (synOpp Cost.brDirs layQ)`,
run against any big table `body'` with `body' (ι f) = embProg e ι (layerTable hQ Cost.brDirs f)`.

**Precondition** (`embPre e Pk v₀`). The stacks read along `e` satisfy `synPre Pk v₀`: the left
stacks of the image are empty and every image register other than `e (lreg .io)` is in the rest
file of the transforms. Tapes outside the image are unconstrained. `embPre_framed`: when the
convolution layout `rg` meets the image of `e` at most in `e (lreg .io)`, `embPre` is framed
(`CvFramed rg`), since a change confined to `rg` keeps `inp`, `out`, the left stacks and every
other image register, and `synPre` leaves `lreg .io` free. `embPre_framed_io` is the case
`cvSynth_runs` uses: `rg .io = e (lreg .io)` (the contracts act on `rg .io`) and every other
register of `rg` outside the image.

**Contracts** (`embSynFwd_spec`, `embSynOpp_spec`). `SynFwdSpec`, `SynOppSpec` for the embedded
programs on the register `e (lreg .io)` under `embPre e Pk v₀`, with the step bounds of
`synFwd_spec_br`, `synOpp_spec_br`. The layout hypotheses `hLay` and the parking predicate `Pk`
stay on the small file.

**Alphabet** (`embKa`). `embKa` is the maximum of `9^4`, `NW` and the gate bounds
`(2 gateBound g + 1)^(2 |gateWires g|)` over the gates of the finite list `program Cost.brDirs`;
for `embKa ≤ Ka` the alphabet `prime + Ka` meets `hA`, `hA9`, `hNW` and `hgate` of the
transforms (`embKa_hA`, `embKa_hA9`, `embKa_hNW`, `embKa_gate`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.Networks
  IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.MathlibTM2.Fast.ConvSt (CvFramed CvR)
open IntegerMultBounds.MathlibTM2.Fast.ResampA (rsaFr)

noncomputable section

/-! ### The alphabet bound -/

section Alphabet

/-- The alphabet bound of one instruction: `(2 gateBound g + 1)^(2 |gateWires g|)` for a gate,
`0` for a factor. -/
def embGateBd : Instr → ℕ
  | .gate g => (2 * gateBound g + 1) ^ (2 * (gateWires g).length)
  | .factor _ _ => 0

/-- The alphabet constant: `9^4`, `NW` and every gate bound of `program Cost.brDirs`. -/
def embKa : ℕ := max (max (9 ^ 4) NW) (((program Cost.brDirs).map embGateBd).foldr max 0)

theorem embLe_foldr_max : ∀ (l : List ℕ) {x : ℕ}, x ∈ l → x ≤ l.foldr max 0
  | [], _, h => absurd h List.not_mem_nil
  | y :: l, x, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact le_max_left _ _
      · exact (embLe_foldr_max l h).trans (le_max_right _ _)

variable {Ka : ℕ} (hKa : embKa ≤ Ka)
include hKa

theorem embKa_gate : ∀ g, Instr.gate g ∈ program Cost.brDirs →
    (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4 := by
  intro g hg
  have h1 : embGateBd (.gate g) ≤ ((program Cost.brDirs).map embGateBd).foldr max 0 :=
    embLe_foldr_max _ (List.mem_map_of_mem hg)
  have h2 : ((program Cost.brDirs).map embGateBd).foldr max 0 ≤ embKa := le_max_right _ _
  simp only [embGateBd] at h1
  omega

theorem embKa_hA9 : 9 ^ 4 ≤ prime + Ka + 4 := by
  have : 9 ^ 4 ≤ embKa := (le_max_left _ _).trans (le_max_left _ _)
  omega

theorem embKa_hA : 14 ≤ prime + Ka := by
  have : 9 ^ 4 ≤ embKa := (le_max_left _ _).trans (le_max_left _ _)
  omega

theorem embKa_hNW : NW ≤ prime + Ka + 4 := by
  have : NW ≤ embKa := (le_max_right _ _).trans (le_max_left _ _)
  omega

end Alphabet

/-! ### The framed precondition -/

section Pre

variable {T' A : ℕ} (e : Fin (nT SXReg) → Fin T')

/-- The precondition of the embedded transforms: the stacks read along `e` meet `synPre Pk v₀`. -/
def embPre (Pk : List (Fin (A + 4)) → Prop) (v₀ : SynW → List (Fin (A + 4)))
    (S : Stacks T' A) : Prop :=
  synPre Pk v₀ (embStk e S)

/-- `embPre` is framed by every convolution layout meeting the image of `e` at most in
`e (lreg .io)`: a change confined to `rg` keeps `inp`, `out`, the left stacks and every image
register other than `e (lreg .io)`, and `synPre` does not read `lreg .io`. -/
theorem embPre_framed (Pk : List (Fin (A + 4)) → Prop) (v₀ : SynW → List (Fin (A + 4)))
    (rg : CvR → Fin T') (hdisj : ∀ r i, rg r = e i → i = lreg .io) :
    CvFramed rg (embPre e Pk v₀) := by
  intro S S' hS hfr
  obtain ⟨-, -, hL, hR⟩ := hfr
  obtain ⟨hL0, P₀, hPk, hP⟩ := hS
  refine ⟨fun y => ?_, P₀, hPk, fun k hk => ?_⟩
  · rw [embStk_L, hL, ← embStk_L]
    exact hL0 y
  · rw [embStk_R, hR (e k) fun r h => hk (hdisj r k h), ← embStk_R]
    exact hP k hk

/-- The layout of the convolution stage: `rg .io` is the transforms' register `e (lreg .io)`,
every other register of `rg` lies outside the image of `e`. Then `embPre` is framed by `rg`. -/
theorem embPre_framed_io (he : Function.Injective e) (Pk : List (Fin (A + 4)) → Prop)
    (v₀ : SynW → List (Fin (A + 4))) (rg : CvR → Fin T') (hio : rg .io = e (lreg .io))
    (hdisj : ∀ r, r ≠ .io → ∀ i, rg r ≠ e i) : CvFramed rg (embPre e Pk v₀) := by
  refine embPre_framed e Pk v₀ rg fun r i h => ?_
  by_cases hr : r = .io
  · subst hr
    exact he (h.symm.trans hio)
  · exact absurd h (hdisj r hr i)

end Pre

/-! ### The lifted contracts -/

section Lift

variable {Q Ka : ℕ} {U : Type} (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q) (hKa : embKa ≤ Ka)
  {T' : ℕ} {e : Fin (nT SXReg) → Fin T'} (he : Function.Injective e)
  {P' : Type} {ι : LProc → P'} {body' : P' → Pr P' T' Q (prime + Ka) U}
  (hbody : ∀ f, body' (ι f) = embProg e ι (layerTable (Ka := Ka) (U := U) hQ Cost.brDirs f))
include hKa he hbody

/-- **The forward synthetic transform in the big file.** `synFwd_spec_br` for the embedded
program on `e (lreg .io)` under `embPre e Pk v₀`. -/
theorem embSynFwd_spec {d : ℕ} (a : Fin d → ℕ) {ℓ K l w p : ℕ}
    (H : LayHyp (List.ofFn a) ℓ K) (hAl : nRounds a ≤ l + 1) (hpw : p + 2 ≤ w)
    (v₀ : SynW → List (Fin (prime + Ka + 4)))
    (hv₀ : SynV v₀ (List.ofFn a) ℓ K w l 0 (layPerm (List.ofFn a) ℓ K))
    (hvh : v₀ (.p .h) = []) (hvt : v₀ (.p .t) = []) (hvc : (v₀ (.p .c)).length = nRounds a)
    (hcb : blank ∉ v₀ (.p .c))
    (Pk : List (Fin (prime + Ka + 4)) → Prop)
    (layP : Pr LProc (nT SXReg) Q (prime + Ka) U) (cL : ℕ)
    (hLay : ∀ (P₀ : List (Fin (prime + Ka + 4))), Pk P₀ → ∀ (Z : ℕ → Fin (2 ^ l) → GaussianInt),
      LayRuns (layerTable (Ka := Ka) (U := U) hQ Cost.brDirs) layP
        (synG (synIdle (cstream (prime + Ka) w (rpStream (cvM a) Z)) P₀) v₀)
        (synG (synIdle (cstream (prime + Ka) w (rpStream (cvM a)
          (fun m => Z (synPi (layPerm (List.ofFn a) ℓ K) m)))) P₀) v₀) cL) :
    SynFwdSpec body' (embProg e ι (synFwd Cost.brDirs layP)) (e (lreg .io)) (embPre e Pk v₀)
      w p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (cL + synLoopFCost Cost.brDirs (List.ofFn a) ℓ K w l (nRounds a)
        (synStashCostW v₀ synXS + 6 * nRounds a + 6)) := by
  intro Z v S hPre hdisk hio
  have hs := synFwd_spec_br hQ (embKa_hA hKa) (embKa_hA9 hKa) (embKa_hNW hKa) (embKa_gate hKa)
    a H hAl hpw v₀ hv₀ hvh hvt hvc hcb Pk layP cL hLay
  obtain ⟨v₁, n, hu, hn, hex⟩ := hs Z (embDn e v) (embStk e S) hPre hdisk
    ((embStk_R (e := e) S _).trans hio)
  obtain ⟨v₁', -, hu₁, hex'⟩ := exec_emb_ovr he hbody hex v rfl S rfl
  refine ⟨v₁', n, hu₁.trans (hu.trans (embDn_user v)), hn, ?_⟩
  rw [embOvr_updR he, embOvr_stk] at hex'
  exact hex'

/-- **The opposite synthetic transform in the big file.** `synOpp_spec_br` for the embedded
program on `e (lreg .io)` under `embPre e Pk v₀`. -/
theorem embSynOpp_spec {d : ℕ} (a : Fin d → ℕ) {ℓ K l w p : ℕ}
    (H : LayHyp (List.ofFn a) ℓ K) (hAl : nRounds a ≤ l + 1) (hpw : p + 2 ≤ w)
    (v₀ : SynW → List (Fin (prime + Ka + 4)))
    (hv₀ : SynV v₀ (List.ofFn a) ℓ K w l 0 (layPerm (List.ofFn a) ℓ K))
    (hvh : v₀ (.p .h) = []) (hvt : v₀ (.p .t) = []) (hvc : (v₀ (.p .c)).length = nRounds a)
    (hcb : blank ∉ v₀ (.p .c))
    (Pk : List (Fin (prime + Ka + 4)) → Prop)
    (layQ : Pr LProc (nT SXReg) Q (prime + Ka) U) (cL : ℕ)
    (hLay : ∀ (P₀ : List (Fin (prime + Ka + 4))), Pk P₀ → ∀ (Y : ℕ → Fin (2 ^ l) → GaussianInt),
      LayRuns (layerTable (Ka := Ka) (U := U) hQ Cost.brDirs) layQ
        (synG (synIdle (cstream (prime + Ka) w (rpStream (cvM a) Y)) P₀) v₀)
        (synG (synIdle (cstream (prime + Ka) w (rpStream (cvM a)
          (fun x => Y ((layRec (layPerm (List.ofFn a) ℓ K)) ⟨x % 2 ^ (List.ofFn a).sum,
            Nat.mod_lt _ (by positivity)⟩)))) P₀) v₀) cL) :
    SynOppSpec body' (embProg e ι (synOpp Cost.brDirs layQ)) (e (lreg .io)) (embPre e Pk v₀)
      w p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (synLoopOCost Cost.brDirs (List.ofFn a) ℓ K w l (nRounds a)
        (synStashCostW v₀ synXS + 6 * nRounds a + 6) + cL) := by
  intro V v S hPre hdisk hio
  have hs := synOpp_spec_br hQ (embKa_hA hKa) (embKa_hA9 hKa) (embKa_hNW hKa) (embKa_gate hKa)
    a H hAl hpw v₀ hv₀ hvh hvt hvc hcb Pk layQ cL hLay
  obtain ⟨v₁, n, hu, hn, hex⟩ := hs V (embDn e v) (embStk e S) hPre hdisk
    ((embStk_R (e := e) S _).trans hio)
  obtain ⟨v₁', -, hu₁, hex'⟩ := exec_emb_ovr he hbody hex v rfl S rfl
  refine ⟨v₁', n, hu₁.trans (hu.trans (embDn_user v)), hn, ?_⟩
  rw [embOvr_updR he, embOvr_stk] at hex'
  exact hex'

end Lift

end

end IntegerMultBounds.MathlibTM2.Fast
