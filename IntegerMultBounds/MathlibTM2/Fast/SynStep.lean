module

public import IntegerMultBounds.MathlibTM2.Fast.SynRound
public import IntegerMultBounds.MathlibTM2.Fast.SynMath
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The rounds of the computed synthetic transforms on record streams

Paper §6, proof of `lem:synthetic-transform-cost`. The forward round at named position `h` is the
layer step (`synLayerStep`: `Q_p(ℋ)` on the selected bits in the layout `L = layPerm es ℓ K`)
followed by the twiddle `J_E` (`synTwStep true`); the opposite round is `J_E⁻¹`
(`synTwStep false`) followed by the layer step.

* `SynNum p L u Y`: the stream records `Y` are the numerators at scale `2^p` of the logical array
  `u` stored in the physical order of `L`: `Y x / 2^p = u (synPi L x)` for `x < 2^N`.
* `synRoundF_math`, `synRoundO_math`: the stream of the layer and twiddle outputs carries
  `rdR p (fwdRound es h u)`, resp. `rdR p (oppRound es h u)` (`Mult/SynthErrRounds`:
  `mulYInv_rdR_bflyL`, `oppRound_layer_input`).
* `sg_synRoundF`, `sg_synRoundO`: the rounds as machines on `synG (synIdle io P₀) v`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.Networks
  IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option maxHeartbeats 4000000

/-! ### Numerators of physical arrays -/

section Num

variable {r : ℕ}

/-- The records `Y` are the numerators at scale `2^p` of the logical array `u` stored in the
physical order of the layout `L`. -/
def SynNum {N : ℕ} (p : ℕ) (L : Equiv.Perm (Fin N)) (u : Recs r) (Y : ℕ → Fin r → GaussianInt) :
    Prop :=
  ∀ x < 2 ^ N, ∀ c, GaussianInt.toComplex (Y x c) / 2 ^ p = u (synPi L x) c

theorem bfly_smul (k : ℂ) (q : ℕ) (u : Recs r) :
    bfly q (fun x c => k * u x c) = fun x c => k * bfly q u x c := by
  funext x c
  simp only [bfly, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem bflyL_smul (k : ℂ) : ∀ (l : List ℕ) (u : Recs r),
    bflyL l (fun x c => k * u x c) = fun x c => k * bflyL l u x c
  | [], _ => rfl
  | q :: l, u => by
      show bfly q (bflyL l _) = _
      rw [bflyL_smul k l u, bfly_smul]
      rfl

/-- The records masked to the first `M`. -/
def synMask (M : ℕ) (Y : ℕ → Fin r → GaussianInt) : ℕ → Fin r → GaussianInt :=
  fun x c => if x < M then Y x c else 0

theorem rpStream_synMask (M : ℕ) (Y : ℕ → Fin r → GaussianInt) :
    IntegerMultBounds.MathlibTM2.Fast.rpStream M (synMask M Y) = IntegerMultBounds.MathlibTM2.Fast.rpStream M Y :=
  rpStream_congr fun x hx => by funext c; simp [synMask, hx]

theorem synNum_mask {N p : ℕ} {L : Equiv.Perm (Fin N)} {u : Recs r} {Y : ℕ → Fin r → GaussianInt}
    (h : SynNum p L u Y) : SynNum p L u (synMask (2 ^ N) Y) := by
  intro x hx c
  simp only [synMask, hx, ite_true]
  exact h x hx c

theorem synMask_norm {N p : ℕ} {L : Equiv.Perm (Fin N)} {u : Recs r}
    {Y : ℕ → Fin r → GaussianInt} (h : SynNum p L u Y) (hu : SupLe N u 1) :
    ∀ x c, ‖GaussianInt.toComplex (synMask (2 ^ N) Y x c)‖ ≤ 2 ^ p := by
  intro x c
  by_cases hx : x < 2 ^ N
  · simp only [synMask, hx, ite_true]
    have e := h x hx c
    have hb := hu (synPi L x) (synPi_lt L x) c
    rw [← e] at hb
    have hp : (0 : ℝ) < 2 ^ p := by positivity
    rw [norm_div] at hb
    have : ‖(2 : ℂ) ^ p‖ = 2 ^ p := by simp
    rw [this, div_le_one hp] at hb
    exact hb
  · simp only [synMask, hx, ite_false]
    simp

end Num

/-! ### The arithmetic of one round -/

section RoundMath

variable {l : ℕ}

/-- **The forward round on physical numerators**: the layer output (componentwise truncation of
the butterflies on the physical selected bits) followed by the twiddle of the logical addresses
carries `Q_p(fwdRound z)`. -/
theorem synRoundF_math (es : List ℕ) (L : Equiv.Perm (Fin es.sum)) (p h : ℕ)
    (u : Recs (2 ^ l)) (Y : ℕ → Fin (2 ^ l) → GaussianInt) (hY : SynNum p L u Y) :
    SynNum p L (rdR p (fwdRound es h u))
      (fun m => twShiftZ (twEx true es l h (twGat (twPosL L) es.sum m))
        (synTrunc (bflyL ((selBits es h).map (twPosL L))
          (fun x c => GaussianInt.toComplex (Y x c))) m)) := by
  intro x hx c
  have hP : ∀ q ∈ (selBits es h).map (twPosL L), q < es.sum := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hq
    exact twPosL_lt L k (selBits_lt es hk)
  -- the layer
  have hB : ∀ m < 2 ^ es.sum, ∀ c', GaussianInt.toComplex (synTrunc (bflyL ((selBits es h).map
      (twPosL L)) (fun x c => GaussianInt.toComplex (Y x c))) m c') / 2 ^ p =
        rdR p (bflyL (selBits es h) u) (synPi L m) c' := by
    intro m hm c'
    have e1 : (fun x c => GaussianInt.toComplex (Y x c)) =
        fun x c => (2 : ℂ) ^ p * (GaussianInt.toComplex (Y x c) / 2 ^ p) := by
      funext x c; field_simp
    have heq : EqBelow es.sum (fun x c => GaussianInt.toComplex (Y x c) / 2 ^ p)
        (synPhys L u) := by
      intro x hx; funext c; exact hY x hx c
    have h2 := bflyL_eqBelow hP heq m hm
    rw [bflyL_phys L u _ (fun q hq => selBits_lt es hq)] at h2
    simp only [synTrunc]
    rw [e1, bflyL_smul]
    have h3 := synTr_toComplex p (bflyL ((selBits es h).map (twPosL L))
      (fun x c => GaussianInt.toComplex (Y x c) / 2 ^ p) m c')
    simpa [h2, synPhys, rdR] using h3
  -- the twiddle
  rw [twShiftZ_toComplex]
  have hrec : (fun c' => GaussianInt.toComplex (synTrunc (bflyL ((selBits es h).map (twPosL L))
      (fun x c => GaussianInt.toComplex (Y x c))) x c') / 2 ^ p) =
        rdR p (bflyL (selBits es h) u) (synPi L x) := by
    funext c'; exact hB x hx c'
  rw [hrec]
  show shiftInv _ _ c = _
  rw [← mulYInv_rdR_bflyL es p h u]
  rfl

/-- **The opposite round on physical numerators**: the inverse twiddle followed by the layer
carries `Q_p(oppRound z)`. -/
theorem synRoundO_math (es : List ℕ) (L : Equiv.Perm (Fin es.sum)) (p h : ℕ)
    (u : Recs (2 ^ l)) (Y : ℕ → Fin (2 ^ l) → GaussianInt) (hY : SynNum p L u Y) :
    SynNum p L (mulY (twE es (2 ^ l) h (parts es h)) u)
      (fun m => twShiftZ (twEx false es l h (twGat (twPosL L) es.sum m)) (Y m)) := by
  intro x hx c
  rw [twShiftZ_toComplex]
  have hrec : (fun c' => GaussianInt.toComplex (Y x c') / 2 ^ p) = u (synPi L x) := by
    funext c'; exact hY x hx c'
  rw [hrec, twEx_false, ← shiftNegZ_mod]
  rfl

theorem synRoundO_math2 (es : List ℕ) (L : Equiv.Perm (Fin es.sum)) (p h : ℕ)
    (u : Recs (2 ^ l)) (Y : ℕ → Fin (2 ^ l) → GaussianInt)
    (hY : SynNum p L (mulY (twE es (2 ^ l) h (parts es h)) u) Y) :
    SynNum p L (rdR p (oppRound es h u))
      (synTrunc (bflyL ((selBits es h).map (twPosL L))
        (fun x c => GaussianInt.toComplex (Y x c)))) := by
  intro m hm c'
  have hP : ∀ q ∈ (selBits es h).map (twPosL L), q < es.sum := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hq
    exact twPosL_lt L k (selBits_lt es hk)
  have e1 : (fun x c => GaussianInt.toComplex (Y x c)) =
      fun x c => (2 : ℂ) ^ p * (GaussianInt.toComplex (Y x c) / 2 ^ p) := by
    funext x c; field_simp
  have heq : EqBelow es.sum (fun x c => GaussianInt.toComplex (Y x c) / 2 ^ p)
      (synPhys L (mulY (twE es (2 ^ l) h (parts es h)) u)) := by
    intro x hx; funext c; exact hY x hx c
  have h2 := bflyL_eqBelow hP heq m hm
  rw [bflyL_phys L _ _ (fun q hq => selBits_lt es hq)] at h2
  simp only [synTrunc]
  rw [e1, bflyL_smul]
  have h3 := synTr_toComplex p (bflyL ((selBits es h).map (twPosL L))
    (fun x c => GaussianInt.toComplex (Y x c) / 2 ^ p) m c')
  simpa [h2, synPhys, rdR, oppRound] using h3

end RoundMath

/-! ### The rounds as machines -/

section Rounds

variable {Q Ka : ℕ} {U : Type}

/-- The forward round: the layer step, then the twiddle `y^(-E)`. -/
noncomputable def synRoundF (ds : ComplexFramedExecution.Directions) :
    Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq (synLayerStep ds) (synTwStep true)

/-- The opposite round: the twiddle `y^E`, then the layer step. -/
noncomputable def synRoundO (ds : ComplexFramedExecution.Directions) :
    Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq (synTwStep false) (synLayerStep ds)

/-- The step bound of one round. -/
noncomputable def synRoundCost (ds : ComplexFramedExecution.Directions) (es : List ℕ)
    (ℓ K w l h stk : ℕ) : ℕ :=
  synLayerStepCost ds es ℓ K w l h stk + synTwCost es l w h

variable (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
  (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
  (hA : 14 ≤ prime + Ka) (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
  (hgate : ∀ g, Instr.gate g ∈ program ds →
    (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
include hd hA hA9 hNW hgate

/-- **The forward round at named position `h`.** From the stream of the physical numerators of
a disk array `u` (layout `L = layPerm es ℓ K`), the round leaves the stream of the physical
numerators of `rdR p (fwdRound es h u)`; the wires `v` and `park` are restored. -/
theorem sg_synRoundF {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) {l w p h : ℕ}
    (hh : h + 1 ≤ ℓ) (hhl : h ≤ l) (hpw : p + 2 ≤ w) (v : SynW → List (Fin (prime + Ka + 4)))
    (hv : SynV v es ℓ K w l h (layPerm es ℓ K)) (P₀ : List (Fin (prime + Ka + 4)))
    (u : Recs (2 ^ l)) (hu : SupLe es.sum u 1) (Y : ℕ → Fin (2 ^ l) → GaussianInt)
    (hY : SynNum p (layPerm es ℓ K) u Y) :
    ∃ Y', SynNum p (layPerm es ℓ K) (rdR p (fwdRound es h u)) Y' ∧
      LayRuns (layerTable (Ka := Ka) (U := U) hQ ds) (synRoundF ds)
        (synG (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum) Y)) P₀) v)
        (synG (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum) Y')) P₀) v)
        (synRoundCost ds es ℓ K w l h (synStashCostW v synXS)) := by
  set Ym := synMask (2 ^ es.sum) Y with hYm
  have hYm' := synNum_mask hY
  refine ⟨_, synRoundF_math es (layPerm es ℓ K) p h u Ym hYm', ?_⟩
  have s1 := sg_synLayerStep (U := U) hQ ds hd hA hA9 hNW hgate H hh hpw v hv P₀ Ym
    (synMask_norm hY hu)
  rw [hYm, rpStream_synMask] at s1
  have s2 := sg_synTwStep (layerTable (Ka := Ka) (U := U) hQ ds) true (by omega) (by omega) hhl
    (layPerm es ℓ K) (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum)
      (synTrunc (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
        (fun x c => GaussianInt.toComplex (synMask (2 ^ es.sum) Y x c)))))) P₀) v
    (synTrunc (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
        (fun x c => GaussianInt.toComplex (synMask (2 ^ es.sum) Y x c))))
    (by simp [synIdle, lreg]) hv.hpz hv.htw hv.hN
    hv.hw hv.hr hv.hlr hv.hh hv.hes hv.hD (hv.hs 2) (hv.hs 3) (hv.hs 23) (hv.hs 25) (hv.hs 26)
    (hv.hs 27) (hv.hs 28)
  rw [synIdle_update_io] at s2
  exact s1.seq s2

/-- **The opposite round at named position `h`.** -/
theorem sg_synRoundO {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) {l w p h : ℕ}
    (hh : h + 1 ≤ ℓ) (hhl : h ≤ l) (hpw : p + 2 ≤ w) (v : SynW → List (Fin (prime + Ka + 4)))
    (hv : SynV v es ℓ K w l h (layPerm es ℓ K)) (P₀ : List (Fin (prime + Ka + 4)))
    (u : Recs (2 ^ l)) (hu : SupLe es.sum u 1) (Y : ℕ → Fin (2 ^ l) → GaussianInt)
    (hY : SynNum p (layPerm es ℓ K) u Y) :
    ∃ Y', SynNum p (layPerm es ℓ K) (rdR p (oppRound es h u)) Y' ∧
      LayRuns (layerTable (Ka := Ka) (U := U) hQ ds) (synRoundO ds)
        (synG (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum) Y)) P₀) v)
        (synG (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum) Y')) P₀) v)
        (synTwCost es l w h + synLayerStepCost ds es ℓ K w l h (synStashCostW v synXS)) := by
  set Y₁ := fun m => twShiftZ (twEx false es l h (twGat (twPosL (layPerm es ℓ K)) es.sum m)) (Y m)
    with hY₁
  have hY₁' := synRoundO_math es (layPerm es ℓ K) p h u Y hY
  set Ym := synMask (2 ^ es.sum) Y₁ with hYm
  have hu₁ : SupLe es.sum (mulY (twE es (2 ^ l) h (parts es h)) u) 1 := mulY_supLe _ hu
  refine ⟨_, synRoundO_math2 es (layPerm es ℓ K) p h u Ym (synNum_mask hY₁'), ?_⟩
  have s1 := sg_synTwStep (layerTable (Ka := Ka) (U := U) hQ ds) false (by omega) (by omega) hhl
    (layPerm es ℓ K) (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum) Y)) P₀) v
    Y (by simp [synIdle, lreg]) hv.hpz hv.htw hv.hN
    hv.hw hv.hr hv.hlr hv.hh hv.hes hv.hD (hv.hs 2) (hv.hs 3) (hv.hs 23) (hv.hs 25) (hv.hs 26)
    (hv.hs 27) (hv.hs 28)
  rw [synIdle_update_io] at s1
  have s2 := sg_synLayerStep (U := U) hQ ds hd hA hA9 hNW hgate H hh hpw v hv P₀ Ym
    (synMask_norm hY₁' hu₁)
  rw [hYm, rpStream_synMask] at s2
  exact s1.seq s2

end Rounds

end IntegerMultBounds.MathlibTM2.Fast
