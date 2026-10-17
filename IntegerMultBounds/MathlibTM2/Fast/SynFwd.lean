module

public import IntegerMultBounds.MathlibTM2.Fast.SynStep
public import IntegerMultBounds.MathlibTM2.Fast.ConvSpec
public import IntegerMultBounds.MathlibTM2.Cost.Branching
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The computed synthetic transforms

Paper §6, `lem:synthetic-transform-cost`. The forward transform runs the forward rounds at named
positions `h = A - 1, …, 0` (`A = nRounds a`), the opposite transform the opposite rounds at
`h = 0, …, A - 1`, by one loop over the round counter `p .c` (`scanP`, spare `p .t`). The
records stay in the physical order of the layout `L = layPerm es ℓ K`: record `x` of the stream is
the logical record `synPi L x`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.Networks
  IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option maxHeartbeats 4000000

/-! ### Numerators of grid arrays -/

section Ynum

variable {r : ℕ}

/-- The numerators at scale `2^p` of the logical array `u` in the physical order of `L`. -/
noncomputable def synYnum {N : ℕ} (p : ℕ) (L : Equiv.Perm (Fin N)) (u : Recs r) :
    ℕ → Fin r → GaussianInt :=
  fun x c => numer p (u (synPi L x) c)

theorem synNum_ynum {N p : ℕ} {L : Equiv.Perm (Fin N)} {u : Recs r} (hu : GridR p u) :
    SynNum p L u (synYnum p L u) := by
  intro x _ c
  obtain ⟨a, b, hab⟩ := hu (synPi L x) c
  have e : u (synPi L x) c = GaussianInt.toComplex ⟨a, b⟩ / 2 ^ p := by
    rw [hab, two_pow_complex]
    apply Complex.ext
    · rw [toComplex_div_re]
    · rw [toComplex_div_im]
  simp only [synYnum]
  rw [e, numer_grid]

theorem synNum_stream {N p : ℕ} {L : Equiv.Perm (Fin N)} {u : Recs r}
    {Y : ℕ → Fin r → GaussianInt} (h : SynNum p L u Y) :
    IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ N) Y = IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ N) (synYnum p L u) := by
  refine rpStream_congr fun x hx => ?_
  funext c
  simp only [synYnum]
  rw [← h x hx c, numer_grid]

end Ynum

/-! ### The sequences of rounds -/

section Seqs

variable {r : ℕ} [NeZero r] (p : ℕ) (es : List ℕ)

/-- The array after `j` forward rounds of `A`: the rounds at `h = A - 1, …, A - j`. -/
noncomputable def synUF (A : ℕ) (z : Recs r) : ℕ → Recs r
  | 0 => z
  | j + 1 => rdR p (fwdRound es (A - 1 - j) (synUF A z j))

theorem fwdRoundsC_synUF (A : ℕ) (z : Recs r) : ∀ j ≤ A,
    fwdRoundsC p es A z = fwdRoundsC p es (A - j) (synUF p es A z j)
  | 0, _ => rfl
  | j + 1, hj => by
      rw [fwdRoundsC_synUF A z j (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, A - j = k + 1 := ⟨A - j - 1, by omega⟩
      rw [hk, fwdRoundsC, synUF, show A - (j + 1) = k by omega, show A - 1 - j = k by omega]

theorem fwdRoundsC_eq_synUF (A : ℕ) (z : Recs r) : fwdRoundsC p es A z = synUF p es A z A := by
  have := fwdRoundsC_synUF p es A z A le_rfl
  rwa [Nat.sub_self, fwdRoundsC] at this

theorem synUF_supLe (A : ℕ) {z : Recs r} (hz : SupLe es.sum z 1) :
    ∀ j, SupLe es.sum (synUF p es A z j) 1
  | 0 => hz
  | j + 1 => rdR_supLe p (fwdRound_supLe es _ (synUF_supLe A hz j))

theorem synUF_grid (A : ℕ) {z : Recs r} (hz : GridR p z) : ∀ j, GridR p (synUF p es A z j)
  | 0 => hz
  | _ + 1 => gridR_rdR p _

theorem oppRoundsC_supLe' (k : ℕ) {z : Recs r} (hz : SupLe es.sum z 1) :
    SupLe es.sum (oppRoundsC p es k z) 1 := oppRoundsC_supLe p es k hz

end Seqs

/-! ### The round wires during the loop -/

section LoopWires

variable {A : ℕ}

/-- The round wires with the counter `p .c := c'`, its spare `p .t := t'` and `p .h := h` ticks. -/
def synSetH (v : SynW → List (Fin (A + 4))) (c' t' : List (Fin (A + 4))) (h : ℕ) :
    SynW → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update v (.p .c) c') (.p .t) t') (.p .h)
    (List.replicate h tick)

theorem tick_ne_blank : (tick : Fin (A + 4)) ≠ blank := by
  simp [tick, bitSymbol, blank, Fin.ext_iff]

theorem SynV.setH {v : SynW → List (Fin (A + 4))} {es : List ℕ} {ℓ K w l h₀ : ℕ}
    {L : Equiv.Perm (Fin es.sum)} (hv : SynV v es ℓ K w l h₀ L) {c' t' : List (Fin (A + 4))}
    (hc : blank ∉ c') (ht : blank ∉ t') (h : ℕ) :
    SynV (synSetH v c' t' h) es ℓ K w l h L where
  hh := by simp [synSetH]
  hK := by simp [synSetH]; exact hv.hK
  hℓ := by simp [synSetH]; exact hv.hℓ
  hb := by simp [synSetH]; exact hv.hb
  hD := by simp [synSetH]; exact hv.hD
  hLg := by simp [synSetH]; exact hv.hLg
  hN := by simp [synSetH]; exact hv.hN
  hw := by simp [synSetH]; exact hv.hw
  hr := by simp [synSetH]; exact hv.hr
  hlr := by simp [synSetH]; exact hv.hlr
  hes := by simp [synSetH]; exact hv.hes
  hpz := by simp [synSetH]; exact hv.hpz
  htw := fun a hx => by simp [synSetH]; exact hv.htw a hx
  hs := fun i => by simp [synSetH]; exact hv.hs i
  hly := fun i => by simp [synSetH]; exact hv.hly i
  hw2 := by simp [synSetH]; exact hv.hw2
  hcf := by simp [synSetH]; exact hv.hcf
  hkh := by simp [synSetH]; exact hv.hkh
  hrh := by simp [synSetH]; exact hv.hrh
  hpr := by simp [synSetH]; exact hv.hpr
  hblank := by
    intro x hx
    simp only [synXS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    · simp [synSetH, List.mem_replicate]; intro _ h; exact tick_ne_blank h.symm
    · simpa [synSetH] using hc
    · simpa [synSetH] using ht
    all_goals
      first
      | (simpa [synSetH] using hv.hblank _ (by simp [synXS]))

theorem synStashCostW_setH (v : SynW → List (Fin (A + 4))) (c' t' : List (Fin (A + 4)))
    (h : ℕ) :
    synStashCostW (synSetH v c' t' h) synXS ≤
      synStashCostW v synXS + 2 * h + 2 * c'.length + 2 * t'.length := by
  simp only [synStashCostW, synXS, synSetH, Function.update_apply]
  simp
  omega

end LoopWires

/-! ### The loops of rounds -/

section Loops

variable {Q Ka : ℕ} {U : Type}

/-- One pass of the forward loop: `h := |p .c|` (the rounds left), the forward round, `p .h`
cleared. -/
noncomputable def synBodyF (ds : ComplexFramedExecution.Directions) :
    Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq (ucopy (sreg (.p .c)) (sreg (.p .h)) (sreg (.s 2)))
    (.seq (synRoundF ds) (uclear (sreg (.p .h))))

/-- One pass of the opposite loop: `h := |p .t| - 1` (the rounds done), the opposite round,
`p .h` cleared. -/
noncomputable def synBodyO (ds : ComplexFramedExecution.Directions) :
    Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq (ucopy (sreg (.p .t)) (sreg (.p .h)) (sreg (.s 2)))
    (.seq (synPop (sreg (.p .h))) (.seq (synRoundO ds) (uclear (sreg (.p .h)))))

/-- The loop of forward rounds over the counter `p .c`. -/
noncomputable def synLoopF (ds : ComplexFramedExecution.Directions) :
    Pr LProc (nT SXReg) Q (prime + Ka) U :=
  scanP (sreg (.p .c)) (sreg (.p .t)) (synBodyF ds)

/-- The loop of opposite rounds over the counter `p .c`. -/
noncomputable def synLoopO (ds : ComplexFramedExecution.Directions) :
    Pr LProc (nT SXReg) Q (prime + Ka) U :=
  scanP (sreg (.p .c)) (sreg (.p .t)) (synBodyO ds)

/-- The step bound of the forward loop of `A` rounds, `stk` bounding the parking costs. -/
noncomputable def synLoopFCost (ds : ComplexFramedExecution.Directions) (es : List ℕ)
    (ℓ K w l A stk : ℕ) : ℕ :=
  (∑ j ∈ Finset.range A, ((4 * (A - 1 - j) + 4) +
    synRoundCost ds es ℓ K w l (A - 1 - j) stk + (2 * (A - 1 - j) + 2) + 3)) + 2 * A + 4

/-- The step bound of the opposite loop of `A` rounds. -/
noncomputable def synLoopOCost (ds : ComplexFramedExecution.Directions) (es : List ℕ)
    (ℓ K w l A stk : ℕ) : ℕ :=
  (∑ j ∈ Finset.range A, ((4 * (j + 1) + 4) + 1 +
    (synTwCost es l w j + synLayerStepCost ds es ℓ K w l j stk) + (2 * j + 2) + 3)) +
    2 * A + 4

end Loops

section LoopRuns

variable {Q Ka : ℕ} {U : Type}

theorem synRoundCost_mono (ds : ComplexFramedExecution.Directions) (es : List ℕ)
    (ℓ K w l h : ℕ) {s s' : ℕ} (hs : s ≤ s') :
    synRoundCost ds es ℓ K w l h s ≤ synRoundCost ds es ℓ K w l h s' := by
  simp only [synRoundCost, synLayerStepCost]
  omega

theorem synLayerStepCost_mono (ds : ComplexFramedExecution.Directions) (es : List ℕ)
    (ℓ K w l h : ℕ) {s s' : ℕ} (hs : s ≤ s') :
    synLayerStepCost ds es ℓ K w l h s ≤ synLayerStepCost ds es ℓ K w l h s' := by
  simp only [synLayerStepCost]
  omega

variable (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
  (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
  (hA : 14 ≤ prime + Ka) (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
  (hgate : ∀ g, Instr.gate g ∈ program ds →
    (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
include hd hA hA9 hNW hgate

/-- **The loop of forward rounds.** With `A` symbols on the counter `p .c`, the loop runs the
forward rounds at `h = A - 1, …, 0` on the physical numerators of the disk grid array `z`. -/
theorem sg_synLoopF {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) {l w p A : ℕ} (hAℓ : A ≤ ℓ)
    (hAl : A ≤ l + 1) (hpw : p + 2 ≤ w) (v : SynW → List (Fin (prime + Ka + 4)))
    (hv : SynV v es ℓ K w l 0 (layPerm es ℓ K)) (hvh : v (.p .h) = []) (hvt : v (.p .t) = [])
    (hvc : (v (.p .c)).length = A) (hcb : blank ∉ v (.p .c)) (P₀ : List (Fin (prime + Ka + 4)))
    (z : Recs (2 ^ l)) (hz : SupLe es.sum z 1) (hzg : GridR p z) :
    LayRuns (layerTable (Ka := Ka) (U := U) hQ ds) (synLoopF ds)
      (synG (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum)
        (synYnum p (layPerm es ℓ K) z))) P₀) v)
      (synG (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum)
        (synYnum p (layPerm es ℓ K) (fwdRoundsC p (es) A z)))) P₀) v)
      (synLoopFCost ds es ℓ K w l A (synStashCostW v synXS + 6 * A + 6)) := by
  set L := layPerm es ℓ K with hL
  set cs := v (.p .c) with hcs
  set stk := synStashCostW v synXS + 6 * A + 6 with hstk
  let Φ : ℕ → Fin (nT SXReg) → List (Fin (prime + Ka + 4)) := fun j =>
    synG (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum)
      (synYnum p L (synUF p es A z j)))) P₀) v
  have hstep : ∀ j < cs.length, LayRuns (layerTable (Ka := Ka) (U := U) hQ ds) (synBodyF ds)
      (Function.update (Function.update (Φ j) (sreg (.p .c)) (cs.drop (j + 1))) (sreg (.p .t))
        (cs.take (j + 1)).reverse)
      (Function.update (Function.update (Φ (j + 1)) (sreg (.p .c)) (cs.drop (j + 1)))
        (sreg (.p .t)) (cs.take (j + 1)).reverse)
      ((4 * (A - 1 - j) + 4) + synRoundCost ds es ℓ K w l (A - 1 - j) stk +
        (2 * (A - 1 - j) + 2)) := by
    intro j hj
    have hjA : j < A := by rw [← hvc]; exact hj
    simp only [Φ, synG_update]
    have hcd : blank ∉ cs.drop (j + 1) := fun h => hcb (List.mem_of_mem_drop h)
    have hct : blank ∉ (cs.take (j + 1)).reverse := fun h =>
      hcb (List.mem_of_mem_take (List.mem_reverse.1 h))
    have hvs := hv.setH hcd hct (A - 1 - j)
    have hround := sg_synRoundF (U := U) hQ ds hd hA hA9 hNW hgate H (by omega) (by omega) hpw _
      hvs P₀ (synUF p es A z j) (synUF_supLe p es A hz j) _
      (synNum_ynum (synUF_grid p es A hzg j))
    obtain ⟨Y', hY', hr⟩ := hround
    rw [synNum_stream hY'] at hr
    have hst : synStashCostW (synSetH v (cs.drop (j + 1)) (cs.take (j + 1)).reverse (A - 1 - j))
        synXS ≤ stk := by
      have := synStashCostW_setH v (cs.drop (j + 1)) (cs.take (j + 1)).reverse (A - 1 - j)
      simp only [List.length_drop, List.length_reverse, List.length_take] at this
      rw [hstk]
      have : min (j + 1) cs.length ≤ A := by omega
      omega
    refine lr_weaken (layerTable (Ka := Ka) (U := U) hQ ds)
      ((sgU_copy (layerTable (Ka := Ka) (U := U) hQ ds) (a := .p .c) (b := .p .h) (t := .s 2)
        (x := A - 1 - j) (y := 0) (by decide) (by decide) (by decide) (by simp [hv.hs 2])
        (by simp; omega) (by simp [hvh])).seq <|
      (lr_weaken (layerTable (Ka := Ka) (U := U) hQ ds) hr rfl le_rfl).seq <|
      sgU_clear (layerTable (Ka := Ka) (U := U) hQ ds) (a := .p .h) (x := A - 1 - j)
        (by simp [synSetH])) ?_ ?_
    · refine congrArg (synG _) ?_
      simp only [synSetH, Function.update_idem]
      funext y
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    · have := synRoundCost_mono ds es ℓ K w l (A - 1 - j) hst
      omega
  have hscan := layScan_exec (body := layerTable (Ka := Ka) (U := U) hQ ds)
    (sreg_injective.ne (by decide : SynW.p .c ≠ .p .t)) Φ cs _ hstep
  rw [hvc] at hscan
  refine lr_weaken (layerTable (Ka := Ka) (U := U) hQ ds) (lr_congr_left _ hscan ?_) ?_ ?_
  · simp only [Φ, synG_update, synUF, ← hvt]
    rw [hcs, Function.update_eq_self, Function.update_eq_self]
  · simp only [Φ, synG_update, ← hvt, fwdRoundsC_eq_synUF]
    rw [hcs, Function.update_eq_self, Function.update_eq_self]
  · simp only [synLoopFCost]
    omega

/-- **The loop of opposite rounds.** With `A` symbols on the counter `p .c`, the loop runs the
opposite rounds at `h = 0, …, A - 1` on the physical numerators of the disk grid array `z`. -/
theorem sg_synLoopO {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) {l w p A : ℕ} (hAℓ : A ≤ ℓ)
    (hAl : A ≤ l + 1) (hpw : p + 2 ≤ w) (v : SynW → List (Fin (prime + Ka + 4)))
    (hv : SynV v es ℓ K w l 0 (layPerm es ℓ K)) (hvh : v (.p .h) = []) (hvt : v (.p .t) = [])
    (hvc : (v (.p .c)).length = A) (hcb : blank ∉ v (.p .c)) (P₀ : List (Fin (prime + Ka + 4)))
    (z : Recs (2 ^ l)) (hz : SupLe es.sum z 1) (hzg : GridR p z) :
    LayRuns (layerTable (Ka := Ka) (U := U) hQ ds) (synLoopO ds)
      (synG (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum)
        (synYnum p (layPerm es ℓ K) z))) P₀) v)
      (synG (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum)
        (synYnum p (layPerm es ℓ K) (oppRoundsC p es A z)))) P₀) v)
      (synLoopOCost ds es ℓ K w l A (synStashCostW v synXS + 6 * A + 6)) := by
  set L := layPerm es ℓ K with hL
  set cs := v (.p .c) with hcs
  set stk := synStashCostW v synXS + 6 * A + 6 with hstk
  let Φ : ℕ → Fin (nT SXReg) → List (Fin (prime + Ka + 4)) := fun j =>
    synG (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum)
      (synYnum p L (oppRoundsC p es j z)))) P₀) v
  have hstep : ∀ j < cs.length, LayRuns (layerTable (Ka := Ka) (U := U) hQ ds) (synBodyO ds)
      (Function.update (Function.update (Φ j) (sreg (.p .c)) (cs.drop (j + 1))) (sreg (.p .t))
        (cs.take (j + 1)).reverse)
      (Function.update (Function.update (Φ (j + 1)) (sreg (.p .c)) (cs.drop (j + 1)))
        (sreg (.p .t)) (cs.take (j + 1)).reverse)
      ((4 * (j + 1) + 4) + 1 + (synTwCost es l w j + synLayerStepCost ds es ℓ K w l j stk) +
        (2 * j + 2)) := by
    intro j hj
    have hjA : j < A := by rw [← hvc]; exact hj
    simp only [Φ, synG_update]
    have hcd : blank ∉ cs.drop (j + 1) := fun h => hcb (List.mem_of_mem_drop h)
    have hct : blank ∉ (cs.take (j + 1)).reverse := fun h =>
      hcb (List.mem_of_mem_take (List.mem_reverse.1 h))
    have hvs := hv.setH hcd hct j
    have hround := sg_synRoundO (U := U) hQ ds hd hA hA9 hNW hgate H (by omega) (by omega) hpw _
      hvs P₀ (oppRoundsC p es j z) (oppRoundsC_supLe p es j hz) _
      (synNum_ynum (oppRoundsC_grid p es j hzg))
    obtain ⟨Y', hY', hr⟩ := hround
    rw [synNum_stream hY'] at hr
    have hst : synStashCostW (synSetH v (cs.drop (j + 1)) (cs.take (j + 1)).reverse j)
        synXS ≤ stk := by
      have := synStashCostW_setH v (cs.drop (j + 1)) (cs.take (j + 1)).reverse j
      simp only [List.length_drop, List.length_reverse, List.length_take] at this
      rw [hstk]
      have : min (j + 1) cs.length ≤ A := by omega
      omega
    have hlen : ((cs.take (j + 1)).reverse).length = j + 1 := by
      simp only [List.length_reverse, List.length_take]; omega
    refine lr_weaken (layerTable (Ka := Ka) (U := U) hQ ds)
      ((sgU_copy (layerTable (Ka := Ka) (U := U) hQ ds) (a := .p .t) (b := .p .h) (t := .s 2)
        (x := j + 1) (y := 0) (by decide) (by decide) (by decide) (by simp [hv.hs 2])
        (by simp [hlen]) (by simp [hvh])).seq <|
      (sgU_pop (layerTable (Ka := Ka) (U := U) hQ ds) (a := .p .h) (y := j + 1 + 0)
        (by simp)).seq <|
      (lr_congr_left (layerTable (Ka := Ka) (U := U) hQ ds)
        (lr_weaken (layerTable (Ka := Ka) (U := U) hQ ds) hr rfl le_rfl) ?_).seq <|
      sgU_clear (layerTable (Ka := Ka) (U := U) hQ ds) (a := .p .h) (x := j)
        (by simp [synSetH])) ?_ ?_
    · refine congrArg (synG _) ?_
      simp only [synSetH, Function.update_idem]
      congr 1
    · refine congrArg (synG _) ?_
      simp only [synSetH, Function.update_idem]
      funext y
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    · have := synLayerStepCost_mono ds es ℓ K w l j hst
      omega
  have hscan := layScan_exec (body := layerTable (Ka := Ka) (U := U) hQ ds)
    (sreg_injective.ne (by decide : SynW.p .c ≠ .p .t)) Φ cs _ hstep
  rw [hvc] at hscan
  refine lr_weaken (layerTable (Ka := Ka) (U := U) hQ ds) (lr_congr_left _ hscan ?_) ?_ ?_
  · simp only [Φ, synG_update, oppRoundsC, ← hvt]
    rw [hcs, Function.update_eq_self, Function.update_eq_self]
  · simp only [Φ, synG_update, ← hvt]
    rw [hcs, Function.update_eq_self, Function.update_eq_self]
  · simp only [synLoopOCost]
    omega

end LoopRuns

/-! ### The transforms -/

section Transforms

variable {Q Ka : ℕ} {U : Type}

theorem rpGrid_apply (p : ℕ) {r : ℕ} (Z : ℕ → Fin r → GaussianInt) (n : ℕ) (c : Fin r) :
    rpGrid p Z n c = GaussianInt.toComplex (Z n c) / 2 ^ p := by
  rw [two_pow_complex]
  apply Complex.ext
  · rw [toComplex_div_re]; rfl
  · rw [toComplex_div_im]; rfl

theorem rpGrid_grid (p : ℕ) {r : ℕ} (Z : ℕ → Fin r → GaussianInt) : GridR p (rpGrid p Z) :=
  fun n c => ⟨(Z n c).re, (Z n c).im, rfl⟩

theorem synYnum_rpGrid {N p : ℕ} (L : Equiv.Perm (Fin N)) {r : ℕ} (Z : ℕ → Fin r → GaussianInt) :
    synYnum p L (rpGrid p Z) = fun m c => Z (synPi L m) c := by
  funext m c
  simp only [synYnum]
  rw [rpGrid_apply, numer_grid]

/-- The forward transform: the layout program `layP` (records into the physical order of the
layout), then the loop of forward rounds. -/
noncomputable def synFwd (ds : ComplexFramedExecution.Directions)
    (layP : Pr LProc (nT SXReg) Q (prime + Ka) U) : Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq layP (synLoopF ds)

/-- The opposite transform: the loop of opposite rounds, then the program `layQ` (records back
into the natural order). -/
noncomputable def synOpp (ds : ComplexFramedExecution.Directions)
    (layQ : Pr LProc (nT SXReg) Q (prime + Ka) U) : Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq (synLoopO ds) layQ

/-- The precondition of the transforms: empty left stacks, and every register other than `io`
as in the file `synG (synIdle [] P₀) v₀` for some contents `P₀` of `park` with `Pk P₀`. -/
def synPre {A : ℕ} (Pk : List (Fin (A + 4)) → Prop) (v₀ : SynW → List (Fin (A + 4)))
    (S : Stacks (nT SXReg) A) : Prop :=
  (∀ y, S.L y = []) ∧ ∃ P₀, Pk P₀ ∧ ∀ k, k ≠ lreg .io → S.R k = synG (synIdle [] P₀) v₀ k

theorem synPre_R {A : ℕ} {Pk : List (Fin (A + 4)) → Prop} {v₀ : SynW → List (Fin (A + 4))}
    {S : Stacks (nT SXReg) A} (h : synPre Pk v₀ S) :
    ∃ P₀, Pk P₀ ∧ S.R = synG (synIdle (S.R (lreg .io)) P₀) v₀ := by
  obtain ⟨-, P₀, hPk, hP⟩ := h
  refine ⟨P₀, hPk, funext fun k => ?_⟩
  by_cases hk : k = lreg .io
  · subst hk
    rw [synG_of_ne (lreg_out (by simp))]
    simp [synIdle, lreg]
  · rw [hP k hk]
    by_cases hw : ∃ x, sreg x = k
    · obtain ⟨x, rfl⟩ := hw
      simp
    · rw [synG_of_ne (fun x hx => hw ⟨x, hx⟩), synG_of_ne (fun x hx => hw ⟨x, hx⟩)]
      simp [synIdle, Function.update_apply, hk]

theorem nRounds_le {d : ℕ} {a : Fin d → ℕ} {ℓ K : ℕ} (H : LayHyp (List.ofFn a) ℓ K) :
    nRounds a ≤ ℓ := by
  apply Finset.sup_le
  intro i _
  have := H.widths (a i) (by simp)
  have := H.ℓ_ge
  omega

variable (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
  (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
  (hA : 14 ≤ prime + Ka) (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
  (hgate : ∀ g, Instr.gate g ∈ program ds →
    (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
include hd hA hA9 hNW hgate

/-- **The forward synthetic transform** in the form `SynFwdSpec` of the convolution stage. -/
theorem synFwd_spec {d : ℕ} (a : Fin d → ℕ) {ℓ K l w p : ℕ}
    (H : LayHyp (List.ofFn a) ℓ K) (hAl : nRounds a ≤ l + 1) (hpw : p + 2 ≤ w)
    (v₀ : SynW → List (Fin (prime + Ka + 4)))
    (hv₀ : SynV v₀ (List.ofFn a) ℓ K w l 0 (layPerm (List.ofFn a) ℓ K))
    (hvh : v₀ (.p .h) = []) (hvt : v₀ (.p .t) = []) (hvc : (v₀ (.p .c)).length = nRounds a)
    (hcb : blank ∉ v₀ (.p .c))
    (Pk : List (Fin (prime + Ka + 4)) → Prop)
    (layP : Pr LProc (nT SXReg) Q (prime + Ka) U) (cL : ℕ)
    (hLay : ∀ (P₀ : List (Fin (prime + Ka + 4))), Pk P₀ → ∀ (Z : ℕ → Fin (2 ^ l) → GaussianInt),
      LayRuns (layerTable (Ka := Ka) (U := U) hQ ds) layP
        (synG (synIdle (cstream (prime + Ka) w (rpStream (cvM a) Z)) P₀) v₀)
        (synG (synIdle (cstream (prime + Ka) w (rpStream (cvM a)
          (fun m => Z (synPi (layPerm (List.ofFn a) ℓ K) m)))) P₀) v₀) cL) :
    SynFwdSpec (layerTable (Ka := Ka) (U := U) hQ ds) (synFwd ds layP) (lreg .io) (synPre Pk v₀)
      w p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (cL + synLoopFCost ds (List.ofFn a) ℓ K w l (nRounds a)
        (synStashCostW v₀ synXS + 6 * nRounds a + 6)) := by
  intro Z vv S hPre hdisk hio
  obtain ⟨P₀, hPk, hR⟩ := synPre_R hPre
  rw [hio] at hR
  have hloop := sg_synLoopF (U := U) hQ ds hd hA hA9 hNW hgate H (nRounds_le H) hAl hpw v₀ hv₀
    hvh hvt hvc hcb P₀ (rpGrid p Z) hdisk (rpGrid_grid p Z)
  rw [synYnum_rpGrid] at hloop
  obtain ⟨v', n, hu, hn, he⟩ := (hLay P₀ hPk Z).seq hloop vv S hPre.1 hR
  refine ⟨v', n, hu, hn, Exec.cast he rfl ?_⟩
  congr 2
  rw [hR, synG_update_out (lreg_out (by simp)), synIdle_update_io]
  rfl

/-- **The opposite synthetic transform** in the form `SynOppSpec` of the convolution stage. -/
theorem synOpp_spec {d : ℕ} (a : Fin d → ℕ) {ℓ K l w p : ℕ}
    (H : LayHyp (List.ofFn a) ℓ K) (hAl : nRounds a ≤ l + 1) (hpw : p + 2 ≤ w)
    (v₀ : SynW → List (Fin (prime + Ka + 4)))
    (hv₀ : SynV v₀ (List.ofFn a) ℓ K w l 0 (layPerm (List.ofFn a) ℓ K))
    (hvh : v₀ (.p .h) = []) (hvt : v₀ (.p .t) = []) (hvc : (v₀ (.p .c)).length = nRounds a)
    (hcb : blank ∉ v₀ (.p .c))
    (Pk : List (Fin (prime + Ka + 4)) → Prop)
    (layQ : Pr LProc (nT SXReg) Q (prime + Ka) U) (cL : ℕ)
    (hLay : ∀ (P₀ : List (Fin (prime + Ka + 4))), Pk P₀ → ∀ (Y : ℕ → Fin (2 ^ l) → GaussianInt),
      LayRuns (layerTable (Ka := Ka) (U := U) hQ ds) layQ
        (synG (synIdle (cstream (prime + Ka) w (rpStream (cvM a) Y)) P₀) v₀)
        (synG (synIdle (cstream (prime + Ka) w (rpStream (cvM a)
          (fun x => Y ((layRec (layPerm (List.ofFn a) ℓ K)) ⟨x % 2 ^ (List.ofFn a).sum,
            Nat.mod_lt _ (by positivity)⟩)))) P₀) v₀) cL) :
    SynOppSpec (layerTable (Ka := Ka) (U := U) hQ ds) (synOpp ds layQ) (lreg .io) (synPre Pk v₀)
      w p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (synLoopOCost ds (List.ofFn a) ℓ K w l (nRounds a)
        (synStashCostW v₀ synXS + 6 * nRounds a + 6) + cL) := by
  intro V vv S hPre hdisk hio
  obtain ⟨P₀, hPk, hR⟩ := synPre_R hPre
  rw [hio] at hR
  set L := layPerm (List.ofFn a) ℓ K with hL
  have hloop := sg_synLoopO (U := U) hQ ds hd hA hA9 hNW hgate H (nRounds_le H) hAl hpw v₀ hv₀
    hvh hvt hvc hcb P₀ (rpGrid p V) hdisk (rpGrid_grid p V)
  rw [synYnum_rpGrid] at hloop
  obtain ⟨v', n, hu, hn, he⟩ := hloop.seq (hLay P₀ hPk _) vv S hPre.1 hR
  refine ⟨v', n, hu, hn, Exec.cast he rfl ?_⟩
  congr 2
  rw [hR, synG_update_out (lreg_out (by simp)), synIdle_update_io]
  congr 3
  refine rpStream_congr fun x hx => ?_
  funext c
  simp only [synYnum, cvOppOut, cvNum]
  have hpi : synPi L ((layRec L) ⟨x % 2 ^ (List.ofFn a).sum, Nat.mod_lt _ (by positivity)⟩) = x := by
    rw [synPi_layRec, Equiv.symm_apply_apply]
    simp [Nat.mod_eq_of_lt hx]
  rw [hpi]

end Transforms

/-! ### The fixed directions and the address bound

The programs `synFwd Cost.brDirs layP` and `synOpp Cost.brDirs layQ` are single fixed texts: the
sizes `p, ℓ, K, b, D, Lg, N, w, r, l`, the axis list `topRec es`, the positions `twPosReg` and the
round counter come from registers.

**Cost.** In `synLoopFCost`/`synLoopOCost`, round `h` costs `synRoundCost = synLayerStepCost +
synTwCost` plus `O(h)` loop bookkeeping. Against the transform part
`T p (d K + p K^{τ-1} + ℓ d^{λ'})` of `Cost.totConv` (paper eq. `synthetic-transform-cost`):
* `d K`: the rounds on prefix slots (`h = ℓ - 1` on the long axes and `h < b`, `synSel_top`,
  `synSel_low`), whose `synLayerCost` is `topCost` on top kernels of one bit, and the prefix
  moves of the layout inside `cL`;
* `p K^{τ-1}`: the chunk exchanges of the layout, inside `cL` (the hypothesis `hLay`);
* `ℓ d^{λ'}`: the chunk rounds (`synChunk`, `synSel_chunk`), whose `synLayerCost` is `topCost`
  with `q₀ = min (46 J) D` top kernels (`synQK`, `J = ⌊log_m D⌋`; the kernel stage costs
  `O(q₀ · V')`, `leafCost` being linear in the leaf bits) and the pieces `synPcsR` of the
  remaining `D' = D - q₀` bits on `R₂ = 2^X NW^J'` rows with `2^a' ≤ R₂ < 2^(a' + 1)`
  (`synR2c_ge`, `synR2c_lt`): the padded volume `V' = R₂ 2^(N - a') 2^l w'` is below
  `2 · 2^N 2^l w'`; the twiddle passes (`synTwCost`, `twPassLCost` on `2^N` records, `O(T p)` per
  round) and the per-round records, rest setup and parking (`synRecCost`, `synRestUpCost`,
  `synRestDownCost`, `stk`, all polynomial in `p` and `2^N`) are of lower order in the same `ℓ`
  rounds.
The factor `grLogLog (r p)` of `totConv` is the ring product of the convolution stage; the
transforms have no part in it. -/

/-- The layout addresses stay below `cvM a` (the hypothesis `hπ` of `cvSynth_runs`). -/
theorem synPi_cvM {d : ℕ} (a : Fin d → ℕ) (ℓ K : ℕ) :
    ∀ n < cvM a, synPi (layPerm (List.ofFn a) ℓ K) n < cvM a :=
  fun n _ => synPi_lt _ n

section Fixed

variable {Q Ka : ℕ} {U : Type} (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
  (hA : 14 ≤ prime + Ka) (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
  (hgate : ∀ g, Instr.gate g ∈ program Cost.brDirs →
    (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
include hA hA9 hNW hgate

/-- `synFwd_spec` at the fixed directions `Cost.brDirs`. -/
theorem synFwd_spec_br {d : ℕ} (a : Fin d → ℕ) {ℓ K l w p : ℕ}
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
    SynFwdSpec (layerTable (Ka := Ka) (U := U) hQ Cost.brDirs) (synFwd Cost.brDirs layP)
      (lreg .io) (synPre Pk v₀) w p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (cL + synLoopFCost Cost.brDirs (List.ofFn a) ℓ K w l (nRounds a)
        (synStashCostW v₀ synXS + 6 * nRounds a + 6)) :=
  synFwd_spec hQ Cost.brDirs Cost.br_directions_realizes hA hA9 hNW hgate a H hAl hpw v₀ hv₀
    hvh hvt hvc hcb Pk layP cL hLay

/-- `synOpp_spec` at the fixed directions `Cost.brDirs`. -/
theorem synOpp_spec_br {d : ℕ} (a : Fin d → ℕ) {ℓ K l w p : ℕ}
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
    SynOppSpec (layerTable (Ka := Ka) (U := U) hQ Cost.brDirs) (synOpp Cost.brDirs layQ)
      (lreg .io) (synPre Pk v₀) w p l a (synPi (layPerm (List.ofFn a) ℓ K))
      (synLoopOCost Cost.brDirs (List.ofFn a) ℓ K w l (nRounds a)
        (synStashCostW v₀ synXS + 6 * nRounds a + 6) + cL) :=
  synOpp_spec hQ Cost.brDirs Cost.br_directions_realizes hA hA9 hNW hgate a H hAl hpw v₀ hv₀
    hvh hvt hvc hcb Pk layQ cL hLay

end Fixed

end IntegerMultBounds.MathlibTM2.Fast
