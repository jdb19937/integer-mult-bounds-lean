module

public import IntegerMultBounds.MathlibTM2.Node.CompactSetup

/-!
# The compact slot XOR from its unary inputs

`cxSlotRun_exec`: from a register file holding the unary inputs (`CxSetupIn`), empty setup and
bank registers, and the stream of an array `Z` in `src`, the setup (`cxSetupProg`), the core
(`cxCore`) and the cleanup (`cxCleanProg`) leave every register as it was except `src`, which
holds the stream of `pullAddr (sxMap e x y) Z`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Layer (ZArr encZ pullAddr m)
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {T Q K : ℕ} {U : Type} {P : Type} {ι : CxReg → Fin T}
  {bank : Fin 2 → Fin (swapT 6) → Fin T} {inp : Fin 12 → Fin T}

/-- The program of the compact slot XOR. -/
noncomputable def cxSlotProg (d : CxData) (hA : 4 ≤ prime + K) (hb : Banks ι bank)
    (hQ : swapStates cxHd cxPay cxHd_inj ≤ Q) (hT : swapT 6 ≤ T) : Pr P T Q (prime + K) U :=
  .seq (cxSetupProg ι bank inp d.lo d.hi)
    (.seq (cxCore ι d.fields hA hb hQ hT) (cxCleanProg ι bank))

variable (hall : Function.Injective (cxAll ι bank inp)) (hb : Banks ι bank)
  (hbank : ∀ c c' j j', bank c j = bank c' j' → c = c')
include hall hb hbank

/-- A bank register other than a header is not a setup register. -/
lemma cx_bank_out {c : Fin 2} {j : Fin (swapT 6)} (hj : ∀ k, j ≠ reg (cxHd k)) (x : CxSet) :
    cxSetReg ι bank x ≠ bank c j := by
  rcases x with x | ⟨c', k⟩
  · exact (hb.ne c j x).symm
  · intro e
    obtain rfl := hbank _ _ _ _ e
    exact hj k (hb.inj _ e).symm

/-- After the setup the registers hold the pass state of `cxCore`. -/
lemma cxPassState {d : CxData} (hd : d.OK) {R₀ : Fin T → List (Fin (prime + K + 4))}
    (h0 : ∀ x : CxSet, x ≠ .reg .src → R₀ (cxSetReg ι bank x) = [])
    (hbank0 : ∀ c j, R₀ (bank c j) = []) (S : Stacks T (prime + K)) (hL : ∀ y, S.L y = []) :
    PassState ι bank d.par d.lens (d.n + d.rb + d.B) (d.R * 2 ^ d.n) d.hs
      { S with R := cxFile ι bank d 41 R₀ } := by
  have hle : ∀ x, cxStage x ≤ 41 := by
    rintro (x | ⟨c, k⟩)
    · cases x <;> simp only [cxStage] <;> (try split_ifs) <;> omega
    · simp only [cxStage]; omega
  have hset : ∀ x : CxReg, 1 ≤ cxStage (.reg x) → cxFile ι bank d 41 R₀ (ι x) = cxBc _ d (.reg x) :=
    fun x h1 => cxFile_set hall h1 (hle _)
  have hun : ∀ x : CxReg, x ≠ .src → cxStage (.reg x) = 0 → cxFile ι bank d 41 R₀ (ι x) = [] :=
    fun x hs hx => (cxFile_unset hall (x := .reg x) (Or.inr hx)).trans
      (h0 _ fun e => hs (CxSet.reg.inj e))
  have hout : ∀ c j, (∀ k, j ≠ reg (cxHd k)) → cxFile ι bank d 41 R₀ (bank c j) = [] :=
    fun c j hj => (stFill_out _ _ _ (cx_bank_out hall hb hbank hj)).trans (hbank0 c j)
  refine ⟨hL, ?_, ?_, hun _ (by simp) rfl, hun _ (by simp) rfl, hun _ (by simp) rfl, fun _ => hun _ (by simp) rfl, fun _ => hun _ (by simp) rfl,
    ⟨fun g => ?_, ?_, ?_, ?_, ?_, hun _ (by simp) rfl, hun _ (by simp) rfl, hun _ (by simp) rfl, hun _ (by simp) rfl, hun _ (by simp) rfl, hun _ (by simp) rfl,
      fun _ => hun _ (by simp) rfl⟩, fun c => hout c _ fun k e => ?_, fun c j hj => hout c j fun k e => ?_,
    fun c k => ?_⟩
  · simp only; rw [hset _ (by simp [cxStage])]; simp [cxBc]
  · simp only; rw [hset _ (by simp [cxStage])]; simp [cxBc]
  · show cxFile ι bank d 41 R₀ (ι (.fld g)) = _
    rw [hset _ (by simp only [cxStage]; omega)]
    simp [cxBc, digit]
  · exact hset _ (by simp [cxStage])
  · exact hset _ (by simp [cxStage])
  · exact hset _ (by simp [cxStage])
  · exact hset _ (by simp [cxStage])
  · have := congrArg Fin.val e
    simp only [reg_val, cxPay, cxHd, Fin.val_last, Fin.coe_castSucc] at this
    exact absurd this (by have := k.isLt; omega)
  · have := congrArg Fin.val e
    simp only [reg_val, cxHd, Fin.coe_castSucc] at this
    have := k.isLt
    omega
  · exact cxFile_set hall (x := .hdr c k) (by simp only [cxStage]; omega) (hle _)

variable (body : P → Pr P T Q (prime + K) U) in
/-- **The compact slot XOR from its unary inputs.** -/
theorem cxSlotRun_exec {d : CxData} (hd : d.OK) {o hB act cr cw : ℕ}
    {R₀ : Fin T → List (Fin (prime + K + 4))}
    (h0 : ∀ x : CxSet, x ≠ .reg .src → R₀ (cxSetReg ι bank x) = [])
    (hbank0 : ∀ c j, R₀ (bank c j) = []) (hin : CxSetupIn d inp R₀ o hB act cr cw)
    {r w : ℕ} (hBrw : d.B = r * w) (Z : ZArr (Fin d.R × Fin r) d.n)
    (hZ : R₀ (ι .src) = encZ (prime + K) w Z) {e : Fin (m * d.k) → Fin d.n}
    (he : Function.Injective e) (heval : ∀ i, (e i : ℕ) = d.a₀ + d.ρ + d.K * i)
    (hA : 4 ≤ prime + K) (hQ : swapStates cxHd cxPay cxHd_inj ≤ Q) (hT : swapT 6 ≤ T)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K)) (hL : ∀ y, S.L y = [])
    (hS : S.R = R₀) :
    ∃ (v' : HS T Q (prime + K) U) (m' : ℕ), v'.user = v.user ∧
      (m' : ℝ) ≤ ((41 * d.setupStep o hB act cr cw + 1 : ℕ) : ℝ) +
        cxCoreCost d.par d.lens d.fields T d.R d.n d.B
          (fun c => ∑ j, (cxFile ι bank d 41 R₀ (bank c j)).length) +
        ((41 * (2 * d.setupStep o hB act cr cw + 2) + 1 : ℕ) : ℝ) ∧
      Exec body (cxSlotProg (inp := inp) d hA hb hQ hT) (mk v S) m'
        (mk v' { S with
          R := Function.update S.R (ι .src)
            (encZ (prime + K) w (pullAddr (sxMap e d.x d.y) Z)) }) := by
  have hι : Function.Injective ι := fun x y e => CxSet.reg.inj (cxSetReg_inj' hall e)
  have hsne : ∀ x : CxSet, x ≠ .reg .src → cxSetReg ι bank x ≠ ι .src := fun x hx e =>
    hx (cxSetReg_inj' hall (e.trans rfl))
  have hun : ∀ x : CxReg, x ≠ .src → cxStage (.reg x) = 0 → cxFile ι bank d 41 R₀ (ι x) = [] :=
    fun x hs hx => (cxFile_unset hall (x := .reg x) (Or.inr hx)).trans
      (h0 _ fun e => hs (CxSet.reg.inj e))
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := cxSetup_exec body hall h0 hin hd v S hL hS
  have hsrc : cxFile ι bank d 41 R₀ (ι .src) = encZ (prime + K) w Z :=
    (cxFile_unset hall (x := .reg .src) (Or.inr rfl)).trans hZ
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := cxSlot_exec ι body hd hBrw Z he heval hι hb hA hQ hT d.hs
    (CxData.hs_value hd) (CxData.hs_canonical hd) { S with R := cxFile ι bank d 41 R₀ }
    (cxPassState hall hb hbank hd h0 hbank0 S hL)
    (by show (cxFile ι bank d 41 R₀ (cxSetReg ι bank (.reg .ctrB))).length = _
        rw [cxFile_set hall (x := .reg .ctrB) (by simp [cxStage]) (by simp [cxStage])]
        simp [cxBc])
    (by show (cxFile ι bank d 41 R₀ (cxSetReg ι bank (.reg .ctrK))).length = _
        rw [cxFile_set hall (x := .reg .ctrK) (by simp [cxStage]) (by simp [cxStage])]
        simp [cxBc])
    (fun _ => hun _ (by simp) rfl) (fun _ => hun _ (by simp) rfl) (fun _ => hun _ (by simp) rfl) v₁
  have hS1 : Function.update (cxFile ι bank d 41 R₀) (ι .src) (encZ (prime + K) w Z) =
      cxFile ι bank d 41 R₀ := by rw [← hsrc, Function.update_eq_self]
  dsimp only at he₂
  rw [hS1, cxFile_src hall] at he₂
  have h0' : ∀ x : CxSet, x ≠ .reg .src → Function.update R₀ (ι .src)
      (encZ (prime + K) w (pullAddr (sxMap e d.x d.y) Z)) (cxSetReg ι bank x) = [] :=
    fun x hx => by rw [Function.update_of_ne (hsne x hx)]; exact h0 x hx
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := cxClean_exec body hall h0' (o := o) (hB := hB) (act := act)
    (cr := cr) (cw := cw) hd v₂ { S with R := cxFile ι bank d 41 (Function.update R₀ (ι .src)
      (encZ (prime + K) w (pullAddr (sxMap e d.x d.y) Z))) } hL rfl
  refine ⟨v₃, m₁ + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · push_cast
    have h1 : (m₁ : ℝ) ≤ ((41 * d.setupStep o hB act cr cw + 1 : ℕ) : ℝ) := by exact_mod_cast hm₁
    have h3 : (m₃ : ℝ) ≤ ((41 * (2 * d.setupStep o hB act cr cw + 2) + 1 : ℕ) : ℝ) := by
      exact_mod_cast hm₃
    push_cast at h1 h3
    linarith
  · rw [hS]
    exact Exec.seq he₁ (Exec.seq he₂ he₃)

end IntegerMultBounds.MathlibTM2.Node
