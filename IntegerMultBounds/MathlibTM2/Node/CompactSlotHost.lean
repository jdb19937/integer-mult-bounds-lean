module

public import IntegerMultBounds.MathlibTM2.Node.CompactLayout

/-!
# The compact slot XOR on an array

`cxSlot_exec`: with the registers of the compact selected-bit XOR set up for the numbers `d`
(`CxData`), `cxCore` turns the stream of an array `Z` (rows of `2^n` addresses, records of
`B` symbols) into the stream of `pullAddr (sxMap e x y) Z`, where `e` places column `c` of slot
`j` at address bit `a₀ + ρ + K (j k + c)`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.MathlibTM2.Layer (ZArr encZ recList addrNum pullAddr bitIdx m)
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {T Q K : ℕ} {U : Type} {P : Type} {ι : CxReg → Fin T}
  {bank : Fin 2 → Fin (swapT 6) → Fin T}

/-- The inverse of the target permutation acts on the address as the slot XOR. -/
lemma cxPerm_symm_val {d : CxData} (hd : d.OK) {e : Fin (m * d.k) → Fin d.n}
    (he : Function.Injective e) (heval : ∀ i, (e i : ℕ) = d.a₀ + d.ρ + d.K * i)
    (j : Fin (d.R * 2 ^ d.n)) :
    ((cxPerm d.par (R := d.R) hd.valid hd.touched_le).symm j : ℕ) =
      2 ^ d.n * (j / 2 ^ d.n) + addrNum (sxMap e d.x d.y) (j % 2 ^ d.n) := by
  have hX := hd.valid.xorFields
  have hK : 0 < d.par.K := by have := hd.ρK; unfold CxData.par; simp only; omega
  have hval : ((cxPerm d.par (R := d.R) hd.valid hd.touched_le).symm j : ℕ) =
      xorIdx d.lens d.fields (Layer.CompactMasks.maskVal d.par.n (posS d.par))
        (xorIdx d.lens d.fields (2 ^ posS d.par d.par.n) j) := rfl
  rw [hval, xorIdx_comp hX, Nat.xor_comm, maskVal_xor_top hK]
  refine xorIdx_sxMap e he d.x d.y hK (by have := hd.k1; unfold CxData.par; simp only; omega)
    (fun c => ?_) (fun c => ?_) hd.valid (by have := hd.ρK; unfold CxData.par; simp only; omega)
    (hd.touched_le _ (Or.inr (Or.inr (Or.inr rfl)))) j
  · rw [heval, show ((bitIdx d.y c : Fin (m * d.k)) : ℕ) = d.y * d.k + c by
      simp [bitIdx, finProdFinEquiv]; ring]
    exact (hd.slot_bits c).1
  · rw [heval, show ((bitIdx d.x c : Fin (m * d.k)) : ℕ) = d.x * d.k + c by
      simp [bitIdx, finProdFinEquiv]; ring]
    exact (hd.slot_bits c).2

variable (body : P → Pr P T Q (prime + K) U) (ι) in
/-- **The compact slot XOR on an array.** -/
theorem cxSlot_exec {d : CxData} (hd : d.OK) {r w : ℕ} (hB : d.B = r * w)
    (Z : ZArr (Fin d.R × Fin r) d.n) {e : Fin (m * d.k) → Fin d.n} (he : Function.Injective e)
    (heval : ∀ i, (e i : ℕ) = d.a₀ + d.ρ + d.K * i)
    (hι : Function.Injective ι) (hb : Banks ι bank) (hA : 4 ≤ prime + K)
    (hQ : swapStates cxHd cxPay cxHd_inj ≤ Q) (hT : swapT 6 ≤ T)
    (hs : Fin 2 → Fin 5 → List Bool)
    (hv : ∀ c k, Counter.value (hs c k) = swapValues
      (swapDimsIdx (len := d.lens) d.fields.b (swapFld d.fields c) d.par.wc d.R d.n
        (d.n + d.rb + d.B)).1
      (swapDimsIdx (len := d.lens) d.fields.b (swapFld d.fields c) d.par.wc d.R d.n
        (d.n + d.rb + d.B)).2.1
      (swapDimsIdx (len := d.lens) d.fields.b (swapFld d.fields c) d.par.wc d.R d.n
        (d.n + d.rb + d.B)).2.2 d.par.wc d.par.wc k)
    (hc : ∀ c k, GrowingCounterData.Canonical (hs c k))
    (S₀ : Stacks T (prime + K))
    (hS : PassState ι bank d.par d.lens (d.n + d.rb + d.B) (d.R * 2 ^ d.n) hs S₀)
    (hctrB : (S₀.R (ι .ctrB)).length = d.B) (hctrK : (S₀.R (ι .ctrK)).length = d.n + d.rb)
    (hkt : ∀ i, S₀.R (ι (.kt i)) = []) (hfr : ∀ i, S₀.R (ι (.fr i)) = [])
    (hfq : ∀ i, S₀.R (ι (.fq i)) = []) (v : HS T Q (prime + K) U) :
    ∃ (v' : HS T Q (prime + K) U) (m' : ℕ), v'.user = v.user ∧
      (m' : ℝ) ≤ cxCoreCost d.par d.lens d.fields T d.R d.n d.B
        (fun c => ∑ j, (S₀.R (bank c j)).length) ∧
      Exec body (cxCore ι d.fields hA hb hQ hT)
        (mk v { S₀ with R := Function.update S₀.R (ι .src) (encZ (prime + K) w Z) }) m'
        (mk v' { S₀ with
          R := Function.update S₀.R (ι .src) (encZ (prime + K) w (pullAddr (sxMap e d.x d.y) Z)) })
      := by
  have hK : 0 < d.par.K := by have := hd.ρK; unfold CxData.par; simp only; omega
  have hfl := hd.offs.2.2.2.2.2
  obtain ⟨hlen, hrec, h8⟩ := sx_recSyms_facts (w := w) hA Z
  set l := (recList w Z).map (IntegerMultBounds.MathlibTM2.Layer.recSyms (prime + K) w)
  have hMk : d.R * 2 ^ d.n ≤ 2 ^ fieldsLen d.lens := by
    rw [hfl, Nat.pow_add, Nat.mul_comm (2 ^ d.n)]
    exact Nat.mul_le_mul_right _ (lt_two_pow_length_sxBits d.R).le
  rw [← hfl] at hv hS hctrK
  obtain ⟨v', m', hu, hm, he'⟩ := cxCore_exec body ι d.fields hι hd.valid CxData.order hb hK
    (by unfold CxData.par; exact hd.G0) (by unfold CxData.par; exact hd.GK)
    (by have := hd.ρK; unfold CxData.par; simp only; omega) hA hQ hT hd.R0 hd.touched_le hMk
    (B := d.B) hd.B1 hs hv hc S₀ hS hctrB hctrK hkt hfr hfq l hlen
    (fun x hx => ⟨by rw [hrec x hx, hB], h8 x hx⟩) v
  refine ⟨v', m', hu, hm, ?_⟩
  rw [moveRecs_pullAddr (sxMap e d.x d.y) _ (cxPerm_symm_val hd he heval) Z] at he'
  rw [sx_encZ_eq_flatten]
  exact he'

end IntegerMultBounds.MathlibTM2.Node
