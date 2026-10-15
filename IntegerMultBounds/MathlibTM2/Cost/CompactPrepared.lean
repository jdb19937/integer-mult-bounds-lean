module

public import IntegerMultBounds.MathlibTM2.Cost.CompactSlotXor
public import IntegerMultBounds.MathlibTM2.Node.CompactSlotPrepared

/-! Complete prepared compact slot-XOR cost, including conversion of all thirteen
unary descriptors and exact cleanup. Descriptor values remain runtime inputs;
the coefficient is a fixed power of two depending only on host size and repair allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData
noncomputable section

private theorem compactPrepared_volume_pos {s : Shape} (d : Inputs s) :
    1 ≤ d.rows*s.recordWidth := by
  have hp : 0<s.payload := by have := d.hrecord; omega
  exact Nat.mul_pos d.hr (by unfold Shape.recordWidth; positivity)

/-- Original unary descriptor values are bounded by the actual array volume. -/
theorem compactOriginalValues_le {s : Shape} (d : Inputs s) :
    ∀ i, ActivePrefixStageHeadersData.originalValues d.stage d.rows i ≤ d.rows*s.recordWidth := by
  have hne : d.stage.source.val ≠ d.stage.target.val := fun h => d.stage.distinct (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact (ActivePrefixStageHeadersBudget.original_bounds .early d.stage d.rows d.hG d.hGK h d.hr d.hrecord).1
  · exact (ActivePrefixStageHeadersBudget.original_bounds .late d.stage d.rows d.hG d.hGK h d.hr d.hrecord).1

/-- All thirteen conversions, including their terminating instruction, are linear in volume. -/
theorem compactPrepared_build_le {s : Shape} (d : Inputs s) :
    (∑ i : Fin 13, (16*ActivePrefixStageHeadersData.originalValues d.stage d.rows i+5))+1 ≤
      274*(d.rows*s.recordWidth) := by
  have hV := compactPrepared_volume_pos d
  have hs : (∑ i : Fin 13, (16*ActivePrefixStageHeadersData.originalValues d.stage d.rows i+5)) ≤
      ∑ _i : Fin 13, 21*(d.rows*s.recordWidth) := by
    apply Finset.sum_le_sum
    intro i _
    have hi := compactOriginalValues_le d i
    omega
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  omega

/-- Clearing the thirteen canonical binary words is also charged to the same volume. -/
theorem compactPrepared_clear_le {s : Shape} (A : ℕ) (d : Inputs s) :
    (∑ i : Fin 13, (2*(compactHeaderWord A
      (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)).length+2))+1 ≤
      105*(d.rows*s.recordWidth) := by
  have hV := compactPrepared_volume_pos d
  have hs : (∑ i : Fin 13, (2*(compactHeaderWord A
      (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)).length+2)) ≤
      ∑ _i : Fin 13, 8*(d.rows*s.recordWidth) := by
    apply Finset.sum_le_sum
    intro i _
    have hi := compactOriginalValues_le d i
    have hb := ActiveRepairRankHeadersCommands.bits_length
      (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)
    simp only [compactHeaderWord,List.length_cons,List.length_map]
    omega
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  omega

/-- A fixed power-of-two coefficient for setup, full execution and cleanup. -/
def compactPreparedConst (T D : ℕ) : ℝ := 2^(compactSlotXorExponent T D+9)

theorem compactPreparedConst_pos (T D : ℕ) : 0<compactPreparedConst T D := by
  unfold compactPreparedConst
  positivity

theorem compactPreparedConst_le (T D : ℕ) :
    compactSlotXorConst T D+379 ≤ compactPreparedConst T D := by
  have h : (1:ℝ) ≤ compactSlotXorConst T D := one_le_pow₀ (by norm_num)
  unfold compactPreparedConst
  rw [pow_add]
  norm_num
  change compactSlotXorConst T D+379 ≤ compactSlotXorConst T D*512
  nlinarith

/-- The literal prepared-program budget satisfies the compact-width envelope. -/
theorem compactSlotPreparedCost_le {s : Shape} (T K D : ℕ) (d : Inputs s)
    (hp : 1<d.stage.f → ActivePrefixStageRuntimeData.Packed d D)
    (length : ℕ) (hlength : length≤d.rows*s.recordWidth) :
    (compactSlotPreparedCost T K D d hp length : ℝ) ≤
      compactPreparedConst T D*(d.rows*s.recordWidth : ℕ)*
        ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^Parameters.tau := by
  have hb := compactSlotXorCost_le T K D d hp length hlength
  have hbuild : (((∑ i : Fin 13,(16*ActivePrefixStageHeadersData.originalValues d.stage d.rows i+5))+1 : ℕ):ℝ) ≤
      274*(d.rows*s.recordWidth : ℕ) := by exact_mod_cast compactPrepared_build_le d
  have hclear : (((∑ i : Fin 13,(2*(compactHeaderWord (prime+K)
      (ActivePrefixStageHeadersData.originalValues d.stage d.rows i)).length+2))+1 : ℕ):ℝ) ≤
      105*(d.rows*s.recordWidth : ℕ) := by exact_mod_cast compactPrepared_clear_le (prime+K) d
  have he : (1:ℝ) ≤ ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 ((d.stage.f-1)*s.guard))
      (by norm_num [Parameters.tau])
  have hm := mul_le_mul_of_nonneg_left he
    (show (0:ℝ) ≤ 379*(d.rows*s.recordWidth : ℕ) by positivity)
  have hd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (compactPreparedConst_le T D)
      (show (0:ℝ) ≤ (d.rows*s.recordWidth : ℕ) by positivity))
    (show (0:ℝ) ≤ ((max 1 ((d.stage.f-1)*s.guard) : ℕ) : ℝ)^Parameters.tau by positivity)
  unfold compactSlotPreparedCost
  push_cast at hb hbuild hclear hm hd ⊢
  nlinarith only [hb,hbuild,hclear,hm,hd]

variable {s : Shape} {T Q K : ℕ} {U F : Type}

/-- Actual preparation, encoded action and cleanup, with all runtime source facts explicit. -/
theorem compactSlotPrepared_exec_le {n a₀ k ρ left right rows R r w : ℕ}
    (body : F → Pr F T Q (prime+K) U)
    (hQ : compactRuntimeStates ≤ Q)
    (ι : Fin ActivePrefixStageRuntimeProgram.count → Fin T) (hι : Function.Injective ι)
    (hT : ActivePrefixStageRuntimeProgram.count ≤ T)
    (src : Fin 13 → Fin T) (t₁ t₂ str tmp : Fin T)
    (hsrc : ∀ i j,src i≠ι j) (hsrc₁ : ∀ i,src i≠t₁) (hsrc₂ : ∀ i,src i≠t₂)
    (hsrcstr : ∀ i,src i≠str) (hsrctmp : ∀ i,src i≠tmp)
    (h₁bank : ∀ j,ι j≠t₁) (h₂bank : ∀ j,ι j≠t₂) (h₁₂ : t₁≠t₂)
    (h₁str : t₁≠str) (h₂str : t₂≠str) (h₁tmp : t₁≠tmp) (h₂tmp : t₂≠tmp)
    (hst : str≠tmp) (hstr : ∀ j,ι j≠str) (htmp : ∀ j,ι j≠tmp)
    (layout : CompactRecursiveLayout s n a₀ k ρ left right) (x y : Fin m) (hxy : x≠y)
    (hG : 1≤s.guard) (hGK : s.guard+1≤s.chunk) (hr : 0<rows) (hrecord : s.bits+1≤s.payload)
    (hA : 4≤prime+K) (hpayload : s.payload=3*(r*w))
    (hvolume : rows*s.recordWidth=(R*2^n)*s.payload)
    (D : ℕ)
    (hp : 1<k → ActivePrefixStageRuntimeData.Packed
      (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord) D)
    (Z : ZArr (Fin R × Fin r) n)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ j,S.L (ι j)=[]) (hbank : ∀ j,S.R (ι j)=[])
    (hR : S.R str=encZ (prime+K) w Z)
    (htmp0 : S.R tmp=[]) (h₁ : S.R t₁=[]) (h₂ : S.R t₂=[])
    (hvalues : ∀ i,(S.R (src i)).length = ActivePrefixStageHeadersData.originalValues
      (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord).stage rows i) :
    ∃ v', ∃ steps : ℕ, v'.user=v.user ∧
      (steps:ℝ) ≤ compactPreparedConst T D*(rows*s.recordWidth : ℕ)*
        ((max 1 ((k-1)*s.guard) : ℕ) : ℝ)^Parameters.tau ∧
      Exec body (compactSlotPreparedProg hQ ι hι hT src t₁ t₂ str tmp) (mk v S) steps
        (mk v' {S with R:=Function.update S.R str (encZ (prime+K) w (pullM (compactRecursiveBits layout) (sxXorCol x y) Z))}) := by
  obtain ⟨v',steps,hu,hm,he⟩ := compactSlotPrepared_exec body hQ ι hι hT src t₁ t₂ str tmp
    hsrc hsrc₁ hsrc₂ hsrcstr hsrctmp h₁bank h₂bank h₁₂ h₁str h₂str h₁tmp h₂tmp hst hstr htmp
    layout x y hxy hG hGK hr hrecord hA hpayload hvolume D hp Z v S hL hbank hR htmp0 h₁ h₂ hvalues
  refine ⟨v',steps,hu,?_,he⟩
  have hlength : (encZ (prime+K) w Z).length ≤ rows*s.recordWidth := by
    have h := compactEncoding_length (w:=w) hA Z
    rw [length_toBits,←hpayload,←hvolume] at h
    omega
  exact (Nat.cast_le.mpr hm).trans
    (compactSlotPreparedCost_le T K D (compactRecursiveInputs layout x y hxy rows hG hGK hr hrecord)
      hp _ hlength)

end
end IntegerMultBounds.MathlibTM2.Cost
