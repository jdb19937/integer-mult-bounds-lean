module

public import IntegerMultBounds.MathlibTM2.Node.CompactBasisRegisters
public import IntegerMultBounds.MathlibTM2.Node.Factor

/-! Compact basis contract at the factor's post-division boundary. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape (Shape)
noncomputable section
variable {Q Ka : ℕ} {U P : Type} {shape : Shape}

/-- Exact basis budget, including parent-length setup and all cleanup. -/
def compactFactorBasisCost {n a₀ k ρ left right R : ℕ}
    (layout : CompactRecursiveLayout shape n a₀ k ρ left right)
    (hG : 1 ≤ shape.guard) (hGK : shape.guard+1 ≤ shape.chunk) (hR : 0<R)
    (hrecord : shape.bits+1 ≤ shape.payload) (D : ℕ)
    (hp : ∀ x y (hxy : x≠y),1<k → ActivePrefixStageRuntimeData.Packed
      (compactSlotComputedInputs layout x y hxy R hG hGK hR hrecord) D)
    (T Ka o r w : ℕ) (vv : BinaryWalsh.Address m) (x : Fin m) :=
  ((basisTargets vv x).map (compactBasisTargetCost layout x hG hGK hR hrecord D (hp x) T Ka o r w)).sum+1

theorem compactBasisW_factor_exec (body : P → Pr P (nT CompactBReg) Q (prime+Ka) U)
    (hQ : compactRuntimeStates ≤ Q) (hA : 4 ≤ prime+Ka)
    {n a₀ k ρ left right o R r w : ℕ}
    (layout : CompactRecursiveLayout shape n a₀ k ρ left right)
    (hG : 1 ≤ shape.guard) (hGK : shape.guard+1 ≤ shape.chunk) (hR : 0<R)
    (hrecord : shape.bits+1 ≤ shape.payload) (hpayload : shape.payload=2^o*(3*(r*w))) (D : ℕ)
    (hp : ∀ x y (hxy : x≠y),1<k → ActivePrefixStageRuntimeData.Packed
      (compactSlotComputedInputs layout x y hxy R hG hGK hR hrecord) D)
    {e : Fin (m*k) → Fin (o+n)}
    (he : ∀ i,(e i).val=(o+a₀)+ρ+shape.chunk*i.val)
    (fw : NWire) (vv : BinaryWalsh.Address m) (x : Fin m) (hv : vv x=1)
    (Z : ZArr (Fin R × Fin r) (o+n)) (v : HS (nT CompactBReg) Q (prime+Ka) U)
    (S : Stacks (nT CompactBReg) (prime+Ka)) (hL : ∀ z,S.L z=[])
    (hstream : S.R (reg (.wire fw))=encZ (prime+Ka) w Z)
    (hK : (S.R (reg .K)).length=shape.chunk) (hρ : (S.R (reg .ρ)).length=ρ)
    (ha : (S.R (reg .a₀)).length=o+a₀) (hLen : (S.R (reg .L)).length=shape.chunk*k)
    (hrows : (S.R (reg .rows)).length=R) (hn : (S.R (reg .n)).length=o+n)
    (hrw : (S.R (reg .rw)).length=r*w) (hw : (S.R (reg .w)).length=w)
    (hbc : ∀ z,compactBasisRest shape o r z (S.R (reg (.bc z)))) (htmp : S.R (reg .tmp)=[]) :
    ∃ v' c,v'.user=v.user ∧
      c ≤ compactFactorBasisCost layout hG hGK hR hrecord D hp (nT CompactBReg) Ka o r w vv x ∧
      Exec body (compactBasisW hQ fw vv x) (mk v S) c
        (mk v' {S with R:=Function.update S.R (reg (.wire fw)) (encZ (prime+Ka) w (pullM e (basisMap vv x) Z))}) := by
  have hpar : ParState S.R (S.R (reg .lev)).length (S.R (reg .u)).length
      shape.chunk ρ (o+a₀) (shape.chunk*k) R (o+n) w (r*w) := by
    intro z
    cases z <;> first | exact trivial | exact rfl | assumption
  have heq : compactOffsetEmbedding o (compactRecursiveBits layout)=e := by
    funext i
    apply Fin.ext
    rw [compactOffsetEmbedding_reserved_val,he]
  obtain ⟨v',c,hu,hc,hex⟩ := compactBasisW_exec body hQ layout x hG hGK hR hrecord hA
    hpayload D (hp x) fw vv hv Z v S hL hpar hbc htmp hstream
  rw [heq] at hex
  exact ⟨v',c,hu,hc,hex⟩

end
end IntegerMultBounds.MathlibTM2.LayerMachine
