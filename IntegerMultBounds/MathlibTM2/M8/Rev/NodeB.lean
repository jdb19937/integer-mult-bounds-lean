module

public import IntegerMultBounds.MathlibTM2.M8.Rev.Node
public import IntegerMultBounds.MathlibTM2.M8.Rev.FramedRingB

/-! The reversed edge programs execute the actual gauged design-B node. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Rev
noncomputable section
open IntegerMultBounds IntegerMultBounds.Networks Matrix
open IntegerMultBounds.MathlibTM2.M8.Global
open IntegerMultBounds.Swap.Modular (Admissible)
open ReversedExchange (rev)
open TwistedExchange (twist)
open Classical
variable {q b : Nat} {S : Type} [CommRing S]
variable {φ : ZMod (q ^ b) →+* S} {σ : S →+* S}
variable (hσ : ∀ x, σ (σ x) = x) (hφ : ∀ c, σ (φ c) = φ c)
include hσ hφ

theorem rev_node_runB {G G' : Mat 529} (hB : Basis G G' q b)
    (hrev : Admissible (q ^ b) (rev 529 : Mat 529))
    (hedge : ∀ U ∈ edgeMats Global.DesignB.framedNode, ∀ e ∈ revNumbers (G * U * G'), e < q)
    (stored : Wire → Streams 529 S) (hz : ∀ t, stored (.inr t) = 0) (i : World) (a : Addr 529 S) :
    Step.run (twEdgeAction φ σ) (revPhysOf G G' Global.DesignB.framedNode) stored (.inl i) a =
      stored (.inl (route i)) (twist σ (revS φ *ᵥ a.2), twist σ (revS φ *ᵥ a.1)) := by
  have hL : ∀ U ∈ edgeMats Global.DesignB.framedNode, EdgeMat U ∧ ∀ e ∈ revNumbers (G * U * G'), e < q :=
    fun U hU => ⟨edgeMat_of_valid Global.DesignB.framedNode Global.DesignB.gInit tempZero Global.DesignB.isFrame_gInit Global.DesignB.valid_node U hU, hedge U hU⟩
  have h := congrFun (congrFun (rev_run hσ hφ hB hrev Global.DesignB.framedNode hL stored) (.inl i)) (Φ φ σ a)
  simp only [cΦ, Φ_involutive hσ hφ hrev a] at h
  rw [h, Global.DesignB.node_run_ring (conjInterp (φ := φ) hB) _ (fun t => by funext c; simp [cΦ, hz t])]
  simp only [cΦ, Φ]

end
end IntegerMultBounds.MathlibTM2.M8.Rev
