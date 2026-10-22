module

public import IntegerMultBounds.MathlibTM2.Routing.SparseProfiles
public import IntegerMultBounds.MathlibTM2.Routing.SourceCoordinates

/-!
# Sparse masks and source constructors for R2

Compile an arbitrary source map preserving a complete target set into allowed R2
sources. Inactive slots read themselves, so their otherwise unused descriptors
also satisfy the actual R2 precondition. No executed metadata generation or
physical reservoir placement is asserted here.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable (p : Par) (hK : 0 < p.K)

def profileTarget (c : Fin p.n) : Fin p.wy :=
  ⟨p.ρ + c.val * p.K, by
    have hc := Nat.mul_lt_mul_of_pos_right c.isLt hK
    unfold Par.wy
    omega⟩

theorem profileTarget_injective : Function.Injective (profileTarget p hK) := by
  intro c d he
  apply Fin.ext
  have hv := congrArg Fin.val he
  change p.ρ + c.val * p.K = p.ρ + d.val * p.K at hv
  exact Nat.eq_of_mul_eq_mul_right hK (by omega)

def profileActive (targets : Finset (Fin p.wy)) (c : Fin p.n) : Bool :=
  decide (profileTarget p hK c ∈ targets)

def profileSourceCoordinate (targets : Finset (Fin p.wy)) (source : Fin p.wy → Fin p.wy)
    (c : Fin p.n) : Fin p.wy :=
  if profileTarget p hK c ∈ targets then source (profileTarget p hK c)
  else profileTarget p hK c

def profileSources {X : ℕ} (targets : Finset (Fin p.wy))
    (source : Fin p.wy → Fin p.wy) (c : Fin p.n) : SlotSource p X :=
  sourceOfY p hK (profileSourceCoordinate p hK targets source c)

theorem profileSources_allowed {X : ℕ} (targets : Finset (Fin p.wy))
    (source : Fin p.wy → Fin p.wy)
    (hsource : ∀ i ∈ targets, source i ∉ targets) (c : Fin p.n) :
    (profileSources p hK targets source c : SlotSource p X).Allowed
      (profileActive p hK targets) := by
  apply sourceOfY_allowed
  intro d hd he
  have hd' : profileTarget p hK d ∈ targets := by simpa [profileActive] using hd
  have he' : profileSourceCoordinate p hK targets source c = profileTarget p hK d :=
    Fin.ext he
  unfold profileSourceCoordinate at he'
  split_ifs at he' with hc
  · exact hsource _ hc (he' ▸ hd')
  · have hcd := profileTarget_injective p hK he'
    exact hc (hcd ▸ hd')

/-- Every active source descriptor reads the requested original coordinate. -/
theorem profileSources_physical {X : ℕ} (targets : Finset (Fin p.wy))
    (source : Fin p.wy → Fin p.wy) (c : Fin p.n)
    (hc : profileActive p hK targets c = true) (y x : ℕ) :
    (profileSources p hK targets source c : SlotSource p X).physical y x =
      y.testBit (source (profileTarget p hK c)).val := by
  have ht : profileTarget p hK c ∈ targets := by simpa [profileActive] using hc
  simp only [profileSources, sourceOfY_physical, profileSourceCoordinate, ite_eq_left ht]

/-- A complete-segment profile with prefix r and its exact remaining suffix. -/
def sparseProfileParameters (n K G r : ℕ) : Par :=
  ⟨K, r, sparseSlotCount n K r, G, (n - r) % K⟩

theorem sparseProfileParameters_width (n K G r : ℕ) (hr : r ≤ n) :
    (sparseProfileParameters n K G r).wy = n := by
  have he := Nat.mod_add_div (n - r) K
  have hs : n - r + r = n := by omega
  unfold sparseProfileParameters Par.wy sparseSlotCount
  nlinarith

/-- The concrete R2 target coordinates are exactly the complete-segment slots. -/
theorem sparseProfileParameters_target (n K G : ℕ) (hK : 0 < K) (r : Fin K)
    (hr : r.val ≤ n) (c : Fin (sparseSlotCount n K r.val)) :
    Fin.cast (sparseProfileParameters_width n K G r.val hr)
      (profileTarget (sparseProfileParameters n K G r.val) hK c) =
        sparseSlot n K hK r c := by
  apply Fin.ext
  rfl

/-- Every borrowed field fits the common reservoir allocation for all residues. -/
theorem sparseProfileParameters_borrowed (n K G r : ℕ) :
    (sparseProfileParameters n K G r).wc ≤ (n / K + 1) * G := by
  have h := Nat.mul_le_mul_right G (sparseSlotCount_le n K r)
  change sparseSlotCount n K r * G ≤ _
  nlinarith

end IntegerMultBounds.MathlibTM2.Routing
