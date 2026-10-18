module

public import IntegerMultBounds.Networks.Certificates.T16.Impl.Adapter
public import IntegerMultBounds.Networks.Certificates.T16.Impl.Chart

/-! The operator algebra of one register through a chart. A frame over a port basis, read
through an orthogonal chart, splits as a lifted nine-bit kernel list after an exterior kernel
product (`ChartSplit`). If two frames split with the same exterior part, the change between
them is the chart conjugate of the change between their lists. A register whose word frames
are wrapped by the pre- and post-adapters of its lists therefore realizes exactly the change of
frame, and two registers through the same chart combine as the word combines them. -/
@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.T16.Impl

open BinaryWalsh BinaryPhase Streams Pauli Multiplicative

/-- `lift9` as a monoid homomorphism. -/
noncomputable def lift9Hom : Module.End ℂ (Arrays 9) →* Module.End ℂ (Arrays 73) where
  toFun := lift9
  map_one' := LinearMap.ext lift9_id
  map_mul' T S := (LinearMap.ext fun f => lift9_comp T S f).symm

@[simp] theorem lift9Hom_apply (T : Module.End ℂ (Arrays 9)) : lift9Hom T = lift9 T := rfl

theorem permOp_mul_symm (χ : Addr ≃ₗ[ZMod 2] Addr) : permOp χ * permOp χ.symm = 1 := by
  apply LinearMap.ext
  intro f
  funext x
  simp [permOp_apply]

theorem permOp_symm_mul (χ : Addr ≃ₗ[ZMod 2] Addr) : permOp χ.symm * permOp χ = 1 := by
  apply LinearMap.ext
  intro f
  funext x
  simp [permOp_apply]

/-- A frame `f` over `B`, read through the chart `χ`: a lifted local list after an exterior
kernel product. -/
structure ChartSplit (χ : Addr ≃ₗ[ZMod 2] Addr) (B : Fin 73 → Addr) (f : Fin 73 → ZMod 4) where
  gs : List (ZMod 4 × Address 9)
  ext : Fin 73 → ZMod 4
  split : permOp χ.symm * basisOp B (ofAdd f) =
    lift9 (kernelList gs) * basisOp (fun k => χ.symm (B k)) (ofAdd ext) * permOp χ.symm
  exterior : ∀ k, ext k ≠ 0 → lowPart (χ.symm (B k)) = 0

/-- The exact nine-bit operator of a split's list. -/
noncomputable def ChartSplit.local {χ : Addr ≃ₗ[ZMod 2] Addr} {B : Fin 73 → Addr}
    {f : Fin 73 → ZMod 4} (s : ChartSplit χ B f) : Arrays 9 ≃ₗ[ℂ] Arrays 9 :=
  (kernelListRealization s.gs).scalar

theorem ChartSplit.local_toLinearMap {χ : Addr ≃ₗ[ZMod 2] Addr} {B : Fin 73 → Addr}
    {f : Fin 73 → ZMod 4} (s : ChartSplit χ B f) : s.local.toLinearMap = kernelList s.gs :=
  LinearMap.ext fun g => kernelListRealization_scalar s.gs g

theorem lift9_equiv_mul_symm (T : Arrays 9 ≃ₗ[ℂ] Arrays 9) :
    lift9 T.toLinearMap * lift9 T.symm.toLinearMap = 1 := by
  rw [← lift9Hom_apply, ← lift9Hom_apply, ← map_mul,
    show T.toLinearMap * T.symm.toLinearMap = 1 from by ext f; simp, map_one]

theorem lift9_equiv_symm_mul (T : Arrays 9 ≃ₗ[ℂ] Arrays 9) :
    lift9 T.symm.toLinearMap * lift9 T.toLinearMap = 1 := by
  rw [← lift9Hom_apply, ← lift9Hom_apply, ← map_mul,
    show T.symm.toLinearMap * T.toLinearMap = 1 from by ext f; simp, map_one]

theorem exterior_commute (χ : Addr ≃ₗ[ZMod 2] Addr) (B : Fin 73 → Addr)
    (T : Arrays 9 →ₗ[ℂ] Arrays 9) (c : Fin 73 → ZMod 4)
    (hc : ∀ k, c k ≠ 0 → lowPart (χ.symm (B k)) = 0) :
    lift9 T * basisOp (fun k => χ.symm (B k)) (ofAdd c) =
      basisOp (fun k => χ.symm (B k)) (ofAdd c) * lift9 T :=
  LinearMap.ext fun g => lift9_basisOp_exterior T _ c hc g

/-- **Change of frame through a chart.** Two frames splitting with the same exterior part
change by the chart conjugate of the change of their lists. -/
theorem ChartSplit.change {χ : Addr ≃ₗ[ZMod 2] Addr} {B : Fin 73 → Addr} {f f' : Fin 73 → ZMod 4}
    (s : ChartSplit χ B f) (s' : ChartSplit χ B f') (he : s.ext = s'.ext) :
    basisOp B (ofAdd f') * basisOp B (ofAdd (-f)) =
      permOp χ * lift9 s'.local.toLinearMap * lift9 s.local.symm.toLinearMap * permOp χ.symm := by
  set V : Fin 73 → Addr := fun k => χ.symm (B k)
  set E := basisOp V (ofAdd s.ext)
  set Einv := basisOp V (ofAdd (-s.ext))
  have hE : E * Einv = 1 := by rw [← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one]
  have hf' : basisOp B (ofAdd f') = permOp χ * lift9 (kernelList s'.gs) * E * permOp χ.symm := by
    have h : permOp χ * (permOp χ.symm * basisOp B (ofAdd f')) = permOp χ *
        (lift9 (kernelList s'.gs) * basisOp (fun k => χ.symm (B k)) (ofAdd s'.ext) *
          permOp χ.symm) := congrArg _ s'.split
    rw [← mul_assoc, permOp_mul_symm, one_mul, ← he] at h
    rw [h]
    simp only [mul_assoc]
    rfl
  have hfinv : basisOp B (ofAdd (-f)) =
      permOp χ * Einv * lift9 s.local.symm.toLinearMap * permOp χ.symm := by
    -- invert the split of `f`
    have hf : basisOp B (ofAdd f) = permOp χ * lift9 (kernelList s.gs) * E * permOp χ.symm := by
      have h : permOp χ * (permOp χ.symm * basisOp B (ofAdd f)) = permOp χ *
          (lift9 (kernelList s.gs) * basisOp (fun k => χ.symm (B k)) (ofAdd s.ext) *
            permOp χ.symm) := congrArg _ s.split
      rw [← mul_assoc, permOp_mul_symm, one_mul] at h
      rw [h]
      simp only [mul_assoc]
      rfl
    have hinv : basisOp B (ofAdd (-f)) * basisOp B (ofAdd f) = 1 := by
      rw [← map_mul, ← ofAdd_add, neg_add_cancel, ofAdd_zero, map_one]
    have hcand : (permOp χ * Einv * lift9 s.local.symm.toLinearMap * permOp χ.symm) *
        basisOp B (ofAdd f) = 1 := by
      rw [hf, ← s.local_toLinearMap]
      calc permOp χ * Einv * lift9 s.local.symm.toLinearMap * permOp χ.symm *
            (permOp χ * lift9 s.local.toLinearMap * E * permOp χ.symm)
          = permOp χ * Einv * (lift9 s.local.symm.toLinearMap * (permOp χ.symm * permOp χ) *
              lift9 s.local.toLinearMap) * E * permOp χ.symm := by simp only [mul_assoc]
        _ = permOp χ * Einv * E * permOp χ.symm := by
              rw [permOp_symm_mul, mul_one, lift9_equiv_symm_mul, mul_one]
        _ = permOp χ * (Einv * E) * permOp χ.symm := by simp only [mul_assoc]
        _ = 1 := by
              rw [show Einv * E = 1 by rw [← map_mul, ← ofAdd_add, neg_add_cancel, ofAdd_zero,
                map_one], mul_one, permOp_mul_symm]
    -- left inverses agree
    have hright : basisOp B (ofAdd f) * basisOp B (ofAdd (-f)) = 1 := by
      rw [← map_mul, ← ofAdd_add, add_neg_cancel, ofAdd_zero, map_one]
    calc basisOp B (ofAdd (-f))
        = ((permOp χ * Einv * lift9 s.local.symm.toLinearMap * permOp χ.symm) *
            basisOp B (ofAdd f)) * basisOp B (ofAdd (-f)) := by rw [hcand, one_mul]
      _ = permOp χ * Einv * lift9 s.local.symm.toLinearMap * permOp χ.symm := by
            rw [mul_assoc _ (basisOp B (ofAdd f)), hright, mul_one]
  rw [hf', hfinv]
  have hc : lift9 (kernelList s'.gs) * E = E * lift9 (kernelList s'.gs) :=
    exterior_commute χ B _ _ s.exterior
  calc permOp χ * lift9 (kernelList s'.gs) * E * permOp χ.symm *
        (permOp χ * Einv * lift9 s.local.symm.toLinearMap * permOp χ.symm)
      = permOp χ * lift9 (kernelList s'.gs) * E * (permOp χ.symm * permOp χ) * Einv *
          lift9 s.local.symm.toLinearMap * permOp χ.symm := by simp only [mul_assoc]
    _ = permOp χ * lift9 (kernelList s'.gs) * (E * Einv) * lift9 s.local.symm.toLinearMap *
          permOp χ.symm := by rw [permOp_symm_mul, mul_one]; simp only [mul_assoc]
    _ = permOp χ * lift9 s'.local.toLinearMap * lift9 s.local.symm.toLinearMap *
          permOp χ.symm := by rw [hE, mul_one, s'.local_toLinearMap]

/-- The split of a frame through a chart whose pulled-back basis is local on `L` and exterior
off `L`. -/
noncomputable def ChartSplit.ofLocal (χ : Addr ≃ₗ[ZMod 2] Addr) (hχ : IsOrth χ) (B : Fin 73 → Addr)
    (f : Fin 73 → ZMod 4) (L : List (Fin 73)) (hL : L.Nodup)
    (hloc : ∀ k ∈ L, χ.symm (B k) = padLow (lowPart (χ.symm (B k))))
    (hext : ∀ k, k ∉ L → f k ≠ 0 → lowPart (χ.symm (B k)) = 0) : ChartSplit χ B f where
  gs := L.map fun k => (f k, lowPart (χ.symm (B k)))
  ext k := if k ∈ L then 0 else f k
  split := by
    apply LinearMap.ext
    intro g
    change permOp χ.symm (basisOp B (ofAdd f) g) = _
    rw [permOp_basisOp hχ.symm]
    change _ = lift9 (kernelList _) (basisOp (fun k => χ.symm (B k)) (ofAdd _) (permOp χ.symm g))
    exact basisOp_split _ f _ _ _
      (phaseExp_split _ f L hL (fun k => lowPart (χ.symm (B k))) hloc) _
  exterior k hk := by
    by_cases h : k ∈ L
    · simp [h] at hk
    · exact hext k h (by simpa [h] using hk)

theorem ChartSplit.ofLocal_gs (χ : Addr ≃ₗ[ZMod 2] Addr) (hχ : IsOrth χ) (B : Fin 73 → Addr)
    (f : Fin 73 → ZMod 4) (L : List (Fin 73)) (hL : L.Nodup) (hloc) (hext) :
    (ChartSplit.ofLocal χ hχ B f L hL hloc hext).gs = L.map fun k => (f k, lowPart (χ.symm (B k))) :=
  rfl

theorem ChartSplit.ofLocal_ext (χ : Addr ≃ₗ[ZMod 2] Addr) (hχ : IsOrth χ) (B : Fin 73 → Addr)
    (f : Fin 73 → ZMod 4) (L : List (Fin 73)) (hL : L.Nodup) (hloc) (hext) :
    (ChartSplit.ofLocal χ hχ B f L hL hloc hext).ext = fun k => if k ∈ L then 0 else f k := rfl

/-! ### Registers wrapped by adapters -/

theorem preAdapter_lift (gs : List (ZMod 4 × Address 9)) (i : ℕ) :
    lift9 (preAdapter gs i).scalar.toLinearMap =
      lift9 (nativeRealization i).scalar.toLinearMap *
        lift9 (kernelListRealization gs).scalar.symm.toLinearMap := by
  rw [← lift9Hom_apply, ← lift9Hom_apply, ← lift9Hom_apply, ← map_mul]
  rfl

theorem postAdapter_lift (gs : List (ZMod 4 × Address 9)) (i : ℕ) :
    lift9 (postAdapter gs i).scalar.toLinearMap =
      lift9 (kernelListRealization gs).scalar.toLinearMap *
        lift9 (nativeRealization i).scalar.symm.toLinearMap := by
  rw [← lift9Hom_apply, ← lift9Hom_apply, ← lift9Hom_apply, ← map_mul]
  rfl

/-- **Wrapped register.** Wrapping the word frames `a` (entry) and `b` (exit) of a register by
the adapters of the splits of `f` and `f'` realizes the change of frame from `f` to `f'`. -/
theorem wrapped_change {χ : Addr ≃ₗ[ZMod 2] Addr} {B : Fin 73 → Addr} {f f' : Fin 73 → ZMod 4}
    (s : ChartSplit χ B f) (s' : ChartSplit χ B f') (he : s.ext = s'.ext) (a b : ℕ) :
    (permOp χ * lift9 (postAdapter s'.gs b).scalar.toLinearMap) *
        lift9 (nativeRealization b).scalar.toLinearMap *
        lift9 (nativeRealization a).scalar.symm.toLinearMap *
        (lift9 (preAdapter s.gs a).scalar.toLinearMap * permOp χ.symm) =
      basisOp B (ofAdd f') * basisOp B (ofAdd (-f)) := by
  rw [s.change s' he, postAdapter_lift, preAdapter_lift]
  have e1 := lift9_equiv_symm_mul (nativeRealization b).scalar
  have e2 := lift9_equiv_symm_mul (nativeRealization a).scalar
  calc permOp χ * (lift9 (kernelListRealization s'.gs).scalar.toLinearMap *
          lift9 (nativeRealization b).scalar.symm.toLinearMap) *
        lift9 (nativeRealization b).scalar.toLinearMap *
        lift9 (nativeRealization a).scalar.symm.toLinearMap *
        (lift9 (nativeRealization a).scalar.toLinearMap *
          lift9 (kernelListRealization s.gs).scalar.symm.toLinearMap * permOp χ.symm)
      = permOp χ * lift9 (kernelListRealization s'.gs).scalar.toLinearMap *
          (lift9 (nativeRealization b).scalar.symm.toLinearMap *
            lift9 (nativeRealization b).scalar.toLinearMap) *
          (lift9 (nativeRealization a).scalar.symm.toLinearMap *
            lift9 (nativeRealization a).scalar.toLinearMap) *
          lift9 (kernelListRealization s.gs).scalar.symm.toLinearMap * permOp χ.symm := by
        simp only [mul_assoc]
    _ = _ := by rw [e1, e2, mul_one, mul_one]; rfl

end IntegerMultBounds.Networks.Certificates.T16.Impl
