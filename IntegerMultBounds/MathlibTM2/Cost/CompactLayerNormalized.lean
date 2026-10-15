module

public import IntegerMultBounds.MathlibTM2.Cost.CompactLayer

/-! Volume-normalized compact layer recurrence. The original leaf and the
full-address-to-payload ratio remain explicit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
noncomputable section

private theorem normalized_algebra {F C M B W R P q N : ℕ}
    (hW : 0<W) (hR : 0<R) (hP : 0<P) (hq : 0<q) :
    (((F*(M+2*B)+C*(W*(R*P*q+R*P*N)) : ℕ):ℝ)/((W*R*P*q:ℕ):ℝ)) =
      (F:ℝ)/W*((M:ℝ)/((R*P*q:ℕ):ℝ))+
      2*(F:ℝ)/W*((B:ℝ)/((R*P*q:ℕ):ℝ))+(C:ℝ)*(1+(N:ℝ)/q) := by
  have hw : (W:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hW)
  have hr : (R:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have hp : (P:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have hq' : (q:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  push_cast
  field_simp

/-- Normalize by the actual encoded coefficient volume at each recursive level. -/
def compactLayerNormalized (ds : ComplexFramedExecution.Directions)
    (u R₀ N r w : ℕ) (B : ℕ → ℕ) (j : ℕ) : ℝ :=
  (compactLayerMajorant ds u R₀ N r w B j : ℝ)/
    ((rowsAt R₀ j*2^N*(r*w) : ℕ):ℝ)

/-- Exact recursive ratio: factor count divided by row fanout. The only basis
term is the explicit levelwise compact basis budget per local wire volume. -/
theorem compactLayerNormalized_succ (ds : ComplexFramedExecution.Directions)
    (u R₀ N r w : ℕ) (B : ℕ → ℕ) (j : ℕ)
    (hR₀ : 0<R₀) (hr : 0<r) (hw : 0<w) :
    compactLayerNormalized ds u R₀ N r w B (j+1) =
      (factorCount (program ds):ℝ)/NW*compactLayerNormalized ds u R₀ N r w B j+
      2*(factorCount (program ds):ℝ)/NW*
        ((B j:ℝ)/((rowsAt R₀ j*2^N*(r*w):ℕ):ℝ))+
      (lcLin ds:ℝ)*(1+(N:ℝ)/(r*w:ℕ)) := by
  unfold compactLayerNormalized
  exact normalized_algebra (F := factorCount (program ds)) (C := lcLin ds)
    (M := compactLayerMajorant ds u R₀ N r w B j) (B := B j) (N := N) (Nat.pos_of_neZero NW) (rowsAt_pos hR₀ j)
    (pow_pos (by decide : 0<2) N) (Nat.mul_pos hr hw)

private theorem normalized_leaf_algebra {u R P q N : ℕ}
    (hR : 0<R) (hP : 0<P) (hq : 0<q) :
    (((200*u*(R*P*q+R*P*N):ℕ):ℝ)/((R*P*q:ℕ):ℝ)) =
      200*(u:ℝ)*(1+(N:ℝ)/q) := by
  have hr : (R:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have hp : (P:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hP)
  have hq' : (q:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  push_cast
  field_simp

/-- The current stopping regime retains its linear-in-u leaf contribution. -/
theorem compactLayerNormalized_zero (ds : ComplexFramedExecution.Directions)
    (u R₀ N r w : ℕ) (B : ℕ → ℕ)
    (hR₀ : 0<R₀) (hr : 0<r) (hw : 0<w) :
    compactLayerNormalized ds u R₀ N r w B 0 =
      200*(u:ℝ)*(1+(N:ℝ)/(r*w:ℕ)) :=
  normalized_leaf_algebra hR₀ (pow_pos (by decide : 0<2) N) (Nat.mul_pos hr hw)

private theorem ceil_volume_ratio (C E : ℝ) (V : ℕ) (hC : 0≤C) (hE : 0≤E) (hV : 0<V) :
    (⌈C*((3*V:ℕ):ℝ)*E⌉₊:ℝ)/(V:ℝ)≤3*C*E+1/(V:ℝ) := by
  have hv : (0:ℝ)<V := by exact_mod_cast hV
  have hc := (Nat.ceil_lt_add_one (show 0≤C*((3*V:ℕ):ℝ)*E by positivity)).le
  apply (div_le_iff₀ hv).mpr
  push_cast at hc ⊢
  rw [add_mul,div_mul_cancel₀ _ (ne_of_gt hv)]
  nlinarith only [hc]

/-- The canonical basis term per local volume depends on guard times selected
width; neither a chunk-width power nor an independent setup-cost assumption occurs. -/
theorem compactLayerBasisBound_ratio (T D : ℕ) (s : CompactGadgetReservationShape.Shape)
    (u R₀ n o r w j : ℕ) (hbits : s.bits≤n)
    (hpayload : s.payload=2^o*(3*(r*w)))
    (hR₀ : 0<R₀) (hr : 0<r) (hw : 0<w) :
    (compactLayerBasisBound T D s u R₀ n j:ℝ)/((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ) ≤
      3*compactBasisConst T D*((max 1 ((bits u j-1)*s.guard):ℕ):ℝ)^Parameters.tau+
      1/((rowsAt R₀ j*2^(o+n)*(r*w):ℕ):ℝ) := by
  have hvol : (2^(n-s.bits)*rowsAt R₀ j)*s.recordWidth=
      3*(rowsAt R₀ j*2^(o+n)*(r*w)) := by
    unfold CompactGadgetReservationShape.Shape.recordWidth
    rw [hpayload]
    have he : 2^(n-s.bits)*2^s.bits=2^n := by rw [←pow_add,Nat.sub_add_cancel hbits]
    calc
      _ = 3*rowsAt R₀ j*(2^(n-s.bits)*2^s.bits)*2^o*(r*w) := by ring
      _ = _ := by rw [he,pow_add]; ring
  unfold compactLayerBasisBound
  rw [hvol]
  exact ceil_volume_ratio _ _ _ (by unfold compactBasisConst; positivity)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Nat.mul_pos (Nat.mul_pos (rowsAt_pos hR₀ j) (pow_pos (by decide) _)) (Nat.mul_pos hr hw))

end
end IntegerMultBounds.MathlibTM2.Cost
