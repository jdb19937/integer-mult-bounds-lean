module

public import IntegerMultBounds.MathlibTM2.Routing.ProfileCompiler
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirBudget

/-!
# One physical field geometry for every residue pass

Borrowed fields consume coordinates of the same record as the target field.
Choose the digit count using K+3G, not K, and reserve one extra K-bit terminal
segment. Then all K residues share the same three borrowed fields, and the
remaining elementary suffix is shorter than 2K+3G. No extra coordinates are added.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

def routerDigits (n K G : ℕ) : ℕ := (n - K) / (K + 3 * G)

def routerBorrowed (n K G : ℕ) : ℕ := routerDigits n K G * G

def routerTargetWidth (n K G : ℕ) : ℕ := n - 3 * routerBorrowed n K G

def routerTail (n K G : ℕ) : ℕ := routerTargetWidth n K G - routerDigits n K G * K

theorem routerGeometry_decomposition (n K G : ℕ) (hn : K ≤ n) :
    n = 3 * routerBorrowed n K G + routerDigits n K G * K + K +
      (n - K) % (K + 3 * G) := by
  have he := Nat.mod_add_div (n - K) (K + 3 * G)
  have hs := Nat.sub_add_cancel hn
  unfold routerBorrowed routerDigits
  nlinarith

theorem routerTargetWidth_eq (n K G : ℕ) (hn : K ≤ n) :
    routerTargetWidth n K G = routerDigits n K G * K + K +
      (n - K) % (K + 3 * G) := by
  have he := routerGeometry_decomposition n K G hn
  unfold routerTargetWidth
  omega

theorem routerTail_eq (n K G : ℕ) (hn : K ≤ n) :
    routerTail n K G = K + (n - K) % (K + 3 * G) := by
  unfold routerTail
  rw [routerTargetWidth_eq n K G hn]
  omega

theorem routerTail_lt (n K G : ℕ) (hK : 0 < K) (hn : K ≤ n) :
    routerTail n K G < 2 * K + 3 * G := by
  rw [routerTail_eq n K G hn]
  have hm := Nat.mod_lt (n - K) (show 0 < K + 3 * G by omega)
  omega

/-- All residues use the same digit count and physical borrowed-field widths. -/
def routerProfileParameters (n K G r : ℕ) : Par :=
  ⟨K, r, routerDigits n K G, G, routerTail n K G - r⟩

theorem routerProfileParameters_width (n K G : ℕ) (hn : K ≤ n) (r : Fin K) :
    (routerProfileParameters n K G r.val).wy = routerTargetWidth n K G := by
  have he := routerTargetWidth_eq n K G hn
  have ht := routerTail_eq n K G hn
  have hr := r.isLt
  change r.val + routerDigits n K G * K + (routerTail n K G - r.val) = _
  omega

theorem routerProfileParameters_borrowed (n K G r : ℕ) :
    (routerProfileParameters n K G r).wc = routerBorrowed n K G := rfl

/-- R2's complete field bank has exactly the original record width. -/
theorem routerProfileParameters_total (n K G : ℕ) (hn : K ≤ n) (r : Fin K) :
    3 * (routerProfileParameters n K G r.val).wc +
      (routerProfileParameters n K G r.val).wy = n := by
  rw [routerProfileParameters_width n K G hn r, routerProfileParameters_borrowed]
  have he := routerGeometry_decomposition n K G hn
  have hw := routerTargetWidth_eq n K G hn
  omega

/-- The common compact fields fit the already constructed reservoirs. -/
theorem routerBorrowed_le_reservoir (n G : ℕ) (hG : 0 < G) :
    routerBorrowed n (64 * G) G ≤ routingReservoirWidth n G := by
  have hd := Nat.div_mul_le_self (n - 64 * G) (64 * G + 3 * G)
  have hs := Nat.sub_le n (64 * G)
  have hm : routerDigits n (64 * G) G * (64 * G) ≤ n := by
    unfold routerDigits
    nlinarith
  have hq := (Nat.le_div_iff_mul_le (show 0 < 64 * G by omega)).mpr hm
  have hb := Nat.mul_le_mul_right G hq
  unfold routerBorrowed routingReservoirWidth
  nlinarith

/-- The fixed-count residue passes cover every bulk target-field coordinate. -/
theorem routerProfile_covers (n K G : ℕ) (hK : 0 < K)
    (i : Fin (routerTargetWidth n K G)) (hi : i.val < routerDigits n K G * K) :
    ∃ (r : Fin K) (c : Fin (routerDigits n K G)),
      (profileTarget (routerProfileParameters n K G r.val) hK c).val = i.val := by
  have hc := (Nat.div_lt_iff_lt_mul hK).mpr hi
  refine ⟨⟨i.val % K, Nat.mod_lt _ hK⟩, ⟨i.val / K, hc⟩, ?_⟩
  change i.val % K + i.val / K * K = i.val
  have he := Nat.mod_add_div i.val K
  nlinarith

/-- No fixed-count residue pass targets the elementary suffix. -/
theorem routerProfile_target_bulk (n K G : ℕ) (hK : 0 < K)
    (r : Fin K) (c : Fin (routerDigits n K G)) :
    (profileTarget (routerProfileParameters n K G r.val) hK c).val <
      routerDigits n K G * K := by
  have hc := Nat.mul_le_mul_right K (show c.val + 1 ≤ routerDigits n K G from c.isLt)
  have hr := r.isLt
  change r.val + c.val * K < _
  nlinarith

/-- With reservoir-compatible spacing the entire fallback has O(G) targets. -/
theorem routerTail_spacing (n G : ℕ) (hG : 0 < G) (hn : 64 * G ≤ n) :
    routerTail n (64 * G) G < 131 * G := by
  have h := routerTail_lt n (64 * G) G (by omega) hn
  omega

end IntegerMultBounds.MathlibTM2.Routing
