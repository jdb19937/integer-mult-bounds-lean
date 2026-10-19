module

import IntegerMultBounds.MathlibTM2.Fast.CompactSynSel
public import IntegerMultBounds.MathlibTM2.Node.CompactEncodingOffset
public import IntegerMultBounds.Machine.CompactGlobalRowPadding
public import IntegerMultBounds.MathlibTM2.Fast.CompactSynRecPieces
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! The runtime reservation counts determine one native shape shared by every
active digit piece and child. Capacity is explicit; subtraction is never used
to assert a reservation fits in the fallback case. Row padding is separate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.Networks
open CompactGadgetReservationCapacity
open CompactGadgetReservationShape (Shape)
noncomputable section

/-- The literal active count produced by the reserved-record arithmetic. -/
def compactReservationActive (d g K D : ℕ) : ℕ :=
  D - CompactGlobalRowPadding.rowAxes NW m d - frontChunks d g K - backChunks d g K

/-- One shape for all pieces; the payload may already contain a folded low offset. -/
def compactReservationShape (d g K D payload : ℕ) : Shape :=
  ⟨d,g,K,compactReservationActive d g K D,payload⟩

/-- Nonfallback capacity: the row, front and back reservations fit before carving active axes. -/
def CompactReservationFits (d g K D : ℕ) : Prop :=
  CompactGlobalRowPadding.rowAxes NW m d + frontChunks d g K + backChunks d g K ≤ D

theorem compactReservation_axes {d g K D : ℕ} (h : CompactReservationFits d g K D) :
    CompactGlobalRowPadding.rowAxes NW m d + frontChunks d g K +
      compactReservationActive d g K D + backChunks d g K = D := by
  unfold CompactReservationFits at h
  unfold compactReservationActive
  omega

/-- The native address contains every non-row chunk, including all dirty spectators. -/
theorem compactReservation_bits {d g K D payload : ℕ}
    (hK : 0<K) (h : CompactReservationFits d g K D) :
    (compactReservationShape d g K D payload).bits =
      K*(D-CompactGlobalRowPadding.rowAxes NW m d) := by
  rw [Shape.existing_bits _ hK]
  have he := compactReservation_axes h
  change (frontChunks d g K + compactReservationActive d g K D + backChunks d g K)*K = _
  have hh : frontChunks d g K + compactReservationActive d g K D + backChunks d g K =
      D-CompactGlobalRowPadding.rowAxes NW m d := by omega
  rw [hh,Nat.mul_comm]

theorem compactReservation_back (d g K D payload : ℕ) (hK : 0<K) :
    (compactReservationShape d g K D payload).H +
      (compactReservationShape d g K D payload).B = K*backChunks d g K := by
  simpa only [compactReservationShape,Shape.H,Shape.B,Nat.mul_comm] using back_exact d g K hK

/-- Any whole node interval in the active region gets the same front and back reservation. -/
theorem compactReservationLayout {d g K D payload ρ t k : ℕ}
    (hK : 0<K) (h : CompactReservationFits d g K D)
    (hρ : ρ<K) (hk : 0<k) (hkd : k≤d)
    (hinterval : t+m*k ≤ compactReservationActive d g K D) :
    CompactRecursiveLayout (compactReservationShape d g K D payload)
      (K*(D-CompactGlobalRowPadding.rowAxes NW m d)) (K*backChunks d g K+K*t) k ρ
      (compactReservationActive d g K D-t-m*k) t where
  active := by change compactReservationActive d g K D = _; omega
  positiveWidth := hk
  widthFits := hkd
  selectedFits := hρ
  lowReserve := by
    rw [compactReservation_back _ _ _ _ _ hK]
    change K*backChunks d g K+K*t=K*backChunks d g K+t*K
    ring
  totalFits := (compactReservation_bits hK h).le

/-- Descending into any slot reuses the same shape and shifts only active spectators. -/
theorem compactReservationChildLayout {d g K D payload ρ t k k' : ℕ}
    (hK : 0<K) (h : CompactReservationFits d g K D)
    (hρ : ρ<K) (hkd : k≤d)
    (hinterval : t+m*k ≤ compactReservationActive d g K D)
    (p : Fin m) (hk' : 0<k') (hdivide : m*k'=k) :
    CompactRecursiveLayout (compactReservationShape d g K D payload)
      (K*(D-CompactGlobalRowPadding.rowAxes NW m d))
      (K*backChunks d g K+K*(t+p.val*k)) k' ρ
      (compactReservationActive d g K D-(t+p.val*k)-m*k') (t+p.val*k) := by
  have hm : 1≤m := m_pos
  have hkd' : k'≤d := by nlinarith
  have hp := p.isLt
  have hi : t+p.val*k+m*k'≤compactReservationActive d g K D := by nlinarith
  exact compactReservationLayout hK h hρ hk' hkd' hi

private theorem compactReservation_digit_fit (a j : ℕ) :
    a % m^(j+1) + m*bits (synDg a (j+1)) j ≤ a := by
  have hh := Nat.mod_le a (m^(j+2))
  rw [show j+2=(j+1)+1 by omega,mod_pow_succ_dg] at hh
  rw [bits_eq_mul,pow_succ] at *
  nlinarith

/-- Every nonzero, nonleaf digit record determines a native node interval. -/
theorem compactReservationDigitLayout {d g K D payload ρ j : ℕ}
    (hK : 0<K) (h : CompactReservationFits d g K D) (hD : D≤d) (hρ : ρ<K)
    (hdigit : synDg (compactReservationActive d g K D) (j+1) ≠ 0) :
    CompactRecursiveLayout (compactReservationShape d g K D payload)
      (K*(D-CompactGlobalRowPadding.rowAxes NW m d))
      (K*backChunks d g K+K*(compactReservationActive d g K D % m^(j+1)))
      (bits (synDg (compactReservationActive d g K D) (j+1)) j) ρ
      (compactReservationActive d g K D - compactReservationActive d g K D % m^(j+1) -
        m*bits (synDg (compactReservationActive d g K D) (j+1)) j)
      (compactReservationActive d g K D % m^(j+1)) := by
  have hi := compactReservation_digit_fit (compactReservationActive d g K D) j
  have hk : 0 < bits (synDg (compactReservationActive d g K D) (j+1)) j := by
    rw [bits_eq_mul]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hdigit) (pow_pos m_pos _)
  have hactive : compactReservationActive d g K D ≤ D := by unfold compactReservationActive; omega
  have hmul : bits (synDg (compactReservationActive d g K D) (j+1)) j ≤
      m*bits (synDg (compactReservationActive d g K D) (j+1)) j := Nat.le_mul_of_pos_left _ m_pos
  have hfit : m*bits (synDg (compactReservationActive d g K D) (j+1)) j ≤
      compactReservationActive d g K D := (Nat.le_add_left _ _).trans hi
  have hkd : bits (synDg (compactReservationActive d g K D) (j+1)) j ≤ d :=
    hmul.trans (hfit.trans (hactive.trans hD))
  exact compactReservationLayout hK h hρ hk hkd hi

/-- Before row padding, the shape and folded payload retain the exact original bit volume.
This does not identify padded rows with the power-of-two metadata of `synPc`. -/
theorem compactReservation_volume {d g K D oS R r w : ℕ}
    (hK : 0<K) (h : CompactReservationFits d g K D) :
    (R*2^(K*CompactGlobalRowPadding.rowAxes NW m d))*
      (compactReservationShape d g K D (2^oS*(3*(r*w)))).recordWidth =
      (R*2^(oS+K*D))*(3*(r*w)) := by
  have hq : CompactGlobalRowPadding.rowAxes NW m d≤D := by
    unfold CompactReservationFits at h
    omega
  unfold Shape.recordWidth
  rw [compactReservation_bits hK h]
  change (R*2^(K*CompactGlobalRowPadding.rowAxes NW m d))*
    (2^(K*(D-CompactGlobalRowPadding.rowAxes NW m d))*(2^oS*(3*(r*w)))) = _
  have he : K*CompactGlobalRowPadding.rowAxes NW m d+K*(D-CompactGlobalRowPadding.rowAxes NW m d)=K*D := by
    rw [←Nat.mul_add,Nat.add_sub_of_le hq]
  calc
    _ = R*2^oS*(2^(K*CompactGlobalRowPadding.rowAxes NW m d)*
        2^(K*(D-CompactGlobalRowPadding.rowAxes NW m d)))*(3*(r*w)) := by ring
    _ = _ := by rw [←pow_add,he,pow_add]; ring

end
end IntegerMultBounds.MathlibTM2.Fast
