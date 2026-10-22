module

public import IntegerMultBounds.MathlibTM2.Routing.BlockExchange
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirBudget

/-!
# Place three borrowed fields with at most three block interchanges

Bring the chosen complete reservoir to the front, then move two compact slices
to the end. The remaining compact slice stays at the front. The resulting
physical layout is b, y, t, u, and each borrowed coordinate comes from the chosen
reservoir. This file specifies coordinate interchanges; their host execution and
canonical header generation remain separate obligations.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

variable (n H : ℕ) (hfit : 9 * H ≤ n)

def reservoirFrontPerm (k : Fin 3) : Equiv.Perm (Fin n) :=
  if hk : k.val = 0 then Equiv.refl _
  else blockExchangePerm n 0 (k.val * (3 * H)) (3 * H)
    (by
      have hk' : 1 ≤ k.val := by omega
      nlinarith)
    (by
      have hk' : k.val ≤ 2 := by omega
      nlinarith)

theorem reservoirFront_value (k : Fin 3) (i : Fin n) (hi : i.val < 3 * H) :
    (reservoirFrontPerm n H hfit k i).val = k.val * (3 * H) + i.val := by
  unfold reservoirFrontPerm
  split_ifs with hk
  · simp [hk]
  · change blockExchange 0 (k.val * (3 * H)) (3 * H) i.val = _
    have h := blockExchange_left 0 (k.val * (3 * H)) (3 * H) i.val
      (by
      have hk' : 1 ≤ k.val := by omega
      nlinarith) hi
    simpa using h

variable (w : ℕ) (hw : w ≤ H)

def reservoirTailT : Equiv.Perm (Fin n) :=
  blockExchangePerm n w (n - 2 * w) w (by omega) (by omega)

def reservoirTailU : Equiv.Perm (Fin n) :=
  blockExchangePerm n (2 * w) (n - w) w (by omega) (by omega)

def reservoirPlacement (k : Fin 3) : Equiv.Perm (Fin n) :=
  ((reservoirTailU n H hfit w hw).trans (reservoirTailT n H hfit w hw)).trans
    (reservoirFrontPerm n H hfit k)

/-- The compact b field draws from the first slice of the chosen reservoir. -/
theorem reservoirPlacement_b (k : Fin 3) (i : Fin n) (hi : i.val < w) :
    (reservoirPlacement n H hfit w hw k i).val = k.val * (3 * H) + i.val := by
  have hu : blockExchange (2 * w) (n - w) w i.val = i.val := by
    apply blockExchange_outside <;> omega
  have ht : blockExchange w (n - 2 * w) w i.val = i.val := by
    apply blockExchange_outside <;> omega
  let j := (reservoirTailT n H hfit w hw) ((reservoirTailU n H hfit w hw) i)
  have hj : j.val = i.val := by
    change blockExchange w (n - 2 * w) w (blockExchange (2 * w) (n - w) w i.val) = _
    rw [hu, ht]
  change (reservoirFrontPerm n H hfit k j).val = _
  rw [reservoirFront_value n H hfit k j (by omega), hj]

/-- The compact t field draws from the second slice of the chosen reservoir. -/
theorem reservoirPlacement_t (k : Fin 3) (i : Fin n)
    (hi : n - 2 * w ≤ i.val ∧ i.val < n - w) :
    (reservoirPlacement n H hfit w hw k i).val =
      k.val * (3 * H) + w + (i.val - (n - 2 * w)) := by
  have hu : blockExchange (2 * w) (n - w) w i.val = i.val := by
    apply blockExchange_outside <;> omega
  have ht : blockExchange w (n - 2 * w) w i.val = w + (i.val - (n - 2 * w)) := by
    have hr : i.val - (n - 2 * w) < w := by omega
    have he : n - 2 * w + (i.val - (n - 2 * w)) = i.val := by omega
    have h := blockExchange_right w (n - 2 * w) w _ (by omega) hr
    rwa [he] at h
  let j := (reservoirTailT n H hfit w hw) ((reservoirTailU n H hfit w hw) i)
  have hj : j.val = w + (i.val - (n - 2 * w)) := by
    change blockExchange w (n - 2 * w) w (blockExchange (2 * w) (n - w) w i.val) = _
    rw [hu, ht]
  change (reservoirFrontPerm n H hfit k j).val = _
  rw [reservoirFront_value n H hfit k j (by omega), hj]
  omega

/-- The compact u field draws from the third slice of the chosen reservoir. -/
theorem reservoirPlacement_u (k : Fin 3) (i : Fin n) (hi : n - w ≤ i.val) :
    (reservoirPlacement n H hfit w hw k i).val =
      k.val * (3 * H) + 2 * w + (i.val - (n - w)) := by
  have hb := i.isLt
  have hu : blockExchange (2 * w) (n - w) w i.val = 2 * w + (i.val - (n - w)) := by
    have hr : i.val - (n - w) < w := by omega
    have he : n - w + (i.val - (n - w)) = i.val := by omega
    have h := blockExchange_right (2 * w) (n - w) w _ (by omega) hr
    rwa [he] at h
  have ht : blockExchange w (n - 2 * w) w (2 * w + (i.val - (n - w))) =
      2 * w + (i.val - (n - w)) := by
    apply blockExchange_outside <;> omega
  let j := (reservoirTailT n H hfit w hw) ((reservoirTailU n H hfit w hw) i)
  have hj : j.val = 2 * w + (i.val - (n - w)) := by
    change blockExchange w (n - 2 * w) w (blockExchange (2 * w) (n - w) w i.val) = _
    rw [hu, ht]
  change (reservoirFrontPerm n H hfit k j).val = _
  rw [reservoirFront_value n H hfit k j (by omega), hj]
  omega

theorem routingReservoir_mem_iff (k : Fin 3) (i : Fin n) :
    i ∈ routingReservoir n H hfit k ↔
      k.val * (3 * H) ≤ i.val ∧ i.val < k.val * (3 * H) + 3 * H := by
  constructor
  · intro hi
    obtain ⟨r, _, he⟩ := Finset.mem_map.mp hi
    have hv := congrArg Fin.val he
    change k.val * (3 * H) + r.val = i.val at hv
    have hr := r.isLt
    omega
  · intro hi
    apply Finset.mem_map.mpr
    refine ⟨⟨i.val - k.val * (3 * H), by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change k.val * (3 * H) + (i.val - k.val * (3 * H)) = i.val
    omega

/-- Every physical borrowed position originates inside the selected reservoir. -/
theorem reservoirPlacement_borrowed_mem (k : Fin 3) (i : Fin n)
    (hi : i.val < w ∨ n - 2 * w ≤ i.val) :
    reservoirPlacement n H hfit w hw k i ∈ routingReservoir n H hfit k := by
  rw [routingReservoir_mem_iff]
  have hb := i.isLt
  rcases hi with hi | hi
  · rw [reservoirPlacement_b n H hfit w hw k i hi]
    omega
  · by_cases ht : i.val < n - w
    · rw [reservoirPlacement_t n H hfit w hw k i ⟨hi, ht⟩]
      omega
    · rw [reservoirPlacement_u n H hfit w hw k i (by omega)]
      omega

end IntegerMultBounds.MathlibTM2.Routing
