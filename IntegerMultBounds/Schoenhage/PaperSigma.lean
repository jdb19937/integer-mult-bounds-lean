module

public import IntegerMultBounds.Schoenhage.PaperRounds
public import IntegerMultBounds.Schoenhage.TwistDescriptors

/-! The paper layout in closed form. The physical bit holding slot `h` of
axis `i` is `paperSigma`: a bottom slot `h < b` sits at `DqK + hD + (D-1-i)`,
a chunk-group slot `b + cK + ρ` at `cDK + (D-1-i)K + ρ`, and the top slot
`ℓ - 1` of a long axis at `DqK + Db + (L-1-k)`, `k` the number of long axes
before it and `L` their total (`paperPerm_σ_eq`). The exponent table of a
slot round is therefore plain arithmetic in the axis, the slot and the lower
slot (`slotTable_paper`), which is what a tape program computes. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN TwistDescriptors

variable {r : ℕ}

/-- The number of long axes before axis `i`. -/
def longRank (ts : List ℕ) (ℓ i : ℕ) : ℕ := ((List.range i).filter fun j => axLen ts j = ℓ).length

/-- The physical bit of slot `h` of axis `i` in the paper's layout. -/
def paperSigma (ts : List ℕ) (ℓ K i h : ℕ) : ℕ :=
  if h < (ℓ - 1) % K then
    ts.length * ((ℓ - 1) / K) * K + h * ts.length + (ts.length - 1 - i)
  else if h < ℓ - 1 then
    (h - (ℓ - 1) % K) / K * ts.length * K + (ts.length - 1 - i) * K + (h - (ℓ - 1) % K) % K
  else
    ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K) +
      ((longs ts ℓ).length - 1 - longRank ts ℓ i)

theorem longs_getElem_longRank {ts : List ℕ} {ℓ i : ℕ} (hi : i < ts.length) (hl : axLen ts i = ℓ) :
    ∃ h : longRank ts ℓ i < (longs ts ℓ).length, (longs ts ℓ)[longRank ts ℓ i] = i := by
  have hsplit : List.range ts.length = List.range i ++ i :: (List.range (ts.length - i - 1)).map (i + 1 + ·) := by
    have e : ts.length = i + (1 + (ts.length - i - 1)) := by omega
    conv_lhs => rw [e]
    rw [List.range_add, List.range_add]
    simp [List.map_map, Function.comp_def, Nat.add_assoc]
  have hl' : longs ts ℓ = (List.range i).filter (fun j => axLen ts j = ℓ) ++
      i :: ((List.range (ts.length - i - 1)).map (i + 1 + ·)).filter (fun j => axLen ts j = ℓ) := by
    unfold longs
    rw [hsplit, List.filter_append, List.filter_cons_of_pos (by simpa using hl)]
  have hlen : longRank ts ℓ i < (longs ts ℓ).length := by
    rw [hl']; simp [longRank]
  refine ⟨hlen, ?_⟩
  simp only [hl', longRank]
  rw [List.getElem_append_right (by simp)]
  simp

/-- `paperPerm_σ_eq`: the paper's layout stores slot `h` of axis `i` at `paperSigma`. -/
theorem paperPerm_σ_eq {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {i h : ℕ}
    (hi : i < ts.length) (hh : h < axLen ts i) :
    (paperPerm hL).σ (axOff ts i + h) = paperSigma ts ℓ K i h := by
  have hK : 0 < K := hL.2.2.1
  have hlen := log_prod_layout hL
  set D := ts.length
  set b := (ℓ - 1) % K
  set q := (ℓ - 1) / K
  have hbK : b < K := Nat.mod_lt _ hK
  have hbq : b + q * K = ℓ - 1 := by have := Nat.mod_add_div (ℓ - 1) K; simp only [b, q]; linarith
  have hax := hL.2.1 i hi
  have hD : 0 < D := by omega
  by_cases hb : h < b
  · -- a bottom slot
    set Q := D * q * K + h * D + (D - 1 - i) with hQ
    have hlow : h * D + (D - 1 - i) < D * b := by
      have h1 : (h + 1) * D ≤ b * D := Nat.mul_le_mul_right _ (by omega)
      have h2 : (h + 1) * D = h * D + D := by ring
      have h3 : b * D = D * b := Nat.mul_comm _ _
      omega
    have hQn : Q < Nat.log 2 ts.prod := by rw [hlen]; omega
    have hslot : paperSlot ts ℓ K Q = (i, h) := by
      unfold paperSlot
      have h1 : ¬ Q < D * q * K := by omega
      have h2 : Q < D * q * K + D * b := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
      have e : Q - D * q * K = (D - 1 - i) + D * h := by
        have : h * D = D * h := Nat.mul_comm _ _
        omega
      rw [e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hD, Nat.mod_eq_of_lt (by omega),
        Nat.div_eq_of_lt (by omega)]
      simp only [Prod.mk.injEq]; omega
    have htau : paperTau ts ℓ K Q = axOff ts i + h := by unfold paperTau; rw [hslot]
    unfold paperSigma
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb), ← htau]
    exact BitPerm.ofTau_σ hQn
  · by_cases ht : h < ℓ - 1
    · -- a chunk-group slot
      have e : h = b + (h - b) / K * K + (h - b) % K := by
        have := Nat.div_add_mod (h - b) K; rw [Nat.mul_comm] at this; omega
      have hc : (h - b) / K < q := by
        rw [Nat.div_lt_iff_lt_mul hK]; omega
      have := paperPerm_σ_chunk hL hc (Nat.mod_lt (h - b) hK) hi
      rw [← e] at this
      unfold paperSigma
      rw [ite_eq_right_of_eq_false _ _ (eq_false hb), ite_eq_left_of_eq_true _ _ (eq_true ht)]
      exact this
    · -- the top slot of a long axis
      have hhl : h = ℓ - 1 := by rcases hax with e | e <;> omega
      have hlong : axLen ts i = ℓ := by rcases hax with e | e <;> omega
      obtain ⟨hk, hki⟩ := longs_getElem_longRank hi hlong
      set k := longRank ts ℓ i
      set L := (longs ts ℓ).length
      set Q := D * q * K + D * b + (L - 1 - k) with hQ
      have hQn : Q < Nat.log 2 ts.prod := by rw [hlen]; omega
      have hslot : paperSlot ts ℓ K Q = (i, h) := by
        unfold paperSlot
        have n1 : ¬ Q < D * q * K := by omega
        have n2 : ¬ Q < D * q * K + D * b := by omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false n1), ite_eq_right_of_eq_false _ _ (eq_false n2)]
        have e : L - 1 - (Q - D * q * K - D * b) = k := by omega
        rw [e, List.getD_eq_getElem _ _ hk, hki, hhl]
      have htau : paperTau ts ℓ K Q = axOff ts i + h := by unfold paperTau; rw [hslot]
      unfold paperSigma
      rw [ite_eq_right_of_eq_false _ _ (eq_false hb), ite_eq_right_of_eq_false _ _ (eq_false ht), ← htau]
      exact BitPerm.ofTau_σ hQn

/-- The exponent table of a slot round in the paper layout, in closed form. -/
def slotTableP (ts : List ℕ) (ℓ K r : ℕ) (Is : List ℕ) (h : ℕ) : List Entry :=
  Is.flatMap fun i => (List.range h).map fun h' =>
    (paperSigma ts ℓ K i h, paperSigma ts ℓ K i h', 2 * (2 * r / 2 ^ (h + 1) * 2 ^ h'))

/-- `slotTable_paper`: the exponent table of a slot round in the paper layout is `slotTableP`. -/
theorem slotTable_paper {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (r' : ℕ) {Is : List ℕ} {h : ℕ}
    (hIs : ∀ i ∈ Is, i < ts.length ∧ h < axLen ts i) :
    slotTable (paperPerm hL) r' ts Is h = slotTableP ts ℓ K r' Is h := by
  unfold slotTable slotTableP
  apply List.flatMap_congr
  intro i hi
  obtain ⟨hil, hhl⟩ := hIs i hi
  apply List.map_congr_left
  intro h' hh'
  have hh'l : h' < axLen ts i := by have := List.mem_range.mp hh'; omega
  rw [paperPerm_σ_eq hL hil hhl, paperPerm_σ_eq hL hil hh'l]

/-- The participating axes of a slot round satisfy the table's hypothesis. -/
theorem slotAxes_valid (ts : List ℕ) (h : ℕ) : ∀ i ∈ slotAxes ts h, i < ts.length ∧ h < axLen ts i := by
  intro i hi
  simp only [slotAxes, List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
  exact hi

end IntegerMultBounds.Schoenhage
