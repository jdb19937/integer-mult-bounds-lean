module

public import IntegerMultBounds.Schoenhage.DifRound

/-! The paper's layout `L` (Lemma "Transform layout and cost") as a bit
permutation. Axes have `ℓ - 1` or `ℓ` bits; put `b = (ℓ - 1) mod K` and
`q = ⌊(ℓ - 1)/K⌋`. From the least significant physical bit up: the `D q`
chunks of `K` slots, chunk-major (chunk group `c` holds the slots
`b + cK, …, b + cK + K - 1` of every axis, axis `0` in the most significant
chunk of the group); then the bottom slots `h < b`, slot-major; then the top
slots `ℓ - 1` of the long axes, axis order from the top. `paperTau` sends a
physical bit to its logical bit, and `paperPerm` is the resulting
`BitPerm`. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

/-! ### Bit permutations from an injection -/

/-- A bit permutation from an injective map of `[0, n)` into itself, read as physical to logical. -/
noncomputable def BitPerm.ofTau (n : ℕ) (τ : ℕ → ℕ) (hlt : ∀ Q < n, τ Q < n)
    (hinj : ∀ Q < n, ∀ Q' < n, τ Q = τ Q' → Q = Q') : BitPerm n :=
  let e : Fin n → Fin n := fun Q => ⟨τ Q, hlt Q Q.2⟩
  have he : Function.Bijective e :=
    Finite.injective_iff_bijective.mp fun a c h => Fin.ext (hinj a a.2 c c.2 (congrArg Fin.val h))
  let E := Equiv.ofBijective e he
  { σ := fun P => if h : P < n then (E.symm ⟨P, h⟩).val else 0
    τ := τ
    σ_lt := fun P hP => by simp only [hP, ↓reduceDIte]; exact (E.symm ⟨P, hP⟩).2
    τ_lt := hlt
    τσ := fun P hP => by
      simp only [hP, ↓reduceDIte]
      have := E.apply_symm_apply ⟨P, hP⟩
      exact congrArg Fin.val this
    στ := fun Q hQ => by
      have h' : τ Q < n := hlt Q hQ
      simp only [h', ↓reduceDIte]
      have := E.symm_apply_apply ⟨Q, hQ⟩
      exact congrArg Fin.val this }

theorem BitPerm.ofTau_σ {n : ℕ} {τ : ℕ → ℕ} {hlt} {hinj} {Q : ℕ} (hQ : Q < n) :
    (BitPerm.ofTau n τ hlt hinj).σ (τ Q) = Q :=
  (BitPerm.ofTau n τ hlt hinj).στ Q hQ

/-! ### The layout -/

variable {r : ℕ}

/-- The long axes, in axis order. -/
def longs (ts : List ℕ) (ℓ : ℕ) : List ℕ := (List.range ts.length).filter fun i => axLen ts i = ℓ

/-- The axis slot `(i, h)` held by physical bit `Q`. -/
def paperSlot (ts : List ℕ) (ℓ K Q : ℕ) : ℕ × ℕ :=
  if Q < ts.length * ((ℓ - 1) / K) * K then
    (ts.length - 1 - Q / K % ts.length, (ℓ - 1) % K + Q / K / ts.length * K + Q % K)
  else if Q < ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K) then
    (ts.length - 1 - (Q - ts.length * ((ℓ - 1) / K) * K) % ts.length,
      (Q - ts.length * ((ℓ - 1) / K) * K) / ts.length)
  else
    ((longs ts ℓ).getD ((longs ts ℓ).length - 1 -
      (Q - ts.length * ((ℓ - 1) / K) * K - ts.length * ((ℓ - 1) % K))) 0, ℓ - 1)

/-- The logical bit held by physical bit `Q`. -/
def paperTau (ts : List ℕ) (ℓ K Q : ℕ) : ℕ := axOff ts (paperSlot ts ℓ K Q).1 + (paperSlot ts ℓ K Q).2

/-- The admissible axis lengths: every axis has `ℓ - 1` or `ℓ` bits. -/
def LayoutOK (r : ℕ) (ts : List ℕ) (ℓ K : ℕ) : Prop :=
  PowAxes r ts ∧ (∀ i < ts.length, axLen ts i = ℓ - 1 ∨ axLen ts i = ℓ) ∧ 1 ≤ K ∧ 1 ≤ ℓ

theorem log_prod_eq_sum {ts : List ℕ} (hts : PowAxes r ts) :
    Nat.log 2 ts.prod = ((List.range ts.length).map (axLen ts)).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [log_prod_cons hts, ih (powAxes_cons hts), List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map, List.sum_cons]
    simp only [axLen, List.getD_cons_zero, List.getD_cons_succ, Function.comp_def]
    rfl

theorem sum_axLen {ts : List ℕ} {ℓ : ℕ} (h : ∀ i < ts.length, axLen ts i = ℓ - 1 ∨ axLen ts i = ℓ) (hℓ : 1 ≤ ℓ) :
    ((List.range ts.length).map (axLen ts)).sum = ts.length * (ℓ - 1) + (longs ts ℓ).length := by
  unfold longs
  generalize hD : ts.length = D at h
  have : ∀ m ≤ D, ((List.range m).map (axLen ts)).sum =
      m * (ℓ - 1) + ((List.range m).filter fun i => axLen ts i = ℓ).length := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega), List.filter_append,
        List.length_append]
      rcases h m (by omega) with e | e
      · have hne : ¬ (ℓ - 1 = ℓ) := by omega
        simp [e, hne, Nat.succ_mul]; omega
      · simp [e, Nat.succ_mul]; omega
  exact this D le_rfl

/-- The number of address bits. -/
theorem log_prod_layout {ts : List ℕ} {ℓ K : ℕ} (h : LayoutOK r ts ℓ K) :
    Nat.log 2 ts.prod = ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K) + (longs ts ℓ).length := by
  rw [log_prod_eq_sum h.1, sum_axLen h.2.1 h.2.2.2]
  have := Nat.div_add_mod (ℓ - 1) K
  have e : ts.length * (ℓ - 1) = ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K) := by
    conv_lhs => rw [← this]
    ring
  omega

/-- Distinct axis slots have distinct logical bits. -/
theorem pos_inj {ts : List ℕ} (hts : PowAxes r ts) {i h i' h' : ℕ} (hi : i < ts.length) (hi' : i' < ts.length)
    (hh : h < axLen ts i) (hh' : h' < axLen ts i') (e : axOff ts i + h = axOff ts i' + h') : i = i' ∧ h = h' := by
  rcases Nat.lt_trichotomy i i' with hl | rfl | hl
  · have := axOff_le hts hl hi'; omega
  · omega
  · have := axOff_le hts hl hi; omega

theorem longs_lt {ts : List ℕ} {ℓ : ℕ} {k : ℕ} (hk : k < (longs ts ℓ).length) :
    (longs ts ℓ)[k] < ts.length ∧ axLen ts (longs ts ℓ)[k] = ℓ := by
  have := List.getElem_mem hk
  simp only [longs, List.mem_filter, List.mem_range, decide_eq_true_eq] at this
  exact this

/-- Each physical bit holds a valid slot, with its region determined by the slot. -/
theorem paperSlot_valid {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {Q : ℕ}
    (hQ : Q < Nat.log 2 ts.prod) :
    (paperSlot ts ℓ K Q).1 < ts.length ∧ (paperSlot ts ℓ K Q).2 < axLen ts (paperSlot ts ℓ K Q).1 ∧
      (Q < ts.length * ((ℓ - 1) / K) * K ↔
        (ℓ - 1) % K ≤ (paperSlot ts ℓ K Q).2 ∧ (paperSlot ts ℓ K Q).2 < ℓ - 1) ∧
      (Q < ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K) ↔ (paperSlot ts ℓ K Q).2 < ℓ - 1) := by
  obtain ⟨hts, hax, hK, hℓ⟩ := hL
  rw [log_prod_layout ⟨hts, hax, hK, hℓ⟩] at hQ
  unfold paperSlot
  set D := ts.length
  set b := (ℓ - 1) % K
  set q := (ℓ - 1) / K
  have hbq : b + q * K = ℓ - 1 := by have := Nat.mod_add_div (ℓ - 1) K; simp only [b, q]; linarith
  have hbK : b < K := Nat.mod_lt _ (by omega)
  by_cases h1 : Q < D * q * K
  · have hD : 0 < D := by rcases Nat.eq_zero_or_pos D with h0 | h0 <;> [rw [h0] at h1; skip] <;> simp_all
    have hv : Q / K < D * q := by rw [Nat.div_lt_iff_lt_mul (by omega)]; exact h1
    have hvq : Q / K / D < q := by rw [Nat.div_lt_iff_lt_mul hD, mul_comm]; exact hv
    have hmK : Q % K < K := Nat.mod_lt _ (by omega)
    have hh : b + Q / K / D * K + Q % K < ℓ - 1 := by
      have : Q / K / D * K + K ≤ q * K := by nlinarith
      omega
    simp only [h1, ↓reduceIte, true_iff, show Q < D * q * K + D * b by omega]
    refine ⟨by omega, ?_, by omega, hh⟩
    rcases hax (D - 1 - Q / K % D) (by omega) with e | e <;> rw [e] <;> omega
  · by_cases h2 : Q < D * q * K + D * b
    · have hD : 0 < D := by rcases Nat.eq_zero_or_pos D with h0 | h0 <;> [rw [h0] at h2; skip] <;> simp_all
      have hu : (Q - D * q * K) / D < b := by rw [Nat.div_lt_iff_lt_mul hD, Nat.mul_comm b D]; omega
      simp only [h1, h2, ↓reduceIte, true_iff, false_iff, not_and, not_lt]
      refine ⟨by omega, ?_, by omega, by omega⟩
      rcases hax (D - 1 - (Q - D * q * K) % D) (by omega) with e | e <;> rw [e] <;> omega
    · set k := (longs ts ℓ).length - 1 - (Q - D * q * K - D * b)
      have hk : k < (longs ts ℓ).length := by omega
      obtain ⟨hil, hel⟩ := longs_lt hk
      have hg : (longs ts ℓ).getD k 0 = (longs ts ℓ)[k] := by rw [List.getD_eq_getElem _ _ hk]
      simp only [h1, h2, ↓reduceIte, false_iff, not_and, not_lt, hg]
      exact ⟨hil, by omega, fun _ => le_rfl, le_rfl⟩

theorem div_mod_unique {K a c a' c' : ℕ} (hc : c < K) (hc' : c' < K) (e : a * K + c = a' * K + c') :
    a = a' ∧ c = c' := by
  have h1 : (a * K + c) / K = a := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]
  have h2 : (a' * K + c') / K = a' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc', zero_add]
  have h3 : (a * K + c) % K = c := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have h4 : (a' * K + c') % K = c' := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc']
  rw [e] at h1 h3
  exact ⟨h1.symm.trans h2, h3.symm.trans h4⟩

theorem longs_nodup (ts : List ℕ) (ℓ : ℕ) : (longs ts ℓ).Nodup := (List.nodup_range).filter _

theorem paperSlot_inj {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {Q Q' : ℕ}
    (hQ : Q < Nat.log 2 ts.prod) (hQ' : Q' < Nat.log 2 ts.prod) (e : paperSlot ts ℓ K Q = paperSlot ts ℓ K Q') :
    Q = Q' := by
  have v := paperSlot_valid hL hQ
  have v' := paperSlot_valid hL hQ'
  rw [e] at v
  have r1 : (Q < ts.length * ((ℓ - 1) / K) * K) ↔ (Q' < ts.length * ((ℓ - 1) / K) * K) := v.2.2.1.trans v'.2.2.1.symm
  have r2 := v.2.2.2.trans v'.2.2.2.symm
  obtain ⟨hts, hax, hK, hℓ⟩ := hL
  rw [log_prod_layout ⟨hts, hax, hK, hℓ⟩] at hQ hQ'
  unfold paperSlot at e
  set D := ts.length
  set b := (ℓ - 1) % K
  set q := (ℓ - 1) / K
  by_cases h1 : Q < D * q * K
  · have h1' := r1.mp h1
    simp only [h1, h1', ↓reduceIte, Prod.mk.injEq] at e
    have hD : 0 < D := by rcases Nat.eq_zero_or_pos D with h0 | h0 <;> [rw [h0] at h1; skip] <;> simp_all
    have m1 : Q / K % D = Q' / K % D := by
      have := Nat.mod_lt (Q / K) hD; have := Nat.mod_lt (Q' / K) hD; omega
    obtain ⟨d1, d2⟩ := div_mod_unique (Nat.mod_lt Q (by omega)) (Nat.mod_lt Q' (by omega)) (by omega : Q / K / D * K + Q % K = Q' / K / D * K + Q' % K)
    have hv : Q / K = Q' / K := by rw [← Nat.div_add_mod (Q / K) D, ← Nat.div_add_mod (Q' / K) D, d1, m1]
    rw [← Nat.div_add_mod Q K, ← Nat.div_add_mod Q' K, hv, d2]
  · have h1' : ¬ Q' < D * q * K := fun h => h1 (r1.mpr h)
    by_cases h2 : Q < D * q * K + D * b
    · have h2'' : Q' < D * q * K + D * b := r2.mp h2
      simp only [h1, h1', h2, h2'', ↓reduceIte, Prod.mk.injEq] at e
      have hD : 0 < D := by rcases Nat.eq_zero_or_pos D with h0 | h0 <;> [rw [h0] at h2; skip] <;> simp_all
      have m1 : (Q - D * q * K) % D = (Q' - D * q * K) % D := by
        have := Nat.mod_lt (Q - D * q * K) hD; have := Nat.mod_lt (Q' - D * q * K) hD; omega
      have : Q - D * q * K = Q' - D * q * K := by
        rw [← Nat.div_add_mod (Q - D * q * K) D, ← Nat.div_add_mod (Q' - D * q * K) D, e.2, m1]
      omega
    · have h2'' : ¬ Q' < D * q * K + D * b := fun h => h2 (r2.mpr h)
      simp only [h1, h1', h2, h2'', ↓reduceIte, Prod.mk.injEq] at e
      have hk : (longs ts ℓ).length - 1 - (Q - D * q * K - D * b) < (longs ts ℓ).length := by omega
      have hk' : (longs ts ℓ).length - 1 - (Q' - D * q * K - D * b) < (longs ts ℓ).length := by omega
      rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk'] at e
      have := (longs_nodup ts ℓ).getElem_inj_iff.mp e.1
      omega

theorem paperTau_lt {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {Q : ℕ} (hQ : Q < Nat.log 2 ts.prod) :
    paperTau ts ℓ K Q < Nat.log 2 ts.prod := by
  obtain ⟨h1, h2, -⟩ := paperSlot_valid hL hQ
  have := axOff_add_len_le hL.1 h1
  unfold paperTau; omega

theorem paperTau_inj {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {Q Q' : ℕ}
    (hQ : Q < Nat.log 2 ts.prod) (hQ' : Q' < Nat.log 2 ts.prod) (e : paperTau ts ℓ K Q = paperTau ts ℓ K Q') :
    Q = Q' := by
  obtain ⟨a1, a2, -⟩ := paperSlot_valid hL hQ
  obtain ⟨b1, b2, -⟩ := paperSlot_valid hL hQ'
  obtain ⟨c1, c2⟩ := pos_inj hL.1 a1 b1 a2 b2 e
  exact paperSlot_inj hL hQ hQ' (Prod.ext c1 c2)

/-- The paper's layout as a bit permutation. -/
noncomputable def paperPerm {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) : BitPerm (Nat.log 2 ts.prod) :=
  BitPerm.ofTau _ (paperTau ts ℓ K) (fun _ hQ => paperTau_lt hL hQ) (fun _ hQ _ hQ' e => paperTau_inj hL hQ hQ' e)

end IntegerMultBounds.Schoenhage
