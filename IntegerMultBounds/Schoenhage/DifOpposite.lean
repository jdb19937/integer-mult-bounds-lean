module

public import IntegerMultBounds.Schoenhage.PaperLayout

/-! The opposite schedule of §6 (`eq:stored-opposite`). Each forward round is a
butterfly `H₀` followed by a twist `y^(-f)`; its opposite round applies the
inverse monomial `y^f` first and the butterfly second (`oppRound`). As
`H₀² = I/2`, an opposite round undoes its forward round up to `1/2` in both
orders, so the opposite rounds in reverse order compose with the forward
schedule to `2^(-n) = 1/M` either way (`run_opp_fwd`, `run_fwd_opp`). The
forward schedule computes `L B F⁻` (`physSchedule_fwdExact`), so the opposite
schedule computes `F⁺ B⁻¹ L⁻¹`, i.e. `oppExact`, with its output stored in the
same layout (`oppSchedule_eq`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

variable {r : ℕ} [NeZero r]

/-! ### Inverse monomials -/

theorem shiftNegZ_shiftInv (e : ℕ) (v : Fin r → ℂ) : shiftNegZ e (shiftInv e v) = v := by
  have hr : 0 < 2 * r := by have := NeZero.pos r; omega
  unfold shiftInv
  rw [shiftNegZ_add, shiftNegZ_mod]
  have : (e + (2 * r - e % (2 * r)) % (2 * r)) % (2 * r) = 0 := by
    have hs := Nat.mod_lt e hr
    rcases Nat.eq_zero_or_pos (e % (2 * r)) with h0 | hpos
    · rw [h0, Nat.sub_zero, Nat.mod_self, add_zero, h0]
    · rw [Nat.mod_eq_of_lt (by omega : 2 * r - e % (2 * r) < 2 * r), Nat.add_mod, Nat.mod_eq_of_lt
        (by omega : 2 * r - e % (2 * r) < 2 * r)]
      rw [show e % (2 * r) + (2 * r - e % (2 * r)) = 2 * r by omega, Nat.mod_self]
  rw [this, shiftNegZ_zero]

theorem shiftInv_shiftNegZ (e : ℕ) (v : Fin r → ℂ) : shiftInv e (shiftNegZ e v) = v := by
  unfold shiftInv
  rw [shiftNegZ_add, shiftNegZ_mod]
  have hr : 0 < 2 * r := by have := NeZero.pos r; omega
  have : ((2 * r - e % (2 * r)) % (2 * r) + e) % (2 * r) = 0 := by
    have hs := Nat.mod_lt e hr
    rcases Nat.eq_zero_or_pos (e % (2 * r)) with h0 | hpos
    · rw [h0, Nat.sub_zero, Nat.mod_self, zero_add, h0]
    · rw [Nat.mod_eq_of_lt (by omega : 2 * r - e % (2 * r) < 2 * r), Nat.add_mod,
        Nat.mod_eq_of_lt (by omega : 2 * r - e % (2 * r) < 2 * r)]
      rw [show 2 * r - e % (2 * r) + e % (2 * r) = 2 * r by omega, Nat.mod_self]
  rw [this, shiftNegZ_zero]

/-- The pointwise inverse twist by `y^(f(x))`. -/
noncomputable def untwist (f : ℕ → ℕ) (z : ℕ → Fin r → ℂ) : ℕ → Fin r → ℂ :=
  fun x => shiftNegZ (f x) (z x)

theorem untwist_twist (f : ℕ → ℕ) (z : ℕ → Fin r → ℂ) : untwist f (twist f z) = z := by
  funext x; exact shiftNegZ_shiftInv _ _

theorem twist_untwist (f : ℕ → ℕ) (z : ℕ → Fin r → ℂ) : twist f (untwist f z) = z := by
  funext x; exact shiftInv_shiftNegZ _ _

theorem twist_smul (f : ℕ → ℕ) (c : ℂ) (z : ℕ → Fin r → ℂ) : twist f (c • z) = c • twist f z := by
  funext x; exact shiftInv_smul _ _ _

theorem untwist_smul (f : ℕ → ℕ) (c : ℂ) (z : ℕ → Fin r → ℂ) : untwist f (c • z) = c • untwist f z := by
  funext x; exact shiftNegZ_smul _ _ _

/-! ### Butterflies -/

omit [NeZero r] in
theorem bfly_smul (P : ℕ) (c : ℂ) (z : ℕ → Fin r → ℂ) : bfly P (c • z) = c • bfly P z := by
  funext x
  by_cases hb : bitAt x P = 0
  · simp only [bfly, hb, ↓reduceIte, Pi.smul_apply]; module
  · simp only [bfly, hb, ↓reduceIte, Pi.smul_apply]; module

omit [NeZero r] in
/-- `H₀² = I/2`. -/
theorem bfly_bfly (P : ℕ) (z : ℕ → Fin r → ℂ) : bfly P (bfly P z) = (1 / 2 : ℂ) • z := by
  funext x
  unfold bfly
  by_cases hb : bitAt x P = 0
  · have h1 : bitAt (x + 2 ^ P) P ≠ 0 := by rw [bitAt_add_pow_self hb]; norm_num
    simp only [hb, ↓reduceIte, h1, Nat.add_sub_cancel, Pi.smul_apply]
    module
  · have h0 := bitAt_sub_pow_self hb
    have hle := le_of_bitAt hb
    simp only [hb, ↓reduceIte, h0, Nat.sub_add_cancel hle, Pi.smul_apply]
    module

/-! ### Rounds -/

/-- The opposite of a physical round: the inverse monomial first, then the butterfly. -/
noncomputable def oppRound {n : ℕ} (π : BitPerm n) (ts : List ℕ) (i h : ℕ) :
    (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ :=
  fun w => bfly (π.σ (axOff ts i + h)) (untwist (fun y => rexp r (axOff ts i) h (π.logi y)) w)

theorem oppRound_physRound {n : ℕ} (π : BitPerm n) (ts : List ℕ) (i h : ℕ) (z : ℕ → Fin r → ℂ) :
    oppRound π ts i h (physRound π ts i h z) = (1 / 2 : ℂ) • z := by
  unfold oppRound physRound
  rw [untwist_twist, bfly_bfly]

theorem physRound_oppRound {n : ℕ} (π : BitPerm n) (ts : List ℕ) (i h : ℕ) (z : ℕ → Fin r → ℂ) :
    physRound π ts i h (oppRound π ts i h z) = (1 / 2 : ℂ) • z := by
  unfold oppRound physRound
  rw [bfly_bfly, twist_smul, twist_untwist]

theorem physRound_smul {n : ℕ} (π : BitPerm n) (ts : List ℕ) (i h : ℕ) (c : ℂ) (z : ℕ → Fin r → ℂ) :
    physRound π ts i h (c • z) = c • physRound π ts i h z := by
  unfold physRound; rw [bfly_smul, twist_smul]

theorem oppRound_smul {n : ℕ} (π : BitPerm n) (ts : List ℕ) (i h : ℕ) (c : ℂ) (z : ℕ → Fin r → ℂ) :
    oppRound π ts i h (c • z) = c • oppRound π ts i h z := by
  unfold oppRound; rw [untwist_smul, bfly_smul]

/-! ### Schedules -/

section Cancel

variable {β α : Type*} [AddCommGroup α] [Module ℂ α]

theorem run_map_smul (F : β → α → α) (hF : ∀ b (c : ℂ) z, F b (c • z) = c • F b z) :
    ∀ (L : List β) (c : ℂ) (z : α), run (L.map F) (c • z) = c • run (L.map F) z
  | [], _, _ => rfl
  | b :: L, c, z => by
    simp only [List.map_cons, run]
    rw [hF, run_map_smul F hF L]

/-- The reversed opposite rounds undo the forward rounds up to `2^(-length)`. -/
theorem run_rev_cancel (F G : β → α → α) (hGF : ∀ b z, G b (F b z) = (1 / 2 : ℂ) • z)
    (hG : ∀ b (c : ℂ) z, G b (c • z) = c • G b z) :
    ∀ (L : List β) (z : α), run (L.map G).reverse (run (L.map F) z) = ((1 / 2 : ℂ) ^ L.length) • z
  | [], z => by simp [run]
  | b :: L, z => by
    simp only [List.map_cons, List.reverse_cons, run_append, run, List.length_cons]
    rw [run_rev_cancel F G hGF hG L (F b z), hG, hGF, smul_smul, pow_succ]

/-- The forward rounds undo the reversed opposite rounds up to `2^(-length)`. -/
theorem run_cancel_rev (F G : β → α → α) (hFG : ∀ b z, F b (G b z) = (1 / 2 : ℂ) • z)
    (hF : ∀ b (c : ℂ) z, F b (c • z) = c • F b z) :
    ∀ (L : List β) (z : α), run (L.map F) (run (L.map G).reverse z) = ((1 / 2 : ℂ) ^ L.length) • z
  | [], z => by simp [run]
  | b :: L, z => by
    simp only [List.map_cons, List.reverse_cons, run_append, run, List.length_cons]
    rw [hFG, run_map_smul F hF, run_cancel_rev F G hFG hF L z, smul_smul, pow_succ, mul_comm]

end Cancel

/-- The forward schedule on physical bits. -/
noncomputable def fwdSchedule {n : ℕ} (π : BitPerm n) (ts : List ℕ) (H : ℕ) :
    (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ :=
  run ((slotPairs ts H).map fun p => physRound π ts p.1 p.2)

/-- The opposite schedule: the opposite rounds in reverse order. -/
noncomputable def oppSchedule {n : ℕ} (π : BitPerm n) (ts : List ℕ) (H : ℕ) :
    (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ :=
  run ((slotPairs ts H).map fun p => oppRound π ts p.1 p.2).reverse

theorem oppSchedule_fwdSchedule {n : ℕ} (π : BitPerm n) (ts : List ℕ) (H : ℕ) (z : ℕ → Fin r → ℂ) :
    oppSchedule π ts H (fwdSchedule π ts H z) = ((1 / 2 : ℂ) ^ (slotPairs ts H).length) • z := by
  exact run_rev_cancel (β := ℕ × ℕ) (α := ℕ → Fin r → ℂ) (fun p => physRound π ts p.1 p.2)
    (fun p => oppRound π ts p.1 p.2)
    (fun p z => oppRound_physRound π ts p.1 p.2 z) (fun p c z => oppRound_smul π ts p.1 p.2 c z)
    (slotPairs ts H) z

theorem fwdSchedule_oppSchedule {n : ℕ} (π : BitPerm n) (ts : List ℕ) (H : ℕ) (z : ℕ → Fin r → ℂ) :
    fwdSchedule π ts H (oppSchedule π ts H z) = ((1 / 2 : ℂ) ^ (slotPairs ts H).length) • z := by
  exact run_cancel_rev (β := ℕ × ℕ) (α := ℕ → Fin r → ℂ) (fun p => physRound π ts p.1 p.2)
    (fun p => oppRound π ts p.1 p.2)
    (fun p z => physRound_oppRound π ts p.1 p.2 z) (fun p c z => physRound_smul π ts p.1 p.2 c z)
    (slotPairs ts H) z

/-! ### Counting rounds -/

omit [NeZero r] in
theorem slotPairs_length (ts : List ℕ) {H : ℕ} (hH : ∀ i < ts.length, axLen ts i ≤ H) :
    (slotPairs ts H).length = ((List.range ts.length).map (axLen ts)).sum := by
  unfold slotPairs
  rw [List.length_flatMap]
  simp only [List.length_map, List.map_reverse, List.sum_reverse]
  have hcount : ∀ h, ((List.range ts.length).filter fun i => h < axLen ts i).length =
      ∑ i ∈ Finset.range ts.length, if h < axLen ts i then 1 else 0 := by
    intro h
    rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _), List.toFinset_filter,
      List.toFinset_range, Finset.card_filter]
    simp
  simp only [hcount]
  rw [← List.sum_toFinset _ (List.nodup_range), List.toFinset_range, Finset.sum_comm,
    ← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_boole]
  have : (Finset.filter (fun h => h < axLen ts i) (Finset.range H)) = Finset.range (axLen ts i) := by
    ext h; simp only [Finset.mem_filter, Finset.mem_range]
    have := hH i (Finset.mem_range.mp hi); constructor <;> intro hh <;> omega
  rw [this, Finset.card_range]
  simp

omit [NeZero r] in
theorem slotPairs_length_eq {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    {H : ℕ} (hH : ∀ i < ts.length, axLen ts i ≤ H) : (slotPairs ts H).length = n := by
  rw [slotPairs_length ts hH, ← log_prod_eq_sum hts, hn, Nat.log_pow (by norm_num)]

/-! ### The layout as a record permutation -/

/-- The record permutation of a bit layout: logical address `x` is stored at `phys x`. -/
def BitPerm.toPerm {n : ℕ} (π : BitPerm n) {M : ℕ} (hM : M = 2 ^ n) : Equiv.Perm (Fin M) where
  toFun x := ⟨π.phys x, hM ▸ π.phys_lt x⟩
  invFun y := ⟨π.logi y, hM ▸ π.logi_lt y⟩
  left_inv x := Fin.ext (π.logi_phys (hM ▸ x.2))
  right_inv y := Fin.ext (π.phys_logi (hM ▸ y.2))

/-! ### The forward and opposite schedules as the paper's procedures -/

/-- The forward schedule, on any array that agrees with `z` stored in layout `π`,
computes `L B F⁻ z` with `L` the record permutation of `π`. -/
theorem fwdSchedule_fwdExact {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) {H : ℕ} (hH : ∀ i < ts.length, axLen ts i ≤ H) (z w : ℕ → Fin r → ℂ)
    (hw : Agree n w fun y => z (π.logi y)) {y : ℕ} (hy : y < 2 ^ n) :
    fwdSchedule π ts H w y = fwdExact ts (π.toPerm hn) z y := by
  have hlog : Nat.log 2 ts.prod = n := by rw [hn, Nat.log_pow (by norm_num)]
  have hab : ∀ i < ts.length, ∀ h < axLen ts i, axOff ts i + h < n := fun i hi h hh => by
    have := axOff_add_len_le hts hi; omega
  have ag := run_physM π ts (axLen ts) hab 0 0 (Nat.zero_le _) (slotPairs ts H)
    (fun p hp => by
      simp only [slotPairs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at hp
      obtain ⟨h, -, i, ⟨hi, hih⟩, rfl⟩ := hp
      exact ⟨hi, hih⟩) w z hw
  have hyM : y < ts.prod := hn ▸ hy
  unfold fwdSchedule fwdExact
  rw [ag y hy]
  simp only [hyM, ↓reduceDIte]
  rw [← slotM_eq_pairs, slotMajor_eq hts hH z (by rw [hn]; exact π.logi_lt y)]
  rfl

theorem oppExact_congr {ts : List ℕ} (Lp : Equiv.Perm (Fin ts.prod)) {u v : ℕ → Fin r → ℂ}
    (h : ∀ y < ts.prod, u y = v y) : oppExact ts Lp u = oppExact ts Lp v := by
  unfold oppExact
  congr 1
  funext j
  split_ifs with hj
  · exact h _ (Lp _).2
  · rfl

theorem oppExact_smul {ts : List ℕ} (Lp : Equiv.Perm (Fin ts.prod)) (c : ℂ) (u : ℕ → Fin r → ℂ) (j : ℕ) :
    oppExact ts Lp (c • u) j = c • oppExact ts Lp u j := by
  unfold oppExact oppT
  rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  split_ifs
  · rw [Pi.smul_apply, shiftNegZ_smul, smul_comm]
  · rw [shiftNegZ_zero_vec, smul_zero, smul_zero]

/-- `oppSchedule_eq`: the opposite schedule computes `F⁺ B⁻¹ L⁻¹`, storing the
output entry with logical address `x` at physical address `phys x`. -/
theorem oppSchedule_eq {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) {H : ℕ} (hH : ∀ i < ts.length, axLen ts i ≤ H) (u : ℕ → Fin r → ℂ)
    {y : ℕ} (hy : y < 2 ^ n) :
    oppSchedule π ts H u y = oppExact ts (π.toPerm hn) u (π.logi y) := by
  have hlen := slotPairs_length_eq hts hn hH
  have hM : (ts.prod : ℂ) = 2 ^ n := by rw [hn]; push_cast; ring
  have hc : ((1 / 2 : ℂ) ^ n) * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  -- `w` is a forward preimage of `u`
  set w := ((2 : ℂ) ^ n) • oppSchedule π ts H u with hwdef
  have hFw : fwdSchedule π ts H w = u := by
    rw [hwdef]
    unfold fwdSchedule
    rw [run_map_smul _ (fun p c z => physRound_smul π ts p.1 p.2 c z)]
    change ((2 : ℂ) ^ n) • fwdSchedule π ts H (oppSchedule π ts H u) = u
    rw [fwdSchedule_oppSchedule, hlen, smul_smul, mul_comm, hc, one_smul]
  set z : ℕ → Fin r → ℂ := fun x => w (π.phys x) with hzdef
  have hagree : Agree n w fun y => z (π.logi y) := fun y hy => by
    simp only [hzdef, π.phys_logi hy]
  have hfwd : ∀ y' < ts.prod, u y' = fwdExact ts (π.toPerm hn) z y' := fun y' hy' => by
    rw [← hFw]; exact fwdSchedule_fwdExact hts hn π hH z w hagree (hn ▸ hy')
  have hlogi : π.logi y < ts.prod := hn ▸ π.logi_lt y
  rw [oppExact_congr _ hfwd, oppExact_fwdExact hts _ z hlogi]
  have hsched : oppSchedule π ts H u y = ((1 / 2 : ℂ) ^ n) • w y := by
    rw [← hFw, oppSchedule_fwdSchedule, hlen]; rfl
  rw [hsched, hzdef]
  simp only [π.phys_logi hy, hM, one_div, inv_pow]

end IntegerMultBounds.Schoenhage
