module

public import IntegerMultBounds.Schoenhage.DifHadamard

/-! The opposite schedule grouped by slot, and its rounding error. The
opposite round of slot `h` applies the inverse monomial `y^E` of the slot's
summed exponent first and then the butterflies on the slot's bits
(`oppSlotRound`). Running these from the bottom slot up is the opposite
schedule (`oppSchedule_oppSlotRounds`), because each forward slot round is
inverted, up to `2^(-m)`, both by its per-axis opposite rounds and by the
grouped opposite round. Rounding after every opposite slot round keeps the
computed opposite schedule within `√2 · H · 2^(-p)` of `F⁺ B⁻¹ L⁻¹` and in
the unit disk (`compOppSchedule_close`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

variable {r : ℕ}

/-! ### Commuting butterflies -/

section Commuting

variable {α : Type*}

/-- A list of pairwise commuting operators runs the same in reverse. -/
theorem run_reverse_of_comm : ∀ (L : List (α → α)), L.Pairwise (fun f g => ∀ x, f (g x) = g (f x)) →
    ∀ x, run L.reverse x = run L x
  | [], _, _ => rfl
  | f :: L, h, x => by
    have hp := List.pairwise_cons.mp h
    rw [List.reverse_cons, run_append, run_reverse_of_comm L hp.2]
    show f (run L x) = run (f :: L) x
    rw [run_comm_one L (fun g hg y => hp.1 g hg y), run_append]
    rfl

end Commuting

theorem bflys_reverse {Ps : List ℕ} (hPs : Ps.Nodup) (w : ℕ → Fin r → ℂ) :
    run (Ps.map bfly).reverse w = bflys Ps w := by
  unfold bflys
  apply run_reverse_of_comm
  rw [List.pairwise_map]
  exact hPs.imp fun hne x => bfly_comm hne x

theorem bflys_bflys {Ps : List ℕ} (hPs : Ps.Nodup) (w : ℕ → Fin r → ℂ) :
    bflys Ps (bflys Ps w) = ((1 / 2 : ℂ) ^ Ps.length) • w := by
  rw [← bflys_reverse hPs (bflys Ps w)]
  unfold bflys
  have := run_rev_cancel (β := ℕ) (α := ℕ → Fin r → ℂ) bfly bfly (fun P z => bfly_bfly P z)
    (fun P c z => bfly_smul P c z) Ps w
  exact this

theorem bflys_smul (Ps : List ℕ) (c : ℂ) (w : ℕ → Fin r → ℂ) : bflys Ps (c • w) = c • bflys Ps w :=
  run_map_smul bfly (fun P c z => bfly_smul P c z) Ps c w

variable [NeZero r]

/-! ### The grouped opposite round -/

/-- The opposite round of slot `h`: the inverse monomial of the summed exponent, then the
butterflies of every participating axis. -/
noncomputable def oppSlotRound {n : ℕ} (π : BitPerm n) (ts : List ℕ) (h : ℕ) :
    (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ :=
  fun w => bflys (slotBits π ts (slotAxes ts h) h) (untwist (slotExp π r ts (slotAxes ts h) h) w)

omit [NeZero r] in
theorem slotBits_nodup {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) (h : ℕ) : (slotBits π ts (slotAxes ts h) h).Nodup := by
  have hlog : Nat.log 2 ts.prod = n := by rw [hn, Nat.log_pow (by norm_num)]
  unfold slotBits
  refine List.Nodup.map_on ?_ ((List.nodup_range).filter _)
  intro i hi j hj e
  simp only [slotAxes, List.mem_filter, List.mem_range, decide_eq_true_eq] at hi hj
  have hi' := axOff_add_len_le hts hi.1
  have hj' := axOff_add_len_le hts hj.1
  have e' := congrArg π.τ e
  rw [π.τσ _ (by omega), π.τσ _ (by omega)] at e'
  exact (pos_inj hts hi.1 hj.1 hi.2 hj.2 e').1

theorem oppSlotRound_slotRound {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) (h : ℕ) (w : ℕ → Fin r → ℂ) :
    oppSlotRound π ts h (slotRound π ts h w) = ((1 / 2 : ℂ) ^ (slotAxes ts h).length) • w := by
  unfold oppSlotRound slotRound
  rw [untwist_twist, bflys_bflys (slotBits_nodup hts hn π h)]
  simp [slotBits]

/-- The per-axis opposite rounds of slot `h`, in reverse axis order. -/
noncomputable def axisOppRounds {n : ℕ} (π : BitPerm n) (ts : List ℕ) (h : ℕ) :
    (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ :=
  run ((slotAxes ts h).map fun i => oppRound π ts i h).reverse

/-- The grouped opposite round equals the slot's per-axis opposite rounds in reverse order. -/
theorem axisOppRounds_eq {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) (h : ℕ) : axisOppRounds (r := r) π ts h = oppSlotRound π ts h := by
  have hgroup : run ((slotAxes ts h).map fun i => physRound (r := r) π ts i h) = slotRound π ts h := by
    funext v
    exact run_group π hts hn h (slotAxes ts h) ((List.nodup_range).filter _)
      (fun i hi => by
        simp only [slotAxes, List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
        exact hi) v
  set m := (slotAxes ts h).length
  have hc : ((2 : ℂ) ^ m) * (1 / 2 : ℂ) ^ m = 1 := by rw [← mul_pow]; norm_num
  funext v
  -- `v` is the forward image of `2^m · (axis opposite rounds v)`
  have hpre : slotRound π ts h (((2 : ℂ) ^ m) • axisOppRounds π ts h v) = v := by
    rw [← hgroup, run_map_smul _ (fun i c z => physRound_smul π ts i h c z)]
    unfold axisOppRounds
    rw [run_cancel_rev (β := ℕ) (α := ℕ → Fin r → ℂ) (fun i => physRound π ts i h)
      (fun i => oppRound π ts i h) (fun i z => physRound_oppRound π ts i h z)
      (fun i c z => physRound_smul π ts i h c z) (slotAxes ts h) v, smul_smul, hc, one_smul]
  conv_rhs => rw [← hpre]
  rw [oppSlotRound_slotRound hts hn π h, smul_smul, mul_comm, hc, one_smul]

omit [NeZero r] in
theorem run_flatMap_id {β : Type*} (g : β → List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ)) :
    ∀ (L : List β) (w : ℕ → Fin r → ℂ), run (L.flatMap g) w = run (L.map fun a => run (g a)) w
  | [], _ => rfl
  | a :: L, w => by
    rw [List.flatMap_cons, run_append, List.map_cons]
    exact run_flatMap_id g L _

/-- The opposite slot rounds, from the bottom slot up. -/
noncomputable def oppSlotRounds {n : ℕ} (π : BitPerm n) (ts : List ℕ) (H : ℕ) :
    List ((ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ) :=
  (List.range H).map (oppSlotRound π ts)

/-- Grouping the opposite schedule by slot. -/
theorem oppSchedule_oppSlotRounds {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) (H : ℕ) : oppSchedule (r := r) π ts H = run (oppSlotRounds (r := r) π ts H) := by
  funext w
  unfold oppSchedule oppSlotRounds slotPairs
  rw [List.map_flatMap, List.reverse_flatMap, List.reverse_reverse, run_flatMap_id]
  congr 1
  apply List.map_congr_left
  intro h _
  rw [← axisOppRounds_eq hts hn π h]
  unfold axisOppRounds
  simp [List.map_map, Function.comp_def]
  rfl

/-! ### Contraction and the computed opposite schedule -/

theorem untwist_contracts (n : ℕ) (f : ℕ → ℕ) : Contracts (r := r) n (untwist f) := by
  intro v ε hv y hy k
  simp only [untwist, shiftNegZ_apply, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hv y hy _

theorem untwist_additive (f : ℕ → ℕ) : Additive (r := r) (untwist f) := by
  intro a b
  funext y
  simp only [untwist, Pi.sub_apply]
  rw [sub_eq_add_neg, shiftNegZ_add_vec, shiftNegZ_neg, ← sub_eq_add_neg]

theorem oppSlotRound_contracts {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) (h : ℕ) :
    Contracts n (oppSlotRound (r := r) π ts h) ∧ Additive (oppSlotRound (r := r) π ts h) := by
  have hlog : Nat.log 2 ts.prod = n := by rw [hn, Nat.log_pow (by norm_num)]
  have hbits : ∀ P ∈ slotBits π ts (slotAxes ts h) h, P < n := by
    intro P hP
    simp only [slotBits, slotAxes, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hP
    obtain ⟨i, ⟨hi, hih⟩, rfl⟩ := hP
    have := axOff_add_len_le hts hi
    exact π.σ_lt _ (by omega)
  constructor
  · intro v ε hv
    exact run_contracts _ (fun G hG => by
      simp only [List.mem_map] at hG
      obtain ⟨P, hP, rfl⟩ := hG
      exact bfly_contracts (hbits P hP)) _ ε (untwist_contracts n _ v ε hv)
  · intro a b
    unfold oppSlotRound
    rw [untwist_additive]
    exact run_additive _ (fun G hG => by
      simp only [List.mem_map] at hG
      obtain ⟨P, -, rfl⟩ := hG
      exact bfly_additive P) _ _

/-- The computed opposite schedule: every opposite slot round rounded to the grid. -/
noncomputable def compOppSchedule (p : ℕ) {n : ℕ} (π : BitPerm n) (ts : List ℕ) (H : ℕ) :
    (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ :=
  roundRun p (oppSlotRounds π ts H)

/-- `compOppSchedule_close`: the computed opposite schedule over `H ≥ 1` slots stays within
`√2 · H · 2^(-p)` per coefficient of `F⁺ B⁻¹ L⁻¹ u`, whose entry with logical address `x` is stored
at `phys x`, and in the unit disk for unit-disk input. -/
theorem compOppSchedule_close {ts : List ℕ} (hts : PowAxes r ts) {n : ℕ} (hn : ts.prod = 2 ^ n)
    (π : BitPerm n) {H : ℕ} (hH : ∀ i < ts.length, axLen ts i ≤ H) (hH0 : 0 < H) (p : ℕ)
    (u : ℕ → Fin r → ℂ) :
    (∀ y < 2 ^ n, ∀ k, ‖compOppSchedule p π ts H u y k - oppExact ts (π.toPerm hn) u (π.logi y) k‖ <
      Real.sqrt 2 * H / 2 ^ p) ∧
    ((∀ y < 2 ^ n, ∀ k, ‖u y k‖ ≤ 1) → ∀ y < 2 ^ n, ∀ k, ‖compOppSchedule p π ts H u y k‖ ≤ 1) := by
  have hrounds : ∀ G ∈ oppSlotRounds (r := r) π ts H, Contracts n G ∧ Additive G := by
    intro G hG
    simp only [oppSlotRounds, List.mem_map] at hG
    obtain ⟨h, -, rfl⟩ := hG
    exact oppSlotRound_contracts hts hn π h
  have hlen : (oppSlotRounds (r := r) π ts H).length = H := by simp [oppSlotRounds]
  have hne : oppSlotRounds (r := r) π ts H ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  refine ⟨fun y hy k => ?_, fun hdisk => roundRun_disk p n _ (fun G hG => (hrounds G hG).1) u hdisk⟩
  have hlt := roundRun_lt p n _ hne hrounds u y hy k
  rw [← oppSchedule_oppSlotRounds hts hn π H, oppSchedule_eq hts hn π hH u hy, hlen] at hlt
  unfold compOppSchedule
  calc _ < (H : ℝ) * (Real.sqrt 2 / 2 ^ p) := hlt
    _ = Real.sqrt 2 * H / 2 ^ p := by ring

end IntegerMultBounds.Schoenhage
