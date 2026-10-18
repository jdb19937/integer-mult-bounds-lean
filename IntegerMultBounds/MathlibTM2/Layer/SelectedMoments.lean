module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Fin
public import IntegerMultBounds.MathlibTM2.Layer.OccurrenceRecurrence
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Forward
public import IntegerMultBounds.Networks.Certificates.T16.Geometry.Backward
public import IntegerMultBounds.Networks.Certificates.T16.Streams.Template

/-!
# Exact moment inequalities for the selected suppliers

The selected construction (upstream CrocSwap/integer-mult-bounds revision
0fdd7d82de03e43c9e5a1000dfbcd380d1b687d2, `research/community-frontier1094-audit/ASSEMBLY.json`
and the PR589 `EXPECTED.json` it cites) bills a supplier of parent width `m` with live stock `W`
and child-rank histogram `n_r` at saving `a` by

`(Σ n_r (r/m)^(1-a) + surcharge) / W`,

where the inherited bad-residue surcharge is `32 m² N (1/m)^(1-a) / 10^16` with
`N = Σ n_r` calls. The assembly charges it for the bit side only; for the complex side we
prove the native bill and also the conservative surcharged bill.

* complex (T16): `m = 73`, `W = 14336`, endpoint `a_c ≈ 0.00167546`; we prove the bill at
  `a = 7/4178 ≈ 0.00167544`.
* bit (PR589): `m = 64`, `W = 28416`, endpoint `a_b ≈ 0.00173343`; we prove the bill at
  `a = 10/5769 ≈ 0.00173340`.

Real powers are bounded by integer certificates: `(m/r)^(p/q) ≤ U/10^D` follows from
`m^p · 10^(D q) ≤ U^q · r^p`, checked with GMP-backed kernel arithmetic.

The T16 histogram is tied to the checked owner schedule: `t16Ranks` lists every child
occurrence (each of the 144 calls' charge chunks, then the residual inventory), and it is a
permutation of the expanded histogram by `selected_profile_cost`. The PR589 histogram is not yet
tied to Lean data; its occurrence theorem takes the named open link `Realizes L bitHistogram`.

None of this proves execution, child-size or hosting premises; see `OccurrenceRecurrence`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.SelectedMoments

open Finset

/-! ### Integer certificates for rational real powers -/

theorem rpow_div_le {x u : ℝ} {p q : ℕ} (hx : 0 ≤ x) (hu : 0 ≤ u) (hq : 0 < q)
    (h : x ^ p ≤ u ^ q) : x ^ ((p : ℝ) / q) ≤ u := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpow : (x ^ ((p : ℝ) / q)) ^ q = x ^ p := by
    rw [← Real.rpow_natCast (x ^ _), ← Real.rpow_mul hx, div_mul_cancel₀ _ hq',
      Real.rpow_natCast]
  exact le_of_pow_le_pow_left₀ hq.ne' hu (hpow ▸ h)

/-- One certified child power: `(r/m)^(1-p/q) ≤ (r/m) · U/10^D`. -/
theorem child_power_le {r m p q D U : ℕ} (hr : 0 < r) (hm : 0 < m) (hq : 0 < q)
    (h : m ^ p * 10 ^ (D * q) ≤ U ^ q * r ^ p) :
    ((r : ℝ) / m) ^ (1 - (p : ℝ) / q) ≤ (r : ℝ) / m * ((U : ℝ) / 10 ^ D) := by
  have hx : (0 : ℝ) < r / m := by positivity
  rw [Real.rpow_sub hx, Real.rpow_one, div_eq_mul_inv ((r : ℝ) / m),
    ← Real.inv_rpow hx.le, inv_div]
  apply mul_le_mul_of_nonneg_left _ hx.le
  apply rpow_div_le (by positivity) (by positivity) hq
  rw [div_pow, div_pow, div_le_div_iff₀ (by positivity) (by positivity), ← pow_mul]
  exact_mod_cast h

/-! ### Histogram moments -/

/-- `Σ n_r (r/m)^σ` for a histogram given as `(rank, count)` pairs. -/
noncomputable def histMoment (hist : List (ℕ × ℕ)) (m σ : ℝ) : ℝ :=
  (hist.map fun e => (e.2 : ℝ) * ((e.1 : ℝ) / m) ^ σ).sum

/-- Number of calls `N = Σ n_r`. -/
def callCount (hist : List (ℕ × ℕ)) : ℕ := (hist.map Prod.snd).sum

/-- The inherited bad-residue surcharge `32 m² N (1/m)^σ / 10^16`. -/
noncomputable def surcharge (hist : List (ℕ × ℕ)) (m σ : ℝ) : ℝ :=
  32 * m ^ 2 * callCount hist * (1 / m) ^ σ / 10 ^ 16

/-- Pointwise check of a certificate `(rank, count, U)`. -/
def certOk (m p q D : ℕ) (e : ℕ × ℕ × ℕ) : Bool :=
  decide (0 < e.1) && decide (m ^ p * 10 ^ (D * q) ≤ e.2.2 ^ q * e.1 ^ p)

theorem histMoment_le (cert : List (ℕ × ℕ × ℕ)) {m p q D : ℕ} (hm : 0 < m) (hq : 0 < q)
    (hcert : cert.all (certOk m p q D) = true) :
    histMoment (cert.map fun e => (e.1, e.2.1)) m (1 - (p : ℝ) / q) ≤
      ((cert.map fun e => e.2.1 * e.1 * e.2.2).sum : ℕ) / ((m : ℝ) * 10 ^ D) := by
  induction cert with
  | nil => simp [histMoment]
  | cons e cert ih =>
    simp only [List.all_cons, Bool.and_eq_true, certOk, decide_eq_true_eq] at hcert
    obtain ⟨⟨hr, hpow⟩, hrest⟩ := hcert
    have ih' := ih hrest
    simp only [histMoment, List.map_cons, List.sum_cons, Nat.cast_add] at ih' ⊢
    rw [add_div]
    refine add_le_add ?_ ih'
    calc (e.2.1 : ℝ) * ((e.1 : ℝ) / m) ^ (1 - (p : ℝ) / q)
        ≤ e.2.1 * ((e.1 : ℝ) / m * ((e.2.2 : ℝ) / 10 ^ D)) :=
          mul_le_mul_of_nonneg_left (child_power_le hr hm hq hpow) (by positivity)
      _ = _ := by push_cast; field_simp

/-- The surcharge is bounded by the certificate for rank one. -/
theorem surcharge_le (hist : List (ℕ × ℕ)) {m p q D U : ℕ} (hm : 0 < m) (hq : 0 < q)
    (h : m ^ p * 10 ^ (D * q) ≤ U ^ q * 1 ^ p) :
    surcharge hist m (1 - (p : ℝ) / q) ≤
      ((32 * m * callCount hist * U : ℕ) : ℝ) / (10 ^ 16 * 10 ^ D) := by
  have hone := child_power_le (r := 1) Nat.one_pos hm hq h
  simp only [Nat.cast_one] at hone
  unfold surcharge
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  calc 32 * (m : ℝ) ^ 2 * callCount hist * (1 / m) ^ (1 - (p : ℝ) / q) / 10 ^ 16
      ≤ 32 * (m : ℝ) ^ 2 * callCount hist * (1 / m * ((U : ℝ) / 10 ^ D)) / 10 ^ 16 := by
        gcongr
    _ = _ := by push_cast; field_simp

/-! ### Selected data -/

/-- Complex certificate `(rank, count, U)` with `(73/r)^(7/4178) ≤ U/10^10`. -/
def complexCertificate : List (ℕ × ℕ × ℕ) :=
  [(1, 349604, 10072143181), (2, 60192, 10060452904), (3, 62585, 10053620821),
   (4, 20448, 10048776196), (5, 11808, 10045020020), (7, 7, 10039358836),
   (8, 1152, 10037113040), (48, 4866, 10007026903)]

/-- Bit certificate `(rank, count, U)` with `(64/r)^(10/5769) ≤ U/10^10`. -/
def bitCertificate : List (ℕ × ℕ × ℕ) :=
  [(1, 381024, 10072350666), (2, 400416, 10060255972), (3, 22752, 10053187763),
   (4, 26880, 10048175801), (5, 29376, 10044289942), (6, 17376, 10041116080),
   (7, 26784, 10038433400), (42, 288, 10007303992)]

/-- The selected T16 complex child histogram (ASSEMBLY.json `complex_profile`). -/
def complexHistogram : List (ℕ × ℕ) :=
  [(1, 349604), (2, 60192), (3, 62585), (4, 20448), (5, 11808), (7, 7), (8, 1152), (48, 4866)]

/-- The PR589 nine-stage bit child histogram (`EXPECTED.json` `nine.profile`). -/
def bitHistogram : List (ℕ × ℕ) :=
  [(1, 381024), (2, 400416), (3, 22752), (4, 26880), (5, 29376), (6, 17376), (7, 26784),
   (42, 288)]

theorem complexCertificate_histogram :
    complexCertificate.map (fun e => (e.1, e.2.1)) = complexHistogram := rfl

theorem bitCertificate_histogram :
    bitCertificate.map (fun e => (e.1, e.2.1)) = bitHistogram := rfl

theorem complexCertificate_ok : complexCertificate.all (certOk 73 7 4178 10) = true := by
  decide +kernel

theorem bitCertificate_ok : bitCertificate.all (certOk 64 10 5769 10) = true := by
  decide +kernel

/-- Complex saving `7/4178`, just below the endpoint `0.0016754626768081035`. -/
noncomputable def complexSaving : ℝ := 7 / 4178

/-- Bit saving `10/5769`, just below the endpoint `0.0017334270395898442`. -/
noncomputable def bitSaving : ℝ := 10 / 5769

theorem complexSaving_eq : complexSaving = ((7 : ℕ) : ℝ) / (4178 : ℕ) := by
  norm_num [complexSaving]

theorem bitSaving_eq : bitSaving = ((10 : ℕ) : ℝ) / (5769 : ℕ) := by
  norm_num [bitSaving]

theorem complex_histMoment_le :
    histMoment complexHistogram 73 (1 - complexSaving) ≤
      (10465279390935855 : ℝ) / (73 * 10 ^ 10) := by
  have h := histMoment_le complexCertificate (m := 73) (p := 7) (q := 4178) (D := 10)
    (by norm_num) (by norm_num) complexCertificate_ok
  rw [complexCertificate_histogram, ← complexSaving_eq] at h
  refine h.trans (le_of_eq ?_)
  norm_num [complexCertificate]

theorem bit_histMoment_le :
    histMoment bitHistogram 64 (1 - bitSaving) ≤
      (18186238551909408 : ℝ) / (64 * 10 ^ 10) := by
  have h := histMoment_le bitCertificate (m := 64) (p := 10) (q := 5769) (D := 10)
    (by norm_num) (by norm_num) bitCertificate_ok
  rw [bitCertificate_histogram, ← bitSaving_eq] at h
  refine h.trans (le_of_eq ?_)
  norm_num [bitCertificate]

theorem complex_surcharge_le :
    surcharge complexHistogram 73 (1 - complexSaving) ≤
      ((32 * 73 * 510662 * 10072143181 : ℕ) : ℝ) / (10 ^ 16 * 10 ^ 10) := by
  have h := surcharge_le complexHistogram (m := 73) (p := 7) (q := 4178) (D := 10)
    (U := 10072143181) (by norm_num) (by norm_num) (by decide +kernel)
  rw [← complexSaving_eq] at h
  simpa [callCount, complexHistogram] using h

theorem bit_surcharge_le :
    surcharge bitHistogram 64 (1 - bitSaving) ≤
      ((32 * 64 * 904896 * 10072350666 : ℕ) : ℝ) / (10 ^ 16 * 10 ^ 10) := by
  have h := surcharge_le bitHistogram (m := 64) (p := 10) (q := 5769) (D := 10)
    (U := 10072350666) (by norm_num) (by norm_num) (by decide +kernel)
  rw [← bitSaving_eq] at h
  simpa [callCount, bitHistogram] using h

/-! ### The selected bills -/

/-- Native complex bill (the assembly's complex surcharge model is off). -/
theorem complex_bill_le : histMoment complexHistogram 73 (1 - complexSaving) / 14336 ≤ 1 := by
  rw [div_le_one (by norm_num)]
  exact complex_histMoment_le.trans (by norm_num)

/-- Conservative complex bill, including the bad-residue surcharge. -/
theorem complex_surcharged_bill_le :
    (histMoment complexHistogram 73 (1 - complexSaving) +
      surcharge complexHistogram 73 (1 - complexSaving)) / 14336 ≤ 1 := by
  rw [div_le_one (by norm_num)]
  exact (add_le_add complex_histMoment_le complex_surcharge_le).trans (by norm_num)

/-- PR589 bit bill with its surcharge. -/
theorem bit_bill_le :
    (histMoment bitHistogram 64 (1 - bitSaving) +
      surcharge bitHistogram 64 (1 - bitSaving)) / 28416 ≤ 1 := by
  rw [div_le_one (by norm_num)]
  exact (add_le_add bit_histMoment_le bit_surcharge_le).trans (by norm_num)

/-! ### Occurrence lists realizing a histogram -/

/-- Each histogram entry `(r, n)` expanded into `n` occurrences of rank `r`. -/
def expand (hist : List (ℕ × ℕ)) : List ℕ := hist.flatMap fun e => List.replicate e.2 e.1

/-- An occurrence list realizes a histogram when it is a reordering of its expansion. -/
def Realizes (L : List ℕ) (hist : List (ℕ × ℕ)) : Prop := L.Perm (expand hist)

theorem sum_map_expand {M : Type*} [AddCommMonoid M] (hist : List (ℕ × ℕ)) (f : ℕ → M) :
    ((expand hist).map f).sum = (hist.map fun e => e.2 • f e.1).sum := by
  induction hist with
  | nil => simp [expand]
  | cons e hist ih =>
    simp only [expand, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

theorem Realizes.sum_map {L : List ℕ} {hist : List (ℕ × ℕ)} (hL : Realizes L hist)
    (f : ℕ → ℝ) : (L.map f).sum = (hist.map fun e => (e.2 : ℝ) * f e.1).sum := by
  rw [(hL.map f).sum_eq, sum_map_expand]
  simp only [nsmul_eq_mul]

theorem count_eq_sum_ite (a : ℕ) (L : List ℕ) :
    L.count a = (L.map fun x => if x = a then 1 else 0).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.count_cons, ih, List.map_cons, List.sum_cons, add_comm]
    simp

/-- Equal natural-valued costs under every price determine the occurrence multiset. -/
theorem realizes_of_cost {L : List ℕ} {hist : List (ℕ × ℕ)}
    (h : ∀ price : ℕ → ℕ, (L.map price).sum = (hist.map fun e => e.2 * price e.1).sum) :
    Realizes L hist := by
  rw [Realizes, List.perm_iff_count]
  intro a
  rw [count_eq_sum_ite, count_eq_sum_ite, h, sum_map_expand]
  simp only [smul_eq_mul]

/-- The occurrence moment of a realized histogram is its histogram moment over `W`. -/
theorem occurrence_moment_eq {L : List ℕ} {hist : List (ℕ × ℕ)} (hL : Realizes L hist)
    (m W σ : ℝ) :
    ∑ i : Fin L.length, (1 / W) * ((L[i.1] : ℝ) / m) ^ σ = histMoment hist m σ / W := by
  rw [Fin.sum_univ_fun_getElem L (fun r => (1 / W) * ((r : ℝ) / m) ^ σ),
    List.sum_map_mul_left, hL.sum_map, histMoment]
  ring

/-! ### T16 child occurrences from the native traces -/

section T16

open IntegerMultBounds.Networks.Certificates.T16

/-- The child rank charged by a trace event: frame climbs and center moves. -/
def eventRank : Trace.Event → Option ℕ
  | .climb _ _ _ _ rank => some rank
  | .center _ _ _ rank => some rank
  | _ => none

/-- Child ranks charged by one call in the given orientation. -/
def callRanks (backward : Bool) : List ℕ :=
  (if backward then Trace.backwardEvents else Trace.forwardEvents).filterMap eventRank

/-- Every charged rank is the dimension jump of a certified frame edge. -/
theorem callRanks_geometry {backward : Bool} {rank : ℕ} (h : rank ∈ callRanks backward) :
    ∃ old next, Geometry.EdgeGood Geometry.catalog old next rank := by
  obtain ⟨event, hmem, hrank⟩ := List.mem_filterMap.mp h
  have hgood : Geometry.EventGood Geometry.catalog backward event := by
    cases backward
    · exact Geometry.forward_geometry event hmem
    · exact Geometry.backward_geometry event hmem
  cases event <;> simp only [eventRank, Option.some.injEq, reduceCtorEq] at hrank <;>
    subst hrank <;> simp only [Geometry.EventGood] at hgood
  · exact ⟨_, _, hgood⟩
  · split at hgood
    · exact ⟨_, _, hgood⟩
    · exact ⟨_, _, hgood⟩

/-- The per-call rank profile `(rank, count)`. -/
def callProfile : List (ℕ × ℕ) :=
  [(1, 2412), (2, 418), (3, 432), (4, 142), (5, 82), (8, 8)]

def profileRanks : List ℕ := (callProfile.map fun e => List.replicate e.2 e.1).flatten

theorem perm_of_counts {l l' ks : List ℕ} (hl : ∀ x ∈ l, x ∈ ks) (hl' : ∀ x ∈ l', x ∈ ks)
    (hcount : ks.all (fun k => l.count k == l'.count k) = true) : l.Perm l' := by
  rw [List.perm_iff_count]
  intro a
  by_cases ha : a ∈ ks
  · simpa using List.all_eq_true.mp hcount a ha
  · rw [List.count_eq_zero.mpr (fun hx => ha (hl a hx)),
      List.count_eq_zero.mpr (fun hx => ha (hl' a hx))]

theorem forward_ranks_all :
    (callRanks false).all (· ∈ [1, 2, 3, 4, 5, 8]) = true := by decide +kernel

theorem backward_ranks_all :
    (callRanks true).all (· ∈ [1, 2, 3, 4, 5, 8]) = true := by decide +kernel

theorem forward_ranks_count :
    [1, 2, 3, 4, 5, 8].all (fun k => (callRanks false).count k == profileRanks.count k) = true := by
  decide +kernel

theorem backward_ranks_count :
    [1, 2, 3, 4, 5, 8].all (fun k => (callRanks true).count k == profileRanks.count k) = true := by
  decide +kernel

/-- Both orientations charge exactly the per-call profile. -/
theorem callRanks_perm (backward : Bool) : (callRanks backward).Perm profileRanks := by
  have hprofile : ∀ x ∈ profileRanks, x ∈ [1, 2, 3, 4, 5, 8] := by
    simpa using (by decide +kernel : profileRanks.all (· ∈ [1, 2, 3, 4, 5, 8]) = true)
  cases backward
  · exact perm_of_counts (by simpa using forward_ranks_all) hprofile forward_ranks_count
  · exact perm_of_counts (by simpa using backward_ranks_all) hprofile backward_ranks_count

/-- The residual (idle) inventory added to the scheduled calls. -/
def idleRanks : List ℕ :=
  List.replicate 2276 1 ++ List.replicate 377 3 ++ List.replicate 7 7 ++ List.replicate 4866 48

/-- One call per stage and replica, in the stage's orientation. -/
def scheduledRanks : List ℕ :=
  ((List.range 9).flatMap fun s =>
    (List.range 16).map fun _ => callRanks (Streams.localReverse s)).flatten

/-- Every T16 child occurrence: the 144 scheduled calls, then the residual inventory. -/
def t16Ranks : List ℕ := scheduledRanks ++ idleRanks

theorem sum_flatten_const {l : List (List ℕ)} {price : ℕ → ℕ} {c : ℕ}
    (h : ∀ x ∈ l, (x.map price).sum = c) : (l.flatten.map price).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatten_cons, List.map_append, List.sum_append, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem x hy), List.length_cons]
    ring

theorem scheduledRanks_cost (price : ℕ → ℕ) :
    (scheduledRanks.map price).sum = 144 * (profileRanks.map price).sum := by
  rw [scheduledRanks, sum_flatten_const (c := (profileRanks.map price).sum)]
  · rfl
  · intro x hx
    obtain ⟨s, -, hs⟩ := List.mem_flatMap.mp hx
    obtain ⟨-, -, rfl⟩ := List.mem_map.mp hs
    exact ((callRanks_perm _).map price).sum_eq

theorem t16Ranks_cost (price : ℕ → ℕ) :
    (t16Ranks.map price).sum = (complexHistogram.map fun e => e.2 * price e.1).sum := by
  rw [t16Ranks, List.map_append, List.sum_append, scheduledRanks_cost]
  simp only [profileRanks, callProfile, idleRanks, complexHistogram, List.map_append,
    List.sum_append, List.map_replicate, List.sum_replicate,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.sum_cons,
    List.sum_nil, smul_eq_mul]
  ring

theorem t16Ranks_realizes : Realizes t16Ranks complexHistogram :=
  realizes_of_cost t16Ranks_cost

/-- The T16 occurrence moment in the form consumed by
`OccurrenceRecurrence.rank_moment_le`: weight `1/14336` per occurrence, `m = 73`. -/
theorem t16_occurrence_moment_le :
    ∑ i : Fin t16Ranks.length,
      (1 / (14336 : ℝ)) * ((t16Ranks[i.1] : ℝ) / 73) ^ (1 - complexSaving) ≤ 1 := by
  rw [occurrence_moment_eq t16Ranks_realizes]
  exact complex_bill_le

/-- The T16 moment with the conservative surcharge left as unused potential. -/
theorem t16_occurrence_moment_le_surcharged :
    ∑ i : Fin t16Ranks.length,
      (1 / (14336 : ℝ)) * ((t16Ranks[i.1] : ℝ) / 73) ^ (1 - complexSaving) ≤
      1 - surcharge complexHistogram 73 (1 - complexSaving) / 14336 := by
  rw [occurrence_moment_eq t16Ranks_realizes]
  have := complex_surcharged_bill_le
  rw [add_div] at this
  linarith

/-- Consumer check: per-occurrence child sizes `≤ (rank/73) · parent` contract the
`(1 - complexSaving)`-power potential. -/
theorem t16_child_power_le (childSize : Fin t16Ranks.length → ℕ) {parentSize : ℝ}
    (hparent : 0 ≤ parentSize)
    (hsize : ∀ i, (childSize i : ℝ) ≤ ((t16Ranks[i.1] : ℝ) / 73) * parentSize) :
    ∑ i, (1 / (14336 : ℝ)) * (childSize i : ℝ) ^ (1 - complexSaving) ≤
      1 * parentSize ^ (1 - complexSaving) :=
  OccurrenceRecurrence.rank_moment_le (fun i => t16Ranks[i.1]) childSize _ hparent
    (by norm_num) (by norm_num [complexSaving]) (fun _ => by norm_num) hsize
    t16_occurrence_moment_le

end T16

/-! ### PR589 occurrences (open link) -/

/-- Open link: an occurrence list for the PR589 bit supplier realizing `bitHistogram`.
No Lean data yet produces this list; consumers must supply it. -/
theorem bit_occurrence_moment_le {L : List ℕ} (hL : Realizes L bitHistogram) :
    ∑ i : Fin L.length, (1 / (28416 : ℝ)) * ((L[i.1] : ℝ) / 64) ^ (1 - bitSaving) ≤
      1 - surcharge bitHistogram 64 (1 - bitSaving) / 28416 := by
  rw [occurrence_moment_eq hL]
  have := bit_bill_le
  rw [add_div] at this
  linarith

end IntegerMultBounds.MathlibTM2.Layer.SelectedMoments
