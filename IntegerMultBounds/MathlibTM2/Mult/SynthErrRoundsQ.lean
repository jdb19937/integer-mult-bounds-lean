module

public import IntegerMultBounds.MathlibTM2.Mult.SynthErrRounds

/-!
# Computed transform rounds with an approximate rounding

`SynthErrRounds` follows each exact round by the truncation `Q_p`. A rounded synthetic layer
returns an array that is only close to the exact round. `RoundOp N p R η` records what the error
analysis needs of a computed round `Q h` against an exact round `R h`, on the first `2^N`
records:

* `err`: every coefficient is within `η` of the exact one;
* `dom`: no coefficient is larger in modulus than the exact one (so the disk is preserved);
* `grid`: every coefficient lies on the `p`-bit grid;

all three on disk inputs on the `p`-bit grid, the inputs on which the machine round is defined.

`fwdRoundsQ`, `oppRoundsQ` run such rounds in the orders of `fwdRounds` and `oppRounds`.
`fwdRoundsQ_err`, `oppRoundsQ_err`: input error `e` gives error at most `e + k η` on disk grid
inputs; `fwdRoundsQ_dom`, `oppRoundsQ_dom`: the disk and the grid are preserved. `rdOp`: the truncation `Q_p` after the exact round is a `RoundOp` with
`η = √2 2^{-p}`, and `fwdRoundsQ_rdOp`, `oppRoundsQ_rdOp` recover `fwdRoundsC`, `oppRoundsC`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.SynthErr

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct
open IntegerMultBounds.MathlibTM2.Mult.Rounds

variable {r : ℕ}

/-- A computed round `Q h` against the exact round `R h`, on the first `2^N` records. -/
structure RoundOp (N p : ℕ) (R : ℕ → Recs r → Recs r) (η : ℝ) where
  Q : ℕ → Recs r → Recs r
  err : ∀ h u, SupLe N u 1 → GridR p u → ∀ n < 2 ^ N, ∀ c, ‖Q h u n c - R h u n c‖ ≤ η
  dom : ∀ h u, SupLe N u 1 → GridR p u → ∀ n < 2 ^ N, ∀ c, ‖Q h u n c‖ ≤ ‖R h u n c‖
  grid : ∀ h u, SupLe N u 1 → GridR p u → GridR p (Q h u)

section Ops

variable {N p : ℕ} {R : ℕ → Recs r → Recs r} {η : ℝ}

/-- The computed forward rounds at `h = k - 1, …, 0`. -/
noncomputable def fwdRoundsQ (F : RoundOp N p R η) : ℕ → Recs r → Recs r
  | 0, u => u
  | k + 1, u => fwdRoundsQ F k (F.Q k u)

/-- The computed opposite rounds at `h = 0, …, k - 1`. -/
noncomputable def oppRoundsQ (F : RoundOp N p R η) : ℕ → Recs r → Recs r
  | 0, u => u
  | k + 1, u => F.Q k (oppRoundsQ F k u)

lemma RoundOp.supLe (F : RoundOp N p R η) {h : ℕ} {u : Recs r} {a : ℝ} (hu : SupLe N u 1)
    (hg : GridR p u) (hR : SupLe N (R h u) a) : SupLe N (F.Q h u) a :=
  fun n hn c => (F.dom h u hu hg n hn c).trans (hR n hn c)

/-- One computed round against the exact round of another array. -/
lemma RoundOp.round_err (F : RoundOp N p R η) (hlin : ∀ h u v, R h (u - v) = R h u - R h v)
    (hc : ∀ h {w : Recs r} {a : ℝ}, SupLe N w a → SupLe N (R h w) a) (h : ℕ) {u v : Recs r}
    (hu : SupLe N u 1) (hg : GridR p u)
    {e : ℝ} (he : SupLe N (u - v) e) : SupLe N (F.Q h u - R h v) (e + η) := by
  intro n hn c
  have h1 := F.err h u hu hg n hn c
  have h2 : ‖R h u n c - R h v n c‖ ≤ e := by
    have := hc h he n hn c
    rwa [hlin] at this
  calc ‖(F.Q h u - R h v) n c‖ = ‖(F.Q h u n c - R h u n c) + (R h u n c - R h v n c)‖ := by
        simp only [Pi.sub_apply]; congr 1; abel
    _ ≤ ‖F.Q h u n c - R h u n c‖ + ‖R h u n c - R h v n c‖ := norm_add_le _ _
    _ ≤ e + η := by linarith

end Ops

section Rounds

variable [NeZero r] (es : List ℕ) {p : ℕ} {η : ℝ}

/-- The computed forward rounds keep disk grid arrays disk grid arrays. -/
theorem fwdRoundsQ_dom (F : RoundOp es.sum p (fwdRound es) η) :
    ∀ (k : ℕ) {u : Recs r}, SupLe es.sum u 1 → GridR p u →
      SupLe es.sum (fwdRoundsQ F k u) 1 ∧ GridR p (fwdRoundsQ F k u)
  | 0, _, hu, hg => ⟨hu, hg⟩
  | k + 1, _, hu, hg =>
    fwdRoundsQ_dom F k (F.supLe hu hg (fwdRound_supLe es k hu)) (F.grid k _ hu hg)

/-- The computed opposite rounds keep disk grid arrays disk grid arrays. -/
theorem oppRoundsQ_dom (F : RoundOp es.sum p (oppRound es) η) :
    ∀ (k : ℕ) {u : Recs r}, SupLe es.sum u 1 → GridR p u →
      SupLe es.sum (oppRoundsQ F k u) 1 ∧ GridR p (oppRoundsQ F k u)
  | 0, _, hu, hg => ⟨hu, hg⟩
  | k + 1, _, hu, hg => by
    obtain ⟨h1, h2⟩ := oppRoundsQ_dom F k hu hg
    exact ⟨F.supLe h1 h2 (oppRound_supLe es k h1), F.grid k _ h1 h2⟩

/-- `k` computed forward rounds stay within `e + k η` of the exact rounds. -/
theorem fwdRoundsQ_err (F : RoundOp es.sum p (fwdRound es) η) :
    ∀ (k : ℕ) {u v : Recs r} {e : ℝ}, SupLe es.sum u 1 → GridR p u →
      SupLe es.sum (u - v) e → SupLe es.sum (fwdRoundsQ F k u - fwdRounds es k v) (e + k * η)
  | 0, u, v, e, _, _, h => by simpa [fwdRoundsQ, fwdRounds] using h
  | k + 1, u, v, e, hu, hg, h => by
    have h' := F.round_err (fwdRound_sub es) (fwdRound_supLe es) k hu hg h
    refine (fwdRoundsQ_err F k (F.supLe hu hg (fwdRound_supLe es k hu)) (F.grid k _ hu hg)
      h').mono (le_of_eq ?_)
    push_cast; ring

/-- `k` computed opposite rounds stay within `e + k η` of the exact rounds. -/
theorem oppRoundsQ_err (F : RoundOp es.sum p (oppRound es) η) :
    ∀ (k : ℕ) {u v : Recs r} {e : ℝ}, SupLe es.sum u 1 → GridR p u →
      SupLe es.sum (u - v) e → SupLe es.sum (oppRoundsQ F k u - oppRounds es k v) (e + k * η)
  | 0, u, v, e, _, _, h => by simpa [oppRoundsQ, oppRounds] using h
  | k + 1, u, v, e, hu, hg, h => by
    obtain ⟨h1, h2⟩ := oppRoundsQ_dom es F k hu hg
    have h' := F.round_err (oppRound_sub es) (oppRound_supLe es) k h1 h2
      (oppRoundsQ_err F k hu hg h)
    refine h'.mono (le_of_eq ?_)
    push_cast; ring

/-! ### The truncation as a computed round -/

/-- `Q_p` after the exact round. -/
noncomputable def rdOp (p : ℕ) (R : ℕ → Recs r → Recs r) :
    RoundOp es.sum p R (Real.sqrt 2 / 2 ^ p) where
  Q h u := rdR p (R h u)
  err h u _ _ n _ c := (rdR_sub_lt p (R h u) n c).le
  dom _ _ _ _ _ _ _ := norm_rhoC_le p _
  grid _ _ _ _ := gridR_rdR p _

theorem fwdRoundsQ_rdOp (p : ℕ) : ∀ (k : ℕ) (u : Recs r),
    fwdRoundsQ (rdOp es p (fwdRound es)) k u = fwdRoundsC p es k u
  | 0, _ => rfl
  | k + 1, _ => fwdRoundsQ_rdOp p k _

theorem oppRoundsQ_rdOp (p : ℕ) : ∀ (k : ℕ) (u : Recs r),
    oppRoundsQ (rdOp es p (oppRound es)) k u = oppRoundsC p es k u
  | 0, _ => rfl
  | k + 1, u => by
    show rdR p (oppRound es k (oppRoundsQ _ k u)) = rdR p (oppRound es k (oppRoundsC p es k u))
    rw [oppRoundsQ_rdOp p k u]

end Rounds

/-! ### Computed rounds on flat arrays in a layout -/

section Flat

open IntegerMultBounds.MathlibTM2.Layer

theorem ofBits_toBits {N n : ℕ} (hn : n < 2 ^ N) : ofBits (toBits N n) = n := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_ofBits]
  split_ifs with hj
  · simp only [toBits]
    by_cases h : n.testBit j <;> simp [h]
  · exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hn
      (pow_le_pow_right₀ (by norm_num) (not_lt.1 hj)))).symm

variable {N p : ℕ} {η : ℝ}

/-- A computed round on flat arrays stored in the layout `L`, against the exact flat round `Rf`
in the logical layout. -/
structure FlatRoundOp (N p : ℕ) (L : Equiv.Perm (Fin N)) (Rf : ℕ → Arr (Fin r) N → Arr (Fin r) N)
    (η : ℝ) where
  Q : ℕ → Arr (Fin r) N → Arr (Fin r) N
  err : ∀ h f q, ‖Q h f q - relabel L (Rf h (relabel L.symm f)) q‖ ≤ η
  dom : ∀ h f q, ‖Q h f q‖ ≤ ‖relabel L (Rf h (relabel L.symm f)) q‖
  grid : ∀ h f q, IsFixed p (Q h f q)

/-- The record form of a flat computed round. -/
noncomputable def FlatRoundOp.toRoundOp {L : Equiv.Perm (Fin N)}
    {R : ℕ → Recs r → Recs r} {Rf : ℕ → Arr (Fin r) N → Arr (Fin r) N}
    (hR : ∀ h u, flat N (R h u) = Rf h (flat N u)) (F : FlatRoundOp N p L Rf η) :
    RoundOp N p R η where
  Q h u := unflat (relabel L.symm (F.Q h (relabel L (flat N u))))
  err h u _ _ n hn c := by
    have := F.err h (relabel L (flat N u)) (c, toBits N n ∘ L.symm)
    rw [relabel_symm_relabel, ← hR] at this
    have e : relabel L (flat N (R h u)) (c, toBits N n ∘ L.symm) = R h u n c := by
      simp only [relabel, flat, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id,
        ofBits_toBits hn]
    rw [e] at this
    exact this
  dom h u _ _ n hn c := by
    have := F.dom h (relabel L (flat N u)) (c, toBits N n ∘ L.symm)
    rw [relabel_symm_relabel, ← hR] at this
    have e : relabel L (flat N (R h u)) (c, toBits N n ∘ L.symm) = R h u n c := by
      simp only [relabel, flat, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id,
        ofBits_toBits hn]
    rw [e] at this
    exact this
  grid h u _ _ n c := F.grid h _ _

end Flat

end IntegerMultBounds.MathlibTM2.Mult.SynthErr
