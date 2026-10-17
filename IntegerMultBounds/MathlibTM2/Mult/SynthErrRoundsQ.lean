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
* `grid`: every coefficient lies on the `p`-bit grid.

`fwdRoundsQ`, `oppRoundsQ` run such rounds in the orders of `fwdRounds` and `oppRounds`.
`fwdRoundsQ_err`, `oppRoundsQ_err`: input error `e` gives error at most `e + k η`; the disk and
the grid are preserved. `rdOp`: the truncation `Q_p` after the exact round is a `RoundOp` with
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
  err : ∀ h u, ∀ n < 2 ^ N, ∀ c, ‖Q h u n c - R h u n c‖ ≤ η
  dom : ∀ h u, ∀ n < 2 ^ N, ∀ c, ‖Q h u n c‖ ≤ ‖R h u n c‖
  grid : ∀ h u, GridR p (Q h u)

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

lemma RoundOp.supLe (F : RoundOp N p R η) {h : ℕ} {u : Recs r} {a : ℝ}
    (hR : SupLe N (R h u) a) : SupLe N (F.Q h u) a :=
  fun n hn c => (F.dom h u n hn c).trans (hR n hn c)

/-- One computed round against the exact round of another array. -/
lemma RoundOp.round_err (F : RoundOp N p R η) (hlin : ∀ h u v, R h (u - v) = R h u - R h v)
    (hc : ∀ h {w : Recs r} {a : ℝ}, SupLe N w a → SupLe N (R h w) a) (h : ℕ) {u v : Recs r}
    {e : ℝ} (he : SupLe N (u - v) e) : SupLe N (F.Q h u - R h v) (e + η) := by
  intro n hn c
  have h1 := F.err h u n hn c
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

/-- `k` computed forward rounds stay within `e + k η` of the exact rounds. -/
theorem fwdRoundsQ_err (F : RoundOp es.sum p (fwdRound es) η) :
    ∀ (k : ℕ) {u v : Recs r} {e : ℝ}, SupLe es.sum (u - v) e →
      SupLe es.sum (fwdRoundsQ F k u - fwdRounds es k v) (e + k * η)
  | 0, u, v, e, h => by simpa [fwdRoundsQ, fwdRounds] using h
  | k + 1, u, v, e, h => by
    have h' := F.round_err (fwdRound_sub es) (fwdRound_supLe es) k h
    refine (fwdRoundsQ_err F k h').mono (le_of_eq ?_)
    push_cast; ring

/-- `k` computed opposite rounds stay within `e + k η` of the exact rounds. -/
theorem oppRoundsQ_err (F : RoundOp es.sum p (oppRound es) η) :
    ∀ (k : ℕ) {u v : Recs r} {e : ℝ}, SupLe es.sum (u - v) e →
      SupLe es.sum (oppRoundsQ F k u - oppRounds es k v) (e + k * η)
  | 0, u, v, e, h => by simpa [oppRoundsQ, oppRounds] using h
  | k + 1, u, v, e, h => by
    have h' := F.round_err (oppRound_sub es) (oppRound_supLe es) k (oppRoundsQ_err F k h)
    refine h'.mono (le_of_eq ?_)
    push_cast; ring

theorem fwdRoundsQ_supLe (F : RoundOp es.sum p (fwdRound es) η) :
    ∀ (k : ℕ) {u : Recs r} {a : ℝ}, SupLe es.sum u a → SupLe es.sum (fwdRoundsQ F k u) a
  | 0, _, _, h => h
  | k + 1, _, _, h => fwdRoundsQ_supLe F k (F.supLe (fwdRound_supLe es k h))

theorem oppRoundsQ_supLe (F : RoundOp es.sum p (oppRound es) η) :
    ∀ (k : ℕ) {u : Recs r} {a : ℝ}, SupLe es.sum u a → SupLe es.sum (oppRoundsQ F k u) a
  | 0, _, _, h => h
  | k + 1, _, _, h => F.supLe (oppRound_supLe es k (oppRoundsQ_supLe F k h))

omit [NeZero r] in
theorem fwdRoundsQ_grid {R : ℕ → Recs r → Recs r} (F : RoundOp es.sum p R η) :
    ∀ (k : ℕ) {u : Recs r}, GridR p u → GridR p (fwdRoundsQ F k u)
  | 0, _, h => h
  | k + 1, _, _ => fwdRoundsQ_grid F k (F.grid _ _)

omit [NeZero r] in
theorem oppRoundsQ_grid {R : ℕ → Recs r → Recs r} (F : RoundOp es.sum p R η) :
    ∀ (k : ℕ) {u : Recs r}, GridR p u → GridR p (oppRoundsQ F k u)
  | 0, _, h => h
  | _ + 1, _, _ => F.grid _ _

/-! ### The truncation as a computed round -/

/-- `Q_p` after the exact round. -/
noncomputable def rdOp (p : ℕ) (R : ℕ → Recs r → Recs r) :
    RoundOp es.sum p R (Real.sqrt 2 / 2 ^ p) where
  Q h u := rdR p (R h u)
  err h u n _ c := (rdR_sub_lt p (R h u) n c).le
  dom _ _ _ _ _ := norm_rhoC_le p _
  grid _ _ := gridR_rdR p _

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

end IntegerMultBounds.MathlibTM2.Mult.SynthErr
