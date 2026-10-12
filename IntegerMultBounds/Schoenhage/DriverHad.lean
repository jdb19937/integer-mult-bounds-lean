module

public import IntegerMultBounds.Schoenhage.DriverRounds
public import IntegerMultBounds.Schoenhage.DriverScript
public import IntegerMultBounds.Schoenhage.DriverRest
public import IntegerMultBounds.Schoenhage.DriverMath

/-! The Hadamard part of a slot's round on the drivers' bank (§6 task 6). Between rounds the named
tapes hold the array, the record width in unary, the round script and the layout script, all else
empty (`rnamed`). The kind word selects the chunk step or the prefix step (`hadStep`), which replaces
the array's records by the slot's Hadamard output (`hadOut`) and consumes the slot's Hadamard words
(`runs_hadStep`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct

variable {A tL nL : ℕ}

/-- The named tapes between rounds: array `X`, record width `w`, round script `S`, layout script `T7`. -/
def rnamed (w : ℕ) (X : List Bool) (S T7 : WTape) : Fin 13 → WTape := fun i =>
  if i = 0 then reg X else if i = 2 then reg (ones w) else if i = 6 then S else if i = 7 then T7 else emp

/-- The Hadamard part of a round: the chunk step for kind word `[true]`, else the prefix step. -/
noncomputable def hadStep {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A) : Cmd A (DB tL nL) :=
  .cond (nm tL nL 6) (chunkStep M ht haA) (bflyStep A tL nL)

/-- The records after slot `h`'s Hadamard part. -/
noncomputable def hadOut {r : ℕ} (p : ℕ) (ts : List ℕ) (ℓ K h : ℕ) (R : List (Rec r)) : List (Rec r) :=
  if h < (ℓ - 1) % K then
    (bflysRecs ((List.range ts.length).map (prefixBase ts.length ℓ K h + ·)) R).map (truncRec ts.length)
  else if h < ℓ - 1 then
    layerOut p ts.length K (rhoOf ℓ K h) (2 ^ (chunkOf ℓ K h * ts.length * K)) (2 ^ Nat.log 2 ts.prod) R
  else (bflysRecs ((List.range (longs ts ℓ).length).map (topBase ts.length ℓ K + ·)) R).map
    (truncRec (longs ts ℓ).length)

/-- The cost bound of slot `h`'s Hadamard part, with layer calls within `CL`. -/
def hadCost (p d r w : ℕ) (ts : List ℕ) (ℓ K CL h : ℕ) : ℕ :=
  (if h < (ℓ - 1) % K then prefixCost w ts.length (2 * r * ts.prod) else if h < ℓ - 1 then CL
    else prefixCost w (longs ts ℓ).length (2 * r * ts.prod)) +
  8 * (2 * r * w * ts.prod) + 8 * clen (hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h) + 201

/-- The layer program meets every chunk-group slot's call within `CL` steps. -/
def LayerCalls {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (r p d w : ℕ) (ts : List ℕ) (ℓ K CL : ℕ) : Prop :=
  ∀ h, (ℓ - 1) % K ≤ h → h < ℓ - 1 → ∀ zs : List (Rec r), zs.length = ts.prod →
    (∀ z ∈ zs, DiskGrid p z.1 z.2) → ∃ k ≤ CL,
      HoareTo (prog1 M ht) (start1 tL (chunkHdr p d r w (Nat.log 2 ts.prod) ts ℓ K h) (array w zs))
        (start1 tL (chunkHdr p d r w (Nat.log 2 ts.prod) ts ℓ K h) (array w (layerOut p ts.length K (rhoOf ℓ K h)
          (2 ^ (chunkOf ℓ K h * ts.length * K)) (2 ^ Nat.log 2 ts.prod) zs))) k

variable {r : ℕ} [NeZero r]

theorem length_hadOut (p : ℕ) {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (h : ℕ) (R : List (Rec r))
    (hR : R.length = ts.prod) : (hadOut p ts ℓ K h R).length = ts.prod := by
  unfold hadOut
  split_ifs
  · simp [hR]
  · simp [layerOut, ← powAxes_prod_pow hL.1]
  · simp [hR]

theorem diskGrid_twistRec {p E : ℕ} {f : Rec r} (hf : DiskGrid p f.1 f.2) : DiskGrid p (twistRec E f).1 (twistRec E f).2 := by
  intro j
  have hs : ∀ k, sgnZ k ^ 2 = 1 := fun k => by rw [sgnZ, ← pow_mul, mul_comm, pow_mul]; norm_num
  simp only [twistRec, mul_pow, hs, one_mul]
  exact hf _

theorem disk_untwistRecs {p : ℕ} (f : ℕ → ℕ) {R : List (Rec r)} (hR : ∀ g ∈ R, DiskGrid p g.1 g.2) :
    ∀ g ∈ TwistRound.untwistRecs f R, DiskGrid p g.1 g.2 := by
  intro g hg
  simp only [TwistRound.untwistRecs, List.mem_mapIdx] at hg
  obtain ⟨y, hy, rfl⟩ := hg
  exact diskGrid_twistRec (hR _ (List.getElem_mem hy))

theorem disk_of_step {n p : ℕ} {G : (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ} (hG : Contracts n G) {R R' : List (Rec r)}
    (hRl : R'.length = 2 ^ n) (hd : ∀ f ∈ R, DiskGrid p f.1 f.2) (hs : RoundStep n p G R R') :
    ∀ f ∈ R', DiskGrid p f.1 f.2 :=
  diskGrid_of_agree hRl hs (roundRun_disk p n [G] (by simpa using hG) _
    (fun y _ k => (pi_norm_le_iff_of_nonneg zero_le_one).mp (norm_arrayVec_le hd _) k))

set_option maxHeartbeats 8000000 in
theorem runs_hadStep {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A)
    {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {p d w CL : ℕ} (hpw : p + 2 ≤ w)
    (hLayer : LayerCalls M ht r p d w ts ℓ K CL) {h : ℕ} (hh : h < ℓ) (R : List (Rec r))
    (hRl : R.length = ts.prod) (hRd : ∀ f ∈ R, DiskGrid p f.1 f.2) (Lr Rs : List (List Bool)) (T7 : WTape)
    (tw : Fin 29 → WTape) :
    Runs (hadStep (nL := nL) M ht haA)
      (dstate tL nL (rnamed w (array w R) ⟨Lr, hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h ++ Rs⟩ T7) tw)
      (· = dstate tL nL (rnamed w (array w (hadOut p ts ℓ K h R))
        ⟨(hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h).reverse ++ Lr, Rs⟩ T7) tw)
      (hadCost p d r w ts ℓ K CL h) := by
  have hr : 1 ≤ r := NeZero.one_le
  have hw : 2 ≤ w := by omega
  set v := rnamed w (array w R) ⟨Lr, hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h ++ Rs⟩ T7
  have v0 : v 0 = reg (array w R) := by simp [v, rnamed]
  have v1 : v 1 = emp := by simp (config := {decide := true}) [v, rnamed]
  have v2 : v 2 = reg (ones w) := by simp (config := {decide := true}) [v, rnamed]
  have v3 : v 3 = emp := by simp (config := {decide := true}) [v, rnamed]
  have v4 : v 4 = emp := by simp (config := {decide := true}) [v, rnamed]
  have v5 : v 5 = emp := by simp (config := {decide := true}) [v, rnamed]
  have v12 : v 12 = emp := by simp (config := {decide := true}) [v, rnamed]
  have v6 : v 6 = ⟨Lr, hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h ++ Rs⟩ := by simp (config := {decide := true}) [v, rnamed]
  have hX : (array w R).length = 2 * r * w * ts.prod := by rw [length_array, hRl]
  by_cases h1 : h < (ℓ - 1) % K
  · -- a prefix slot
    have hW : hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h =
        [[false], ones (2 * r * 2 ^ prefixBase ts.length ℓ K h), ones ts.length] := by simp [hadWords, h1]
    obtain ⟨hb, ⟨c, hc, hlen⟩, -⟩ := prefix_had_spec hL h1 hpw R hRl hRd
    rw [hW] at v6
    have s := runs_bflyStep (A := A) (tL := tL) (nL := nL) hr hw hc R hlen hb v tw (Lr := Lr) (R := Rs)
      (by rw [v6]; rfl) v0 v1 v2 v3 v4 v12
    refine (Runs.cond_false (by rw [dstate_nm, v6]; simp [StartsOne]) s).mono (fun σ e => ?_) ?_
    · rw [e, hW]
      congr 1
      funext i
      simp only [hadOut, h1, if_true]
      fin_cases i <;> simp (config := {decide := true}) [v, rnamed, Function.update_apply, emp]
    · simp only [hadCost, h1, if_true, hW, clen_cons, clen_nil, length_ones, List.length_cons,
        List.length_nil, hX, hRl]
      omega
  · by_cases h2 : h < ℓ - 1
    · -- a chunk-group slot
      have hW : hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h = [[true], chunkHdr p d r w (Nat.log 2 ts.prod) ts ℓ K h] := by
        simp [hadWords, h1, h2]
      obtain ⟨k, hk, hM⟩ := hLayer h (by omega) h2 R hRl hRd
      rw [hW] at v6
      have s := runs_chunkStep (A := A) (nL := nL) M ht haA v tw (Lr := Lr) (R := Rs) (by rw [v6]; rfl) v0 v5 v12 hM
      refine (Runs.cond_true (by rw [dstate_nm, v6]; exact ⟨[], _, rfl⟩) s).mono (fun σ e => ?_) ?_
      · rw [e, hW]
        congr 1
        funext i
        simp only [hadOut, h1, h2, if_true, if_false]
        fin_cases i <;> simp (config := {decide := true}) [v, rnamed, Function.update_apply, emp]
      · simp only [hadCost, h1, h2, if_true, if_false, hW, clen_cons, clen_nil, List.length_cons,
          List.length_nil]
        omega
    · -- the top slot
      have hW : hadWords p d r w (Nat.log 2 ts.prod) ts ℓ K h =
          [[false], ones (2 * r * 2 ^ topBase ts.length ℓ K), ones (longs ts ℓ).length] := by
        simp [hadWords, h1, h2]
      have hlen : R.length = 2 ^ (topBase ts.length ℓ K + (longs ts ℓ).length) * 1 := by
        rw [hRl, powAxes_prod_pow hL.1, log_prod_layout hL, mul_one]
        simp only [topBase]
      rw [hW] at v6
      have s := runs_bflyStep (A := A) (tL := tL) (nL := nL) hr hw le_rfl R hlen (bounded_of_disk hpw hRd) v tw
        (Lr := Lr) (R := Rs) (by rw [v6]; rfl) v0 v1 v2 v3 v4 v12
      refine (Runs.cond_false (by rw [dstate_nm, v6]; simp [StartsOne]) s).mono (fun σ e => ?_) ?_
      · rw [e, hW]
        congr 1
        funext i
        simp only [hadOut, h1, h2, if_false]
        fin_cases i <;> simp (config := {decide := true}) [v, rnamed, Function.update_apply, emp]
      · simp only [hadCost, h1, h2, if_false, hW, clen_cons, clen_nil, length_ones, List.length_cons,
          List.length_nil, hX, hRl]
        omega

end IntegerMultBounds.Schoenhage
