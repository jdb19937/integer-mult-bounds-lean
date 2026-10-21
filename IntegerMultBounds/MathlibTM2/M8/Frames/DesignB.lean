module

public import IntegerMultBounds.MathlibTM2.M8.Frames.LiftFrame
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift00
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift01
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift02
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift03
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift04
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift05
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift06
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift07
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift08
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift09
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift10
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift11
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift12
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift13
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift14
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Lift15
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.LiftRoots

/-!
# The design-B node frames of the PR97 side DAG

Node `n` gets the frame `frameB n`: the root-complement frame `liftFrame c M r` of its lift
record when it has one, its plain frame `nodeFrame n` otherwise. The checks of
`Checks/Lift*` pass at every node and root (`liftOk_at`, `liftRootOk_at`), so:
* every frame is a frame of height at most `2 · 10 ^ 200` (`frameB_idem`, `frameB_bounded`), and
  a lifted frame has rank `23 − dimC c M` or `22 − dimC c M` (`frameB_rank`);
* a node's plain frame lies in its design-B frame (`nodeFrame_le_frameB`): its triples pass
  through `c` and avoid the points of `M`, so they meet every output in `c` alone;
* the frame of the source of an argument (its donor, else the argument) lies in the node's
  (`frameB_src`): two lifted frames nest as their roots shrink, and a plain source lies in the
  node's plain frame;
* a root node's frame lies in its root's frame (`frameB_out`, `frameB_centre`).
So along every slot the design-B frames nest exactly where the plain ones do.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Frames

open Finset Matrix IntegerMultBounds.MathlibTM2.M8.Local

noncomputable section

/-! ### The checks at every node and root -/

/-- The lift record of node `n`. -/
def liftAt (n : ℕ) : Option LiftRec := lifts.get width n

private theorem liftChunk (k : ℕ) (t : Local.Tree NodeRec) (ht : t.Perfect 4096)
    (hall : Tree.all (liftOk lifts) (fun _ => true) nodeCount t (4096 * k) 4096 = true)
    (hget : ∀ i < 4096, records.get 65536 (4096 * k + i) = t.get 4096 i)
    (i : ℕ) (hi : i < 4096) (hn : 4096 * k + i < nodeCount) :
    liftOk lifts (4096 * k + i) (recAt (4096 * k + i)) = true := by
  rw [recAt, width, hget i hi]
  exact Local.Tree.all_get _ _ _ t 4096 (4096 * k) ht hall i hi hn

theorem liftOk_at {n : ℕ} (hn : n < nodeCount) : liftOk lifts n (recAt n) = true := by
  have hn' : n < 64042 := hn
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 4096 ∧ n = 4096 * k + i :=
    ⟨n / 4096, n % 4096, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4096).symm⟩
  have hk : k < 16 := by omega
  interval_cases k
  · exact liftChunk 0 rec00 rec00_perfect liftOk00 records_get_00 i hi hn
  · exact liftChunk 1 rec01 rec01_perfect liftOk01 records_get_01 i hi hn
  · exact liftChunk 2 rec02 rec02_perfect liftOk02 records_get_02 i hi hn
  · exact liftChunk 3 rec03 rec03_perfect liftOk03 records_get_03 i hi hn
  · exact liftChunk 4 rec04 rec04_perfect liftOk04 records_get_04 i hi hn
  · exact liftChunk 5 rec05 rec05_perfect liftOk05 records_get_05 i hi hn
  · exact liftChunk 6 rec06 rec06_perfect liftOk06 records_get_06 i hi hn
  · exact liftChunk 7 rec07 rec07_perfect liftOk07 records_get_07 i hi hn
  · exact liftChunk 8 rec08 rec08_perfect liftOk08 records_get_08 i hi hn
  · exact liftChunk 9 rec09 rec09_perfect liftOk09 records_get_09 i hi hn
  · exact liftChunk 10 rec10 rec10_perfect liftOk10 records_get_10 i hi hn
  · exact liftChunk 11 rec11 rec11_perfect liftOk11 records_get_11 i hi hn
  · exact liftChunk 12 rec12 rec12_perfect liftOk12 records_get_12 i hi hn
  · exact liftChunk 13 rec13 rec13_perfect liftOk13 records_get_13 i hi hn
  · exact liftChunk 14 rec14 rec14_perfect liftOk14 records_get_14 i hi hn
  · exact liftChunk 15 rec15 rec15_perfect liftOk15 records_get_15 i hi hn

theorem liftRootOk_at {j : ℕ} (hj : j < rootCount) : liftRootOk lifts records j (rootAt j) = true := by
  have hj' : j < 5336 := hj
  have := Local.Tree.all_get _ _ _ roots 8192 0 roots_perfect liftRoots j (by omega) (by simpa using hj)
  rwa [zero_add] at this

/-! ### What a lifted record gives -/

theorem testBit_ptsAux (M : ℕ) :
    ∀ k x, (ptsAux M k).testBit x = true ↔ x < k ∧ Nat.land M (touch x) ≠ 0 := by
  intro k
  induction k with
  | zero => intro x; simp [ptsAux]
  | succ k ih =>
    intro x
    show (Nat.lor (ptsAux M k) (bif Nat.beq (Nat.land M (touch k)) 0 then 0 else bit k)).testBit x
      = true ↔ _
    rw [show ∀ a b : ℕ, Nat.lor a b = a ||| b from fun _ _ => rfl, Nat.testBit_lor, Bool.or_eq_true,
      ih, cond_ite]
    by_cases h0 : Nat.land M (touch k) = 0
    · rw [ite_eq_left_iff.mpr fun h => absurd ((beq_iff _ _).mpr h0) h]
      simp only [Nat.zero_testBit, Bool.false_eq_true, or_false]
      constructor
      · rintro ⟨hx, h⟩; exact ⟨by omega, h⟩
      · rintro ⟨hx, h⟩
        refine ⟨?_, h⟩
        by_contra hk
        exact h (by rw [show x = k by omega]; exact h0)
    · rw [ite_eq_right_iff.mpr fun h => absurd ((beq_iff _ _).mp h) h0, testBit_bit, decide_eq_true_eq]
      constructor
      · rintro (⟨hx, h⟩ | rfl)
        · exact ⟨by omega, h⟩
        · exact ⟨by omega, h0⟩
      · rintro ⟨hx, h⟩
        by_cases hk : x < k
        · exact Or.inl ⟨hk, h⟩
        · exact Or.inr (by omega)

/-- A point of a pair of `M` is a point of `onPts M`. -/
theorem onPts_of_bit {M u w : ℕ} (hu : u < 23) (hw : w < 23) (huw : u ≠ w)
    (h : M.testBit (pb u w) = true) : (onPts M).testBit u = true := by
  rw [onPts, testBit_ptsAux]
  refine ⟨hu, fun h0 => ?_⟩
  have := congrArg (fun x => Nat.testBit x (pb u w)) h0
  simp only [show ∀ a b : ℕ, Nat.land a b = a &&& b from fun _ _ => rfl, Nat.testBit_land, h,
    Bool.true_and, Nat.zero_testBit] at this
  rw [(testBit_touch _).mpr ⟨w, hw, Ne.symm huw, rfl⟩] at this
  cases this

theorem not_both {A B x : ℕ} (h : Nat.land A B = 0) (hA : A.testBit x = true) :
    B.testBit x = false := by
  have := congrArg (fun y => Nat.testBit y x) h
  simp only [show ∀ a b : ℕ, Nat.land a b = a &&& b from fun _ _ => rfl, Nat.testBit_land, hA,
    Bool.true_and, Nat.zero_testBit] at this
  exact this

/-- The facts of a lifted node's record. -/
theorem lift_valid {n : ℕ} (hn : n < nodeCount) {L : LiftRec} (h : liftAt n = some L) :
    L.c < 23 ∧ subB L.mask (pairsWithout L.c) = true ∧ okC L.c L.mask = true ∧
      ∃ P, relP L.c (recAt n).supp = some P ∧ Nat.land (onPts P) (onPts L.mask) = 0 := by
  have hok := liftOk_at hn
  simp only [liftOk, Bool.and_eq_true] at hok
  have hv := hok.1
  rw [show lifts.get width n = some L from h] at hv
  simp only [liftValid, Bool.and_eq_true, blt_iff] at hv
  obtain ⟨⟨⟨hc, hM⟩, hokC⟩, hrel⟩ := hv
  refine ⟨hc, hM, hokC, ?_⟩
  split at hrel
  · next P hP => exact ⟨P, hP, (beq_iff _ _).mp hrel⟩
  · cases hrel

/-! ### The design-B frames -/

/-- **The design-B frame** of node `n`. -/
def frameB (n : ℕ) : Matrix (Fin 23) (Fin 23) ℚ :=
  match liftAt n with
  | some L => liftFrame L.c L.mask L.ret
  | none => nodeFrame n

theorem frameB_some {n : ℕ} {L : LiftRec} (h : liftAt n = some L) :
    frameB n = liftFrame L.c L.mask L.ret := by
  rw [frameB, h]

theorem frameB_none {n : ℕ} (h : liftAt n = none) : frameB n = nodeFrame n := by
  rw [frameB, h]

theorem frameB_idem {n : ℕ} (hn : n < nodeCount) : frameB n * frameB n = frameB n := by
  cases h : liftAt n with
  | none => rw [frameB_none h]; exact nodeFrame_idem hn
  | some L =>
    obtain ⟨hc, hM, -⟩ := lift_valid hn h
    rw [frameB_some h]
    exact liftFrame_idem hc hM L.ret

theorem frameB_bounded {n : ℕ} (hn : n < nodeCount) : Height.Bounded (frameB n) (2 * 10 ^ 200) := by
  cases h : liftAt n with
  | none =>
    rw [frameB_none h]
    exact (nodeFrame_bounded hn).mono (by norm_num)
  | some L =>
    obtain ⟨hc, hM, -⟩ := lift_valid hn h
    rw [frameB_some h]
    exact liftFrame_bounded hc hM L.ret

theorem frameB_rank {n : ℕ} (hn : n < nodeCount) {L : LiftRec} (h : liftAt n = some L) :
    (frameB n).rank = (if L.ret then 22 else 23) - dimC L.c L.mask := by
  obtain ⟨hc, hM, hokC, -⟩ := lift_valid hn h
  rw [frameB_some h]
  exact liftFrame_rank hc hM hokC L.ret

/-- **A node's plain frame lies in its design-B frame.** -/
theorem nodeFrame_le_frameB {n : ℕ} (hn : n < nodeCount) : Nested (nodeFrame n) (frameB n) := by
  cases h : liftAt n with
  | none => rw [frameB_none h]; exact ⟨nodeFrame_idem hn, nodeFrame_idem hn⟩
  | some L =>
    obtain ⟨hc, hM, -, P, hP, hdisj⟩ := lift_valid hn h
    have hs := recOk_at n hn
    have hspec := relP_spec hs hc hP
    rw [frameB_some h]
    refine frameOf_lift hc hM (fun S hS => ?_) (fun S hS T hT => ?_) L.ret
    · have hm := (mem_suppSet hs).mp hS
      obtain ⟨u, w, -, -, -, -, rfl, -⟩ := (hspec _).mp hm
      exact ⟨(Supp.mem_triple hs hm).1, by simp⟩
    · obtain ⟨u', w', huw', hw', hcu', hcw', rfl, hb'⟩ := (hspec _).mp ((mem_suppSet hs).mp hS)
      obtain ⟨u, w, huw, hw, hcu, hcw, rfl, hb⟩ := liftFrame_mem hc hM hT
      have hb'' : P.testBit (pb w' u') = true := by rwa [pb_comm] at hb'
      have hbb : L.mask.testBit (pb w u) = true := by rwa [pb_comm] at hb
      have hP1 := onPts_of_bit (M := P) (u := u') (w := w') (by omega) hw' (by omega) hb'
      have hP2 := onPts_of_bit (M := P) (u := w') (w := u') hw' (by omega) (by omega) hb''
      have hM1 := onPts_of_bit (M := L.mask) (u := u) (w := w) (by omega) hw (by omega) hb
      have hM2 := onPts_of_bit (M := L.mask) (u := w) (w := u) hw (by omega) (by omega) hbb
      have n1 := not_both hdisj hP1
      have n2 := not_both hdisj hP2
      have e1 : u' ≠ u := fun e => by rw [e, hM1] at n1; cases n1
      have e2 : u' ≠ w := fun e => by rw [e, hM2] at n1; cases n1
      have e3 : w' ≠ u := fun e => by rw [e, hM1] at n2; cases n2
      have e4 : w' ≠ w := fun e => by rw [e, hM2] at n2; cases n2
      have : ({L.c, u', w'} : Finset ℕ) ∩ {L.c, u, w} = {L.c} := by
        ext z
        simp only [mem_inter, mem_insert, mem_singleton]
        omega
      rw [this, card_singleton]

/-- The plain frame of an argument's source lies in the node's plain frame. -/
theorem nodeFrame_src {k : ℕ} (hk : leafCount ≤ k) (hkN : k < nodeCount) (pos : Bool) :
    Nested (nodeFrame (((recAt k).donor pos).getD ((recAt k).arg pos))) (nodeFrame k) := by
  have hdonor : donorOk records k pos ((recAt k).donor pos) = true := by
    have := allOk_parts (allOk_at k hkN)
    cases pos
    · exact this.2.2.1
    · exact this.2.2.2.1
  cases hd : (recAt k).donor pos with
  | none => exact nodeFrame_arg (by omega) hkN pos
  | some m =>
    rw [hd] at hdonor
    simp only [donorOk, Bool.and_eq_true, blt_iff] at hdonor
    obtain ⟨-, hl⟩ := hdonor
    split at hl
    · next L hL =>
      simp only [Bool.and_eq_true, beq_iff, beq_iff_eq] at hl
      have hlink : dag.link m = some (L.operand, k, pos) := by
        show Option.map _ (recAt m).link = _
        rw [show (recAt m).link = some L from hL, Option.map_some, hl.1, hl.2]
      exact nodeFrame_link hlink
    · cases hl

theorem src_lt {k : ℕ} (hk : leafCount ≤ k) (hkN : k < nodeCount) (pos : Bool) :
    ((recAt k).donor pos).getD ((recAt k).arg pos) < nodeCount := by
  have h := allOk_parts (allOk_at k hkN)
  cases hd : (recAt k).donor pos with
  | some m =>
    have hok : donorOk records k pos (some m) = true := by
      rw [← hd]; cases pos
      · exact h.2.2.1
      · exact h.2.2.2.1
    simp only [donorOk, Bool.and_eq_true, blt_iff] at hok
    exact hok.1
  | none =>
    have h := nodeOk_add h.1 (by omega)
    cases pos
    · exact h.2.1.trans hkN
    · exact h.2.2.1.trans hkN

/-- **Sources.** The frame of an argument's source lies in the node's frame. -/
theorem frameB_src {k : ℕ} (hk : leafCount ≤ k) (hkN : k < nodeCount) (pos : Bool) :
    Nested (frameB (((recAt k).donor pos).getD ((recAt k).arg pos))) (frameB k) := by
  set p := ((recAt k).donor pos).getD ((recAt k).arg pos)
  have hpN : p < nodeCount := src_lt hk hkN pos
  cases hp : liftAt p with
  | none =>
    rw [frameB_none hp]
    exact (nodeFrame_src hk hkN pos).trans (nodeFrame_le_frameB hkN)
  | some Lp =>
    have hok := liftOk_at hkN
    have hadd : (recAt k).isAdd = true := by
      have := nodeOk_add (allOk_parts (allOk_at k hkN)).1 (by omega)
      exact this.1
    simp only [liftOk, Bool.and_eq_true, hadd, Bool.cond_true] at hok
    have hle : liftLe (liftAt k) (liftAt p) = true := by
      cases pos
      · exact hok.2.1
      · exact hok.2.2
    rw [hp] at hle
    cases hk' : liftAt k with
    | none => rw [hk'] at hle; cases hle
    | some Lk =>
      rw [hk'] at hle
      simp only [liftLe, Bool.and_eq_true, beq_iff, Bool.or_eq_true, Bool.not_eq_true'] at hle
      obtain ⟨⟨hcc, hsub⟩, hr⟩ := hle
      obtain ⟨hc, hM, -⟩ := lift_valid hpN hp
      rw [frameB_some hp, frameB_some hk', hcc]
      refine liftFrame_nest hc hM hsub fun h => ?_
      rcases hr with h' | h'
      · rw [h] at h'; cases h'
      · exact h'

/-- **Output roots.** A root node's frame lies in the hyperplane of its triple. -/
theorem frameB_out {j : ℕ} (hj : j < 3 * leafCount) :
    Nested (frameB (rootAt j).node) (hyperFrame (leafTriple (j / 3))) := by
  have ht : j / 3 < leafCount := by have : j < 3 * 1771 := hj; show j / 3 < 1771; omega
  have hjr : j < rootCount := by have : j < 3 * 1771 := hj; show j < 5336; omega
  cases h : liftAt (rootAt j).node with
  | none =>
    rw [frameB_none h]
    have := nodeFrame_out ht (show j % 3 < 3 from Nat.mod_lt _ (by norm_num))
    rwa [Nat.div_add_mod] at this
  | some L =>
    obtain ⟨hc, hM, -⟩ := lift_valid (root_node hjr) h
    obtain ⟨p0, p1, p2, hp, h01, h12, h2⟩ := leaf_supp ht
    have hok : (bif Nat.beq (j % 3) 0 then (Nat.beq L.c p0 && testB L.mask (pb p1 p2))
        else bif Nat.beq (j % 3) 1 then (Nat.beq L.c p1 && testB L.mask (pb p0 p2))
        else (Nat.beq L.c p2 && testB L.mask (pb p0 p1))) = true := by
      have := liftRootOk_at hjr
      unfold liftRootOk at this
      rw [show lifts.get width (rootAt j).node = some L from h,
        show Nat.blt j (Nat.mul 3 leafCount) = true from (blt_iff _ _).mpr hj,
        show (records.get width (Nat.div j 3)).supp = Supp.three p0 p1 p2 from hp] at this
      exact this
    rw [frameB_some h, leafTriple_of hp]
    rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with e | e | e <;>
      simp only [e, cond_ite, beq_iff, Bool.and_eq_true, testB_eq, ↓reduceIte,
        show (1 : ℕ) ≠ 0 from one_ne_zero, show (2 : ℕ) ≠ 0 by norm_num,
        show (2 : ℕ) ≠ 1 by norm_num] at hok <;> obtain ⟨rfl, hb⟩ := hok
    · exact liftFrame_hyper hc hM (by omega) h2 (by omega) (by omega) (by omega) hb L.ret
    · rw [Finset.insert_comm]
      exact liftFrame_hyper hc hM (by omega) h2 (by omega) (by omega) (by omega) hb L.ret
    · rw [rot3]
      exact liftFrame_hyper hc hM (by omega) (by omega) (by omega) (by omega) (by omega) hb L.ret

/-- **Centre roots.** A centre's root node's frame lies in the star. -/
theorem frameB_centre {c : ℕ} (hc : c < 23) :
    Nested (frameB (rootAt (3 * leafCount + c)).node) (starFrame c) := by
  have hjr : 3 * leafCount + c < rootCount := by show 3 * 1771 + c < 5336; omega
  cases h : liftAt (rootAt (3 * leafCount + c)).node with
  | none =>
    rw [frameB_none h, nodeFrame_centre hc]
    exact ⟨frameOf_idem (starSet_mem hc), frameOf_idem (starSet_mem hc)⟩
  | some L =>
    obtain ⟨hc', hM, -⟩ := lift_valid (root_node hjr) h
    have hn : ¬ 3 * leafCount + c < 3 * leafCount := by omega
    have hok : (Nat.beq L.c (Nat.sub (3 * leafCount + c) (Nat.mul 3 leafCount)) && L.ret) = true := by
      have := liftRootOk_at hjr
      unfold liftRootOk at this
      rw [show lifts.get width (rootAt (3 * leafCount + c)).node = some L from h,
        show Nat.blt (3 * leafCount + c) (Nat.mul 3 leafCount) = false from
          Bool.eq_false_iff.mpr fun e => hn ((blt_iff _ _).mp e)] at this
      exact this
    rw [Bool.and_eq_true, beq_iff] at hok
    obtain ⟨hcc, hr⟩ := hok
    have hcc' : L.c = c := by rw [hcc]; show 3 * leafCount + c - 3 * leafCount = c; omega
    rw [frameB_some h, hr, ← hcc']
    exact liftFrame_star hc' hM

end

end IntegerMultBounds.MathlibTM2.M8.Frames
