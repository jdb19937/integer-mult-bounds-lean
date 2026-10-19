module

public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes00
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes01
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes02
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes03
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes04
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes05
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes06
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes07
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes08
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes09
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes10
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes11
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes12
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes13
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes14
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Nodes15
public import IntegerMultBounds.MathlibTM2.M8.Local.Checks.Roots
public import IntegerMultBounds.MathlibTM2.M8.Local.Bits
public import IntegerMultBounds.MathlibTM2.M8.Local.Compile
public import Mathlib.Tactic.IntervalCases

/-!
# The PR97 side DAG

The kernel checks of `M8/Local/Checks/*` hold at every node and root (`allOk_at`, `rootOk_at`),
and the records past the last node are padding (`recAt_pad`). From them:
* `dag`, the side DAG of the PR97 word read from the records, is valid (`dag_valid`);
* every support is valid (`recOk_at`), and an addition's support is the disjoint union of its
  arguments' supports (`supp_add`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

noncomputable section

/-- The record of node `n`. -/
def recAt (n : ℕ) : NodeRec := records.get width n

/-- The record of root `j`. -/
def rootAt (j : ℕ) : RootRec := roots.get rootWidth j

private theorem chunk (k : ℕ) (t : Tree NodeRec) (ht : t.Perfect 4096)
    (hall : Tree.all (allOk records roots) NodeRec.isPad nodeCount t (4096 * k) 4096 = true)
    (hget : ∀ i < 4096, records.get 65536 (4096 * k + i) = t.get 4096 i)
    (i : ℕ) (hi : i < 4096) (hn : 4096 * k + i < nodeCount) :
    allOk records roots (4096 * k + i) (recAt (4096 * k + i)) = true := by
  rw [recAt, width, hget i hi]
  exact Tree.all_get _ _ _ t 4096 (4096 * k) ht hall i hi hn

/-- Every node passes its checks. -/
theorem allOk_at (n : ℕ) (hn : n < nodeCount) : allOk records roots n (recAt n) = true := by
  have hn' : n < 64042 := hn
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 4096 ∧ n = 4096 * k + i :=
    ⟨n / 4096, n % 4096, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4096).symm⟩
  have hk : k < 16 := by omega
  interval_cases k
  · exact chunk 0 rec00 rec00_perfect nodes00 records_get_00 i hi hn
  · exact chunk 1 rec01 rec01_perfect nodes01 records_get_01 i hi hn
  · exact chunk 2 rec02 rec02_perfect nodes02 records_get_02 i hi hn
  · exact chunk 3 rec03 rec03_perfect nodes03 records_get_03 i hi hn
  · exact chunk 4 rec04 rec04_perfect nodes04 records_get_04 i hi hn
  · exact chunk 5 rec05 rec05_perfect nodes05 records_get_05 i hi hn
  · exact chunk 6 rec06 rec06_perfect nodes06 records_get_06 i hi hn
  · exact chunk 7 rec07 rec07_perfect nodes07 records_get_07 i hi hn
  · exact chunk 8 rec08 rec08_perfect nodes08 records_get_08 i hi hn
  · exact chunk 9 rec09 rec09_perfect nodes09 records_get_09 i hi hn
  · exact chunk 10 rec10 rec10_perfect nodes10 records_get_10 i hi hn
  · exact chunk 11 rec11 rec11_perfect nodes11 records_get_11 i hi hn
  · exact chunk 12 rec12 rec12_perfect nodes12 records_get_12 i hi hn
  · exact chunk 13 rec13 rec13_perfect nodes13 records_get_13 i hi hn
  · exact chunk 14 rec14 rec14_perfect nodes14 records_get_14 i hi hn
  · exact chunk 15 rec15 rec15_perfect nodes15 records_get_15 i hi hn

theorem records_perfect : records.Perfect 65536 := by
  unfold records
  exact ⟨by norm_num, by norm_num,
    ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num,
      rec00_perfect, rec01_perfect⟩, ⟨by norm_num, by norm_num, rec02_perfect, rec03_perfect⟩⟩,
      ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num, rec04_perfect, rec05_perfect⟩,
        ⟨by norm_num, by norm_num, rec06_perfect, rec07_perfect⟩⟩⟩,
    ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num,
      rec08_perfect, rec09_perfect⟩, ⟨by norm_num, by norm_num, rec10_perfect, rec11_perfect⟩⟩,
      ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num, rec12_perfect, rec13_perfect⟩,
        ⟨by norm_num, by norm_num, rec14_perfect, rec15_perfect⟩⟩⟩⟩

/-- The records past the last node are padding. -/
theorem recAt_pad (n : ℕ) (hn : nodeCount ≤ n) : (recAt n).isPad = true := by
  have h15 : ∀ i < 4096, nodeCount ≤ 4096 * 15 + i → (recAt (4096 * 15 + i)).isPad = true := by
    intro i hi hb
    rw [recAt, width, records_get_15 i hi]
    exact Tree.all_get_pad _ _ _ rec15 4096 (4096 * 15) rec15_perfect nodes15 i hi hb
  have hN : nodeCount = 64042 := rfl
  by_cases hw : n < 65536
  · have := h15 (n - 4096 * 15) (by omega) (by omega)
    rwa [show 4096 * 15 + (n - 4096 * 15) = n by omega] at this
  · rw [recAt, width, Tree.get_ge records 65536 n records_perfect (by omega)]
    have := h15 4095 (by norm_num) (by omega)
    rwa [recAt, width] at this

/-- Every root passes its check. -/
theorem rootOk_at (j : ℕ) (hj : j < rootCount) : rootOk records j (rootAt j) = true := by
  have hj' : j < 5336 := hj
  have := Tree.all_get _ _ _ roots 8192 0 roots_perfect roots_ok j (by omega) (by simpa using hj)
  rwa [zero_add] at this

/-! ### The DAG -/

/-- The side DAG of the PR97 word, read from the records. -/
def dag : Dag where
  N := nodeCount
  v := leafCount
  arg n pos := (recAt n).arg pos
  rootCount := rootCount
  rootNode j := (rootAt j).node
  link n := (recAt n).link.map fun L => (L.operand, L.user, L.pos)

/-! ### What the checks give -/

theorem allOk_parts {n : ℕ} {r : NodeRec} (h : allOk records roots n r = true) :
    nodeOk records n r = true ∧ linkOk records n r = true ∧ donorOk records n false r.donor0 = true ∧
      donorOk records n true r.donor1 = true ∧ freeOk records roots n r = true := by
  simpa only [allOk, Bool.and_eq_true, and_assoc] using h

theorem records_get (n : ℕ) : records.get width n = recAt n := rfl

theorem nodeOk_leaf {n : ℕ} {r : NodeRec} (h : nodeOk records n r = true) (hn : n < leafCount) :
    r.isAdd = false ∧ (∃ p0 p1 p2, r.supp = .three p0 p1 p2 ∧ p0 < p1 ∧ p1 < p2 ∧ p2 < 23) ∧
      (n ≠ 0 → lexLt (points3 (recAt (n - 1)).supp) (points3 r.supp) = true) := by
  unfold nodeOk at h
  rw [cond_ite, ite_eq_left ((blt_iff _ _).mpr hn)] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hadd, hs⟩, hlex⟩ := h
  refine ⟨hadd, ?_, ?_⟩
  · cases hr : r.supp with
    | three p0 p1 p2 =>
      rw [hr] at hs
      simp only [Bool.and_eq_true, blt_iff] at hs
      exact ⟨p0, p1, p2, rfl, hs.1.1, hs.1.2, hs.2⟩
    | two _ _ _ => rw [hr] at hs; cases hs
    | one _ _ => rw [hr] at hs; cases hs
  · intro hn0
    rw [cond_ite, ite_eq_right (by rw [beq_iff]; exact hn0)] at hlex
    exact hlex

theorem nodeOk_add {n : ℕ} {r : NodeRec} (h : nodeOk records n r = true) (hn : ¬ n < leafCount) :
    r.isAdd = true ∧ r.a < n ∧ r.b < n ∧ supportOk r.supp (recAt r.a).supp (recAt r.b).supp = true := by
  unfold nodeOk at h
  rw [cond_ite, ite_eq_right (by rw [blt_iff]; exact hn)] at h
  simpa only [Bool.and_eq_true, blt_iff, records_get, and_assoc] using h

theorem isAdd_lt {n : ℕ} (hk : (recAt n).isAdd = true) : leafCount ≤ n ∧ n < nodeCount := by
  by_cases hN : n < nodeCount
  · refine ⟨?_, hN⟩
    by_contra hv
    have := (nodeOk_leaf (allOk_parts (allOk_at n hN)).1 (by omega)).1
    rw [hk] at this; cases this
  · have := recAt_pad n (by omega)
    simp only [NodeRec.isPad, Bool.and_eq_true, Bool.not_eq_true'] at this
    rw [hk] at this
    exact absurd this.1.1.1.1.1 (by simp)

theorem dag_link {n : ℕ} {o : Bool} {t : ℕ} {pos : Bool} (h : dag.link n = some (o, t, pos)) :
    ∃ L, (recAt n).link = some L ∧ L.operand = o ∧ L.user = t ∧ L.pos = pos := by
  simp only [dag, Option.map_eq_some_iff] at h
  obtain ⟨L, hL, he⟩ := h
  simp only [Prod.mk.injEq] at he
  exact ⟨L, hL, he.1, he.2.1, he.2.2⟩

/-- The link check, at a donor. -/
theorem linkOk_donor {n : ℕ} {L : Link} (hL : (recAt n).link = some L) :
    (recAt n).isAdd = true ∧ n < L.user ∧ L.user < nodeCount ∧ (recAt L.user).isAdd = true ∧
      (recAt L.user).arg L.pos = (recAt n).arg L.operand ∧ (recAt L.user).donor L.pos = some n ∧
      spanOk L (recAt n).supp (recAt L.user).supp = true := by
  have hN : n < nodeCount := by
    by_contra h
    have := recAt_pad n (by omega)
    simp only [NodeRec.isPad, Bool.and_eq_true, hL, Option.isNone_some] at this
    exact absurd this.1.1.2 (by simp)
  have hok := (allOk_parts (allOk_at n hN)).2.1
  unfold linkOk at hok
  rw [hL] at hok
  simp only [Bool.and_eq_true, blt_iff, beq_iff, records_get] at hok
  obtain ⟨⟨⟨⟨⟨⟨hadd, hnt⟩, htN⟩, htadd⟩, harg⟩, hd⟩, hspan⟩ := hok
  refine ⟨hadd, hnt, htN, htadd, harg, ?_, hspan⟩
  revert hd
  cases (recAt L.user).donor L.pos with
  | none => intro h; cases h
  | some d => intro h; rw [(beq_iff _ _).mp h]

theorem dag_valid : dag.Valid where
  arg_lt n hv hN pos := by
    have h := nodeOk_add (allOk_parts (allOk_at n hN)).1 (by simp only [dag] at hv; omega)
    cases pos
    · exact h.2.1
    · exact h.2.2.1
  link_donor n o t pos h := by
    obtain ⟨L, hL, _⟩ := dag_link h
    exact isAdd_lt (linkOk_donor hL).1
  link_user n o t pos h := by
    obtain ⟨L, hL, rfl, rfl, rfl⟩ := dag_link h
    obtain ⟨_, hnt, htN, _, harg, _⟩ := linkOk_donor hL
    exact ⟨hnt, htN, harg⟩
  link_inj n n' o o' t pos h h' := by
    obtain ⟨L, hL, _, rfl, rfl⟩ := dag_link h
    obtain ⟨L', hL', _, ht, hp⟩ := dag_link h'
    have a := (linkOk_donor hL).2.2.2.2.2.1
    have b := (linkOk_donor hL').2.2.2.2.2.1
    rw [ht, hp] at b
    rw [a] at b
    exact Option.some.inj b
  free_ne y hy := by
    have hok := (allOk_parts (allOk_at y hy)).2.2.2.2
    unfold freeOk at hok
    intro hnil
    cases hf : (recAt y).free with
    | gate u pos =>
      rw [hf] at hok
      simp only [Bool.and_eq_true, blt_iff, beq_iff, records_get] at hok
      obtain ⟨⟨⟨⟨hyu, huN⟩, hku⟩, harg⟩, hnone⟩ := hok
      have hmem : Use.gate u pos ∈ dag.freeUses y := by
        rw [Dag.mem_freeUses, Dag.mem_uses_gate]
        refine ⟨⟨huN, (isAdd_lt hku).1, harg⟩, ?_⟩
        rcases hb : dag.linkedB (.gate u pos) with _ | _
        · rfl
        · exfalso
          obtain ⟨d, _, hd⟩ := (dag.linkedB_iff _).mp hb
          obtain ⟨o, t, pos', hl, he⟩ := dag.linkUse_eq.mp hd
          cases he
          obtain ⟨L, hL, _, rfl, rfl⟩ := dag_link hl
          have := (linkOk_donor hL).2.2.2.2.2.1
          revert hnone
          rw [this]
          intro h; cases h
      rw [hnil] at hmem
      exact List.not_mem_nil hmem
    | root j =>
      rw [hf] at hok
      simp only [Bool.and_eq_true, blt_iff, beq_iff] at hok
      have hmem : Use.root j ∈ dag.freeUses y := by
        rw [Dag.mem_freeUses, Dag.mem_uses_root]
        exact ⟨⟨hok.1, hok.2⟩, dag.root_not_linked _⟩
      rw [hnil] at hmem
      exact List.not_mem_nil hmem
  root_lt j hj := by
    have h := rootOk_at j hj
    unfold rootOk at h
    simp only [Bool.and_eq_true, blt_iff] at h
    exact h.1.1
  v_le := by simp only [dag]; decide

/-! ### Supports -/

/-- Every node's support is valid. -/
theorem recOk_at : ∀ n, n < nodeCount → (recAt n).supp.Ok := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hok := (allOk_parts (allOk_at n hn)).1
    by_cases hv : n < leafCount
    · obtain ⟨_, ⟨p0, p1, p2, hs, h01, h12, h2⟩, _⟩ := nodeOk_leaf hok hv
      rw [hs]
      exact ⟨h01, h12, h2⟩
    · obtain ⟨_, ha, hb, hs⟩ := nodeOk_add hok hv
      exact (supportOk_spec (ih _ ha (by omega)) (ih _ hb (by omega)) hs).1

/-- An addition's support is the disjoint union of its arguments' supports. -/
theorem supp_add {n : ℕ} (hv : ¬ n < leafCount) (hn : n < nodeCount) :
    (∀ S, (recAt n).supp.mem S ↔ (recAt (dag.arg n false)).supp.mem S ∨
      (recAt (dag.arg n true)).supp.mem S) ∧
    ∀ S, (recAt (dag.arg n false)).supp.mem S → (recAt (dag.arg n true)).supp.mem S → False := by
  obtain ⟨_, ha, hb, hs⟩ := nodeOk_add (allOk_parts (allOk_at n hn)).1 hv
  exact (supportOk_spec (recOk_at _ (by omega)) (recOk_at _ (by omega)) hs).2

end

end IntegerMultBounds.MathlibTM2.M8.Local
