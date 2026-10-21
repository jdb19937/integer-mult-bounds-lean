module

public import IntegerMultBounds.MathlibTM2.M8.Local.WordB
public import IntegerMultBounds.MathlibTM2.M8.Local.Scalar
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes00
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes01
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes02
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes03
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes04
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes05
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes06
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes07
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes08
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes09
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes10
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes11
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes12
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes13
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes14
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Nodes15
public import IntegerMultBounds.MathlibTM2.M8.Local.ChecksB.Deferred

/-!
# The design-B word of the PR97 side slots

`dagB` is the side DAG with upstream's design-B serving orders (`DataB`). With the phase bits and
the deferred uses of the data, the kernel checks of `ChecksB/*` give the phase hypotheses
(`phaseHypB`), and these give the conditions of `Dag.wordB_run` for the plan `planB`: the first
phase leaves the deferred slots alone, the second leaves the centres alone. So on arbitrary
contents the design-B word adds every source into the target of its triple and leaves the other
registers unchanged (`wordB_run_target`, `wordB_run_other`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Local

noncomputable section

open Networks

/-! ### The checks at every node -/

private theorem bchunk (k : ℕ) (t : Tree (Nat × List Use)) (ht : t.Perfect 4096)
    (hall : Tree.all bnodeOk (fun x => Nat.beq x.1 0) nodeCount t (4096 * k) 4096 = true)
    (hget : ∀ i < 4096, bdata.get 65536 (4096 * k + i) = t.get 4096 i)
    (i : ℕ) (hi : i < 4096) (hn : 4096 * k + i < nodeCount) :
    bnodeOk (4096 * k + i) (bAt (4096 * k + i)) = true := by
  rw [bAt, width, hget i hi]
  exact Tree.all_get _ _ _ t 4096 (4096 * k) ht hall i hi hn

/-- Every node passes the design-B checks. -/
theorem bnodeOk_at (n : ℕ) (hn : n < nodeCount) : bnodeOk n (bAt n) = true := by
  have hn' : n < 64042 := hn
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 4096 ∧ n = 4096 * k + i :=
    ⟨n / 4096, n % 4096, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4096).symm⟩
  have hk : k < 16 := by omega
  interval_cases k
  · exact bchunk 0 bdata00 bdata00_perfect bnodes00 bdata_get_00 i hi hn
  · exact bchunk 1 bdata01 bdata01_perfect bnodes01 bdata_get_01 i hi hn
  · exact bchunk 2 bdata02 bdata02_perfect bnodes02 bdata_get_02 i hi hn
  · exact bchunk 3 bdata03 bdata03_perfect bnodes03 bdata_get_03 i hi hn
  · exact bchunk 4 bdata04 bdata04_perfect bnodes04 bdata_get_04 i hi hn
  · exact bchunk 5 bdata05 bdata05_perfect bnodes05 bdata_get_05 i hi hn
  · exact bchunk 6 bdata06 bdata06_perfect bnodes06 bdata_get_06 i hi hn
  · exact bchunk 7 bdata07 bdata07_perfect bnodes07 bdata_get_07 i hi hn
  · exact bchunk 8 bdata08 bdata08_perfect bnodes08 bdata_get_08 i hi hn
  · exact bchunk 9 bdata09 bdata09_perfect bnodes09 bdata_get_09 i hi hn
  · exact bchunk 10 bdata10 bdata10_perfect bnodes10 bdata_get_10 i hi hn
  · exact bchunk 11 bdata11 bdata11_perfect bnodes11 bdata_get_11 i hi hn
  · exact bchunk 12 bdata12 bdata12_perfect bnodes12 bdata_get_12 i hi hn
  · exact bchunk 13 bdata13 bdata13_perfect bnodes13 bdata_get_13 i hi hn
  · exact bchunk 14 bdata14 bdata14_perfect bnodes14 bdata_get_14 i hi hn
  · exact bchunk 15 bdata15 bdata15_perfect bnodes15 bdata_get_15 i hi hn

theorem bdata_perfect : bdata.Perfect 65536 := by
  unfold bdata
  exact ⟨by norm_num, by norm_num,
    ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num,
      bdata00_perfect, bdata01_perfect⟩, ⟨by norm_num, by norm_num, bdata02_perfect,
        bdata03_perfect⟩⟩,
      ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num, bdata04_perfect, bdata05_perfect⟩,
        ⟨by norm_num, by norm_num, bdata06_perfect, bdata07_perfect⟩⟩⟩,
    ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num,
      bdata08_perfect, bdata09_perfect⟩, ⟨by norm_num, by norm_num, bdata10_perfect,
        bdata11_perfect⟩⟩,
      ⟨by norm_num, by norm_num, ⟨by norm_num, by norm_num, bdata12_perfect, bdata13_perfect⟩,
        ⟨by norm_num, by norm_num, bdata14_perfect, bdata15_perfect⟩⟩⟩⟩

/-- Past the last node the phase bits are zero. -/
theorem bAt_pad (n : ℕ) (hn : nodeCount ≤ n) : (bAt n).1 = 0 := by
  have h15 : ∀ i < 4096, nodeCount ≤ 4096 * 15 + i → (bAt (4096 * 15 + i)).1 = 0 := by
    intro i hi hb
    rw [bAt, width, bdata_get_15 i hi]
    have := Tree.all_get_pad _ _ _ bdata15 4096 (4096 * 15) bdata15_perfect bnodes15 i hi hb
    exact Nat.eq_of_beq_eq_true this
  have hN : nodeCount = 64042 := rfl
  by_cases hw : n < 65536
  · have := h15 (n - 4096 * 15) (by omega) (by omega)
    rwa [show 4096 * 15 + (n - 4096 * 15) = n by omega] at this
  · rw [bAt, width, Tree.get_ge bdata 65536 n bdata_perfect (by omega)]
    have := h15 4095 (by norm_num) (by omega)
    rwa [bAt, width] at this

theorem bnode_parts {n : ℕ} (hn : n < nodeCount) :
    (psiB n = true → phiB n = true) ∧
    (phiB n = true → argOkB (recAt n).a = true ∧ argOkB (recAt n).b = true) ∧
    (∀ L, (recAt n).link = some L → phiB L.user = true → phiB n = true) := by
  have h := bnodeOk_at n hn
  unfold bnodeOk at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun hp => ?_, fun hp => ?_, fun L hL hu => ?_⟩
  · rcases h1 with h1 | h1
    · simp only [psiB] at hp; rw [hp] at h1; cases h1
    · exact h1
  · rcases h2 with h2 | h2
    · simp only [phiB] at hp; rw [hp] at h2; cases h2
    · exact h2
  · rw [show records.get width n = recAt n from rfl, hL] at h3
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h3
    rcases h3 with h3 | h3
    · rw [hu] at h3; cases h3
    · exact h3

theorem psiB_phiB (n : ℕ) (h : psiB n = true) : phiB n = true := by
  by_cases hn : n < nodeCount
  · exact (bnode_parts hn).1 h
  · simp [psiB, bAt_pad n (by omega)] at h

/-! ### The design-B DAG -/

/-- The side DAG with the design-B serving orders. -/
def dagB : Dag := { dag with rank := fun y u => (bAt y).2.idxOf u }

theorem dagB_mem_freeUses {y : ℕ} {u : Use} : u ∈ dagB.freeUses y ↔ u ∈ dag.freeUses y := by
  rw [Dag.mem_freeUses, Dag.mem_freeUses]
  cases u with
  | gate t pos => rw [Dag.mem_uses_gate, Dag.mem_uses_gate]; rfl
  | root r => rw [Dag.mem_uses_root, Dag.mem_uses_root]; rfl

theorem dagB_valid : dagB.Valid where
  arg_lt := dag_valid.arg_lt
  link_donor := dag_valid.link_donor
  link_user := dag_valid.link_user
  link_inj := dag_valid.link_inj
  free_ne y hy h := by
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ (dag_valid.free_ne y hy)
    have := dagB_mem_freeUses.mpr hu
    rw [h] at this
    exact List.not_mem_nil this
  root_lt := dag_valid.root_lt
  v_le := dag_valid.v_le

theorem dagB_val : dagB.val = dag.val := by
  funext x n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    conv_lhs => rw [Dag.val]
    conv_rhs => rw [Dag.val]
    simp only [show dagB.v = dag.v from rfl, show dagB.arg = dag.arg from rfl]
    split_ifs with h1 h2
    · rfl
    · show dagB.val x _ + dagB.val x _ = dag.val x _ + dag.val x _
      rw [ih _ h2.1, ih _ h2.2]
    · rfl

/-- A use that no donor links is no linked use. -/
theorem linkedB_of_donor {t : ℕ} {pos : Bool} (hnone : (recAt t).donor pos = none) :
    dag.linkedB (.gate t pos) = false := by
  rcases hb : dag.linkedB (.gate t pos) with _ | _
  · rfl
  · exfalso
    obtain ⟨d, _, hd⟩ := (dag.linkedB_iff _).mp hb
    obtain ⟨o, t', pos', hl, he⟩ := dag.linkUse_eq.mp hd
    cases he
    obtain ⟨L, hL, _, rfl, rfl⟩ := dag_link hl
    have := (linkOk_donor hL).2.2.2.2.2.1
    rw [this] at hnone
    cases hnone

theorem freeB_mem {y : ℕ} {u : Use} (h : freeB y u = true) : u ∈ dagB.freeUses y := by
  rw [dagB_mem_freeUses]
  cases u with
  | gate t pos =>
    unfold freeB at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨⟨htN, hadd⟩, harg⟩, hnone⟩ := h
    have hnone' : (recAt t).donor pos = none := by
      unfold recAt
      revert hnone
      cases (records.get width t).donor pos <;> simp
    rw [Dag.mem_freeUses, Dag.mem_uses_gate]
    exact ⟨⟨htN, (isAdd_lt hadd).1, harg⟩, linkedB_of_donor hnone'⟩
  | root j =>
    unfold freeB at h
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    rw [Dag.mem_freeUses, Dag.mem_uses_root]
    exact ⟨⟨h.1, h.2⟩, dag.root_not_linked j⟩

theorem useNodeB_eq (u : Use) : dagB.useNode u = useNodeB u := by
  cases u <;> rfl

/-- The first free use in serving order is the use of rank zero. -/
theorem freeUses_head {D : Dag} {y : ℕ} {w : Use} (hw : w ∈ D.freeUses y)
    (huniq : ∀ u, D.rank y u = 0 → u = w) (h0 : D.rank y w = 0) :
    (D.freeUses y).head? = some w := by
  have hs : (D.uses y).Pairwise fun a b => decide (D.rank y a ≤ D.rank y b) = true :=
    List.pairwise_mergeSort (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _
  have hf : (D.freeUses y).Pairwise fun a b => decide (D.rank y a ≤ D.rank y b) = true :=
    hs.filter _
  cases hl : D.freeUses y with
  | nil => rw [hl] at hw; simp at hw
  | cons h rest =>
    rw [hl] at hw hf
    rw [List.pairwise_cons] at hf
    rcases List.mem_cons.mp hw with rfl | hm
    · rfl
    · have := hf.1 w hm
      simp only [decide_eq_true_eq, h0] at this
      rw [huniq h (by omega)]
      rfl

/-! ### The phase hypotheses -/

/-- The retained centres. -/
def cenB (j : ℕ) : Bool := Nat.ble (3 * leafCount) j

theorem deferredOk_of_mem {u : Use} (hu : u ∈ deferredUses) : deferredOk u = true := by
  simp only [deferredUses, List.mem_append] at hu
  rcases hu with ((h | h) | h) | h
  · exact List.all_eq_true.mp deferredOk0 u h
  · exact List.all_eq_true.mp deferredOk1 u h
  · exact List.all_eq_true.mp deferredOk2 u h
  · exact List.all_eq_true.mp deferredOk3 u h

theorem centreOk_of {j : ℕ} (hj : j < rootCount) (hc : cenB j = true) : centreOk j = true := by
  simp only [cenB, Nat.ble_eq] at hc
  exact List.all_eq_true.mp centresOk j (List.mem_range'_1.mpr ⟨hc, by
    simp only [rootCount, leafCount] at hj ⊢; omega⟩)

theorem phaseHypB : dagB.PhaseHyp phiB psiB cenB (· ∈ deferredUses) where
  psi := psiB_phiB
  arg t hvt htN hp pos hva := by
    obtain ⟨ha, hb⟩ := (bnode_parts htN).2.1 hp
    have hy : dagB.arg t pos = (recAt t).arg pos := rfl
    rw [hy] at hva ⊢
    have hv : leafCount ≤ (recAt t).arg pos := hva
    cases pos
    · simp only [NodeRec.arg, Bool.cond_false] at hv ⊢
      simpa [argOkB, Nat.not_lt.mpr hv] using ha
    · simp only [NodeRec.arg, Bool.cond_true] at hv ⊢
      simpa [argOkB, Nat.not_lt.mpr hv] using hb
  link n o t pos h ht := by
    obtain ⟨L, hL, -, rfl, -⟩ := dag_link h
    exact (bnode_parts (dag_valid.link_donor n o _ pos h).2).2.2 L hL ht
  centre j hj hc := by
    have h := centreOk_of hj hc
    simp only [centreOk, Bool.and_eq_true] at h
    exact h.2
  dfr u hu := by
    have h := deferredOk_of_mem hu
    unfold deferredOk at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨hfree, hlt⟩, hcase⟩ := h
    rw [useNodeB_eq]
    refine ⟨freeB_mem hfree, hlt, ?_⟩
    by_cases hv : leafCount ≤ useNodeB u
    · rw [show dagB.v = leafCount from rfl, ite_eq_left hv]
      rw [show Nat.ble leafCount (useNodeB u) = true from Nat.ble_eq.mpr hv, Bool.cond_true] at hcase
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcase
      obtain ⟨hpsi, hw⟩ := hcase
      refine ⟨hpsi, ?_⟩
      cases hb : (bAt (useNodeB u)).2 with
      | nil => rw [hb] at hw; cases hw
      | cons w ws =>
        rw [hb] at hw
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hw
        obtain ⟨hne, hfw⟩ := hw
        rw [freeUses_head (freeB_mem hfw) (fun u' hu' => by
            have h0 : (w :: ws).idxOf u' = 0 := by rw [← hb]; exact hu'
            rw [List.idxOf_cons] at h0
            by_cases he : (w == u') = true
            · exact (beq_iff_eq.mp he).symm
            · rw [ite_eq_right he] at h0; omega)
          (by simp [dagB, hb])]
        exact fun h => hne (Option.some.inj h)
    · rw [show dagB.v = leafCount from rfl, ite_eq_right hv]
      have hb' : Nat.ble leafCount (useNodeB u) = false := by
        cases h : Nat.ble leafCount (useNodeB u)
        · rfl
        · exact absurd (Nat.le_of_ble_eq_true h) hv
      rw [hb', Bool.cond_false] at hcase
      cases u with
      | gate t pos => simpa [Dag.need] using hcase
      | root j =>
        simp only [Dag.need, cenB]
        simp only [Nat.blt_eq] at hcase
        cases h : Nat.ble (3 * leafCount) j
        · rfl
        · exact absurd (Nat.le_of_ble_eq_true h) (by omega)

end

end IntegerMultBounds.MathlibTM2.M8.Local
