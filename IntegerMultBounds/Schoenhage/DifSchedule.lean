module

public import IntegerMultBounds.Schoenhage.DifGroup

/-! The rounds grouped by slot (the paper's schedule). Rounds of different axes
commute, so running, for each slot from the top down, the round of every
axis long enough to have that slot equals running every axis in turn
(`run_slotMajor`), and so computes `F⁻` with every axis address bit-reversed
(`slotMajor_eq`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Spec.SignedRingProduct NLogN

section Generic

variable {α : Type*}

/-- Axis by axis, each from its top slot down. -/
def axisM (f : ℕ → ℕ → α → α) (a : ℕ → ℕ) (D : ℕ) : List (α → α) :=
  (List.range D).flatMap fun i => (List.range (a i)).reverse.map (f i)

/-- Slot by slot from the top, each over the axes having that slot. -/
def slotM (f : ℕ → ℕ → α → α) (a : ℕ → ℕ) (D H : ℕ) : List (α → α) :=
  (List.range H).reverse.flatMap fun h => ((List.range D).filter fun i => h < a i).map fun i => f i h

theorem flatMap_ite_true (g : ℕ → α → α) (a : ℕ) :
    ∀ l : List ℕ, (∀ h ∈ l, h < a) → (l.flatMap fun h => if h < a then [g h] else []) = l.map g
  | [], _ => rfl
  | x :: l, hl => by
    rw [List.flatMap_cons, if_pos (hl x (by simp)), List.map_cons, flatMap_ite_true g a l
      (fun h hh => hl h (by simp [hh]))]
    rfl

theorem flatMap_desc (g : ℕ → α → α) (a : ℕ) : ∀ H, a ≤ H →
    ((List.range H).reverse.flatMap fun h => if h < a then [g h] else []) = (List.range a).reverse.map g
  | 0, h => by simp at h; subst h; simp
  | H + 1, h => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.flatMap_cons]
    rcases Nat.lt_or_ge H a with hl | hl
    · have ha : a = H + 1 := by omega
      subst ha
      rw [if_pos (by omega), flatMap_ite_true g (H + 1) _ (fun h hh => by simp at hh; omega),
        List.range_succ, List.reverse_append, List.reverse_singleton]
      simp
    · rw [if_neg (by omega), List.nil_append, flatMap_desc g a H hl]

theorem flatMap_nil' (l : List ℕ) : (l.flatMap fun _ => ([] : List (α → α))) = [] := by
  induction l <;> simp_all

theorem run_axisM_slotM (f : ℕ → ℕ → α → α) (a : ℕ → ℕ) (H : ℕ) :
    ∀ D, (∀ i < D, a i ≤ H) → (∀ i j h h', i < D → j < D → i ≠ j → ∀ x, f i h (f j h' x) = f j h' (f i h x)) →
      ∀ x, run (axisM f a D) x = run (slotM f a D H) x
  | 0, _, _, x => by simp [axisM, slotM, run, flatMap_nil']
  | D + 1, ha, hc, x => by
    have e1 : axisM f a (D + 1) = axisM f a D ++ (List.range (a D)).reverse.map (f D) := by
      simp [axisM, List.range_succ, List.flatMap_append]
    have e2 : slotM f a (D + 1) H = (((List.range H).reverse.map fun h =>
        ((((List.range D).filter fun i => h < a i).map fun i => f i h),
          (if h < a D then [f D h] else []))).flatMap fun p => p.1 ++ p.2) := by
      simp only [slotM, List.flatMap_map, List.range_succ, List.filter_append, List.map_append]
      congr 1; funext h
      by_cases hh : h < a D <;> simp [hh]
    rw [e1, e2, run_interleave]
    · rw [run_append, run_append, run_axisM_slotM f a H D (fun i hi => ha i (by omega))
        (fun i j h h' hi hj hij x => hc i j h h' (by omega) (by omega) hij x)]
      simp only [List.flatMap_map]
      rw [flatMap_desc (f D) (a D) H (ha D (by omega))]
      rfl
    · intro p hp q hq g hg g' hg' y
      obtain ⟨h, -, rfl⟩ := List.mem_map.mp hp
      obtain ⟨h', -, rfl⟩ := List.mem_map.mp hq
      simp only at hg hg'
      split_ifs at hg with hhh
      · simp only [List.mem_singleton] at hg
        subst hg
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg'
        simp only [List.mem_filter, List.mem_range] at hj
        exact hc D j h h' (by omega) (by omega) (by omega) y
      · simp at hg

end Generic

variable {r : ℕ} [NeZero r]

/-- The offset of axis `i`: the bits of the later axes. -/
def axOff (ts : List ℕ) (i : ℕ) : ℕ := Nat.log 2 (ts.drop (i + 1)).prod

/-- The number of bits of axis `i`. -/
def axLen (ts : List ℕ) (i : ℕ) : ℕ := Nat.log 2 (ts.getD i 1)

/-- The rounds of axis `i`. -/
noncomputable def axRound (ts : List ℕ) (i h : ℕ) : (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ := difRoundAt (axOff ts i) h

theorem difAllAt_run (o : ℕ) : ∀ (a : ℕ) (z : ℕ → Fin r → ℂ),
    difAllAt o a z = run ((List.range a).reverse.map (difRoundAt o)) z
  | 0, z => rfl
  | a + 1, z => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons]
    exact difAllAt_run o a _

theorem difAxes_run : ∀ (ts : List ℕ) (z : ℕ → Fin r → ℂ),
    difAxes ts z = run (axisM (axRound (r := r) ts) (axLen ts) ts.length) z
  | [], z => rfl
  | t :: ts, z => by
    simp only [difAxes]
    rw [difAxes_run ts, difAllAt_run]
    simp only [axisM, List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, run_append]
    rfl

omit [NeZero r] in
theorem log_prod_cons {t : ℕ} {ts : List ℕ} (h : PowAxes r (t :: ts)) :
    Nat.log 2 (t :: ts).prod = Nat.log 2 t + Nat.log 2 ts.prod := by
  obtain ⟨a, rfl, -⟩ := h t (by simp)
  rw [List.prod_cons, powAxes_prod_pow (powAxes_cons h), ← pow_add, Nat.log_pow (by norm_num),
    Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)]

omit [NeZero r] in
theorem powAxes_drop {ts : List ℕ} (h : PowAxes r ts) (k : ℕ) : PowAxes r (ts.drop k) :=
  fun t ht => h t (List.mem_of_mem_drop ht)

omit [NeZero r] in
/-- A later axis's bits lie below an earlier axis's offset. -/
theorem axOff_le {ts : List ℕ} (h : PowAxes r ts) {i j : ℕ} (hij : i < j) (hj : j < ts.length) :
    axOff ts j + axLen ts j ≤ axOff ts i := by
  unfold axOff axLen
  have key : ∀ k, k < ts.length →
      Nat.log 2 (ts.drop k).prod = Nat.log 2 (ts.getD k 1) + Nat.log 2 (ts.drop (k + 1)).prod := by
    intro k hk
    rw [List.drop_eq_getElem_cons hk, List.getD_eq_getElem _ _ hk]
    exact log_prod_cons (powAxes_drop h k |> fun h' => by rwa [List.drop_eq_getElem_cons hk] at h')
  have mono : ∀ m n, m ≤ n → n ≤ ts.length → Nat.log 2 (ts.drop n).prod ≤ Nat.log 2 (ts.drop m).prod := by
    intro m n hmn hn
    induction n, hmn using Nat.le_induction with
    | base => exact le_refl _
    | succ n hmn ih => have := ih (by omega); rw [key n (by omega)] at this; omega
  rw [Nat.add_comm, ← key j hj]
  exact mono (i + 1) j (by omega) hj.le

theorem axRound_comm {ts : List ℕ} (hts : PowAxes r ts) (i j h h' : ℕ) (hh : h < axLen ts i) (hh' : h' < axLen ts j)
    (hi : i < ts.length) (hj : j < ts.length) (hij : i ≠ j) (z : ℕ → Fin r → ℂ) :
    axRound ts i h (axRound ts j h' z) = axRound ts j h' (axRound ts i h z) := by
  apply difRoundAt_comm
  rcases Nat.lt_or_gt_of_ne hij with hl | hl
  · have := axOff_le hts hl hj; omega
  · have := axOff_le hts hl hi; omega

/-- A round past an axis's length acts as on its own, but never occurs in the schedules. -/
noncomputable def axRoundG (ts : List ℕ) (i h : ℕ) : (ℕ → Fin r → ℂ) → ℕ → Fin r → ℂ :=
  if h < axLen ts i then axRound ts i h else id

/-- `run_slotMajor`: the slot-major schedule equals the axis-major one. -/
theorem run_slotMajor {ts : List ℕ} (hts : PowAxes r ts) {H : ℕ} (hH : ∀ i < ts.length, axLen ts i ≤ H)
    (z : ℕ → Fin r → ℂ) :
    run (slotM (axRound (r := r) ts) (axLen ts) ts.length H) z = difAxes ts z := by
  have e1 : slotM (axRound (r := r) ts) (axLen ts) ts.length H = slotM (axRoundG ts) (axLen ts) ts.length H := by
    simp only [slotM]
    congr 1; funext h
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_filter, decide_eq_true_eq] at hi
    simp [axRoundG, hi.2]
  have e2 : axisM (axRound (r := r) ts) (axLen ts) ts.length = axisM (axRoundG ts) (axLen ts) ts.length := by
    simp only [axisM]
    congr 1; funext i
    apply List.map_congr_left
    intro h hh
    simp only [List.mem_reverse, List.mem_range] at hh
    simp [axRoundG, hh]
  rw [difAxes_run, e1, e2, run_axisM_slotM _ _ H _ hH]
  intro i j h h' hi hj hij x
  unfold axRoundG
  split_ifs with a1 a2 a2
  · exact axRound_comm hts i j h h' a1 a2 hi hj hij x
  all_goals rfl

/-- `slotMajor_eq`: the paper's schedule computes `F⁻` with every axis address bit-reversed. -/
theorem slotMajor_eq {ts : List ℕ} (hts : PowAxes r ts) {H : ℕ} (hH : ∀ i < ts.length, axLen ts i ≤ H)
    (z : ℕ → Fin r → ℂ) {x : ℕ} (hx : x < ts.prod) :
    run (slotM (axRound (r := r) ts) (axLen ts) ts.length H) z x = fwdT ts z (bitrevAddr ts x) := by
  rw [run_slotMajor hts hH, difAxes_eq ts hts z x hx]

end IntegerMultBounds.Schoenhage
