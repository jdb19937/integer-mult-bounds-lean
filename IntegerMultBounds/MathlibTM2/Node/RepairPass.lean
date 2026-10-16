module

public import IntegerMultBounds.MathlibTM2.Node.KeyPass

/-!
# The exact repair after the packed program

After the key pass (`IntegerMultBounds.MathlibTM2.Node.KeyPass`) and the packed program, the stream in rank order holds
`moveRecs π_S (keyRecs k π_T l)`: the record at rank `q` is the record of `l` at rank
`π_S⁻¹ q`, preceded by the `k` bits of its destination `π_T (π_S⁻¹ q)`. Here
`π_S = rankPerm (prog σ)` moves the record at `enc σ a` to `enc σ (packedS a)` and
`π_T = addrPerm σ (idealT L K ρ f)` to `enc σ (idealT a)`.

**The code of the exceptional set.** `badAuto` reads, least significant bit first, the chunk
fields of `y` and `z`, the marker mask `selMask K ρ (f - 1)` (bits `ρ + i K`, `i < f - 1`) and the
guard mask `guardMask` (the guard bits `ρ + i K + 1, …, ρ + i K + K - 1`). Each marker closes the
previous segment and opens a new one; on the guard bits it tracks whether all bits of `y`, resp.
`z`, are `0` or all are `1` (`BSt`). Its code is `1` exactly on `Bad` with margin `1`
(`badAuto_eval`, `idxCode_bad`): a guard `g` fails `1 ≤ g ≤ 2^(K-1) - 2` exactly when it is all
zeros or all ones. It has 18 states, so the alphabet needs `14 ≤ A`.

**The machine** (`repairAt`, `repairPass`). Route the records by the code of their rank into
`gR` (code `0`) and `bR` (code `1`), move them back into forward order in `g` and `b`, reset the
counter, radix sort `b` on its first `k` symbols (`radixSort`), merge `g` and `b` by the same code,
reset the counter, and strip the `k` key symbols of every record (`stripPass`, which reads the
merged stream in reverse and so restores forward order).

**Correctness.** Off `Bad` the packed program agrees with `idealT`, so the code-`0` records are
already those of the ideal stream (`repair_good`, from `inverse_agrees_off_bad`); the code-`1`
records, sorted by destination, are the code-`1` records of the ideal stream (`repair_bad`, from
the vendored `sortedExtracted_eq` behind `repair_exact`, through a map `G` that carries the key
bits). `repairPass_exec`: `src` ends holding `(moveRecs π_T l).flatten`, every other register
ends as it started, in at most `103 M (B + k + 1) + 13 |Bad| k (B + k + 1) + 18 k + 82` steps.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.PackedXor


/-! ### Masks -/

/-- The number whose bit `t` is `p t` for `t < n` and `0` from `n` on. -/
def bitsMask (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bitsMask p n ||| (if p n then 2 ^ n else 0)

lemma testBit_bitsMask (p : ℕ → Bool) (n t : ℕ) :
    (bitsMask p n).testBit t = (decide (t < n) && p t) := by
  induction n with
  | zero => simp [bitsMask]
  | succ n ih =>
      rw [bitsMask, Nat.testBit_or, ih]
      by_cases hp : p n
      · simp only [hp, ↓reduceIte, Nat.testBit_two_pow]
        by_cases htn : t = n
        · subst htn; simp [hp]
        · have : (decide (t < n + 1)) = decide (t < n) := by
            apply decide_eq_decide.mpr; omega
          rw [this]; simp [Ne.symm htn]
      · simp only [hp, Bool.false_eq_true, ↓reduceIte, Nat.zero_testBit, Bool.or_false]
        by_cases htn : t = n
        · subst htn; simp [hp]
        · have : (decide (t < n + 1)) = decide (t < n) := by
            apply decide_eq_decide.mpr; omega
          rw [this]

/-- Bit `t` lies in the guard of a used segment `i < n`: `ρ + i K + 1 ≤ t < ρ + i K + K`. -/
def IsGuardBit (K ρ n t : ℕ) : Prop := ∃ i < n, ρ + i * K + 1 ≤ t ∧ t < ρ + i * K + K

instance (K ρ n t : ℕ) : Decidable (IsGuardBit K ρ n t) := by unfold IsGuardBit; infer_instance

/-- The guard mask: the bits of the guards of the used segments `i < n`, below `L`. -/
def guardMask (K ρ n L : ℕ) : ℕ := bitsMask (fun t => decide (IsGuardBit K ρ n t)) L

lemma testBit_guardMask (K ρ n L t : ℕ) :
    (guardMask K ρ n L).testBit t = (decide (t < L) && decide (IsGuardBit K ρ n t)) :=
  testBit_bitsMask _ _ _

/-! ### The code automaton of the exceptional set -/

/-- States of the exceptional-set automaton: before the first used segment, exceptional, or
inside a used segment with the four flags "all guard bits of `y` so far are `0`", "… are `1`",
and the same for `z`. -/
inductive BSt
  | inact
  | bad
  | act (y0 y1 z0 z1 : Bool)
  deriving DecidableEq

/-- Whether the segments read so far make the address exceptional. -/
def BSt.β : BSt → Bool
  | .inact => false
  | .bad => true
  | .act a b c d => a || b || c || d

/-- One column `(y_t, z_t, marker_t, guard_t)`: a marker (bit `ρ + i K`) closes the previous
segment and opens a new one; a guard bit updates the flags. -/
def bStep (s : BSt) (col : Fin 4 → Bool) : BSt :=
  if col 2 then (if s.β then .bad else .act true true true true)
  else if col 3 then
    match s with
    | .act a b c d => .act (a && !col 0) (b && col 0) (c && !col 1) (d && col 1)
    | s => s
  else s

/-- The state number. -/
def BSt.code : BSt → ℕ
  | .inact => 0
  | .bad => 1
  | .act a b c d => 2 + a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat

lemma BSt.code_lt (s : BSt) : s.code < 18 := by
  cases s with
  | inact => decide
  | bad => decide
  | act a b c d => cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- A state as a stack symbol. -/
def bEnc {A : ℕ} (s : BSt) : Fin (A + 4) := ⟨s.code % (A + 4), Nat.mod_lt _ (by omega)⟩

/-- A stack symbol as a state. -/
def bDec {A : ℕ} (x : Fin (A + 4)) : BSt :=
  if x.val = 0 then .inact
  else if x.val = 1 then .bad
  else .act ((x.val - 2).testBit 0) ((x.val - 2).testBit 1) ((x.val - 2).testBit 2)
    ((x.val - 2).testBit 3)

lemma bDec_bEnc {A : ℕ} (hA : 14 ≤ A) (s : BSt) : bDec (bEnc (A := A) s) = s := by
  have h := s.code_lt
  simp only [bDec, bEnc, Nat.mod_eq_of_lt (show s.code < A + 4 by omega)]
  cases s with
  | inact => rfl
  | bad => rfl
  | act a b c d => cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- The code automaton of the exceptional set on the registers `(y, z, marker, guard)`: code `1`
when some used guard of `y` or of `z` is all zeros or all ones. -/
def badAuto (A : ℕ) : CAuto A 4 2 :=
  absAuto bEnc bDec .inact bStep fun s => if s.β then 1 else 0

/-! ### Correctness of the automaton -/

section BadCorrect

variable (y z mk g : ℕ)

/-- The input column at bit position `t`. -/
def bcol (t : ℕ) : Fin 4 → Bool := ![y.testBit t, z.testBit t, mk.testBit t, g.testBit t]

lemma foldl_idle (ts : List ℕ) (h : ∀ t ∈ ts, mk.testBit t = false ∧ g.testBit t = false)
    (s : BSt) : ts.foldl (fun s t => bStep s (bcol y z mk g t)) s = s := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      rw [List.foldl_cons]
      have h1 := h t List.mem_cons_self
      have : bStep s (bcol y z mk g t) = s := by simp [bStep, bcol, h1.1, h1.2]
      rw [this]
      exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht)) s

lemma foldl_guard (ts : List ℕ) (h : ∀ t ∈ ts, mk.testBit t = false ∧ g.testBit t = true) :
    ∀ a b c d : Bool, ts.foldl (fun s t => bStep s (bcol y z mk g t)) (.act a b c d) =
      .act (a && ts.all fun t => !y.testBit t) (b && ts.all fun t => y.testBit t)
        (c && ts.all fun t => !z.testBit t) (d && ts.all fun t => z.testBit t) := by
  induction ts with
  | nil => intro a b c d; simp
  | cons t ts ih =>
      intro a b c d
      rw [List.foldl_cons]
      have h1 := h t List.mem_cons_self
      have : bStep (.act a b c d) (bcol y z mk g t) =
          .act (a && !y.testBit t) (b && y.testBit t) (c && !z.testBit t) (d && z.testBit t) := by
        simp [bStep, bcol, h1.1, h1.2]
      rw [this, ih (fun t ht => h t (List.mem_cons_of_mem _ ht))]
      simp [Bool.and_assoc]

lemma foldl_guard_bad (ts : List ℕ) (h : ∀ t ∈ ts, mk.testBit t = false ∧ g.testBit t = true) :
    ts.foldl (fun s t => bStep s (bcol y z mk g t)) .bad = .bad := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      rw [List.foldl_cons]
      have h1 := h t List.mem_cons_self
      have : bStep .bad (bcol y z mk g t) = .bad := by simp [bStep, bcol, h1.1, h1.2]
      rw [this, ih (fun t ht => h t (List.mem_cons_of_mem _ ht))]

/-- The badness of one segment: some guard run is constant. -/
def segBadB (p w : ℕ) : Bool :=
  ((List.range w).all fun u => !y.testBit (p + u)) ||
    ((List.range w).all fun u => y.testBit (p + u)) ||
    ((List.range w).all fun u => !z.testBit (p + u)) ||
    ((List.range w).all fun u => z.testBit (p + u))

/-- One segment: a marker at `p`, then `w` guard bits. -/
lemma foldl_segment (p w : ℕ) (hmk : mk.testBit p = true)
    (hg : ∀ u < w, mk.testBit (p + 1 + u) = false ∧ g.testBit (p + 1 + u) = true) (s : BSt) :
    (((List.range (w + 1)).map (p + ·)).foldl (fun s t => bStep s (bcol y z mk g t)) s).β =
      (s.β || segBadB y z (p + 1) w) := by
  rw [List.range_succ_eq_map, List.map_cons, List.foldl_cons, List.map_map]
  have hs : bStep s (bcol y z mk g (p + 0)) = if s.β then .bad else .act true true true true := by
    simp [bStep, bcol, hmk]
  rw [hs]
  have hts : ∀ t ∈ (List.range w).map ((p + ·) ∘ Nat.succ),
      mk.testBit t = false ∧ g.testBit t = true := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
    have := hg u (List.mem_range.1 hu)
    simpa [Nat.add_assoc, Nat.add_comm 1 u] using this
  have hall : ∀ (q : ℕ → Bool), ((List.range w).map ((p + ·) ∘ Nat.succ)).all q =
      (List.range w).all fun u => q (p + 1 + u) := by
    intro q
    rw [List.all_map]
    congr 1
    funext u
    simp [Nat.add_assoc, Nat.add_comm 1 u]
  by_cases hb : s.β
  · simp only [hb, ↓reduceIte, Bool.true_or]
    rw [foldl_guard_bad y z mk g _ hts]; rfl
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.false_or]
    rw [foldl_guard y z mk g _ hts]
    simp only [BSt.β, Bool.true_and, hall, segBadB]

/-- A guard is `0` exactly when all its bits are `0`. -/
lemma mod_eq_zero_iff_bits (v p w : ℕ) :
    v / 2 ^ p % 2 ^ w = 0 ↔ ((List.range w).all fun u => !v.testBit (p + u)) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h u hu
    have := congrArg (fun x => x.testBit u) h
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit] at this
    simp only [List.mem_range] at hu
    simp [hu] at this
    simp only [Bool.not_eq_true']
    rw [Nat.add_comm p u]
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro u
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit]
    by_cases hu : u < w
    · have := h u (List.mem_range.2 hu)
      simp only [Bool.not_eq_true'] at this
      simp [hu, Nat.add_comm u p, this]
    · simp [hu]

/-- A guard is `2^w - 1` exactly when all its bits are `1`. -/
lemma mod_eq_max_iff_bits (v p w : ℕ) :
    v / 2 ^ p % 2 ^ w = 2 ^ w - 1 ↔ ((List.range w).all fun u => v.testBit (p + u)) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h u hu
    have := congrArg (fun x => x.testBit u) h
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one]
      at this
    simp only [List.mem_range] at hu
    simpa [hu, Nat.add_comm p u] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro u
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one]
    by_cases hu : u < w
    · have := h u (List.mem_range.2 hu)
      simp [hu, Nat.add_comm u p, this]
    · simp [hu]

end BadCorrect

section BadEval

variable (K ρ n : ℕ)

lemma not_guardOK_iff (v i : ℕ) :
    ¬ GuardOK K ρ 1 v i ↔ guard K ρ v i = 0 ∨ guard K ρ v i = 2 ^ (K - 1) - 1 := by
  have hlt : guard K ρ v i < 2 ^ (K - 1) := Nat.mod_lt _ (by positivity)
  have hpos : 0 < 2 ^ (K - 1) := by positivity
  unfold GuardOK
  omega

lemma segBadB_eq (y z i : ℕ) :
    segBadB y z (ρ + i * K + 1) (K - 1) =
      decide (¬ (GuardOK K ρ 1 y i ∧ GuardOK K ρ 1 z i)) := by
  have hy0 := mod_eq_zero_iff_bits y (ρ + i * K + 1) (K - 1)
  have hy1 := mod_eq_max_iff_bits y (ρ + i * K + 1) (K - 1)
  have hz0 := mod_eq_zero_iff_bits z (ρ + i * K + 1) (K - 1)
  have hz1 := mod_eq_max_iff_bits z (ρ + i * K + 1) (K - 1)
  rw [Bool.eq_iff_iff, decide_eq_true_iff, not_and_or, not_guardOK_iff, not_guardOK_iff]
  unfold IntegerMultBounds.MathlibTM2.Layer.PackedXor.guard segBadB
  simp only [Bool.or_eq_true]
  rw [← hy0, ← hy1, ← hz0, ← hz1]
  tauto

lemma testBit_selMask_seg (m u : ℕ) (hm : m < n) (hu : u < K) :
    (selMask K ρ n).testBit (ρ + m * K + u) = decide (u = 0) := by
  rw [Bool.eq_iff_iff, testBit_selMask, decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, he⟩
    rcases Nat.lt_or_ge i (m + 1) with h | h
    · have : i * K ≤ m * K := Nat.mul_le_mul_right K (by omega)
      by_contra hu0
      rcases Nat.lt_or_ge i m with h' | h'
      · have : (i + 1) * K ≤ m * K := Nat.mul_le_mul_right K h'
        rw [Nat.add_mul] at this
        omega
      · have : i = m := by omega
        subst this; omega
    · have : (m + 1) * K ≤ i * K := Nat.mul_le_mul_right K h
      rw [Nat.add_mul] at this
      omega
  · rintro rfl
    exact ⟨m, hm, by omega⟩

lemma isGuardBit_seg (m u : ℕ) (hm : m < n) (hu : u < K) :
    IsGuardBit K ρ n (ρ + m * K + u) ↔ u ≠ 0 := by
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    rintro rfl
    rcases Nat.lt_or_ge i m with h | h
    · have : (i + 1) * K ≤ m * K := Nat.mul_le_mul_right K h
      rw [Nat.add_mul] at this
      omega
    · have : m * K ≤ i * K := Nat.mul_le_mul_right K h
      omega
  · intro hu0
    exact ⟨m, hm, by omega, by omega⟩

lemma not_isSel_lo (t : ℕ) (ht : t < ρ) : (selMask K ρ n).testBit t = false := by
  rw [← Bool.not_eq_true, testBit_selMask]
  rintro ⟨i, _, rfl⟩
  omega

lemma not_isGuardBit_lo (t : ℕ) (ht : t < ρ) : ¬ IsGuardBit K ρ n t := by
  rintro ⟨i, _, h1, _⟩
  omega

lemma not_isSel_hi (hK : 1 ≤ K) (t : ℕ) (ht : ρ + n * K ≤ t) :
    (selMask K ρ n).testBit t = false := by
  rw [← Bool.not_eq_true, testBit_selMask]
  rintro ⟨i, hi, rfl⟩
  have : (i + 1) * K ≤ n * K := Nat.mul_le_mul_right K hi
  rw [Nat.add_mul] at this
  omega

lemma not_isGuardBit_hi (t : ℕ) (ht : ρ + n * K ≤ t) : ¬ IsGuardBit K ρ n t := by
  rintro ⟨i, hi, _, h2⟩
  have : (i + 1) * K ≤ n * K := Nat.mul_le_mul_right K hi
  rw [Nat.add_mul] at this
  omega

/-- The used segments `i < m` of the middle part. -/
lemma foldl_segments (hK : 1 ≤ K) (L : ℕ) (hL : ρ + n * K ≤ L) (y z : ℕ) :
    ∀ m ≤ n, (((List.range (m * K)).map (ρ + ·)).foldl
        (fun s t => bStep s (bcol y z (selMask K ρ n) (guardMask K ρ n L) t)) .inact).β =
      (List.range m).any fun i => segBadB y z (ρ + i * K + 1) (K - 1) := by
  intro m
  induction m with
  | zero => intro _; simp [BSt.β]
  | succ m ih =>
      intro hm
      rw [Nat.add_mul, Nat.one_mul, List.range_add, List.map_append, List.foldl_append,
        List.map_map]
      have hK' : K = K - 1 + 1 := by omega
      have hseg := foldl_segment y z (selMask K ρ n) (guardMask K ρ n L) (ρ + m * K) (K - 1)
        (by rw [show ρ + m * K = ρ + m * K + 0 by ring, testBit_selMask_seg K ρ n m 0 (by omega)
          (by omega)]; rfl)
        (by
          intro u hu
          refine ⟨?_, ?_⟩
          · rw [show ρ + m * K + 1 + u = ρ + m * K + (1 + u) by ring,
              testBit_selMask_seg K ρ n m (1 + u) (by omega) (by omega)]
            simp
          · rw [testBit_guardMask, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
              show ρ + m * K + 1 + u = ρ + m * K + (1 + u) by ring]
            refine ⟨?_, (isGuardBit_seg K ρ n m (1 + u) (by omega) (by omega)).2 (by omega)⟩
            have : (m + 1) * K ≤ n * K := Nat.mul_le_mul_right K hm
            rw [Nat.add_mul] at this
            omega)
      have hmap : (List.range K).map ((ρ + ·) ∘ (m * K + ·)) =
          (List.range (K - 1 + 1)).map (ρ + m * K + ·) := by
        rw [← hK']
        refine List.map_congr_left fun t _ => ?_
        simp [Nat.add_assoc]
      rw [hmap, hseg, ih (by omega), List.range_succ, List.any_append]
      simp

/-- **The code of the exceptional set.** On the registers `y`, `z`, the marker mask
`selMask K ρ n` and the guard mask, the automaton outputs `1` exactly when some used guard
`i < n` of `y` or `z` fails `GuardOK` with margin `1`. -/
theorem badAuto_eval {A : ℕ} (hA : 14 ≤ A) (hρ : ρ < K) (y z : ℕ) :
    (badAuto A).eval ((n + 1) * K) ![y, z, selMask K ρ n, guardMask K ρ n ((n + 1) * K)] =
      if ∃ i < n, ¬ (GuardOK K ρ 1 y i ∧ GuardOK K ρ 1 z i) then 1 else 0 := by
  have hK : 1 ≤ K := by omega
  set mk := selMask K ρ n
  set g := guardMask K ρ n ((n + 1) * K)
  unfold badAuto
  rw [absAuto_eval _ _ (bDec_bEnc hA)]
  have hcol : (fun s t => bStep s fun r => ((![y, z, mk, g] : Fin 4 → ℕ) r).testBit t) =
      fun s t => bStep s (bcol y z mk g t) := by
    funext s t
    congr 1
    funext r
    fin_cases r <;> rfl
  rw [hcol]
  have hL : (n + 1) * K = ρ + n * K + (K - ρ) := by rw [Nat.add_mul]; omega
  rw [hL, List.range_add, List.range_add, List.foldl_append, List.foldl_append]
  rw [foldl_idle y z mk g (List.range ρ) (fun t ht => by
      have ht' := List.mem_range.1 ht
      refine ⟨not_isSel_lo K ρ n t ht', ?_⟩
      rw [testBit_guardMask]
      simp [not_isGuardBit_lo K ρ n t ht'])]
  rw [foldl_idle y z mk g _ (fun t ht => by
      obtain ⟨u, _, rfl⟩ := List.mem_map.1 ht
      refine ⟨not_isSel_hi K ρ n hK _ (by omega), ?_⟩
      rw [testBit_guardMask]
      simp [not_isGuardBit_hi K ρ n _ (by omega : ρ + n * K ≤ ρ + n * K + u)])]
  have hseg : ((((List.range (n * K)).map (ρ + ·)).foldl
      (fun s t => bStep s (bcol y z mk g t)) .inact).β) =
      (List.range n).any fun i => segBadB y z (ρ + i * K + 1) (K - 1) :=
    foldl_segments K ρ n hK ((n + 1) * K) (by rw [Nat.add_mul]; omega) y z n le_rfl
  have hiff : ((List.range n).any fun i => segBadB y z (ρ + i * K + 1) (K - 1)) = true ↔
      ∃ i < n, ¬ (GuardOK K ρ 1 y i ∧ GuardOK K ρ 1 z i) := by
    rw [List.any_eq_true]
    simp only [List.mem_range, segBadB_eq K ρ y z, decide_eq_true_iff]
  rw [hseg]
  by_cases h : ∃ i < n, ¬ (GuardOK K ρ 1 y i ∧ GuardOK K ρ 1 z i)
  · simp only [hiff.2 h, h, ↓reduceIte]
  · have h' := mt hiff.1 h
    simp only [h', h, ↓reduceIte, Bool.false_eq_true]

end BadEval

/-! ### Stripping the keys -/

section Strip

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- One symbol of `dropBlock`: move a counter symbol from `ctr` to `tmp` and pop `src`. -/
def stripStep (src ctr tmp : Fin T) : Act T Q A U :=
  .pop (.rt ctr) (fun v o => { v with sym := o })
    (.push (.rt tmp) (fun v => v.sym.getD blank) (.pop (.rt src) (fun v _ => v) (peekR ctr)))

/-- Pop `|ctr|` symbols of `src`, counted by `ctr` through the empty register `tmp`. -/
def dropBlock (src ctr tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR ctr)) (.seq (.loop (·.flag) (.act (stripStep src ctr tmp))) (moveR tmp ctr id))

/-- The symbol loop of `dropBlock`. -/
theorem stripStep_loop (src ctr tmp : Fin T) (h1 : src ≠ ctr) (h2 : src ≠ tmp) (h3 : ctr ≠ tmp) :
    ∀ (c₁ ys rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      c₁.length = ys.length → S.R ctr = c₁ → S.R src = ys ++ rest → v.flag = c₁.head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (stripStep src ctr tmp))) (mk v S) (2 * c₁.length + 1)
          (mk v' { S with R := R' }) ∧
        R' = Function.update (Function.update (Function.update S.R ctr []) tmp
          (c₁.reverse ++ S.R tmp)) src rest := by
  intro c₁
  induction c₁ with
  | nil =>
      intro ys rest v S hlen hc hs hf
      obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
      refine ⟨v, S.R, rfl, .loop_false (by simpa using hf), ?_⟩
      funext k
      by_cases hk : k = src
      · subst hk; simp [hs]
      by_cases hk' : k = tmp
      · subst hk'; simp [hk]
      by_cases hk'' : k = ctr
      · subst hk''; simp [hk, hk', hc]
      simp [hk, hk', hk'']
  | cons e c₁ ih =>
      intro ys rest v S hlen hc hs hf
      cases ys with
      | nil => simp at hlen
      | cons x ys =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        obtain ⟨v', R', hu, he, hR'⟩ := ih ys rest { v with sym := some e, flag := c₁.head?.isSome }
          { S with R := Function.update (Function.update (Function.update S.R ctr c₁) tmp
            (e :: S.R tmp)) src (ys ++ rest) } hlen
          (by simp [Function.update_of_ne h1.symm, Function.update_of_ne h3])
          (by simp) rfl
        have hrun : (stripStep src ctr tmp : Act T Q A U).run (mk v S) =
            mk { v with sym := some e, flag := c₁.head?.isSome }
              { S with R := Function.update (Function.update (Function.update S.R ctr c₁) tmp
                (e :: S.R tmp)) src (ys ++ rest) } := by
          simp [stripStep, peekR, Action.run, hc, hs, update_rt, Function.update_of_ne h1,
            Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1.symm,
            Function.update_of_ne h3.symm]
        refine ⟨v', R', hu, Exec.cast (Exec.loop_true (body := body) (f := (·.flag))
          (by simpa using hf) (hrun ▸ Exec.act (body := body) _ (mk v S)) he)
          (by simp; ring) rfl, ?_⟩
        rw [hR']
        funext k
        by_cases hk : k = src
        · subst hk; simp
        by_cases hk' : k = tmp
        · subst hk'; simp [hk]
        by_cases hk'' : k = ctr
        · subst hk''; simp [hk, hk']
        simp [hk, hk', hk'']

/-- `dropBlock` pops `ys` (as many symbols as `ctr`) from `src`; `ctr` and `tmp` are restored.
Exactly `4 * |ctr| + 4` steps. -/
theorem dropBlock_exec (src ctr tmp : Fin T) (h1 : src ≠ ctr) (h2 : src ≠ tmp) (h3 : ctr ≠ tmp)
    (c ys rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hlen : c.length = ys.length) (hc : S.R ctr = c) (ht : S.R tmp = [])
    (hs : S.R src = ys ++ rest) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (dropBlock src ctr tmp) (mk v S) (4 * c.length + 4)
        (mk v' { S with R := Function.update S.R src rest }) := by
  obtain ⟨v₁, R₁, hu₁, he₁, hR₁⟩ := stripStep_loop body src ctr tmp h1 h2 h3 c ys rest
    { v with flag := c.head?.isSome } S hlen hc hs rfl
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tmp ctr h3.symm id v₁ { S with R := R₁ }
  have he₀ := Exec.act (body := body) (peekR ctr) (mk v S)
  rw [peekR_run, hc] at he₀
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq he₀ (Exec.seq he₁ he₂)) ?_ ?_⟩
  · simp [hR₁, Function.update_of_ne h2.symm, ht]; ring
  · congr 2
    funext k
    rw [hR₁]
    by_cases hk : k = src
    · subst hk; simp [movedR, h1, h2]
    by_cases hk' : k = tmp
    · subst hk'; simp [movedR, hk, Function.update_of_ne h3.symm, ht]
    by_cases hk'' : k = ctr
    · subst hk''; simp [movedR, hk, hk', Function.update_of_ne h2.symm, hc,
        ht]
    simp [movedR, hk, hk', hk'']

/-- One record of the strip pass: `|ctrB|` symbols from `src` onto `dst`, then `|ctrK|` symbols
of `src` dropped. -/
def stripRec (src dst ctrB ctrK tmp st : Fin T) : Pr P T Q A U :=
  .seq (xferBlock (fun _ : Fin 1 => src) (fun _ => dst) ctrB tmp st 1 (fun _ => 0) .done)
    (.seq (dropBlock src ctrK tmp) (.act (peekR src)))

/-- The strip pass: records `stripRec` while `src` is nonempty. -/
def stripPass (src dst ctrB ctrK tmp st : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR src)) (.loop (·.flag) (stripRec src dst ctrB ctrK tmp st))

/-- The record loop of the strip pass on the reversed records `Z`. -/
theorem stripLoop_exec (src dst ctrB ctrK tmp st : Fin T)
    (hnd : [src, dst, ctrB, ctrK, tmp].Nodup) {k B : ℕ} (hB : 1 ≤ B) (cB cK : List (Fin (A + 4)))
    (hcB : cB.length = B) (hcK : cK.length = k) :
    ∀ (Z : List (List (Fin (A + 4)))) (v : HS T Q A U) (S : Stacks T A),
      (∀ z ∈ Z, z.length = k + B) → S.R src = (Z.map List.reverse).flatten → S.R ctrB = cB →
      S.R ctrK = cK → S.R tmp = [] → v.flag = (Z.map List.reverse).flatten.head?.isSome →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (stripRec src dst ctrB ctrK tmp st)) (mk v S)
          (Z.length * (4 * B + 4 * k + 11) + 1)
          (mk v' { S with R := (Function.update (Function.update S.R src [])
            dst ((Z.reverse.map (·.drop k)).flatten ++ S.R dst)) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hnd
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1⟩ := hnd
  intro Z
  induction Z with
  | nil =>
      intro v S _ hs _ _ _ hf
      refine ⟨v, rfl, Exec.cast (.loop_false (by simpa using hf)) (by simp) ?_⟩
      congr 1
      refine Stacks.ext rfl rfl rfl ?_
      funext x
      show S.R x = _
      by_cases hx : x = dst
      · subst hx; simp
      by_cases hx' : x = src
      · subst hx'; simp [hx, hs]
      simp [hx, hx']
  | cons z Z ih =>
      intro v S hZ hs hcb hck ht hf
      have hz : z.length = k + B := hZ z List.mem_cons_self
      have hzr : z.reverse = (z.drop k).reverse ++ (z.take k).reverse := by
        conv_lhs => rw [← List.take_append_drop k z]
        rw [List.reverse_append]
      have hdl : (z.drop k).reverse.length = B := by simp [hz]
      have htl : (z.take k).reverse.length = k := by simp [hz]
      obtain ⟨v₁, R₁, hu₁, -, he₁, hctr₁, htmp₁, hsrc₁, hdst₁, hoth₁⟩ :=
        xferBlock_exec body (fun _ : Fin 1 => src) (fun _ => dst) ctrB tmp st 1 (fun _ => 0) .done 0
          a2 a4 c2 (Ne.symm a1) b1 b3 cB (z.drop k).reverse
          ((z.take k).reverse ++ (Z.map List.reverse).flatten) v S (by rw [hcB, hdl]) hcb ht
          (by simp [hs, hzr]) (Subsingleton.elim _ _)
      rw [run_done] at he₁
      have hR₁ : ∀ x, x ≠ src → x ≠ dst → R₁ x = S.R x := fun x h1 h2 => by
        by_cases hx : x = ctrB
        · subst hx; rw [hctr₁, hcb]
        by_cases hx' : x = tmp
        · subst hx'; rw [htmp₁, ht]
        exact hoth₁ x h1 hx hx' h2
      obtain ⟨v₂, hu₂, he₂⟩ := dropBlock_exec body src ctrK tmp a3 a4 d1 cK (z.take k).reverse
        (Z.map List.reverse).flatten _ { S with R := R₁ } (by rw [hcK, htl])
        (by show R₁ ctrK = cK; rw [hR₁ _ (Ne.symm a3) (Ne.symm b2), hck]) htmp₁ hsrc₁
      set S₂ : Stacks T A := { S with
        R := Function.update R₁ src (Z.map List.reverse).flatten } with hS₂
      have he₃ : Exec body (.act (peekR src)) (mk v₂ S₂) 1
          (mk { v₂ with flag := ((Z.map List.reverse).flatten).head?.isSome } S₂) :=
        Exec.cast (Exec.act (body := body) (peekR src) (mk v₂ S₂)) rfl
          (by rw [peekR_run]; simp [hS₂])
      obtain ⟨v', hu', he'⟩ := ih { v₂ with flag := ((Z.map List.reverse).flatten).head?.isSome }
        S₂ (fun z' hz' => hZ z' (List.mem_cons_of_mem _ hz')) (by simp [hS₂])
        (by simp [hS₂, Function.update_of_ne (Ne.symm a2), hR₁ _ (Ne.symm a2) (Ne.symm b1), hcb])
        (by simp [hS₂, Function.update_of_ne (Ne.symm a3), hR₁ _ (Ne.symm a3) (Ne.symm b2), hck])
        (by simp [hS₂, Function.update_of_ne (Ne.symm a4), htmp₁]) rfl
      have hne : z.reverse ≠ [] := by
        intro e; have := congrArg List.length e; simp [hz] at this; omega
      have hft : v.flag = true := by
        rw [hf]
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
        simp [hx]
      refine ⟨v', by rw [hu', hu₂, hu₁], Exec.cast (Exec.loop_true (body := body) (f := (·.flag))
        hft (Exec.seq he₁ (Exec.seq he₂ he₃)) he') (by rw [hcB, hcK, List.length_cons]; ring) ?_⟩
      congr 2
      funext x
      by_cases hx : x = dst
      · subst hx
        simp [hS₂, Ne.symm a1, hdst₁, List.reverse_cons, List.map_append, List.flatten_append]
      by_cases hx' : x = src
      · subst hx'; simp [hS₂, hx]
      simp [hS₂, hx, hx', hR₁ x hx' hx]

/-- **Strip pass.** The register `src` holds the records `Y` (each of `k + B` symbols, `B ≥ 1`)
flattened and reversed; `dst` gains the records with their first `k` symbols dropped, in forward
order, and `src` is emptied. Every other register is restored. Exactly
`|Y| * (4 * B + 4 * k + 11) + 2` steps. -/
theorem stripPass_exec (src dst ctrB ctrK tmp st : Fin T)
    (hnd : [src, dst, ctrB, ctrK, tmp].Nodup) {k B : ℕ} (hB : 1 ≤ B)
    (Y : List (List (Fin (A + 4)))) (hY : ∀ y ∈ Y, y.length = k + B) (v : HS T Q A U)
    (S : Stacks T A) (hs : S.R src = Y.flatten.reverse) (hcb : (S.R ctrB).length = B)
    (hck : (S.R ctrK).length = k) (ht : S.R tmp = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (stripPass src dst ctrB ctrK tmp st) (mk v S) (Y.length * (4 * B + 4 * k + 11) + 2)
        (mk v' { S with R := (Function.update (Function.update S.R src [])
          dst ((Y.map (·.drop k)).flatten ++ S.R dst)) }) := by
  have hs' : S.R src = (Y.reverse.map List.reverse).flatten := by
    rw [hs, List.reverse_flatten, List.map_reverse]
  obtain ⟨v', hu, he⟩ := stripLoop_exec body src dst ctrB ctrK tmp st hnd hB (S.R ctrB) (S.R ctrK)
    hcb hck Y.reverse { v with flag := (S.R src).head?.isSome } S
    (fun y hy => hY y (List.mem_reverse.1 hy)) hs' rfl rfl ht (by rw [hs'])
  rw [List.reverse_reverse, List.length_reverse] at he
  exact ⟨v', hu, Exec.cast (Exec.seq (Exec.act (body := body) (peekR src) (mk v S)) he)
    (by ring) rfl⟩

end Strip

/-! ### Record lists by code -/

section Lists

variable {α : Type}

lemma map_getD_range (X : List (List α)) :
    (List.range X.length).map (fun n => X.getD n []) = X := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [List.getElem?_eq_getElem h2]

/-- The records of `X` with index code `d`, in order. -/
def codeRecs {nd : ℕ} (X : List (List α)) (code : ℕ → Fin nd) (d : Fin nd) : List (List α) :=
  ((List.range X.length).filter fun n => code n = d).map fun n => X.getD n []

lemma blocksIdx_flatten {nd : ℕ} (X : List (List α)) (W : ℕ) (hX : ∀ r ∈ X, r.length = W)
    (code : ℕ → Fin nd) (d : Fin nd) :
    blocksIdx X.flatten W X.length code 0 d = (codeRecs X code d).flatten := by
  have hg : ∀ j < X.length, (X.getD j []).length = W := fun j hj => by
    rw [List.getD_eq_getElem _ _ hj]; exact hX _ (List.getElem_mem hj)
  have hflat : X.flatten = (List.range X.length).flatMap fun n => X.getD n [] := by
    rw [List.flatMap_def, map_getD_range]
  unfold blocksIdx codeRecs
  rw [List.flatMap_def]
  congr 1
  simp only [Nat.zero_add]
  refine List.map_congr_left fun n hn => ?_
  have hn' : n < X.length := List.mem_range.1 (List.mem_filter.1 hn).1
  rw [hflat]
  exact blk_flatMap_range X.length hg n hn'

lemma length_codeRecs {nd : ℕ} (X : List (List α)) (code : ℕ → Fin nd) (d : Fin nd) :
    (codeRecs X code d).length ≤ X.length := by
  unfold codeRecs
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

lemma length_codeRecs_flatten {nd : ℕ} (X : List (List α)) (W : ℕ) (hX : ∀ r ∈ X, r.length = W)
    (code : ℕ → Fin nd) (d : Fin nd) :
    (codeRecs X code d).flatten.length = (codeRecs X code d).length * W := by
  apply length_flatten_of_length
  intro r hr
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hr
  have hn' : n < X.length := List.mem_range.1 (List.mem_filter.1 hn).1
  rw [List.getD_eq_getElem _ _ hn']
  exact hX _ (List.getElem_mem hn')

lemma mem_codeRecs {nd : ℕ} {X : List (List α)} {code : ℕ → Fin nd} {d : Fin nd} {r : List α}
    (hr : r ∈ codeRecs X code d) : r ∈ X := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hr
  have hn' : n < X.length := List.mem_range.1 (List.mem_filter.1 hn).1
  rw [List.getD_eq_getElem _ _ hn']
  exact List.getElem_mem hn'

end Lists

/-! ### The repair machine -/

section RepairMachine

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {nf : ℕ}

/-- The repair pass on generic code registers: route by the code `C` into `gR` (code `0`) and
`bR` (code `1`); restore forward order into `g` and `b`; reset the counter; radix sort `b` on
`|ctrK|` key bits (temporaries `us`, buckets `gR`, `bR`); merge `g` and `b` by the same code into
`gR`; reset the counter; strip `|ctrK|` key symbols from every record, back into `src`. -/
def repairAt (src gR bR g b ctrKB ctrB ctrK cnt tmp st : Fin T) (cf : Fin nf → Fin T)
    (rs us : Fin 4 → Fin T) (C : CAuto A 4 2) : Pr P T Q A U :=
  .seq (routeIdx src ![gR, bR] ctrKB tmp cf rs us st C)
    (.seq (moveR gR g id)
      (.seq (moveR bR b id)
        (.seq (resetFields cf tmp)
          (.seq (radixSort b ctrKB (us 0) (us 1) (us 2) (us 3) gR bR st ctrK)
            (.seq (mergeIdx ![g, b] gR ctrKB tmp cnt bR cf rs us st C)
              (.seq (resetFields cf tmp) (stripPass gR src ctrB ctrK tmp st)))))))

/-- Register facts of the repair machine. -/
structure RepairLayout (src gR bR g b ctrKB ctrB ctrK cnt tmp st : Fin T) (cf : Fin nf → Fin T)
    (len : Fin nf → ℕ) (L : ℕ) (rs us : Fin 4 → Fin T) (rsrc : Fin 4 → Fin nf ⊕ ℕ) : Prop where
  route : IdxLayout cf len L rs us rsrc st (routeRegs src ![gR, bR] ctrKB tmp)
  merge : IdxLayout cf len L rs us rsrc st (mergeRegs ![g, b] gR ctrKB tmp cnt bR)
  regs : [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp].Nodup
  cf_regs : ∀ f, cf f ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp]
  us_regs : ∀ r, us r ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp]

/-- **The repair machine.** The register `src` holds the records `X` (each of `k + B` symbols,
`B ≥ 1`), the counter is at index `0`. If the records of code `0` of `X` and of `Y` agree, and the
records of code `1` of `X`, radix sorted on their first `k` symbols, are the records of code `1`
of `Y`, then `src` ends holding the records of `Y` without their first `k` symbols; every other
register ends as it started. -/
theorem repairAt_exec {src gR bR g b ctrKB ctrB ctrK cnt tmp st : Fin T} {cf : Fin nf → Fin T}
    {len : Fin nf → ℕ} {L : ℕ} {rs us : Fin 4 → Fin T} {rsrc : Fin 4 → Fin nf ⊕ ℕ}
    (h : RepairLayout src gR bR g b ctrKB ctrB ctrK cnt tmp st cf len L rs us rsrc)
    (C : CAuto A 4 2) {k B : ℕ} (hB : 1 ≤ B) (X Y : List (List (Fin (A + 4))))
    (hXY : X.length = Y.length) (hX : ∀ r ∈ X, r.length = k + B)
    (hY : ∀ r ∈ Y, r.length = k + B)
    (hgood : codeRecs X (idxCode C L len rsrc) 0 = codeRecs Y (idxCode C L len rsrc) 0)
    (hbad : RadixSort.sort (fun rec j => symBit (rec.getD j 0)) k
        (codeRecs X (idxCode C L len rsrc) 1) = codeRecs Y (idxCode C L len rsrc) 1)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = X.flatten)
    (hgR : S.R gR = []) (hbR : S.R bR = []) (hg : S.R g = []) (hb : S.R b = [])
    (hctr : (S.R ctrKB).length = k + B) (hctrB : (S.R ctrB).length = B)
    (hctrK : (S.R ctrK).length = k) (hcnt : (S.R cnt).length = X.length) (htmp : S.R tmp = [])
    (hI : IdxState cf len L rs us rsrc S.R 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ X.length * (16 * (k + B) + 12 * L + 8 * (∑ f, len f) + 8 * nf + 39) +
        k * ((codeRecs X (idxCode C L len rsrc) 1).length * (12 * k + 6 * B + 13)) +
        10 * k + 8 * (∑ f, len f) + 8 * nf + 18 ∧
      Exec body (repairAt src gR bR g b ctrKB ctrB ctrK cnt tmp st cf rs us C) (mk v S) m
        (mk v' { S with R := (Function.update S.R src (Y.map (·.drop k)).flatten) }) := by
  -- register facts
  have hregs := h.regs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hregs
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩,
    ⟨c1, c2, c3, c4, c5, c6, c7⟩, ⟨d1, d2, d3, d4, d5, d6⟩, ⟨e1, e2, e3, e4, e5⟩,
    ⟨f1, f2, f3, f4⟩, ⟨g1, g2, g3⟩, ⟨h1, h2⟩, i1⟩ := hregs
  have hcf : ∀ f, cf f ≠ src ∧ cf f ≠ gR ∧ cf f ≠ bR ∧ cf f ≠ g ∧ cf f ≠ b ∧ cf f ≠ ctrKB ∧
      cf f ≠ ctrB ∧ cf f ≠ ctrK ∧ cf f ≠ cnt ∧ cf f ≠ tmp := fun f => by
    have := h.cf_regs f
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this
  have hus : ∀ r, us r ≠ src ∧ us r ≠ gR ∧ us r ≠ bR ∧ us r ≠ g ∧ us r ≠ b ∧ us r ≠ ctrKB ∧
      us r ≠ ctrB ∧ us r ≠ ctrK ∧ us r ≠ cnt ∧ us r ≠ tmp := fun r => by
    have := h.us_regs r
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this
  have hcfinj : Function.Injective cf := h.route.cf_inj
  have hcftmp : ∀ f, cf f ≠ tmp := fun f => (hcf f).2.2.2.2.2.2.2.2.2
  set code := idxCode C L len rsrc with hcode
  set Xg := codeRecs X code 0 with hXg
  set Xb := codeRecs X code 1 with hXb
  have hXl : X.flatten.length = X.length * (k + B) := length_flatten_of_length X hX
  have hYl : Y.flatten.length = X.length * (k + B) := by
    rw [hXY]; exact length_flatten_of_length Y hY
  have hblkX : ∀ d, blocksIdx X.flatten (k + B) X.length code 0 d =
      (codeRecs X code d).flatten := fun d => blocksIdx_flatten X (k + B) hX code d
  have hblkY : ∀ d, blocksIdx Y.flatten (k + B) X.length code 0 d =
      (codeRecs Y code d).flatten := by
    intro d; rw [hXY]; exact blocksIdx_flatten Y (k + B) hY code d
  -- the registers that are never written
  let Oth : Fin T → Prop := fun x =>
    x ≠ src ∧ x ≠ gR ∧ x ≠ bR ∧ x ≠ g ∧ x ≠ b ∧ ∀ f, cf f ≠ x
  -- stage 1: route
  obtain ⟨v₁, R₁, hu₁, he₁, hsrc₁, hdst₁, hcf₁, hoth₁⟩ := routeIdx_exec body src ![gR, bR] ctrKB
    tmp cf len L rs us rsrc st C h.route
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]; exact ⟨⟨a5, a9⟩, f4⟩)
    (by intro d; fin_cases d <;> simp [Ne.symm a1, b4, b8, Ne.symm a2, c3, c7])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Ne.symm b1])
    (l := X.flatten) (c := S.R ctrKB) (nb := X.length) (B := k + B) (i₀ := 0) (by omega) hXl
    hctr v S
    hsrc rfl htmp hI
  have hR₁ : ∀ x, Oth x → R₁ x = S.R x := fun x hx =>
    hoth₁ x hx.1 (fun d => by fin_cases d <;> simp [Ne.symm hx.2.1, Ne.symm hx.2.2.1]) hx.2.2.2.2.2
  have hR₁gR : R₁ gR = Xg.flatten.reverse := by
    have := hdst₁ 0; simp only [Matrix.cons_val_zero] at this; rw [this, hgR, hblkX]; simp [Xg]
  have hR₁bR : R₁ bR = Xb.flatten.reverse := by
    have := hdst₁ 1; simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    rw [this, hbR, hblkX]; simp [Xb]
  have hR₁g : R₁ g = [] := by
    rw [hoth₁ g (Ne.symm a3) (fun d => by fin_cases d <;> simp [b2, c1]) (fun f => (hcf f).2.2.2.1),
      hg]
  have hR₁b : R₁ b = [] := by
    rw [hoth₁ b (Ne.symm a4) (fun d => by fin_cases d <;> simp [b3,
        c2]) (fun f => (hcf f).2.2.2.2.1),
      hb]
  -- stage 2, 3: restore forward order
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body gR g b2 id v₁ { S with R := R₁ }
  set R₂ := movedR R₁ gR g id (R₁ gR) with hR₂
  have hR₂f : ∀ x, x ≠ gR → x ≠ g → R₂ x = R₁ x := fun x h1 h2 => by
    simp [hR₂, movedR, h1, h2]
  have hR₂g : R₂ g = Xg.flatten := by simp [hR₂, movedR, hR₁gR, hR₁g]
  have hR₂gR : R₂ gR = [] := by simp [hR₂, movedR, b2]
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body bR b c2 id v₂ { S with R := R₂ }
  set R₃ := movedR R₂ bR b id (R₂ bR) with hR₃
  have hR₃f : ∀ x, x ≠ bR → x ≠ b → R₃ x = R₂ x := fun x h1 h2 => by
    simp [hR₃, movedR, h1, h2]
  have hR₂bR : R₂ bR = Xb.flatten.reverse := by rw [hR₂f _ (Ne.symm b1) c1, hR₁bR]
  have hR₂b : R₂ b = [] := by rw [hR₂f _ (Ne.symm b3) (Ne.symm d1), hR₁b]
  have hR₃b : R₃ b = Xb.flatten := by simp [hR₃, movedR, hR₂bR, hR₂b]
  have hR₃bR : R₃ bR = [] := by simp [hR₃, movedR, c2]
  -- stage 4: reset
  obtain ⟨v₄, R₄, hu₄, he₄, hcf₄, hoth₄⟩ := resetFields_exec body cf hcfinj tmp hcftmp len v₃
    { S with R := R₃ }
    (by
      show R₃ tmp = []
      rw [hR₃f _ (Ne.symm c7) (Ne.symm e5), hR₂f _ (Ne.symm b8) (Ne.symm d6),
        hR₁ _ ⟨Ne.symm a9, Ne.symm b8, Ne.symm c7, Ne.symm d6, Ne.symm e5, hcftmp⟩, htmp])
    (fun f => by
      show (R₃ (cf f)).length = _
      rw [hR₃f _ (hcf f).2.2.1 (hcf f).2.2.2.2.1, hR₂f _ (hcf f).2.1 (hcf f).2.2.2.1, hcf₁ f]
      simp)
  have hR₄f : ∀ x, (∀ f, x ≠ cf f) → R₄ x = R₃ x := hoth₄
  -- the registers outside the stream registers
  have hO₄ : ∀ x, Oth x → R₄ x = S.R x := fun x hx => by
    rw [hR₄f x (fun f e => hx.2.2.2.2.2 f e.symm), hR₃f x hx.2.2.1 hx.2.2.2.2.1,
      hR₂f x hx.2.1 hx.2.2.2.1, hR₁ x hx]
  have hOus : ∀ r, Oth (us r) := fun r =>
    ⟨(hus r).1, (hus r).2.1, (hus r).2.2.1, (hus r).2.2.2.1, (hus r).2.2.2.2.1,
      fun f e => h.route.tmps_cf r f e.symm⟩
  have hOctr : Oth ctrKB := ⟨Ne.symm a5, Ne.symm b4, Ne.symm c3, Ne.symm d2, Ne.symm e1,
    fun f => (hcf f).2.2.2.2.2.1⟩
  have hOctrB : Oth ctrB := ⟨Ne.symm a6, Ne.symm b5, Ne.symm c4, Ne.symm d3, Ne.symm e2,
    fun f => (hcf f).2.2.2.2.2.2.1⟩
  have hOctrK : Oth ctrK := ⟨Ne.symm a7, Ne.symm b6, Ne.symm c5, Ne.symm d4, Ne.symm e3,
    fun f => (hcf f).2.2.2.2.2.2.2.1⟩
  have hOcnt : Oth cnt := ⟨Ne.symm a8, Ne.symm b7, Ne.symm c6, Ne.symm d5, Ne.symm e4,
    fun f => (hcf f).2.2.2.2.2.2.2.2.1⟩
  have hOtmp : Oth tmp := ⟨Ne.symm a9, Ne.symm b8, Ne.symm c7, Ne.symm d6, Ne.symm e5, hcftmp⟩
  have hR₄gR : R₄ gR = [] := by
    rw [hR₄f _ (fun f e => (hcf f).2.1 e.symm), hR₃f _ b1 b3, hR₂gR]
  have hR₄g : R₄ g = Xg.flatten := by
    rw [hR₄f _ (fun f e => (hcf f).2.2.2.1 e.symm), hR₃f _ (Ne.symm c1) d1, hR₂g]
  have hR₄b : R₄ b = Xb.flatten := by rw [hR₄f _ (fun f e => (hcf f).2.2.2.2.1 e.symm), hR₃b]
  have hR₄bR : R₄ bR = [] := by rw [hR₄f _ (fun f e => (hcf f).2.2.1 e.symm), hR₃bR]
  -- stage 5: radix sort
  have hus' := h.route.tmps_inj
  obtain ⟨v₅, m₅, hu₅, hm₅, he₅⟩ := radixSort_exec body b ctrKB (us 0) (us 1) (us 2) (us 3) gR bR
    st ctrK
    (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      refine ⟨⟨e1, fun e => (hus 0).2.2.2.2.1 e.symm, fun e => (hus 1).2.2.2.2.1 e.symm,
        fun e => (hus 2).2.2.2.2.1 e.symm, fun e => (hus 3).2.2.2.2.1 e.symm, Ne.symm b3,
        Ne.symm c2, e3⟩, ⟨fun e => (hus 0).2.2.2.2.2.1 e.symm, fun e => (hus 1).2.2.2.2.2.1 e.symm,
        fun e => (hus 2).2.2.2.2.2.1 e.symm, fun e => (hus 3).2.2.2.2.2.1 e.symm, Ne.symm b4,
        Ne.symm c3, f2⟩, ⟨fun e => by have := hus' e; simp at this,
        fun e => by have := hus' e; simp at this, fun e => by have := hus' e; simp at this,
        (hus 0).2.1, (hus 0).2.2.1, (hus 0).2.2.2.2.2.2.2.1⟩,
        ⟨fun e => by have := hus' e; simp at this, fun e => by have := hus' e; simp at this,
        (hus 1).2.1, (hus 1).2.2.1, (hus 1).2.2.2.2.2.2.2.1⟩,
        ⟨fun e => by have := hus' e; simp at this, (hus 2).2.1, (hus 2).2.2.1,
        (hus 2).2.2.2.2.2.2.2.1⟩, ⟨(hus 3).2.1, (hus 3).2.2.1, (hus 3).2.2.2.2.2.2.2.1⟩,
        ⟨b1, b6⟩, c5⟩)
    (recs := Xb) (B := k + B) (K := k) (K' := k) (by omega) le_rfl
    (fun r hr => hX r (mem_codeRecs hr)) v₄ { S with R := R₄ } hR₄b
    (by show (R₄ ctrK).length = k; rw [hO₄ _ hOctrK, hctrK])
    (by show (R₄ ctrKB).length = k + B; rw [hO₄ _ hOctr, hctr])
    (by show R₄ (us 0) = []; rw [hO₄ _ (hOus 0), hI.2.2 0])
    (by show R₄ (us 1) = []; rw [hO₄ _ (hOus 1), hI.2.2 1])
    (by show R₄ (us 2) = []; rw [hO₄ _ (hOus 2), hI.2.2 2])
    (by show R₄ (us 3) = []; rw [hO₄ _ (hOus 3), hI.2.2 3])
    hR₄gR hR₄bR
  rw [hbad] at he₅
  set R₅ := Function.update R₄ b (codeRecs Y code 1).flatten with hR₅
  have hR₅f : ∀ x, x ≠ b → R₅ x = R₄ x := fun x hx => Function.update_of_ne hx _ _
  have hOrs : ∀ r p, rsrc r = .inr p → Oth (rs r) := fun r p hr =>
    ⟨fun e => h.route.rs_X r (Or.inl e),
      fun e => h.merge.rs_X r (Or.inl e),
      fun e => h.merge.rs_X r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))),
      fun e => h.merge.rs_X r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨0, e.symm⟩))))),
      fun e => h.merge.rs_X r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1, e.symm⟩))))),
      fun f e => h.route.param r p f hr e.symm⟩
  have hdig0 : ∀ f, digit len f 0 = 0 := fun f => by simp [digit]
  have hI₅ : IdxState cf len L rs us rsrc R₅ 0 :=
    ⟨fun f => by
        rw [hR₅f _ (hcf f).2.2.2.2.1, hcf₄ f, hdig0],
      fun r p hr => by
        rw [hR₅f _ (hOrs r p hr).2.2.2.2.1, hO₄ _ (hOrs r p hr), hI.2.1 r p hr],
      fun r => by
        rw [hR₅f _ (hOus r).2.2.2.2.1, hO₄ _ (hOus r), hI.2.2 r]⟩
  -- stage 6: merge
  obtain ⟨v₆, R₆, hu₆, he₆, hgR₆, hsrcs₆, hcf₆, hoth₆⟩ := mergeIdx_exec_blocks body ![g, b] gR
    ctrKB tmp cnt bR cf len L rs us rsrc st C h.merge
    (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨b4, b8, b7, b1⟩, ⟨f4, f3, Ne.symm c3⟩, ⟨Ne.symm i1, Ne.symm c7⟩, Ne.symm c6⟩)
    (by
      intro d
      fin_cases d
      · simp [Ne.symm b2, d2, d6, d5, Ne.symm c1]
      · simp [Ne.symm b3, e1, e5, e4, Ne.symm c2])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Ne.symm d1])
    (l := Y.flatten) (c := S.R ctrKB) (kk := S.R cnt) (nb := X.length) (B := k + B) (i₀ := 0)
    hYl hctr hcnt (fun _ => []) v₅ { S with R := R₅ }
    (by
      intro d
      fin_cases d
      · show R₅ g = blocksIdx Y.flatten (k + B) X.length code 0 0 ++ []
        rw [hR₅f _ d1, hR₄g, hblkY 0, List.append_nil, ← hgood]
      · show R₅ b = blocksIdx Y.flatten (k + B) X.length code 0 1 ++ []
        rw [hR₅, Function.update_self, hblkY 1, List.append_nil])
    (by show R₅ ctrKB = _; rw [hR₅f _ (Ne.symm e1), hO₄ _ hOctr])
    (by show R₅ tmp = _; rw [hR₅f _ (Ne.symm e5), hO₄ _ hOtmp, htmp])
    (by show R₅ cnt = _; rw [hR₅f _ (Ne.symm e4), hO₄ _ hOcnt])
    (by show R₅ bR = _; rw [hR₅f _ c2, hR₄bR])
    hI₅
  have hR₆f : ∀ x, x ≠ gR → x ≠ g → x ≠ b → (∀ f, cf f ≠ x) → R₆ x = R₅ x :=
    fun x h1 h2 h3 h4 => hoth₆ x h1 (fun d => by fin_cases d <;> simp [Ne.symm h2, Ne.symm h3]) h4
  have hR₆gR : R₆ gR = Y.flatten.reverse := by
    rw [hgR₆]
    show Y.flatten.reverse ++ R₅ gR = _
    rw [hR₅f _ b3, hR₄gR, List.append_nil]
  -- stage 7: reset
  obtain ⟨v₇, R₇, hu₇, he₇, hcf₇, hoth₇⟩ := resetFields_exec body cf hcfinj tmp hcftmp len v₆
    { S with R := R₆ }
    (by
      show R₆ tmp = []
      rw [hR₆f _ (Ne.symm b8) (Ne.symm d6) (Ne.symm e5) (fun f => hcftmp f), hR₅f _ (Ne.symm e5),
        hO₄ _ hOtmp, htmp])
    (fun f => by show (R₆ (cf f)).length = _; rw [hcf₆ f]; simp)
  have hR₇f : ∀ x, (∀ f, x ≠ cf f) → R₇ x = R₆ x := hoth₇
  have hO₇ : ∀ x, Oth x → R₇ x = S.R x := fun x hx => by
    rw [hR₇f x (fun f e => hx.2.2.2.2.2 f e.symm),
      hR₆f x hx.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2, hR₅f x hx.2.2.2.2.1, hO₄ x hx]
  have hR₇gR : R₇ gR = Y.flatten.reverse := by
    rw [hR₇f _ (fun f e => (hcf f).2.1 e.symm), hR₆gR]
  have hR₇src : R₇ src = [] := by
    rw [hR₇f _ (fun f e => (hcf f).1 e.symm), hR₆f _ a1 a3 a4 (fun f => (hcf f).1),
      hR₅f _ a4, hR₄f _ (fun f e => (hcf f).1 e.symm), hR₃f _ a2 a4, hR₂f _ a1 a3, hsrc₁]
  -- stage 8: strip
  obtain ⟨v₈, hu₈, he₈⟩ := stripPass_exec body gR src ctrB ctrK tmp st
    (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨Ne.symm a1, b5, b6, b8⟩, ⟨a6, a7, a9⟩, ⟨g1, g3⟩, h2⟩)
    hB Y hY v₇ { S with R := R₇ } hR₇gR
    (by show (R₇ ctrB).length = B; rw [hO₇ _ hOctrB, hctrB])
    (by show (R₇ ctrK).length = k; rw [hO₇ _ hOctrK, hctrK])
    (by show R₇ tmp = []; rw [hO₇ _ hOtmp, htmp])
  refine ⟨v₈, _, by rw [hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆
      (Exec.seq he₇ he₈))))))) rfl ?_⟩
  · simp only [hR₁gR, hR₂bR, List.length_reverse]
    rw [length_codeRecs_flatten X _ hX, length_codeRecs_flatten X _ hX, ← hXY]
    have hg' := Nat.mul_le_mul_right (k + B) (length_codeRecs X code 0)
    have hb' := Nat.mul_le_mul_right (k + B) (length_codeRecs X code 1)
    nlinarith [hg', hb', hm₅]
  · congr 2
    funext x
    show Function.update (Function.update R₇ gR []) src
      ((Y.map (·.drop k)).flatten ++ R₇ src) x = _
    rw [hR₇src, List.append_nil]
    by_cases hx : x = src
    · subst hx; simp
    rw [Function.update_of_ne hx, Function.update_of_ne hx]
    by_cases hxg : x = gR
    · subst hxg; rw [Function.update_self, hgR]
    rw [Function.update_of_ne hxg]
    by_cases hxf : ∃ f, x = cf f
    · obtain ⟨f, rfl⟩ := hxf
      rw [hcf₇ f, hI.1 f, hdig0]
    simp only [not_exists] at hxf
    rw [hR₇f x hxf]
    by_cases hxg' : x = g
    · subst hxg'
      have := hsrcs₆ 0
      simp only [Matrix.cons_val_zero] at this
      rw [this, hg]
    by_cases hxb : x = b
    · subst hxb
      have := hsrcs₆ 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
      rw [this, hb]
    rw [hR₆f x hxg hxg' hxb (fun f e => hxf f e.symm), hR₅f x hxb]
    by_cases hxbR : x = bR
    · subst hxbR; rw [hR₄bR, hbR]
    exact hO₄ x ⟨hx, hxg, hxbR, hxg', hxb, fun f e => hxf f e.symm⟩

end RepairMachine

/-! ### The repair on the rectangle: list semantics -/

section RepairLists

open IntegerMultBounds.Compact IntegerMultBounds.Machine.Partition

lemma getD_moveRecs {α : Type} {M : ℕ} (π : Equiv.Perm (Fin M)) (l : List (List α)) (j : Fin M) :
    (moveRecs π l).getD j [] = l.getD (π.symm j) [] := by
  rw [List.getD_eq_getElem _ _ (by simp [length_moveRecs])]
  simp [moveRecs]

lemma getD_keyRecs {A M : ℕ} (k : ℕ) (π : Equiv.Perm (Fin M)) (l : List (List (Fin (A + 4))))
    (j : Fin M) : (keyRecs k π l).getD j [] = binSyms k (π j) ++ l.getD j [] := by
  rw [List.getD_eq_getElem _ _ (by simp [keyRecs])]
  simp [keyRecs]

lemma length_keyRecs {A M : ℕ} (k : ℕ) (π : Equiv.Perm (Fin M)) (l : List (List (Fin (A + 4)))) :
    (keyRecs k π l).length = M := by simp [keyRecs]

/-- Every keyed record has `k + B` symbols. -/
lemma keyRecs_length_mem {A M : ℕ} (k B : ℕ) (π : Equiv.Perm (Fin M))
    (l : List (List (Fin (A + 4)))) (hl : l.length = M) (hlB : ∀ r ∈ l, r.length = B) :
    ∀ r ∈ keyRecs k π l, r.length = k + B := by
  intro r hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hr
  have hj : (j : ℕ) < l.length := by rw [hl]; exact j.isLt
  rw [List.length_append, length_binSyms, List.getD_eq_getElem _ _ hj,
    hlB _ (List.getElem_mem hj)]

lemma moveRecs_length_mem {α : Type} {M W : ℕ} (π : Equiv.Perm (Fin M)) (l : List (List α))
    (hl : l.length = M) (hW : ∀ r ∈ l, r.length = W) : ∀ r ∈ moveRecs π l, r.length = W := by
  intro r hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hr
  have hj : ((π.symm j : Fin M) : ℕ) < l.length := by rw [hl]; exact (π.symm j).isLt
  rw [List.getD_eq_getElem _ _ hj]
  exact hW _ (List.getElem_mem hj)

/-- Stripping the keys of the moved keyed records. -/
lemma map_drop_moveRecs_keyRecs {A M : ℕ} (k : ℕ) (π π' : Equiv.Perm (Fin M))
    (l : List (List (Fin (A + 4)))) :
    (moveRecs π' (keyRecs k π l)).map (·.drop k) = moveRecs π' l := by
  unfold moveRecs
  rw [List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply]
  rw [getD_keyRecs]
  simp

/-- A stable radix sort commutes with a map that carries the key bits. -/
lemma sort_map {α β : Type} (bit : α → ℕ → Bool) (bit' : β → ℕ → Bool) (G : β → α) (k : ℕ)
    (h : ∀ x j, j < k → bit (G x) j = bit' x j) (xs : List β) :
    RadixSort.sort bit k (xs.map G) = (RadixSort.sort bit' k xs).map G := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [RadixSort.sort, RadixSort.sort, ih (fun x j hj => h x j (by omega))]
      simp only [RadixSort.pass, List.filter_map, List.map_append]
      congr 2 <;> apply List.filter_congr <;> intro x _ <;> simp [h x k (by omega)]

variable {A : ℕ} {N₀ N₁ N₂ N₃ L n₀ n₁ n₂ n₃ rb R : ℕ}

/-- The code-pass sources of the exceptional-set code: the field of `y`, the field of `z`, the
marker mask `selMask K ρ (f - 1)` and the guard mask. -/
def badSrc (σ : Equiv.Perm (Fin 3)) (K ρ f L : ℕ) : Fin 4 → Fin 8 ⊕ ℕ :=
  ![.inl (slotF (σ.symm 1)), .inl (slotF (σ.symm 2)), .inr (selMask K ρ (f - 1)),
    .inr (guardMask K ρ (f - 1) L)]

/-- The index code of the exceptional set is `Bad` (margin `1`). -/
lemma idxCode_bad (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (hA : 14 ≤ A) {K ρ f : ℕ} (hρ : ρ < K)
    (hL : L = f * K) (hf : 1 ≤ f) (σ : Equiv.Perm (Fin 3)) (a : Addr N₀ N₁ N₂ N₃ L) :
    idxCode (badAuto A) L (idxLen n₀ n₁ n₂ n₃ L rb) (badSrc σ K ρ f L)
        (enc N₀ N₁ N₂ N₃ L σ a) =
      if Bad N₀ N₁ N₂ N₃ L K ρ f 1 a then 1 else 0 := by
  have hvals : regVal (idxLen n₀ n₁ n₂ n₃ L rb) (badSrc σ K ρ f L) (enc N₀ N₁ N₂ N₃ L σ a) =
      ![((a.2 1 : Fin (2 ^ L)) : ℕ), ((a.2 2 : Fin (2 ^ L)) : ℕ), selMask K ρ (f - 1),
        guardMask K ρ (f - 1) L] := by
    funext r
    fin_cases r <;>
      simp [regVal, badSrc, digit_enc_name hN₀ hR hN₁ hN₂ hN₃]
  have hL' : L = (f - 1 + 1) * K := by rw [Nat.sub_add_cancel hf, hL]
  have he := badAuto_eval K ρ (f - 1) hA hρ ((a.2 1 : Fin (2 ^ L)) : ℕ) ((a.2 2 : Fin (2 ^ L)) : ℕ)
  rw [← hL'] at he
  unfold idxCode
  rw [hvals, he]
  have hiff : (∃ i < f - 1, ¬ (GuardOK K ρ 1 ((a.2 1 : Fin (2 ^ L)) : ℕ) i ∧
      GuardOK K ρ 1 ((a.2 2 : Fin (2 ^ L)) : ℕ) i)) ↔ Bad N₀ N₁ N₂ N₃ L K ρ f 1 a := by
    simp only [Bad, Good, not_forall, exists_prop]
  by_cases hb : Bad N₀ N₁ N₂ N₃ L K ρ f 1 a
  · simp only [hb, hiff.2 hb, ↓reduceIte]
  · simp only [hb, mt hiff.1 hb, ↓reduceIte]

lemma rankPerm_symm_enc (K ρ f : ℕ) (σ : Equiv.Perm (Fin 3)) (b : Addr N₀ N₁ N₂ N₃ L) :
    (rankPerm N₀ N₁ N₂ N₃ L K ρ (f - 1) (prog σ)).symm (enc N₀ N₁ N₂ N₃ L σ b) =
      enc N₀ N₁ N₂ N₃ L σ ((liftA N₀ N₁ N₂ N₃ L (packedS L K ρ f)).symm b) := by
  rw [Equiv.symm_apply_eq, rankPerm_prog, Equiv.apply_symm_apply]

lemma addrPerm_symm_enc (σ : Equiv.Perm (Fin 3)) (Pm : Equiv.Perm (Tri L))
    (b : Addr N₀ N₁ N₂ N₃ L) :
    (addrPerm N₀ N₁ N₂ N₃ L σ Pm).symm (enc N₀ N₁ N₂ N₃ L σ b) =
      enc N₀ N₁ N₂ N₃ L σ ((liftA N₀ N₁ N₂ N₃ L Pm).symm b) := by
  rw [Equiv.symm_apply_eq, addrPerm_enc, Equiv.apply_symm_apply]

/-- The code-`1` records of a stream of `M` records are its records at the exceptional ranks. -/
lemma codeRecs_bad (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (hA : 14 ≤ A) {K ρ f : ℕ} (hρ : ρ < K)
    (hL : L = f * K) (hf : 1 ≤ f) (σ : Equiv.Perm (Fin 3)) (Z : List (List (Fin (A + 4))))
    (hZ : Z.length = rectSize N₀ N₁ N₂ N₃ L) :
    codeRecs Z (idxCode (badAuto A) L (idxLen n₀ n₁ n₂ n₃ L rb) (badSrc σ K ρ f L)) 1 =
      (badRanks (enc N₀ N₁ N₂ N₃ L σ) (Bad N₀ N₁ N₂ N₃ L K ρ f 1)).map
        fun (i : Fin (rectSize N₀ N₁ N₂ N₃ L)) => Z.getD (i : ℕ) [] := by
  unfold codeRecs badRanks
  rw [hZ, ← List.map_coe_finRange_eq_range, List.filter_map, List.map_map]
  refine congrArg (List.map _) (List.filter_congr fun i _ => ?_)
  obtain ⟨a, rfl⟩ := (enc N₀ N₁ N₂ N₃ L σ).surjective i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [idxCode_bad hN₀ hR hN₁ hN₂ hN₃ hA hρ hL hf σ a]
  by_cases hb : Bad N₀ N₁ N₂ N₃ L K ρ f 1 a <;> simp [hb]

/-- **Good records.** Off the exceptional ranks, the stream after the packed program already
holds the records of the ideal map. -/
theorem repair_good (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (hA : 14 ≤ A) {K ρ f : ℕ} (hρ : ρ < K)
    (hL : L = f * K) (hf : 1 ≤ f) (σ : Equiv.Perm (Fin 3)) (k : ℕ)
    (l : List (List (Fin (A + 4)))) :
    codeRecs (moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ (f - 1) (prog σ))
        (keyRecs k (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f)) l))
        (idxCode (badAuto A) L (idxLen n₀ n₁ n₂ n₃ L rb) (badSrc σ K ρ f L)) 0 =
      codeRecs (moveRecs (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f))
        (keyRecs k (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f)) l))
        (idxCode (badAuto A) L (idxLen n₀ n₁ n₂ n₃ L rb) (badSrc σ K ρ f L)) 0 := by
  unfold codeRecs
  rw [length_moveRecs, length_moveRecs]
  refine List.map_congr_left fun n hn => ?_
  have hnM : n < rectSize N₀ N₁ N₂ N₃ L := List.mem_range.1 (List.mem_filter.1 hn).1
  have hc := (List.mem_filter.1 hn).2
  obtain ⟨b, hb⟩ := (enc N₀ N₁ N₂ N₃ L σ).surjective ⟨n, hnM⟩
  have hn : n = (enc N₀ N₁ N₂ N₃ L σ b : ℕ) := by rw [hb]
  rw [hn, idxCode_bad hN₀ hR hN₁ hN₂ hN₃ hA hρ hL hf σ b] at hc
  have hnb : ¬ Bad N₀ N₁ N₂ N₃ L K ρ f 1 b := by
    intro h; simp [h] at hc
  rw [hn, getD_moveRecs, getD_moveRecs, rankPerm_symm_enc, addrPerm_symm_enc,
    inverse_agrees_off_bad _ _ _ (idealT_preserves_bad N₀ N₁ N₂ N₃ L K ρ f 1 (by omega))
      (packed_agrees N₀ N₁ N₂ N₃ L K ρ f 1 hρ hL hf le_rfl) b hnb]

/-- **Exceptional records.** At the exceptional ranks, the records of the stream after the packed
program, radix sorted on their `k` key bits, are the records of the ideal map, in rank order
(from the vendored `sortedExtracted_eq`). -/
theorem repair_bad (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (hA : 14 ≤ A) {K ρ f : ℕ} (hρ : ρ < K)
    (hL : L = f * K) (hf : 1 ≤ f) (σ : Equiv.Perm (Fin 3)) (k : ℕ)
    (hk : rectSize N₀ N₁ N₂ N₃ L ≤ 2 ^ k) (l : List (List (Fin (A + 4)))) :
    RadixSort.sort (fun rec j => symBit (rec.getD j 0)) k
        (codeRecs (moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ (f - 1) (prog σ))
          (keyRecs k (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f)) l))
          (idxCode (badAuto A) L (idxLen n₀ n₁ n₂ n₃ L rb) (badSrc σ K ρ f L)) 1) =
      codeRecs (moveRecs (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f))
        (keyRecs k (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f)) l))
        (idxCode (badAuto A) L (idxLen n₀ n₁ n₂ n₃ L rb) (badSrc σ K ρ f L)) 1 := by
  set e := enc N₀ N₁ N₂ N₃ L σ with he
  set Sp := liftA N₀ N₁ N₂ N₃ L (packedS L K ρ f) with hSp
  set Tp := liftA N₀ N₁ N₂ N₃ L (idealT L K ρ f) with hTp
  set bad := Bad N₀ N₁ N₂ N₃ L K ρ f 1 with hbad
  have hT : ∀ x, bad (Tp x) ↔ bad x := idealT_preserves_bad N₀ N₁ N₂ N₃ L K ρ f 1 (by omega)
  have agree : ∀ x, ¬ bad x → Sp x = Tp x := packed_agrees N₀ N₁ N₂ N₃ L K ρ f 1 hρ hL hf le_rfl
  let data : Addr N₀ N₁ N₂ N₃ L → List Bool := fun a => List.replicate (e a) true
  let G : Fin (rectSize N₀ N₁ N₂ N₃ L) × Record → List (Fin (A + 4)) :=
    fun x => binSyms k x.1 ++ l.getD x.2.payload.length []
  have hG : ∀ x j, j < k → symBit ((G x).getD j 0) = keyBit x j := by
    intro x j hj
    simp only [G, keyBit]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega)]
    simp [binSyms]
  have hsort := sortedExtracted_eq e Sp Tp bad hT agree k hk data
  have hXe : codeRecs (moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ (f - 1) (prog σ))
      (keyRecs k (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f)) l))
      (idxCode (badAuto A) L (idxLen n₀ n₁ n₂ n₃ L rb) (badSrc σ K ρ f L)) 1 =
      (extracted e Sp Tp bad data).map G := by
    rw [codeRecs_bad hN₀ hR hN₁ hN₂ hN₃ hA hρ hL hf σ _ (length_moveRecs _ _), extracted,
      List.map_map]
    refine List.map_congr_left fun i _ => ?_
    obtain ⟨a, rfl⟩ := e.surjective i
    simp only [Function.comp_apply, G, data, List.length_replicate]
    rw [getD_moveRecs, rankPerm_symm_enc, getD_keyRecs, addrPerm_enc]
    simp [destRank, he, hSp, hTp]
  have hYe : codeRecs (moveRecs (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f))
      (keyRecs k (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f)) l))
      (idxCode (badAuto A) L (idxLen n₀ n₁ n₂ n₃ L rb) (badSrc σ K ρ f L)) 1 =
      (target e Tp bad data).map G := by
    rw [codeRecs_bad hN₀ hR hN₁ hN₂ hN₃ hA hρ hL hf σ _ (length_moveRecs _ _), target,
      List.map_map]
    refine List.map_congr_left fun i _ => ?_
    obtain ⟨a, rfl⟩ := e.surjective i
    simp only [Function.comp_apply, G, data, List.length_replicate]
    rw [getD_moveRecs, addrPerm_symm_enc, getD_keyRecs, addrPerm_enc]
    simp [he, hTp]
  rw [hXe, hYe, sort_map _ keyBit G k hG, ← hsort]
  rfl

end RepairLists

/-! ### The repair pass on the rectangle -/

section RepairMain

open IntegerMultBounds.Compact

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
  {N₀ N₁ N₂ N₃ L n₀ n₁ n₂ n₃ rb R : ℕ}

/-- Disjointness of four concatenated lists without duplicates. -/
lemma nodup_append4 {α : Type} {l₁ l₂ l₃ l₄ : List α} (h : (l₁ ++ l₂ ++ l₃ ++ l₄).Nodup) :
    l₁.Nodup ∧ l₂.Nodup ∧ l₃.Nodup ∧ l₄.Nodup ∧ (∀ x ∈ l₁, ∀ y ∈ l₂, x ≠ y) ∧
      (∀ x ∈ l₁, ∀ y ∈ l₃, x ≠ y) ∧ (∀ x ∈ l₁, ∀ y ∈ l₄, x ≠ y) ∧
      (∀ x ∈ l₂, ∀ y ∈ l₃, x ≠ y) ∧ (∀ x ∈ l₂, ∀ y ∈ l₄, x ≠ y) ∧
      (∀ x ∈ l₃, ∀ y ∈ l₄, x ≠ y) := by
  rw [List.nodup_append, List.nodup_append, List.nodup_append] at h
  obtain ⟨⟨⟨h1, h2, h12⟩, h3, h123⟩, h4, h1234⟩ := h
  refine ⟨h1, h2, h3, h4, h12, fun x hx y hy => h123 x (List.mem_append_left _ hx) y hy,
    fun x hx y hy => h1234 x (List.mem_append_left _ (List.mem_append_left _ hx)) y hy,
    fun x hx y hy => h123 x (List.mem_append_right _ hx) y hy,
    fun x hx y hy => h1234 x (List.mem_append_left _ (List.mem_append_right _ hx)) y hy,
    fun x hx y hy => h1234 x (List.mem_append_right _ hx) y hy⟩

/-- **The repair pass** for physical order `σ`: `repairAt` with the exceptional-set code read
from the field of `y`, the field of `z`, the marker mask register `mkR` and the guard mask
register `gmR`. -/
def repairPass (σ : Equiv.Perm (Fin 3)) (src gR bR g b ctrKB ctrB ctrK cnt tmp mkR gmR st : Fin T)
    (cf : Fin 8 → Fin T) (us : Fin 4 → Fin T) : Pr P T Q A U :=
  repairAt src gR bR g b ctrKB ctrB ctrK cnt tmp st cf
    ![cf (slotF (σ.symm 1)), cf (slotF (σ.symm 2)), mkR, gmR] us (badAuto A)

/-- **Repair pass.** The register `src` holds the keyed stream after the packed program,
`moveRecs π_S (keyRecs k π_T l)` with `π_S = rankPerm (prog σ)` and
`π_T = addrPerm σ (idealT L K ρ f)`; the field counter `cf` is at index `0`; `mkR` and `gmR` hold
the marker mask `selMask K ρ (f - 1)` and the guard mask; `ctrKB`, `ctrB`, `ctrK`, `cnt` hold
`k + B`, `B`, `k`, `M` symbols; `gR`, `bR`, `g`, `b`, `tmp` and `us` are empty. The pass leaves
`(moveRecs π_T l).flatten` in `src`, the stream of the ideal map `idealT`, and every other
register as it started, in at most `103 M (B + k + 1) + 13 |Bad| k (B + k + 1) + 18 k + 82` steps,
where `|Bad|` is the number of exceptional addresses (margin `1`). -/
theorem repairPass_exec (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (hA : 14 ≤ A) {K ρ f : ℕ} (hρ : ρ < K)
    (hL : L = f * K) (hf : 1 ≤ f) (σ : Equiv.Perm (Fin 3))
    {src gR bR g b ctrKB ctrB ctrK cnt tmp mkR gmR st : Fin T} {cf : Fin 8 → Fin T}
    {us : Fin 4 → Fin T}
    (hreg : ([src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp] ++ [mkR, gmR] ++ List.ofFn us ++
      List.ofFn cf).Nodup)
    (hst : st ∉ [mkR, gmR] ++ List.ofFn us ++ List.ofFn cf) {B : ℕ} (hB : 1 ≤ B)
    (l : List (List (Fin (A + 4)))) (hl : l.length = rectSize N₀ N₁ N₂ N₃ L)
    (hlB : ∀ r ∈ l, r.length = B) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = (moveRecs (rankPerm N₀ N₁ N₂ N₃ L K ρ (f - 1) (prog σ))
      (keyRecs (keyLen n₀ n₁ n₂ n₃ L rb) (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f)) l)).flatten)
    (hgR : S.R gR = []) (hbR : S.R bR = []) (hg : S.R g = []) (hb : S.R b = [])
    (hctr : (S.R ctrKB).length = keyLen n₀ n₁ n₂ n₃ L rb + B) (hctrB : (S.R ctrB).length = B)
    (hctrK : (S.R ctrK).length = keyLen n₀ n₁ n₂ n₃ L rb)
    (hcnt : (S.R cnt).length = rectSize N₀ N₁ N₂ N₃ L) (htmp : S.R tmp = [])
    (hmk : S.R mkR = binSyms L (selMask K ρ (f - 1)))
    (hgm : S.R gmR = binSyms L (guardMask K ρ (f - 1) L)) (hus : ∀ r, S.R (us r) = [])
    (hcf : ∀ j, S.R (cf j) = binSyms (idxLen n₀ n₁ n₂ n₃ L rb j) 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 103 * (rectSize N₀ N₁ N₂ N₃ L * (B + keyLen n₀ n₁ n₂ n₃ L rb + 1)) +
        13 * (Nat.card {a // Bad N₀ N₁ N₂ N₃ L K ρ f 1 a} * keyLen n₀ n₁ n₂ n₃ L rb *
          (B + keyLen n₀ n₁ n₂ n₃ L rb + 1)) + 18 * keyLen n₀ n₁ n₂ n₃ L rb + 82 ∧
      Exec body (repairPass σ src gR bR g b ctrKB ctrB ctrK cnt tmp mkR gmR st cf us) (mk v S) m
        (mk v' { S with R := (Function.update S.R src
          (moveRecs (addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f)) l).flatten) }) := by
  set k := keyLen n₀ n₁ n₂ n₃ L rb with hk
  set M := rectSize N₀ N₁ N₂ N₃ L with hM
  obtain ⟨n10, n2, nus, ncf, d12, d1u, d1c, d2u, d2c, duc⟩ := nodup_append4 hreg
  have husinj : Function.Injective us := List.nodup_ofFn.1 nus
  have hcfinj : Function.Injective cf := List.nodup_ofFn.1 ncf
  have hmkgm : mkR ≠ gmR := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      and_true] at n2
    exact n2.1
  have hus10 : ∀ r, us r ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp] :=
    fun r hr => d1u _ hr _ (List.mem_ofFn.2 ⟨r, rfl⟩) rfl
  have hcf10 : ∀ j, cf j ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp] :=
    fun j hj => d1c _ hj _ (List.mem_ofFn.2 ⟨j, rfl⟩) rfl
  have hmk10 : mkR ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp] :=
    fun h => d12 _ h _ (by simp) rfl
  have hgm10 : gmR ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp] :=
    fun h => d12 _ h _ (by simp) rfl
  have hmkus : ∀ r, mkR ≠ us r := fun r => d2u _ (by simp) _ (List.mem_ofFn.2 ⟨r, rfl⟩)
  have hgmus : ∀ r, gmR ≠ us r := fun r => d2u _ (by simp) _ (List.mem_ofFn.2 ⟨r, rfl⟩)
  have hmkcf : ∀ j, mkR ≠ cf j := fun j => d2c _ (by simp) _ (List.mem_ofFn.2 ⟨j, rfl⟩)
  have hgmcf : ∀ j, gmR ≠ cf j := fun j => d2c _ (by simp) _ (List.mem_ofFn.2 ⟨j, rfl⟩)
  have hucf : ∀ r j, us r ≠ cf j := fun r j =>
    duc _ (List.mem_ofFn.2 ⟨r, rfl⟩) _ (List.mem_ofFn.2 ⟨j, rfl⟩)
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.mem_ofFn] at hst
  obtain ⟨⟨⟨hstmk, hstgm⟩, hstus⟩, hstcf⟩ := hst
  have hyz : slotF (σ.symm 1) ≠ slotF (σ.symm 2) := fun e => by
    have := σ.symm.injective (slotF_injective e)
    exact absurd this (by decide)
  set rs : Fin 4 → Fin T := ![cf (slotF (σ.symm 1)), cf (slotF (σ.symm 2)), mkR, gmR] with hrs
  have hcode : CodeLayout rs us st :=
    { rs_inj := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          first
          | rfl
          | (exfalso; revert hij
             simp [rs, hcfinj.eq_iff, hyz, Ne.symm hyz, hmkcf, hgmcf, Ne.symm (hmkcf _),
               Ne.symm (hgmcf _), hmkgm, Ne.symm hmkgm])
      tmps_inj := husinj
      rs_tmps := by
        intro r r'
        fin_cases r <;> simp [rs, Ne.symm (hucf _ _), hmkus, hgmus]
      rs_st := by
        intro r
        fin_cases r <;> simp [rs]
        · exact fun e => hstcf ⟨_, e⟩
        · exact fun e => hstcf ⟨_, e⟩
        · exact Ne.symm hstmk
        · exact Ne.symm hstgm
      tmps_st := fun r e => hstus ⟨r, e⟩ }
  have hfield : ∀ r j, badSrc σ K ρ f L r = .inl j →
      rs r = cf j ∧ idxLen n₀ n₁ n₂ n₃ L rb j = L := by
    intro r j hr
    fin_cases r <;> simp [badSrc] at hr <;> subst hr <;> simp [rs, idxLen_slotF]
  have hparam : ∀ r p j, badSrc σ K ρ f L r = .inr p → rs r ≠ cf j := by
    intro r p j hr
    fin_cases r <;> simp [badSrc] at hr <;> simp [rs, hmkcf, hgmcf]
  have hrs10 : ∀ r, rs r ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp] := by
    intro r
    fin_cases r
    · exact hcf10 _
    · exact hcf10 _
    · exact hmk10
    · exact hgm10
  have hX : ∀ (Xp : Fin T → Prop),
      (∀ x, Xp x → x ∈ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp]) →
      IdxLayout cf (idxLen n₀ n₁ n₂ n₃ L rb) L rs us (badSrc σ K ρ f L) st Xp := fun Xp hXp =>
    { hcode with
      cf_inj := hcfinj
      tmps_cf := hucf
      field := hfield
      param := hparam
      cf_X := fun j hx => hcf10 j (hXp _ hx)
      rs_X := fun r hx => hrs10 r (hXp _ hx)
      tmps_X := fun r hx => hus10 r (hXp _ hx) }
  have hlay : RepairLayout src gR bR g b ctrKB ctrB ctrK cnt tmp st cf
      (idxLen n₀ n₁ n₂ n₃ L rb) L rs us (badSrc σ K ρ f L) :=
    { route := hX _ (by
        intro x hx
        rcases hx with rfl | rfl | rfl | ⟨d, rfl⟩
        · simp
        · simp
        · simp
        · fin_cases d <;> simp)
      merge := hX _ (by
        intro x hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | ⟨d, rfl⟩
        · simp
        · simp
        · simp
        · simp
        · simp
        · fin_cases d <;> simp)
      regs := n10
      cf_regs := hcf10
      us_regs := hus10 }
  have hIdx : IdxState cf (idxLen n₀ n₁ n₂ n₃ L rb) L rs us (badSrc σ K ρ f L) S.R 0 :=
    ⟨fun j => by rw [hcf j]; simp [digit],
      fun r p hr => by
        fin_cases r <;> simp [badSrc] at hr <;> subst hr
        · exact hmk
        · exact hgm,
      hus⟩
  have hkM : M ≤ 2 ^ k := rectSize_le hN₀ hR hN₁ hN₂ hN₃
  set πT := addrPerm N₀ N₁ N₂ N₃ L σ (idealT L K ρ f) with hπT
  set πS := rankPerm N₀ N₁ N₂ N₃ L K ρ (f - 1) (prog σ) with hπS
  have hKR := keyRecs_length_mem k B πT l hl hlB
  obtain ⟨v', m, hu, hm, he⟩ := repairAt_exec body hlay (badAuto A) hB
    (moveRecs πS (keyRecs k πT l)) (moveRecs πT (keyRecs k πT l))
    (by simp [length_moveRecs])
    (moveRecs_length_mem _ _ (length_keyRecs k πT l) hKR)
    (moveRecs_length_mem _ _ (length_keyRecs k πT l) hKR)
    (repair_good hN₀ hR hN₁ hN₂ hN₃ hA hρ hL hf σ k l)
    (repair_bad hN₀ hR hN₁ hN₂ hN₃ hA hρ hL hf σ k hkM l)
    v S hsrc hgR hbR hg hb hctr hctrB hctrK (by rw [hcnt, length_moveRecs]) htmp hIdx
  rw [map_drop_moveRecs_keyRecs] at he
  refine ⟨v', m, hu, ?_, he⟩
  rw [codeRecs_bad hN₀ hR hN₁ hN₂ hN₃ hA hρ hL hf σ _ (length_moveRecs _ _), List.length_map,
    badRanks_length, length_moveRecs, sum_idxLen] at hm
  have hLk : L ≤ k := by simp only [hk, keyLen]; omega
  set nb := Nat.card {a // Bad N₀ N₁ N₂ N₃ L K ρ f 1 a}
  have h1 : M * (16 * (k + B) + 12 * L + 8 * k + 8 * 8 + 39) ≤ 103 * (M * (B + k + 1)) := by
    have : 16 * (k + B) + 12 * L + 8 * k + 8 * 8 + 39 ≤ 103 * (B + k + 1) := by omega
    nlinarith [Nat.mul_le_mul_left M this]
  have h2 : k * (nb * (12 * k + 6 * B + 13)) ≤ 13 * (nb * k * (B + k + 1)) := by
    have : 12 * k + 6 * B + 13 ≤ 13 * (B + k + 1) := by omega
    nlinarith [Nat.mul_le_mul_left (k * nb) this]
  rw [← hM, ← hk] at hm
  rw [← hM]
  omega

end RepairMain

end IntegerMultBounds.MathlibTM2.Node
