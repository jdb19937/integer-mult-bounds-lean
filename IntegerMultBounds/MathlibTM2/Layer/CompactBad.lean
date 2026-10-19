module

public import IntegerMultBounds.MathlibTM2.Layer.CompactOffsets

/-!
# The code of the bad states of the compact gadget

A state is bad (`¬ Good`) when, for some used segment `c`, digit `c` of `t` or of `u` is all
ones, or the bits `posS c + 1 + G, …, posS c + K - 1` of `y` are all ones (the guard of segment `c`
reaches `2^(K-1) - 2^G`).

`badC` reads four registers of slot width, least significant bit first: `y`, the bits of `u` and
of `t` spread to the positions `posA` (digit `c` of a compact field lands at bits
`posS c + 1, …, posS c + G`), and the phase mask `mkV` with set bits at `posS c` (`c ≤ n`),
`posS c + 1` and `posS c + 1 + G` (`c < n`). Each set bit of the mask starts the next phase:
`p0` (the selected bit), `p1` (the digit window, testing `t` and `u` for all ones), `p2` (the guard
window, testing `y`). Leaving a window whose test holds enters the absorbing state `bad`.
`badC_eval`: the code is `0` on good states and `1` on bad ones.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.CompactGadget

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactMasks
  IntegerMultBounds.MathlibTM2.Host Finset

/-! ### The automaton -/

/-- The phases of the bad-state automaton. -/
inductive BS where
  | p0
  | p1 (rt ru : Bool)
  | p2 (ry : Bool)
  | bad
  deriving DecidableEq

/-- One column `(y, u, t, mark)`. -/
def bstep : BS → (Fin 4 → Bool) → BS
  | .bad, _ => .bad
  | .p0, c => if c 3 then .p1 (c 2) (c 1) else .p0
  | .p1 rt ru, c => if c 3 then (if rt || ru then .bad else .p2 (c 0)) else .p1 (rt && c 2) (ru && c 1)
  | .p2 ry, c => if c 3 then (if ry then .bad else .p0) else .p2 (ry && c 0)

/-- The symbol code of a phase. -/
def BS.code : BS → ℕ
  | .p0 => 0
  | .p1 rt ru => 1 + 2 * rt.toNat + ru.toNat
  | .p2 ry => 5 + ry.toNat
  | .bad => 7

/-- The phase of a symbol code. -/
def BS.ofCode : ℕ → BS
  | 0 => .p0
  | 1 => .p1 false false
  | 2 => .p1 false true
  | 3 => .p1 true false
  | 4 => .p1 true true
  | 5 => .p2 false
  | 6 => .p2 true
  | _ => .bad

lemma BS.ofCode_code (s : BS) : BS.ofCode s.code = s := by
  rcases s with _ | ⟨_ | _, _ | _⟩ | (_ | _) | _ <;> rfl

lemma BS.code_lt (s : BS) : s.code < 8 := by
  rcases s with _ | ⟨_ | _, _ | _⟩ | (_ | _) | _ <;> decide

/-- The bad-state automaton. -/
def badC (A : ℕ) (hA : 4 ≤ A) : CAuto A 4 2 where
  init := ⟨(BS.p2 false).code, by have := (BS.p2 false).code_lt; omega⟩
  step s col := ⟨(bstep (BS.ofCode s.val) col).code, by
    have := (bstep (BS.ofCode s.val) col).code_lt; omega⟩
  out s := if BS.ofCode s.val = .bad then 1 else 0

section Fold

variable (col : ℕ → Fin 4 → Bool)

/-- The phase after the columns `l`. -/
def bfold (l : List ℕ) (s : BS) : BS := l.foldl (fun s q => bstep s (col q)) s

lemma badC_run {A : ℕ} (hA : 4 ≤ A) (l : List ℕ) (s : BS) :
    BS.ofCode (l.foldl (fun x q => (badC A hA).step x (col q))
      ⟨s.code, by have := s.code_lt; omega⟩).val = bfold col l s := by
  induction l generalizing s with
  | nil => exact BS.ofCode_code s
  | cons q l ih =>
    simp only [bfold] at ih ⊢
    simp only [List.foldl_cons]
    rw [← ih]
    simp only [badC, BS.ofCode_code]

lemma bfold_bad (l : List ℕ) : bfold col l .bad = .bad := by
  induction l with
  | nil => rfl
  | cons q l ih => simpa [bfold, bstep] using ih

variable {col}

lemma bfold_p0 {l : List ℕ} (h : ∀ q ∈ l, col q 3 = false) : bfold col l .p0 = .p0 := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    simp only [bfold, List.foldl_cons, bstep, h q List.mem_cons_self, Bool.false_eq_true,
      ↓reduceIte]
    exact ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')

lemma bfold_p1 {l : List ℕ} (h : ∀ q ∈ l, col q 3 = false) (rt ru : Bool) :
    bfold col l (.p1 rt ru) = .p1 (rt && l.all (col · 2)) (ru && l.all (col · 1)) := by
  induction l generalizing rt ru with
  | nil => simp [bfold]
  | cons q l ih =>
    have ih' := ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')
    have e : bstep (.p1 rt ru) (col q) = .p1 (rt && col q 2) (ru && col q 1) := by
      simp [bstep, h q List.mem_cons_self]
    simp only [bfold] at ih' ⊢
    rw [List.foldl_cons, e, ih']
    simp [Bool.and_assoc]

lemma bfold_p2 {l : List ℕ} (h : ∀ q ∈ l, col q 3 = false) (ry : Bool) :
    bfold col l (.p2 ry) = .p2 (ry && l.all (col · 0)) := by
  induction l generalizing ry with
  | nil => simp [bfold]
  | cons q l ih =>
    have ih' := ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')
    have e : bstep (.p2 ry) (col q) = .p2 (ry && col q 0) := by
      simp [bstep, h q List.mem_cons_self]
    simp only [bfold] at ih' ⊢
    rw [List.foldl_cons, e, ih']
    simp [Bool.and_assoc]

lemma bfold_append (l l' : List ℕ) (s : BS) : bfold col (l ++ l') s = bfold col l' (bfold col l s) :=
  List.foldl_append

lemma range'_split (s a b : ℕ) :
    List.range' s (a + b) = List.range' s a ++ List.range' (s + a) b := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, List.range'_succ, List.range'_succ, ih (s + 1),
      show s + 1 + a = s + (a + 1) by omega, List.cons_append]

/-- **One segment.** Marks at `a`, `a + g` and `a + g + w` and none in between: from `p0`, the
phase is `bad` if the digit window `[a, a + g)` is all ones in `t` or in `u`, or the guard window
`[a + g, a + g + w)` is all ones in `y`, and `p0` otherwise. -/
lemma bfold_seg {a g w : ℕ} (hg : 0 < g) (hw : 0 < w) (h₁ : col a 3 = true)
    (h₂ : col (a + g) 3 = true) (h₃ : col (a + g + w) 3 = true)
    (hn : ∀ q, a < q → q < a + g + w → q ≠ a + g → col q 3 = false) :
    bfold col (List.range' a (g + w + 1)) .p0 =
      if (List.range' a g).all (col · 2) || (List.range' a g).all (col · 1) ||
        (List.range' (a + g) w).all (col · 0) then .bad else .p0 := by
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  obtain ⟨w, rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  rw [range'_split a (g + 1 + (w + 1)) 1, range'_split a (g + 1) (w + 1), bfold_append,
    bfold_append]
  simp only [List.range'_succ, List.range'_zero, List.all_cons]
  have hA : ∀ q ∈ List.range' (a + 1) g, col q 3 = false := fun q hq => by
    rw [List.mem_range'_1] at hq; exact hn q (by omega) (by omega) (by omega)
  have hB : ∀ q ∈ List.range' (a + (g + 1) + 1) w, col q 3 = false := fun q hq => by
    rw [List.mem_range'_1] at hq; exact hn q (by omega) (by omega) (by omega)
  have e₁ : bfold col (a :: List.range' (a + 1) g) .p0 =
      .p1 (col a 2 && (List.range' (a + 1) g).all (col · 2))
        (col a 1 && (List.range' (a + 1) g).all (col · 1)) := by
    simp only [bfold, List.foldl_cons, bstep, h₁, ↓reduceIte]
    exact bfold_p1 hA _ _
  rw [e₁]
  set X := col a 2 && (List.range' (a + 1) g).all (col · 2)
  set Y := col a 1 && (List.range' (a + 1) g).all (col · 1)
  by_cases hXY : (X || Y) = true
  · have e₂ : bfold col ((a + (g + 1)) :: List.range' (a + (g + 1) + 1) w) (.p1 X Y) = .bad := by
      simp only [bfold, List.foldl_cons, bstep, h₂, hXY, ↓reduceIte]
      exact bfold_bad col _
    rw [e₂, bfold_bad]
    rw [Bool.or_eq_true] at hXY
    rcases hXY with h | h <;> simp [h]
  · have e₂ : bfold col ((a + (g + 1)) :: List.range' (a + (g + 1) + 1) w) (.p1 X Y) =
        .p2 (col (a + (g + 1)) 0 && (List.range' (a + (g + 1) + 1) w).all (col · 0)) := by
      simp only [bfold, List.foldl_cons, bstep, h₂, hXY, ↓reduceIte, Bool.false_eq_true]
      exact bfold_p2 hB _
    rw [e₂]
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hXY
    simp only [bfold, List.foldl_cons, List.foldl_nil, bstep,
      show a + (g + 1 + (w + 1)) = a + (g + 1) + (w + 1) by omega, h₃, ↓reduceIte, hXY.1, hXY.2,
      Bool.false_or]

lemma seg_uniq {K a c d e : ℕ} (hd : d < K) (he : e < K) (h : a * K + d = c * K + e) :
    a = c ∧ d = e := by
  have h1 : (d + a * K) / K = a := by
    rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hd, Nat.zero_add]
  have h2 : (e + c * K) / K = c := by
    rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt he, Nat.zero_add]
  have hac : a = c := by rw [← h1, ← h2, Nat.add_comm d, Nat.add_comm e, h]
  subst hac
  exact ⟨rfl, by omega⟩

/-- The segment test: the digit window of `t` or of `u`, or the guard window of `y`, is all ones. -/
def segBad (col : ℕ → Fin 4 → Bool) (ρ K G c : ℕ) : Bool :=
  (List.range' (ρ + c * K + 1) G).all (col · 2) || (List.range' (ρ + c * K + 1) G).all (col · 1) ||
    (List.range' (ρ + c * K + 1 + G) (K - 1 - G)).all (col · 0)

/-- **The whole slot.** The marks of the phase mask sit exactly at `ρ + c K` (`c ≤ n`),
`ρ + c K + 1` and `ρ + c K + 1 + G` (`c < n`): from `p2 false`, the phase after the
`ρ + n K + m` columns is `bad` if some segment test holds and `p0` otherwise. -/
theorem bfold_slot {ρ K n G m : ℕ} (hG : 0 < G) (hGK : G + 1 < K) (hm : 0 < m)
    (hS : ∀ c ≤ n, col (ρ + c * K) 3 = true) (h₁ : ∀ c < n, col (ρ + c * K + 1) 3 = true)
    (h₂ : ∀ c < n, col (ρ + c * K + 1 + G) 3 = true)
    (hmk : ∀ q, col q 3 = true → (∃ c ≤ n, q = ρ + c * K) ∨
      ∃ c < n, q = ρ + c * K + 1 ∨ q = ρ + c * K + 1 + G) :
    bfold col (List.range (ρ + n * K + m)) (.p2 false) =
      if ∃ c < n, segBad col ρ K G c = true then .bad else .p0 := by
  have hun : ∀ q, (∀ c ≤ n, q ≠ ρ + c * K) → (∀ c < n, q ≠ ρ + c * K + 1) →
      (∀ c < n, q ≠ ρ + c * K + 1 + G) → col q 3 = false := by
    intro q a b c
    by_contra hq
    rcases hmk q (by simpa using hq) with ⟨c', hc', e⟩ | ⟨c', hc', e | e⟩
    · exact a c' hc' e
    · exact b c' hc' e
    · exact c c' hc' e
  -- the marks lie at or below `ρ + n K`
  have hle : ∀ c < n, c * K + K ≤ n * K := fun c hc => by
    have := Nat.mul_le_mul_right K (show c + 1 ≤ n by omega); rwa [Nat.add_mul, Nat.one_mul] at this
  have hle' : ∀ c ≤ n, c * K ≤ n * K := fun c hc => Nat.mul_le_mul_right K hc
  -- the middle segments
  have hmid : ∀ c ≤ n, bfold col (List.range' (ρ + 1) (c * K)) .p0 =
      if ∃ c' < c, segBad col ρ K G c' = true then .bad else .p0 := by
    intro c
    induction c with
    | zero => intro _; simp [bfold]
    | succ c ih =>
      intro hc
      rw [Nat.add_mul, Nat.one_mul, range'_split, bfold_append, ih (by omega)]
      by_cases hb : ∃ c' < c, segBad col ρ K G c' = true
      · have hb' : ∃ c' < c + 1, segBad col ρ K G c' = true := by
          obtain ⟨c', h, e⟩ := hb; exact ⟨c', by omega, e⟩
        simp only [hb, hb', ↓reduceIte, bfold_bad]
      · simp only [hb, ↓reduceIte]
        have ha : ρ + 1 + c * K = ρ + c * K + 1 := by omega
        have e : List.range' (ρ + c * K + 1) K =
            List.range' (ρ + c * K + 1) (G + (K - 1 - G) + 1) := by congr 1; omega
        rw [ha, e, bfold_seg (a := ρ + c * K + 1) (g := G) (w := K - 1 - G) hG (by omega)
          (h₁ c (by omega)) (h₂ c (by omega))
          (by
            have := hS (c + 1) hc
            rwa [show ρ + (c + 1) * K = ρ + c * K + 1 + G + (K - 1 - G) by
              rw [Nat.add_mul, Nat.one_mul]; omega] at this)
          (fun q hq1 hq2 hq3 => hun q (fun c' _ e => ?_) (fun c' _ e => ?_) (fun c' _ e => ?_))]
        · by_cases hs : segBad col ρ K G c = true
          · have hs' : ∃ c' < c + 1, segBad col ρ K G c' = true := ⟨c, by omega, hs⟩
            simp only [segBad] at hs
            simp only [hs, hs', ↓reduceIte]
          · have hs' : ¬ ∃ c' < c + 1, segBad col ρ K G c' = true := by
              rintro ⟨c', hc', hbc⟩
              rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with h | rfl
              · exact hb ⟨c', h, hbc⟩
              · exact hs hbc
            simp only [segBad, Bool.not_eq_true] at hs
            simp only [hs, hs', ↓reduceIte, Bool.false_eq_true]
        all_goals
          have := seg_uniq (a := c') (c := c) (K := K) (d := q - ρ - c' * K)
            (e := q - ρ - c * K) (by omega) (by omega) (by omega)
          omega
  have e : List.range (ρ + n * K + m) = List.range' 0 ρ ++ [ρ] ++ List.range' (ρ + 1) (n * K) ++
      List.range' (ρ + 1 + n * K) (m - 1) := by
    rw [List.range_eq_range', show ρ + n * K + m = ρ + 1 + n * K + (m - 1) by omega, range'_split,
      range'_split, range'_split 0 ρ 1]
    simp
  have hlow : bfold col (List.range' 0 ρ) (.p2 false) = .p2 false := by
    rw [bfold_p2 (fun q hq => ?_)]
    · simp
    · rw [List.mem_range'_1] at hq
      exact hun q (fun c _ e => by omega) (fun c _ e => by omega) (fun c _ e => by omega)
  have hρ : bfold col [ρ] (.p2 false) = .p0 := by
    have := hS 0 (Nat.zero_le _)
    simp only [Nat.zero_mul, Nat.add_zero] at this
    simp [bfold, bstep, this]
  rw [e, bfold_append, bfold_append, bfold_append, hlow, hρ, hmid n le_rfl]
  have htop : ∀ q ∈ List.range' (ρ + 1 + n * K) (m - 1), col q 3 = false := fun q hq => by
    rw [List.mem_range'_1] at hq
    refine hun q (fun c hc e => ?_) (fun c hc e => ?_) (fun c hc e => ?_)
    · have := hle' c hc; omega
    · have := hle c hc; omega
    · have := hle c hc; omega
  split_ifs
  · exact bfold_bad col _
  · exact bfold_p0 htop

end Fold

/-! ### The registers of the bad-state code -/

section Concrete

variable (p : Par)

/-- The offset of mark `r < 3` within its segment. -/
def mOff (G r : ℕ) : ℕ := if r = 0 then 0 else if r = 1 then 1 else G + 1

/-- Mark `j` of the phase mask. -/
def posM (j : ℕ) : ℕ := posS p (j / 3) + mOff p.G (j % 3)

/-- The phase mask: marks at `posS c` (`c ≤ n`), `posS c + 1` and `posS c + 1 + G` (`c < n`). -/
def mkV : ℕ := maskVal (3 * p.n + 1) (posM p)

/-- The four registers read by `badC`. -/
def badVals (v : V) : Fin 4 → ℕ :=
  ![v.y, placeVal (p.n * p.G) (posA p) v.u.testBit, placeVal (p.n * p.G) (posA p) v.t.testBit,
    mkV p]

variable {p}

lemma posM_mono (hG : 0 < p.G) (hGK : p.G + 1 < p.K) : StrictMono (posM p) := by
  refine strictMono_nat_of_lt_succ fun j => ?_
  unfold posM posS mOff
  rcases (by omega : (j + 1) / 3 = j / 3 ∧ (j % 3 = 0 ∧ (j + 1) % 3 = 1 ∨ j % 3 = 1 ∧ (j + 1) % 3 = 2)
    ∨ (j + 1) / 3 = j / 3 + 1 ∧ j % 3 = 2 ∧ (j + 1) % 3 = 0) with ⟨h, h' | h'⟩ | ⟨h, h1, h2⟩
  · rw [h, h'.1, h'.2]; simp
  · rw [h, h'.1, h'.2]; simp; omega
  · rw [h, h1, h2, Nat.add_mul, Nat.one_mul]; simp; omega

lemma testBit_mkV (hG : 0 < p.G) (hGK : p.G + 1 < p.K) (q : ℕ) :
    (mkV p).testBit q = true ↔ (∃ c ≤ p.n, q = posS p c) ∨
      ∃ c < p.n, q = posS p c + 1 ∨ q = posS p c + 1 + p.G := by
  rw [mkV, testBit_maskVal (posM_mono hG hGK), decide_eq_true_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    unfold posM mOff
    rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
    · exact Or.inl ⟨j / 3, by omega, by simp [h]⟩
    · exact Or.inr ⟨j / 3, by omega, Or.inl (by simp [h])⟩
    · exact Or.inr ⟨j / 3, by omega, Or.inr (by simp [h]; omega)⟩
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl | rfl⟩)
    · exact ⟨3 * c, by omega, by simp [posM, mOff]⟩
    · exact ⟨3 * c + 1, by omega, by
        simp [posM, mOff, show (3 * c + 1) / 3 = c by omega, show (3 * c + 1) % 3 = 1 by omega]⟩
    · exact ⟨3 * c + 2, by omega, by
        simp [posM, mOff, show (3 * c + 2) / 3 = c by omega, show (3 * c + 2) % 3 = 2 by omega]
        omega⟩

/-- A digit window of a spread compact field is all ones exactly when the digit is. -/
lemma all_spread (hG : 0 < p.G) (hGK : p.G < p.K) {c : ℕ} (hc : c < p.n) (b : ℕ → Bool) :
    (List.range' (posS p c + 1) p.G).all (fun q => (placeVal (p.n * p.G) (posA p) b).testBit q) =
      true ↔ ∀ g < p.G, b (c * p.G + g) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h g hg
    have := h (posS p c + 1 + g) (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    rwa [← posA_split hG c g hg, testBit_placeVal_at (posA_mono hG hGK)
      (by nlinarith) b] at this
  · intro h q hq
    rw [List.mem_range'_1] at hq
    obtain ⟨g, rfl⟩ : ∃ g, q = posS p c + 1 + g := ⟨q - (posS p c + 1), by omega⟩
    rw [← posA_split hG c g (by omega), testBit_placeVal_at (posA_mono hG hGK) (by nlinarith) b]
    exact h g (by omega)

lemma lt_all_ones {x w : ℕ} (hx : x < 2 ^ w) : x + 1 < 2 ^ w ↔ ¬ ∀ g < w, x.testBit g = true := by
  constructor
  · intro h hall
    have : x = 2 ^ w - 1 := Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_two_pow_sub_one]
      by_cases hi : i < w
      · simp [hall i hi, hi]
      · simp only [hi, decide_false]
        exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num)
          (by omega)))
    omega
  · intro h
    by_contra hge
    have hx' : x = 2 ^ w - 1 := by omega
    exact h fun g hg => by rw [hx', Nat.testBit_two_pow_sub_one]; simp [hg]

lemma add_pow_lt_iff {z a b : ℕ} : z + 2 ^ a < 2 ^ (a + b) ↔ z / 2 ^ a + 1 < 2 ^ b := by
  have hP : 0 < 2 ^ a := by positivity
  have hz := Nat.div_add_mod z (2 ^ a)
  have hr := Nat.mod_lt z hP
  rw [Nat.pow_add]
  constructor
  · intro h
    by_contra hge
    have := Nat.mul_le_mul_left (2 ^ a) (show 2 ^ b ≤ z / 2 ^ a + 1 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  · intro h
    have := Nat.mul_le_mul_left (2 ^ a) (show z / 2 ^ a + 2 ≤ 2 ^ b by omega)
    rw [Nat.mul_add] at this
    omega

/-- The digit condition of `Good` as a bit test. -/
lemma cdig_good_iff (G c t : ℕ) :
    cdig G c t + 1 < 2 ^ G ↔ ¬ ∀ g < G, t.testBit (c * G + g) = true := by
  rw [cdig, lt_all_ones (window_lt _ _ _)]
  refine not_congr (forall₂_congr fun g hg => ?_)
  rw [window, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm g]
  simp [hg]

/-- The guard condition of `Good` as a bit test. -/
lemma seg_good_iff (hGK : p.G + 1 < p.K) (c y : ℕ) :
    seg p.ρ p.K c y / 2 + 2 ^ p.G < 2 ^ (p.K - 1) ↔
      ¬ ∀ g < p.K - 1 - p.G, y.testBit (posS p c + 1 + p.G + g) = true := by
  rw [show p.K - 1 = p.G + (p.K - 1 - p.G) by omega, add_pow_lt_iff, Nat.add_sub_cancel_left]
  have hlt : seg p.ρ p.K c y / 2 / 2 ^ p.G < 2 ^ (p.K - 1 - p.G) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, Nat.div_lt_iff_lt_mul (by norm_num),
      ← Nat.pow_succ, show (p.K - 1 - p.G + p.G).succ = p.K by omega]
    exact window_lt _ _ _
  rw [lt_all_ones hlt]
  refine not_congr (forall₂_congr fun g hg => ?_)
  have hgK : g + (p.G + 1) < p.K := by
    clear hlt
    omega
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ', Nat.testBit_div_two_pow, seg, window,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [hgK, decide_true, Bool.true_and, posS]
  rw [Nat.succ_eq_add_one, show g + (p.G + 1) + (p.ρ + c * p.K) = p.ρ + c * p.K + 1 + p.G + g by omega]

open Classical in
/-- **The code of the bad states.** -/
theorem badC_eval {A : ℕ} (hA : 4 ≤ A) (hG : 0 < p.G) (hGK : p.G + 1 < p.K) (hm : 0 < p.m)
    (v : V) : (badC A hA).eval p.wy (badVals p v) = if Good p v then 0 else 1 := by
  set col : ℕ → Fin 4 → Bool := fun q r => (badVals p v r).testBit q with hcol
  have hrun : BS.ofCode ((badC A hA).run p.wy (badC A hA).init (badVals p v)).val =
      bfold col (List.range p.wy) (.p2 false) := by
    rw [CAuto.run_eq_foldl]
    exact badC_run col hA _ (.p2 false)
  have h3 : ∀ q, col q 3 = (mkV p).testBit q := fun q => rfl
  have hslot := bfold_slot (col := col) (ρ := p.ρ) (K := p.K) (n := p.n) (G := p.G) (m := p.m)
    hG hGK hm (fun c hc => by rw [h3]; exact (testBit_mkV hG hGK _).2 (Or.inl ⟨c, hc, rfl⟩))
    (fun c hc => by rw [h3]; exact (testBit_mkV hG hGK _).2 (Or.inr ⟨c, hc, Or.inl rfl⟩))
    (fun c hc => by rw [h3]; exact (testBit_mkV hG hGK _).2 (Or.inr ⟨c, hc, Or.inr rfl⟩))
    (fun q hq => by rw [h3] at hq; exact (testBit_mkV hG hGK q).1 hq)
  have hseg : ∀ c < p.n, segBad col p.ρ p.K p.G c = true ↔
      ¬ (cdig p.G c v.t + 1 < 2 ^ p.G ∧ cdig p.G c v.u + 1 < 2 ^ p.G ∧
        seg p.ρ p.K c v.y / 2 + 2 ^ p.G < 2 ^ (p.K - 1)) := by
    intro c hc
    rw [cdig_good_iff, cdig_good_iff, seg_good_iff hGK]
    have ht := all_spread hG (by omega) hc v.t.testBit
    have hu := all_spread hG (by omega) hc v.u.testBit
    simp only [segBad, Bool.or_eq_true]
    rw [show posS p c = p.ρ + c * p.K from rfl] at ht hu
    have hy : (List.range' (p.ρ + c * p.K + 1 + p.G) (p.K - 1 - p.G)).all (col · 0) = true ↔
        ∀ g < p.K - 1 - p.G, v.y.testBit (posS p c + 1 + p.G + g) = true := by
      rw [List.all_eq_true]
      constructor
      · intro h g hg; exact h _ (List.mem_range'_1.2 ⟨by simp [posS], by simp [posS]; omega⟩)
      · intro h q hq
        rw [List.mem_range'_1] at hq
        have := h (q - (p.ρ + c * p.K + 1 + p.G)) (by omega)
        rwa [show posS p c + 1 + p.G + (q - (p.ρ + c * p.K + 1 + p.G)) = q by
          simp [posS]; omega] at this
    rw [hy]
    have ht' : ((List.range' (p.ρ + c * p.K + 1) p.G).all fun x => col x 2) = true ↔
        ∀ g < p.G, v.t.testBit (c * p.G + g) = true := ht
    have hu' : ((List.range' (p.ρ + c * p.K + 1) p.G).all fun x => col x 1) = true ↔
        ∀ g < p.G, v.u.testBit (c * p.G + g) = true := hu
    rw [ht', hu']
    tauto
  unfold CAuto.eval
  show (if BS.ofCode _ = .bad then 1 else 0) = _
  rw [hrun, show p.wy = p.ρ + p.n * p.K + p.m from rfl, hslot]
  by_cases hgood : Good p v
  · have hb : ¬ ∃ c < p.n, segBad col p.ρ p.K p.G c = true :=
      fun ⟨c, hc, hb⟩ => (hseg c hc).1 hb (hgood c hc)
    simp [hb, hgood]
  · have hb : ∃ c < p.n, segBad col p.ρ p.K p.G c = true := by
      by_contra hno
      exact hgood fun c hc => by
        by_contra hc'
        exact hno ⟨c, hc, (hseg c hc).2 hc'⟩
    simp [hb, hgood]

end Concrete

end IntegerMultBounds.MathlibTM2.Layer.CompactGadget
