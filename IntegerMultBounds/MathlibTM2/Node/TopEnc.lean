module

public import IntegerMultBounds.MathlibTM2.Node.Phase
public import IntegerMultBounds.MathlibTM2.Layer.TopZ

/-!
# Streams of the simultaneous layer

Stream identities for the host machine of the simultaneous layer (`Node/TopProc.lean`):
`topRecList_getElem` (record `k` is row `k / 2^n`, address `k % 2^n`); `topEnc_toRows`,
`topEnc_ofRows` (turning top address bits into rows and back changes no symbol);
`topEnc_padRows` (zero rows append zero pairs); `topEnc_unpadRows` (the first rows are a prefix);
`topPhase_sZ` (`phaseZ` with the indicator mask `topSelMask sel` and `c = 1` is `sZ sel` for
distinct `sel`); `topCoeffList_mul` (multiplication by a constant is `GR.mulG` on the
coefficients).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Layer

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {A R r n w : ℕ}

/-! ### Records by index -/

/-- Record `k` of the stream: row `k / 2^n`, address `k % 2^n`. -/
lemma topRecList_getElem (Z : ZArr (Fin R × Fin r) n) (k : ℕ) (hk : k < (recList w Z).length) :
    (recList w Z)[k] = List.ofFn fun c : Fin r =>
      red w (Z ((⟨k / 2 ^ n, Nat.div_lt_of_lt_mul (by
        rw [length_recList] at hk; rw [Nat.mul_comm]; exact hk)⟩, c), addrBits n (k % 2 ^ n))) := by
  have hlen := length_recList (w := w) Z
  have hpos : 0 < 2 ^ n := by positivity
  have hm : k / 2 ^ n < (List.finRange R).length := by
    rw [List.length_finRange]
    exact Nat.div_lt_of_lt_mul (by rw [hlen] at hk; rw [Nat.mul_comm]; exact hk)
  have ha : k % 2 ^ n < 2 ^ n := Nat.mod_lt _ hpos
  have hk' : 2 ^ n * (k / 2 ^ n) + k % 2 ^ n = k := Nat.div_add_mod k (2 ^ n)
  have h := getElem_flatMap_const (fun u : Fin R => (List.range (2 ^ n)).map fun a =>
      List.ofFn fun c : Fin r => red w (Z ((u, c), addrBits n a))) (2 ^ n) (by simp)
    (List.finRange R) (k / 2 ^ n) (k % 2 ^ n) hm ha (by rw [hk']; exact hk)
  simp only [hk'] at h
  refine h.trans ?_
  simp

/-! ### Rows from the top bits -/

/-- `toRows` changes no symbol. -/
theorem topEnc_toRows (a : ℕ) (Z : ZArr (Fin R × Fin r) (n + a)) :
    encZ A w (toRows a Z) = encZ A w Z := by
  have hrec : recList w (toRows a Z) = recList w Z := by
    apply List.ext_getElem
    · simp [length_recList, pow_add]; ring
    · intro k h1 h2
      rw [topRecList_getElem, topRecList_getElem]
      congr 1
      funext c
      simp only [toRows]
      congr 3
      · simp [Nat.div_div_eq_div_mul, pow_add]
      · funext t
        refine Fin.addCases (fun i => ?_) (fun j => ?_) t
        · rw [Fin.append_left]
          simp [addrBits, Nat.testBit_mod_two_pow, show (i : ℕ) < n + a by omega]
        · rw [Fin.append_right]
          simp [addrBits, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm]
  simp only [encZ, coeffList, hrec]

lemma topBitsVal_addrBits {a c : ℕ} (hc : c < 2 ^ a) : bitsVal (addrBits a c) = c :=
  addrBits_bijOn.injOn (bitsVal_lt _) hc (addrBits_bitsVal (addrBits a c))

theorem topToRows_ofRows (a : ℕ) (G : ZArr (Fin (R * 2 ^ a) × Fin r) n) :
    toRows a (ofRows a G) = G := by
  funext p
  obtain ⟨⟨u, c⟩, b⟩ := p
  simp only [toRows, ofRows]
  have hv : bitsVal (fun t : Fin a => Fin.append b (addrBits a (u.1 % 2 ^ a)) (Fin.natAdd n t)) =
      u.1 % 2 ^ a := by
    simp only [Fin.append_right]
    exact topBitsVal_addrBits (Nat.mod_lt _ (by positivity))
  congr 1
  refine Prod.ext (Prod.ext (Fin.ext ?_) rfl) ?_
  · simp only [hv]; exact Nat.div_add_mod _ _
  · funext t; simp

/-- `ofRows` changes no symbol. -/
theorem topEnc_ofRows (a : ℕ) (G : ZArr (Fin (R * 2 ^ a) × Fin r) n) :
    encZ A w (ofRows a G) = encZ A w G := by
  rw [← topEnc_toRows a (ofRows a G), topToRows_ofRows]

/-! ### Padding rows -/

lemma topCoeffSyms_zero : coeffSyms A w (0 : GR w) = List.replicate w (pairSym A false false) := by
  simp [coeffSyms, List.ofFn_const]

/-- Zero rows appended: the stream gains zero pairs. -/
theorem topEnc_padRows {R₂ : ℕ} (h : R ≤ R₂) (Z : ZArr (Fin R × Fin r) n) :
    encZ A w (padRows R₂ Z) =
      encZ A w Z ++ List.replicate ((R₂ - R) * 2 ^ n * r * w) (pairSym A false false) := by
  have hrec : recList w (padRows R₂ Z) =
      recList w Z ++ List.replicate ((R₂ - R) * 2 ^ n) (List.replicate r (0 : GR w)) := by
    apply List.ext_getElem
    · simp [length_recList]
      rw [← Nat.add_mul, Nat.add_sub_cancel' h]
    · intro k h1 h2
      rw [topRecList_getElem]
      have hl := length_recList (w := w) Z
      by_cases hk : k < R * 2 ^ n
      · rw [List.getElem_append_left (by rw [hl]; exact hk), topRecList_getElem]
        have hrow : k / 2 ^ n < R := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)
        simp [padRows, hrow]
      · rw [List.getElem_append_right (by rw [hl]; omega)]
        have hrow : ¬ k / 2 ^ n < R := by
          intro hr
          have := Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ n) |>.1 hr
          omega
        simp [padRows, hrow, red, List.ofFn_const]
  simp only [encZ, coeffList, hrec, List.flatten_append, List.flatten_replicate_replicate,
    List.flatMap_append, List.flatMap_replicate, topCoeffSyms_zero]

/-- Concatenations of pieces of length `k`: taking `j k` elements takes `j` pieces. -/
lemma topTake_flatten {α : Type} (k : ℕ) : ∀ (l : List (List α)), (∀ x ∈ l, x.length = k) →
    ∀ j, l.flatten.take (j * k) = (l.take j).flatten
  | [], _, j => by simp
  | x :: l, hl, 0 => by simp
  | x :: l, hl, j + 1 => by
      have hx : x.length = k := hl x List.mem_cons_self
      rw [List.flatten_cons, List.take_succ_cons, List.flatten_cons, List.take_append,
        List.take_of_length_le (by rw [hx]; nlinarith), hx,
        show (j + 1) * k - k = j * k by rw [Nat.succ_mul, Nat.add_sub_cancel],
        topTake_flatten k l (fun y hy => hl y (List.mem_cons_of_mem _ hy)) j]

/-- The first `R` rows: the first `R 2^n r w` symbols. -/
theorem topEnc_unpadRows {R₂ : ℕ} (h : R ≤ R₂) (G : ZArr (Fin R₂ × Fin r) n) :
    encZ A w (unpadRows h G) = (encZ A w G).take (R * 2 ^ n * r * w) := by
  have hrec : recList w (unpadRows h G) = (recList w G).take (R * 2 ^ n) := by
    apply List.ext_getElem
    · simp [length_recList]
      exact h
    · intro k h1 h2
      rw [List.getElem_take, topRecList_getElem, topRecList_getElem]
      rfl
  have hr : ∀ x ∈ recList w G, x.length = r := by
    intro x hx
    simp only [recList, List.mem_flatMap, List.mem_map] at hx
    obtain ⟨_, _, _, _, rfl⟩ := hx
    simp
  rw [encZ, encZ, coeffList, coeffList, hrec, ← topTake_flatten r _ hr,
    show R * 2 ^ n * r * w = (R * 2 ^ n * r) * w by ring,
    take_flatMap_const _ w (length_coeffSyms A w)]

/-! ### The phase and the unit -/

/-- The indicator of the selected bits. -/
def topSelMask {N : ℕ} (sel : List (Fin N)) : Fin N → ZMod 2 := fun t => if t ∈ sel then 1 else 0

/-- **The phase is `sZ`.** For distinct selected bits, `phaseZ` with the indicator mask and
`c = 1` is the phase `i ^ (number of set selected bits)`. -/
theorem topPhase_sZ {N : ℕ} (sel : List (Fin N)) (hsel : sel.Nodup)
    (Z : ZArr (Fin R × Fin r) N) : phaseZ (topSelMask sel) 1 Z = sZ sel Z := by
  funext p
  simp only [phaseZ, sZ]
  congr 1
  have h4 : (⟨0, 1⟩ : GaussianInt) ^ 4 = 1 := by decide
  have hval : ∀ t, ((topSelMask sel t * p.2 t).val : ℕ) =
      if t ∈ sel ∧ p.2 t = 1 then 1 else 0 := by
    intro t
    simp only [topSelMask]
    rcases zmod2_zero_or_one (p.2 t) with h | h <;> by_cases ht : t ∈ sel <;>
      simp [h, ht, ZMod.val_one]
  have hsum : (∑ t, (topSelMask sel t * p.2 t).val) = sel.countP (fun t => p.2 t = 1) := by
    simp only [hval]
    rw [Finset.sum_boole, Nat.cast_id, List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup (hsel.filter _)]
    congr 1
    ext t
    simp
  have hexp : (phaseExp (topSelMask sel) 1 p.2).val = sel.countP (fun t => p.2 t = 1) % 4 := by
    rw [phaseExp, one_mul, ← hsum, ← Nat.cast_sum, ZMod.val_natCast]
  rw [hexp, ← pow_eq_pow_mod _ h4]

/-- Multiplication by a constant acts on the coefficient list by `mulG`. -/
lemma topCoeffList_mul (g : GaussianInt) (Z : ZArr (Fin R × Fin r) n) :
    coeffList w (fun p => g * Z p) = (coeffList w Z).map (GR.mulG g.re g.im) :=
  coeffList_map _ _ (fun z => by
    rw [← red_mulG]) Z

end IntegerMultBounds.MathlibTM2.Layer
