module

public import IntegerMultBounds.Schoenhage.TransformOfLayer
public import IntegerMultBounds.Schoenhage.TransformWrap
public import IntegerMultBounds.Resampling.SwapCost

/-! §6 task 7, the step count of the transform programs. On an admissible instance with
`w ≤ r` every part of the forward and opposite programs beyond the generator is bounded by a
fixed multiple of the record volume `V = 2 r w M` times the number of rounds, the layer calls,
or the chunk exchanges, and these add up to a fixed multiple of the paper's bound
`T p [d K + p K^(τ-1) + ℓ d^λ']`. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Spec.SignedRingProduct TwistDescriptors LayoutMachines

/-! ### Word counts -/

theorem clen_flatMap {α : Type*} (L : List α) (f : α → List (List Bool)) :
    clen (L.flatMap f) = (L.map fun x => clen (f x)).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => simp [List.flatMap_cons, clen_append, ih]

theorem sum_map_le {α : Type*} (L : List α) (f : α → ℕ) {B : ℕ} (h : ∀ x ∈ L, f x ≤ B) :
    (L.map f).sum ≤ L.length * B := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have := h x List.mem_cons_self
    nlinarith

/-- The words of one field swap of the layout scripts. -/
theorem clen_opRec {n R : ℕ} {o : Op} (h : OpOK n o) :
    clen (opRec n R o).words ≤ 3 * 2 ^ n + 2 ^ n * R + 2 * n + 9 := by
  obtain ⟨h1, h2, h3⟩ := h
  have b1 := Resampling.SwapCost.bin_length (opP n o)
  have b2 := Resampling.SwapCost.bin_length (2 ^ o.2.1)
  have b3 := Resampling.SwapCost.bin_length (2 ^ o.2.2.2 * R)
  have b4 := Resampling.SwapCost.bin_length o.1
  have b5 := Resampling.SwapCost.bin_length o.2.2.1
  have hP : opP n o ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hG : 2 ^ o.2.1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hB : 2 ^ o.2.2.2 * R ≤ 2 ^ n * R :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  simp only [opRec, Resampling.AxisDriver.Rec.words, opHdrs, Resampling.Script.swapHdrsG, clen_cons, clen_nil,
    List.length_cons, List.length_nil]
  omega

theorem clen_ops_le {n R : ℕ} (os : List Op) (h : ∀ o ∈ os, OpOK n o) :
    clen ((os.map (opRec n R)).flatMap Resampling.AxisDriver.Rec.words) ≤
      os.length * (3 * 2 ^ n + 2 ^ n * R + 2 * n + 9) := by
  rw [clen_flatMap, List.map_map]
  exact sum_map_le os _ (fun o ho => clen_opRec (R := R) (h o ho))

/-! ### Sizes of an admissible instance -/

/-- The sizes of an admissible instance with `w ≤ r`, with `C = ⌈C_l⌉`. -/
theorem adm_sizes {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ} (hadm : Admissible P p d ℓ K w ts)
    (hwr : w ≤ 2 ^ ℓ) :
    ts.prod = 2 ^ Nat.log 2 ts.prod ∧ Nat.log 2 ts.prod ≤ ⌈P.Cl⌉₊ * w ∧ ts.length + 1 = d ∧
      1 ≤ ts.length ∧ d * ℓ ≤ ⌈P.Cl⌉₊ * w ∧ ℓ < p ∧ p + 2 ≤ w ∧ K + 1 ≤ ℓ ∧ 1 ≤ K ∧ 2 ≤ ℓ ∧
      w ≤ 2 * 2 ^ Nat.log 2 ts.prod ∧ ℓ - 1 ≤ Nat.log 2 ts.prod ∧ Nat.log 2 ts.prod ≤ ts.length * ℓ := by
  have hL := layoutOK_of_admissible hadm
  have hsz := admissible_size hadm
  have hpow := powAxes_prod_pow hL.1
  have hn := addr_le hL
  have hlay := log_prod_layout hL
  obtain ⟨-, -, -, -, hd, hℓ, hℓp, -, -, hK, hKℓ, hax, hpw, -⟩ := hadm
  have hlen := hax.1
  have hD : 1 ≤ ts.length := by omega
  have hdm := Nat.div_add_mod' (ℓ - 1) K
  have hlow : ℓ - 1 ≤ Nat.log 2 ts.prod := by
    have e : ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K) = ts.length * (ℓ - 1) := by
      calc ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K) =
          ts.length * ((ℓ - 1) / K * K + (ℓ - 1) % K) := by ring
        _ = ts.length * (ℓ - 1) := by rw [hdm]
    have : ℓ - 1 ≤ ts.length * (ℓ - 1) := Nat.le_mul_of_pos_left _ hD
    omega
  have hw2 : w ≤ 2 * 2 ^ Nat.log 2 ts.prod := by
    calc w ≤ 2 ^ ℓ := hwr
      _ = 2 * 2 ^ (ℓ - 1) := by rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * 2 ^ Nat.log 2 ts.prod := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlow)
  have hnd : Nat.log 2 ts.prod ≤ d * ℓ := hn.trans (Nat.mul_le_mul_right _ (by omega))
  exact ⟨hpow, hnd.trans hsz, by omega, hD, hsz, hℓp, hpw, by omega, hK, hℓ, hw2, hlow, hn⟩

/-! ### One slot's twist -/

theorem length_slotTable {n : ℕ} (π : BitPerm n) (r : ℕ) (ts Is : List ℕ) (h : ℕ) :
    (slotTable π r ts Is h).length = Is.length * h := by
  unfold slotTable
  rw [List.length_flatMap]
  simp [List.sum_replicate, Nat.mul_comm]

theorem length_tableWords (es : List Entry) : (tableWords es).length = 3 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [tableWords, List.flatMap_cons, List.length_append] at ih ⊢; simp [ih]; ring

theorem length_slotAxes_le (ts : List ℕ) (h : ℕ) : (slotAxes ts h).length ≤ ts.length := by
  unfold slotAxes
  exact (List.length_filter_le _ _).trans (by simp)

/-- The constant of one slot's twist. -/
def twC (C : ℕ) : ℕ := 2200 * (C + 1) ^ 2 + 15 * C ^ 2 * (2 * C + 7) + 120 * C + 600

/-- The arithmetic of one slot's twist, with `S` the twist's step count, `E` the table's entries and
`L` its word count. -/
theorem tw_arith {C n r w M E L S : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hwr : w ≤ r) (hw2 : w ≤ 2 * M)
    (hM : 1 ≤ M) (hnC : n ≤ C * w) (hE : E ≤ C * w) (hL : L ≤ E * (2 * n + 4 * r + 3))
    (hS : S ≤ 2200 * (C + 1) ^ 2 * M * r * w + 21) :
    S + M * (8 * r + 13) + 14 + 3 * E * (5 * L + 40) + 80 * (2 * r * w * M) + 400 ≤
      twC C * (2 * r * w * M) := by
  set X := r * w * M with hX
  have hV : 2 * r * w * M = 2 * X := by rw [hX]; ring
  rw [hV]
  have hX1 : 1 ≤ X := by rw [hX]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hS' : S ≤ 2200 * (C + 1) ^ 2 * X + 21 := by
    have : 2200 * (C + 1) ^ 2 * M * r * w = 2200 * (C + 1) ^ 2 * X := by rw [hX]; ring
    omega
  have hMr : M * (8 * r + 13) ≤ 21 * X := by
    have h1 : M * (8 * r + 13) ≤ M * (21 * r) := Nat.mul_le_mul_left _ (by omega)
    have h2 : M * (21 * r) ≤ 21 * X := by
      rw [hX]
      calc M * (21 * r) = 21 * (r * 1 * M) := by ring
        _ ≤ 21 * (r * w * M) := by gcongr
    omega
  have hwwr : w * w * r ≤ 2 * X := by
    have : w * w * r ≤ 2 * M * w * r := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hw2)
    have e : 2 * M * w * r = 2 * X := by rw [hX]; ring
    omega
  have hsum : 2 * n + 4 * r + 3 ≤ (2 * C + 7) * r := by
    have h1 : n ≤ C * r := hnC.trans (Nat.mul_le_mul_left _ hwr)
    have : (2 * C + 7) * r = 2 * (C * r) + 7 * r := by ring
    omega
  have hEE : E * E ≤ C * C * (w * w) := by
    calc E * E ≤ C * w * (C * w) := Nat.mul_le_mul hE hE
      _ = C * C * (w * w) := by ring
  have hT1 : 3 * E * (5 * L + 40) ≤ 15 * (E * E) * (2 * n + 4 * r + 3) + 120 * E := by
    have e : 3 * E * (5 * L + 40) = 15 * E * L + 120 * E := by ring
    have : 15 * E * L ≤ 15 * E * (E * (2 * n + 4 * r + 3)) := Nat.mul_le_mul_left _ hL
    have e2 : 15 * E * (E * (2 * n + 4 * r + 3)) = 15 * (E * E) * (2 * n + 4 * r + 3) := by ring
    omega
  have hT2 : 15 * (E * E) * (2 * n + 4 * r + 3) ≤ 15 * C ^ 2 * (2 * C + 7) * (2 * X) := by
    calc 15 * (E * E) * (2 * n + 4 * r + 3) ≤ 15 * (C * C * (w * w)) * ((2 * C + 7) * r) := by gcongr
      _ = 15 * C ^ 2 * (2 * C + 7) * (w * w * r) := by ring
      _ ≤ 15 * C ^ 2 * (2 * C + 7) * (2 * X) := Nat.mul_le_mul_left _ hwwr
  have hT3 : 120 * E ≤ 120 * C * X := by
    have hwX : w ≤ X := by
      rw [hX]
      calc w = 1 * w * 1 := by ring
        _ ≤ r * w * M := by gcongr
    calc 120 * E ≤ 120 * (C * w) := Nat.mul_le_mul_left _ hE
      _ ≤ 120 * (C * X) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hwX)
      _ = 120 * C * X := by ring
  unfold twC
  set A := 2200 * (C + 1) ^ 2 * X
  set B := 15 * C ^ 2 * (2 * C + 7) * (2 * X)
  set D := 120 * C * X
  have e : (2200 * (C + 1) ^ 2 + 15 * C ^ 2 * (2 * C + 7) + 120 * C + 600) * (2 * X) =
      2 * A + B + 2 * D + 1200 * X := by simp only [A, B, D]; ring
  rw [e]
  omega

/-- One slot's twist costs at most `twC C · V`. -/
theorem twCost_le {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ} (hadm : Admissible P p d ℓ K w ts)
    (hwr : w ≤ 2 ^ ℓ) {h : ℕ} (hh : h < ℓ) :
    twCost (paperPerm (layoutOK_of_admissible hadm)) (2 ^ ℓ) w ts h ≤
      twC ⌈P.Cl⌉₊ * (2 * 2 ^ ℓ * w * ts.prod) := by
  have hL := layoutOK_of_admissible hadm
  obtain ⟨hpow, hnC, hdD, hD, hdl, hℓp, hpw, hKℓ, hK, hℓ, hw2, hlow, hnD⟩ := adm_sizes hadm hwr
  have hE : (slotTable (paperPerm hL) (2 ^ ℓ) ts (slotAxes ts h) h).length ≤ ⌈P.Cl⌉₊ * w := by
    rw [length_slotTable]
    have h1 : (slotAxes ts h).length * h ≤ ts.length * ℓ :=
      Nat.mul_le_mul (length_slotAxes_le ts h) hh.le
    have h2 : ts.length * ℓ ≤ d * ℓ := Nat.mul_le_mul_right _ (by omega)
    omega
  have hok : TableOK (2 ^ ℓ) (Nat.log 2 ts.prod) (slotTable (paperPerm hL) (2 ^ ℓ) ts (slotAxes ts h) h) :=
    slotTable_ok (paperPerm hL) _ ts _ h (fun i hi => by
      have hi' : i < ts.length ∧ h < axLen ts i := by
        unfold slotAxes at hi; simpa using hi
      have := axOff_add_len_le hL.1 hi'.1
      omega)
  have hcl := clen_tableWords_le hok
  have hst := slotTwistCost_le (A := ⌈P.Cl⌉₊) (M := ts.prod) hnC hE Nat.one_le_two_pow (by omega) hwr
  have hclean : ∀ es : List Entry, cleanCost (Nat.log 2 ts.prod) (2 ^ ℓ) w ts.prod es =
      slotTwistCost (Nat.log 2 ts.prod) (2 ^ ℓ) w ts.prod es + ts.prod * (8 * 2 ^ ℓ + 13) + 14 := by
    intro es; unfold cleanCost slotTwistCost; ring
  have hM : 1 ≤ ts.prod := by rw [hpow]; exact Nat.one_le_two_pow
  have hw2' : w ≤ 2 * ts.prod := by rw [hpow]; exact hw2
  unfold twCost
  rw [hclean, length_tableWords]
  have := tw_arith (C := ⌈P.Cl⌉₊) Nat.one_le_two_pow (by omega) hwr hw2' hM hnC hE hcl hst
  linarith

/-! ### One slot's Hadamard part -/

/-- The constant of a prefix-slot Hadamard step. -/
def prC (C : ℕ) : ℕ := 240 * (C + 1) + 1700

theorem prefix_arith {C w D' N V d : ℕ} (hD' : D' ≤ d) (hd : d ≤ C * w) (hw : 1 ≤ w) (hd1 : 1 ≤ d)
    (hN1 : 1 ≤ N) (hNw : N * w = V) :
    prefixCost w D' N ≤ prC C * d * V := by
  unfold prefixCost prC
  have hN : N ≤ V := by rw [← hNw]; exact Nat.le_mul_of_pos_right _ hw
  have hwV : w ≤ V := by rw [← hNw]; exact Nat.le_mul_of_pos_left _ hN1
  have hV1 : 1 ≤ V := le_trans hw hwV
  have hwD : w + D' ≤ (C + 1) * w := by
    have : (C + 1) * w = C * w + w := by ring
    omega
  have hdV : V ≤ d * V := Nat.le_mul_of_pos_left _ hd1
  have t1 : D' * (N * (40 * (w + D') + 400) + 200) ≤ (40 * (C + 1) + 600) * (d * V) + 200 * d := by
    have a1 : N * (40 * (w + D')) ≤ 40 * (C + 1) * V := by
      calc N * (40 * (w + D')) ≤ N * (40 * ((C + 1) * w)) := by gcongr
        _ = 40 * (C + 1) * (N * w) := by ring
        _ = 40 * (C + 1) * V := by rw [hNw]
    have a2 : D' * (N * (40 * (w + D') + 400) + 200) ≤ d * (40 * (C + 1) * V + 400 * V + 200) := by
      have : N * (40 * (w + D') + 400) + 200 ≤ 40 * (C + 1) * V + 400 * V + 200 := by
        have : N * 400 ≤ 400 * V := by omega
        have e : N * (40 * (w + D') + 400) = N * (40 * (w + D')) + N * 400 := by ring
        linarith
      exact Nat.mul_le_mul hD' this
    have e : d * (40 * (C + 1) * V + 400 * V + 200) = (40 * (C + 1) + 400) * (d * V) + 200 * d := by ring
    have : (40 * (C + 1) + 400) * (d * V) ≤ (40 * (C + 1) + 600) * (d * V) := Nat.mul_le_mul_right _ (by omega)
    omega
  have t2 : N * (100 * (w + D') + 400) ≤ (100 * (C + 1) + 400) * V := by
    calc N * (100 * (w + D') + 400) ≤ N * (100 * ((C + 1) * w) + 400) := by gcongr
      _ = 100 * (C + 1) * (N * w) + 400 * N := by ring
      _ ≤ 100 * (C + 1) * V + 400 * V := by rw [hNw]; omega
      _ = (100 * (C + 1) + 400) * V := by ring
  have t3 : 100 * (w + D') ≤ 100 * (C + 1) * w := by
    have := Nat.mul_le_mul_left 100 hwD
    calc 100 * (w + D') ≤ 100 * ((C + 1) * w) := this
      _ = 100 * (C + 1) * w := by ring
  have hdV' : d ≤ d * V := Nat.le_mul_of_pos_right _ hV1
  have s1 : (100 * (C + 1) + 400) * V ≤ (100 * (C + 1) + 400) * (d * V) := Nat.mul_le_mul_left _ hdV
  have s2 : 100 * (C + 1) * w ≤ 100 * (C + 1) * (d * V) := Nat.mul_le_mul_left _ (hwV.trans hdV)
  have s3 : 200 * d ≤ 200 * (d * V) := Nat.mul_le_mul_left _ hdV'
  have s4 : 500 ≤ 500 * (d * V) := by
    have : 1 ≤ d * V := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have e : (240 * (C + 1) + 1700) * d * V = (40 * (C + 1) + 600) * (d * V) +
      (100 * (C + 1) + 400) * (d * V) + 100 * (C + 1) * (d * V) + 200 * (d * V) + 500 * (d * V) := by ring
  rw [e]
  linarith

/-- The constant of a slot's Hadamard bookkeeping. -/
def hdC (C Cw : ℕ) : ℕ := 8 + 8 * (32 * (C + Cw + 1) + C + 8) + 201

theorem prefixBase_le {D ℓ K h n L : ℕ} (hn : n = D * ((ℓ - 1) / K) * K + D * ((ℓ - 1) % K) + L)
    (hh : h < (ℓ - 1) % K) : prefixBase D ℓ K h ≤ n := by
  unfold prefixBase
  have : h * D ≤ D * ((ℓ - 1) % K) := by
    calc h * D ≤ (ℓ - 1) % K * D := Nat.mul_le_mul_right _ hh.le
      _ = D * ((ℓ - 1) % K) := by ring
  omega

/-- One slot's Hadamard part: a prefix or top slot costs at most `prC C · d V`, a chunk-group slot
its layer call `CL`, plus `hdC · V` of bookkeeping. -/
theorem hadCost_le {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ} (hadm : Admissible P p d ℓ K w ts)
    (hwr : w ≤ 2 ^ ℓ) (CL : ℕ) {h : ℕ} :
    hadCost p d (2 ^ ℓ) w ts ℓ K CL h ≤
      (if h < (ℓ - 1) % K ∨ ℓ - 1 ≤ h then prC ⌈P.Cl⌉₊ * d * (2 * 2 ^ ℓ * w * ts.prod) else CL) +
        hdC ⌈P.Cl⌉₊ P.Cw * (2 * 2 ^ ℓ * w * ts.prod) := by
  have hL := layoutOK_of_admissible hadm
  have hlay := log_prod_layout hL
  obtain ⟨hpow, hnC, hdD, hD, hdl, hℓp, hpw, hKℓ, hK, hℓ, hw2, hlow, hnD⟩ := adm_sizes hadm hwr
  have hhdr := fun hb hh => chunkHdr_length hadm (by omega) (h := h) hb hh
  have hd1 : 1 ≤ d := by omega
  have hdCw : d ≤ ⌈P.Cl⌉₊ * w := by
    have : d ≤ d * ℓ := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hw : 1 ≤ w := by omega
  set V := 2 * 2 ^ ℓ * w * ts.prod with hV
  set C := ⌈P.Cl⌉₊
  have hM : 1 ≤ ts.prod := by rw [hpow]; exact Nat.one_le_two_pow
  have hN1 : 1 ≤ 2 * 2 ^ ℓ * ts.prod := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hNw : 2 * 2 ^ ℓ * ts.prod * w = V := by rw [hV]; ring
  have hwV : w ≤ V := by rw [← hNw]; exact Nat.le_mul_of_pos_left _ hN1
  have hpV : p ≤ V := by omega
  have hdV : d ≤ C * V := hdCw.trans (Nat.mul_le_mul_left _ hwV)
  have hV1 : 1 ≤ V := le_trans hw hwV
  -- unary words of at most `2 r M` bits
  have hones : ∀ s, s ≤ Nat.log 2 ts.prod → 2 * 2 ^ ℓ * 2 ^ s ≤ V := by
    intro s hs
    have h1 : 2 ^ s ≤ ts.prod := by rw [hpow]; exact Nat.pow_le_pow_right (by norm_num) hs
    calc 2 * 2 ^ ℓ * 2 ^ s ≤ 2 * 2 ^ ℓ * ts.prod := Nat.mul_le_mul_left _ h1
      _ ≤ 2 * 2 ^ ℓ * ts.prod * w := Nat.le_mul_of_pos_right _ hw
      _ = V := hNw
  have hCV : C * V ≤ C * V := le_rfl
  have hbig : 32 * (C + P.Cw + 1) * p ≤ 32 * (C + P.Cw + 1) * V := Nat.mul_le_mul_left _ hpV
  unfold hadCost
  by_cases h1 : h < (ℓ - 1) % K
  · have hcl : clen (hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h) ≤ (32 * (C + P.Cw + 1) + C + 8) * V := by
      simp only [hadWords, h1, if_true, clen_cons, clen_nil, length_ones, List.length_cons, List.length_nil]
      have := hones _ (prefixBase_le hlay h1)
      have hDV : ts.length ≤ C * V := by omega
      have e : (32 * (C + P.Cw + 1) + C + 8) * V = 32 * (C + P.Cw + 1) * V + C * V + 8 * V := by ring
      omega
    have hp := prefix_arith (C := C) (D' := ts.length) (N := 2 * 2 ^ ℓ * ts.prod) (by omega) hdCw hw hd1 hN1 hNw
    simp only [h1, if_true, true_or]
    unfold hdC
    have e : (8 + 8 * (32 * (C + P.Cw + 1) + C + 8) + 201) * V = 8 * V + 8 * ((32 * (C + P.Cw + 1) + C + 8) * V) + 201 * V := by ring
    rw [e]
    omega
  · by_cases h2 : h < ℓ - 1
    · have hcl : clen (hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h) ≤ (32 * (C + P.Cw + 1) + C + 8) * V := by
        simp only [hadWords, h1, h2, if_true, if_false, clen_cons, clen_nil, List.length_cons, List.length_nil]
        have := hhdr (by omega) h2
        have e : (32 * (C + P.Cw + 1) + C + 8) * V = 32 * (C + P.Cw + 1) * V + C * V + 8 * V := by ring
        omega
      have hn : ¬ (h < (ℓ - 1) % K ∨ ℓ - 1 ≤ h) := by omega
      rw [if_neg h1, if_pos h2, if_neg hn]
      unfold hdC
      have e : (8 + 8 * (32 * (C + P.Cw + 1) + C + 8) + 201) * V = 8 * V + 8 * ((32 * (C + P.Cw + 1) + C + 8) * V) + 201 * V := by ring
      rw [e]
      omega
    · have hcl : clen (hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h) ≤ (32 * (C + P.Cw + 1) + C + 8) * V := by
        simp only [hadWords, h1, h2, if_false, clen_cons, clen_nil, length_ones, List.length_cons, List.length_nil]
        have := hones (topBase ts.length ℓ K) (by unfold topBase; omega)
        have hLD := longs_length_le ts ℓ
        have hDV : ts.length ≤ C * V := by omega
        have e : (32 * (C + P.Cw + 1) + C + 8) * V = 32 * (C + P.Cw + 1) * V + C * V + 8 * V := by ring
        omega
      have hp := prefix_arith (C := C) (D' := (longs ts ℓ).length) (N := 2 * 2 ^ ℓ * ts.prod)
        (by have := longs_length_le ts ℓ; omega) hdCw hw hd1 hN1 hNw
      have hc : h < (ℓ - 1) % K ∨ ℓ - 1 ≤ h := Or.inr (by omega)
      rw [if_neg h1, if_neg h2, if_pos hc]
      unfold hdC
      have e : (8 + 8 * (32 * (C + P.Cw + 1) + C + 8) + 201) * V = 8 * V + 8 * ((32 * (C + P.Cw + 1) + C + 8) * V) + 201 * V := by ring
      rw [e]
      omega

/-! ### All rounds -/

theorem sum_range_sel {A B : ℕ} (g : ℕ → ℕ) (c : ℕ → Bool) :
    ∀ ℓ : ℕ, (∀ h < ℓ, g h ≤ (if c h then A else 0) + B) →
      ((List.range ℓ).map g).sum ≤ ((List.range ℓ).filter c).length * A + ℓ * B
  | 0, _ => by simp
  | ℓ + 1, hg => by
    rw [List.range_succ, List.map_append, List.sum_append, List.filter_append]
    have ih := sum_range_sel g c ℓ (fun h hh => hg h (by omega))
    have hl := hg ℓ (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_append]
    by_cases hc : c ℓ = true
    · simp only [hc, if_true] at hl
      simp only [List.filter_cons, hc, if_true, List.filter_nil, List.length_cons, List.length_nil]
      nlinarith
    · simp only [hc, Bool.false_eq_true, if_false] at hl
      have hc' : c ℓ = false := by simpa using hc
      simp only [List.filter_cons, hc', Bool.false_eq_true, if_false, List.filter_nil, List.length_nil]
      nlinarith

theorem filter_range_length_le (c : ℕ → Bool) (ℓ : ℕ) (S : Finset ℕ) (h : ∀ x < ℓ, c x = true → x ∈ S) :
    ((List.range ℓ).filter c).length ≤ S.card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  apply Finset.card_le_card
  intro x hx
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range] at hx
  exact h x hx.1 hx.2

/-- The prefix and top slots number at most `K`. -/
theorem sel_count {ℓ K : ℕ} (hK : 1 ≤ K) :
    ((List.range ℓ).filter fun h => decide (h < (ℓ - 1) % K ∨ ℓ - 1 ≤ h)).length ≤ K := by
  have hb : (ℓ - 1) % K < K := Nat.mod_lt _ (by omega)
  have := filter_range_length_le (fun h => decide (h < (ℓ - 1) % K ∨ ℓ - 1 ≤ h)) ℓ
    (Finset.range ((ℓ - 1) % K) ∪ {ℓ - 1}) (fun x hx hc => by
      simp only [decide_eq_true_eq] at hc
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton]
      omega)
  refine this.trans ((Finset.card_union_le _ _).trans ?_)
  simp; omega

theorem opp_sel_count {ℓ K : ℕ} (hK : 1 ≤ K) :
    ((List.range ℓ).filter fun k => decide (ℓ - 1 - k < (ℓ - 1) % K ∨ ℓ - 1 ≤ ℓ - 1 - k)).length ≤ K := by
  have hb : (ℓ - 1) % K < K := Nat.mod_lt _ (by omega)
  have := filter_range_length_le (fun k => decide (ℓ - 1 - k < (ℓ - 1) % K ∨ ℓ - 1 ≤ ℓ - 1 - k)) ℓ
    (Finset.Ico (ℓ - (ℓ - 1) % K) ℓ ∪ {0}) (fun x hx hc => by
      simp only [decide_eq_true_eq] at hc
      simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_singleton]
      omega)
  refine this.trans ((Finset.card_union_le _ _).trans ?_)
  simp; omega

/-- All forward rounds: the prefix and top slots' Hadamard steps, every chunk-group layer call and
every slot's bookkeeping and twist. -/
theorem fwdRoundsCost_le {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) (CL : ℕ) :
    fwdRoundsCost (layoutOK_of_admissible hadm) p d w CL ≤
      K * (prC ⌈P.Cl⌉₊ * d * (2 * 2 ^ ℓ * w * ts.prod)) + ℓ * CL +
        ℓ * ((hdC ⌈P.Cl⌉₊ P.Cw + twC ⌈P.Cl⌉₊ + 3) * (2 * 2 ^ ℓ * w * ts.prod)) := by
  have hK := (adm_sizes hadm hwr).2.2.2.2.2.2.2.2.1
  obtain ⟨V, hV⟩ : ∃ V, V = 2 * 2 ^ ℓ * w * ts.prod := ⟨_, rfl⟩
  have hV1 : 1 ≤ V := by
    have hw : 0 < w := by have := (adm_sizes hadm hwr).2.2.2.2.2.2.1; omega
    have hM : 0 < ts.prod := by rw [(adm_sizes hadm hwr).1]; exact Nat.two_pow_pos _
    rw [hV]; exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos two_pos (Nat.two_pow_pos _)) hw) hM
  rw [← hV]
  unfold fwdRoundsCost
  have hs := sum_range_sel (A := prC ⌈P.Cl⌉₊ * d * V)
    (B := CL + (hdC ⌈P.Cl⌉₊ P.Cw + twC ⌈P.Cl⌉₊ + 3) * V)
    (fun h => hadCost p d (2 ^ ℓ) w ts ℓ K CL h + 1 + twCost (paperPerm (layoutOK_of_admissible hadm)) (2 ^ ℓ) w ts h + 2)
    (fun h => decide (h < (ℓ - 1) % K ∨ ℓ - 1 ≤ h)) ℓ (fun h hh => by
      have h1 := hadCost_le hadm hwr CL (h := h)
      have h2 := twCost_le hadm hwr hh
      rw [← hV] at h1 h2
      have e : (hdC ⌈P.Cl⌉₊ P.Cw + twC ⌈P.Cl⌉₊ + 3) * V = hdC ⌈P.Cl⌉₊ P.Cw * V + twC ⌈P.Cl⌉₊ * V + 3 * V := by ring
      have key : hadCost p d (2 ^ ℓ) w ts ℓ K CL h ≤
          (if decide (h < (ℓ - 1) % K ∨ ℓ - 1 ≤ h) = true then prC ⌈P.Cl⌉₊ * d * V else 0) + CL +
            hdC ⌈P.Cl⌉₊ P.Cw * V := by
        by_cases hc : h < (ℓ - 1) % K ∨ ℓ - 1 ≤ h
        · rw [if_pos hc] at h1; rw [if_pos (by simpa using hc)]; omega
        · rw [if_neg hc] at h1; rw [if_neg (by simpa using hc)]; omega
      show _ ≤ (if decide (h < (ℓ - 1) % K ∨ ℓ - 1 ≤ h) = true then prC ⌈P.Cl⌉₊ * d * V else 0) +
        (CL + (hdC ⌈P.Cl⌉₊ P.Cw + twC ⌈P.Cl⌉₊ + 3) * V)
      omega)
  have hc := sel_count (ℓ := ℓ) hK
  have := Nat.mul_le_mul_right (prC ⌈P.Cl⌉₊ * d * V) hc
  have e : ℓ * (CL + (hdC ⌈P.Cl⌉₊ P.Cw + twC ⌈P.Cl⌉₊ + 3) * V) =
      ℓ * CL + ℓ * ((hdC ⌈P.Cl⌉₊ P.Cw + twC ⌈P.Cl⌉₊ + 3) * V) := by ring
  omega

/-- All opposite rounds, with the same bound. -/
theorem oppRoundsCost_le {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) (CL : ℕ) :
    oppRoundsCost (layoutOK_of_admissible hadm) p d w CL ≤
      K * (prC ⌈P.Cl⌉₊ * d * (2 * 2 ^ ℓ * w * ts.prod)) + ℓ * CL +
        ℓ * ((hdC ⌈P.Cl⌉₊ P.Cw + twC ⌈P.Cl⌉₊ + 3) * (2 * 2 ^ ℓ * w * ts.prod)) := by
  have hK := (adm_sizes hadm hwr).2.2.2.2.2.2.2.2.1
  obtain ⟨V, hV⟩ : ∃ V, V = 2 * 2 ^ ℓ * w * ts.prod := ⟨_, rfl⟩
  have hV1 : 1 ≤ V := by
    have hw : 0 < w := by have := (adm_sizes hadm hwr).2.2.2.2.2.2.1; omega
    have hM : 0 < ts.prod := by rw [(adm_sizes hadm hwr).1]; exact Nat.two_pow_pos _
    rw [hV]; exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos two_pos (Nat.two_pow_pos _)) hw) hM
  rw [← hV]
  unfold oppRoundsCost
  have hs := sum_range_sel (A := prC ⌈P.Cl⌉₊ * d * V)
    (B := CL + (hdC ⌈P.Cl⌉₊ P.Cw + twC ⌈P.Cl⌉₊ + 3) * V)
    (fun k => twCost (paperPerm (layoutOK_of_admissible hadm)) (2 ^ ℓ) w ts (ℓ - 1 - k) + 1 +
      hadCost p d (2 ^ ℓ) w ts ℓ K CL (ℓ - 1 - k) + 2)
    (fun k => decide (ℓ - 1 - k < (ℓ - 1) % K ∨ ℓ - 1 ≤ ℓ - 1 - k)) ℓ (fun k hk => by
      have h1 := hadCost_le hadm hwr CL (h := ℓ - 1 - k)
      have h2 := twCost_le hadm hwr (h := ℓ - 1 - k) (by omega)
      rw [← hV] at h1 h2
      have e : (hdC ⌈P.Cl⌉₊ P.Cw + twC ⌈P.Cl⌉₊ + 3) * V = hdC ⌈P.Cl⌉₊ P.Cw * V + twC ⌈P.Cl⌉₊ * V + 3 * V := by ring
      have key : hadCost p d (2 ^ ℓ) w ts ℓ K CL (ℓ - 1 - k) ≤
          (if decide (ℓ - 1 - k < (ℓ - 1) % K ∨ ℓ - 1 ≤ ℓ - 1 - k) = true then prC ⌈P.Cl⌉₊ * d * V else 0) +
            CL + hdC ⌈P.Cl⌉₊ P.Cw * V := by
        by_cases hc : ℓ - 1 - k < (ℓ - 1) % K ∨ ℓ - 1 ≤ ℓ - 1 - k
        · rw [if_pos hc] at h1; rw [if_pos (by simpa using hc)]; omega
        · rw [if_neg hc] at h1; rw [if_neg (by simpa using hc)]; omega
      show _ ≤ (if decide (ℓ - 1 - k < (ℓ - 1) % K ∨ ℓ - 1 ≤ ℓ - 1 - k) = true then prC ⌈P.Cl⌉₊ * d * V else 0) +
        (CL + (hdC ⌈P.Cl⌉₊ P.Cw + twC ⌈P.Cl⌉₊ + 3) * V)
      omega)
  have hc := opp_sel_count (ℓ := ℓ) hK
  have := Nat.mul_le_mul_right (prC ⌈P.Cl⌉₊ * d * V) hc
  have e : ℓ * (CL + (hdC ⌈P.Cl⌉₊ P.Cw + twC ⌈P.Cl⌉₊ + 3) * V) =
      ℓ * CL + ℓ * ((hdC ⌈P.Cl⌉₊ P.Cw + twC ⌈P.Cl⌉₊ + 3) * V) := by ring
  omega

/-! ### The wrapper's words -/

/-- The constant of one slot's script words. -/
def scC (C Cw : ℕ) : ℕ := 32 * (C + Cw + 1) + C * (2 * C + 7) + 4 * C + 9

theorem clen_hadWords_le {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) (h : ℕ) :
    clen (hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h) ≤
      (32 * (⌈P.Cl⌉₊ + P.Cw + 1) + ⌈P.Cl⌉₊ + 8) * (2 * 2 ^ ℓ * w * ts.prod) := by
  have hL := layoutOK_of_admissible hadm
  have hlay := log_prod_layout hL
  obtain ⟨hpow, hnC, hdD, hD, hdl, hℓp, hpw, hKℓ, hK, hℓ, hw2, hlow, hnD⟩ := adm_sizes hadm hwr
  have hhdr := fun hb hh => chunkHdr_length hadm (by omega) (h := h) hb hh
  have hdCw : d ≤ ⌈P.Cl⌉₊ * w := by
    have : d ≤ d * ℓ := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hw : 1 ≤ w := by omega
  obtain ⟨V, hV⟩ : ∃ V, V = 2 * 2 ^ ℓ * w * ts.prod := ⟨_, rfl⟩
  rw [← hV]
  set C := ⌈P.Cl⌉₊
  have hN1 : 1 ≤ 2 * 2 ^ ℓ * ts.prod := by
    have hM : 0 < ts.prod := by rw [hpow]; exact Nat.two_pow_pos _
    exact Nat.mul_pos (Nat.mul_pos two_pos (Nat.two_pow_pos _)) hM
  have hNw : 2 * 2 ^ ℓ * ts.prod * w = V := by rw [hV]; ring
  have hwV : w ≤ V := by rw [← hNw]; exact Nat.le_mul_of_pos_left _ hN1
  have hpV : p ≤ V := by omega
  have hdV : d ≤ C * V := hdCw.trans (Nat.mul_le_mul_left _ hwV)
  have hones : ∀ s, s ≤ Nat.log 2 ts.prod → 2 * 2 ^ ℓ * 2 ^ s ≤ V := by
    intro s hs
    have h1 : 2 ^ s ≤ ts.prod := by rw [hpow]; exact Nat.pow_le_pow_right (by norm_num) hs
    calc 2 * 2 ^ ℓ * 2 ^ s ≤ 2 * 2 ^ ℓ * ts.prod := Nat.mul_le_mul_left _ h1
      _ ≤ 2 * 2 ^ ℓ * ts.prod * w := Nat.le_mul_of_pos_right _ hw
      _ = V := hNw
  have hbig : 32 * (C + P.Cw + 1) * p ≤ 32 * (C + P.Cw + 1) * V := Nat.mul_le_mul_left _ hpV
  have e : (32 * (C + P.Cw + 1) + C + 8) * V = 32 * (C + P.Cw + 1) * V + C * V + 8 * V := by ring
  rw [e]
  have hV1 : 1 ≤ V := le_trans hw hwV
  by_cases h1 : h < (ℓ - 1) % K
  · simp only [hadWords, h1, if_true, clen_cons, clen_nil, length_ones, List.length_cons, List.length_nil]
    have := hones _ (prefixBase_le hlay h1)
    omega
  · by_cases h2 : h < ℓ - 1
    · simp only [hadWords, h1, h2, if_true, if_false, clen_cons, clen_nil, List.length_cons, List.length_nil]
      have := hhdr (by omega) h2
      omega
    · simp only [hadWords, h1, h2, if_false, clen_cons, clen_nil, length_ones, List.length_cons, List.length_nil]
      have := hones (topBase ts.length ℓ K) (by unfold topBase; omega)
      have hLD := longs_length_le ts ℓ
      omega

theorem twWords_arith {C n r w M E L : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hwr : w ≤ r) (hM : 1 ≤ M)
    (hnC : n ≤ C * w) (hE : E ≤ C * w) (hL : L ≤ E * (2 * n + 4 * r + 3)) :
    3 * E + 1 + L ≤ (C * (2 * C + 7) + 3 * C + 1) * (2 * r * w * M) := by
  have hsum : 2 * n + 4 * r + 3 ≤ (2 * C + 7) * r := by
    have h1 : n ≤ C * r := hnC.trans (Nat.mul_le_mul_left _ hwr)
    have : (2 * C + 7) * r = 2 * (C * r) + 7 * r := by ring
    omega
  have hrw : r * w ≤ 2 * r * w * M := by
    calc r * w = 1 * r * w * 1 := by ring
      _ ≤ 2 * r * w * M := by gcongr <;> omega
  have h1 : E * (2 * n + 4 * r + 3) ≤ C * (2 * C + 7) * (2 * r * w * M) := by
    calc E * (2 * n + 4 * r + 3) ≤ C * w * ((2 * C + 7) * r) := Nat.mul_le_mul hE hsum
      _ = C * (2 * C + 7) * (r * w) := by ring
      _ ≤ C * (2 * C + 7) * (2 * r * w * M) := Nat.mul_le_mul_left _ hrw
  have hwV : w ≤ 2 * r * w * M := by
    calc w = 1 * 1 * w * 1 := by ring
      _ ≤ 2 * r * w * M := by gcongr <;> omega
  have h2 : 3 * E ≤ 3 * C * (2 * r * w * M) := by
    calc 3 * E ≤ 3 * (C * w) := Nat.mul_le_mul_left _ hE
      _ ≤ 3 * (C * (2 * r * w * M)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hwV)
      _ = 3 * C * (2 * r * w * M) := by ring
  have hV1 : 1 ≤ 2 * r * w * M := le_trans hw hwV
  have e : (C * (2 * C + 7) + 3 * C + 1) * (2 * r * w * M) =
      C * (2 * C + 7) * (2 * r * w * M) + 3 * C * (2 * r * w * M) + 2 * r * w * M := by ring
  rw [e]
  omega

theorem clen_twistWords_le {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) {h : ℕ} (hh : h < ℓ) :
    clen (twistWords (paperPerm (layoutOK_of_admissible hadm)) (2 ^ ℓ) ts h) ≤
      (⌈P.Cl⌉₊ * (2 * ⌈P.Cl⌉₊ + 7) + 3 * ⌈P.Cl⌉₊ + 1) * (2 * 2 ^ ℓ * w * ts.prod) := by
  obtain ⟨hpow, hnC, hdD, hD, hdl, hℓp, hpw, hKℓ, hK, hℓ, hw2, hlow, hnD⟩ := adm_sizes hadm hwr
  have hE : (slotTable (paperPerm (layoutOK_of_admissible hadm)) (2 ^ ℓ) ts (slotAxes ts h) h).length ≤ ⌈P.Cl⌉₊ * w := by
    rw [length_slotTable]
    have h1 : (slotAxes ts h).length * h ≤ ts.length * ℓ :=
      Nat.mul_le_mul (length_slotAxes_le ts h) hh.le
    have h2 : ts.length * ℓ ≤ d * ℓ := Nat.mul_le_mul_right _ (by omega)
    omega
  have hok : TableOK (2 ^ ℓ) (Nat.log 2 ts.prod) (slotTable (paperPerm (layoutOK_of_admissible hadm)) (2 ^ ℓ) ts (slotAxes ts h) h) :=
    slotTable_ok (paperPerm (layoutOK_of_admissible hadm)) _ ts _ h (fun i hi => by
      have hi' : i < ts.length ∧ h < axLen ts i := by
        unfold slotAxes at hi; simpa using hi
      have := axOff_add_len_le (layoutOK_of_admissible hadm).1 hi'.1
      omega)
  have hcl := clen_tableWords_le hok
  unfold twistWords
  rw [clen_cons, length_ones, length_tableWords]
  have hM : 1 ≤ ts.prod := by rw [hpow]; exact Nat.one_le_two_pow
  exact twWords_arith Nat.one_le_two_pow (by omega) hwr hM hnC hE hcl

theorem clen_fwdScript_le {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) :
    clen (fwdScript p d (2 ^ ℓ) w (paperPerm (layoutOK_of_admissible hadm)) ts ℓ K) ≤
      ℓ * (scC ⌈P.Cl⌉₊ P.Cw * (2 * 2 ^ ℓ * w * ts.prod)) := by
  unfold fwdScript
  rw [clen_flatMap]
  have := sum_map_le (List.range ℓ).reverse
    (fun h => clen (hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h ++
      twistWords (paperPerm (layoutOK_of_admissible hadm)) (2 ^ ℓ) ts h))
    (B := scC ⌈P.Cl⌉₊ P.Cw * (2 * 2 ^ ℓ * w * ts.prod)) (fun h hh => by
      have hh' : h < ℓ := by simpa using hh
      rw [clen_append]
      have h1 := clen_hadWords_le hadm hwr h
      have h2 := clen_twistWords_le hadm hwr hh'
      have e : scC ⌈P.Cl⌉₊ P.Cw * (2 * 2 ^ ℓ * w * ts.prod) =
          (32 * (⌈P.Cl⌉₊ + P.Cw + 1) + ⌈P.Cl⌉₊ + 8) * (2 * 2 ^ ℓ * w * ts.prod) +
            (⌈P.Cl⌉₊ * (2 * ⌈P.Cl⌉₊ + 7) + 3 * ⌈P.Cl⌉₊ + 1) * (2 * 2 ^ ℓ * w * ts.prod) := by
        unfold scC; ring
      omega)
  simpa using this

theorem clen_oppScript_le {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) :
    clen (oppScript p d (2 ^ ℓ) w (paperPerm (layoutOK_of_admissible hadm)) ts ℓ K) ≤
      ℓ * (scC ⌈P.Cl⌉₊ P.Cw * (2 * 2 ^ ℓ * w * ts.prod)) := by
  unfold oppScript
  rw [clen_flatMap]
  have := sum_map_le (List.range ℓ)
    (fun h => clen (twistWords (paperPerm (layoutOK_of_admissible hadm)) (2 ^ ℓ) ts h ++
      hadWords p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h))
    (B := scC ⌈P.Cl⌉₊ P.Cw * (2 * 2 ^ ℓ * w * ts.prod)) (fun h hh => by
      have hh' : h < ℓ := by simpa using hh
      rw [clen_append]
      have h1 := clen_hadWords_le hadm hwr h
      have h2 := clen_twistWords_le hadm hwr hh'
      have e : scC ⌈P.Cl⌉₊ P.Cw * (2 * 2 ^ ℓ * w * ts.prod) =
          (32 * (⌈P.Cl⌉₊ + P.Cw + 1) + ⌈P.Cl⌉₊ + 8) * (2 * 2 ^ ℓ * w * ts.prod) +
            (⌈P.Cl⌉₊ * (2 * ⌈P.Cl⌉₊ + 7) + 3 * ⌈P.Cl⌉₊ + 1) * (2 * 2 ^ ℓ * w * ts.prod) := by
        unfold scC; ring
      omega)
  simpa using this

theorem length_layoutOpList (ts : List ℕ) (ℓ K : ℕ) :
    (layoutOpList ts ℓ K).length = (layoutMoves ts ℓ K).length + (layoutSwaps ts ℓ K).length := by
  simp [layoutOpList, moveOps, exOps]

theorem length_undoOpList (ts : List ℕ) (ℓ K : ℕ) :
    (undoOpList ts ℓ K).length = (layoutMoves ts ℓ K).length + (layoutSwaps ts ℓ K).length := by
  simp [undoOpList, backOps, exOps]; ring

theorem ops_word_le {n r w : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) :
    3 * 2 ^ n + 2 ^ n * (2 * r * w) + 2 * n + 9 ≤ 15 * (2 * r * w * 2 ^ n) := by
  have hn : n < 2 ^ n := Nat.lt_two_pow_self
  have h1 : 2 ^ n ≤ 2 * r * w * 2 ^ n := by
    calc 2 ^ n = 1 * 1 * 1 * 2 ^ n := by ring
      _ ≤ 2 * r * w * 2 ^ n := by gcongr <;> omega
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have e : 2 ^ n * (2 * r * w) = 2 * r * w * 2 ^ n := by ring
  omega

theorem clen_layoutWords_le {r w : ℕ} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (hr : 1 ≤ r)
    (hw : 1 ≤ w) :
    clen (layoutWords r w ts ℓ K) ≤
      ((layoutMoves ts ℓ K).length + (layoutSwaps ts ℓ K).length) * (15 * (2 * r * w * 2 ^ addrBits ts)) := by
  unfold layoutWords
  refine (clen_ops_le _ (layoutOpList_ok hL)).trans ?_
  rw [length_layoutOpList]
  exact Nat.mul_le_mul_left _ (ops_word_le hr hw)

theorem clen_undoWords_le {r w : ℕ} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (hr : 1 ≤ r)
    (hw : 1 ≤ w) :
    clen (undoWords r w ts ℓ K) ≤
      ((layoutMoves ts ℓ K).length + (layoutSwaps ts ℓ K).length) * (15 * (2 * r * w * 2 ^ addrBits ts)) := by
  unfold undoWords
  refine (clen_ops_le _ (undoOpList_ok hL)).trans ?_
  rw [length_undoOpList]
  exact Nat.mul_le_mul_left _ (ops_word_le hr hw)

/-- The constant of the transform header. -/
def hdrC (C : ℕ) : ℕ := 5 * C + 15

theorem transformHeader_length_le {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) :
    (transformHeader p d (2 ^ ℓ) K w ts).length ≤ hdrC ⌈P.Cl⌉₊ * (2 * 2 ^ ℓ * w * ts.prod) := by
  obtain ⟨hpow, hnC, hdD, hD, hdl, hℓp, hpw, hKℓ, hK, hℓ, hw2, hlow, hnD⟩ := adm_sizes hadm hwr
  have hax := hadm.2.2.2.2.2.2.2.2.2.2.2.1
  have hdCw : d ≤ ⌈P.Cl⌉₊ * w := by
    have : d ≤ d * ℓ := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hw : 1 ≤ w := by omega
  have hr : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hM : 1 ≤ ts.prod := by rw [hpow]; exact Nat.one_le_two_pow
  obtain ⟨V, hV⟩ : ∃ V, V = 2 * 2 ^ ℓ * w * ts.prod := ⟨_, rfl⟩
  rw [← hV]
  have hrV : 2 ^ ℓ ≤ V := by
    rw [hV]; calc 2 ^ ℓ = 1 * 2 ^ ℓ * 1 * 1 := by ring
      _ ≤ 2 * 2 ^ ℓ * w * ts.prod := by gcongr <;> omega
  have hwV : w ≤ V := by
    rw [hV]; calc w = 1 * 1 * w * 1 := by ring
      _ ≤ 2 * 2 ^ ℓ * w * ts.prod := by gcongr <;> omega
  have hwrV : w * 2 ^ ℓ ≤ V := by
    rw [hV]; calc w * 2 ^ ℓ = 1 * 2 ^ ℓ * w * 1 := by ring
      _ ≤ 2 * 2 ^ ℓ * w * ts.prod := by gcongr <;> omega
  unfold transformHeader
  simp only [List.length_append, List.length_flatMap]
  have g1 := hdrGamma_le p
  have g2 := hdrGamma_le d
  have g3 := hdrGamma_pow ℓ
  have g4 := hdrGamma_le K
  have g5 := hdrGamma_le w
  have hts : (ts.map fun t => (gamma t).length).sum ≤ ts.length * (2 * 2 ^ ℓ + 1) :=
    sum_map_le ts _ (fun t ht => by
      rcases mem_axisLengths hax ht with rfl | rfl
      · rw [hdrGamma_pow]
        have : ℓ - 1 < 2 ^ ℓ := lt_of_le_of_lt (Nat.sub_le _ _) Nat.lt_two_pow_self
        omega
      · rw [hdrGamma_pow]
        have : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
        omega)
  have hℓr : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
  have hD3 : ts.length * (2 * 2 ^ ℓ + 1) ≤ 3 * ⌈P.Cl⌉₊ * V := by
    calc ts.length * (2 * 2 ^ ℓ + 1) ≤ (⌈P.Cl⌉₊ * w) * (3 * 2 ^ ℓ) := Nat.mul_le_mul (by omega) (by omega)
      _ = 3 * ⌈P.Cl⌉₊ * (w * 2 ^ ℓ) := by ring
      _ ≤ 3 * ⌈P.Cl⌉₊ * V := Nat.mul_le_mul_left _ hwrV
  have hdV : d ≤ ⌈P.Cl⌉₊ * V := hdCw.trans (Nat.mul_le_mul_left _ hwV)
  have hV1 : 1 ≤ V := le_trans hw hwV
  have e : hdrC ⌈P.Cl⌉₊ * V = 3 * ⌈P.Cl⌉₊ * V + 2 * (⌈P.Cl⌉₊ * V) + 15 * V := by unfold hdrC; ring
  rw [e]
  omega

end IntegerMultBounds.Schoenhage
