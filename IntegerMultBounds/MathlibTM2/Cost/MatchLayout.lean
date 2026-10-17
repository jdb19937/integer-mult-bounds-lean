module

import IntegerMultBounds.MathlibTM2.Cost.MatchBase
public import IntegerMultBounds.MathlibTM2.Fast.LoadLayoutGen
public import IntegerMultBounds.MathlibTM2.Cost.Total
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# Cost matching: the layout stage

`ldLayGenStage_exec` (`Fast/LoadLayoutGen`) runs the writer of the description streams
(`ldgWriterCost`) and the layout machine (`layBitCost + layXcLoopCost`). At the pipeline
parameters (`D = es.length = d`, `N = es.sum = log₂ T`, `ℓ = ℓ n`, `K = K n`, records of
`B ≤ cw p` symbols, so `V = 2^N B ≤ cw T p` stream symbols) its cost `mtLayCost` is at most a
constant times `T p (d K + p K^{τ-1})`, the `d K` and `p K^{τ-1}` parts of `totConv`
(`mt_lay_stage_le`, and `mt_lay_stage_le_conv` against `totConv`).

* **Single-bit moves** (`ldLayStage_cost_le`): at most `D (b + 1) ≤ d K` moves of
  `layMvCost N B = 2^N (18 B + 20 N + 36) + 8 N + 26 = O(T p)` steps: `O(T p d K)`.
* **Chunk exchanges**: at most `D q - 1` with `q = ⌊(ℓ - 1)/K⌋`, each at most
  `3 C_swap (Tm + 12 swapT t₀ + 5) 2^N B K^τ` plus the bank term `6 · bank` and `O(2^N B)`
  (`layXcStep_le`). The bank of exchange `j` holds the five headers (`mt_lay_hs_le`: at most
  `3 · 2^N B` bits each, being canonical counters of the interchange dimensions) and the other
  bank registers of the input file `R`, which the stage does not touch (`mt_lay_bank_le`); their
  total is a hypothesis (`≤ T B`). So an exchange costs `O(T p K^τ)`, and with
  `D q K ≤ d ℓ ≤ p/3` (`Big.ℓ_bounds`) the exchanges cost `O(T p · p K^{τ-1})`.
* **The writer** is a polynomial of degree `6` in its arguments (`mt_lay_writer_poly`:
  `ldgWriterCost Z … Z (ldxAtoms Z Z Z) ≤ 555210 Z^6`; `mt_lay_writer_mono`). The word condition
  `(N + 1)^N < 2^W` of the stage forces `W > N log₂ (N + 1) ≈ B log B`, so the writer's word size
  is not `O(p)`; with `W ≤ cW p²` every argument is at most `Z = (36 cW + 6 cw + 2) b²` and the
  writer costs `O(b^12) ≤ T p` eventually (`mt_small_le`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds IntegerMultBounds.Machine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-! ### The writer -/

theorem mt_lay_ldxAtoms_mono {N D q N' D' q' : ℕ} (hN : N ≤ N') (hD : D ≤ D') (hq : q ≤ q') :
    ldxAtoms N D q ≤ ldxAtoms N' D' q' := by
  unfold ldxAtoms ldxBodyAtoms ldxEmitAtoms
  gcongr

theorem mt_lay_writer_mono {W N ℓ K D B b len1 lenX KX W' N' ℓ' K' D' B' b' len1' lenX' KX' : ℕ}
    (hW : W ≤ W') (hN : N ≤ N') (hℓ : ℓ ≤ ℓ') (hK : K ≤ K') (hD : D ≤ D') (hB : B ≤ B')
    (hb : b ≤ b') (h1 : len1 ≤ len1') (hX : lenX ≤ lenX') (hKX : KX ≤ KX') :
    ldgWriterCost W N ℓ K D B b len1 lenX KX ≤
      ldgWriterCost W' N' ℓ' K' D' B' b' len1' lenX' KX' := by
  unfold ldgWriterCost ldgRun1Cost ldgRunUCost ldgLoad4Cost tblC ldw1Atoms ldwPart1Atoms
    ldwPart2Atoms ldwP1Atoms ldwP2OAtoms ldwP2Atoms ldwMoveAtoms
  gcongr

/-- The writer at arguments `Z` is at most `555210 Z^6`. -/
theorem mt_lay_writer_poly {Z : ℕ} (hZ : 1 ≤ Z) :
    ldgWriterCost Z Z Z Z Z Z Z Z Z (ldxAtoms Z Z Z) ≤ 555210 * Z ^ 6 := by
  have h1 : Z ≤ Z ^ 6 := Nat.le_self_pow (by norm_num) Z
  have h0 : 1 ≤ Z ^ 6 := Nat.one_le_pow _ _ hZ
  have h2 : Z ^ 2 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ (by norm_num)
  have h3 : Z ^ 3 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ (by norm_num)
  have h4 : Z ^ 4 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ (by norm_num)
  have h5 : Z ^ 5 ≤ Z ^ 6 := Nat.pow_le_pow_right hZ (by norm_num)
  unfold ldgWriterCost ldgRun1Cost ldgRunUCost ldgLoad4Cost tblC ldw1Atoms ldwPart1Atoms
    ldwPart2Atoms ldwP1Atoms ldwP2OAtoms ldwP2Atoms ldwMoveAtoms ldxAtoms ldxBodyAtoms ldxEmitAtoms
  ring_nf
  linarith

/-! ### The bank of an exchange -/

/-- A header of an exchange of the layout has at most `3 · 2^n B` bits: it is the canonical
counter of one of the interchange dimensions `P`, `G`, `E`, `K`, each at most the volume
`P 2^K G 2^K E = 3 · 2^n B`. -/
theorem mt_lay_hs_le {n K B : ℕ} {d : LayXcD} (hd : d.OK n K B) (hB : 0 < B) (k : Fin 5) :
    (d.hs k).length ≤ 3 * (2 ^ n * B) := by
  obtain ⟨hO, hab, hh⟩ := hd
  have hl := mt_length_le_value (hh.2 k)
  rw [hh.1 k] at hl
  simp only [layXcDims] at hl
  have hp : ∀ e : ℕ, 0 < 2 ^ e := fun e => Nat.two_pow_pos e
  obtain ⟨hP, hG, hE⟩ := swapDims_pos (layN0 n K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K
    d.a d.b (hp _) (hp _) (hp _) (hp _)
  have hvol := swapDims_vol (layN0 n K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K d.a d.b hab
    (3 * B)
  rw [lay_rectSize hO] at hvol
  set P := (swapDims (layN0 n K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K d.a d.b).1
  set G := (swapDims (layN0 n K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K d.a d.b).2.1
  set E := (swapDims (layN0 n K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K d.a d.b).2.2
  have hK1 : 0 < 2 ^ K := hp K
  have hKK : K < 2 ^ K := Nat.lt_two_pow_self
  have hE3 : 0 < E * (3 * B) := Nat.mul_pos hE (by omega)
  have e1 : P * 2 ^ K * G * 2 ^ K * (E * (3 * B)) = 3 * (2 ^ n * B) := by rw [hvol]; ring
  have c1 : P ≤ P * 2 ^ K * G * 2 ^ K * (E * (3 * B)) := by
    calc P ≤ P * 2 ^ K := Nat.le_mul_of_pos_right _ hK1
      _ ≤ P * 2 ^ K * G := Nat.le_mul_of_pos_right _ hG
      _ ≤ P * 2 ^ K * G * 2 ^ K := Nat.le_mul_of_pos_right _ hK1
      _ ≤ _ := Nat.le_mul_of_pos_right _ hE3
  have c2 : G ≤ P * 2 ^ K * G * 2 ^ K * (E * (3 * B)) := by
    calc G ≤ P * 2 ^ K * G := Nat.le_mul_of_pos_left _ (Nat.mul_pos hP hK1)
      _ ≤ P * 2 ^ K * G * 2 ^ K := Nat.le_mul_of_pos_right _ hK1
      _ ≤ _ := Nat.le_mul_of_pos_right _ hE3
  have c3 : E * (3 * B) ≤ P * 2 ^ K * G * 2 ^ K * (E * (3 * B)) :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hP hK1) hG) hK1)
  have c4 : K ≤ P * 2 ^ K * G * 2 ^ K * (E * (3 * B)) := by
    calc K ≤ 2 ^ K := hKK.le
      _ ≤ P * 2 ^ K := Nat.le_mul_of_pos_left _ hP
      _ ≤ P * 2 ^ K * G := Nat.le_mul_of_pos_right _ hG
      _ ≤ P * 2 ^ K * G * 2 ^ K := Nat.le_mul_of_pos_right _ hK1
      _ ≤ _ := Nat.le_mul_of_pos_right _ hE3
  rw [e1] at c1 c2 c3 c4
  fin_cases k <;> simp [BinaryInterchangeRun.values] at hl ⊢ <;> omega

/-- The writer's output file agrees with its input on the layout registers other than `cM`,
`cX`. -/
theorem mt_lay_post_rg {T t₀ Ka : ℕ} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}
    (hl : LdlRegs rg lr) (R : Fin T → List (Fin (prime + Ka + 4))) (es : List ℕ) (ℓ K B : ℕ)
    (xs : List LayXcD) {x : LayReg t₀} (h1 : x ≠ .cM) (h2 : x ≠ .cX) :
    ldgPost rg lr R es ℓ K B xs (rg x) = R (rg x) := by
  simp [ldgPost, hl.rl, hl.rg_inj.eq_iff, h1, h2]

/-- **The bank of exchange `j`**: the bank registers of the loader file before exchange `j`
hold the five headers of the exchange (at most `Hm` bits each, plus the separator) or the
contents of the base file `R₀`. -/
theorem mt_lay_bank_le {T t₀ A : ℕ} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}
    (hl : LdlRegs rg lr) {hd : Fin 5 → Fin t₀} (hi : Function.Injective hd)
    (R₀ : Fin T → List (Fin (A + 4))) (n w : ℕ) (bs : List (ℕ × ℕ)) (xs : List LayXcD)
    (j Hm : ℕ) (hH : ∀ k, ((xs.getD j default).hs k).length ≤ Hm) :
    ∑ i, (ldlW rg lr hd A n w R₀ bs xs (bs.length + (j + 1)) (rg (.sw i))).length ≤
      ∑ i, (R₀ (rg (.sw i))).length + swapT t₀ * (Hm + 1) := by
  have hpt : ∀ i, (ldlW rg lr hd A n w R₀ bs xs (bs.length + (j + 1)) (rg (.sw i))).length ≤
      (R₀ (rg (.sw i))).length + (Hm + 1) := by
    intro i
    rw [ldlW_X]
    simp only [ldlWX]
    rw [Function.update_of_ne (hl.disj _ _), ldlSetH_apply hl.rg_inj hi]
    split_ifs with hy
    · simp only [List.length_cons, List.length_map]
      have := hH hy.choose
      omega
    · have e : ldlWM rg lr A n R₀ bs bs.length (rg (.sw i)) = R₀ (rg (.sw i)) := by
        rcases Nat.eq_zero_or_pos bs.length with h0 | h0
        · rw [h0]; rfl
        · obtain ⟨m, hm⟩ : ∃ m, bs.length = m + 1 := ⟨bs.length - 1, by omega⟩
          rw [hm]
          simp [ldlWM, hl.rg_inj.eq_iff, hl.rl]
      rw [e]
      omega
  calc ∑ i, (ldlW rg lr hd A n w R₀ bs xs (bs.length + (j + 1)) (rg (.sw i))).length ≤
        ∑ i, ((R₀ (rg (.sw i))).length + (Hm + 1)) := Finset.sum_le_sum fun i _ => hpt i
    _ = ∑ i, (R₀ (rg (.sw i))).length + swapT t₀ * (Hm + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]

/-! ### Real arithmetic of the bound -/

/-- One exchange with its loader against `T p K^τ`. -/
theorem mt_lay_xr_le {Tr Pr Kτ N B V cw sw Tm s X : ℝ} (hTr : 1 ≤ Tr) (hPr : 1 ≤ Pr)
    (hK : 1 ≤ Kτ) (hN : N ≤ Pr) (hB : B ≤ cw * Pr) (hV : V ≤ cw * (Tr * Pr)) (hsw : 0 ≤ sw)
    (hTm : 0 ≤ Tm) (hcw : 0 ≤ cw) (hs : 0 ≤ s)
    (hX : X ≤ 3 * s * (Tm + 12 * sw + 5) * V * Kτ +
      (6 * (V + sw * (3 * V + 1)) + 34 * V + 2 * Tm + 6 * sw + 23) + 1) :
    60 * (N + B + 2) + 80 + X ≤
      (3 * s * (Tm + 12 * sw + 5) * cw + 60 * (cw + 3) + 81 + 6 * (cw + sw * (3 * cw + 1)) +
        34 * cw + 2 * Tm + 6 * sw + 23) * (Tr * Pr * Kτ) := by
  have hTP : 1 ≤ Tr * Pr := by nlinarith
  have hN' : N ≤ Tr * Pr := by nlinarith
  have hB' : B ≤ cw * (Tr * Pr) := by
    have := mul_le_mul_of_nonneg_left (show Pr ≤ Tr * Pr by nlinarith) hcw
    linarith
  have hsw' : sw ≤ sw * (Tr * Pr) := by nlinarith
  have hTm' : Tm ≤ Tm * (Tr * Pr) := by nlinarith
  have hswV : sw * V ≤ sw * (cw * (Tr * Pr)) := mul_le_mul_of_nonneg_left hV hsw
  have hc : 0 ≤ 60 * (cw + 3) + 81 + 6 * (cw + sw * (3 * cw + 1)) + 34 * cw + 2 * Tm + 6 * sw + 23 := by
    positivity
  have hS : 0 ≤ 3 * s * (Tm + 12 * sw + 5) := by positivity
  have h1 : 60 * (N + B + 2) + 81 + (6 * (V + sw * (3 * V + 1)) + 34 * V + 2 * Tm + 6 * sw + 23) ≤
      (60 * (cw + 3) + 81 + 6 * (cw + sw * (3 * cw + 1)) + 34 * cw + 2 * Tm + 6 * sw + 23) *
        (Tr * Pr) := by
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left (show Tr * Pr ≤ Tr * Pr * Kτ by nlinarith) hc
  have h3 : 3 * s * (Tm + 12 * sw + 5) * V * Kτ ≤ 3 * s * (Tm + 12 * sw + 5) * cw * (Tr * Pr * Kτ) := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hV (by linarith : (0 : ℝ) ≤ Kτ)) hS
    calc _ = 3 * s * (Tm + 12 * sw + 5) * (V * Kτ) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  nlinarith

/-- The `D q` exchanges against `T p · p K^{τ-1}`, from `q K ≤ ℓ`, `d ℓ ≤ p` and
`K^τ = K · K^{τ-1}`. -/
theorem mt_lay_exch_le {D q Kr L Pr Kτ Kτ1 Y Z : ℝ} (hD0 : 0 ≤ D) (hq0 : 0 ≤ q)
    (hqK : q * Kr ≤ L) (hDL : D * L ≤ Pr) (hKe : Kτ = Kr * Kτ1) (hKτ1 : 0 ≤ Kτ1)
    (hY : Y ≤ Z * Kτ) (hZ : 0 ≤ Z) : D * q * Y ≤ Z * (Pr * Kτ1) := by
  have h1 := mul_le_mul_of_nonneg_left hY (mul_nonneg hD0 hq0)
  have h3 : D * (q * Kr) ≤ D * L := mul_le_mul_of_nonneg_left hqK hD0
  have h4 := mul_le_mul_of_nonneg_right (h3.trans hDL) hKτ1
  have h5 := mul_le_mul_of_nonneg_left h4 hZ
  calc D * q * Y ≤ D * q * (Z * Kτ) := h1
    _ = Z * (D * (q * Kr) * Kτ1) := by rw [hKe]; ring
    _ ≤ Z * (Pr * Kτ1) := h5

/-! ### The stage -/

/-- The step bound of `ldLayGenStage_exec` (the writer, then the layout machine) on a host of
`Tm` stacks, for the axis widths `es`, round width `ℓ`, chunk width `K`, records of `B` symbols,
table word size `W`, input file `R`. -/
noncomputable def mtLayCost (Tm t₀ Ka : ℕ) (rg : LayReg t₀ → Fin Tm) (lr : LdlReg → Fin Tm)
    (hd : Fin 5 → Fin t₀) (R : Fin Tm → List (Fin (prime + Ka + 4))) (es : List ℕ)
    (ℓ K B W : ℕ) : ℕ :=
  ldgWriterCost W es.sum ℓ K es.length B (layB ℓ K) (layBits es ℓ K).length
      (layXcs es ℓ K B).length (ldxAtoms es.sum es.length (layQ ℓ K)) +
    (layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es ℓ K).length +
      layXcLoopCost Tm t₀ es.sum K B rg
        (fun j => ldlW rg lr hd (prime + Ka) es.sum (es.sum + B + 2)
          (ldgPost rg lr R es ℓ K B (layXcs es ℓ K B)) (layBits es ℓ K) (layXcs es ℓ K B)
          ((layBits es ℓ K).length + j))
        (fun _ => 60 * (es.sum + B + 2) + 75) (layXcs es ℓ K B))

/-- The constant of one exchange against `T p K^τ`. -/
noncomputable def mtLayC2 (Tm t₀ cw : ℕ) : ℝ :=
  3 * swapConst * ((Tm : ℝ) + 12 * swapT t₀ + 5) * cw + 60 * ((cw : ℝ) + 3) + 81 +
    6 * ((cw : ℝ) + swapT t₀ * (3 * cw + 1)) + 34 * cw + 2 * Tm + 6 * swapT t₀ + 23

theorem mt_lay_C2_nonneg (Tm t₀ cw : ℕ) : 0 ≤ mtLayC2 Tm t₀ cw := by
  have := mt_swapConst_nonneg
  unfold mtLayC2
  positivity

/-- **The layout stage against `totConv`.** At the pipeline parameters (`es.length = d`,
`es.sum = log₂ T`, `ℓ = ℓ n`, `K = K n`), records of `1 ≤ B ≤ cw p` symbols, a writer word size
`W ≤ cW p²`, and the bank registers of the input file holding at most `T B` symbols, the cost of
`ldLayGenStage_exec` is at most `C · T p (d K + p K^{τ-1})`, with
`C = 18 cw + 130 + mtLayC2 Tm t₀ cw`. -/
theorem mt_lay_stage_le (Tm t₀ Ka cw cW : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ (es : List ℕ) (B W : ℕ) (rg : LayReg t₀ → Fin Tm)
      (lr : LdlReg → Fin Tm) (hd : Fin 5 → Fin t₀) (R : Fin Tm → List (Fin (prime + Ka + 4))),
      LayHyp es (ℓ n) (K n) → LdlRegs rg lr → Function.Injective hd →
      es.length = d n → es.sum = logT n → 1 ≤ B → B ≤ cw * p n → W ≤ cW * p n ^ 2 →
      ∑ j, (R (rg (.sw j))).length ≤ T n * B →
      (mtLayCost Tm t₀ Ka rg lr hd R es (ℓ n) (K n) B W : ℝ) ≤
        C * ((T n : ℝ) * p n * ((d n : ℝ) * K n + (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1))) := by
  set C2 := mtLayC2 Tm t₀ cw with hC2def
  have hC2 : 0 ≤ C2 := mt_lay_C2_nonneg Tm t₀ cw
  set cZ := 36 * cW + 6 * cw + 2 with hcZ
  refine ⟨18 * cw + 130 + C2, by positivity, ?_⟩
  filter_upwards [eventually_big, gr_one_le_K, mt_small_le (555210 * cZ ^ 6) 12] with n h hK1 hsmall
  intro es B W rg lr hd R H hl hi hD hN hB1 hBc hW hbank
  -- sizes
  have hb16 := h.sixteen_le_b
  have hpb : p n = 6 * b n := rfl
  have hT2 : 2 ^ es.sum = T n := by rw [hN]; rfl
  have hTpos : 1 ≤ T n := Nat.one_le_two_pow
  have hNb : es.sum ≤ b n := hN ▸ mt_logT_le_b h
  have hdb : d n ≤ b n := mt_d_le_b n
  have hℓb : ℓ n ≤ b n := mt_ℓ_le_b h
  have hKb : K n ≤ b n := mt_K_le_b n
  have hbK : layB (ℓ n) (K n) + 1 ≤ K n := H.b_lt
  have hq : layQ (ℓ n) (K n) * K n ≤ ℓ n := by
    unfold layQ
    exact (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  have hqℓ : layQ (ℓ n) (K n) ≤ ℓ n := by
    have : layQ (ℓ n) (K n) ≤ layQ (ℓ n) (K n) * K n := Nat.le_mul_of_pos_right _ hK1
    omega
  obtain ⟨c1, c2⟩ := layMoves_counts (es := es) (ℓ := ℓ n) (K := K n)
  rw [layPreMoves, layPreMovesK, List.length_map, List.length_range] at c1
  have hlen1 : (layBits es (ℓ n) (K n)).length ≤ es.length * (layB (ℓ n) (K n) + 1) := by
    rw [length_layBits]; exact c1
  have hlenX : (layXcs es (ℓ n) (K n) B).length ≤ es.length * layQ (ℓ n) (K n) := by
    rw [length_layXcs]; omega
  have h3dℓ : 3 * d n * ℓ n ≤ p n := h.ℓ_bounds.2
  -- the writer
  have hwr : (ldgWriterCost W es.sum (ℓ n) (K n) es.length B (layB (ℓ n) (K n))
      (layBits es (ℓ n) (K n)).length (layXcs es (ℓ n) (K n) B).length
      (ldxAtoms es.sum es.length (layQ (ℓ n) (K n))) : ℝ) ≤ (T n : ℝ) * p n := by
    apply hsmall
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = cZ * b n ^ 2 := ⟨_, rfl⟩
    have hb2 : b n ≤ b n ^ 2 := Nat.le_self_pow two_ne_zero _
    have hZe : Z = 36 * cW * b n ^ 2 + 6 * cw * b n ^ 2 + 2 * b n ^ 2 := by rw [hZ, hcZ]; ring
    have hZ2 : b n ^ 2 ≤ Z := by rw [hZe]; omega
    have hbZ : b n ≤ Z := hb2.trans hZ2
    have hbbZ : b n * b n ≤ Z := by rw [← sq]; exact hZ2
    have hBZ : B ≤ Z := by
      have h6 : 6 * cw * b n ≤ 6 * cw * b n ^ 2 := Nat.mul_le_mul_left _ hb2
      have : B ≤ 6 * cw * b n := by
        calc B ≤ cw * p n := hBc
          _ = 6 * cw * b n := by rw [hpb]; ring
      rw [hZe]; omega
    have hWZ : W ≤ Z := by
      have : W ≤ 36 * cW * b n ^ 2 := by
        calc W ≤ cW * p n ^ 2 := hW
          _ = 36 * cW * b n ^ 2 := by rw [hpb]; ring
      rw [hZe]; omega
    have hD' : es.length ≤ b n := hD ▸ hdb
    have h1Z : (layBits es (ℓ n) (K n)).length ≤ Z := by
      refine hlen1.trans (le_trans ?_ hbbZ)
      exact Nat.mul_le_mul hD' (hbK.trans hKb)
    have hXZ : (layXcs es (ℓ n) (K n) B).length ≤ Z := by
      refine hlenX.trans (le_trans ?_ hbbZ)
      exact Nat.mul_le_mul hD' (hqℓ.trans hℓb)
    have hZ1 : 1 ≤ Z := by omega
    have hm := mt_lay_writer_mono (W' := Z) (N' := Z) (ℓ' := Z) (K' := Z) (D' := Z) (B' := Z)
      (b' := Z) (len1' := Z) (lenX' := Z) (KX' := ldxAtoms Z Z Z) hWZ (hNb.trans hbZ)
      (hℓb.trans hbZ) (hKb.trans hbZ) (hD'.trans hbZ) hBZ
      (show layB (ℓ n) (K n) ≤ Z by omega) h1Z hXZ
      (mt_lay_ldxAtoms_mono (hNb.trans hbZ) (hD'.trans hbZ) ((hqℓ.trans hℓb).trans hbZ))
    have hp := mt_lay_writer_poly hZ1
    have hr : 1 ≤ r n := Nat.one_le_two_pow
    have e : 555210 * Z ^ 6 = 555210 * cZ ^ 6 * b n ^ 12 := by rw [hZ]; ring
    calc _ ≤ 555210 * Z ^ 6 := hm.trans hp
      _ = 555210 * cZ ^ 6 * b n ^ 12 := e
      _ ≤ 555210 * cZ ^ 6 * b n ^ 12 * r n := Nat.le_mul_of_pos_right _ hr
  -- one exchange
  obtain ⟨V, hV⟩ : ∃ V, V = 2 ^ es.sum * B := ⟨_, rfl⟩
  have hVT : V = T n * B := by rw [hV, hT2]
  obtain ⟨Xr, hXr⟩ : ∃ x : ℝ, x = 3 * swapConst * ((Tm + 12 * swapT t₀ + 5 : ℕ) : ℝ) * (V : ℝ) *
      (K n : ℝ) ^ Parameters.tau +
      ((6 * (V + swapT t₀ * (3 * V + 1)) + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hXs : ∀ j < (layXcs es (ℓ n) (K n) B).length,
      layXcStep Tm t₀ es.sum (K n) B rg
        (ldlW rg lr hd (prime + Ka) es.sum (es.sum + B + 2)
          (ldgPost rg lr R es (ℓ n) (K n) B (layXcs es (ℓ n) (K n) B)) (layBits es (ℓ n) (K n))
          (layXcs es (ℓ n) (K n) B) ((layBits es (ℓ n) (K n)).length + (j + 1)))
        ((layXcs es (ℓ n) (K n) B).getD j default) ≤ ⌈Xr⌉₊ := by
    intro j hj
    have hok : ((layXcs es (ℓ n) (K n) B).getD j default).OK es.sum (K n) B := by
      rw [List.getD_eq_getElem _ _ hj]
      exact layXcs_OK B H _ (List.getElem_mem hj)
    have hs := layXcStep_le Tm t₀ es.sum (K n) B rg
      (ldlW rg lr hd (prime + Ka) es.sum (es.sum + B + 2)
          (ldgPost rg lr R es (ℓ n) (K n) B (layXcs es (ℓ n) (K n) B)) (layBits es (ℓ n) (K n))
          (layXcs es (ℓ n) (K n) B) ((layBits es (ℓ n) (K n)).length + (j + 1))) hok (by omega)
    have hbk := mt_lay_bank_le hl hi
      (ldgPost rg lr R es (ℓ n) (K n) B (layXcs es (ℓ n) (K n) B)) es.sum (es.sum + B + 2)
      (layBits es (ℓ n) (K n)) (layXcs es (ℓ n) (K n) B) j (3 * V)
      (fun k => hV ▸ mt_lay_hs_le hok (by omega) k)
    have hR0 : ∑ i, (ldgPost rg lr R es (ℓ n) (K n) B (layXcs es (ℓ n) (K n) B)
        (rg (.sw i))).length = ∑ i, (R (rg (.sw i))).length := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mt_lay_post_rg hl R es (ℓ n) (K n) B _ (by simp) (by simp)]
    rw [hR0] at hbk
    have hmax : max 1 (K n) = K n := max_eq_right hK1
    rw [hmax, ← hV] at hs
    generalize (∑ i, (ldlW rg lr hd (prime + Ka) es.sum (es.sum + B + 2)
          (ldgPost rg lr R es (ℓ n) (K n) B (layXcs es (ℓ n) (K n) B)) (layBits es (ℓ n) (K n))
          (layXcs es (ℓ n) (K n) B) ((layBits es (ℓ n) (K n)).length + (j + 1))
          (rg (.sw i))).length) = bk at hs hbk
    have hnat : 6 * bk + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 ≤
        6 * (V + swapT t₀ * (3 * V + 1)) + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 := by
      rw [hVT]; rw [hVT] at hbk; omega
    have hnat' : ((6 * bk + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 : ℕ) : ℝ) ≤
        ((6 * (V + swapT t₀ * (3 * V + 1)) + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hle : (layXcStep Tm t₀ es.sum (K n) B rg
        (ldlW rg lr hd (prime + Ka) es.sum (es.sum + B + 2)
          (ldgPost rg lr R es (ℓ n) (K n) B (layXcs es (ℓ n) (K n) B)) (layBits es (ℓ n) (K n))
          (layXcs es (ℓ n) (K n) B) ((layBits es (ℓ n) (K n)).length + (j + 1)))
        ((layXcs es (ℓ n) (K n) B).getD j default) : ℝ) ≤ Xr := by
      rw [hXr]
      linarith
    exact Nat.cast_le.1 (hle.trans (Nat.le_ceil Xr))
  have hst := ldLayStage_cost_le (lr := lr)
    (ldgPost rg lr R es (ℓ n) (K n) B (layXcs es (ℓ n) (K n) B)) hd (es.sum + B + 2) ⌈Xr⌉₊ hXs
  -- the natural-number bound
  have hNp : es.sum ≤ p n := by rw [hpb]; omega
  have hA1 : es.length * (layB (ℓ n) (K n) + 1) ≤ d n * K n := Nat.mul_le_mul hD.le hbK
  have hA2 : 14 * es.sum + 12 + layMvCost es.sum B + 5 ≤ (18 * cw + 121) * (T n * p n) := by
    unfold layMvCost
    rw [hT2]
    have hp1 : 1 ≤ p n := by omega
    have hcp : 18 * B ≤ 18 * (cw * p n) := Nat.mul_le_mul_left _ hBc
    have e1 : 18 * B + 20 * es.sum + 36 ≤ (18 * cw + 56) * p n := by
      have : (18 * cw + 56) * p n = 18 * (cw * p n) + 20 * p n + 36 * p n := by ring
      rw [this]; omega
    have e2 : T n * (18 * B + 20 * es.sum + 36) ≤ T n * ((18 * cw + 56) * p n) :=
      Nat.mul_le_mul_left _ e1
    have e3 : 22 * es.sum + 43 ≤ 65 * (T n * p n) := by
      have : p n ≤ T n * p n := Nat.le_mul_of_pos_left _ hTpos
      omega
    calc _ = T n * (18 * B + 20 * es.sum + 36) + (22 * es.sum + 43) := by ring
      _ ≤ T n * ((18 * cw + 56) * p n) + 65 * (T n * p n) := Nat.add_le_add e2 e3
      _ = (18 * cw + 121) * (T n * p n) := by ring
  have hA := Nat.mul_le_mul hA1 hA2
  have hB' : (es.length * layQ (ℓ n) (K n) - 1) * (60 * (es.sum + B + 2) + 75 + ⌈Xr⌉₊ + 5) ≤
      es.length * layQ (ℓ n) (K n) * (60 * (es.sum + B + 2) + 80 + ⌈Xr⌉₊) := by
    have : 60 * (es.sum + B + 2) + 75 + ⌈Xr⌉₊ + 5 = 60 * (es.sum + B + 2) + 80 + ⌈Xr⌉₊ := by ring
    rw [this]; exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hN1 := hst.trans (Nat.add_le_add (Nat.add_le_add hA hB') (le_refl 8))
  have hR1 := (Nat.cast_le (α := ℝ)).2 hN1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hR1
  -- real facts
  have hTr1 : (1 : ℝ) ≤ T n := mt_one_le_T n
  have hPr1 : (1 : ℝ) ≤ p n := mt_one_le_p h
  have hKr1 : (1 : ℝ) ≤ K n := by exact_mod_cast hK1
  have hDr1 : (1 : ℝ) ≤ d n := by exact_mod_cast h.one_le_d
  have hKr0 : (0 : ℝ) < K n := by linarith only [hKr1]
  have hKτ : (1 : ℝ) ≤ (K n : ℝ) ^ Parameters.tau := Real.one_le_rpow hKr1 tot_tau_nonneg
  have hKτ1 : (0 : ℝ) ≤ (K n : ℝ) ^ (Parameters.tau - 1) := Real.rpow_nonneg hKr0.le _
  have hKτe : (K n : ℝ) ^ Parameters.tau = (K n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) := by
    rw [Real.rpow_sub_one hKr0.ne']
    field_simp
  have hqK : (layQ (ℓ n) (K n) : ℝ) * K n ≤ ℓ n := by exact_mod_cast hq
  have hdℓ : (d n : ℝ) * ℓ n ≤ p n := by
    have h1 : (3 * d n * ℓ n : ℝ) ≤ p n := by exact_mod_cast h3dℓ
    have h2 : (0 : ℝ) ≤ (d n : ℝ) * ℓ n := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith only [h1, h2]
  have hBr : (B : ℝ) ≤ cw * p n := by exact_mod_cast hBc
  have hVr : (V : ℝ) ≤ cw * ((T n : ℝ) * p n) := by
    have h1 : (V : ℝ) = T n * B := by rw [hVT]; push_cast; ring
    have h2 := mul_le_mul_of_nonneg_left hBr (Nat.cast_nonneg (α := ℝ) (T n))
    rw [h1]
    linarith only [h2]
  have hNr : (es.sum : ℝ) ≤ p n := by exact_mod_cast hNp
  have hXr0 : 0 ≤ Xr := by
    rw [hXr]
    have := mt_swapConst_nonneg
    have : (0 : ℝ) ≤ (K n : ℝ) ^ Parameters.tau := by linarith only [hKτ]
    positivity
  have hceil : (⌈Xr⌉₊ : ℝ) ≤ Xr + 1 := (Nat.ceil_lt_add_one hXr0).le
  have hXrb : 60 * ((es.sum : ℝ) + B + 2) + 80 + (⌈Xr⌉₊ : ℝ) ≤
      C2 * ((T n : ℝ) * p n * (K n : ℝ) ^ Parameters.tau) := by
    rw [hC2def, mtLayC2]
    refine mt_lay_xr_le hTr1 hPr1 hKτ hNr hBr hVr (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) mt_swapConst_nonneg ?_
    calc (⌈Xr⌉₊ : ℝ) ≤ Xr + 1 := hceil
      _ = _ := by rw [hXr]; simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have hTP0 : (0 : ℝ) ≤ (T n : ℝ) * p n := by
    have := mul_le_mul hTr1 hPr1 zero_le_one (by linarith only [hTr1]); linarith only [this]
  have hexch : (es.length : ℝ) * layQ (ℓ n) (K n) * (60 * ((es.sum : ℝ) + B + 2) + 80 + ⌈Xr⌉₊) ≤
      C2 * ((T n : ℝ) * p n) * ((p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1)) := by
    have hDe : (es.length : ℝ) = d n := by exact_mod_cast hD
    rw [hDe]
    refine mt_lay_exch_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) hqK hdℓ hKτe hKτ1 ?_
      (mul_nonneg hC2 hTP0)
    rw [mul_assoc]
    exact hXrb
  -- assembly
  have hDK : (1 : ℝ) ≤ (d n : ℝ) * K n := by nlinarith only [hDr1, hKr1]
  have hX1 : (T n : ℝ) * p n ≤ (T n : ℝ) * p n * ((d n : ℝ) * K n) := by
    nlinarith only [hDK, hTP0]
  have hX2 : (0 : ℝ) ≤ (T n : ℝ) * p n * ((p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1)) :=
    mul_nonneg hTP0 (mul_nonneg (by linarith only [hPr1]) hKτ1)
  have hX10 : (0 : ℝ) ≤ (T n : ℝ) * p n * ((d n : ℝ) * K n) := by linarith only [hX1, hTP0]
  have hTP1 : (1 : ℝ) ≤ (T n : ℝ) * p n := by nlinarith only [hTr1, hPr1]
  have hcost : (mtLayCost Tm t₀ Ka rg lr hd R es (ℓ n) (K n) B W : ℝ) =
      (ldgWriterCost W es.sum (ℓ n) (K n) es.length B (layB (ℓ n) (K n))
        (layBits es (ℓ n) (K n)).length (layXcs es (ℓ n) (K n) B).length
        (ldxAtoms es.sum es.length (layQ (ℓ n) (K n))) : ℝ) +
      ((layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es (ℓ n) (K n)).length +
        layXcLoopCost Tm t₀ es.sum (K n) B rg
        (fun j => ldlW rg lr hd (prime + Ka) es.sum (es.sum + B + 2)
          (ldgPost rg lr R es (ℓ n) (K n) B (layXcs es (ℓ n) (K n) B)) (layBits es (ℓ n) (K n))
          (layXcs es (ℓ n) (K n) B) ((layBits es (ℓ n) (K n)).length + j))
        (fun _ => 60 * (es.sum + B + 2) + 75) (layXcs es (ℓ n) (K n) B) : ℕ) : ℝ) := by
    unfold mtLayCost; rw [Nat.cast_add]
  rw [hcost]
  have hTPY : (0 : ℝ) ≤ (T n : ℝ) * p n * ((p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1)) := hX2
  have hcwY : (0 : ℝ) ≤ (cw : ℝ) * ((T n : ℝ) * p n * ((p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1))) :=
    mul_nonneg (Nat.cast_nonneg _) hX2
  have hC2X : (0 : ℝ) ≤ C2 * ((T n : ℝ) * p n * ((d n : ℝ) * K n)) := mul_nonneg hC2 hX10
  have h8 : (8 : ℝ) ≤ 8 * ((T n : ℝ) * p n * ((d n : ℝ) * K n)) := by
    linarith only [hX1, hTP1]
  have hbit : (d n : ℝ) * K n * ((18 * cw + 121) * ((T n : ℝ) * p n)) =
      (18 * cw + 121) * ((T n : ℝ) * p n * ((d n : ℝ) * K n)) := by ring
  have hgoal : C2 * ((T n : ℝ) * p n) * ((p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1)) =
      C2 * ((T n : ℝ) * p n * ((p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1))) := by ring
  have hR : (18 * (cw : ℝ) + 130 + C2) * ((T n : ℝ) * p n * ((d n : ℝ) * K n +
      (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1))) =
      (18 * cw + 121) * ((T n : ℝ) * p n * ((d n : ℝ) * K n)) +
        9 * ((T n : ℝ) * p n * ((d n : ℝ) * K n)) +
        C2 * ((T n : ℝ) * p n * ((d n : ℝ) * K n)) +
        18 * ((cw : ℝ) * ((T n : ℝ) * p n * ((p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1)))) +
        130 * ((T n : ℝ) * p n * ((p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1))) +
        C2 * ((T n : ℝ) * p n * ((p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1))) := by ring
  rw [hR, Nat.cast_add]
  rw [hbit] at hR1
  rw [hgoal] at hexch
  linarith only [hR1, hexch, hwr, hX1, h8, hC2X, hcwY, hTPY]

/-- `T p (d K + p K^{τ-1}) ≤ totConv`. -/
theorem mt_lay_le_conv {n : ℕ} (h : Big n) :
    (T n : ℝ) * p n * ((d n : ℝ) * K n + (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1)) ≤
      totConv n := by
  unfold totConv
  have hr : (1 : ℝ) ≤ (r n : ℝ) * p n := one_le_mul_of_one_le_of_one_le (mt_one_le_r n) (mt_one_le_p h)
  have h1 := gr_one_le_logLog hr
  have h2 : (0 : ℝ) ≤ (ℓ n : ℝ) * (d n : ℝ) ^ totLam' :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hTP := mt_Tp_nonneg n
  apply mul_le_mul_of_nonneg_left _ hTP
  linarith

/-- **The layout stage against `totConv`**: the bound of `mt_lay_stage_le` with `totConv n` on
the right. -/
theorem mt_lay_stage_le_conv (Tm t₀ Ka cw cW : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ (es : List ℕ) (B W : ℕ) (rg : LayReg t₀ → Fin Tm)
      (lr : LdlReg → Fin Tm) (hd : Fin 5 → Fin t₀) (R : Fin Tm → List (Fin (prime + Ka + 4))),
      LayHyp es (ℓ n) (K n) → LdlRegs rg lr → Function.Injective hd →
      es.length = d n → es.sum = logT n → 1 ≤ B → B ≤ cw * p n → W ≤ cW * p n ^ 2 →
      ∑ j, (R (rg (.sw j))).length ≤ T n * B →
      (mtLayCost Tm t₀ Ka rg lr hd R es (ℓ n) (K n) B W : ℝ) ≤ C * totConv n := by
  obtain ⟨C, hC, hev⟩ := mt_lay_stage_le Tm t₀ Ka cw cW
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, eventually_big] with n hn h es B W rg lr hd R H hl hi hD hN hB1 hBc hW hbank
  exact (hn es B W rg lr hd R H hl hi hD hN hB1 hBc hW hbank).trans
    (mul_le_mul_of_nonneg_left (mt_lay_le_conv h) hC)

end IntegerMultBounds.MathlibTM2.Cost
