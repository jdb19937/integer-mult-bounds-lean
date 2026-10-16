module

public import IntegerMultBounds.Schoenhage.TransformCost
public import IntegerMultBounds.Schoenhage.TransformGenRun

/-! §6 task 7, `lem:synthetic-transform-cost` from `prop:simultaneous-layer`. The header
generator's own steps are within a fixed multiple of the record volume (`genCost_le`), so with
round-script and layout-script writers within a fixed multiple of the paper's bound, a program
meeting the layer gives two fixed programs meeting the forward and opposite transforms on every
admissible instance (`transformTarget_of_layer`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Spec.SignedRingProduct TwistDescriptors LayoutMachines
open Networks.Shared50ModularControl (prime)

/-! ### The header generator's steps -/

/-- A short bound on the transform header: its codes are of numbers below `w`, `C w` and `2^ℓ`. -/
theorem transformHeader_length_small {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) :
    (transformHeader p d (2 ^ ℓ) K w ts).length ≤ (5 * ⌈P.Cl⌉₊ + 13) * (w * w) := by
  obtain ⟨hpow, hnC, hdD, hD, hdl, hℓp, hpw, hKℓ, hK, hℓ, hw2, hlow, hnD⟩ := adm_sizes hadm hwr
  have hax := hadm.2.2.2.2.2.2.2.2.2.2.2.1
  have hdCw : d ≤ ⌈P.Cl⌉₊ * w := by
    have : d ≤ d * ℓ := Nat.le_mul_of_pos_right _ (by omega)
    omega
  unfold transformHeader
  simp only [List.length_append, List.length_flatMap]
  have g1 := hdrGamma_le p
  have g2 := hdrGamma_le d
  have g3 := hdrGamma_pow ℓ
  have g4 := hdrGamma_le K
  have g5 := hdrGamma_le w
  have hts : (ts.map fun t => (gamma t).length).sum ≤ ts.length * (2 * ℓ + 1) :=
    sum_map_le ts _ (fun t ht => by
      rcases mem_axisLengths hax ht with rfl | rfl <;> rw [hdrGamma_pow]; omega)
  set C := ⌈P.Cl⌉₊
  have hw : 1 ≤ w := by omega
  have hww : w ≤ w * w := Nat.le_mul_of_pos_left _ hw
  have hD3 : ts.length * (2 * ℓ + 1) ≤ 3 * C * (w * w) := by
    calc ts.length * (2 * ℓ + 1) ≤ (C * w) * (3 * w) := Nat.mul_le_mul (by omega) (by omega)
      _ = 3 * C * (w * w) := by ring
  have hCw : C * w ≤ C * (w * w) := Nat.mul_le_mul_left _ hww
  have e : (5 * C + 13) * (w * w) = 3 * C * (w * w) + 2 * (C * (w * w)) + 13 * (w * w) := by ring
  rw [e]
  omega

/-- The constant of the header generator. -/
def genC (C : ℕ) : ℕ := 3000 * (C + 1) ^ 2 * (5 * C + 14) + 10000

set_option maxHeartbeats 4000000 in
theorem gen_arith {p d K l w D n r M H C : ℕ} (hp : p ≤ w) (hd : d ≤ C * w) (hK : K ≤ w) (hl : l ≤ w)
    (hD : D ≤ d) (hn : n ≤ C * w) (hw1 : 1 ≤ w) (hwr : w ≤ r) (hr : r = 2 ^ l) (hrM : r ≤ 2 * M)
    (hM : M = 2 ^ n) (hH : H ≤ (5 * C + 13) * (w * w)) :
    TransformParams.paramsCost p d r K w H D l +
        (6 * w + l * (20 * 2 ^ l * 1 + 70) + 200 * 2 ^ l + 40 * l + D * (3 * (l - 1) + 50) +
          n * (20 * 2 ^ n * 1 + 70) + 10 * 2 ^ n + 20 * n + 800) +
        2 * (p + d + l + K + w + 3 * D) + 60 ≤ genC C * (2 * r * w * M) := by
  subst hr hM
  set r := 2 ^ l
  set M := 2 ^ n
  have hr1 : 1 ≤ r := Nat.one_le_two_pow
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  have hlr : l + 1 ≤ r := Nat.lt_two_pow_self
  set X := r * w * M with hX
  have hwwX : w * w ≤ X := by
    rw [hX]; calc w * w = w * w * 1 := by ring
      _ ≤ r * w * M := by gcongr
  have hwX : w ≤ X := le_trans (Nat.le_mul_of_pos_left _ hw1) hwwX
  have hrX : r ≤ X := by
    rw [hX]; calc r = r * 1 * 1 := by ring
      _ ≤ r * w * M := by gcongr
  have hMX : M ≤ X := by
    rw [hX]; calc M = 1 * 1 * M := by ring
      _ ≤ r * w * M := by gcongr
  have hnMX : n * M ≤ C * X := by
    rw [hX]; calc n * M ≤ C * w * M := Nat.mul_le_mul_right _ hn
      _ = C * (1 * w * M) := by ring
      _ ≤ C * (r * w * M) := by gcongr
  have hlrX : l * r ≤ X := by
    rw [hX]; calc l * r ≤ w * r := Nat.mul_le_mul_right _ hl
      _ = r * w * 1 := by ring
      _ ≤ r * w * M := by gcongr
  have hw3 : w * (w * w) ≤ 2 * X := by
    have : w ≤ 2 * M := hwr.trans hrM
    calc w * (w * w) ≤ w * (w * r) := by gcongr
      _ = r * w * w := by ring
      _ ≤ r * w * (2 * M) := Nat.mul_le_mul_left _ this
      _ = 2 * X := by rw [hX]; ring
  -- sizes of codes
  have sp := size_le_self p
  have sd := size_le_self d
  have sK := size_le_self K
  have sw := size_le_self w
  have sr : Nat.size r = l + 1 := Nat.size_pow
  have hdw : d ≤ C * w := hd
  have hCw : C * w ≤ C * X := Nat.mul_le_mul_left _ hwX
  have hCww : C * (w * w) ≤ C * X := Nat.mul_le_mul_left _ hwwX
  have q1 : Nat.size p * (Nat.size p + p + 10) ≤ 12 * X := by
    calc Nat.size p * (Nat.size p + p + 10) ≤ w * (w + w + 10 * w) := by gcongr <;> omega
      _ = 12 * (w * w) := by ring
      _ ≤ 12 * X := Nat.mul_le_mul_left _ hwwX
  have q2 : Nat.size K * (Nat.size K + K + 10) ≤ 12 * X := by
    calc Nat.size K * (Nat.size K + K + 10) ≤ w * (w + w + 10 * w) := by gcongr <;> omega
      _ = 12 * (w * w) := by ring
      _ ≤ 12 * X := Nat.mul_le_mul_left _ hwwX
  have q3 : Nat.size w * (Nat.size w + w + 10) ≤ 12 * X := by
    calc Nat.size w * (Nat.size w + w + 10) ≤ w * (w + w + 10 * w) := by gcongr; omega
      _ = 12 * (w * w) := by ring
      _ ≤ 12 * X := Nat.mul_le_mul_left _ hwwX
  have q4 : Nat.size d * (Nat.size d + d + 10) ≤ 12 * (C * C) * X := by
    calc Nat.size d * (Nat.size d + d + 10) ≤ (C * w) * (C * w + C * w + 10 * (C * w)) := by
          have : 1 ≤ C * w ∨ d = 0 := by
            rcases Nat.eq_zero_or_pos d with h | h
            · right; exact h
            · left; omega
          rcases this with h | h
          · gcongr <;> omega
          · subst h; simp
      _ = 12 * (C * C) * (w * w) := by ring
      _ ≤ 12 * (C * C) * X := Nat.mul_le_mul_left _ hwwX
  have q5 : Nat.size r * (Nat.size r + r + 10) ≤ 24 * X := by
    rw [sr]
    calc (l + 1) * (l + 1 + r + 10) ≤ (2 * w) * (12 * r) := by gcongr <;> omega
      _ = 24 * (r * w * 1) := by ring
      _ ≤ 24 * X := by rw [hX]; gcongr
  have hHX : H ≤ (5 * C + 13) * X := hH.trans (Nat.mul_le_mul_left _ hwwX)
  have hDH : D * H ≤ 2 * (C * (5 * C + 13)) * X := by
    calc D * H ≤ (C * w) * ((5 * C + 13) * (w * w)) := Nat.mul_le_mul (by omega) hH
      _ = C * (5 * C + 13) * (w * (w * w)) := by ring
      _ ≤ C * (5 * C + 13) * (2 * X) := Nat.mul_le_mul_left _ hw3
      _ = 2 * (C * (5 * C + 13)) * X := by ring
  have hDl : D * (4 * l + 402) ≤ 406 * (C * X) := by
    calc D * (4 * l + 402) ≤ (C * w) * (406 * w) := Nat.mul_le_mul (by omega) (by omega)
      _ = 406 * (C * (w * w)) := by ring
      _ ≤ 406 * (C * X) := Nat.mul_le_mul_left _ hCww
  have hDl2 : D * (3 * (l - 1) + 50) ≤ 53 * (C * X) := by
    calc D * (3 * (l - 1) + 50) ≤ (C * w) * (53 * w) := Nat.mul_le_mul (by omega) (by omega)
      _ = 53 * (C * (w * w)) := by ring
      _ ≤ 53 * (C * X) := Nat.mul_le_mul_left _ hCww
  have hlr2 : l * (20 * r * 1 + 70) ≤ 90 * X := by
    calc l * (20 * r * 1 + 70) = 20 * (l * r) + 70 * l := by ring
      _ ≤ 20 * X + 70 * X := by
        have : l ≤ X := hl.trans hwX
        omega
      _ = 90 * X := by ring
  have hnM2 : n * (20 * M * 1 + 70) ≤ 90 * (C * X) := by
    calc n * (20 * M * 1 + 70) = 20 * (n * M) + 70 * n := by ring
      _ ≤ 20 * (C * X) + 70 * (C * X) := by omega
      _ = 90 * (C * X) := by ring
  have hX1 : 1 ≤ X := le_trans hw1 hwX
  have hCX : C * X ≤ (C + 1) ^ 2 * X := Nat.mul_le_mul_right _ (by nlinarith)
  have hCCX : C * C * X ≤ (C + 1) ^ 2 * X := Nat.mul_le_mul_right _ (by nlinarith)
  have hCCX2 : C * (5 * C + 13) * X ≤ (C + 1) ^ 2 * (5 * C + 14) * X := Nat.mul_le_mul_right _ (by nlinarith)
  have hgen : genC C * (2 * r * w * M) = 2 * (3000 * ((C + 1) ^ 2 * (5 * C + 14) * X) + 10000 * X) := by
    unfold genC; rw [hX]; ring
  rw [hgen]
  unfold TransformParams.paramsCost
  have hb : (C + 1) ^ 2 * X ≤ (C + 1) ^ 2 * (5 * C + 14) * X := by
    have : (C + 1) ^ 2 * X * 1 ≤ (C + 1) ^ 2 * X * (5 * C + 14) := Nat.mul_le_mul_left _ (by omega)
    calc (C + 1) ^ 2 * X = (C + 1) ^ 2 * X * 1 := by ring
      _ ≤ (C + 1) ^ 2 * X * (5 * C + 14) := this
      _ = (C + 1) ^ 2 * (5 * C + 14) * X := by ring
  have hb2 : (5 * C + 13) * X ≤ (C + 1) ^ 2 * (5 * C + 14) * X := by
    have : 5 * C + 13 ≤ (C + 1) ^ 2 * (5 * C + 14) := by nlinarith
    exact Nat.mul_le_mul_right _ this
  set B := (C + 1) ^ 2 * (5 * C + 14) * X
  have e1 : 2 * (C * (5 * C + 13)) * X = 2 * (C * (5 * C + 13) * X) := by ring
  have e2 : 12 * (C * C) * X = 12 * (C * C * X) := by ring
  rw [e1] at hDH
  rw [e2] at q4
  linarith

/-- `genCost_le`: the header generator's own steps are within `genC · V`. -/
theorem genCost_le {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) :
    genCost p d ℓ K w ts ≤ genC ⌈P.Cl⌉₊ * (2 * 2 ^ ℓ * w * ts.prod) := by
  have hL := layoutOK_of_admissible hadm
  obtain ⟨hpow, hnC, hdD, hD, hdl, hℓp, hpw, hKℓ, hK, hℓ, hw2, hlow, hnD⟩ := adm_sizes hadm hwr
  have hH := transformHeader_length_small hadm hwr
  have hdCw : d ≤ ⌈P.Cl⌉₊ * w := by
    have : d ≤ d * ℓ := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hfs := flagSum_lengthFlags hL
  have hfl : (TransformParams.lengthFlags ℓ ts).length = ts.length := by
    simp [TransformParams.lengthFlags]
  unfold genCost TwistConsts.constCost
  rw [hfs, hfl]
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.log 2 ts.prod := ⟨_, rfl⟩
  rw [← hn] at hpow hnC hw2 hlow ⊢
  rw [hpow]
  have hrM : 2 ^ ℓ ≤ 2 * 2 ^ n := by
    calc 2 ^ ℓ = 2 * 2 ^ (ℓ - 1) := by rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlow)
  exact gen_arith (by omega) hdCw (by omega) (by omega) (by omega) hnC (by omega) hwr rfl hrM rfl hH

/-! ### The assembly -/

/-- The paper's layout as a layout for every parameter choice (the identity where the layout
conditions fail). -/
noncomputable def paperLayout : Layout := fun _ _ ℓ K _ ts =>
  haveI := Classical.propDecidable (LayoutOK (2 ^ ℓ) ts ℓ K)
  if h : LayoutOK (2 ^ ℓ) ts ℓ K then (paperPerm h).toPerm (powAxes_prod_pow h.1) else Equiv.refl _

/-- Round-script and layout-script writers for the forward and opposite programs, on every bank,
within a fixed multiple of the paper's bound beyond a cutoff. -/
def ScriptWriters (P : TransformParams) : Prop :=
  ∀ A tL : ℕ, ∃ (sgF lgF sgO lgO : Cmd A (4 + DB tL NL)) (Cs : ℝ) (p₂ : ℕ),
    ∀ p d ℓ K w ts (hadm : Admissible P p d ℓ K w ts), p₂ ≤ p →
      ∃ Bs Bl Bs' Bl' : ℕ, ((Bs + Bl : ℕ) : ℝ) ≤ Cs * transformCost P p d ℓ K ts ∧
        ((Bs' + Bl' : ℕ) : ℝ) ≤ Cs * transformCost P p d ℓ K ts ∧
        ScriptGen true sgF (layoutOK_of_admissible hadm) p d w Bs ∧ LayoutGen true lgF ℓ K ts p d w Bl ∧
        ScriptGen false sgO (layoutOK_of_admissible hadm) p d w Bs' ∧ LayoutGen false lgO ℓ K ts p d w Bl'

/-- The record volume is within `2 C_w` of the paper's bound. -/
theorem volume_le_cost {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) :
    ((2 * 2 ^ ℓ * w * ts.prod : ℕ) : ℝ) ≤ 2 * P.Cw * transformCost P p d ℓ K ts := by
  obtain ⟨hpow, hnC, hdD, hD, hdl, hℓp, hpw, hKℓ, hK, hℓ, hw2, hlow, hnD⟩ := adm_sizes hadm hwr
  have hwC := hadm.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hY : ((2 * 2 ^ ℓ * w * ts.prod : ℕ) : ℝ) ≤ 2 * P.Cw * (((2 ^ ℓ * ts.prod : ℕ) : ℝ) * p) := by
    have : 2 * 2 ^ ℓ * w * ts.prod ≤ 2 * P.Cw * (2 ^ ℓ * ts.prod * p) := by
      calc 2 * 2 ^ ℓ * w * ts.prod ≤ 2 * 2 ^ ℓ * (P.Cw * p) * ts.prod := by gcongr
        _ = 2 * P.Cw * (2 ^ ℓ * ts.prod * p) := by ring
    have h := (Nat.cast_le (α := ℝ)).mpr this
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
    linarith
  refine hY.trans ?_
  unfold transformCost
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hdK : (1 : ℝ) ≤ d * K := one_le_mul_of_one_le_of_one_le hd1 hK1
  have h0 : (0 : ℝ) ≤ p * (K : ℝ) ^ (P.τ - 1) + ℓ * (d : ℝ) ^ P.lam' := by positivity
  have hY0 : (0 : ℝ) ≤ ((2 ^ ℓ * ts.prod : ℕ) : ℝ) * p := by positivity
  have hCw : (0 : ℝ) ≤ 2 * P.Cw := by positivity
  have : ((2 ^ ℓ * ts.prod : ℕ) : ℝ) * p ≤
      ((2 ^ ℓ * ts.prod : ℕ) : ℝ) * p * (d * K + p * (K : ℝ) ^ (P.τ - 1) + ℓ * (d : ℝ) ^ P.lam') :=
    le_mul_of_one_le_right hY0 (by linarith)
  have := mul_le_mul_of_nonneg_left this hCw
  push_cast at this ⊢
  linarith

/-- `transformTarget_of_layer`: `prop:simultaneous-layer` gives `lem:synthetic-transform-cost` for
compatible fixed constants, given round-script and layout-script writers within the paper's bound. -/
theorem transformTarget_of_layer {LP : LayerParams} {P : TransformParams} (hc : Compatible LP P)
    (hlayer : layerTarget LP) (hwriters : ScriptWriters P) : transformTarget P := by
  obtain ⟨p₀, tL, qL, aL, M, C, ht, hM⟩ := hlayer
  set A := max aL prime
  have haA : aL ≤ A := le_max_left _ _
  have hP : prime ≤ A := le_max_right _ _
  obtain ⟨sgF, lgF, sgO, lgO, Cs, p₂, hW⟩ := hwriters A tL
  have hc' := hc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hε, har, hbd, -⟩ := hc'
  obtain ⟨p₁, hwr⟩ := eventually_w_le_r P hε har hbd
  refine ⟨max p₀ (max p₂ (max p₁ 1)), paperLayout, 4 + DB tL NL, _, _, A,
    fwdProg (genCmd sgF lgF) M ht haA hP, oppProg (genCmd sgO lgO) M ht haA hP,
    totC P LP C + 2 * P.Cw * (genC ⌈P.Cl⌉₊ : ℕ) + Cs, four_le_wb, ?_⟩
  intro p d ℓ K w ts hp hadm
  have hp0 : p₀ ≤ p := le_trans (le_max_left _ _) hp
  have hp2 : p₂ ≤ p := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hp
  have hp1 : p₁ ≤ p := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hp
  have hp1' : 1 ≤ p := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hp
  have hwr' := hwr p d ℓ K w ts hp1 hadm
  have hL := layoutOK_of_admissible hadm
  obtain ⟨hpow, hnC, hdD, hD, hdl, hℓp, hpw, hKℓ, hK, hℓ, hw2, hlow, hnD⟩ := adm_sizes hadm hwr'
  have hLayer := layerCalls_of_meets hc M ht hM hp0 hp1' hadm
  obtain ⟨Bs, Bl, Bs', Bl', hB, hB', hsgF, hlgF, hsgO, hlgO⟩ := hW p d ℓ K w ts hadm hp2
  have hDd : ts.length = d - 1 := by omega
  have hgF := fwdGen_of hL hp1' (by omega) hK (by omega) hDd hsgF hlgF
  have hgO := oppGen_of hL hp1' (by omega) hK (by omega) hDd hsgO hlgO
  have hlay : paperLayout p d ℓ K w ts = (paperPerm hL).toPerm (powAxes_prod_pow hL.1) := by
    unfold paperLayout; simp only [hL, ↓reduceDIte]
  have hgen := genCost_le hadm hwr'
  have hgenR : (genCost p d ℓ K w ts : ℝ) ≤ 2 * P.Cw * (genC ⌈P.Cl⌉₊ : ℕ) * transformCost P p d ℓ K ts := by
    have h1 : (genCost p d ℓ K w ts : ℝ) ≤ (genC ⌈P.Cl⌉₊ : ℕ) * ((2 * 2 ^ ℓ * w * ts.prod : ℕ) : ℝ) := by
      exact_mod_cast hgen
    have h2 := volume_le_cost hadm hwr'
    have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) (genC ⌈P.Cl⌉₊))
    linarith
  have hTC0 : 0 ≤ transformCost P p d ℓ K ts := by
    unfold transformCost; positivity
  constructor
  · intro fs hfl hfd
    obtain ⟨gs, k, hgl, hgd, hcl, hk, hH⟩ :=
      fwd_bank (genCmd sgF lgF) M ht haA hP hL (by omega) hgF hLayer fs hfl hfd
    refine ⟨gs, k, hgl, hgd, by rw [hlay]; exact hcl, ?_, hH⟩
    have htot := fwdTotal_le hc C hadm hwr'
    have hk' : (k : ℝ) ≤ ((genCost p d ℓ K w ts + Bs + Bl : ℕ) : ℝ) +
        ((fwdRoundsCost hL p d w (layerCL LP C p d ℓ w ts) +
          wrapCost (2 ^ ℓ) w ts ℓ K (transformHeader p d (2 ^ ℓ) K w ts)
            (fwdScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K) (layoutWords (2 ^ ℓ) w ts ℓ K) : ℕ) : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hk
      push_cast at this ⊢
      linarith
    push_cast at hk' hB htot
    have e : (totC P LP C + 2 * P.Cw * (genC ⌈P.Cl⌉₊ : ℕ) + Cs) * transformCost P p d ℓ K ts =
        totC P LP C * transformCost P p d ℓ K ts + 2 * P.Cw * (genC ⌈P.Cl⌉₊ : ℕ) * transformCost P p d ℓ K ts +
          Cs * transformCost P p d ℓ K ts := by ring
    rw [e]
    linarith
  · intro us hul hud
    obtain ⟨gs, k, hgl, hgd, hcl, hk, hH⟩ :=
      opp_bank (genCmd sgO lgO) M ht haA hP hL (by omega) hgO hLayer us hul hud
    refine ⟨gs, k, hgl, hgd, by rw [hlay]; exact hcl, ?_, hH⟩
    have htot := oppTotal_le hc C hadm hwr'
    have hk' : (k : ℝ) ≤ ((genCost p d ℓ K w ts + Bs' + Bl' : ℕ) : ℝ) +
        ((oppRoundsCost hL p d w (layerCL LP C p d ℓ w ts) +
          wrapCost (2 ^ ℓ) w ts ℓ K (transformHeader p d (2 ^ ℓ) K w ts)
            (oppScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K) (undoWords (2 ^ ℓ) w ts ℓ K) : ℕ) : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr hk
      push_cast at this ⊢
      linarith
    push_cast at hk' hB' htot
    have e : (totC P LP C + 2 * P.Cw * (genC ⌈P.Cl⌉₊ : ℕ) + Cs) * transformCost P p d ℓ K ts =
        totC P LP C * transformCost P p d ℓ K ts + 2 * P.Cw * (genC ⌈P.Cl⌉₊ : ℕ) * transformCost P p d ℓ K ts +
          Cs * transformCost P p d ℓ K ts := by ring
    rw [e]
    linarith

end IntegerMultBounds.Schoenhage
