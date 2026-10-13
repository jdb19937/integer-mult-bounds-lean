module

public import IntegerMultBounds.Schoenhage.TransformTarget
public import IntegerMultBounds.Schoenhage.LayoutGenWrap

/-! §6 task 7, the layout-script writers' steps within the paper's bound. Every count in
`LayoutGenMain.lgFwdCost` and `LayoutGenMain.lgUndoCost` is at most `B = 4 (C + 1) w` (with
`C = ⌈C_l⌉`), the costs are at most a cubic in `B`, and with `w ≤ r` the cube of `w` is at most the
record volume. So both writers are within a fixed multiple of `transformCost` beyond a cutoff
(`lgCost_le_transformCost`), which discharges the layout half of `ScriptWriters`
(`scriptWriters_of_scriptGen`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Spec.SignedRingProduct TwistDescriptors LayoutMachines LayoutGenRun LayoutGenMain
  LayoutScriptTape LayoutGenSetup Resampling Script

namespace LayoutGenCost

/-! ### `midCost` as a polynomial in its counts -/

/-- `midCost` with every count a separate argument: `D` axes, `f` flags, `nO` address bits, `l = ℓ`,
`l1 = ℓ - 1`, `q` and `m` the quotient and remainder of `ℓ - 1` by `K`, `W = q D` exchanges,
`N` moves, `bR` and `bK` the binary lengths of the record length and of `K`, `nK` the free bits. -/
def midPoly (D f nO l l1 K w q m W N bR bK nK : ℕ) : ℕ :=
  40 + (13 * f + 10 * D + 4 * l + 60) +
  (D * (2 * l1 + 18) + f * 30 + 3 * D + 4 * f + 3 * (D * l1 + f) + 30 + 4 * nO + 20) +
  (l1 * (16 * l1 + 10 * K + 110) + 100 * l + 600) +
  (8 * w * w + 76 * w + 8 * K * K + 80 * K + 20 * nO + 10 * l + 400) +
  (arrCost D q (D + W) + 4 * (W * (D + W + 1)) + 4 * q + 20) +
  (D * ((150 * N + 8 * bR + 4 * l1 + 1100) + 2) + 1 +
    m * ((D * ((150 * N + 8 * bR + 1100) + 2) + 20 * N + 2 * D + 300) + 2)) +
  (W * (((W * ((10 * W + 2 * K + 160) + 2) + 50 * nK + 60 * (W * K) + 8 * (bR + bK) + 1000) +
    8 * (W + 1) * (W + 13) + 100) + 2)) + 10

theorem midCost_eq (ℓ K w : ℕ) (ts : List ℕ) :
    midCost ℓ K w ts = midPoly ts.length (pf ts ℓ).length (nOf ℓ ts.length (pf ts ℓ)) ℓ (ℓ - 1) K w
      ((ℓ - 1) / K) ((ℓ - 1) % K) ((ℓ - 1) / K * ts.length) (movesN ℓ ts)
      (bin (recLen ℓ w)).length (bin K).length (LayoutMachines.addrBits ts - 2 * K) := by
  unfold midCost midPoly topCost levelCost levCost LayoutSwapTape.stepCost LayoutSwapTape.exchCost
    LayoutSwapTape.passCost
  rfl

theorem midPoly_mono {D f nO l l1 K w q m W N bR bK nK B : ℕ} (hD : D ≤ B) (hf : f ≤ B) (hnO : nO ≤ B)
    (hl : l ≤ B) (hl1 : l1 ≤ B) (hK : K ≤ B) (hw : w ≤ B) (hq : q ≤ B) (hm : m ≤ B) (hW : W ≤ B)
    (hN : N ≤ B) (hbR : bR ≤ B) (hbK : bK ≤ B) (hnK : nK ≤ B) :
    midPoly D f nO l l1 K w q m W N bR bK nK ≤ midPoly B B B B B B B B B B B B B B := by
  unfold midPoly arrCost outerCost
  gcongr

theorem midPoly_cube {B : ℕ} (hB : 1 ≤ B) : midPoly B B B B B B B B B B B B B B ≤ 20000 * B ^ 3 := by
  have h2 : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right hB (by norm_num)
  have h1 : B ≤ B ^ 2 := by nlinarith
  have h0 : 1 ≤ B := hB
  unfold midPoly arrCost outerCost
  ring_nf
  omega

/-! ### The counts of an admissible instance -/

theorem words_opRec_length (n R : ℕ) (o : LayoutMachines.Op) :
    (AxisDriver.Rec.words (LayoutMachines.opRec n R o)).length = 6 := by
  simp [LayoutMachines.opRec, AxisDriver.Rec.words, LayoutMachines.opHdrs, swapHdrsG]

theorem length_layoutWords (r w : ℕ) (ts : List ℕ) (ℓ K : ℕ) :
    (layoutWords r w ts ℓ K).length = 6 * (layoutOpList ts ℓ K).length := by
  simp [layoutWords, List.length_flatMap, words_opRec_length, Function.comp_def, mul_comm]

theorem length_undoWords (r w : ℕ) (ts : List ℕ) (ℓ K : ℕ) :
    (undoWords r w ts ℓ K).length = 6 * (undoOpList ts ℓ K).length := by
  simp [undoWords, List.length_flatMap, words_opRec_length, Function.comp_def, mul_comm]

/-- The bound on every count: `B = 4 (C + 1) w`. -/
def countBound (C w : ℕ) : ℕ := 4 * (C + 1) * w

set_option maxHeartbeats 4000000 in
/-- Both writers' steps are at most a cubic in `B = 4 (C + 1) w`. -/
theorem lgCost_le_cube {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) :
    lgFwdCost ℓ K w ts ≤ 30000 * countBound ⌈P.Cl⌉₊ w ^ 3 ∧
      lgUndoCost ℓ K w ts ≤ 30000 * countBound ⌈P.Cl⌉₊ w ^ 3 := by
  have hL := layoutOK_of_admissible hadm
  obtain ⟨hpow, hnC, hdD, hD, hdl, hℓp, hpw, hKℓ, hK, hℓ, hw2, hlow, hnD⟩ := adm_sizes hadm hwr
  set C := ⌈P.Cl⌉₊
  set B := countBound C w with hBdef
  have hw1 : 1 ≤ w := by omega
  have hBe : B = 4 * (C * w) + 4 * w := by rw [hBdef, countBound]; ring
  have hB1 : 1 ≤ B := by omega
  set D := ts.length with hDdef
  have hdℓ : d ≤ d * ℓ := Nat.le_mul_of_pos_right _ (by omega)
  have hDB : D ≤ C * w := by omega
  have hℓD : ℓ * D ≤ C * w := by
    have : ℓ * D ≤ d * ℓ := by rw [mul_comm]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  -- the counts of `midCost`
  have hf : (pf ts ℓ).length = D := by simp [pf, SigmaConstsTape.paperFlags, hDdef]
  have hnO : nOf ℓ D (pf ts ℓ) = LayoutMachines.addrBits ts := nOf_paper hL
  have haddr : LayoutMachines.addrBits ts ≤ C * w := hnC
  have hq : (ℓ - 1) / K ≤ ℓ := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hm : (ℓ - 1) % K ≤ ℓ := (Nat.mod_le _ _).trans (Nat.sub_le _ _)
  have hW : (ℓ - 1) / K * D ≤ C * w := (Nat.mul_le_mul_right _ hq).trans hℓD
  have hmD : (ℓ - 1) % K * D ≤ C * w := (Nat.mul_le_mul_right _ hm).trans hℓD
  have hN : movesN ℓ ts ≤ B := by
    have e : movesN ℓ ts = LayoutMachines.addrBits ts + D * ℓ + ℓ + D := rfl
    have : D * ℓ = ℓ * D := mul_comm _ _
    omega
  have hbw := Resampling.SwapCost.bin_length w
  have hbR : (bin (recLen ℓ w)).length = ℓ + 1 + (bin w).length := by
    have e : recLen ℓ w = 2 ^ (ℓ + 1) * w := by unfold recLen; ring
    rw [e, bin_two_pow_mul _ _ (by omega)]; simp
  have hbK := Resampling.SwapCost.bin_length K
  have hmid : midCost ℓ K w ts ≤ 20000 * B ^ 3 := by
    rw [midCost_eq, ← hDdef]
    refine (midPoly_mono (B := B) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hN ?_ ?_ ?_).trans (midPoly_cube hB1) <;>
      omega
  -- the scripts
  have hmoves : (layoutMoves ts ℓ K).length ≤ D + C * w := by
    rw [(layout_counts hL).1, ← hDdef]
    have := longs_length_le ts ℓ
    omega
  have hswaps : (layoutSwaps ts ℓ K).length ≤ C * w := by
    have := (layout_counts hL).2
    rw [← hDdef] at this
    omega
  have hops : (layoutOpList ts ℓ K).length ≤ B := by
    rw [length_layoutOpList]; omega
  have hops' : (undoOpList ts ℓ K).length ≤ B := by
    rw [length_undoOpList]; omega
  have hwl : wordLen ℓ w ts ≤ B := by unfold wordLen; omega
  have hnF : (layoutWords (2 ^ ℓ) w ts ℓ K).length ≤ 6 * B := by rw [length_layoutWords]; omega
  have hnU : (undoWords (2 ^ ℓ) w ts ℓ K).length ≤ 6 * B := by rw [length_undoWords]; omega
  have hBB : B ≤ B * B := Nat.le_mul_of_pos_left _ (by omega)
  have hclF : clen (layoutWords (2 ^ ℓ) w ts ℓ K) ≤ 12 * (B * B) := by
    refine (clen_le_of (layoutWords_length hL (by omega))).trans ?_
    calc (layoutWords (2 ^ ℓ) w ts ℓ K).length * (wordLen ℓ w ts + 1) ≤ (6 * B) * (B + 1) :=
          Nat.mul_le_mul hnF (by omega)
      _ = 6 * (B * B) + 6 * B := by ring
      _ ≤ 12 * (B * B) := by omega
  have hclU : clen (undoWords (2 ^ ℓ) w ts ℓ K) ≤ 12 * (B * B) := by
    refine (clen_le_of (undoWords_length hL (by omega))).trans ?_
    calc (undoWords (2 ^ ℓ) w ts ℓ K).length * (wordLen ℓ w ts + 1) ≤ (6 * B) * (B + 1) :=
          Nat.mul_le_mul hnU (by omega)
      _ = 6 * (B * B) + 6 * B := by ring
      _ ≤ 12 * (B * B) := by omega
  have htape : tapeC ℓ K w ts ≤ 50 * (B * B) := by
    unfold tapeC
    rw [fwdOut_eq, _root_.IntegerMultBounds.Schoenhage.clen_reverse, undoOut_eq]
    omega
  have hclear : clearCost ℓ K w ts ≤ 4400 * (B * B) := by unfold clearCost; omega
  have htF : (layoutWords (2 ^ ℓ) w ts ℓ K).length * (wordLen ℓ w ts + 8) ≤ 54 * (B * B) := by
    calc _ ≤ (6 * B) * (B + 8) := Nat.mul_le_mul hnF (by omega)
      _ = 6 * (B * B) + 48 * B := by ring
      _ ≤ 54 * (B * B) := by omega
  have htU : (undoWords (2 ^ ℓ) w ts ℓ K).length * (5 * wordLen ℓ w ts + 38) ≤ 258 * (B * B) := by
    calc _ ≤ (6 * B) * (5 * B + 38) := Nat.mul_le_mul hnU (by omega)
      _ = 30 * (B * B) + 228 * B := by ring
      _ ≤ 258 * (B * B) := by omega
  have hcube : B * B ≤ B ^ 3 := by
    calc B * B = B * B * 1 := by ring
      _ ≤ B * B * B := Nat.mul_le_mul_left _ hB1
      _ = B ^ 3 := by ring
  constructor
  · unfold lgFwdCost; omega
  · unfold lgUndoCost; omega

/-- The constant of the layout-script writers against the record volume. -/
def lgC (C : ℕ) : ℕ := 30000 * 64 * (C + 1) ^ 3

/-- The cube of the count bound is within `64 (C + 1)^3` record volumes. -/
theorem countBound_cube_le {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) :
    countBound ⌈P.Cl⌉₊ w ^ 3 ≤ 64 * (⌈P.Cl⌉₊ + 1) ^ 3 * (2 * 2 ^ ℓ * w * ts.prod) := by
  obtain ⟨hpow, -, -, -, -, -, -, -, -, -, hw2, -, -⟩ := adm_sizes hadm hwr
  have hwM : w ≤ 2 * ts.prod := by rw [hpow]; exact hw2
  have hw3 : w * w * w ≤ 2 * 2 ^ ℓ * w * ts.prod := by
    calc w * w * w ≤ 2 ^ ℓ * w * (2 * ts.prod) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hwr) hwM
      _ = 2 * 2 ^ ℓ * w * ts.prod := by ring
  calc countBound ⌈P.Cl⌉₊ w ^ 3 = 64 * (⌈P.Cl⌉₊ + 1) ^ 3 * (w * w * w) := by unfold countBound; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hw3

/-- `lgCost_le_volume`: both writers' steps are within `lgC C` record volumes. -/
theorem lgCost_le_volume {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) :
    lgFwdCost ℓ K w ts ≤ lgC ⌈P.Cl⌉₊ * (2 * 2 ^ ℓ * w * ts.prod) ∧
      lgUndoCost ℓ K w ts ≤ lgC ⌈P.Cl⌉₊ * (2 * 2 ^ ℓ * w * ts.prod) := by
  obtain ⟨hF, hU⟩ := lgCost_le_cube hadm hwr
  have hV := countBound_cube_le hadm hwr
  have e : lgC ⌈P.Cl⌉₊ * (2 * 2 ^ ℓ * w * ts.prod) =
      30000 * (64 * (⌈P.Cl⌉₊ + 1) ^ 3 * (2 * 2 ^ ℓ * w * ts.prod)) := by unfold lgC; ring
  rw [e]
  exact ⟨hF.trans (Nat.mul_le_mul_left _ hV), hU.trans (Nat.mul_le_mul_left _ hV)⟩

/-- `lgCost_le_transformCost`: both writers' steps are within `2 C_w lgC` times the paper's bound. -/
theorem lgCost_le_transformCost {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hwr : w ≤ 2 ^ ℓ) :
    (lgFwdCost ℓ K w ts : ℝ) ≤ 2 * P.Cw * (lgC ⌈P.Cl⌉₊ : ℕ) * transformCost P p d ℓ K ts ∧
      (lgUndoCost ℓ K w ts : ℝ) ≤ 2 * P.Cw * (lgC ⌈P.Cl⌉₊ : ℕ) * transformCost P p d ℓ K ts := by
  obtain ⟨hF, hU⟩ := lgCost_le_volume hadm hwr
  have hV := volume_le_cost hadm hwr
  have hC0 : (0 : ℝ) ≤ (lgC ⌈P.Cl⌉₊ : ℕ) := Nat.cast_nonneg _
  have hscale := mul_le_mul_of_nonneg_left hV hC0
  have hF' : (lgFwdCost ℓ K w ts : ℝ) ≤ (lgC ⌈P.Cl⌉₊ : ℕ) * ((2 * 2 ^ ℓ * w * ts.prod : ℕ) : ℝ) := by
    exact_mod_cast hF
  have hU' : (lgUndoCost ℓ K w ts : ℝ) ≤ (lgC ⌈P.Cl⌉₊ : ℕ) * ((2 * 2 ^ ℓ * w * ts.prod : ℕ) : ℝ) := by
    exact_mod_cast hU
  constructor <;> nlinarith

/-! ### The layout half of `ScriptWriters` -/

/-- `scriptWriters_of_scriptGen`: with the transform's size comparison (`ε < 1`, `a_r > 0`,
`b_d > 0`, as in `Compatible`), round-script writers within a fixed multiple of the paper's bound
give `ScriptWriters`; the layout-script writers are `LayoutGenWrap.layoutGenFwd` and
`LayoutGenWrap.layoutGenUndo`. -/
theorem scriptWriters_of_scriptGen {P : TransformParams} (hε : P.ε < 1) (har : 0 < P.ar) (hbd : 0 < P.bd)
    (hsg : ∀ A tL : ℕ, ∃ (sgF sgO : Cmd A (4 + DB tL NL)) (Cs : ℝ) (p₂ : ℕ),
      ∀ p d ℓ K w ts (hadm : Admissible P p d ℓ K w ts), p₂ ≤ p →
        ∃ Bs Bs' : ℕ, (Bs : ℝ) ≤ Cs * transformCost P p d ℓ K ts ∧
          (Bs' : ℝ) ≤ Cs * transformCost P p d ℓ K ts ∧
          ScriptGen true sgF (layoutOK_of_admissible hadm) p d w Bs ∧
          ScriptGen false sgO (layoutOK_of_admissible hadm) p d w Bs') :
    ScriptWriters P := by
  intro A tL
  obtain ⟨sgF, sgO, Cs, p₂, hW⟩ := hsg A tL
  obtain ⟨p₁, hwr⟩ := eventually_w_le_r P hε har hbd
  refine ⟨sgF, LayoutGenWrap.layoutGenFwd A tL NL, sgO, LayoutGenWrap.layoutGenUndo A tL NL,
    Cs + 2 * P.Cw * (lgC ⌈P.Cl⌉₊ : ℕ), max p₂ p₁, ?_⟩
  intro p d ℓ K w ts hadm hp
  have hwr' := hwr p d ℓ K w ts (le_trans (le_max_right _ _) hp) hadm
  obtain ⟨Bs, Bs', hBs, hBs', hsgF, hsgO⟩ := hW p d ℓ K w ts hadm (le_trans (le_max_left _ _) hp)
  have hL := layoutOK_of_admissible hadm
  obtain ⟨-, -, hdD, -, -, -, hpw, -, -, -, -, -, -⟩ := adm_sizes hadm hwr'
  have hDd : ts.length = d - 1 := by omega
  obtain ⟨hF, hU⟩ := lgCost_le_transformCost hadm hwr'
  refine ⟨Bs, lgFwdCost ℓ K w ts, Bs', lgUndoCost ℓ K w ts, ?_, ?_, hsgF,
    LayoutGenWrap.layoutGen_fwd hL (by omega) hDd, hsgO, LayoutGenWrap.layoutGen_undo hL (by omega) hDd⟩
  · push_cast; linarith
  · push_cast; linarith

end LayoutGenCost

end IntegerMultBounds.Schoenhage
