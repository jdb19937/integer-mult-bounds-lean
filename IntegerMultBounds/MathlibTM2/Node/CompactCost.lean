module

public import IntegerMultBounds.MathlibTM2.Node.CompactSlotXorPasses

/-!
# The step bound of the compact slot XOR in closed form

`cxCost` is the vendored interchange term of at most twelve interchanges plus a natural-number
part. This file bounds the natural-number part by an explicit expression in the parameter sum
`M (r w + L + n + k' + nG + 1)` (`M = R 2^n` records, `k' = n + rb` the key length, `nG` the
control field width), the exceptional-index term `|Bad| k' (r w + k' + 1)`, the register count
`T` and the interchange register count `swapT 6`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.PackedXor
  IntegerMultBounds.MathlibTM2.Layer.CompactXor

section CostBound

variable {d : CxD}

/-! ### Arithmetic of a valid datum -/

/-- The fields of the interchange rectangle in terms of the datum. -/
lemma CxD.swapD_fields (d : CxD) :
    d.swapD.M = d.M ∧ d.swapD.Bk = d.Bk ∧ d.swapD.kl = d.kl ∧ d.swapD.rb = d.rb ∧
      d.swapD.n = d.n ∧ d.swapD.R = d.R ∧ d.swapD.rw = d.rw ∧ d.swapD.L = d.nG ∧
      d.swapD.K = d.nG ∧ d.swapD.ρ = 0 ∧ d.swapD.a₀ = d.bB :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The gaps of the interchange rectangle sum to the address width. -/
lemma CxD.swapD_sum (hv : d.Valid) :
    d.swapD.n3 + d.nG + d.swapD.n2 + d.nG + d.swapD.n1 + d.nG + d.swapD.n0 = d.n :=
  SxD.sum_eq (swapD_valid hv)

/-- The parameter sum of the bound. -/
lemma CxD.Valid.cost_facts (hv : d.Valid) :
    1 ≤ d.M ∧ d.n ≤ d.M ∧ d.R ≤ d.M ∧ d.rb ≤ d.R ∧ d.L ≤ d.n ∧ d.K ≤ d.L ∧ d.G ≤ d.K ∧
      d.ρ ≤ d.K ∧ d.nG ≤ d.L ∧ d.nn * d.K ≤ d.L ∧ d.nn ≤ d.L ∧ d.k ≤ d.L ∧ d.a₀ ≤ d.n ∧
      d.bB ≤ d.n ∧ 1 ≤ d.nG ∧ 1 ≤ d.K ∧
      d.L * d.L ≤ d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1) ∧
      d.M ≤ d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1) ∧
      d.rw + d.L + d.n + d.kl + d.nG + 1 ≤ d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1) ∧
      d.pT ≤ d.n ∧ d.pU ≤ d.n ∧ d.n * d.n ≤ d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1) := by
  have hK : 1 ≤ d.K := d.K_pos hv
  have hR := hv.hR
  have hpow : 1 ≤ 2 ^ d.n := Nat.one_le_two_pow
  have hM2 : 2 ^ d.n ≤ d.M := by unfold CxD.M; exact Nat.le_mul_of_pos_left _ (by omega)
  have hRM : d.R ≤ d.M := by unfold CxD.M; exact Nat.le_mul_of_pos_right _ (by omega)
  have hn2 : d.n ≤ 2 ^ d.n := (Nat.lt_two_pow_self).le
  have hM1 : 1 ≤ d.M := le_trans hpow hM2
  have hnM : d.n ≤ d.M := hn2.trans hM2
  have hrbR : d.rb ≤ d.R := length_sxBits_le d.R
  obtain ⟨hhi, -, -, hpTn, hpUn, -, hbT, -, hnGL⟩ := hv.prods
  have hLn : d.L ≤ d.n := (Nat.le_mul_of_pos_left d.L (by omega : 0 < d.hi + 1)).trans hhi
  have hKL : d.K ≤ d.L := by rw [hv.hLK]; exact Nat.le_mul_of_pos_right _ (by have := hv.hk; omega)
  have hGK : d.G ≤ d.K := by have := hv.hGK; omega
  have hρK : d.ρ ≤ d.K := hv.hρ.le
  have hnnK : d.nn * d.K ≤ d.L := by
    have h := d.L_eq hv
    have : (d.nn + 1) * d.K = d.nn * d.K + d.K := by ring
    omega
  have hnn : d.nn ≤ d.L := (Nat.le_mul_of_pos_right d.nn hK).trans hnnK
  have hkL : d.k ≤ d.L := by rw [hv.hLK]; exact Nat.le_mul_of_pos_left _ hK
  have ha₀ : d.a₀ ≤ d.n := by have := hv.hhiT; omega
  have hbB : d.bB ≤ d.n := by have : d.bT = d.bB + d.pT * d.nG := rfl; omega
  have hnG1 : 1 ≤ d.nG := (swapD_valid hv).hρ
  have hLL : d.L * d.L ≤ d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1) :=
    (Nat.mul_le_mul hLn hLn).trans ((Nat.mul_le_mul_right _ hnM).trans
      (Nat.mul_le_mul_left _ (by omega)))
  have hMX : d.M ≤ d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hYX : d.rw + d.L + d.n + d.kl + d.nG + 1 ≤ d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1) :=
    Nat.le_mul_of_pos_left _ hM1
  have hpT : d.pT ≤ d.n := (Nat.le_mul_of_pos_right d.pT hnG1).trans hpTn
  have hpU : d.pU ≤ d.n :=
    ((Nat.le_succ _).trans (Nat.le_mul_of_pos_right (d.pU + 1) hnG1)).trans hpUn
  have hnnX : d.n * d.n ≤ d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1) :=
    (Nat.mul_le_mul_right _ hnM).trans (Nat.mul_le_mul_left _ (by omega))
  exact ⟨hM1, hnM, hRM, hrbR, hLn, hKL, hGK, hρK, hnGL, hnnK, hnn, hkL, ha₀, hbB, hnG1, hK,
    hLL, hMX, hYX, hpT, hpU, hnnX⟩

/-- A multiple of the record count against the parameter sum. -/
lemma CxD.mul_le_X (d : CxD) (c : ℕ) {a : ℕ}
    (h : a ≤ c * (d.rw + d.L + d.n + d.kl + d.nG + 1)) :
    d.M * a ≤ c * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) :=
  (Nat.mul_le_mul_left d.M h).trans (le_of_eq (by ring))

/-- The exceptional addresses are among the records. -/
lemma cxBad_le_M (d : CxD) : cxBad d ≤ d.M := by
  unfold cxBad
  exact (Fintype.card_le_of_injective _ Subtype.val_injective).trans (Fintype.card_fin _).le

/-! ### The setup and the cleanup -/

/-- A uniform bound on the setup stages. -/
lemma cxStageCost_le (hv : d.Valid) (s : ℕ) :
    cxStageCost d s ≤ 26000 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 8000 := by
  obtain ⟨hM1, hnM, hRM, hrbR, hLn, hKL, hGK, hρK, hnGL, hnnK, hnn, hkL, ha₀, hbB, hnG1, hK,
    hLL, hMX, hYX, hpT, hpU, hnnX⟩ := hv.cost_facts
  have hkl : d.kl = d.n + d.rb := rfl
  have hBk : d.Bk = d.rw + d.kl := rfl
  obtain ⟨eM, eBk, ekl, erb, en, eR, erw, eL, eK, eρ, ea⟩ := d.swapD_fields
  have hs := d.swapD_sum hv
  have hfit := (swapD_valid hv).hfit
  have hU : cxUnit d ≤ 666 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 200 := by
    unfold cxUnit
    have h1 : d.L * (4 * d.K + 9) ≤ 13 * (d.L * d.L) :=
      (Nat.mul_le_mul_left d.L (by omega : 4 * d.K + 9 ≤ 13 * d.L)).trans (le_of_eq (by ring))
    have h2 : d.nn * (12 * d.K + 20) = 12 * (d.nn * d.K) + 20 * d.nn := by ring
    have h3 : d.L * (8 * d.G + 13) ≤ 21 * (d.L * d.L) :=
      (Nat.mul_le_mul_left d.L (by omega : 8 * d.G + 13 ≤ 21 * d.L)).trans (le_of_eq (by ring))
    have h4 : (d.pT + d.pU) * (4 * d.nG + 20) ≤ 48 * (d.n * d.n) :=
      (Nat.mul_le_mul (by omega : d.pT + d.pU ≤ 2 * d.n) (by omega : 4 * d.nG + 20 ≤ 24 * d.n)).trans
        (le_of_eq (by ring))
    omega
  have h15 : ∑ i ∈ Finset.range 38, cxGapCost d (i + 1) + 1 ≤
      38 * (683 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 200) + 1 := by
    have hB : ∀ s, sxStageCost d.swapD s ≤
        683 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 200 := by
      intro s
      refine (sxStageCost_le d.swapD s).trans ?_
      have hq : d.swapD.L * (4 * d.swapD.K + 9) ≤ 13 * (d.L * d.L) := by
        show d.nG * (4 * d.nG + 9) ≤ _
        calc d.nG * (4 * d.nG + 9) ≤ d.nG * (13 * d.nG) := Nat.mul_le_mul_left _ (by omega)
          _ = 13 * (d.nG * d.nG) := by ring
          _ ≤ 13 * (d.L * d.L) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hnGL hnGL)
      omega
    have hG : ∀ s, cxGapCost d s ≤ 683 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 200 := by
      intro s
      obtain ⟨-, -, -, -, hpU1, -, -, -, -⟩ := hv.prods
      have hpTq : d.pT * (4 * d.nG + 9) ≤ 13 * (d.n * d.n) :=
        (Nat.mul_le_mul hpT (by omega : 4 * d.nG + 9 ≤ 13 * d.n)).trans (le_of_eq (by ring))
      have hpUq : d.pU * (4 * d.nG + 9) ≤ 13 * (d.n * d.n) :=
        (Nat.mul_le_mul hpU (by omega : 4 * d.nG + 9 ≤ 13 * d.n)).trans (le_of_eq (by ring))
      rcases s with _ | _ | _ | _ | _ | s
      · exact hB 0
      · simp only [cxGapCost]; omega
      · simp only [cxGapCost]; omega
      · simp only [cxGapCost]; omega
      · simp only [cxGapCost]; omega
      · exact hB (s + 5)
    refine Nat.add_le_add_right ((Finset.sum_le_sum fun i _ => hG (i + 1)).trans ?_) 1
    simp
  unfold cxStageCost
  split_ifs <;> omega

/-- A uniform bound on the register contents. -/
lemma cxBc_length_le (hv : d.Valid) (A : ℕ) (x : CXReg) :
    (cxBc A d x).length ≤ 11 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 2 := by
  obtain ⟨hM1, hnM, hRM, hrbR, hLn, hKL, hGK, hρK, hnGL, hnnK, hnn, hkL, ha₀, hbB, hnG1, hK,
    hLL, hMX, hYX, hpT, hpU, hnnX⟩ := hv.cost_facts
  have hkl : d.kl = d.n + d.rb := rfl
  have hBk : d.Bk = d.rw + d.kl := rfl
  cases x with
  | sx r =>
      have h := sxBc_length_le A d.swapD r
      obtain ⟨eM, eBk, ekl, erb, en, eR, erw, eL, eK, eρ, ea⟩ := d.swapD_fields
      have hs := d.swapD_sum hv
      unfold sxHL at h
      simp only [cxBc]
      omega
  | fld g =>
      have h : d.len11 g ≤ d.n := by
        rw [← d.sum_len11 hv]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
      simp only [cxBc, length_binSyms]
      omega
  | kf j =>
      have h : d.len8 j ≤ d.n + d.rb := by
        rw [← d.sum_len8 hv]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      simp only [cxBc, length_binSyms]
      omega
  | val i =>
      cases i <;> simp only [cxBc, CxD.valOf, List.length_replicate] <;> omega
  | _ =>
      simp only [cxBc, length_binSyms, List.length_replicate, List.length_nil]
      omega

/-- The cleanup bound. -/
lemma cxCleanupCost_le (hv : d.Valid) (A : ℕ) :
    cxCleanupCost (A := A) d ≤
      37 * (38 * (2 * (11 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 2) + 2) + 1) + 1 := by
  have hb : ∀ i, (if 37 - i = 15 then
      ∑ j ∈ Finset.range 38, (2 * (sxBc A d.swapD (sxOfStage (38 - j))).length + 2) + 1
      else 2 * (cxBc A d (cxOfStage (37 - i))).length + 2) ≤
      38 * (2 * (11 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 2) + 2) + 1 := by
    intro i
    split_ifs
    · have h2 : ∑ j ∈ Finset.range 38, (2 * (sxBc A d.swapD (sxOfStage (38 - j))).length + 2) ≤
          38 * (2 * (11 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 2) + 2) := by
        have hj : ∀ j, 2 * (sxBc A d.swapD (sxOfStage (38 - j))).length + 2 ≤
            2 * (11 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 2) + 2 := fun j => by
          have : (sxBc A d.swapD (sxOfStage (38 - j))).length ≤
              11 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 2 :=
            cxBc_length_le hv A (.sx (sxOfStage (38 - j)))
          omega
        refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
        simp
      omega
    · have := cxBc_length_le hv A (cxOfStage (37 - i))
      omega
  unfold cxCleanupCost
  refine Nat.add_le_add_right ((Finset.sum_le_sum fun i _ => hb i).trans ?_) 1
  simp

/-! ### The passes -/

/-- The key pass bound. -/
lemma cxKeyCost_le (hv : d.Valid) :
    cxKeyCost d ≤ 116 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 40 := by
  obtain ⟨hM1, hnM, hRM, hrbR, hLn, hKL, hGK, hρK, hnGL, hnnK, hnn, hkL, ha₀, hbB, hnG1, hK,
    hLL, hMX, hYX, hpT, hpU, hnnX⟩ := hv.cost_facts
  have h1 : d.M * (15 * d.kl + 6 * d.rw + 110) ≤
      110 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) := d.mul_le_X 110 (by omega)
  unfold cxKeyCost
  omega

/-- The fix pass bound. -/
lemma cxFixCost_le (hv : d.Valid) :
    cxFixCost d ≤ 124 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 106 := by
  obtain ⟨hM1, hnM, hRM, hrbR, hLn, hKL, hGK, hρK, hnGL, hnnK, hnn, hkL, ha₀, hbB, hnG1, hK,
    hLL, hMX, hYX, hpT, hpU, hnnX⟩ := hv.cost_facts
  have h1 : d.M * (18 * d.rw + 12 * d.L + 8 * d.n + 8 * 11 + 28) ≤
      116 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) := d.mul_le_X 116 (by omega)
  unfold cxFixCost
  omega

/-- The repair pass bound with `bad` exceptional indices. -/
lemma cxRepairCost_le (hv : d.Valid) (bad : ℕ) :
    cxRepairCost d bad ≤ 321 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) +
      13 * (bad * d.kl * (d.rw + d.kl + 1)) + 111 := by
  obtain ⟨hM1, hnM, hRM, hrbR, hLn, hKL, hGK, hρK, hnGL, hnnK, hnn, hkL, ha₀, hbB, hnG1, hK,
    hLL, hMX, hYX, hpT, hpU, hnnX⟩ := hv.cost_facts
  have h1 : d.M * (2 * badPrepCost d.L d.nG 1 + 16 * (d.kl + d.rw) + 12 + 8 * d.n + 8 * 11 + 39) ≤
      303 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) :=
    d.mul_le_X 303 (by unfold badPrepCost; omega)
  have h2 : d.kl * (bad * (12 * d.kl + 6 * d.rw + 13)) ≤
      13 * (bad * d.kl * (d.rw + d.kl + 1)) :=
    calc d.kl * (bad * (12 * d.kl + 6 * d.rw + 13)) ≤ d.kl * (bad * (13 * (d.rw + d.kl + 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = 13 * (bad * d.kl * (d.rw + d.kl + 1)) := by ring
  unfold cxRepairCost
  omega

/-! ### The instructions -/

/-- The preparation cost against the slot width. -/
lemma prepCost_le (hv : d.Valid) (useT : Bool) (p : PData) (lenComp : ℕ)
    (hW : p.W ≤ d.L) (hoO : p.oO ≤ d.L) (hoA : p.oA ≤ d.L) (hoY : p.oY ≤ d.L)
    (hsA : p.sA ≤ d.K) (hpK : p.K ≤ d.K) (hpG : p.G ≤ d.K) (hpad : p.pad ≤ d.K)
    (hn : p.n = d.nn) (hlA : p.lA ≤ d.L) (hlY : p.lY ≤ d.L) (hlT : p.lT ≤ d.L)
    (hlen : lenComp ≤ d.L) :
    prepCost useT p lenComp ≤ 100 * d.L + 34 := by
  obtain ⟨hM1, hnM, hRM, hrbR, hLn, hKL, hGK, hρK, hnGL, hnnK, hnn, hkL, ha₀, hbB, hnG1, hK,
    hLL, hMX, hYX, hpT, hpU, hnnX⟩ := hv.cost_facts
  unfold prepCost colCost
  have hcol : 6 * (if useT then p.G else 0) + 4 * p.pad + 6 * p.sA + 6 * p.K + 19 + 5 ≤
      22 * d.K + 24 := by
    cases useT <;> simp <;> omega
  have h1 := Nat.mul_le_mul_left d.nn hcol
  rw [hn]
  have h2 : d.nn * (22 * d.K + 24) = 22 * (d.nn * d.K) + 24 * d.nn := by ring
  omega

/-- The preparation cost of the indexed data. -/
lemma prepCost_pdataP_le (hv : d.Valid) (useT : Bool) (fA fY fT : Fin 11)
    (W oO oA oY sA pad lenComp : ℕ) (hW : W ≤ d.L) (hoO : oO ≤ d.L) (hoA : oA ≤ d.L)
    (hoY : oY ≤ d.L) (hsA : sA ≤ d.K) (hpad : pad ≤ d.K) (hlen : lenComp ≤ d.L)
    (hA : d.len11 fA ≤ d.L) (hY : d.len11 fY ≤ d.L) (hT : d.len11 fT ≤ d.L) :
    prepCost useT (pdataP d.len11 fA fY fT W oO oA oY sA d.K d.G d.nn pad 0) lenComp ≤
      100 * d.L + 34 :=
  prepCost_le hv useT _ lenComp hW hoO hoA hoY hsA le_rfl (show d.G ≤ d.K by have := hv.hGK; omega)
    hpad rfl
    hA hY hT hlen

/-- The preparation cost of every instruction. -/
lemma cxPrepC_le (hv : d.Valid) (i : CxInstr) : CxInstr.prepC d i ≤ 100 * d.L + 34 := by
  obtain ⟨hM1, hnM, hRM, hrbR, hLn, hKL, hGK, hρK, hnGL, hnnK, hnn, hkL, ha₀, hbB, hnG1, hK,
    hLL, hMX, hYX, hpT, hpU, hnnX⟩ := hv.cost_facts
  have hρL : d.ρ ≤ d.L := hρK.trans hKL
  have hctrl : ∀ b, d.len11 (CxInstr.ctrl d b) ≤ d.L := fun b => by
    cases b <;> simp only [CxInstr.ctrl, Bool.false_eq_true, ↓reduceIte, CxD.len11_fU,
      CxD.len11_fX] <;> omega
  have hoA : ∀ b, CxInstr.oA d b ≤ d.L := fun b => by
    cases b <;> simp only [CxInstr.oA, Bool.false_eq_true, ↓reduceIte] <;> omega
  have hsA : ∀ b, CxInstr.sA d b ≤ d.K := fun b => by
    cases b <;> simp only [CxInstr.sA, Bool.false_eq_true, ↓reduceIte] <;> omega
  have hfY : d.len11 d.fY ≤ d.L := d.len11_fY.le
  have hfX : d.len11 d.fX ≤ d.L := d.len11_fX.le
  have hfT : d.len11 CxD.fT ≤ d.L := by rw [CxD.len11_fT]; exact hnGL
  have hfB : d.len11 CxD.fB ≤ d.L := by rw [CxD.len11_fB]; exact hnGL
  cases i with
  | swapTB => simp [CxInstr.prepC]
  | swapUB => simp [CxInstr.prepC]
  | rotYW ctrlU neg =>
      simp only [CxInstr.prepC]
      exact prepCost_pdataP_le hv true _ _ _ _ _ _ _ _ _ _ hfY hρL (hoA ctrlU) hρL (hsA ctrlU)
        (by omega) hfY (hctrl ctrlU) hfY hfT
  | rotBbY =>
      simp only [CxInstr.prepC]
      exact prepCost_pdataP_le hv false _ _ _ _ _ _ _ _ _ _ hfB (Nat.zero_le _) hρL hρL le_rfl
        (by omega) hfB hfY hfX hfT
  | rotYb ctrlU =>
      simp only [CxInstr.prepC]
      exact prepCost_pdataP_le hv false _ _ _ _ _ _ _ _ _ _ hfY hρL (hoA ctrlU) hρL (hsA ctrlU)
        (by omega) hfY (hctrl ctrlU) hfY hfT
  | rotBx ctrlU =>
      simp only [CxInstr.prepC]
      exact prepCost_pdataP_le hv false _ _ _ _ _ _ _ _ _ _ hfB (Nat.zero_le _) (hoA ctrlU) hρL
        (hsA ctrlU) (by omega) hfB (hctrl ctrlU) hfY hfT
  | rotBbX neg =>
      simp only [CxInstr.prepC]
      exact prepCost_pdataP_le hv false _ _ _ _ _ _ _ _ _ _ hfB (Nat.zero_le _) hρL hρL le_rfl
        (by omega) hfB hfX hfY hfT

/-- The rotation pass bound. -/
lemma cxRotCost_le (hv : d.Valid) {cP : ℕ} (hcP : cP ≤ 100 * d.L + 34) :
    cxRotCost d cP ≤ 218 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 19 := by
  obtain ⟨hM1, hnM, hRM, hrbR, hLn, hKL, hGK, hρK, hnGL, hnnK, hnn, hkL, ha₀, hbB, hnG1, hK,
    hLL, hMX, hYX, hpT, hpU, hnnX⟩ := hv.cost_facts
  have hBk : d.Bk = d.rw + d.kl := rfl
  have hidx : idxStepCost d.Bk d.L d.len11 ≤ 4 * d.Bk + 6 * d.L + 4 * d.n + 56 := by
    have := d.sum_len11 hv
    unfold idxStepCost
    omega
  have h1 : d.M * (2 * cP + 2 * idxStepCost d.Bk d.L d.len11 + 4 * d.Bk + 4) ≤
      212 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) := d.mul_le_X 212 (by omega)
  unfold cxRotCost
  omega

/-- The rotation pass bound of every instruction. -/
lemma cxRot_le (hv : d.Valid) (i : CxInstr) :
    cxRotCost d (CxInstr.prepC d i) ≤ 218 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 19 :=
  cxRotCost_le hv (cxPrepC_le hv i)

/-- The linear part of one interchange. -/
lemma sxSwapNat_le (hv : d.Valid) (T : ℕ) :
    sxSwapNat d.swapD T ≤
      154 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 2 * T + 6 * swapT 6 + 53 := by
  obtain ⟨hM1, hnM, hRM, hrbR, hLn, hKL, hGK, hρK, hnGL, hnnK, hnn, hkL, ha₀, hbB, hnG1, hK,
    hLL, hMX, hYX, hpT, hpU, hnnX⟩ := hv.cost_facts
  have hkl : d.kl = d.n + d.rb := rfl
  have hBk : d.Bk = d.rw + d.kl := rfl
  obtain ⟨eM, eBk, ekl, erb, en, eR, erw, eL, eK, eρ, ea⟩ := d.swapD_fields
  have hs := d.swapD_sum hv
  have hMB : d.swapD.M * d.swapD.Bk ≤ d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1) := by
    show d.M * d.Bk ≤ _
    exact Nat.mul_le_mul_left _ (by omega)
  unfold sxSwapNat sxHL
  omega

/-- The instructions: at most twelve interchanges and twelve rotations. -/
lemma cxInstrSum_le (hv : d.Valid) (T : ℕ) :
    ((CxInstr.prog d).map (CxInstr.cost d T)).sum ≤ 12 * sxSwapCost d.swapD T +
      12 * ((218 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 19 : ℕ) : ℝ) := by
  have hsw := sxSwapCost_nonneg d.swapD T
  have hr : ∀ i, (cxRotCost d (CxInstr.prepC d i) : ℝ) ≤
      ((218 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 19 : ℕ) : ℝ) :=
    fun i => Nat.cast_le.2 (cxRot_le hv i)
  have h0 : (0 : ℝ) ≤ ((218 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 19 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  unfold CxInstr.prog
  split_ifs
  · simp only [CxInstr.core, CxInstr.loadU, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, CxInstr.cost, add_zero]
    linarith [hr (.rotYW true false), hr (.rotYW true true), hr .rotBbY, hr (.rotYb true),
      hr (.rotBx true), hr (.rotBbX false), hr (.rotBbX true)]
  · simp only [CxInstr.core, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      CxInstr.cost, add_zero]
    linarith [hr (.rotYW false false), hr (.rotYW false true), hr .rotBbY, hr (.rotYb false),
      hr (.rotBx false)]

/-! ### The closed form -/

/-- The natural-number part of the bound. -/
lemma cxNat_le (hv : d.Valid) (A T : ℕ) :
    ∑ i ∈ Finset.range 37, cxStageCost d (i + 1) + 1 + cxKeyCost d + (2 * d.L + 2) +
      cxRepairCost d (cxBad d) + cxFixCost d + cxCleanupCost (A := A) d +
      12 * sxSwapNat d.swapD T +
      12 * (218 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 19) + 1 ≤
    1000000 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) +
      13 * (cxBad d * d.kl * (d.rw + d.kl + 1)) + 24 * T + 72 * swapT 6 + 400000 := by
  obtain ⟨hM1, hnM, hRM, hrbR, hLn, hKL, hGK, hρK, hnGL, hnnK, hnn, hkL, ha₀, hbB, hnG1, hK,
    hLL, hMX, hYX, hpT, hpU, hnnX⟩ := hv.cost_facts
  have h1 : ∑ i ∈ Finset.range 37, cxStageCost d (i + 1) ≤
      37 * (26000 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) + 8000) := by
    refine (Finset.sum_le_sum fun i _ => cxStageCost_le hv (i + 1)).trans ?_
    simp
  have h2 := cxKeyCost_le hv
  have h3 := cxRepairCost_le hv (cxBad d)
  have h4 := cxFixCost_le hv
  have h5 := cxCleanupCost_le hv A
  have h6 := sxSwapNat_le hv T
  omega

/-- **The closed form of the compact slot-XOR bound**: twelve vendored interchange terms plus
`10^6 M (r w + L + n + k' + nG + 1) + 13 |Bad| k' (r w + k' + 1) + 24 T + 72 t + 4·10^5`. -/
theorem cxCost_le (hv : d.Valid) (A T : ℕ) :
    cxCost A d T ≤ 12 * sxSwapReal d.swapD T +
      ((1000000 * (d.M * (d.rw + d.L + d.n + d.kl + d.nG + 1)) +
        13 * (cxBad d * d.kl * (d.rw + d.kl + 1)) + 24 * T + 72 * swapT 6 + 400000 : ℕ) : ℝ) := by
  have hI := cxInstrSum_le hv T
  have hN := (Nat.cast_le (α := ℝ)).2 (cxNat_le hv A T)
  have hsplit : sxSwapCost d.swapD T = sxSwapReal d.swapD T + (sxSwapNat d.swapD T : ℝ) := rfl
  rw [hsplit] at hI
  unfold cxCost
  push_cast at hI hN ⊢
  linarith

end CostBound

end IntegerMultBounds.MathlibTM2.Node
