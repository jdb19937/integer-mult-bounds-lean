module

public import IntegerMultBounds.MathlibTM2.Fast.DistSynMain

/-!
# The cost of the wires program

* `dsySynCostG_le`: for `N, ℓ, K, D ≤ M`, `2 ≤ M`, the wire machine runs within
  `130000 M^7 + 20 W_L` steps;
* `dsyWiresCost_le`: eventually `dsyWiresCost n ≤ 2·10^7 (b n + 1)^7 + 30 · 2^ℓ · dsW n`;
* `dsyWires_lower`: the park record alone has at least `2^ℓ dsW n` symbols, so the second term
  is unavoidable for any program writing `mnσ (blP₀ dsW n) v₀`;
* `dsyStash_le`, `dsyStash_ge`: the stash cost `synStashCostW (dsyV₀ n) synXS` of the wires is
  `2 · 2^ℓ + O((b n + 1)^2)` (it is not `O(p n)`: the wire `p .r` has `2^ℓ` ticks);
The `BdWires` bundle built from these is `dsyWires` (`Fast/BundleWires.lean`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.Rounds
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter

set_option linter.unusedSectionVars false

noncomputable section

/-! ### The machine at a common bound -/

/-- The atoms of the phases with every parameter at `M`. -/
def dsyAtomsM (M : ℕ) : ℕ :=
  ldw1Atoms M M M + dsyLoopAtoms M + dsyLgAtoms M + dsyLoopAtoms M + dsyNrAtoms M +
    dsyRecAtoms M M + dsyPosAtoms M

theorem dsyAtoms_le_M {N ℓ K D M : ℕ} (hN : N ≤ M) (hℓ : ℓ ≤ M) (hD : D ≤ M) :
    dsyAtoms N ℓ K D ≤ dsyAtomsM M := by
  have hb : layB ℓ K ≤ M := le_trans (Nat.mod_le _ _) (le_trans (Nat.sub_le _ _) hℓ)
  simp only [dsyAtoms, dsyAtomsM, ldw1Atoms, ldwPart1Atoms, ldwPart2Atoms, ldwP1Atoms,
    ldwP2OAtoms, ldwP2Atoms, ldwMoveAtoms, dsyLoopAtoms, dsyLgAtoms, dsyNrAtoms, dsyRecAtoms,
    dsyRecBodyAtoms, dsyPosAtoms, dsyPosBodyAtoms]
  gcongr

theorem dsyAtomsM_le {M : ℕ} (h2 : 2 ≤ M) : dsyAtomsM M ≤ 160 * M ^ 3 := by
  simp only [dsyAtomsM, ldw1Atoms, ldwPart1Atoms, ldwPart2Atoms, ldwP1Atoms, ldwP2OAtoms,
    ldwP2Atoms, ldwMoveAtoms, dsyLoopAtoms, dsyLgAtoms, dsyNrAtoms, dsyRecAtoms, dsyRecBodyAtoms,
    dsyPosAtoms, dsyPosBodyAtoms]
  have h1 : M ≤ M ^ 2 := by nlinarith
  have h2' : M ^ 2 ≤ M ^ 3 := by nlinarith
  have h3 : 8 ≤ M ^ 3 := by nlinarith
  ring_nf
  nlinarith

theorem dsyW_le {N ℓ M : ℕ} (hN : N ≤ M) (hℓ : ℓ ≤ M) (h2 : 2 ≤ M) : dsyW N ℓ ≤ 4 * M ^ 2 := by
  unfold dsyW
  have := Nat.mul_le_mul hN hN
  nlinarith

theorem dsy_tblC_le {W M : ℕ} (h2 : 2 ≤ M) (hW : W ≤ 4 * M ^ 2) : tblC W 1 ≤ 808 * M ^ 4 := by
  unfold tblC
  have h4 : 4 ≤ M ^ 2 := by nlinarith
  have := Nat.pow_le_pow_left (show W + 4 ≤ 5 * M ^ 2 by omega) 2
  have e : (5 * M ^ 2) ^ 2 = 25 * M ^ 4 := by ring
  have h1 : 1 ≤ M ^ 4 := Nat.one_le_pow _ _ (by omega)
  omega

/-- **The cost of the wire machine** at a common bound `M` of `N, ℓ, K, D`. -/
theorem dsySynCostG_le {N ℓ K D WL M : ℕ} (hN : N ≤ M) (hℓ : ℓ ≤ M) (hK : K ≤ M) (hD : D ≤ M)
    (h2 : 2 ≤ M) : dsySynCostG N ℓ K D WL ≤ 130000 * M ^ 7 + 20 * WL := by
  have hW := dsyW_le hN hℓ h2
  have hT := dsy_tblC_le h2 hW
  have hA := (dsyAtoms_le_M (K := K) hN hℓ hD).trans (dsyAtomsM_le h2)
  have hprod : dsyAtoms N ℓ K D * tblC (dsyW N ℓ) 1 ≤ 160 * M ^ 3 * (808 * M ^ 4) :=
    Nat.mul_le_mul hA hT
  have e : 160 * M ^ 3 * (808 * M ^ 4) = 129280 * M ^ 7 := by ring
  rw [e] at hprod
  have hNN : N * N ≤ M ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hN hN
  have hDℓ : D * (ℓ + 1) ≤ 2 * M ^ 2 := by
    calc D * (ℓ + 1) ≤ M * (M + 1) := Nat.mul_le_mul hD (by omega)
      _ ≤ M * (2 * M) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * M ^ 2 := by ring
  have hsum : N + ℓ + K + D ≤ 4 * M := by omega
  have hloads : (N + ℓ + K + D) * (4 * dsyW N ℓ + 10) ≤ 4 * M * (16 * M ^ 2 + 10) :=
    Nat.mul_le_mul hsum (by omega)
  have h1 : M ≤ M ^ 7 := Nat.le_self_pow (by norm_num) M
  have h2' : M ^ 2 ≤ M ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : M ^ 3 ≤ M ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have e3 : 4 * M * (16 * M ^ 2 + 10) = 64 * M ^ 3 + 40 * M := by ring
  rw [e3] at hloads
  unfold dsySynCostG dsyParkCost dsyWidthCost dsyLoadsCost
  nlinarith

/-! ### At the pipeline sizes -/

theorem dsy_sizes {n : ℕ} (hbig : Big n) :
    (dsyEs n).sum ≤ b n + 2 ∧ ℓ n ≤ b n + 2 ∧ K n ≤ b n + 2 ∧ (dsyEs n).length ≤ b n + 2 ∧
      dsW n ≤ 9 * (b n + 2) ∧ dsWW n ≤ 200 * (b n + 2) := by
  have hn := hbig.1
  have h1 := pm_logT_le hn
  have h2 := ℓ_le_logT hbig
  have h3 := K_le_d n
  have h4 := d_le_b n
  have h5 := ds_dsW_le hn
  have h6 := ds_dsWW_le hn
  rw [ds_sum_cvAx hn, ds_length_cvAx]
  omega

/-- **The cost of the wires program**: eventually
`dsyWiresCost n ≤ 2·10^7 (b n + 1)^7 + 30 · 2^ℓ · dsW n`. -/
theorem dsyWiresCost_le : ∀ᶠ n in atTop,
    dsyWiresCost n ≤ 2 * 10 ^ 7 * (b n + 1) ^ 7 + 30 * (r n * dsW n) := by
  filter_upwards [eventually_big] with n hbig
  have hn := hbig.1
  obtain ⟨hN, hℓ, hK, hD, hw, hWW⟩ := dsy_sizes hbig
  have hw1 : 1 ≤ dsW n := by unfold dsW; omega
  set M := b n + 2 with hM
  have h2 : 2 ≤ M := by omega
  have hG := dsySynCostG_le (WL := dsWL n (dsW n)) hN hℓ hK hD h2
  have hWL : dsWL n (dsW n) ≤ r n * dsW n + 3 * M ^ 2 := by
    unfold dsWL
    have hN' : logT n - ℓ n ≤ M := by rw [← ds_sum_cvAx hn]; exact hN
    have : (logT n - ℓ n) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hN' 2
    nlinarith
  have hr : r n ≤ r n * dsW n := Nat.le_mul_of_pos_right _ hw1
  have hM7 : M ^ 7 ≤ 128 * (b n + 1) ^ 7 := by
    have : M ≤ 2 * (b n + 1) := by omega
    calc M ^ 7 ≤ (2 * (b n + 1)) ^ 7 := Nat.pow_le_pow_left this 7
      _ = 128 * (b n + 1) ^ 7 := by ring
  have hM2 : M ^ 2 ≤ M ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hM1 : M ≤ M ^ 7 := Nat.le_self_pow (by norm_num) M
  unfold dsyWiresCost dsyTailCost
  nlinarith

/-- The park record alone has at least `2^ℓ dsW n` symbols: the term `2^ℓ dsW n` of the cost
cannot be avoided by any program writing `mnσ (blP₀ dsW n) v₀` on `park`. -/
theorem dsyWires_lower (n : ℕ) (v₀ : SynW → List (Fin (bdA + 4))) :
    2 ^ ℓ n * dsW n ≤ (mnσ (blP₀ dsW n) v₀ .park).length := by
  rw [mnσ_park]
  unfold blP₀ slyPark blW slyW
  simp only [List.length_cons, List.length_append, List.length_reverse, length_binSyms,
    List.length_replicate, List.length_nil]
  omega

/-! ### The stash cost of the wires -/

theorem dsy_nRounds_le (n : ℕ) : nRounds (cvAx (t n)) ≤ ℓ n :=
  Finset.sup_le fun _ _ => log_t_le n _

/-- The stash cost of the persistent wires: `2 · 2^ℓ + O((b n + 1)^2)`. -/
theorem dsyStash_le : ∀ᶠ n in atTop,
    synStashCostW (dsyV₀ n) synXS ≤ 2 * r n + 800 * (b n + 1) ^ 2 := by
  filter_upwards [eventually_big] with n hbig
  have hn := hbig.1
  have H := ds_layHyp hbig
  obtain ⟨hN, hℓ, hK, hD, hw, -⟩ := dsy_sizes hbig
  have hb : layB (ℓ n) (K n) ≤ ℓ n := le_trans (Nat.mod_le _ _) (Nat.sub_le _ _)
  have hLg : (layLongs (List.ofFn (cvAx (t n))) (ℓ n)).length ≤ (List.ofFn (cvAx (t n))).sum := by
    have := lay_sum H; omega
  have hrec := dsy_length_topRec_le (A := bdA) H
  have hpos := dsy_length_twPosReg (A := bdA) (List.ofFn (cvAx (t n))).sum
    (twPosL (layPerm (List.ofFn (cvAx (t n))) (ℓ n) (K n))) (fun k hk => (twPosL_lt _ k hk).le)
  have hnr := dsy_nRounds_le n
  simp only [synXS, synStashCostW, dsyV₀, dsyEs, List.length_replicate, List.length_nil]
  rw [hpos]
  simp only [dsyEs] at hN hD
  set M := b n + 2 with hM
  have hM1 : M ≤ 2 * (b n + 1) := by omega
  have hM : M * M ≤ 4 * (b n + 1) ^ 2 := by
    calc M * M ≤ (2 * (b n + 1)) * (2 * (b n + 1)) := Nat.mul_le_mul hM1 hM1
      _ = 4 * (b n + 1) ^ 2 := by ring
  have hM' : M ≤ 4 * (b n + 1) ^ 2 := by nlinarith
  have hNN : (List.ofFn (cvAx (t n))).sum * (List.ofFn (cvAx (t n))).sum ≤ 4 * (b n + 1) ^ 2 :=
    le_trans (Nat.mul_le_mul hN hN) hM
  have hDℓ : (List.ofFn (cvAx (t n))).length * (ℓ n + 1) ≤ 8 * (b n + 1) ^ 2 := by
    calc (List.ofFn (cvAx (t n))).length * (ℓ n + 1) ≤ M * (M + 1) :=
          Nat.mul_le_mul hD (by omega)
      _ ≤ M * (2 * M) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (M * M) := by ring
      _ ≤ 8 * (b n + 1) ^ 2 := by omega
  omega

/-- The stash cost of the persistent wires is at least `2 · 2^ℓ` (the wire `p .r`). -/
theorem dsyStash_ge (n : ℕ) : 2 * r n ≤ synStashCostW (dsyV₀ n) synXS := by
  simp only [synXS, synStashCostW, dsyV₀, List.length_replicate, List.length_nil]
  omega

end

end IntegerMultBounds.MathlibTM2.Fast.Main
