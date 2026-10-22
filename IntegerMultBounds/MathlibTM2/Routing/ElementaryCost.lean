module

public import IntegerMultBounds.MathlibTM2.Routing.ConfigurationSize
public import IntegerMultBounds.MathlibTM2.Routing.ElementaryLoopData

/-!
# Closed elementary routing costs

The two bit exchanges have width at most one. Their actual bank-size terms are
bounded by the reusable bank plus the current raw frame; archived earlier frames
do not enter. The scan is linear in volume when record width dominates address
width. All metadata installation and cleanup costs are retained.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem elementarySwap_max {n : ℕ} (t : Fin n) : max 1 (elementarySwapSpec t).w = 1 := by
  by_cases ht : t.val = 0 <;> simp [elementarySwapSpec, ht]

theorem elementaryXorCost_eq {t₀ T K n : ℕ} (rg : LayReg t₀ → Fin T)
    (t : Fin n) (rows B : ℕ) (S : Stacks T (prime + K)) :
    elementaryXorCost rg t rows B S =
      6 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (rows * 2 ^ n * B : ℕ) +
        2 * (6 * ∑ j, (S.R (rg (.sw j))).length + 34 * (rows * 2 ^ n * B) +
          2 * T + 6 * swapT t₀ + 23 : ℕ) + elementaryScanCost n (rows * 2 ^ n) B := by
  simp only [elementaryXorCost, exchangeStepCost, elementarySwap_max,
    Nat.cast_one, Real.one_rpow, mul_one]
  ring

/-- Both actual bit exchanges and the scan have linear volume cost, plus bank size. -/
theorem elementaryXorCost_le {t₀ T K n : ℕ} (rg : LayReg t₀ → Fin T)
    (t : Fin n) (rows B bankSize : ℕ) (S : Stacks T (prime + K))
    (hrows : 0 < rows) (hB : 1 ≤ B) (hn : n ≤ B)
    (hbank : (∑ j, (S.R (rg (.sw j))).length) ≤ bankSize) :
    elementaryXorCost rg t rows B S ≤
      6 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (rows * 2 ^ n * B : ℕ) +
        (12 * bankSize + 176 * (rows * 2 ^ n * B) + 4 * T + 12 * swapT t₀ + 46 : ℕ) := by
  have hm : 1 ≤ rows * 2 ^ n := by
    have h : 0 < rows * 2 ^ n := Nat.mul_pos hrows (by positivity)
    omega
  have hscan := elementaryScanCost_le_volume n (rows * 2 ^ n) B hm hB hn
  have hnat : 2 * (6 * ∑ j, (S.R (rg (.sw j))).length + 34 * (rows * 2 ^ n * B) +
      2 * T + 6 * swapT t₀ + 23) + elementaryScanCost n (rows * 2 ^ n) B ≤
        12 * bankSize + 176 * (rows * 2 ^ n * B) + 4 * T + 12 * swapT t₀ + 46 := by nlinarith
  rw [elementaryXorCost_eq]
  have hr : ((2 * (6 * ∑ j, (S.R (rg (.sw j))).length + 34 * (rows * 2 ^ n * B) +
      2 * T + 6 * swapT t₀ + 23) + elementaryScanCost n (rows * 2 ^ n) B : ℕ) : ℝ) ≤
        (12 * bankSize + 176 * (rows * 2 ^ n * B) + 4 * T + 12 * swapT t₀ + 46 : ℕ) := by exact_mod_cast hnat
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hr ⊢
  linarith only [hr]

/-- Installing the current frame grows the actual interchange bank by at most
its size times the frame length; no archived prefix is charged here. -/
theorem elementaryLoaded_bankSize {t₀ T A n : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : LayReg t₀ → Fin T) (hd : Fin 5 → Fin t₀) (config saved : Fin T)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (d : ElementaryInstruction n) (rest : List (Fin (A + 4))) :
    (∑ j, (elementaryLoaded R rg hd config saved n
      ((elementarySwapSpec d.target).coordinate d.source).val d.headers rest (rg (.sw j))).length) ≤
      (∑ j, (R (rg (.sw j))).length) + swapT t₀ * (d.frame : List (Fin (A + 4))).length := by
  have h : ∀ j : Fin (swapT t₀),
      (elementaryLoaded R rg hd config saved n
        ((elementarySwapSpec d.target).coordinate d.source).val d.headers rest (rg (.sw j))).length ≤
          (R (rg (.sw j))).length + (d.frame : List (Fin (A + 4))).length := by
    intro j
    exact configurationBatchLoaded_length_le R config (rg .tmp) saved _ _ rest (rg (.sw j))
      (hconfig (.sw j)).symm (hsaved (.sw j)).symm
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] using hs

/-- Empty mutable destinations cost at most twelve frame lengths plus thirteen to clear. -/
theorem elementaryLoaded_cleanCost {t₀ T A n : ℕ} (R : Fin T → List (Fin (A + 4)))
    (rg : LayReg t₀ → Fin T) (hd : Fin 5 → Fin t₀) (config saved : Fin T)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (hempty : ∀ key, R (elementaryConfigTarget rg hd key) = [])
    (d : ElementaryInstruction n) (rest : List (Fin (A + 4))) :
    metadataCleanCost (elementaryLoaded R rg hd config saved n
      ((elementarySwapSpec d.target).coordinate d.source).val d.headers rest) (elementaryConfigKeys rg hd) ≤
        12 * (d.frame : List (Fin (A + 4))).length + 13 := by
  have h := metadataCleanCost_le
    (elementaryLoaded R rg hd config saved n ((elementarySwapSpec d.target).coordinate d.source).val d.headers rest)
    (elementaryConfigKeys rg hd) (d.frame : List (Fin (A + 4))).length (by
      intro j hj
      obtain ⟨key, rfl⟩ := List.mem_ofFn.mp hj
      have hb := configurationBatchLoaded_length_le R config (rg .tmp) saved
        (List.ofFn (elementaryConfigSlot rg hd)) d.words rest (elementaryConfigTarget rg hd key) ?_ ?_
      · change (elementaryLoaded R rg hd config saved n
          ((elementarySwapSpec d.target).coordinate d.source).val d.headers rest
          (elementaryConfigTarget rg hd key)).length ≤
            (R (elementaryConfigTarget rg hd key)).length + (d.frame : List (Fin (A + 4))).length at hb
        simpa only [hempty key, List.length_nil, Nat.zero_add] using hb
      · rcases elementaryConfigTarget_role rg hd key with ⟨j, hj⟩ | hj <;>
          rw [hj] <;> exact (hconfig _).symm
      · rcases elementaryConfigTarget_role rg hd key with ⟨j, hj⟩ | hj <;>
          rw [hj] <;> exact (hsaved _).symm)
  have hlen : (elementaryConfigKeys rg hd).length = 6 := by simp [elementaryConfigKeys]
  rw [hlen] at h
  omega

private theorem elementaryMetadataCost_algebra (setup clean bank tapes F V T : ℕ)
    (hs : setup ≤ 6 * F + 1) (hc : clean ≤ 12 * F + 13) :
    setup + clean + (12 * (bank + tapes * F) + 176 * V + 4 * T + 12 * tapes + 46) ≤
      12 * bank + 176 * V + (12 * tapes + 18) * F + 4 * T + 12 * tapes + 60 := by
  nlinarith only [hs, hc]

private theorem elementaryStepCost_algebra (setup clean x a V bank tapes F T : ℝ)
    (hx : x ≤ a * V + (12 * (bank + tapes * F) + 176 * V + 4 * T + 12 * tapes + 46))
    (hm : setup + clean + (12 * (bank + tapes * F) + 176 * V + 4 * T + 12 * tapes + 46) ≤
      12 * bank + 176 * V + (12 * tapes + 18) * F + 4 * T + 12 * tapes + 60) :
    setup + x + clean ≤ (a + 176) * V +
      (12 * bank + (12 * tapes + 18) * F + 4 * T + 12 * tapes + 60) := by
  nlinarith only [hx, hm]

/-- One fully configured call has linear volume cost plus its raw frame and
restored interchange bank. This bounds the actual loader/execute/cleanup ledger. -/
theorem elementaryStepPrice_le {t₀ T K n : ℕ} (rg : LayReg t₀ → Fin T)
    (hd : Fin 5 → Fin t₀) (config saved : Fin T)
    (hconfig : ∀ r, config ≠ rg r) (hsaved : ∀ r, saved ≠ rg r)
    (rows B : ℕ) (hrows : 0 < rows) (hB : 1 ≤ B) (hn : n ≤ B)
    (S : Stacks T (prime + K)) (hempty : ∀ key, S.R (elementaryConfigTarget rg hd key) = [])
    (d : ElementaryInstruction n) (rest : List (Fin (prime + K + 4))) :
    elementaryStepPrice rg hd config saved rows B S d rest ≤
      (6 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) + 176) * (rows * 2 ^ n * B : ℕ) +
        (12 * ∑ j, (S.R (rg (.sw j))).length +
          (12 * swapT t₀ + 18) * (d.frame : List (Fin (prime + K + 4))).length +
          4 * T + 12 * swapT t₀ + 60 : ℕ) := by
  let installed := elementaryLoaded S.R rg hd config saved n
    ((elementarySwapSpec d.target).coordinate d.source).val d.headers rest
  let F := (d.frame : List (Fin (prime + K + 4))).length
  let bankSize := ∑ j, (S.R (rg (.sw j))).length
  let setup := configurationBatchCost (d.words (A := prime + K))
  let clean := metadataCleanCost installed (elementaryConfigKeys rg hd)
  have hsetup : setup ≤ 6 * F + 1 := configurationBatchCost_le d.words
  have hclean : clean ≤ 12 * F + 13 :=
    elementaryLoaded_cleanCost S.R rg hd config saved hconfig hsaved hempty d rest
  have hx := elementaryXorCost_le rg d.target rows B (bankSize + swapT t₀ * F)
    { S with R := installed } hrows hB hn
    (elementaryLoaded_bankSize S.R rg hd config saved hconfig hsaved d rest)
  have hnat : setup + clean + (12 * (bankSize + swapT t₀ * F) + 176 * (rows * 2 ^ n * B) +
      4 * T + 12 * swapT t₀ + 46) ≤
        12 * bankSize + 176 * (rows * 2 ^ n * B) + (12 * swapT t₀ + 18) * F +
          4 * T + 12 * swapT t₀ + 60 :=
    elementaryMetadataCost_algebra setup clean bankSize (swapT t₀) F (rows * 2 ^ n * B) T hsetup hclean
  have hr : (setup : ℝ) + clean + (12 * (bankSize + swapT t₀ * F) + 176 * (rows * 2 ^ n * B) +
      4 * T + 12 * swapT t₀ + 46 : ℕ) ≤
        (12 * bankSize + 176 * (rows * 2 ^ n * B) + (12 * swapT t₀ + 18) * F +
          4 * T + 12 * swapT t₀ + 60 : ℕ) := by exact_mod_cast hnat
  change (setup : ℝ) + elementaryXorCost rg d.target rows B { S with R := installed } + clean ≤ _
  change (setup : ℝ) + elementaryXorCost rg d.target rows B { S with R := installed } + clean ≤
    (6 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) + 176) * (rows * 2 ^ n * B : ℕ) +
      (12 * bankSize + (12 * swapT t₀ + 18) * F + 4 * T + 12 * swapT t₀ + 60 : ℕ)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hr hx ⊢
  exact elementaryStepCost_algebra _ _ _ _ _ _ _ _ _ hx hr

end IntegerMultBounds.MathlibTM2.Routing
