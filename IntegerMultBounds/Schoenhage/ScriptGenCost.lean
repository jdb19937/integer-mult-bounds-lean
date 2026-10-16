module

public import IntegerMultBounds.Schoenhage.ScriptGen
public import IntegerMultBounds.Schoenhage.LayoutGenCost

/-! §6, the round-script writers' steps within the paper's bound. Every piece of
`ScriptGen.writerCost` is a polynomial in the instance's sizes (bounded by `B = (⌈C_l⌉ + 1) w`),
possibly times `2^ℓ`, except the slot loop's power words, of length at most `2^(ℓ + 1) ∏ tᵢ`, and
the script itself. Beyond a cutoff the polynomial is at most `2^(ℓ - 1) ≤ ∏ tᵢ`, so the writer is
within a fixed multiple of `ℓ` record volumes (`writerCost_le_volume`), hence of the paper's bound
(`writerCost_le_transformCost`). -/

@[expose] public section

set_option maxRecDepth 100000

namespace IntegerMultBounds.Schoenhage

open Machine Spec.SignedRingProduct TwistDescriptors ScriptOps ScriptParts ScriptMain ScriptPrep Filter

namespace ScriptGenCost

/-! ### Bounds up to a polynomial factor -/

section Dom

variable {ι : Type*} {S : Set ι} {B E : ι → ℕ}

/-- `f` is at most a polynomial in `B` times `E + 1` on `S`, with fixed degree and constant. -/
def Dom (S : Set ι) (B E : ι → ℕ) (f : ι → ℕ) : Prop :=
  ∃ k c : ℕ, ∀ i ∈ S, f i ≤ c * (B i + 1) ^ k * (E i + 1)

theorem dom_const (n : ℕ) : Dom S B E (fun _ => n) :=
  ⟨0, n, fun i _ => by simp only [pow_zero, mul_one]; exact Nat.le_mul_of_pos_right _ (by omega)⟩

theorem dom_atom {f : ι → ℕ} (h : ∀ i ∈ S, f i ≤ 100 * (B i + 1)) : Dom S B E f :=
  ⟨1, 100, fun i hi => by
    have := h i hi
    calc f i ≤ 100 * (B i + 1) ^ 1 * 1 := by simpa using this
      _ ≤ 100 * (B i + 1) ^ 1 * (E i + 1) := Nat.mul_le_mul_left _ (by omega)⟩

theorem dom_atomE {f : ι → ℕ} (h : ∀ i ∈ S, f i ≤ 100 * (E i + 1)) : Dom S B E f :=
  ⟨0, 100, fun i hi => by simpa using h i hi⟩

theorem dom_add {f g : ι → ℕ} (hf : Dom S B E f) (hg : Dom S B E g) : Dom S B E (fun i => f i + g i) := by
  obtain ⟨k₁, c₁, h₁⟩ := hf
  obtain ⟨k₂, c₂, h₂⟩ := hg
  refine ⟨k₁ + k₂, c₁ + c₂, fun i hi => ?_⟩
  have a₁ : (B i + 1) ^ k₁ ≤ (B i + 1) ^ (k₁ + k₂) := Nat.pow_le_pow_right (by omega) (by omega)
  have a₂ : (B i + 1) ^ k₂ ≤ (B i + 1) ^ (k₁ + k₂) := Nat.pow_le_pow_right (by omega) (by omega)
  have b₁ := Nat.mul_le_mul_right (E i + 1) (Nat.mul_le_mul_left c₁ a₁)
  have b₂ := Nat.mul_le_mul_right (E i + 1) (Nat.mul_le_mul_left c₂ a₂)
  have := h₁ i hi
  have := h₂ i hi
  calc f i + g i ≤ c₁ * (B i + 1) ^ (k₁ + k₂) * (E i + 1) + c₂ * (B i + 1) ^ (k₁ + k₂) * (E i + 1) := by omega
    _ = (c₁ + c₂) * (B i + 1) ^ (k₁ + k₂) * (E i + 1) := by ring

theorem dom_le {f g : ι → ℕ} (hg : Dom S B E g) (h : ∀ i ∈ S, f i ≤ g i) : Dom S B E f := by
  obtain ⟨k, c, hk⟩ := hg
  exact ⟨k, c, fun i hi => (h i hi).trans (hk i hi)⟩

theorem dom_sub {f g : ι → ℕ} (hf : Dom S B E f) : Dom S B E (fun i => f i - g i) :=
  dom_le hf fun _ _ => Nat.sub_le _ _

theorem dom_div {f g : ι → ℕ} (hf : Dom S B E f) : Dom S B E (fun i => f i / g i) :=
  dom_le hf fun _ _ => Nat.div_le_self _ _

theorem dom_mod {f g : ι → ℕ} (hf : Dom S B E f) : Dom S B E (fun i => f i % g i) :=
  dom_le hf fun _ _ => Nat.mod_le _ _

theorem dom_min {f g : ι → ℕ} (hf : Dom S B E f) : Dom S B E (fun i => min (f i) (g i)) :=
  dom_le hf fun _ _ => min_le_left _ _

theorem dom_mul {f g : ι → ℕ} (hf : Dom S B (fun _ => 0) f) (hg : Dom S B E g) :
    Dom S B E (fun i => f i * g i) := by
  obtain ⟨k₁, c₁, h₁⟩ := hf
  obtain ⟨k₂, c₂, h₂⟩ := hg
  refine ⟨k₁ + k₂, c₁ * c₂, fun i hi => ?_⟩
  have := Nat.mul_le_mul (h₁ i hi) (h₂ i hi)
  calc f i * g i ≤ c₁ * (B i + 1) ^ k₁ * (0 + 1) * (c₂ * (B i + 1) ^ k₂ * (E i + 1)) := this
    _ = c₁ * c₂ * (B i + 1) ^ (k₁ + k₂) * (E i + 1) := by ring

theorem dom_mul' {f g : ι → ℕ} (hf : Dom S B E f) (hg : Dom S B (fun _ => 0) g) :
    Dom S B E (fun i => f i * g i) := by
  simp only [Nat.mul_comm (f _)]
  exact dom_mul hg hf

theorem dom_zeroE {f : ι → ℕ} (hf : Dom S B (fun _ => 0) f) : Dom S B E f := by
  obtain ⟨k, c, h⟩ := hf
  exact ⟨k, c, fun i hi => (h i hi).trans (Nat.mul_le_mul_left _ (by simp))⟩

theorem dom_mul_bound {f n : ι → ℕ} (hn : Dom S B (fun _ => 0) n) (k c : ℕ)
    (h : ∀ i ∈ S, f i ≤ n i * (c * (B i + 1) ^ k * (E i + 1) + 2)) : Dom S B E f := by
  have hX : Dom S B E (fun i => c * (B i + 1) ^ k * (E i + 1) + 2) :=
    dom_add ⟨k, c, fun i _ => le_rfl⟩ (dom_const 2)
  exact dom_le (dom_mul hn hX) h

end Dom

/-! ### The instances -/

/-- An instance of the writer, with a slot `h`, a chunk group `c` and a header `ρ`. -/
structure Inst where
  p : ℕ
  d : ℕ
  ℓ : ℕ
  K : ℕ
  w : ℕ
  ts : List ℕ
  h : ℕ
  c : ℕ
  ρ : ℕ

/-- The admissible instances with `w ≤ 2^ℓ`, `h ≤ ℓ`, `c ≤ ⌊(ℓ - 1) / K⌋` and `ρ ≤ K`. -/
def Adm (P : TransformParams) : Set Inst :=
  {i | Admissible P i.p i.d i.ℓ i.K i.w i.ts ∧ i.w ≤ 2 ^ i.ℓ ∧ i.h ≤ i.ℓ ∧ i.c ≤ (i.ℓ - 1) / i.K ∧ i.ρ ≤ i.K}

/-- The size bound `B = (⌈C_l⌉ + 1) w`. -/
noncomputable def sizeB (P : TransformParams) (i : Inst) : ℕ := (⌈P.Cl⌉₊ + 1) * i.w

/-- The weight `2^ℓ`. -/
def powR (i : Inst) : ℕ := 2 ^ i.ℓ

theorem eZero_le_log {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) :
    ScriptGen.eZero ℓ K ts ≤ Nat.log 2 ts.prod := by
  rw [log_prod_layout hL]
  unfold ScriptGen.eZero
  have e1 : (ℓ - 1) / K * (ts.length * K) = ts.length * ((ℓ - 1) / K) * K := by ring
  have e2 : (ℓ - 1) % K * ts.length = ts.length * ((ℓ - 1) % K) := by ring
  omega

/-- The sizes of an admissible instance, all within `B`. -/
theorem sizes {P : TransformParams} {i : Inst} (hi : i ∈ Adm P) :
    i.p ≤ sizeB P i ∧ i.d ≤ sizeB P i ∧ i.ℓ ≤ sizeB P i ∧ i.ts.length ≤ sizeB P i ∧ i.K + 1 ≤ i.ℓ ∧
      1 ≤ i.K ∧ 2 ≤ i.ℓ ∧ Nat.log 2 i.ts.prod ≤ sizeB P i ∧ i.w ≤ sizeB P i ∧
      (longs i.ts i.ℓ).length ≤ i.ts.length ∧ i.h ≤ i.ℓ ∧ i.c ≤ i.ℓ ∧ i.ρ ≤ i.K ∧
      ScriptGen.eZero i.ℓ i.K i.ts ≤ Nat.log 2 i.ts.prod ∧ i.ts.length + 1 = i.d := by
  obtain ⟨hadm, hwr, hh, hc, hρ⟩ := hi
  obtain ⟨hpow, hnC, hdD, hD, hdl, hℓp, hpw, hKℓ, hK, hℓ, hw2, hlow, hnD⟩ := adm_sizes hadm hwr
  have hB : sizeB P i = ⌈P.Cl⌉₊ * i.w + i.w := by unfold sizeB; ring
  have hdℓ : i.d ≤ i.d * i.ℓ := Nat.le_mul_of_pos_right _ (by omega)
  have hℓd : i.ℓ ≤ i.d * i.ℓ := Nat.le_mul_of_pos_left _ (by omega)
  have hq : (i.ℓ - 1) / i.K ≤ i.ℓ := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  exact ⟨by omega, by omega, by omega, by omega, hKℓ, hK, hℓ, by omega, by omega, longs_length_le _ _, hh,
    by omega, hρ, eZero_le_log (layoutOK_of_admissible hadm), by omega⟩

theorem pow_le_powR {i : Inst} {a : ℕ} (h : a ≤ i.ℓ + 1) : 2 ^ a ≤ 100 * (powR i + 1) := by
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
  rw [pow_succ] at this
  unfold powR; omega

theorem w0_le_powR {i : Inst} (b : ℕ) : 2 * (2 * 2 ^ i.ℓ / 2 ^ (b + 1)) * 2 ^ b ≤ 100 * (powR i + 1) := by
  have h1 := Nat.div_mul_le_self (2 * 2 ^ i.ℓ) (2 ^ (b + 1))
  rw [pow_succ] at h1
  have e : 2 * (2 * 2 ^ i.ℓ / (2 ^ b * 2)) * 2 ^ b = 2 * 2 ^ i.ℓ / (2 ^ b * 2) * (2 ^ b * 2) := by ring
  rw [pow_succ, e]
  unfold powR; omega

theorem gamma_mod_le (a K : ℕ) : (gamma (a % K + 1)).length ≤ 2 * a + 3 := by
  have := hdrGamma_le (a % K + 1)
  have := Nat.mod_le a K
  omega

/-- The closure steps of `Dom`, with atoms within `100 (B + 1)` (by `omega` from `sizes`) or
`100 (2^ℓ + 1)`. -/
syntax "dom_tac" : tactic
macro_rules
  | `(tactic| dom_tac) => `(tactic| first
    | with_reducible exact dom_const _
    | with_reducible assumption
    | ((with_reducible apply dom_add) <;> dom_tac)
    | ((with_reducible apply dom_sub); dom_tac)
    | ((with_reducible apply dom_div); dom_tac)
    | ((with_reducible apply dom_mod); dom_tac)
    | ((with_reducible apply dom_min); dom_tac)
    | ((with_reducible apply dom_atomE); intro i hi; first | (with_reducible refine pow_le_powR ?_); omega | with_reducible exact w0_le_powR _)
    | ((with_reducible apply dom_mul) <;> dom_tac)
    | ((with_reducible apply dom_mul') <;> dom_tac)
    | ((with_reducible apply dom_atom); intro i hi
       obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := sizes hi
       first
         | omega
         | ((with_reducible refine (gamma_mod_le _ _).trans ?_); omega)
         | ((with_reducible refine (hdrGamma_le _).trans ?_); omega))
    | ((with_reducible apply dom_zeroE); with_reducible assumption))

/-! ### The slot loop -/

/-! ### The word lists -/

theorem clen_rowWords_le {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) :
    clen (rowWords ts ℓ K) ≤ ts.length * (ℓ - 1) * (Nat.log 2 ts.prod + 1) := by
  have hlen : (rowWords ts ℓ K).length = ts.length * (ℓ - 1) := by
    simp [rowWords, List.length_flatMap, List.sum_replicate]
  rw [← hlen]
  refine clen_le_of fun x hx => ?_
  simp only [rowWords, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, h', hh, rfl⟩ := hx
  rw [length_ones]
  have hax : h' < axLen ts i := by rcases hL.2.1 i hi with e | e <;> omega
  exact (SigmaTableTape.paperSigma_lt hL hi hax).le

theorem clen_topsW_le {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) :
    clen (topsW ts ℓ K) ≤ (longs ts ℓ).length * (Nat.log 2 ts.prod + 1) := by
  have hlen : (topsW ts ℓ K).length = (longs ts ℓ).length := by simp [topsW]
  rw [← hlen]
  refine clen_le_of fun x hx => ?_
  simp only [topsW, List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  simp only [longs, List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
  rw [length_ones]
  have hℓ := hL.2.2.2
  exact (SigmaTableTape.paperSigma_lt hL hi.1 (by omega)).le

theorem clen_flagsW_le (ts : List ℕ) (ℓ : ℕ) : clen (flagsW ts ℓ) ≤ ts.length * 2 := by
  have hlen : (flagsW ts ℓ).length = ts.length := by simp [flagsW]
  rw [← hlen]
  refine clen_le_of fun x hx => ?_
  simp only [flagsW, List.mem_map] at hx
  obtain ⟨_, _, rfl⟩ := hx
  simp

theorem layoutOK_of_mem {P : TransformParams} {i : Inst} (hi : i ∈ Adm P) : LayoutOK (2 ^ i.ℓ) i.ts i.ℓ i.K :=
  layoutOK_of_admissible hi.1

section Atoms

variable {P : TransformParams} {E : Inst → ℕ}

theorem dom_rowWords : Dom (Adm P) (sizeB P) E (fun i => clen (rowWords i.ts i.ℓ i.K)) :=
  dom_le (g := fun i => i.ts.length * (i.ℓ - 1) * (Nat.log 2 i.ts.prod + 1)) (by dom_tac)
    fun _ hi => clen_rowWords_le (layoutOK_of_mem hi)

theorem dom_topsW : Dom (Adm P) (sizeB P) E (fun i => clen (topsW i.ts i.ℓ i.K)) :=
  dom_le (g := fun i => (longs i.ts i.ℓ).length * (Nat.log 2 i.ts.prod + 1)) (by dom_tac)
    fun _ hi => clen_topsW_le (layoutOK_of_mem hi)

theorem dom_flagsW : Dom (Adm P) (sizeB P) E (fun i => clen (flagsW i.ts i.ℓ)) :=
  dom_le (g := fun i => i.ts.length * 2) (by dom_tac) fun _ _ => clen_flagsW_le _ _

end Atoms

/-! ### The preparation -/

theorem dom_prep (P : TransformParams) :
    Dom (Adm P) (sizeB P) (fun _ => 0) (fun i => prepCost i.ℓ i.K i.d i.ts) := by
  have h1 : Dom (Adm P) (sizeB P) (fun _ => 0) (fun i => clen (rowWords i.ts i.ℓ i.K)) := dom_rowWords
  have h2 : Dom (Adm P) (sizeB P) (fun _ => 0) (fun i => clen (topsW i.ts i.ℓ i.K)) := dom_topsW
  have h3 : Dom (Adm P) (sizeB P) (fun _ => 0) (fun i => clen (flagsW i.ts i.ℓ)) := dom_flagsW
  simp only [prepCost, costAB, costC, costD, SigmaConstsTape.constsTopCost, SigmaRowsTape.axisCost,
    SigmaRowsTape.groupCost]
  dom_tac

theorem mem_withH {P : TransformParams} {i : Inst} (hi : i ∈ Adm P) {h : ℕ} (hh : h ≤ i.ℓ) :
    { i with h := h } ∈ Adm P := ⟨hi.1, hi.2.1, hh, hi.2.2.2⟩

theorem mem_withC {P : TransformParams} {i : Inst} (hi : i ∈ Adm P) {c : ℕ} (hc : c ≤ (i.ℓ - 1) / i.K) :
    { i with c := c } ∈ Adm P := ⟨hi.1, hi.2.1, hi.2.2.1, hc, hi.2.2.2.2⟩

theorem mem_withRho {P : TransformParams} {i : Inst} (hi : i ∈ Adm P) {ρ : ℕ} (hρ : ρ ≤ i.K) :
    { i with ρ := ρ } ∈ Adm P := ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hρ⟩

/-! ### The header pass -/

theorem innerCost_le {p d ℓ D K w eP eS U : ℕ} : ∀ (r ρ : ℕ),
    (∀ j, ρ ≤ j → j < ρ + r → ScriptHdr.hdrCost p d ℓ D K w eP eS j ≤ U) →
      ScriptHdr.innerCost p d ℓ D K w eP eS ρ r ≤ r * (U + 2)
  | 0, _, _ => by simp [ScriptHdr.innerCost]
  | r + 1, ρ, h => by
    have h1 := h ρ le_rfl (by omega)
    have h2 := innerCost_le r (ρ + 1) fun j hj hj' => h j (by omega) (by omega)
    simp only [ScriptHdr.innerCost]
    rw [Nat.succ_mul]
    omega

theorem passCost_le {p d ℓ D K w e0 DK U : ℕ} : ∀ (r c : ℕ),
    (∀ j, c ≤ j → j < c + r → ScriptHdr.groupCost p d ℓ D K w e0 DK j ≤ U) →
      ScriptHdr.passCost p d ℓ D K w e0 DK c r ≤ r * (U + 2)
  | 0, _, _ => by simp [ScriptHdr.passCost]
  | r + 1, c, h => by
    have h1 := h c le_rfl (by omega)
    have h2 := passCost_le r (c + 1) fun j hj hj' => h j (by omega) (by omega)
    simp only [ScriptHdr.passCost]
    rw [Nat.succ_mul]
    omega

theorem dom_hdr (P : TransformParams) : Dom (Adm P) (sizeB P) (fun _ => 0) (fun i =>
    ScriptHdr.hdrCost i.p i.d i.ℓ i.ts.length i.K i.w (ScriptGen.eZero i.ℓ i.K i.ts - i.c * (i.ts.length * i.K))
      (i.c * (i.ts.length * i.K)) i.ρ) := by
  simp only [ScriptHdr.hdrCost, clen_cons, clen_nil, layerHeader,
    List.length_append, hdrGamma_pow]
  dom_tac

theorem dom_inner (P : TransformParams) : Dom (Adm P) (sizeB P) (fun _ => 0) (fun i =>
    ScriptHdr.innerCost i.p i.d i.ℓ i.ts.length i.K i.w (ScriptGen.eZero i.ℓ i.K i.ts - i.c * (i.ts.length * i.K))
      (i.c * (i.ts.length * i.K)) 0 i.K) := by
  obtain ⟨k, c, hk⟩ := dom_hdr P
  refine dom_mul_bound (n := fun i => i.K) (by dom_tac) k c fun i hi => innerCost_le _ _ fun j _ hj => ?_
  exact (hk { i with ρ := j } (mem_withRho hi (by omega))).trans (by simp [sizeB])

theorem dom_group (P : TransformParams) : Dom (Adm P) (sizeB P) (fun _ => 0) (fun i =>
    ScriptHdr.groupCost i.p i.d i.ℓ i.ts.length i.K i.w (ScriptGen.eZero i.ℓ i.K i.ts) (i.ts.length * i.K) i.c) := by
  have := dom_inner P
  simp only [ScriptHdr.groupCost]
  dom_tac

theorem dom_costH (P : TransformParams) :
    Dom (Adm P) (sizeB P) (fun _ => 0) (fun i => ScriptGen.costH i.p i.d i.ℓ i.K i.w i.ts) := by
  obtain ⟨k, c, hk⟩ := dom_group P
  have hpass : Dom (Adm P) (sizeB P) (fun _ => 0) (fun i => ScriptHdr.passCost i.p i.d i.ℓ i.ts.length i.K i.w
      (ScriptGen.eZero i.ℓ i.K i.ts) (i.ts.length * i.K) 0 ((i.ℓ - 1) / i.K)) := by
    refine dom_mul_bound (n := fun i => (i.ℓ - 1) / i.K) (by dom_tac) k c fun i hi =>
      passCost_le _ _ fun j _ hj => ?_
    exact (hk { i with c := j } (mem_withC hi (by omega))).trans (by simp [sizeB])
  simp only [ScriptGen.costH]
  dom_tac

/-! ### The slot loop -/

/-- A slot step's cost without its two power words. -/
def stepRest (p d w ℓ K : ℕ) (ts : List ℕ) (h : ℕ) : ℕ :=
  2 * (ℓ - 1) + 2 * h + 30 + 1 + (2 * (longs ts ℓ).length + 2 * (ℓ - 1) + 2 * h + 200 +
    (clen [[false]] + 1 + (1 + (2 * (longs ts ℓ).length + 10))) + twTopCost ℓ K ts +
    (8 * preExp ℓ K ts (min h ((ℓ - 1) % K)) + 2 * ts.length + 100) +
    (clen [[true]] + 1 + (3 * (chunkHdr p d (2 ^ ℓ) w (Nat.log 2 ts.prod) ts ℓ K h).length + 15)) +
    ScriptMain.twCost ℓ K ts h) + 1 + (decCost ts.length (h + 1) + 1 + 5)

theorem stepCost_eq (p d w ℓ K : ℕ) (ts : List ℕ) (h : ℕ) :
    stepCost p d w ℓ K ts h = stepRest p d w ℓ K ts h + powOutCost (topExp ℓ K ts) +
      powOutCost (preExp ℓ K ts (min h ((ℓ - 1) % K))) := by
  simp only [stepCost, stepRest, bodyCost, hadPreCost]
  omega

theorem powOutCost_le (e : ℕ) : powOutCost e ≤ 100 * (e + 1) * 2 ^ e := by
  have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have h2 : e ≤ e * 2 ^ e := Nat.le_mul_of_pos_right _ h1
  unfold powOutCost
  nlinarith

theorem two_pow_topExp_le {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) :
    topExp ℓ K ts ≤ ℓ + 1 + Nat.log 2 ts.prod ∧ 2 ^ topExp ℓ K ts ≤ 2 ^ (ℓ + 1) * 2 ^ Nat.log 2 ts.prod := by
  have hn := log_prod_layout hL
  have e1 : (ℓ - 1) / K * (ts.length * K) = ts.length * ((ℓ - 1) / K) * K := by ring
  have e2 : (ℓ - 1) % K * ts.length = ts.length * ((ℓ - 1) % K) := by ring
  have hle : topExp ℓ K ts ≤ ℓ + 1 + Nat.log 2 ts.prod := by unfold topExp; omega
  refine ⟨hle, ?_⟩
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) hle

/-- The power words of one step: at most `200 (ℓ + 2 + n) 2^(ℓ + 1) 2^n`. -/
theorem powWords_le {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (h : ℕ) :
    powOutCost (topExp ℓ K ts) + powOutCost (preExp ℓ K ts (min h ((ℓ - 1) % K))) ≤
      200 * (ℓ + 2 + Nat.log 2 ts.prod) * (2 ^ (ℓ + 1) * 2 ^ Nat.log 2 ts.prod) := by
  obtain ⟨hT, hT2⟩ := two_pow_topExp_le hL
  have hpre : preExp ℓ K ts (min h ((ℓ - 1) % K)) ≤ topExp ℓ K ts := by
    unfold preExp topExp
    have := Nat.mul_le_mul_right ts.length (min_le_right h ((ℓ - 1) % K))
    omega
  have a1 := powOutCost_le (topExp ℓ K ts)
  have a2 := powOutCost_le (preExp ℓ K ts (min h ((ℓ - 1) % K)))
  have b1 : 2 ^ preExp ℓ K ts (min h ((ℓ - 1) % K)) ≤ 2 ^ topExp ℓ K ts := Nat.pow_le_pow_right (by norm_num) hpre
  have c1 : 100 * (topExp ℓ K ts + 1) * 2 ^ topExp ℓ K ts ≤
      100 * (ℓ + 2 + Nat.log 2 ts.prod) * (2 ^ (ℓ + 1) * 2 ^ Nat.log 2 ts.prod) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hT2
  have c2 : 100 * (preExp ℓ K ts (min h ((ℓ - 1) % K)) + 1) * 2 ^ preExp ℓ K ts (min h ((ℓ - 1) % K)) ≤
      100 * (ℓ + 2 + Nat.log 2 ts.prod) * (2 ^ (ℓ + 1) * 2 ^ Nat.log 2 ts.prod) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (b1.trans hT2)
  have e : 200 * (ℓ + 2 + Nat.log 2 ts.prod) * (2 ^ (ℓ + 1) * 2 ^ Nat.log 2 ts.prod) =
      100 * (ℓ + 2 + Nat.log 2 ts.prod) * (2 ^ (ℓ + 1) * 2 ^ Nat.log 2 ts.prod) +
        100 * (ℓ + 2 + Nat.log 2 ts.prod) * (2 ^ (ℓ + 1) * 2 ^ Nat.log 2 ts.prod) := by ring
  omega

theorem dom_chunkHdr (P : TransformParams) {E : Inst → ℕ} : Dom (Adm P) (sizeB P) E (fun i =>
    (chunkHdr i.p i.d (2 ^ i.ℓ) i.w (Nat.log 2 i.ts.prod) i.ts i.ℓ i.K i.h).length) := by
  simp only [chunkHdr, layerHeader, List.length_append, hdrGamma_pow, chunkOf, rhoOf]
  dom_tac

theorem dom_stepRest (P : TransformParams) :
    Dom (Adm P) (sizeB P) powR (fun i => stepRest i.p i.d i.w i.ℓ i.K i.ts i.h) := by
  have h1 : Dom (Adm P) (sizeB P) powR (fun i => clen (rowWords i.ts i.ℓ i.K)) := dom_rowWords
  have h2 : Dom (Adm P) (sizeB P) powR (fun i => clen (topsW i.ts i.ℓ i.K)) := dom_topsW
  have h3 : Dom (Adm P) (sizeB P) powR (fun i => clen (flagsW i.ts i.ℓ)) := dom_flagsW
  have h4 : Dom (Adm P) (sizeB P) powR (fun i =>
      (chunkHdr i.p i.d (2 ^ i.ℓ) i.w (Nat.log 2 i.ts.prod) i.ts i.ℓ i.K i.h).length) := dom_chunkHdr P
  simp only [stepRest, twTopCost, ScriptMain.twCost, SigmaTableTape.roundAxisCost, SigmaTableTape.topAxisCost,
    decCost, preExp, clen_cons, clen_nil, List.length_cons, List.length_nil]
  dom_tac

theorem loopCostF_le {p d w ℓ K U : ℕ} {ts : List ℕ} : ∀ m : ℕ,
    (∀ j < m, stepCost p d w ℓ K ts j ≤ U) → loopCostF p d w ℓ K ts m ≤ m * (U + 2)
  | 0, _ => by simp [loopCostF]
  | m + 1, h => by
    have h1 := h m (by omega)
    have h2 := loopCostF_le m fun j hj => h j (by omega)
    simp only [loopCostF]
    rw [Nat.succ_mul]
    omega

theorem loopCostO_le {p d w ℓ K U : ℕ} {ts : List ℕ} (h : ∀ j ≤ ℓ, stepCost p d w ℓ K ts j ≤ U) :
    ∀ r : ℕ, loopCostO p d w ℓ K ts r ≤ r * (U + 2)
  | 0 => by simp [loopCostO]
  | r + 1 => by
    have h1 := h (ℓ - (r + 1)) (by omega)
    have h2 := loopCostO_le h r
    simp only [loopCostO]
    rw [Nat.succ_mul]
    omega

theorem dom_chunkHdrs (P : TransformParams) {E : Inst → ℕ} :
    Dom (Adm P) (sizeB P) E (fun i => clen (chunkHdrs i.p i.d i.w i.ℓ i.K i.ts)) := by
  obtain ⟨k, c, hk⟩ := dom_chunkHdr P (E := fun _ => 0)
  refine dom_mul_bound (n := fun i => i.ℓ) (by dom_tac) k c fun i hi => ?_
  refine (clen_le_of (W := c * (sizeB P i + 1) ^ k * (0 + 1)) fun x hx => ?_).trans ?_
  · simp only [chunkHdrs, List.mem_map, List.mem_drop_iff_getElem] at hx
    obtain ⟨h, hh, rfl⟩ := hx
    have hh' : h < i.ℓ := by
      obtain ⟨j, hj, e⟩ := hh
      simp only [List.getElem_range, List.length_range] at e hj
      omega
    exact (hk { i with h := h } (mem_withH hi hh'.le)).trans (by simp [sizeB])
  · have : (chunkHdrs i.p i.d i.w i.ℓ i.K i.ts).length ≤ i.ℓ := by
      simp only [chunkHdrs, List.length_map, List.length_drop, List.length_range]; omega
    have hE : c * (sizeB P i + 1) ^ k * (0 + 1) ≤ c * (sizeB P i + 1) ^ k * (E i + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    calc _ ≤ i.ℓ * (c * (sizeB P i + 1) ^ k * (0 + 1) + 1) := Nat.mul_le_mul_right _ this
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

theorem costZ_eq (ℓ K : ℕ) (ts : List ℕ) (S : List (List Bool)) :
    ScriptGen.costZ ℓ K ts S = ScriptGen.costZ ℓ K ts [] + clen S := by
  simp only [ScriptGen.costZ, clen_nil]
  omega

/-- The writer's steps outside the slot loop and the script. -/
theorem dom_outer (P : TransformParams) : Dom (Adm P) (sizeB P) powR (fun i =>
    prepCost i.ℓ i.K i.d i.ts + ScriptGen.costH i.p i.d i.ℓ i.K i.w i.ts + mainExtra i.p i.d i.w i.ℓ i.K i.ts +
      ScriptGen.costZ i.ℓ i.K i.ts [] + 3) := by
  have h1 := dom_zeroE (E := powR) (dom_prep P)
  have h2 := dom_zeroE (E := powR) (dom_costH P)
  have h3 : Dom (Adm P) (sizeB P) powR (fun i => clen (chunkHdrs i.p i.d i.w i.ℓ i.K i.ts)) := dom_chunkHdrs P
  have h4 : Dom (Adm P) (sizeB P) powR (fun i => clen (rowWords i.ts i.ℓ i.K)) := dom_rowWords
  have h5 : Dom (Adm P) (sizeB P) powR (fun i => clen (topsW i.ts i.ℓ i.K)) := dom_topsW
  have h6 : Dom (Adm P) (sizeB P) powR (fun i => clen (flagsW i.ts i.ℓ)) := dom_flagsW
  refine dom_add (dom_add (dom_add (dom_add h1 h2) ?_) ?_) (dom_const 3)
  · simp only [mainExtra]; dom_tac
  · simp only [ScriptGen.costZ, clen_nil]; dom_tac

/-- `writerCost_le_parts`: the writer's steps are within a polynomial times `2^ℓ`, `ℓ` times the
power words, and the script. -/
theorem writerCost_le_parts (P : TransformParams) : ∃ k c : ℕ, ∀ (fwd : Bool) (i : Inst) (hi : i ∈ Adm P),
    ScriptGen.writerCost fwd i.p i.d i.w i.ℓ i.K i.ts (layoutOK_of_mem hi) ≤
      c * (sizeB P i + 1) ^ k * (2 ^ i.ℓ + 1) * (i.ℓ + 1) +
        i.ℓ * (200 * (i.ℓ + 2 + Nat.log 2 i.ts.prod) * (2 ^ (i.ℓ + 1) * 2 ^ Nat.log 2 i.ts.prod)) +
        clen (ScriptGen.script fwd i.p i.d i.w i.ℓ i.K i.ts (layoutOK_of_mem hi)) := by
  obtain ⟨k₁, c₁, h₁⟩ := dom_outer P
  obtain ⟨k₂, c₂, h₂⟩ := dom_stepRest P
  refine ⟨k₁ + k₂, c₁ + c₂ + 2, fun fwd i hi => ?_⟩
  have hL := layoutOK_of_mem hi
  have hout := h₁ i hi
  simp only [powR] at hout
  set X := (sizeB P i + 1)
  set R := 2 ^ i.ℓ + 1
  set W := 200 * (i.ℓ + 2 + Nat.log 2 i.ts.prod) * (2 ^ (i.ℓ + 1) * 2 ^ Nat.log 2 i.ts.prod)
  have hstep : ∀ j ≤ i.ℓ, stepCost i.p i.d i.w i.ℓ i.K i.ts j ≤ c₂ * X ^ k₂ * R + W := by
    intro j hj
    rw [stepCost_eq]
    have a := h₂ { i with h := j } (mem_withH hi hj)
    have b := powWords_le hL j
    have hB : sizeB P { i with h := j } = sizeB P i := rfl
    simp only [powR, hB] at a
    change _ ≤ c₂ * X ^ k₂ * R at a
    omega
  have hloop : ScriptGen.costM fwd i.p i.d i.w i.ℓ i.K i.ts ≤
      mainExtra i.p i.d i.w i.ℓ i.K i.ts + i.ℓ * (c₂ * X ^ k₂ * R + W + 2) := by
    unfold ScriptGen.costM
    cases fwd
    · simp only [Bool.false_eq_true, ite_false]
      have := loopCostO_le hstep i.ℓ
      omega
    · simp only [ite_true]
      have := loopCostF_le i.ℓ fun j hj => hstep j hj.le
      omega
  have hX1 : X ^ k₁ ≤ X ^ (k₁ + k₂) := Nat.pow_le_pow_right (by omega) (by omega)
  have hX2 : X ^ k₂ ≤ X ^ (k₁ + k₂) := Nat.pow_le_pow_right (by omega) (by omega)
  have hR : 1 ≤ R := Nat.le_add_left _ _
  have g1 : c₁ * X ^ k₁ * R ≤ (c₁ + c₂ + 2) * X ^ (k₁ + k₂) * R :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) hX1)
  have g2 : i.ℓ * (c₂ * X ^ k₂ * R + 2) ≤ (c₁ + c₂ + 2) * X ^ (k₁ + k₂) * R * i.ℓ := by
    have hXp : 1 ≤ X ^ (k₁ + k₂) := Nat.one_le_pow _ _ (by omega)
    have : c₂ * X ^ k₂ * R + 2 ≤ (c₁ + c₂ + 2) * X ^ (k₁ + k₂) * R := by
      have e1 : c₂ * X ^ k₂ * R ≤ c₂ * X ^ (k₁ + k₂) * R := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hX2)
      have e2 : 2 ≤ 2 * X ^ (k₁ + k₂) * R := by nlinarith
      have e3 : (c₁ + c₂ + 2) * X ^ (k₁ + k₂) * R = c₁ * X ^ (k₁ + k₂) * R + c₂ * X ^ (k₁ + k₂) * R +
          2 * X ^ (k₁ + k₂) * R := by ring
      omega
    calc i.ℓ * (c₂ * X ^ k₂ * R + 2) ≤ i.ℓ * ((c₁ + c₂ + 2) * X ^ (k₁ + k₂) * R) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have e4 : (c₁ + c₂ + 2) * X ^ (k₁ + k₂) * R * (i.ℓ + 1) =
      (c₁ + c₂ + 2) * X ^ (k₁ + k₂) * R * i.ℓ + (c₁ + c₂ + 2) * X ^ (k₁ + k₂) * R := by ring
  have e5 : i.ℓ * (c₂ * X ^ k₂ * R + W + 2) = i.ℓ * (c₂ * X ^ k₂ * R + 2) + i.ℓ * W := by ring
  have hZ := costZ_eq i.ℓ i.K i.ts (ScriptGen.script fwd i.p i.d i.w i.ℓ i.K i.ts hL)
  unfold ScriptGen.writerCost
  omega

/-! ### Beyond a cutoff -/

/-- Beyond a cutoff, every fixed power of a fixed multiple of `p` is at most `2^(ℓ - 1)`. -/
theorem eventually_pow_le (P : TransformParams) (hε : P.ε < 1) (har : 0 < P.ar) (hbd : 0 < P.bd) (A k : ℕ) :
    ∃ p₁ : ℕ, ∀ p d ℓ K w ts, p₁ ≤ p → Admissible P p d ℓ K w ts → (A * p) ^ k * 2 ≤ 2 ^ ℓ := by
  set δ := 1 - P.ε with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set c := P.ar / P.bd with hc
  have hcpos : 0 < c := div_pos har hbd
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set κ := c * Real.log 2 / 2 with hκ
  have hκpos : 0 < κ := by positivity
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have e1 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ κ / (k + 1) * x ^ δ := by
    have := (isLittleO_log_rpow_atTop hδpos).bound (div_pos hκpos hk1)
    filter_upwards [this, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg (by positivity)] at hx
    exact hx
  have e2 : ∀ᶠ x : ℝ in atTop, k * Real.log (A + 1) + Real.log 2 ≤ κ * x ^ δ := by
    have := (tendsto_rpow_atTop hδpos).const_mul_atTop hκpos
    exact this.eventually_ge_atTop _
  obtain ⟨X, hX⟩ := (e1.and (e2.and (eventually_ge_atTop (1 : ℝ)))).exists_forall_of_atTop
  refine ⟨⌈X⌉₊, fun p d ℓ K w ts hp hadm => ?_⟩
  obtain ⟨had, hbd', har', -, hd2, -, -, -, -, -, -, -, -, -⟩ := hadm
  have hpX : X ≤ (p : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hp)
  obtain ⟨hl1, hl2, hp1⟩ := hX p hpX
  have hp0 : (0 : ℝ) < p := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hpe : (0 : ℝ) < (p : ℝ) ^ P.ε := Real.rpow_pos_of_pos hp0 _
  have hsplit : (p : ℝ) = (p : ℝ) ^ P.ε * (p : ℝ) ^ δ := by
    rw [← Real.rpow_add hp0, hδ, show P.ε + (1 - P.ε) = 1 by ring, Real.rpow_one]
  have hexp : c * (p : ℝ) ^ δ ≤ P.ar * p / d := by
    rw [le_div_iff₀ hd0, hc]
    calc P.ar / P.bd * (p : ℝ) ^ δ * d ≤ P.ar / P.bd * (p : ℝ) ^ δ * (P.bd * (p : ℝ) ^ P.ε) := by
          gcongr
      _ = P.ar * ((p : ℝ) ^ P.ε * (p : ℝ) ^ δ) := by field_simp
      _ = P.ar * p := by rw [← hsplit]
  -- `((A + 1) p)^k 2 ≤ 2^(c p^δ) ≤ 2^ℓ`
  have hA0 : (0 : ℝ) < A + 1 := by positivity
  have hlogp : k * Real.log p ≤ κ * (p : ℝ) ^ δ := by
    have h0 : 0 ≤ Real.log p := Real.log_nonneg hp1
    have h1 : k * Real.log p ≤ (k + 1) * Real.log p := by nlinarith
    have h2 : (k + 1) * Real.log p ≤ (k + 1) * (κ / (k + 1) * (p : ℝ) ^ δ) := mul_le_mul_of_nonneg_left hl1 hk1.le
    have h3 : (k + 1 : ℝ) * (κ / (k + 1) * (p : ℝ) ^ δ) = κ * (p : ℝ) ^ δ := by field_simp
    linarith
  have hlog : Real.log ((((A + 1) * p : ℝ)) ^ k * 2) ≤ c * (p : ℝ) ^ δ * Real.log 2 := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow, Real.log_mul hA0.ne' hp0.ne']
    have : κ * (p : ℝ) ^ δ + κ * (p : ℝ) ^ δ = c * (p : ℝ) ^ δ * Real.log 2 := by rw [hκ]; ring
    nlinarith
  have hw2 : ((A + 1) * p : ℝ) ^ k * 2 ≤ (2 : ℝ) ^ (c * (p : ℝ) ^ δ) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < ((A + 1) * p : ℝ) ^ k * 2), Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    linarith
  have hw3 : (2 : ℝ) ^ (c * (p : ℝ) ^ δ) ≤ (2 : ℝ) ^ ((ℓ : ℕ) : ℝ) := by
    apply le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
    rw [Real.rpow_natCast]
    exact har'
  have hmono : ((A * p : ℕ) : ℝ) ^ k * 2 ≤ ((A + 1) * p : ℝ) ^ k * 2 := by
    push_cast
    gcongr
    linarith
  have : (((A * p) ^ k * 2 : ℕ) : ℝ) ≤ ((2 ^ ℓ : ℕ) : ℝ) := by
    push_cast at hmono ⊢
    rw [← Real.rpow_natCast 2 ℓ]
    linarith
  exact_mod_cast this

/-- The writer's constant against `ℓ` record volumes. -/
def sgC (c C Cw : ℕ) : ℕ := 4 * c + 600 * (C + 1) + scC C Cw

theorem clen_script_le {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ} (hadm : Admissible P p d ℓ K w ts)
    (hwr : w ≤ 2 ^ ℓ) (fwd : Bool) :
    clen (ScriptGen.script fwd p d w ℓ K ts (layoutOK_of_admissible hadm)) ≤
      ℓ * (scC ⌈P.Cl⌉₊ P.Cw * (2 * 2 ^ ℓ * w * ts.prod)) := by
  cases fwd
  · exact clen_oppScript_le hadm hwr
  · exact clen_fwdScript_le hadm hwr

/-- `writerCost_le_volume`: beyond a cutoff, both round-script writers' steps are within a fixed
multiple of `ℓ` record volumes. -/
theorem writerCost_le_volume (P : TransformParams) (hε : P.ε < 1) (har : 0 < P.ar) (hbd : 0 < P.bd) :
    ∃ Cs p₂ : ℕ, ∀ (fwd : Bool) p d ℓ K w ts (hadm : Admissible P p d ℓ K w ts), p₂ ≤ p →
      ScriptGen.writerCost fwd p d w ℓ K ts (layoutOK_of_admissible hadm) ≤
        Cs * (ℓ * (2 * 2 ^ ℓ * w * ts.prod)) := by
  obtain ⟨k, c, hW⟩ := writerCost_le_parts P
  set C := ⌈P.Cl⌉₊ with hC
  obtain ⟨p₁, hwr⟩ := eventually_w_le_r P hε har hbd
  obtain ⟨p₃, hpw⟩ := eventually_pow_le P hε har hbd ((C + 1) * P.Cw + 1) k
  refine ⟨sgC c C P.Cw, max p₁ p₃, fun fwd p d ℓ K w ts hadm hp => ?_⟩
  have hwr' := hwr p d ℓ K w ts (le_trans (le_max_left _ _) hp) hadm
  have hpow2 := hpw p d ℓ K w ts (le_trans (le_max_right _ _) hp) hadm
  set i : Inst := ⟨p, d, ℓ, K, w, ts, 0, 0, 0⟩
  have hi : i ∈ Adm P := ⟨hadm, hwr', Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
  have hparts := hW fwd i hi
  have hS := clen_script_le hadm hwr' fwd
  obtain ⟨hpow, hnC, hdD, hD, hdl, hℓp, hpw', hKℓ, hK, hℓ, hw2, hlow, hnD⟩ := adm_sizes hadm hwr'
  rw [← hC] at hnC hdl hS
  have hwp : w ≤ P.Cw * p := hadm.2.2.2.2.2.2.2.2.2.2.2.2.2
  set n := Nat.log 2 ts.prod
  set M := ts.prod
  change ScriptGen.writerCost fwd p d w ℓ K ts (layoutOK_of_admissible hadm) ≤
      c * (sizeB P i + 1) ^ k * (2 ^ ℓ + 1) * (ℓ + 1) + ℓ * (200 * (ℓ + 2 + n) * (2 ^ (ℓ + 1) * 2 ^ n)) +
        clen (ScriptGen.script fwd p d w ℓ K ts (layoutOK_of_admissible hadm)) at hparts
  rw [← hpow] at hparts
  have hB : sizeB P i = (C + 1) * w := rfl
  -- the polynomial is at most `M`
  have hY : (sizeB P i + 1) ^ k ≤ M := by
    have h1 : sizeB P i + 1 ≤ ((C + 1) * P.Cw + 1) * p := by
      rw [hB]
      have : (C + 1) * w ≤ (C + 1) * (P.Cw * p) := Nat.mul_le_mul_left _ hwp
      nlinarith
    have h2 : (sizeB P i + 1) ^ k ≤ (((C + 1) * P.Cw + 1) * p) ^ k := Nat.pow_le_pow_left h1 k
    have h3 : 2 ^ ℓ ≤ 2 * M := by
      rw [hpow, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hRM : 1 ≤ M := by rw [hpow]; exact Nat.one_le_two_pow
  set V := 2 * 2 ^ ℓ * w * M with hV
  have hQ : 2 ^ ℓ * M ≤ V := by
    rw [hV]
    calc 2 ^ ℓ * M = 1 * 2 ^ ℓ * 1 * M := by ring
      _ ≤ 2 * 2 ^ ℓ * w * M := by gcongr <;> omega
  -- the three parts
  have t1 : c * (sizeB P i + 1) ^ k * (2 ^ ℓ + 1) * (ℓ + 1) ≤ 4 * c * (ℓ * V) := by
    have a1 : 2 ^ ℓ + 1 ≤ 2 * 2 ^ ℓ := by have := Nat.one_le_two_pow (n := ℓ); omega
    calc c * (sizeB P i + 1) ^ k * (2 ^ ℓ + 1) * (ℓ + 1) ≤ c * M * (2 * 2 ^ ℓ) * (2 * ℓ) := by
          gcongr; omega
      _ = 4 * c * (ℓ * (2 ^ ℓ * M)) := by ring
      _ ≤ 4 * c * (ℓ * V) := by gcongr
  have t2 : ℓ * (200 * (ℓ + 2 + n) * (2 ^ (ℓ + 1) * M)) ≤ 600 * (C + 1) * (ℓ * V) := by
    have hdℓ : ℓ ≤ d * ℓ := Nat.le_mul_of_pos_left _ (by omega)
    have a1 : ℓ + 2 + n ≤ 3 * ((C + 1) * w) := by
      have : C * w ≤ (C + 1) * w := Nat.mul_le_mul_right _ (by omega)
      have : w ≤ (C + 1) * w := Nat.le_mul_of_pos_left _ (by omega)
      omega
    calc ℓ * (200 * (ℓ + 2 + n) * (2 ^ (ℓ + 1) * M)) ≤ ℓ * (200 * (3 * ((C + 1) * w)) * (2 ^ (ℓ + 1) * M)) := by
          gcongr
      _ = 600 * (C + 1) * (ℓ * V) := by rw [hV, pow_succ]; ring
  have e : sgC c C P.Cw * (ℓ * V) = 4 * c * (ℓ * V) + 600 * (C + 1) * (ℓ * V) + ℓ * (scC C P.Cw * V) := by
    unfold sgC; ring
  omega

/-- `ℓ` record volumes are within `2 C_w` of the paper's bound when `λ' ≥ 0`. -/
theorem ell_volume_le_cost {P : TransformParams} {p d ℓ K w : ℕ} {ts : List ℕ}
    (hadm : Admissible P p d ℓ K w ts) (hlam : 0 ≤ P.lam') :
    ((ℓ * (2 * 2 ^ ℓ * w * ts.prod) : ℕ) : ℝ) ≤ 2 * P.Cw * transformCost P p d ℓ K ts := by
  have hwp : w ≤ P.Cw * p := hadm.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hd : 2 ≤ d := hadm.2.2.2.2.1
  have hY : ((ℓ * (2 * 2 ^ ℓ * w * ts.prod) : ℕ) : ℝ) ≤ 2 * P.Cw * (((2 ^ ℓ * ts.prod : ℕ) : ℝ) * p * ℓ) := by
    have : ℓ * (2 * 2 ^ ℓ * w * ts.prod) ≤ 2 * P.Cw * (2 ^ ℓ * ts.prod * p * ℓ) := by
      calc ℓ * (2 * 2 ^ ℓ * w * ts.prod) ≤ ℓ * (2 * 2 ^ ℓ * (P.Cw * p) * ts.prod) := by gcongr
        _ = 2 * P.Cw * (2 ^ ℓ * ts.prod * p * ℓ) := by ring
    have h := (Nat.cast_le (α := ℝ)).mpr this
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
    linarith
  refine hY.trans ?_
  unfold transformCost
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hdl : (1 : ℝ) ≤ (d : ℝ) ^ P.lam' := Real.one_le_rpow hd1 hlam
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  have hdK : (0 : ℝ) ≤ d * K := by positivity
  have hpK : (0 : ℝ) ≤ p * (K : ℝ) ^ (P.τ - 1) := by positivity
  have hY0 : (0 : ℝ) ≤ ((2 ^ ℓ * ts.prod : ℕ) : ℝ) * p := by positivity
  have hCw : (0 : ℝ) ≤ 2 * P.Cw := by positivity
  have h1 : (ℓ : ℝ) ≤ d * K + p * (K : ℝ) ^ (P.τ - 1) + ℓ * (d : ℝ) ^ P.lam' := by nlinarith
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hY0) hCw
  push_cast at this ⊢
  linarith

/-- `writerCost_le_transformCost`: beyond a cutoff, both round-script writers' steps are within a
fixed multiple of the paper's bound. -/
theorem writerCost_le_transformCost (P : TransformParams) (hε : P.ε < 1) (har : 0 < P.ar) (hbd : 0 < P.bd)
    (hlam : 0 ≤ P.lam') :
    ∃ (Cs : ℝ) (p₂ : ℕ), ∀ (fwd : Bool) p d ℓ K w ts (hadm : Admissible P p d ℓ K w ts), p₂ ≤ p →
      (ScriptGen.writerCost fwd p d w ℓ K ts (layoutOK_of_admissible hadm) : ℝ) ≤
        Cs * transformCost P p d ℓ K ts := by
  obtain ⟨Cs, p₂, h⟩ := writerCost_le_volume P hε har hbd
  refine ⟨Cs * (2 * P.Cw), p₂, fun fwd p d ℓ K w ts hadm hp => ?_⟩
  have h1 : (ScriptGen.writerCost fwd p d w ℓ K ts (layoutOK_of_admissible hadm) : ℝ) ≤
      (Cs : ℝ) * ((ℓ * (2 * 2 ^ ℓ * w * ts.prod) : ℕ) : ℝ) := by
    exact_mod_cast h fwd p d ℓ K w ts hadm hp
  have h2 := mul_le_mul_of_nonneg_left (ell_volume_le_cost hadm hlam) (Nat.cast_nonneg (α := ℝ) Cs)
  linarith

/-! ### The script writers -/

/-- `scriptWriters_of_compatible`: for transform parameters compatible with some layer parameters,
the round-script writers `ScriptGen.scriptGen` and the layout-script writers give `ScriptWriters`. -/
theorem scriptWriters_of_compatible {LP : LayerParams} {P : TransformParams} (hc : Compatible LP P) :
    ScriptWriters P := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hlam, -, hε, har, hbd, hlam0⟩ := hc
  obtain ⟨Cs, p₂, hW⟩ := writerCost_le_transformCost P hε har hbd (by linarith)
  refine LayoutGenCost.scriptWriters_of_scriptGen hε har hbd fun A tL =>
    ⟨ScriptGen.scriptGen true A tL NL, ScriptGen.scriptGen false A tL NL, Cs, p₂, fun p d ℓ K w ts hadm hp => ?_⟩
  have hL := layoutOK_of_admissible hadm
  have hd : 2 ≤ d := hadm.2.2.2.2.1
  have hD : ts.length = d - 1 := hadm.2.2.2.2.2.2.2.2.2.2.2.1.1
  exact ⟨_, _, hW true p d ℓ K w ts hadm hp, hW false p d ℓ K w ts hadm hp,
    ScriptGen.scriptGen_fwd hL (by omega) (by omega), ScriptGen.scriptGen_opp hL (by omega) (by omega)⟩

end ScriptGenCost

end IntegerMultBounds.Schoenhage
