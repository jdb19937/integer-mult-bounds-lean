module

public import IntegerMultBounds.MathlibTM2.Node.CompactSlotHost
public import IntegerMultBounds.MathlibTM2.Node.RunMask
public import IntegerMultBounds.MathlibTM2.Fast.StageFill

/-!
# The setup of the compact slot XOR

From unary input registers (`CxIn`: the segment length `K`, the offset `ρ`, the digit length `G`,
`o + a₀`, the low offset `o`, `H + B`, the active chunks, `o + n`, the rows `R`, the coefficients
`r`, the coefficient width `w`, and the slot width `k K`), the setup fills, one register per
stage (`cxStage`, `cxBc`), the registers `cxCore` reads (`PassState`):

* stages `1–10`: the unary values `a₀`, `n`, `k - 1`, `(k - 1) G`, `sT`, `1`, `K - 1`, `G - 1`,
  `K - 1 - G`, `K - 2 - G` (`sc i`);
* stages `11–17`: the row count in binary (`hb 0`), the counters `ctrB`, `ctrK`, `ctr`, `cnt`,
  the binary keyed record length `3 (n + rb + B)` (`hb 1`) and the binary compact width (`hb 2`);
* stages `18–27`: the index fields at zero;
* stages `28–31`: the masks;
* stages `32–41`: the interchange headers.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Layer (m)

/-- The unary input registers of the setup. -/
structure CxIn (T : ℕ) where
  K : Fin T
  ρ : Fin T
  G : Fin T
  OA : Fin T
  O : Fin T
  HB : Fin T
  Act : Fin T
  ON : Fin T
  R : Fin T
  r : Fin T
  w : Fin T
  ell : Fin T

/-- The registers the setup fills: compact registers and interchange headers. -/
inductive CxSet where
  | reg (x : CxReg)
  | hdr (c : Fin 2) (k : Fin 5)
  deriving DecidableEq

variable {T : ℕ}

/-- The registers of `CxSet`. -/
noncomputable def cxSetReg (ι : CxReg → Fin T) (bank : Fin 2 → Fin (swapT 6) → Fin T) : CxSet → Fin T
  | .reg x => ι x
  | .hdr c k => bank c (reg (cxHd k))

lemma cxSetReg_inj {ι : CxReg → Fin T} {bank : Fin 2 → Fin (swapT 6) → Fin T}
    (hι : Function.Injective ι) (hb : Banks ι bank)
    (hbc : ∀ c c' j j', bank c j = bank c' j' → c = c') :
    Function.Injective (cxSetReg ι bank) := by
  have hreg : Function.Injective fun k : Fin 5 => (reg (cxHd k) : Fin (swapT 6)) :=
    fun k k' e => cxHd_inj (BinaryInterchangeRun.slot_injective e)
  rintro (x | ⟨c, k⟩) (y | ⟨c', k'⟩) e <;> simp only [cxSetReg] at e
  · rw [hι e]
  · exact absurd e.symm (hb.ne _ _ _)
  · exact absurd e (hb.ne _ _ _)
  · have hc := hbc _ _ _ _ e
    subst hc
    rw [hreg (hb.inj c e)]

/-- The setup stage of each register (`0`: not filled). -/
def cxStage : CxSet → ℕ
  | .reg (.sc i) => 1 + i
  | .reg (.hb i) => if i = 0 then 11 else if i = 1 then 16 else 17
  | .reg .ctrB => 12
  | .reg .ctrK => 13
  | .reg .ctr => 14
  | .reg .cnt => 15
  | .reg (.fld g) => 18 + g
  | .reg .mSel => 28
  | .reg .mC => 29
  | .reg .mA => 30
  | .reg .mMk => 31
  | .hdr c k => 32 + 5 * c + k
  | _ => 0

/-- The register of each setup stage. -/
def cxOfStage (s : ℕ) : CxSet :=
  if h : 1 ≤ s ∧ s ≤ 10 then .reg (.sc ⟨s - 1, by omega⟩)
  else if s = 11 then .reg (.hb 0) else if s = 12 then .reg .ctrB
  else if s = 13 then .reg .ctrK else if s = 14 then .reg .ctr else if s = 15 then .reg .cnt
  else if s = 16 then .reg (.hb 1) else if s = 17 then .reg (.hb 2)
  else if h : 18 ≤ s ∧ s ≤ 27 then .reg (.fld ⟨s - 18, by omega⟩)
  else if s = 28 then .reg .mSel else if s = 29 then .reg .mC else if s = 30 then .reg .mA
  else if s = 31 then .reg .mMk
  else if h : 32 ≤ s ∧ s ≤ 41 then .hdr ⟨(s - 32) / 5, by omega⟩ ⟨(s - 32) % 5, by omega⟩
  else .reg .src

lemma cxOfStage_stage (x : CxSet) (hx : 1 ≤ cxStage x) : cxOfStage (cxStage x) = x := by
  rcases x with x | ⟨c, k⟩
  · cases x <;> simp only [cxStage] at hx ⊢
    case sc i =>
      rw [cxOfStage, dite_eq_left (by omega)]
      congr; omega
    case hb i =>
      fin_cases i <;> simp [cxOfStage]
    case fld g =>
      rw [cxOfStage, dite_eq_right (by omega)]
      simp only [show ¬ (18 + (g : ℕ) = 11) by omega, show ¬ (18 + (g : ℕ) = 12) by omega,
        show ¬ (18 + (g : ℕ) = 13) by omega, show ¬ (18 + (g : ℕ) = 14) by omega,
        show ¬ (18 + (g : ℕ) = 15) by omega, show ¬ (18 + (g : ℕ) = 16) by omega,
        show ¬ (18 + (g : ℕ) = 17) by omega, ↓reduceIte]
      rw [dite_eq_left (by omega)]
      congr; omega
    all_goals first | omega | rfl
  · simp only [cxStage]
    rw [cxOfStage, dite_eq_right (by omega)]
    simp only [show ¬ (32 + 5 * (c : ℕ) + k = 11) by omega, show ¬ (32 + 5 * (c : ℕ) + k = 12) by omega,
      show ¬ (32 + 5 * (c : ℕ) + k = 13) by omega, show ¬ (32 + 5 * (c : ℕ) + k = 14) by omega,
      show ¬ (32 + 5 * (c : ℕ) + k = 15) by omega, show ¬ (32 + 5 * (c : ℕ) + k = 16) by omega,
      show ¬ (32 + 5 * (c : ℕ) + k = 17) by omega, show ¬ (32 + 5 * (c : ℕ) + k = 28) by omega,
      show ¬ (32 + 5 * (c : ℕ) + k = 29) by omega, show ¬ (32 + 5 * (c : ℕ) + k = 30) by omega,
      show ¬ (32 + 5 * (c : ℕ) + k = 31) by omega, ↓reduceIte]
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr <;> omega

lemma cxStage_inj (x y : CxSet) (hx : 1 ≤ cxStage x) (h : cxStage x = cxStage y) : x = y := by
  rw [← cxOfStage_stage x hx, ← cxOfStage_stage y (h ▸ hx), h]

lemma cxStage_ofStage (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ 41) : cxStage (cxOfStage t) = t := by
  interval_cases t <;> rfl

/-! ### The contents of the setup registers -/

namespace CxData

variable (d : CxData)

/-- The unary setup values. -/
def scv : Fin 10 → ℕ :=
  ![d.a₀, d.n, d.k - 1, d.wc, d.sT, 1, d.K - 1, d.G - 1, d.K - 1 - d.G, d.K - 2 - d.G]

/-- The binary setup numbers: the rows, three keyed record lengths, the compact width. -/
def hbv : Fin 3 → ℕ := ![d.R, 3 * (d.n + d.rb + d.B), d.wc]

/-- The low zero bits of header `k` of bank `c`. -/
def he : Fin 2 → Fin 5 → ℕ
  | 0, 0 => d.n - (d.sT + d.wc)
  | 1, 0 => d.n - (d.sT + 2 * d.wc)
  | 0, 1 => d.sT - d.wc
  | 1, 1 => d.sT
  | _, _ => 0

/-- The high bits of header `k`. -/
def hbits : Fin 5 → List Bool
  | 0 => sxBits d.R
  | 1 => [true]
  | 2 => sxBits (3 * (d.n + d.rb + d.B))
  | _ => sxBits d.wc

/-- The canonical counter of header `k` of bank `c`. -/
def hs (c : Fin 2) (k : Fin 5) : List Bool := List.replicate (d.he c k) false ++ d.hbits k

variable {d}

lemma swapFld_off (hd : d.OK) (c : Fin 2) :
    fieldOff d.lens (swapFld d.fields c) = d.sT + c * d.wc := by
  obtain ⟨-, -, -, e6, e8, -⟩ := hd.offs
  fin_cases c
  · simp [swapFld, fields, e6]
  · simp [swapFld, fields, e8]

lemma hs_value (hd : d.OK) (c : Fin 2) (k : Fin 5) :
    Counter.value (d.hs c k) = BinaryInterchangeRun.values
      (swapDimsIdx (len := d.lens) d.fields.b (swapFld d.fields c) d.par.wc d.R d.n
        (d.n + d.rb + d.B)).1
      (swapDimsIdx (len := d.lens) d.fields.b (swapFld d.fields c) d.par.wc d.R d.n
        (d.n + d.rb + d.B)).2.1
      (swapDimsIdx (len := d.lens) d.fields.b (swapFld d.fields c) d.par.wc d.R d.n
        (d.n + d.rb + d.B)).2.2 d.par.wc d.par.wc k := by
  have hb0 : fieldOff d.lens d.fields.b = 0 := hd.offs.1
  have hoff := swapFld_off hd c
  simp only [swapDimsIdx, hb0, hoff, par_wc, pow_zero, Nat.one_mul, Nat.sub_zero]
  fin_cases c <;> fin_cases k <;>
    (simp [hs, he, hbits, sx_value_rep_false, value_sxBits, BinaryInterchangeRun.values,
      Counter.value, Nat.mul_comm]; try (ring_nf; try simp))

lemma hs_canonical (hd : d.OK) (c : Fin 2) (k : Fin 5) :
    GrowingCounterData.Canonical (d.hs c k) := by
  have hR : 0 < d.R := hd.R0
  have hB : 0 < 3 * (d.n + d.rb + d.B) := by have := hd.B1; omega
  fin_cases k
  · exact sx_canonical_rep_false _ (sxBits_ne_nil hR) (canonical_sxBits _)
  · exact sx_canonical_rep_false _ (by simp [hbits]) (Or.inr rfl)
  · exact sx_canonical_rep_false _ (sxBits_ne_nil hB) (canonical_sxBits _)
  · fin_cases c <;> simpa [hs, he, hbits] using canonical_sxBits d.wc
  · fin_cases c <;> simpa [hs, he, hbits] using canonical_sxBits d.wc

end CxData

/-- The contents of the setup registers. -/
def cxBc (A : ℕ) (d : CxData) : CxSet → List (Fin (A + 4))
  | .reg (.sc i) => List.replicate (d.scv i) tick
  | .reg (.hb i) => (sxBits (d.hbv i)).map bitSymbol
  | .reg .ctrB => List.replicate d.B tick
  | .reg .ctrK => List.replicate (d.n + d.rb) tick
  | .reg .ctr => List.replicate (d.n + d.rb + d.B) tick
  | .reg .cnt => List.replicate (d.R * 2 ^ d.n) tick
  | .reg (.fld g) => binSyms (d.lens g) 0
  | .reg .mSel => binSyms d.par.wy (selV d.par)
  | .reg .mC => binSyms d.par.wc (mCV d.par)
  | .reg .mA => binSyms d.par.wy (mAV d.par)
  | .reg .mMk => binSyms d.par.wy (mkV d.par)
  | .hdr c k => separator :: (d.hs c k).map bitSymbol
  | _ => []

/-! ### The register file of the setup -/

section File

variable {A : ℕ} (ι : CxReg → Fin T) (bank : Fin 2 → Fin (swapT 6) → Fin T) (inp : Fin 12 → Fin T)

/-- Every register of the setup: the filled registers and the twelve inputs (`K`, `ρ`, `G`,
`o + a₀`, `o`, `H + B`, the active chunks, `o + n`, `R`, `r`, `w`, `k K`). -/
noncomputable def cxAll : CxSet ⊕ Fin 12 → Fin T := Sum.elim (cxSetReg ι bank) inp

/-- The register file after `s` setup stages. -/
noncomputable def cxFile (d : CxData) (s : ℕ) (R₀ : Fin T → List (Fin (A + 4))) :
    Fin T → List (Fin (A + 4)) :=
  stFill (cxSetReg ι bank) cxStage (cxBc A d) s R₀

variable {ι bank inp}

lemma cxAll_set (x : CxSet) : cxAll ι bank inp (.inl x) = cxSetReg ι bank x := rfl
lemma cxAll_inp (i : Fin 12) : cxAll ι bank inp (.inr i) = inp i := rfl

variable (hall : Function.Injective (cxAll ι bank inp))
include hall

lemma cxSetReg_inj' : Function.Injective (cxSetReg ι bank) :=
  fun _ _ e => Sum.inl_injective (hall e)

lemma cxFile_set {d : CxData} {s : ℕ} {R₀ : Fin T → List (Fin (A + 4))} {x : CxSet}
    (h1 : 1 ≤ cxStage x) (h2 : cxStage x ≤ s) :
    cxFile ι bank d s R₀ (cxSetReg ι bank x) = cxBc A d x :=
  stFill_of_le (cxSetReg_inj' hall) _ _ h1 h2

lemma cxFile_unset {d : CxData} {s : ℕ} {R₀ : Fin T → List (Fin (A + 4))} {x : CxSet}
    (h : s < cxStage x ∨ cxStage x = 0) :
    cxFile ι bank d s R₀ (cxSetReg ι bank x) = R₀ (cxSetReg ι bank x) :=
  stFill_of_gt (cxSetReg_inj' hall) _ _ h

lemma cxFile_inp {d : CxData} {s : ℕ} {R₀ : Fin T → List (Fin (A + 4))} (i : Fin 12) :
    cxFile ι bank d s R₀ (inp i) = R₀ (inp i) :=
  stFill_out _ _ _ fun x e => by
    have := hall (show cxAll ι bank inp (.inl x) = cxAll ι bank inp (.inr i) from e)
    simp at this

/-- A stage that fills its register with its contents advances the file. -/
lemma cxFile_step {d : CxData} {s : ℕ} {R₀ : Fin T → List (Fin (A + 4))} {x : CxSet}
    (hx : cxStage x = s + 1) :
    Function.update (cxFile ι bank d s R₀) (cxSetReg ι bank x) (cxBc A d x) =
      cxFile ι bank d (s + 1) R₀ :=
  stFill_step (cxSetReg_inj' hall) cxStage_inj _ _ hx

/-- The stream register is not a setup register. -/
lemma cxFile_src {d : CxData} {s : ℕ} {R₀ : Fin T → List (Fin (A + 4))} (Y : List (Fin (A + 4))) :
    Function.update (cxFile ι bank d s R₀) (ι .src) Y =
      cxFile ι bank d s (Function.update R₀ (ι .src) Y) := by
  funext t
  by_cases ht : ∃ y, cxSetReg ι bank y = t
  · obtain ⟨y, rfl⟩ := ht
    by_cases hy : y = .reg .src
    · subst hy
      show Function.update (cxFile ι bank d s R₀) (ι .src) Y (ι .src) =
        cxFile ι bank d s (Function.update R₀ (ι .src) Y) (ι .src)
      rw [Function.update_self, show ι CxReg.src = cxSetReg ι bank (.reg .src) from rfl,
        cxFile_unset hall (Or.inr rfl)]
      simp [cxSetReg]
    · have hne : cxSetReg ι bank y ≠ ι .src := fun e =>
        hy (cxSetReg_inj' hall (e.trans (rfl : ι .src = cxSetReg ι bank (.reg .src))))
      rw [Function.update_of_ne hne, cxFile, cxFile, stFill_ι (cxSetReg_inj' hall),
        stFill_ι (cxSetReg_inj' hall), Function.update_of_ne hne]
  · simp only [not_exists] at ht
    have hne : t ≠ ι .src := fun e => ht (.reg .src) e.symm
    rw [Function.update_of_ne hne, cxFile, cxFile, stFill_out _ _ _ ht, stFill_out _ _ _ ht,
      Function.update_of_ne hne]

end File

/-! ### The stage programs -/

section Programs

variable {Q A : ℕ} {U : Type} {P : Type}
variable (ι : CxReg → Fin T) (bank : Fin 2 → Fin (swapT 6) → Fin T) (inp : Fin 12 → Fin T)

/-- The start of header `k` of bank `c`: its high bits. -/
noncomputable def cxHdrStart (c : Fin 2) : Fin 5 → Pr P T Q A U
  | 0 => sxDupR (ι (.hb 0)) (bank c (reg (cxHd 0))) (ι (.tw 0)) (ι (.tw 1))
  | 1 => synPush (bank c (reg (cxHd 1))) (bitSymbol true)
  | 2 => sxDupR (ι (.hb 1)) (bank c (reg (cxHd 2))) (ι (.tw 0)) (ι (.tw 1))
  | k => sxDupR (ι (.hb 2)) (bank c (reg (cxHd k))) (ι (.tw 0)) (ι (.tw 1))

/-- The low zero bits of header `k` of bank `c`. -/
noncomputable def cxHdrZeros : Fin 2 → Fin 5 → Pr P T Q A U
  | c, 0 => .seq (.seq (.seq (ucopy (ι (.sc 1)) (ι (.tw 2)) (ι (.tw 0)))
      (usub (ι (.sc 4)) (ι (.tw 2)) (ι (.tw 0))))
      (if c = 0 then usub (ι (.sc 3)) (ι (.tw 2)) (ι (.tw 0)) else
        .seq (usub (ι (.sc 3)) (ι (.tw 2)) (ι (.tw 0))) (usub (ι (.sc 3)) (ι (.tw 2)) (ι (.tw 0)))))
      (.seq (zeroBits (ι (.tw 2)) (bank c (reg (cxHd 0))) (ι (.tw 0))) (uclear (ι (.tw 2))))
  | c, 1 => if c = 0 then
      .seq (.seq (ucopy (ι (.sc 4)) (ι (.tw 2)) (ι (.tw 0))) (usub (ι (.sc 3)) (ι (.tw 2)) (ι (.tw 0))))
        (.seq (zeroBits (ι (.tw 2)) (bank c (reg (cxHd 1))) (ι (.tw 0))) (uclear (ι (.tw 2))))
      else zeroBits (ι (.sc 4)) (bank c (reg (cxHd 1))) (ι (.tw 0))
  | _, _ => synSkip

/-- Build header `k` of bank `c`. -/
noncomputable def cxHdrProg (c : Fin 2) (k : Fin 5) : Pr P T Q A U :=
  .seq (cxHdrStart ι bank c k)
    (.seq (cxHdrZeros ι bank c k) (synPush (bank c (reg (cxHd k))) separator))

/-- The program of setup stage `s` for the slots `lo < hi`. -/
noncomputable def cxStageProg (lo hi : ℕ) : ℕ → Pr P T Q A U
  | 1 => .seq (ucopy (inp 3) (ι (.sc 0)) (ι (.tw 0))) (usub (inp 4) (ι (.sc 0)) (ι (.tw 0)))
  | 2 => .seq (ucopy (inp 7) (ι (.sc 1)) (ι (.tw 0))) (usub (inp 4) (ι (.sc 1)) (ι (.tw 0)))
  | 3 => .seq (synDivModR (inp 11) (inp 0) (ι (.sc 2)) (ι (.tw 1)) (ι (.tw 0)) (ι (.tw 2))
      (ι (.tw 3))) (synPop (ι (.sc 2)))
  | 4 => synMulR (ι (.sc 2)) (inp 2) (ι (.sc 3)) (ι (.tw 0)) (ι (.tw 1))
  | 5 => .seq (ucopy (inp 5) (ι (.sc 4)) (ι (.tw 0)))
      (synMulR (inp 6) (inp 0) (ι (.sc 4)) (ι (.tw 0)) (ι (.tw 1)))
  | 6 => synPush (ι (.sc 5)) tick
  | 7 => .seq (ucopy (inp 0) (ι (.sc 6)) (ι (.tw 0))) (synPop (ι (.sc 6)))
  | 8 => .seq (ucopy (inp 2) (ι (.sc 7)) (ι (.tw 0))) (synPop (ι (.sc 7)))
  | 9 => .seq (.seq (ucopy (inp 0) (ι (.sc 8)) (ι (.tw 0))) (synPop (ι (.sc 8))))
      (usub (inp 2) (ι (.sc 8)) (ι (.tw 0)))
  | 10 => .seq (ucopy (ι (.sc 8)) (ι (.sc 9)) (ι (.tw 0))) (synPop (ι (.sc 9)))
  | 11 => sxBinConv (inp 8) (ι (.hb 0)) (ι (.tw 0)) (ι (.tw 1))
  | 12 => .seq (synMulR (inp 9) (inp 10) (ι .ctrB) (ι (.tw 0)) (ι (.tw 1)))
      (upow2 (inp 4) (ι .ctrB) (ι (.tw 0)) (ι (.tw 1)))
  | 13 => .seq (ucopy (ι (.sc 1)) (ι .ctrK) (ι (.tw 0))) (ucopy (ι (.hb 0)) (ι .ctrK) (ι (.tw 0)))
  | 14 => .seq (ucopy (ι .ctrK) (ι .ctr) (ι (.tw 0))) (ucopy (ι .ctrB) (ι .ctr) (ι (.tw 0)))
  | 15 => .seq (ucopy (inp 8) (ι .cnt) (ι (.tw 0))) (upow2 (ι (.sc 1)) (ι .cnt) (ι (.tw 0)) (ι (.tw 1)))
  | 16 => .seq (.seq (umul 3 (ι .ctr) (ι (.tw 2)) (ι (.tw 0)))
      (sxBinConv (ι (.tw 2)) (ι (.hb 1)) (ι (.tw 0)) (ι (.tw 1)))) (uclear (ι (.tw 2)))
  | 17 => sxBinConv (ι (.sc 3)) (ι (.hb 2)) (ι (.tw 0)) (ι (.tw 1))
  | 18 => zeroBits (ι (.sc 3)) (ι (.fld 0)) (ι (.tw 0))
  | 19 => .seq (.seq (.seq (ucopy (ι (.sc 0)) (ι (.tw 2)) (ι (.tw 0)))
      (umul lo (inp 11) (ι (.tw 2)) (ι (.tw 0)))) (usub (ι (.sc 3)) (ι (.tw 2)) (ι (.tw 0))))
      (.seq (zeroBits (ι (.tw 2)) (ι (.fld 1)) (ι (.tw 0))) (uclear (ι (.tw 2))))
  | 20 => zeroBits (inp 11) (ι (.fld 2)) (ι (.tw 0))
  | 21 => .seq (umul (hi - lo - 1) (inp 11) (ι (.tw 2)) (ι (.tw 0)))
      (.seq (zeroBits (ι (.tw 2)) (ι (.fld 3)) (ι (.tw 0))) (uclear (ι (.tw 2))))
  | 22 => zeroBits (inp 11) (ι (.fld 4)) (ι (.tw 0))
  | 23 => .seq (.seq (.seq (.seq (.seq (ucopy (ι (.sc 4)) (ι (.tw 2)) (ι (.tw 0)))
      (ucopy (ι (.sc 0)) (ι (.tw 3)) (ι (.tw 0)))) (umul (hi + 1) (inp 11) (ι (.tw 3)) (ι (.tw 0))))
      (usub (ι (.tw 3)) (ι (.tw 2)) (ι (.tw 0)))) (uclear (ι (.tw 3))))
      (.seq (zeroBits (ι (.tw 2)) (ι (.fld 5)) (ι (.tw 0))) (uclear (ι (.tw 2))))
  | 24 => zeroBits (ι (.sc 3)) (ι (.fld 6)) (ι (.tw 0))
  | 25 => synSkip
  | 26 => zeroBits (ι (.sc 3)) (ι (.fld 8)) (ι (.tw 0))
  | 27 => .seq (.seq (.seq (.seq (.seq (ucopy (ι (.sc 1)) (ι (.tw 2)) (ι (.tw 0)))
      (usub (ι (.sc 4)) (ι (.tw 2)) (ι (.tw 0)))) (usub (ι (.sc 3)) (ι (.tw 2)) (ι (.tw 0))))
      (usub (ι (.sc 3)) (ι (.tw 2)) (ι (.tw 0)))) (ucopy (ι (.hb 0)) (ι (.tw 2)) (ι (.tw 0))))
      (.seq (zeroBits (ι (.tw 2)) (ι (.fld 9)) (ι (.tw 0))) (uclear (ι (.tw 2))))
  | 28 => runMask (inp 11) [(inp 1, false)] (ι (.sc 2)) [(ι (.sc 5), true), (ι (.sc 6), false)] []
      (ι .mSel) (ι (.tw 0)) (ι (.tw 1)) (ι (.tw 2)) (ι (.tw 3))
  | 29 => runMask (ι (.sc 3)) [] (ι (.sc 2)) [(ι (.sc 5), true), (ι (.sc 7), false)] []
      (ι .mC) (ι (.tw 0)) (ι (.tw 1)) (ι (.tw 2)) (ι (.tw 3))
  | 30 => runMask (inp 11) [(inp 1, false)] (ι (.sc 2))
      [(ι (.sc 5), false), (inp 2, true), (ι (.sc 8), false)] []
      (ι .mA) (ι (.tw 0)) (ι (.tw 1)) (ι (.tw 2)) (ι (.tw 3))
  | 31 => runMask (inp 11) [(inp 1, false)] (ι (.sc 2))
      [(ι (.sc 5), true), (ι (.sc 5), true), (ι (.sc 7), false), (ι (.sc 5), true),
        (ι (.sc 9), false)] [(ι (.sc 5), true)]
      (ι .mMk) (ι (.tw 0)) (ι (.tw 1)) (ι (.tw 2)) (ι (.tw 3))
  | s => if h : 32 ≤ s ∧ s ≤ 41 then
      cxHdrProg ι bank ⟨(s - 32) / 5, by omega⟩ ⟨(s - 32) % 5, by omega⟩ else synSkip

/-- The setup: stages `1` to `41`. -/
noncomputable def cxSetupProg (lo hi : ℕ) : Pr P T Q A U :=
  Prog.seqList ((List.range 41).map fun i => cxStageProg ι bank inp lo hi (i + 1))

/-- The cleanup: clear the setup registers, last stage first. -/
noncomputable def cxCleanProg : Pr P T Q A U :=
  Prog.seqList ((List.range 41).map fun j => uclear (cxSetReg ι bank (cxOfStage (41 - j))))

end Programs


/-- The unary inputs of the setup for the numbers `d`, the low offset `o`, `H + B`, the active
chunks, and `cr` coefficients of width `cw`. -/
structure CxSetupIn {A : ℕ} (d : CxData) (inp : Fin 12 → Fin T) (R₀ : Fin T → List (Fin (A + 4)))
    (o hB act cr cw : ℕ) : Prop where
  K : (R₀ (inp 0)).length = d.K
  ρ : (R₀ (inp 1)).length = d.ρ
  G : (R₀ (inp 2)).length = d.G
  OA : (R₀ (inp 3)).length = o + d.a₀
  O : (R₀ (inp 4)).length = o
  HB : (R₀ (inp 5)).length = hB
  Act : (R₀ (inp 6)).length = act
  ON : (R₀ (inp 7)).length = o + d.n
  R : (R₀ (inp 8)).length = d.R
  r : (R₀ (inp 9)).length = cr
  w : (R₀ (inp 10)).length = cw
  ell : (R₀ (inp 11)).length = d.k * d.K
  sT : d.sT = hB + act * d.K
  B : d.B = cr * cw * 2 ^ o

/-! ### Distinct registers -/

section Distinct

variable {ι : CxReg → Fin T} {bank : Fin 2 → Fin (swapT 6) → Fin T} {inp : Fin 12 → Fin T}
  (hall : Function.Injective (cxAll ι bank inp))
include hall

lemma cxι_ne {x y : CxReg} (h : x ≠ y) : ι x ≠ ι y := fun e =>
  h (CxSet.reg.inj (Sum.inl_injective
    (hall (show cxAll ι bank inp (.inl (.reg x)) = cxAll ι bank inp (.inl (.reg y)) from e))))

lemma cxι_inp (x : CxReg) (i : Fin 12) : ι x ≠ inp i := fun e => by
  have := hall (show cxAll ι bank inp (.inl (.reg x)) = cxAll ι bank inp (.inr i) from e)
  simp at this

lemma cxinp_ne {i j : Fin 12} (h : i ≠ j) : inp i ≠ inp j := fun e =>
  h (Sum.inr_injective (hall (show cxAll ι bank inp (.inr i) = cxAll ι bank inp (.inr j) from e)))

lemma cxbank_ι (c : Fin 2) (k : Fin 5) (x : CxReg) : bank c (reg (cxHd k)) ≠ ι x := fun e => by
  have := hall (show cxAll ι bank inp (.inl (.hdr c k)) = cxAll ι bank inp (.inl (.reg x)) from e)
  simp at this

lemma cxbank_inp (c : Fin 2) (k : Fin 5) (i : Fin 12) : bank c (reg (cxHd k)) ≠ inp i := fun e => by
  have := hall (show cxAll ι bank inp (.inl (.hdr c k)) = cxAll ι bank inp (.inr i) from e)
  simp at this

lemma cx_nodup (l : List (CxSet ⊕ Fin 12)) (hl : l.Nodup) : (l.map (cxAll ι bank inp)).Nodup :=
  hl.map hall

end Distinct

/-- Distinct setup registers. -/
macro "cxne" : tactic => `(tactic| first
  | exact cxι_ne ‹_› (by decide)
  | exact cxι_ne ‹_› (by simp)
  | exact cxι_inp ‹_› _ _
  | exact (cxι_inp ‹_› _ _).symm
  | exact cxinp_ne ‹_› (by decide)
  | exact cxbank_ι ‹_› _ _ _
  | exact (cxbank_ι ‹_› _ _ _).symm
  | exact cxbank_inp ‹_› _ _ _
  | exact (cxbank_inp ‹_› _ _ _).symm)

/-- Run registers apart from the mask temporaries. -/
macro "cxmem" : tactic => `(tactic| (
  simp only [List.cons_append, List.nil_append, List.forall_mem_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or, and_true, List.forall_mem_nil, forall_eq_or_imp,
    forall_eq, List.append_nil]
  repeat' constructor
  all_goals cxne))

/-! ### Run contracts of the binary helpers -/

section Kit

variable {Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {R : Fin T → List (Fin (A + 4))}

theorem lr_sxBinConv {a d t₁ t₂ : Fin T} (hreg : [a, d, t₁, t₂].Nodup) (hd : R d = [])
    (ht₁ : R t₁ = []) (ht₂ : R t₂ = []) :
    LayRuns body (sxBinConv a d t₁ t₂) R
      (Function.update R d ((sxBits (R a).length).map bitSymbol)) (16 * (R a).length + 4) :=
  lr_of_exec_le body fun v S hS => by subst hS; exact sxBinConv_exec body hreg v S hd ht₁ ht₂

theorem lr_sxDupR {a b t t₂ : Fin T} (hreg : [a, b, t, t₂].Nodup) (ht : R t = [])
    (ht₂ : R t₂ = []) :
    LayRuns body (sxDupR a b t t₂) R (Function.update R b (R a ++ R b)) (6 * (R a).length + 6) :=
  lr_of_exec body fun v S hS => by subst hS; exact sxDupR_exec body hreg v S ht ht₂

lemma flatMap_replicate_rep {α : Type*} (x : α) (n k : ℕ) :
    (List.replicate n x).flatMap (List.replicate k) = List.replicate (n * k) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatMap_cons, ih, List.replicate_append_replicate, Nat.succ_mul,
      Nat.add_comm]


theorem lr_copyTemp {a t₂ t₀ : Fin T} (ha2 : a ≠ t₂) (ha0 : a ≠ t₀) (h20 : t₂ ≠ t₀)
    (ht : R t₀ = []) (h2 : R t₂ = []) :
    LayRuns body (ucopy a t₂ t₀) R (Function.update R t₂ (List.replicate (R a).length tick))
      (4 * (R a).length + 4) := by
  have h := lr_ucopy body ha2 ha0 h20 ht
  rwa [h2, List.append_nil] at h

theorem lr_subTemp {a t₂ t₀ : Fin T} (ha2 : a ≠ t₂) (ha0 : a ≠ t₀) (h20 : t₂ ≠ t₀)
    (ht : R t₀ = []) (L : ℕ) :
    LayRuns body (usub a t₂ t₀) (Function.update R t₂ (List.replicate L tick))
      (Function.update R t₂ (List.replicate (L - (R a).length) tick)) (4 * (R a).length + 4) := by
  have h := lr_usub body (R := Function.update R t₂ (List.replicate L tick)) (a := a) (b := t₂)
    (t := t₀) ha2 ha0 h20 (by rw [Function.update_of_ne h20.symm]; exact ht)
  rwa [Function.update_self, Function.update_of_ne ha2, Function.update_idem,
    List.drop_replicate] at h

end Kit

/-! ### The mask patterns -/

section Masks

variable {A : ℕ} {F : Fin T → List (Fin (A + 4))}

lemma exists_mul_add_iff {K a n b q : ℕ} (hb : b < K) :
    (∃ c < n, a + c * K + b = q) ↔ a ≤ q ∧ q < a + n * K ∧ (q - a) % K = b := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    have h := Nat.mul_le_mul_right K (show c + 1 ≤ n by omega)
    rw [Nat.add_mul, Nat.one_mul] at h
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hb]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(q - a) / K, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    · have := Nat.div_add_mod (q - a) K
      rw [h3] at this
      rw [Nat.mul_comm]; omega

/-- The pattern of the selected-bit mask. -/
lemma runPat_sel {r₁ r₅ r₆ : Fin T} {K ρ N : ℕ} (q : ℕ) (hK : 0 < K) (h1 : (F r₁).length = ρ)
    (h5 : (F r₅).length = 1) (h6 : (F r₆).length = K - 1) :
    runPat F [(r₁, false)] N [(r₅, true), (r₆, false)] [] q =
      decide (ρ ≤ q ∧ q < ρ + N * K ∧ (q - ρ) % K = 0) := by
  simp only [runPat, runsLen, runBit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, h1, h5, h6]
  rw [show 1 + (K - 1) = K by omega]
  have := Nat.mod_lt (q - ρ) hK
  split_ifs <;> simp <;> omega

/-- The pattern of the digit-start mask. -/
lemma runPat_dig {r₅ r₇ : Fin T} {G N : ℕ} (q : ℕ) (hG : 0 < G) (h5 : (F r₅).length = 1)
    (h7 : (F r₇).length = G - 1) :
    runPat F [] N [(r₅, true), (r₇, false)] [] q = decide (q < N * G ∧ q % G = 0) := by
  simp only [runPat, runsLen, runBit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, Nat.zero_add, Nat.sub_zero, h5, h7]
  rw [show 1 + (G - 1) = G by omega]
  have := Nat.mod_lt q hG
  split_ifs <;> simp <;> omega

lemma testBit_selV (p : Par) (hK : 0 < p.K) (q : ℕ) :
    (selV p).testBit q = decide (p.ρ ≤ q ∧ q < p.ρ + p.n * p.K ∧ (q - p.ρ) % p.K = 0) := by
  rw [selV, Layer.CompactMasks.testBit_maskVal (posS_mono hK)]
  congr 1
  rw [← exists_mul_add_iff hK]
  simp [posS]

lemma testBit_mCV (p : Par) (hG : 0 < p.G) (q : ℕ) :
    (mCV p).testBit q = decide (q < p.n * p.G ∧ q % p.G = 0) := by
  rw [mCV, Layer.CompactMasks.testBit_maskVal (posC_mono hG)]
  congr 1
  have := exists_mul_add_iff (a := 0) (b := 0) (n := p.n) (q := q) hG
  simp only [Nat.zero_add, Nat.add_zero, Nat.zero_le, true_and, Nat.sub_zero] at this
  rw [← this]
  simp [posC]

/-- The pattern of the temporary mask. -/
lemma runPat_aux {r₁ r₅ r₂ r₈ : Fin T} {K ρ G N : ℕ} (q : ℕ) (hGK : G < K)
    (h1 : (F r₁).length = ρ) (h5 : (F r₅).length = 1) (h2 : (F r₂).length = G)
    (h8 : (F r₈).length = K - 1 - G) :
    runPat F [(r₁, false)] N [(r₅, false), (r₂, true), (r₈, false)] [] q =
      decide (ρ ≤ q ∧ q < ρ + N * K ∧ 1 ≤ (q - ρ) % K ∧ (q - ρ) % K < 1 + G) := by
  simp only [runPat, runsLen, runBit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, h1, h5, h2, h8]
  rw [show 1 + (G + (K - 1 - G)) = K by omega]
  have := Nat.mod_lt (q - ρ) (show 0 < K by omega)
  split_ifs <;> simp <;> omega

/-- The pattern of the phase mask. -/
lemma runPat_mk {r₁ r₅ r₇ r₉ : Fin T} {K ρ G N : ℕ} (q : ℕ) (hG : 0 < G) (hGK : G + 1 < K)
    (h1 : (F r₁).length = ρ) (h5 : (F r₅).length = 1) (h7 : (F r₇).length = G - 1)
    (h9 : (F r₉).length = K - 2 - G) :
    runPat F [(r₁, false)] N [(r₅, true), (r₅, true), (r₇, false), (r₅, true), (r₉, false)]
      [(r₅, true)] q =
      decide (ρ ≤ q ∧ ((q < ρ + N * K ∧
        ((q - ρ) % K = 0 ∨ (q - ρ) % K = 1 ∨ (q - ρ) % K = G + 1)) ∨ q = ρ + N * K)) := by
  simp only [runPat, runsLen, runBit, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, h1, h5, h7, h9]
  rw [show 1 + (1 + (G - 1 + (1 + (K - 2 - G)))) = K by omega]
  have := Nat.mod_lt (q - ρ) (show 0 < K by omega)
  split_ifs <;> simp <;> omega

lemma testBit_mAV (p : Par) (hG : 0 < p.G) (hGK : p.G < p.K) (q : ℕ) :
    (mAV p).testBit q = decide (p.ρ ≤ q ∧ q < p.ρ + p.n * p.K ∧ 1 ≤ (q - p.ρ) % p.K ∧
      (q - p.ρ) % p.K < 1 + p.G) := by
  rw [mAV, Layer.CompactMasks.testBit_maskVal (posA_mono hG hGK)]
  congr 1
  apply propext
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : j = j / p.G * p.G + j % p.G := (Nat.div_add_mod' j p.G).symm
    have hc : j / p.G < p.n := by rw [Nat.div_lt_iff_lt_mul hG]; exact hj
    have hg := Nat.mod_lt j hG
    rw [hj', posA_split hG _ _ hg]
    have := (exists_mul_add_iff (K := p.K) (a := p.ρ) (n := p.n) (b := 1 + j % p.G)
      (q := posS p (j / p.G) + 1 + j % p.G) (by omega)).1 ⟨j / p.G, hc, by unfold posS; omega⟩
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨c, hc, hq⟩ := (exists_mul_add_iff (K := p.K) (a := p.ρ) (n := p.n)
      (b := (q - p.ρ) % p.K) (q := q) (Nat.mod_lt _ (by omega))).2 ⟨h1, h2, rfl⟩
    refine ⟨c * p.G + ((q - p.ρ) % p.K - 1), ?_, ?_⟩
    · have := Nat.mul_le_mul_right p.G (show c + 1 ≤ p.n by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · rw [posA_split hG _ _ (by omega)]; unfold posS; omega

lemma testBit_mkV' (p : Par) (hG : 0 < p.G) (hGK : p.G + 1 < p.K) (q : ℕ) :
    (mkV p).testBit q = decide (p.ρ ≤ q ∧ ((q < p.ρ + p.n * p.K ∧
      ((q - p.ρ) % p.K = 0 ∨ (q - p.ρ) % p.K = 1 ∨ (q - p.ρ) % p.K = p.G + 1)) ∨
        q = p.ρ + p.n * p.K)) := by
  rw [Bool.eq_iff_iff, testBit_mkV hG hGK, decide_eq_true_iff]
  have hb : ∀ {b c}, b < p.K → c < p.n → p.ρ ≤ posS p c + b ∧
      posS p c + b < p.ρ + p.n * p.K ∧ (posS p c + b - p.ρ) % p.K = b := fun hb hc =>
    (exists_mul_add_iff hb).1 ⟨_, hc, by unfold posS; omega⟩
  constructor
  · rintro (⟨c, hc, rfl⟩ | ⟨c, hc, rfl | rfl⟩)
    · rcases Nat.lt_or_ge c p.n with h | h
      · have := hb (b := 0) (by omega) h
        simp only [Nat.add_zero] at this
        omega
      · obtain rfl : c = p.n := by omega
        unfold posS; omega
    · have := hb (b := 1) (by omega) hc; omega
    · have := hb (b := p.G + 1) (by omega) hc
      rw [show posS p c + 1 + p.G = posS p c + (p.G + 1) by omega]; omega
  · rintro ⟨h1, ⟨h2, h3⟩ | h2⟩
    · obtain ⟨c, hc, hq⟩ := (exists_mul_add_iff (K := p.K) (a := p.ρ) (n := p.n)
        (b := (q - p.ρ) % p.K) (q := q) (Nat.mod_lt _ (by omega))).2 ⟨h1, h2, rfl⟩
      rcases h3 with h | h | h
      · exact Or.inl ⟨c, hc.le, by unfold posS; omega⟩
      · exact Or.inr ⟨c, hc, Or.inl (by unfold posS; omega)⟩
      · exact Or.inr ⟨c, hc, Or.inr (by unfold posS; omega)⟩
    · exact Or.inl ⟨p.n, le_rfl, by unfold posS; omega⟩

lemma runMaskCost_le {n N a b c : ℕ} {pre item post : List (Fin T × Bool)}
    (hpre : runsCost F pre ≤ a) (hitem : runsCost F item ≤ b) (hpost : runsCost F post ≤ c) :
    runMaskCost F n N pre item post ≤ 10 * n + 10 + a + (N * (b + 3) + 2 * N + 4) + c := by
  unfold runMaskCost
  have := Nat.mul_le_mul_left N (Nat.add_le_add_right hitem 3)
  omega

/-- The step bound of a mask stage of width `n`. -/
def CxData.maskCost (d : CxData) (n : ℕ) : ℕ :=
  10 * n + 10 + (4 * d.ρ + 5) + ((d.k - 1) * (4 * d.K + 40 + 3) + 2 * (d.k - 1) + 4) + 9

end Masks

/-- A bound on the steps of each setup stage. -/
def CxData.setupStep (d : CxData) (o hB act cr cw : ℕ) : ℕ :=
  4 * (o + d.a₀) + 4 * (o + d.n) + 8 * o + 4 * hB + synDivModCost (d.k * d.K) d.K +
    synMulRCost (d.k - 1) d.G + synMulRCost act d.K + synMulRCost cr cw +
    4 * (2 ^ o * (cr * cw)) + 9 * o + 4 * (2 ^ d.n * d.R) + 16 * d.R + 64 * d.n + 64 * d.rb +
    64 * d.B + 16 * d.wc + 8 * d.K + 4 * d.G + 4 * d.a₀ + 4 * d.sT + 8 * (d.k * d.K) +
    6 * ((d.hi + 1) * (d.k * d.K) + d.a₀) +
    6 * (d.lens 0 + d.lens 1 + d.lens 2 + d.lens 3 + d.lens 4 + d.lens 5 + d.lens 6 + d.lens 7 +
      d.lens 8 + d.lens 9) + d.maskCost (d.k * d.K) + d.maskCost d.wc +
    6 * ((sxBits d.R).length + (sxBits (3 * (d.n + d.rb + d.B))).length + (sxBits d.wc).length + 1) +
    100


/-- Every setup register holds at most `setupStep` symbols. -/
lemma cxBc_length_le {A : ℕ} {d : CxData} (hd : d.OK) (o hB act cr cw : ℕ) (x : CxSet)
    (hx : 1 ≤ cxStage x) : (cxBc A d x).length ≤ d.setupStep o hB act cr cw := by
  have hfr := hd.front
  have hc : 2 ^ d.n * d.R = d.R * 2 ^ d.n := Nat.mul_comm _ _
  unfold CxData.setupStep
  simp only [synMulRCost, synDivModCost]
  rcases x with x | ⟨c, k⟩
  · cases x <;> simp only [cxStage] at hx
    case sc i => fin_cases i <;> simp [cxBc, CxData.scv] <;> omega
    case hb i => fin_cases i <;> simp [cxBc, CxData.hbv] <;> omega
    case fld g =>
      simp only [cxBc, length_binSyms]
      fin_cases g <;> simp <;> omega
    case mSel => simp only [cxBc, length_binSyms, hd.wy_eq, CxData.wy]; omega
    case mC => simp only [cxBc, length_binSyms, CxData.par_wc]; omega
    case mA => simp only [cxBc, length_binSyms, hd.wy_eq, CxData.wy]; omega
    case mMk => simp only [cxBc, length_binSyms, hd.wy_eq, CxData.wy]; omega
    all_goals simp [cxBc] <;> omega
  · simp only [cxBc, List.length_cons, CxData.hs, List.length_map, List.length_append,
      List.length_replicate]
    fin_cases c <;> fin_cases k <;> simp [CxData.he, CxData.hbits] <;> omega

/-! ### The stages -/

section Runs

variable {Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
variable {ι : CxReg → Fin T} {bank : Fin 2 → Fin (swapT 6) → Fin T} {inp : Fin 12 → Fin T}
  {d : CxData} {R₀ : Fin T → List (Fin (A + 4))} {o hB act cr cw : ℕ}
  (hall : Function.Injective (cxAll ι bank inp))
  (h0 : ∀ x : CxSet, x ≠ .reg .src → R₀ (cxSetReg ι bank x) = [])
include hall h0

/-- An empty temporary. -/
lemma cx_tw {s : ℕ} (i : Fin 4) : cxFile ι bank d s R₀ (ι (.tw i)) = [] :=
  (cxFile_unset hall (x := .reg (.tw i)) (Or.inr rfl)).trans (h0 _ (by simp))

/-- A register not yet filled. -/
lemma cx_unset {s : ℕ} {x : CxReg} (hx : s < cxStage (.reg x)) :
    cxFile ι bank d s R₀ (ι x) = [] :=
  (cxFile_unset hall (x := .reg x) (Or.inl hx)).trans (h0 _ (by
    intro e; cases e; simp [cxStage] at hx))

omit h0 in
/-- A filled register. -/
lemma cx_set {s : ℕ} {x : CxReg} (h1 : 1 ≤ cxStage (.reg x)) (h2 : cxStage (.reg x) ≤ s) :
    cxFile ι bank d s R₀ (ι x) = cxBc A d (.reg x) :=
  cxFile_set hall h1 h2

omit h0 in
/-- Stage `s + 1` from its run to the filled register. -/
lemma cx_stage {s : ℕ} {x : CxReg} (hx : cxStage (.reg x) = s + 1) {p : Pr P T Q A U} {c : ℕ}
    (h : LayRuns body p (cxFile ι bank d s R₀)
      (Function.update (cxFile ι bank d s R₀) (ι x) (cxBc A d (.reg x))) c) :
    LayRuns body p (cxFile ι bank d s R₀) (cxFile ι bank d (s + 1) R₀) c := by
  rw [← cxFile_step hall hx]; exact h

variable (hin : CxSetupIn d inp R₀ o hB act cr cw)
include hin

lemma cxRun1 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 1) (cxFile ι bank d 0 R₀) (cxFile ι bank d 1 R₀)
      (4 * (o + d.a₀) + 4 + (4 * o + 4)) := by
  refine cx_stage body hall (x := .sc 0) rfl ?_
  have ht := cx_tw hall h0 (d := d) (s := 0) 0
  have hz := cx_unset hall h0 (d := d) (s := 0) (x := .sc 0) (by simp [cxStage])
  have h1 := lr_ucopy body (R := cxFile ι bank d 0 R₀) (a := inp 3) (b := ι (.sc 0))
    (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) ht
  refine lr_weaken body (h1.seq (lr_usub body (a := inp 4) (by cxne) (by cxne) (by cxne)
    (by rw [Function.update_of_ne (by cxne)]; exact ht))) ?_ ?_
  · rw [Function.update_idem, Function.update_self, Function.update_of_ne (by cxne),
      cxFile_inp hall, cxFile_inp hall, hin.OA, hin.O, hz, List.append_nil, List.drop_replicate]
    simp [cxBc, CxData.scv]
  · rw [Function.update_of_ne (by cxne), cxFile_inp hall, cxFile_inp hall, hin.OA, hin.O]

lemma cxRun2 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 2) (cxFile ι bank d 1 R₀) (cxFile ι bank d 2 R₀)
      (4 * (o + d.n) + 4 + (4 * o + 4)) := by
  refine cx_stage body hall (x := .sc 1) rfl ?_
  have ht := cx_tw hall h0 (d := d) (s := 1) 0
  have hz := cx_unset hall h0 (d := d) (s := 1) (x := .sc 1) (by simp [cxStage])
  have h1 := lr_ucopy body (R := cxFile ι bank d 1 R₀) (a := inp 7) (b := ι (.sc 1))
    (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) ht
  refine lr_weaken body (h1.seq (lr_usub body (a := inp 4) (by cxne) (by cxne) (by cxne)
    (by rw [Function.update_of_ne (by cxne)]; exact ht))) ?_ ?_
  · rw [Function.update_idem, Function.update_self, Function.update_of_ne (by cxne),
      cxFile_inp hall, cxFile_inp hall, hin.ON, hin.O, hz, List.append_nil, List.drop_replicate]
    simp [cxBc, CxData.scv]
  · rw [Function.update_of_ne (by cxne), cxFile_inp hall, cxFile_inp hall, hin.ON, hin.O]

lemma cxRun3 (hd : d.OK) (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 3) (cxFile ι bank d 2 R₀) (cxFile ι bank d 3 R₀)
      (synDivModCost (d.k * d.K) d.K + 1) := by
  refine cx_stage body hall (x := .sc 2) rfl ?_
  have hK : 0 < d.K := by have := hd.ρK; omega
  have ht : ∀ i, cxFile ι bank d 2 R₀ (ι (.tw i)) = [] := fun i => cx_tw hall h0 (d := d) i
  have hz := cx_unset hall h0 (d := d) (s := 2) (x := .sc 2) (by simp [cxStage])
  have hell : (cxFile ι bank d 2 R₀ (inp 11)).length = d.k * d.K := by
    rw [cxFile_inp hall, hin.ell]
  have hKl : (cxFile ι bank d 2 R₀ (inp 0)).length = d.K := by rw [cxFile_inp hall, hin.K]
  have h1 := lr_synDivModR body (R := cxFile ι bank d 2 R₀) (x := inp 11) (k := inp 0)
    (q := ι (.sc 2)) (r := ι (.tw 1)) (t₁ := ι (.tw 0)) (t₂ := ι (.tw 2)) (t₃ := ι (.tw 3))
    (by
      exact cx_nodup hall [.inr 11, .inr 0, .inl (.reg (.sc 2)), .inl (.reg (.tw 1)),
      .inl (.reg (.tw 0)), .inl (.reg (.tw 2)), .inl (.reg (.tw 3))] (by decide))
    (by rw [hKl]; exact hK) (ht 1) (ht 0) (ht 2) (ht 3)
  rw [hell, hKl, Nat.mul_mod_left, Nat.mul_div_cancel _ hK, List.replicate_zero, hz,
    List.append_nil] at h1
  refine lr_weaken body (h1.seq (lr_pop body _)) ?_ le_rfl
  have hF : Function.update (cxFile ι bank d 2 R₀) (ι (.tw 1)) [] = cxFile ι bank d 2 R₀ := by
    rw [← ht 1, Function.update_eq_self]
  rw [Function.update_self, Function.update_idem, List.tail_replicate, hF]
  simp [cxBc, CxData.scv]

lemma cxRun4 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 4) (cxFile ι bank d 3 R₀) (cxFile ι bank d 4 R₀)
      (synMulRCost (d.k - 1) d.G) := by
  refine cx_stage body hall (x := .sc 3) rfl ?_
  have ht : ∀ i, cxFile ι bank d 3 R₀ (ι (.tw i)) = [] := fun i => cx_tw hall h0 (d := d) i
  have hz := cx_unset hall h0 (d := d) (s := 3) (x := .sc 3) (by simp [cxStage])
  have hk : (cxFile ι bank d 3 R₀ (ι (.sc 2))).length = d.k - 1 := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have hG : (cxFile ι bank d 3 R₀ (inp 2)).length = d.G := by rw [cxFile_inp hall, hin.G]
  have h1 := lr_synMulR body (R := cxFile ι bank d 3 R₀) (a := ι (.sc 2)) (b := inp 2)
    (c := ι (.sc 3)) (t₁ := ι (.tw 0)) (t₂ := ι (.tw 1))
    (by
      exact cx_nodup hall [.inl (.reg (.sc 2)), .inr 2, .inl (.reg (.sc 3)), .inl (.reg (.tw 0)),
      .inl (.reg (.tw 1))] (by decide)) (ht 0) (ht 1)
  rw [hk, hG, hz, List.append_nil] at h1
  refine lr_weaken body h1 ?_ le_rfl
  simp [cxBc, CxData.scv, CxData.wc]

lemma cxRun5 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 5) (cxFile ι bank d 4 R₀) (cxFile ι bank d 5 R₀)
      (4 * hB + 4 + synMulRCost act d.K) := by
  refine cx_stage body hall (x := .sc 4) rfl ?_
  have ht : ∀ i, cxFile ι bank d 4 R₀ (ι (.tw i)) = [] := fun i => cx_tw hall h0 (d := d) i
  have hz := cx_unset hall h0 (d := d) (s := 4) (x := .sc 4) (by simp [cxStage])
  have h1 := lr_ucopy body (R := cxFile ι bank d 4 R₀) (a := inp 5) (b := ι (.sc 4))
    (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) (ht 0)
  rw [cxFile_inp hall, hin.HB, hz, List.append_nil] at h1
  have h2 := lr_synMulR body
    (R := Function.update (cxFile ι bank d 4 R₀) (ι (.sc 4)) (List.replicate hB tick))
    (a := inp 6) (b := inp 0) (c := ι (.sc 4)) (t₁ := ι (.tw 0)) (t₂ := ι (.tw 1))
    (by
      exact cx_nodup hall [.inr 6, .inr 0, .inl (.reg (.sc 4)), .inl (.reg (.tw 0)),
      .inl (.reg (.tw 1))] (by decide))
    (by rw [Function.update_of_ne (by cxne)]; exact ht 0)
    (by rw [Function.update_of_ne (by cxne)]; exact ht 1)
  simp only [Function.update_self, Function.update_of_ne (cxι_inp hall _ _).symm,
    cxFile_inp hall, hin.Act, hin.K] at h2
  refine lr_weaken body (h1.seq h2) ?_ le_rfl
  rw [Function.update_idem, List.replicate_append_replicate]
  simp [cxBc, CxData.scv, hin.sT, Nat.add_comm]

omit hin in
lemma cxRun6 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 6) (cxFile ι bank d 5 R₀) (cxFile ι bank d 6 R₀) 1 := by
  refine cx_stage body hall (x := .sc 5) rfl ?_
  have hz := cx_unset hall h0 (d := d) (s := 5) (x := .sc 5) (by simp [cxStage])
  refine lr_weaken body (lr_push body _ _) ?_ le_rfl
  rw [hz]; simp [cxBc, CxData.scv]

omit hin in
/-- Copy an input of `a` ticks and drop one tick. -/
lemma cx_copyPop {s : ℕ} {x : CxReg} (hx : s < cxStage (.reg x)) (hxt : x ≠ .tw 0) (i : Fin 12)
    {a : ℕ} (ha : (R₀ (inp i)).length = a) :
    LayRuns body (.seq (ucopy (inp i) (ι x) (ι (.tw 0))) (synPop (ι x))) (cxFile ι bank d s R₀)
      (Function.update (cxFile ι bank d s R₀) (ι x) (List.replicate (a - 1) tick)) (4 * a + 5) := by
  have ht := cx_tw hall h0 (d := d) (s := s) 0
  have hz := cx_unset hall h0 (d := d) (s := s) (x := x) hx
  have h1 := lr_ucopy body (R := cxFile ι bank d s R₀) (a := inp i) (b := ι x)
    (t := ι (.tw 0)) (cxι_inp hall _ _).symm (by cxne) (cxι_ne hall hxt) ht
  rw [cxFile_inp hall, ha, hz, List.append_nil] at h1
  refine lr_weaken body (h1.seq (lr_pop body _)) ?_ le_rfl
  rw [Function.update_self, Function.update_idem, List.tail_replicate]

lemma cxRun7 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 7) (cxFile ι bank d 6 R₀) (cxFile ι bank d 7 R₀)
      (4 * d.K + 5) := by
  refine cx_stage body hall (x := .sc 6) rfl ?_
  refine lr_weaken body (cx_copyPop body hall h0 (by simp [cxStage]) (by decide) 0 hin.K) ?_ le_rfl
  simp [cxBc, CxData.scv]

lemma cxRun8 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 8) (cxFile ι bank d 7 R₀) (cxFile ι bank d 8 R₀)
      (4 * d.G + 5) := by
  refine cx_stage body hall (x := .sc 7) rfl ?_
  refine lr_weaken body (cx_copyPop body hall h0 (by simp [cxStage]) (by decide) 2 hin.G) ?_ le_rfl
  simp [cxBc, CxData.scv]

lemma cxRun9 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 9) (cxFile ι bank d 8 R₀) (cxFile ι bank d 9 R₀)
      (4 * d.K + 5 + (4 * d.G + 4)) := by
  refine cx_stage body hall (x := .sc 8) rfl ?_
  have ht := cx_tw hall h0 (d := d) (s := 8) 0
  have h1 := cx_copyPop body hall h0 (d := d) (s := 8) (x := .sc 8) (by simp [cxStage])
    (by decide) 0 hin.K
  refine lr_weaken body (h1.seq (lr_usub body (a := inp 2) (by cxne) (by cxne) (by cxne)
    (by rw [Function.update_of_ne (by cxne)]; exact ht))) ?_ ?_
  · rw [Function.update_idem, Function.update_self, Function.update_of_ne (by cxne),
      cxFile_inp hall, hin.G, List.drop_replicate]
    simp [cxBc, CxData.scv, Nat.sub_sub]
  · rw [Function.update_of_ne (by cxne), cxFile_inp hall, hin.G]

omit hin in
lemma cxRun10 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 10) (cxFile ι bank d 9 R₀) (cxFile ι bank d 10 R₀)
      (4 * (d.K - 1 - d.G) + 5) := by
  refine cx_stage body hall (x := .sc 9) rfl ?_
  have ht := cx_tw hall h0 (d := d) (s := 9) 0
  have hz := cx_unset hall h0 (d := d) (s := 9) (x := .sc 9) (by simp [cxStage])
  have h8 : cxFile ι bank d 9 R₀ (ι (.sc 8)) = List.replicate (d.K - 1 - d.G) tick := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have h1 := lr_ucopy body (R := cxFile ι bank d 9 R₀) (a := ι (.sc 8)) (b := ι (.sc 9))
    (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) ht
  rw [h8, hz, List.append_nil, List.length_replicate] at h1
  refine lr_weaken body (h1.seq (lr_pop body _)) ?_ le_rfl
  rw [Function.update_self, Function.update_idem, List.tail_replicate]
  simp only [cxBc, CxData.scv]
  congr 2
  simp; omega

lemma cxRun11 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 11) (cxFile ι bank d 10 R₀) (cxFile ι bank d 11 R₀)
      (16 * d.R + 4) := by
  refine cx_stage body hall (x := .hb 0) rfl ?_
  have ht : ∀ i, cxFile ι bank d 10 R₀ (ι (.tw i)) = [] := fun i => cx_tw hall h0 (d := d) i
  have hz := cx_unset hall h0 (d := d) (s := 10) (x := .hb 0) (by simp [cxStage])
  have h1 := lr_sxBinConv body (R := cxFile ι bank d 10 R₀) (a := inp 8) (d := ι (.hb 0))
    (t₁ := ι (.tw 0)) (t₂ := ι (.tw 1))
    (by
      exact cx_nodup hall [.inr 8, .inl (.reg (.hb 0)), .inl (.reg (.tw 0)),
      .inl (.reg (.tw 1))] (by decide)) hz (ht 0) (ht 1)
  rw [cxFile_inp hall, hin.R] at h1
  exact lr_weaken body h1 (by simp [cxBc, CxData.hbv]) le_rfl

lemma cxRun12 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 12) (cxFile ι bank d 11 R₀) (cxFile ι bank d 12 R₀)
      (synMulRCost cr cw + (4 * (2 ^ o * (cr * cw)) + 9 * o + 4)) := by
  refine cx_stage body hall (x := .ctrB) rfl ?_
  have ht : ∀ i, cxFile ι bank d 11 R₀ (ι (.tw i)) = [] := fun i => cx_tw hall h0 (d := d) i
  have hz := cx_unset hall h0 (d := d) (s := 11) (x := .ctrB) (by simp [cxStage])
  have h1 := lr_synMulR body (R := cxFile ι bank d 11 R₀) (a := inp 9) (b := inp 10)
    (c := ι .ctrB) (t₁ := ι (.tw 0)) (t₂ := ι (.tw 1))
    (by
      exact cx_nodup hall [.inr 9, .inr 10, .inl (.reg .ctrB), .inl (.reg (.tw 0)),
      .inl (.reg (.tw 1))] (by decide)) (ht 0) (ht 1)
  rw [cxFile_inp hall, cxFile_inp hall, hin.r, hin.w, hz, List.append_nil] at h1
  have h2 := lr_upow2 body
    (R := Function.update (cxFile ι bank d 11 R₀) (ι .ctrB) (List.replicate (cr * cw) tick))
    (a := inp 4) (b := ι .ctrB) (t₁ := ι (.tw 0)) (t₂ := ι (.tw 1))
    (by
      exact cx_nodup hall [.inr 4, .inl (.reg .ctrB), .inl (.reg (.tw 0)),
      .inl (.reg (.tw 1))] (by decide))
    (by rw [Function.update_of_ne (by cxne)]; exact ht 0)
    (by rw [Function.update_of_ne (by cxne)]; exact ht 1)
  simp only [Function.update_self, Function.update_of_ne (cxι_inp hall _ _).symm,
    cxFile_inp hall, hin.O, List.length_replicate] at h2
  refine lr_weaken body (h1.seq h2) ?_ (by omega)
  rw [Function.update_idem, flatMap_replicate_rep]
  simp [cxBc, hin.B]

omit hin in
lemma cxRun13 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 13) (cxFile ι bank d 12 R₀) (cxFile ι bank d 13 R₀)
      (4 * d.n + 4 + (4 * d.rb + 4)) := by
  refine cx_stage body hall (x := .ctrK) rfl ?_
  have ht := cx_tw hall h0 (d := d) (s := 12) 0
  have hz := cx_unset hall h0 (d := d) (s := 12) (x := .ctrK) (by simp [cxStage])
  have hn : cxFile ι bank d 12 R₀ (ι (.sc 1)) = List.replicate d.n tick := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have hb : (cxFile ι bank d 12 R₀ (ι (.hb 0))).length = d.rb := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.hbv, CxData.rb]
  have h1 := lr_ucopy body (R := cxFile ι bank d 12 R₀) (a := ι (.sc 1)) (b := ι .ctrK)
    (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) ht
  rw [hn, hz, List.append_nil, List.length_replicate] at h1
  refine lr_weaken body (h1.seq (lr_ucopy body (a := ι (.hb 0)) (by cxne) (by cxne) (by cxne)
    (by rw [Function.update_of_ne (by cxne)]; exact ht))) ?_ ?_
  · rw [Function.update_idem, Function.update_self, Function.update_of_ne (by cxne), hb,
      List.replicate_append_replicate]
    simp [cxBc, Nat.add_comm]
  · rw [Function.update_of_ne (by cxne), hb]

omit hin in
lemma cxRun14 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 14) (cxFile ι bank d 13 R₀) (cxFile ι bank d 14 R₀)
      (4 * (d.n + d.rb) + 4 + (4 * d.B + 4)) := by
  refine cx_stage body hall (x := .ctr) rfl ?_
  have ht := cx_tw hall h0 (d := d) (s := 13) 0
  have hz := cx_unset hall h0 (d := d) (s := 13) (x := .ctr) (by simp [cxStage])
  have hk : cxFile ι bank d 13 R₀ (ι .ctrK) = List.replicate (d.n + d.rb) tick := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; rfl
  have hb : (cxFile ι bank d 13 R₀ (ι .ctrB)).length = d.B := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc]
  have h1 := lr_ucopy body (R := cxFile ι bank d 13 R₀) (a := ι .ctrK) (b := ι .ctr)
    (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) ht
  rw [hk, hz, List.append_nil, List.length_replicate] at h1
  refine lr_weaken body (h1.seq (lr_ucopy body (a := ι .ctrB) (by cxne) (by cxne) (by cxne)
    (by rw [Function.update_of_ne (by cxne)]; exact ht))) ?_ ?_
  · rw [Function.update_idem, Function.update_self, Function.update_of_ne (by cxne), hb,
      List.replicate_append_replicate]
    simp only [cxBc]
    congr 2; omega
  · rw [Function.update_of_ne (by cxne), hb]

lemma cxRun15 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 15) (cxFile ι bank d 14 R₀) (cxFile ι bank d 15 R₀)
      (4 * d.R + 4 + (4 * (2 ^ d.n * d.R) + 9 * d.n + 4)) := by
  refine cx_stage body hall (x := .cnt) rfl ?_
  have ht : ∀ i, cxFile ι bank d 14 R₀ (ι (.tw i)) = [] := fun i => cx_tw hall h0 (d := d) i
  have hz := cx_unset hall h0 (d := d) (s := 14) (x := .cnt) (by simp [cxStage])
  have hn : (cxFile ι bank d 14 R₀ (ι (.sc 1))).length = d.n := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have h1 := lr_ucopy body (R := cxFile ι bank d 14 R₀) (a := inp 8) (b := ι .cnt)
    (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) (ht 0)
  rw [cxFile_inp hall, hin.R, hz, List.append_nil] at h1
  have h2 := lr_upow2 body
    (R := Function.update (cxFile ι bank d 14 R₀) (ι .cnt) (List.replicate d.R tick))
    (a := ι (.sc 1)) (b := ι .cnt) (t₁ := ι (.tw 0)) (t₂ := ι (.tw 1))
    (by
      exact cx_nodup hall [.inl (.reg (.sc 1)), .inl (.reg .cnt), .inl (.reg (.tw 0)),
      .inl (.reg (.tw 1))] (by decide))
    (by rw [Function.update_of_ne (by cxne)]; exact ht 0)
    (by rw [Function.update_of_ne (by cxne)]; exact ht 1)
  simp only [Function.update_self, Function.update_of_ne (cxι_ne hall (by decide :
    CxReg.sc 1 ≠ .cnt)), hn, List.length_replicate] at h2
  refine lr_weaken body (h1.seq h2) ?_ le_rfl
  rw [Function.update_idem, flatMap_replicate_rep]
  rfl

omit hin in
lemma cxRun16 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 16) (cxFile ι bank d 15 R₀) (cxFile ι bank d 16 R₀)
      (4 * (d.n + d.rb + d.B) + 4 + (16 * (3 * (d.n + d.rb + d.B)) + 4) +
        (2 * (3 * (d.n + d.rb + d.B)) + 2)) := by
  refine cx_stage body hall (x := .hb 1) rfl ?_
  have ht : ∀ i, cxFile ι bank d 15 R₀ (ι (.tw i)) = [] := fun i => cx_tw hall h0 (d := d) i
  have hz := cx_unset hall h0 (d := d) (s := 15) (x := .hb 1) (by simp [cxStage])
  have hc : (cxFile ι bank d 15 R₀ (ι .ctr)).length = d.n + d.rb + d.B := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc]
  have h1 := lr_umul body (R := cxFile ι bank d 15 R₀) 3 (a := ι .ctr) (b := ι (.tw 2))
    (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) (ht 0)
  rw [hc, ht 2, List.append_nil] at h1
  have h2 := lr_sxBinConv body
    (R := Function.update (cxFile ι bank d 15 R₀) (ι (.tw 2))
      (List.replicate (3 * (d.n + d.rb + d.B)) tick))
    (a := ι (.tw 2)) (d := ι (.hb 1)) (t₁ := ι (.tw 0)) (t₂ := ι (.tw 1))
    (by
      exact cx_nodup hall [.inl (.reg (.tw 2)), .inl (.reg (.hb 1)), .inl (.reg (.tw 0)),
      .inl (.reg (.tw 1))] (by decide))
    (by rw [Function.update_of_ne (by cxne)]; exact hz)
    (by rw [Function.update_of_ne (by cxne)]; exact ht 0)
    (by rw [Function.update_of_ne (by cxne)]; exact ht 1)
  simp only [Function.update_self, List.length_replicate] at h2
  refine lr_weaken body ((h1.seq h2).seq (lr_uclear body _)) ?_ ?_
  · rw [Function.update_comm (by cxne : ι (.tw 2) ≠ ι (.hb 1)), Function.update_idem]
    have hF : Function.update (cxFile ι bank d 15 R₀) (ι (.tw 2)) [] = cxFile ι bank d 15 R₀ := by
      rw [← ht 2, Function.update_eq_self]
    rw [Function.update_comm (by cxne : ι (.hb 1) ≠ ι (.tw 2)), hF]
    simp [cxBc, CxData.hbv]
  · rw [Function.update_of_ne (by cxne), Function.update_self, List.length_replicate]

omit hin in
lemma cxRun17 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 17) (cxFile ι bank d 16 R₀) (cxFile ι bank d 17 R₀)
      (16 * d.wc + 4) := by
  refine cx_stage body hall (x := .hb 2) rfl ?_
  have ht : ∀ i, cxFile ι bank d 16 R₀ (ι (.tw i)) = [] := fun i => cx_tw hall h0 (d := d) i
  have hz := cx_unset hall h0 (d := d) (s := 16) (x := .hb 2) (by simp [cxStage])
  have hw : (cxFile ι bank d 16 R₀ (ι (.sc 3))).length = d.wc := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have h1 := lr_sxBinConv body (R := cxFile ι bank d 16 R₀) (a := ι (.sc 3)) (d := ι (.hb 2))
    (t₁ := ι (.tw 0)) (t₂ := ι (.tw 1))
    (by
      exact cx_nodup hall [.inl (.reg (.sc 3)), .inl (.reg (.hb 2)), .inl (.reg (.tw 0)),
      .inl (.reg (.tw 1))] (by decide)) hz (ht 0) (ht 1)
  rw [hw] at h1
  exact lr_weaken body h1 (by simp [cxBc, CxData.hbv]) le_rfl

omit hin in
/-- A field at zero from a register of its length. -/
lemma cx_zeroField {s : ℕ} {g : Fin 10} (hg : cxStage (.reg (.fld g)) = s + 1) {r : Fin T}
    (hr1 : r ≠ ι (.fld g)) (hr2 : r ≠ ι (.tw 0)) (hl : (cxFile ι bank d s R₀ r).length = d.lens g) :
    LayRuns body (zeroBits r (ι (.fld g)) (ι (.tw 0))) (cxFile ι bank d s R₀)
      (cxFile ι bank d (s + 1) R₀) (4 * d.lens g + 4) := by
  refine cx_stage body hall (x := .fld g) hg ?_
  have hz := cx_unset hall h0 (d := d) (s := s) (x := .fld g) (by omega)
  have h1 := lr_zeroBits body (R := cxFile ι bank d s R₀) hr1 hr2 (by cxne)
    (cx_tw hall h0 (d := d) 0)
  rw [hl, hz, List.append_nil] at h1
  exact lr_weaken body h1 (by simp [cxBc]) le_rfl

omit hin in
/-- A field at zero from a temporary built by `p`. -/
lemma cx_tempField {s : ℕ} {g : Fin 10} (hg : cxStage (.reg (.fld g)) = s + 1) {p : Pr P T Q A U}
    {c : ℕ} (hp : LayRuns body p (cxFile ι bank d s R₀)
      (Function.update (cxFile ι bank d s R₀) (ι (.tw 2)) (List.replicate (d.lens g) tick)) c) :
    LayRuns body (.seq p (.seq (zeroBits (ι (.tw 2)) (ι (.fld g)) (ι (.tw 0))) (uclear (ι (.tw 2)))))
      (cxFile ι bank d s R₀) (cxFile ι bank d (s + 1) R₀)
      (c + (4 * d.lens g + 4 + (2 * d.lens g + 2))) := by
  refine cx_stage body hall (x := .fld g) hg ?_
  have ht := cx_tw hall h0 (d := d) (s := s)
  have hz := cx_unset hall h0 (d := d) (s := s) (x := .fld g) (by omega)
  refine lr_weaken body (hp.seq ((lr_zeroBits body (by cxne) (by cxne) (by cxne)
    (by rw [Function.update_of_ne (by cxne)]; exact ht 0)).seq (lr_uclear body _))) ?_ ?_
  · rw [Function.update_self, Function.update_of_ne (by cxne), hz, List.append_nil,
      Function.update_comm (by cxne : ι (.tw 2) ≠ ι (.fld g)), Function.update_idem]
    have hF : Function.update (cxFile ι bank d s R₀) (ι (.tw 2)) [] = cxFile ι bank d s R₀ := by
      rw [← ht 2, Function.update_eq_self]
    rw [Function.update_comm (by cxne : ι (.fld g) ≠ ι (.tw 2)), hF, List.length_replicate]
    simp [cxBc]
  · rw [Function.update_self, Function.update_of_ne (by cxne), Function.update_self,
      List.length_replicate]

omit hin in
lemma cxRun18 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 18) (cxFile ι bank d 17 R₀) (cxFile ι bank d 18 R₀)
      (4 * d.lens 0 + 4) :=
  cx_zeroField body hall h0 (g := 0) rfl (by cxne) (by cxne) (by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv, CxData.lens])

lemma cxRun20 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 20) (cxFile ι bank d 19 R₀) (cxFile ι bank d 20 R₀)
      (4 * d.lens 2 + 4) :=
  cx_zeroField body hall h0 (g := 2) rfl (by cxne) (by cxne) (by
    rw [cxFile_inp hall, hin.ell]; simp [CxData.lens, CxData.wy])

lemma cxRun22 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 22) (cxFile ι bank d 21 R₀) (cxFile ι bank d 22 R₀)
      (4 * d.lens 4 + 4) :=
  cx_zeroField body hall h0 (g := 4) rfl (by cxne) (by cxne) (by
    rw [cxFile_inp hall, hin.ell]; simp [CxData.lens, CxData.wy])

omit hin in
lemma cxRun24 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 24) (cxFile ι bank d 23 R₀) (cxFile ι bank d 24 R₀)
      (4 * d.lens 6 + 4) :=
  cx_zeroField body hall h0 (g := 6) rfl (by cxne) (by cxne) (by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv, CxData.lens])

omit hin in
lemma cxRun26 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 26) (cxFile ι bank d 25 R₀) (cxFile ι bank d 26 R₀)
      (4 * d.lens 8 + 4) :=
  cx_zeroField body hall h0 (g := 8) rfl (by cxne) (by cxne) (by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv, CxData.lens])

omit hin in
lemma cxRun25 (lo hi : ℕ) :
    LayRuns body (cxStageProg ι bank inp lo hi 25) (cxFile ι bank d 24 R₀) (cxFile ι bank d 25 R₀) 1 := by
  refine cx_stage body hall (x := .fld 7) rfl ?_
  have hz := cx_unset hall h0 (d := d) (s := 24) (x := .fld 7) (by simp [cxStage])
  refine lr_weaken body (lr_skip body _) ?_ le_rfl
  have hc : cxBc A d (.reg (.fld 7)) = [] := by simp [cxBc, CxData.lens, binSyms]
  rw [hc, ← hz, Function.update_eq_self]

lemma cxRun19 :
    LayRuns body (cxStageProg ι bank inp d.lo d.hi 19) (cxFile ι bank d 18 R₀)
      (cxFile ι bank d 19 R₀)
      ((4 * d.a₀ + 4 + (4 * (d.k * d.K) + 4) + (4 * d.wc + 4)) +
        (4 * d.lens 1 + 4 + (2 * d.lens 1 + 2))) := by
  refine cx_tempField body hall h0 (g := 1) rfl ?_
  have ht : ∀ i, cxFile ι bank d 18 R₀ (ι (.tw i)) = [] := fun i => cx_tw hall h0 (d := d) i
  have h0' : cxFile ι bank d 18 R₀ (ι (.sc 0)) = List.replicate d.a₀ tick := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have h3 : (cxFile ι bank d 18 R₀ (ι (.sc 3))).length = d.wc := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have h1 := lr_ucopy body (R := cxFile ι bank d 18 R₀) (a := ι (.sc 0)) (b := ι (.tw 2))
    (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) (ht 0)
  rw [h0', ht 2, List.append_nil, List.length_replicate] at h1
  have h2 := lr_umul body (R := Function.update (cxFile ι bank d 18 R₀) (ι (.tw 2))
    (List.replicate d.a₀ tick)) d.lo (a := inp 11) (b := ι (.tw 2)) (t := ι (.tw 0)) (by cxne)
    (by cxne) (by cxne) (by rw [Function.update_of_ne (by cxne)]; exact ht 0)
  simp only [Function.update_self, Function.update_of_ne (cxι_inp hall _ _).symm, cxFile_inp hall,
    hin.ell, Function.update_idem, List.replicate_append_replicate] at h2
  have h3' := lr_usub body (R := Function.update (cxFile ι bank d 18 R₀) (ι (.tw 2))
    (List.replicate (d.lo * (d.k * d.K) + d.a₀) tick)) (a := ι (.sc 3)) (b := ι (.tw 2))
    (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne)
    (by rw [Function.update_of_ne (by cxne)]; exact ht 0)
  simp only [Function.update_self, Function.update_of_ne (cxι_ne hall (by decide :
    CxReg.sc 3 ≠ .tw 2)), h3, Function.update_idem, List.drop_replicate] at h3'
  refine lr_weaken body ((h1.seq h2).seq h3') ?_ (by omega)
  congr 2
  simp only [CxData.lens, CxData.sLo, CxData.wy, Matrix.cons_val_one]
  congr 1; ring_nf

lemma cxRun21 (hd : d.OK) :
    LayRuns body (cxStageProg ι bank inp d.lo d.hi 21) (cxFile ι bank d 20 R₀)
      (cxFile ι bank d 21 R₀)
      ((4 * (d.k * d.K) + 4) + (4 * d.lens 3 + 4 + (2 * d.lens 3 + 2))) := by
  refine cx_tempField body hall h0 (g := 3) rfl ?_
  have ht : ∀ i, cxFile ι bank d 20 R₀ (ι (.tw i)) = [] := fun i => cx_tw hall h0 (d := d) i
  have h1 := lr_umul body (R := cxFile ι bank d 20 R₀) (d.hi - d.lo - 1) (a := inp 11)
    (b := ι (.tw 2)) (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) (ht 0)
  rw [cxFile_inp hall, hin.ell, ht 2, List.append_nil] at h1
  refine lr_weaken body h1 ?_ le_rfl
  have hlh := hd.lo_hi
  congr 2
  simp only [CxData.lens, CxData.sLo, CxData.sHi, CxData.wy]
  simp only [Fin.isValue, Matrix.cons_val]
  obtain ⟨j, hj⟩ : ∃ j, d.hi = d.lo + 1 + j := ⟨d.hi - d.lo - 1, by omega⟩
  rw [hj, show d.lo + 1 + j - d.lo - 1 = j by omega]
  ring_nf; omega

omit hin in
lemma cxRun27 :
    LayRuns body (cxStageProg ι bank inp d.lo d.hi 27) (cxFile ι bank d 26 R₀)
      (cxFile ι bank d 27 R₀)
      ((4 * d.n + 4 + (4 * d.sT + 4) + (4 * d.wc + 4) + (4 * d.wc + 4) + (4 * d.rb + 4)) +
        (4 * d.lens 9 + 4 + (2 * d.lens 9 + 2))) := by
  refine cx_tempField body hall h0 (g := 9) rfl ?_
  have ht : ∀ i, cxFile ι bank d 26 R₀ (ι (.tw i)) = [] := fun i => cx_tw hall h0 (d := d) i
  have e1 : cxFile ι bank d 26 R₀ (ι (.sc 1)) = List.replicate d.n tick := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e4 : (cxFile ι bank d 26 R₀ (ι (.sc 4))).length = d.sT := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e3 : (cxFile ι bank d 26 R₀ (ι (.sc 3))).length = d.wc := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have eb : (cxFile ι bank d 26 R₀ (ι (.hb 0))).length = d.rb := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.hbv, CxData.rb]
  set F := cxFile ι bank d 26 R₀
  have ht' : ∀ X, Function.update F (ι (.tw 2)) X (ι (.tw 0)) = [] := fun X => by
    rw [Function.update_of_ne (by cxne)]; exact ht 0
  have hr : ∀ (X : List (Fin (A + 4))) (x : CxReg), x ≠ .tw 2 →
      Function.update F (ι (.tw 2)) X (ι x) = F (ι x) := fun X x hx =>
    Function.update_of_ne (cxι_ne hall hx) _ _
  have h1 := lr_ucopy body (R := F) (a := ι (.sc 1)) (b := ι (.tw 2)) (t := ι (.tw 0)) (by cxne)
    (by cxne) (by cxne) (ht 0)
  rw [e1, ht 2, List.append_nil, List.length_replicate] at h1
  have h2 := lr_usub body (R := Function.update F (ι (.tw 2)) (List.replicate d.n tick))
    (a := ι (.sc 4)) (b := ι (.tw 2)) (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) (ht' _)
  rw [Function.update_self, hr _ _ (by decide), e4, Function.update_idem,
    List.drop_replicate] at h2
  have h3 := lr_usub body (R := Function.update F (ι (.tw 2)) (List.replicate (d.n - d.sT) tick))
    (a := ι (.sc 3)) (b := ι (.tw 2)) (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) (ht' _)
  rw [Function.update_self, hr _ _ (by decide), e3, Function.update_idem,
    List.drop_replicate] at h3
  have h4 := lr_usub body (R := Function.update F (ι (.tw 2))
    (List.replicate (d.n - d.sT - d.wc) tick))
    (a := ι (.sc 3)) (b := ι (.tw 2)) (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) (ht' _)
  rw [Function.update_self, hr _ _ (by decide), e3, Function.update_idem,
    List.drop_replicate] at h4
  have h5 := lr_ucopy body (R := Function.update F (ι (.tw 2))
    (List.replicate (d.n - d.sT - d.wc - d.wc) tick))
    (a := ι (.hb 0)) (b := ι (.tw 2)) (t := ι (.tw 0)) (by cxne) (by cxne) (by cxne) (ht' _)
  rw [Function.update_self, hr _ _ (by decide), eb, Function.update_idem,
    List.replicate_append_replicate] at h5
  refine lr_weaken body ((((h1.seq h2).seq h3).seq h4).seq h5) ?_ (by omega)
  congr 2
  simp only [CxData.lens]
  simp only [Fin.isValue, Matrix.cons_val]
  omega

lemma cxRun23 :
    LayRuns body (cxStageProg ι bank inp d.lo d.hi 23) (cxFile ι bank d 22 R₀)
      (cxFile ι bank d 23 R₀)
      ((4 * d.sT + 4 + (4 * d.a₀ + 4) + (4 * (d.k * d.K) + 4) +
        (4 * ((d.hi + 1) * (d.k * d.K) + d.a₀) + 4) +
        (2 * ((d.hi + 1) * (d.k * d.K) + d.a₀) + 2)) +
        (4 * d.lens 5 + 4 + (2 * d.lens 5 + 2))) := by
  refine cx_tempField body hall h0 (g := 5) rfl ?_
  have ht : ∀ i, cxFile ι bank d 22 R₀ (ι (.tw i)) = [] := fun i => cx_tw hall h0 (d := d) i
  have e4 : (cxFile ι bank d 22 R₀ (ι (.sc 4))).length = d.sT := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e0 : (cxFile ι bank d 22 R₀ (ι (.sc 0))).length = d.a₀ := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have eL : (cxFile ι bank d 22 R₀ (inp 11)).length = d.k * d.K := by
    rw [cxFile_inp hall, hin.ell]
  set F := cxFile ι bank d 22 R₀
  have h1 := lr_ucopy body (R := F) (a := ι (.sc 4)) (b := ι (.tw 2)) (t := ι (.tw 0)) (by cxne)
    (by cxne) (by cxne) (ht 0)
  rw [e4, ht 2, List.append_nil] at h1
  have h2 := lr_ucopy body (R := Function.update F (ι (.tw 2)) (List.replicate d.sT tick)) (a := ι (.sc 0)) (b := ι (.tw 3)) (t := ι (.tw 0)) (by cxne)
    (by cxne) (by cxne) (by rw [Function.update_of_ne (by cxne)]; exact ht 0)
  rw [Function.update_of_ne (by cxne), e0, Function.update_of_ne (by cxne), ht 3,
    List.append_nil] at h2
  have h3 := lr_umul body (R := Function.update (Function.update F (ι (.tw 2)) (List.replicate d.sT tick)) (ι (.tw 3)) (List.replicate d.a₀ tick)) (d.hi + 1) (a := inp 11) (b := ι (.tw 3)) (t := ι (.tw 0))
    (by cxne) (by cxne) (by cxne)
    (by rw [Function.update_of_ne (by cxne), Function.update_of_ne (by cxne)]; exact ht 0)
  rw [Function.update_of_ne (cxι_inp hall _ _).symm, Function.update_of_ne (cxι_inp hall _ _).symm,
    eL, Function.update_self,
    List.replicate_append_replicate, Function.update_idem] at h3
  have h4 := lr_usub body (R := Function.update (Function.update F (ι (.tw 2)) (List.replicate d.sT tick)) (ι (.tw 3))
    (List.replicate ((d.hi + 1) * (d.k * d.K) + d.a₀) tick)) (a := ι (.tw 3)) (b := ι (.tw 2)) (t := ι (.tw 0))
    (by cxne) (by cxne) (by cxne)
    (by rw [Function.update_of_ne (by cxne), Function.update_of_ne (by cxne)]; exact ht 0)
  rw [Function.update_self, Function.update_of_ne (by cxne), Function.update_self,
    List.length_replicate, List.drop_replicate] at h4
  have h5 := lr_uclear body (R := Function.update (Function.update (Function.update F (ι (.tw 2)) (List.replicate d.sT tick)) (ι (.tw 3))
    (List.replicate ((d.hi + 1) * (d.k * d.K) + d.a₀) tick)) (ι (.tw 2))
    (List.replicate (d.sT - ((d.hi + 1) * (d.k * d.K) + d.a₀)) tick)) (ι (.tw 3))
  rw [Function.update_of_ne (by cxne), Function.update_self, List.length_replicate] at h5
  refine lr_weaken body ((((h1.seq h2).seq h3).seq h4).seq h5) ?_ le_rfl
  have hF : Function.update F (ι (.tw 3)) [] = F := by rw [← ht 3, Function.update_eq_self]
  rw [Function.update_comm (by cxne : ι (.tw 2) ≠ ι (.tw 3)), Function.update_idem,
    Function.update_comm (by cxne : ι (.tw 2) ≠ ι (.tw 3)), hF, Function.update_idem]
  congr 2
  simp only [CxData.lens, CxData.sHi, CxData.wy]
  simp only [Fin.isValue, Matrix.cons_val]
  congr 1; ring_nf

omit hin in
/-- A mask stage: `runMask` fills the mask register. -/
lemma cx_mask {s : ℕ} {x : CxReg} (hx : cxStage (.reg x) = s + 1) {nR kR : Fin T}
    {pre item post : List (Fin T × Bool)} {n X : ℕ}
    (hreg : [nR, kR, ι x, ι (.tw 0), ι (.tw 1), ι (.tw 2), ι (.tw 3)].Nodup)
    (hpre : ∀ y ∈ pre ++ post, y.1 ∉ [ι (.tw 0), ι (.tw 1), ι (.tw 2)])
    (hitem : ∀ y ∈ item, y.1 ∉ [kR, ι (.tw 0), ι (.tw 1), ι (.tw 2), ι (.tw 3)])
    (hn : (cxFile ι bank d s R₀ nR).length = n)
    (hX : ∀ q < n, X.testBit q =
      runPat (cxFile ι bank d s R₀) pre (cxFile ι bank d s R₀ kR).length item post q)
    (hc : cxBc A d (.reg x) = binSyms n X) :
    LayRuns body (runMask nR pre kR item post (ι x) (ι (.tw 0)) (ι (.tw 1)) (ι (.tw 2))
      (ι (.tw 3))) (cxFile ι bank d s R₀) (cxFile ι bank d (s + 1) R₀)
      (runMaskCost (cxFile ι bank d s R₀) n (cxFile ι bank d s R₀ kR).length pre item post) := by
  refine cx_stage body hall hx (lr_of_exec_le body fun v S hS => ?_)
  obtain ⟨v', m, hu, hm, he⟩ := runMask_exec body (n := n) (X := X) hreg pre item post hpre hitem
    v S (by rw [hS]; exact hn) (by rw [hS]; exact cx_tw hall h0 0) (by rw [hS]; exact cx_tw hall h0 1)
    (by rw [hS]; exact cx_tw hall h0 2) (by rw [hS]; exact cx_tw hall h0 3) (by rw [hS]; exact hX)
  rw [hS, cx_unset hall h0 (by omega), List.append_nil, ← hc] at he
  rw [hS] at hm
  exact ⟨v', m, hu, hm, he⟩

lemma cxRun28 (hd : d.OK) :
    LayRuns body (cxStageProg ι bank inp d.lo d.hi 28) (cxFile ι bank d 27 R₀)
      (cxFile ι bank d 28 R₀)
      (d.maskCost (d.k * d.K)) := by
  have hK : 0 < d.K := by have := hd.ρK; omega
  have e2 : (cxFile ι bank d 27 R₀ (ι (.sc 2))).length = d.k - 1 := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e5 : (cxFile ι bank d 27 R₀ (ι (.sc 5))).length = 1 := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e6 : (cxFile ι bank d 27 R₀ (ι (.sc 6))).length = d.K - 1 := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e1 : (cxFile ι bank d 27 R₀ (inp 1)).length = d.ρ := by rw [cxFile_inp hall, hin.ρ]
  have eL : (cxFile ι bank d 27 R₀ (inp 11)).length = d.k * d.K := by
    rw [cxFile_inp hall, hin.ell]
  refine lr_weaken body (cx_mask body hall h0 (x := .mSel) (X := selV d.par) (nR := inp 11) (kR := ι (.sc 2)) rfl
    (by
      exact cx_nodup hall [.inr 11, .inl (.reg (.sc 2)), .inl (.reg .mSel),
      .inl (.reg (.tw 0)), .inl (.reg (.tw 1)), .inl (.reg (.tw 2)), .inl (.reg (.tw 3))]
        (by decide))
    (by cxmem) (by cxmem) eL (fun q _ => ?_) ?_) rfl ?_
  · rw [e2, runPat_sel q hK e1 e5 e6, testBit_selV _ hK]; rfl
  · simp only [cxBc]; rw [hd.wy_eq]; rfl
  · rw [e2]
    refine runMaskCost_le (by simp [runsCost, e1])
      (by simp [runsCost, e5, e6]; omega) (by simp [runsCost])

omit hin in
lemma cxRun29 (hd : d.OK) :
    LayRuns body (cxStageProg ι bank inp d.lo d.hi 29) (cxFile ι bank d 28 R₀)
      (cxFile ι bank d 29 R₀)
      (d.maskCost (d.wc)) := by
  have hG := hd.G0
  have hGK := hd.GK
  have e2 : (cxFile ι bank d 28 R₀ (ι (.sc 2))).length = d.k - 1 := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e3 : (cxFile ι bank d 28 R₀ (ι (.sc 3))).length = d.wc := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e5 : (cxFile ι bank d 28 R₀ (ι (.sc 5))).length = 1 := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e7 : (cxFile ι bank d 28 R₀ (ι (.sc 7))).length = d.G - 1 := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  refine lr_weaken body (cx_mask body hall h0 (x := .mC) (X := mCV d.par) (nR := ι (.sc 3)) (kR := ι (.sc 2)) rfl
    (by
      exact cx_nodup hall [.inl (.reg (.sc 3)), .inl (.reg (.sc 2)), .inl (.reg .mC),
      .inl (.reg (.tw 0)), .inl (.reg (.tw 1)), .inl (.reg (.tw 2)), .inl (.reg (.tw 3))]
        (by decide))
    (by simp) (by cxmem) e3 (fun q _ => ?_) ?_) rfl ?_
  · rw [e2, runPat_dig q hG e5 e7, testBit_mCV _ hG]; rfl
  · simp only [cxBc]; rw [CxData.par_wc]
  · rw [e2]
    refine runMaskCost_le (by simp [runsCost])
      (by simp [runsCost, e5, e7]; omega) (by simp [runsCost])

lemma cxRun30 (hd : d.OK) :
    LayRuns body (cxStageProg ι bank inp d.lo d.hi 30) (cxFile ι bank d 29 R₀)
      (cxFile ι bank d 30 R₀)
      (d.maskCost (d.k * d.K)) := by
  have hG := hd.G0
  have hGK : d.G < d.K := by have := hd.GK; omega
  have e2 : (cxFile ι bank d 29 R₀ (ι (.sc 2))).length = d.k - 1 := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e5 : (cxFile ι bank d 29 R₀ (ι (.sc 5))).length = 1 := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e8 : (cxFile ι bank d 29 R₀ (ι (.sc 8))).length = d.K - 1 - d.G := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e1 : (cxFile ι bank d 29 R₀ (inp 1)).length = d.ρ := by rw [cxFile_inp hall, hin.ρ]
  have eG : (cxFile ι bank d 29 R₀ (inp 2)).length = d.G := by rw [cxFile_inp hall, hin.G]
  have eL : (cxFile ι bank d 29 R₀ (inp 11)).length = d.k * d.K := by
    rw [cxFile_inp hall, hin.ell]
  refine lr_weaken body (cx_mask body hall h0 (x := .mA) (X := mAV d.par) (nR := inp 11) (kR := ι (.sc 2)) rfl
    (by
      exact cx_nodup hall [.inr 11, .inl (.reg (.sc 2)), .inl (.reg .mA),
      .inl (.reg (.tw 0)), .inl (.reg (.tw 1)), .inl (.reg (.tw 2)), .inl (.reg (.tw 3))]
        (by decide))
    (by cxmem) (by cxmem) eL (fun q _ => ?_) ?_) rfl ?_
  · rw [e2, runPat_aux q hGK e1 e5 eG e8, testBit_mAV _ hG hGK]; rfl
  · simp only [cxBc]; rw [hd.wy_eq]; rfl
  · rw [e2]
    refine runMaskCost_le (by simp [runsCost, e1])
      (by simp [runsCost, e5, eG, e8]; omega) (by simp [runsCost])

lemma cxRun31 (hd : d.OK) :
    LayRuns body (cxStageProg ι bank inp d.lo d.hi 31) (cxFile ι bank d 30 R₀)
      (cxFile ι bank d 31 R₀)
      (d.maskCost (d.k * d.K)) := by
  have hG := hd.G0
  have hGK := hd.GK
  have e2 : (cxFile ι bank d 30 R₀ (ι (.sc 2))).length = d.k - 1 := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e5 : (cxFile ι bank d 30 R₀ (ι (.sc 5))).length = 1 := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e7 : (cxFile ι bank d 30 R₀ (ι (.sc 7))).length = d.G - 1 := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e9 : (cxFile ι bank d 30 R₀ (ι (.sc 9))).length = d.K - 2 - d.G := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage])]; simp [cxBc, CxData.scv]
  have e1 : (cxFile ι bank d 30 R₀ (inp 1)).length = d.ρ := by rw [cxFile_inp hall, hin.ρ]
  have eL : (cxFile ι bank d 30 R₀ (inp 11)).length = d.k * d.K := by
    rw [cxFile_inp hall, hin.ell]
  refine lr_weaken body (cx_mask body hall h0 (x := .mMk) (X := mkV d.par) (nR := inp 11) (kR := ι (.sc 2)) rfl
    (by
      exact cx_nodup hall [.inr 11, .inl (.reg (.sc 2)), .inl (.reg .mMk),
      .inl (.reg (.tw 0)), .inl (.reg (.tw 1)), .inl (.reg (.tw 2)), .inl (.reg (.tw 3))]
        (by decide))
    (by cxmem) (by cxmem) eL (fun q _ => ?_) ?_) rfl ?_
  · rw [e2, runPat_mk q hG hGK e1 e5 e7 e9, testBit_mkV' _ hG hGK]; rfl
  · simp only [cxBc]; rw [hd.wy_eq]; rfl
  · rw [e2]
    refine runMaskCost_le (by simp [runsCost, e1])
      (by simp [runsCost, e5, e7, e9]; omega) (by simp [runsCost, e5])

omit hin in
/-- The high bits of a header. -/
lemma cx_hdrStart (c : Fin 2) (k : Fin 5) {s : ℕ} (hs : 17 ≤ s)
    (hb : cxFile ι bank d s R₀ (bank c (reg (cxHd k))) = []) :
    LayRuns body (cxHdrStart ι bank c k) (cxFile ι bank d s R₀)
      (Function.update (cxFile ι bank d s R₀) (bank c (reg (cxHd k))) ((d.hbits k).map bitSymbol))
      (6 * (d.hbits k).length + 6) := by
  have ht := cx_tw hall h0 (d := d) (s := s)
  have hreg : ∀ i : Fin 3, [ι (.hb i), bank c (reg (cxHd k)), ι (.tw 0), ι (.tw 1)].Nodup :=
    fun i => by
      exact cx_nodup hall [.inl (.reg (.hb i)), .inl (.hdr c k), .inl (.reg (.tw 0)),
        .inl (.reg (.tw 1))] (by fin_cases i <;> simp)
  have hv : ∀ i : Fin 3, cxFile ι bank d s R₀ (ι (.hb i)) = (sxBits (d.hbv i)).map bitSymbol :=
    fun i => by
      rw [cx_set hall (by fin_cases i <;> simp [cxStage]) (by fin_cases i <;> simp [cxStage] <;> omega)]
      rfl
  have hdup : ∀ i : Fin 3, LayRuns body (sxDupR (ι (.hb i)) (bank c (reg (cxHd k))) (ι (.tw 0))
      (ι (.tw 1))) (cxFile ι bank d s R₀) (Function.update (cxFile ι bank d s R₀)
        (bank c (reg (cxHd k))) ((sxBits (d.hbv i)).map bitSymbol))
      (6 * (sxBits (d.hbv i)).length + 6) := fun i => by
    have h := lr_sxDupR body (R := cxFile ι bank d s R₀) (hreg i) (ht 0) (ht 1)
    rw [hv i, hb, List.append_nil, List.length_map] at h
    exact h
  fin_cases k
  · exact hdup 0
  · have hb' : cxFile ι bank d s R₀ (bank c (reg (cxHd 1))) = [] := hb
    have h := lr_push body (R := cxFile ι bank d s R₀) (bank c (reg (cxHd 1))) (bitSymbol true)
    rw [hb'] at h
    exact lr_weaken body h rfl (by simp [CxData.hbits])
  · exact hdup 1
  · exact hdup 2
  · exact hdup 2

omit hin in
/-- A temporary turned into the low zero bits of a header. -/
lemma cx_bankTemp {s : ℕ} (c : Fin 2) (k : Fin 5) {X : List (Fin (A + 4))} {p : Pr P T Q A U}
    {L n : ℕ} (hp : LayRuns body p
      (Function.update (cxFile ι bank d s R₀) (bank c (reg (cxHd k))) X)
      (Function.update (Function.update (cxFile ι bank d s R₀) (bank c (reg (cxHd k))) X)
        (ι (.tw 2)) (List.replicate L tick)) n) :
    LayRuns body (.seq p (.seq (zeroBits (ι (.tw 2)) (bank c (reg (cxHd k))) (ι (.tw 0)))
      (uclear (ι (.tw 2)))))
      (Function.update (cxFile ι bank d s R₀) (bank c (reg (cxHd k))) X)
      (Function.update (cxFile ι bank d s R₀) (bank c (reg (cxHd k)))
        ((List.replicate L false).map bitSymbol ++ X)) (n + (4 * L + 4 + (2 * L + 2))) := by
  have ht := cx_tw hall h0 (d := d) (s := s)
  refine lr_weaken body (hp.seq ((lr_zeroBits body (by cxne) (by cxne) (by cxne)
    (by rw [Function.update_of_ne (by cxne), Function.update_of_ne (by cxne)]; exact ht 0)).seq
      (lr_uclear body _))) ?_ ?_
  · rw [Function.update_self, Function.update_of_ne (by cxne), Function.update_self,
      List.length_replicate, Function.update_comm (by cxne : ι (.tw 2) ≠ bank c (reg (cxHd k))),
      Function.update_idem, Function.update_comm (by cxne : bank c (reg (cxHd k)) ≠ ι (.tw 2)),
      binSyms_zero_eq, List.map_replicate]
    have hF : Function.update (cxFile ι bank d s R₀) (ι (.tw 2)) [] = cxFile ι bank d s R₀ := by
      rw [← ht 2, Function.update_eq_self]
    rw [Function.update_comm (by cxne : bank c (reg (cxHd k)) ≠ ι (.tw 2)), hF,
      Function.update_idem]
  · rw [Function.update_self, Function.update_of_ne (by cxne), Function.update_self,
      List.length_replicate]

omit hin in
/-- The low zero bits of a header. -/
lemma cx_hdrZeros (hd : d.OK) (c : Fin 2) (k : Fin 5) {s : ℕ} (hs : 17 ≤ s)
    (X : List (Fin (A + 4))) :
    LayRuns body (cxHdrZeros ι bank c k)
      (Function.update (cxFile ι bank d s R₀) (bank c (reg (cxHd k))) X)
      (Function.update (cxFile ι bank d s R₀) (bank c (reg (cxHd k)))
        ((List.replicate (d.he c k) false).map bitSymbol ++ X)) (30 * d.n + 30) := by
  have ht := cx_tw hall h0 (d := d) (s := s)
  have hfr := hd.front
  have e1 : (cxFile ι bank d s R₀ (ι (.sc 1))).length = d.n := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage]; omega)]; simp [cxBc, CxData.scv]
  have e3 : (cxFile ι bank d s R₀ (ι (.sc 3))).length = d.wc := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage]; omega)]; simp [cxBc, CxData.scv]
  have e4 : (cxFile ι bank d s R₀ (ι (.sc 4))).length = d.sT := by
    rw [cx_set hall (by simp [cxStage]) (by simp [cxStage]; omega)]; simp [cxBc, CxData.scv]
  have hG : ∀ x : CxReg, Function.update (cxFile ι bank d s R₀) (bank c (reg (cxHd k))) X (ι x) =
      cxFile ι bank d s R₀ (ι x) := fun x => Function.update_of_ne (cxbank_ι hall c k x).symm _ _
  obtain rfl | rfl : c = 0 ∨ c = 1 := by fin_cases c <;> simp
  all_goals obtain rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 :=
    (by fin_cases k <;> simp)
  · refine lr_weaken body (cx_bankTemp body hall h0 0 0 (((lr_copyTemp body (by cxne) (by cxne)
      (by cxne) (by rw [hG]; exact ht 0) (by rw [hG]; exact ht 2)).seq (lr_subTemp body (by cxne)
      (by cxne) (by cxne) (by rw [hG]; exact ht 0) _)).seq (lr_subTemp body (by cxne) (by cxne)
      (by cxne) (by rw [hG]; exact ht 0) _))) ?_ ?_
    · simp only [hG, e1, e3, e4, CxData.he]; rw [Nat.sub_sub]
    · simp only [hG, e1, e3, e4]; omega
  · refine lr_weaken body (cx_bankTemp body hall h0 0 1 ((lr_copyTemp body (by cxne) (by cxne)
      (by cxne) (by rw [hG]; exact ht 0) (by rw [hG]; exact ht 2)).seq (lr_subTemp body (by cxne)
      (by cxne) (by cxne) (by rw [hG]; exact ht 0) _))) ?_ ?_
    · simp only [hG, e3, e4]; simp [CxData.he]
    · simp only [hG, e3, e4]; omega
  · exact lr_weaken body (lr_skip body _) (by simp [CxData.he]) (by omega)
  · exact lr_weaken body (lr_skip body _) (by simp [CxData.he]) (by omega)
  · exact lr_weaken body (lr_skip body _) (by simp [CxData.he]) (by omega)
  · refine lr_weaken body (cx_bankTemp body hall h0 1 0 ((lr_copyTemp body (by cxne) (by cxne)
      (by cxne) (by rw [hG]; exact ht 0) (by rw [hG]; exact ht 2)).seq (lr_subTemp body (by cxne)
      (by cxne) (by cxne) (by rw [hG]; exact ht 0) _) |>.seq ((lr_subTemp body (by cxne) (by cxne)
      (by cxne) (by rw [hG]; exact ht 0) _).seq (lr_subTemp body (by cxne) (by cxne) (by cxne)
      (by rw [hG]; exact ht 0) _)))) ?_ ?_
    · simp only [hG, e1, e3, e4, CxData.he]; congr 4; omega
    · simp only [hG, e1, e3, e4]; omega
  · have h := lr_zeroBits body (R := Function.update (cxFile ι bank d s R₀) (bank 1 (reg (cxHd 1))) X)
      (len := ι (.sc 4)) (z := bank 1 (reg (cxHd 1))) (t := ι (.tw 0)) (by cxne) (by cxne)
      (by cxne) (by rw [hG]; exact ht 0)
    rw [hG, e4, Function.update_idem, Function.update_self, binSyms_zero_eq] at h
    exact lr_weaken body h (by simp [CxData.he]) (by omega)
  · exact lr_weaken body (lr_skip body _) (by simp [CxData.he]) (by omega)
  · exact lr_weaken body (lr_skip body _) (by simp [CxData.he]) (by omega)
  · exact lr_weaken body (lr_skip body _) (by simp [CxData.he]) (by omega)

omit hin in
/-- Header stage `32 + 5 c + k`. -/
lemma cxRunHdr (hd : d.OK) (lo hi : ℕ) (c : Fin 2) (k : Fin 5) :
    LayRuns body (cxStageProg ι bank inp lo hi (32 + 5 * c + k))
      (cxFile ι bank d (31 + 5 * c + k) R₀) (cxFile ι bank d (32 + 5 * c + k) R₀)
      (6 * (d.hbits k).length + 6 + (30 * d.n + 30 + 1)) := by
  have hp : (cxStageProg ι bank inp lo hi (32 + 5 * c + k) : Pr P T Q A U) =
      cxHdrProg ι bank c k := by
    fin_cases c <;> fin_cases k <;> rfl
  rw [hp]
  have hst : cxStage (.hdr c k) = 31 + 5 * c + k + 1 := by simp [cxStage]; omega
  have hb : cxFile ι bank d (31 + 5 * c + k) R₀ (bank c (reg (cxHd k))) = [] :=
    (cxFile_unset hall (x := .hdr c k) (Or.inl (by rw [hst]; omega))).trans (h0 _ (by simp))
  have h1 := cx_hdrStart body hall h0 c k (s := 31 + 5 * c + k) (by omega) hb
  have h2 := cx_hdrZeros body hall h0 hd c k (s := 31 + 5 * c + k) (by omega)
    ((d.hbits k).map bitSymbol)
  have h3 := lr_push body (R := Function.update (cxFile ι bank d (31 + 5 * c + k) R₀)
    (bank c (reg (cxHd k))) ((List.replicate (d.he c k) false).map bitSymbol ++
      (d.hbits k).map bitSymbol)) (bank c (reg (cxHd k))) separator
  rw [Function.update_self, Function.update_idem] at h3
  rw [show 32 + 5 * (c : ℕ) + k = 31 + 5 * c + k + 1 by omega, ← cxFile_step hall hst]
  refine lr_weaken body (h1.seq (h2.seq h3)) ?_ le_rfl
  simp only [cxSetReg, cxBc, CxData.hs, List.map_append]

/-- **The setup.** -/
theorem cxSetup_exec (hd : d.OK) :
    LayRuns body (cxSetupProg ι bank inp d.lo d.hi) R₀ (cxFile ι bank d 41 R₀)
      (41 * d.setupStep o hB act cr cw + 1) := by
  have h := lr_chain body (fun s => cxFile ι bank d s R₀)
    (fun s => cxStageProg ι bank inp d.lo d.hi (s + 1)) (fun _ => d.setupStep o hB act cr cw) 41 0
    (fun i hi => ?_)
  · simp only [Nat.zero_add, Finset.sum_const, Finset.card_range, smul_eq_mul] at h
    rw [cxFile, stFill_zero (cxSetReg_inj' hall)] at h
    exact h
  simp only [Nat.zero_add]
  unfold CxData.setupStep
  interval_cases i
  · exact lr_weaken body (cxRun1 body hall h0 hin d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun2 body hall h0 hin d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun3 body hall h0 hin hd d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun4 body hall h0 hin d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun5 body hall h0 hin d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun6 body hall h0 d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun7 body hall h0 hin d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun8 body hall h0 hin d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun9 body hall h0 hin d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun10 body hall h0 d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun11 body hall h0 hin d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun12 body hall h0 hin d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun13 body hall h0 d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun14 body hall h0 d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun15 body hall h0 hin d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun16 body hall h0 d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun17 body hall h0 d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun18 body hall h0 d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun19 body hall h0 hin) rfl (by omega)
  · exact lr_weaken body (cxRun20 body hall h0 hin d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun21 body hall h0 hin hd) rfl (by omega)
  · exact lr_weaken body (cxRun22 body hall h0 hin d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun23 body hall h0 hin) rfl (by omega)
  · exact lr_weaken body (cxRun24 body hall h0 d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun25 body hall h0 d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun26 body hall h0 d.lo d.hi) rfl (by omega)
  · exact lr_weaken body (cxRun27 body hall h0) rfl (by omega)
  · exact lr_weaken body (cxRun28 body hall h0 hin hd) rfl (by omega)
  · exact lr_weaken body (cxRun29 body hall h0 hd) rfl (by omega)
  · exact lr_weaken body (cxRun30 body hall h0 hin hd) rfl (by omega)
  · exact lr_weaken body (cxRun31 body hall h0 hin hd) rfl (by omega)
  · exact lr_weaken body (cxRunHdr body hall h0 hd d.lo d.hi 0 0) rfl (by simp only [CxData.hbits]; omega)
  · exact lr_weaken body (cxRunHdr body hall h0 hd d.lo d.hi 0 1) rfl (by simp only [CxData.hbits, List.length_singleton]; omega)
  · exact lr_weaken body (cxRunHdr body hall h0 hd d.lo d.hi 0 2) rfl (by simp only [CxData.hbits]; omega)
  · exact lr_weaken body (cxRunHdr body hall h0 hd d.lo d.hi 0 3) rfl (by simp only [CxData.hbits]; omega)
  · exact lr_weaken body (cxRunHdr body hall h0 hd d.lo d.hi 0 4) rfl (by simp only [CxData.hbits]; omega)
  · exact lr_weaken body (cxRunHdr body hall h0 hd d.lo d.hi 1 0) rfl (by simp only [CxData.hbits]; omega)
  · exact lr_weaken body (cxRunHdr body hall h0 hd d.lo d.hi 1 1) rfl (by simp only [CxData.hbits, List.length_singleton]; omega)
  · exact lr_weaken body (cxRunHdr body hall h0 hd d.lo d.hi 1 2) rfl (by simp only [CxData.hbits]; omega)
  · exact lr_weaken body (cxRunHdr body hall h0 hd d.lo d.hi 1 3) rfl (by simp only [CxData.hbits]; omega)
  · exact lr_weaken body (cxRunHdr body hall h0 hd d.lo d.hi 1 4) rfl (by simp only [CxData.hbits]; omega)

omit hin in
/-- Clearing the register of stage `s + 1`. -/
lemma cx_clear (hd : d.OK) {s : ℕ} (hs : s < 41) :
    LayRuns body (uclear (cxSetReg ι bank (cxOfStage (s + 1)))) (cxFile ι bank d (s + 1) R₀)
      (cxFile ι bank d s R₀) (2 * d.setupStep o hB act cr cw + 2) := by
  obtain ⟨x, hx⟩ : ∃ x, cxOfStage (s + 1) = x := ⟨_, rfl⟩
  rw [hx]
  have hst : cxStage x = s + 1 := hx ▸ cxStage_ofStage _ (by omega) (by omega)
  have hsrc : x ≠ .reg .src := by rintro rfl; simp [cxStage] at hst
  refine lr_weaken body (lr_uclear body _) ?_ ?_
  · rw [← h0 x hsrc]
    exact stFill_unstep (cxSetReg_inj' hall) cxStage_inj _ _ hst
  · rw [cxFile_set hall (by omega) (by omega)]
    have := cxBc_length_le (A := A) hd o hB act cr cw x (by omega)
    omega

omit hin in
/-- **The cleanup.** -/
theorem cxClean_exec (hd : d.OK) :
    LayRuns body (cxCleanProg ι bank) (cxFile ι bank d 41 R₀) R₀
      (41 * (2 * d.setupStep o hB act cr cw + 2) + 1) := by
  have hstep : ∀ i < 41, LayRuns body (uclear (cxSetReg ι bank (cxOfStage (41 - (0 + i)))))
      (cxFile ι bank d (41 - (0 + i)) R₀) (cxFile ι bank d (41 - (0 + i + 1)) R₀)
      (2 * d.setupStep o hB act cr cw + 2) := fun i hi => by
    have := cx_clear body hall h0 (o := o) (hB := hB) (act := act) (cr := cr) (cw := cw) hd
      (s := 40 - i) (by omega)
    rw [show 40 - i + 1 = 41 - (0 + i) by omega, show 40 - i = 41 - (0 + i + 1) by omega] at this
    exact this
  have h := lr_chain body (fun j => cxFile ι bank d (41 - j) R₀)
    (fun j => uclear (cxSetReg ι bank (cxOfStage (41 - j))))
    (fun _ => 2 * d.setupStep o hB act cr cw + 2) 41 0 hstep
  simp only [Nat.zero_add, Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.sub_self,
    Nat.sub_zero] at h
  rwa [show cxFile ι bank d 0 R₀ = R₀ from stFill_zero (cxSetReg_inj' hall) _ _] at h

end Runs

end IntegerMultBounds.MathlibTM2.Node
