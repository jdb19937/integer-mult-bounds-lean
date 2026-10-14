module

public import IntegerMultBounds.Schoenhage.TransformGen
public import IntegerMultBounds.Schoenhage.TwistConstsTape

/-! The header generators of the transform programs (§6), assembled: decode the header
(`runs_decodeParams` on the ring product's bank inside the word bank), write the round script and
the layout script (`ScriptGen`, `LayoutGen`), write the twist block's constants and the record width
(`TwistConsts.runs_constGen`), clear the decoded parameters. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Spec.SignedRingProduct Resampling AxisDriver LayoutMachines TwistDescriptors

theorem bits_zero_eq : ∀ n : ℕ, bits n 0 = List.replicate n false
  | 0 => rfl
  | n + 1 => by simp [bits, bits_zero_eq n, List.replicate_succ]

/-- On the paper's axis lengths the flag sum is the address length. -/
theorem flagSum_lengthFlags {r : ℕ} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) :
    TwistConsts.flagSum (ℓ - 1) (TransformParams.lengthFlags ℓ ts) = Nat.log 2 ts.prod := by
  have hℓ : 1 ≤ ℓ := hL.2.2.2
  have hts : ∀ t ∈ ts, t = 2 ^ (ℓ - 1) ∨ t = 2 ^ ℓ := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨a, ha, -⟩ := hL.1 _ ht
    have hax : axLen ts i = a := by
      simp only [axLen, List.getD_eq_getElem _ _ hi, ha, Nat.log_pow (by norm_num : 1 < 2)]
    rw [ha]
    rcases hL.2.1 i hi with h | h <;> rw [hax] at h <;> simp [h]
  rw [TransformParams.flags_paper hℓ hts, log_prod_eq_sum hL.1]
  simp only [TwistConsts.flagSum, SigmaConstsTape.paperFlags, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rcases hL.2.1 i hi with h | h <;> simp [h] <;> omega

variable {tL nL : ℕ}

/-! ### The word bank by parts -/

/-- The word bank: paper tapes `S0`, named tapes `v`, the twist block `tw`, the ring product's bank
`dec` on drivers' tapes `50 + x` (its header tape is paper tape 0), every other tape empty. -/
def wbank (S0 : Fin 4 → WTape) (dec : Fin 𝕌 → WTape) (v : Fin 13 → WTape) (tw : Fin 29 → WTape) :
    Fin (4 + DB tL nL) → WTape :=
  wst S0 fun x => if h : x.val < 13 then v ⟨x.val, h⟩
    else if h' : 20 ≤ x.val ∧ x.val < 49 then tw ⟨x.val - 20, by omega⟩
    else if h'' : 50 ≤ x.val ∧ x.val < 141 ∧ x.val ≠ 137 then dec ⟨x.val - 50, by change _ < 91; omega⟩ else emp

theorem gslot_val (x : Fin 𝕌) : (gslot tL nL x).val = if x = zH then 0 else 54 + x.val := by
  unfold gslot; split_ifs <;> simp [pt, drv]; omega

theorem wbank_gslot (S0 : Fin 4 → WTape) (dec : Fin 𝕌 → WTape) (v : Fin 13 → WTape) (tw : Fin 29 → WTape)
    {x : Fin 𝕌} (hx : x ≠ zH) : wbank (tL := tL) (nL := nL) S0 dec v tw (gslot tL nL x) = dec x := by
  have h := x.isLt; change x.val < 91 at h
  have hx' : x.val ≠ 87 := fun e => hx (Fin.ext e)
  simp only [gslot, hx, if_false, wbank, wst_drv]
  rw [dif_neg (by simp; omega), dif_neg (by simp; omega), dif_pos (by simp; omega)]
  congr 1; ext; simp

theorem wbank_nm (S0 : Fin 4 → WTape) (dec : Fin 𝕌 → WTape) (v : Fin 13 → WTape) (tw : Fin 29 → WTape)
    (i : Fin 13) : wbank (tL := tL) (nL := nL) S0 dec v tw (drv tL nL (nm tL nL i)) = v i := by
  simp [wbank, wst_drv, nm]

theorem wbank_twT (S0 : Fin 4 → WTape) (dec : Fin 𝕌 → WTape) (v : Fin 13 → WTape) (tw : Fin 29 → WTape)
    (j : Fin 29) : wbank (tL := tL) (nL := nL) S0 dec v tw (drv tL nL (twT tL nL j)) = tw j := by
  have := j.isLt
  simp only [wbank, wst_drv, twT]
  rw [dif_neg (by simp; omega), dif_pos (by simp; omega)]
  congr 1; ext; simp

theorem wbank_pt (S0 : Fin 4 → WTape) (dec : Fin 𝕌 → WTape) (v : Fin 13 → WTape) (tw : Fin 29 → WTape)
    (i : Fin 4) : wbank (tL := tL) (nL := nL) S0 dec v tw (pt tL nL i) = S0 i := by
  simp [wbank, wst_pt]

/-- With the ring product's bank cleared, the word bank is the drivers' bank behind the paper tapes. -/
theorem wbank_dstate (S0 : Fin 4 → WTape) (dec : Fin 𝕌 → WTape) (v : Fin 13 → WTape) (tw : Fin 29 → WTape)
    (hdec : ∀ x, x ≠ zH → dec x = emp) :
    wbank (tL := tL) (nL := nL) S0 dec v tw = wst S0 (dstate tL nL v tw) := by
  unfold wbank
  congr 1
  funext x
  simp only [dstate]
  split_ifs with h1 h2 h3 <;> try rfl
  apply hdec
  intro e
  have := congrArg Fin.val e
  simp at this
  omega

theorem castAdd_ne_drv (k : Fin 4) (x : Fin (DB tL nL)) : (Fin.castAdd (DB tL nL) k : Fin (4 + DB tL nL)) ≠ drv tL nL x :=
  pt_ne_drv k x

theorem update_wbank_nm (S0 : Fin 4 → WTape) (dec : Fin 𝕌 → WTape) (v : Fin 13 → WTape) (tw : Fin 29 → WTape)
    (i : Fin 13) (u : WTape) :
    Function.update (wbank (tL := tL) (nL := nL) S0 dec v tw) (drv tL nL (nm tL nL i)) u =
      wbank S0 dec (Function.update v i u) tw := by
  funext y
  refine Fin.addCases (fun k => ?_) (fun x => ?_) y
  · rw [Function.update_of_ne (castAdd_ne_drv k _)]; simp [wbank, wst]
  · by_cases hx : x = nm tL nL i
    · subst hx
      rw [show (Fin.natAdd 4 (nm tL nL i) : Fin (4 + DB tL nL)) = drv tL nL (nm tL nL i) from rfl,
        Function.update_self, wbank_nm, Function.update_self]
    · rw [Function.update_of_ne (show (Fin.natAdd 4 x : Fin (4 + DB tL nL)) ≠ drv tL nL (nm tL nL i) from
        fun e => hx (drv_injective e))]
      simp only [wbank, wst, Fin.addCases_right]
      split_ifs with h1 <;> first | rfl |
        rw [Function.update_of_ne (fun e => hx (by rw [← e]; exact Fin.ext rfl))]

theorem update_wbank_twT (S0 : Fin 4 → WTape) (dec : Fin 𝕌 → WTape) (v : Fin 13 → WTape) (tw : Fin 29 → WTape)
    (j : Fin 29) (u : WTape) :
    Function.update (wbank (tL := tL) (nL := nL) S0 dec v tw) (drv tL nL (twT tL nL j)) u =
      wbank S0 dec v (Function.update tw j u) := by
  funext y
  refine Fin.addCases (fun k => ?_) (fun x => ?_) y
  · rw [Function.update_of_ne (castAdd_ne_drv k _)]; simp [wbank, wst]
  · by_cases hx : x = twT tL nL j
    · subst hx
      rw [show (Fin.natAdd 4 (twT tL nL j) : Fin (4 + DB tL nL)) = drv tL nL (twT tL nL j) from rfl,
        Function.update_self, wbank_twT, Function.update_self]
    · rw [Function.update_of_ne (show (Fin.natAdd 4 x : Fin (4 + DB tL nL)) ≠ drv tL nL (twT tL nL j) from
        fun e => hx (drv_injective e))]
      simp only [wbank, wst, Fin.addCases_right]
      split_ifs with h1 h2 <;> first | rfl |
        rw [Function.update_of_ne (fun e => hx (by
          apply Fin.ext; have := congrArg Fin.val e; simp [twT] at this ⊢; omega))]

theorem update_wbank_gslot (S0 : Fin 4 → WTape) (dec : Fin 𝕌 → WTape) (v : Fin 13 → WTape) (tw : Fin 29 → WTape)
    {x : Fin 𝕌} (hx : x ≠ zH) (u : WTape) :
    Function.update (wbank (tL := tL) (nL := nL) S0 dec v tw) (gslot tL nL x) u =
      wbank S0 (Function.update dec x u) v tw := by
  have hxl := x.isLt; change x.val < 91 at hxl
  have hx' : x.val ≠ 87 := fun e => hx (Fin.ext e)
  have hg : gslot tL nL x = drv tL nL ⟨50 + x.val, by unfold DB; omega⟩ := by simp [gslot, hx]
  rw [hg]
  funext y
  refine Fin.addCases (fun k => ?_) (fun z => ?_) y
  · rw [Function.update_of_ne (castAdd_ne_drv k _)]; simp [wbank, wst]
  · by_cases hz : z = ⟨50 + x.val, by unfold DB; omega⟩
    · subst hz
      simp only [Function.update_self, wbank, wst, drv, Fin.addCases_right]
      rw [dif_neg (by simp; omega), dif_neg (by simp; omega), dif_pos (by simp; omega)]
      rw [show (⟨50 + x.val - 50, _⟩ : Fin 𝕌) = x from Fin.ext (by simp)]; simp
    · rw [Function.update_of_ne (show (Fin.natAdd 4 z : Fin (4 + DB tL nL)) ≠ drv tL nL _ from
        fun e => hz (drv_injective e))]
      simp only [wbank, wst, Fin.addCases_right]
      split_ifs with h1 h2 h3 <;> first | rfl |
        rw [Function.update_of_ne (fun e => hz (by
          apply Fin.ext; have := congrArg Fin.val e; simp at this ⊢; omega))]

/-! ### Decoding the header -/

theorem wb_cases {n : ℕ} (y : Fin (4 + n)) : (∃ k, y = Fin.castAdd n k) ∨ ∃ z, y = Fin.natAdd 4 z :=
  Fin.addCases (motive := fun y => (∃ k, y = Fin.castAdd n k) ∨ ∃ z, y = Fin.natAdd 4 z)
    (fun k => Or.inl ⟨k, rfl⟩) (fun z => Or.inr ⟨z, rfl⟩) y

theorem decoded_zH (p d l K w : ℕ) (ts : List ℕ) :
    decoded p d l K w ts zH = reg (transformHeader p d (2 ^ l) K w ts) := by
  simp (config := {decide := true}) [decoded, decStart, Function.update_apply]

/-- After decoding, the word bank by parts. -/
theorem decState_eq (p d l K w : ℕ) (ts : List ℕ) (F : List Bool) :
    decState (tL := tL) (nL := nL) p d l K w ts F =
      wbank ![reg (transformHeader p d (2 ^ l) K w ts), reg F, emp, emp] (decoded p d l K w ts)
        (fun _ => emp) (fun _ => emp) := by
  unfold decState
  apply upd_eq_of _ gslot_injective
  · intro x
    by_cases hx : x = zH
    · subst hx
      rw [show gslot tL nL zH = pt tL nL 0 by simp [gslot], wbank_pt, decoded_zH]; rfl
    · exact wbank_gslot _ _ _ _ hx
  · intro y hy
    rcases wb_cases y with ⟨k, rfl⟩ | ⟨z, rfl⟩
    · simp [wbank, wst]
    · have hz := hy
      simp only [wbank, wst, Fin.addCases_right]
      split_ifs with h1 h2 h3 <;> try rfl
      exfalso
      have hz' : z.val - 50 < 91 := by omega
      have hne : (⟨z.val - 50, hz'⟩ : Fin 𝕌) ≠ zH := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      apply hz ⟨z.val - 50, hz'⟩
      simp only [gslot, hne, if_false, drv]
      apply Fin.ext; simp; omega

/-- The header decoder on the ring product's bank inside the word bank. -/
noncomputable def decStep (A tL nL : ℕ) : Cmd A (4 + DB tL nL) :=
  .prim (Prim.liftE (Nat.zero_le A) (Prim.ofHoare (compile (a := 0) (by decide) TransformParams.decodeParams).2
    (by decide))) (gslot tL nL) gslot_injective

theorem runs_decStep {A : ℕ} {p d l K w : ℕ} {ts : List ℕ} (hp : 1 ≤ p) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : 1 ≤ w)
    (hts : ∀ t ∈ ts, 1 ≤ t) (hD : ts.length = d - 1) (F : List Bool) :
    Runs (decStep A tL nL) (wst ![reg (transformHeader p d (2 ^ l) K w ts), reg F, emp, emp] (fun _ => emp))
      (· = decState p d l K w ts F)
      (TransformParams.paramsCost p d (2 ^ l) K w (transformHeader p d (2 ^ l) K w ts).length ts.length l) := by
  set hdr := transformHeader p d (2 ^ l) K w ts
  have hcomp : wst ![reg hdr, reg F, emp, emp] (fun _ => emp) ∘ gslot tL nL = decStart hdr := by
    funext x
    simp only [Function.comp_apply, decStart]
    by_cases hx : x = zH
    · subst hx; simp [gslot, wst_pt]
    · simp [gslot, hx, wst_drv]
  have hz : ∀ x : Fin 𝕌, 64 ≤ x.val → x ≠ zH → decStart hdr x = emp := fun x _ hx => by simp [decStart, hx]
  have hcl : Clean (decStart hdr) := by
    funext i
    have hi := i.isLt; change i.val < 64 at hi
    have : ι i ≠ zH := fun e => by have := congrArg Fin.val e; simp at this; omega
    simp [decStart, this]
  obtain ⟨τ', k, hx, hq, hk⟩ := TransformParams.runs_decodeParams (l := l) hp hd hK hw hts hD (decStart hdr) hcl
    (by simp [decStart, hdr]) (by simp (config := {decide := true}) [decStart])
    (by simp (config := {decide := true}) [decStart]) (by simp (config := {decide := true}) [decStart])
    (by simp (config := {decide := true}) [decStart]) (by simp (config := {decide := true}) [decStart])
    (by simp (config := {decide := true}) [decStart]) (by simp (config := {decide := true}) [decStart])
    (by simp (config := {decide := true}) [decStart])
  subst hq
  have hT : HoareTo (compile (a := 0) (by decide) TransformParams.decodeParams).2
      (wst ![reg hdr, reg F, emp, emp] (fun _ => emp) ∘ gslot tL nL) (decoded p d l K w ts) k := by
    rw [hcomp]
    exact (compile_correct (by decide) hx).consequence (fun _ h => h) (fun _ h => h) le_rfl
  exact (runs_ofHoare_liftE (Nat.zero_le A) _ (by decide) gslot_injective hT).mono (fun _ h => h) hk

/-! ### The constants -/

/-- Where the constants program's tapes sit in the word bank. -/
def cvals : Fin 16 → ℕ := ![139, 140, 130, 6, 27, 39, 41, 46, 47, 48, 49, 17, 18, 19, 20, 21]

theorem cvals_lt (i : Fin 16) : cvals i < 141 := by fin_cases i <;> decide

/-- The constants program's tapes in the word bank. -/
def cslot (tL nL : ℕ) (i : Fin 16) : Fin (4 + DB tL nL) := ⟨cvals i, by have := cvals_lt i; unfold DB; omega⟩

theorem cvals_injective : Function.Injective cvals := by decide

theorem cslot_injective : Function.Injective (cslot tL nL) := fun i j h =>
  cvals_injective (congrArg Fin.val h)

theorem cslot_cL : cslot tL nL TwistConsts.cL = gslot tL nL iL := Fin.ext (by rw [gslot_val]; rfl)
theorem cslot_cW : cslot tL nL TwistConsts.cW = gslot tL nL iW := Fin.ext (by rw [gslot_val]; rfl)
theorem cslot_cF : cslot tL nL TwistConsts.cF = gslot tL nL xA := Fin.ext (by rw [gslot_val]; rfl)
theorem cslot_oW : cslot tL nL TwistConsts.oW = drv tL nL (nm tL nL 2) := Fin.ext rfl
theorem cslot_o3 : cslot tL nL TwistConsts.o3 = drv tL nL (twT tL nL 3) := Fin.ext rfl
theorem cslot_o15 : cslot tL nL TwistConsts.o15 = drv tL nL (twT tL nL 15) := Fin.ext rfl
theorem cslot_o17 : cslot tL nL TwistConsts.o17 = drv tL nL (twT tL nL 17) := Fin.ext rfl
theorem cslot_o22 : cslot tL nL TwistConsts.o22 = drv tL nL (twT tL nL 22) := Fin.ext rfl
theorem cslot_o23 : cslot tL nL TwistConsts.o23 = drv tL nL (twT tL nL 23) := Fin.ext rfl
theorem cslot_o24 : cslot tL nL TwistConsts.o24 = drv tL nL (twT tL nL 24) := Fin.ext rfl
theorem cslot_o25 : cslot tL nL TwistConsts.o25 = drv tL nL (twT tL nL 25) := Fin.ext rfl

theorem cslot_scratch (i : Fin 16) (h : 11 ≤ i.val) :
    cslot tL nL i = drv tL nL ⟨cvals i - 4, by have := cvals_lt i; unfold DB; omega⟩ := by
  apply Fin.ext
  have : 4 ≤ cvals i := by fin_cases i <;> simp at h <;> decide
  simp [cslot, drv]; omega

theorem wbank_scratch (S0 : Fin 4 → WTape) (dec : Fin 𝕌 → WTape) (v : Fin 13 → WTape) (tw : Fin 29 → WTape)
    (i : Fin 16) (h : 11 ≤ i.val) : wbank (tL := tL) (nL := nL) S0 dec v tw (cslot tL nL i) = emp := by
  rw [cslot_scratch i h]
  have h1 : 17 ≤ cvals i ∧ cvals i ≤ 21 := by fin_cases i <;> simp at h <;> decide
  simp only [wbank, wst_drv]
  rw [dif_neg (by simp; omega), dif_neg (by simp; omega), dif_neg (by simp; omega)]

/-- The constants program on the word bank. -/
noncomputable def constStep (A tL nL : ℕ) : Cmd A (4 + DB tL nL) :=
  .prim (Prim.liftE (Nat.zero_le A) (Prim.ofHoare (compile (a := 0) (by decide) TwistConsts.constGen).2
    (by decide))) (cslot tL nL) cslot_injective

theorem runs_constStep {A : ℕ} (S0 : Fin 4 → WTape) (dec : Fin 𝕌 → WTape) (v : Fin 13 → WTape)
    (tw : Fin 29 → WTape) (l w : ℕ) (fl : List Bool) (hL : dec iL = reg (ones l)) (hW : dec iW = reg (ones w))
    (hF : dec xA = ⟨(fl.map fun b => [b]).reverse, []⟩) (h2 : v 2 = emp) (t3 : tw 3 = emp) (t15 : tw 15 = emp)
    (t17 : tw 17 = emp) (t22 : tw 22 = emp) (t23 : tw 23 = emp) (t24 : tw 24 = emp) (t25 : tw 25 = emp) :
    Runs (constStep A tL nL) (wbank S0 dec v tw)
      (· = wbank S0 dec (Function.update v 2 (reg (ones w)))
        (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update tw 3 (reg (ones (2 * 2 ^ l)))) 15 (reg (List.replicate (TwistConsts.flagSum (l - 1) fl) false)))
          17 ⟨[], List.replicate (2 ^ TwistConsts.flagSum (l - 1) fl) []⟩) 22 (reg (ones (4 * 2 ^ l - 1))))
          23 (reg (ones (4 * 2 ^ l)))) 24 (reg (ones (2 * 2 ^ l - 1)))) 25 (reg (ones (2 * 2 ^ l)))))
      (TwistConsts.constCost l w fl) := by
  have hcomp : wbank (tL := tL) (nL := nL) S0 dec v tw ∘ cslot tL nL = TwistConsts.cIn l w fl := by
    funext i
    simp only [Function.comp_apply]
    by_cases hs : 11 ≤ i.val
    · rw [wbank_scratch _ _ _ _ i hs]
      fin_cases i <;> simp at hs <;> simp (config := {decide := true}) [TwistConsts.cIn]
    · fin_cases i <;> simp at hs
      · show wbank S0 dec v tw (cslot tL nL TwistConsts.cL) = TwistConsts.cIn l w fl TwistConsts.cL
        rw [cslot_cL, wbank_gslot _ _ _ _ (by decide), hL]; rfl
      · show wbank S0 dec v tw (cslot tL nL TwistConsts.cW) = TwistConsts.cIn l w fl TwistConsts.cW
        rw [cslot_cW, wbank_gslot _ _ _ _ (by decide), hW]; rfl
      · show wbank S0 dec v tw (cslot tL nL TwistConsts.cF) = TwistConsts.cIn l w fl TwistConsts.cF
        rw [cslot_cF, wbank_gslot _ _ _ _ (by decide), hF]; rfl
      · show wbank S0 dec v tw (cslot tL nL TwistConsts.oW) = TwistConsts.cIn l w fl TwistConsts.oW
        rw [cslot_oW, wbank_nm, h2]; rfl
      · show wbank S0 dec v tw (cslot tL nL TwistConsts.o3) = TwistConsts.cIn l w fl TwistConsts.o3
        rw [cslot_o3, wbank_twT, t3]; rfl
      · show wbank S0 dec v tw (cslot tL nL TwistConsts.o15) = TwistConsts.cIn l w fl TwistConsts.o15
        rw [cslot_o15, wbank_twT, t15]; rfl
      · show wbank S0 dec v tw (cslot tL nL TwistConsts.o17) = TwistConsts.cIn l w fl TwistConsts.o17
        rw [cslot_o17, wbank_twT, t17]; rfl
      · show wbank S0 dec v tw (cslot tL nL TwistConsts.o22) = TwistConsts.cIn l w fl TwistConsts.o22
        rw [cslot_o22, wbank_twT, t22]; rfl
      · show wbank S0 dec v tw (cslot tL nL TwistConsts.o23) = TwistConsts.cIn l w fl TwistConsts.o23
        rw [cslot_o23, wbank_twT, t23]; rfl
      · show wbank S0 dec v tw (cslot tL nL TwistConsts.o24) = TwistConsts.cIn l w fl TwistConsts.o24
        rw [cslot_o24, wbank_twT, t24]; rfl
      · show wbank S0 dec v tw (cslot tL nL TwistConsts.o25) = TwistConsts.cIn l w fl TwistConsts.o25
        rw [cslot_o25, wbank_twT, t25]; rfl
  obtain ⟨τ', k, hx, hq, hk⟩ := TwistConsts.runs_constGen l w fl
  subst hq
  have hT : HoareTo (compile (a := 0) (by decide) TwistConsts.constGen).2
      (wbank (tL := tL) (nL := nL) S0 dec v tw ∘ cslot tL nL)
      (TwistConsts.cOut l w fl) k := by
    rw [hcomp]
    exact (compile_correct (by decide) hx).consequence (fun _ h => h) (fun _ h => h) le_rfl
  refine (runs_ofHoare_liftE (Nat.zero_le A) _ (by decide) cslot_injective hT).mono (fun τ e => ?_) hk
  rw [e, ← update_wbank_nm, ← update_wbank_twT, ← update_wbank_twT, ← update_wbank_twT, ← update_wbank_twT,
    ← update_wbank_twT, ← update_wbank_twT, ← update_wbank_twT, ← cslot_oW, ← cslot_o3, ← cslot_o15, ← cslot_o17,
    ← cslot_o22, ← cslot_o23, ← cslot_o24, ← cslot_o25]
  apply upd_eq_of _ cslot_injective
  · intro i
    have hi := congrFun hcomp i
    simp only [Function.comp_apply] at hi
    simp only [Function.update_apply, cslot_injective.eq_iff]
    fin_cases i <;> simp (config := {decide := true}) [TwistConsts.cOut, TwistConsts.cIn] at hi ⊢ <;> exact hi
  · intro y hy
    have hy' : ∀ i, (y = cslot tL nL i) ↔ False := fun i => ⟨fun e => hy i e.symm, False.elim⟩
    simp only [Function.update_apply, hy', if_false]

/-! ### The generators -/

/-- Clear the decoded parameters. -/
noncomputable def cleanDec (A tL nL : ℕ) : Cmd A (4 + DB tL nL) :=
  .seq (clear (gslot tL nL iP)) <| .seq (clear (gslot tL nL kN)) <| .seq (clear (gslot tL nL iL)) <|
  .seq (clear (gslot tL nL kI)) <| .seq (clear (gslot tL nL iW)) <| .seq (clear (gslot tL nL xB))
    (clear (gslot tL nL xA))

/-- A header generator from a round-script writer `sg` and a layout-script writer `lg`. -/
noncomputable def genCmd {A : ℕ} (sg lg : Cmd A (4 + DB tL nL)) : Cmd A (4 + DB tL nL) :=
  .seq (decStep A tL nL) <| .seq sg <| .seq lg <| .seq (constStep A tL nL) (cleanDec A tL nL)

/-- The generator's steps beyond the two script writers. -/
noncomputable def genCost (p d l K w : ℕ) (ts : List ℕ) : ℕ :=
  TransformParams.paramsCost p d (2 ^ l) K w (transformHeader p d (2 ^ l) K w ts).length ts.length l +
    TwistConsts.constCost l w (TransformParams.lengthFlags l ts) + 2 * (p + d + l + K + w + 3 * ts.length) + 60

set_option maxHeartbeats 8000000 in
theorem runs_genCmd {A : ℕ} (sg lg : Cmd A (4 + DB tL nL)) {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K)
    {p d w Bs Bl : ℕ} (hp : 1 ≤ p) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : 1 ≤ w) (hD : ts.length = d - 1) (fwd : Bool)
    (hsg : ScriptGen fwd sg hL p d w Bs) (hlg : LayoutGen fwd lg ℓ K ts p d w Bl) (F : List Bool) :
    Runs (genCmd sg lg) (wst ![reg (transformHeader p d (2 ^ ℓ) K w ts), reg F, emp, emp] (fun _ => emp))
      (· = wst ![reg (transformHeader p d (2 ^ ℓ) K w ts), reg F, emp, emp]
        (dstate tL nL (Function.update (rnamed w []
          ⟨[], if fwd then fwdScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K else oppScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K⟩
          ⟨[], if fwd then layoutWords (2 ^ ℓ) w ts ℓ K else undoWords (2 ^ ℓ) w ts ℓ K⟩) 0 emp) (rest (2 ^ ℓ) ts)))
      (genCost p d ℓ K w ts + Bs + Bl) := by
  have hts : ∀ t ∈ ts, 1 ≤ t := fun t ht => by
    obtain ⟨a, rfl, -⟩ := hL.1 t ht; exact Nat.one_le_two_pow
  set S0 : Fin 4 → WTape := ![reg (transformHeader p d (2 ^ ℓ) K w ts), reg F, emp, emp]
  set S6 : WTape := ⟨[], if fwd then fwdScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K
    else oppScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K⟩
  set S7 : WTape := ⟨[], if fwd then layoutWords (2 ^ ℓ) w ts ℓ K else undoWords (2 ^ ℓ) w ts ℓ K⟩
  set fl := TransformParams.lengthFlags ℓ ts
  have s1 := runs_decStep (A := A) (tL := tL) (nL := nL) (l := ℓ) hp hd hK hw hts hD F
  have s2 := hsg F
  have s3 := hlg F S6
  rw [decState_eq, update_wbank_nm, update_wbank_nm] at s3
  rw [decState_eq] at s1 s2
  rw [update_wbank_nm] at s2
  set dec := decoded p d ℓ K w ts
  set v3 := Function.update (Function.update (fun _ : Fin 13 => emp) 6 S6) 7 S7
  have s4 := runs_constStep (A := A) (tL := tL) (nL := nL) S0 dec v3 (fun _ => emp) ℓ w fl
    (by simp (config := {decide := true}) [dec, decoded, Function.update_apply])
    (by simp (config := {decide := true}) [dec, decoded, Function.update_apply])
    (by simp (config := {decide := true}) [dec, decoded, Function.update_apply, fl])
    (by simp (config := {decide := true}) [v3]) rfl rfl rfl rfl rfl rfl rfl
  set v4 := Function.update v3 2 (reg (ones w))
  set tw4 := Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _ : Fin 29 => emp) 3 (reg (ones (2 * 2 ^ ℓ))))
    15 (reg (List.replicate (TwistConsts.flagSum (ℓ - 1) fl) false)))
    17 ⟨[], List.replicate (2 ^ TwistConsts.flagSum (ℓ - 1) fl) []⟩) 22 (reg (ones (4 * 2 ^ ℓ - 1))))
    23 (reg (ones (4 * 2 ^ ℓ)))) 24 (reg (ones (2 * 2 ^ ℓ - 1)))) 25 (reg (ones (2 * 2 ^ ℓ)))
  have c1 := runs_clear (a := A) (gslot tL nL iP) (wbank S0 dec v4 tw4)
  rw [update_wbank_gslot _ _ _ _ (by decide)] at c1
  have c2 := runs_clear (a := A) (gslot tL nL kN) (wbank S0 (Function.update dec iP ⟨[], []⟩) v4 tw4)
  rw [update_wbank_gslot _ _ _ _ (by decide)] at c2
  set d2 := Function.update (Function.update dec iP ⟨[], []⟩) kN ⟨[], []⟩
  have c3 := runs_clear (a := A) (gslot tL nL iL) (wbank S0 d2 v4 tw4)
  rw [update_wbank_gslot _ _ _ _ (by decide)] at c3
  have c4 := runs_clear (a := A) (gslot tL nL kI) (wbank S0 (Function.update d2 iL ⟨[], []⟩) v4 tw4)
  rw [update_wbank_gslot _ _ _ _ (by decide)] at c4
  set d4 := Function.update (Function.update d2 iL ⟨[], []⟩) kI ⟨[], []⟩
  have c5 := runs_clear (a := A) (gslot tL nL iW) (wbank S0 d4 v4 tw4)
  rw [update_wbank_gslot _ _ _ _ (by decide)] at c5
  have c6 := runs_clear (a := A) (gslot tL nL xB) (wbank S0 (Function.update d4 iW ⟨[], []⟩) v4 tw4)
  rw [update_wbank_gslot _ _ _ _ (by decide)] at c6
  set d6 := Function.update (Function.update d4 iW ⟨[], []⟩) xB ⟨[], []⟩
  have c7 := runs_clear (a := A) (gslot tL nL xA) (wbank S0 d6 v4 tw4)
  rw [update_wbank_gslot _ _ _ _ (by decide)] at c7
  have hd7 : ∀ x, x ≠ zH → Function.update d6 xA ⟨[], []⟩ x = emp := by
    intro x hx
    simp only [d6, d4, d2, dec, decoded, decStart, Function.update_apply]
    split_ifs <;> first | rfl | (exfalso; tauto)
  rw [wbank_dstate _ _ _ _ hd7] at c7
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then c1 (Runs.then c2 (Runs.then c3
    (Runs.then c4 (Runs.then c5 (Runs.then c6 c7)))))))))).mono (fun τ e => ?_) ?_
  · rw [e]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp (config := {decide := true}) [v4, v3, rnamed, Function.update_apply, S6, S7]
    · have hn := flagSum_lengthFlags hL
      funext j; fin_cases j <;> simp (config := {decide := true}) [tw4, twRest, Function.update_apply, fl, hn,
        bits_zero_eq]
  · simp only [wbank_gslot _ _ _ _ (show iP ≠ zH by decide), wbank_gslot _ _ _ _ (show kN ≠ zH by decide),
      wbank_gslot _ _ _ _ (show iL ≠ zH by decide), wbank_gslot _ _ _ _ (show kI ≠ zH by decide),
      wbank_gslot _ _ _ _ (show iW ≠ zH by decide), wbank_gslot _ _ _ _ (show xB ≠ zH by decide),
      wbank_gslot _ _ _ _ (show xA ≠ zH by decide)]
    simp (config := {decide := true}) only [d6, d4, d2, dec, decoded, Function.update_apply, if_true, if_false,
      WTape.words, reg, List.reverse_nil, List.nil_append, List.append_nil, clen_cons, clen_nil, length_ones,
      List.reverse_replicate, TwistConsts.clen_ticks, genCost]
    have hf : clen ((fl.map fun b => [b]).reverse.reverse) = 2 * ts.length := by
      rw [clen_reverse, TwistConsts.clen_flags]; simp [fl, TransformParams.lengthFlags]
    simp only [fl] at hf ⊢
    rw [hf]
    omega

/-- `fwdGen_of`: the generator meets the forward driver's interface, given the two script writers. -/
theorem fwdGen_of {A : ℕ} {sg lg : Cmd A (4 + DB tL NL)} {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K)
    {p d w Bs Bl : ℕ} (hp : 1 ≤ p) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : 1 ≤ w) (hD : ts.length = d - 1)
    (hsg : ScriptGen true sg hL p d w Bs) (hlg : LayoutGen true lg ℓ K ts p d w Bl) :
    FwdGen (genCmd sg lg) hL p d w (genCost p d ℓ K w ts + Bs + Bl) := fun F => by
  have := runs_genCmd sg lg hL hp hd hK hw hD true hsg hlg F
  simpa only [if_true, fwdGenOut] using this

/-- `oppGen_of`: the generator meets the opposite driver's interface, given the two script writers. -/
theorem oppGen_of {A : ℕ} {sg lg : Cmd A (4 + DB tL NL)} {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K)
    {p d w Bs Bl : ℕ} (hp : 1 ≤ p) (hd : 1 ≤ d) (hK : 1 ≤ K) (hw : 1 ≤ w) (hD : ts.length = d - 1)
    (hsg : ScriptGen false sg hL p d w Bs) (hlg : LayoutGen false lg ℓ K ts p d w Bl) :
    OppGen (genCmd sg lg) hL p d w (genCost p d ℓ K w ts + Bs + Bl) := fun F => by
  have := runs_genCmd sg lg hL hp hd hK hw hD false hsg hlg F
  simpa only [Bool.false_eq_true, if_false, oppGenOut] using this

end IntegerMultBounds.Schoenhage
