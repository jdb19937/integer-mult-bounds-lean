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

end IntegerMultBounds.Schoenhage
