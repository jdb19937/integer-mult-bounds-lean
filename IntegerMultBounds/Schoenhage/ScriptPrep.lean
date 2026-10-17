module

public import IntegerMultBounds.Schoenhage.ScriptMain
public import IntegerMultBounds.Schoenhage.ScriptHdr
public import IntegerMultBounds.Schoenhage.TransformGen

/-! The preparation of the round-script writer (§6) on its bank of 102 tapes. Tapes `0..90` are
the ring product's bank (`decoded` holds the parameters there), tape 91 receives the script, and
tapes `92..101` hold the slot loop's constants. From the decoded parameters the preparation
computes the constants of the slot loop (`runs_constsTopX`, `runs_rowsGenX`) and the inputs of the
header pass. -/

@[expose] public section

set_option maxRecDepth 100000

namespace IntegerMultBounds.Schoenhage

open Machine Strm TwistDescriptors Spec.SignedRingProduct ScriptOps ScriptParts ScriptMain

namespace ScriptPrep

/-! ### The bank -/

abbrev wrF : Fin 102 := 64
abbrev wrG : Fin 102 := 65
abbrev wkN : Fin 102 := 68
abbrev wkI : Fin 102 := 70
abbrev wkO : Fin 102 := 71
abbrev wkC : Fin 102 := 75
abbrev wxA : Fin 102 := 76
abbrev wxP : Fin 102 := 80
abbrev wlR : Fin 102 := 82
abbrev wlI : Fin 102 := 83
abbrev wiL : Fin 102 := 85
abbrev wO : Fin 102 := 91
abbrev wB : Fin 102 := 92
abbrev wFL : Fin 102 := 93
abbrev wLL : Fin 102 := 94
abbrev wTP : Fin 102 := 95
abbrev wRW : Fin 102 := 96
abbrev wE0 : Fin 102 := 97
abbrev wET : Fin 102 := 98
abbrev wP1 : Fin 102 := 99
abbrev wM1 : Fin 102 := 100
abbrev wM2 : Fin 102 := 101

/-- The writer's start: the decoded parameters on the ring product's bank, every other tape empty. -/
def wIn (p d ℓ K w : ℕ) (ts : List ℕ) : Fin 102 → WTape :=
  fun i => if h : i.val < 91 then decoded p d ℓ K w ts ⟨i.val, h⟩ else emp

/-- The paper's flags as words. -/
theorem flagsW_eq (ts : List ℕ) (ℓ : ℕ) :
    flagsW ts ℓ = (SigmaConstsTape.paperFlags ts ℓ).map fun b => [b] := by
  simp [flagsW, SigmaConstsTape.paperFlags]

/-- On the paper's axis lengths the decoded flags are the paper's flags. -/
theorem lengthFlags_eq {r : ℕ} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) :
    TransformParams.lengthFlags ℓ ts = SigmaConstsTape.paperFlags ts ℓ := by
  have hℓ : 1 ≤ ℓ := hL.2.2.2
  have hts : ∀ t ∈ ts, t = 2 ^ (ℓ - 1) ∨ t = 2 ^ ℓ := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨a, ha, -⟩ := hL.1 _ ht
    have hax : axLen ts i = a := by
      simp only [axLen, List.getD_eq_getElem _ _ hi, ha, Nat.log_pow (by norm_num : 1 < 2)]
    rw [ha]
    rcases hL.2.1 i hi with h | h <;> rw [hax] at h <;> simp [h]
  exact TransformParams.flags_paper hℓ hts

/-! ### The constants -/

/-- The constants program's tapes in the bank. -/
def cmap : Fin 20 → Fin 102 := ![wB, wkI, wkN, wFL, 0, wrG, 1, 2, wkO, 3, 4, wLL, wkC, 5, 6, 7, 8, 9, 10, wTP]

theorem cmap_injective : Function.Injective cmap := by decide

/-- Set up `[1]`, `ℓ - 1` and a copy of the flags. -/
noncomputable def prepA : Cmd 0 102 :=
  .seq (emit [[true]] wkC) <| .seq (rewind wkC) <| .seq (dropReg wiL wkC wB (by decide) (by decide) (by decide)) <|
  .seq (rewind wxA) <| .seq (appendAll wxA wFL (by decide)) (rewind wFL)

/-- The setup, then the constants. -/
noncomputable def prepAB : Cmd 0 102 := .seq prepA (SigmaConstsTape.constsTop.map cmap cmap_injective)

/-- The bank after the constants. -/
def stB (p d ℓ K w : ℕ) (ts : List ℕ) : Fin 102 → WTape :=
  let D := ts.length
  let q := (ℓ - 1) / K
  let b := (ℓ - 1) % K
  let L := (longs ts ℓ).length
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (wIn p d ℓ K w ts)
    wkC (reg [true])) wB (reg (ones b))) wFL ⟨(flagsW ts ℓ).reverse, []⟩) 0 ⟨List.replicate (ℓ - 1) [], []⟩)
    wrG (SigmaRowsTape.ticks q)) 1 (SigmaRowsTape.ticks b)) 2 (SigmaRowsTape.ticks D))
    wkO (SigmaRowsTape.endv (D * K))) 3 (SigmaRowsTape.endv (q * (D * K)))) 4 (reg (ones (b * D))))
    wLL (reg (ones L))) 8 (SigmaRowsTape.endv (q * (D * K) + D - 1))) 9 (SigmaRowsTape.endv (D * K - K)))
    10 (SigmaRowsTape.endv (D * q * K + D * b + L - 1 - L))) wTP ⟨(topsW ts ℓ K).reverse, []⟩

/-- The cost of the setup and the constants. -/
def costAB (ℓ K D L : ℕ) : ℕ :=
  16 * D + 4 * ℓ + 60 + SigmaConstsTape.constsTopCost (ℓ - 1) K D D L

set_option maxHeartbeats 64000000 in
theorem runs_prepAB {p d ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hD : ts.length = d - 1) :
    Runs prepAB (wIn p d ℓ K w ts) (· = stB p d ℓ K w ts) (costAB ℓ K ts.length (longs ts ℓ).length) := by
  have hK0 : 0 < K := hL.2.2.1
  have hfl := lengthFlags_eq hL
  set σ := wIn p d ℓ K w ts with hσ
  have s1 := runs_emit (a := 0) [[true]] wkC σ (by tsimp [hσ, wIn, decoded, decStart, emp])
  set σ₁ := Function.update σ wkC ⟨[[true]], []⟩ with hσ₁
  have e1 : Function.update σ wkC ⟨[[true]].reverse ++ (σ wkC).left, []⟩ = σ₁ := by
    tsimp [hσ₁, hσ, wIn, decoded, decStart, emp]
  rw [e1] at s1
  have s2 := runs_rewind' (a := 0) wkC σ₁ (L := [[true]]) (R := []) (by tsimp [hσ₁])
  set σ₂ := Function.update σ₁ wkC (reg [true]) with hσ₂
  have e2 : Function.update σ₁ wkC ⟨[], [[true]].reverse ++ []⟩ = σ₂ := by tsimp [hσ₂, reg]
  rw [e2] at s2
  have s3 := runs_dropReg (a := 0) (show wiL ≠ wkC by decide) (show wiL ≠ wB by decide)
    (show wkC ≠ wB by decide) σ₂ (u := ones ℓ) (v := [true]) (by tsimp [hσ₂, hσ₁, hσ, wIn, decoded])
    (by tsimp [hσ₂]) (by tsimp [hσ₂, hσ₁, hσ, wIn])
  set σ₃ := Function.update σ₂ wB (reg (ones (ℓ - 1))) with hσ₃
  have e3 : Function.update σ₂ wB (reg ((ones ℓ).drop [true].length)) = σ₃ := by
    rw [hσ₃, List.length_singleton, drop_ones]
  rw [e3] at s3
  set F := (SigmaConstsTape.paperFlags ts ℓ).map fun b => [b] with hF
  have hxA : σ₃ wxA = ⟨F.reverse, []⟩ := by tsimp [hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, hfl, hF]
  have s4 := runs_rewind' (a := 0) wxA σ₃ hxA
  set σ₄ := Function.update σ₃ wxA ⟨[], F⟩ with hσ₄
  have e4 : Function.update σ₃ wxA ⟨[], F.reverse.reverse ++ []⟩ = σ₄ := by tsimp [hσ₄]
  rw [e4] at s4
  have s5 := runs_appendAll (a := 0) (show wxA ≠ wFL by decide) 1 F σ₄ [] []
    (by tsimp [hσ₄]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, emp])
    (by intro x hx; simp only [hF, List.mem_map] at hx; obtain ⟨b, -, rfl⟩ := hx; simp)
  set σ₅ := Function.update (Function.update σ₄ wxA ⟨F.reverse, []⟩) wFL ⟨F.reverse, []⟩ with hσ₅
  have e5 : Function.update (Function.update σ₄ wxA ⟨F.reverse ++ [], []⟩) wFL ⟨F.reverse ++ [], []⟩ = σ₅ := by
    tsimp [hσ₅]
  rw [e5] at s5
  have s6 := runs_rewind' (a := 0) wFL σ₅ (L := F.reverse) (R := []) (by tsimp [hσ₅])
  set σ₆ := Function.update σ₅ wFL ⟨[], F⟩ with hσ₆
  have e6 : Function.update σ₅ wFL ⟨[], F.reverse.reverse ++ []⟩ = σ₆ := by tsimp [hσ₆]
  rw [e6] at s6
  have s7 := runs_constsTopX (x := ℓ - 1) (K := K) (D := ts.length) (flags := SigmaConstsTape.paperFlags ts ℓ)
    hK0 (σ₆ ∘ cmap)
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃]) (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, hD])
    (by tsimp [cmap, hσ₆, hF]) (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, ones])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
    (by tsimp [cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, wIn, decoded, decStart])
  have s8 := runs_lift cmap cmap_injective s7
  refine (Runs.seq ((Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono
    (fun τ e => by rw [e]; exact s8) le_rfl)).mono (fun τ e => ?_) ?_
  · rw [e]
    have htop := SigmaConstsTape.topWords_paper ts ℓ K
    have hv : (ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length = ts.length * ((ℓ - 1) / K) * K +
        ts.length * ((ℓ - 1) % K) := by ring
    simp only [ScriptParts.constsOut, upd_update cmap_injective, upd_comp_self cmap_injective,
      SigmaConstsTape.paperFlags_count, hv, htop]
    funext i; fin_cases i <;> first | rfl | tsimp [stB, cmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, hF, flagsW_eq,
      topsW, reg, ones, wIn, decoded, hfl]
  · simp only [costAB, clen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, length_ones,
      List.map_reverse, List.sum_reverse, SigmaConstsTape.paperFlags_count]
    have hlen : (SigmaConstsTape.paperFlags ts ℓ).length = ts.length := by simp [SigmaConstsTape.paperFlags]
    have hc : clen F = 2 * ts.length := by rw [hF, SigmaConstsTape.clen_flags, hlen]
    simp only [clen] at hc
    have hFlen : F.length = ts.length := by simp [hF, hlen]
    rw [hFlen, hlen]
    omega

/-! ### The axis rows -/

/-- The axis-rows program's tapes in the bank. -/
def rmap : Fin 15 → Fin 102 := ![2, 1, wrG, 11, wkN, wkO, wkI, wkC, 8, 9, 12, 13, wRW, 14, 15]

theorem rmap_injective : Function.Injective rmap := by decide

/-- Rewind the constants, then the axis rows. -/
noncomputable def prepC : Cmd 0 102 :=
  .seq (clear 0) <| .seq (clear 10) <| .seq (rewind wFL) <| .seq (rewind wTP) <| .seq (rewind wkO) <|
  .seq (ticksReg wkI 11 (by decide)) <| .seq (SigmaRowsTape.rowsGen.map rmap rmap_injective) <|
  .seq (rewind wRW) <| .seq (clear 8) <| .seq (clear 9) <| .seq (clear 2) <| .seq (clear 1) (clear 11)

/-- The bank after the axis rows. -/
def stC (p d ℓ K w : ℕ) (ts : List ℕ) : Fin 102 → WTape :=
  let D := ts.length
  let q := (ℓ - 1) / K
  let b := (ℓ - 1) % K
  let L := (longs ts ℓ).length
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (wIn p d ℓ K w ts)
    wkC (reg [true])) wB (reg (ones b))) wFL ⟨[], flagsW ts ℓ⟩) wrG (SigmaRowsTape.ticks q))
    wkO (reg (ones (D * K)))) 3 (SigmaRowsTape.endv (q * (D * K)))) 4 (reg (ones (b * D))))
    wLL (reg (ones L))) wTP ⟨[], topsW ts ℓ K⟩) wRW ⟨[], rowWords ts ℓ K⟩

/-- The cost of the axis rows. -/
def costC (ℓ K : ℕ) (ts : List ℕ) : ℕ :=
  let D := ts.length
  4 * ℓ + 4 * (D * K) + 10 * D + 6 * K + 4 * clen (flagsW ts ℓ) + 4 * clen (topsW ts ℓ K) +
    4 * clen (rowWords ts ℓ K) + 4 * (D * ((ℓ - 1) / K) * K + D * ((ℓ - 1) % K) + D) + 200 +
    D * (SigmaRowsTape.axisCost D (D * K) K ((ℓ - 1) % K) ((ℓ - 1) / K) (D * ((ℓ - 1) / K) * K + (D - 1))
      ((D - 1) * K) + 2)

set_option maxHeartbeats 64000000 in
theorem runs_prepC {p d ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hD : ts.length = d - 1) :
    Runs prepC (stB p d ℓ K w ts) (· = stC p d ℓ K w ts) (costC ℓ K ts) := by
  set σ := stB p d ℓ K w ts with hσ
  have s1 := runs_clear' (a := 0) 0 σ (T := ⟨List.replicate (ℓ - 1) [], []⟩) (by tsimp [hσ, stB])
  set σ₁ := Function.update σ 0 emp with hσ₁
  have s2 := runs_clear' (a := 0) 10 σ₁
    (T := SigmaRowsTape.endv (ts.length * ((ℓ - 1) / K) * K + ts.length * ((ℓ - 1) % K) + (longs ts ℓ).length - 1 -
      (longs ts ℓ).length)) (by tsimp [hσ₁, hσ, stB])
  set σ₂ := Function.update σ₁ 10 emp with hσ₂
  have s3 := runs_rewind' (a := 0) wFL σ₂ (L := (flagsW ts ℓ).reverse) (R := []) (by tsimp [hσ₂, hσ₁, hσ, stB])
  set σ₃ := Function.update σ₂ wFL ⟨[], flagsW ts ℓ⟩ with hσ₃
  have e3 : Function.update σ₂ wFL ⟨[], (flagsW ts ℓ).reverse.reverse ++ []⟩ = σ₃ := by tsimp [hσ₃]
  rw [e3] at s3
  have s4 := runs_rewind' (a := 0) wTP σ₃ (L := (topsW ts ℓ K).reverse) (R := [])
    (by tsimp [hσ₃, hσ₂, hσ₁, hσ, stB])
  set σ₄ := Function.update σ₃ wTP ⟨[], topsW ts ℓ K⟩ with hσ₄
  have e4 : Function.update σ₃ wTP ⟨[], (topsW ts ℓ K).reverse.reverse ++ []⟩ = σ₄ := by tsimp [hσ₄]
  rw [e4] at s4
  have s5 := runs_rewind' (a := 0) wkO σ₄ (L := [ones (ts.length * K)]) (R := [])
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, SigmaRowsTape.endv])
  set σ₅ := Function.update σ₄ wkO (reg (ones (ts.length * K))) with hσ₅
  have e5 : Function.update σ₄ wkO ⟨[], [ones (ts.length * K)].reverse ++ []⟩ = σ₅ := by tsimp [hσ₅, reg]
  rw [e5] at s5
  have s6 := runs_ticksReg (a := 0) (show wkI ≠ 11 by decide) σ₅ (u := ones K)
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, wIn, decoded])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, wIn, decoded, decStart, emp])
  set σ₆ := Function.update σ₅ 11 (SigmaRowsTape.ticks K) with hσ₆
  have e6 : Function.update σ₅ 11 ⟨[], List.replicate (ones K).length []⟩ = σ₆ := by
    rw [hσ₆, length_ones]; rfl
  rw [e6] at s6
  have hA : ts.length * ((ℓ - 1) / K) * K + (ts.length - 1) = (ℓ - 1) / K * (ts.length * K) + ts.length - 1 := by
    have : ts.length * ((ℓ - 1) / K) * K = (ℓ - 1) / K * (ts.length * K) := by ring
    rcases Nat.eq_zero_or_pos ts.length with h0 | h0
    · rw [h0]; simp
    · omega
  have hB : (ts.length - 1) * K = ts.length * K - K := by rw [Nat.sub_one_mul]
  have s7 := runs_rowsGenX hL (σ₆ ∘ rmap)
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB])
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, hA])
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, hB])
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, wIn, decoded, decStart, emp])
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, wIn, decoded, decStart, emp])
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB])
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB])
    (by tsimp [rmap, hσ₆])
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, wIn, decoded, hD])
    (by tsimp [rmap, hσ₆, hσ₅])
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, wIn, decoded])
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, ones])
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, wIn])
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, wIn, decoded, decStart])
    (by tsimp [rmap, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB, wIn, decoded, decStart])
  have s8 := runs_lift rmap rmap_injective s7
  set σ₇ := Function.update (Function.update (Function.update (Function.update σ₆ wRW
    ⟨(rowWords ts ℓ K).reverse, []⟩)
    8 (SigmaRowsTape.endv (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1) - ts.length)))
    9 (SigmaRowsTape.endv ((ts.length - 1) * K - ts.length * K))) 2 ⟨List.replicate ts.length [], []⟩ with hσ₇
  have e8 : upd σ₆ rmap (Function.update (Function.update (Function.update (Function.update (σ₆ ∘ rmap)
      SigmaRowsTape.gO ⟨(rowWords ts ℓ K).reverse, []⟩)
      SigmaRowsTape.gA (SigmaRowsTape.endv (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1) - ts.length)))
      SigmaRowsTape.gB (SigmaRowsTape.endv ((ts.length - 1) * K - ts.length * K)))
      SigmaRowsTape.gAx ⟨List.replicate ts.length [], []⟩) = σ₇ := by
    rw [upd_update rmap_injective, upd_update rmap_injective, upd_update rmap_injective,
      upd_update rmap_injective, upd_comp_self rmap_injective]
    rfl
  rw [e8] at s8
  have s9 := runs_rewind' (a := 0) wRW σ₇ (L := (rowWords ts ℓ K).reverse) (R := []) (by tsimp [hσ₇])
  set σ₈ := Function.update σ₇ wRW ⟨[], rowWords ts ℓ K⟩ with hσ₈
  have e9 : Function.update σ₇ wRW ⟨[], (rowWords ts ℓ K).reverse.reverse ++ []⟩ = σ₈ := by tsimp [hσ₈]
  rw [e9] at s9
  have s10 := runs_clear' (a := 0) 8 σ₈
    (T := SigmaRowsTape.endv (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1) - ts.length)) (by tsimp [hσ₈, hσ₇])
  set σ₉ := Function.update σ₈ 8 emp with hσ₉
  have s11 := runs_clear' (a := 0) 9 σ₉ (T := SigmaRowsTape.endv ((ts.length - 1) * K - ts.length * K)) (by tsimp [hσ₉, hσ₈, hσ₇])
  set σ₁₀ := Function.update σ₉ 9 emp with hσ₁₀
  have s12 := runs_clear' (a := 0) 2 σ₁₀ (T := ⟨List.replicate ts.length [], []⟩) (by tsimp [hσ₁₀, hσ₉, hσ₈, hσ₇])
  set σ₁₁ := Function.update σ₁₀ 2 emp with hσ₁₁
  have s13 := runs_clear' (a := 0) 1 σ₁₁ (T := SigmaRowsTape.ticks ((ℓ - 1) % K)) (by tsimp [hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stB])
  set σ₁₂ := Function.update σ₁₁ 1 emp with hσ₁₂
  have s14 := runs_clear' (a := 0) 11 σ₁₂ (T := SigmaRowsTape.ticks K) (by tsimp [hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s8
    (Runs.then s9 (Runs.then s10 (Runs.then s11 (Runs.then s12 (Runs.then s13 s14)))))))))))).mono
    (fun τ e => ?_) ?_
  · rw [e]
    funext i; fin_cases i <;> rfl
  · simp only [costC, clen, WTape.words, SigmaRowsTape.endv, SigmaRowsTape.ticks, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, List.length_nil, List.reverse_nil,
      List.nil_append, List.append_nil, length_ones, 
      List.map_reverse, List.sum_reverse, List.map_replicate, List.sum_replicate, smul_eq_mul]
    have := Nat.mod_le (ℓ - 1) K
    omega

/-! ### The numbers -/

/-- `o := a + b` in unary. -/
noncomputable def addTo {t : ℕ} (a b o : Fin t) (h1 : a ≠ o) (h2 : b ≠ o) : Cmd 0 t :=
  .seq (cpyReg a o h1) <| .seq (appendReg b o h2) (rewind o)

theorem runs_addTo {t : ℕ} {a b o : Fin t} (h1 : a ≠ o) (h2 : b ≠ o) (σ : Fin t → WTape) {x y : ℕ}
    (ha : σ a = reg (ones x)) (hb : σ b = reg (ones y)) (ho : σ o = emp) :
    Runs (addTo a b o h1 h2) σ (· = Function.update σ o (reg (ones (x + y)))) (3 * x + 3 * y + 30) := by
  have s1 := runs_cpyReg (a := 0) h1 σ (u := ones x) (M := []) ha (by rw [ho]; rfl)
  have s2 := runs_appendReg (a := 0) h2 (Function.update σ o ⟨[ones x], []⟩) (u := ones y) (v := ones x) (M := [])
    (by rw [Function.update_of_ne h2]; exact hb) (by simp)
  have s3 := runs_rewind' (a := 0) o (Function.update (Function.update σ o ⟨[ones x], []⟩) o
    ⟨[ones x ++ ones y], []⟩) (L := [ones x ++ ones y]) (R := []) (by simp)
  refine (Runs.then s1 (Runs.then s2 s3)).mono (fun τ e => ?_) ?_
  · rw [e]; simp [ones_append_ones, reg]
  · simp [clen]; omega

/-- The slot loop's numbers and the header pass's inputs. -/
noncomputable def prepD : Cmd 0 102 :=
  .seq (rewind 3) <| .seq (addTo wiL wkC wP1 (by decide) (by decide)) <|
  .seq (addTo wP1 3 wE0 (by decide) (by decide)) <| .seq (addTo wE0 4 wET (by decide) (by decide)) <|
  .seq (dropReg wiL wkC wM1 (by decide) (by decide) (by decide)) <|
  .seq (dropReg wM1 wkC wM2 (by decide) (by decide) (by decide)) <|
  .seq (addTo wkN wkC wxP (by decide) (by decide)) <| .seq (addTo 3 4 16 (by decide) (by decide)) <|
  .seq (addTo 16 wLL 17 (by decide) (by decide)) <| .seq (dropReg 17 wkO wlR (by decide) (by decide) (by decide)) <|
  .seq (clear 16) <| .seq (clear 17) <| .seq (emit [[]] wlI) <| .seq (rewind wlI) <| .seq (clear 3) (clear 4)

/-- The bank after the preparation. -/
def stD (p d ℓ K w : ℕ) (ts : List ℕ) : Fin 102 → WTape :=
  let D := ts.length
  let q := (ℓ - 1) / K
  let b := (ℓ - 1) % K
  let L := (longs ts ℓ).length
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (wIn p d ℓ K w ts)
    wkC (reg [true])) wB (reg (ones b))) wFL ⟨[], flagsW ts ℓ⟩) wrG (SigmaRowsTape.ticks q))
    wkO (reg (ones (D * K)))) wLL (reg (ones L))) wTP ⟨[], topsW ts ℓ K⟩) wRW ⟨[], rowWords ts ℓ K⟩)
    wP1 (reg (ones (ℓ + 1)))) wE0 (reg (ones (ℓ + 1 + q * (D * K)))))
    wET (reg (ones (ℓ + 1 + q * (D * K) + b * D)))) wM1 (reg (ones (ℓ - 1)))) wM2 (reg (ones (ℓ - 2))))
    wxP (reg (ones d))) wlR (reg (ones (q * (D * K) + b * D + L - D * K)))) wlI (reg [])

/-- The cost of the numbers. -/
def costD (ℓ K d : ℕ) (ts : List ℕ) : ℕ :=
  30 * ℓ + 30 * ((ℓ - 1) / K * (ts.length * K)) + 30 * ((ℓ - 1) % K * ts.length) + 10 * (longs ts ℓ).length +
    4 * (ts.length * K) + 3 * d + 600

set_option maxHeartbeats 64000000 in
theorem runs_prepD {p d ℓ K w : ℕ} {ts : List ℕ} (hd : 1 ≤ d) (_hD : ts.length = d - 1) :
    Runs prepD (stC p d ℓ K w ts) (· = stD p d ℓ K w ts) (costD ℓ K d ts) := by
  set σ := stC p d ℓ K w ts with hσ
  have s1 := runs_rewind' (a := 0) 3 σ (L := [ones ((ℓ - 1) / K * (ts.length * K))]) (R := []) (by tsimp [hσ, stC, SigmaRowsTape.endv])
  set σ₁ := Function.update σ 3 (reg (ones ((ℓ - 1) / K * (ts.length * K)))) with hσ₁
  have e1 : Function.update σ 3 ⟨[], [ones ((ℓ - 1) / K * (ts.length * K))].reverse ++ []⟩ = σ₁ := by tsimp [hσ₁, reg]
  rw [e1] at s1
  have s2 := runs_addTo (show wiL ≠ wP1 by decide) (show wkC ≠ wP1 by decide) σ₁ (x := ℓ) (y := 1)
    (by tsimp [hσ₁, hσ, stC, wIn, decoded]) (by tsimp [hσ₁, hσ, stC, ones])
    (by tsimp [hσ₁, hσ, stC, wIn])
  set σ₂ := Function.update σ₁ wP1 (reg (ones (ℓ + 1))) with hσ₂
  have s3 := runs_addTo (show wP1 ≠ wE0 by decide) (show (3 : Fin 102) ≠ wE0 by decide) σ₂ (x := ℓ + 1)
    (y := (ℓ - 1) / K * (ts.length * K)) (by tsimp [hσ₂]) (by tsimp [hσ₂, hσ₁]) (by tsimp [hσ₂, hσ₁, hσ, stC, wIn])
  set σ₃ := Function.update σ₂ wE0 (reg (ones (ℓ + 1 + (ℓ - 1) / K * (ts.length * K)))) with hσ₃
  have s4 := runs_addTo (show wE0 ≠ wET by decide) (show (4 : Fin 102) ≠ wET by decide) σ₃
    (x := ℓ + 1 + (ℓ - 1) / K * (ts.length * K)) (y := (ℓ - 1) % K * ts.length) (by tsimp [hσ₃]) (by tsimp [hσ₃, hσ₂, hσ₁, hσ, stC])
    (by tsimp [hσ₃, hσ₂, hσ₁, hσ, stC, wIn])
  set σ₄ := Function.update σ₃ wET (reg (ones (ℓ + 1 + (ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length))) with hσ₄
  have s5 := runs_dropReg (a := 0) (show wiL ≠ wkC by decide) (show wiL ≠ wM1 by decide)
    (show wkC ≠ wM1 by decide) σ₄ (u := ones ℓ) (v := [true])
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC, wIn, decoded]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC])
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC, wIn])
  set σ₅ := Function.update σ₄ wM1 (reg (ones (ℓ - 1))) with hσ₅
  have e5 : Function.update σ₄ wM1 (reg ((ones ℓ).drop [true].length)) = σ₅ := by
    rw [hσ₅, List.length_singleton, drop_ones]
  rw [e5] at s5
  have s6 := runs_dropReg (a := 0) (show wM1 ≠ wkC by decide) (show wM1 ≠ wM2 by decide)
    (show wkC ≠ wM2 by decide) σ₅ (u := ones (ℓ - 1)) (v := [true])
    (by tsimp [hσ₅]) (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC])
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC, wIn])
  set σ₆ := Function.update σ₅ wM2 (reg (ones (ℓ - 2))) with hσ₆
  have e6 : Function.update σ₅ wM2 (reg ((ones (ℓ - 1)).drop [true].length)) = σ₆ := by
    rw [hσ₆, List.length_singleton, drop_ones, Nat.sub_sub]
  rw [e6] at s6
  have s7 := runs_addTo (show wkN ≠ wxP by decide) (show wkC ≠ wxP by decide) σ₆ (x := d - 1) (y := 1)
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC, wIn, decoded])
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC, ones])
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC, wIn, decoded, decStart, emp])
  set σ₇ := Function.update σ₆ wxP (reg (ones d)) with hσ₇
  have e7 : Function.update σ₆ wxP (reg (ones (d - 1 + 1))) = σ₇ := by
    rw [hσ₇, Nat.sub_add_cancel hd]
  rw [e7] at s7
  have s8 := runs_addTo (show (3 : Fin 102) ≠ 16 by decide) (show (4 : Fin 102) ≠ 16 by decide) σ₇
    (x := (ℓ - 1) / K * (ts.length * K)) (y := (ℓ - 1) % K * ts.length) (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁])
    (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC])
    (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC, wIn, decoded, decStart, emp])
  set σ₈ := Function.update σ₇ 16 (reg (ones ((ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length))) with hσ₈
  have s9 := runs_addTo (show (16 : Fin 102) ≠ 17 by decide) (show wLL ≠ 17 by decide) σ₈
    (x := (ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length) (y := (longs ts ℓ).length) (by tsimp [hσ₈])
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC])
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC, wIn, decoded, decStart, emp])
  set σ₉ := Function.update σ₈ 17 (reg (ones ((ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length + (longs ts ℓ).length))) with hσ₉
  have s10 := runs_dropReg (a := 0) (show (17 : Fin 102) ≠ wkO by decide) (show (17 : Fin 102) ≠ wlR by decide)
    (show wkO ≠ wlR by decide) σ₉ (u := ones ((ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length + (longs ts ℓ).length)) (v := ones (ts.length * K))
    (by tsimp [hσ₉]) (by tsimp [hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC])
    (by tsimp [hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC, wIn, decoded, decStart, emp])
  set σ₁₀ := Function.update σ₉ wlR (reg (ones ((ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length + (longs ts ℓ).length - ts.length * K))) with hσ₁₀
  have e10 : Function.update σ₉ wlR (reg ((ones ((ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length + (longs ts ℓ).length)).drop (ones (ts.length * K)).length)) = σ₁₀ := by
    rw [hσ₁₀, length_ones, drop_ones]
  rw [e10] at s10
  have s11 := runs_clear' (a := 0) 16 σ₁₀ (T := reg (ones ((ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length))) (by tsimp [hσ₁₀, hσ₉, hσ₈])
  set σ₁₁ := Function.update σ₁₀ 16 emp with hσ₁₁
  have s12 := runs_clear' (a := 0) 17 σ₁₁ (T := reg (ones ((ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length + (longs ts ℓ).length))) (by tsimp [hσ₁₁, hσ₁₀, hσ₉])
  set σ₁₂ := Function.update σ₁₁ 17 emp with hσ₁₂
  have s13 := runs_emit (a := 0) [[]] wlI σ₁₂
    (by tsimp [hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC, wIn, decoded, decStart, emp])
  set σ₁₃ := Function.update σ₁₂ wlI ⟨[[]], []⟩ with hσ₁₃
  have e13 : Function.update σ₁₂ wlI ⟨[[]].reverse ++ (σ₁₂ wlI).left, []⟩ = σ₁₃ := by
    tsimp [hσ₁₃, hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC, wIn, decoded, decStart, emp]
  rw [e13] at s13
  have s14 := runs_rewind' (a := 0) wlI σ₁₃ (L := [[]]) (R := []) (by tsimp [hσ₁₃])
  set σ₁₄ := Function.update σ₁₃ wlI (reg []) with hσ₁₄
  have e14 : Function.update σ₁₃ wlI ⟨[], [[]].reverse ++ []⟩ = σ₁₄ := by tsimp [hσ₁₄, reg]
  rw [e14] at s14
  have s15 := runs_clear' (a := 0) 3 σ₁₄ (T := reg (ones ((ℓ - 1) / K * (ts.length * K))))
    (by tsimp [hσ₁₄, hσ₁₃, hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁])
  set σ₁₅ := Function.update σ₁₄ 3 emp with hσ₁₅
  have s16 := runs_clear' (a := 0) 4 σ₁₅ (T := reg (ones ((ℓ - 1) % K * ts.length)))
    (by tsimp [hσ₁₅, hσ₁₄, hσ₁₃, hσ₁₂, hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stC])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 (Runs.then s12 (Runs.then s13 (Runs.then s14
    (Runs.then s15 s16))))))))))))))).mono (fun τ e => ?_) ?_
  · rw [e]
    funext i; fin_cases i <;> rfl
  · simp only [costD, clen, WTape.words, reg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, List.reverse_nil, List.nil_append, length_ones]
    omega

/-! ### The preparation -/

/-- The preparation: the constants, the axis rows, the numbers. -/
noncomputable def prep : Cmd 0 102 := .seq prepAB (.seq prepC prepD)

/-- The cost of the preparation. -/
def prepCost (ℓ K d : ℕ) (ts : List ℕ) : ℕ :=
  costAB ℓ K ts.length (longs ts ℓ).length + 1 + (costC ℓ K ts + 1 + costD ℓ K d ts)

/-- `runs_prep`: from the decoded parameters the preparation leaves the slot loop's constants and
the header pass's inputs (`stD`). -/
theorem runs_prep {p d ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hd : 1 ≤ d)
    (hD : ts.length = d - 1) :
    Runs prep (wIn p d ℓ K w ts) (· = stD p d ℓ K w ts) (prepCost ℓ K d ts) :=
  Runs.then (runs_prepAB (p := p) (w := w) hL hD) (Runs.then (runs_prepC hL hD) (runs_prepD hd hD))

end ScriptPrep

end IntegerMultBounds.Schoenhage
