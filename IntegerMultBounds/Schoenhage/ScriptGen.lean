module

public import IntegerMultBounds.Schoenhage.ScriptPrep

/-! The round-script writer (§6) on its bank of 102 tapes: the preparation (`ScriptPrep.runs_prep`),
the header pass on the ring product's bank (`ScriptHdr.runs_hdrPass`), the slot loop on the slot
bank (`ScriptMain.runs_mainF`, `ScriptMain.runs_mainO`), then clearing. From the decoded parameters
it leaves the forward or opposite round script on tape 91 and restores every other tape. -/

@[expose] public section

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntegerMultBounds.Schoenhage

open Machine Strm TwistDescriptors Spec.SignedRingProduct ScriptOps ScriptParts ScriptMain ScriptPrep

namespace ScriptGen

/-! ### The headers in slot order -/

theorem map_range_mul {α : Type*} (g : ℕ → α) (K : ℕ) : ∀ q : ℕ,
    (List.range (q * K)).map g = (List.range q).flatMap fun c => (List.range K).map fun ρ => g (c * K + ρ)
  | 0 => by simp
  | q + 1 => by
    rw [Nat.succ_mul, List.range_add, List.map_append, map_range_mul g K q, List.range_succ,
      List.flatMap_append]
    simp [List.map_map, Function.comp_def]

/-- The exponent `e₀ = n - DK` of the header pass, `n = log₂ ∏ ts`. -/
def eZero (ℓ K : ℕ) (ts : List ℕ) : ℕ :=
  (ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length + (longs ts ℓ).length - ts.length * K

/-- `allHdrs_eq`: the header pass's headers are the chunk-group headers in slot order. -/
theorem allHdrs_eq {p d w ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) :
    ScriptHdr.allHdrs p d ℓ ts.length K w (eZero ℓ K ts) (ts.length * K) ((ℓ - 1) / K) =
      chunkHdrs p d w ℓ K ts := by
  have hK : 0 < K := hL.2.2.1
  have hn := log_prod_layout hL
  have hx := Nat.mod_add_div (ℓ - 1) K
  unfold chunkHdrs ScriptHdr.allHdrs ScriptHdr.groupHdrs
  conv_rhs => rw [← hx, List.range_add, List.drop_left' (by simp), List.map_map, Nat.mul_comm K,
    map_range_mul _ K]
  apply List.flatMap_congr
  intro c hc
  apply List.map_congr_left
  intro ρ hρ
  simp only [List.mem_range] at hc hρ
  simp only [Function.comp_apply, chunkHdr, chunkOf, rhoOf, Nat.add_sub_cancel_left]
  have h1 : (c * K + ρ) / K = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hρ, Nat.zero_add]
  have h2 : (c * K + ρ) % K = ρ := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hρ]
  rw [h1, h2]
  have e1 : c * ts.length * K = c * (ts.length * K) := Nat.mul_assoc _ _ _
  have e2 : K * ts.length = ts.length * K := Nat.mul_comm _ _
  have e3 : ts.length * ((ℓ - 1) / K) * K = (ℓ - 1) / K * (ts.length * K) := by ring
  have e4 : ts.length * ((ℓ - 1) % K) = (ℓ - 1) % K * ts.length := Nat.mul_comm _ _
  rw [e1, e2, show eZero ℓ K ts - c * (ts.length * K) =
    Nat.log 2 ts.prod - (c * (ts.length * K) + ts.length * K) by unfold eZero; omega]

/-! ### The header pass on the bank -/

/-- The ring product's bank inside the writer's bank. -/
def ui (x : Fin 𝕌) : Fin 102 := ⟨x.val, by have := x.isLt; omega⟩

theorem ui_injective : Function.Injective ui := fun x y h => Fin.ext (by simpa [ui] using congrArg Fin.val h)

/-- The header pass, then clearing its counters. -/
noncomputable def hdrW : Cmd 0 102 :=
  .seq (ScriptHdr.hdrPass.map ui ui_injective) <| .seq (clear wrG) <| .seq (clear wlI) <| .seq (clear wlR) <|
  .seq (clear wkO) (clear wxP)

/-- The bank after the header pass. -/
noncomputable def stH (p d ℓ K w : ℕ) (ts : List ℕ) : Fin 102 → WTape :=
  let D := ts.length
  let q := (ℓ - 1) / K
  let b := (ℓ - 1) % K
  let L := (longs ts ℓ).length
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (wIn p d ℓ K w ts)
    wkC (reg [true])) wB (reg (ones b))) wFL ⟨[], flagsW ts ℓ⟩) wLL (reg (ones L))) wTP ⟨[], topsW ts ℓ K⟩)
    wRW ⟨[], rowWords ts ℓ K⟩) wP1 (reg (ones (ℓ + 1)))) wE0 (reg (ones (ℓ + 1 + q * (D * K)))))
    wET (reg (ones (ℓ + 1 + q * (D * K) + b * D)))) wM1 (reg (ones (ℓ - 1)))) wM2 (reg (ones (ℓ - 2))))
    wrF (hdFull p d w ℓ K ts)

theorem decoded_low {p d ℓ K w : ℕ} {ts : List ℕ} {x : Fin 𝕌} (hx : x.val < 64) :
    decoded p d ℓ K w ts x = emp := by
  have h : ∀ y : Fin 𝕌, 64 ≤ y.val → (x = y) = False := fun y hy => by
    apply propext; constructor
    · intro e; rw [e] at hx; omega
    · exact False.elim
  simp only [decoded, decStart, Function.update_apply, h _ (by decide : 64 ≤ (Tp.iP : Fin 𝕌).val),
    h _ (by decide : 64 ≤ (Tp.kN : Fin 𝕌).val), h _ (by decide : 64 ≤ (Tp.iL : Fin 𝕌).val),
    h _ (by decide : 64 ≤ (Tp.kI : Fin 𝕌).val), h _ (by decide : 64 ≤ (Tp.iW : Fin 𝕌).val),
    h _ (by decide : 64 ≤ (Tp.xB : Fin 𝕌).val), h _ (by decide : 64 ≤ (Tp.xA : Fin 𝕌).val),
    h _ (by decide : 64 ≤ (Tp.zH : Fin 𝕌).val), ite_false]

theorem stD_low {p d ℓ K w : ℕ} {ts : List ℕ} (x : Fin 𝕋) : stD p d ℓ K w ts (ui (ι x)) = emp := by
  have hx : (ui (ι x)).val < 64 := by simp [ui]
  have h : ∀ y : Fin 102, 64 ≤ y.val → (ui (ι x) = y) = False := fun y hy => by
    apply propext; constructor
    · intro e; rw [e] at hx; omega
    · exact False.elim
  simp only [stD, Function.update_apply, h _ (by decide : 64 ≤ (wkC : Fin 102).val),
    h _ (by decide : 64 ≤ (wB : Fin 102).val), h _ (by decide : 64 ≤ (wFL : Fin 102).val),
    h _ (by decide : 64 ≤ (wrG : Fin 102).val), h _ (by decide : 64 ≤ (wkO : Fin 102).val),
    h _ (by decide : 64 ≤ (wLL : Fin 102).val), h _ (by decide : 64 ≤ (wTP : Fin 102).val),
    h _ (by decide : 64 ≤ (wRW : Fin 102).val), h _ (by decide : 64 ≤ (wP1 : Fin 102).val),
    h _ (by decide : 64 ≤ (wE0 : Fin 102).val), h _ (by decide : 64 ≤ (wET : Fin 102).val),
    h _ (by decide : 64 ≤ (wM1 : Fin 102).val), h _ (by decide : 64 ≤ (wM2 : Fin 102).val),
    h _ (by decide : 64 ≤ (wxP : Fin 102).val), h _ (by decide : 64 ≤ (wlR : Fin 102).val),
    h _ (by decide : 64 ≤ (wlI : Fin 102).val), ite_false, wIn]
  rw [dite_eq_left_of_eq_true (by simp [ui]; omega)]
  exact decoded_low (by simp [ui])

/-- The cost of the header pass and its clearing. -/
def costH (p d ℓ K w : ℕ) (ts : List ℕ) : ℕ :=
  ScriptHdr.passCost p d ℓ ts.length K w (eZero ℓ K ts) (ts.length * K) 0 ((ℓ - 1) / K) +
    4 * ((ℓ - 1) / K) + 4 * ((ℓ - 1) / K * (ts.length * K)) + 4 * eZero ℓ K ts + 4 * (ts.length * K) + 2 * d + 50

set_option maxHeartbeats 64000000 in
theorem runs_hdrW {p d ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hD : ts.length = d - 1) :
    Runs hdrW (stD p d ℓ K w ts) (· = stH p d ℓ K w ts) (costH p d ℓ K w ts) := by
  set σ := stD p d ℓ K w ts with hσ
  have hc : Clean (σ ∘ ui) := by funext x; exact stD_low x
  have s1 := ScriptHdr.runs_hdrPass (p := p) (d := d) (ℓ := ℓ) (D := ts.length) (K := K) (w := w) (e0 := eZero ℓ K ts)
    (DK := ts.length * K) (q := (ℓ - 1) / K) (σ ∘ ui) hc
    (by tsimp [ui, hσ, stD, wIn, decoded]) (by tsimp [ui, hσ, stD]) (by tsimp [ui, hσ, stD, wIn, decoded])
    (by tsimp [ui, hσ, stD, wIn, decoded, hD]) (by tsimp [ui, hσ, stD, wIn, decoded])
    (by tsimp [ui, hσ, stD, wIn, decoded]) (by tsimp [ui, hσ, stD])
    (by tsimp [ui, hσ, stD, wIn, decoded, decStart]) (by tsimp [ui, hσ, stD, wIn, decoded, decStart])
    (by tsimp [ui, hσ, stD, wIn, decoded, decStart]) (by tsimp [ui, hσ, stD, wIn, decoded, decStart])
    (by tsimp [ui, hσ, stD, wIn, decoded, decStart]) (by tsimp [ui, hσ, stD, wIn, decoded, decStart])
    (by tsimp [ui, hσ, stD, wIn, decoded, decStart]) (by tsimp [ui, hσ, stD, wIn, decoded, decStart])
    (by tsimp [ui, hσ, stD, wIn, decoded, decStart]) (by tsimp [ui, hσ, stD]) ((ℓ - 1) / K) 0 (by omega)
  rw [ScriptHdr.passSt_zero (σ ∘ ui) (by tsimp [ui, hσ, stD, wIn, decoded, decStart])
    (by tsimp [ui, hσ, stD, SigmaRowsTape.ticks]) (by tsimp [ui, hσ, stD]) (by tsimp [ui, hσ, stD, eZero])]
    at s1
  have s2 := runs_lift ui ui_injective s1
  set σ₁ := Function.update (Function.update (Function.update (Function.update σ wrF
    ⟨(ScriptHdr.allHdrs p d ℓ ts.length K w (eZero ℓ K ts) (ts.length * K) ((ℓ - 1) / K)).reverse, []⟩)
    wrG ⟨List.replicate ((ℓ - 1) / K) [], List.replicate (((ℓ - 1) / K) - ((ℓ - 1) / K)) []⟩) wlI (reg (ones (((ℓ - 1) / K) * (ts.length * K)))))
    wlR (reg (ones ((eZero ℓ K ts) - ((ℓ - 1) / K) * (ts.length * K)))) with hσ₁
  have e2 : upd σ ui (ScriptHdr.passSt (σ ∘ ui) p d ℓ ts.length K w (eZero ℓ K ts) (ts.length * K) ((ℓ - 1) / K) ((ℓ - 1) / K)) = σ₁ := by
    rw [ScriptHdr.passSt, upd_update ui_injective, upd_update ui_injective, upd_update ui_injective,
      upd_update ui_injective, upd_comp_self ui_injective]
    rfl
  rw [e2] at s2
  have s3 := runs_clear' (a := 0) wrG σ₁ (T := ⟨List.replicate ((ℓ - 1) / K) [], List.replicate ((ℓ - 1) / K - (ℓ - 1) / K) []⟩) (by tsimp [hσ₁])
  set σ₂ := Function.update σ₁ wrG emp with hσ₂
  have s4 := runs_clear' (a := 0) wlI σ₂ (T := reg (ones ((ℓ - 1) / K * (ts.length * K)))) (by tsimp [hσ₂, hσ₁])
  set σ₃ := Function.update σ₂ wlI emp with hσ₃
  have s5 := runs_clear' (a := 0) wlR σ₃ (T := reg (ones (eZero ℓ K ts - (ℓ - 1) / K * (ts.length * K)))) (by tsimp [hσ₃, hσ₂, hσ₁])
  set σ₄ := Function.update σ₃ wlR emp with hσ₄
  have s6 := runs_clear' (a := 0) wkO σ₄ (T := reg (ones (ts.length * K))) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, stD])
  set σ₅ := Function.update σ₄ wkO emp with hσ₅
  have s7 := runs_clear' (a := 0) wxP σ₅ (T := reg (ones d)) (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stD])
  have hall := allHdrs_eq (p := p) (d := d) (w := w) hL
  refine (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 s7))))).mono (fun τ e => ?_) ?_
  · rw [e]
    funext i; fin_cases i <;> first | rfl | tsimp [stH, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stD, wIn, decoded, decStart,
      emp, hall, hdFull]
  · simp only [costH, clen, WTape.words, reg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, List.reverse_nil, List.nil_append, List.append_nil, length_ones,
      List.map_replicate, List.sum_replicate, smul_eq_mul, Nat.sub_self, List.replicate_zero, List.length_replicate,
      List.reverse_replicate]
    omega

/-! ### The slot loop on the bank -/

/-- The slot bank inside the writer's bank. -/
def mmap : Fin 37 → Fin 102 := ![wO, wrF, 0, 1, 2, wkC, wB, wFL, wLL, wTP, wRW, wE0, wET, wP1, wM1, wM2, wkN,
  3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

theorem mmap_injective : Function.Injective mmap := by decide

/-- The forward or opposite slot program. -/
noncomputable def mainFO : Bool → Cmd 0 37
  | true => mainF
  | false => mainO

/-- The forward or opposite round script. -/
noncomputable def script (fwd : Bool) (p d w ℓ K : ℕ) (ts : List ℕ) (hL : LayoutOK (2 ^ ℓ) ts ℓ K) :
    List (List Bool) :=
  if fwd then fwdScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K else oppScript p d (2 ^ ℓ) w (paperPerm hL) ts ℓ K

/-- The cost of the slot loop. -/
noncomputable def costM (fwd : Bool) (p d w ℓ K : ℕ) (ts : List ℕ) : ℕ :=
  mainExtra p d w ℓ K ts + if fwd then loopCostF p d w ℓ K ts ℓ else loopCostO p d w ℓ K ts ℓ

set_option maxHeartbeats 64000000 in
theorem runs_mainW (fwd : Bool) {p d ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K)
    (hD : ts.length = d - 1) :
    Runs ((mainFO fwd).map mmap mmap_injective) (stH p d ℓ K w ts)
      (· = Function.update (Function.update (stH p d ℓ K w ts) wrF emp) wO
        ⟨(script fwd p d w ℓ K ts hL).reverse, []⟩) (costM fwd p d w ℓ K ts) := by
  have hcomp : stH p d ℓ K w ts ∘ mmap = mIn p d w ℓ K ts := by
    funext i; fin_cases i <;> tsimp [mmap, stH, mIn, mconst, wIn, decoded, decStart, emp, hD]
  have hmc : mconst ℓ K ts = Function.update (stH p d ℓ K w ts ∘ mmap) ScriptMain.mHD emp := by
    rw [hcomp, mIn, Function.update_idem]
    funext i; by_cases h : i = ScriptMain.mHD
    · subst h; tsimp [mconst, emp]
    · rw [Function.update_of_ne h]
  have key : ∀ X : List (List Bool), upd (stH p d ℓ K w ts) mmap (Function.update (mconst ℓ K ts) ScriptMain.mO ⟨X, []⟩) =
      Function.update (Function.update (stH p d ℓ K w ts) wrF emp) wO ⟨X, []⟩ := by
    intro X
    rw [hmc, upd_update mmap_injective, upd_update mmap_injective, upd_comp_self mmap_injective]
    rfl
  cases fwd
  · have s := runs_mainO p d w hL
    rw [← hcomp] at s
    have s' := runs_lift mmap mmap_injective s
    rw [key] at s'
    exact s'
  · have s := runs_mainF p d w hL
    rw [← hcomp] at s
    have s' := runs_lift mmap mmap_injective s
    rw [key] at s'
    exact s'

/-! ### Clearing -/

/-- Clear the constants and rewind the script. -/
noncomputable def finish : Cmd 0 102 :=
  .seq (clear wB) <| .seq (clear wFL) <| .seq (clear wLL) <| .seq (clear wTP) <| .seq (clear wRW) <|
  .seq (clear wE0) <| .seq (clear wET) <| .seq (clear wP1) <| .seq (clear wM1) <| .seq (clear wM2) <|
  .seq (clear wkC) (rewind wO)

/-- The cost of the clearing. -/
def costZ (ℓ K : ℕ) (ts : List ℕ) (S : List (List Bool)) : ℕ :=
  2 * clen (flagsW ts ℓ) + 2 * clen (topsW ts ℓ K) + 2 * clen (rowWords ts ℓ K) + clen S +
    12 * ℓ + 6 * ((ℓ - 1) / K * (ts.length * K)) + 4 * ((ℓ - 1) % K * ts.length) + 2 * (longs ts ℓ).length +
    2 * ((ℓ - 1) % K) + 100

set_option maxHeartbeats 64000000 in
theorem runs_finish {p d ℓ K w : ℕ} {ts : List ℕ} (S : List (List Bool)) :
    Runs finish (Function.update (Function.update (stH p d ℓ K w ts) wrF emp) wO ⟨S.reverse, []⟩)
      (· = Function.update (wIn p d ℓ K w ts) wO ⟨[], S⟩) (costZ ℓ K ts S) := by
  set σ := Function.update (Function.update (stH p d ℓ K w ts) wrF emp) wO ⟨S.reverse, []⟩ with hσ
  have s1 := runs_clear' (a := 0) wB σ (T := reg (ones ((ℓ - 1) % K))) (by tsimp [hσ, stH])
  set σ₁ := Function.update σ wB emp with hσ₁
  have s2 := runs_clear' (a := 0) wFL σ₁ (T := ⟨[], flagsW ts ℓ⟩) (by tsimp [hσ₁, hσ, stH])
  set σ₂ := Function.update σ₁ wFL emp with hσ₂
  have s3 := runs_clear' (a := 0) wLL σ₂ (T := reg (ones (longs ts ℓ).length)) (by tsimp [hσ₂, hσ₁, hσ, stH])
  set σ₃ := Function.update σ₂ wLL emp with hσ₃
  have s4 := runs_clear' (a := 0) wTP σ₃ (T := ⟨[], topsW ts ℓ K⟩) (by tsimp [hσ₃, hσ₂, hσ₁, hσ, stH])
  set σ₄ := Function.update σ₃ wTP emp with hσ₄
  have s5 := runs_clear' (a := 0) wRW σ₄ (T := ⟨[], rowWords ts ℓ K⟩) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hσ, stH])
  set σ₅ := Function.update σ₄ wRW emp with hσ₅
  have s6 := runs_clear' (a := 0) wE0 σ₅ (T := reg (ones (ℓ + 1 + (ℓ - 1) / K * (ts.length * K))))
    (by tsimp [hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stH])
  set σ₆ := Function.update σ₅ wE0 emp with hσ₆
  have s7 := runs_clear' (a := 0) wET σ₆
    (T := reg (ones (ℓ + 1 + (ℓ - 1) / K * (ts.length * K) + (ℓ - 1) % K * ts.length)))
    (by tsimp [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stH])
  set σ₇ := Function.update σ₆ wET emp with hσ₇
  have s8 := runs_clear' (a := 0) wP1 σ₇ (T := reg (ones (ℓ + 1)))
    (by tsimp [hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stH])
  set σ₈ := Function.update σ₇ wP1 emp with hσ₈
  have s9 := runs_clear' (a := 0) wM1 σ₈ (T := reg (ones (ℓ - 1)))
    (by tsimp [hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stH])
  set σ₉ := Function.update σ₈ wM1 emp with hσ₉
  have s10 := runs_clear' (a := 0) wM2 σ₉ (T := reg (ones (ℓ - 2)))
    (by tsimp [hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stH])
  set σ₁₀ := Function.update σ₉ wM2 emp with hσ₁₀
  have s11 := runs_clear' (a := 0) wkC σ₁₀ (T := reg [true])
    (by tsimp [hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ, stH])
  set σ₁₁ := Function.update σ₁₀ wkC emp with hσ₁₁
  have s12 := runs_rewind' (a := 0) wO σ₁₁ (L := S.reverse) (R := [])
    (by tsimp [hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 (Runs.then s7
    (Runs.then s8 (Runs.then s9 (Runs.then s10 (Runs.then s11 s12))))))))))).mono (fun τ e => ?_) ?_
  · rw [e]
    funext i; fin_cases i <;> first | rfl | tsimp [hσ₁₁, hσ₁₀, hσ₉, hσ₈, hσ₇, hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁, hσ,
      stH, wIn, decoded, decStart, emp]
  · simp only [costZ, clen, WTape.words, reg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, List.reverse_nil, List.nil_append, List.append_nil, length_ones,
      List.map_reverse, List.sum_reverse]
    have := Nat.mod_le (ℓ - 1) K
    omega

/-! ### The writer -/

/-- The round-script writer on its bank. -/
noncomputable def writer (fwd : Bool) : Cmd 0 102 :=
  .seq prep (.seq hdrW (.seq ((mainFO fwd).map mmap mmap_injective) finish))

/-- The writer's cost. -/
noncomputable def writerCost (fwd : Bool) (p d w ℓ K : ℕ) (ts : List ℕ) (hL : LayoutOK (2 ^ ℓ) ts ℓ K) : ℕ :=
  prepCost ℓ K d ts + 1 + (costH p d ℓ K w ts + 1 + (costM fwd p d w ℓ K ts + 1 +
    costZ ℓ K ts (script fwd p d w ℓ K ts hL)))

/-- `runs_writer`: from the decoded parameters the writer leaves the round script on tape 91 and
restores every other tape. -/
theorem runs_writer (fwd : Bool) {p d ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hd : 1 ≤ d)
    (hD : ts.length = d - 1) :
    Runs (writer fwd) (wIn p d ℓ K w ts) (· = Function.update (wIn p d ℓ K w ts) wO ⟨[], script fwd p d w ℓ K ts hL⟩)
      (writerCost fwd p d w ℓ K ts hL) :=
  Runs.then (runs_prep hL hd hD) (Runs.then (runs_hdrW hL hD) (Runs.then (runs_mainW fwd hL hD) (runs_finish _)))

/-! ### On the word bank -/

variable {tL nL : ℕ}

/-- The writer's tapes in the word bank: the ring product's bank as in `decState`, the script on
named tape 6, the constants on drivers' tapes `141..150`. -/
def wmap (tL nL : ℕ) (i : Fin 102) : Fin (4 + DB tL nL) :=
  if h : i.val < 91 then gslot tL nL ⟨i.val, h⟩
  else if i.val = 91 then drv tL nL (nm tL nL 6)
  else drv tL nL ⟨i.val + 49, by have := i.isLt; unfold DB; omega⟩

theorem wmap_val (i : Fin 102) : (wmap tL nL i).val =
    if i.val < 91 then (if i.val = 87 then 0 else 54 + i.val) else if i.val = 91 then 10 else i.val + 53 := by
  unfold wmap
  split_ifs with h1 h2 <;> simp_all [gslot, pt, drv, nm, Fin.ext_iff] <;> omega

theorem wmap_injective : Function.Injective (wmap tL nL) := by
  intro i j e
  have e' := congrArg Fin.val e
  rw [wmap_val, wmap_val] at e'
  apply Fin.ext
  have := i.isLt; have := j.isLt
  split_ifs at e' <;> omega

theorem gslot_ne_drv {y : Fin 𝕌} {x : Fin (DB tL nL)} (hx : x.val < 50 ∨ 141 ≤ x.val) :
    gslot tL nL y ≠ drv tL nL x := by
  intro e
  have e' := congrArg Fin.val e
  have := y.isLt
  unfold gslot at e'
  split_ifs at e' with h
  · simp [pt, drv] at e'; omega
  · simp [drv] at e'; omega

theorem decState_wmap (p d ℓ K w : ℕ) (ts : List ℕ) (F : List Bool) :
    decState (tL := tL) (nL := nL) p d ℓ K w ts F ∘ wmap tL nL = wIn p d ℓ K w ts := by
  funext i
  simp only [Function.comp_apply, wIn]
  unfold wmap
  split_ifs with h1 h2
  · exact upd_slot _ gslot_injective _ _
  · rw [decState, upd_other _ _ _ _ (fun y => gslot_ne_drv (by simp [nm])), wst_drv]
  · rw [decState, upd_other _ _ _ _ (fun y => gslot_ne_drv (by simp; omega)), wst_drv]

/-- The round-script writer on the word bank. -/
noncomputable def scriptGen (fwd : Bool) (A tL nL : ℕ) : Cmd A (4 + DB tL nL) :=
  .prim (Prim.liftE (Nat.zero_le A) (Prim.ofHoare (compile (a := 0) (by decide) (writer fwd)).2 (by decide)))
    (wmap tL nL) wmap_injective

theorem scriptGen_spec (fwd : Bool) {A : ℕ} {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) {p d w : ℕ}
    (hd : 1 ≤ d) (hD : ts.length = d - 1) :
    ScriptGen fwd (scriptGen fwd A tL nL) hL p d w (writerCost fwd p d w ℓ K ts hL) := by
  intro F
  have hcomp := decState_wmap (tL := tL) (nL := nL) p d ℓ K w ts F
  obtain ⟨τ', k, hx, hq, hk⟩ := runs_writer fwd (p := p) (w := w) hL hd hD
  subst hq
  have hT : HoareTo (compile (a := 0) (by decide) (writer fwd)).2
      (decState (tL := tL) (nL := nL) p d ℓ K w ts F ∘ wmap tL nL)
      (Function.update (wIn p d ℓ K w ts) wO ⟨[], script fwd p d w ℓ K ts hL⟩) k := by
    rw [hcomp]
    exact (compile_correct (by decide) hx).consequence (fun _ h => h) (fun _ h => h) le_rfl
  refine (runs_ofHoare_liftE (Nat.zero_le A) _ (by decide) wmap_injective hT).mono (fun τ e => ?_) hk
  rw [e, ← hcomp, upd_update wmap_injective, upd_comp_self wmap_injective]
  rfl

/-- `scriptGen_fwd`: the forward round-script writer meets `ScriptGen true`. -/
theorem scriptGen_fwd {A : ℕ} {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) {p d w : ℕ}
    (hd : 1 ≤ d) (hD : ts.length = d - 1) :
    ScriptGen true (scriptGen true A tL nL) hL p d w (writerCost true p d w ℓ K ts hL) :=
  scriptGen_spec true hL hd hD

/-- `scriptGen_opp`: the opposite round-script writer meets `ScriptGen false`. -/
theorem scriptGen_opp {A : ℕ} {ℓ K : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) {p d w : ℕ}
    (hd : 1 ≤ d) (hD : ts.length = d - 1) :
    ScriptGen false (scriptGen false A tL nL) hL p d w (writerCost false p d w ℓ K ts hL) :=
  scriptGen_spec false hL hd hD

end ScriptGen

end IntegerMultBounds.Schoenhage
