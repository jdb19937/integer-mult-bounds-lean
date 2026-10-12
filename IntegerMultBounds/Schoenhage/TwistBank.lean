module

public import IntegerMultBounds.Schoenhage.TwistDescriptors

/-! Exact final banks of the slot twist programs, for chaining rounds. `slotTwistClean` and
`slotUntwistClean` run `slotTwist` or `slotUntwist` and then rewind the tick tape and clear the
four descriptor lists. From the same start as `runs_slotTwist` the whole 29-tape bank ends equal
to the start except on three tapes (`runs_slotTwistClean`, `runs_slotUntwistClean`): the input
tape `0` has moved past the array words, the output tape `1` holds the twisted records, and the
address counter `15` holds `bits n M`, which is `bits n 0` again when `M = 2^n`
(`bits_pow_self`). The table tape `16` keeps this round's table and the tick tape `17` its `M`
ticks; a driver replaces the table between rounds. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct NLogN

namespace TwistDescriptors

theorem Runs.map_eq {a t t' : ℕ} (f : Fin t → Fin t') (hf : Function.Injective f) {c : Cmd a t}
    {τ : Fin t' → WTape} {σ₁ : Fin t → WTape} {B : ℕ} (h : Runs c (τ ∘ f) (· = σ₁) B)
    (τ₁ : Fin t' → WTape) (h1 : τ₁ ∘ f = σ₁) (h2 : ∀ x, (∀ y, f y ≠ x) → τ₁ x = τ x) :
    Runs (c.map f hf) τ (· = τ₁) B := by
  refine (h.map f hf τ rfl).mono (fun τ' ⟨e, o⟩ => ?_) le_rfl
  funext x
  by_cases hx : ∃ y, f y = x
  · obtain ⟨y, rfl⟩ := hx
    exact (congrFun e y).trans (congrFun h1 y).symm
  · simp only [not_exists] at hx
    rw [o x hx, h2 x hx]

theorem bits_pow_self (n : ℕ) : bits n (2 ^ n) = bits n 0 := by
  rw [← bits_mod n (2 ^ n), Nat.mod_self]

/-- After a twist: rewind the ticks, clear the four descriptor lists. -/
noncomputable def cleanup : Cmd 0 29 :=
  .seq (rewind 17) <| .seq (clear 11) <| .seq (clear 12) <| .seq (clear 13) (clear 14)

/-- `slotTwist` with its bank restored. -/
noncomputable def slotTwistClean : Cmd 0 29 := .seq slotTwist cleanup

/-- `slotUntwist` with its bank restored. -/
noncomputable def slotUntwistClean : Cmd 0 29 := .seq slotUntwist cleanup

/-- The rewinds of the four descriptor lists. -/
noncomputable def rewinds : Cmd 0 29 := .seq (rewind 11) <| .seq (rewind 12) <| .seq (rewind 13) (rewind 14)

theorem clen_hdW {r : ℕ} (ps : List (ℕ × Rec r)) :
    clen (ps.map fun p => TwistArray.hdW r p.1) ≤ ps.length * (2 * r + 1) := by
  have := clen_map_le ps (fun p => TwistArray.hdW r p.1) (2 * r) (fun p _ => by simp [TwistArray.hdW, ones])
  simpa using this

theorem clen_tlW {r : ℕ} [NeZero r] (ps : List (ℕ × Rec r)) :
    clen (ps.map fun p => TwistArray.tlW r p.1) ≤ ps.length * (2 * r + 1) := by
  have := clen_map_le ps (fun p => TwistArray.tlW r p.1) (2 * r) (fun p _ => by
    simp [TwistArray.tlW, ones]; have := Nat.mod_lt p.1 (NeZero.pos r); omega)
  simpa using this

theorem clen_hfW {r : ℕ} (ps : List (ℕ × Rec r)) :
    clen (ps.map fun p => TwistArray.hfW r p.1) ≤ ps.length * (1 + 1) := by
  have := clen_map_le ps (fun p => TwistArray.hfW r p.1) 1 (fun p _ => by simp [TwistArray.hfW])
  simpa using this

theorem clen_tfW {r : ℕ} (ps : List (ℕ × Rec r)) :
    clen (ps.map fun p => TwistArray.tfW r p.1) ≤ ps.length * (1 + 1) := by
  have := clen_map_le ps (fun p => TwistArray.tfW r p.1) 1 (fun p _ => by simp [TwistArray.tfW])
  simpa using this

theorem clen_replicate_nil' (M : ℕ) : clen (List.replicate M ([] : List Bool)) = M := by
  simp [clen]

set_option maxHeartbeats 32000000 in
/-- `runs_bank`: a descriptor program `G` that leaves its four lists for `ps`, its ticks consumed
and its counter at `bits n M`, followed by the rewinds, the array monomial and the cleanup, returns
the whole bank to its start except the input, output and counter tapes. -/
theorem runs_bank {r : ℕ} [NeZero r] (G : Cmd 0 18) (n w M : ℕ) (σ : Fin 29 → WTape) (B : ℕ)
    (ps : List (ℕ × Rec r)) (hps : ps.length = M)
    (hG : Runs G (σ ∘ φ) (· = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (σ ∘ φ) gY (reg (bits n M))) gC ⟨List.replicate M [], []⟩)
      gdH ⟨(ps.map fun p => TwistArray.hdW r p.1).reverse, []⟩)
      gdT ⟨(ps.map fun p => TwistArray.tlW r p.1).reverse, []⟩)
      gdF ⟨(ps.map fun p => TwistArray.hfW r p.1).reverse, []⟩)
      gdG ⟨(ps.map fun p => TwistArray.tfW r p.1).reverse, []⟩) B)
    (hI : TwistArray.Idle r (σ ∘ ψ)) {Lx R D : List (List Bool)}
    (hX : σ 0 = ⟨Lx, TwistArray.arrWords w (ps.map Prod.snd) ++ R⟩) (hO : σ 1 = ⟨D, []⟩)
    (hC : σ 17 = ⟨[], List.replicate M []⟩) (h11 : σ 11 = emp) (h12 : σ 12 = emp) (h13 : σ 13 = emp)
    (h14 : σ 14 = emp) :
    Runs (.seq (.seq (G.map φ φ_injective) (.seq rewinds (TwistArray.twistArray.map ψ ψ_injective))) cleanup) σ
      (· = Function.update (Function.update (Function.update σ
        0 ⟨(TwistArray.arrWords w (ps.map Prod.snd)).reverse ++ Lx, R⟩)
        1 ⟨(TwistArray.arrWords w (ps.map fun p => twistRec p.1 p.2)).reverse ++ D, []⟩)
        15 (reg (bits n M)))
      (B + 1 + (M * (4 * r + 6) + 16 + 1 + M * (2 * r * (25 * w + 200) + 50 * r + 402)) + 1 +
        (M * (8 * r + 13) + 16)) := by
  set LH := ps.map fun p => TwistArray.hdW r p.1
  set LT := ps.map fun p => TwistArray.tlW r p.1
  set LF := ps.map fun p => TwistArray.hfW r p.1
  set LG := ps.map fun p => TwistArray.tfW r p.1
  -- the descriptor program
  set τ₁ : Fin 29 → WTape := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update σ 15 (reg (bits n M))) 17 ⟨List.replicate M [], []⟩)
    11 ⟨LH.reverse, []⟩) 12 ⟨LT.reverse, []⟩) 13 ⟨LF.reverse, []⟩) 14 ⟨LG.reverse, []⟩ with hτ₁
  have s1 : Runs (G.map φ φ_injective) σ (· = τ₁) B := by
    refine Runs.map_eq φ φ_injective hG τ₁ ?_ ?_
    · funext y
      fin_cases y <;> simp (config := {decide := true}) [hτ₁, φ]
    · intro x hx
      have e15 : x ≠ 15 := fun h => hx 0 (by rw [h]; rfl)
      have e17 : x ≠ 17 := fun h => hx 2 (by rw [h]; rfl)
      have e11 : x ≠ 11 := fun h => hx 14 (by rw [h]; rfl)
      have e12 : x ≠ 12 := fun h => hx 15 (by rw [h]; rfl)
      have e13 : x ≠ 13 := fun h => hx 16 (by rw [h]; rfl)
      have e14 : x ≠ 14 := fun h => hx 17 (by rw [h]; rfl)
      simp only [hτ₁]
      rw [Function.update_of_ne e14, Function.update_of_ne e13, Function.update_of_ne e12,
        Function.update_of_ne e11, Function.update_of_ne e17, Function.update_of_ne e15]
  -- the rewinds
  set τ₂ : Fin 29 → WTape := Function.update (Function.update (Function.update (Function.update τ₁
    11 ⟨[], LH⟩) 12 ⟨[], LT⟩) 13 ⟨[], LF⟩) 14 ⟨[], LG⟩ with hτ₂
  have s2 : Runs rewinds τ₁ (· = τ₂) (M * (4 * r + 6) + 16) := by
    apply Runs.of_wp
    simp only [rewinds, WP, wp_rewind]
    refine ⟨?_, ?_⟩
    · funext x; fin_cases x <;> simp (config := {decide := true}) [hτ₂, hτ₁]
    · have c1 : clen LH ≤ ps.length * (2 * r + 1) := clen_hdW ps
      have c2 : clen LT ≤ ps.length * (2 * r + 1) := clen_tlW ps
      have c3 : clen LF ≤ ps.length * (1 + 1) := clen_hfW ps
      have c4 : clen LG ≤ ps.length * (1 + 1) := clen_tfW ps
      simp (config := {decide := true}) [hτ₁, clen_reverse]
      rw [hps] at c1 c2 c3 c4
      have : M * (2 * r + 1) + M * (2 * r + 1) + M * (1 + 1) + M * (1 + 1) = M * (4 * r + 6) := by ring
      omega
  -- the array monomial
  have hτ₂ψ : ∀ x : Fin 15, x.val < 11 → τ₂ (ψ x) = σ (ψ x) := by
    intro x hx
    fin_cases x <;> first
      | exact absurd hx (by decide)
      | simp (config := {decide := true}) [hτ₂, hτ₁, ψ]
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ := hI
  have hI₂ : TwistArray.Idle r (τ₂ ∘ ψ) := ⟨(hτ₂ψ 3 (by decide)).trans i1, (hτ₂ψ 2 (by decide)).trans i2,
    (hτ₂ψ 4 (by decide)).trans i3, (hτ₂ψ 5 (by decide)).trans i4, (hτ₂ψ 6 (by decide)).trans i5,
    (hτ₂ψ 7 (by decide)).trans i6, (hτ₂ψ 8 (by decide)).trans i7, (hτ₂ψ 9 (by decide)).trans i8,
    (hτ₂ψ 10 (by decide)).trans i9⟩
  have s3a := TwistArray.runs_twistArray w ps (τ₂ ∘ ψ) Lx R [] [] [] [] D hI₂
    (by rw [Function.comp_apply, hτ₂ψ 0 (by decide)]; exact hX)
    (by rw [Function.comp_apply, hτ₂ψ 1 (by decide)]; exact hO)
    (by simp (config := {decide := true}) [hτ₂, ψ, Function.update_apply, LH, LT, LF, LG])
    (by simp (config := {decide := true}) [hτ₂, ψ, Function.update_apply, LH, LT, LF, LG])
    (by simp (config := {decide := true}) [hτ₂, ψ, Function.update_apply, LH, LT, LF, LG])
    (by simp (config := {decide := true}) [hτ₂, ψ, Function.update_apply, LH, LT, LF, LG])
  set τ₃ : Fin 29 → WTape := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update τ₂
      0 ⟨(TwistArray.arrWords w (ps.map Prod.snd)).reverse ++ Lx, R⟩)
      1 ⟨(TwistArray.arrWords w (ps.map fun p => twistRec p.1 p.2)).reverse ++ D, []⟩)
      11 ⟨LH.reverse ++ [], []⟩) 12 ⟨LT.reverse ++ [], []⟩) 13 ⟨LF.reverse ++ [], []⟩)
      14 ⟨LG.reverse ++ [], []⟩ with hτ₃
  have s3 : Runs (TwistArray.twistArray.map ψ ψ_injective) τ₂ (· = τ₃)
      (ps.length * (2 * r * (25 * w + 200) + 50 * r + 402)) := by
    refine Runs.map_eq ψ ψ_injective s3a τ₃ ?_ ?_
    · funext y
      fin_cases y <;> simp (config := {decide := true}) [hτ₃, ψ, LH, LT, LF, LG]
    · intro x hx
      have e0 : x ≠ 0 := fun h => hx 0 (by rw [h]; rfl)
      have e1 : x ≠ 1 := fun h => hx 1 (by rw [h]; rfl)
      have e11 : x ≠ 11 := fun h => hx 11 (by rw [h]; rfl)
      have e12 : x ≠ 12 := fun h => hx 12 (by rw [h]; rfl)
      have e13 : x ≠ 13 := fun h => hx 13 (by rw [h]; rfl)
      have e14 : x ≠ 14 := fun h => hx 14 (by rw [h]; rfl)
      simp only [hτ₃]
      rw [Function.update_of_ne e14, Function.update_of_ne e13, Function.update_of_ne e12,
        Function.update_of_ne e11, Function.update_of_ne e1, Function.update_of_ne e0]
  -- the cleanup
  set τ₄ : Fin 29 → WTape := Function.update (Function.update (Function.update σ
    0 ⟨(TwistArray.arrWords w (ps.map Prod.snd)).reverse ++ Lx, R⟩)
    1 ⟨(TwistArray.arrWords w (ps.map fun p => twistRec p.1 p.2)).reverse ++ D, []⟩)
    15 (reg (bits n M)) with hτ₄
  have s4 : Runs cleanup τ₃ (· = τ₄) (M * (8 * r + 13) + 16) := by
    apply Runs.of_wp
    simp only [cleanup, WP, wp_rewind, wp_clear]
    refine ⟨?_, ?_⟩
    · funext x
      fin_cases x <;> simp (config := {decide := true}) [hτ₄, hτ₃, hτ₂, hτ₁, hC,
        h11, h12, h13, h14, emp]
    · have c1 : clen LH ≤ ps.length * (2 * r + 1) := clen_hdW ps
      have c2 : clen LT ≤ ps.length * (2 * r + 1) := clen_tlW ps
      have c3 : clen LF ≤ ps.length * (1 + 1) := clen_hfW ps
      have c4 : clen LG ≤ ps.length * (1 + 1) := clen_tfW ps
      rw [hps] at c1 c2 c3 c4
      simp (config := {decide := true}) [hτ₃, hτ₂, hτ₁, WTape.words,
        clen_replicate_nil']
      have : 2 * (M * (2 * r + 1)) + 2 * (M * (2 * r + 1)) + 2 * (M * (1 + 1)) + 2 * (M * (1 + 1)) + M =
        M * (8 * r + 13) := by ring
      omega
  rw [hps] at s3
  exact Runs.then (Runs.then s1 (Runs.then s2 s3)) s4

/-- The step bound of a clean slot twist over `M` records with exponent table `es`. -/
def cleanCost (n r w M : ℕ) (es : List Entry) : ℕ :=
  M * (recordCost n r es [] + 2) + 1 + (M * (4 * r + 6) + 16 + 1 + M * (2 * r * (25 * w + 200) + 50 * r + 402)) +
    1 + (M * (8 * r + 13) + 16)

theorem descRev_mapIdx {r : ℕ} (D : ℕ → List Bool) (E : ℕ → ℕ) (q : ℕ → List Bool) (fs : List (Rec r))
    (hD : ∀ y, D y = q (E y)) :
    descRev D 0 fs.length ++ [] = ((fs.mapIdx fun y g => (E y, g)).map fun p => q p.1).reverse := by
  rw [List.append_nil]
  simp only [descRev, zero_add]
  congr 1
  apply List.ext_getElem (by simp); intro k h1 h2; simp [hD]

theorem mapIdx_snd {r : ℕ} (E : ℕ → ℕ) (fs : List (Rec r)) :
    (fs.mapIdx fun y g => (E y, g)).map Prod.snd = fs := by
  apply List.ext_getElem (by simp); intro k h1 h2; simp

set_option maxHeartbeats 16000000 in
/-- `runs_slotTwistClean`: from the start of `runs_slotTwist`, the clean twist leaves the whole bank
as it found it except the input tape `0` (moved past the array words), the output tape `1` (the
twisted records' words) and the address counter `15` (`bits n M`). -/
theorem runs_slotTwistClean {n : ℕ} (π : BitPerm n) {r : ℕ} [NeZero r] (ts Is : List ℕ) (h : ℕ)
    (hpos : ∀ i ∈ Is, axOff ts i + h < n) (p w : ℕ) (fs : List (Rec r)) (σ : Fin 29 → WTape)
    (hgen : GenPre π r ts Is h fs.length (σ ∘ φ)) (hI : TwistArray.Idle r (σ ∘ ψ))
    {Lx R D : List (List Bool)} (hX : σ 0 = ⟨Lx, TwistArray.arrWords w fs ++ R⟩) (hO : σ 1 = ⟨D, []⟩) :
    arrayVec p (TwistRound.twistRecs (slotExp π r ts Is h) fs) = twist (slotExp π r ts Is h) (arrayVec p fs) ∧
    Runs slotTwistClean σ
      (· = Function.update (Function.update (Function.update σ
        0 ⟨(TwistArray.arrWords w fs).reverse ++ Lx, R⟩)
        1 ⟨(TwistArray.arrWords w (TwistRound.twistRecs (slotExp π r ts Is h) fs)).reverse ++ D, []⟩)
        15 (reg (bits n fs.length)))
      (cleanCost n r w fs.length (slotTable π r ts Is h)) := by
  have hr : 1 ≤ r := NeZero.one_le
  refine ⟨TwistRound.arrayVec_twist p _ fs, ?_⟩
  obtain ⟨hR, hY, hT, hA, hE, hC, hH, hDT, hF, hG⟩ := hgen
  set f := slotExp π r ts Is h
  set M := fs.length
  set ps : List (ℕ × Rec r) := fs.mapIdx fun y g => (TwistRound.twistExp r (f y), g) with hpsdef
  have hps : ps.length = M := by simp [ps, M]
  have hok := slotTable_ok π r ts Is h hpos
  have s0 := runs_gen (LC := []) (LH := []) (LT := []) (LF := []) (LG := []) hr hok M (σ ∘ φ) 0
    hR hY hT hA hE hC hH hDT hF hG
  have hG' : Runs gen (σ ∘ φ) (· = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (σ ∘ φ) gY (reg (bits n M))) gC ⟨List.replicate M [], []⟩)
      gdH ⟨(ps.map fun p => TwistArray.hdW r p.1).reverse, []⟩)
      gdT ⟨(ps.map fun p => TwistArray.tlW r p.1).reverse, []⟩)
      gdF ⟨(ps.map fun p => TwistArray.hfW r p.1).reverse, []⟩)
      gdG ⟨(ps.map fun p => TwistArray.tfW r p.1).reverse, []⟩) (M * (recordCost n r (slotTable π r ts Is h) [] + 2)) := by
    refine s0.mono (fun τ e => ?_) le_rfl
    rw [e, zero_add, List.append_nil,
      descRev_mapIdx _ _ _ fs (fun y => (desc_slot π hr ts Is h hpos y).1),
      descRev_mapIdx _ _ _ fs (fun y => (desc_slot π hr ts Is h hpos y).2.1),
      descRev_mapIdx _ _ _ fs (fun y => (desc_slot π hr ts Is h hpos y).2.2.1),
      descRev_mapIdx _ _ _ fs (fun y => (desc_slot π hr ts Is h hpos y).2.2.2)]
  have hX' : σ 0 = ⟨Lx, TwistArray.arrWords w (ps.map Prod.snd) ++ R⟩ := by rw [hpsdef, mapIdx_snd]; exact hX
  have hb := runs_bank gen n w M σ _ ps hps hG' hI hX' hO hC hH hDT hF hG
  have htw : ps.map (fun p => twistRec p.1 p.2) = TwistRound.twistRecs f fs := by
    apply List.ext_getElem (by simp [ps, TwistRound.twistRecs]); intro k h1 h2; simp [ps, TwistRound.twistRecs]
  rw [mapIdx_snd, htw] at hb
  exact hb

set_option maxHeartbeats 16000000 in
/-- `runs_slotUntwistClean`: the opposite round's clean inverse monomial, with the same exact bank. -/
theorem runs_slotUntwistClean {n : ℕ} (π : BitPerm n) {r : ℕ} [NeZero r] (ts Is : List ℕ) (h : ℕ)
    (hpos : ∀ i ∈ Is, axOff ts i + h < n) (p w : ℕ) (fs : List (Rec r)) (σ : Fin 29 → WTape)
    (hgen : GenPre π r ts Is h fs.length (σ ∘ φ)) (hI : TwistArray.Idle r (σ ∘ ψ))
    {Lx R D : List (List Bool)} (hX : σ 0 = ⟨Lx, TwistArray.arrWords w fs ++ R⟩) (hO : σ 1 = ⟨D, []⟩) :
    arrayVec p (TwistRound.untwistRecs (slotExp π r ts Is h) fs) = untwist (slotExp π r ts Is h) (arrayVec p fs) ∧
    Runs slotUntwistClean σ
      (· = Function.update (Function.update (Function.update σ
        0 ⟨(TwistArray.arrWords w fs).reverse ++ Lx, R⟩)
        1 ⟨(TwistArray.arrWords w (TwistRound.untwistRecs (slotExp π r ts Is h) fs)).reverse ++ D, []⟩)
        15 (reg (bits n fs.length)))
      (cleanCost n r w fs.length (slotTable π r ts Is h)) := by
  have hr : 1 ≤ r := NeZero.one_le
  refine ⟨TwistRound.arrayVec_untwist p _ fs, ?_⟩
  obtain ⟨hR, hY, hT, hA, hE, hC, hH, hDT, hF, hG⟩ := hgen
  set f := slotExp π r ts Is h
  set M := fs.length
  set ps : List (ℕ × Rec r) := fs.mapIdx fun y g => (f y % (2 * r), g) with hpsdef
  have hps : ps.length = M := by simp [ps, M]
  have hok := slotTable_ok π r ts Is h hpos
  have s0 := runs_genOpp (LC := []) (LH := []) (LT := []) (LF := []) (LG := []) hr hok M (σ ∘ φ) 0
    hR hY hT hA hE hC hH hDT hF hG
  have hG' : Runs genOpp (σ ∘ φ) (· = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (σ ∘ φ) gY (reg (bits n M))) gC ⟨List.replicate M [], []⟩)
      gdH ⟨(ps.map fun p => TwistArray.hdW r p.1).reverse, []⟩)
      gdT ⟨(ps.map fun p => TwistArray.tlW r p.1).reverse, []⟩)
      gdF ⟨(ps.map fun p => TwistArray.hfW r p.1).reverse, []⟩)
      gdG ⟨(ps.map fun p => TwistArray.tfW r p.1).reverse, []⟩) (M * (recordCost n r (slotTable π r ts Is h) [] + 2)) := by
    refine s0.mono (fun τ e => ?_) le_rfl
    rw [e, zero_add, List.append_nil,
      descRev_mapIdx _ _ _ fs (fun y => (desc_slotOpp π hr ts Is h hpos y).1),
      descRev_mapIdx _ _ _ fs (fun y => (desc_slotOpp π hr ts Is h hpos y).2.1),
      descRev_mapIdx _ _ _ fs (fun y => (desc_slotOpp π hr ts Is h hpos y).2.2.1),
      descRev_mapIdx _ _ _ fs (fun y => (desc_slotOpp π hr ts Is h hpos y).2.2.2)]
  have hX' : σ 0 = ⟨Lx, TwistArray.arrWords w (ps.map Prod.snd) ++ R⟩ := by rw [hpsdef, mapIdx_snd]; exact hX
  have hb := runs_bank genOpp n w M σ _ ps hps hG' hI hX' hO hC hH hDT hF hG
  have htw : ps.map (fun p => twistRec p.1 p.2) = TwistRound.untwistRecs f fs := by
    apply List.ext_getElem (by simp [ps, TwistRound.untwistRecs]); intro k h1 h2; simp [ps, TwistRound.untwistRecs]
  rw [mapIdx_snd, htw] at hb
  exact hb

end TwistDescriptors

end IntegerMultBounds.Schoenhage
