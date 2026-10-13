module

public import IntegerMultBounds.Schoenhage.SigmaConstsTape

/-! Exact versions of the §6 table generators. `runs_constsTopX`, `runs_rowsGenX`,
`runs_tableGenX` and `runs_topGenX` state the whole bank after the constants, the axis
rows and a round's exponent table, on the paper's parameters, so that the round-script
writer can chain them and restore its scratch tapes. -/

@[expose] public section

set_option maxRecDepth 100000

namespace IntegerMultBounds.Schoenhage

open Machine Strm TwistDescriptors SigmaRowsTape

namespace ScriptParts

/-! ### The constants -/

open SigmaConstsTape in
/-- The constants bank after `constsTop`, from `x`, `K`, `D` and the flags. -/
def constsOut (σ : Fin 20 → WTape) (x K D : ℕ) (flags : List Bool) : Fin 20 → WTape :=
  let q := x / K
  let b := x % K
  let L := (flags.filter id).length
  let v := q * (D * K) + b * D + L - 1
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update σ
    kFuel ⟨List.replicate x [], []⟩) kX (reg (ones b))) kQt (ticks q)) kBt (ticks b)) kDt (ticks D))
    kDK (endv (D * K))) kDqK (endv (q * (D * K)))) kDb (reg (ones (b * D)))) kLc (reg (ones L)))
    kA0 (endv (q * (D * K) + D - 1))) kB0 (endv (D * K - K))) kT0 (endv (v - L)))
    kTop ⟨((List.range L).map fun k => ones (v - k)).reverse, []⟩)
    kF ⟨(flags.map fun b => [b]).reverse, []⟩

open SigmaConstsTape in
set_option maxHeartbeats 16000000 in
/-- `runs_constsTopX`: `constsTop` with its whole result. -/
theorem runs_constsTopX {x K D : ℕ} {flags : List Bool} (hK0 : 0 < K) (σ : Fin 20 → WTape)
    (hX : σ kX = reg (ones x)) (hK : σ kK = reg (ones K)) (hD : σ kD = reg (ones D))
    (hF : σ kF = ⟨[], flags.map fun b => [b]⟩) (hOne : σ kOne = reg (ones 1)) (hFuel : σ kFuel = emp)
    (hQ : σ kQt = emp) (hB : σ kBt = emp) (hDt : σ kDt = emp) (hDK : σ kDK = emp) (hDqK : σ kDqK = emp)
    (hDb : σ kDb = emp) (hLc : σ kLc = emp) (hG : σ kG = emp) (hS : σ kS = emp) (hJ : σ kJ = emp)
    (hA0 : σ kA0 = emp) (hB0 : σ kB0 = emp) (hT0 : σ kT0 = emp) (hTop : σ kTop = emp) :
    Runs constsTop σ (· = constsOut σ x K D flags) (constsTopCost x K D flags.length (flags.filter id).length) := by
  have s1 := runs_consts1 hK0 σ hX hK hD hFuel hQ hB hDt hG hS hJ
  set σ₁ := Function.update (Function.update (Function.update (Function.update (Function.update σ
    kFuel ⟨List.replicate x [], []⟩) kX (reg (ones (x % K)))) kQt (ticks (x / K))) kBt (ticks (x % K)))
    kDt (ticks D) with hσ₁
  have s2 := runs_consts2 (K := K) (D := D) (q := x / K) (b := x % K) σ₁ (by tsimp [hσ₁, hK])
    (by tsimp [hσ₁, hD]) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁]) (by tsimp [hσ₁, hDK])
    (by tsimp [hσ₁, hDqK]) (by tsimp [hσ₁, hDb]) (by tsimp [hσ₁, hJ])
  set σ₂ := Function.update (Function.update (Function.update σ₁ kDK (reg (ones (D * K))))
    kDqK (endv (x / K * (D * K)))) kDb (endv (x % K * D)) with hσ₂
  have s3 := runs_consts3 (flags := flags) σ₂ (by tsimp [hσ₂, hσ₁, hF]) (by tsimp [hσ₂, hσ₁, hOne])
    (by tsimp [hσ₂, hσ₁, hLc]) (by tsimp [hσ₂, hσ₁, hJ])
  set σ₃ := Function.update σ₂ kLc (endv (flags.filter id).length) with hσ₃
  have s4 := runs_consts4 (Q := x / K * (D * K)) (D := D) (DK := D * K) (K := K) (Bd := x % K * D)
    (L := (flags.filter id).length) σ₃ (by tsimp [hσ₃, hσ₂]) (by tsimp [hσ₃, hσ₂, hσ₁, hD])
    (by tsimp [hσ₃, hσ₂, hσ₁, hOne]) (by tsimp [hσ₃, hσ₂]) (by tsimp [hσ₃, hσ₂, hσ₁, hK])
    (by tsimp [hσ₃, hσ₂]) (by tsimp [hσ₃]) (by tsimp [hσ₃, hσ₂, hσ₁, hA0]) (by tsimp [hσ₃, hσ₂, hσ₁, hB0])
    (by tsimp [hσ₃, hσ₂, hσ₁, hT0]) (by tsimp [hσ₃, hσ₂, hσ₁, hS])
  set σ₄ := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update σ₃ kDK (endv (D * K))) kDb (reg (ones (x % K * D))))
    kLc (reg (ones (flags.filter id).length)))
    kA0 (endv (x / K * (D * K) + D - 1))) kB0 (endv (D * K - K)))
    kT0 (endv (x / K * (D * K) + x % K * D + (flags.filter id).length - 1))) kDqK (endv (x / K * (D * K)))
    with hσ₄
  have s5 := runs_topLoop flags (x / K * (D * K) + x % K * D + (flags.filter id).length - 1) σ₄ [] []
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hF]) (by tsimp [hσ₄]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hOne])
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hTop, emp]) (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hS])
    (by tsimp [hσ₄, hσ₃, hσ₂, hσ₁, hJ])
  refine (Runs.seq ((Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun τ e => by rw [e]; exact s5)
    le_rfl)).mono (fun τ e => ?_) ?_
  · rw [e]
    funext i; fin_cases i <;> first | rfl | tsimp [constsOut, hσ₄, hσ₃, hσ₂, hσ₁]
  · unfold constsTopCost
    have : (x / K * (D * K) + x % K * D + (flags.filter id).length - 1) =
        (x / K * (D * K) + x % K * D + (flags.filter id).length - 1) := rfl
    simp only [Nat.mul_comm (x / K) (D * K)] at *
    omega

/-! ### The axis rows -/

/-- The paper's axis rows as words. -/
def rowWords (ts : List ℕ) (ℓ K : ℕ) : List (List Bool) :=
  (List.range ts.length).flatMap fun i => (List.range (ℓ - 1)).map fun h' => ones (paperSigma ts ℓ K i h')

set_option maxHeartbeats 8000000 in
/-- `runs_rowsGenX`: the axis rows of the paper's parameters, with the whole result. -/
theorem runs_rowsGenX {r : ℕ} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (σ : Fin 15 → WTape)
    (hAx : σ gAx = ticks ts.length)
    (hA : σ gA = endv (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1)))
    (hB : σ gB = endv ((ts.length - 1) * K)) (hV : σ gV = emp) (hU : σ gU = emp)
    (hBt : σ gBt = ticks ((ℓ - 1) % K)) (hQt : σ gQt = ticks ((ℓ - 1) / K)) (hKt : σ gKt = ticks K)
    (hD : σ gD = reg (ones ts.length)) (hDK : σ gDK = reg (ones (ts.length * K))) (hK : σ gK = reg (ones K))
    (hOne : σ gOne = reg (ones 1)) (hO : σ gO = emp) (hS : σ gS = emp) (hJ : σ gJ = emp) :
    Runs rowsGen σ (· = Function.update (Function.update (Function.update (Function.update σ gO
        ⟨(rowWords ts ℓ K).reverse, []⟩)
        gA (endv (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1) - ts.length)))
        gB (endv ((ts.length - 1) * K - ts.length * K))) gAx ⟨List.replicate ts.length [], []⟩)
      (ts.length * (axisCost ts.length (ts.length * K) K ((ℓ - 1) % K) ((ℓ - 1) / K)
        (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1)) ((ts.length - 1) * K) + 2)) := by
  refine (runs_axisLoop ts.length _ _ σ [] [] (by rw [hAx]; rfl) hA hB hV hU hBt hQt hKt hD hDK hK hOne
    (by rw [hO]; rfl) hS hJ).mono (fun τ e => ?_) le_rfl
  rw [e]
  have hrows : ((List.range ts.length).flatMap fun i =>
      (axisRow ts.length (ts.length * K) K ((ℓ - 1) % K) ((ℓ - 1) / K)
        (ts.length * ((ℓ - 1) / K) * K + (ts.length - 1) - i) ((ts.length - 1) * K - i * K)).map ones) =
      rowWords ts ℓ K := by
    have h2 := congrArg (fun rows : List (List ℕ) => rows.flatMap fun row => row.map ones) (axisRows_paper hL)
    simp only [axisRows, List.flatMap_map] at h2
    rw [h2, rowWords]
    simp [List.map_map, Function.comp_def]
  rw [hrows]
  simp

/-! ### A round's table below the top -/

set_option maxHeartbeats 8000000 in
/-- `runs_tableGenX`: the exponent table of a round below the top, with the whole result. -/
theorem runs_tableGenX {r : ℕ} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (r' : ℕ) {h : ℕ}
    (hh : h < ℓ - 1) (σ : Fin 14 → WTape) (hAx : σ SigmaTableTape.tAx = ticks ts.length)
    (hH : σ SigmaTableTape.tH = ticks h) (hRest : σ SigmaTableTape.tRest = ticks (ℓ - 1 - 1 - h))
    (hR : σ SigmaTableTape.tR = ⟨[], rowWords ts ℓ K⟩)
    (hS : σ SigmaTableTape.tS = emp) (hX : σ SigmaTableTape.tX = emp) (hW : σ SigmaTableTape.tW = emp)
    (hW0 : σ SigmaTableTape.tW0 = endv (2 * (2 * r' / 2 ^ (h + 1)))) (hT : σ SigmaTableTape.tT = emp)
    (hTab : σ SigmaTableTape.tTab = emp) (hJ : σ SigmaTableTape.tJ = emp) :
    Runs SigmaTableTape.tableGen σ (· = Function.update (Function.update (Function.update σ
        SigmaTableTape.tR ⟨(rowWords ts ℓ K).reverse, []⟩)
        SigmaTableTape.tTab ⟨(tableWords (slotTable (paperPerm hL) r' ts (slotAxes ts h) h)).reverse, []⟩)
        SigmaTableTape.tAx ⟨List.replicate ts.length [], []⟩)
      (ts.length * (SigmaTableTape.roundAxisCost (ℓ - 1) h (Nat.log 2 ts.prod) (2 * (2 * r' / 2 ^ (h + 1))) + 2)) := by
  set rows := (List.range ts.length).map fun i => (List.range (ℓ - 1)).map (paperSigma ts ℓ K i) with hrows
  have hrowsOK : ∀ row ∈ rows, row.length = ℓ - 1 ∧ ∀ v ∈ row, v ≤ Nat.log 2 ts.prod := by
    intro row hrow
    simp only [hrows, List.mem_map, List.mem_range] at hrow
    obtain ⟨i, hi, rfl⟩ := hrow
    refine ⟨by simp, fun v hv => ?_⟩
    simp only [List.mem_map, List.mem_range] at hv
    obtain ⟨h', hh', rfl⟩ := hv
    have := hL.2.1 i hi
    exact (SigmaTableTape.paperSigma_lt hL hi (by omega)).le
  have hwords : rows.flatMap (fun row => row.map ones) = rowWords ts ℓ K := by
    rw [hrows, rowWords]; simp [List.flatMap_map, List.map_map, Function.comp_def]
  have hRw : σ SigmaTableTape.tR = ⟨[], rows.flatMap (fun row => row.map ones) ++ []⟩ := by
    rw [hR, hwords]; simp
  have hlen : rows.length = ts.length := by simp [hrows]
  have s := SigmaTableTape.runs_tableGen (m := ℓ - 1) (h := h) (Vm := Nat.log 2 ts.prod)
    (w0 := 2 * (2 * r' / 2 ^ (h + 1))) hh rows σ [] [] [] [] hrowsOK (by rw [hAx, hlen]; rfl) hH hRest hRw hS
    hX hW hW0 hT (by rw [hTab]; rfl) hJ
  rw [hlen] at s
  refine s.mono (fun τ e => ?_) le_rfl
  rw [e]
  have hIs : ∀ i ∈ slotAxes ts h, i < ts.length ∧ h < axLen ts i := slotAxes_valid ts h
  have htab : (rows.flatMap fun row => tableWords (axisEntries (row.getD h 0) (2 * (2 * r' / 2 ^ (h + 1)))
      (row.take h))) = tableWords (slotTable (paperPerm hL) r' ts (slotAxes ts h) h) := by
    rw [slotTable_paper hL r' hIs, slotAxes_below_top hL hh, slotTableP_rows ts ℓ K r' hh.le]
    simp [hrows, tableWords, List.flatMap_map, List.flatMap_assoc, List.getD_eq_getElem, hh]
  rw [hwords, htab]
  simp

/-! ### The top round's table -/

set_option maxHeartbeats 16000000 in
/-- `runs_topGenX`: the top round's exponent table, with the whole result. -/
theorem runs_topGenX {r : ℕ} {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (r' : ℕ)
    (σ : Fin 14 → WTape)
    (hF : σ SigmaTableTape.tF = ⟨[], (List.range ts.length).map fun i => [decide (axLen ts i = ℓ)]⟩)
    (hFull : σ SigmaTableTape.tFull = ticks (ℓ - 1))
    (hR : σ SigmaTableTape.tR = ⟨[], rowWords ts ℓ K⟩)
    (hTop : σ SigmaTableTape.tTop = ⟨[], (longs ts ℓ).map fun i => ones (paperSigma ts ℓ K i (ℓ - 1))⟩)
    (hS : σ SigmaTableTape.tS = emp) (hX : σ SigmaTableTape.tX = emp) (hW : σ SigmaTableTape.tW = emp)
    (hW0 : σ SigmaTableTape.tW0 = endv (2 * (2 * r' / 2 ^ (ℓ - 1 + 1)))) (hT : σ SigmaTableTape.tT = emp)
    (hTab : σ SigmaTableTape.tTab = emp) (hJ : σ SigmaTableTape.tJ = emp) :
    Runs SigmaTableTape.topGen σ (· = Function.update (Function.update (Function.update (Function.update σ
        SigmaTableTape.tR ⟨(rowWords ts ℓ K).reverse, []⟩)
        SigmaTableTape.tTab
          ⟨(tableWords (slotTable (paperPerm hL) r' ts (slotAxes ts (ℓ - 1)) (ℓ - 1))).reverse, []⟩)
        SigmaTableTape.tTop ⟨((longs ts ℓ).map fun i => ones (paperSigma ts ℓ K i (ℓ - 1))).reverse, []⟩)
        SigmaTableTape.tF ⟨((List.range ts.length).map fun i => [decide (axLen ts i = ℓ)]).reverse, []⟩)
      (ts.length * (SigmaTableTape.topAxisCost (ℓ - 1) (Nat.log 2 ts.prod) (2 * (2 * r' / 2 ^ (ℓ - 1 + 1))) +
        (ℓ - 1) * (Nat.log 2 ts.prod + 18) + 10)) := by
  have hℓ := hL.2.2.2
  set rowf : ℕ → List ℕ := fun i => (List.range (ℓ - 1)).map (paperSigma ts ℓ K i) with hrowf
  set flagf : ℕ → Bool := fun i => decide (axLen ts i = ℓ) with hflagf
  set topf : ℕ → ℕ := fun i => paperSigma ts ℓ K i (ℓ - 1) with htopf
  set L := List.range ts.length with hLdef
  have hlongs : L.filter flagf = longs ts ℓ := rfl
  have hrowsOK : ∀ row ∈ L.map rowf, row.length = ℓ - 1 ∧ ∀ v ∈ row, v ≤ Nat.log 2 ts.prod := by
    intro row hrow
    simp only [hLdef, List.mem_map, List.mem_range] at hrow
    obtain ⟨i, hi, rfl⟩ := hrow
    refine ⟨by simp [hrowf], fun v hv => ?_⟩
    simp only [hrowf, List.mem_map, List.mem_range] at hv
    obtain ⟨h', hh', rfl⟩ := hv
    have := hL.2.1 i hi
    exact (SigmaTableTape.paperSigma_lt hL hi (by omega)).le
  have htopsOK : ∀ x ∈ (L.filter flagf).map topf, x ≤ Nat.log 2 ts.prod := by
    intro x hx
    rw [hlongs] at hx
    simp only [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [longs, List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    exact (SigmaTableTape.paperSigma_lt hL hi.1 (by omega)).le
  have hwords : (L.map rowf).flatMap (fun row => row.map ones) = rowWords ts ℓ K := by
    simp [hLdef, hrowf, rowWords, List.flatMap_map, Function.comp_def]
  have s := SigmaTableTape.runs_topGen (m := ℓ - 1) (Vm := Nat.log 2 ts.prod)
    (w0 := 2 * (2 * r' / 2 ^ (ℓ - 1 + 1)))
    (L.map rowf) (L.map flagf) ((L.filter flagf).map topf) σ [] [] [] [] [] []
    (by simp) (by simp [List.filter_map]) hrowsOK htopsOK
    (by rw [hF]; simp [hLdef, hflagf]) hFull (by rw [hR, hwords]; simp)
    (by rw [hTop, ← hlongs]; simp [htopf]) hS hX hW hW0 hT (by rw [hTab]; rfl) hJ
  have hlen : (L.map rowf).length = ts.length := by simp [hLdef]
  rw [hlen] at s
  refine s.mono (fun τ e => ?_) le_rfl
  rw [e]
  have hIs : ∀ i ∈ slotAxes ts (ℓ - 1), i < ts.length ∧ ℓ - 1 < axLen ts i := slotAxes_valid ts (ℓ - 1)
  have hslot : slotAxes ts (ℓ - 1) = longs ts ℓ := by
    unfold slotAxes longs
    apply List.filter_congr
    intro i hi
    have := hL.2.1 i (List.mem_range.mp hi)
    simp only [decide_eq_decide]
    omega
  have htab : SigmaTableTape.topEntries (2 * (2 * r' / 2 ^ (ℓ - 1 + 1))) (L.map rowf) (L.map flagf)
      ((L.filter flagf).map topf) = slotTable (paperPerm hL) r' ts (slotAxes ts (ℓ - 1)) (ℓ - 1) := by
    rw [slotTable_paper hL r' hIs, hslot, slotTableP_rows ts ℓ K r' le_rfl, SigmaTableTape.topEntries_filter,
      hlongs]
    have htake : ∀ i, List.take (ℓ - 1) ((List.range (ℓ - 1)).map (paperSigma ts ℓ K i)) =
        (List.range (ℓ - 1)).map (paperSigma ts ℓ K i) := fun i => List.take_of_length_le (by simp)
    simp [htake, htopf, hrowf]
  have eC : (List.map ones (List.map topf (List.filter flagf L))).reverse ++ [] =
      ((longs ts ℓ).map fun i => ones (paperSigma ts ℓ K i (ℓ - 1))).reverse := by
    rw [hlongs]; simp [htopf, List.map_map, Function.comp_def]
  have eD : (List.map (fun b => [b]) (List.map flagf L)).reverse ++ [] =
      ((List.range ts.length).map fun i => [decide (axLen ts i = ℓ)]).reverse := by
    simp [hLdef, hflagf, List.map_map, Function.comp_def]
  rw [hwords, htab, eC, eD]
  simp [hLdef]

end ScriptParts

end IntegerMultBounds.Schoenhage
