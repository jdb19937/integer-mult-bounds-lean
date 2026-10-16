module

public import IntegerMultBounds.Schoenhage.DriverLoop
public import IntegerMultBounds.Schoenhage.DriverLayout

/-! The forward and opposite transform drivers (§6 task 6). The forward driver moves the array to
the paper's layout, then runs the forward rounds slot by slot (`fwdDriver`); the opposite driver runs
the opposite rounds, then moves the array back to the natural order (`oppDriver`). Started on the
drivers' bank with the array, the record width, the round script and the layout script
(`fwdStart`, `oppStart`), with every chunk-group layer call met (`LayerCalls`), each ends with disk
records within `√2 ℓ 2^(-p)` of the exact transform, the scripts consumed and every other tape as it
was (`runs_fwdDriver`, `runs_oppDriver`), within an explicit step count. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct Resampling AxisDriver LayoutMachines
open Networks.Shared50ModularControl (prime)

variable {A tL : ℕ}

/-- The layout scripts' cost constant. -/
noncomputable def layoutC : ℝ := Classical.choose (driveCost_layout_le layoutSpec)

/-- The cost bound of the layout or the undo script. -/
noncomputable def layoutCost (r w : ℕ) (ts : List ℕ) (ℓ K : ℕ) : ℕ :=
  ⌈(layoutMoves ts ℓ K).length * (layoutC * (2 * r * w * 2 ^ addrBits ts : ℕ) + 3) +
    (layoutSwaps ts ℓ K).length *
      (layoutC * (2 * r * w * 2 ^ addrBits ts : ℕ) * ((max 1 K : ℕ) : ℝ) ^ Parameters.tau + 3)⌉₊

/-- The forward driver: the layout moves, then the forward rounds. -/
noncomputable def fwdDriver {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A) (hP : prime ≤ A) :
    Cmd A (DB tL NL) :=
  .seq (layoutStep A tL hP) (fwdRounds M ht haA)

/-- The opposite driver: the opposite rounds, then the undo moves. -/
noncomputable def oppDriver {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A) (hP : prime ≤ A) :
    Cmd A (DB tL NL) :=
  .seq (oppRounds M ht haA) (layoutStep A tL hP)

variable {r : ℕ} [NeZero r]

/-- The forward driver's start: array `fs` on named tape 0, `ones w` on named tape 2, the forward round
script on named tape 6, the layout script on named tape 7, the twist block at rest. -/
noncomputable def fwdStart {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (p d w : ℕ) (fs : List (Rec r)) :
    Fin (DB tL NL) → WTape :=
  dstate tL NL (rnamed w (array w fs) ⟨[], fwdScript p d r w (paperPerm hL) ts ℓ K⟩ ⟨[], layoutWords r w ts ℓ K⟩)
    (rest r ts)

/-- The forward driver's end: array `gs`, both scripts consumed. -/
noncomputable def fwdEnd {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (p d w : ℕ) (gs : List (Rec r)) :
    Fin (DB tL NL) → WTape :=
  dstate tL NL (rnamed w (array w gs) ⟨(fwdScript p d r w (paperPerm hL) ts ℓ K).reverse, []⟩
    ⟨(layoutWords r w ts ℓ K).reverse, []⟩) (rest r ts)

/-- The opposite driver's start: as the forward one with the opposite round script and the undo script. -/
noncomputable def oppStart {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (p d w : ℕ) (us : List (Rec r)) :
    Fin (DB tL NL) → WTape :=
  dstate tL NL (rnamed w (array w us) ⟨[], oppScript p d r w (paperPerm hL) ts ℓ K⟩ ⟨[], undoWords r w ts ℓ K⟩)
    (rest r ts)

/-- The opposite driver's end. -/
noncomputable def oppEnd {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) (p d w : ℕ) (gs : List (Rec r)) :
    Fin (DB tL NL) → WTape :=
  dstate tL NL (rnamed w (array w gs) ⟨(oppScript p d r w (paperPerm hL) ts ℓ K).reverse, []⟩
    ⟨(undoWords r w ts ℓ K).reverse, []⟩) (rest r ts)

/-- The zero record. -/
def zeroRec (r : ℕ) : Rec r := (fun _ => 0, fun _ => 0)

omit [NeZero r] in
theorem ofFn_getD {N : ℕ} (fs : List (Rec r)) (hl : fs.length = N) :
    List.ofFn (fun y : Fin N => fs.getD y (zeroRec r)) = fs := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp [List.getElem?_eq_getElem h2]

omit [NeZero r] in
theorem arrayVec_ofFn (p : ℕ) {N : ℕ} (g : ℕ → Rec r) {y : ℕ} (hy : y < N) :
    arrayVec p (List.ofFn fun x : Fin N => g x) y = gridPoly p (g y).1 (g y).2 := by
  simp [arrayVec, hy]

omit [NeZero r] in
theorem arrayVec_getD_zero (p : ℕ) {fs : List (Rec r)} {y : ℕ} (hy : y < fs.length) :
    gridPoly p (fs.getD y (zeroRec r)).1 (fs.getD y (zeroRec r)).2 = arrayVec p fs y := by
  simp [arrayVec, List.getElem?_eq_getElem hy]

omit [NeZero r] in
theorem driveCost_le_layout {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {w : ℕ} (hw : 0 < 2 * r * w)
    (z : ℕ → Rec r) :
    driveCost layoutSpec ((layoutOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w)))
        (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y)) ≤ layoutCost r w ts ℓ K ∧
      driveCost layoutSpec ((undoOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w)))
        (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y))) ≤ layoutCost r w ts ℓ K := by
  obtain ⟨-, hb⟩ := Classical.choose_spec (driveCost_layout_le layoutSpec)
  obtain ⟨h1, h2⟩ := hb hL hw z
  exact ⟨by exact_mod_cast h1.trans (Nat.le_ceil _), by exact_mod_cast h2.trans (Nat.le_ceil _)⟩

set_option maxHeartbeats 4000000 in
theorem runs_fwdDriver {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A) (hP : prime ≤ A)
    {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {p d w CL : ℕ} (hpw : p + 2 ≤ w)
    (hLayer : LayerCalls M ht r p d w ts ℓ K CL) (fs : List (Rec r))
    (hfl : fs.length = ts.prod) (hfd : ∀ f ∈ fs, DiskGrid p f.1 f.2) :
    Runs (fwdDriver M ht haA hP) (fwdStart (tL := tL) hL p d w fs)
      (fun σ => ∃ gs : List (Rec r), gs.length = ts.prod ∧ (∀ g ∈ gs, DiskGrid p g.1 g.2) ∧
        Close ts.prod (arrayVec p gs)
          (fwdExact ts ((paperPerm hL).toPerm (powAxes_prod_pow hL.1)) (arrayVec p fs)) (Real.sqrt 2 * ℓ / 2 ^ p) ∧
        σ = fwdEnd hL p d w gs)
      (layoutCost r w ts ℓ K + 1 + fwdRoundsCost hL p d w CL) := by
  have hpow := powAxes_prod_pow hL.1
  have hr : 1 ≤ r := NeZero.one_le
  have hw : 0 < 2 * r * w := Nat.mul_pos (by omega) (by omega)
  have hfn : fs.length = 2 ^ Nat.log 2 ts.prod := hfl.trans hpow
  let z : ℕ → Rec r := fun y => fs.getD y (zeroRec r)
  have hfz : List.ofFn (fun y : Fin (2 ^ addrBits ts) => z y) = fs := ofFn_getD fs hfn
  have s1 := runs_layoutStep (A := A) (tL := tL) hP hL hw z
    (rnamed w (array w fs) ⟨[], fwdScript p d r w (paperPerm hL) ts ℓ K⟩ ⟨[], layoutWords r w ts ℓ K⟩)
    (rest r ts) [] (by simp [rnamed, hfz]) (by simp (config := {decide := true}) [rnamed])
  let R₀ := List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y)
  have hR₀l : R₀.length = ts.prod := by simp only [R₀, List.length_ofFn]; exact hpow.symm
  have hR₀d : ∀ f ∈ R₀, DiskGrid p f.1 f.2 := by
    intro f hf
    simp only [R₀, List.mem_ofFn] at hf
    obtain ⟨y, rfl⟩ := hf
    have hy : (paperPerm hL).logi y < fs.length := lt_of_lt_of_eq ((paperPerm hL).logi_lt _) hfn.symm
    simp only [z, List.getD_eq_getElem _ _ hy]
    exact hfd _ (List.getElem_mem hy)
  have hv : Function.update (Function.update
      (rnamed w (array w fs) ⟨[], fwdScript p d r w (paperPerm hL) ts ℓ K⟩ ⟨[], layoutWords r w ts ℓ K⟩)
      0 (reg (array w R₀))) 7 ⟨(layoutWords r w ts ℓ K).reverse ++ [], []⟩ =
      rnamed w (array w R₀) ⟨[], fwdScript p d r w (paperPerm hL) ts ℓ K⟩ ⟨(layoutWords r w ts ℓ K).reverse, []⟩ := by
    funext i
    fin_cases i <;> simp (config := {decide := true}) [rnamed]
  rw [hv] at s1
  have s2 := runs_fwdRounds (nL := NL) M ht haA hL hpw hLayer R₀ hR₀l hR₀d ⟨(layoutWords r w ts ℓ K).reverse, []⟩
  refine (Runs.then s1 s2).mono (fun σ ⟨R, hc, hl, hd, e⟩ => ⟨R, hl, hd, ?_, e⟩) ?_
  · have h0 : Agree (Nat.log 2 ts.prod) (arrayVec p R₀) fun y => arrayVec p fs ((paperPerm hL).logi y) := by
      intro y hy
      show arrayVec p (List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y)) y = _
      rw [arrayVec_ofFn p (fun x => z ((paperPerm hL).logi x)) hy, arrayVec_getD_zero p (lt_of_lt_of_eq ((paperPerm hL).logi_lt _) hfn.symm)]
    exact (forward_close hL.1 hpow (paperPerm hL) (H := ℓ) (fun i hi => by rcases hL.2.1 i hi with h | h <;> omega)
      (by have := hL.2.2.2; omega) p fs R₀ R hfd (hl.trans hpow) h0 hc).1
  · have := (driveCost_le_layout hL hw z).1
    omega

set_option maxHeartbeats 4000000 in
theorem runs_oppDriver {q a : ℕ} (M : Program tL q a) (ht : 2 ≤ tL) (haA : a ≤ A) (hP : prime ≤ A)
    {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {p d w CL : ℕ} (hpw : p + 2 ≤ w)
    (hLayer : LayerCalls M ht r p d w ts ℓ K CL) (us : List (Rec r))
    (hul : us.length = ts.prod) (hud : ∀ u ∈ us, DiskGrid p u.1 u.2) :
    Runs (oppDriver M ht haA hP) (oppStart (tL := tL) hL p d w us)
      (fun σ => ∃ gs : List (Rec r), gs.length = ts.prod ∧ (∀ g ∈ gs, DiskGrid p g.1 g.2) ∧
        Close ts.prod (arrayVec p gs)
          (oppExact ts ((paperPerm hL).toPerm (powAxes_prod_pow hL.1)) (arrayVec p us)) (Real.sqrt 2 * ℓ / 2 ^ p) ∧
        σ = oppEnd hL p d w gs)
      (oppRoundsCost hL p d w CL + 1 + layoutCost r w ts ℓ K) := by
  have hpow := powAxes_prod_pow hL.1
  have hr : 1 ≤ r := NeZero.one_le
  have hw : 0 < 2 * r * w := Nat.mul_pos (by omega) (by omega)
  have s1 := runs_oppRounds (nL := NL) M ht haA hL hpw hLayer us hul hud ⟨[], undoWords r w ts ℓ K⟩
  refine Runs.seq (s1.mono (fun σ ⟨R, hc, hl, hd, e⟩ => ?_) le_rfl)
  have hRn : R.length = 2 ^ Nat.log 2 ts.prod := hl.trans hpow
  let z : ℕ → Rec r := fun x => R.getD ((paperPerm hL).phys x) (zeroRec r)
  have hRz : List.ofFn (fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y)) = R := by
    apply List.ext_getElem (by simp [hRn])
    intro i h1 h2
    have hi : i < 2 ^ Nat.log 2 ts.prod := by simpa using h1
    simp [z, (paperPerm hL).phys_logi hi, List.getElem?_eq_getElem h2]
  let G := List.ofFn fun y : Fin (2 ^ addrBits ts) => z y
  have s2 := runs_undoStep (A := A) (tL := tL) hP hL hw z
    (rnamed w (array w R) ⟨(oppScript p d r w (paperPerm hL) ts ℓ K).reverse, []⟩ ⟨[], undoWords r w ts ℓ K⟩)
    (rest r ts) [] (by rw [hRz]; simp [rnamed]) (by simp (config := {decide := true}) [rnamed])
  rw [e]
  refine s2.mono (fun σ' e' => ?_) (driveCost_le_layout hL hw z).2
  have hGl : G.length = ts.prod := by simp only [G, List.length_ofFn]; exact hpow.symm
  refine ⟨G, hGl, ?_, ?_, ?_⟩
  · intro g hg
    simp only [G, List.mem_ofFn] at hg
    obtain ⟨y, rfl⟩ := hg
    have hy : (paperPerm hL).phys y < R.length := lt_of_lt_of_eq ((paperPerm hL).phys_lt _) hRn.symm
    simp only [z, List.getD_eq_getElem _ _ hy]
    exact hd _ (List.getElem_mem hy)
  · have hG : Agree (Nat.log 2 ts.prod) (arrayVec p G) fun x => arrayVec p R ((paperPerm hL).phys x) := by
      intro x hx
      show arrayVec p (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y) x = _
      rw [arrayVec_ofFn p _ hx, arrayVec_getD_zero p (lt_of_lt_of_eq ((paperPerm hL).phys_lt _) hRn.symm)]
    exact (opposite_close hL.1 hpow (paperPerm hL) (H := ℓ) (fun i hi => by rcases hL.2.1 i hi with h | h <;> omega)
      (by have := hL.2.2.2; omega) p us R G hud (hGl.trans hpow) hc hG).1
  · rw [e']
    unfold oppEnd
    congr 1
    funext i
    fin_cases i <;> simp (config := {decide := true}) [rnamed, G]

end IntegerMultBounds.Schoenhage
