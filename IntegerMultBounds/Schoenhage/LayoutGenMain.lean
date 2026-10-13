module

public import IntegerMultBounds.Schoenhage.LayoutGenRun

/-! The §6 layout-script writer on its bank of 48 tapes, end to end: setup, prefix moves, chunk
exchanges, the forward script copied (or the undo script reversed) onto the output tape, and every
tape other than the inputs and the output emptied. -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Resampling Script TwistDescriptors LayoutScriptTape LayoutGenSetup LayoutGenRun

namespace LayoutGenMain

/-! ### Word lengths of the scripts -/

theorem opRec_word_length {n R : ℕ} (hR : 0 < R) {o : LayoutMachines.Op} (hok : LayoutMachines.OpOK n o) :
    ∀ x ∈ AxisDriver.Rec.words (LayoutMachines.opRec n R o), x.length ≤ n + (bin R).length + 1 := by
  obtain ⟨h1, h2, h3⟩ := hok
  intro x hx
  simp only [LayoutMachines.opRec, AxisDriver.Rec.words, LayoutMachines.opHdrs, swapHdrsG, List.mem_cons,
    List.mem_nil_iff, or_false] at hx
  have b4 := Resampling.SwapCost.bin_length o.1
  have b5 := Resampling.SwapCost.bin_length o.2.2.1
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · simp only [LayoutMachines.opP, bin_two_pow, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  · simp only [bin_two_pow, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  · rw [bin_two_pow_mul _ _ hR, List.length_append, List.length_replicate]
    omega
  · omega
  · omega

theorem ops_word_length {n R : ℕ} (hR : 0 < R) (ops : List LayoutMachines.Op)
    (hok : ∀ o ∈ ops, LayoutMachines.OpOK n o) :
    ∀ x ∈ (ops.map (LayoutMachines.opRec n R)).flatMap AxisDriver.Rec.words, x.length ≤ n + (bin R).length + 1 := by
  intro x hx
  simp only [List.mem_flatMap, List.mem_map] at hx
  obtain ⟨_, ⟨o, ho, rfl⟩, hx⟩ := hx
  exact opRec_word_length hR (hok o ho) x hx

/-- The longest word of either script. -/
def wordLen (ℓ w : ℕ) (ts : List ℕ) : ℕ := LayoutMachines.addrBits ts + (bin (recLen ℓ w)).length + 1

theorem layoutWords_length {ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hw : 0 < w) :
    ∀ x ∈ layoutWords (2 ^ ℓ) w ts ℓ K, x.length ≤ wordLen ℓ w ts :=
  ops_word_length (R := recLen ℓ w) (by unfold recLen; positivity) _ (LayoutMachines.layoutOpList_ok hL)

theorem undoWords_length {ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hw : 0 < w) :
    ∀ x ∈ undoWords (2 ^ ℓ) w ts ℓ K, x.length ≤ wordLen ℓ w ts :=
  ops_word_length (R := recLen ℓ w) (by unfold recLen; positivity) _ (LayoutMachines.undoOpList_ok hL)

/-! ### Emptying tapes -/

/-- Empty tape `0` and every tape of the list. -/
noncomputable def clearsL : List (Fin 48) → Cmd 0 48
  | [] => clear 0
  | i :: is => .seq (clear i) (clearsL is)

theorem runs_clearsL {C : ℕ} : ∀ (is : List (Fin 48)) (σ : Fin 48 → WTape),
    (∀ x, (x ∈ is ∨ x = 0) → clen (σ x).words ≤ C) →
    Runs (clearsL is) σ (· = fun x => if x ∈ is ∨ x = 0 then emp else σ x) ((is.length + 1) * (2 * C + 3))
  | [], σ, hC => by
    refine (runs_clear (a := 0) 0 σ).mono (fun τ e => ?_) ?_
    · rw [e]; funext x
      by_cases hx : x = 0
      · subst hx; simp [emp]
      · simp [hx]
    · have := hC 0 (Or.inr rfl); simp; omega
  | i :: is, σ, hC => by
    have s1 := runs_clear (a := 0) i σ
    have ih := runs_clearsL is (Function.update σ i ⟨[], []⟩) (fun x hx => by
      by_cases e : x = i
      · subst e; simp [WTape.clen_words]
      · rw [Function.update_of_ne e]
        exact hC x (by rcases hx with hx | hx <;> simp [hx]))
    refine (Runs.then s1 ih).mono (fun τ e => ?_) ?_
    · rw [e]; funext x
      by_cases hx : x = i
      · subst hx; simp [emp]
      · simp [hx]
    · have := hC i (Or.inl (by simp))
      simp only [List.length_cons]
      nlinarith

/-- The tapes the writer empties at the end: all but the inputs and the output. -/
def clearList : List (Fin 48) := (List.finRange 48).filter fun i => i.val < 32 ∨ 39 ≤ i.val

theorem clearList_length : clearList.length = 41 := by decide

theorem mem_clearList (x : Fin 48) : (x ∈ clearList ∨ x = 0) ↔ (x.val < 32 ∨ 39 ≤ x.val) := by
  constructor
  · rintro (h | rfl)
    · simpa [clearList] using h
    · simp
  · intro h; left; simpa [clearList] using h

/-! ### The tape sizes after the exchanges -/

theorem clen_repl (n : ℕ) : clen (List.replicate n ([] : List Bool)) = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, clen_cons, ih]; simp; omega

/-- A bound on every tape's contents after the exchanges. -/
def tapeC (ℓ K w : ℕ) (ts : List ℕ) : ℕ :=
  clen (fwdOut ℓ K w ts) + clen (undoOut ℓ K w ts) + 2 * movesN ℓ ts + 2 * ts.length + K + w +
    (bin (recLen ℓ w)).length + 2 * ℓ + 10

set_option maxHeartbeats 16000000 in
theorem stH_clen {ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) {k L m s : ℕ}
    (hk : k ≤ movesN ℓ ts) (hLm : L ≤ movesN ℓ ts) (hm : m ≤ movesN ℓ ts) (hs : s ≤ movesN ℓ ts) (i : Fin 48) :
    clen (stH ℓ K w ts k L m s i).words ≤ tapeC ℓ K w ts := by
  have hn := nOf_paper hL
  have hn' : nOf ℓ ts.length ((List.range ts.length).map fun i => decide (axLen ts i = ℓ)) =
      LayoutMachines.addrBits ts := hn
  have hN : movesN ℓ ts = LayoutMachines.addrBits ts + ts.length * ℓ + ℓ + ts.length := rfl
  have hq : (ℓ - 1) / K * ts.length ≤ ts.length * ℓ := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ ((Nat.div_le_self _ _).trans (Nat.sub_le _ _))
  have hb : (ℓ - 1) % K ≤ ℓ := (Nat.mod_le _ _).trans (Nat.sub_le _ _)
  have hbK := Resampling.SwapCost.bin_length K
  have hfl : clen (((pf ts ℓ).map fun x => [x]).reverse) = 2 * ts.length := by
    rw [clen_reverse, clen_flagWords]; simp [SigmaConstsTape.paperFlags]
  have hfl' : clen (((List.range ts.length).map fun i => decide (axLen ts i = ℓ)).map fun x => [x]).reverse =
      2 * ts.length := hfl
  have hfl'' : clen (List.map ((fun x => [x]) ∘ fun i => decide (axLen ts i = ℓ)) (List.range ts.length)) =
      2 * ts.length := by
    rw [← List.map_map, clen_flagWords]; simp
  unfold tapeC
  rw [hN] at hk hLm hm hs ⊢
  fin_cases i <;> tsimp [stH, stG, stF, stE, stD, stC, stB, stA, lstart, bank, emp, endv, reg, ones, WTape.clen_words,
    clen_cons, clen_repl, clen_reverse, hn, hn', hfl, hfl', pf, SigmaConstsTape.paperFlags] <;> omega

/-! ### The writer on its bank -/

/-- Setup, moves and exchanges, then `out`, then emptying the scratch tapes. -/
noncomputable def lgBody (out : Cmd 0 48) : Cmd 0 48 :=
  .seq constsA <| .seq (.seq copyFlags (.seq copyTicks lm1Calc)) <| .seq nPhase <| .seq divPhase <|
  .seq binPhase <| .seq arrPhase <| .seq (movesGen.map fm fm_injective) <|
  .seq (Cmd.map fe fe_injective (.loop LayoutSwapTape.xA LayoutSwapTape.step)) <| .seq out (clearsL clearList)

/-- The forward writer. -/
noncomputable def lgFwd : Cmd 0 48 := lgBody outFwd

/-- The undo writer. -/
noncomputable def lgUndo : Cmd 0 48 := lgBody outUndo

/-- The steps of setup, moves and exchanges. -/
def midCost (ℓ K w : ℕ) (ts : List ℕ) : ℕ :=
  40 + (13 * (pf ts ℓ).length + 10 * ts.length + 4 * ℓ + 60) +
  (ts.length * (2 * (ℓ - 1) + 18) + (pf ts ℓ).length * 30 + 3 * ts.length + 4 * (pf ts ℓ).length +
    3 * (ts.length * (ℓ - 1) + (pf ts ℓ).length) + 30 + 4 * nOf ℓ ts.length (pf ts ℓ) + 20) +
  ((ℓ - 1) * (16 * (ℓ - 1) + 10 * K + 110) + 100 * ℓ + 600) +
  (8 * w * w + 76 * w + 8 * K * K + 80 * K + 20 * nOf ℓ ts.length (pf ts ℓ) + 10 * ℓ + 400) +
  (arrCost ts.length ((ℓ - 1) / K) (ts.length + (ℓ - 1) / K * ts.length) +
    4 * ((ℓ - 1) / K * ts.length * (ts.length + (ℓ - 1) / K * ts.length + 1)) + 4 * ((ℓ - 1) / K) + 20) +
  (ts.length * (topCost (movesN ℓ ts) (recLen ℓ w) (ℓ - 1) + 2) + 1 +
    (ℓ - 1) % K * (levelCost (movesN ℓ ts) (recLen ℓ w) ts.length + 2)) +
  ((ℓ - 1) / K * ts.length * (LayoutSwapTape.stepCost ((ℓ - 1) / K * ts.length) K
    (LayoutMachines.addrBits ts - 2 * K) (recLen ℓ w) + 2)) + 10

/-- The steps of emptying the scratch tapes. -/
def clearCost (ℓ K w : ℕ) (ts : List ℕ) : ℕ := 42 * (2 * tapeC ℓ K w ts + 3) + 1

/-- The forward writer's steps. -/
def lgFwdCost (ℓ K w : ℕ) (ts : List ℕ) : ℕ :=
  midCost ℓ K w ts + (2 * clen (layoutWords (2 ^ ℓ) w ts ℓ K) +
    (layoutWords (2 ^ ℓ) w ts ℓ K).length * (wordLen ℓ w ts + 8) + 10) + clearCost ℓ K w ts

/-- The undo writer's steps. -/
def lgUndoCost (ℓ K w : ℕ) (ts : List ℕ) : ℕ :=
  midCost ℓ K w ts + (3 * clen (undoWords (2 ^ ℓ) w ts ℓ K) +
    (undoWords (2 ^ ℓ) w ts ℓ K).length * (5 * wordLen ℓ w ts + 38) + 10) + clearCost ℓ K w ts

/-- Setup, moves, exchanges, then any tail that works from every state after the exchanges. -/
theorem runs_lgBody {ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hw : 0 < w) (hK : 0 < K)
    {out : Cmd 0 48} {Q : (Fin 48 → WTape) → Prop} {Bt : ℕ}
    (htail : ∀ k L m s, k ≤ movesN ℓ ts → L ≤ movesN ℓ ts → m ≤ movesN ℓ ts → s ≤ movesN ℓ ts →
      Runs (.seq out (clearsL clearList)) (stH ℓ K w ts k L m s) Q Bt) :
    Runs (lgBody out) (lstart ℓ K w ts.length (pf ts ℓ)) Q (midCost ℓ K w ts + Bt) := by
  have s1 := runs_constsA ℓ K w ts.length (pf ts ℓ)
  have s2 := runs_copies ℓ K w ts.length (pf ts ℓ)
  have s3 := runs_nPhase ℓ K w ts.length (pf ts ℓ)
  have s4 := runs_divPhase (ℓ := ℓ) hK w ts.length (pf ts ℓ)
  have s5 := runs_binPhase (ℓ := ℓ) (K := K) hw ts.length (pf ts ℓ)
  have s6 := runs_arrPhase ℓ K w ts.length (pf ts ℓ)
  have s7 := runs_movesPhase (K := K) hL hw
  have rest : Runs (.seq (movesGen.map fm fm_injective)
      (.seq (Cmd.map fe fe_injective (.loop LayoutSwapTape.xA LayoutSwapTape.step)) (.seq out (clearsL clearList))))
      (stF ℓ K w ts.length (pf ts ℓ)) Q _ :=
    Runs.seq (s7.mono (fun σ ⟨k, L, m, s, hk, hLm, hm, hs, he⟩ => by
      rw [he]; exact Runs.then (runs_exPhase hL hw k L m s) (htail k L m s hk hLm hm hs)) le_rfl)
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6 rest)))))).mono
    (fun _ h => h) ?_
  unfold midCost
  omega

theorem stH_zero (ℓ K w : ℕ) (ts : List ℕ) (k L m s : ℕ) :
    stH ℓ K w ts k L m s 0 = ⟨(layoutWords (2 ^ ℓ) w ts ℓ K).reverse, []⟩ := by
  simp [stH, fwdOut_eq]

theorem stH_one (ℓ K w : ℕ) (ts : List ℕ) (k L m s : ℕ) :
    stH ℓ K w ts k L m s 1 = ⟨undoWords (2 ^ ℓ) w ts ℓ K, []⟩ := by
  simp [stH, undoOut_eq]

theorem stH_emp (ℓ K w : ℕ) (ts : List ℕ) (k L m s : ℕ) :
    stH ℓ K w ts k L m s 38 = emp ∧ stH ℓ K w ts k L m s 47 = emp ∧ stH ℓ K w ts k L m s 10 = emp := by
  refine ⟨?_, ?_, ?_⟩ <;> tsimp [stH, stG, stF, stE, stD, stC, stB, stA, lstart, bank, emp]

theorem clen_layoutWords_le (ℓ K w : ℕ) (ts : List ℕ) : clen (layoutWords (2 ^ ℓ) w ts ℓ K) ≤ tapeC ℓ K w ts := by
  have : clen (fwdOut ℓ K w ts) = clen (layoutWords (2 ^ ℓ) w ts ℓ K) := by rw [fwdOut_eq, clen_reverse]
  unfold tapeC; omega

theorem clen_undoWords_le (ℓ K w : ℕ) (ts : List ℕ) : clen (undoWords (2 ^ ℓ) w ts ℓ K) ≤ tapeC ℓ K w ts := by
  have : clen (undoOut ℓ K w ts) = clen (undoWords (2 ^ ℓ) w ts ℓ K) := by rw [undoOut_eq]
  unfold tapeC; omega

set_option maxHeartbeats 16000000 in
/-- The forward writer: the layout script on the output tape, every other tape as at the start. -/
theorem runs_lgFwd {ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hw : 0 < w) (hK : 0 < K) :
    Runs lgFwd (lstart ℓ K w ts.length (pf ts ℓ))
      (· = Function.update (lstart ℓ K w ts.length (pf ts ℓ)) 38 ⟨[], layoutWords (2 ^ ℓ) w ts ℓ K⟩)
      (lgFwdCost ℓ K w ts) := by
  refine (runs_lgBody (out := outFwd) hL hw hK (Bt := (2 * clen (layoutWords (2 ^ ℓ) w ts ℓ K) +
    (layoutWords (2 ^ ℓ) w ts ℓ K).length * (wordLen ℓ w ts + 8) + 10) + 1 +
    (clearList.length + 1) * (2 * tapeC ℓ K w ts + 3)) (fun k L m s hk hLm hm hs => ?_)).le ?_
  swap
  · rw [clearList_length]; unfold lgFwdCost clearCost; omega
  obtain ⟨h38, -, -⟩ := stH_emp ℓ K w ts k L m s
  have s9 := runs_outFwd (stH ℓ K w ts k L m s) (layoutWords_length hL hw) (stH_zero ℓ K w ts k L m s) h38
  rw [← stH_zero ℓ K w ts k L m s, Function.update_eq_self] at s9
  have s10 := runs_clearsL (C := tapeC ℓ K w ts) clearList
    (Function.update (stH ℓ K w ts k L m s) 38 ⟨[], layoutWords (2 ^ ℓ) w ts ℓ K⟩) (fun x hx => by
      have hx38 : x ≠ 38 := fun e => by rw [mem_clearList, e] at hx; simp at hx
      rw [Function.update_of_ne hx38]
      exact stH_clen hL hk hLm hm hs x)
  refine (Runs.then s9 s10).mono (fun τ e => ?_) le_rfl
  rw [e]; funext i
  simp only [mem_clearList]
  fin_cases i <;> tsimp [stH, stG, stF, stE, stD, stC, stB, stA, lstart, bank, emp, endv]

set_option maxHeartbeats 16000000 in
/-- The undo writer: the undo script on the output tape, every other tape as at the start. -/
theorem runs_lgUndo {ℓ K w : ℕ} {ts : List ℕ} (hL : LayoutOK (2 ^ ℓ) ts ℓ K) (hw : 0 < w) (hK : 0 < K) :
    Runs lgUndo (lstart ℓ K w ts.length (pf ts ℓ))
      (· = Function.update (lstart ℓ K w ts.length (pf ts ℓ)) 38 ⟨[], undoWords (2 ^ ℓ) w ts ℓ K⟩)
      (lgUndoCost ℓ K w ts) := by
  refine (runs_lgBody (out := outUndo) hL hw hK (Bt := (3 * clen (undoWords (2 ^ ℓ) w ts ℓ K) +
    (undoWords (2 ^ ℓ) w ts ℓ K).length * (5 * wordLen ℓ w ts + 38) + 10) + 1 +
    (clearList.length + 1) * (2 * tapeC ℓ K w ts + 3)) (fun k L m s hk hLm hm hs => ?_)).le ?_
  swap
  · rw [clearList_length]; unfold lgUndoCost clearCost; omega
  obtain ⟨h38, h47, h10⟩ := stH_emp ℓ K w ts k L m s
  have s9 := runs_outUndo (stH ℓ K w ts k L m s) (undoWords_length hL hw) (stH_one ℓ K w ts k L m s) h38 h47 h10
  have s10 := runs_clearsL (C := tapeC ℓ K w ts) clearList
    (Function.update (Function.update (Function.update (stH ℓ K w ts k L m s) 1
      ⟨[], (undoWords (2 ^ ℓ) w ts ℓ K).reverse⟩) 47 ⟨undoWords (2 ^ ℓ) w ts ℓ K, []⟩) 38
      ⟨[], undoWords (2 ^ ℓ) w ts ℓ K⟩) (fun x hx => by
      have hx38 : x ≠ 38 := fun e => by rw [mem_clearList, e] at hx; simp at hx
      rw [Function.update_of_ne hx38]
      by_cases hx47 : x = 47
      · subst hx47; simp [WTape.clen_words, clen_undoWords_le]
      · rw [Function.update_of_ne hx47]
        by_cases hx1 : x = 1
        · subst hx1; simp [WTape.clen_words, clen_reverse, clen_undoWords_le]
        · rw [Function.update_of_ne hx1]
          exact stH_clen hL hk hLm hm hs x)
  refine (Runs.then s9 s10).mono (fun τ e => ?_) le_rfl
  rw [e]; funext i
  simp only [mem_clearList]
  fin_cases i <;> tsimp [stH, stG, stF, stE, stD, stC, stB, stA, lstart, bank, emp, endv]

end LayoutGenMain

end IntegerMultBounds.Schoenhage
