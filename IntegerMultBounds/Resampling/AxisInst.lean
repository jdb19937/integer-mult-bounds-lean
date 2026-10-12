module

public import IntegerMultBounds.Resampling.AxisDriver

/-! The expansion and compression axes as driver axis programs. An axis
record carries the packed `Ã` weight table and the per-axis rulers; the
program unpacks the table and runs `AxisStep.expandStep` (`expandSpec`). -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Resampling.AxisInst
noncomputable section

open Machine Schoenhage AxisStep AxisDriver
open Networks.Shared50ModularControl (prime)

/-! ### Expansion -/

/-- The register for the packed weight table: the `Ã` primitive's last caller tape. -/
abbrev tWt : Fin EB := 30

/-- Unpack the weight table onto the primitive's table tape, then expand. -/
def expandCmd : Cmd prime EB :=
  .seq (chunkw tWt 9 0 (by decide) (by decide) (by decide)) <| .seq (rewind 0) <| .seq (clear tWt) expandStep

/-- The registers an expansion record fills. -/
def eRegs : List (Fin EB) := [tWt, 19, 20, 25, 26, 27, 28, tU, tV]

/-- The tapes cleared after an expansion record. -/
def eJunk : List (Fin EB) := 0 :: eRegs

/-- The expansion bank at rest: the global rulers of the `Ã` primitive and the word `[true]`. -/
def eRest (m p w W : ℕ) : Fin EB → WTape := fun x =>
  if x = 8 then reg (ones p) else if x = 9 then reg (ones w) else if x = 10 then reg (ones (2 * w))
  else if x = 13 then reg (List.replicate W false) else if x = 14 then reg (List.replicate W false)
  else if x = 16 then reg (ones (2 * m + 1)) else if x = 17 then reg (ones W) else if x = tOne then reg [true]
  else emp

/-- An expansion record's words. -/
def eWords (wt : List (List Bool)) (s t m w L : ℕ) (sW tW : List Bool) : List (List Bool) :=
  [wt.flatten, sW, tW, ones (2 * s), ones (2 * (s - m)), ones (2 * (m + 1)), ones L, ones (2 * t * w),
    ones (2 * s * w)]

/-- The expansion bank once a record is loaded and its table unpacked. -/
theorem unpacked_eq (A : List Bool) (wt : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool)
    (hw : 1 ≤ w) (hwt : ∀ x ∈ wt, x.length = w) (i : Fin (31 + 91)) :
    Function.update (Function.update (Function.update (Function.update
      (setRegs (Function.update (eRest m p w W) tX (reg A)) eRegs (eWords wt s t m w L sW tW))
      tWt ⟨[wt.flatten], []⟩) 0 ⟨(cut w wt.flatten).reverse ++ [], []⟩) 0
      ⟨[], ((cut w wt.flatten).reverse ++ []).reverse ++ []⟩) tWt ⟨[], []⟩ (aSlot i) =
    LineAPrim.sigIn wt [] s t m p w W L sW tW i := by
  have hc : cut w wt.flatten = wt := cut_flatten_words hw wt hwt
  induction i using Fin.addCases with
  | left j =>
    simp only [LineAPrim.sigIn, Fin.addCases_left]
    fin_cases j <;> simp (config := {decide := true}) [aSlot, setRegs, eRegs, eWords, eRest, hc, reg, emp, Function.update_apply]
  | right j =>
    have hv : (aSlot (Fin.natAdd 31 j)).val = 31 + j.val := rfl
    have hj := j.isLt
    simp only [LineAPrim.sigIn, Fin.addCases_right]
    have ne : ∀ k : Fin EB, k.val < 31 ∨ 122 ≤ k.val → aSlot (Fin.natAdd 31 j) ≠ k := fun k hk e => by
      have := congrArg Fin.val e; rw [hv] at this; omega
    have lit : ∀ k : ℕ, (hk : k < 130) → ((OfNat.ofNat k : Fin EB) : ℕ) = k := fun k hk => Nat.mod_eq_of_lt hk
    rw [Function.update_of_ne (ne _ (by rw [lit 30 (by omega)]; omega)),
      Function.update_of_ne (ne _ (by rw [lit 0 (by omega)]; omega)),
      Function.update_of_ne (ne _ (by rw [lit 0 (by omega)]; omega)),
      Function.update_of_ne (ne _ (by rw [lit 30 (by omega)]; omega)),
      setRegs_other _ _ _ _ (by
        simp only [eRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨ne _ ?_, ne _ ?_, ne _ ?_, ne _ ?_, ne _ ?_, ne _ ?_, ne _ ?_, ne _ ?_, ne _ ?_⟩ <;>
          first | (right; decide) | (left; decide)),
      Function.update_of_ne (ne _ (by right; decide))]
    simp only [eRest]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (ne _ (by left; decide))), ite_eq_right_of_eq_false _ _ (eq_false (ne _ (by left; decide))), ite_eq_right_of_eq_false _ _ (eq_false (ne _ (by left; decide))),
      ite_eq_right_of_eq_false _ _ (eq_false (ne _ (by left; decide))), ite_eq_right_of_eq_false _ _ (eq_false (ne _ (by left; decide))), ite_eq_right_of_eq_false _ _ (eq_false (ne _ (by left; decide))),
      ite_eq_right_of_eq_false _ _ (eq_false (ne _ (by left; decide))), ite_eq_right_of_eq_false _ _ (eq_false (ne _ (by right; decide)))]

/-- The hypotheses of `runs_expandStep` for one record. -/
def EHyp (A : List Bool) (wt : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool) : Prop :=
  1 ≤ w ∧ p ≤ w ∧ w ≤ W ∧ (∀ x ∈ wt, x.length = w) ∧ wt.length = t * (2 * m + 1) ∧
  m + 1 ≤ s ∧ s ≤ t ∧ 0 < s ∧ Counter.value sW = s ∧ Counter.value tW = t ∧
  sW.length ≤ tW.length + 1 ∧ A.length = L * (2 * t * w)

/-- The parameters of an expansion record read back from its words. -/
def eDec (w : ℕ) (ws : List (List Bool)) : List (List Bool) × ℕ × ℕ × ℕ × List Bool × List Bool :=
  (cut w (ws.getD 0 []), (ws.getD 3 []).length / 2, Counter.value (ws.getD 2 []), (ws.getD 6 []).length,
    ws.getD 1 [], ws.getD 2 [])

theorem clen_le_of_mem {x : List Bool} {ws : List (List Bool)} (h : x ∈ ws) : x.length + 1 ≤ clen ws := by
  induction ws with
  | nil => simp at h
  | cons y ws ih =>
    rw [clen_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem eDec_eWords (wt : List (List Bool)) (s t m w L : ℕ) (sW tW : List Bool) (hw : 1 ≤ w)
    (hwt : ∀ x ∈ wt, x.length = w) (htv : Counter.value tW = t) :
    eDec w (eWords wt s t m w L sW tW) = (wt, s, t, L, sW, tW) := by
  simp [eDec, eWords, cut_flatten_words hw wt hwt, htv]

set_option linter.unusedSimpArgs false in
/-- The expansion axis as a driver axis program, for the global `m, p, w, W`. -/
def expandSpec (m p w W : ℕ) : AxisSpec EB where
  cmd := expandCmd
  X := tX
  regs := eRegs
  junk := eJunk
  ρ := eRest m p w W
  Good ws A := ∃ wt s t L sW tW, ws = eWords wt s t m w L sW tW ∧ EHyp A wt s t m p w W L sW tW
  f ws A := let q := eDec w ws; expandOut A q.1 q.2.1 q.2.2.1 m p w W q.2.2.2.1
  cost ws A := let q := eDec w ws; 10 * clen ws + 20 + expandBound A q.1 q.2.1 q.2.2.1 m p w W q.2.2.2.1
    q.2.2.2.2.1 q.2.2.2.2.2
  J ws _ := clen ws
  regs_nodup := by decide
  junk_nodup := by decide
  regs_junk := fun r hr => List.mem_cons_of_mem _ hr
  X_junk := by decide
  ρ_junk := by intro j hj; simp only [eJunk, eRegs, List.mem_cons, List.not_mem_nil, or_false] at hj
               rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  run := by
    rintro ws A ⟨wt, s, t, L, sW, tW, rfl, hw, hpw, hwW, hwt, hwtl, hms, hst, hs, hsv, htv, hsl, hAl⟩ -
    have hdec := eDec_eWords wt s t m w L sW tW hw hwt htv
    simp only [hdec]
    set σ0 := setRegs (Function.update (eRest m p w W) tX (reg A)) eRegs (eWords wt s t m w L sW tW)
    have g0 : σ0 0 = emp := by simp (config := {decide := true}) [σ0, setRegs, eRegs, eWords, eRest]
    have g30 : σ0 tWt = ⟨[], [wt.flatten]⟩ := by simp [σ0, setRegs, eRegs, eWords]; rfl
    have g9 : σ0 9 = reg (ones w) := by simp (config := {decide := true}) [σ0, setRegs, eRegs, eWords, eRest]
    have s1 := runs_chunkw (a := prime) (s := tWt) (r := 9) (d := 0) (by decide) (by decide) (by decide) σ0
      (L := []) (R := []) (x := wt.flatten) g30 g9 hw (by rw [g0]; rfl)
    rw [g0] at s1
    set σ1 := Function.update (Function.update σ0 tWt ⟨[wt.flatten], []⟩) 0
      ⟨(cut w wt.flatten).reverse ++ emp.left, []⟩
    have s2 := runs_rewind (a := prime) 0 σ1
    set σ2 := Function.update σ1 0 ⟨[], (σ1 0).left.reverse ++ (σ1 0).right⟩
    have s3 := runs_clear (a := prime) tWt σ2
    set σ3 := Function.update σ2 tWt ⟨[], []⟩
    have hA : ∀ i, σ3 (aSlot i) = LineAPrim.sigIn wt [] s t m p w W L sW tW i := fun i => by
      have := unpacked_eq A wt s t m p w W L sW tW hw hwt i
      simpa [σ3, σ2, σ1, emp] using this
    have hlit : ∀ x : Fin EB, x ∉ eJunk → x ≠ tX → σ3 x = eRest m p w W x := fun x hj hX => by
      have h0 : x ≠ 0 := fun e => hj (by rw [e]; decide)
      have hr : x ∉ eRegs := fun h => hj (List.mem_cons_of_mem _ h)
      have h30 : x ≠ tWt := fun e => hr (by rw [e]; decide)
      simp only [σ3, σ2, σ1]
      rw [Function.update_of_ne h30, Function.update_of_ne h0, Function.update_of_ne h0,
        Function.update_of_ne h30]
      simp only [σ0]; rw [setRegs_other _ _ _ _ hr, Function.update_of_ne hX]
    have s4 := runs_expandStep (a := prime) σ3 A wt s t m p w W L sW tW hw hpw hwW hwt hwtl hms hst hs hsv htv
      hsl hAl hA
      (by simp (config := {decide := true}) [σ3, σ2, σ1, σ0, Function.update_apply, setRegs, eRegs, eWords, eRest]) (by simp (config := {decide := true}) [σ3, σ2, σ1, σ0, Function.update_apply, setRegs, eRegs, eWords, eRest])
      (by simp (config := {decide := true}) [σ3, σ2, σ1, σ0, Function.update_apply, setRegs, eRegs, eWords, eRest]) (by simp (config := {decide := true}) [σ3, σ2, σ1, σ0, Function.update_apply, setRegs, eRegs, eWords, eRest])
      (by simp (config := {decide := true}) [σ3, σ2, σ1, σ0, Function.update_apply, setRegs, eRegs, eWords, eRest]) (by simp (config := {decide := true}) [σ3, σ2, σ1, σ0, Function.update_apply, setRegs, eRegs, eWords, eRest])
      (by simp (config := {decide := true}) [σ3, σ2, σ1, σ0, Function.update_apply, setRegs, eRegs, eWords, eRest]) (by simp (config := {decide := true}) [σ3, σ2, σ1, σ0, Function.update_apply, setRegs, eRegs, eWords, eRest])
    have hfl : wt.flatten.length = wt.length * w := by
      rw [List.length_flatten, List.map_congr_left (g := fun _ => w) (fun x hx => hwt x hx)]; simp
    have hcl : (cut w wt.flatten).length ≤ wt.flatten.length := by
      rw [length_cut hw _ ⟨wt.length, by rw [hfl]; ring⟩]; exact Nat.div_le_self _ _
    have hflat : wt.flatten.length + 1 ≤ clen (eWords wt s t m w L sW tW) := clen_le_of_mem (by simp [eWords])
    refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun τ e => ?_) ?_
    · subst e
      refine ⟨by simp [expandCmd], fun x hj hX => ?_, fun j hj => ?_⟩
      · have h0 : x ≠ 0 := fun e => hj (by rw [e]; decide)
        rw [Function.update_of_ne hX, Function.update_of_ne h0]; exact hlit x hj hX
      · have hjX : j ≠ tX := fun e => by rw [e] at hj; exact absurd hj (by decide)
        rw [Function.update_of_ne hjX]
        simp only [eJunk, eRegs, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (config := {decide := true}) [σ3, σ2, σ1, σ0, Function.update_apply, setRegs, eRegs, eWords, emp,
            WTape.words, reg] <;>
          omega
    · simp only [σ2, σ1, Function.update_self, WTape.words]
      simp (config := {decide := true}) only [emp, List.append_nil, clen_reverse, List.reverse_nil,
        List.nil_append, Function.update_apply, ite_false, ite_true]
      rw [clen_eq, cut_flatten]
      simp only [clen, List.length_flatten] at hflat ⊢
      simp [List.length_flatten] at hcl
      simp [eWords]
      omega

end
end IntegerMultBounds.Resampling.AxisInst
