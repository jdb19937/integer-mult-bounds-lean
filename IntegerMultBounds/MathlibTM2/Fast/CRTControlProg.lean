module

public import IntegerMultBounds.MathlibTM2.Fast.CRTControl
public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-!
# Executable arithmetic for a CRT control descriptor

Ten binary variables suffice: remaining address (0), place (1), bound (2),
weight (3), active flag (4), accumulated value (5), validity flag (6), digit
scratch (7), product scratch (8), and a zero register (9). A step consumes one
descriptor, updates the address and accumulator, and clears its scratch.

The descriptor list and outer fiber loop still need to be connected to this
fixed program. `TblDo.host` supplies its finite-host implementation and cost.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open TableVM

def crtCtlPrefix : List (TblIns 10) := [.div 0 1 7, .mod 0 1 0]
def crtCtlAdd : List (TblIns 10) := [.mul 7 3 8, .add 5 8 5]
def crtCtlClear : List (TblIns 10) := [.zero 7, .zero 8]

/-- Decode, conditionally accumulate and validate, then clear both scratch variables. -/
def crtControlStep : TblCode 10 :=
  tblStraight 10 crtCtlPrefix <|
    .seq (.ite 9 4
      (.seq (tblBlock 10 [.mul 7 3 8] (.add 5 8 5))
        (.ite 7 2 (.ins (.copy 6 6)) (.ins (.zero 6))))
      (.ins (.copy 5 5)))
      (tblBlock 10 [.zero 7] (.zero 8))

/-- Exact arithmetic state of the fixed descriptor program. -/
def crtControlStepState {A : ℕ} (w : ℕ) (st : TblSt 10 A) : TblSt 10 A :=
  let s := tblExactList A w crtCtlPrefix st
  let t := if st.val 9 < st.val 4 then
      let t := tblExactList A w crtCtlAdd s
      if st.val 0 / st.val 1 < st.val 2 then (.copy 6 6 : TblIns 10).exact A w t
      else (.zero 6 : TblIns 10).exact A w t
    else (.copy 5 5 : TblIns 10).exact A w s
  tblExactList A w crtCtlClear t

/-- One descriptor takes at most nine interpreter atoms. Only the active
branch needs a multiplication/addition bound; no proof limits are changed. -/
theorem crtControlStep_do {A W w : ℕ} (st : TblSt 10 A)
    (hfit : st.val 9 < st.val 4 →
      st.val 5 + st.val 0 / st.val 1 * st.val 3 < 2 ^ W) :
    TblDo A W w crtControlStep st (fun s => s = crtControlStepState w st) 9 := by
  let s := tblExactList A w crtCtlPrefix st
  let clear : TblCode 10 := tblBlock 10 [.zero 7] (.zero 8)
  have hclear : ∀ t : TblSt 10 A,
      TblDo A W w clear t (fun t' => t' = tblExactList A w crtCtlClear t) 2 := by
    intro t
    exact TblDo.block _ _ (by simp [tblFitsList, TblIns.fits]) rfl
  have hp : tblFitsList A W w crtCtlPrefix st := by
    simp [crtCtlPrefix, tblFitsList, TblIns.fits]
  unfold crtControlStep
  refine (TblDo.straightX crtCtlPrefix (K := 7) hp ?_).mono (fun _ h => h) (by decide)
  change TblDo A W w _ s _ 7
  by_cases ha : st.val 9 < st.val 4
  · have ha' : s.val 9 < s.val 4 := by simpa [s, crtCtlPrefix, tblExactList, TblIns.exact] using ha
    let t := tblExactList A w crtCtlAdd s
    have hmul : st.val 0 / st.val 1 * st.val 3 < 2 ^ W := by have := hfit ha; omega
    have hadd : TblDo A W w (tblBlock 10 [.mul 7 3 8] (.add 5 8 5)) s
        (fun t' => t' = t) 2 := by
      apply TblDo.block
      · simpa [s, crtCtlPrefix, tblFitsList, TblIns.fits, TblIns.exact, tblExactList] using
          And.intro hmul (And.intro (hfit ha) True.intro)
      · rfl
    by_cases hv : st.val 0 / st.val 1 < st.val 2
    · have hv' : t.val 7 < t.val 2 := by
        simpa [t, s, crtCtlAdd, crtCtlPrefix, tblExactList, TblIns.exact] using hv
      have hvalid := TblDo.iteT (d := .ins (.zero 6)) hv' (TblDo.insX (.copy 6 6)
        (st := t) (A := A) (W := W) (w := w) trivial (P := fun t' => t' =
          (.copy 6 6 : TblIns 10).exact A w t) rfl)
      have hbranch := TblDo.iteT (d := .ins (.copy 5 5)) ha' (hadd.seq (fun t' ht => by subst t'; exact hvalid))
      have h := hbranch.seq (fun t' ht => by subst t'; exact hclear _)
      simpa only [crtControlStepState, ite_eq_left ha, ite_eq_left hv] using h
    · have hv' : ¬t.val 7 < t.val 2 := by
        simpa [t, s, crtCtlAdd, crtCtlPrefix, tblExactList, TblIns.exact] using hv
      have hvalid := TblDo.iteF (c := .ins (.copy 6 6)) hv' (TblDo.insX (.zero 6)
        (st := t) (A := A) (W := W) (w := w) trivial (P := fun t' => t' =
          (.zero 6 : TblIns 10).exact A w t) rfl)
      have hbranch := TblDo.iteT (d := .ins (.copy 5 5)) ha' (hadd.seq (fun t' ht => by subst t'; exact hvalid))
      have h := hbranch.seq (fun t' ht => by subst t'; exact hclear _)
      simpa only [crtControlStepState, ite_eq_left ha, ite_eq_right hv] using h
  · have ha' : ¬s.val 9 < s.val 4 := by simpa [s, crtCtlPrefix, tblExactList, TblIns.exact] using ha
    have hbranch := TblDo.iteF (c := .seq (tblBlock 10 [.mul 7 3 8] (.add 5 8 5))
      (.ite 7 2 (.ins (.copy 6 6)) (.ins (.zero 6)))) ha' (TblDo.insX (.copy 5 5)
      (st := s) (A := A) (W := W) (w := w) trivial (P := fun t' => t' =
        (.copy 5 5 : TblIns 10).exact A w s) rfl)
    have h := hbranch.seq (fun t' ht => by subst t'; exact hclear _)
    refine h.mono ?_ (by decide)
    intro t ht
    subst t
    simp only [crtControlStepState, ite_eq_right ha]
    rfl

/-- The program's mathematical effect, including scratch cleanup and preservation
of every descriptor field. A failed validity test is sticky. -/
theorem crtControlStepState_spec {A : ℕ} (w : ℕ) (st : TblSt 10 A) :
    let t := crtControlStepState w st
    t.val 0 = st.val 0 % st.val 1 ∧
    t.val 5 = st.val 5 + (if st.val 9 < st.val 4 then st.val 0 / st.val 1 * st.val 3 else 0) ∧
    t.val 6 = (if st.val 9 < st.val 4 ∧ ¬st.val 0 / st.val 1 < st.val 2 then 0 else st.val 6) ∧
    t.val 7 = 0 ∧ t.val 8 = 0 ∧
    (∀ j, j ≠ 0 → j ≠ 5 → j ≠ 6 → j ≠ 7 → j ≠ 8 → t.val j = st.val j) ∧
    t.acc = st.acc := by
  by_cases ha : st.val 9 < st.val 4 <;>
    by_cases hv : st.val 0 / st.val 1 < st.val 2 <;>
      simp [crtControlStepState, crtCtlPrefix, crtCtlAdd, crtCtlClear,
        tblExactList, TblIns.exact, ha, hv] <;>
      intro j h0 h5 h6 h7 h8 <;> simp_all

/-- A descriptor represented in the ten-variable interpreter bank. -/
def crtControlStepInput {A : ℕ} (f : CrtControlField) (F K : ℕ) (valid : Bool)
    (st : TblSt 10 A) : Prop :=
  st.val 0 = F ∧ st.val 1 = f.place ∧ st.val 2 = f.bound ∧ st.val 3 = f.weight ∧
  st.val 4 = (if f.active then 1 else 0) ∧ st.val 5 = K ∧
  st.val 6 = (if valid then 1 else 0) ∧ st.val 9 = 0

/-- The fixed executable step implements one descriptor of the arbitrary-order
control evaluator, with a preserved validity flag on inactive spectator fields. -/
theorem crtControlStep_descriptor {A W w : ℕ} (f : CrtControlField) (F K : ℕ) (valid : Bool)
    (st : TblSt 10 A) (hin : crtControlStepInput f F K valid st)
    (hfit : f.active = true → K + F / f.place * f.weight < 2 ^ W) :
    TblDo A W w crtControlStep st (fun t =>
      t.val 0 = F % f.place ∧
      t.val 5 = K + (if f.active then F / f.place * f.weight else 0) ∧
      t.val 6 = (if valid && (!f.active || decide (F / f.place < f.bound)) then 1 else 0) ∧
      t.val 7 = 0 ∧ t.val 8 = 0 ∧
      (∀ j, j ≠ 0 → j ≠ 5 → j ≠ 6 → j ≠ 7 → j ≠ 8 → t.val j = st.val j) ∧
      t.acc = st.acc) 9 := by
  obtain ⟨hF, hp, hb, hw, ha, hK, hv, hz⟩ := hin
  have hfits : st.val 9 < st.val 4 →
      st.val 5 + st.val 0 / st.val 1 * st.val 3 < 2 ^ W := by
    rw [hz, ha, hK, hF, hp, hw]
    cases hactive : f.active <;> simp_all
  refine (crtControlStep_do st hfits).mono ?_ le_rfl
  intro t ht
  subst t
  have hs := crtControlStepState_spec w st
  simp only [hF, hp, hb, hw, ha, hK, hv, hz] at hs
  cases hactive : f.active <;> cases valid <;>
    by_cases hlt : F / f.place < f.bound <;>
      simpa [hactive, hlt] using hs

/-- Compute the low offset and its complement. Variables 0, 1, 2 hold
`S`, `μ`, `K`; variables 3, 4 receive `μ*K % S` and `S - μ*K % S`. -/
def crtControlOffset : TblCode 5 :=
  tblBlock 5 [.mul 1 2 3, .mod 3 0 3] (.sub 0 3 4)

/-- The modular offset and both directional rotation lengths require three
interpreter atoms, independent of the number of preceding valid fibers. -/
theorem crtControlOffset_do {A W w : ℕ} (st : TblSt 5 A)
    (hS : 0 < st.val 0) (hSlt : st.val 0 < 2 ^ W)
    (hprod : st.val 1 * st.val 2 < 2 ^ W) :
    TblDo A W w crtControlOffset st (fun t =>
      t.val 3 = st.val 1 * st.val 2 % st.val 0 ∧
      t.val 4 = st.val 0 - st.val 1 * st.val 2 % st.val 0 ∧
      (∀ j, j ≠ 3 → j ≠ 4 → t.val j = st.val j) ∧ t.acc = st.acc) 3 := by
  have hlo := (Nat.mod_lt (st.val 1 * st.val 2) hS).le
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hprod, hlo, hSlt]
  · simp [tblExactList, TblIns.exact]
    intro j h3 h4
    simp [h3, h4]

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host

/-- Actual finite-host steps for one descriptor, including the interpreter's
arithmetic workspace restoration and preservation of spectator registers. -/
theorem crtControlStep_host {T Q A W w : ℕ} {U P : Type}
    {body : P → Pr P T Q A U} {rg : TblR 10 → Fin T}
    (hrg : Function.Injective rg) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W) (st : TblSt 10 A)
    (hst : ∀ j, st.val j < 2 ^ W)
    (hfit : st.val 9 < st.val 4 →
      st.val 5 + st.val 0 / st.val 1 * st.val 3 < 2 ^ W) :
    tblRuns body rg (tblCompile rg crtControlStep)
      (tblRho W wl nl st) (tblRho W wl nl (crtControlStepState w st)) (9 * tblC W w) := by
  obtain ⟨st', hst', hr⟩ := (crtControlStep_do st hfit).host (body := body)
    hrg wl nl hwl hnl hw hst
  subst st'
  exact hr

end IntegerMultBounds.MathlibTM2.Fast
