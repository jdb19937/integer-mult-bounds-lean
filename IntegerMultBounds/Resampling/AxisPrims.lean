module

public import IntegerMultBounds.Resampling.LineAPrim
public import IntegerMultBounds.Resampling.B0Prim

/-! The `Ã` and `B̃₀` line loops as word-program primitives over the
four-symbol alphabet. The parameters are read back from the word tapes
(`aSem_sigIn`, `bSem_sigIn`), so the effect and cost are functions of the
tapes alone. -/

@[expose] public section

namespace IntegerMultBounds.Resampling.AxisPrims

open Machine Schoenhage

/-! ### `Ã` -/

/-- Tape `i` of the `Ã` primitive's caller block. -/
def aT (σ : Fin (31 + 91) → WTape) (i : Fin 31) : WTape := σ (Fin.castAdd 91 i)

/-- The parameters `s, t, m, p, w, W, L` read back from the tapes. -/
def aPar (σ : Fin (31 + 91) → WTape) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  ((aT σ 25).cur.length / 2, Counter.value (aT σ 20).cur, (aT σ 16).cur.length / 2, (aT σ 8).cur.length,
    (aT σ 9).cur.length, (aT σ 17).cur.length, (aT σ 28).cur.length)

noncomputable def aSem (σ : Fin (31 + 91) → WTape) : Fin (31 + 91) → WTape :=
  let q := aPar σ
  LineAPrim.sigOut (aT σ 0).right (aT σ 22).right q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1
    q.2.2.2.2.2.2 (aT σ 19).cur (aT σ 20).cur

noncomputable def aCost (σ : Fin (31 + 91) → WTape) : ℕ :=
  let q := aPar σ
  LineAPrim.progBound (aT σ 0).right (aT σ 22).right q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1
    q.2.2.2.2.2.2 (aT σ 19).cur (aT σ 20).cur

/-- The hypotheses of `LineAPrim.prim_hoare`. -/
def AHyp (wt arr : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool) : Prop :=
  1 ≤ w ∧ p ≤ w ∧ w ≤ W ∧ (∀ x ∈ wt, x.length = w) ∧ wt.length = t * (2 * m + 1) ∧
  arr.length = 2 * s * L ∧ (∀ x ∈ arr, x.length = w) ∧ m + 1 ≤ s ∧ s ≤ t ∧ 0 < s ∧
  Counter.value sW = s ∧ Counter.value tW = t ∧ sW.length ≤ tW.length + 1

def APre (σ : Fin (31 + 91) → WTape) : Prop :=
  ∃ wt arr s t m p w W L sW tW, σ = LineAPrim.sigIn wt arr s t m p w W L sW tW ∧ AHyp wt arr s t m p w W L sW tW

theorem aT_sigIn (wt arr : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool) :
    aT (LineAPrim.sigIn wt arr s t m p w W L sW tW) = ![⟨[], wt⟩, emp, emp, emp, emp, emp, emp, emp,
      reg (ones p), reg (ones w), reg (ones (2 * w)), emp, emp, reg (List.replicate W false),
      reg (List.replicate W false), emp, reg (ones (2 * m + 1)), reg (ones W), emp, reg (sW), reg (tW), emp,
      ⟨[], arr⟩, emp, emp, reg (ones (2 * s)), reg (ones (2 * (s - m))), reg (ones (2 * (m + 1))),
      reg (ones L), emp, emp] := by
  funext i; simp only [aT, LineAPrim.sigIn, Fin.addCases_left]

theorem aSem_sigIn (wt arr : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool) (ht : Counter.value tW = t) :
    aSem (LineAPrim.sigIn wt arr s t m p w W L sW tW) = LineAPrim.sigOut wt arr s t m p w W L sW tW ∧
    aCost (LineAPrim.sigIn wt arr s t m p w W L sW tW) = LineAPrim.progBound wt arr s t m p w W L sW tW := by
  have hp : aPar (LineAPrim.sigIn wt arr s t m p w W L sW tW) = (s, t, m, p, w, W, L) := by
    simp only [aPar]; rw [aT_sigIn]
    simp [reg, ht]
    omega
  simp only [aSem, aCost, hp]; rw [aT_sigIn]
  simp [reg]

theorem aSpec (σ : Fin (31 + 91) → WTape) (hσ : APre σ) :
    HoareTime LineAPrim.progF (· = enc σ) (· = enc (aSem σ)) (aCost σ) := by
  obtain ⟨wt, arr, s, t, m, p, w, W, L, sW, tW, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hσ
  obtain ⟨e1, e2⟩ := aSem_sigIn wt arr s t m p w W L sW tW h12
  rw [e1, e2]
  exact LineAPrim.prim_hoare wt arr s t m p w W L sW tW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

/-- The `Ã` line loop as a primitive. -/
noncomputable def aPrim : Prim 0 := Prim.ofProgram LineAPrim.progF (by omega) APre aSem aCost aSpec

/-! ### `B̃₀` -/

/-- Tape `i` of the `B̃₀` primitive's caller block. -/
def bT (σ : Fin (49 + 91) → WTape) (i : Fin 49) : WTape := σ (Fin.castAdd 91 i)

/-- The parameters `s, t, m, p, w, W, L` read back from the tapes. -/
def bPar (σ : Fin (49 + 91) → WTape) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  ((bT σ 34).cur.length / 2, (bT σ 44).cur.length / 2, (bT σ 16).cur.length / 2, (bT σ 8).cur.length,
    (bT σ 9).cur.length, (bT σ 17).cur.length, (bT σ 45).cur.length)

noncomputable def bSem (σ : Fin (49 + 91) → WTape) : Fin (49 + 91) → WTape :=
  let q := bPar σ
  B0Prim.sigOut (bT σ 42).right (bT σ 0).right (bT σ 27).right (bT σ 28).right (bT σ 33).right q.1 q.2.1
    q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2 (bT σ 19).cur (bT σ 20).cur

noncomputable def bCost (σ : Fin (49 + 91) → WTape) : ℕ :=
  let q := bPar σ
  B0Prim.progBound (bT σ 42).right (bT σ 0).right (bT σ 27).right (bT σ 28).right (bT σ 33).right q.1 q.2.1
    q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2 (bT σ 19).cur (bT σ 20).cur

/-- The hypotheses of `B0Prim.prim_hoare`. -/
def BHyp (arr wtE wtH wtD zeros : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool) : Prop :=
  1 ≤ w ∧ p ≤ w ∧ w ≤ W ∧ arr.length = 2 * t * L ∧ (∀ x ∈ arr, x.length = w) ∧ 2 ≤ p ∧
  (∀ x ∈ wtE, x.length = w) ∧ wtE.length = s * (2 * m + 1) ∧ (∀ x ∈ wtH, x.length = w) ∧
  wtH.length = s * (2 * 0 + 1) ∧ (∀ x ∈ wtD, x.length = w) ∧ wtD.length = s * (2 * 0 + 1) ∧
  zeros.length = 2 * s ∧ (∀ x ∈ zeros, x.length = w) ∧ m + 1 ≤ s ∧ 0 < s ∧ s < t ∧
  Counter.value sW = s ∧ Counter.value tW = s ∧ sW.length ≤ tW.length + 1

def BPre (σ : Fin (49 + 91) → WTape) : Prop :=
  ∃ arr wtE wtH wtD zeros s t m p w W L sW tW, σ = B0Prim.sigIn arr wtE wtH wtD zeros s t m p w W L sW tW ∧
    BHyp arr wtE wtH wtD zeros s t m p w W L sW tW

theorem bT_sigIn (arr wtE wtH wtD zeros : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool) :
    bT (B0Prim.sigIn arr wtE wtH wtD zeros s t m p w W L sW tW) = ![⟨[], wtE⟩, emp, emp, emp, emp, emp, emp, emp,
      reg (ones (p)), reg (ones (w)), reg (ones (2 * w)), emp, emp, reg (List.replicate W false),
      reg (List.replicate W false), emp, reg (ones (2 * m + 1)), reg (ones (W)), emp, reg (sW), reg (tW), emp, emp,
      emp, reg (ones (2 * (s - m))), reg (ones (2 * (m + 1))), reg (ones (p)), ⟨[], wtH⟩, ⟨[], wtD⟩,
      reg (List.replicate w false), reg (List.replicate w false), reg (ones (2 * 0 + 1)), reg (ones (w)),
      ⟨[], zeros⟩, reg (ones (2 * (s - 0))), reg (ones (2 * (0 + 1))), reg (ones (p)), emp, reg (RowSelect.R0 s t),
      reg (RowSelect.twoS s), reg (RowSelect.twoT t), emp, ⟨[], arr⟩, emp, reg (ones (2 * t)), reg (ones (L)),
      reg (RowSelect.R0 s t), emp, emp] := by
  funext i; simp only [bT, B0Prim.sigIn, Fin.addCases_left]

theorem bSem_sigIn (arr wtE wtH wtD zeros : List (List Bool)) (s t m p w W L : ℕ) (sW tW : List Bool) :
    bSem (B0Prim.sigIn arr wtE wtH wtD zeros s t m p w W L sW tW) =
      B0Prim.sigOut arr wtE wtH wtD zeros s t m p w W L sW tW ∧
    bCost (B0Prim.sigIn arr wtE wtH wtD zeros s t m p w W L sW tW) =
      B0Prim.progBound arr wtE wtH wtD zeros s t m p w W L sW tW := by
  have hp : bPar (B0Prim.sigIn arr wtE wtH wtD zeros s t m p w W L sW tW) = (s, t, m, p, w, W, L) := by
    simp only [bPar]; rw [bT_sigIn]
    simp [reg]
    omega
  simp only [bSem, bCost, hp]; rw [bT_sigIn]
  simp [reg]

theorem bSpec (σ : Fin (49 + 91) → WTape) (hσ : BPre σ) :
    HoareTime B0Prim.progF (· = enc σ) (· = enc (bSem σ)) (bCost σ) := by
  obtain ⟨arr, wtE, wtH, wtD, zeros, s, t, m, p, w, W, L, sW, tW, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := hσ
  obtain ⟨e1, e2⟩ := bSem_sigIn arr wtE wtH wtD zeros s t m p w W L sW tW
  rw [e1, e2]
  have : NeZero s := ⟨by omega⟩
  exact B0Prim.prim_hoare arr wtE wtH wtD zeros s t m p w W L sW tW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    h14 h15 h16 h17 h18 h19 h20

/-- The `B̃₀` line loop as a primitive. -/
noncomputable def bPrim : Prim 0 := Prim.ofProgram B0Prim.progF (by omega) BPre bSem bCost bSpec

end IntegerMultBounds.Resampling.AxisPrims
