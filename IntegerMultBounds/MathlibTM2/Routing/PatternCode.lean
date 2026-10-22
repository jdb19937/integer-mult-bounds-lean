module

public import IntegerMultBounds.MathlibTM2.Routing.PatternGate
public import IntegerMultBounds.MathlibTM2.Host.IndexCode
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-!
# Concrete two-pattern callbacks

Both operand words are computed by fixed descriptor interpreters from the current
source field. Optional selectors provide inactive zeros without restricting any
physical address bit. A three-input code pass combines the operands while reading
the current target. Both operands and all scratch are cleared afterwards.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

inductive PatternReg (nf : ℕ) where
  | fld (f : Fin nf)
  | desc (k : Fin 2) | word (k : Fin 2)
  | ts | tm | dst | spare (k : Fin 3) | st
  deriving DecidableEq

def patternStatic (A : ℕ) {nf W L : ℕ} (s : Fin 2 → Fin L → Option (Fin W)) :
    PatternReg nf → List (Fin (A + 4))
  | .desc k => (patternTable (s k)).flatten.map bitSymbol
  | _ => []

/-- Static descriptors and empty scratch beside field counters for the live index. -/
def PatternInv {T A nf W L : ℕ} (len : Fin nf → ℕ) (ι : PatternReg nf → Fin T)
    (s : Fin 2 → Fin L → Option (Fin W)) (R : Fin T → List (Fin (A + 4))) (i : ℕ) : Prop :=
  ∀ r, r ≠ .st → R (ι r) = match r with
    | .fld f => binSyms (len f) (digit len f i)
    | _ => patternStatic A s r

variable {T Q A nf W L : ℕ} {U P : Type}

def patternCodeInputs (ι : PatternReg nf → Fin T) (ft : Fin nf) : Fin 3 → Fin T :=
  ![ι (.fld ft), ι (.word 0), ι (.word 1)]

/-- Prepare two patterns, evaluate the code automaton and clear both patterns. -/
def patternCode (ι : PatternReg nf → Fin T) (fs ft : Fin nf) {nd : ℕ}
    (C : CAuto A 3 nd) : Pr P T Q A U :=
  .seq (readPattern (ι (.fld fs)) (ι (.desc 0)) (ι .ts) (ι .tm) (ι .dst) (ι (.word 0)) (ι .st))
    (.seq (readPattern (ι (.fld fs)) (ι (.desc 1)) (ι .ts) (ι .tm) (ι .dst) (ι (.word 1)) (ι .st))
      (.seq (codePass (patternCodeInputs ι ft) (fun k => ι (.spare k)) (ι .st) C)
        (.seq (bclear (ι (.word 0))) (bclear (ι (.word 1))))))

def patternCodeCost (L W : ℕ) : ℕ := L * (12 * W + 38) + 24

variable (body : P → Pr P T Q A U) {len : Fin nf → ℕ} {ι : PatternReg nf → Fin T}

/-- The mixed-control callback has a complete live-index `CodeSpec`, with actual
execution and both source scans, all cleanup and code evaluation charged. -/
theorem patternCode_spec (hι : Function.Injective ι) (fs ft : Fin nf)
    (hs : len fs = W) (ht : len ft = L)
    (s : Fin 2 → Fin L → Option (Fin W)) {nd : ℕ} (C : CAuto A 3 nd) :
    CodeSpec body (patternCode ι fs ft C) (fun f => ι (.fld f)) len (ι .st)
      (fun k => ∃ r, ι r = k) (PatternInv len ι s) (codeSel C)
      (fun i => C.eval L ![digit len ft i, patternValue (s 0) (digit len fs i),
        patternValue (s 1) (digit len fs i)]) (patternCodeCost L W) where
  runs i v S hI := by
    have hne : ∀ {r r' : PatternReg nf}, r ≠ r' → ι r ≠ ι r' := fun h => hι.ne h
    have hzero : ∀ k : Fin 2, S.R (ι (.word k)) = [] := fun k => hI (.word k) (by simp)
    have hsrc : S.R (ι (.fld fs)) =
        (List.ofFn fun q : Fin W => (digit len fs i).testBit q.val).map bitSymbol := by
      simpa [hs, binSyms_eq, binBits] using hI (.fld fs) (by simp)
    have hregs (k : Fin 2) :
        [ι (.fld fs), ι (.desc k), ι .ts, ι .tm, ι .dst, ι (.word k)].Nodup := by
      simp [hι.eq_iff]
    obtain ⟨v₁, hu₁, he₁⟩ := readPattern_exec body (cs := ι .st) (hregs 0) (s 0)
      (fun q : Fin W => (digit len fs i).testBit q.val) v S hsrc
      (hI (.desc 0) (by simp)) (hI .ts (by simp)) (hI .tm (by simp)) (hI .dst (by simp))
    rw [hzero 0, List.append_nil, ← patternValue_bits, ← binSyms_eq] at he₁
    let p (k : Fin 2) := patternValue (s k) (digit len fs i)
    let R₁ := Function.update S.R (ι (.word 0)) (binSyms L (p 0))
    have hkeep₁ (r : PatternReg nf) (hr : r ≠ .word 0) : R₁ (ι r) = S.R (ι r) := by
      simp only [R₁, Function.update_of_ne (hne hr)]
    obtain ⟨v₂, hu₂, he₂⟩ := readPattern_exec body (cs := ι .st) (hregs 1) (s 1)
      (fun q : Fin W => (digit len fs i).testBit q.val) v₁ { S with R := R₁ }
      (by dsimp only; rw [hkeep₁ _ (by simp)]; exact hsrc)
      (by dsimp only; rw [hkeep₁ _ (by simp)]; exact hI (.desc 1) (by simp))
      (by dsimp only; rw [hkeep₁ _ (by simp)]; exact hI .ts (by simp))
      (by dsimp only; rw [hkeep₁ _ (by simp)]; exact hI .tm (by simp))
      (by dsimp only; rw [hkeep₁ _ (by simp)]; exact hI .dst (by simp))
    dsimp only at he₂
    rw [hkeep₁ _ (by simp), hzero 1, List.append_nil, ← patternValue_bits, ← binSyms_eq] at he₂
    let R₂ := Function.update R₁ (ι (.word 1)) (binSyms L (p 1))
    have hlay : CodeLayout (patternCodeInputs ι ft) (fun k => ι (.spare k)) (ι .st) := {
      rs_inj := by
        intro k k' he
        fin_cases k <;> fin_cases k' <;> simp_all [patternCodeInputs, hι.eq_iff]
      tmps_inj := fun k k' he => by simpa using hι he
      rs_tmps := by intro k k'; fin_cases k <;> simp [patternCodeInputs, hι.eq_iff]
      rs_st := by intro k; fin_cases k <;> simp [patternCodeInputs, hι.eq_iff]
      tmps_st := by intro k; simp [hι.eq_iff] }
    obtain ⟨v₃, hu₃, hsc₃, he₃⟩ := codePass_exec body hlay C L
      ![digit len ft i, p 0, p 1] v₂ { S with R := R₂ }
      (fun k => by
        fin_cases k
        · change R₂ (ι (.fld ft)) = _
          simp only [R₂, Function.update_of_ne (hne (show PatternReg.fld ft ≠ .word 1 by simp)),
            R₁, Function.update_of_ne (hne (show PatternReg.fld ft ≠ .word 0 by simp))]
          simpa [ht] using hI (.fld ft) (by simp)
        · change R₂ (ι (.word 0)) = _
          simp [R₂, R₁, hι.eq_iff]
        · change R₂ (ι (.word 1)) = _
          simp [R₂])
      (fun k => by
        change R₂ (ι (.spare k)) = _
        simp only [R₂, Function.update_of_ne (hne (show PatternReg.spare k ≠ .word 1 by simp)),
          R₁, Function.update_of_ne (hne (show PatternReg.spare k ≠ .word 0 by simp))]
        exact hI (.spare k) (by simp))
    obtain ⟨v₄, hu₄, hsc₄, he₄⟩ := bclear_exec body (ι (.word 0)) v₃ { S with R := R₂ }
    let R₃ := Function.update R₂ (ι (.word 0)) []
    obtain ⟨v₅, hu₅, hsc₅, he₅⟩ := bclear_exec body (ι (.word 1)) v₄ { S with R := R₃ }
    have hlen₀ : (R₂ (ι (.word 0))).length = L := by simp [R₂, R₁, hι.eq_iff]
    have hlen₁ : (R₃ (ι (.word 1))).length = L := by simp [R₃, R₂, hι.eq_iff]
    have hfin : Function.update R₃ (ι (.word 1)) [] = S.R := by
      funext k
      by_cases hk₀ : k = ι (.word 0)
      · subst k; simp [R₃, R₂, R₁, hι.eq_iff, hzero]
      by_cases hk₁ : k = ι (.word 1)
      · subst k; simp [hzero]
      simp [R₃, R₂, R₁, hk₀, hk₁]
    refine ⟨v₅, (L * (6 * W + 14) + 8) + ((L * (6 * W + 14) + 8) +
      ((6 * L + 4) + ((2 * (R₂ (ι (.word 0))).length + 2) +
        (2 * (R₃ (ι (.word 1))).length + 2)))),
      hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_, ?_, ?_⟩
    · apply le_of_eq
      simp only [hlen₀, hlen₁, patternCodeCost]
      ring
    · rw [hsc₅, hsc₄, hsc₃, codeSel_val]
      rfl
    · exact Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄
        (Exec.cast he₅ rfl (by rw [hfin])))))
  cf_inj := fun f f' he => by simpa using hι he
  cf_Y := fun f => ⟨.fld f, rfl⟩
  digits := fun R i hI f => hI (.fld f) (by simp)
  frame := by
    intro R R' i hI hR r hr
    rw [hR (ι r) ⟨r, rfl⟩]
    exact hI r hr
  reidx := by
    intro R R' i j hI hfields hother r hr
    cases r <;> first
      | exact hfields _
      | contradiction
      | (rw [hother _ (fun f => hι.ne (by simp))]; exact hI _ (by simp))

end IntegerMultBounds.MathlibTM2.Routing
