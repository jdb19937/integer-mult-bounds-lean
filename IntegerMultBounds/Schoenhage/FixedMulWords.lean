module

public import IntegerMultBounds.Schoenhage.ExactMul
public import IntegerMultBounds.Machine.FixedMulValue
public import IntegerMultBounds.Schoenhage.Reverse

/-! The signed fixed-point multiply `FixedMul.result` as a word program on the
ring product's bank, with the quasi-linear product of `ExactMul`. From the
operands on `zF`, `zG` and rulers `ones p`, `ones w` on `iP`, `iW`: the signs
are read from reversed copies, the magnitudes are formed by the streaming
two's-complement negation `FixedMulRules.neg`, the exact product of the magnitudes is
the padded product `FixedMul.padProd` (`padProd_eq_bits`), its bits `p` to
`p + w` are cut out by `drop` and `take`, and negated when the signs differ
(`runs_fixedMulW`). Every scratch tape is empty again. -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule
open TwosComplement (negWord)

namespace FixedMulRules

/-- Two's-complement negation: copy up to and including the lowest one, then
complement. -/
abbrev neg : Rule 0 where
  Q := Bool
  q0 := false
  step q b _ := (q || b, some (some (if q then !b else b)), fun _ => false)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

theorem go_neg (w : List Bool) (ws : Fin 0 → List Bool) :
    ∀ q, (go neg q w ws).2.1 = (if q then w.map not else negWord w).map some := by
  induction w generalizing ws with
  | nil => intro q; cases q <;> simp [go, negWord]
  | cons b w ih =>
    intro q
    cases q <;> cases b <;> simp [go, ih, negWord]

theorem output_neg (w : List Bool) (ws : Fin 0 → List Bool) : output neg w ws = syms [negWord w] := by
  simp [output, syms_cons, go_neg]

end FixedMulRules

/-! ### Values and words -/

theorem bval_eq_value (bs : List Bool) : bval bs = Counter.value bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [bval, Counter.value, ih]

theorem eq_bits_of_length {bs : List Bool} {n : ℕ} (h : bs.length = n) : bs = bits n (bval bs) := by
  subst h; exact (bits_bval bs).symm

theorem padProd_eq_bits {x y : List Bool} {w : ℕ} (hx : x.length = w) (hy : y.length = w) :
    FixedMul.padProd x y w = bits (2 * w) (bval (FixedMul.mag x) * bval (FixedMul.mag y)) := by
  have hl := FixedMul.padProd_length x y w hx hy
  rw [eq_bits_of_length hl]
  congr 1
  unfold FixedMul.padProd
  rw [bval_eq_value, bval_eq_value, bval_eq_value, TwosComplement.value_append,
    TwosComplement.value_replicate_false, mul_zero, add_zero, BinaryMultiply.horner_value]

theorem field_eq_fit (xs : List Bool) (s d : ℕ) : Gather.field xs s d = Rules.fit d (xs.drop s) := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih =>
    rw [FixedMul.field_cons, ih, Rules.fit]
    congr 1
    · rcases h : xs.drop s with _ | ⟨b, r⟩
      · have : xs.length ≤ s := by simpa using h
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
      · have hs : s < xs.length := by
          by_contra hc; push Not at hc; simp [List.drop_eq_nil_of_le hc] at h
        have := congrArg List.head? h
        rw [List.head?_drop] at this
        simp [List.getD_eq_getElem?_getD, this]
    · rw [List.drop_add_one_eq_tail_drop]

theorem startsOne_reverse {x : List Bool} (hx : x ≠ []) :
    StartsOne (reg x.reverse) ↔ x.getLastD false = true := by
  obtain ⟨l, b, rfl⟩ := List.eq_nil_or_concat x |>.resolve_left hx
  cases b <;> simp [StartsOne, reg]

/-! ### One streamed word -/

/-- Stream the word on `s` through `R` onto the empty tape `d`, then rewind both. -/
noncomputable def streamTo (R : Rule 0) (s d : Fin 𝕌) (h : s ≠ d) : Cmd 0 𝕌 :=
  .seq (op0 R false s d h) (.seq (rewind s) (rewind d))

theorem runs_streamTo (R : Rule 0) {s d : Fin 𝕌} (h : s ≠ d) {x v : List Bool} (τ : Fin 𝕌 → WTape)
    (hs : τ s = reg x) (hd : τ d = emp) (ho : output R x (fun j => j.elim0) = syms [v]) :
    Runs (streamTo R s d h) τ (· = Function.update τ d (reg v))
      (time R x (fun j => j.elim0) + x.length + v.length + 10) := by
  apply Runs.of_wp
  simp only [streamTo, WP, wp_op0, wp_rewind]
  have hc : (τ s).cur = x := by rw [hs]; rfl
  rw [hc, ho, parse_syms]
  refine ⟨⟨by tsimp [hs, reg], by tsimp [hd, emp], rfl, by simp⟩, ?_, ?_⟩
  · funext i
    by_cases h1 : i = d
    · subst h1; tsimp [h.symm, hd, emp, reg, WTape.put]
    · by_cases h2 : i = s
      · subst h2; tsimp [h, hs, reg, WTape.next, WTape.cur, h1]
      · tsimp [h1, h2]
  · tsimp [hd, emp, reg, WTape.put, hs, WTape.next, WTape.cur, h, h.symm]
    omega

/-! ### Magnitudes -/

/-- `d = mag x` from `s = x` and `rv = x` reversed. -/
noncomputable def magTo (s rv d : Fin 𝕌) (h : s ≠ d) : Cmd 0 𝕌 :=
  .cond rv (streamTo FixedMulRules.neg s d h) (streamTo Rules.copy s d h)

theorem runs_magTo {s rv d : Fin 𝕌} (h : s ≠ d) {x : List Bool} (hx : x ≠ []) (τ : Fin 𝕌 → WTape)
    (hs : τ s = reg x) (hr : τ rv = reg x.reverse) (hd : τ d = emp) :
    Runs (magTo s rv d h) τ (· = Function.update τ d (reg (FixedMul.mag x))) (3 * x.length + 20) := by
  by_cases hl : x.getLastD false = true
  · have r := runs_streamTo FixedMulRules.neg h τ hs hd (FixedMulRules.output_neg x _)
    have t1 := time_le FixedMulRules.neg x (fun j => j.elim0) 0 (fun j => j.elim0)
    have hB : FixedMulRules.neg.B = 1 := rfl
    rw [show FixedMul.mag x = negWord x by unfold FixedMul.mag; rw [hl]; rfl]
    refine (Runs.cond_true (by rw [hr]; exact (startsOne_reverse hx).2 hl) r).le ?_
    rw [TwosComplement.negWord_length]; omega
  · have r := runs_streamTo Rules.copy h τ hs hd (Rules.output_copy x _)
    rw [show FixedMul.mag x = x by unfold FixedMul.mag; rw [Bool.not_eq_true] at hl; rw [hl]; rfl]
    refine (Runs.cond_false (by rw [hr]; exact fun h' => hl ((startsOne_reverse hx).1 h')) r).le ?_
    rw [time_copy]; omega

/-! ### Reversed copies, the double ruler, the field -/

/-- `d` = the word on `s` reversed. -/
noncomputable def revTo (s d : Fin 𝕌) (h : s ≠ d) : Cmd 0 𝕌 := .seq (revw s d h) (.seq (rewind s) (rewind d))

theorem runs_revTo {s d : Fin 𝕌} (h : s ≠ d) {x : List Bool} (τ : Fin 𝕌 → WTape)
    (hs : τ s = reg x) (hd : τ d = emp) :
    Runs (revTo s d h) τ (· = Function.update τ d (reg x.reverse)) (5 * x.length + 20) := by
  have s1 := runs_revw (a := 0) h τ (L := []) (R := []) (w := x) (by rw [hs]; rfl) (by rw [hd]; rfl)
  refine (Runs.then s1 (Runs.then (runs_rewind s _) (runs_rewind d _))).mono (fun τ' e => ?_) ?_
  · rw [e]
    funext i
    by_cases h1 : i = d
    · subst h1; tsimp [h.symm, hd, emp, reg]
    · by_cases h2 : i = s
      · subst h2; tsimp [h, hs, reg, h1]
      · tsimp [h1, h2]
  · tsimp [hd, emp, h, h.symm]
    omega

/-- `xC = ones (2 w)` from `iW = ones w`. -/
noncomputable def ruler2 : Cmd 0 𝕌 :=
  .seq (op0 Rules.copy false iW xC (by decide)) <| .seq (rewind iW) <|
  .seq (op0 Rules.copy true iW xC (by decide)) <| .seq (rewind iW) (rewind xC)

theorem runs_ruler2 {w : ℕ} (τ : Fin 𝕌 → WTape) (hW : τ iW = reg (ones w)) (hC : τ xC = emp) :
    Runs ruler2 τ (· = Function.update τ xC (reg (ones (2 * w)))) (10 * w + 40) := by
  apply Runs.of_wp
  simp only [ruler2, WP, wp_op0, wp_rewind]
  tsimp [hW, hC, emp, reg, Rules.output_copy, ones_append]
  refine ⟨?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hW, hC, emp, reg, ones_append, two_mul] at *
  · simp only [time_copy, length_ones]
    omega

/-- `kR` = bits `p` to `p + w` of `xQ`, through `kS`. -/
noncomputable def fieldOut : Cmd 0 𝕌 :=
  .seq (op1 Rules.drop false xQ iP kS (by decide) (by decide) (by decide)) <| .seq (rewind xQ) <|
  .seq (rewind iP) <| .seq (rewind kS) <|
  .seq (op1 Rules.take false iW kS kR (by decide) (by decide) (by decide)) <| .seq (rewind iW) <|
  .seq (rewind kS) (rewind kR)

theorem runs_fieldOut {p w : ℕ} {z : List Bool} (τ : Fin 𝕌 → WTape) (hQ : τ xQ = reg z)
    (hP : τ iP = reg (ones p)) (hW : τ iW = reg (ones w)) (hS : τ kS = emp) (hR : τ kR = emp) :
    Runs fieldOut τ (· = Function.update (Function.update τ kS (reg (z.drop p)))
      kR (reg (Rules.fit w (z.drop p)))) (6 * z.length + 6 * p + 6 * w + 100) := by
  apply Runs.of_wp
  simp only [fieldOut, WP, wp_op1, wp_rewind]
  tsimp [hQ, hP, hW, hS, hR, emp, reg, Rules.output_drop, Rules.output_take]
  have t1 := time_le Rules.drop z (fun _ => ones p) p (fun _ => by simp)
  have t2 := time_le Rules.take (ones w) (fun _ => z.drop p) z.length (fun _ => by simp)
  refine ⟨?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hQ, hP, hW, hS, hR, emp, reg] at *
  · simp only [length_ones] at t1 t2 ⊢
    omega

/-! ### The sign of the result -/

/-- Copy `kR` to `zO`, negated when the reversed operands on `lR`, `lI` start differently. -/
noncomputable def signOut : Cmd 0 𝕌 :=
  .cond lR (.cond lI (streamTo Rules.copy kR zO (by decide)) (streamTo FixedMulRules.neg kR zO (by decide)))
    (.cond lI (streamTo FixedMulRules.neg kR zO (by decide)) (streamTo Rules.copy kR zO (by decide)))

theorem runs_signOut {x y F : List Bool} (hx : x ≠ []) (hy : y ≠ []) (τ : Fin 𝕌 → WTape)
    (hX : τ lR = reg x.reverse) (hY : τ lI = reg y.reverse) (hF : τ kR = reg F) (hO : τ zO = emp) :
    Runs signOut τ (· = Function.update τ zO
      (reg (if x.getLastD false = y.getLastD false then F else negWord F))) (3 * F.length + 30) := by
  have rc := runs_streamTo Rules.copy (show kR ≠ zO by decide) τ hF hO (Rules.output_copy F _)
  have rn := runs_streamTo FixedMulRules.neg (show kR ≠ zO by decide) τ hF hO (FixedMulRules.output_neg F _)
  have t1 := time_le FixedMulRules.neg F (fun j => j.elim0) 0 (fun j => j.elim0)
  have hB : FixedMulRules.neg.B = 1 := rfl
  rw [time_copy] at rc
  rw [TwosComplement.negWord_length] at rn
  have sx := startsOne_reverse hx; have sy := startsOne_reverse hy
  rw [← hX] at sx; rw [← hY] at sy
  cases ex : x.getLastD false <;> cases ey : y.getLastD false
  · exact (Runs.cond_false (by rw [sx, ex]; simp) (Runs.cond_false (by rw [sy, ey]; simp) rc)).le (by omega)
  · exact (Runs.cond_false (by rw [sx, ex]; simp) (Runs.cond_true (by rw [sy, ey]) rn)).le (by omega)
  · exact (Runs.cond_true (by rw [sx, ex]) (Runs.cond_false (by rw [sy, ey]; simp) rn)).le (by omega)
  · exact (Runs.cond_true (by rw [sx, ex]) (Runs.cond_true (by rw [sy, ey]) rc)).le (by omega)

/-! ### The whole multiply -/

/-- Clear the scratch tapes. -/
noncomputable def fmClean : Cmd 0 𝕌 :=
  .seq (clear lR) <| .seq (clear lI) <| .seq (clear xA) <| .seq (clear xB) <| .seq (clear xC) <|
  .seq (clear xQ) <| .seq (clear kS) (clear kR)

/-- Signs, magnitudes, exact product, field, sign of the result. -/
noncomputable def fixedMulW : Cmd 0 𝕌 :=
  .seq (revTo zF lR (by decide)) <| .seq (revTo zG lI (by decide)) <| .seq ruler2 <|
  .seq (magTo zF lR xA (by decide)) <| .seq (magTo zG lI xB (by decide)) <| .seq exactMul <|
  .seq fieldOut <| .seq signOut fmClean

/-- The cost of `fixedMulW` at width `w`. -/
noncomputable def fixedMulWCost (w : ℕ) (x y : List Bool) : ℕ :=
  exCost (2 * w) (FixedMul.mag x) (FixedMul.mag y) + 200 * w + 1000

set_option maxHeartbeats 8000000 in
/-- `zO = FixedMul.result x y p w` from `zF = x`, `zG = y`, `iP = ones p`, `iW = ones w`. -/
theorem runs_fixedMulW {x y : List Bool} {p w : ℕ} (hx : x.length = w) (hy : y.length = w) (hw : 1 ≤ w)
    (hpw : p ≤ w) (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hF : τ zF = reg x) (hG : τ zG = reg y)
    (hP : τ iP = reg (ones p)) (hW : τ iW = reg (ones w)) (hR : τ lR = emp) (hI : τ lI = emp)
    (hA : τ xA = emp) (hB : τ xB = emp) (hC : τ xC = emp) (hQ : τ xQ = emp) (hS : τ kS = emp)
    (hK : τ kR = emp) (hN : τ kN = emp) (hE : τ xE = emp) (hXP : τ xP = emp) (hH : τ zH = emp)
    (hO : τ zO = emp) :
    Runs fixedMulW τ (· = Function.update τ zO (reg (FixedMul.result x y p w))) (fixedMulWCost w x y) := by
  have hx0 : x ≠ [] := by rintro rfl; simp at hx; omega
  have hy0 : y ≠ [] := by rintro rfl; simp at hy; omega
  have hmx := FixedMul.mag_length x; have hmy := FixedMul.mag_length y
  have own : ∀ s : Fin 𝕌, 64 ≤ s.val → Own s := fun s h => h
  have s1 := runs_revTo (show zF ≠ lR by decide) τ hF hR
  set τ₁ := Function.update τ lR (reg x.reverse)
  have s2 := runs_revTo (show zG ≠ lI by decide) (x := y) τ₁ (by tsimp [τ₁, hG]) (by tsimp [τ₁, hI])
  set τ₂ := Function.update τ₁ lI (reg y.reverse)
  have s3 := runs_ruler2 (w := w) τ₂ (by tsimp [τ₂, τ₁, hW]) (by tsimp [τ₂, τ₁, hC])
  set τ₃ := Function.update τ₂ xC (reg (ones (2 * w)))
  have s4 := runs_magTo (rv := lR) (show zF ≠ xA by decide) hx0 τ₃ (by tsimp [τ₃, τ₂, τ₁, hF]) (by tsimp [τ₃, τ₂, τ₁])
    (by tsimp [τ₃, τ₂, τ₁, hA])
  set τ₄ := Function.update τ₃ xA (reg (FixedMul.mag x))
  have s5 := runs_magTo (rv := lI) (show zG ≠ xB by decide) hy0 τ₄ (by tsimp [τ₄, τ₃, τ₂, τ₁, hG])
    (by tsimp [τ₄, τ₃, τ₂, τ₁]) (by tsimp [τ₄, τ₃, τ₂, τ₁, hB])
  set τ₅ := Function.update τ₄ xB (reg (FixedMul.mag y))
  have hc5 : Clean τ₅ :=
    clean_update_own (clean_update_own (clean_update_own (clean_update_own (clean_update_own hc
      (own _ (by decide)) _) (own _ (by decide)) _) (own _ (by decide)) _) (own _ (by decide)) _)
      (own _ (by decide)) _
  have s6 := runs_exactMul (n := 2 * w) (x := FixedMul.mag x) (y := FixedMul.mag y) (by omega) (by omega)
    τ₅ hc5 (by tsimp [τ₅, τ₄]) (by tsimp [τ₅]) (by tsimp [τ₅, τ₄, τ₃])
    (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hN]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hE])
    (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hXP]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hQ]) (by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁, hH])
  rw [← padProd_eq_bits hx hy] at s6
  set z := FixedMul.padProd x y w
  have hz : z.length = 2 * w := FixedMul.padProd_length x y w hx hy
  set τ₆ := Function.update τ₅ xQ (reg z)
  have s7 := runs_fieldOut (p := p) (w := w) (z := z) τ₆ (by tsimp [τ₆]) (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hP])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hW]) (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hS])
    (by tsimp [τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hK])
  rw [← field_eq_fit] at s7
  set F := Gather.field z p w
  have hFl : F.length = w := by simp [F, Gather.field]
  set τ₇ := Function.update (Function.update τ₆ kS (reg (z.drop p))) kR (reg F)
  have s8 := runs_signOut (F := F) hx0 hy0 τ₇ (by tsimp [τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁]) (by tsimp [τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁])
    (by tsimp [τ₇]) (by tsimp [τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, hO])
  have hres : (if x.getLastD false = y.getLastD false then F else negWord F) = FixedMul.result x y p w := rfl
  rw [hres] at s8
  set τ₈ := Function.update τ₇ zO (reg (FixedMul.result x y p w))
  have s9 : Runs fmClean τ₈ (· = Function.update τ zO (reg (FixedMul.result x y p w))) (30 * w + 100) := by
    apply Runs.of_wp
    simp only [fmClean, WP, wp_clear]
    refine ⟨?_, ?_⟩
    · funext i
      simp only [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, Function.update_apply]
      split_ifs <;> (try subst_vars) <;> tsimp [emp, hR, hI, hA, hB, hC, hQ, hS, hK] at *
    · tsimp [τ₈, τ₇, τ₆, τ₅, τ₄, τ₃, τ₂, τ₁, reg, WTape.words]
      simp [hmx, hmy, hx, hy, hz, hFl]
      omega
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 (Runs.then s6
    (Runs.then s7 (Runs.then s8 s9)))))))).le ?_
  unfold fixedMulWCost
  simp only [hmx, hmy, hx, hy, hz, hFl] at *
  omega

end IntegerMultBounds.Schoenhage
