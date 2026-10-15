module

public import IntegerMultBounds.MathlibTM2.Fast.CMulRegs

/-!
# The three passes of the complex fixed-point product, and list loops

* `split_runs`: the split pass (`splitP`) on a coefficient `coeffSyms A w (red w N)` on top of an
  operand register: the save register gains the coefficient's symbols (reversed), and four
  registers gain the two's complement residues of `re N`, `-re N`, `im N`, `-im N` modulo `2^w`
  (`rbits`), most significant bit on top.
* `comb_runs`: the combination pass (`combP`) on two `K`-bit numbers `X₁`, `X₂` with mode bits
  `m = f (sign bits)`: the residues modulo `2^K` of `Z = bsgn m₁ X₁ + bsgn m₂ X₂` and of `-Z`, most
  significant bit on top.
* `fin_runs`: the final pass (`finP`) on two `w`-bit numbers with signs `s₁`, `s₂` read from two
  sign registers: the output register gains the coefficient `(bsgn s₁ X₁, bsgn s₂ X₂)` modulo `2^w`
  as pair symbols, most significant pair on top.
* `cwhileP_runs`: `cwhileP g p` repeats `p` while register `g` is nonempty; one contract per element
  of a list gives the contract of the loop.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node

set_option linter.unusedSimpArgs false

/-- The coefficient symbols of a Gaussian integer. -/
abbrev csyms (A w : ℕ) (N : GaussianInt) : List (Fin (A + 4)) := coeffSyms A w (red w N)

/-- The `w`-bit two's complement residue of an integer as bit symbols. -/
abbrev rbits (A w : ℕ) (x : ℤ) : List (Fin (A + 4)) := binSyms w (x : ZMod (2 ^ w)).val

/-! ### Input columns -/

/-- The input columns of the split pass. -/
def splitCol (A w : ℕ) (N : GaussianInt) : Fin w → Fin 1 → Fin (A + 4) := fun t _ =>
  pairSym A ((N.re : ZMod (2 ^ w)).val.testBit t) ((N.im : ZMod (2 ^ w)).val.testBit t)

/-- The input columns of two binary numerals. -/
def binCol (A K : ℕ) (X₁ X₂ : ℕ) : Fin K → Fin 2 → Fin (A + 4) := fun t =>
  ![bitSymbol (X₁.testBit t), bitSymbol (X₂.testBit t)]

lemma getD_cs_append {A w : ℕ} (N : GaussianInt) (rest : List (Fin (A + 4))) (t : Fin w) :
    (csyms A w N ++ rest).getD t blank = splitCol A w N t 0 := by
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [csyms, coeffSyms, splitCol, red, List.getD_eq_getElem?_getD]

lemma getD_binSyms_append {A K : ℕ} (X : ℕ) (rest : List (Fin (A + 4))) (t : Fin K) :
    (binSyms K X ++ rest).getD t blank = bitSymbol (X.testBit t) := by
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [binSyms, List.getD_eq_getElem?_getD]

lemma splitD_bitsA {A w : ℕ} (hA : 4 ≤ A) (N : GaussianInt) :
    (splitD A).bitsA false false (splitCol A w N) 0 =
      List.ofFn fun t : Fin w => ((-N.re : ℤ) : ZMod (2 ^ w)).val.testBit t := by
  simp only [Duo.bitsA, splitD, splitCol, pairRe_pairSym hA]
  exact carryRun_neg w N.re

lemma splitD_bitsB {A w : ℕ} (hA : 4 ≤ A) (N : GaussianInt) :
    (splitD A).bitsB false false (splitCol A w N) 0 =
      List.ofFn fun t : Fin w => ((-N.im : ℤ) : ZMod (2 ^ w)).val.testBit t := by
  simp only [Duo.bitsB, splitD, splitCol, pairIm_pairSym hA]
  exact carryRun_neg w N.im

lemma combD_bitsA {A K : ℕ} (m₁ m₂ : Bool) (X₁ X₂ : ℕ) :
    (combD A).bitsA m₁ m₂ (binCol A K X₁ X₂) 0 =
      List.ofFn fun t : Fin K => ((bsgn m₁ * X₁ + bsgn m₂ * X₂ : ℤ) : ZMod (2 ^ K)).val.testBit t := by
  simp only [Duo.bitsA, combD, binCol, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, symBit_bitSymbol]
  exact carryRun_comb K m₁ m₂ X₁ X₂

lemma combD_bitsB {A K : ℕ} (m₁ m₂ : Bool) (X₁ X₂ : ℕ) :
    (combD A).bitsB m₁ m₂ (binCol A K X₁ X₂) 0 =
      List.ofFn fun t : Fin K =>
        ((-(bsgn m₁ * X₁ + bsgn m₂ * X₂) : ℤ) : ZMod (2 ^ K)).val.testBit t := by
  simp only [Duo.bitsB, combD, binCol, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, symBit_bitSymbol]
  exact carryRun_comb_neg K m₁ m₂ X₁ X₂

lemma finD_bitsA {A K : ℕ} (m₁ m₂ : Bool) (X₁ X₂ : ℕ) :
    (finD A).bitsA m₁ m₂ (binCol A K X₁ X₂) 0 =
      List.ofFn fun t : Fin K => ((bsgn m₁ * X₁ : ℤ) : ZMod (2 ^ K)).val.testBit t := by
  simp only [Duo.bitsA, finD, binCol, Matrix.cons_val_zero, symBit_bitSymbol]
  exact carryRun_sgn K m₁ X₁

lemma finD_bitsB {A K : ℕ} (m₁ m₂ : Bool) (X₁ X₂ : ℕ) :
    (finD A).bitsB m₁ m₂ (binCol A K X₁ X₂) 0 =
      List.ofFn fun t : Fin K => ((bsgn m₂ * X₂ : ℤ) : ZMod (2 ^ K)).val.testBit t := by
  simp only [Duo.bitsB, finD, binCol, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    symBit_bitSymbol]
  exact carryRun_sgn K m₂ X₂

lemma splitD_out (A : ℕ) (col : Fin 1 → Fin (A + 4)) (b₁ b₂ : Bool) :
    (splitD A).out col b₁ b₂ = ![col 0, bitSymbol (pairRe (col 0)), bitSymbol b₁,
      bitSymbol (pairIm (col 0)), bitSymbol b₂] := rfl

lemma combD_out (A : ℕ) (col : Fin 2 → Fin (A + 4)) (b₁ b₂ : Bool) :
    (combD A).out col b₁ b₂ = ![bitSymbol b₁, bitSymbol b₂] := rfl

lemma finD_out (A : ℕ) (col : Fin 2 → Fin (A + 4)) (b₁ b₂ : Bool) :
    (finD A).out col b₁ b₂ = ![pairSym A b₁ b₂] := rfl

section Passes

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {cr : CR → Fin T}
  {ι : Fin 64 → Fin T}

/-- The split pass on the operand register `I`: save register `Sv`, outputs `O₀ … O₃`, counter
`C`, spare `Tm`. -/
def splitP (cr : CR → Fin T) (I Sv O₀ O₁ O₂ O₃ C Tm : CR) : Pr P T Q A U :=
  dpass (splitD A) (fun _ _ _ _ => (false, false)) (cr Tm) (cr Tm) (cr Tm) (cr Tm)
    (fun i => cr (![I] i)) (fun j => cr (![Sv, O₀, O₁, O₂, O₃] j)) (cr C) (cr Tm)

theorem split_runs (hcr : Function.Injective cr) (hA : 96 ≤ A) {I Sv O₀ O₁ O₂ O₃ C Tm : CR}
    (hd : [I, Sv, O₀, O₁, O₂, O₃, C, Tm].Nodup) {ρ : CR → List (Fin (A + 4))} {w : ℕ}
    (N : GaussianInt) (rest : List (Fin (A + 4))) (hI : ρ I = csyms A w N ++ rest)
    (hC : (ρ C).length = w) (hT : ρ Tm = []) :
    CRuns body cr ι (splitP cr I Sv O₀ O₁ O₂ O₃ C Tm) ρ
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update ρ I rest) Sv ((csyms A w N).reverse ++ ρ Sv))
        O₀ ((rbits A w N.re).reverse ++ ρ O₀)) O₁ ((rbits A w (-N.re)).reverse ++ ρ O₁))
        O₂ ((rbits A w N.im).reverse ++ ρ O₂)) O₃ ((rbits A w (-N.im)).reverse ++ ρ O₃))
      (5 * w + 4) := by
  have hA4 : 4 ≤ A := by omega
  have hd' : (List.ofFn ![I] ++ List.ofFn ![Sv, O₀, O₁, O₂, O₃] ++ [C, Tm]).Nodup := by
    simpa using hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h05, h06, h07⟩, ⟨h12, h13, h14, h15, h16, h17⟩,
    ⟨h23, h24, h25, h26, h27⟩, ⟨h34, h35, h36, h37⟩, ⟨h45, h46, h47⟩, ⟨h56, h57⟩, h67, -⟩ := hd
  refine dpass_runs hcr (splitD A) hA (splitD_bounded A) _ Tm Tm Tm Tm ![I]
    ![Sv, O₀, O₁, O₂, O₃] C Tm hd' hC hT (splitCol A w N) (fun i t => ?_) (false, false) rfl
    (fun i => ?_) (fun j => ?_) (fun r h1 h2 => ?_)
  · fin_cases i
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one, hI]
    exact getD_cs_append N rest t
  · fin_cases i
    simp [Function.update_apply, h01, h02, h03, h04, h05, hI]
  · fin_cases j
    · simp [Function.update_apply, h12, h13, h14, h15, splitD]
      rfl
    · simp [Function.update_apply, h23, h24, h25, splitD, splitCol, pairRe_pairSym hA4]
      rfl
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val, Function.update_apply, h34, h35,
        if_false, if_true, splitD_out, splitD_bitsA hA4, getD_ofFn_bool]
      rfl
    · simp [Function.update_apply, h45, splitD, splitCol, pairIm_pairSym hA4]
      rfl
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val, Function.update_apply,
        if_true, splitD_out, splitD_bitsB hA4, getD_ofFn_bool]
      rfl
  · have a0 := h1 0
    have b0 := h2 0; have b1 := h2 1; have b2 := h2 2; have b3 := h2 3; have b4 := h2 4
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.isValue] at a0 b0 b1 b2 b3 b4
    simp [Function.update_apply, Ne.symm a0, Ne.symm b0, Ne.symm b1, Ne.symm b2, Ne.symm b3,
      Ne.symm b4]

/-- The combination pass: inputs `I₁`, `I₂`, outputs `O₁`, `O₂`, mode bits from the top bits of
`ra … rd` through `f`. -/
def combP (cr : CR → Fin T) (f : Bool → Bool → Bool → Bool → Bool × Bool)
    (ra rb rc rd I₁ I₂ O₁ O₂ C Tm : CR) : Pr P T Q A U :=
  dpass (combD A) f (cr ra) (cr rb) (cr rc) (cr rd) (fun i => cr (![I₁, I₂] i))
    (fun j => cr (![O₁, O₂] j)) (cr C) (cr Tm)

theorem comb_runs (hcr : Function.Injective cr) (hA : 96 ≤ A)
    (f : Bool → Bool → Bool → Bool → Bool × Bool) (ra rb rc rd : CR) {I₁ I₂ O₁ O₂ C Tm : CR}
    (hd : [I₁, I₂, O₁, O₂, C, Tm].Nodup) {ρ : CR → List (Fin (A + 4))} {K X₁ X₂ : ℕ}
    {e₁ e₂ : List (Fin (A + 4))} (h₁ : ρ I₁ = binSyms K X₁ ++ e₁) (h₂ : ρ I₂ = binSyms K X₂ ++ e₂)
    (hC : (ρ C).length = K) (hT : ρ Tm = []) {m : Bool × Bool}
    (hm : f (topB (ρ ra)) (topB (ρ rb)) (topB (ρ rc)) (topB (ρ rd)) = m) :
    CRuns body cr ι (combP cr f ra rb rc rd I₁ I₂ O₁ O₂ C Tm) ρ
      (Function.update (Function.update (Function.update (Function.update ρ I₁ e₁) I₂ e₂)
        O₁ ((rbits A K (bsgn m.1 * X₁ + bsgn m.2 * X₂)).reverse ++ ρ O₁))
        O₂ ((rbits A K (-(bsgn m.1 * X₁ + bsgn m.2 * X₂))).reverse ++ ρ O₂))
      (5 * K + 4) := by
  have hd' : (List.ofFn ![I₁, I₂] ++ List.ofFn ![O₁, O₂] ++ [C, Tm]).Nodup := by
    simpa using hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h05⟩, ⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45,
    -⟩ := hd
  refine dpass_runs hcr (combD A) hA (combD_bounded A) f ra rb rc rd ![I₁, I₂] ![O₁, O₂] C Tm
    hd' hC hT (binCol A K X₁ X₂) (fun i t => ?_) m hm (fun i => ?_) (fun j => ?_)
    (fun r h1 h2 => ?_)
  · fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, h₁]
      exact getD_binSyms_append X₁ e₁ t
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, h₂]
      exact getD_binSyms_append X₂ e₂ t
  · fin_cases i
    · simp [Function.update_apply, h01, h02, h03, h₁]
    · simp [Function.update_apply, h12, h13, h₂]
  · fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Function.update_apply, h23,
        if_false, if_true, combD_out, combD_bitsA, getD_ofFn_bool]
      rfl
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Function.update_apply, if_true, combD_out, combD_bitsB, getD_ofFn_bool]
      rfl
  · have a0 := h1 0; have a1 := h1 1
    have b0 := h2 0; have b1 := h2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Fin.isValue] at a0 a1 b0 b1
    simp [Function.update_apply, Ne.symm a0, Ne.symm a1, Ne.symm b0, Ne.symm b1]

/-- The final pass: inputs `I₁`, `I₂`, output `O`, signs from the top bits of `ra`, `rb`. -/
def finP (cr : CR → Fin T) (ra rb I₁ I₂ O C Tm : CR) : Pr P T Q A U :=
  dpass (finD A) (fun a b _ _ => (a, b)) (cr ra) (cr rb) (cr ra) (cr rb)
    (fun i => cr (![I₁, I₂] i)) (fun j => cr (![O] j)) (cr C) (cr Tm)

theorem fin_runs (hcr : Function.Injective cr) (hA : 96 ≤ A) (ra rb : CR) {I₁ I₂ O C Tm : CR}
    (hd : [I₁, I₂, O, C, Tm].Nodup) {ρ : CR → List (Fin (A + 4))} {w X₁ X₂ : ℕ}
    {e₁ e₂ : List (Fin (A + 4))} (h₁ : ρ I₁ = binSyms w X₁ ++ e₁) (h₂ : ρ I₂ = binSyms w X₂ ++ e₂)
    (hC : (ρ C).length = w) (hT : ρ Tm = []) {s₁ s₂ : Bool} (hs₁ : topB (ρ ra) = s₁)
    (hs₂ : topB (ρ rb) = s₂) :
    CRuns body cr ι (finP cr ra rb I₁ I₂ O C Tm) ρ
      (Function.update (Function.update (Function.update ρ I₁ e₁) I₂ e₂)
        O ((coeffSyms A w (((bsgn s₁ * X₁ : ℤ) : ZMod (2 ^ w)),
          ((bsgn s₂ * X₂ : ℤ) : ZMod (2 ^ w)))).reverse ++ ρ O))
      (5 * w + 4) := by
  have hA4 : 4 ≤ A := by omega
  have hd' : (List.ofFn ![I₁, I₂] ++ List.ofFn ![O] ++ [C, Tm]).Nodup := by
    simpa using hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, -⟩ := hd
  refine dpass_runs hcr (finD A) hA (finD_bounded A) _ ra rb ra rb ![I₁, I₂] ![O] C Tm
    hd' hC hT (binCol A w X₁ X₂) (fun i t => ?_) (s₁, s₂) (by rw [hs₁, hs₂]) (fun i => ?_)
    (fun j => ?_) (fun r h1 h2 => ?_)
  · fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, h₁]
      exact getD_binSyms_append X₁ e₁ t
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, h₂]
      exact getD_binSyms_append X₂ e₂ t
  · fin_cases i
    · simp [Function.update_apply, h01, h02, h₁]
    · simp [Function.update_apply, h12, h₂]
  · fin_cases j
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one, Function.update_apply,
      if_true, finD_out, finD_bitsA, finD_bitsB, getD_ofFn_bool]
    rfl
  · have a0 := h1 0; have a1 := h1 1
    have b0 := h2 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Fin.isValue] at a0 a1 b0
    simp [Function.update_apply, Ne.symm a0, Ne.symm a1, Ne.symm b0]

end Passes

/-! ### Loops over lists -/

section Loops

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {cr : CR → Fin T}
  {ι : Fin 64 → Fin T}

/-- Repeat `p` while register `g` is nonempty. -/
def cwhileP (g : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR g)) (.loop (·.flag) (.seq p (.act (peekR g))))

/-- A loop over a list: the register file `st l done` holds the remaining elements `l` and the
processed ones `done`; register `g` is nonempty exactly while elements remain, and each element
satisfying `ok` is processed by `p` within `b` steps. -/
theorem cwhileP_runs (hdisj : ∀ r j, cr r ≠ ι j) {α : Type} (g : CR) (p : Pr P T Q A U)
    (ok : α → Prop) (st : List α → List α → CR → List (Fin (A + 4))) (b : ℕ)
    (hstep : ∀ a rest done, ok a →
      CRuns body cr ι p (st (a :: rest) done) (st rest (done ++ [a])) b)
    (hne : ∀ a rest done, ok a → st (a :: rest) done g ≠ [])
    (hend : ∀ done, st [] done g = []) :
    ∀ l done, (∀ a ∈ l, ok a) →
      CRuns body cr ι (cwhileP (cr g) p) (st l done) (st [] (done ++ l)) (l.length * (b + 2) + 2) := by
  have key : ∀ (l done : List α), (∀ a ∈ l, ok a) → ∀ (v : HS T Q A U) (S : Stacks T A),
      CClean ι S → CHolds cr S (st l done) → v.flag = (S.R (cr g)).head?.isSome →
      ∃ v' S' n, v'.user = v.user ∧ n ≤ l.length * (b + 2) + 1 ∧
        Exec body (.loop (·.flag) (.seq p (.act (peekR (cr g))))) (mk v S) n (mk v' S') ∧
        CHolds cr S' (st [] (done ++ l)) ∧ CFr cr S S' := by
    intro l
    induction l with
    | nil =>
        intro done _ v S _ hS hf
        refine ⟨v, S, 1, rfl, by simp, .loop_false ?_, by simpa using hS, CFr.refl S⟩
        rw [mk_var, hf, hS g, hend]; rfl
    | cons a rest ih =>
        intro done hok v S hc hS hf
        obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ :=
          hstep a rest done (hok a (by simp)) v S hc hS
        have e₂ := peekR_run (cr g) v₁ S₁ ▸ Exec.act (body := body) (peekR (cr g)) (mk v₁ S₁)
        obtain ⟨v₃, S₃, n₃, hu₃, hn₃, he₃, hS₃, hf₃⟩ := ih (done ++ [a])
          (fun x hx => hok x (by simp [hx])) { v₁ with flag := (S₁.R (cr g)).head?.isSome } S₁
          (hc.of_fr hdisj hf₁) hS₁ rfl
        have hft : v.flag = true := by
          rw [hf, hS g]
          cases h : st (a :: rest) done g with
          | nil => exact absurd h (hne a rest done (hok a (by simp)))
          | cons _ _ => rfl
        refine ⟨v₃, S₃, n₁ + 1 + n₃ + 1, hu₃.trans hu₁, ?_,
          Exec.loop_true (by simpa using hft) (Exec.seq he₁ e₂) he₃, ?_, hf₁.trans hf₃⟩
        · simp only [List.length_cons]
          nlinarith
        · simpa using hS₃
  intro l done hok v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ :=
    key l done hok { v with flag := (S.R (cr g)).head?.isSome } S hc hS rfl
  exact ⟨v', S', 1 + n, hu, by omega,
    Exec.seq (peekR_run (cr g) v S ▸ Exec.act (body := body) (peekR (cr g)) (mk v S)) he, hS', hf⟩

end Loops

end IntegerMultBounds.MathlibTM2.Fast
