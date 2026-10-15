module

public import IntegerMultBounds.MathlibTM2.Fast.CMulAuto
public import IntegerMultBounds.MathlibTM2.Host.SSMul

/-!
# Registers of the complex fixed-point product and register-level contracts

**Registers.** The product uses the host registers `cr r`, `r : CR` (`cr` injective), and the 64
registers `ι j` of the Schönhage–Strassen multiplier (`Host/SSMul`), disjoint from them:

* `xs`, `ys`: the operand streams; `xsv`, `ysv`: their consumed symbols (save registers);
  `acc`: the results, latest on top; `out`: the destination of the result stream;
* `wn`, `pn`, `nn`: `w`, `p` and `topN w` in unary (any symbols; restored);
* `tmp`: an empty spare (its scan slot holds the automaton state of a pass);
* scratch, empty before and after a product: `u0 … u3` (two's complement words), `ma … md`
  (magnitudes of the operand parts), `sa … sd` (their signs), `p1 … p4` (the four products),
  `qr`, `qi` (magnitudes of the result parts), `sr`, `si` (their signs).

**Contracts.** A register file is described by `ρ : CR → List`; `CHolds cr S ρ` says the stacks
`S` carry it. `CFr cr S S'` says `S'` agrees with `S` on `inp`, `out`, every left stack and every
register outside the family `cr`. `CClean ι S` says the multiplier's registers are empty.
`CRuns body cr ι p ρ ρ' b`: from any stacks carrying `ρ` with clean multiplier registers, `p`
runs in at most `b` steps to stacks carrying `ρ'`, framed by `CFr`, with the `user` component
unchanged. `CRuns.seq` composes contracts (the multiplier registers stay clean by the frame).

Register-level contracts: `moveR_runs`, `uclear_runs`, `usub_runs`, `zeroBits_runs`, `ssMul_runs`,
`selectP_runs` (with `select_runs`: sign and magnitude of `x` from the residues of `x` and `-x`
modulo `2^K`, most significant bit on top, when `|x| < 2^(K-1)`), and the counted passes
`dpass_runs`.

The three two-carry automata of the product: `splitD` (a coefficient's pair symbols to the bits
of `re`, `-re`, `im`, `-im`), `combD` (two bit streams to `Z = bsgn m₁ X₁ + bsgn m₂ X₂` and `-Z`),
`finD` (two bit streams to the pair symbols of `(bsgn m₁ X₁, bsgn m₂ X₂)`), with the bit lemmas
`carryRun_neg`, `carryRun_sgn`, `carryRun_comb`, `carryRun_comb_neg`; their passes are in
`CMulPass`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Schoenhage.Schedule (topN)

set_option linter.unusedSimpArgs false

/-- The registers of the complex fixed-point product. -/
inductive CR
  | xs | ys | xsv | ysv | acc | out | wn | pn | nn | tmp
  | u0 | u1 | u2 | u3 | ma | mb | mc | md | sa | sb | sc | sd
  | p1 | p2 | p3 | p4 | qr | qi | sr | si
  deriving DecidableEq

/-- The top bit of a list of symbols. -/
def topB {A : ℕ} (l : List (Fin (A + 4))) : Bool := symBit (l.head?.getD blank)

@[simp] lemma topB_cons {A : ℕ} (x : Fin (A + 4)) (l : List (Fin (A + 4))) :
    topB (x :: l) = symBit x := rfl

section Contracts

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) (cr : CR → Fin T)
  (ι : Fin 64 → Fin T)

/-- The stacks `S` carry the register file `ρ`. -/
def CHolds (S : Stacks T A) (ρ : CR → List (Fin (A + 4))) : Prop := ∀ r, S.R (cr r) = ρ r

/-- `S'` agrees with `S` on `inp`, `out`, the left stacks and every register outside `cr`. -/
def CFr (S S' : Stacks T A) : Prop :=
  S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ ∀ k, (∀ r, cr r ≠ k) → S'.R k = S.R k

/-- The multiplier's registers are empty. -/
def CClean (S : Stacks T A) : Prop := ∀ j, S.L (ι j) = [] ∧ S.R (ι j) = []

/-- The contract of a program on the register file: from `ρ` to `ρ'` within `b` steps. -/
def CRuns (p : Pr P T Q A U) (ρ ρ' : CR → List (Fin (A + 4))) (b : ℕ) : Prop :=
  ∀ v S, CClean ι S → CHolds cr S ρ → ∃ v' S' n, v'.user = v.user ∧ n ≤ b ∧
    Exec body p (mk v S) n (mk v' S') ∧ CHolds cr S' ρ' ∧ CFr cr S S'

variable {body cr ι}

lemma CFr.refl (S : Stacks T A) : CFr cr S S := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

lemma CFr.trans {S₁ S₂ S₃ : Stacks T A} (h₁ : CFr cr S₁ S₂) (h₂ : CFr cr S₂ S₃) : CFr cr S₁ S₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun k hk => (h₂.2.2.2 k hk).trans (h₁.2.2.2 k hk)⟩

lemma CClean.of_fr (hdisj : ∀ r j, cr r ≠ ι j) {S S' : Stacks T A} (hc : CClean ι S)
    (h : CFr cr S S') : CClean ι S' := fun j =>
  ⟨by rw [h.2.2.1]; exact (hc j).1, by rw [h.2.2.2 _ (fun r => hdisj r j)]; exact (hc j).2⟩

theorem CRuns.seq (hdisj : ∀ r j, cr r ≠ ι j) {p q : Pr P T Q A U}
    {ρ₁ ρ₂ ρ₃ : CR → List (Fin (A + 4))} {b₁ b₂ : ℕ} (h₁ : CRuns body cr ι p ρ₁ ρ₂ b₁)
    (h₂ : CRuns body cr ι q ρ₂ ρ₃ b₂) : CRuns body cr ι (.seq p q) ρ₁ ρ₃ (b₁ + b₂) := by
  intro v S hc hS
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h₁ v S hc hS
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := h₂ v₁ S₁ (hc.of_fr hdisj hf₁) hS₁
  exact ⟨v₂, S₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hS₂, hf₁.trans hf₂⟩

theorem CRuns.mono {p : Pr P T Q A U} {ρ ρ' : CR → List (Fin (A + 4))} {b b' : ℕ}
    (h : CRuns body cr ι p ρ ρ' b) (hb : b ≤ b') : CRuns body cr ι p ρ ρ' b' := by
  intro v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := h v S hc hS
  exact ⟨v', S', n, hu, hn.trans hb, he, hS', hf⟩

theorem CRuns.congr {p : Pr P T Q A U} {ρ ρ' ρ'' : CR → List (Fin (A + 4))} {b : ℕ}
    (h : CRuns body cr ι p ρ ρ' b) (he : ρ' = ρ'') : CRuns body cr ι p ρ ρ'' b := he ▸ h

/-! ### Register files under updates -/

lemma upd_comp (hcr : Function.Injective cr) {β : Type} (g : Fin T → β) (a : CR) (x : β)
    (r : CR) : Function.update g (cr a) x (cr r) = Function.update (fun r => g (cr r)) a x r := by
  by_cases h : r = a
  · subst h; simp
  · rw [Function.update_of_ne (hcr.ne h), Function.update_of_ne h]

lemma holds_upd (hcr : Function.Injective cr) {R : Fin T → List (Fin (A + 4))}
    {ρ : CR → List (Fin (A + 4))} (h : ∀ r, R (cr r) = ρ r) (a : CR) (x : List (Fin (A + 4))) :
    ∀ r, Function.update R (cr a) x (cr r) = Function.update ρ a x r := by
  intro r
  rw [upd_comp hcr]
  have : (fun r => R (cr r)) = ρ := funext h
  rw [this]

lemma upd_off {β : Type} (g : Fin T → β) (a : CR) (x : β) {k : Fin T} (hk : ∀ r, cr r ≠ k) :
    Function.update g (cr a) x k = g k := Function.update_of_ne (hk a).symm _ _

/-! ### Primitive contracts -/

variable (hcr : Function.Injective cr)
include hcr

theorem moveR_runs {a b : CR} (hab : a ≠ b) {ρ : CR → List (Fin (A + 4))} {n : ℕ}
    (hn : (ρ a).length = n) :
    CRuns body cr ι (moveR (cr a) (cr b) id) ρ
      (Function.update (Function.update ρ a []) b ((ρ a).reverse ++ ρ b)) (2 * n + 2) := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := moveR_exec body (cr a) (cr b) (hcr.ne hab) id v S
  refine ⟨v', _, _, hu, by rw [hS, hn], he, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · intro r
    simp only [movedR, List.map_id]
    rw [holds_upd hcr (holds_upd hcr hS a []) b, hS, hS]
  · simp only [movedR, upd_off _ _ _ hk]

theorem uclear_runs (a : CR) {ρ : CR → List (Fin (A + 4))} {n : ℕ} (hn : (ρ a).length = n) :
    CRuns body cr ι (uclear (cr a)) ρ (Function.update ρ a []) (2 * n + 2) := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := uclear_exec body (cr a) v S
  exact ⟨v', _, _, hu, by rw [hS, hn], he, holds_upd hcr hS a [],
    ⟨rfl, rfl, rfl, fun k hk => upd_off _ _ _ hk⟩⟩

theorem usub_runs {a b t : CR} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    {ρ : CR → List (Fin (A + 4))} {n : ℕ} (hn : (ρ a).length = n) (ht : ρ t = []) :
    CRuns body cr ι (usub (cr a) (cr b) (cr t)) ρ (Function.update ρ b ((ρ b).drop n))
      (4 * n + 4) := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := usub_exec body (hcr.ne hab) (hcr.ne hat) (hcr.ne hbt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS, hn], he, ?_, ⟨rfl, rfl, rfl, fun k hk => upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [holds_upd hcr hS b, hS, hS, hn]

theorem zeroBits_runs {len z t : CR} (hlz : len ≠ z) (hlt : len ≠ t) (hzt : z ≠ t)
    {ρ : CR → List (Fin (A + 4))} {n : ℕ} (hn : (ρ len).length = n) (ht : ρ t = []) :
    CRuns body cr ι (zeroBits (cr len) (cr z) (cr t)) ρ
      (Function.update ρ z (binSyms n 0 ++ ρ z)) (4 * n + 4) := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := zeroBits_exec body (hcr.ne hlz) (hcr.ne hlt) (hcr.ne hzt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS, hn], he, ?_, ⟨rfl, rfl, rfl, fun k hk => upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [holds_upd hcr hS z, hS, hS, hn]

theorem ssMul_runs (hdisj : ∀ r j, cr r ≠ ι j) (hι : Function.Injective ι) (hT : 64 ≤ T)
    (hQ : SS.states ≤ Q) {xa xb xn xc : CR} (hna : xn ≠ xa) (hnb : xn ≠ xb) {m a b : ℕ}
    (hm : 1 ≤ m) (ha : a < 2 ^ m) (hb : b < 2 ^ m) {ρ : CR → List (Fin (A + 4))}
    (hSa : ρ xa = binSyms m a) (hSb : ρ xb = binSyms m b) (hSn : (ρ xn).length = topN m) :
    CRuns body cr ι (ssMul ι hι hT hQ (cr xa) (cr xb) (cr xn) (cr xc)) ρ
      (Function.update ρ xc (binSyms (topN m + 1) (a * b) ++ ρ xc))
      (ssMulConst * (T + 1) * mLogLog m) := by
  intro v S hc hS
  obtain ⟨v', n, hu, hn, he⟩ := ssMul_exec_log body ι hι hT hQ (fun j => (hdisj xa j).symm)
    (fun j => (hdisj xb j).symm) (fun j => (hdisj xn j).symm) (fun j => (hdisj xc j).symm)
    (hcr.ne hna) (hcr.ne hnb) hm ha hb v S (fun j => (hc j).1) (fun j => (hc j).2)
    (by rw [hS, hSa]) (by rw [hS, hSb]) (by rw [hS, hSn])
  refine ⟨v', _, n, hu, hn, he, ?_, ⟨rfl, rfl, rfl, fun k hk => upd_off _ _ _ hk⟩⟩
  intro r
  dsimp only
  rw [holds_upd hcr hS xc, hS]

/-! ### Sign selection -/

theorem selectP_runs {X Y M Sg : CR} (hd : [X, Y, M, Sg].Nodup) {ρ : CR → List (Fin (A + 4))}
    {n₁ n₂ : ℕ} (h₁ : (ρ X).length = n₁) (h₂ : (ρ Y).length = n₂) :
    CRuns body cr ι (selectP (cr X) (cr Y) (cr M) (cr Sg)) ρ
      (Function.update (Function.update (Function.update (Function.update ρ X []) Y [])
        M ((if topB (ρ X) then (ρ Y).reverse else (ρ X).reverse) ++ ρ M))
        Sg ((ρ X).head?.getD blank :: ρ Sg))
      (2 * n₁ + 2 * n₂ + 6) := by
  intro v S _ hS
  have hd' : [cr X, cr Y, cr M, cr Sg].Nodup := by
    have := hd.map hcr
    simpa using this
  obtain ⟨v', hu, he⟩ := selectP_exec body hd' v S
  refine ⟨v', _, _, hu, by rw [hS, hS, h₁, h₂], he, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · intro r
    dsimp only
    rw [holds_upd hcr (holds_upd hcr (holds_upd hcr (holds_upd hcr hS X []) Y []) M _) Sg]
    have hS' : ∀ r, S.R (cr r) = ρ r := hS
    simp only [topBit, topB, hS']
    rfl
  · simp only [upd_off _ _ _ hk]

omit hcr in
lemma head_reverse_binSyms {K x : ℕ} (hK : 1 ≤ K) :
    ((binSyms K x : List (Fin (A + 4))).reverse).head?.getD blank =
      bitSymbol (x.testBit (K - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  rw [binSyms_add, List.reverse_append]
  simp [binSyms, Nat.testBit_div_two_pow, Nat.testBit_eq_decide_div_mod_eq]

/-- Sign and magnitude of `x` from the residues of `x` and `-x` modulo `2^K`, most significant
bit on top, when `|x| < 2^(K-1)`. -/
theorem select_runs {X Y M Sg : CR} (hd : [X, Y, M, Sg].Nodup) {ρ : CR → List (Fin (A + 4))}
    {K : ℕ} (hK : 1 ≤ K) {x : ℤ} (hx : |x| < 2 ^ (K - 1))
    (hX : ρ X = (binSyms K (x : ZMod (2 ^ K)).val).reverse)
    (hY : ρ Y = (binSyms K ((-x : ℤ) : ZMod (2 ^ K)).val).reverse) :
    CRuns body cr ι (selectP (cr X) (cr Y) (cr M) (cr Sg)) ρ
      (Function.update (Function.update (Function.update (Function.update ρ X []) Y [])
        M (binSyms K x.natAbs ++ ρ M)) Sg (bitSymbol (decide (x < 0)) :: ρ Sg))
      (4 * K + 6) := by
  refine (selectP_runs hcr hd (n₁ := K) (n₂ := K) (by rw [hX]; simp) (by rw [hY]; simp)).congr ?_
    |>.mono (by omega)
  have htop := head_reverse_binSyms (A := A) (x := (x : ZMod (2 ^ K)).val) hK
  rw [select_testBit hK hx] at htop
  have hsel := select_natAbs (K := K) hx
  rw [hX, hY, htop]
  simp only [topB, htop, symBit_bitSymbol, List.reverse_reverse]
  congr 2
  rw [← hsel]
  split_ifs <;> rfl

/-! ### Counted passes -/

omit hcr in
lemma layout_of_nodup {ni no : ℕ} {insR : Fin ni → CR} {outsR : Fin no → CR} {C Tm : CR}
    (hcr : Function.Injective cr) (h : (List.ofFn insR ++ List.ofFn outsR ++ [C, Tm]).Nodup) :
    AutoLayout (fun i => cr (insR i)) (fun j => cr (outsR j)) (cr Tm) (cr C) (cr Tm) := by
  rw [List.nodup_append, List.nodup_append] at h
  obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := h
  rw [List.nodup_ofFn] at h1 h2
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.mem_append,
    List.mem_ofFn, Set.mem_range] at h4 h5 h3
  have hCT : C ≠ Tm := h4.1
  refine ⟨hcr.comp h1, hcr.comp h2, fun i j he => ?_, fun i he => ?_, fun i he => ?_,
    fun j he => ?_, fun j he => ?_, hcr.ne hCT, fun i he => ?_⟩
  · exact h3 _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ (hcr he)
  · exact h5 _ (Or.inl ⟨i, rfl⟩) C (Or.inl rfl) (hcr he)
  · exact h5 _ (Or.inl ⟨i, rfl⟩) Tm (Or.inr rfl) (hcr he)
  · exact h5 _ (Or.inr ⟨j, rfl⟩) C (Or.inl rfl) (hcr he)
  · exact h5 _ (Or.inr ⟨j, rfl⟩) Tm (Or.inr rfl) (hcr he)
  · exact h5 _ (Or.inl ⟨i, rfl⟩) Tm (Or.inr rfl) (hcr he)

/-- A counted pass on the register file. -/
theorem dpass_runs {ni no : ℕ} (D : Duo A ni no) (hA : 96 ≤ A) (hD : D.Bounded)
    (f : Bool → Bool → Bool → Bool → Bool × Bool) (r₁ r₂ r₃ r₄ : CR) (insR : Fin ni → CR)
    (outsR : Fin no → CR) (C Tm : CR) (hlay : (List.ofFn insR ++ List.ofFn outsR ++ [C, Tm]).Nodup)
    {ρ ρ' : CR → List (Fin (A + 4))} {K : ℕ} (hC : (ρ C).length = K) (hT : ρ Tm = [])
    (col : Fin K → Fin ni → Fin (A + 4))
    (hcol : ∀ i (t : Fin K), (ρ (insR i)).getD t blank = col t i)
    (m : Bool × Bool) (hm : f (topB (ρ r₁)) (topB (ρ r₂)) (topB (ρ r₃)) (topB (ρ r₄)) = m)
    (hin : ∀ i, ρ' (insR i) = (ρ (insR i)).drop K)
    (hout : ∀ j, ρ' (outsR j) = (List.ofFn fun t => D.out (col t)
        ((D.bitsA m.1 m.2 col 0).getD t false) ((D.bitsB m.1 m.2 col 0).getD t false) j).reverse ++
      ρ (outsR j))
    (hoth : ∀ r, (∀ i, insR i ≠ r) → (∀ j, outsR j ≠ r) → ρ' r = ρ r) :
    CRuns body cr ι (dpass D f (cr r₁) (cr r₂) (cr r₃) (cr r₄) (fun i => cr (insR i))
      (fun j => cr (outsR j)) (cr C) (cr Tm)) ρ ρ' (5 * K + 4) := by
  intro v S _ hS
  obtain ⟨v', S', hu, he, hi, ho, hl, hin', hout', hoth'⟩ :=
    dpass_exec body D hA hD f (cr r₁) (cr r₂) (cr r₃) (cr r₄) (layout_of_nodup hcr hlay) v S
      (by rw [hS, hC]) (by rw [hS, hT]) col (fun i t => by rw [hS]; exact hcol i t) m
      (by have hS' : ∀ r, S.R (cr r) = ρ r := hS
          simp only [topBit, hS']; exact hm)
  refine ⟨v', S', _, hu, le_rfl, he, ?_, ⟨hi, ho, hl, fun k hk => ?_⟩⟩
  · intro r
    by_cases h1 : ∃ i, insR i = r
    · obtain ⟨i, rfl⟩ := h1
      rw [hin' i, hS, hin i]
    by_cases h2 : ∃ j, outsR j = r
    · obtain ⟨j, rfl⟩ := h2
      rw [hout' j, hS, hout j]
    push Not at h1 h2
    rw [hoth' (cr r) (by rintro ⟨i, hi⟩; exact h1 i (hcr hi))
      (by rintro ⟨j, hj⟩; exact h2 j (hcr hj)), hS, hoth r h1 h2]
  · exact hoth' k (by rintro ⟨i, rfl⟩; exact hk _ rfl) (by rintro ⟨j, rfl⟩; exact hk _ rfl)

end Contracts

/-! ### The three two-carry automata -/

/-- Split a coefficient: outputs the coefficient symbol, the bits of `re`, `-re`, `im`, `-im`. -/
def splitD (A : ℕ) : Duo A 1 5 where
  sums _ _ col := (-((pairRe (col 0)).toNat : ℤ), -((pairIm (col 0)).toNat : ℤ))
  out col b₁ b₂ := ![col 0, bitSymbol (pairRe (col 0)), bitSymbol b₁, bitSymbol (pairIm (col 0)),
    bitSymbol b₂]

/-- Signed combination: the bits of `Z = bsgn m₁ X₁ + bsgn m₂ X₂` and of `-Z`. -/
def combD (A : ℕ) : Duo A 2 2 where
  sums m₁ m₂ col :=
    (bsgn m₁ * (symBit (col 0)).toNat + bsgn m₂ * (symBit (col 1)).toNat,
      -(bsgn m₁ * (symBit (col 0)).toNat + bsgn m₂ * (symBit (col 1)).toNat))
  out _ b₁ b₂ := ![bitSymbol b₁, bitSymbol b₂]

/-- The result coefficient: pair symbols of `bsgn m₁ X₁` and `bsgn m₂ X₂`. -/
def finD (A : ℕ) : Duo A 2 1 where
  sums m₁ m₂ col := (bsgn m₁ * (symBit (col 0)).toNat, bsgn m₂ * (symBit (col 1)).toNat)
  out _ b₁ b₂ := ![pairSym A b₁ b₂]

lemma abs_bit_le (b : Bool) : |((b.toNat : ℕ) : ℤ)| ≤ 1 := by cases b <;> simp

lemma abs_bsgn_bit_le (s b : Bool) : |bsgn s * ((b.toNat : ℕ) : ℤ)| ≤ 1 := by
  cases s <;> cases b <;> simp [bsgn]

lemma splitD_bounded (A : ℕ) : (splitD A).Bounded := by
  intro _ _ col
  constructor <;> simp only [splitD, abs_neg] <;> exact (abs_bit_le _).trans (by norm_num)

lemma combD_bounded (A : ℕ) : (combD A).Bounded := by
  intro m₁ m₂ col
  have h1 := abs_bsgn_bit_le m₁ (symBit (col 0))
  have h2 := abs_bsgn_bit_le m₂ (symBit (col 1))
  have h := abs_add_le (bsgn m₁ * ((symBit (col 0)).toNat : ℤ)) (bsgn m₂ * ((symBit (col 1)).toNat))
  constructor <;> simp only [combD, abs_neg] <;> linarith

lemma finD_bounded (A : ℕ) : (finD A).Bounded := by
  intro m₁ m₂ col
  exact ⟨(abs_bsgn_bit_le _ _).trans (by norm_num), (abs_bsgn_bit_le _ _).trans (by norm_num)⟩

/-! ### Bits of the carry adders -/

lemma carryRun_neg (K : ℕ) (x : ℤ) :
    (carryRun 0 (List.ofFn fun t : Fin K =>
        -((((x : ZMod (2 ^ K)).val.testBit t).toNat : ℕ) : ℤ))).1 =
      List.ofFn fun t : Fin K => ((-x : ℤ) : ZMod (2 ^ K)).val.testBit t := by
  have h := carryRun_nat K 1 ![-1] ![(x : ZMod (2 ^ K)).val]
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, neg_one_mul] at h
  have e : (((-(((x : ZMod (2 ^ K)).val : ℕ) : ℤ)) : ℤ) : ZMod (2 ^ K)) =
      ((-x : ℤ) : ZMod (2 ^ K)) := by
    push_cast [ZMod.natCast_zmod_val]; rfl
  rw [h]
  congr 1
  funext t
  rw [e]

lemma carryRun_sgn (K : ℕ) (s : Bool) (X : ℕ) :
    (carryRun 0 (List.ofFn fun t : Fin K => bsgn s * (((X.testBit t).toNat : ℕ) : ℤ))).1 =
      List.ofFn fun t : Fin K => ((bsgn s * X : ℤ) : ZMod (2 ^ K)).val.testBit t := by
  have h := carryRun_nat K 1 ![bsgn s] ![X]
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at h
  exact h

lemma carryRun_comb (K : ℕ) (s₁ s₂ : Bool) (X₁ X₂ : ℕ) :
    (carryRun 0 (List.ofFn fun t : Fin K => bsgn s₁ * (((X₁.testBit t).toNat : ℕ) : ℤ) +
        bsgn s₂ * (((X₂.testBit t).toNat : ℕ) : ℤ))).1 =
      List.ofFn fun t : Fin K =>
        ((bsgn s₁ * X₁ + bsgn s₂ * X₂ : ℤ) : ZMod (2 ^ K)).val.testBit t := by
  have h := carryRun_nat K 2 ![bsgn s₁, bsgn s₂] ![X₁, X₂]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  exact h

lemma carryRun_comb_neg (K : ℕ) (s₁ s₂ : Bool) (X₁ X₂ : ℕ) :
    (carryRun 0 (List.ofFn fun t : Fin K => -(bsgn s₁ * (((X₁.testBit t).toNat : ℕ) : ℤ) +
        bsgn s₂ * (((X₂.testBit t).toNat : ℕ) : ℤ)))).1 =
      List.ofFn fun t : Fin K =>
        ((-(bsgn s₁ * X₁ + bsgn s₂ * X₂) : ℤ) : ZMod (2 ^ K)).val.testBit t := by
  have h := carryRun_nat K 2 ![-bsgn s₁, -bsgn s₂] ![X₁, X₂]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  have e1 : (List.ofFn fun t : Fin K => -(bsgn s₁ * (((X₁.testBit t).toNat : ℕ) : ℤ) +
        bsgn s₂ * (((X₂.testBit t).toNat : ℕ) : ℤ))) =
      List.ofFn fun t : Fin K => -bsgn s₁ * (((X₁.testBit t).toNat : ℕ) : ℤ) +
        -bsgn s₂ * (((X₂.testBit t).toNat : ℕ) : ℤ) := by
    congr 1; funext t; ring
  rw [e1, h]
  congr 1
  funext t
  congr 4
  ring

end IntegerMultBounds.MathlibTM2.Fast
