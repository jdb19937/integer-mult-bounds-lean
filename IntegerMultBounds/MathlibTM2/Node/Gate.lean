module

public import IntegerMultBounds.MathlibTM2.Layer.Enc
public import IntegerMultBounds.MathlibTM2.Layer.GaussStream
public import IntegerMultBounds.MathlibTM2.Layer.Shift
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init

/-!
# One scaled gate on a bank of wire registers

The wires of the node live in registers `ρ v`, one coefficient stream `encZ A w (B v)` per wire
`v`. A scaled gate `gateZ g B` replaces the target by `2 x_t + Σ dbl c · x_s` and doubles every
other wire. `gateProg` runs it in three passes:

1. one Gaussian linear automaton (`gaussAuto`) over the gate wires `gateWires g`, reading the
   registers `ρ v` and pushing the outputs, reversed, onto the temporaries `σ v`; its matrix
   `gateMat g` has the target row `gateCoef g` and the doubling `2` on the diagonal elsewhere;
2. `moveR (σ v) (ρ v) id` for every gate wire, which restores forward order;
3. `shiftInto (ρ v) (σ v) (ρ v)` with shift `1` (in place doubling) for every other wire.

`gateProg_exec`: every register `ρ v` ends holding `encZ A w (gateZ g B v)`, all registers
outside the range of `ρ` end as they started, in at most
`|NWire| · (R 2^n r) · (11 w + 24) + 4 |NWire| + 4` steps.

The list semantics is `gate_coeffList`: the automaton output for gate wire `j` is the coefficient
list of `gateZ g B (gateWire g j)`, by `coeffList_zip` and `red_glin`, since
`gateZ g B (gateWire g j) = Σᵢ (gateMat g j i) · B (gateWire g i)` exactly (`gateZ_eq_sum`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer


/-! ### The gate matrix -/

section Matrix

variable (g : Circuit.Gate NWire ℚ)

/-- The wires of a gate: the target and the sources, without duplicates. -/
def gateWires : List NWire := (g.target :: g.terms.map Prod.fst).dedup

lemma nodup_gateWires : (gateWires g).Nodup := List.nodup_dedup _

lemma target_mem_gateWires : g.target ∈ gateWires g := List.mem_dedup.2 List.mem_cons_self

lemma fst_mem_gateWires {t : NWire × ℚ} (ht : t ∈ g.terms) : t.1 ∈ gateWires g :=
  List.mem_dedup.2 (List.mem_cons_of_mem _ (List.mem_map_of_mem ht))

instance : NeZero (gateWires g).length :=
  ⟨(List.length_pos_of_mem (target_mem_gateWires g)).ne'⟩

/-- Wire `i` of the gate. -/
def gateWire (i : Fin (gateWires g).length) : NWire := (gateWires g)[i]

lemma gateWire_injective : Function.Injective (gateWire g) := fun _ _ h =>
  Fin.ext ((nodup_gateWires g).getElem_inj_iff.1 h)

lemma gateWire_mem (i : Fin (gateWires g).length) : gateWire g i ∈ gateWires g :=
  List.getElem_mem _

lemma exists_gateWire {u : NWire} (hu : u ∈ gateWires g) : ∃ i, gateWire g i = u := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hu
  exact ⟨⟨i, hi⟩, rfl⟩

/-- A sum over the gate wires. -/
lemma sum_gateWire {M : Type} [AddCommMonoid M] (f : NWire → M) :
    ∑ i, f (gateWire g i) = ∑ u ∈ (gateWires g).toFinset, f u := by
  rw [List.sum_toFinset f (nodup_gateWires g)]
  exact Fin.sum_univ_fun_getElem _ f

/-- The coefficient of wire `u` in the target output: `2` for the target and `(2 c).num` for each
term `(u, c)`. -/
def gateCoef (u : NWire) : ℤ :=
  (if u = g.target then 2 else 0) +
    (g.terms.map fun t => if t.1 = u then (2 * t.2).num else 0).sum

/-- The matrix of the scaled gate on the gate wires: output `j` at input `i`. The target row holds
`gateCoef g`, every other row `2` on the diagonal; all imaginary parts are `0`. -/
def gateMat : Fin (gateWires g).length → Fin (gateWires g).length → ℤ × ℤ := fun j i =>
  if gateWire g j = g.target then (gateCoef g (gateWire g i), 0) else (if i = j then 2 else 0, 0)

/-- The row bound of `gateMat g`: `2` plus the absolute values of the doubled coefficients. -/
def gateBound : ℕ := 2 + (g.terms.map fun t => (2 * t.2).num.natAbs).sum

/-- Summing the per-wire indicator sums of a term list over a set containing all its wires. -/
lemma sum_terms_ite {M : Type} [AddCommMonoid M] (s : Finset NWire) (a : NWire × ℚ → NWire → M) :
    ∀ ts : List (NWire × ℚ), (∀ t ∈ ts, t.1 ∈ s) →
      ∑ u ∈ s, (ts.map fun t => if t.1 = u then a t u else 0).sum = (ts.map fun t => a t t.1).sum
  | [], _ => by simp
  | t :: ts, h => by
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
      rw [sum_terms_ite s a ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')),
        Finset.sum_ite_eq]
      simp only [h t List.mem_cons_self, ↓reduceIte]

lemma abs_terms_le (u : NWire) : ∀ ts : List (NWire × ℚ),
    |(ts.map fun t => if t.1 = u then (2 * t.2).num else 0).sum| ≤
      (ts.map fun t => if t.1 = u then |(2 * t.2).num| else 0).sum
  | [] => by simp
  | t :: ts => by
      simp only [List.map_cons, List.sum_cons]
      refine (abs_add_le _ _).trans (add_le_add ?_ (abs_terms_le u ts))
      split_ifs <;> simp

/-- The row sums of absolute values of `gateMat g` are at most `gateBound g`. -/
theorem gateMat_bound (j : Fin (gateWires g).length) :
    ∑ i, (|(gateMat g j i).1| + |(gateMat g j i).2|) ≤ (gateBound g : ℤ) := by
  have hs : ∀ t ∈ g.terms, t.1 ∈ (gateWires g).toFinset :=
    fun t ht => List.mem_toFinset.2 (fst_mem_gateWires g ht)
  by_cases hj : gateWire g j = g.target
  · simp only [gateMat, hj, ↓reduceIte, abs_zero, add_zero]
    rw [sum_gateWire g (fun u => |gateCoef g u|)]
    calc ∑ u ∈ (gateWires g).toFinset, |gateCoef g u|
        ≤ ∑ u ∈ (gateWires g).toFinset, ((if u = g.target then 2 else 0) +
            (g.terms.map fun t => if t.1 = u then |(2 * t.2).num| else 0).sum) := by
          refine Finset.sum_le_sum fun u _ => (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · split_ifs <;> simp
          · exact abs_terms_le u g.terms
      _ = (gateBound g : ℤ) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq',
            sum_terms_ite _ (fun t _ => |(2 * t.2).num|) g.terms hs]
          simp [List.mem_toFinset.2 (target_mem_gateWires g), gateBound, Nat.cast_list_sum,
            Function.comp_def]
  · simp only [gateMat, hj, ↓reduceIte, abs_zero, add_zero]
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
    have h2 : (2 : ℤ) ≤ (gateBound g : ℤ) := by unfold gateBound; omega
    simpa using h2

end Matrix

/-! ### The arithmetic of one output -/

section Arith

variable (g : Circuit.Gate NWire ℚ) {Y : Type} {n : ℕ}

lemma mk_zero_mul (a : ℤ) (z : GaussianInt) :
    (⟨a, 0⟩ : GaussianInt) * z = (a : GaussianInt) * z := by
  rw [show (⟨a, 0⟩ : GaussianInt) = (a : GaussianInt) by ext <;> simp]

lemma gateCoef_mul (u : NWire) (z : GaussianInt) :
    (gateCoef g u : GaussianInt) * z = (if u = g.target then 2 * z else 0) +
      (g.terms.map fun t => if t.1 = u then dbl t.2 * z else 0).sum := by
  simp only [gateCoef, Int.cast_add, Int.cast_list_sum, add_mul, List.map_map]
  rw [← List.sum_map_mul_right]
  congr 1
  · split_ifs <;> simp
  · congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    split_ifs <;> simp [dbl]

/-- Output `j` of the scaled gate is the integer combination of row `j` of `gateMat g`. -/
theorem gateZ_eq_sum (B : NWire → ZArr Y n) (j : Fin (gateWires g).length)
    (p : Y × (Fin n → ZMod 2)) :
    gateZ g B (gateWire g j) p =
      ∑ i, (⟨(gateMat g j i).1, (gateMat g j i).2⟩ : GaussianInt) * B (gateWire g i) p := by
  by_cases hj : gateWire g j = g.target
  · simp only [gateMat, hj, ↓reduceIte, mk_zero_mul, gateZ]
    rw [sum_gateWire g (fun u => (gateCoef g u : GaussianInt) * B u p)]
    simp only [gateCoef_mul, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', sum_terms_ite _ (fun t u => dbl t.2 * B u p) g.terms
        (fun t ht => List.mem_toFinset.2 (fst_mem_gateWires g ht))]
    simp [List.mem_toFinset.2 (target_mem_gateWires g)]
  · simp only [gateMat, hj, ↓reduceIte, mk_zero_mul, gateZ]
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
    simp

variable {R r w : ℕ}

/-- **List semantics of the gate.** The automaton output for gate wire `j` is the coefficient
list of the scaled gate on that wire. -/
theorem gate_coeffList (B : NWire → ZArr (Fin R × Fin r) n) (j : Fin (gateWires g).length) :
    List.ofFn (fun c : Fin (R * 2 ^ n * r) => glin (gateMat g)
        (fun i => (coeffList w (B (gateWire g i)))[(c : ℕ)]'(by
          rw [length_coeffList]; exact c.isLt)) j) =
      coeffList w (gateZ g B (gateWire g j)) := by
  have h := coeffList_zip (w := w)
    (fun z : Fin (gateWires g).length → GaussianInt =>
      ∑ i, (⟨(gateMat g j i).1, (gateMat g j i).2⟩ : GaussianInt) * z i)
    (fun zs => glin (gateMat g) zs j) (fun z => red_glin (gateMat g) z j)
    (fun i => B (gateWire g i))
  calc _ = List.ofFn (fun t : Fin (R * 2 ^ n * r) => glin (gateMat g)
        (fun i => (coeffList w (B (gateWire g i)))[t]'(by rw [length_coeffList]; exact t.2)) j) :=
        rfl
    _ = _ := h.symm
    _ = _ := by
      congr 1
      funext p
      exact (gateZ_eq_sum g B j p).symm

/-- Off the gate, the scaled gate doubles: the coefficient list is shifted by one bit. -/
theorem gate_coeffList_off (B : NWire → ZArr (Fin R × Fin r) n) {u : NWire} (hu : u ≠ g.target) :
    coeffList w (gateZ g B u) = (coeffList w (B u)).map
      fun z => ((2 ^ 1 : ZMod (2 ^ w)) * z.1, (2 ^ 1 : ZMod (2 ^ w)) * z.2) := by
  have h : gateZ g B u = fun p => 2 * B u p := by
    funext p
    simp [gateZ, hu]
  rw [h]
  exact coeffList_map (fun z => 2 * z) _ (fun z => by simp [red]) (B u)

end Arith

/-! ### The program -/

section Program

variable {T Q A : ℕ} {U : Type} {P : Type}

/-- Register layout of `gateProg`: wire registers `ρ` and output temporaries `σ`, injective with
disjoint ranges; the automaton state slot `st` outside the range of `ρ`; the word counter `ctr`,
its spare `tmp` and the shift registers `cS cR tS tR`, all distinct and outside both ranges. -/
structure GateLayout (ρ σ : NWire → Fin T) (st ctr tmp cS cR tS tR : Fin T) : Prop where
  ρ_inj : Function.Injective ρ
  σ_inj : Function.Injective σ
  ρ_σ : ∀ u u', ρ u ≠ σ u'
  ρ_st : ∀ u, ρ u ≠ st
  regs_nodup : [ctr, tmp, cS, cR, tS, tR].Nodup
  ρ_regs : ∀ u, ρ u ∉ [ctr, tmp, cS, cR, tS, tR]
  σ_regs : ∀ u, σ u ∉ [ctr, tmp, cS, cR, tS, tR]

namespace GateLayout

variable {ρ σ : NWire → Fin T} {st ctr tmp cS cR tS tR : Fin T}
  (h : GateLayout ρ σ st ctr tmp cS cR tS tR)
include h

lemma ρ_ne (u : NWire) : ρ u ≠ ctr ∧ ρ u ≠ tmp ∧ ρ u ≠ cS ∧ ρ u ≠ cR ∧ ρ u ≠ tS ∧ ρ u ≠ tR := by
  have := h.ρ_regs u
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
  exact this

lemma σ_ne (u : NWire) : σ u ≠ ctr ∧ σ u ≠ tmp ∧ σ u ≠ cS ∧ σ u ≠ cR ∧ σ u ≠ tS ∧ σ u ≠ tR := by
  have := h.σ_regs u
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
  exact this

/-- The registers of one in-place shift are distinct. -/
lemma shift_nodup (u : NWire) : [ρ u, σ u, cS, cR, tS, tR].Nodup := by
  have h1 := h.regs_nodup
  obtain ⟨-, -, a1, a2, a3, a4⟩ := h.ρ_ne u
  obtain ⟨-, -, b1, b2, b3, b4⟩ := h.σ_ne u
  have h4 := h.ρ_σ u u
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 ⊢
  exact ⟨⟨h4, a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩, h1.2.2⟩

/-- The automaton layout on the gate wires. -/
lemma autoLayout (g : Circuit.Gate NWire ℚ) :
    AutoLayout (ρ ∘ gateWire g) (σ ∘ gateWire g) st ctr tmp where
  ins_inj := h.ρ_inj.comp (gateWire_injective g)
  outs_inj := h.σ_inj.comp (gateWire_injective g)
  ins_outs _ _ := h.ρ_σ _ _
  ins_ctr _ := (h.ρ_ne _).1
  ins_tmp _ := (h.ρ_ne _).2.1
  outs_ctr _ := (h.σ_ne _).1
  outs_tmp _ := (h.σ_ne _).2.1
  ctr_tmp := by
    have h1 := h.regs_nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h1
    exact h1.1.1
  ins_st _ := h.ρ_st _

end GateLayout

/-- The wires outside the gate. -/
noncomputable def otherWires (g : Circuit.Gate NWire ℚ) : List NWire :=
  ((Finset.univ : Finset NWire) \ (gateWires g).toFinset).toList

lemma mem_otherWires (g : Circuit.Gate NWire ℚ) {u : NWire} :
    u ∈ otherWires g ↔ u ∉ gateWires g := by
  simp [otherWires]

lemma nodup_otherWires (g : Circuit.Gate NWire ℚ) : (otherWires g).Nodup :=
  Finset.nodup_toList _

/-- Every wire is a gate wire or an other wire, exactly once. -/
lemma length_gateWires_add_otherWires (g : Circuit.Gate NWire ℚ) :
    (gateWires g).length + (otherWires g).length = Fintype.card NWire := by
  rw [otherWires, Finset.length_toList, Finset.card_univ_sdiff,
    List.toFinset_card_of_nodup (nodup_gateWires g)]
  have : (gateWires g).length ≤ Fintype.card NWire := by
    rw [← List.toFinset_card_of_nodup (nodup_gateWires g)]
    exact Finset.card_le_univ _
  omega

/-- **The host program of one scaled gate.** The Gaussian linear automaton of `gateMat g` reads
the gate wires `ρ v` and pushes its outputs, reversed, onto `σ v`; `moveR` returns them to `ρ v`
in forward order; every other wire is doubled in place by `shiftInto` with shift `1`. -/
noncomputable def gateProg (ρ σ : NWire → Fin T) (st ctr tmp cS cR tS tR : Fin T)
    (g : Circuit.Gate NWire ℚ) : Pr P T Q A U :=
  .seq (autoWords (ρ ∘ gateWire g) (σ ∘ gateWire g) st ctr tmp
      (gaussAuto A (gateMat g) (gateBound g) false))
    (.seq (Prog.seqList ((gateWires g).map fun u => moveR (σ u) (ρ u) id))
      (Prog.seqList ((otherWires g).map fun u =>
        shiftInto (ρ u) (σ u) (ρ u) cS cR tS tR (pairSym A false false))))

variable (body : P → Pr P T Q A U)

/-- In-place doubling (`shiftInto` with shift `1`) of the registers `ρ u`, `u ∈ ws`, each holding
`N` coefficients, with temporaries `σ u`. Exactly `|ws| (N (6 w + 18) + 4) + 1` steps; only the
registers `ρ u`, `u ∈ ws`, change. -/
theorem shiftList_exec {ι : Type} (ρ σ : ι → Fin T) (cS cR tS tR : Fin T)
    (hρ : Function.Injective ρ) (hρσ : ∀ u u', ρ u ≠ σ u')
    (hreg : ∀ u, [ρ u, σ u, cS, cR, tS, tR].Nodup) {w : ℕ} (hw : 1 ≤ w) (N : ℕ)
    (zs : ι → List (GR w)) (hzs : ∀ u, (zs u).length = N) :
    ∀ (ws : List ι), ws.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A),
      (∀ u ∈ ws, S.R (ρ u) = (zs u).flatMap (coeffSyms A w)) → (∀ u ∈ ws, S.R (σ u) = []) →
      (S.R cS).length = 1 → (S.R cR).length = w - 1 → S.R tS = [] → S.R tR = [] →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (Prog.seqList (ws.map fun u =>
            shiftInto (ρ u) (σ u) (ρ u) cS cR tS tR (pairSym A false false)))
          (mk v S) (ws.length * (N * (6 * w + 18) + 4) + 1) (mk v' { S with R := R' }) ∧
        (∀ u ∈ ws, R' (ρ u) = ((zs u).map fun z =>
          ((2 ^ 1 : ZMod (2 ^ w)) * z.1, (2 ^ 1 : ZMod (2 ^ w)) * z.2)).flatMap (coeffSyms A w)) ∧
        ∀ k, (∀ u ∈ ws, k ≠ ρ u) → R' k = S.R k := by
  intro ws
  induction ws with
  | nil =>
      intro _ v S _ _ _ _ _ _
      exact ⟨v, S.R, rfl, by simpa [Prog.seqList] using Exec.act (body := body) .done (mk v S),
        by simp, fun _ _ => rfl⟩
  | cons u ws ih =>
      intro hnd v S hsrc hdst hcS hcR htS htR
      rw [List.nodup_cons] at hnd
      have hn := hreg u
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      obtain ⟨⟨-, h1, h2, h3, h4⟩, -⟩ := hn
      obtain ⟨v₁, R₁, hu₁, -, he₁, hout₁, -, hoth₁⟩ := shiftInto_exec body (ρ u) (σ u) (ρ u)
        cS cR tS tR (hreg u) (hρσ u u) hw hw (zs u) v S (hsrc u List.mem_cons_self) hcS hcR htS
        htR (hdst u List.mem_cons_self)
      have hfr : ∀ k, k ≠ ρ u → R₁ k = S.R k := fun k hk => hoth₁ k hk hk
      have hne : ∀ u' ∈ ws, ρ u' ≠ ρ u := fun u' hu' e => hnd.1 (hρ e ▸ hu')
      obtain ⟨v', R', hu', he', hρ', hoth'⟩ := ih hnd.2 v₁ { S with R := R₁ }
        (fun u' hu' => (hfr _ (hne u' hu')).trans (hsrc u' (List.mem_cons_of_mem _ hu')))
        (fun u' hu' => (hfr _ (hρσ u u').symm).trans (hdst u' (List.mem_cons_of_mem _ hu')))
        ((congrArg List.length (hfr _ (Ne.symm h1))).trans hcS)
        ((congrArg List.length (hfr _ (Ne.symm h2))).trans hcR)
        ((hfr _ (Ne.symm h3)).trans htS) ((hfr _ (Ne.symm h4)).trans htR)
      refine ⟨v', R', hu'.trans hu₁, Exec.cast (Exec.seq he₁ he') ?_ rfl, ?_, ?_⟩
      · rw [hzs u, List.length_cons]
        ring
      · intro u' hu'
        rcases List.mem_cons.1 hu' with rfl | hu'
        · rw [hoth' _ (fun u'' hu'' => (hne u'' hu'').symm)]
          simpa using hout₁
        · exact hρ' u' hu'
      · intro k hk
        rw [hoth' k (fun u' hu' => hk u' (List.mem_cons_of_mem _ hu'))]
        exact hfr k (hk u List.mem_cons_self)

/-- The moves of `gateProg` in the form of `revList_exec`. -/
lemma moveList_eq (ρ σ : NWire → Fin T) (g : Circuit.Gate NWire ℚ) :
    ((gateWires g).map fun u => (moveR (σ u) (ρ u) id : Pr P T Q A U)) =
      (List.finRange (gateWires g).length).map fun d =>
        moveR ((σ ∘ gateWire g) d) ((ρ ∘ gateWire g) d) id := by
  conv_lhs => rw [← List.map_getElem_finRange (gateWires g)]
  rw [List.map_map]
  rfl

/-- **One scaled gate on the bank of wire registers.** If every wire register `ρ u` holds the
stream `encZ A w (B u)` of an array `B u`, the temporaries `σ u`, `tmp`, `tS`, `tR` are empty, `ctr`
holds `w ≥ 1` symbols, `cS` one and `cR` `w - 1`, and the symbol range covers the carry codes
(`4 ≤ A`, `(2 gateBound g + 1)^(2 l) ≤ A + 4`), then `gateProg` leaves `encZ A w (gateZ g B u)`
in every `ρ u` and every register outside the range of `ρ` as it was. -/
theorem gateProg_exec {ρ σ : NWire → Fin T} {st ctr tmp cS cR tS tR : Fin T}
    (hL : GateLayout ρ σ st ctr tmp cS cR tS tR) (g : Circuit.Gate NWire ℚ) {R r n w : ℕ}
    (hA : 4 ≤ A) (hR : (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ A + 4) (hw : 1 ≤ w)
    (B : NWire → ZArr (Fin R × Fin r) n) (v : HS T Q A U) (S : Stacks T A)
    (hB : ∀ u, S.R (ρ u) = encZ A w (B u)) (hσ : ∀ u, S.R (σ u) = [])
    (hctr : (S.R ctr).length = w) (htmp : S.R tmp = []) (hcS : (S.R cS).length = 1)
    (hcR : (S.R cR).length = w - 1) (htS : S.R tS = []) (htR : S.R tR = []) :
    ∃ (v' : HS T Q A U) (m : ℕ) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
      m ≤ Fintype.card NWire * (R * 2 ^ n * r) * (11 * w + 24) + 4 * Fintype.card NWire + 4 ∧
      Exec body (gateProg ρ σ st ctr tmp cS cR tS tR g) (mk v S) m (mk v' { S with R := R' }) ∧
      (∀ u, R' (ρ u) = encZ A w (gateZ g B u)) ∧
      ∀ k, k ∉ Set.range ρ → R' k = S.R k := by
  -- the automaton on the gate wires
  obtain ⟨v₁, m₁, S₁, hu₁, hm₁, he₁, hi₁, ho₁, hl₁, hins₁, houts₁, hoth₁⟩ :=
    gaussAuto_exec body (hL.autoLayout g) hA (gateMat_bound g) hR hw hctr
      (fun i => coeffList w (B (gateWire g i))) (fun i => length_coeffList _) v S rfl htmp
      (fun i => hB (gateWire g i))
  have hS₁σ : ∀ j, S₁.R (σ (gateWire g j)) = (encZ A w (gateZ g B (gateWire g j))).reverse := by
    intro j
    have h := houts₁ j
    simp only [Function.comp_apply, hσ, List.append_nil] at h
    rw [h, gate_coeffList]
    rfl
  have hS₁ : ∀ k, (∀ d, k ≠ ρ (gateWire g d) ∧ k ≠ σ (gateWire g d)) → S₁.R k = S.R k :=
    fun k hk => hoth₁ k (by rintro ⟨d, rfl⟩; exact (hk d).1 rfl)
      (by rintro ⟨d, rfl⟩; exact (hk d).2 rfl)
  have hlen : ∀ u, (encZ A w (gateZ g B u)).length = R * 2 ^ n * r * w := fun u => by
    rw [encZ, length_flatMap_coeffSyms, length_coeffList]
  -- the moves back
  obtain ⟨v₂, R₂, hu₂, he₂, hmv₂, hoth₂⟩ := revList_exec body (σ ∘ gateWire g) (ρ ∘ gateWire g)
    (fun _ _ => (hL.ρ_σ _ _).symm) (hL.σ_inj.comp (gateWire_injective g))
    (hL.ρ_inj.comp (gateWire_injective g)) (List.finRange (gateWires g).length)
    (List.nodup_finRange _) v₁ S₁
  have hm₂ : ((List.finRange (gateWires g).length).map fun d =>
      2 * (S₁.R ((σ ∘ gateWire g) d)).length + 2).sum =
        (gateWires g).length * (2 * (R * 2 ^ n * r * w) + 2) := by
    rw [List.map_congr_left (g := fun _ => 2 * (R * 2 ^ n * r * w) + 2) (fun d _ => by
      rw [Function.comp_apply, hS₁σ d, List.length_reverse, hlen])]
    simp [List.map_const', List.sum_replicate]
  have he₂' : Exec body (Prog.seqList ((gateWires g).map fun u => moveR (σ u) (ρ u) id))
      (mk v₁ S₁) ((gateWires g).length * (2 * (R * 2 ^ n * r * w) + 2) + 1)
      (mk v₂ { S₁ with R := R₂ }) := by
    rw [moveList_eq, ← hm₂]
    exact he₂
  have hR₂ : ∀ k, (∀ d, k ≠ σ (gateWire g d) ∧ k ≠ ρ (gateWire g d)) → R₂ k = S₁.R k :=
    fun k hk => hoth₂ k fun d _ => hk d
  -- registers off the gate wires keep their contents through both passes
  have hoff : ∀ k, (∀ d, k ≠ ρ (gateWire g d) ∧ k ≠ σ (gateWire g d)) → R₂ k = S.R k :=
    fun k hk => (hR₂ k fun d => ⟨(hk d).2, (hk d).1⟩).trans (hS₁ k hk)
  have hoffρ : ∀ u ∈ otherWires g, ∀ d, ρ u ≠ ρ (gateWire g d) ∧ ρ u ≠ σ (gateWire g d) :=
    fun u hu d => ⟨fun e => (mem_otherWires g).1 hu (hL.ρ_inj e ▸ gateWire_mem g d), hL.ρ_σ _ _⟩
  have hoffσ : ∀ u ∈ otherWires g, ∀ d, σ u ≠ ρ (gateWire g d) ∧ σ u ≠ σ (gateWire g d) :=
    fun u hu d => ⟨(hL.ρ_σ _ _).symm,
      fun e => (mem_otherWires g).1 hu (hL.σ_inj e ▸ gateWire_mem g d)⟩
  have hreg : ∀ k ∈ [cS, cR, tS, tR], ∀ d, k ≠ ρ (gateWire g d) ∧ k ≠ σ (gateWire g d) := by
    intro k hk d
    obtain ⟨-, -, a1, a2, a3, a4⟩ := hL.ρ_ne (gateWire g d)
    obtain ⟨-, -, b1, b2, b3, b4⟩ := hL.σ_ne (gateWire g d)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨a1.symm, b1.symm⟩
    · exact ⟨a2.symm, b2.symm⟩
    · exact ⟨a3.symm, b3.symm⟩
    · exact ⟨a4.symm, b4.symm⟩
  -- the in-place doublings off the gate
  obtain ⟨v₃, R₃, hu₃, he₃, hρ₃, hoth₃⟩ := shiftList_exec body ρ σ cS cR tS tR hL.ρ_inj hL.ρ_σ
    hL.shift_nodup hw (R * 2 ^ n * r) (fun u => coeffList w (B u)) (fun u => length_coeffList _)
    (otherWires g) (nodup_otherWires g) v₂ { S₁ with R := R₂ }
    (fun u hu => (hoff _ (hoffρ u hu)).trans (hB u))
    (fun u hu => (hoff _ (hoffσ u hu)).trans (hσ u))
    ((congrArg List.length (hoff _ (hreg cS (by simp)))).trans hcS)
    ((congrArg List.length (hoff _ (hreg cR (by simp)))).trans hcR)
    ((hoff _ (hreg tS (by simp))).trans htS) ((hoff _ (hreg tR (by simp))).trans htR)
  refine ⟨v₃, _, R₃, hu₃.trans (hu₂.trans hu₁), ?_, Exec.cast (Exec.seq he₁ (Exec.seq he₂' he₃))
    rfl (by congr 1; exact Stacks.ext hi₁ ho₁ hl₁ rfl), ?_, ?_⟩
  · -- the step bound
    have hC := length_gateWires_add_otherWires g
    have hl1 : 1 ≤ (gateWires g).length := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
    generalize Fintype.card NWire = C at hC ⊢
    generalize (gateWires g).length = l at hC hl1 ⊢
    generalize (otherWires g).length = k at hC ⊢
    generalize R * 2 ^ n * r = N at hm₁ ⊢
    subst hC
    have h1 : N * (5 * w + 6) ≤ l * (N * (5 * w + 6)) := Nat.le_mul_of_pos_left _ hl1
    have h2 : l * (2 * (N * w) + 2) ≤ l * (N * (6 * w + 18) + 4) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    nlinarith [Nat.zero_le (k * (N * (5 * w + 6)))]
  · intro u
    by_cases hu : u ∈ gateWires g
    · obtain ⟨j, rfl⟩ := exists_gateWire g hu
      have hj : ∀ u' ∈ otherWires g, ρ (gateWire g j) ≠ ρ u' := fun u' hu' e =>
        (mem_otherWires g).1 hu' (hL.ρ_inj e ▸ gateWire_mem g j)
      refine (hoth₃ _ hj).trans ?_
      have h := (hmv₂ j (List.mem_finRange j)).2
      simp only [Function.comp_apply] at h
      have h' := hins₁ j
      simp only [Function.comp_apply] at h'
      show R₂ (ρ (gateWire g j)) = _
      rw [h, hS₁σ, h', List.reverse_reverse, List.append_nil]
    · have hu' : u ∈ otherWires g := (mem_otherWires g).2 hu
      rw [hρ₃ u hu', encZ, gate_coeffList_off g B
        (fun e => hu (by rw [e]; exact target_mem_gateWires g))]
  · intro k hk
    have hk₃ : ∀ u ∈ otherWires g, k ≠ ρ u := fun u _ e => hk ⟨u, e.symm⟩
    rw [hoth₃ k hk₃]
    by_cases hkσ : ∃ d, k = σ (gateWire g d)
    · obtain ⟨d, rfl⟩ := hkσ
      exact ((hmv₂ d (List.mem_finRange d)).1).trans (hσ _).symm
    · push Not at hkσ
      exact hoff k fun d => ⟨fun e => hk ⟨_, e.symm⟩, hkσ d⟩

end Program

end IntegerMultBounds.MathlibTM2.Node
