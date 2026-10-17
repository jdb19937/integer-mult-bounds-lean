module
public import IntegerMultBounds.MathlibTM2.Fast.DistSrcCode
public import IntegerMultBounds.MathlibTM2.Fast.DistSrcBase
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.ENatToNat


/-!
# Phase 2 of the converter: the single values

Batches of unary pushes (`dsUnL`: values of variables) and unary copies (`dsCopyL`: copies of
one register) with contracts in the family form (`dsF_unL`, `dsF_copyL`), over the update
`dsUpdL X ws` of the family file by a list of writes.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src


section Batch

variable {T Q A t₀ : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {g : DsY t₀ → Fin T}

/-- The family file `X` after the writes `ws`, in order. -/
noncomputable def dsUpdL (X : DsY t₀ → List (Fin (A + 4))) (ws : List (DsY t₀ × List (Fin (A + 4)))) :
    DsY t₀ → List (Fin (A + 4)) :=
  ws.foldl (fun X e => Function.update X e.1 e.2) X

theorem dsUpdL_cons (X : DsY t₀ → List (Fin (A + 4))) (e : DsY t₀ × List (Fin (A + 4)))
    (ws : List (DsY t₀ × List (Fin (A + 4)))) :
    dsUpdL X (e :: ws) = dsUpdL (Function.update X e.1 e.2) ws := rfl

theorem dsUpdL_off : ∀ (ws : List (DsY t₀ × List (Fin (A + 4)))) (X : DsY t₀ → List (Fin (A + 4)))
    (y : DsY t₀), y ∉ ws.map Prod.fst → dsUpdL X ws y = X y
  | [], X, y, _ => rfl
  | e :: ws, X, y, hy => by
    simp only [List.map_cons, List.mem_cons, not_or] at hy
    rw [dsUpdL_cons, dsUpdL_off ws _ y hy.2, Function.update_of_ne hy.1]

theorem dsUpdL_on : ∀ (ws : List (DsY t₀ × List (Fin (A + 4)))) (X : DsY t₀ → List (Fin (A + 4))),
    (ws.map Prod.fst).Nodup → ∀ e ∈ ws, dsUpdL X ws e.1 = e.2
  | [], _, _, e, he => by simp at he
  | e :: ws, X, hnd, e', he' => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 he' with rfl | he
    · rw [dsUpdL_cons, dsUpdL_off ws _ _ hnd.1, Function.update_self]
    · rw [dsUpdL_cons, dsUpdL_on ws _ hnd.2 e' he]

theorem dsUpdL_append (X : DsY t₀ → List (Fin (A + 4)))
    (ws ws' : List (DsY t₀ × List (Fin (A + 4)))) :
    dsUpdL X (ws ++ ws') = dsUpdL (dsUpdL X ws) ws' := List.foldl_append

theorem dsUpdL_snoc (X : DsY t₀ → List (Fin (A + 4))) (ws : List (DsY t₀ × List (Fin (A + 4))))
    (y : DsY t₀) (v : List (Fin (A + 4))) :
    Function.update (dsUpdL X ws) y v = dsUpdL X (ws ++ [(y, v)]) := by
  rw [dsUpdL_append]; rfl

/-- Push the values of variables onto registers of the family. -/
def dsUnL (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) :
    List (Fin pmNV × DsY t₀) → Pr P T Q A U
  | [] => .act .done
  | e :: l => .seq (dsUn rg e.1 (g e.2)) (dsUnL rg g l)

/-- Copy register `src` onto registers of the family, through `tm`. -/
def dsCopyL (g : DsY t₀ → Fin T) (src tm : DsY t₀) : List (DsY t₀) → Pr P T Q A U
  | [] => .act .done
  | y :: l => .seq (ucopy (g src) (g y) (g tm)) (dsCopyL g src tm l)

variable (h : DsLay rg g) (R : Regs T A) {W : ℕ} (wl : List (Fin (A + 4)))
include h

theorem dsF_unL (σ : Fin pmNV → ℕ) :
    ∀ (l : List (Fin pmNV × DsY t₀)) (X : DsY t₀ → List (Fin (A + 4))),
      (l.map Prod.snd).Nodup → (∀ e ∈ l, X e.2 = []) → (∀ e ∈ l, σ e.1 < 2 ^ W) →
      dsRuns body (dsUnL rg g l) (dsF rg g R X W wl σ)
        (dsF rg g R (dsUpdL X (l.map fun e => (e.2, List.replicate (σ e.1) tick))) W wl σ)
        ((l.map fun e => W * (4 * σ e.1 + 11) + 2 * σ e.1 + 6).sum + 1)
  | [], X, _, _, _ => by
    refine (ds_act _ _ _ fun v S hS => ⟨v, rfl, ?_⟩).mono (by simp)
    simp [Action.run, dsUpdL, ← hS]
  | e :: l, X, hnd, h0, hv => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have s1 := dsF_un (body := body) h R wl X σ e.1 e.2 (hv e List.mem_cons_self)
      (h0 e List.mem_cons_self)
    rw [List.append_nil] at s1
    have s2 := dsF_unL σ l (Function.update X e.2 (List.replicate (σ e.1) tick)) hnd.2
      (fun e' he' => by
        have hne : e'.2 ≠ e.2 := fun h' => hnd.1 (h' ▸ List.mem_map.2 ⟨e', he', rfl⟩)
        rw [Function.update_of_ne hne]; exact h0 e' (List.mem_cons_of_mem _ he'))
      (fun e' he' => hv e' (List.mem_cons_of_mem _ he'))
    refine (s1.seq s2).mono ?_
    simp only [List.map_cons, List.sum_cons]
    omega

theorem dsF_copyL (σ : Fin pmNV → ℕ) (src tm : DsY t₀) {c : ℕ} :
    ∀ (l : List (DsY t₀)) (X : DsY t₀ → List (Fin (A + 4))),
      l.Nodup → src ∉ l → tm ∉ l → src ≠ tm → (X src).length = c → X tm = [] →
      (∀ y ∈ l, X y = []) →
      dsRuns body (dsCopyL g src tm l) (dsF rg g R X W wl σ)
        (dsF rg g R (dsUpdL X (l.map fun y => (y, List.replicate c tick))) W wl σ)
        (l.length * (4 * c + 4) + 1)
  | [], X, _, _, _, _, _, _, _ => by
    refine (ds_act _ _ _ fun v S hS => ⟨v, rfl, ?_⟩).mono (by simp)
    simp [Action.run, dsUpdL, ← hS]
  | y :: l, X, hnd, hs, ht, hst, hX, hXt, h0 => by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd hs ht
    have s1 := dsF_ucopy (body := body) (W := W) h R wl X σ src y tm hs.1
      hst (fun e => ht.1 e.symm) hX (h0 y List.mem_cons_self) hXt
    rw [List.append_nil] at s1
    have s2 := dsF_copyL σ src tm (c := c) l (Function.update X y (List.replicate c tick)) hnd.2 hs.2
      ht.2 hst (by rw [Function.update_of_ne hs.1]; exact hX)
      (by rw [Function.update_of_ne ht.1]; exact hXt)
      (fun y' hy' => by
        have hne : y' ≠ y := fun e => hnd.1 (e ▸ hy')
        rw [Function.update_of_ne hne]; exact h0 y' (List.mem_cons_of_mem _ hy'))
    refine (s1.seq s2).mono ?_
    simp only [List.length_cons]
    ring_nf; omega

end Batch

/-! ### Phase 2a: unary values and copies -/

section P2a

variable {T Q A t₀ : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {g : DsY t₀ → Fin T}

/-- The unary pushes of phase 2a: `p, g, ℓ, γ, p + g, p, r, K, ℓ`. -/
def dsP2un : List (Fin pmNV × DsY t₀) :=
  [(2, .s (.k (.x .pU))), (21, .s (.k (.x .gU))), (7, .s (.x .lU)), (14, .s (.x .gS)),
    (28, .s (.k (.c .pn))), (2, .s (.v (.cm .pn))), (8, .o .rR), (4, .o .lK), (7, .o .lL)]

/-- The copies of `w`. -/
def dsP2wcp : List (DsY t₀) :=
  [.s (.a (.c .wn)), .s (.b (.inl (.cm .wn))), .s (.k (.c .wn)), .s (.k (.x .wU)),
    .s (.k (.x (.tbl .wn))), .s (.v (.cm .wn)), .s (.m .wn)]

/-- The copies of `d - 1`. -/
def dsP2dcp : List (DsY t₀) := [.s (.a (.x .ax)), .s (.b (.inr .ax)), .o .lD]

/-- The copies of `topN w`. -/
def dsP2ncp : List (DsY t₀) :=
  [.s (.a (.c .nn)), .s (.b (.inl (.cm .nn))), .s (.v (.cm .nn)), .s (.m .nn)]

/-- Phase 2a. -/
def dsP2a (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) : Pr P T Q A U :=
  .seq (dsLoad rg (g (.o .uw)) 39) <| .seq (dsUnL rg g dsP2un) <|
  .seq (dsCopyL g (.o .uw) (.o .tm) dsP2wcp) <|
  .seq (ucopy (g (.o .uW)) (g (.s (.k (.x (.tbl .wr))))) (g (.o .tm))) <|
  .seq (dsStep rg dsCD (g (.s (.k .ax)))) <| .seq (dsCopyL g (.s (.k .ax)) (.o .tm) dsP2dcp) <|
  .seq (dsStep rg dsCN (g (.s (.v .shS)))) <|
  .seq (ucopy (g (.s (.v .shS))) (g (.o .lN)) (g (.o .tm))) <|
  .seq (dsStep rg dsCwg (g (.s (.x .gR)))) <| .seq (dsStep rg dsCwN (g (.s (.v .shR)))) <|
  .seq (dsStep rg dsCp1 (g (.s (.m .pn)))) <| .seq (dsStep rg dsCpg2 (g (.s (.k .pn2)))) <|
  .seq (dsStep rg dsCTop (g (.s (.k (.c .nn))))) (dsCopyL g (.s (.k (.c .nn))) (.o .tm) dsP2ncp)

/-- The unary writes of phase 2a. -/
def dsP2aW₁ (n : ℕ) : List (DsY t₀ × List (Fin (A + 4))) :=
  [(.s (.k (.x .pU)), List.replicate (p n) tick),
   (.s (.k (.x .gU)), List.replicate (Chirp.chirpGuard (d n)) tick),
   (.s (.x .lU), List.replicate (ℓ n) tick), (.s (.x .gS), List.replicate (gamma n) tick),
   (.s (.k (.c .pn)), List.replicate (p n + Chirp.chirpGuard (d n)) tick),
   (.s (.v (.cm .pn)), List.replicate (p n) tick), (.o .rR, List.replicate (r n) tick),
   (.o .lK, List.replicate (K n) tick), (.o .lL, List.replicate (ℓ n) tick)]

/-- The writes of phase 2a, in order. -/
def dsP2aW (n w Wt : ℕ) : List (DsY t₀ × List (Fin (A + 4))) :=
  dsP2aW₁ n ++
  (dsP2wcp.map fun y => (y, List.replicate w tick)) ++
  [(.s (.k (.x (.tbl .wr))), List.replicate Wt tick),
   (.s (.k .ax), List.replicate (d n - 1) tick)] ++
  (dsP2dcp.map fun y => (y, List.replicate (d n - 1) tick)) ++
  [(.s (.v .shS), List.replicate (logT n - ℓ n) tick), (.o .lN, List.replicate (logT n - ℓ n) tick),
   (.s (.x .gR), List.replicate (w - gamma n) tick),
   (.s (.v .shR), List.replicate (w - (logT n - ℓ n)) tick),
   (.s (.m .pn), List.replicate (p n + 1) tick),
   (.s (.k .pn2), List.replicate (p n + Chirp.chirpGuard (d n) + 2) tick),
   (.s (.k (.c .nn)), List.replicate (dsTopN w) tick)] ++
  (dsP2ncp.map fun y => (y, List.replicate (dsTopN w) tick))

theorem dsP2aW_nodup (n w Wt : ℕ) :
    ((dsP2aW (A := A) (t₀ := t₀) n w Wt).map Prod.fst).Nodup := by
  simp [dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp, List.nodup_cons]

/-- The step bound of phase 2a. -/
def dsP2aCost (n w Wt : ℕ) : ℕ :=
  (2 * pmW n + 2 + (w * (4 * pmW n + 10) + 4 * pmW n + 8)) +
    (((dsP2un (t₀ := 0)).map fun e => pmW n * (4 * pmVal n e.1 + 11) + 2 * pmVal n e.1 + 6).sum + 1)
    + (7 * (4 * w + 4) + 1) + (4 * Wt + 4) + dsStepCost (pmW n) 3 (d n - 1) +
    (3 * (4 * (d n - 1) + 4) + 1) + dsStepCost (pmW n) 1 (logT n - ℓ n) +
    (4 * (logT n - ℓ n) + 4) + dsStepCost (pmW n) 1 (w - gamma n) +
    dsStepCost (pmW n) 2 (w - (logT n - ℓ n)) + dsStepCost (pmW n) 2 (p n + 1) +
    dsStepCost (pmW n) 3 (p n + Chirp.chirpGuard (d n) + 2) +
    dsStepCost (pmW n) (dsTopK w) (dsTopN w) + (4 * (4 * dsTopN w + 4) + 1)

variable (h : DsLay rg g)
include h

set_option maxHeartbeats 2000000 in
/-- **Phase 2a.** -/
theorem ds_P2a (R : Regs T A) {n w Wt : ℕ} (hB : Big n) (hgw : gamma n ≤ w)
    (hNw : logT n - ℓ n ≤ w) (hw4 : 4 * w + 2 < 2 ^ pmW n) (wl : List (Fin (A + 4)))
    (hwl : wl.length = pmW n) (X : DsY t₀ → List (Fin (A + 4))) (huw : (X (.o .uw)).length = w)
    (huW : (X (.o .uW)).length = Wt) (htm : X (.o .tm) = [])
    (h0 : ∀ y ∈ (dsP2aW (A := A) (t₀ := t₀) n w Wt).map Prod.fst, X y = []) :
    dsRuns body (dsP2a rg g) (dsF rg g R X (pmW n) wl (pmVals n))
      (dsF rg g R (dsUpdL X (dsP2aW n w Wt)) (pmW n) wl (dsV1 n 0 w)) (dsP2aCost n w Wt) := by
  have hw2 : w < 2 ^ pmW n := by omega
  set V := dsV1 n 0 w with hV
  have hVlt : ∀ j, V j < 2 ^ pmW n := dsV1_lt hB (Nat.two_pow_pos _) hw2
  have hV0 := dsV1_scr n 0 w
  have hz : ∀ y ∈ (dsP2aW (A := A) (t₀ := t₀) n w Wt).map Prod.fst, X y = [] := h0
  simp only [dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp, List.map_append, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h0
  -- `w`
  have s1 := dsF_load (body := body) h R wl X (pmVals n) (.o .uw) 39 hwl
  rw [huw, ← dsV1_pm, dsV1_upd39] at s1
  -- unary values
  have s2 := dsF_unL (body := body) (W := pmW n) h R wl V dsP2un X (by simp [dsP2un, List.nodup_cons])
    (fun e he => h0 e.2 (by simp [dsP2un] at he; rcases he with rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> simp)) (fun e _ => hVlt e.1)
  have e2 : (dsP2un (t₀ := t₀)).map (fun e => (e.2, List.replicate (V e.1) (tick : Fin (A + 4)))) =
      dsP2aW₁ n := by
    simp [dsP2un, dsP2aW₁, hV, dsV1, pmNV, pmVal]
  rw [e2] at s2
  set W₁ : List (DsY t₀ × List (Fin (A + 4))) := dsP2aW₁ n with hW₁
  -- copies of `w`
  have s3 := dsF_copyL (body := body) (W := pmW n) h R wl V (.o .uw) (.o .tm) (c := w) dsP2wcp
    (dsUpdL X W₁) (by simp [dsP2wcp, List.nodup_cons]) (by simp [dsP2wcp])
    (by simp [dsP2wcp]) (fun e => by cases e)
    (by rw [dsUpdL_off _ _ _ (by simp [hW₁, dsP2aW₁]), huw])
    (by rw [dsUpdL_off _ _ _ (by simp [hW₁, dsP2aW₁]), htm])
    (fun y hy => by
      simp only [dsP2wcp, List.mem_cons, List.not_mem_nil, or_false] at hy
      rw [dsUpdL_off _ _ _ (by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [hW₁, dsP2aW₁])]
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact h0 _ (by simp))
  rw [← dsUpdL_append] at s3
  set W₂ := W₁ ++ (dsP2wcp.map fun y => (y, List.replicate w (tick : Fin (A + 4)))) with hW₂
  -- `Wt`
  have s4 := dsF_ucopy (body := body) (W := pmW n) h R wl (dsUpdL X W₂) V (.o .uW)
    (.s (.k (.x (.tbl .wr)))) (.o .tm) (fun e => by cases e) (fun e => by cases e)
    (fun e => by cases e) (c := Wt) (l := [])
    (by rw [dsUpdL_off _ _ _ (by simp [hW₂, hW₁, dsP2aW₁, dsP2wcp]), huW])
    (by rw [dsUpdL_off _ _ _ (by simp [hW₂, hW₁, dsP2aW₁, dsP2wcp])]; exact h0 _ (by simp))
    (by rw [dsUpdL_off _ _ _ (by simp [hW₂, hW₁, dsP2aW₁, dsP2wcp]), htm])
  rw [List.append_nil, dsUpdL_snoc] at s4
  set W₃ := W₂ ++ [((.s (.k (.x (.tbl .wr))) : DsY t₀), List.replicate Wt (tick : Fin (A + 4)))]
    with hW₃
  have off : ∀ (ws : List (DsY t₀ × List (Fin (A + 4)))) (y : DsY t₀),
      y ∈ (dsP2aW (A := A) (t₀ := t₀) n w Wt).map Prod.fst → y ∉ ws.map Prod.fst →
      dsUpdL X ws y = [] := fun ws y hy hn' => by rw [dsUpdL_off _ _ _ hn']; exact hz y hy
  -- `d - 1` and its copies
  have s5 := dsF_step (body := body) h R wl (dsUpdL X W₃) V (.s (.k .ax))
    (dsCD_do (A := A) (w' := pmW n) (Wt := 0) (w := w) hB) hV0 hVlt hwl (l := [])
    (off _ _ (by simp [dsP2aW]) (by simp [hW₃, hW₂, hW₁, dsP2aW₁, dsP2wcp]))
  rw [List.append_nil, dsUpdL_snoc] at s5
  set W₄ := W₃ ++ [((.s (.k .ax) : DsY t₀), List.replicate (d n - 1) (tick : Fin (A + 4)))]
    with hW₄
  have s6 := dsF_copyL (body := body) (W := pmW n) h R wl V (.s (.k .ax)) (.o .tm) (c := d n - 1)
    dsP2dcp (dsUpdL X W₄) (by simp [dsP2dcp, List.nodup_cons]) (by simp [dsP2dcp])
    (by simp [dsP2dcp]) (fun e => by cases e)
    (by rw [hW₄, dsUpdL_append]; simp [dsUpdL])
    (by rw [dsUpdL_off _ _ _ (by simp [hW₄, hW₃, hW₂, hW₁, dsP2aW₁, dsP2wcp]), htm])
    (fun y hy => by
      simp only [dsP2dcp, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl <;>
        exact off _ _ (by simp [dsP2aW, dsP2dcp]) (by simp [hW₄, hW₃, hW₂, hW₁, dsP2aW₁, dsP2wcp]))
  rw [← dsUpdL_append] at s6
  set W₅ := W₄ ++ (dsP2dcp.map fun y => (y, List.replicate (d n - 1) (tick : Fin (A + 4))))
    with hW₅
  -- `N` and its copy
  have s7 := dsF_step (body := body) h R wl (dsUpdL X W₅) V (.s (.v .shS))
    (dsCN_do (A := A) (w' := pmW n) (Wt := 0) (w := w) hB) hV0 hVlt hwl (l := [])
    (off _ _ (by simp [dsP2aW]) (by simp [hW₅, hW₄, hW₃, hW₂, hW₁, dsP2aW₁, dsP2wcp, dsP2dcp]))
  rw [List.append_nil, dsUpdL_snoc] at s7
  set W₆ := W₅ ++ [((.s (.v .shS) : DsY t₀), List.replicate (logT n - ℓ n) (tick : Fin (A + 4)))]
    with hW₆
  have s8 := dsF_ucopy (body := body) (W := pmW n) h R wl (dsUpdL X W₆) V (.s (.v .shS))
    (.o .lN) (.o .tm) (fun e => by cases e) (fun e => by cases e) (fun e => by cases e)
    (c := logT n - ℓ n) (l := []) (by rw [hW₆, dsUpdL_append]; simp [dsUpdL])
    (off _ _ (by simp [dsP2aW]) (by simp [hW₆, hW₅, hW₄, hW₃, hW₂, hW₁, dsP2aW₁, dsP2wcp, dsP2dcp]))
    (by rw [dsUpdL_off _ _ _ (by simp [hW₆, hW₅, hW₄, hW₃, hW₂, hW₁, dsP2aW₁, dsP2wcp, dsP2dcp]),
      htm])
  rw [List.append_nil, dsUpdL_snoc] at s8
  set W₇ := W₆ ++ [((.o .lN : DsY t₀), List.replicate (logT n - ℓ n) (tick : Fin (A + 4)))]
    with hW₇
  -- `w - γ`, `w - N`, `p + 1`, `p + g + 2`
  have s9 := dsF_step (body := body) h R wl (dsUpdL X W₇) V (.s (.x .gR))
    (dsCwg_do (A := A) (w' := pmW n) (n := n) hgw hw2) hV0 hVlt hwl (l := [])
    (off _ _ (by simp [dsP2aW]) (by simp [hW₇, hW₆, hW₅, hW₄, hW₃, hW₂, hW₁, dsP2aW₁, dsP2wcp,
      dsP2dcp]))
  rw [List.append_nil, dsUpdL_snoc] at s9
  set W₈ := W₇ ++ [((.s (.x .gR) : DsY t₀), List.replicate (w - gamma n) (tick : Fin (A + 4)))]
    with hW₈
  have s10 := dsF_step (body := body) h R wl (dsUpdL X W₈) V (.s (.v .shR))
    (dsCwN_do (A := A) (w' := pmW n) (n := n) hB hNw hw2) hV0 hVlt hwl (l := [])
    (off _ _ (by simp [dsP2aW]) (by simp [hW₈, hW₇, hW₆, hW₅, hW₄, hW₃, hW₂, hW₁, dsP2aW₁, dsP2wcp,
      dsP2dcp]))
  rw [List.append_nil, dsUpdL_snoc] at s10
  set W₉ := W₈ ++ [((.s (.v .shR) : DsY t₀),
    List.replicate (w - (logT n - ℓ n)) (tick : Fin (A + 4)))] with hW₉
  have s11 := dsF_step (body := body) h R wl (dsUpdL X W₉) V (.s (.m .pn))
    (dsCp1_do (A := A) (w' := pmW n) (n := n) (w := w)) hV0 hVlt hwl (l := [])
    (off _ _ (by simp [dsP2aW]) (by simp [hW₉, hW₈, hW₇, hW₆, hW₅, hW₄, hW₃, hW₂, hW₁, dsP2aW₁,
      dsP2wcp, dsP2dcp]))
  rw [List.append_nil, dsUpdL_snoc] at s11
  set W₁₀ := W₉ ++ [((.s (.m .pn) : DsY t₀), List.replicate (p n + 1) (tick : Fin (A + 4)))]
    with hW₁₀
  have s12 := dsF_step (body := body) h R wl (dsUpdL X W₁₀) V (.s (.k .pn2))
    (dsCpg2_do (A := A) (w' := pmW n) (n := n) (w := w)) hV0 hVlt hwl (l := [])
    (off _ _ (by simp [dsP2aW]) (by simp [hW₁₀, hW₉, hW₈, hW₇, hW₆, hW₅, hW₄, hW₃, hW₂, hW₁,
      dsP2aW₁, dsP2wcp, dsP2dcp]))
  rw [List.append_nil, dsUpdL_snoc] at s12
  set W₁₁ := W₁₀ ++ [((.s (.k .pn2) : DsY t₀),
    List.replicate (p n + Chirp.chirpGuard (d n) + 2) (tick : Fin (A + 4)))] with hW₁₁
  -- `topN w` and its copies
  have s13 := dsF_step (body := body) h R wl (dsUpdL X W₁₁) V (.s (.k (.c .nn)))
    (dsCTop_do (A := A) (w' := pmW n) (n := n) (Wt := 0) (w := w) hw4) hV0 hVlt hwl (l := [])
    (off _ _ (by simp [dsP2aW]) (by simp [hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆, hW₅, hW₄, hW₃, hW₂, hW₁,
      dsP2aW₁, dsP2wcp, dsP2dcp]))
  rw [List.append_nil, dsUpdL_snoc] at s13
  set W₁₂ := W₁₁ ++ [((.s (.k (.c .nn)) : DsY t₀), List.replicate (dsTopN w) (tick : Fin (A + 4)))]
    with hW₁₂
  have s14 := dsF_copyL (body := body) (W := pmW n) h R wl V (.s (.k (.c .nn))) (.o .tm)
    (c := dsTopN w) dsP2ncp (dsUpdL X W₁₂) (by simp [dsP2ncp, List.nodup_cons])
    (by simp [dsP2ncp]) (by simp [dsP2ncp]) (fun e => by cases e)
    (by rw [hW₁₂, dsUpdL_append]; simp [dsUpdL])
    (by rw [dsUpdL_off _ _ _ (by simp [hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆, hW₅, hW₄, hW₃, hW₂,
      hW₁, dsP2aW₁, dsP2wcp, dsP2dcp]), htm])
    (fun y hy => by
      simp only [dsP2ncp, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        exact off _ _ (by simp [dsP2aW, dsP2ncp]) (by simp [hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆,
          hW₅, hW₄, hW₃, hW₂, hW₁, dsP2aW₁, dsP2wcp, dsP2dcp]))
  rw [← dsUpdL_append] at s14
  have eW : W₁₂ ++ (dsP2ncp.map fun y => (y, List.replicate (dsTopN w) (tick : Fin (A + 4)))) =
      dsP2aW n w Wt := by
    simp [hW₁₂, hW₁₁, hW₁₀, hW₉, hW₈, hW₇, hW₆, hW₅, hW₄, hW₃, hW₂, hW₁, dsP2aW]
  rw [eW] at s14
  refine (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    (s11.seq (s12.seq (s13.seq s14))))))))))))).congr_left (by rw [dsV1_pm]) |>.mono ?_
  unfold dsP2aCost
  have e : ∀ e ∈ (dsP2un (t₀ := t₀)), V e.1 = pmVal n e.1 := fun e he => by
    simp [dsP2un] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hV, dsV1, pmNV]
  have e' : ((dsP2un (t₀ := t₀)).map fun e => pmW n * (4 * V e.1 + 11) + 2 * V e.1 + 6) =
      ((dsP2un (t₀ := 0)).map fun e => pmW n * (4 * pmVal n e.1 + 11) + 2 * pmVal n e.1 + 6) := by
    simp [dsP2un, hV, dsV1, pmNV]
  rw [e']
  simp only [dsP2wcp, dsP2dcp, dsP2ncp, List.length_cons, List.length_nil]
  omega

end P2a

end IntegerMultBounds.MathlibTM2.Fast.TableVM
