module

public import IntegerMultBounds.MathlibTM2.Fast.DistSrcP2c
public import IntegerMultBounds.MathlibTM2.Fast.DistSrcP2b
public import IntegerMultBounds.MathlibTM2.Fast.DistSrcPC
public import IntegerMultBounds.MathlibTM2.Fast.DistSrcP1
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The converter into the source transform

`dsSrc rg g = dsP1; dsPC; dsP2a; dsP2b; dsP2c`: one fixed program running after the parameter
machine on its layout `rg` and on the registers `g = dsGY sg io` of the source transform
(`sg : SrcR t₀ → Fin T`) and of the converter (`io : DsX → Fin T`). From `Wt` symbols on
`o .uW`, `w` symbols on `o .uw` and every other register of the family empty, it ends with the
writes `dsSrcW n w Wt hd0` (`ds_src_runs`): every register of the family not written ends as it
started; the parameter layout ends as it started.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ChirpSt


section Src

variable {T Q A t₀ : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {g : DsY t₀ → Fin T}

/-- **The converter.** -/
def dsSrc (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) : Pr P T Q A U :=
  .seq (dsP1 rg g) (.seq (dsPC rg g) (.seq (dsP2a rg g) (.seq (dsP2b rg g) (dsP2c rg g))))

/-- The step bound of the converter. -/
noncomputable def dsSrcCost (n w Wt : ℕ) : ℕ :=
  dsP1Cost n Wt + dsPCCost n + dsP2aCost n w Wt + dsP2bCost n w + dsP2cCost n w Wt

/-- The writes of phases 1 and C. -/
noncomputable def dsSrcW₁ (n Wt : ℕ) (hd0 : 0 < d n) : List (DsY t₀ × List (Fin (A + 4))) :=
  [(dsyA, preRecsA n Wt hd0 0 ++ (preRecsA n Wt hd0 0 ++ preRecsA n Wt hd0 0)),
   (dsyB, preRecsB n Wt hd0 0 ++ (preRecsB n Wt hd0 0 ++ preRecsB n Wt hd0 0)),
   (.s (.x .tSp), ldcBlocks (List.ofFn (t n))), (.s (.x .sSp), ldcBlocks (List.ofFn (s n))),
   (dsyWT, crtEnts ((crtRevAx (d n)).map (srcAx n))),
   (dsySTc, crtEnts ((crtRevAx (d n)).map (s n))),
   (dsyMT, crtEnts ((crtRevAx (d n)).map fun j =>
      (crtMu (s n) (Pipeline.s_pairwise n) j : ZMod (s n j)).val)),
   (dsySig, binSyms (crtPre (srcAx n) (d n)) (crtSig (srcAx n) (s n) (d n))),
   (dsyMsk, binSyms (crtPre (srcAx n) (d n)) (crtMask (srcAx n) (d n)))]

/-- All the writes of the converter. -/
noncomputable def dsSrcW (n w Wt : ℕ) (hd0 : 0 < d n) : List (DsY t₀ × List (Fin (A + 4))) :=
  dsSrcW₁ n Wt hd0 ++ dsP2aW n w Wt ++ dsP2bW n w ++ dsP2cW n w

theorem dsSrcW_nodup (n w Wt : ℕ) (hd0 : 0 < d n) :
    ((dsSrcW (A := A) (t₀ := t₀) n w Wt hd0).map Prod.fst).Nodup := by
  simp [dsSrcW, dsSrcW₁, dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp, dsP2bW, dsP2cW,
    List.nodup_cons]

/-- The registers phases 2a, 2b, 2c write are not written before and are not inputs. -/
theorem dsP2_keys (n w Wt : ℕ) :
    ∀ y ∈ (dsP2aW (A := A) (t₀ := t₀) n w Wt ++ dsP2bW n w ++ dsP2cW n w).map Prod.fst,
      y ∉ (dsP1Out : List (DsY t₀)) ∧ y ∉ (dsPCOut : List (DsY t₀)) ∧ y ≠ .o .uW ∧ y ≠ .o .uw ∧
      y ≠ .o .tm ∧ y ≠ .o .xT ∧ y ≠ .o .uq ∧ ∀ r, y ≠ .s (.k (.x (.tbl (.v r)))) := by
  rw [List.forall_mem_map]
  simp only [dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp, dsP2bW, dsP2cW, 
    List.map_cons, List.map_nil, List.forall_mem_append, List.forall_mem_cons]
  simp [dsP1Out, dsPCOut]

variable (h : DsLay rg g)
include h

set_option maxHeartbeats 4000000 in
/-- **The converter.** -/
theorem ds_src_runs (R : Regs T A) {n w Wt : ℕ} (hbig : Big n) (hd0 : 0 < d n)
    (hpw : p n + 2 ≤ w) (hgw : gamma n ≤ w) (hNw : logT n - ℓ n ≤ w)
    (hw4 : 4 * w + 2 < 2 ^ pmW n) (hWL : pmW n ≤ dsWL n w) (hWt : Wt < 2 ^ pmW n)
    (hwW : w < Wt) (hW8 : 8 * p n + Nat.size (r n) + 80 ≤ Wt)
    (wl : List (Fin (A + 4))) (hwl : wl.length = pmW n) (X : DsY t₀ → List (Fin (A + 4)))
    (huW : (X (.o .uW)).length = Wt) (huw : (X (.o .uw)).length = w)
    (hX : ∀ y, y ≠ .o .uW → y ≠ .o .uw → X y = []) :
    ∃ X' : DsY t₀ → List (Fin (A + 4)),
      (∀ e ∈ dsSrcW (A := A) (t₀ := t₀) n w Wt hd0, X' e.1 = e.2) ∧
      (∀ y, y ∉ (dsSrcW (A := A) (t₀ := t₀) n w Wt hd0).map Prod.fst → X' y = X y) ∧
      dsRuns body (dsSrc rg g) (dsF rg g R X (pmW n) wl (pmVals n))
        (dsF rg g R X' (pmW n) wl (pmVals n)) (dsSrcCost n w Wt) := by
  have hn := hbig.1
  have hw2 : w < 2 ^ pmW n := by omega
  have e0 : ∀ y : DsY t₀, (∀ x, y ≠ .o x) → X y = [] := fun y hy => hX y (hy _) (hy _)
  -- phase 1
  obtain ⟨X₁, o1, v1D, v1A, v1B, v1TS, v1SS, v1WT, v1ST, s1⟩ := ds_P1 (body := body) h R hbig hd0
    hWt wl hwl X huW (fun y hy => by
      simp only [dsP1Pre, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hX _ (fun e => by cases e) (fun e => by cases e))
  -- phase C
  obtain ⟨X₂, o2, v2D, v2MT, v2Sig, v2Msk, s2⟩ := ds_PC (body := body) h R hbig wl hwl X₁
    (by rw [v1D, List.length_replicate]) (fun y hy => by
      simp only [dsPCPre, List.mem_cons, List.not_mem_nil, or_false] at hy
      rw [o1 y (by rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dsP1Out])]
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hX _ (fun e => by cases e) (fun e => by cases e))
  have x2 : ∀ y, y ∉ (dsP1Out : List (DsY t₀)) → y ∉ (dsPCOut : List (DsY t₀)) → X₂ y = X y :=
    fun y h1 h2 => by rw [o2 y h2, o1 y h1]
  have hK := dsP2_keys (A := A) (t₀ := t₀) n w Wt
  have hK2 : ∀ y, y ∈ (dsP2aW (A := A) (t₀ := t₀) n w Wt ++ dsP2bW n w ++ dsP2cW n w).map
      Prod.fst → X₂ y = [] := fun y hy => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hK y hy
    rw [x2 y h1 h2]; exact hX y h3 h4
  have hO : ∀ x : DsX, x ≠ .uD → x ≠ .uW → x ≠ .uw → X₂ (.o x) = [] := fun x h1 h2 h3 => by
    rw [x2 _ (by simp [dsP1Out]; exact h1) (by simp [dsPCOut]; exact h1)]
    exact hX _ (by simpa using h2) (by simpa using h3)
  -- phase 2a
  have s3 := ds_P2a (body := body) h R hbig hgw hNw hw4 wl hwl X₂
    (by rw [x2 _ (by simp [dsP1Out]) (by simp [dsPCOut]), huw])
    (by rw [x2 _ (by simp [dsP1Out]) (by simp [dsPCOut]), huW])
    (hO .tm (by decide) (by decide) (by decide))
    (fun y hy => hK2 y (by simp only [List.map_append, List.mem_append]; exact Or.inl (Or.inl hy)))
  set X₃ := dsUpdL X₂ (dsP2aW (A := A) (t₀ := t₀) n w Wt) with hX₃
  have o3 : ∀ y, y ∉ (dsP2aW (A := A) (t₀ := t₀) n w Wt).map Prod.fst → X₃ y = X₂ y :=
    fun y hy => dsUpdL_off _ _ y hy
  have v3 : ∀ e ∈ dsP2aW (A := A) (t₀ := t₀) n w Wt, X₃ e.1 = e.2 :=
    dsUpdL_on _ _ (dsP2aW_nodup n w Wt)
  -- phase 2b
  have s4 := ds_P2b (body := body) h R hbig hpw hw4 hWL wl hwl X₃
    (by rw [o3 _ (by simp [dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp]),
      x2 _ (by simp [dsP1Out]) (by simp [dsPCOut]), huw])
    (by rw [v3 (.o .rR, List.replicate (r n) tick) (by simp [dsP2aW, dsP2aW₁])]; simp)
    (by rw [o3 _ (by simp [dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp])]
        exact hO .tm (by decide) (by decide) (by decide))
    (by rw [o3 _ (by simp [dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp])]
        exact hO .xT (by decide) (by decide) (by decide))
    (by rw [o3 _ (by simp [dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp])]
        exact hO .uq (by decide) (by decide) (by decide))
    (fun y hy => by
      rw [o3 _ (by
        simp only [dsP2bW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl <;>
          simp [dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp])]
      exact hK2 y (by simp only [List.map_append, List.mem_append]; exact Or.inl (Or.inr hy)))
  set X₄ := dsUpdL X₃ (dsP2bW (A := A) (t₀ := t₀) n w) with hX₄
  have o4 : ∀ y, y ∉ (dsP2bW (A := A) (t₀ := t₀) n w).map Prod.fst → X₄ y = X₃ y :=
    fun y hy => dsUpdL_off _ _ y hy
  have v4 : ∀ e ∈ dsP2bW (A := A) (t₀ := t₀) n w, X₄ e.1 = e.2 :=
    dsUpdL_on _ _ (by simp [dsP2bW, List.nodup_cons])
  -- the kernel table registers
  have hTbl : ∀ x : TblR 84, x ≠ .wr → x ≠ .wn → X₄ (.s (.k (.x (.tbl x)))) = [] := by
    intro x h1 h2
    rw [o4 _ (by simp [dsP2bW]), o3 _ (by simp [dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp, h1, h2]),
      x2 _ (by simp [dsP1Out]) (by simp [dsPCOut])]
    exact hX _ (by simp) (by simp)
  -- disjointness of the write lists
  have hnd := dsSrcW_nodup (A := A) (t₀ := t₀) n w Wt hd0
  simp only [dsSrcW, List.map_append, List.nodup_append] at hnd
  obtain ⟨⟨⟨-, -, d1a⟩, -, d12b⟩, -, d123c⟩ := hnd
  have dab : ∀ e ∈ dsP2aW (A := A) (t₀ := t₀) n w Wt, e.1 ∉ (dsP2bW (A := A) (t₀ := t₀) n w).map
      Prod.fst := fun e he hm =>
    d12b e.1 (List.mem_append_right _ (List.mem_map_of_mem he)) e.1 hm rfl
  have dac : ∀ e ∈ dsP2aW (A := A) (t₀ := t₀) n w Wt, e.1 ∉ (dsP2cW (A := A) (t₀ := t₀) n w).map
      Prod.fst := fun e he hm =>
    d123c e.1 (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem he))) e.1 hm rfl
  have dbc : ∀ e ∈ dsP2bW (A := A) (t₀ := t₀) n w, e.1 ∉ (dsP2cW (A := A) (t₀ := t₀) n w).map
      Prod.fst := fun e he hm =>
    d123c e.1 (List.mem_append_right _ (List.mem_map_of_mem he)) e.1 hm rfl
  have d1 : ∀ e ∈ dsSrcW₁ (A := A) (t₀ := t₀) n Wt hd0,
      e.1 ∉ (dsP2aW (A := A) (t₀ := t₀) n w Wt).map Prod.fst ∧
      e.1 ∉ (dsP2bW (A := A) (t₀ := t₀) n w).map Prod.fst ∧
      e.1 ∉ (dsP2cW (A := A) (t₀ := t₀) n w).map Prod.fst := fun e he =>
    ⟨fun hm => d1a e.1 (List.mem_map_of_mem he) e.1 hm rfl,
      fun hm => d12b e.1 (List.mem_append_left _ (List.mem_map_of_mem he)) e.1 hm rfl,
      fun hm => d123c e.1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem he)))
        e.1 hm rfl⟩
  have k4 : ∀ e ∈ dsP2aW (A := A) (t₀ := t₀) n w Wt, X₄ e.1 = e.2 := fun e he => by
    rw [o4 _ (dab e he)]
    exact v3 e he
  -- phase 2c
  have s5 := ds_P2c (body := body) h R hbig hw2 hwW hW8 wl hwl X₄
    (fun i => hTbl _ (by simp) (by simp)) (hTbl _ (by simp) (by simp))
    (fun j => hTbl _ (by simp) (by simp))
    (by rw [k4 (.s (.k (.x (.tbl .wr))), List.replicate Wt tick) (by simp [dsP2aW])]; simp)
    (by rw [k4 (.s (.k (.x (.tbl .wn))), List.replicate w tick) (by simp [dsP2aW, dsP2wcp])]; simp)
    (by rw [k4 (.s (.k (.x .pU)), List.replicate (p n) tick) (by simp [dsP2aW, dsP2aW₁])]; simp)
    (by rw [k4 (.o .rR, List.replicate (r n) tick) (by simp [dsP2aW, dsP2aW₁])]; simp)
    (by rw [o4 _ (by simp [dsP2bW]), o3 _ (by simp [dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp]),
      x2 _ (by simp [dsP1Out]) (by simp [dsPCOut]), huw])
    (hK2 _ (by simp [dsP2cW])) (hK2 _ (by simp [dsP2cW]))
  set X₅ := dsUpdL X₄ (dsP2cW (A := A) (t₀ := t₀) n w) with hX₅
  have o5 : ∀ y, y ∉ (dsP2cW (A := A) (t₀ := t₀) n w).map Prod.fst → X₅ y = X₄ y :=
    fun y hy => dsUpdL_off _ _ y hy
  have v5 : ∀ e ∈ dsP2cW (A := A) (t₀ := t₀) n w, X₅ e.1 = e.2 :=
    dsUpdL_on _ _ (by simp [dsP2cW])
  have x2v : ∀ e ∈ dsSrcW₁ (A := A) (t₀ := t₀) n Wt hd0, X₂ e.1 = e.2 := by
    intro e he
    simp only [dsSrcW₁, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [o2 _ (by simp [dsPCOut])]; exact v1A
    · rw [o2 _ (by simp [dsPCOut])]; exact v1B
    · rw [o2 _ (by simp [dsPCOut])]; exact v1TS
    · rw [o2 _ (by simp [dsPCOut])]; exact v1SS
    · rw [o2 _ (by simp [dsPCOut])]; exact v1WT
    · rw [o2 _ (by simp [dsPCOut])]; exact v1ST
    · exact v2MT
    · exact v2Sig
    · exact v2Msk
  refine ⟨X₅, fun e he => ?_, fun y hy => ?_, ?_⟩
  · simp only [dsSrcW, List.mem_append] at he
    rcases he with ((he | he) | he) | he
    · obtain ⟨h1, h2, h3⟩ := d1 e he
      rw [o5 _ h3, o4 _ h2, o3 _ h1]; exact x2v e he
    · rw [o5 _ (dac e he)]; exact k4 e he
    · rw [o5 _ (dbc e he)]; exact v4 e he
    · exact v5 e he
  · simp only [dsSrcW, List.map_append, List.mem_append, not_or] at hy
    obtain ⟨⟨⟨hy1, hy2⟩, hy3⟩, hy4⟩ := hy
    rw [o5 _ hy4, o4 _ hy3, o3 _ hy2]
    by_cases hD : y = .o .uD
    · subst hD; rw [v2D, hX _ (by simp) (by simp)]
    · refine x2 y ?_ ?_
      · simp only [dsP1Out, List.mem_cons, List.not_mem_nil, or_false, not_or]
        simp only [dsSrcW₁, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false, not_or] at hy1
        exact ⟨hD, hy1.1, hy1.2.1, hy1.2.2.2.2.1, hy1.2.2.2.2.2.1, hy1.2.2.1, hy1.2.2.2.1⟩
      · simp only [dsPCOut, List.mem_cons, List.not_mem_nil, or_false, not_or]
        simp only [dsSrcW₁, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false, not_or] at hy1
        exact ⟨hD, hy1.2.2.2.2.2.2.1, hy1.2.2.2.2.2.2.2.1, hy1.2.2.2.2.2.2.2.2⟩
  · refine (s1.seq (s2.seq (s3.seq (s4.seq s5)))).mono ?_
    unfold dsSrcCost
    omega

end Src

end IntegerMultBounds.MathlibTM2.Fast.TableVM
