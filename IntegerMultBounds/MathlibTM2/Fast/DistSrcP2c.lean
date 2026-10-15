module

public import IntegerMultBounds.MathlibTM2.Fast.DistSrcP2b

/-!
# Phase 2c of the converter: the twist tables

`dsP2c rg g`: the twist streams `tblTwistStream A w p r false` and `… true` of the convolution
stage onto `v .tp`, `v .tm`, by the twist table program on the 84 table registers of the chirp
kernel family (`k (.x (.tbl r))`, with `Wt` symbols on `wr` and `w` on `wn`), then `w` cleared
from variable `39`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ChirpSt

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section P2c

variable {T Q A t₀ : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR pmNV → Fin T}
  {g : DsY t₀ → Fin T}

/-- The table registers of the chirp kernel family. -/
def dsRgK (g : DsY t₀ → Fin T) (r : TblR 84) : Fin T := g (.s (.k (.x (.tbl r))))

/-- Phase 2c. -/
def dsP2c (rg : TblR pmNV → Fin T) (g : DsY t₀ → Fin T) : Pr P T Q A U :=
  .seq (dsTwist (dsRgK g) (g (.s (.k (.x .pU)))) (g (.o .rR)) (g (.o .uw)) (g (.s (.v .tp))) false)
    (.seq (dsTwist (dsRgK g) (g (.s (.k (.x .pU)))) (g (.o .rR)) (g (.o .uw)) (g (.s (.v .tm)))
      true) (tblCompile rg dsZ39))

/-- The writes of phase 2c. -/
def dsP2cW (n w : ℕ) : List (DsY t₀ × List (Fin (A + 4))) :=
  [(.s (.v .tp), tblTwistStream A w (p n) (r n) false),
   (.s (.v .tm), tblTwistStream A w (p n) (r n) true)]

/-- The step bound of phase 2c. -/
def dsP2cCost (n w Wt : ℕ) : ℕ :=
  2 * dsTwistCost Wt w (p n) (r n) + tblC (pmW n) (pmW n)

variable (h : DsLay rg g)
include h

theorem dsRgK_inj : Function.Injective (dsRgK g) := by
  intro x y e
  have := h.ig e
  simp only [DsY.s.injEq, SrcR.k.injEq, CsR.x.injEq, ldcX.tbl.injEq] at this
  exact this

/-- The twist stream in the family form. -/
theorem dsF_twist (R : Regs T A) {W : ℕ} (wl : List (Fin (A + 4))) (X : DsY t₀ → List (Fin (A + 4)))
    (σ : Fin pmNV → ℕ) (yP yR yW yo : DsY t₀)
    (hyk : ∀ y ∈ [yP, yR, yW, yo], ∀ r, (.s (.k (.x (.tbl r))) : DsY t₀) ≠ y) (conj : Bool)
    {Wt w pv rv : ℕ} {l : List (Fin (A + 4))}
    (hv : ∀ i, X (.s (.k (.x (.tbl (.v i))))) = []) (hacc : X (.s (.k (.x (.tbl .acc)))) = [])
    (hz : ∀ j, X (.s (.k (.x (.tbl (.z j))))) = [])
    (hwr : (X (.s (.k (.x (.tbl .wr))))).length = Wt)
    (hwn : (X (.s (.k (.x (.tbl .wn))))).length = w) (hwW : w < Wt)
    (hP : (X yP).length = pv) (hR : (X yR).length = rv) (hW : (X yW).length = w)
    (hp2 : pv < 2 ^ Wt) (hr2 : rv < 2 ^ Wt) (hr0 : 0 < rv) (hW8 : 8 * pv + Nat.size rv + 80 ≤ Wt)
    (ho : X yo = l) :
    dsRuns body (dsTwist (dsRgK g) (g yP) (g yR) (g yW) (g yo) conj) (dsF rg g R X W wl σ)
      (dsF rg g R (Function.update X yo (tblTwistStream A w pv rv conj ++ l)) W wl σ)
      (dsTwistCost Wt w pv rv) := by
  have s := ds_twist (body := body) (rg := dsRgK g) (dsRgK_inj h) (uP := g yP) (uR := g yR)
    (uW := g yW) (out := g yo)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro k (rfl | rfl | rfl | rfl) r e <;> exact hyk _ (by simp) r (h.ig e))
    conj (dsF rg g R X W wl σ) (fun i => by rw [dsRgK, dsF_g h, hv]) (by rw [dsRgK, dsF_g h, hacc])
    (fun j => by rw [dsRgK, dsF_g h, hz]) (by rw [dsRgK, dsF_g h, hwr])
    (by rw [dsRgK, dsF_g h, hwn]) hwW (by rw [dsF_g h, hP]) (by rw [dsF_g h, hR])
    (by rw [dsF_g h, hW]) hp2 hr2 hr0 hW8
  rw [dsF_g h, dsF_upd h, ho] at s
  exact s

set_option maxHeartbeats 1000000 in
/-- **Phase 2c.** -/
theorem ds_P2c (R : Regs T A) {n w Wt : ℕ} (hn : 2 ≤ n) (hw2 : w < 2 ^ pmW n) (hwW : w < Wt)
    (hW8 : 8 * p n + Nat.size (r n) + 80 ≤ Wt) (wl : List (Fin (A + 4)))
    (hwl : wl.length = pmW n) (X : DsY t₀ → List (Fin (A + 4)))
    (hv : ∀ i, X (.s (.k (.x (.tbl (.v i))))) = []) (hacc : X (.s (.k (.x (.tbl .acc)))) = [])
    (hz : ∀ j, X (.s (.k (.x (.tbl (.z j))))) = [])
    (hwr : (X (.s (.k (.x (.tbl .wr))))).length = Wt)
    (hwn : (X (.s (.k (.x (.tbl .wn))))).length = w)
    (hP : (X (.s (.k (.x .pU)))).length = p n) (hR : (X (.o .rR)).length = r n)
    (hW : (X (.o .uw)).length = w) (htp : X (.s (.v .tp)) = []) (htm : X (.s (.v .tm)) = []) :
    dsRuns body (dsP2c rg g) (dsF rg g R X (pmW n) wl (dsV1 n 0 w))
      (dsF rg g R (dsUpdL X (dsP2cW n w)) (pmW n) wl (pmVals n)) (dsP2cCost n w Wt) := by
  have hr0 : 0 < r n := by unfold r; positivity
  have hp2 : p n < 2 ^ Wt := by
    have := Nat.lt_two_pow_self (n := p n)
    exact this.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hr2 : r n < 2 ^ Wt := by
    have h1 : r n < 2 ^ Nat.size (r n) := Nat.lt_size_self _
    exact h1.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hyk : ∀ y ∈ [(.s (.k (.x .pU)) : DsY t₀), .o .rR, .o .uw, .s (.v .tp)],
      ∀ r, (.s (.k (.x (.tbl r))) : DsY t₀) ≠ y := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro y (rfl | rfl | rfl | rfl) r e <;> cases e
  have hyk' : ∀ y ∈ [(.s (.k (.x .pU)) : DsY t₀), .o .rR, .o .uw, .s (.v .tm)],
      ∀ r, (.s (.k (.x (.tbl r))) : DsY t₀) ≠ y := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro y (rfl | rfl | rfl | rfl) r e <;> cases e
  have s1 := dsF_twist (body := body) (W := pmW n) h R wl X (dsV1 n 0 w) _ _ _ _ hyk false hv hacc
    hz hwr hwn hwW hP hR hW hp2 hr2 hr0 hW8 htp
  rw [List.append_nil] at s1
  set X₁ := Function.update X (.s (.v .tp)) (tblTwistStream A w (p n) (r n) false) with hX₁
  have s2 := dsF_twist (body := body) (W := pmW n) h R wl X₁ (dsV1 n 0 w) _ _ _ _ hyk' true
    (fun i => by simp [hX₁, hv]) (by simp [hX₁, hacc]) (fun j => by simp [hX₁, hz])
    (by simp [hX₁, hwr]) (by simp [hX₁, hwn]) hwW (by simp [hX₁, hP]) (by simp [hX₁, hR])
    (by simp [hX₁, hW]) hp2 hr2 hr0 hW8 (l := []) (by simp [hX₁, htm])
  rw [List.append_nil] at s2
  have s3 := dsF_code (body := body) h R wl
    (Function.update X₁ (.s (.v .tm)) (tblTwistStream A w (p n) (r n) true)) (dsV1 n 0 w)
    (dsZ39_do (A := A) (n := n) (w := w)) (dsV1_lt hn (Nat.two_pow_pos _) hw2) hwl
  refine (s1.seq (s2.seq s3)).mono ?_
  unfold dsP2cCost
  omega

end P2c

end IntegerMultBounds.MathlibTM2.Fast.TableVM
