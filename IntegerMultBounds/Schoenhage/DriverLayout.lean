module

public import IntegerMultBounds.Schoenhage.DriverCalls
public import IntegerMultBounds.Schoenhage.AlphaLift

/-! The layout step of the transform drivers (§6 task 6): the tensor driver of the resampling
section, with no axis programs, runs the layout's field swaps on the array (named tape 0) from the
layout script (named tape 7). The layout script moves the natural order to the paper's layout
(`runs_layoutStep`); the undo script moves it back (`runs_undoStep`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage

open Machine Strm Spec.SignedRingProduct Resampling AxisDriver LayoutMachines
open Networks.Shared50ModularControl (prime)

/-- The tensor driver with no axis programs: only swap records are run. -/
noncomputable def layoutSpec : AxisSpec 1 where
  cmd := clear 0
  X := 0
  regs := []
  junk := []
  ρ := fun _ => emp
  Good := fun _ _ => False
  f := fun _ A => A
  cost := fun _ _ => 0
  J := fun _ _ => 0
  regs_nodup := List.nodup_nil
  junk_nodup := List.nodup_nil
  regs_junk := by simp
  X_junk := by simp
  ρ_junk := by simp
  run := fun _ _ h => h.elim

theorem nl_pos : 0 < NL := by unfold NL AxisDriver.NB; omega

/-- The layout driver as a primitive over the alphabet `A ≥ prime`. -/
noncomputable def layoutPrim (A : ℕ) (hP : prime ≤ A) : Prim A :=
  Prim.liftE hP (Prim.ofHoare (compile nl_pos (drive layoutSpec)).2 nl_pos)

/-- Run the script on named tape 7 against the array on named tape 0. -/
noncomputable def layoutStep (A tL : ℕ) (hP : prime ≤ A) : Cmd A (DB tL NL) :=
  .prim (layoutPrim A hP) (aslot tL) aslot_injective

/-- The layout script's words. -/
def layoutWords (r w : ℕ) (ts : List ℕ) (ℓ K : ℕ) : List (List Bool) :=
  ((layoutOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w))).flatMap AxisDriver.Rec.words

/-- The undo script's words. -/
def undoWords (r w : ℕ) (ts : List ℕ) (ℓ K : ℕ) : List (List Bool) :=
  ((undoOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w))).flatMap AxisDriver.Rec.words

variable {A tL : ℕ} {r : ℕ}

theorem runs_driveStep (hP : prime ≤ A) (v : Fin 13 → WTape) (tw : Fin 29 → WTape) {X X' : List Bool}
    {S S' : WTape} {k : ℕ} (h0 : v 0 = reg X) (h7 : v 7 = S)
    (hd : Runs (drive layoutSpec) (bank (fun _ => emp) 0 X S) (· = bank (fun _ => emp) 0 X' S') k) :
    Runs (layoutStep A tL hP) (dstate tL NL v tw)
      (· = dstate tL NL (Function.update (Function.update v 0 (reg X')) 7 S') tw) k := by
  obtain ⟨σ', k', hx, hq, hk⟩ := hd
  subst hq
  have hT : HoareTo (compile nl_pos (drive layoutSpec)).2 (dstate tL NL v tw ∘ aslot tL)
      (bank (fun _ => emp) 0 X' S') k := by
    rw [dstate_comp_aslot v tw h0 h7]
    exact (compile_correct nl_pos hx).consequence (fun _ h => h) (fun _ h => h) hk
  have s := runs_ofHoare_liftE hP _ nl_pos aslot_injective hT
  rwa [upd_dstate_aslot] at s

theorem runs_layoutStep (hP : prime ≤ A) {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {w : ℕ}
    (hw : 0 < 2 * r * w) (z : ℕ → Rec r) (v : Fin 13 → WTape) (tw : Fin 29 → WTape) (L : List (List Bool))
    (h0 : v 0 = reg (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y)))
    (h7 : v 7 = ⟨L, layoutWords r w ts ℓ K⟩) :
    Runs (layoutStep A tL hP) (dstate tL NL v tw)
      (· = dstate tL NL (Function.update (Function.update v 0
        (reg (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y)))))
        7 ⟨(layoutWords r w ts ℓ K).reverse ++ L, []⟩) tw)
      (driveCost layoutSpec ((layoutOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w)))
        (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y))) :=
  runs_driveStep hP v tw h0 h7 (runs_layout layoutSpec hL hw z L)

theorem runs_undoStep (hP : prime ≤ A) {ts : List ℕ} {ℓ K : ℕ} (hL : LayoutOK r ts ℓ K) {w : ℕ}
    (hw : 0 < 2 * r * w) (z : ℕ → Rec r) (v : Fin 13 → WTape) (tw : Fin 29 → WTape) (L : List (List Bool))
    (h0 : v 0 = reg (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y))))
    (h7 : v 7 = ⟨L, undoWords r w ts ℓ K⟩) :
    Runs (layoutStep A tL hP) (dstate tL NL v tw)
      (· = dstate tL NL (Function.update (Function.update v 0
        (reg (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z y))))
        7 ⟨(undoWords r w ts ℓ K).reverse ++ L, []⟩) tw)
      (driveCost layoutSpec ((undoOpList ts ℓ K).map (opRec (addrBits ts) (2 * r * w)))
        (array w (List.ofFn fun y : Fin (2 ^ addrBits ts) => z ((paperPerm hL).logi y)))) :=
  runs_driveStep hP v tw h0 h7 (runs_undo layoutSpec hL hw z L)

end IntegerMultBounds.Schoenhage
