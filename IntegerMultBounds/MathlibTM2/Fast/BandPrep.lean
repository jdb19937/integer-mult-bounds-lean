module

public import IntegerMultBounds.MathlibTM2.Fast.BandPrepVM
public import IntegerMultBounds.MathlibTM2.Fast.BandAxis
public import IntegerMultBounds.MathlibTM2.Fast.BandLineSpec
public import IntegerMultBounds.MathlibTM2.Fast.TableFold
public import IntegerMultBounds.MathlibTM2.Fast.PrepB
import IntegerMultBounds.MathlibTM2.Fast.ResampBSwap
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The parameter loader of the banded `B̃₀`

`bandPreB` is the loader `prep` of `rsbAllG` for the banded line. It reads the same per-axis
record as the Neumann loader (`PreAxB`: `t`, `s`, `m`, `L`, `Ld`, `P`, `G`, `α`, `p`, `W`) from the
parameter register `prm` and derives the band parameters by unary arithmetic: the working
precision `5p`, the window `8m`, the half band `B = 16m + 1`, the scale exponent `j = α²` and
`4α²` Newton steps.

**Program.**
1. (`bandPreA`) Clear the previous axis, take the fields, write the interchange headers.
2. (`bandPreF`) The factor-phase counters and constants, and the folded rows of the window
   matrix onto `src` by the `60`-variable table machine.
3. (`bandPreL`) The line-phase values, parked on the spares `vx`: the row mask, the constants
   `2^(9p-1)` and `2^(p-α²)`, the fold counters, the padding counter, and the diagonal table
   `D · 2^(4p)` on `dtab`.
4. The factorization `bandAxisPrepP`: forward table `bo`, backward columns `hf`, reciprocals
   `df`.
5. (`bandPreE`) Clear the factor-phase counters and move the parked values into place.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Resampling.WeightTable (tableD)
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


noncomputable section

/-! ### Unary primitives -/

section Prims

variable {T Q A : ℕ} {U P : Type} {R : Type} [DecidableEq R] {body : P → Pr P T Q A U}
  {tg : R → Fin T} (htg : Function.Injective tg)
include htg

theorem twRuns_umulSym (c : ℕ) (y : Fin (A + 4)) {a b t : R} (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) :
    TwRuns body tg (umulSym c y (tg a) (tg b) (tg t)) ρ
      (Function.update ρ b (List.replicate (c * (ρ a).length) y ++ ρ b))
      (4 * (ρ a).length + 4) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := umulSym_exec body c y (htg.ne hab) (htg.ne hat) (htg.ne hbt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, twFr_upd S b _⟩
  rw [hS a, hS b]
  exact twHolds_upd htg hS b _

theorem twRuns_udiv (c : ℕ) (hc : 1 ≤ c) {a b t : R} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) :
    TwRuns body tg (udiv c (tg a) (tg b) (tg t)) ρ
      (Function.update ρ b (List.replicate ((ρ a).length / c) tick ++ ρ b))
      (4 * (ρ a).length + 4) := by
  intro v S hS
  obtain ⟨v', m, hu, hm, he⟩ := udiv_exec body hc (htg.ne hab) (htg.ne hat) (htg.ne hbt) v S
    (by rw [hS, ht])
  refine ⟨v', _, m, hu, by rw [hS] at hm; exact hm, he, ?_, twFr_upd S b _⟩
  rw [hS a, hS b]
  exact twHolds_upd htg hS b _

end Prims

/-! ### Derived parameters -/

namespace PreAxB

/-- The working precision `5p`. -/
def bP (D : PreAxB) : ℕ := 5 * D.p

/-- The Gaussian window `8m`. -/
def bWd (D : PreAxB) : ℕ := 8 * D.m

/-- The half band `2 · 8m + 1` of the folded matrix. -/
def bB (D : PreAxB) : ℕ := 2 * D.bWd + 1

/-- The Newton steps `4α²`. -/
def bK (D : PreAxB) : ℕ := 4 * (D.α * D.α)

end PreAxB

variable {t₀ T Q K : ℕ} {U F : Type}

/-- The registers cleared before loading an axis. -/
def bandClrB (hd : Fin 5 → Fin t₀) : List (RsbR ⊕ RsbX t₀) :=
  [.inl .msk, .inl .bo, .inl .hf, .inl .df, .inl .dtab, .inl .padc, .inl .sn, .inl .mwn,
    .inl .m2wn, .inl .m2n, .inl .smwn, .inl .tswn, .inl .kn, .inl .ms, .inl .bx, .inl (.cm .pn),
    preHB hd 0, preHB hd 1, preHB hd 2, preHB hd 3, preHB hd 4]

/-- The registers receiving the fields `t, s, m, L, Ld, P, G, α, p, W`. -/
def bandDstB : List (RsbR ⊕ RsbX t₀) :=
  [.inl .ya, .inl .sn, .inl .b1, .inl .tb, .inl .xa, .inl .xs, .inl .pr, .inl .hc, .inl .ac,
    .inl .hv]

section Prog

variable (g : RsbR ⊕ RsbX t₀ → Fin T) (ι : Fin 64 → Fin T) (hd : Fin 5 → Fin t₀)

/-- Step 1: clear, take the fields, the headers, clear the header fields. -/
def bandPreA : Pr F T Q (prime + K) U :=
  .seq (preClears ((bandClrB hd).map g))
  (.seq (preTakes (g (.inl .prm)) (bandDstB.map g))
  (.seq (preHdrB g hd)
    (preClears (([.inl .tb, .inl .xa, .inl .xs, .inl .pr] : List (RsbR ⊕ RsbX t₀)).map g))))

end Prog

/-! ### Step 1 -/

section StepA

variable {A : ℕ}

open Classical in
/-- Clearing the previous axis. -/
def bandF0 (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  fun r => if r ∈ bandClrB hd then [] else σ r

/-- The register file after step 1: the previous axis cleared, the parameter register `rest`,
the fields `t, s, m, α, p, W` on `ya, sn, b1, hc, ac, hv`, the interchange headers. -/
def bandFA (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) (rest : List (Fin (A + 4))) : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  preBankB (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (bandF0 σ hd)
    (.inl .prm) rest)
    (.inl .ya) (List.replicate D.t tick))
    (.inl .sn) (List.replicate D.s tick))
    (.inl .b1) (List.replicate D.m tick))
    (.inl .hc) (List.replicate D.α tick))
    (.inl .ac) (List.replicate D.p tick))
    (.inl .hv) (List.replicate D.W tick)) hd (D.hs w)

/-- The step bound of step 1. -/
def bandCostA (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) : ℕ :=
  (((bandClrB hd).map fun r => 2 * (σ r).length + 2).sum + 1) + (3 * D.fields.sum + 3 * 10 + 1) +
    preHdrCostB D w + (2 * (D.L + D.Ld + D.P + D.G) + 9)

variable {body : F → Pr F T Q (prime + K) U} {g : RsbR ⊕ RsbX t₀ → Fin T} {ι : Fin 64 → Fin T}

lemma bandClrB_nodup {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd) :
    ((bandClrB hd).map (Sum.inl : _ → (RsbR ⊕ RsbX t₀) ⊕ TblR 48)).Nodup := by
  have h : ∀ a b, reg (hd a) = reg (hd b) ↔ a = b := fun a b =>
    ⟨fun e => hdi (BinaryInterchangeRun.slot_injective e), fun e => e ▸ rfl⟩
  simp [bandClrB, preHB, List.nodup_cons, h]

/-- **Step 1 of the band loader.** -/
theorem band_preA (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd)
    (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (rest : List (Fin (prime + K + 4))) (w : ℕ)
    (hprm : σ (.inl .prm) = preRec D.fields ++ rest) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hya : σ (.inl .ya) = []) (hb1 : σ (.inl .b1) = []) (htb : σ (.inl .tb) = [])
    (hxa : σ (.inl .xa) = []) (hxs : σ (.inl .xs) = []) (hpr : σ (.inl .pr) = [])
    (hhc : σ (.inl .hc) = []) (hac : σ (.inl .ac) = []) (hhv : σ (.inl .hv) = [])
    (htL : σ (.inl .tL) = []) (hac2 : σ (.inl .ac2) = []) (hnv : σ (.inl .nv) = []) :
    TwRuns body (preLay g ι) (bandPreA g hd) (preStB σ) (preStB (bandFA σ hd w D rest))
      (bandCostA σ hd w D) := by
  have htg := preLay_inj hg hι hdisj
  -- 1. clear
  have h1 := preClears_runs (body := body) htg _ (bandClrB_nodup hdi) (preStB σ)
  rw [preLayB_map] at h1
  have h1' := twRuns_congr h1
    (show _ = preStB (bandF0 σ hd) by
      funext r; rcases r with r | y
      · simp only [preStB, bandF0, Sum.elim_inl, List.mem_map]
        by_cases h : r ∈ bandClrB hd
        · simp [h]
        · have : ¬∃ a, a ∈ bandClrB hd ∧ Sum.inl a = (Sum.inl r : (RsbR ⊕ RsbX t₀) ⊕ TblR 48) := by
            rintro ⟨a, ha, e⟩; cases e; exact h ha
          simp [h]
      · simp [preStB])
  -- 2. take the fields
  set σ1 := bandF0 σ hd with hσ1
  have h2 := preTakes_runs (body := body) htg (.inl (.inl .prm)) (bandDstB.map Sum.inl) D.fields
    (by simp [bandDstB, PreAxB.fields]) (by simp [bandDstB]) (preStB σ1) rest
    (by simp [preStB, hσ1, bandF0, bandClrB, preHB, hprm]) (fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨r', hr', rfl⟩ := hr
      simp only [bandDstB, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [preStB, hσ1, bandF0, bandClrB, preHB, hya, hb1, htb, hxa, hxs, hpr, hhc, hac, hhv])
  rw [preLayB_map] at h2
  set σ2 := preTV (.inl .prm) bandDstB D.fields rest σ1 with hσ2
  have h2' := twRuns_congr h2 (show _ = preStB σ2 by
    simp only [hσ2, preTV, bandDstB, PreAxB.fields, List.map_cons, List.map_nil, List.zip_cons_cons,
      List.zip_nil_left, List.foldl_cons, List.foldl_nil, preStB, Sum.update_elim_inl])
  -- 3. the headers
  have hv2 : σ2 (.inl .xs) = List.replicate D.P tick ∧ σ2 (.inl .pr) = List.replicate D.G tick ∧
      σ2 (.inl .tb) = List.replicate D.L tick ∧ σ2 (.inl .xa) = List.replicate D.Ld tick := by
    simp [hσ2, preTV, bandDstB, PreAxB.fields]
  have h3 := preB_hdr (body := body) hg hι hdisj hdi σ2 D w hv2.1 hv2.2.1 hv2.2.2.1 hv2.2.2.2
    (by simp [hσ2, preTV, bandDstB, PreAxB.fields, hσ1, bandF0, bandClrB,
      preHB, hwn])
    (by simp [hσ2, preTV, bandDstB, PreAxB.fields, hσ1, bandF0, bandClrB,
      preHB, htL])
    (by simp [hσ2, preTV, bandDstB, PreAxB.fields, hσ1, bandF0, bandClrB,
      preHB, hac2])
    (by simp [hσ2, preTV, bandDstB, PreAxB.fields, hσ1, bandF0, bandClrB,
      preHB, hnv])
    (fun k => by
      simp [hσ2, preTV, bandDstB, PreAxB.fields, hσ1, bandF0, bandClrB,
        preHB]
      fin_cases k <;> simp)
  -- 4. clear the header fields
  set σ3 := preBankB σ2 hd (D.hs w) with hσ3
  have h4 := preClears_runs (body := body) htg
    (([.inl .tb, .inl .xa, .inl .xs, .inl .pr] : List (RsbR ⊕ RsbX t₀)).map Sum.inl)
    (by simp) (preStB σ3)
  rw [preLayB_map] at h4
  refine twRuns_congr (twRuns_mono (twRuns_seq h1' (twRuns_seq h2' (twRuns_seq h3 h4))) ?_) ?_
  · simp only [List.map_map, Function.comp_def, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, preStB, Sum.elim_inl, hσ3]
    simp [preBankB, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2, bandCostA, PreAxB.fields]
    omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp [preStB, hσ3, hσ2, hσ1, bandFA, preBankB, preTV, bandDstB, PreAxB.fields,
        bandF0, bandClrB, preHB, htb, hxa, hxs, hpr]
    · have hx : σ2 (.inr x) = (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (bandF0 σ hd) (.inl .prm) rest)
          (.inl .ya) (List.replicate D.t tick)) (.inl .sn) (List.replicate D.s tick))
          (.inl .b1) (List.replicate D.m tick)) (.inl .hc) (List.replicate D.α tick))
          (.inl .ac) (List.replicate D.p tick)) (.inl .hv) (List.replicate D.W tick)) (.inr x) := by
        simp [hσ2, hσ1, preTV, bandDstB, PreAxB.fields]
      simp only [preStB, Sum.elim_inl]
      rw [ite_eq_right (by simp)]
      simp only [hσ3, bandFA]
      cases x with
      | sw j =>
        simp only [preBankB]
        split_ifs
        · rfl
        · exact hx
      | _ => exact hx
    · simp [preStB]

end StepA

/-! ### Step 2a: derived counts -/

section StepF1

variable (g : RsbR ⊕ RsbX t₀ → Fin T)

/-- `pn = 5p`, `tA = 8m`, `tJ = B`, `tL = 2B + 1`, `xs = B + 1 + s`. -/
def bandPreF1 : Pr F T Q (prime + K) U :=
  .seq (umul 5 (g (.inl .ac)) (g (.inl (.cm .pn))) (g (.inl .ac2)))
  (.seq (umul 8 (g (.inl .b1)) (g (.inl .tA)) (g (.inl .ac2)))
  (.seq (umul 2 (g (.inl .tA)) (g (.inl .tJ)) (g (.inl .ac2)))
  (.seq (.act (.push (.rt (g (.inl .tJ))) (fun _ => tick) .done))
  (.seq (umul 2 (g (.inl .tJ)) (g (.inl .tL)) (g (.inl .ac2)))
  (.seq (.act (.push (.rt (g (.inl .tL))) (fun _ => tick) .done))
  (.seq (ucopy (g (.inl .tJ)) (g (.inl .xs)) (g (.inl .ac2)))
  (.seq (.act (.push (.rt (g (.inl .xs))) (fun _ => tick) .done))
    (ucopy (g (.inl .sn)) (g (.inl .xs)) (g (.inl .ac2))))))))))

variable {A : ℕ}

/-- The register file after step 2a. -/
def bandFF1 (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (D : PreAxB) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update σ
    (.inl (.cm .pn)) (List.replicate D.bP tick))
    (.inl .tA) (List.replicate D.bWd tick))
    (.inl .tJ) (List.replicate D.bB tick))
    (.inl .tL) (List.replicate (2 * D.bB + 1) tick))
    (.inl .xs) (List.replicate (D.bB + 1 + D.s) tick)

/-- The step bound of step 2a. -/
def bandCostF1 (D : PreAxB) : ℕ :=
  (4 * D.p + 4) + (4 * D.m + 4) + (4 * D.bWd + 4) + 1 + (4 * D.bB + 4) + 1 + (4 * D.bB + 4) + 1 +
    (4 * D.s + 4)

lemma rep_tick_cons {A : ℕ} (n : ℕ) :
    (tick : Fin (A + 4)) :: List.replicate n tick = List.replicate (n + 1) tick := by
  rw [List.replicate_succ]

variable {body : F → Pr F T Q (prime + K) U} {g : RsbR ⊕ RsbX t₀ → Fin T} {ι : Fin 64 → Fin T}

theorem band_preF1 (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (hac : σ (.inl .ac) = List.replicate D.p tick) (hb1 : σ (.inl .b1) = List.replicate D.m tick)
    (hsn : σ (.inl .sn) = List.replicate D.s tick) (hpn : σ (.inl (.cm .pn)) = [])
    (htA : σ (.inl .tA) = []) (htJ : σ (.inl .tJ) = []) (htL : σ (.inl .tL) = [])
    (hxs : σ (.inl .xs) = []) (hac2 : σ (.inl .ac2) = []) :
    TwRuns body (preLay g ι) (bandPreF1 g) (preStB σ) (preStB (bandFF1 σ D)) (bandCostF1 D) := by
  have htg := preLay_inj hg hι hdisj
  refine twRuns_congr (twRuns_mono
    (twRuns_seq (twRuns_umul (body := body) htg 5 (a := .inl (.inl .ac)) (b := .inl (.inl (.cm .pn)))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) (preStB σ) ?_)
    (twRuns_seq (twRuns_umul (body := body) htg 8 (a := .inl (.inl .b1)) (b := .inl (.inl .tA))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (twRuns_umul (body := body) htg 2 (a := .inl (.inl .tA)) (b := .inl (.inl .tJ))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (twRuns_push (body := body) htg (.inl (.inl .tJ)) tick _)
    (twRuns_seq (twRuns_umul (body := body) htg 2 (a := .inl (.inl .tJ)) (b := .inl (.inl .tL))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (twRuns_push (body := body) htg (.inl (.inl .tL)) tick _)
    (twRuns_seq (twRuns_ucopy (body := body) htg (a := .inl (.inl .tJ)) (b := .inl (.inl .xs))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (twRuns_push (body := body) htg (.inl (.inl .xs)) tick _)
      (twRuns_ucopy (body := body) htg (a := .inl (.inl .sn)) (b := .inl (.inl .xs))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_))))))))) ?_) ?_
  all_goals try (simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq,
    reduceCtorEq, ite_false, ite_true, hac2]; done)
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, hac, hb1, hsn, htA, htJ, htL, hxs, hpn, List.length_replicate,
      List.length_cons, List.append_nil]
    unfold bandCostF1 PreAxB.bB PreAxB.bWd
    omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, bandFF1, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true, RsbR.cm.injEq]
      all_goals simp [hac, hb1, hsn, htA, htJ, htL, hxs, hpn, List.replicate_succ,
        PreAxB.bB, PreAxB.bWd, PreAxB.bP]
      all_goals (rw [List.eq_replicate_iff]; refine ⟨by simp; omega, by simp; tauto⟩)
    · simp only [Function.update_apply, preStB, bandFF1, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

end StepF1

/-! ### Step 2b: the folded rows -/

section StepFold

/-- The loads of the folded-row program: `P`, `s`, `t`, `α`, the window, the row count, the row
length and the half band. -/
def bandFoldLs : List (RsbR × Fin 60) :=
  [(.cm .pn, 19), (.sn, 34), (.ya, 35), (.hc, 36), (.tA, 39), (.xs, 49), (.tL, 51), (.tJ, 52)]

/-- The folded rows of the window matrix onto `src`. -/
def bandPreFold (rg : RsbR → Fin T) (rgx : RsbX t₀ → Fin T) (ι : Fin 64 → Fin T) :
    Pr F T Q (prime + K) U :=
  preVM (bandLay rg rgx ι) .hv (.cm .wn) bandFoldLs tblFoldStreamCode .src

/-- The atom bound of the folded-row program. -/
def bandKFold (D : PreAxB) : ℕ :=
  1 + (150 * D.bP + 400) + 8 + (1 + (D.bP * (1 + 1 + 2) + 2)) +
    (1 + ((D.bB + 1 + D.s) * (11 + 2 + (1 + ((2 * D.bB + 1) * (310 * D.bP + 201 + 1 + 2) + 2)) +
      1 + 2) + 2))

/-- The word-size conditions of the folded-row program. -/
structure BandFoldW (D : PreAxB) : Prop where
  ws : 2 * D.bWd + 1 < D.s
  p13 : 13 ≤ D.bP
  off : TblOffW D.W D.bP D.α D.s D.t D.bWd ((D.s + D.t) * (D.bWd + 1))
  w5 : 5 * D.bP + 16 ≤ D.W
  sW : 2 * D.s * (D.t + 1) < 2 ^ D.W
  ss : D.s * D.s < 2 ^ D.W
  αW : D.α * D.α < 2 ^ D.W
  PW : 2 ^ D.bP < 2 ^ D.W
  NW : (D.bB + 1 + D.s) + 2 * D.bB + 1 < 2 ^ D.W
  tW : D.t < 2 ^ D.W
  wdW : D.bWd < 2 ^ D.W

variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

/-- **The folded rows onto `src`.** -/
theorem band_preFold (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hι : Function.Injective ι)
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (D : PreAxB) [NeZero D.s] (w : ℕ) (hwW : w ≤ D.W) (hW : BandFoldW D)
    (hpn : σ (.inl (.cm .pn)) = List.replicate D.bP tick)
    (hsn : σ (.inl .sn) = List.replicate D.s tick) (hya : σ (.inl .ya) = List.replicate D.t tick)
    (hhc : σ (.inl .hc) = List.replicate D.α tick) (htA : σ (.inl .tA) = List.replicate D.bWd tick)
    (hxs : σ (.inl .xs) = List.replicate (D.bB + 1 + D.s) tick)
    (htL : σ (.inl .tL) = List.replicate (2 * D.bB + 1) tick)
    (htJ : σ (.inl .tJ) = List.replicate D.bB tick) (hhv : σ (.inl .hv) = List.replicate D.W tick)
    (hwn : (σ (.inl (.cm .wn))).length = w) (hvx : ∀ j, σ (.inr (.vx j)) = []) :
    RsbRuns body (Sum.elim rg rgx) ι (bandPreFold rg rgx ι) σ
      (Function.update σ (.inl .src)
        (tblFoldStream (prime + K) w D.s D.t D.α D.bP D.bWd D.bB (D.bB + 1 + D.s) ++ σ (.inl .src)))
      (preVMCost 60 D.W w [D.bP, D.s, D.t, D.α, D.bWd, D.bB + 1 + D.s, 2 * D.bB + 1, D.bB]
        (bandKFold D) ((D.bB + 1 + D.s) * (2 * D.bB + 1) * w)) := by
  have htg := bandLay_inj hrg₂ hι hdisj₂
  set ρ : RsbR → List (Fin (prime + K + 4)) := fun r => σ (.inl r) with hρ
  have hv : preLoadVal (Sum.elim ρ fun _ => ([] : List (Fin (prime + K + 4)))) bandFoldLs
      (fun _ : Fin 60 => 0) = Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (fun _ : Fin 60 => 0)
        19 D.bP) 34 D.s) 35 D.t) 36 D.α) 39 D.bWd) 49 (D.bB + 1 + D.s)) 51 (2 * D.bB + 1))
        52 D.bB := by
    simp [preLoadVal, bandFoldLs, hρ, hpn, hsn, hya, hhc, htA, hxs, htL, htJ]
  have hst : ∀ j, preLoadVal (Sum.elim ρ fun _ => ([] : List (Fin (prime + K + 4)))) bandFoldLs
      (fun _ => 0) j < 2 ^ D.W := by
    intro j
    rw [hv]
    have hP := hW.PW
    have hPl : D.bP < 2 ^ D.W := lt_trans (Nat.lt_two_pow_self) hP
    have hsl : D.s < 2 ^ D.W := by nlinarith [hW.ss, NeZero.ne D.s, Nat.pos_of_ne_zero (NeZero.ne D.s)]
    have hαl : D.α < 2 ^ D.W := by
      rcases Nat.eq_zero_or_pos D.α with h0 | h0
      · rw [h0]; exact Nat.two_pow_pos _
      · nlinarith [hW.αW]
    have hNl := hW.NW
    simp only [Function.update_apply]
    split_ifs <;> first | exact Nat.two_pow_pos _ | omega | exact hW.tW | exact hW.wdW
  have h := preVM_runs (body := body) htg .hv (.cm .wn) bandFoldLs tblFoldStreamCode .src
    (Sum.elim ρ fun _ => []) (fun _ => rfl) (by simp [hρ, hhv]) (by simp [hρ, hwn]) hwW hst
    (tblFoldStream_do (A := prime + K) (W := D.W) (w := w) ⟨_, []⟩ (s := D.s) (t := D.t)
      (α := D.α) (P := D.bP) (wd := D.bWd) (B := D.bB) (NR := D.bB + 1 + D.s)
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true }))
      hW.ws hW.p13 hW.off hW.w5 hW.sW hW.ss hW.αW hW.PW (by have := hW.NW; omega))
    (tblFoldStream (prime + K) w D.s D.t D.α D.bP D.bWd D.bB (D.bB + 1 + D.s))
    (fun s' hs' => by simp only at hs'; rw [hs', List.append_nil, List.reverse_reverse])
  rw [length_tblFoldStream, Sum.update_elim_inl] at h
  have h2 := band_toRuns hrg₂ hdisj₂ h (fun x => σ (.inr x)) hvx
  convert h2 using 1
  · rfl
  · funext r; rcases r with r | x <;> rfl
  · funext r; rcases r with r | x
    · by_cases hr : r = .src
      · subst hr; simp only [Function.update_self, Sum.elim_inl, hρ]
      · simp only [Function.update_apply, hr, Sum.elim_inl, hρ, ite_false, Sum.inl.injEq]
    · simp only [Function.update_apply, Sum.elim_inr, reduceCtorEq, ite_false]
  · simp only [bandFoldLs, List.map_cons, List.map_nil, Sum.elim_inl, hρ, hpn, hsn, hya, hhc, htA,
      hxs, htL, htJ, List.length_replicate, bandKFold]

end StepFold

/-! ### Step 2c: the factor-phase counters -/

section StepF2

variable (g : RsbR ⊕ RsbX t₀ → Fin T)

/-- `ms = B`, `m2n = 2B`, `dst = B - 1` (`xs` cleared). -/
def bandPreF2a : Pr F T Q (prime + K) U :=
  .seq (uclear (g (.inl .xs)))
  (.seq (ucopy (g (.inl .tJ)) (g (.inl .ms)) (g (.inl .ac2)))
  (.seq (umul 2 (g (.inl .tJ)) (g (.inl .m2n)) (g (.inl .ac2)))
    (umul 2 (g (.inl .tA)) (g (.inl .dst)) (g (.inl .ac2)))))

/-- `m2wn = (B - 1) w`, `mwn = 2B w`, `smwn = (2B + 1) w`. -/
def bandPreF2b : Pr F T Q (prime + K) U :=
  .seq (preUMul (g (.inl .dst)) (g (.inl (.cm .wn))) (g (.inl .m2wn)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (preUMul (g (.inl .m2n)) (g (.inl (.cm .wn))) (g (.inl .mwn)) (g (.inl .ac2)) (g (.inl .nv)))
    (preUMul (g (.inl .tL)) (g (.inl (.cm .wn))) (g (.inl .smwn)) (g (.inl .ac2)) (g (.inl .nv))))

/-- `tswn = (B + 1)(2B + 1) w`. -/
def bandPreF2c : Pr F T Q (prime + K) U :=
  .seq (ucopy (g (.inl .tJ)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (.act (.push (.rt (g (.inl .tC))) (fun _ => tick) .done))
  (.seq (preUMul (g (.inl .tC)) (g (.inl .tL)) (g (.inl .tK)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (preUMul (g (.inl .tK)) (g (.inl (.cm .wn))) (g (.inl .tswn)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (uclear (g (.inl .tC))) (uclear (g (.inl .tK)))))))

/-- `xs = α²`, `kn = 4α²`, `msk` the zero record. -/
def bandPreF2d : Pr F T Q (prime + K) U :=
  .seq (ucopy (g (.inl .hc)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (preUMul (g (.inl .hc)) (g (.inl .tC)) (g (.inl .xs)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (uclear (g (.inl .tC)))
  (.seq (umul 4 (g (.inl .xs)) (g (.inl .kn)) (g (.inl .ac2)))
    (umulSym 1 (pairSym (prime + K) false false) (g (.inl (.cm .wn))) (g (.inl .msk))
      (g (.inl .tC))))))

/-- Step 2c. -/
def bandPreF2 : Pr F T Q (prime + K) U :=
  .seq (bandPreF2a g) (.seq (bandPreF2b g) (.seq (bandPreF2c g) (bandPreF2d g)))

variable {A : ℕ}

/-- After step 2c, part a. -/
def bandFF2a (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (D : PreAxB) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update σ
    (.inl .xs) [])
    (.inl .ms) (List.replicate D.bB tick))
    (.inl .m2n) (List.replicate (2 * D.bB) tick))
    (.inl .dst) (List.replicate (2 * D.bWd) tick)

/-- After step 2c, part b. -/
def bandFF2b (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (D : PreAxB) (w : ℕ) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update σ
    (.inl .m2wn) (List.replicate (2 * D.bWd * w) tick))
    (.inl .mwn) (List.replicate (2 * D.bB * w) tick))
    (.inl .smwn) (List.replicate ((2 * D.bB + 1) * w) tick)

/-- After step 2c, part c. -/
def bandFF2c (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (D : PreAxB) (w : ℕ) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Function.update σ (.inl .tswn) (List.replicate ((D.bB + 1) * (2 * D.bB + 1) * w) tick)

/-- After step 2c, part d. -/
def bandFF2d (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (D : PreAxB) (w : ℕ) (z : Fin (A + 4)) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update σ
    (.inl .xs) (List.replicate (D.α * D.α) tick))
    (.inl .kn) (List.replicate (4 * (D.α * D.α)) tick))
    (.inl .msk) (List.replicate w z)

/-- The register file after step 2c. -/
def bandFF2 (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (D : PreAxB) (w : ℕ) (z : Fin (A + 4)) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  bandFF2d (bandFF2c (bandFF2b (bandFF2a σ D) D w) D w) D w z

def bandCostF2a (D : PreAxB) : ℕ :=
  (2 * (D.bB + 1 + D.s) + 2) + ((4 * D.bB + 4) + ((4 * D.bB + 4) + (4 * D.bWd + 4)))

def bandCostF2b (D : PreAxB) (w : ℕ) : ℕ :=
  (2 * D.bWd * (4 * w + 7) + 2 * (2 * D.bWd) + 4) + ((2 * D.bB * (4 * w + 7) + 2 * (2 * D.bB) + 4) +
    ((2 * D.bB + 1) * (4 * w + 7) + 2 * (2 * D.bB + 1) + 4))

def bandCostF2c (D : PreAxB) (w : ℕ) : ℕ :=
  (4 * D.bB + 4) + (1 + (((D.bB + 1) * (4 * (2 * D.bB + 1) + 7) + 2 * (D.bB + 1) + 4) +
    (((D.bB + 1) * (2 * D.bB + 1) * (4 * w + 7) + 2 * ((D.bB + 1) * (2 * D.bB + 1)) + 4) +
    ((2 * (D.bB + 1) + 2) + (2 * ((D.bB + 1) * (2 * D.bB + 1)) + 2)))))

def bandCostF2d (D : PreAxB) (w : ℕ) : ℕ :=
  (4 * D.α + 4) + ((D.α * (4 * D.α + 7) + 2 * D.α + 4) + ((2 * D.α + 2) +
    ((4 * (D.α * D.α) + 4) + (4 * w + 4))))

def bandCostF2 (D : PreAxB) (w : ℕ) : ℕ :=
  bandCostF2a D + (bandCostF2b D w + (bandCostF2c D w + bandCostF2d D w))

variable {body : F → Pr F T Q (prime + K) U} {g : RsbR ⊕ RsbX t₀ → Fin T} {ι : Fin 64 → Fin T}

set_option maxRecDepth 4000 in
theorem band_preF2a (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (hxs : σ (.inl .xs) = List.replicate (D.bB + 1 + D.s) tick)
    (htA : σ (.inl .tA) = List.replicate D.bWd tick) (htJ : σ (.inl .tJ) = List.replicate D.bB tick)
    (hms : σ (.inl .ms) = []) (hm2n : σ (.inl .m2n) = []) (hdst : σ (.inl .dst) = [])
    (hac2 : σ (.inl .ac2) = []) :
    TwRuns body (preLay g ι) (bandPreF2a g) (preStB σ) (preStB (bandFF2a σ D)) (bandCostF2a D) := by
  have htg := preLay_inj hg hι hdisj
  refine twRuns_congr (twRuns_mono
    (twRuns_seq (twRuns_uclear (body := body) htg (.inl (.inl .xs)) (preStB σ))
    (twRuns_seq (twRuns_ucopy (body := body) htg (a := .inl (.inl .tJ)) (b := .inl (.inl .ms))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (twRuns_umul (body := body) htg 2 (a := .inl (.inl .tJ)) (b := .inl (.inl .m2n))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
      (twRuns_umul (body := body) htg 2 (a := .inl (.inl .tA)) (b := .inl (.inl .dst))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)))) ?_) ?_
  all_goals try (simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq,
    reduceCtorEq, ite_false, hac2]; done)
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      hxs, htA, htJ, List.length_replicate]
    unfold bandCostF2a; omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, bandFF2a, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [htA, htJ, hms, hm2n, hdst]
    · simp only [Function.update_apply, preStB, bandFF2a, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

set_option maxRecDepth 4000 in
theorem band_preF2b (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (w : ℕ) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hdst : σ (.inl .dst) = List.replicate (2 * D.bWd) tick)
    (hm2n : σ (.inl .m2n) = List.replicate (2 * D.bB) tick)
    (htL : σ (.inl .tL) = List.replicate (2 * D.bB + 1) tick)
    (hm2wn : σ (.inl .m2wn) = []) (hmwn : σ (.inl .mwn) = []) (hsmwn : σ (.inl .smwn) = [])
    (hac2 : σ (.inl .ac2) = []) (hnv : σ (.inl .nv) = []) :
    TwRuns body (preLay g ι) (bandPreF2b g) (preStB σ) (preStB (bandFF2b σ D w))
      (bandCostF2b D w) := by
  have htg := preLay_inj hg hι hdisj
  refine twRuns_congr (twRuns_mono
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl (.inl .dst))
      (b := .inl (.inl (.cm .wn))) (c := .inl (.inl .m2wn)) (t₁ := .inl (.inl .ac2))
      (t₂ := .inl (.inl .nv)) (by simp) (preStB σ) ?_ ?_)
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl (.inl .m2n))
      (b := .inl (.inl (.cm .wn))) (c := .inl (.inl .mwn)) (t₁ := .inl (.inl .ac2))
      (t₂ := .inl (.inl .nv)) (by simp) _ ?_ ?_)
      (preUMul_runs (body := body) htg (a := .inl (.inl .tL))
      (b := .inl (.inl (.cm .wn))) (c := .inl (.inl .smwn)) (t₁ := .inl (.inl .ac2))
      (t₂ := .inl (.inl .nv)) (by simp) _ ?_ ?_))) ?_) ?_
  all_goals try (simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq,
    reduceCtorEq, ite_false, hac2, hnv]; done)
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      hwn, hdst, hm2n, htL, List.length_replicate]
    unfold bandCostF2b; omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, bandFF2b, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [hwn, hdst, hm2n, htL, hm2wn, hmwn, hsmwn]
    · simp only [Function.update_apply, preStB, bandFF2b, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

set_option maxRecDepth 4000 in
theorem band_preF2c (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (w : ℕ) (hwn : (σ (.inl (.cm .wn))).length = w)
    (htJ : σ (.inl .tJ) = List.replicate D.bB tick)
    (htL : σ (.inl .tL) = List.replicate (2 * D.bB + 1) tick)
    (htswn : σ (.inl .tswn) = []) (htC : σ (.inl .tC) = []) (htK : σ (.inl .tK) = [])
    (hac2 : σ (.inl .ac2) = []) (hnv : σ (.inl .nv) = []) :
    TwRuns body (preLay g ι) (bandPreF2c g) (preStB σ) (preStB (bandFF2c σ D w))
      (bandCostF2c D w) := by
  have htg := preLay_inj hg hι hdisj
  refine twRuns_congr (twRuns_mono
    (twRuns_seq (twRuns_ucopy (body := body) htg (a := .inl (.inl .tJ)) (b := .inl (.inl .tC))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) (preStB σ) ?_)
    (twRuns_seq (twRuns_push (body := body) htg (.inl (.inl .tC)) tick _)
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl (.inl .tC))
      (b := .inl (.inl .tL)) (c := .inl (.inl .tK)) (t₁ := .inl (.inl .ac2))
      (t₂ := .inl (.inl .nv)) (by simp) _ ?_ ?_)
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl (.inl .tK))
      (b := .inl (.inl (.cm .wn))) (c := .inl (.inl .tswn)) (t₁ := .inl (.inl .ac2))
      (t₂ := .inl (.inl .nv)) (by simp) _ ?_ ?_)
    (twRuns_seq (twRuns_uclear (body := body) htg (.inl (.inl .tC)) _)
      (twRuns_uclear (body := body) htg (.inl (.inl .tK)) _)))))) ?_) ?_
  all_goals try (simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq,
    reduceCtorEq, ite_false, ite_true, hac2, hnv]; done)
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, hwn, htJ, htL, htC, htK, List.length_replicate, List.length_cons,
      List.append_nil]
    unfold bandCostF2c; ring_nf; omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, bandFF2c, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [hwn, htJ, htL, htswn, htC, htK]
    · simp only [Function.update_apply, preStB, bandFF2c, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

set_option maxRecDepth 4000 in
theorem band_preF2d (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (w : ℕ) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hhc : σ (.inl .hc) = List.replicate D.α tick) (hxs : σ (.inl .xs) = [])
    (hkn : σ (.inl .kn) = []) (hmsk : σ (.inl .msk) = []) (htC : σ (.inl .tC) = [])
    (hac2 : σ (.inl .ac2) = []) (hnv : σ (.inl .nv) = []) :
    TwRuns body (preLay g ι) (bandPreF2d g) (preStB σ)
      (preStB (bandFF2d σ D w (pairSym (prime + K) false false))) (bandCostF2d D w) := by
  have htg := preLay_inj hg hι hdisj
  refine twRuns_congr (twRuns_mono
    (twRuns_seq (twRuns_ucopy (body := body) htg (a := .inl (.inl .hc)) (b := .inl (.inl .tC))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) (preStB σ) ?_)
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl (.inl .hc))
      (b := .inl (.inl .tC)) (c := .inl (.inl .xs)) (t₁ := .inl (.inl .ac2))
      (t₂ := .inl (.inl .nv)) (by simp) _ ?_ ?_)
    (twRuns_seq (twRuns_uclear (body := body) htg (.inl (.inl .tC)) _)
    (twRuns_seq (twRuns_umul (body := body) htg 4 (a := .inl (.inl .xs)) (b := .inl (.inl .kn))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
      (twRuns_umulSym htg 1 (pairSym (prime + K) false false) (a := .inl (.inl (.cm .wn)))
        (b := .inl (.inl .msk)) (t := .inl (.inl .tC)) (by simp) (by simp) (by simp) _ ?_))))) ?_) ?_
  all_goals try (simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq,
    reduceCtorEq, ite_false, ite_true, hac2, hnv]; done)
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, hwn, hhc, hxs, htC, List.length_replicate, List.append_nil]
    unfold bandCostF2d; omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, bandFF2d, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [hwn, hhc, hxs, hkn, hmsk, htC]
    · simp only [Function.update_apply, preStB, bandFF2d, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

theorem band_preF2 (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (w : ℕ) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hxs : σ (.inl .xs) = List.replicate (D.bB + 1 + D.s) tick)
    (htA : σ (.inl .tA) = List.replicate D.bWd tick) (htJ : σ (.inl .tJ) = List.replicate D.bB tick)
    (htL : σ (.inl .tL) = List.replicate (2 * D.bB + 1) tick)
    (hhc : σ (.inl .hc) = List.replicate D.α tick)
    (hms : σ (.inl .ms) = []) (hm2n : σ (.inl .m2n) = []) (hdst : σ (.inl .dst) = [])
    (hm2wn : σ (.inl .m2wn) = []) (hmwn : σ (.inl .mwn) = []) (hsmwn : σ (.inl .smwn) = [])
    (htswn : σ (.inl .tswn) = []) (hkn : σ (.inl .kn) = []) (hmsk : σ (.inl .msk) = [])
    (htC : σ (.inl .tC) = []) (htK : σ (.inl .tK) = []) (hac2 : σ (.inl .ac2) = [])
    (hnv : σ (.inl .nv) = []) :
    TwRuns body (preLay g ι) (bandPreF2 g) (preStB σ)
      (preStB (bandFF2 σ D w (pairSym (prime + K) false false))) (bandCostF2 D w) := by
  have h1 := band_preF2a (body := body) hg hι hdisj σ D hxs htA htJ hms hm2n hdst hac2
  have h2 := band_preF2b (body := body) hg hι hdisj (bandFF2a σ D) D w
    (by simp [bandFF2a, hwn]) (by simp [bandFF2a]) (by simp [bandFF2a]) (by simp [bandFF2a, htL])
    (by simp [bandFF2a, hm2wn]) (by simp [bandFF2a, hmwn]) (by simp [bandFF2a, hsmwn])
    (by simp [bandFF2a, hac2]) (by simp [bandFF2a, hnv])
  have h3 := band_preF2c (body := body) hg hι hdisj (bandFF2b (bandFF2a σ D) D w) D w
    (by simp [bandFF2b, bandFF2a, hwn]) (by simp [bandFF2b, bandFF2a, htJ])
    (by simp [bandFF2b, bandFF2a, htL]) (by simp [bandFF2b, bandFF2a, htswn])
    (by simp [bandFF2b, bandFF2a, htC]) (by simp [bandFF2b, bandFF2a, htK])
    (by simp [bandFF2b, bandFF2a, hac2]) (by simp [bandFF2b, bandFF2a, hnv])
  have h4 := band_preF2d (body := body) hg hι hdisj (bandFF2c (bandFF2b (bandFF2a σ D) D w) D w) D w
    (by simp [bandFF2c, bandFF2b, bandFF2a, hwn]) (by simp [bandFF2c, bandFF2b, bandFF2a, hhc])
    (by simp [bandFF2c, bandFF2b, bandFF2a]) (by simp [bandFF2c, bandFF2b, bandFF2a, hkn])
    (by simp [bandFF2c, bandFF2b, bandFF2a, hmsk]) (by simp [bandFF2c, bandFF2b, bandFF2a, htC])
    (by simp [bandFF2c, bandFF2b, bandFF2a, hac2]) (by simp [bandFF2c, bandFF2b, bandFF2a, hnv])
  exact twRuns_seq h1 (twRuns_seq h2 (twRuns_seq h3 h4))

end StepF2


/-! ### Constants by the table machine -/

section Const

variable {A : ℕ}

/-- The atom bound of `preHfCode` at exponent `v - 1`. -/
def bandKH (v : ℕ) : ℕ := 3 + ((4 * (v - 1) + 5) + 2)

variable {body : F → Pr F T Q (prime + K) U} {g : RsbR ⊕ RsbX t₀ → Fin T} {ι : Fin 64 → Fin T}

/-- **A power of two as a coefficient.** With `v` ticks on `e`, `o` receives `2^(v-1)`. -/
theorem band_vmH (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (e o : RsbR ⊕ RsbX t₀) (W v w : ℕ) (he : σ e = List.replicate v tick)
    (hhv : σ (.inl .hv) = List.replicate W tick) (hwn : (σ (.inl (.cm .wn))).length = w)
    (ho : σ o = []) (hv1 : 1 ≤ v) (hvW : v < W) (hwW : w ≤ W) :
    TwRuns body (preLay g ι) (preVM (preLay g ι) (.inl .hv) (.inl (.cm .wn)) [(e, 19)] preHfCode o)
      (preStB σ) (preStB (Function.update σ o (tblPairs (prime + K) w (2 ^ (v - 1)) 0)))
      (preVMCost 48 W w [v] (bandKH v) w) := by
  have htg := preLay_inj hg hι hdisj
  have hp2 : v < 2 ^ W := lt_trans hvW Nat.lt_two_pow_self
  have hv : preLoadVal (preStB σ) [(e, 19)] (fun _ : Fin 48 => 0) =
      Function.update (fun _ : Fin 48 => 0) 19 v := by
    simp [preLoadVal, preStB, he]
  have h := preVM_runs (body := body) htg (.inl .hv) (.inl (.cm .wn)) [(e, 19)]
    preHfCode o (preStB σ) (fun _ => rfl) (by simp [preStB, hhv])
    (by simp [preStB, hwn]) hwW
    (fun j => by
      rw [hv]
      simp only [Function.update_apply]
      split_ifs <;> first | assumption | exact Nat.two_pow_pos _)
    (preHfCode_do (A := prime + K) (W := W) (w := w) ⟨_, []⟩ (p := v)
      (by rw [hv]; simp) hv1 hvW rfl)
    (tblPairs (prime + K) w (2 ^ (v - 1)) 0) (fun s' hs' => by
      rw [hs', List.reverse_reverse])
  rw [preStB_upd, preStB_inl, ho, List.append_nil] at h
  refine twRuns_mono h (le_of_eq ?_)
  simp [preStB, he, bandKH, tblPairs, coeffSyms]

end Const

/-! ### Step 2d: the Newton start on `bx` -/

section StepF3

variable (g : RsbR ⊕ RsbX t₀ → Fin T) (ι : Fin 64 → Fin T)

/-- `bx = 2^(5p - 2)`, the Newton start `2^(P-2)`. -/
def bandPreF3 : Pr F T Q (prime + K) U :=
  .seq (umul 5 (g (.inl .ac)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (.act (.push (.rt (g (.inl .tK))) (fun _ => tick) .done))
  (.seq (usub (g (.inl .tK)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (preVM (preLay g ι) (.inl .hv) (.inl (.cm .wn)) [(.inl .tC, 19)] preHfCode (.inl .bx))
  (.seq (uclear (g (.inl .tC))) (uclear (g (.inl .tK)))))))

variable {A : ℕ}

def bandCostF3 (D : PreAxB) (w : ℕ) : ℕ :=
  (4 * D.p + 4) + (1 + ((4 * 1 + 4) + (preVMCost 48 D.W w [5 * D.p - 1] (bandKH (5 * D.p - 1)) w +
    ((2 * (5 * D.p - 1) + 2) + (2 * 1 + 2)))))

variable {body : F → Pr F T Q (prime + K) U} {g : RsbR ⊕ RsbX t₀ → Fin T} {ι : Fin 64 → Fin T}

set_option maxRecDepth 4000 in
theorem band_preF3 (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (w : ℕ) (hwn : (σ (.inl (.cm .wn))).length = w) (hwW : w ≤ D.W) (hp1 : 1 ≤ D.p)
    (hpW : 5 * D.p < D.W)
    (hac : σ (.inl .ac) = List.replicate D.p tick) (hhv : σ (.inl .hv) = List.replicate D.W tick)
    (hbx : σ (.inl .bx) = []) (htC : σ (.inl .tC) = []) (htK : σ (.inl .tK) = [])
    (hac2 : σ (.inl .ac2) = []) :
    TwRuns body (preLay g ι) (bandPreF3 g ι) (preStB σ)
      (preStB (Function.update σ (.inl .bx) (tblPairs (prime + K) w (2 ^ (5 * D.p - 2)) 0)))
      (bandCostF3 D w) := by
  have htg := preLay_inj hg hι hdisj
  set σ1 := Function.update (Function.update (Function.update σ (.inl .tC)
    (List.replicate (5 * D.p - 1) tick)) (.inl .tK) [tick]) (.inl .ac2) [] with hσ1
  have h2 := band_vmH (body := body) hg hι hdisj σ1 (.inl .tC) (.inl .bx) D.W (5 * D.p - 1) w
    (by simp [hσ1]) (by simp [hσ1, hhv]) (by simp [hσ1, hwn]) (by simp [hσ1, hbx]) (by omega)
    (by omega) hwW
  have h3 := twRuns_seq (twRuns_uclear (body := body) htg (.inl (.inl .tC))
      (preStB (Function.update σ1 (.inl .bx) (tblPairs (prime + K) w (2 ^ (5 * D.p - 1 - 1)) 0))))
    (twRuns_uclear (body := body) htg (.inl (.inl .tK)) _)
  refine twRuns_congr (twRuns_mono (twRuns_seq (twRuns_umul (body := body) htg 5
      (a := .inl (.inl .ac)) (b := .inl (.inl .tC)) (t := .inl (.inl .ac2)) (by simp) (by simp)
      (by simp) (preStB σ) ?_)
    (twRuns_seq (twRuns_push (body := body) htg (.inl (.inl .tK)) tick _)
    (twRuns_seq (twRuns_congr (twRuns_usub (body := body) htg (a := .inl (.inl .tK))
      (b := .inl (.inl .tC)) (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_) ?_)
      (twRuns_seq h2 h3)))) ?_) ?_
  · simp only [preStB, Sum.elim_inl, hac2]
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      hac2]
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [hac, htC, htK, hac2, List.drop_replicate]
    · simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, hσ1, hac, htC, htK, List.length_replicate, List.length_cons, List.length_nil,
      List.append_nil]
    unfold bandCostF3; omega
  · rw [show 5 * D.p - 1 - 1 = 5 * D.p - 2 by omega]
    funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [htC, htK, hac2]
    · simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

end StepF3

/-! ### Step 3: the line-phase values -/

section StepL

variable (g : RsbR ⊕ RsbX t₀ → Fin T) (ι : Fin 64 → Fin T)

/-- The spare register `vx j` of the stage. -/
abbrev bvx (j : Fin 12) : RsbR ⊕ RsbX t₀ := .inr (.vx j)

/-- `padc = (t - s) w`. -/
def bandPreL1 : Pr F T Q (prime + K) U :=
  .seq (ucopy (g (.inl .ya)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (usub (g (.inl .sn)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (preUMul (g (.inl .tC)) (g (.inl (.cm .wn))) (g (.inl .padc)) (g (.inl .ac2)) (g (.inl .nv)))
    (uclear (g (.inl .tC)))))

/-- `vx 1 = 2^(9p - 1)`, the input constant `2^(2P - p - 1)`. -/
def bandPreL3 : Pr F T Q (prime + K) U :=
  .seq (umul 9 (g (.inl .ac)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (preVM (preLay g ι) (.inl .hv) (.inl (.cm .wn)) [(.inl .tC, 19)] preHfCode (bvx 1))
    (uclear (g (.inl .tC))))

/-- `vx 2 = 2^(p - α²)`, the output constant `2^(p - j)` (`xs` holds `α²`). -/
def bandPreL4 : Pr F T Q (prime + K) U :=
  .seq (ucopy (g (.inl .ac)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (.act (.push (.rt (g (.inl .tC))) (fun _ => tick) .done))
  (.seq (usub (g (.inl .xs)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (preVM (preLay g ι) (.inl .hv) (.inl (.cm .wn)) [(.inl .tC, 19)] preHfCode (bvx 2))
    (uclear (g (.inl .tC))))))

/-- `tb = 2^(9p)`, the scale `2^(2P - p)` of the diagonal table. -/
def bandPreL9 : Pr F T Q (prime + K) U :=
  .seq (umul 9 (g (.inl .ac)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (.act (.push (.rt (g (.inl .tC))) (fun _ => tick) .done))
  (.seq (preVM (preLay g ι) (.inl .hv) (.inl (.cm .wn)) [(.inl .tC, 19)] preHfCode (.inl .tb))
    (uclear (g (.inl .tC)))))

variable {A : ℕ}

variable {body : F → Pr F T Q (prime + K) U} {g : RsbR ⊕ RsbX t₀ → Fin T} {ι : Fin 64 → Fin T}

set_option maxRecDepth 4000 in
theorem band_preL1 (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (w : ℕ) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hya : σ (.inl .ya) = List.replicate D.t tick) (hsn : σ (.inl .sn) = List.replicate D.s tick)
    (hpadc : σ (.inl .padc) = []) (htC : σ (.inl .tC) = []) (hac2 : σ (.inl .ac2) = [])
    (hnv : σ (.inl .nv) = []) :
    TwRuns body (preLay g ι) (bandPreL1 g) (preStB σ)
      (preStB (Function.update σ (.inl .padc) (List.replicate ((D.t - D.s) * w) tick)))
      ((4 * D.t + 4) + ((4 * D.s + 4) + (((D.t - D.s) * (4 * w + 7) + 2 * (D.t - D.s) + 4) +
        (2 * (D.t - D.s) + 2)))) := by
  have htg := preLay_inj hg hι hdisj
  refine twRuns_congr (twRuns_mono
    (twRuns_seq (twRuns_ucopy (body := body) htg (a := .inl (.inl .ya)) (b := .inl (.inl .tC))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) (preStB σ) ?_)
    (twRuns_seq (twRuns_usub (body := body) htg (a := .inl (.inl .sn)) (b := .inl (.inl .tC))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl (.inl .tC))
      (b := .inl (.inl (.cm .wn))) (c := .inl (.inl .padc)) (t₁ := .inl (.inl .ac2))
      (t₂ := .inl (.inl .nv)) (by simp) _ ?_ ?_)
      (twRuns_uclear (body := body) htg (.inl (.inl .tC)) _)))) ?_) ?_
  all_goals try (simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq,
    reduceCtorEq, ite_false, ite_true, hac2, hnv]; done)
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, hwn, hya, hsn, htC, List.length_replicate, List.append_nil,
      List.drop_replicate]
    omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [hwn, hya, hsn, hpadc, htC, List.drop_replicate]
    · simp only [Function.update_apply, preStB, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

set_option maxRecDepth 4000 in
theorem band_preL3 (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (w : ℕ) (hwn : (σ (.inl (.cm .wn))).length = w) (hwW : w ≤ D.W) (hp1 : 1 ≤ D.p)
    (hpW : 9 * D.p < D.W)
    (hac : σ (.inl .ac) = List.replicate D.p tick) (hhv : σ (.inl .hv) = List.replicate D.W tick)
    (ho : σ (bvx 1) = []) (htC : σ (.inl .tC) = []) (hac2 : σ (.inl .ac2) = []) :
    TwRuns body (preLay g ι) (bandPreL3 g ι) (preStB σ)
      (preStB (Function.update σ (bvx 1) (tblPairs (prime + K) w (2 ^ (9 * D.p - 1)) 0)))
      ((4 * D.p + 4) + (preVMCost 48 D.W w [9 * D.p] (bandKH (9 * D.p)) w + (2 * (9 * D.p) + 2))) := by
  have htg := preLay_inj hg hι hdisj
  set σ1 := Function.update σ (.inl .tC) (List.replicate (9 * D.p) tick) with hσ1
  have h2 := band_vmH (body := body) hg hι hdisj σ1 (.inl .tC) (bvx 1) D.W (9 * D.p) w
    (by simp [hσ1]) (by simp [hσ1, hhv]) (by simp [hσ1, hwn]) (by simp [hσ1, ho]) (by omega)
    hpW hwW
  refine twRuns_congr (twRuns_mono (twRuns_seq (twRuns_congr (twRuns_umul (body := body) htg 9
      (a := .inl (.inl .ac)) (b := .inl (.inl .tC)) (t := .inl (.inl .ac2)) (by simp) (by simp)
      (by simp) (preStB σ) ?_) ?_)
    (twRuns_seq h2 (twRuns_uclear (body := body) htg (.inl (.inl .tC)) _))) ?_) ?_
  · simp only [preStB, Sum.elim_inl, hac2]
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [hac, htC]
    · simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]
  · simp only [preStB, Function.update_apply, Sum.elim_inl, reduceCtorEq, ite_false,
      ite_true, hσ1, hac, List.length_replicate]
    omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [htC]
    · simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

set_option maxRecDepth 4000 in
theorem band_preL4 (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (w : ℕ) (hwn : (σ (.inl (.cm .wn))).length = w) (hwW : w ≤ D.W) (hjp : D.α * D.α ≤ D.p)
    (hpW : D.p + 1 < D.W)
    (hac : σ (.inl .ac) = List.replicate D.p tick) (hhv : σ (.inl .hv) = List.replicate D.W tick)
    (hxs : σ (.inl .xs) = List.replicate (D.α * D.α) tick)
    (ho : σ (bvx 2) = []) (htC : σ (.inl .tC) = []) (hac2 : σ (.inl .ac2) = []) :
    TwRuns body (preLay g ι) (bandPreL4 g ι) (preStB σ)
      (preStB (Function.update σ (bvx 2) (tblPairs (prime + K) w (2 ^ (D.p - D.α * D.α)) 0)))
      ((4 * D.p + 4) + (1 + ((4 * (D.α * D.α) + 4) + (preVMCost 48 D.W w [D.p + 1 - D.α * D.α]
        (bandKH (D.p + 1 - D.α * D.α)) w + (2 * (D.p + 1 - D.α * D.α) + 2))))) := by
  have htg := preLay_inj hg hι hdisj
  set σ1 := Function.update σ (.inl .tC) (List.replicate (D.p + 1 - D.α * D.α) tick) with hσ1
  have h2 := band_vmH (body := body) hg hι hdisj σ1 (.inl .tC) (bvx 2) D.W (D.p + 1 - D.α * D.α) w
    (by simp [hσ1]) (by simp [hσ1, hhv]) (by simp [hσ1, hwn]) (by simp [hσ1, ho]) (by omega)
    (by omega) hwW
  rw [show D.p + 1 - D.α * D.α - 1 = D.p - D.α * D.α by omega] at h2
  refine twRuns_congr (twRuns_mono (twRuns_seq (twRuns_ucopy (body := body) htg
      (a := .inl (.inl .ac)) (b := .inl (.inl .tC)) (t := .inl (.inl .ac2)) (by simp) (by simp)
      (by simp) (preStB σ) ?_)
    (twRuns_seq (twRuns_push (body := body) htg (.inl (.inl .tC)) tick _)
    (twRuns_seq (twRuns_congr (twRuns_usub (body := body) htg (a := .inl (.inl .xs))
      (b := .inl (.inl .tC)) (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_) ?_)
    (twRuns_seq h2 (twRuns_uclear (body := body) htg (.inl (.inl .tC)) _))))) ?_) ?_
  · simp only [preStB, Sum.elim_inl, hac2]
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, hac2]
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [hac, hxs, htC, List.drop_replicate, rep_tick_cons]
    · simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, hσ1, hac, hxs, htC, List.length_replicate, List.append_nil]
    omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [htC]
    · simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

set_option maxRecDepth 4000 in
theorem band_preL9 (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (w : ℕ) (hwn : (σ (.inl (.cm .wn))).length = w) (hwW : w ≤ D.W)
    (hpW : 9 * D.p + 1 < D.W)
    (hac : σ (.inl .ac) = List.replicate D.p tick) (hhv : σ (.inl .hv) = List.replicate D.W tick)
    (htb : σ (.inl .tb) = []) (htC : σ (.inl .tC) = []) (hac2 : σ (.inl .ac2) = []) :
    TwRuns body (preLay g ι) (bandPreL9 g ι) (preStB σ)
      (preStB (Function.update σ (.inl .tb) (tblPairs (prime + K) w (2 ^ (9 * D.p)) 0)))
      ((4 * D.p + 4) + (1 + (preVMCost 48 D.W w [9 * D.p + 1] (bandKH (9 * D.p + 1)) w +
        (2 * (9 * D.p + 1) + 2)))) := by
  have htg := preLay_inj hg hι hdisj
  set σ1 := Function.update σ (.inl .tC) (List.replicate (9 * D.p + 1) tick) with hσ1
  have h2 := band_vmH (body := body) hg hι hdisj σ1 (.inl .tC) (.inl .tb) D.W (9 * D.p + 1) w
    (by simp [hσ1]) (by simp [hσ1, hhv]) (by simp [hσ1, hwn]) (by simp [hσ1, htb]) (by omega)
    hpW hwW
  rw [show 9 * D.p + 1 - 1 = 9 * D.p by omega] at h2
  refine twRuns_congr (twRuns_mono (twRuns_seq (twRuns_umul (body := body) htg 9
      (a := .inl (.inl .ac)) (b := .inl (.inl .tC)) (t := .inl (.inl .ac2)) (by simp) (by simp)
      (by simp) (preStB σ) ?_)
    (twRuns_seq (twRuns_congr (twRuns_push (body := body) htg (.inl (.inl .tC)) tick _) ?_)
    (twRuns_seq h2 (twRuns_uclear (body := body) htg (.inl (.inl .tC)) _)))) ?_) ?_
  · simp only [preStB, Sum.elim_inl, hac2]
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [hac, htC]
      all_goals (try (rw [List.eq_replicate_iff]; refine ⟨by simp, by simp⟩))
    · simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, hσ1, hac, List.length_replicate]
    omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [htC]
    · simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

/-- `vx 0` gets the row mask. -/
def bandPreL2g (g : RsbR ⊕ RsbX t₀ → Fin T) (ι : Fin 64 → Fin T) : Pr F T Q (prime + K) U :=
  .seq (.act (.push (.rt (g (.inl .tK))) (fun _ => tick) .done))
  (.seq (preVM (preLay g ι) (.inl .hv) (.inl .tK) [(.inl .sn, 34), (.inl .ya, 35)] preMaskCode
    (.inl .sr))
  (.seq (moveR (g (.inl .sr)) (g (.inl .sel)) preBitOf)
  (.seq (moveR (g (.inl .sel)) (g (bvx 0)) id) (uclear (g (.inl .tK))))))

/-- `vx 3 = ((s + 1) / 2) w`, `vx 4 = s / 2`, `vx 5 = (s + 1) / 2 - s / 2`. -/
def bandPreL5g (g : RsbR ⊕ RsbX t₀ → Fin T) : Pr F T Q (prime + K) U :=
  .seq (ucopy (g (.inl .sn)) (g (.inl .tC)) (g (.inl .ac2)))
  (.seq (.act (.push (.rt (g (.inl .tC))) (fun _ => tick) .done))
  (.seq (udiv 2 (g (.inl .tC)) (g (.inl .tK)) (g (.inl .ac2)))
  (.seq (preUMul (g (.inl .tK)) (g (.inl (.cm .wn))) (g (bvx 3)) (g (.inl .ac2)) (g (.inl .nv)))
  (.seq (udiv 2 (g (.inl .sn)) (g (bvx 4)) (g (.inl .ac2)))
  (.seq (usub (g (bvx 4)) (g (.inl .tK)) (g (.inl .ac2)))
  (.seq (moveR (g (.inl .tK)) (g (bvx 5)) id) (uclear (g (.inl .tC)))))))))

/-- `ef` gets the diagonal table at precision `p`. -/
def bandPreL8g (g : RsbR ⊕ RsbX t₀ → Fin T) (ι : Fin 64 → Fin T) : Pr F T Q (prime + K) U :=
  preVM (preLay g ι) (.inl .hv) (.inl (.cm .wn))
    [(.inl .sn, 34), (.inl .ya, 35), (.inl .hc, 36), (.inl .ac, 19)] tblStreamDCode (.inl .ef)

set_option maxRecDepth 4000 in
theorem band_preL2 (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (hsn : σ (.inl .sn) = List.replicate D.s tick) (hya : σ (.inl .ya) = List.replicate D.t tick)
    (hhv : σ (.inl .hv) = List.replicate D.W tick) (htK : σ (.inl .tK) = [])
    (hsr : σ (.inl .sr) = []) (hsel : σ (.inl .sel) = []) (ho : σ (bvx 0) = [])
    (hs : 0 < D.s) (hst : D.s < D.t) (hW1 : 1 ≤ D.W) (hWM : 4 * D.t * (D.s + 1) < 2 ^ D.W) :
    TwRuns body (preLay g ι) (bandPreL2g g ι) (preStB σ)
      (preStB (Function.update σ (bvx 0) ((preMaskE (prime + K) D.s D.t D.t).map preBitOf)))
      (1 + (preVMCost 48 D.W 1 [D.s, D.t] (preKM D) D.t + ((2 * D.t + 2) + ((2 * D.t + 2) +
        (2 * 1 + 2))))) := by
  have htg := preLay_inj hg hι hdisj
  have hs2 : D.s < 2 ^ D.W := by nlinarith
  have ht2 : D.t < 2 ^ D.W := by nlinarith
  set σ1 := Function.update σ (.inl .tK) [tick] with hσ1
  have hv : preLoadVal (preStB σ1) [(.inl .sn, 34), (.inl .ya, 35)] (fun _ : Fin 48 => 0) =
      Function.update (Function.update (fun _ : Fin 48 => 0) 34 D.s) 35 D.t := by
    simp [preLoadVal, preStB, hσ1, hsn, hya]
  have h := preVM_runs (body := body) htg (.inl .hv) (.inl .tK) [(.inl .sn, 34), (.inl .ya, 35)]
    preMaskCode (.inl .sr) (preStB σ1) (fun _ => rfl) (by simp [preStB, hσ1, hhv])
    (by simp [preStB, hσ1]) hW1
    (fun j => by
      rw [hv]
      simp only [Function.update_apply]
      split_ifs <;> first | assumption | exact Nat.two_pow_pos _)
    (preMaskCode_do (A := prime + K) (W := D.W) ⟨_, []⟩ (s := D.s) (t := D.t)
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true })) hs hst rfl hWM)
    (preMaskE (prime + K) D.s D.t D.t) (fun s' hs' => by
      rw [hs', List.reverse_reverse])
  rw [preStB_upd, preStB_inl] at h
  refine twRuns_congr (twRuns_mono (twRuns_seq (twRuns_congr (twRuns_push (body := body) htg
      (.inl (.inl .tK)) tick (preStB σ)) ?_)
    (twRuns_seq h
    (twRuns_seq (twRuns_moveRf (body := body) htg (a := .inl (.inl .sr)) (b := .inl (.inl .sel))
      (by simp) preBitOf _)
    (twRuns_seq (twRuns_moveR (body := body) htg (a := .inl (.inl .sel)) (b := .inl (bvx 0))
      (by simp) _)
      (twRuns_uclear (body := body) htg (.inl (.inl .tK)) _))))) ?_) ?_
  · simp only [preStB, Sum.update_elim_inl, hσ1, Sum.elim_inl, htK]
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, hσ1, hsr, hsel, hsn, hya, List.length_cons, List.length_nil, List.length_reverse,
      List.length_map, List.append_nil, length_preMaskE, List.length_replicate, List.map_cons,
      List.map_nil]
    unfold preKM; omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [hsr, hsel, htK]
    · simp only [Function.update_apply, preStB, hσ1, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false, ite_true]
      by_cases hx : x = .vx 0
      · subst hx; simp [ho, hsel, hsr]
      · simp [hx]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

set_option maxRecDepth 4000 in
theorem band_preL5 (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (w : ℕ) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hsn : σ (.inl .sn) = List.replicate D.s tick) (htC : σ (.inl .tC) = [])
    (htK : σ (.inl .tK) = []) (hac2 : σ (.inl .ac2) = []) (hnv : σ (.inl .nv) = [])
    (h3 : σ (bvx 3) = []) (h4 : σ (bvx 4) = []) (h5 : σ (bvx 5) = []) :
    TwRuns body (preLay g ι) (bandPreL5g g) (preStB σ)
      (preStB (Function.update (Function.update (Function.update σ
        (bvx 3) (List.replicate ((D.s + 1) / 2 * w) tick))
        (bvx 4) (List.replicate (D.s / 2) tick))
        (bvx 5) (List.replicate ((D.s + 1) / 2 - D.s / 2) tick)))
      ((4 * D.s + 4) + (1 + ((4 * (D.s + 1) + 4) + (((D.s + 1) / 2 * (4 * w + 7) +
        2 * ((D.s + 1) / 2) + 4) + ((4 * D.s + 4) + ((4 * (D.s / 2) + 4) +
        ((2 * ((D.s + 1) / 2 - D.s / 2) + 2) + (2 * (D.s + 1) + 2)))))))) := by
  have htg := preLay_inj hg hι hdisj
  refine twRuns_congr (twRuns_mono
    (twRuns_seq (twRuns_ucopy (body := body) htg (a := .inl (.inl .sn)) (b := .inl (.inl .tC))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) (preStB σ) ?_)
    (twRuns_seq (twRuns_push (body := body) htg (.inl (.inl .tC)) tick _)
    (twRuns_seq (twRuns_udiv htg 2 (by norm_num) (a := .inl (.inl .tC)) (b := .inl (.inl .tK))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl (.inl .tK))
      (b := .inl (.inl (.cm .wn))) (c := .inl (bvx 3)) (t₁ := .inl (.inl .ac2))
      (t₂ := .inl (.inl .nv)) (by simp) _ ?_ ?_)
    (twRuns_seq (twRuns_udiv htg 2 (by norm_num) (a := .inl (.inl .sn)) (b := .inl (bvx 4))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (twRuns_usub (body := body) htg (a := .inl (bvx 4)) (b := .inl (.inl .tK))
      (t := .inl (.inl .ac2)) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (twRuns_moveR (body := body) htg (a := .inl (.inl .tK)) (b := .inl (bvx 5))
      (by simp) _)
      (twRuns_uclear (body := body) htg (.inl (.inl .tC)) _)))))))) ?_) ?_
  all_goals try (simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq,
    reduceCtorEq, ite_false, ite_true, hac2, hnv]; done)
  · simp (config := { decide := true }) only [preStB, Function.update_apply, Sum.elim_inl,
      Sum.inl.injEq, Sum.inr.injEq, RsbX.vx.injEq, bvx, reduceCtorEq, ite_false, ite_true,
      hwn, hsn, htC, htK, h3, h4, h5, List.length_replicate, List.length_cons,
      List.append_nil, List.drop_replicate]
    omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true]
      all_goals simp [htC, htK]
    · simp only [Function.update_apply, preStB, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
        ite_false, ite_true]
      rcases x with j | _ | _ | _ | _ | _ | j
      all_goals simp [h3, h4, h5, hsn, htC, htK, hwn, List.drop_replicate]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preStB, Sum.elim_inr]

theorem band_preL8 (hg : Function.Injective g) (hι : Function.Injective ι)
    (hdisj : ∀ r j, g r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    (w : ℕ) (hsn : σ (.inl .sn) = List.replicate D.s tick)
    (hya : σ (.inl .ya) = List.replicate D.t tick) (hhc : σ (.inl .hc) = List.replicate D.α tick)
    (hac : σ (.inl .ac) = List.replicate D.p tick) (hhv : σ (.inl .hv) = List.replicate D.W tick)
    (hwn : (σ (.inl (.cm .wn))).length = w)
    (hef : σ (.inl .ef) = []) (hp : 13 ≤ D.p) (hα : 2 ≤ D.α) (hαp : D.α ^ 2 ≤ D.p) (hs : 0 < D.s)
    (hst : D.s < D.t) (hwW : w ≤ D.W)
    (hW : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W) :
    TwRuns body (preLay g ι) (bandPreL8g g ι) (preStB σ)
      (preStB (Function.update σ (.inl .ef) (tblStreamD (prime + K) w D.s D.t D.α D.p)))
      (preVMCost 48 D.W w [D.s, D.t, D.α, D.p] (preKD D) (D.s * w)) := by
  have htg := preLay_inj hg hι hdisj
  obtain ⟨hs2, ht2, hα2, hm2, hpW, hWD, -⟩ := pre_W_facts hα hs hst hW
  have hp2 : D.p < 2 ^ D.W := lt_trans hpW Nat.lt_two_pow_self
  have hv : preLoadVal (preStB σ)
      [(.inl .sn, 34), (.inl .ya, 35), (.inl .hc, 36), (.inl .ac, 19)]
      (fun _ : Fin 48 => 0) = Function.update (Function.update (Function.update (Function.update
        (fun _ : Fin 48 => 0) 34 D.s) 35 D.t) 36 D.α) 19 D.p := by
    simp [preLoadVal, preStB, hsn, hya, hhc, hac]
  have h := preVM_runs (body := body) htg (.inl .hv) (.inl (.cm .wn))
    [(.inl .sn, 34), (.inl .ya, 35), (.inl .hc, 36), (.inl .ac, 19)]
    tblStreamDCode (.inl .ef) (preStB σ) (fun _ => rfl) (by simp [preStB, hhv])
    (by simp [preStB, hwn]) hwW
    (fun j => by
      rw [hv]
      simp only [Function.update_apply]
      split_ifs <;> first | assumption | exact Nat.two_pow_pos _)
    (tblStreamD_do (A := prime + K) (W := D.W) (w := w) ⟨_, []⟩ (s := D.s) (t := D.t) (α := D.α)
      (p := D.p)
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true })) hp hα hαp hs hWD)
    (tblStreamD (prime + K) w D.s D.t D.α D.p) (fun s' hs' => by
      simp only at hs'; rw [hs', List.append_nil, List.reverse_reverse])
  rw [length_tblStreamD, preStB_upd, preStB_inl, hef, List.append_nil] at h
  refine twRuns_mono h (le_of_eq ?_)
  simp [preStB, hsn, hya, hhc, hac, preKD]

end StepL

/-! ### Step 3b: the diagonal table, scratch -/

section StepD

variable {A : ℕ}

theorem tblPairs_csyms (A w x : ℕ) : tblPairs A w x 0 = csyms A w ⟨(x : ℤ), 0⟩ := by
  rw [tbl_pairs_red]

/-- The scratch registers cleared at the end of step 3. -/
def bandScrL : List (RsbR ⊕ RsbX t₀) :=
  [.inl .tb, .inl .ya, .inl .b1, .inl .hc, .inl .ac, .inl .hv, .inl .xs, .inl .tA, .inl .tJ,
    .inl .tL]

variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

/-- **The diagonal table** `D · 2^(4p)` on `dtab`, at precision `5p`. -/
theorem band_preL10 (hrg₂ : Function.Injective (Sum.elim rg rgx))
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) (hι : Function.Injective ι) (hT : 64 ≤ T)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ prime + K) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (D : PreAxB) [NeZero D.s] (w : ℕ) (hready : RsbReady (fun r => σ (.inl r)) w D.bP)
    (hw : 1 ≤ w) (hpw : D.bP ≤ w)
    (hef : σ (.inl .ef) = tblStreamD (prime + K) w D.s D.t D.α D.p)
    (htb : σ (.inl .tb) = tblPairs (prime + K) w (2 ^ (9 * D.p)) 0) (hdtab : σ (.inl .dtab) = [])
    (hfx : ∀ ℓ : ZMod D.s, Fits w (rsbReal (tableD D.s D.t D.α D.p ℓ)))
    (hfc : Fits w (⟨2 ^ (9 * D.p), 0⟩ : GaussianInt)) :
    RsbRuns body (Sum.elim rg rgx) ι (bandScaleP rg hι hT hQ .ef .tb .dtab) σ
      (Function.update (Function.update σ (.inl .dtab)
        (cstream (prime + K) w ((rsbArr fun ℓ => rsbReal (tableD D.s D.t D.α D.p ℓ)).map
          fun a => tdivN D.bP (a * ⟨2 ^ (9 * D.p), 0⟩)))) (.inl .ef) [])
      (D.s * (rmulCost T w + 6 * w + 8) + 6 + (2 * (D.s * w) + 2)) := by
  have hrg : Function.Injective rg := fun a b h => Sum.inl_injective (hrg₂ (a₁ := .inl a) h)
  have hdisj : ∀ r j, rg r ≠ ι j := fun r j => hdisj₂ (.inl r) j
  have h := band_scale_runs (body := body) (ι := ι) hrg hdisj hι hT hQ hA (x := .ef) (y := .tb)
    (o := .dtab) ⟨by decide, by decide, by decide, fun _ => ⟨by simp, by simp, by simp⟩⟩
    (fun r => σ (.inl r)) hready hw hpw (rsbArr fun ℓ => rsbReal (tableD D.s D.t D.α D.p ℓ))
    (2 ^ (9 * D.p))
    (by intro a ha; simp only [rsbArr, List.mem_map] at ha; obtain ⟨_, _, rfl⟩ := ha; exact hfx _)
    hfc (by simp [hef, tblStreamD_cstream]) (by simp [htb, tblPairs_csyms]) (by simp [hdtab])
  have h2 := rsb_lift_inl hrg₂ h (fun x => σ (.inr x))
  convert h2 using 1
  · funext r; rcases r with r | x <;> rfl
  · funext r; rcases r with r | x
    · by_cases h1 : r = .ef
      · subst h1; simp
      · by_cases h2 : r = .dtab
        · subst h2; simp
        · simp [h1, h2]
    · simp
  · simp [length_rsbArr]

end StepD

/-! ### Step 4: the factorization -/

section StepP

open Mult.BandFactor in
/-- The folded-row stream is the initial window and the factorization inputs of the folded
Gaussian matrix. -/
theorem tblFoldStream_rows (A w s t α P wd : ℕ) [NeZero s] (hsw : 2 * wd + 1 < s) :
    tblFoldStream A w s t α P wd (2 * wd + 1) (2 * wd + 1 + 1 + s) =
      cstream A w (((bandRows wd s (coefZ s t α P)).map colC).flatten ++
        ((bandInputs wd s (coefZ s t α P)).map colC).flatten) := by
  rw [tblFoldStream_cstream, foldRows_eq s t α P wd (2 * wd + 1) hsw, bandRows, bandInputs]
  simp [List.map_flatten, List.flatten_append]
  rfl

theorem prep_hf_eq' (P K w s : ℕ) [NeZero s] (aZ : ZMod s → ℤ → ℤ) :
    ((List.map (fun m => colC (Mult.BandFactor.ucolZ (2 * w + 1)
      (facUr P K (bandRows w s aZ) (bandInputs w s aZ) s) m)) (List.range s)).reverse).flatten =
      ((bandUc P K w s aZ).map colC).flatten := by
  rw [← prep_hf_eq, List.map_reverse]

theorem prep_df_eq' (P K w s : ℕ) [NeZero s] (aZ : ZMod s → ℤ → ℤ) :
    (List.map (fun j => (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K (bandRows w s aZ)
      (bandInputs w s aZ) j)) K, 0⟩ : GaussianInt))
      (List.range s)).reverse = (bandRcs P K w s aZ).map fun x => (⟨x, 0⟩ : GaussianInt) := by
  rw [← prep_df_eq, List.map_reverse]

variable {A : ℕ}

/-- The register file after the factorization: the tables `bo`, `hf`, `df`, the box stream `l`
back on `src`, the counters `m2n`, `kn`, `ms`, `mwn` of its last phase. -/
def bandFP (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (D : PreAxB) [NeZero D.s] (w : ℕ)
    (l : List (Fin (A + 4))) : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update σ
    (.inl .src) l)
    (.inl .bo) (cstream A w (((bandLc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP)).map
      colC).flatten)))
    (.inl .hf) (cstream A w (((bandUc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP)).map
      colC).flatten)))
    (.inl .df) (cstream A w ((bandRcs D.bP D.bK D.bWd D.s
      (Mult.BandFactor.coefZ D.s D.t D.α D.bP)).map fun x => (⟨x, 0⟩ : GaussianInt))))
    (.inl .dout) [])
    (.inl .vk) [])
    (.inl .m2n) (σ (.inl .ms)))
    (.inl .kn) (List.replicate D.s (σ (.inl .ms))).flatten)
    (.inl .ms) (σ (.inl .dst)))
    (.inl .mwn) (σ (.inl (.cm .wn)) ++ σ (.inl .m2wn)))
    (.inl .ef) [])
    (.inl .xs) []

variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

set_option maxRecDepth 4000 in
/-- **The factorization of the folded window matrix.** -/
theorem band_preP (hrg₂ : Function.Injective (Sum.elim rg rgx))
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) (hι : Function.Injective ι) (hT : 64 ≤ T)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ prime + K) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (D : PreAxB) [NeZero D.s] (w : ℕ) (hready : RsbReady (fun r => σ (.inl r)) w D.bP)
    (hw : 1 ≤ w) (hp : D.bP ≤ w) (hsw : 2 * D.bWd + 1 < D.s)
    (hfit : ∀ m < D.s, FacFits w D.bP D.bK (facState D.bP D.bK
      (bandRows D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP))
      (bandInputs D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP)) m))
    (hbx : σ (.inl .bx) = tblPairs (prime + K) w (2 ^ (5 * D.p - 2)) 0)
    (l : List (Fin (prime + K + 4)))
    (hsrc : σ (.inl .src) = tblFoldStream (prime + K) w D.s D.t D.α D.bP D.bWd D.bB
      (D.bB + 1 + D.s) ++ l)
    (htswn : (σ (.inl .tswn)).length = (D.bB + 1) * (2 * D.bB + 1) * w)
    (hhf : σ (.inl .hf) = []) (hdf : σ (.inl .df) = []) (hdout : σ (.inl .dout) = [])
    (hmsk : σ (.inl .msk) = csyms (prime + K) w 0)
    (hvk : σ (.inl .vk) = []) (hef : σ (.inl .ef) = []) (htb : σ (.inl .tb) = [])
    (hsr : σ (.inl .sr) = []) (hbo : σ (.inl .bo) = [])
    (hhv : σ (.inl .hv) = []) (hxa : σ (.inl .xa) = []) (hhc : σ (.inl .hc) = [])
    (hya : σ (.inl .ya) = []) (hxs : σ (.inl .xs) = [])
    (hpr : σ (.inl .pr) = []) (hac : σ (.inl .ac) = []) (hac2 : σ (.inl .ac2) = [])
    (hnv : σ (.inl .nv) = []) (hb1 : σ (.inl .b1) = []) (htC : σ (.inl .tC) = [])
    (htA : σ (.inl .tA) = []) (htJ : σ (.inl .tJ) = []) (htK : σ (.inl .tK) = [])
    (htL : σ (.inl .tL) = []) (hsel : σ (.inl .sel) = []) (hsn : (σ (.inl .sn)).length = D.s)
    (hkn : (σ (.inl .kn)).length = D.bK) (hms : (σ (.inl .ms)).length = D.bB)
    (hm2n : (σ (.inl .m2n)).length = 2 * D.bB) (hmwn : (σ (.inl .mwn)).length = 2 * D.bB * w)
    (hsmwn : (σ (.inl .smwn)).length = (2 * D.bB + 1) * w)
    (hm2wn : (σ (.inl .m2wn)).length = 2 * D.bWd * w)
    (hdst : (σ (.inl .dst)).length = 2 * D.bWd) :
    RsbRuns body (Sum.elim rg rgx) ι (bandAxisPrepP rg hι hT hQ) σ (bandFP σ D w l)
      (bandAxisPrepCost T w (2 * D.bWd) D.bK D.s) := by
  have hrg : Function.Injective rg := fun a b h => Sum.inl_injective (hrg₂ (a₁ := .inl a) h)
  have hdisj : ∀ r j, rg r ≠ ι j := fun r j => hdisj₂ (.inl r) j
  have hB : D.bB = 2 * D.bWd + 1 := rfl
  set aZ := Mult.BandFactor.coefZ D.s D.t D.α D.bP
  set rows := bandRows D.bWd D.s aZ
  set inputs := bandInputs D.bWd D.s aZ
  have hrows : rows.length = 2 * D.bWd + 1 + 1 := by simp [rows, bandRows, Mult.BandFactor.windowZ]
  have hrl : ∀ row ∈ rows, row.length = 2 * (2 * D.bWd + 1) + 1 := by
    intro row hr
    simp only [rows, bandRows, Mult.BandFactor.windowZ, List.mem_map] at hr
    obtain ⟨_, _, rfl⟩ := hr
    simp [Mult.BandFactor.winRowZ]
  have hin : ∀ row ∈ inputs, row.length = 2 * (2 * D.bWd + 1) + 1 := by
    intro row hr
    simp only [inputs, bandInputs, Mult.BandFactor.inputsZ, List.mem_map] at hr
    obtain ⟨_, _, rfl⟩ := hr
    simp [Mult.BandFactor.winRowZ]
  obtain ⟨σ', h, hbo', hhf', hdf', hsrc', hm2n', hmwn', hsn', hdout', hvk', hef', hxs', hkn', hms',
      hm2nv, hknv, hmwnv, hready', hframe⟩ :=
    band_axisPrep_runs (body := body) (ι := ι) hrg hdisj hι hT hQ hA (k := 2 * D.bWd) (K := D.bK)
      (s := D.s) (fun r => σ (.inl r)) hready hw hp rows inputs hrows hrl hin (length_bandInputs _ _ _)
      hfit (fun m _ => by simp [hbx, Mult.BandFactor.newtonZ, tblPairs_csyms, PreAxB.bP]) l
      (by rw [hsrc, hB, tblFoldStream_rows _ _ _ _ _ _ _ hsw])
      (by rw [htswn, hB]) hhf hdf hdout hmsk hvk hef htb hsr hbo hhv hxa hhc hya hxs hpr hac hac2
      hnv hb1 htC htA htJ htK htL hsel hsn hkn (by rw [hms]; rfl) (by rw [hm2n]; rfl)
      (by rw [hmwn]; rfl) (by rw [hsmwn]; rfl) (by rw [hm2wn]) (by rw [hdst])
  have h2 := rsb_lift_inl hrg₂ h (fun x => σ (.inr x))
  convert h2 using 1
  · funext r; rcases r with r | x <;> rfl
  · funext r; rcases r with r | x
    · simp only [Sum.elim_inl]
      by_cases hr : r ∈ ([.src, .hf, .df, .dout, .bo, .vk, .m2n, .kn, .ms, .mwn, .ef, .xs] : List RsbR)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [bandFP, hsrc', hhf', hdf', hdout', hbo', hvk', hm2nv, hknv, hms', hmwnv, hef', hxs',
            prep_bo_eq, prep_hf_eq', prep_df_eq', rows, inputs, aZ]
      · rw [hframe r hr]
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
        simp [bandFP, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
    · simp [bandFP]

end StepP

/-! ### Step 5: the line-phase registers -/

section StepE

variable (g : RsbR ⊕ RsbX t₀ → Fin T)

/-- The factor-phase counters cleared after the factorization. -/
def bandClrE : List (RsbR ⊕ RsbX t₀) :=
  [.inl .kn, .inl .ms, .inl .dst, .inl .msk, .inl .tswn, .inl .smwn, .inl .m2wn, .inl .bx]

/-- Move a coefficient register through `ac2`, keeping its order. -/
def bandMv2 (a b : RsbR ⊕ RsbX t₀) : Pr F T Q (prime + K) U :=
  .seq (moveR (g a) (g (.inl .ac2)) id) (moveR (g (.inl .ac2)) (g b) id)

/-- Clear the factor-phase counters and move the parked line-phase values into place. -/
def bandPreE : Pr F T Q (prime + K) U :=
  .seq (preClears (bandClrE.map g))
  (.seq (bandMv2 g (bvx 0) (.inl .msk)) (.seq (bandMv2 g (bvx 1) (.inl .smwn))
  (.seq (bandMv2 g (bvx 2) (.inl .bx))
  (.seq (moveR (g (bvx 3)) (g (.inl .tswn)) id) (.seq (moveR (g (bvx 4)) (g (.inl .m2wn)) id)
    (moveR (g (bvx 5)) (g (.inl .kn)) id))))))

variable {A : ℕ}

open Classical in
/-- Clearing the factor-phase counters. -/
def bandFE0 (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  fun r => if r ∈ bandClrE then [] else σ r

/-- One move. -/
def bandMvF (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (a b : RsbR ⊕ RsbX t₀) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Function.update (Function.update σ a []) b ((σ a).reverse ++ σ b)

/-- The register file after step 5. -/
def bandFE (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  bandMvF (bandMvF (bandMvF (bandMvF (bandMvF (bandMvF (bandMvF (bandMvF (bandMvF (bandFE0 σ)
    (bvx 0) (.inl .ac2)) (.inl .ac2) (.inl .msk))
    (bvx 1) (.inl .ac2)) (.inl .ac2) (.inl .smwn))
    (bvx 2) (.inl .ac2)) (.inl .ac2) (.inl .bx))
    (bvx 3) (.inl .tswn)) (bvx 4) (.inl .m2wn)) (bvx 5) (.inl .kn)

variable {body : F → Pr F T Q (prime + K) U} {g : RsbR ⊕ RsbX t₀ → Fin T}

theorem twRuns_mvF (hg : Function.Injective g) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    {a b : RsbR ⊕ RsbX t₀} (hab : a ≠ b) :
    TwRuns body g (moveR (g a) (g b) id) σ (bandMvF σ a b) (2 * (σ a).length + 2) :=
  twRuns_moveR (body := body) hg hab σ

/-- The step bound of step 5. -/
def bandCostE (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) : ℕ :=
  ((bandClrE.map fun r => 2 * (σ r).length + 2).sum + 1) +
    (2 * (2 * (σ (bvx 0)).length + 2) + (2 * (2 * (σ (bvx 1)).length + 2) +
    (2 * (2 * (σ (bvx 2)).length + 2) + ((2 * (σ (bvx 3)).length + 2) +
    ((2 * (σ (bvx 4)).length + 2) + (2 * (σ (bvx 5)).length + 2))))))

set_option maxRecDepth 4000 in
theorem band_preE (hg : Function.Injective g) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (hac2 : σ (.inl .ac2) = []) :
    TwRuns body g (bandPreE g) σ (bandFE σ) (bandCostE σ) := by
  have h1 := twRuns_congr (preClears_runs (body := body) hg bandClrE (by simp [bandClrE]) σ)
    (show _ = bandFE0 σ by funext r; by_cases h : r ∈ bandClrE <;> simp [bandFE0, h])
  refine twRuns_mono (twRuns_seq h1
    (twRuns_seq (twRuns_seq (twRuns_mvF hg _ (by simp)) (twRuns_mvF hg _ (by simp)))
    (twRuns_seq (twRuns_seq (twRuns_mvF hg _ (by simp)) (twRuns_mvF hg _ (by simp)))
    (twRuns_seq (twRuns_seq (twRuns_mvF hg _ (by simp)) (twRuns_mvF hg _ (by simp)))
    (twRuns_seq (twRuns_mvF hg _ (by simp)) (twRuns_seq (twRuns_mvF hg _ (by simp))
      (twRuns_mvF hg _ (by simp)))))))) (le_of_eq ?_)
  simp (config := { decide := true }) only [bandMvF, bandFE0, bandClrE, bvx, Function.update_apply,
    Sum.inl.injEq, Sum.inr.injEq, RsbX.vx.injEq, reduceCtorEq, ite_false, ite_true, List.mem_cons,
    List.not_mem_nil, or_false, false_or, or_self, hac2, List.length_append, List.length_reverse,
    List.length_nil, bandCostE]
  omega

end StepE


/-! ### The loader, part 1: record, folded rows, factor-phase counters -/

section Part1

variable (rg : RsbR → Fin T) (rgx : RsbX t₀ → Fin T) (ι : Fin 64 → Fin T) (hd : Fin 5 → Fin t₀)

/-- Steps 1 and 2. -/
def bandPreB1 : Pr F T Q (prime + K) U :=
  .seq (bandPreA (Sum.elim rg rgx) hd) (.seq (bandPreF1 (Sum.elim rg rgx))
  (.seq (bandPreFold rg rgx ι) (.seq (bandPreF2 (Sum.elim rg rgx)) (bandPreF3 (Sum.elim rg rgx) ι))))

variable {A : ℕ}

/-- The register file after steps 1 and 2. -/
def bandFB1 (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) [NeZero D.s] (rest : List (Fin (A + 4))) : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Function.update (bandFF2 (Function.update (bandFF1 (bandFA σ hd w D rest) D) (.inl .src)
    (tblFoldStream A w D.s D.t D.α D.bP D.bWd D.bB (D.bB + 1 + D.s) ++ σ (.inl .src))) D w
    (pairSym A false false))
    (.inl .bx) (tblPairs A w (2 ^ (5 * D.p - 2)) 0)

/-- The step bound of steps 1 and 2. -/
def bandCostB1 (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) : ℕ :=
  bandCostA σ hd w D + (bandCostF1 D +
    (preVMCost 60 D.W w [D.bP, D.s, D.t, D.α, D.bWd, D.bB + 1 + D.s, 2 * D.bB + 1, D.bB]
      (bandKFold D) ((D.bB + 1 + D.s) * (2 * D.bB + 1) * w) +
    (bandCostF2 D w + bandCostF3 D w)))

theorem rsb_of_tw {R : Type} [DecidableEq R] {body : F → Pr F T Q (prime + K) U}
    {g : R → Fin T} {p : Pr F T Q (prime + K) U} {ρ ρ' : R → List (Fin (prime + K + 4))} {b : ℕ}
    (h : TwRuns body g p ρ ρ' b) : RsbRuns body g ι p ρ ρ' b :=
  fun v S _ hS => h v S hS

variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

/-- Registers outside step 1. -/
def bandLA : List RsbR :=
  [.msk, .bo, .hf, .df, .dtab, .padc, .sn, .mwn, .m2wn, .m2n, .smwn, .tswn, .kn, .ms, .bx, .cm .pn,
    .prm, .ya, .b1, .hc, .ac, .hv]

set_option maxRecDepth 4000 in
theorem bandFA_frame (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) (rest : List (Fin (A + 4))) (r : RsbR) (hr : r ∉ bandLA) :
    bandFA σ hd w D rest (.inl r) = σ (.inl r) := by
  simp only [bandLA, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [bandFA, preBankB, bandF0, bandClrB, preHB, hr]

theorem bandFA_vx (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) (rest : List (Fin (A + 4))) (j : Fin 12) :
    bandFA σ hd w D rest (.inr (.vx j)) = σ (.inr (.vx j)) := by
  simp [bandFA, preBankB, bandF0, bandClrB, preHB]

set_option maxRecDepth 4000 in
theorem bandFA_vals (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) (rest : List (Fin (A + 4))) :
    bandFA σ hd w D rest (.inl .ya) = List.replicate D.t tick ∧
    bandFA σ hd w D rest (.inl .sn) = List.replicate D.s tick ∧
    bandFA σ hd w D rest (.inl .b1) = List.replicate D.m tick ∧
    bandFA σ hd w D rest (.inl .hc) = List.replicate D.α tick ∧
    bandFA σ hd w D rest (.inl .ac) = List.replicate D.p tick ∧
    bandFA σ hd w D rest (.inl .hv) = List.replicate D.W tick ∧
    bandFA σ hd w D rest (.inl .prm) = rest ∧
    (∀ r ∈ [RsbR.msk, .bo, .hf, .df, .dtab, .padc, .mwn, .m2wn, .m2n, .smwn, .tswn, .kn, .ms, .bx,
      .cm .pn], bandFA σ hd w D rest (.inl r) = []) := by
  refine ⟨by simp [bandFA, preBankB], by simp [bandFA, preBankB], by simp [bandFA, preBankB],
    by simp [bandFA, preBankB], by simp [bandFA, preBankB], by simp [bandFA, preBankB],
    by simp [bandFA, preBankB], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> simp [bandFA, preBankB, bandF0, bandClrB, preHB]

variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

/-- Steps 2b–2d from the state after step 2a. -/
theorem band_preB1b (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hι : Function.Injective ι)
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (D : PreAxB) [NeZero D.s] (w : ℕ) (hwW : w ≤ D.W) (hW : BandFoldW D) (hp1 : 1 ≤ D.p)
    (hwn : (σ (.inl (.cm .wn))).length = w)
    (hpn : σ (.inl (.cm .pn)) = List.replicate D.bP tick)
    (hsn : σ (.inl .sn) = List.replicate D.s tick) (hya : σ (.inl .ya) = List.replicate D.t tick)
    (hhc : σ (.inl .hc) = List.replicate D.α tick) (hac : σ (.inl .ac) = List.replicate D.p tick)
    (hhv : σ (.inl .hv) = List.replicate D.W tick) (htA : σ (.inl .tA) = List.replicate D.bWd tick)
    (hxs : σ (.inl .xs) = List.replicate (D.bB + 1 + D.s) tick)
    (htL : σ (.inl .tL) = List.replicate (2 * D.bB + 1) tick)
    (htJ : σ (.inl .tJ) = List.replicate D.bB tick) (hvx : ∀ j, σ (.inr (.vx j)) = [])
    (hms : σ (.inl .ms) = []) (hm2n : σ (.inl .m2n) = []) (hdst : σ (.inl .dst) = [])
    (hm2wn : σ (.inl .m2wn) = []) (hmwn : σ (.inl .mwn) = []) (hsmwn : σ (.inl .smwn) = [])
    (htswn : σ (.inl .tswn) = []) (hkn : σ (.inl .kn) = []) (hmsk : σ (.inl .msk) = [])
    (hbx : σ (.inl .bx) = [])
    (htC : σ (.inl .tC) = []) (htK : σ (.inl .tK) = []) (hac2 : σ (.inl .ac2) = [])
    (hnv : σ (.inl .nv) = []) :
    RsbRuns body (Sum.elim rg rgx) ι (.seq (bandPreFold rg rgx ι) (.seq (bandPreF2 (Sum.elim rg rgx))
        (bandPreF3 (Sum.elim rg rgx) ι))) σ
      (Function.update (bandFF2 (Function.update σ (.inl .src)
        (tblFoldStream (prime + K) w D.s D.t D.α D.bP D.bWd D.bB (D.bB + 1 + D.s) ++ σ (.inl .src)))
        D w (pairSym (prime + K) false false))
        (.inl .bx) (tblPairs (prime + K) w (2 ^ (5 * D.p - 2)) 0))
      (preVMCost 60 D.W w [D.bP, D.s, D.t, D.α, D.bWd, D.bB + 1 + D.s, 2 * D.bB + 1, D.bB]
        (bandKFold D) ((D.bB + 1 + D.s) * (2 * D.bB + 1) * w) +
        (bandCostF2 D w + bandCostF3 D w)) := by
  have hpW : 5 * D.p < D.W := by have := hW.w5; unfold PreAxB.bP at this; omega
  have hFold := band_preFold (body := body) hrg₂ hι hdisj₂ σ D w hwW hW hpn hsn hya hhc htA hxs htL
    htJ (by rw [hhv]) hwn hvx
  set σFo := Function.update σ (.inl .src) (tblFoldStream (prime + K) w D.s D.t D.α D.bP D.bWd D.bB
    (D.bB + 1 + D.s) ++ σ (.inl .src)) with hσFo
  have hF2 := pre_rsbRuns (band_preF2 (body := body) (ι := ι) hrg₂ hι hdisj₂ σFo D w
    (by simp [hσFo, hwn]) (by simp [hσFo, hxs]) (by simp [hσFo, htA]) (by simp [hσFo, htJ])
    (by simp [hσFo, htL]) (by simp [hσFo, hhc]) (by simp [hσFo, hms]) (by simp [hσFo, hm2n])
    (by simp [hσFo, hdst]) (by simp [hσFo, hm2wn]) (by simp [hσFo, hmwn]) (by simp [hσFo, hsmwn])
    (by simp [hσFo, htswn]) (by simp [hσFo, hkn]) (by simp [hσFo, hmsk]) (by simp [hσFo, htC])
    (by simp [hσFo, htK]) (by simp [hσFo, hac2]) (by simp [hσFo, hnv]))
  have hF3 := pre_rsbRuns (band_preF3 (body := body) (ι := ι) hrg₂ hι hdisj₂
    (bandFF2 σFo D w (pairSym (prime + K) false false)) D w
    (by simp [bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, hσFo, hwn]) hwW hp1 hpW
    (by simp [bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, hσFo, hac])
    (by simp [bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, hσFo, hhv])
    (by simp [bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, hσFo, hbx])
    (by simp [bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, hσFo, htC])
    (by simp [bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, hσFo, htK])
    (by simp [bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, hσFo, hac2]))
  exact RsbRuns.seq hdisj₂ hFold (RsbRuns.seq hdisj₂ hF2 hF3)

set_option maxRecDepth 4000 in
theorem band_preB1 (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hι : Function.Injective ι)
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd)
    (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) [NeZero D.s]
    (rest : List (Fin (prime + K + 4))) (w : ℕ) (hwW : w ≤ D.W) (hW : BandFoldW D)
    (hp1 : 1 ≤ D.p)
    (hprm : σ (.inl .prm) = preRec D.fields ++ rest) (hwn : (σ (.inl (.cm .wn))).length = w)
    (hya : σ (.inl .ya) = []) (hb1 : σ (.inl .b1) = []) (htb : σ (.inl .tb) = [])
    (hxa : σ (.inl .xa) = []) (hxs : σ (.inl .xs) = []) (hpr : σ (.inl .pr) = [])
    (hhc : σ (.inl .hc) = []) (hac : σ (.inl .ac) = []) (hhv : σ (.inl .hv) = [])
    (htL : σ (.inl .tL) = []) (hac2 : σ (.inl .ac2) = []) (hnv : σ (.inl .nv) = [])
    (htA : σ (.inl .tA) = []) (htJ : σ (.inl .tJ) = []) (hdst : σ (.inl .dst) = [])
    (htC : σ (.inl .tC) = []) (htK : σ (.inl .tK) = []) (hvx : ∀ j, σ (.inr (.vx j)) = []) :
    RsbRuns body (Sum.elim rg rgx) ι (bandPreB1 rg rgx ι hd) σ (bandFB1 σ hd w D rest)
      (bandCostB1 σ hd w D) := by
  have hA := pre_rsbRuns (band_preA (body := body) hrg₂ hι hdisj₂ hdi σ D rest w hprm hwn hya hb1
    htb hxa hxs hpr hhc hac hhv htL hac2 hnv)
  obtain ⟨vya, vsn, vb1, vhc, vac, vhv, -, vclr⟩ := bandFA_vals σ hd w D rest
  have fr : ∀ r, r ∉ bandLA → bandFA σ hd w D rest (.inl r) = σ (.inl r) :=
    bandFA_frame σ hd w D rest
  have hF1 := pre_rsbRuns (band_preF1 (body := body) (ι := ι) hrg₂ hι hdisj₂ (bandFA σ hd w D rest)
    D vac vb1 vsn (vclr _ (by simp)) (by rw [fr _ (by decide)]; exact htA)
    (by rw [fr _ (by decide)]; exact htJ) (by rw [fr _ (by decide)]; exact htL)
    (by rw [fr _ (by decide)]; exact hxs) (by rw [fr _ (by decide)]; exact hac2))
  set σ1 := bandFF1 (bandFA σ hd w D rest) D with hσ1
  have e1 : ∀ r, r ∉ [RsbR.cm .pn, .tA, .tJ, .tL, .xs] → σ1 (.inl r) = bandFA σ hd w D rest (.inl r) := by
    intro r hr
    simp only [hσ1, bandFF1]
    repeat rw [Function.update_of_ne (by rintro ⟨⟩; simp at hr)]
  have hB := band_preB1b (body := body) hrg₂ hι hdisj₂ σ1 D w hwW hW hp1
    (by rw [e1 _ (by decide), fr _ (by decide)]; exact hwn) (by simp [hσ1, bandFF1])
    (by rw [e1 _ (by decide)]; exact vsn) (by rw [e1 _ (by decide)]; exact vya)
    (by rw [e1 _ (by decide)]; exact vhc) (by rw [e1 _ (by decide)]; exact vac)
    (by rw [e1 _ (by decide)]; exact vhv) (by simp [hσ1, bandFF1]) (by simp [hσ1, bandFF1])
    (by simp [hσ1, bandFF1]) (by simp [hσ1, bandFF1])
    (fun j => by
      simp only [hσ1, bandFF1]
      repeat rw [Function.update_of_ne (by simp)]
      rw [bandFA_vx]; exact hvx j)
    (by rw [e1 _ (by decide)]; exact vclr _ (by simp))
    (by rw [e1 _ (by decide)]; exact vclr _ (by simp))
    (by rw [e1 _ (by decide), fr _ (by decide)]; exact hdst)
    (by rw [e1 _ (by decide)]; exact vclr _ (by simp))
    (by rw [e1 _ (by decide)]; exact vclr _ (by simp))
    (by rw [e1 _ (by decide)]; exact vclr _ (by simp))
    (by rw [e1 _ (by decide)]; exact vclr _ (by simp))
    (by rw [e1 _ (by decide)]; exact vclr _ (by simp))
    (by rw [e1 _ (by decide)]; exact vclr _ (by simp))
    (by rw [e1 _ (by decide)]; exact vclr _ (by simp))
    (by rw [e1 _ (by decide), fr _ (by decide)]; exact htC)
    (by rw [e1 _ (by decide), fr _ (by decide)]; exact htK)
    (by rw [e1 _ (by decide), fr _ (by decide)]; exact hac2)
    (by rw [e1 _ (by decide), fr _ (by decide)]; exact hnv)
  have hsrc : σ1 (.inl .src) = σ (.inl .src) := by rw [e1 _ (by decide), fr _ (by decide)]
  rw [hsrc] at hB
  exact RsbRuns.seq hdisj₂ hA (RsbRuns.seq hdisj₂ hF1 hB)

end Part1

/-! ### The loader, part 2: the line-phase values -/

section Part2

variable (rg : RsbR → Fin T) (rgx : RsbX t₀ → Fin T) (ι : Fin 64 → Fin T)

/-- Step 3, first half: padding counter, mask, constants, fold counters. -/
def bandPreB2a : Pr F T Q (prime + K) U :=
  .seq (bandPreL1 (Sum.elim rg rgx)) (.seq (bandPreL2g (Sum.elim rg rgx) ι)
  (.seq (bandPreL3 (Sum.elim rg rgx) ι) (.seq (bandPreL4 (Sum.elim rg rgx) ι)
    (bandPreL5g (Sum.elim rg rgx)))))

variable {A : ℕ}

/-- The register file after the first half of step 3. -/
def bandFB2a (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))) (D : PreAxB) (w : ℕ) :
    RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update σ
    (.inl .padc) (List.replicate ((D.t - D.s) * w) tick))
    (bvx 0) ((preMaskE A D.s D.t D.t).map preBitOf))
    (bvx 1) (tblPairs A w (2 ^ (9 * D.p - 1)) 0))
    (bvx 2) (tblPairs A w (2 ^ (D.p - D.α * D.α)) 0))
    (bvx 3) (List.replicate ((D.s + 1) / 2 * w) tick))
    (bvx 4) (List.replicate (D.s / 2) tick))
    (bvx 5) (List.replicate ((D.s + 1) / 2 - D.s / 2) tick)

/-- The step bound of the first half of step 3. -/
def bandCostB2a (D : PreAxB) (w : ℕ) : ℕ :=
  ((4 * D.t + 4) + ((4 * D.s + 4) + (((D.t - D.s) * (4 * w + 7) + 2 * (D.t - D.s) + 4) +
    (2 * (D.t - D.s) + 2)))) +
  ((1 + (preVMCost 48 D.W 1 [D.s, D.t] (preKM D) D.t + ((2 * D.t + 2) + ((2 * D.t + 2) +
    (2 * 1 + 2))))) +
  (((4 * D.p + 4) + (preVMCost 48 D.W w [9 * D.p] (bandKH (9 * D.p)) w + (2 * (9 * D.p) + 2))) +
  (((4 * D.p + 4) + (1 + ((4 * (D.α * D.α) + 4) + (preVMCost 48 D.W w [D.p + 1 - D.α * D.α]
    (bandKH (D.p + 1 - D.α * D.α)) w + (2 * (D.p + 1 - D.α * D.α) + 2))))) +
  ((4 * D.s + 4) + (1 + ((4 * (D.s + 1) + 4) + (((D.s + 1) / 2 * (4 * w + 7) +
    2 * ((D.s + 1) / 2) + 4) + ((4 * D.s + 4) + ((4 * (D.s / 2) + 4) +
    ((2 * ((D.s + 1) / 2 - D.s / 2) + 2) + (2 * (D.s + 1) + 2)))))))))))

variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

set_option maxRecDepth 4000 in
theorem band_preB2a (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hι : Function.Injective ι)
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (D : PreAxB) (w : ℕ) (hwW : w ≤ D.W) (hp1 : 1 ≤ D.p) (hpW : 9 * D.p < D.W)
    (hjp : D.α * D.α ≤ D.p) (hs : 0 < D.s) (hst : D.s < D.t)
    (hWM : 4 * D.t * (D.s + 1) < 2 ^ D.W)
    (hwn : (σ (.inl (.cm .wn))).length = w)
    (hya : σ (.inl .ya) = List.replicate D.t tick) (hsn : σ (.inl .sn) = List.replicate D.s tick)
    (hac : σ (.inl .ac) = List.replicate D.p tick) (hhv : σ (.inl .hv) = List.replicate D.W tick)
    (hxs : σ (.inl .xs) = List.replicate (D.α * D.α) tick)
    (hpadc : σ (.inl .padc) = []) (htC : σ (.inl .tC) = []) (htK : σ (.inl .tK) = [])
    (hac2 : σ (.inl .ac2) = []) (hnv : σ (.inl .nv) = []) (hsr : σ (.inl .sr) = [])
    (hsel : σ (.inl .sel) = []) (hvx : ∀ j, σ (.inr (.vx j)) = []) :
    RsbRuns body (Sum.elim rg rgx) ι (bandPreB2a rg rgx ι) σ (bandFB2a σ D w)
      (bandCostB2a D w) := by
  set g := Sum.elim rg rgx
  have h1 := pre_rsbRuns (band_preL1 (body := body) (ι := ι) hrg₂ hι hdisj₂ σ D w hwn hya hsn hpadc
    htC hac2 hnv)
  set σ1 := Function.update σ (.inl .padc) (List.replicate ((D.t - D.s) * w) tick) with hσ1
  have h2 := pre_rsbRuns (band_preL2 (body := body) (ι := ι) hrg₂ hι hdisj₂ σ1 D
    (by simp [hσ1, hsn]) (by simp [hσ1, hya]) (by simp [hσ1, hhv]) (by simp [hσ1, htK])
    (by simp [hσ1, hsr]) (by simp [hσ1, hsel]) (by simp [hσ1, hvx]) hs hst (by omega) hWM)
  set σ2 := Function.update σ1 (bvx 0) ((preMaskE (prime + K) D.s D.t D.t).map preBitOf) with hσ2
  have h3 := pre_rsbRuns (band_preL3 (body := body) (ι := ι) hrg₂ hι hdisj₂ σ2 D w
    (by simp [hσ2, hσ1, hwn]) hwW hp1 hpW (by simp [hσ2, hσ1, hac]) (by simp [hσ2, hσ1, hhv])
    (by simp [hσ2, hσ1, hvx]) (by simp [hσ2, hσ1, htC]) (by simp [hσ2, hσ1, hac2]))
  set σ3 := Function.update σ2 (bvx 1) (tblPairs (prime + K) w (2 ^ (9 * D.p - 1)) 0) with hσ3
  have h4 := pre_rsbRuns (band_preL4 (body := body) (ι := ι) hrg₂ hι hdisj₂ σ3 D w
    (by simp [hσ3, hσ2, hσ1, hwn]) hwW hjp (by omega) (by simp [hσ3, hσ2, hσ1, hac])
    (by simp [hσ3, hσ2, hσ1, hhv]) (by simp [hσ3, hσ2, hσ1, hxs]) (by simp [hσ3, hσ2, hσ1, hvx])
    (by simp [hσ3, hσ2, hσ1, htC]) (by simp [hσ3, hσ2, hσ1, hac2]))
  set σ4 := Function.update σ3 (bvx 2) (tblPairs (prime + K) w (2 ^ (D.p - D.α * D.α)) 0) with hσ4
  have h5 := pre_rsbRuns (band_preL5 (body := body) (ι := ι) hrg₂ hι hdisj₂ σ4 D w
    (by simp [hσ4, hσ3, hσ2, hσ1, hwn]) (by simp [hσ4, hσ3, hσ2, hσ1, hsn])
    (by simp [hσ4, hσ3, hσ2, hσ1, htC]) (by simp [hσ4, hσ3, hσ2, hσ1, htK])
    (by simp [hσ4, hσ3, hσ2, hσ1, hac2]) (by simp [hσ4, hσ3, hσ2, hσ1, hnv])
    (by simp [hσ4, hσ3, hσ2, hσ1, hvx]) (by simp [hσ4, hσ3, hσ2, hσ1, hvx])
    (by simp [hσ4, hσ3, hσ2, hσ1, hvx]))
  exact RsbRuns.seq hdisj₂ h1 (RsbRuns.seq hdisj₂ h2 (RsbRuns.seq hdisj₂ h3
    (RsbRuns.seq hdisj₂ h4 h5)))

/-- Step 3, second half: the diagonal table, then the scratch cleared. -/
def bandPreB2b (rg : RsbR → Fin T) (rgx : RsbX t₀ → Fin T) (ι : Fin 64 → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr F T Q (prime + K) U :=
  .seq (bandPreL8g (Sum.elim rg rgx) ι) (.seq (bandPreL9 (Sum.elim rg rgx) ι)
  (.seq (bandScaleP rg hι hT hQ .ef .tb .dtab) (preClears (bandScrL.map (Sum.elim rg rgx)))))

open Classical in
/-- The register file after step 3. -/
def bandFB2b (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) [NeZero D.s] (w : ℕ) :
    RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)) :=
  fun r => if r ∈ bandScrL then [] else
    Function.update σ (.inl .dtab) (cstream (prime + K) w ((rsbArr fun ℓ =>
      rsbReal (tableD D.s D.t D.α D.p ℓ)).map fun a => tdivN D.bP (a * ⟨2 ^ (9 * D.p), 0⟩))) r

/-- The step bound of the second half of step 3. -/
def bandCostB2b (T : ℕ) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) (w : ℕ) : ℕ :=
  preVMCost 48 D.W w [D.s, D.t, D.α, D.p] (preKD D) (D.s * w) +
  (((4 * D.p + 4) + (1 + (preVMCost 48 D.W w [9 * D.p + 1] (bandKH (9 * D.p + 1)) w +
    (2 * (9 * D.p + 1) + 2)))) +
  ((D.s * (rmulCost T w + 6 * w + 8) + 6 + (2 * (D.s * w) + 2)) +
  ((bandScrL.map fun r => 2 * (σ r).length + 2).sum + 1 + 2 * w + 2)))

set_option maxRecDepth 4000 in
theorem band_preB2b (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hι : Function.Injective ι)
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ prime + K) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB)
    [NeZero D.s] (w : ℕ) (hwW : w ≤ D.W) (hpW : 9 * D.p + 1 < D.W)
    (hready : RsbReady (fun r => σ (.inl r)) w D.bP) (hw : 1 ≤ w) (hpw : D.bP ≤ w)
    (hp : 13 ≤ D.p) (hα : 2 ≤ D.α) (hαp : D.α ^ 2 ≤ D.p) (hs : 0 < D.s) (hst : D.s < D.t)
    (hW : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W)
    (hfx : ∀ ℓ : ZMod D.s, Fits w (rsbReal (tableD D.s D.t D.α D.p ℓ)))
    (hfc : Fits w (⟨2 ^ (9 * D.p), 0⟩ : GaussianInt))
    (hya : σ (.inl .ya) = List.replicate D.t tick) (hsn : σ (.inl .sn) = List.replicate D.s tick)
    (hhc : σ (.inl .hc) = List.replicate D.α tick) (hac : σ (.inl .ac) = List.replicate D.p tick)
    (hhv : σ (.inl .hv) = List.replicate D.W tick)
    (hef : σ (.inl .ef) = []) (htb : σ (.inl .tb) = []) (hdtab : σ (.inl .dtab) = [])
    (htC : σ (.inl .tC) = []) (hac2 : σ (.inl .ac2) = []) :
    RsbRuns body (Sum.elim rg rgx) ι (bandPreB2b rg rgx ι hι hT hQ) σ (bandFB2b σ D w)
      (bandCostB2b T σ D w) := by
  have hwn := hready.wn
  have h1 := pre_rsbRuns (band_preL8 (body := body) (ι := ι) hrg₂ hι hdisj₂ σ D w hsn hya hhc hac hhv
    hwn hef hp hα hαp hs hst hwW hW)
  set σ1 := Function.update σ (.inl .ef) (tblStreamD (prime + K) w D.s D.t D.α D.p) with hσ1
  have h2 := pre_rsbRuns (band_preL9 (body := body) (ι := ι) hrg₂ hι hdisj₂ σ1 D w
    (by simp [hσ1, hwn]) hwW hpW (by simp [hσ1, hac]) (by simp [hσ1, hhv]) (by simp [hσ1, htb])
    (by simp [hσ1, htC]) (by simp [hσ1, hac2]))
  set σ2 := Function.update σ1 (.inl .tb) (tblPairs (prime + K) w (2 ^ (9 * D.p)) 0) with hσ2
  have hr2 : RsbReady (fun r => σ2 (.inl r)) w D.bP := by
    have := (hready.update .ef (fun c => by simp) (tblStreamD (prime + K) w D.s D.t D.α D.p)).update
      .tb (fun c => by simp) (tblPairs (prime + K) w (2 ^ (9 * D.p)) 0)
    convert this using 1
    funext r
    simp only [hσ2, hσ1, Function.update_apply, Sum.inl.injEq]
  have h3 := band_preL10 (body := body) hrg₂ hdisj₂ hι hT hQ hA σ2 D w hr2 hw hpw (by simp [hσ2, hσ1]) (by simp [hσ2]) (by simp [hσ2, hσ1, hdtab]) hfx hfc
  set σ3 := Function.update (Function.update σ2 (.inl .dtab) (cstream (prime + K) w
    ((rsbArr fun ℓ => rsbReal (tableD D.s D.t D.α D.p ℓ)).map
      fun a => tdivN D.bP (a * ⟨2 ^ (9 * D.p), 0⟩)))) (.inl .ef) [] with hσ3
  have h4 := rsb_of_tw (ι := ι) (twRuns_congr (preClears_runs (body := body) hrg₂ bandScrL
    (by simp [bandScrL]) σ3) (show _ = bandFB2b σ D w by
      funext r
      by_cases hr : r ∈ bandScrL
      · simp [bandFB2b, hr]
      · simp only [bandFB2b, hr, ite_false]
        simp only [bandScrL, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        by_cases he : r = .inl .ef
        · subst he; simp [hσ3, hef]
        · simp [hσ3, hσ2, hσ1, Function.update_apply, hr, he]))
  refine (RsbRuns.seq hdisj₂ h1 (RsbRuns.seq hdisj₂ h2 (RsbRuns.seq hdisj₂ h3 h4))).mono ?_
  simp only [bandCostB2b, hσ3, hσ2, hσ1, bandScrL, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Function.update_apply, Sum.inl.injEq, reduceCtorEq, ite_false, ite_true,
    tblPairs, coeffSyms, 
    List.length_ofFn, htb, List.length_nil]
  omega

end Part2

/-! ### The loader, part 3 and the whole loader -/

section Whole

variable (rg : RsbR → Fin T) (rgx : RsbX t₀ → Fin T) (ι : Fin 64 → Fin T) (hd : Fin 5 → Fin t₀)
  (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)

/-- **The loader of the banded `B̃₀`.** -/
def bandPreB : Pr F T Q (prime + K) U :=
  .seq (bandPreB1 rg rgx ι hd) (.seq (bandPreB2a rg rgx ι) (.seq (bandPreB2b rg rgx ι hι hT hQ)
    (.seq (bandAxisPrepP rg hι hT hQ) (bandPreE (Sum.elim rg rgx)))))

/-- The register file after loading. -/
def bandLoad (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)) :=
  bandFE (bandFP (bandFB2b (bandFB2a (bandFB1 σ hd w D rest) D w) D w) D w (σ (.inl .src)))

variable {body : F → Pr F T Q (prime + K) U} {rg : RsbR → Fin T} {rgx : RsbX t₀ → Fin T}
  {ι : Fin 64 → Fin T}

theorem bandFB2a_frame (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) (w : ℕ)
    (r : RsbR) (hr : r ≠ .padc) : bandFB2a σ D w (.inl r) = σ (.inl r) := by
  simp [bandFB2a, hr]

theorem bandFB2b_frame (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) [NeZero D.s]
    (w : ℕ) (r : RsbR) (hr : r ∉ [RsbR.tb, .ya, .b1, .hc, .ac, .hv, .xs, .tA, .tJ, .tL, .dtab]) :
    bandFB2b σ D w (.inl r) = σ (.inl r) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [bandFB2b, bandScrL, hr]

theorem bandFB2b_scr (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) [NeZero D.s]
    (w : ℕ) (r : RsbR) (hr : r ∈ [RsbR.tb, .ya, .b1, .hc, .ac, .hv, .xs, .tA, .tJ, .tL]) :
    bandFB2b σ D w (.inl r) = [] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [bandFB2b, bandScrL]

/-- Registers changed by part 1. -/
def bandLB1 : List RsbR := bandLA ++ [.tA, .tJ, .tL, .xs, .src, .dst]

set_option maxRecDepth 4000 in
theorem bandFB1_frame (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) (r : RsbR)
    (hr : r ∉ bandLB1) : bandFB1 σ hd w D rest (.inl r) = σ (.inl r) := by
  have hA : r ∉ bandLA := fun h => hr (List.mem_append_left _ h)
  have h2 : r ∉ [RsbR.tA, .tJ, .tL, .xs, .src, .dst] := fun h => hr (List.mem_append_right _ h)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h2
  simp only [bandLA, List.mem_cons, List.not_mem_nil, or_false, not_or] at hA
  rw [← bandFA_frame σ hd w D rest r (by simp [bandLA, hA])]
  simp [bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1, 
    hA, h2]

theorem bandFB1_vx (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) (j : Fin 12) :
    bandFB1 σ hd w D rest (.inr (.vx j)) = σ (.inr (.vx j)) := by
  rw [← bandFA_vx σ hd w D rest j]
  simp [bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1]

set_option maxRecDepth 4000 in
theorem bandFB1_vals (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) :
    let τ := bandFB1 σ hd w D rest
    τ (.inl (.cm .pn)) = List.replicate D.bP tick ∧ τ (.inl .ya) = List.replicate D.t tick ∧
    τ (.inl .sn) = List.replicate D.s tick ∧ τ (.inl .hc) = List.replicate D.α tick ∧
    τ (.inl .ac) = List.replicate D.p tick ∧ τ (.inl .hv) = List.replicate D.W tick ∧
    τ (.inl .xs) = List.replicate (D.α * D.α) tick ∧ τ (.inl .ms) = List.replicate D.bB tick ∧
    τ (.inl .m2n) = List.replicate (2 * D.bB) tick ∧ τ (.inl .dst) = List.replicate (2 * D.bWd) tick ∧
    τ (.inl .m2wn) = List.replicate (2 * D.bWd * w) tick ∧
    τ (.inl .mwn) = List.replicate (2 * D.bB * w) tick ∧
    τ (.inl .smwn) = List.replicate ((2 * D.bB + 1) * w) tick ∧
    τ (.inl .tswn) = List.replicate ((D.bB + 1) * (2 * D.bB + 1) * w) tick ∧
    τ (.inl .kn) = List.replicate (4 * (D.α * D.α)) tick ∧
    τ (.inl .msk) = List.replicate w (pairSym (prime + K) false false) ∧
    τ (.inl .bx) = tblPairs (prime + K) w (2 ^ (5 * D.p - 2)) 0 ∧
    τ (.inl .src) = tblFoldStream (prime + K) w D.s D.t D.α D.bP D.bWd D.bB (D.bB + 1 + D.s) ++
      σ (.inl .src) ∧
    τ (.inl .prm) = rest ∧
    (∀ r ∈ [RsbR.bo, .hf, .df, .dtab, .padc], τ (.inl r) = []) := by
  intro τ
  obtain ⟨vya, vsn, -, vhc, vac, vhv, vprm, vclr⟩ := bandFA_vals σ hd w D rest
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  all_goals try (simp [τ, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1,
    Function.update_apply, vya, vsn, vhc, vac, vhv, vprm]; done)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      simp [τ, bandFB1, bandFF2, bandFF2a, bandFF2b, bandFF2c, bandFF2d, bandFF1,
        vclr]

/-- The scratch registers of the loader are empty. -/
structure BandPreFree (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) : Prop where
  ya : σ (.inl .ya) = []
  b1 : σ (.inl .b1) = []
  tb : σ (.inl .tb) = []
  xa : σ (.inl .xa) = []
  xs : σ (.inl .xs) = []
  pr : σ (.inl .pr) = []
  hc : σ (.inl .hc) = []
  ac : σ (.inl .ac) = []
  hv : σ (.inl .hv) = []
  tL : σ (.inl .tL) = []
  ac2 : σ (.inl .ac2) = []
  nv : σ (.inl .nv) = []
  tA : σ (.inl .tA) = []
  tJ : σ (.inl .tJ) = []
  dst : σ (.inl .dst) = []
  tC : σ (.inl .tC) = []
  tK : σ (.inl .tK) = []
  sr : σ (.inl .sr) = []
  sel : σ (.inl .sel) = []
  ef : σ (.inl .ef) = []
  dout : σ (.inl .dout) = []
  vk : σ (.inl .vk) = []
  vx : ∀ j, σ (.inr (.vx j)) = []
  cm : ∀ c, c ≠ .xs → c ≠ .ys → c ≠ .out → c ≠ .wn → c ≠ .pn → c ≠ .nn → σ (.inl (.cm c)) = []

/-- The conditions on the parameters of an axis. -/
structure BandPreOk (D : PreAxB) (w : ℕ) : Prop where
  fold : BandFoldW D
  wW : w ≤ D.W
  p13 : 13 ≤ D.p
  α2 : 2 ≤ D.α
  αp : D.α ^ 2 ≤ D.p
  s0 : 0 < D.s
  st : D.s < D.t
  W : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W
  pW : 9 * D.p + 1 < D.W
  Pw : D.bP ≤ w
  fD : ∀ ℓ : ZMod D.s, Fits w (rsbReal (tableD D.s D.t D.α D.p ℓ))
  fc : Fits w (⟨2 ^ (9 * D.p), 0⟩ : GaussianInt)

/-- The step bound of the loader. -/
def bandPreCost (T : ℕ) (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (w : ℕ) (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) : ℕ :=
  bandCostB1 σ hd w D + (bandCostB2a D w + (bandCostB2b T (bandFB2a (bandFB1 σ hd w D rest) D w) D w +
    (bandAxisPrepCost T w (2 * D.bWd) D.bK D.s +
      bandCostE (bandFP (bandFB2b (bandFB2a (bandFB1 σ hd w D rest) D w) D w) D w (σ (.inl .src))))))

set_option maxRecDepth 4000 in
/-- **The loader of the banded `B̃₀`.** -/
theorem band_preB_runs (hrg₂ : Function.Injective (Sum.elim rg rgx)) (hι : Function.Injective ι)
    (hdisj₂ : ∀ r j, Sum.elim rg rgx r ≠ ι j) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ prime + K) {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd)
    (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) [NeZero D.s]
    (rest : List (Fin (prime + K + 4))) (w : ℕ) (hw : 1 ≤ w) (hok : BandPreOk D w)
    (hF : BandPreFree σ) (hprm : σ (.inl .prm) = preRec D.fields ++ rest)
    (hwn : (σ (.inl (.cm .wn))).length = w)
    (hnn : (σ (.inl (.cm .nn))).length = IntegerMultBounds.Schoenhage.Schedule.topN w)
    (hfit : ∀ m < D.s, FacFits w D.bP D.bK (facState D.bP D.bK
      (bandRows D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP))
      (bandInputs D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP)) m)) :
    RsbRuns body (Sum.elim rg rgx) ι (bandPreB rg rgx ι hd hι hT hQ) σ (bandLoad σ hd w D rest)
      (bandPreCost T σ hd w D rest) := by
  have hp1 : 1 ≤ D.p := by have := hok.p13; omega
  have hjp : D.α * D.α ≤ D.p := by have := hok.αp; nlinarith
  obtain ⟨-, -, -, -, -, -, hWM⟩ := pre_W_facts hok.α2 hok.s0 hok.st hok.W
  have hsw := hok.fold.ws
  have h1 := band_preB1 (body := body) hrg₂ hι hdisj₂ hdi σ D rest w hok.wW hok.fold hp1 hprm hwn
    hF.ya hF.b1 hF.tb hF.xa hF.xs hF.pr hF.hc hF.ac hF.hv hF.tL hF.ac2 hF.nv hF.tA hF.tJ hF.dst hF.tC
    hF.tK hF.vx
  obtain ⟨vpn, vya, vsn, vhc, vac, vhv, vxs, vms, vm2n, vdst, vm2wn, vmwn, vsmwn, vtswn, vkn, vmsk,
    vbx, vsrc, -, vclr⟩ := bandFB1_vals σ hd w D rest
  have hvx1 : ∀ j, bandFB1 σ hd w D rest (.inr (.vx j)) = [] := fun j => by
    rw [bandFB1_vx]; exact hF.vx j
  set τ1 := bandFB1 σ hd w D rest with hτ1
  have f1 : ∀ r, r ∉ bandLB1 → τ1 (.inl r) = σ (.inl r) := bandFB1_frame σ hd w D rest
  have h2 := band_preB2a (body := body) hrg₂ hι hdisj₂ τ1 D w hok.wW hp1 (by have := hok.pW; omega)
    hjp hok.s0 hok.st hWM (by rw [f1 _ (by decide)]; exact hwn) vya vsn vac vhv vxs
    (vclr _ (by simp)) (by rw [f1 _ (by decide)]; exact hF.tC) (by rw [f1 _ (by decide)]; exact hF.tK)
    (by rw [f1 _ (by decide)]; exact hF.ac2) (by rw [f1 _ (by decide)]; exact hF.nv)
    (by rw [f1 _ (by decide)]; exact hF.sr) (by rw [f1 _ (by decide)]; exact hF.sel)
    hvx1
  set τ2 := bandFB2a τ1 D w with hτ2
  have f2 : ∀ r, r ≠ .padc → τ2 (.inl r) = τ1 (.inl r) := bandFB2a_frame τ1 D w
  have hcm : ∀ c, c ≠ .xs → c ≠ .ys → c ≠ .out → c ≠ .wn → c ≠ .pn → c ≠ .nn →
      τ2 (.inl (.cm c)) = [] := by
    intro c h1 h2 h3 h4 h5 h6
    rw [f2 _ (by simp), f1 _ (by simp [bandLB1, bandLA, h5])]
    exact hF.cm c h1 h2 h3 h4 h5 h6
  have hready2 : RsbReady (fun r => τ2 (.inl r)) w D.bP :=
    ⟨by rw [f2 _ (by simp), f1 _ (by decide)]; exact hwn,
      by rw [f2 _ (by simp), vpn]; simp,
      by rw [f2 _ (by simp), f1 _ (by decide)]; exact hnn, hcm⟩
  have h3 := band_preB2b (body := body) hrg₂ hι hdisj₂ hT hQ hA τ2 D w hok.wW hok.pW hready2 hw hok.Pw
    hok.p13 hok.α2 hok.αp hok.s0 hok.st hok.W hok.fD hok.fc
    (by rw [f2 _ (by decide)]; exact vya) (by rw [f2 _ (by decide)]; exact vsn)
    (by rw [f2 _ (by decide)]; exact vhc) (by rw [f2 _ (by decide)]; exact vac)
    (by rw [f2 _ (by decide)]; exact vhv)
    (by rw [f2 _ (by decide), f1 _ (by decide)]; exact hF.ef)
    (by rw [f2 _ (by decide), f1 _ (by decide)]; exact hF.tb)
    (by rw [f2 _ (by decide)]; exact vclr _ (by simp))
    (by rw [f2 _ (by decide), f1 _ (by decide)]; exact hF.tC)
    (by rw [f2 _ (by decide), f1 _ (by decide)]; exact hF.ac2)
  set τ3 := bandFB2b τ2 D w with hτ3
  have f3 : ∀ r, r ∉ [RsbR.tb, .ya, .b1, .hc, .ac, .hv, .xs, .tA, .tJ, .tL, .dtab] →
      τ3 (.inl r) = τ2 (.inl r) := bandFB2b_frame τ2 D w
  have s3 : ∀ r, r ∈ [RsbR.tb, .ya, .b1, .hc, .ac, .hv, .xs, .tA, .tJ, .tL] → τ3 (.inl r) = [] :=
    bandFB2b_scr τ2 D w
  have g3 : ∀ r, r ∉ [RsbR.tb, .ya, .b1, .hc, .ac, .hv, .xs, .tA, .tJ, .tL, .dtab] → r ≠ .padc →
      r ∉ bandLB1 → τ3 (.inl r) = σ (.inl r) := fun r h1 h2 h3 => by
    rw [f3 r h1, f2 r h2, f1 r h3]
  have hready3 : RsbReady (fun r => τ3 (.inl r)) w D.bP :=
    ⟨by rw [f3 _ (by decide)]; exact hready2.wn, by rw [f3 _ (by decide)]; exact hready2.pn,
      by rw [f3 _ (by decide)]; exact hready2.nn,
      fun c h1 h2 h3 h4 h5 h6 => by rw [f3 _ (by simp)]; exact hcm c h1 h2 h3 h4 h5 h6⟩
  have e3 : ∀ r, r ∉ [RsbR.tb, .ya, .b1, .hc, .ac, .hv, .xs, .tA, .tJ, .tL, .dtab] → r ≠ .padc →
      τ3 (.inl r) = τ1 (.inl r) := fun r h1 h2 => by rw [f3 r h1, f2 r h2]
  have h4 := band_preP (body := body) hrg₂ hdisj₂ hι hT hQ hA τ3 D w hready3 hw hok.Pw hsw hfit
    (by rw [e3 _ (by decide) (by decide)]; exact vbx) (σ (.inl .src))
    (by rw [e3 _ (by decide) (by decide)]; exact vsrc)
    (by rw [e3 _ (by decide) (by decide), vtswn]; simp)
    (by rw [e3 _ (by decide) (by decide)]; exact vclr _ (by simp))
    (by rw [e3 _ (by decide) (by decide)]; exact vclr _ (by simp))
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hF.dout)
    (by rw [e3 _ (by decide) (by decide), vmsk, csyms_zero'])
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hF.vk)
    (by simp only [hτ3, bandFB2b, bandScrL]; simp; rw [f2 _ (by decide), f1 _ (by decide)]; exact hF.ef)
    (s3 _ (by simp))
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hF.sr)
    (by rw [e3 _ (by decide) (by decide)]; exact vclr _ (by simp))
    (s3 _ (by simp))
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hF.xa)
    (s3 _ (by simp)) (s3 _ (by simp)) (s3 _ (by simp))
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hF.pr)
    (s3 _ (by simp))
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hF.ac2)
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hF.nv)
    (s3 _ (by simp))
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hF.tC)
    (s3 _ (by simp)) (s3 _ (by simp))
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hF.tK)
    (s3 _ (by simp))
    (by rw [g3 _ (by decide) (by decide) (by decide)]; exact hF.sel)
    (by rw [e3 _ (by decide) (by decide), vsn]; simp)
    (by rw [e3 _ (by decide) (by decide), vkn]; simp [PreAxB.bK])
    (by rw [e3 _ (by decide) (by decide), vms]; simp)
    (by rw [e3 _ (by decide) (by decide), vm2n]; simp)
    (by rw [e3 _ (by decide) (by decide), vmwn]; simp)
    (by rw [e3 _ (by decide) (by decide), vsmwn]; simp)
    (by rw [e3 _ (by decide) (by decide), vm2wn]; simp)
    (by rw [e3 _ (by decide) (by decide), vdst]; simp)
  have h5 := rsb_of_tw (ι := ι) (band_preE (body := body) hrg₂ (bandFP τ3 D w (σ (.inl .src)))
    (by simp only [bandFP, Function.update_apply, Sum.inl.injEq, reduceCtorEq, ite_false]
        rw [g3 _ (by decide) (by decide) (by decide)]; exact hF.ac2))
  exact RsbRuns.seq hdisj₂ h1 (RsbRuns.seq hdisj₂ h2 (RsbRuns.seq hdisj₂ h3
    (RsbRuns.seq hdisj₂ h4 h5)))

end Whole


/-! ### The loaded configuration -/

section Cfg

variable {body : F → Pr F T Q (prime + K) U}

theorem tdivN_dscale (p : ℕ) (d : ℤ) :
    tdivN (5 * p) (rsbReal d * ⟨2 ^ (9 * p), 0⟩) = rsbReal (d * 2 ^ (4 * p)) := by
  have e : (2 : ℤ) ^ (9 * p) = 2 ^ (4 * p) * 2 ^ (5 * p) := by rw [← pow_add]; congr 1; ring
  ext <;> simp [tdivN, rsbReal, Zsqrtd.re_mul, Zsqrtd.im_mul, e, ← mul_assoc,
    Int.mul_tdiv_cancel _ (show (2 : ℤ) ^ (5 * p) ≠ 0 by positivity)]

/-- The diagonal table of an axis at precision `5p`: `D · 2^(4p)`. -/
noncomputable def bandDl (D : PreAxB) [NeZero D.s] : List ℤ :=
  rsbArr fun ℓ : ZMod D.s => tableD D.s D.t D.α D.p ℓ * 2 ^ (4 * D.p)

theorem bandFE_frame (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (r : RsbR)
    (hr : r ∉ [RsbR.kn, .ms, .dst, .msk, .tswn, .smwn, .m2wn, .bx, .ac2]) :
    bandFE σ (.inl r) = σ (.inl r) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [bandFE, bandMvF, bandFE0, bandClrE, bvx, hr]

set_option maxRecDepth 4000 in
theorem bandFE_vals (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (hac2 : σ (.inl .ac2) = []) :
    bandFE σ (.inl .msk) = σ (bvx 0) ∧ bandFE σ (.inl .smwn) = σ (bvx 1) ∧
    bandFE σ (.inl .bx) = σ (bvx 2) ∧ bandFE σ (.inl .tswn) = (σ (bvx 3)).reverse ∧
    bandFE σ (.inl .m2wn) = (σ (bvx 4)).reverse ∧ bandFE σ (.inl .kn) = (σ (bvx 5)).reverse ∧
    bandFE σ (.inl .ms) = [] ∧ bandFE σ (.inl .dst) = [] ∧ bandFE σ (.inl .ac2) = [] := by
  simp (config := { decide := true }) [bandFE, bandMvF, bandFE0, bandClrE, bvx,
    hac2]

theorem bandFP_frame (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) [NeZero D.s]
    (w : ℕ) (l : List (Fin (prime + K + 4))) (r : RsbR)
    (hr : r ∉ [RsbR.src, .bo, .hf, .df, .dout, .vk, .m2n, .kn, .ms, .mwn, .ef, .xs]) :
    bandFP σ D w l (.inl r) = σ (.inl r) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [bandFP, hr]

theorem bandFP_inr (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) [NeZero D.s]
    (w : ℕ) (l : List (Fin (prime + K + 4))) (x : RsbX t₀) :
    bandFP σ D w l (.inr x) = σ (.inr x) := by
  simp [bandFP]

theorem bandFB2b_inr (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (D : PreAxB) [NeZero D.s]
    (w : ℕ) (x : RsbX t₀) : bandFB2b σ D w (.inr x) = σ (.inr x) := by
  simp [bandFB2b, bandScrL]

set_option maxRecDepth 4000 in
/-- **The loaded register file is configured for the banded line of its axis.** -/
theorem bandLoad_cfg (σ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (D : PreAxB) [NeZero D.s] (rest : List (Fin (prime + K + 4))) (w : ℕ) (hF : BandPreFree σ)
    (hwn : (σ (.inl (.cm .wn))).length = w)
    (hnn : (σ (.inl (.cm .nn))).length = IntegerMultBounds.Schoenhage.Schedule.topN w)
    (hA3 : 3 ≤ prime + K) :
    BandAxisCfg (fun r => bandLoad σ hd w D rest (.inl r)) w D.bP D.s D.t D.bB
      (bandLc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP))
      (bandUc D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP))
      (bandRcs D.bP D.bK D.bWd D.s (Mult.BandFactor.coefZ D.s D.t D.α D.bP)) (bandDl D)
      (2 ^ (9 * D.p - 1)) (2 ^ (D.p - D.α * D.α)) := by
  obtain ⟨vpn, vya, vsn, vhc, vac, vhv, vxs, vms, vm2n, vdst, vm2wn, vmwn, vsmwn, vtswn, vkn, vmsk,
    vbx, vsrc, -, vclr⟩ := bandFB1_vals σ hd w D rest
  set τ1 := bandFB1 σ hd w D rest with hτ1
  have f1 : ∀ r, r ∉ bandLB1 → τ1 (.inl r) = σ (.inl r) := bandFB1_frame σ hd w D rest
  set τ2 := bandFB2a τ1 D w with hτ2
  have f2 : ∀ r, r ≠ .padc → τ2 (.inl r) = τ1 (.inl r) := bandFB2a_frame τ1 D w
  set τ3 := bandFB2b τ2 D w with hτ3
  have f3 : ∀ r, r ∉ [RsbR.tb, .ya, .b1, .hc, .ac, .hv, .xs, .tA, .tJ, .tL, .dtab] →
      τ3 (.inl r) = τ2 (.inl r) := bandFB2b_frame τ2 D w
  have s3 : ∀ r, r ∈ [RsbR.tb, .ya, .b1, .hc, .ac, .hv, .xs, .tA, .tJ, .tL] → τ3 (.inl r) = [] :=
    bandFB2b_scr τ2 D w
  set τ4 := bandFP τ3 D w (σ (.inl .src)) with hτ4
  have f4 : ∀ r, r ∉ [RsbR.src, .bo, .hf, .df, .dout, .vk, .m2n, .kn, .ms, .mwn, .ef, .xs] →
      τ4 (.inl r) = τ3 (.inl r) := bandFP_frame τ3 D w (σ (.inl .src))
  have hac2 : τ4 (.inl .ac2) = [] := by
    rw [f4 _ (by decide), f3 _ (by decide), f2 _ (by decide), f1 _ (by decide)]; exact hF.ac2
  obtain ⟨emsk, esmwn, ebx, etswn, em2wn, ekn, ems, edst, eac2⟩ := bandFE_vals τ4 hac2
  have f5 : ∀ r, r ∉ [RsbR.kn, .ms, .dst, .msk, .tswn, .smwn, .m2wn, .bx, .ac2] →
      bandFE τ4 (.inl r) = τ4 (.inl r) := bandFE_frame τ4
  have hL : ∀ r, bandLoad σ hd w D rest (.inl r) = bandFE τ4 (.inl r) := fun r => rfl
  have vx4 : ∀ j, τ4 (bvx j) = τ2 (bvx j) := fun j => by
    simp only [bvx, hτ4, bandFP_inr, hτ3, bandFB2b_inr]
  -- the generic route of an untouched register
  have gL : ∀ r, r ∉ [RsbR.kn, .ms, .dst, .msk, .tswn, .smwn, .m2wn, .bx, .ac2] →
      r ∉ [RsbR.src, .bo, .hf, .df, .dout, .vk, .m2n, .kn, .ms, .mwn, .ef, .xs] →
      r ∉ [RsbR.tb, .ya, .b1, .hc, .ac, .hv, .xs, .tA, .tJ, .tL, .dtab] → r ≠ .padc → r ∉ bandLB1 →
      bandLoad σ hd w D rest (.inl r) = σ (.inl r) := fun r h5 h4 h3 h2 h1 => by
    rw [hL, f5 r h5, f4 r h4, f3 r h3, f2 r h2, f1 r h1]
  have zL : ∀ r, r ∉ [RsbR.kn, .ms, .dst, .msk, .tswn, .smwn, .m2wn, .bx, .ac2] →
      r ∉ [RsbR.src, .bo, .hf, .df, .dout, .vk, .m2n, .kn, .ms, .mwn, .ef, .xs] →
      r ∈ [RsbR.tb, .ya, .b1, .hc, .ac, .hv, .xs, .tA, .tJ, .tL] →
      bandLoad σ hd w D rest (.inl r) = [] := fun r h5 h4 h3 => by
    rw [hL, f5 r h5, f4 r h4, s3 r h3]
  have dL : ∀ r, r ∈ [RsbR.dout, .vk, .ef, .xs] → bandLoad σ hd w D rest (.inl r) = [] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rw [hL, f5 _ (by decide)] <;> simp [hτ4, bandFP]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gL _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwn
  · rw [hL, f5 _ (by decide), f4 _ (by decide), f3 _ (by decide), f2 _ (by decide), vpn]
    simp
  · rw [gL _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hnn
  · intro c h1 h2 h3 h4 h5 h6
    rw [gL _ (by simp) (by simp) (by simp) (by simp) (by simp [bandLB1, bandLA, h5])]
    exact hF.cm c h1 h2 h3 h4 h5 h6
  · rw [hL]; exact edst
  · rw [hL, emsk, vx4]
    simp [hτ2, bandFB2a, bvx, preMaskE_map hA3]
  · rw [hL, esmwn, vx4]
    simp [hτ2, bandFB2a, bvx, tblPairs_csyms]
  · rw [hL, ebx, vx4]
    simp [hτ2, bandFB2a, bvx, tblPairs_csyms]
  · rw [hL, f5 _ (by decide)]; simp [hτ4, bandFP]
  · rw [hL, f5 _ (by decide)]; simp [hτ4, bandFP]
  · rw [hL, f5 _ (by decide)]; simp [hτ4, bandFP]
  · rw [hL, f5 _ (by decide), f4 _ (by decide)]
    simp only [hτ3, bandFB2b, bandScrL]
    have hdsc : ∀ d : ℤ, tdivN (5 * D.p) ((⟨d, 0⟩ : GaussianInt) * ⟨2 ^ (9 * D.p), 0⟩) =
        ⟨d * 2 ^ (4 * D.p), 0⟩ := fun d => tdivN_dscale D.p d
    simp [bandDl, rsbArr, List.map_map, Function.comp_def, hdsc, PreAxB.bP, rsbReal]
  · rw [hL, f5 _ (by decide), f4 _ (by decide), f3 _ (by decide)]
    simp [hτ2, bandFB2a]
  · rw [hL, etswn, vx4]; simp [hτ2, bandFB2a, bvx]
  · rw [hL, em2wn, vx4]; simp [hτ2, bandFB2a, bvx]
  · rw [hL, ekn, vx4]; simp [hτ2, bandFB2a, bvx]
  · rw [hL, f5 _ (by decide), f4 _ (by decide), f3 _ (by decide), f2 _ (by decide), vsn]
    simp
  · rw [hL, f5 _ (by decide)]
    simp only [hτ4, bandFP, Function.update_apply, Sum.inl.injEq, reduceCtorEq, ite_true, ite_false]
    simp only [List.length_append, PreAxB.bB]
    rw [f3 (.cm .wn) (by decide), f2 _ (by decide), f1 _ (by decide), hwn,
      f3 .m2wn (by decide), f2 _ (by decide), vm2wn]
    simp; ring
  · rw [hL, f5 _ (by decide)]
    simp only [hτ4, bandFP, Function.update_apply, Sum.inl.injEq, reduceCtorEq, ite_true, ite_false]
    rw [f3 _ (by decide), f2 _ (by decide), vms]; simp
  · rw [hL]; exact ems
  all_goals first
    | (exact dL _ (by decide))
    | (exact zL _ (by decide) (by decide) (by decide))
    | (rw [hL]; exact eac2)
    | (rw [gL _ (by decide) (by decide) (by decide) (by decide) (by decide)]
       first
         | exact hF.sr | exact hF.sel | exact hF.nv | exact hF.tK | exact hF.tC | exact hF.pr
         | exact hF.xa)

end Cfg

end

end IntegerMultBounds.MathlibTM2.Fast
