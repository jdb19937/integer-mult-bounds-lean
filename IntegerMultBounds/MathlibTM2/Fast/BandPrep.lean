module

public import IntegerMultBounds.MathlibTM2.Fast.BandPrepVM
public import IntegerMultBounds.MathlibTM2.Fast.BandAxis

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
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

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
  rw [preLayB_map hg hι hdisj] at h1
  have h1' := twRuns_congr h1
    (show _ = preStB (bandF0 σ hd) by
      funext r; rcases r with r | y
      · simp only [preStB, bandF0, Sum.elim_inl, List.mem_map]
        by_cases h : r ∈ bandClrB hd
        · simp [h]
        · have : ¬∃ a, a ∈ bandClrB hd ∧ Sum.inl a = (Sum.inl r : (RsbR ⊕ RsbX t₀) ⊕ TblR 48) := by
            rintro ⟨a, ha, e⟩; cases e; exact h ha
          simp [h, this]
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
  rw [preLayB_map hg hι hdisj] at h2
  set σ2 := preTV (.inl .prm) bandDstB D.fields rest σ1 with hσ2
  have h2' := twRuns_congr h2 (show _ = preStB σ2 by
    simp only [hσ2, preTV, bandDstB, PreAxB.fields, List.map_cons, List.map_nil, List.zip_cons_cons,
      List.zip_nil_left, List.foldl_cons, List.foldl_nil, preStB, Sum.update_elim_inl])
  -- 3. the headers
  have hv2 : σ2 (.inl .xs) = List.replicate D.P tick ∧ σ2 (.inl .pr) = List.replicate D.G tick ∧
      σ2 (.inl .tb) = List.replicate D.L tick ∧ σ2 (.inl .xa) = List.replicate D.Ld tick := by
    simp [hσ2, preTV, bandDstB, PreAxB.fields, Function.update_apply]
  have h3 := preB_hdr (body := body) hg hι hdisj hdi σ2 D w hv2.1 hv2.2.1 hv2.2.2.1 hv2.2.2.2
    (by simp [hσ2, preTV, bandDstB, PreAxB.fields, Function.update_apply, hσ1, bandF0, bandClrB,
      preHB, hwn])
    (by simp [hσ2, preTV, bandDstB, PreAxB.fields, Function.update_apply, hσ1, bandF0, bandClrB,
      preHB, htL])
    (by simp [hσ2, preTV, bandDstB, PreAxB.fields, Function.update_apply, hσ1, bandF0, bandClrB,
      preHB, hac2])
    (by simp [hσ2, preTV, bandDstB, PreAxB.fields, Function.update_apply, hσ1, bandF0, bandClrB,
      preHB, hnv])
    (fun k => by
      simp [hσ2, preTV, bandDstB, PreAxB.fields, Function.update_apply, hσ1, bandF0, bandClrB,
        preHB]
      fin_cases k <;> simp)
  -- 4. clear the header fields
  set σ3 := preBankB σ2 hd (D.hs w) with hσ3
  have h4 := preClears_runs (body := body) htg
    (([.inl .tb, .inl .xa, .inl .xs, .inl .pr] : List (RsbR ⊕ RsbX t₀)).map Sum.inl)
    (by simp) (preStB σ3)
  rw [preLayB_map hg hι hdisj] at h4
  refine twRuns_congr (twRuns_mono (twRuns_seq h1' (twRuns_seq h2' (twRuns_seq h3 h4))) ?_) ?_
  · simp only [List.map_map, Function.comp_def, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, preStB, Sum.elim_inl, hσ3]
    simp [preBankB, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2, bandCostA, PreAxB.fields]
    omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp [preStB, hσ3, hσ2, hσ1, bandFA, preBankB, preTV, bandDstB, PreAxB.fields,
        Function.update_apply, bandF0, bandClrB, preHB, htb, hxa, hxs, hpr]
    · have hx : σ2 (.inr x) = (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update (bandF0 σ hd) (.inl .prm) rest)
          (.inl .ya) (List.replicate D.t tick)) (.inl .sn) (List.replicate D.s tick))
          (.inl .b1) (List.replicate D.m tick)) (.inl .hc) (List.replicate D.α tick))
          (.inl .ac) (List.replicate D.p tick)) (.inl .hv) (List.replicate D.W tick)) (.inr x) := by
        simp [hσ2, hσ1, preTV, bandDstB, PreAxB.fields, Function.update_apply]
      simp only [preStB, Sum.elim_inl]
      rw [if_neg (by simp)]
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

lemma rep_append_rep {A : ℕ} (a b : ℕ) :
    List.replicate a (tick : Fin (A + 4)) ++ List.replicate b tick = List.replicate (a + b) tick := by
  rw [List.replicate_add]

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
    reduceCtorEq, ite_false, ite_true, RsbR.cm.injEq, hac2]; done)
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, RsbR.cm.injEq, hac, hb1, hsn, htA, htJ, htL, hxs, hpn, List.length_replicate,
      List.length_cons, List.append_nil, List.length_append]
    unfold bandCostF1 PreAxB.bB PreAxB.bWd
    omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, bandFF1, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true, RsbR.cm.injEq]
      all_goals simp [hac, hb1, hsn, htA, htJ, htL, hxs, hpn, List.replicate_succ,
        ← List.replicate_add, PreAxB.bB, PreAxB.bWd, PreAxB.bP]
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
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [hv]; simp (config := { decide := true }) [Function.update_apply])
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
    reduceCtorEq, ite_false, ite_true, RsbR.cm.injEq, hac2]; done)
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, RsbR.cm.injEq, hxs, htA, htJ, List.length_replicate]
    unfold bandCostF2a; omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, bandFF2a, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true, RsbR.cm.injEq]
      all_goals simp [htA, htJ, hms, hm2n, hdst, Nat.mul_comm]
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
    reduceCtorEq, ite_false, ite_true, RsbR.cm.injEq, hac2, hnv]; done)
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, RsbR.cm.injEq, hwn, hdst, hm2n, htL, List.length_replicate]
    unfold bandCostF2b; omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, bandFF2b, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true, RsbR.cm.injEq]
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
    reduceCtorEq, ite_false, ite_true, RsbR.cm.injEq, hac2, hnv]; done)
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, RsbR.cm.injEq, hwn, htJ, htL, htC, htK, List.length_replicate, List.length_cons,
      List.append_nil, List.length_append]
    unfold bandCostF2c; ring_nf; omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, bandFF2c, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true, RsbR.cm.injEq]
      all_goals simp [hwn, htJ, htL, htswn, htC, htK]
      all_goals (rw [List.eq_replicate_iff]; refine ⟨by simp; ring, by simp⟩)
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
    reduceCtorEq, ite_false, ite_true, RsbR.cm.injEq, hac2, hnv]; done)
  · simp only [preStB, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false,
      ite_true, RsbR.cm.injEq, hwn, hhc, hxs, htC, List.length_replicate, List.append_nil]
    unfold bandCostF2d; omega
  · funext r
    rcases r with (r | x) | y
    · cases r <;> simp only [Function.update_apply, preStB, bandFF2d, Sum.elim_inl, Sum.inl.injEq,
        reduceCtorEq, ite_false, ite_true, RsbR.cm.injEq]
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


end

end IntegerMultBounds.MathlibTM2.Fast
