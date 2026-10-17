module

public import IntegerMultBounds.MathlibTM2.Fast.ChirpStage
public import IntegerMultBounds.MathlibTM2.Fast.TablePhaseChirp
public import IntegerMultBounds.MathlibTM2.Fast.TableLoad
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The chirp table loader of the chirp stage

The chirp stage `cstChirpBox` (`IntegerMultBounds.MathlibTM2.Fast.ChirpStage`) takes a loader `prep` that, run with
axis `k` pending, puts the chirp table of axis `k` onto `ys` and `t_k` ticks onto `cL`. This file
builds that loader from the chirp table machine `tblChirpCode` (`IntegerMultBounds.MathlibTM2.Fast.TablePhaseChirp`)
and states the stage without a loader hypothesis.

## Registers and streams

The caller registers are `ldcX`: the 96 table-machine registers `tbl r` (`r : TblR 84`, layout
`ldcTl rg`), the description streams `tS`, `sS`, the unary parameters `pU`, `gU`, `wU`, and the
unary registers `tU`, `sU` of the current axis.

* **Stream format** (`ldcBlocks`): a list of values `m₀, m₁, …` is stored as `m₀` ticks, one
  `bitSymbol false`, `m₁` ticks, one `bitSymbol false`, …, the first value on top. `tS` holds
  `ldcBlocks (List.ofFn t)` (axis lengths), `sS` holds `ldcBlocks (List.ofFn s)` (chirp steps);
  each axis consumes one block of each.
* **Unary registers**: `pU`, `gU`, `wU` hold `p`, `g`, `w` symbols (any); `tU`, `sU` are empty
  between axes.
* **Table registers** are idle between axes (`ldcIdle wl nl`): `wr` holds `W` symbols (the word
  width), `wn` holds `w` symbols (the emission width), every variable, `acc` and every scratch
  register is empty.

## The loader

`ldcPrep rg` (one fixed program): `ldcPopBlock` moves the leading ticks of `tS` onto `tU` and
drops the delimiter (`ldc_popBlock_exec`, `2 m + 3` steps), likewise `sS` onto `sU`; the 84
variables become `binSyms W 0` (`zeroBits` from `wr`, `ldc_zero_runs`); `tblLoad1` loads
`p, g, t_k, s_k, w` from `pU, gU, tU, sU, wU` into the variables `54 … 58` (`ldc_load_runs`);
`tblHost` runs `tblChirpCode` onto `ys` and the 84 variables are emptied
(`ldc_hostClear_runs`); `tU` moves onto `cL`; `sU` is emptied.

* `ldc_cstream_axTab`: the stream of the table of axis `k` is the chirp axis stream,
  `cstream A w (cstTab (List.ofFn t) (cstAxTab p g t s) k) = tblChirpStream A w p g t_k s_k`.
* `ldc_prep_runs`: one axis on an explicit register file; `ldc_prep_hprep`: the loader contract
  `hprep` of `cst_chirpBox_pipeline` for the caller files `ldcCfg xx (List.ofFn t)
  (List.ofFn s) k` (the streams with the first `k` blocks consumed) and `cnt k = t_k` ticks.
* `ldChirpStage_exec`: the instance `cst_chirpBox_kernel` (the chirp kernel
  `Pipeline.chirpKernel n` at the `Mult.Sizes` parameters `p n`, `chirpGuard (d n)`, `t n`,
  `s n`) with `prep := ldcPrep rg` and no loader hypothesis; `kr` gains the numerator box of the
  kernel, `tS` and `sS` end empty, every other register ends as it started.

**Conditions** (per axis, from `tblChirp_do`): `w < W`, `s_k t_k² < 2^W`,
`8 (p + g) + size t_k + 80 ≤ W`; `0 < t_k` holds for the pipeline lengths.

## Costs

* `ldcAxisCost W w p g t_k s_k`: one axis; `ldc_axisCost_le` bounds it by
  `(t_k (39 (p + g) + 641) + 200 (p + g) + 4 w + 1503) · tblC W w + 2 t_k w +
  2 (p + g + t_k + s_k + w) (4 W + 10) + 534 W + 568`, `tblC W w = 32 (W + 4)² + 8 w`.
* `ldChirpStage_cost_le`: the stage costs at most `∑_{k<d} ldcAxisCost … + 4 d V cmulCost T w`,
  `V = ∏ t_k`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ChirpSt

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.TableNum IntegerMultBounds.MathlibTM2.Mult.Chirp


noncomputable section

/-! ### Delimited unary blocks -/

section Block

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- Record in `flag` whether the top of register `i` is a tick. -/
def ldcTopTick (i : Fin T) : Act T Q A U :=
  .peek (.rt i) (fun v o => { v with flag := decide (o = some tick) }) .done

/-- Move the top of register `i` onto register `j`, then test the new top of `i`. -/
def ldcTickStep (i j : Fin T) : Act T Q A U :=
  .pop (.rt i) (fun v o => { v with sym := o })
    (.push (.rt j) (fun v => v.sym.getD blank) (ldcTopTick i))

/-- Move the leading ticks of register `i` onto register `j`, then drop the delimiter. -/
def ldcPopBlock (i j : Fin T) : Pr P T Q A U :=
  .seq (.act (ldcTopTick i))
    (.seq (.loop (·.flag) (.act (ldcTickStep i j))) (.act (dropTop i .done)))

lemma ldc_tick_ne : (tick : Fin (A + 4)) ≠ bitSymbol false := by
  simp [tick, bitSymbol, Fin.ext_iff]

theorem ldc_tickLoop (i j : Fin T) (hij : i ≠ j) (rest : List (Fin (A + 4))) :
    ∀ (m : ℕ) (v : HS T Q A U) (S : Stacks T A),
      S.R i = List.replicate m tick ++ bitSymbol false :: rest →
      v.flag = decide ((S.R i).head? = some tick) →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (ldcTickStep i j))) (mk v S) (2 * m + 1)
          (mk v' { S with
            R := Function.update (Function.update S.R i (bitSymbol false :: rest)) j
              (List.replicate m tick ++ S.R j) }) := by
  intro m
  induction m with
  | zero =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have e : ({ S with
                  R := Function.update (Function.update S.R i (bitSymbol false :: rest)) j
                    (List.replicate 0 tick ++ S.R j) } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          by_cases hk : k = j
          · subst hk; simp
          · by_cases hk' : k = i
            · subst hk'; simp [hk, hS]
            · simp [hk, hk']
      rw [e]
      refine .loop_false ?_
      rw [mk_var, hf, hS]
      simp [Ne.symm ldc_tick_ne]
  | succ m ih =>
      intro v S hS hf
      have hS' : S.R i = tick :: (List.replicate m tick ++ bitSymbol false :: rest) := by
        rw [hS, List.replicate_succ, List.cons_append]
      obtain ⟨v', hu, he⟩ := ih
        { v with
          sym := some tick,
          flag := decide ((List.replicate m tick ++ bitSymbol false :: rest).head? = some tick) }
        { S with
          R := Function.update (Function.update S.R i
            (List.replicate m tick ++ bitSymbol false :: rest)) j (tick :: S.R j) }
        (by simp [Function.update_of_ne hij]) (by simp [Function.update_of_ne hij])
      refine ⟨v', hu, ?_⟩
      have hrun : (ldcTickStep i j : Act T Q A U).run (mk v S) =
          mk
            { v with
              sym := some tick,
              flag := decide ((List.replicate m tick ++ bitSymbol false :: rest).head? = some tick) }
            { S with
              R := Function.update (Function.update S.R i
                (List.replicate m tick ++ bitSymbol false :: rest)) j (tick :: S.R j) } := by
        simp [ldcTickStep, ldcTopTick, Action.run, hS', update_rt, Function.update_of_ne hij,
          Function.update_of_ne hij.symm]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) ?_
        (hrun ▸ Exec.act (body := body) (ldcTickStep i j) (mk v S)) he) (by ring) ?_
      · simp only [mk_var]; rw [hf, hS']; simp
      · congr 2
        funext k
        by_cases hk : k = j
        · subst hk; simp [List.replicate_succ']
        · by_cases hk' : k = i
          · subst hk'; simp [hk]
          · simp [hk, hk']

/-- `ldcPopBlock i j`: the block of `m` ticks moves onto `j` and the delimiter is dropped, in
`2 m + 3` steps. -/
theorem ldc_popBlock_exec (i j : Fin T) (hij : i ≠ j) (m : ℕ) (rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R i = List.replicate m tick ++ bitSymbol false :: rest) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (ldcPopBlock i j) (mk v S) (2 * m + 3)
        (mk v' { S with
          R := Function.update (Function.update S.R i rest) j
            (List.replicate m tick ++ S.R j) }) := by
  have h0 := Exec.act (body := body) (ldcTopTick i) (mk v S)
  have hr0 : (ldcTopTick i : Act T Q A U).run (mk v S) =
      mk { v with flag := decide ((S.R i).head? = some tick) } S := rfl
  rw [hr0] at h0
  obtain ⟨v₁, hu₁, he₁⟩ := ldc_tickLoop body i j hij rest m
    { v with flag := decide ((S.R i).head? = some tick) } S hS rfl
  set S₁ : Stacks T A := { S with
                           R := Function.update (Function.update S.R i
                             (bitSymbol false :: rest)) j (List.replicate m tick ++ S.R j) }
  have h2 := Exec.act (body := body) (dropTop i .done) (mk v₁ S₁)
  have hr2 : (dropTop i .done : Act T Q A U).run (mk v₁ S₁) =
      mk v₁ { S with
              R := Function.update (Function.update S.R i rest) j
                (List.replicate m tick ++ S.R j) } := by
    simp only [dropTop, Action.run, mk_var, mk_stk, get_rt]
    have : S₁.R i = bitSymbol false :: rest := by simp [S₁, Function.update_of_ne hij]
    rw [this, update_rt]
    congr 2
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = i
    · subst hk; simp [S₁, Function.update_of_ne hij]
    · simp [S₁, Function.update_of_ne hk]
      by_cases hk' : k = j
      · subst hk'; simp
      · simp [hk', Function.update_of_ne hk]
  rw [hr2] at h2
  exact ⟨v₁, hu₁, Exec.cast (Exec.seq h0 (Exec.seq he₁ h2)) (by ring) rfl⟩

end Block

/-! ### The caller registers -/

/-- The caller registers of the chirp loader: the table machine `tbl r`, the description streams
`tS`, `sS` of the axis lengths and chirp steps, the unary parameters `pU`, `gU`, `wU`, and the
unary registers `tU`, `sU` of the current axis. -/
inductive ldcX
  | tbl (r : TblR 84)
  | tS | sS | pU | gU | wU | tU | sU
  deriving DecidableEq

/-- The table-machine layout inside the caller registers. -/
def ldcTl {T : ℕ} (rg : CsR ldcX → Fin T) (r : TblR 84) : Fin T := rg (.x (.tbl r))

lemma ldcTl_injective {T : ℕ} {rg : CsR ldcX → Fin T} (hrg : Function.Injective rg) :
    Function.Injective (ldcTl rg) := by
  intro a b h
  have := hrg h
  simpa using this

/-- The register file `ρ` with every table variable in `l` replaced by `c`. -/
def ldcSetVars {A : ℕ} (ρ : CsR ldcX → List (Fin (A + 4))) (l : List (Fin 84))
    (c : List (Fin (A + 4))) : CsR ldcX → List (Fin (A + 4))
  | .x (.tbl (.v i)) => if i ∈ l then c else ρ (.x (.tbl (.v i)))
  | r => ρ r

/-- The register file `ρ` with the table registers replaced by `ρT`. -/
def ldcSetTbl {A : ℕ} (ρ : CsR ldcX → List (Fin (A + 4))) (ρT : TblR 84 → List (Fin (A + 4))) :
    CsR ldcX → List (Fin (A + 4))
  | .x (.tbl r) => ρT r
  | r => ρ r

section Files

variable {A : ℕ}

@[simp] lemma ldcSetVars_v (ρ : CsR ldcX → List (Fin (A + 4))) (l : List (Fin 84))
    (c : List (Fin (A + 4))) (i : Fin 84) :
    ldcSetVars ρ l c (.x (.tbl (.v i))) = if i ∈ l then c else ρ (.x (.tbl (.v i))) := rfl

lemma ldcSetVars_of (ρ : CsR ldcX → List (Fin (A + 4))) (l : List (Fin 84))
    (c : List (Fin (A + 4))) {r : CsR ldcX} (hr : ∀ i, r ≠ .x (.tbl (.v i))) :
    ldcSetVars ρ l c r = ρ r := by
  rcases r with y | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals try rfl
  rcases j with t | _ | _ | _ | _ | _ | _ | _
  all_goals try rfl
  rcases t with i | _ | _ | _ | _
  · exact absurd rfl (hr i)
  all_goals rfl

@[simp] lemma ldcSetVars_nil (ρ : CsR ldcX → List (Fin (A + 4))) (c : List (Fin (A + 4))) :
    ldcSetVars ρ [] c = ρ := by
  funext r
  by_cases hr : ∃ i, r = .x (.tbl (.v i))
  · obtain ⟨i, rfl⟩ := hr; simp
  · exact ldcSetVars_of ρ [] c fun i h => hr ⟨i, h⟩

lemma ldcSetVars_cons (ρ : CsR ldcX → List (Fin (A + 4))) (i : Fin 84) (l : List (Fin 84))
    (c : List (Fin (A + 4))) :
    ldcSetVars (Function.update ρ (.x (.tbl (.v i))) c) l c = ldcSetVars ρ (i :: l) c := by
  funext r
  by_cases hr : ∃ j, r = .x (.tbl (.v j))
  · obtain ⟨j, rfl⟩ := hr
    simp only [ldcSetVars_v, List.mem_cons]
    by_cases hj : j = i
    · subst hj; simp
    · by_cases hjl : j ∈ l
      · simp [hjl]
      · simp [hjl, hj]
  · have hr' : ∀ j, r ≠ .x (.tbl (.v j)) := fun j h => hr ⟨j, h⟩
    rw [ldcSetVars_of _ _ _ hr', ldcSetVars_of _ _ _ hr', Function.update_of_ne (hr' i)]

@[simp] lemma ldcSetTbl_tbl (ρ : CsR ldcX → List (Fin (A + 4))) (ρT : TblR 84 → List (Fin (A + 4)))
    (r : TblR 84) : ldcSetTbl ρ ρT (.x (.tbl r)) = ρT r := rfl

lemma ldcSetTbl_of (ρ : CsR ldcX → List (Fin (A + 4))) (ρT : TblR 84 → List (Fin (A + 4)))
    {r : CsR ldcX} (hr : ∀ t, r ≠ .x (.tbl t)) : ldcSetTbl ρ ρT r = ρ r := by
  rcases r with y | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals try rfl
  rcases j with t | _ | _ | _ | _ | _ | _ | _
  · exact absurd rfl (hr t)
  all_goals rfl

end Files


/-! ### Loops over the table variables -/

section Vars

variable {T Q A : ℕ} {U P : Type}

/-- Run `f i` for the table variables `i` of `l` in order. -/
def ldcVars (f : Fin 84 → Pr P T Q A U) : List (Fin 84) → Pr P T Q A U
  | [] => .act .done
  | i :: l => .seq (f i) (ldcVars f l)

/-- Set table variable `i` to `binSyms W 0` from the word register `wr` (`W` symbols) through
the scratch register `z 0`. -/
def ldcZeroOp (rg : CsR ldcX → Fin T) (i : Fin 84) : Pr P T Q A U :=
  zeroBits (rg (.x (.tbl .wr))) (rg (.x (.tbl (.v i)))) (rg (.x (.tbl (.z 0))))

/-- Empty table variable `i`. -/
def ldcClearOp (rg : CsR ldcX → Fin T) (i : Fin 84) : Pr P T Q A U :=
  uclear (rg (.x (.tbl (.v i))))

end Vars

section HostDefs

variable {T Q A : ℕ} {U P : Type}

/-- The chirp table machine onto `ys`, then every table variable emptied. -/
def ldcHostClear (rg : CsR ldcX → Fin T) : Pr P T Q A U :=
  .seq (tblHost (ldcTl rg) tblChirpCode (rg (.c .ys))) (ldcVars (ldcClearOp rg) (List.finRange 84))

end HostDefs

/-- The step bound of `ldcHostClear`: the chirp table machine (`tblChirp_host`) and the
emptying of the 84 variables. -/
def ldcHostCost (W w p g N : ℕ) : ℕ :=
  (N * (39 * (p + g) + 641) + 200 * (p + g) + 4 * w + 1503) * tblC W w + 2 * (N * w) + 2 +
    (84 * (2 * W + 2) + 1)

/-- The idle table registers: `wr`, `wn` hold `wl`, `nl`, everything else is empty. -/
def ldcIdle {A : ℕ} (wl nl : List (Fin (A + 4))) : TblR 84 → List (Fin (A + 4))
  | .wr => wl
  | .wn => nl
  | _ => []

/-- The table state of one axis: `p, g, N, s, w` in variables `54 … 58`, every other variable
`0`, nothing emitted. -/
def ldcSt (A p g N s w : ℕ) : TblSt 84 A :=
  ⟨Function.update (Function.update (Function.update (Function.update (Function.update
    (fun _ => 0) 54 p) 55 g) 56 N) 57 s) 58 w, []⟩

section PrepDef

variable {T Q A : ℕ} {U P : Type}

/-- **The chirp loader** for one axis: pop the axis' blocks of `tS`, `sS` onto `tU`, `sU`; set
the 84 table variables to `0`; load `p, g, t_k, s_k, w` from `pU, gU, tU, sU, wU` into the
variables `54 … 58`; run the chirp table machine onto `ys` and empty the variables; move `tU`
onto `cL`; empty `sU`. -/
def ldcPrep (rg : CsR ldcX → Fin T) : Pr P T Q A U :=
  .seq (ldcPopBlock (rg (.x .tS)) (rg (.x .tU))) <|
  .seq (ldcPopBlock (rg (.x .sS)) (rg (.x .sU))) <|
  .seq (ldcVars (ldcZeroOp rg) (List.finRange 84)) <|
  .seq (tblLoad1 (ldcTl rg) (rg (.x .pU)) 54) <|
  .seq (tblLoad1 (ldcTl rg) (rg (.x .gU)) 55) <|
  .seq (tblLoad1 (ldcTl rg) (rg (.x .tU)) 56) <|
  .seq (tblLoad1 (ldcTl rg) (rg (.x .sU)) 57) <|
  .seq (tblLoad1 (ldcTl rg) (rg (.x .wU)) 58) <|
  .seq (ldcHostClear rg) <|
  .seq (moveR (rg (.x .tU)) (rg .cL) id) (uclear (rg (.x .sU)))

end PrepDef

/-- The step bound of one `tblLoad1` of the value `k` with `W`-bit words. -/
def ldcLoadCost (W k : ℕ) : ℕ := k * (4 * W + 10) + 6 * W + 10

/-- The step bound of `ldcPrep` for an axis of length `N` and step `s`. -/
def ldcAxisCost (W w p g N s : ℕ) : ℕ :=
  (2 * N + 3) + (2 * s + 3) + (84 * (4 * W + 4) + 1) +
    (ldcLoadCost W p + ldcLoadCost W g + ldcLoadCost W N + ldcLoadCost W s + ldcLoadCost W w) +
    ldcHostCost W w p g N + (2 * N + 2) + (2 * s + 2)

lemma ldc_numer_mk (q : ℕ) (a b : ℤ) :
    numer q (⟨(a : ℝ) / 2 ^ q, (b : ℝ) / 2 ^ q⟩ : ℂ) = ⟨a, b⟩ := by
  have hpos : (2 : ℝ) ^ q ≠ 0 := by positivity
  simp only [numer]
  rw [mul_div_cancel₀ _ hpos, mul_div_cancel₀ _ hpos, IntegerMultBounds.NLogN.rho0_intCast,
    IntegerMultBounds.NLogN.rho0_intCast]

/-- The table of axis `k` as a stream is the chirp axis stream of the table machine. -/
theorem ldc_cstream_axTab (A w p g : ℕ) {d : ℕ} (t s : Fin d → ℕ) {k : ℕ} (hk : k < d) :
    cstream A w (cstTab (List.ofFn t) (cstAxTab p g t s) k) =
      tblChirpStream A w p g (t ⟨k, hk⟩) (s ⟨k, hk⟩) := by
  have hg : (List.ofFn t).getD k 0 = t ⟨k, hk⟩ := by
    rw [cst_getD (by simpa using hk), List.getElem_ofFn]
  rw [cstTab, hg, tblChirpStream, cstream, List.flatMap_map]
  refine List.flatMap_congr fun j _ => ?_
  rw [cstAxTab, dite_eq_left hk, tbl_axisPhase, ldc_numer_mk]
  rfl

section Runs

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : CsR ldcX → Fin T}
  {ι : Fin 64 → Fin T}

variable (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
include hrg

theorem ldc_popBlock_runs {a b : CsR ldcX} (hab : a ≠ b) (ρ : CsR ldcX → List (Fin (A + 4)))
    (m : ℕ) (rest : List (Fin (A + 4))) (ha : ρ a = List.replicate m tick ++ bitSymbol false :: rest) :
    RsaRuns body rg ι (ldcPopBlock (rg a) (rg b)) ρ
      (Function.update (Function.update ρ a rest) b (List.replicate m tick ++ ρ b)) (2 * m + 3) := by
  refine RsaRuns.of_raw fun v S _ hS => ?_
  obtain ⟨v', hu, he⟩ := ldc_popBlock_exec body (rg a) (rg b) (hrg.ne hab) m rest v S
    (by rw [hS, ha])
  refine ⟨v', _, _, hu, le_rfl, he, ?_, fun k hk => ?_⟩
  · intro r
    rw [rsa_holds_upd hrg (rsa_holds_upd hrg hS a rest) b, hS]
  · rw [rsa_upd_off _ _ _ hk, rsa_upd_off _ _ _ hk]

include hdisj in
/-- Zeroing the table variables of `l` (distinct, empty) from `wr`. -/
theorem ldc_zero_runs (l : List (Fin 84)) :
    ∀ (ρ : CsR ldcX → List (Fin (A + 4))), l.Nodup → ρ (.x (.tbl (.z 0))) = [] →
      (∀ i ∈ l, ρ (.x (.tbl (.v i))) = []) →
      RsaRuns body rg ι (ldcVars (ldcZeroOp rg) l) ρ
        (ldcSetVars ρ l (binSyms (ρ (.x (.tbl .wr))).length 0))
        (l.length * (4 * (ρ (.x (.tbl .wr))).length + 4) + 1) := by
  induction l with
  | nil =>
      intro ρ _ _ _
      simpa [ldcVars] using rsa_done (body := body) (ι := ι) ρ
  | cons i l ih =>
      intro ρ hnd hz hv
      have h1 := rsa_umulSym (body := body) (ι := ι) hrg 1 (bitSymbol false)
        (a := .x (.tbl .wr)) (b := .x (.tbl (.v i))) (t := .x (.tbl (.z 0))) (by simp) (by simp)
        (by simp) ρ hz
      rw [hv i List.mem_cons_self, List.append_nil, one_mul, ← binSyms_zero_right] at h1
      set c : List (Fin (A + 4)) := binSyms (ρ (.x (.tbl .wr))).length 0 with hc
      have hwr : Function.update ρ (.x (.tbl (.v i))) c (.x (.tbl .wr)) = ρ (.x (.tbl .wr)) :=
        Function.update_of_ne (by simp) _ _
      have h2 := ih (Function.update ρ (.x (.tbl (.v i))) c) (List.nodup_cons.1 hnd).2
        (by rw [Function.update_of_ne (by simp)]; exact hz)
        (fun j hj => by
          have hji : j ≠ i := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hj)
          rw [Function.update_of_ne (by simpa using hji)]
          exact hv j (List.mem_cons_of_mem _ hj))
      rw [hwr, ← hc, ldcSetVars_cons] at h2
      refine (RsaRuns.seq hdisj h1 h2).mono (le_of_eq ?_)
      simp only [List.length_cons]; ring

include hdisj in
/-- Emptying the table variables of `l` (distinct, `L` symbols each). -/
theorem ldc_clear_runs (L : ℕ) (l : List (Fin 84)) :
    ∀ (ρ : CsR ldcX → List (Fin (A + 4))), l.Nodup →
      (∀ i ∈ l, (ρ (.x (.tbl (.v i)))).length = L) →
      RsaRuns body rg ι (ldcVars (ldcClearOp rg) l) ρ (ldcSetVars ρ l [])
        (l.length * (2 * L + 2) + 1) := by
  induction l with
  | nil =>
      intro ρ _ _
      simpa [ldcVars] using rsa_done (body := body) (ι := ι) ρ
  | cons i l ih =>
      intro ρ hnd hv
      have h1 := rsa_uclear (body := body) (ι := ι) hrg (.x (.tbl (.v i))) ρ
      rw [hv i List.mem_cons_self] at h1
      have h2 := ih (Function.update ρ (.x (.tbl (.v i))) []) (List.nodup_cons.1 hnd).2
        (fun j hj => by
          have hji : j ≠ i := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hj)
          rw [Function.update_of_ne (by simpa using hji)]
          exact hv j (List.mem_cons_of_mem _ hj))
      rw [ldcSetVars_cons] at h2
      refine (RsaRuns.seq hdisj h1 h2).mono (le_of_eq ?_)
      simp only [List.length_cons]; ring

/-- A contract of the table machine on its layout lifts to the caller's register file. -/
theorem ldc_tbl_lift {p : Pr P T Q A U} {ρ : CsR ldcX → List (Fin (A + 4))}
    {ρT : TblR 84 → List (Fin (A + 4))} {b : ℕ}
    (h : ∀ v S, rsaHolds rg S ρ → ∃ v' S' m, v'.user = v.user ∧ m ≤ b ∧
      Exec body p (mk v S) m (mk v' S') ∧ tblHolds (ldcTl rg) S' ρT ∧ tblFr (ldcTl rg) S S') :
    RsaRuns body rg ι p ρ (ldcSetTbl ρ ρT) b := by
  intro v S _ hS
  obtain ⟨v', S', m, hu, hm, he, hT, hf⟩ := h v S hS
  refine ⟨v', S', m, hu, hm, he, fun r => ?_, hf.1, hf.2.1, hf.2.2.1,
    fun k hk => hf.2.2.2 k (fun t => hk _)⟩
  by_cases hr : ∃ t, r = .x (.tbl t)
  · obtain ⟨t, rfl⟩ := hr
    exact hT t
  · have hr' : ∀ t, r ≠ .x (.tbl t) := fun t h => hr ⟨t, h⟩
    rw [ldcSetTbl_of _ _ hr', ← hS r]
    exact hf.2.2.2 _ (fun t h => hr' t (hrg h).symm)

/-- `tblLoad1` from the unary caller register `u`: variable `i` becomes `k = |u|`. -/
theorem ldc_load_runs {u : ldcX} (hu : ∀ t, u ≠ .tbl t) (i : Fin 84) {W : ℕ}
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (st : TblSt 84 A) (k : ℕ)
    (ρ : CsR ldcX → List (Fin (A + 4))) (hk : (ρ (.x u)).length = k)
    (hρ : ∀ r, ρ (.x (.tbl r)) = tblRho W wl nl st r) :
    RsaRuns body rg ι (tblLoad1 (ldcTl rg) (rg (.x u)) i) ρ
      (ldcSetTbl ρ (tblRho W wl nl ⟨Function.update st.val i k, st.acc⟩))
      (k * (4 * W + 10) + 6 * W + 10) := by
  refine ldc_tbl_lift hrg fun v S hS => ?_
  exact tbl_load1_runs (body := body) (ldcTl_injective hrg) wl nl hwl (u := rg (.x u))
    (fun t h => hu t (CsR.x.inj (hrg h)).symm) i st k v S (by rw [hS, hk])
    (fun r => by rw [ldcTl, hS, hρ])

include hdisj in
/-- **The chirp table onto `ys`.** With the table registers carrying a state `st` (empty
emission list, `p, g, N, s, w` in variables `54 … 58`, the size conditions of `tblChirp_do`),
`ldcHostClear` pushes the chirp axis stream `tblChirpStream A w p g N s` onto `ys` and empties
every table variable. -/
theorem ldc_hostClear_runs {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W)
    (hnl : nl.length = w) (hw : w < W) (st : TblSt 84 A) (hst : ∀ j, st.val j < 2 ^ W)
    (hacc : st.acc = []) {p g N s : ℕ}
    (hin : tblKV st [((54 : Fin 84), p), (55, g), (56, N), (57, s), (58, w)]) (hN : 0 < N)
    (hsN : s * N * N < 2 ^ W) (hW : 8 * (p + g) + Nat.size N + 80 ≤ W)
    (ρ : CsR ldcX → List (Fin (A + 4))) (hρ : ∀ r, ρ (.x (.tbl r)) = tblRho W wl nl st r) :
    RsaRuns body rg ι (ldcHostClear rg) ρ
      (Function.update (ldcSetVars ρ (List.finRange 84) []) (.c .ys)
        (tblChirpStream A w p g N s ++ ρ (.c .ys)))
      (ldcHostCost W w p g N) := by
  intro v S hc hS
  have hT : tblHolds (ldcTl rg) S (tblRho W wl nl st) := fun r => by rw [ldcTl, hS, hρ]
  have hout : ∀ r, ldcTl rg r ≠ rg (.c .ys) := fun r h => by
    have := hrg h
    simp at this
  obtain ⟨v₁, S₁, m₁, st', hp, hu₁, hm₁, he₁, hout₁, hS₁, hi₁, ho₁, hL₁, hk₁⟩ :=
    tblHost_runs (body := body) (ldcTl_injective hrg) hout wl nl hwl hnl hw.le
      (tblChirp_do st hin hN hsN hW hw) hst v S hT
  rw [hacc, List.append_nil] at hp
  have hlen : st'.acc.length = N * w := by
    rw [hp, List.length_reverse]
    exact tbl_stream_length A w N _ (fun j => by simp [tblChirpEntry])
  set ρ₁ := Function.update (ldcSetTbl ρ (tblRho W wl nl ⟨st'.val, []⟩)) (.c .ys)
    (tblChirpStream A w p g N s ++ ρ (.c .ys)) with hρ₁
  have hS₁' : rsaHolds rg S₁ ρ₁ := by
    intro r
    by_cases hr : r = .c .ys
    · subst hr
      rw [hρ₁, Function.update_self, hout₁, hp, List.reverse_reverse, hS]
    · rw [hρ₁, Function.update_of_ne hr]
      by_cases ht : ∃ t, r = .x (.tbl t)
      · obtain ⟨t, rfl⟩ := ht
        exact hS₁ t
      · have ht' : ∀ t, r ≠ .x (.tbl t) := fun t h => ht ⟨t, h⟩
        rw [ldcSetTbl_of _ _ ht', ← hS r]
        exact hk₁ _ (hrg.ne hr) (fun t h => ht' t (hrg h).symm)
  have hf₁ : rsaFr rg S S₁ := ⟨hi₁, ho₁, hL₁, fun k hk => hk₁ k (hk _).symm (fun t => hk _)⟩
  obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hS₂, hf₂⟩ :=
    ldc_clear_runs (body := body) (ι := ι) hrg hdisj W (List.finRange 84) ρ₁
      (List.nodup_finRange 84) (fun i _ => by simp [hρ₁]) v₁ S₁ (hc.of_fr hdisj hf₁) hS₁'
  refine ⟨v₂, S₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, ?_, hf₁.trans hf₂⟩
  · rw [hlen] at hm₁
    simp only [List.length_finRange] at hm₂
    unfold ldcHostCost
    omega
  · intro r
    rw [hS₂ r]
    by_cases hr : r = .c .ys
    · subst hr
      rw [ldcSetVars_of _ _ _ (fun i => by simp), hρ₁, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hr]
      by_cases hv : ∃ i, r = .x (.tbl (.v i))
      · obtain ⟨i, rfl⟩ := hv
        simp
      · have hv' : ∀ i, r ≠ .x (.tbl (.v i)) := fun i h => hv ⟨i, h⟩
        rw [ldcSetVars_of _ _ _ hv', ldcSetVars_of _ _ _ hv', hρ₁, Function.update_of_ne hr]
        by_cases ht : ∃ t, r = .x (.tbl t)
        · obtain ⟨t, rfl⟩ := ht
          rw [ldcSetTbl_tbl, hρ]
          cases t with
          | v i => exact absurd rfl (hv' i)
          | acc => simp [hacc]
          | _ => rfl
        · rw [ldcSetTbl_of _ _ (fun t h => ht ⟨t, h⟩)]

omit hrg in
lemma ldc_vals_lt {W w p g N s : ℕ} (hw : w < W) (hN : 0 < N) (hsN : s * N * N < 2 ^ W)
    (hW : 8 * (p + g) + Nat.size N + 80 ≤ W) :
    p < 2 ^ W ∧ g < 2 ^ W ∧ N < 2 ^ W ∧ s < 2 ^ W ∧ w < 2 ^ W := by
  have hW2 : W < 2 ^ W := Nat.lt_two_pow_self
  have h1 : N < 2 ^ W := lt_of_lt_of_le (Nat.lt_size_self N) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : s ≤ s * N * N := by
    have : 1 ≤ N * N := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc s = s * 1 := (mul_one s).symm
      _ ≤ s * (N * N) := Nat.mul_le_mul_left s this
      _ = s * N * N := by ring
  refine ⟨by omega, by omega, h1, by omega, by omega⟩

include hdisj in
/-- **One axis of the chirp loader.** The stream registers `tS`, `sS` start with the blocks of
`N` and `s` ticks (each followed by `bitSymbol false`), `tU`, `sU` are empty, `pU`, `gU`, `wU`
hold `p`, `g`, `w` symbols, and the table registers are idle (`ldcIdle wl nl`, `|wl| = W`,
`|nl| = w`). Then `ldcPrep` drops the two blocks, pushes the chirp axis stream onto `ys` and
`N` ticks onto `cL`, and leaves every other register as it started. -/
theorem ldc_prep_runs {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W)
    (hnl : nl.length = w) (hw : w < W) {p g N s : ℕ} (hN : 0 < N) (hsN : s * N * N < 2 ^ W)
    (hW : 8 * (p + g) + Nat.size N + 80 ≤ W) (rT rS : List (Fin (A + 4)))
    (ρ : CsR ldcX → List (Fin (A + 4)))
    (hts : ρ (.x .tS) = List.replicate N tick ++ bitSymbol false :: rT)
    (hss : ρ (.x .sS) = List.replicate s tick ++ bitSymbol false :: rS)
    (htU : ρ (.x .tU) = []) (hsU : ρ (.x .sU) = []) (hpU : (ρ (.x .pU)).length = p)
    (hgU : (ρ (.x .gU)).length = g) (hwU : (ρ (.x .wU)).length = w)
    (htb : ∀ r, ρ (.x (.tbl r)) = ldcIdle wl nl r) :
    RsaRuns body rg ι (ldcPrep rg) ρ
      (Function.update (Function.update (Function.update (Function.update ρ (.x .tS) rT)
        (.x .sS) rS) (.c .ys) (tblChirpStream A w p g N s ++ ρ (.c .ys))) .cL
        (List.replicate N tick ++ ρ .cL))
      (ldcAxisCost W w p g N s) := by
  obtain ⟨hp2, hg2, hN2, hs2, hw2⟩ := ldc_vals_lt hw hN hsN hW
  -- the blocks
  have s1 := ldc_popBlock_runs (body := body) (ι := ι) hrg (a := .x .tS) (b := .x .tU) (by simp)
    ρ N rT hts
  set ρ1 := Function.update (Function.update ρ (.x .tS) rT) (.x .tU)
    (List.replicate N tick ++ ρ (.x .tU)) with hρ1
  have s2 := ldc_popBlock_runs (body := body) (ι := ι) hrg (a := .x .sS) (b := .x .sU) (by simp)
    ρ1 s rS (by simp [hρ1, hss])
  set ρ2 := Function.update (Function.update ρ1 (.x .sS) rS) (.x .sU)
    (List.replicate s tick ++ ρ1 (.x .sU)) with hρ2
  have e2 : ∀ r, ρ2 (.x (.tbl r)) = ldcIdle wl nl r := fun r => by simp [hρ2, hρ1, htb]
  -- zeroing
  have s3 := ldc_zero_runs (body := body) (ι := ι) hrg hdisj (List.finRange 84) ρ2
    (List.nodup_finRange 84) (by rw [e2]; rfl) (fun i _ => by rw [e2]; rfl)
  rw [e2 .wr, show ldcIdle wl nl .wr = wl from rfl, hwl] at s3
  set ρ3 := ldcSetVars ρ2 (List.finRange 84) (binSyms W 0) with hρ3
  have e3 : ∀ r, ρ3 (.x (.tbl r)) = tblRho W wl nl ⟨fun _ => 0, []⟩ r := by
    intro r
    cases r with
    | v i => simp [hρ3]
    | _ => rw [hρ3, ldcSetVars_of _ _ _ (fun i => by simp), e2]; rfl
  have o3 : ∀ u : ldcX, (∀ t, u ≠ .tbl t) → ρ3 (.x u) = ρ2 (.x u) := fun u hu =>
    ldcSetVars_of _ _ _ (fun i h => hu (.v i) (CsR.x.inj h))
  -- the loads
  have s4 := ldc_load_runs (body := body) (ι := ι) hrg (u := .pU) (by simp) 54 wl nl hwl
    ⟨fun _ => 0, []⟩ p ρ3 (by rw [o3 _ (by simp)]; simpa [hρ2, hρ1] using hpU) e3
  set ρ4 := ldcSetTbl ρ3 (tblRho W wl nl ⟨Function.update (fun _ => 0) 54 p, []⟩) with hρ4
  have s5 := ldc_load_runs (body := body) (ι := ι) hrg (u := .gU) (by simp) 55 wl nl hwl
    ⟨Function.update (fun _ => 0) 54 p, []⟩ g ρ4
    (by rw [hρ4, ldcSetTbl_of _ _ (by simp), o3 _ (by simp)]; simpa [hρ2, hρ1] using hgU)
    (fun r => rfl)
  set ρ5 := ldcSetTbl ρ4 (tblRho W wl nl
    ⟨Function.update (Function.update (fun _ => 0) 54 p) 55 g, []⟩) with hρ5
  have s6 := ldc_load_runs (body := body) (ι := ι) hrg (u := .tU) (by simp) 56 wl nl hwl
    ⟨Function.update (Function.update (fun _ => 0) 54 p) 55 g, []⟩ N ρ5
    (by rw [hρ5, ldcSetTbl_of _ _ (by simp), hρ4, ldcSetTbl_of _ _ (by simp), o3 _ (by simp)]
        simp [hρ2, hρ1, htU])
    (fun r => rfl)
  set ρ6 := ldcSetTbl ρ5 (tblRho W wl nl
    ⟨Function.update (Function.update (Function.update (fun _ => 0) 54 p) 55 g) 56 N, []⟩)
    with hρ6
  have s7 := ldc_load_runs (body := body) (ι := ι) hrg (u := .sU) (by simp) 57 wl nl hwl
    ⟨Function.update (Function.update (Function.update (fun _ => 0) 54 p) 55 g) 56 N, []⟩ s ρ6
    (by rw [hρ6, ldcSetTbl_of _ _ (by simp), hρ5, ldcSetTbl_of _ _ (by simp), hρ4,
          ldcSetTbl_of _ _ (by simp), o3 _ (by simp)]
        simp [hρ2, hρ1, hsU])
    (fun r => rfl)
  set ρ7 := ldcSetTbl ρ6 (tblRho W wl nl ⟨Function.update (Function.update (Function.update
    (Function.update (fun _ => 0) 54 p) 55 g) 56 N) 57 s, []⟩) with hρ7
  have s8 := ldc_load_runs (body := body) (ι := ι) hrg (u := .wU) (by simp) 58 wl nl hwl
    ⟨Function.update (Function.update (Function.update (Function.update (fun _ => 0) 54 p) 55 g)
      56 N) 57 s, []⟩ w ρ7
    (by rw [hρ7, ldcSetTbl_of _ _ (by simp), hρ6, ldcSetTbl_of _ _ (by simp), hρ5,
          ldcSetTbl_of _ _ (by simp), hρ4, ldcSetTbl_of _ _ (by simp), o3 _ (by simp)]
        simpa [hρ2, hρ1] using hwU)
    (fun r => rfl)
  set ρ8 := ldcSetTbl ρ7 (tblRho W wl nl (ldcSt A p g N s w)) with hρ8
  -- the table machine
  have hst : ∀ j, (ldcSt A p g N s w).val j < 2 ^ W := by
    intro j
    simp only [ldcSt, Function.update_apply]
    split_ifs <;> first | assumption | exact Nat.two_pow_pos W
  have hin : tblKV (ldcSt A p g N s w) [((54 : Fin 84), p), (55, g), (56, N), (57, s), (58, w)] := by
    intro e he
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> simp [ldcSt]
  have s9 := ldc_hostClear_runs (body := body) (ι := ι) hrg hdisj wl nl hwl hnl hw
    (ldcSt A p g N s w) hst rfl hin hN hsN hW ρ8 (fun r => rfl)
  set ρ9 := Function.update (ldcSetVars ρ8 (List.finRange 84) []) (.c .ys)
    (tblChirpStream A w p g N s ++ ρ8 (.c .ys)) with hρ9
  -- the counter and the cleanup
  have s10 := rsa_moveR (body := body) (ι := ι) hrg (a := .x .tU) (b := .cL) (by simp) ρ9
  set ρ10 := Function.update (Function.update ρ9 (.x .tU) []) .cL
    ((ρ9 (.x .tU)).reverse ++ ρ9 .cL) with hρ10
  have s11 := rsa_uclear (body := body) (ι := ι) hrg (.x .sU) ρ10
  have hT9 : ρ9 (.x .tU) = List.replicate N tick := by
    simp [hρ9, ldcSetVars_of, ldcSetTbl_of, hρ8, hρ7, hρ6, hρ5, hρ4, hρ3, hρ2, hρ1, htU]
  have hS10 : ρ10 (.x .sU) = List.replicate s tick := by
    simp [hρ10, hρ9, ldcSetVars_of, ldcSetTbl_of, hρ8, hρ7, hρ6, hρ5, hρ4, hρ3, hρ2, hρ1, hsU]
  refine ((RsaRuns.seq hdisj s1 (RsaRuns.seq hdisj s2 (RsaRuns.seq hdisj s3
    (RsaRuns.seq hdisj s4 (RsaRuns.seq hdisj s5 (RsaRuns.seq hdisj s6 (RsaRuns.seq hdisj s7
    (RsaRuns.seq hdisj s8 (RsaRuns.seq hdisj s9 (RsaRuns.seq hdisj s10 s11)))))))))).congr
    ?_).mono ?_
  · funext r
    rcases r with y | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
    · by_cases hy : y = .ys
      · subst hy
        simp [hρ10, hρ9, hρ8, hρ7, hρ6, hρ5, hρ4, hρ3, hρ2, hρ1, ldcSetVars_of, ldcSetTbl_of]
      · simp [hρ10, hρ9, hρ8, hρ7, hρ6, hρ5, hρ4, hρ3, hρ2, hρ1, ldcSetVars_of, ldcSetTbl_of,
          hy]
    all_goals try (simp [hρ10, hρ9, hρ8, hρ7, hρ6, hρ5, hρ4, hρ3, hρ2, hρ1, ldcSetVars_of,
      ldcSetTbl_of, Function.update_apply]; done)
    · rw [Function.update_of_ne (by simp), hρ10, Function.update_self, hT9, List.reverse_replicate]
      simp [hρ9, hρ8, hρ7, hρ6, hρ5, hρ4, hρ3, hρ2, hρ1, ldcSetVars_of, ldcSetTbl_of]
    rcases j with t | _ | _ | _ | _ | _ | _ | _
    · cases t <;> simp [hρ10, hρ9, hρ8, hρ7, hρ6, hρ5, hρ4, hρ3, hρ2, hρ1, ldcSetVars_of,
        ldcSetTbl_of, htb, ldcIdle, ldcSt]
    all_goals simp [hρ10, hρ9, hρ8, hρ7, hρ6, hρ5, hρ4, hρ3, hρ2, hρ1, ldcSetVars_of,
      ldcSetTbl_of, htU, hsU]
  · rw [hT9, hS10]
    simp only [List.length_replicate, List.length_finRange]
    unfold ldcAxisCost ldcLoadCost
    omega

end Runs

/-! ### The description streams and the contract of the stage -/

/-- The description stream of a list of axis values: per value `m`, `m` ticks and one
`bitSymbol false`, the first value on top. -/
def ldcBlocks {A : ℕ} (l : List ℕ) : List (Fin (A + 4)) :=
  l.flatMap fun m => List.replicate m tick ++ [bitSymbol false]

lemma ldcBlocks_drop {A : ℕ} {l : List ℕ} {k : ℕ} (hk : k < l.length) :
    (ldcBlocks (l.drop k) : List (Fin (A + 4))) =
      List.replicate l[k] tick ++ bitSymbol false :: ldcBlocks (l.drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons hk, ldcBlocks, List.flatMap_cons, ← ldcBlocks, List.append_assoc]
  rfl

/-- The caller registers before axis `k`: the streams `tS`, `sS` hold the blocks of the axes
`k, k + 1, …`; every other caller register is as in `xx`. -/
def ldcCfg {A : ℕ} (xx : ldcX → List (Fin (A + 4))) (ts ss : List ℕ) (k : ℕ) :
    ldcX → List (Fin (A + 4))
  | .tS => ldcBlocks (ts.drop k)
  | .sS => ldcBlocks (ss.drop k)
  | j => xx j

section Contract

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : CsR ldcX → Fin T}
  {ι : Fin 64 → Fin T}

variable (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
include hrg hdisj

/-- **The loader contract** (`hprep` of `cst_chirpBox_pipeline`): run with axis `k` pending,
`ldcPrep` loads the chirp table of axis `k` onto `ys` and `t_k` ticks onto `cL`, and moves the
caller registers from `ldcCfg xx … k` to `ldcCfg xx … (k + 1)`, within
`ldcAxisCost W w p g t_k s_k` steps. -/
theorem ldc_prep_hprep {W w p g d : ℕ} (t s : Fin d → ℕ) (xx : ldcX → List (Fin (A + 4)))
    (hwl : (xx (.tbl .wr)).length = W) (hnl : (xx (.tbl .wn)).length = w) (hw : w < W)
    (hN : ∀ k, 0 < t k) (hsN : ∀ k, s k * t k * t k < 2 ^ W)
    (hW : ∀ k, 8 * (p + g) + Nat.size (t k) + 80 ≤ W)
    (htU : xx .tU = []) (hsU : xx .sU = []) (hpU : (xx .pU).length = p)
    (hgU : (xx .gU).length = g) (hwU : (xx .wU).length = w)
    (htb : ∀ r, r ≠ .wr → r ≠ .wn → xx (.tbl r) = []) :
    ∀ k < d, ∀ ρ : CsR ldcX → List (Fin (A + 4)), ρ (.c .ys) = [] → ρ .cL = [] →
      (∀ j, ρ (.x j) = ldcCfg xx (List.ofFn t) (List.ofFn s) k j) →
      RsaRuns body rg ι (ldcPrep rg) ρ
        (cstSetX (Function.update (Function.update ρ (.c .ys)
          (cstream A w (cstTab (List.ofFn t) (cstAxTab p g t s) k))) .cL
          (List.replicate ((List.ofFn t).getD k 0) tick))
          (ldcCfg xx (List.ofFn t) (List.ofFn s) (k + 1)))
        (ldcAxisCost W w p g ((List.ofFn t).getD k 0) ((List.ofFn s).getD k 0)) := by
  intro k hk ρ hys hcL hx
  have hgt : (List.ofFn t).getD k 0 = t ⟨k, hk⟩ := by
    rw [cst_getD (by simpa using hk), List.getElem_ofFn]
  have hgs : (List.ofFn s).getD k 0 = s ⟨k, hk⟩ := by
    rw [cst_getD (by simpa using hk), List.getElem_ofFn]
  have hkt : k < (List.ofFn t).length := by simpa using hk
  have hks : k < (List.ofFn s).length := by simpa using hk
  have hts : ρ (.x .tS) = List.replicate (t ⟨k, hk⟩) tick ++ bitSymbol false ::
      ldcBlocks ((List.ofFn t).drop (k + 1)) := by
    rw [hx, ldcCfg, ldcBlocks_drop hkt, List.getElem_ofFn]
  have hss : ρ (.x .sS) = List.replicate (s ⟨k, hk⟩) tick ++ bitSymbol false ::
      ldcBlocks ((List.ofFn s).drop (k + 1)) := by
    rw [hx, ldcCfg, ldcBlocks_drop hks, List.getElem_ofFn]
  have htb' : ∀ r, ρ (.x (.tbl r)) = ldcIdle (xx (.tbl .wr)) (xx (.tbl .wn)) r := by
    intro r
    rw [hx]
    cases r with
    | wr => rfl
    | wn => rfl
    | _ => exact htb _ (by simp) (by simp)
  have h := ldc_prep_runs (body := body) (ι := ι) hrg hdisj (xx (.tbl .wr)) (xx (.tbl .wn)) hwl hnl
    hw (hN ⟨k, hk⟩) (hsN ⟨k, hk⟩) (hW ⟨k, hk⟩) _ _ ρ hts hss (by rw [hx]; exact htU)
    (by rw [hx]; exact hsU) (by rw [hx]; exact hpU) (by rw [hx]; exact hgU) (by rw [hx]; exact hwU)
    htb'
  rw [hgt, hgs]
  refine h.congr ?_
  funext r
  rcases r with y | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · by_cases hy : y = .ys
    · subst hy
      simp [hys, ldc_cstream_axTab A w p g t s hk]
    · simp [hy]
  all_goals try (simp [Function.update_apply, hcL]; done)
  rcases j with r | _ | _ | _ | _ | _ | _ | _
  all_goals simp [hx, ldcCfg]

/-- **The chirp stage without a loader hypothesis.** The kernel box of the pipeline
(`cst_chirpBox_kernel`) with the loader `ldcPrep`: the caller registers carry the description
streams `ldcBlocks (List.ofFn (t n))`, `ldcBlocks (List.ofFn (s n))` on `tS`, `sS`, the unary
parameters `p n`, `chirpGuard (d n)`, `w` on `pU`, `gU`, `wU`, empty `tU`, `sU`, and idle table
registers with `W` symbols on `wr` and `w` on `wn`. The stage pushes the numerator box of the
chirp kernel `Pipeline.chirpKernel n` onto `kr` and consumes the two streams; every other
register ends as it started. -/
theorem ldChirpStage_exec (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ A) (n : ℕ) {w W : ℕ} (hd : 1 ≤ Mult.Sizes.d n)
    (hw : Mult.Sizes.p n + chirpGuard (Mult.Sizes.d n) + 3 ≤ w) (hwW : w < W)
    (hsN : ∀ k, Mult.Sizes.s n k * Mult.Sizes.t n k * Mult.Sizes.t n k < 2 ^ W)
    (hW : ∀ k, 8 * (Mult.Sizes.p n + chirpGuard (Mult.Sizes.d n)) + Nat.size (Mult.Sizes.t n k) +
      80 ≤ W)
    (ρ : CsR ldcX → List (Fin (A + 4)))
    (hb : CstBase ρ w (Mult.Sizes.p n) (chirpGuard (Mult.Sizes.d n)))
    (hax : (ρ .ax).length + 1 = Mult.Sizes.d n)
    (htS : ρ (.x .tS) = ldcBlocks (List.ofFn (Mult.Sizes.t n)))
    (hsS : ρ (.x .sS) = ldcBlocks (List.ofFn (Mult.Sizes.s n)))
    (htU : ρ (.x .tU) = []) (hsU : ρ (.x .sU) = [])
    (hpU : (ρ (.x .pU)).length = Mult.Sizes.p n)
    (hgU : (ρ (.x .gU)).length = chirpGuard (Mult.Sizes.d n)) (hwU : (ρ (.x .wU)).length = w)
    (hwr : (ρ (.x (.tbl .wr))).length = W) (hwn : (ρ (.x (.tbl .wn))).length = w)
    (htb : ∀ r, r ≠ .wr → r ≠ .wn → ρ (.x (.tbl r)) = []) :
    RsaRuns body rg ι (cstChirpBox ι hι hT hQ rg (ldcPrep rg)) ρ
      (Function.update (Function.update (Function.update ρ .kr
        (cstream A w (cstNumBox (Mult.Sizes.p n) (Mult.Sizes.t n) (Mult.Pipeline.chirpKernel n)) ++
          ρ .kr)) (.x .tS) []) (.x .sS) [])
      (cstChirpCost T w (List.ofFn (Mult.Sizes.t n)) fun k =>
        ldcAxisCost W w (Mult.Sizes.p n) (chirpGuard (Mult.Sizes.d n))
          ((List.ofFn (Mult.Sizes.t n)).getD k 0) ((List.ofFn (Mult.Sizes.s n)).getD k 0)) := by
  set xx : ldcX → List (Fin (A + 4)) := fun j => ρ (.x j) with hxx
  have hpre := ldc_prep_hprep (body := body) (ι := ι) hrg hdisj (Mult.Sizes.t n) (Mult.Sizes.s n) xx
    hwr hwn hwW (fun k => Nat.pos_of_ne_zero (NeZero.ne (Mult.Sizes.t n k))) hsN hW htU hsU hpU hgU
    hwU htb
  have h := cst_chirpBox_kernel (body := body) hrg hdisj hι hT hQ hA n hd hw (ldcPrep rg)
    (ldcCfg xx (List.ofFn (Mult.Sizes.t n)) (List.ofFn (Mult.Sizes.s n)))
    (fun k => List.replicate ((List.ofFn (Mult.Sizes.t n)).getD k 0) tick)
    (fun k => ldcAxisCost W w (Mult.Sizes.p n) (chirpGuard (Mult.Sizes.d n))
      ((List.ofFn (Mult.Sizes.t n)).getD k 0) ((List.ofFn (Mult.Sizes.s n)).getD k 0))
    hpre
    (fun k hk => by
      rw [List.length_replicate, cst_getD (by simpa using hk), List.getElem_ofFn])
    ρ hb hax
    (fun j => by
      cases j with
      | tS => simp [ldcCfg, htS]
      | sS => simp [ldcCfg, hsS]
      | _ => rfl)
  have hd1 : (List.ofFn (Mult.Sizes.t n)).drop (Mult.Sizes.d n) = [] :=
    List.drop_eq_nil_of_le (by simp)
  have hd2 : (List.ofFn (Mult.Sizes.s n)).drop (Mult.Sizes.d n) = [] :=
    List.drop_eq_nil_of_le (by simp)
  refine h.congr ?_
  funext r
  rcases r with y | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals try (simp [Function.update_apply]; done)
  rcases j with r | _ | _ | _ | _ | _ | _ | _
  all_goals simp [ldcCfg, hd1, hd2, ldcBlocks, hxx]

end Contract

/-! ### Costs -/

/-- One axis of the loader: the chirp table machine and `O(W)` steps per unit of the unary
values and per table variable. -/
theorem ldc_axisCost_le (W w p g N s : ℕ) :
    ldcAxisCost W w p g N s ≤
      (N * (39 * (p + g) + 641) + 200 * (p + g) + 4 * w + 1503) * tblC W w + 2 * (N * w) +
        2 * (p + g + N + s + w) * (4 * W + 10) + 534 * W + 568 := by
  unfold ldcAxisCost ldcLoadCost ldcHostCost
  have h1 : 4 * N ≤ N * (4 * W + 10) := by nlinarith
  have h2 : 4 * s ≤ s * (4 * W + 10) := by nlinarith
  nlinarith

/-- **The cost of the chirp stage** (`cst_chirpCost_le`): the loads of the `d` axes and at most
`4 d V cmulCost T w` for the products, `V = ∏ t_k`. -/
theorem ldChirpStage_cost_le (T n : ℕ) {w W : ℕ} (hd : 1 ≤ Mult.Sizes.d n) :
    cstChirpCost T w (List.ofFn (Mult.Sizes.t n)) (fun k =>
        ldcAxisCost W w (Mult.Sizes.p n) (chirpGuard (Mult.Sizes.d n))
          ((List.ofFn (Mult.Sizes.t n)).getD k 0) ((List.ofFn (Mult.Sizes.s n)).getD k 0)) ≤
      ∑ k ∈ Finset.range (Mult.Sizes.d n),
          ldcAxisCost W w (Mult.Sizes.p n) (chirpGuard (Mult.Sizes.d n))
            ((List.ofFn (Mult.Sizes.t n)).getD k 0) ((List.ofFn (Mult.Sizes.s n)).getD k 0) +
        4 * Mult.Sizes.d n * (List.ofFn (Mult.Sizes.t n)).prod * cmulCost T w := by
  have h := cst_chirpCost_le T w (List.ofFn (Mult.Sizes.t n)) (fun k =>
      ldcAxisCost W w (Mult.Sizes.p n) (chirpGuard (Mult.Sizes.d n))
        ((List.ofFn (Mult.Sizes.t n)).getD k 0) ((List.ofFn (Mult.Sizes.s n)).getD k 0))
    (by simpa using hd)
    (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact Nat.one_le_iff_ne_zero.2 (NeZero.ne (Mult.Sizes.t n i)))
  simpa using h

end

end IntegerMultBounds.MathlibTM2.Fast.ChirpSt
