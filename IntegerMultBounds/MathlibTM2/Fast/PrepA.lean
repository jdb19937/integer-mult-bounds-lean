module

public import IntegerMultBounds.MathlibTM2.Fast.PrepBase
public import IntegerMultBounds.MathlibTM2.Fast.ResampAAll
import IntegerMultBounds.MathlibTM2.Fast.ResampBPipe
public import IntegerMultBounds.MathlibTM2.Fast.ResampBMath
public import IntegerMultBounds.MathlibTM2.Fast.TableWeight
import IntegerMultBounds.NLogN.ResamplingManuscript
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The parameter loader of `Ã`

`preA rg ι hd` is the loader `prep` of `ResampA.rsaAllP`: a fixed program over the stage layout
`rg : RsaR (RsaX t₀) → Fin T` (with the table machine on the multiplier registers `ι`), which
configures the register file for the next axis.

**Parameter register.** The complex-product register `c .out` (not used by the stage) holds the
records of the axes in processing order `d - 1, d - 2, …, 0`; the loader consumes the record on
top. A record (`PreAxA.fields`) is eleven unary fields (`preFld`, `v` ticks and the delimiter
`bitSymbol false`): `t`, `q`, `m`, `s`, `L`, `Ld`, `P`, `G`, `α`, `p`, `W` — the target length
`t = 2^L`, the product shift `q` (the length of `pn`), the window radius `m`, the source length
`s`, the target widths `L` and `Ld` of the axis and of the last axis, the products `P` and `G` of
the target lengths before the axis and strictly between it and the last axis, the table
parameters `α`, `p`, and the word size `W` of the table machine. The coefficient width `w` is the
length of `c .wn`.

**Program** (`preA`).
1. Clear the previous axis: `ys`, `cS`, `cM`, `cP`, `cW`, `cT`, `rr`, `bS`, `pn` and the five
   interchange headers.
2. Take the fields onto `cT`, `pn`, `ea`, `eb`, `er`, `ka`, `kb`, `kx`, `kW`, `kT`, `atm`.
3. Counters: `cW = 2m + 1`, `cS = s w`, `cM = m w`, `cP = (t - s) w` (unary products
   `preUMul`), `rr = binSyms L 0`, `bS = binSyms L s` (`toBinary`).
4. Headers: the canonical binary digits of `P`, `G`, `3 w`, `L`, `Ld` (`sxBinConv`) under a
   separator on the header registers `sw (reg (hd k))`.
5. The table `tableA` (`tblStreamACode`, `t (2m + 1)` entries) onto `ys`, by the table machine on
   the multiplier registers (`preVM`).
6. Clear the fields.

**Results.**
* `preA_runs`: from a register file `V` with empty loader scratch (`PreFreeA`), the record `D`
  on top of `c .out` and `w` symbols on `c .wn`, the loader ends in `preLoadA V hd w D rest`: the
  table stream `tblStreamA = cstream (rsaTabL t (2m + 1) (rsaWA s t m tableA))`
  (`tblStreamA_cstream`) on `ys`, `q` ticks on `pn`, the counters `cS = s w`, `cM = m w`,
  `cP = (t - s) w`, `cW = 2m + 1`, `cT = t`, `rr = binSyms L 0`, `bS = binSyms L s`, the bank
  headers `rsaBank hd (D.hs w)` (`preBankA`), and `rest` on `c .out`. `preA_rsaWith` is the
  same contract in the form `hprep` of `rsa_all`; `preLoadA_idle` gives `RsaIdle` of a loaded
  file over a base file (`PreBaseA`).
* `rsaStage_exec`: `rsa_all_lineA` with the loader: the configured files `preCfgA` (one record
  per axis, `preRecsA`), the loader bounds `preCpA`, the window `windowA ≤ s_i`
  (`pre_windowA_le_s`), the table entries fitting `w ≥ p + 1` bits (`pre_tableA_fits`), the
  headers, and every intermediate box of the stage in the unit disk (`pre_flat_ball`, from
  `pre_lineA_ball`: `Ã` keeps the unit disk, by `ball_of_approx`), so all numerators fit
  `w ≥ p + 3` bits.

**Cost** (`preCostA`): clearing the previous axis (`Σ (2 |old| + 2)` over the cleared
registers), `3 Σ fields + 34` for the record, `O((s + m + t)(w + L))` for the counters,
`16 (P + G + 3 w + L + Ld) + O(w)` for the headers, and the table machine:
`preKA D = t (2m + 1)(310 p + 110) + 8 t + 150 p + 420` atoms, each at most
`tblC W w = 32 (W + 4)² + 8 w` steps, plus `O(W + Σ (s, t, α, m, p) · W)` for its setup and
`2 t (2m + 1) w` for moving the stream.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


noncomputable section

/-- The per-axis parameters of `Ã` read by the loader. -/
structure PreAxA where
  /-- the target length `t = 2^L` -/
  t : ℕ
  /-- the product shift -/
  q : ℕ
  /-- the window radius -/
  m : ℕ
  /-- the source length -/
  s : ℕ
  /-- the target width -/
  L : ℕ
  /-- the target width of the last axis -/
  Ld : ℕ
  /-- the product of the target lengths before the axis -/
  P : ℕ
  /-- the product of the target lengths strictly between the axis and the last axis -/
  G : ℕ
  /-- the table parameter `α` -/
  α : ℕ
  /-- the table precision -/
  p : ℕ
  /-- the word size of the table machine -/
  W : ℕ

/-- The fields of a record, in reading order. -/
def PreAxA.fields (D : PreAxA) : List ℕ := [D.t, D.q, D.m, D.s, D.L, D.Ld, D.P, D.G, D.α, D.p, D.W]

/-- The canonical headers of the interchange of the axis with the last axis. -/
def PreAxA.hs (D : PreAxA) (w : ℕ) : Fin 5 → List Bool :=
  fun k => sxBits (BinaryInterchangeRun.values D.P D.G (3 * w) D.L D.Ld k)

variable {t₀ T Q K : ℕ} {U F : Type}

/-- The header register `k` of the interchange bank. -/
def preHA (hd : Fin 5 → Fin t₀) (k : Fin 5) : RsaR (RsaX t₀) := .x (.sw (reg (hd k)))

/-- The registers cleared before loading an axis. -/
def preClrA (hd : Fin 5 → Fin t₀) : List (RsaR (RsaX t₀)) :=
  [.c .ys, .cS, .cM, .cP, .cW, .cT, .rr, .bS, .c .pn, preHA hd 0, preHA hd 1, preHA hd 2, preHA hd 3,
    preHA hd 4]

/-- The registers receiving the fields. -/
def preDstA : List (RsaR (RsaX t₀)) := [.cT, .c .pn, .ea, .eb, .er, .ka, .kb, .kx, .kW, .kT, .atm]

/-- The field registers cleared at the end. -/
def preScrA : List (RsaR (RsaX t₀)) := [.ea, .eb, .er, .ka, .kb, .kx, .kW, .kT, .atm]

/-- The loads of the table machine: `s`, `t`, `α`, `m`, `p` into the variables of
`tblStreamACode`. -/
def preLsA : List (RsaR (RsaX t₀) × Fin 48) := [(.eb, 34), (.cT, 35), (.kW, 36), (.ea, 39), (.kT, 19)]

section Prog

variable (rg : RsaR (RsaX t₀) → Fin T) (ι : Fin 64 → Fin T) (hd : Fin 5 → Fin t₀)

/-- The counters and the binary registers from the fields. -/
def preNumA : Pr F T Q (prime + K) U :=
  .seq (umul 2 (rg .ea) (rg .cW) (rg .sm))
  (.seq (.act (.push (.rt (rg .cW)) (fun _ => tick) .done))
  (.seq (preUMul (rg .eb) (rg (.c .wn)) (rg .cS) (rg .sm) (rg .pz))
  (.seq (preUMul (rg .ea) (rg (.c .wn)) (rg .cM) (rg .sm) (rg .pz))
  (.seq (ucopy (rg .cT) (rg .sm2) (rg .sm))
  (.seq (usub (rg .eb) (rg .sm2) (rg .sm))
  (.seq (preUMul (rg .sm2) (rg (.c .wn)) (rg .cP) (rg .sm) (rg .pz))
  (.seq (uclear (rg .sm2))
  (.seq (zeroBits (rg .er) (rg .rr) (rg .sm))
    (toBinary (rg .eb) (rg .er) (rg .bS) (rg .sm) (rg .pz) (rg .bza))))))))))

/-- The five interchange headers. -/
def preHdrA : Pr F T Q (prime + K) U :=
  .seq (umul 3 (rg (.c .wn)) (rg .sm2) (rg .sm))
  (.seq (preHdr (rg .kb) (rg (preHA hd 0)) (rg .sm) (rg .pz))
  (.seq (preHdr (rg .kx) (rg (preHA hd 1)) (rg .sm) (rg .pz))
  (.seq (preHdr (rg .sm2) (rg (preHA hd 2)) (rg .sm) (rg .pz))
  (.seq (preHdr (rg .er) (rg (preHA hd 3)) (rg .sm) (rg .pz))
  (.seq (preHdr (rg .ka) (rg (preHA hd 4)) (rg .sm) (rg .pz))
    (uclear (rg .sm2)))))))

/-- **The loader of `Ã`.** -/
def preA : Pr F T Q (prime + K) U :=
  .seq (preClears ((preClrA hd).map rg))
  (.seq (preTakes (rg (.c .out)) (preDstA.map rg))
  (.seq (preNumA rg)
  (.seq (preHdrA rg hd)
  (.seq (preVM (preLay rg ι) .atm (.c .wn) preLsA tblStreamACode (.c .ys))
    (preClears (preScrA.map rg))))))

end Prog

/-! ### Register files -/

section Files

variable {A : ℕ}

/-- The register file of the stage with the table machine empty. -/
def preSt (V : RsaV (RsaX t₀) A) : RsaR (RsaX t₀) ⊕ TblR 48 → List (Fin (A + 4)) :=
  Sum.elim V.get fun _ => []

/-- The bank after clearing the headers. -/
def preClrX (xr : RsaX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) :
    RsaX t₀ → List (Fin (A + 4))
  | .sw j => if ∃ k, reg (hd k) = j then [] else xr (.sw j)
  | x => xr x

/-- The bank with the headers `hs`. -/
def preBankA (xr : RsaX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀) (hs : Fin 5 → List Bool) :
    RsaX t₀ → List (Fin (A + 4))
  | .sw j => if ∃ k, reg (hd k) = j then rsaBank hd hs j else xr (.sw j)
  | x => xr x

lemma preHA_iff (hd : Fin 5 → Fin t₀) (j : Fin (swapT t₀)) :
    (∃ k, reg (hd k) = j) ↔
      (j = reg (hd 0) ∨ j = reg (hd 1) ∨ j = reg (hd 2) ∨ j = reg (hd 3) ∨ j = reg (hd 4)) := by
  constructor
  · rintro ⟨k, rfl⟩; fin_cases k <;> simp
  · rintro (h | h | h | h | h) <;> exact ⟨_, h.symm⟩

/-- After step 1. -/
def preV1 (V : RsaV (RsaX t₀) A) (hd : Fin 5 → Fin t₀) : RsaV (RsaX t₀) A :=
  { V with
    cr := Function.update (Function.update V.cr .ys []) .pn []
    cS := [], cM := [], cP := [], cW := [], cT := [], rr := [], bS := []
    xr := preClrX V.xr hd }

/-- After step 2. -/
def preV2 (V : RsaV (RsaX t₀) A) (D : PreAxA) (rest : List (Fin (A + 4))) : RsaV (RsaX t₀) A :=
  { V with
    cr := Function.update (Function.update V.cr .out rest) .pn (List.replicate D.q tick)
    cT := List.replicate D.t tick
    ea := List.replicate D.m tick, eb := List.replicate D.s tick, er := List.replicate D.L tick
    ka := List.replicate D.Ld tick, kb := List.replicate D.P tick, kx := List.replicate D.G tick
    kW := List.replicate D.α tick, kT := List.replicate D.p tick, atm := List.replicate D.W tick }

/-- After step 3. -/
def preV3 (V : RsaV (RsaX t₀) A) (D : PreAxA) (w : ℕ) : RsaV (RsaX t₀) A :=
  { V with
    cW := List.replicate (2 * D.m + 1) tick, cS := List.replicate (D.s * w) tick
    cM := List.replicate (D.m * w) tick, cP := List.replicate ((D.t - D.s) * w) tick
    rr := binSyms D.L 0, bS := binSyms D.L D.s }

/-- The step bound of step 3. -/
def preNumCost (D : PreAxA) (w : ℕ) : ℕ :=
  (4 * D.m + 4) + 1 + (D.s * (4 * w + 7) + 2 * D.s + 4) + (D.m * (4 * w + 7) + 2 * D.m + 4) +
    (4 * D.t + 4) + (4 * D.s + 4) + ((D.t - D.s) * (4 * w + 7) + 2 * (D.t - D.s) + 4) +
    (2 * (D.t - D.s) + 2) + (4 * D.L + 4) + (D.s * (4 * D.L + 10) + 4 * D.L + 8)

/-- The step bound of step 4. -/
def preHdrCost (D : PreAxA) (w : ℕ) : ℕ :=
  (4 * w + 4) + (16 * D.P + 5) + (16 * D.G + 5) + (16 * (3 * w) + 5) + (16 * D.L + 5) +
    (16 * D.Ld + 5) + (2 * (3 * w) + 2)

/-- After step 6. -/
def preV6 (V : RsaV (RsaX t₀) A) : RsaV (RsaX t₀) A :=
  { V with
    ea := [], eb := [], er := [], ka := [], kb := [], kx := [], kW := [], kT := [], atm := [] }

/-- The atom bound of `tblStreamACode`. -/
def preKA (D : PreAxA) : ℕ := D.t * (2 * D.m + 1) * (310 * D.p + 110) + 8 * D.t + (150 * D.p + 420)

/-- The register file after loading the axis `D` from `V` (coefficient width `w`, the rest
`rest` of the parameter register). -/
def preLoadA (V : RsaV (RsaX t₀) A) (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxA)
    (rest : List (Fin (A + 4))) : RsaV (RsaX t₀) A :=
  { V with
    cr := Function.update (Function.update (Function.update V.cr .ys
      (tblStreamA A w D.s D.t D.α D.p D.m)) .pn (List.replicate D.q tick)) .out rest
    cS := List.replicate (D.s * w) tick, cM := List.replicate (D.m * w) tick
    cP := List.replicate ((D.t - D.s) * w) tick, cW := List.replicate (2 * D.m + 1) tick
    cT := List.replicate D.t tick, rr := binSyms D.L 0, bS := binSyms D.L D.s
    xr := preBankA V.xr hd (D.hs w) }

/-- The scratch registers of the loader are empty. -/
structure PreFreeA (V : RsaV (RsaX t₀) A) : Prop where
  ea : V.ea = []
  eb : V.eb = []
  er : V.er = []
  ka : V.ka = []
  kb : V.kb = []
  kx : V.kx = []
  kW : V.kW = []
  kT : V.kT = []
  atm : V.atm = []
  sm : V.sm = []
  pz : V.pz = []
  sm2 : V.sm2 = []

/-- **The step bound of the loader**: clearing the previous axis (the old contents of the
cleared registers of `V`), reading the record, the counters, the headers, the table
(`preKA D` atoms of the table machine at word size `W`, `t (2m + 1)` entries of `w` symbols),
and clearing the fields. -/
def preCostA (V : RsaV (RsaX t₀) A) (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxA) : ℕ :=
  (((preClrA hd).map fun r => 2 * (V.get r).length + 2).sum + 1) + (3 * D.fields.sum + 3 * 11 + 1) +
    preNumCost D w + preHdrCost D w +
    preVMCost 48 D.W w [D.s, D.t, D.α, D.m, D.p] (preKA D) (D.t * (2 * D.m + 1) * w) +
    (2 * (D.m + D.s + D.L + D.Ld + D.P + D.G + D.α + D.p + D.W) + 19)

end Files

/-! ### Steps 1 and 2 -/

section Steps

variable {body : F → Pr F T Q (prime + K) U} {rg : RsaR (RsaX t₀) → Fin T} {ι : Fin 64 → Fin T}

variable (hrg : Function.Injective rg) (hι : Function.Injective ι) (hdisj : ∀ r j, rg r ≠ ι j)
include hrg hι hdisj

omit hrg hι hdisj in
lemma preLay_map (l : List (RsaR (RsaX t₀))) :
    (l.map Sum.inl).map (preLay rg ι) = l.map rg := by
  simp [List.map_map, Function.comp_def, preLay]

omit hrg hι hdisj in
lemma preHA_nodup {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd) :
    ((preClrA hd).map (Sum.inl : _ → RsaR (RsaX t₀) ⊕ TblR 48)).Nodup := by
  have h : ∀ a b, reg (hd a) = reg (hd b) ↔ a = b := fun a b =>
    ⟨fun e => hdi (BinaryInterchangeRun.slot_injective e), fun e => e ▸ rfl⟩
  simp [preClrA, preHA, List.nodup_cons, h]

theorem preA_clr {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd) (V : RsaV (RsaX t₀) (prime + K)) :
    TwRuns body (preLay rg ι) (preClears ((preClrA hd).map rg)) (preSt V) (preSt (preV1 V hd))
      (((preClrA hd).map fun r => 2 * (V.get r).length + 2).sum + 1) := by
  have h := preClears_runs (body := body) (preLay_inj hrg hι hdisj) _ (preHA_nodup hdi) (preSt V)
  rw [preLay_map] at h
  refine twRuns_congr (twRuns_mono h (by simp [List.map_map, Function.comp_def, preSt])) ?_
  funext r
  rcases r with r | x
  · cases r <;> simp [preSt, preV1, preClrA, preHA, RsaV.get]
    · rename_i x; cases x <;> simp
    · rename_i j; cases j <;> simp [preClrX, preHA_iff]
  · simp [preSt, preClrA]

theorem preA_parse (V : RsaV (RsaX t₀) (prime + K)) (D : PreAxA) (rest : List (Fin (prime + K + 4)))
    (hout : V.cr .out = preRec D.fields ++ rest) (hT : V.cT = []) (hpn : V.cr .pn = [])
    (hea : V.ea = []) (heb : V.eb = []) (her : V.er = []) (hka : V.ka = []) (hkb : V.kb = [])
    (hkx : V.kx = []) (hkW : V.kW = []) (hkT : V.kT = []) (hatm : V.atm = []) :
    TwRuns body (preLay rg ι) (preTakes (rg (.c .out)) (preDstA.map rg)) (preSt V)
      (preSt (preV2 V D rest)) (3 * D.fields.sum + 3 * 11 + 1) := by
  have h := preTakes_runs (body := body) (preLay_inj hrg hι hdisj) (.inl (.c .out))
    (preDstA.map Sum.inl) D.fields (by simp [preDstA, PreAxA.fields]) (by simp [preDstA])
    (preSt V) rest (by simp [preSt, hout]) (by
      simp [preDstA, preSt, hT, hpn, hea, heb, her, hka, hkb, hkx, hkW, hkT, hatm])
  rw [preLay_map] at h
  simp only [PreAxA.fields, List.length_cons, List.length_nil] at h ⊢
  refine twRuns_congr h ?_
  simp only [preTV, preDstA, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
    List.foldl_cons, List.foldl_nil]
  funext r
  rcases r with r | x
  · cases r <;> simp only [Function.update_apply, preSt, preV2, RsaV.get, Sum.elim_inl,
      Sum.inl.injEq, reduceCtorEq, ite_false, ite_true, RsaR.c.injEq]
  · simp only [Function.update_apply, reduceCtorEq, ite_false, preSt, Sum.elim_inr]

set_option maxRecDepth 4000 in
theorem preA_num (V : RsaV (RsaX t₀) (prime + K)) (D : PreAxA) (w : ℕ)
    (hea : V.ea = List.replicate D.m tick) (heb : V.eb = List.replicate D.s tick)
    (her : V.er = List.replicate D.L tick) (hT : V.cT = List.replicate D.t tick)
    (hwn : (V.cr .wn).length = w) (hW : V.cW = []) (hS : V.cS = []) (hM : V.cM = [])
    (hP : V.cP = []) (hrr : V.rr = []) (hbS : V.bS = []) (hsm : V.sm = []) (hpz : V.pz = [])
    (hsm2 : V.sm2 = []) :
    TwRuns body (preLay rg ι) (preNumA rg) (preSt V) (preSt (preV3 V D w)) (preNumCost D w) := by
  have htg := preLay_inj hrg hι hdisj
  refine twRuns_congr (twRuns_mono
    (twRuns_seq (twRuns_umul (body := body) htg 2 (a := .inl .ea) (b := .inl .cW) (t := .inl .sm)
      (by simp) (by simp) (by simp) (preSt V) ?_)
    (twRuns_seq (twRuns_push (body := body) htg (.inl .cW) tick _)
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl .eb) (b := .inl (.c .wn))
      (c := .inl .cS) (t₁ := .inl .sm) (t₂ := .inl .pz) (by simp) _ ?_ ?_)
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl .ea) (b := .inl (.c .wn))
      (c := .inl .cM) (t₁ := .inl .sm) (t₂ := .inl .pz) (by simp) _ ?_ ?_)
    (twRuns_seq (twRuns_ucopy (body := body) htg (a := .inl .cT) (b := .inl .sm2) (t := .inl .sm)
      (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (twRuns_usub (body := body) htg (a := .inl .eb) (b := .inl .sm2) (t := .inl .sm)
      (by simp) (by simp) (by simp) _ ?_)
    (twRuns_seq (preUMul_runs (body := body) htg (a := .inl .sm2) (b := .inl (.c .wn))
      (c := .inl .cP) (t₁ := .inl .sm) (t₂ := .inl .pz) (by simp) _ ?_ ?_)
    (twRuns_seq (twRuns_uclear (body := body) htg (.inl .sm2) _)
    (twRuns_seq (twRuns_zeroBits (body := body) htg (len := .inl .er) (z := .inl .rr)
      (t := .inl .sm) (by simp) (by simp) (by simp) _ ?_)
    (twRuns_toBinary (body := body) htg (u := .inl .eb) (wR := .inl .er) (c := .inl .bS)
      (t := .inl .sm) (tmp := .inl .pz) (by simp) (rg .bza) _ ?_ ?_ ?_)))))))))) ?_) ?_
  all_goals try (simp only [preSt, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
    ite_false, ite_true, RsaV.get_sm, RsaV.get_pz, RsaV.get_sm2, RsaV.get_ea, RsaV.get_eb,
    RsaV.get_er, RsaV.get_cT, RsaV.get_cW, RsaV.get_cS, RsaV.get_cM, RsaV.get_cP, RsaV.get_rr,
    RsaV.get_bS, RsaV.get_c, hea, heb, her, hT, hwn, hW, hS, hM, hP, hrr, hbS, hsm,
    hpz, hsm2, List.append_nil, List.length_replicate]; done)
  · simp only [preSt, Function.update_apply, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq,
      ite_false, ite_true, RsaV.get_sm2, RsaV.get_ea, RsaV.get_eb,
      RsaV.get_er, RsaV.get_cT, RsaV.get_cW, RsaV.get_cS, RsaV.get_cM, RsaV.get_cP, RsaV.get_rr,
      RsaV.get_c, hea, heb, her, hT, hwn, hW, hS, hM, hP, hrr, 
      hsm2, List.append_nil, List.length_replicate, List.length_drop]
    unfold preNumCost
    exact le_of_eq (by ring)
  · funext r
    rcases r with r | x
    · cases r <;> simp only [Function.update_apply, preSt, preV3, RsaV.get, Sum.elim_inl,
        Sum.inl.injEq, reduceCtorEq, ite_false, ite_true]
      all_goals simp [hea, heb, her, hT, hwn, hW, hS, hM, hP, hrr, hsm2,
        List.replicate_succ]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preSt, Sum.elim_inr]

theorem preA_hdr {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd)
    (V : RsaV (RsaX t₀) (prime + K)) (D : PreAxA) (w : ℕ)
    (hkb : V.kb = List.replicate D.P tick) (hkx : V.kx = List.replicate D.G tick)
    (her : V.er = List.replicate D.L tick) (hka : V.ka = List.replicate D.Ld tick)
    (hwn : (V.cr .wn).length = w) (hsm : V.sm = []) (hpz : V.pz = []) (hsm2 : V.sm2 = [])
    (hH : ∀ k, V.xr (.sw (reg (hd k))) = []) :
    TwRuns body (preLay rg ι) (preHdrA rg hd) (preSt V)
      (preSt { V with xr := preBankA V.xr hd (D.hs w) }) (preHdrCost D w) := by
  have htg := preLay_inj hrg hι hdisj
  have hinj : ∀ a b, reg (hd a) = reg (hd b) ↔ a = b := fun a b =>
    ⟨fun e => hdi (BinaryInterchangeRun.slot_injective e), fun e => e ▸ rfl⟩
  have hH' : ∀ k, V.get (preHA hd k) = [] := fun k => hH k
  refine twRuns_congr (twRuns_mono
    (twRuns_seq (twRuns_umul (body := body) htg 3 (a := .inl (.c .wn)) (b := .inl .sm2)
      (t := .inl .sm) (by simp) (by simp) (by simp) (preSt V) ?_)
    (twRuns_seq (preHdr_runs (body := body) htg (src := .inl .kb) (h := .inl (preHA hd 0))
      (t₁ := .inl .sm) (t₂ := .inl .pz) (by simp [preHA]) _ ?_ ?_ ?_)
    (twRuns_seq (preHdr_runs (body := body) htg (src := .inl .kx) (h := .inl (preHA hd 1))
      (t₁ := .inl .sm) (t₂ := .inl .pz) (by simp [preHA]) _ ?_ ?_ ?_)
    (twRuns_seq (preHdr_runs (body := body) htg (src := .inl .sm2) (h := .inl (preHA hd 2))
      (t₁ := .inl .sm) (t₂ := .inl .pz) (by simp [preHA]) _ ?_ ?_ ?_)
    (twRuns_seq (preHdr_runs (body := body) htg (src := .inl .er) (h := .inl (preHA hd 3))
      (t₁ := .inl .sm) (t₂ := .inl .pz) (by simp [preHA]) _ ?_ ?_ ?_)
    (twRuns_seq (preHdr_runs (body := body) htg (src := .inl .ka) (h := .inl (preHA hd 4))
      (t₁ := .inl .sm) (t₂ := .inl .pz) (by simp [preHA]) _ ?_ ?_ ?_)
      (twRuns_uclear (body := body) htg (.inl .sm2) _))))))) ?_) ?_
  all_goals try (simp (config := { decide := true }) only [preSt, preHA, Function.update_apply,
    Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false, ite_true, RsaV.get_sm, RsaV.get_pz,
    RsaV.get_sm2, RsaV.get_er, RsaV.get_ka, RsaV.get_kb, RsaV.get_kx,
    RsaV.get_x, RsaV.get_c, RsaR.x.injEq, RsaX.sw.injEq, hinj, hkb, hkx, her, hka,
    hwn, hsm, hpz, hsm2, hH, List.append_nil, List.length_replicate]; done)
  · simp (config := { decide := true }) only [preSt, preHA, Function.update_apply,
      Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, ite_false, ite_true, 
      RsaV.get_sm2, RsaV.get_er, RsaV.get_ka, RsaV.get_kb, RsaV.get_kx,
      RsaV.get_c, hkb, hkx, her, hka,
      hwn, hsm2, List.append_nil, List.length_replicate]
    unfold preHdrCost
    exact le_of_eq (by ring)
  · funext r
    rcases r with r | x
    · cases r
      case x j =>
        simp only [Function.update_apply, preSt, preHA, RsaV.get, Sum.elim_inl,
          Sum.inl.injEq, reduceCtorEq, ite_false, ite_true, RsaR.x.injEq]
        rcases j with j | _ | _ | _ | _ | _
        · by_cases hj : ∃ k, reg (hd k) = j
          · obtain ⟨k, rfl⟩ := hj
            fin_cases k <;> simp (config := { decide := true }) [preBankA, hinj, rsaBank_hd hdi,
              PreAxA.hs, BinaryInterchangeRun.values, hkb, hkx, her, hka, hwn, hsm2]
          · have hne : ∀ k, j ≠ reg (hd k) := fun k h => hj ⟨k, h.symm⟩
            simp [preBankA, hj, hne]
        all_goals simp [preBankA]
      all_goals simp only [Function.update_apply, preSt, preHA, RsaV.get, Sum.elim_inl,
        Sum.inl.injEq, reduceCtorEq, ite_false, ite_true]
      all_goals simp [hsm2]
    · simp only [Function.update_apply, reduceCtorEq, ite_false, preSt, Sum.elim_inr]

omit hrg hι hdisj in
lemma preA_lt {D : PreAxA} (hα : 2 ≤ D.α) (ht : 0 < D.t)
    (hW : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W) :
    D.s < 2 ^ D.W ∧ D.t < 2 ^ D.W ∧ D.α < 2 ^ D.W ∧ D.m < 2 ^ D.W ∧ D.p < 2 ^ D.W := by
  obtain ⟨h1, -, h3, h4⟩ := tbl_W_facts hα (Nat.mul_pos (by omega) (Nat.succ_pos D.m)) hW
  set N := (D.s + D.t) * (D.m + 1)
  have hN : 1 ≤ N := Nat.mul_pos (by omega) (Nat.succ_pos D.m)
  have hsN : D.s + D.t ≤ N := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hmN : D.m + 1 ≤ N := Nat.le_mul_of_pos_left _ (by omega)
  have hNN : N ≤ N * N := Nat.le_mul_self N
  have hαα : D.α ≤ D.α * D.α * (N * N) := by nlinarith
  have hpW : D.p < 2 ^ D.W := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self).le
  exact ⟨by omega, by omega, by omega, by omega, hpW⟩

theorem preA_vm (V : RsaV (RsaX t₀) (prime + K)) (D : PreAxA) (w : ℕ)
    (hea : V.ea = List.replicate D.m tick) (heb : V.eb = List.replicate D.s tick)
    (hT : V.cT = List.replicate D.t tick) (hkW : V.kW = List.replicate D.α tick)
    (hkT : V.kT = List.replicate D.p tick) (hatm : V.atm = List.replicate D.W tick)
    (hwn : (V.cr .wn).length = w) (hys : V.cr .ys = []) (hp : 13 ≤ D.p) (hα : 2 ≤ D.α)
    (ht : 0 < D.t) (hwW : w ≤ D.W)
    (hW : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W) :
    TwRuns body (preLay rg ι) (preVM (preLay rg ι) .atm (.c .wn) preLsA tblStreamACode (.c .ys))
      (preSt V)
      (preSt { V with cr := Function.update V.cr .ys (tblStreamA (prime + K) w D.s D.t D.α D.p D.m) })
      (preVMCost 48 D.W w [D.s, D.t, D.α, D.m, D.p] (preKA D) (D.t * (2 * D.m + 1) * w)) := by
  have htg := preLay_inj hrg hι hdisj
  have hv : preLoadVal (preSt V) preLsA (fun _ => 0) =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (fun _ : Fin 48 => 0) 34 D.s) 35 D.t) 36 D.α) 39 D.m) 19 D.p := by
    simp [preLoadVal, preLsA, preSt, hea, heb, hT, hkW, hkT]
  obtain ⟨hs2, ht2, hα2, hm2, hp2⟩ := preA_lt hα ht hW
  have h := preVM_runs (body := body) htg .atm (.c .wn) preLsA tblStreamACode (.c .ys) (preSt V)
    (fun _ => rfl) (by simp [preSt, hatm]) (by simp [preSt, hwn]) hwW
    (fun j => by
      rw [hv]
      simp only [Function.update_apply]
      split_ifs <;> first | assumption | exact Nat.two_pow_pos _)
    (tblStreamA_do (A := prime + K) (W := D.W) (w := w) ⟨_, []⟩
      (s := D.s) (t := D.t) (α := D.α) (p := D.p) (m := D.m)
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true }))
      (by rw [hv]; simp (config := { decide := true })) hp hα ht hW)
    (tblStreamA (prime + K) w D.s D.t D.α D.p D.m) (fun s' hs' => by
      simp only at hs'; rw [hs', List.append_nil, List.reverse_reverse])
  rw [length_tblStreamA] at h
  refine twRuns_congr (twRuns_mono h (le_of_eq ?_)) ?_
  · simp [preSt, preLsA, hea, heb, hT, hkW, hkT, preKA]
  · simp only [preSt, Sum.update_elim_inl, RsaV.upd_c, Sum.elim_inl, RsaV.get_c, hys,
      List.append_nil]

theorem preA_end (V : RsaV (RsaX t₀) (prime + K)) :
    TwRuns body (preLay rg ι) (preClears (preScrA.map rg)) (preSt V)
      (preSt (preV6 V))
      ((preScrA.map fun r => 2 * (V.get r).length + 2).sum + 1) := by
  have h := preClears_runs (body := body) (preLay_inj hrg hι hdisj) (preScrA.map Sum.inl)
    (by simp [preScrA]) (preSt V)
  rw [preLay_map] at h
  refine twRuns_congr (twRuns_mono h (by simp [List.map_map, Function.comp_def, preSt])) ?_
  funext r
  rcases r with r | x
  · cases r <;> simp [preSt, preScrA, RsaV.get, preV6]
  · simp [preSt, preScrA]

omit hrg hι hdisj in
lemma preBankA_clr (xr : RsaX t₀ → List (Fin (prime + K + 4))) (hd : Fin 5 → Fin t₀)
    (hs : Fin 5 → List Bool) : preBankA (preClrX xr hd) hd hs = preBankA xr hd hs := by
  funext x
  cases x <;> simp only [preBankA, preClrX]
  split_ifs <;> rfl

/-- **The loader of `Ã`.** From a register file `V` whose loader scratch registers are empty,
with the record `D` on top of the parameter register `c .out` and `w` symbols on `c .wn`, `preA`
loads the axis `D`: afterwards the register file is `preLoadA V hd w D rest` (the table
`tableA` on `ys`, the counters, `rr`, `bS`, `pn` and the interchange headers of `D`, the rest
`rest` on `c .out`), within `preCostA V hd w D` steps. Conditions of the table machine:
`13 ≤ p`, `2 ≤ α`, `0 < t`, `w ≤ W` and `α² ((s + t)(m + 1))² 2^(13p+8) < 2^W`. -/
theorem preA_runs {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd)
    (V : RsaV (RsaX t₀) (prime + K)) (D : PreAxA) (rest : List (Fin (prime + K + 4))) (w : ℕ)
    (hF : PreFreeA V) (hout : V.cr .out = preRec D.fields ++ rest)
    (hwn : (V.cr .wn).length = w) (hp : 13 ≤ D.p) (hα : 2 ≤ D.α) (ht : 0 < D.t) (hwW : w ≤ D.W)
    (hW : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W) :
    RsaRuns body rg ι (preA rg ι hd) V.get (preLoadA V hd w D rest).get (preCostA V hd w D) := by
  refine pre_rsaRuns (ρ := V.get) (ρ' := (preLoadA V hd w D rest).get) ?_
  set V1 := preV1 V hd with hV1
  set V2 := preV2 V1 D rest with hV2
  set V3 := preV3 V2 D w with hV3
  set V4 : RsaV (RsaX t₀) (prime + K) := { V3 with xr := preBankA V3.xr hd (D.hs w) } with hV4
  set V5 : RsaV (RsaX t₀) (prime + K) :=
    { V4 with cr := Function.update V4.cr .ys (tblStreamA (prime + K) w D.s D.t D.α D.p D.m) }
    with hV5
  have h1 := preA_clr (body := body) hrg hι hdisj hdi V
  have h2 := preA_parse (body := body) hrg hι hdisj V1 D rest
    (by simp [hV1, preV1, hout]) (by simp [hV1, preV1]) (by simp [hV1, preV1])
    (by simp [hV1, preV1, hF.ea]) (by simp [hV1, preV1, hF.eb]) (by simp [hV1, preV1, hF.er])
    (by simp [hV1, preV1, hF.ka]) (by simp [hV1, preV1, hF.kb]) (by simp [hV1, preV1, hF.kx])
    (by simp [hV1, preV1, hF.kW]) (by simp [hV1, preV1, hF.kT]) (by simp [hV1, preV1, hF.atm])
  have h3 := preA_num (body := body) hrg hι hdisj V2 D w (by simp [hV2, preV2])
    (by simp [hV2, preV2]) (by simp [hV2, preV2]) (by simp [hV2, preV2])
    (by simp [hV2, preV2, hV1, preV1, hwn]) (by simp [hV2, preV2, hV1, preV1])
    (by simp [hV2, preV2, hV1, preV1]) (by simp [hV2, preV2, hV1, preV1])
    (by simp [hV2, preV2, hV1, preV1]) (by simp [hV2, preV2, hV1, preV1])
    (by simp [hV2, preV2, hV1, preV1]) (by simp [hV2, preV2, hV1, preV1, hF.sm])
    (by simp [hV2, preV2, hV1, preV1, hF.pz]) (by simp [hV2, preV2, hV1, preV1, hF.sm2])
  have h4 := preA_hdr (body := body) hrg hι hdisj hdi V3 D w (by simp [hV3, preV3, hV2, preV2])
    (by simp [hV3, preV3, hV2, preV2]) (by simp [hV3, preV3, hV2, preV2])
    (by simp [hV3, preV3, hV2, preV2]) (by simp [hV3, preV3, hV2, preV2, hV1, preV1, hwn])
    (by simp [hV3, preV3, hV2, preV2, hV1, preV1, hF.sm])
    (by simp [hV3, preV3, hV2, preV2, hV1, preV1, hF.pz])
    (by simp [hV3, preV3, hV2, preV2, hV1, preV1, hF.sm2])
    (fun k => by simp only [hV3, preV3, hV2, preV2, hV1, preV1, preClrX]; simp)
  have h5 := preA_vm (body := body) hrg hι hdisj V4 D w (by simp [hV4, hV3, preV3, hV2, preV2])
    (by simp [hV4, hV3, preV3, hV2, preV2]) (by simp [hV4, hV3, preV3, hV2, preV2])
    (by simp [hV4, hV3, preV3, hV2, preV2]) (by simp [hV4, hV3, preV3, hV2, preV2])
    (by simp [hV4, hV3, preV3, hV2, preV2])
    (by simp [hV4, hV3, preV3, hV2, preV2, hV1, preV1, hwn])
    (by simp [hV4, hV3, preV3, hV2, preV2, hV1, preV1]) hp hα ht hwW hW
  have h6 := preA_end (body := body) hrg hι hdisj V5
  have hfin : preV6 V5 = preLoadA V hd w D rest := by
    apply RsaV.ext
    case xr =>
      simp only [preV6, hV5, hV4, hV3, preV3, hV2, preV2, hV1, preV1, preLoadA]
      exact preBankA_clr V.xr hd _
    case cr =>
      simp only [preV6, hV5, hV4, hV3, preV3, hV2, preV2, hV1, preV1, preLoadA]
      funext x
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    all_goals simp [preV6, hV5, hV4, hV3, preV3, hV2, preV2, hV1, preV1, preLoadA,
      hF.ea, hF.eb, hF.er, hF.ka, hF.kb, hF.kx, hF.kW, hF.kT, hF.atm, hF.sm, hF.pz, hF.sm2]
  rw [hfin] at h6
  refine twRuns_mono (twRuns_seq h1 (twRuns_seq h2 (twRuns_seq h3 (twRuns_seq h4
    (twRuns_seq h5 h6))))) (le_of_eq ?_)
  simp [preCostA, preScrA, hV5, hV4, hV3, preV3, hV2, preV2, RsaV.get, PreAxA.fields]
  ring

end Steps

/-! ### Consecutive loads -/

section Glue

open IntegerMultBounds.Schoenhage.Schedule (topN)
open IntegerMultBounds.Resampling.WeightTable (tableA)

variable {A : ℕ}

/-- The register file before the stage: the loader scratch registers, the complex-product
registers other than `ys`, `pn`, `out`, `wn`, `nn`, the output register, the adder spares, the
non-header bank registers, `xt`, `e1`, `e2` are empty; `wn` holds `w` symbols and `nn` holds
`topN w`. -/
structure PreBaseA (V : RsaV (RsaX t₀) A) (w : ℕ) (hd : Fin 5 → Fin t₀) : Prop where
  free : PreFreeA V
  wn : (V.cr .wn).length = w
  nn : (V.cr .nn).length = topN w
  cr : ∀ c, c ≠ .ys → c ≠ .pn → c ≠ .out → c ≠ .wn → c ≠ .nn → V.cr c = []
  ob : V.ob = []
  bxa : V.bxa = []
  bya : V.bya = []
  bza : V.bza = []
  bank : ∀ j, (∀ k, reg (hd k) ≠ j) → V.xr (.sw j) = []
  xt : V.xr .xt = []
  e1 : V.xr .e1 = []
  e2 : V.xr .e2 = []

lemma preBankA_preBankA (xr : RsaX t₀ → List (Fin (A + 4))) (hd : Fin 5 → Fin t₀)
    (hs hs' : Fin 5 → List Bool) : preBankA (preBankA xr hd hs) hd hs' = preBankA xr hd hs' := by
  funext x
  cases x <;> simp only [preBankA]
  split_ifs <;> rfl

lemma preLoadA_preLoadA (V : RsaV (RsaX t₀) A) (hd : Fin 5 → Fin t₀) (w : ℕ) (D D' : PreAxA)
    (r r' : List (Fin (A + 4))) :
    preLoadA (preLoadA V hd w D r) hd w D' r' = preLoadA V hd w D' r' := by
  simp only [preLoadA, preBankA_preBankA]
  congr 1
  funext c
  simp only [Function.update_apply]
  split_ifs <;> rfl

lemma preLoadA_rsaWith (V : RsaV (RsaX t₀) A) (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxA)
    (r l a a' : List (Fin (A + 4))) :
    preLoadA (rsaWith V l a a') hd w D r = rsaWith (preLoadA V hd w D r) l a a' := by
  simp only [preLoadA, rsaWith]
  congr 1
  funext x
  cases x <;> simp [preBankA]

lemma PreFreeA.rsaWith {V : RsaV (RsaX t₀) A} (h : PreFreeA V) (l a a' : List (Fin (A + 4))) :
    PreFreeA (rsaWith V l a a') :=
  ⟨h.ea, h.eb, h.er, h.ka, h.kb, h.kx, h.kW, h.kT, h.atm, h.sm, h.pz, h.sm2⟩

lemma PreFreeA.load {V : RsaV (RsaX t₀) A} (h : PreFreeA V) (hd : Fin 5 → Fin t₀) (w : ℕ)
    (D : PreAxA) (r : List (Fin (A + 4))) : PreFreeA (preLoadA V hd w D r) :=
  ⟨h.ea, h.eb, h.er, h.ka, h.kb, h.kx, h.kW, h.kT, h.atm, h.sm, h.pz, h.sm2⟩

lemma preCostA_rsaWith (V : RsaV (RsaX t₀) A) (hd : Fin 5 → Fin t₀) (w : ℕ) (D : PreAxA)
    (l a a' : List (Fin (A + 4))) : preCostA (rsaWith V l a a') hd w D = preCostA V hd w D := by
  simp [preCostA, preClrA, preHA, rsaWith, RsaV.get]

/-- The stream of `tblStreamACode` is the table stream of the line machine. -/
theorem tblStreamA_cstream (w s t α p m : ℕ) :
    tblStreamA A w s t α p m = cstream A w (rsaTabL t (2 * m + 1) (rsaWA s t m (tableA s t α p))) := by
  rw [tblStreamA_eq]
  simp only [cstream, rsaTabL, List.flatMap_assoc, List.flatMap_map]
  rfl

lemma preLoadA_bank {V : RsaV (RsaX t₀) A} {w : ℕ} {hd : Fin 5 → Fin t₀} (h : PreBaseA V w hd)
    (D : PreAxA) (r : List (Fin (A + 4))) (j : Fin (swapT t₀)) :
    (preLoadA V hd w D r).xr (.sw j) = rsaBank hd (D.hs w) j := by
  simp only [preLoadA, preBankA]
  split_ifs with hj
  · rfl
  · rw [rsaBank_other _ (fun k e => hj ⟨k, e⟩)]
    exact h.bank j (fun k e => hj ⟨k, e⟩)

/-- A loaded register file is configured for its axis. -/
theorem preLoadA_idle {V : RsaV (RsaX t₀) A} {w : ℕ} {hd : Fin 5 → Fin t₀} (h : PreBaseA V w hd)
    (D : PreAxA) (r : List (Fin (A + 4))) :
    RsaIdle (preLoadA V hd w D r) w D.q D.L D.s D.t D.m
      (rsaWA D.s D.t D.m (tableA D.s D.t D.α D.p)) := by
  have e : ∀ c, c ≠ .ys → c ≠ .pn → c ≠ .out → (preLoadA V hd w D r).cr c = V.cr c := by
    intro c h1 h2 h3
    simp [preLoadA, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  have z : ∀ c, c ≠ .ys → c ≠ .pn → c ≠ .out → c ≠ .wn → c ≠ .nn →
      (preLoadA V hd w D r).cr c = [] := fun c h1 h2 h3 h4 h5 => by
    rw [e c h1 h2 h3]; exact h.cr c h1 h2 h3 h4 h5
  exact {
    ready := {
      wn := by rw [e _ (by decide) (by decide) (by decide)]; exact h.wn
      pn := by simp [preLoadA]
      nn := by rw [e _ (by decide) (by decide) (by decide)]; exact h.nn
      tmp := by apply z <;> decide
      u0 := by apply z <;> decide
      u1 := by apply z <;> decide
      u2 := by apply z <;> decide
      u3 := by apply z <;> decide
      ma := by apply z <;> decide
      mb := by apply z <;> decide
      mc := by apply z <;> decide
      md := by apply z <;> decide
      sa := by apply z <;> decide
      sb := by apply z <;> decide
      sc := by apply z <;> decide
      sd := by apply z <;> decide
      p1 := by apply z <;> decide
      p2 := by apply z <;> decide
      p3 := by apply z <;> decide
      p4 := by apply z <;> decide
      qr := by apply z <;> decide
      qi := by apply z <;> decide
      sr := by apply z <;> decide
      si := by apply z <;> decide }
    xs := by apply z <;> decide
    xsv := by apply z <;> decide
    ys := by simp [preLoadA, tblStreamA_cstream]
    ysv := by apply z <;> decide
    acc := by apply z <;> decide
    ea := h.free.ea
    eb := h.free.eb
    er := h.free.er
    ka := h.free.ka
    kb := h.free.kb
    kx := h.free.kx
    kW := h.free.kW
    kT := h.free.kT
    atm := h.free.atm
    sm := h.free.sm
    pz := h.free.pz
    sm2 := h.free.sm2
    bxa := h.bxa
    bya := h.bya
    bza := h.bza
    cS := by simp [preLoadA]
    cM := by simp [preLoadA]
    cP := by simp [preLoadA]
    cW := by simp [preLoadA]
    cT := by simp [preLoadA]
    rr := rfl
    bS := rfl }

end Glue

/-! ### The loader contract of `rsa_all` -/

section Contract

variable {body : F → Pr F T Q (prime + K) U} {rg : RsaR (RsaX t₀) → Fin T} {ι : Fin 64 → Fin T}

/-- **The contract `hprep` of `rsa_all`.** For every box stream `l` and axis counter `a`, `a'`,
`preA` takes `rsaWith V l a a'` to `rsaWith (preLoadA V hd w D rest) l a a'` within
`preCostA V hd w D` steps (the record `D` on top of `c .out`, `rest` below it). -/
theorem preA_rsaWith (hrg : Function.Injective rg) (hι : Function.Injective ι)
    (hdisj : ∀ r j, rg r ≠ ι j) {hd : Fin 5 → Fin t₀} (hdi : Function.Injective hd)
    (V : RsaV (RsaX t₀) (prime + K)) (D : PreAxA) (rest : List (Fin (prime + K + 4))) (w : ℕ)
    (hF : PreFreeA V) (hout : V.cr .out = preRec D.fields ++ rest)
    (hwn : (V.cr .wn).length = w) (hp : 13 ≤ D.p) (hα : 2 ≤ D.α) (ht : 0 < D.t) (hwW : w ≤ D.W)
    (hW : D.α ^ 2 * ((D.s + D.t) * (D.m + 1)) ^ 2 * 2 ^ (13 * D.p + 8) < 2 ^ D.W)
    (l a a' : List (Fin (prime + K + 4))) :
    RsaRuns body rg ι (preA rg ι hd) (rsaWith V l a a').get
      (rsaWith (preLoadA V hd w D rest) l a a').get (preCostA V hd w D) := by
  have h := preA_runs (body := body) hrg hι hdisj hdi (rsaWith V l a a') D rest w (hF.rsaWith l a a')
    (by simp [rsaWith, hout]) (by simp [rsaWith, hwn]) hp hα ht hwW hW
  rwa [preLoadA_rsaWith, preCostA_rsaWith] at h

end Contract

/-! ### The pipeline: sizes, tables and the unit disk -/

section PipeFacts

open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.NLogN
open IntegerMultBounds.Resampling.WeightTable (tableA tables_ok)

variable {n : ℕ}

lemma pre_t_ge (i : Fin (d n)) : 2 ^ (ℓ n - 1) ≤ t n i := by
  unfold t
  split_ifs
  · exact le_rfl
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The precision is at most every source length. -/
lemma pre_p_le_s (h : Big n) (i : Fin (d n)) : p n ≤ s n i := by
  have hb := (h.good.bounds i).lower
  have hd1 := h.one_le_d
  have h2s : t n i < 2 * s n i := by
    by_contra hc
    simp only [not_lt] at hc
    nlinarith
  have ht := pre_t_ge (n := n) i
  have hp := h.eight_p_le_r
  have hl := h.two_le_ℓ
  have e : 2 ^ ℓ n = 2 * 2 ^ (ℓ n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  unfold r at hp
  omega

lemma pre_windowA_le_s (h : Big n) (i : Fin (d n)) : windowA (p n) (alpha n) ≤ s n i :=
  (windowA_spec (alpha_sq_lt_p h)).2.2.trans (pre_p_le_s h i)

lemma pre_log_t (i : Fin (d n)) :
    Nat.log 2 (t n i) = ℓ n - 1 ∨ Nat.log 2 (t n i) = ℓ n := by
  unfold t
  split_ifs <;> simp [Nat.log_pow one_lt_two]

lemma pre_log_last (h : Big n) (hd0 : 0 < d n) :
    Nat.log 2 (t n (rsaStepAx hd0 0)) = ℓ n := by
  rw [t_of_last h _ (by simp [rsaStepAx]; omega), r, Nat.log_pow one_lt_two]

/-- The entries of `tableA` fit `w ≥ p + 1` bits. -/
lemma pre_tableA_fits (h : Big n) (i : Fin (d n)) {w : ℕ} (hw : p n + 1 ≤ w)
    (k : ZMod (t n i)) (j : ℤ) : Fits w ⟨tableA (s n i) (t n i) (alpha n) (p n) k j, 0⟩ := by
  have hα2 := two_le_alpha h.1
  have hp := h.thirteen_le_p
  have he := (tables_ok (s n i) (t n i) (alpha n) (p n) (h.good.lt i) hp hα2 h.alpha_sq_le_p).1 k j
  have hαR : (2 : ℝ) ≤ alpha n := by exact_mod_cast hα2
  have hw0 : 0 ≤ resampWeight (s n i) (t n i) (alpha n : ℝ) k j := by
    unfold resampWeight; positivity
  have hw1 : resampWeight (s n i) (t n i) (alpha n : ℝ) k j ≤ 1 / 2 := by
    unfold resampWeight
    have hx : Real.exp (-Real.pi * (alpha n : ℝ)⁻¹ ^ 2 * (s n i : ℝ) ^ 2 *
        (((k.val : ℝ) / t n i - j / s n i) ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ Real.pi * (alpha n : ℝ)⁻¹ ^ 2 * (s n i : ℝ) ^ 2 *
          (((k.val : ℝ) / t n i - j / s n i) ^ 2) := by positivity
      linarith
    have h1 : 1 / (alpha n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hαR
    have h0 : (0 : ℝ) ≤ 1 / (alpha n : ℝ) := by positivity
    nlinarith [Real.exp_pos (-Real.pi * (alpha n : ℝ)⁻¹ ^ 2 * (s n i : ℝ) ^ 2 *
        (((k.val : ℝ) / t n i - j / s n i) ^ 2))]
  have hP : (0 : ℝ) < 2 ^ p n := by positivity
  have h4 : (8 : ℝ) ≤ 2 ^ p n := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ p n := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlt : (2 : ℝ) ^ p n ≤ 2 ^ (w - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpw : 2 ^ p n * resampWeight (s n i) (t n i) (alpha n : ℝ) k j ≤ 2 ^ p n * (1 / 2) :=
    mul_le_mul_of_nonneg_left hw1 hP.le
  have hpw0 : 0 ≤ 2 ^ p n * resampWeight (s n i) (t n i) (alpha n : ℝ) k j :=
    mul_nonneg hP.le hw0
  refine ⟨?_, by simp⟩
  have hb : |(tableA (s n i) (t n i) (alpha n) (p n) k j : ℝ)| < 2 ^ (w - 1) := by
    rw [abs_le] at he
    rw [abs_lt]
    constructor <;> nlinarith
  exact_mod_cast hb

/-- **`Ã` keeps the unit disk.** -/
theorem pre_lineA_ball (h : Big n) (i : Fin (d n)) (v : ZMod (s n i) → ℂ) (hv : ‖v‖ ≤ 1) :
    ‖lineA n i v‖ ≤ 1 := by
  have hα2 := two_le_alpha h.1
  have hαR : (2 : ℝ) ≤ alpha n := by exact_mod_cast hα2
  have hp := h.thirteen_le_p
  have hαp : alpha n ^ 2 ≤ p n := h.alpha_sq_le_p
  obtain ⟨hm, hm1, hmp⟩ := windowA_spec (alpha_sq_lt_p h)
  have htab := (tables_ok (s n i) (t n i) (alpha n) (p n) (h.good.lt i) hp hα2 hαp).1
  have hAx := IntegerMultBounds.Resampling.TabledMaps.approxMap_resampANumW (s := s n i)
    (t := t n i) (α := (alpha n : ℝ)) (by linarith) (by exact_mod_cast hαp) hm hm1 _
    (fun k j => IntegerMultBounds.Resampling.TabledMaps.tol_of_int (p n) _ _ (htab k j))
  have hA34 := opNorm_resampA_le_three_quarters (s := s n i) (t := t n i) hαR
  have hε : errA (windowA (p n) (alpha n)) < (p n : ℝ) ^ 2 := errA_lt_sq' hmp (by omega)
  have h4 : (4 : ℝ) * (p n : ℝ) ^ 2 ≤ 2 ^ p n := by exact_mod_cast four_sq_le_pow (p n) hp
  have h4' : 4 * ((4 * (2 * (windowA (p n) (alpha n) : ℝ) + 1) + 3) / 2) ≤ 2 ^ p n := by
    unfold errA at hε; linarith
  exact ball_of_approx hA34 hAx h4' v hv

lemma pre_mem_rsaBox {α : Type} : ∀ (d : ℕ) (t : Fin d → ℕ) (F : ((i : Fin d) → Fin (t i)) → α)
    {y : α}, y ∈ rsaBox d t F → ∃ a, F a = y
  | 0, _, F, y, hy => by
      simp only [rsaBox, List.mem_singleton] at hy
      exact ⟨_, hy.symm⟩
  | d + 1, t, F, y, hy => by
      simp only [rsaBox, List.mem_flatMap, List.mem_finRange, true_and] at hy
      obtain ⟨x₀, hx₀⟩ := hy
      obtain ⟨a, ha⟩ := pre_mem_rsaBox d _ _ hx₀
      exact ⟨_, ha⟩

/-- The line machine of axis `i` maps lines in the unit disk (at its input scale) into the
unit disk at scale `p + 1`. -/
theorem pre_lineA_out (h : Big n) (hs : Fin (d n) → Fin 5 → List Bool) (i : Fin (d n))
    (L : List GaussianInt) (hL : L.length = t n i)
    (hLn : ∀ y ∈ L, ‖rsbGrid (if (i : ℕ) + 1 = d n then p n else p n + 1) y‖ ≤ 1) :
    ∀ x ∈ (rsaPipeData n hs i).g (windowA (p n) (alpha n)) (t n i) L,
      ‖rsbGrid (p n + 1) x‖ ≤ 1 := by
  have rel := rsaLineRel_lineA n hs i (h.good.lt i).le (pre_windowA_le_s h i)
  set qi := if (i : ℕ) + 1 = d n then p n else p n + 1 with hqi
  set v : ZMod (s n i) → ℂ := fun j => GaussianInt.toComplex (L.getD j.val 0) / 2 ^ qi with hv
  have hvb : ‖v‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    rcases rsb_mem_getD (L := L) (k := j.val) with e | e
    · show ‖GaussianInt.toComplex (L.getD j.val 0) / 2 ^ qi‖ ≤ 1
      rw [e]; simp
    · exact hLn _ e
  have hball := pre_lineA_ball h i v hvb
  intro x hx
  have hlen := rel.len L
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have e := rel.num L v hL (fun j => rfl) k (by rw [← hlen]; exact hk)
  rw [rsbGrid, ← List.getD_eq_getElem _ 0 hk, ← e]
  exact norm_le_pi_norm _ _ |>.trans hball

/-- **Every intermediate box of the stage is in the unit disk** at scale `p + 1`, from an input
box in the unit disk at scale `p`. -/
theorem pre_flat_ball (h : Big n) (hs : Fin (d n) → Fin 5 → List Bool)
    (l : List GaussianInt) (hl : ∀ y ∈ l, ‖rsbGrid (p n) y‖ ≤ 1) :
    ∀ j k, k + j + 1 = d n → ∀ x ∈ rsaFlat (d n) (t n)
      (fun i => (rsaPipeData n hs i).g (windowA (p n) (alpha n)) (t n i)) k l,
      ‖rsbGrid (p n + 1) x‖ ≤ 1 := by
  intro j
  induction j with
  | zero =>
      intro k hk x hx
      rw [rsaFlat_lt _ _ _ (by omega), rsaFlat_ge _ _ _ (by omega)] at hx
      rcases rsb_mem_rsbAxisL (show x ∈ rsbAxisL _ _ _ _ l from hx) with e | ⟨L', hL', hy, hx'⟩
      · rw [e]; simp [rsbGrid]
      · refine pre_lineA_out h hs _ L' hL' (fun y hyL => ?_) x hx'
        rw [ite_eq_left (by simp; omega)]
        rcases hy y hyL with e | e
        · rw [e]; simp [rsbGrid]
        · exact hl y e
  | succ j ih =>
      intro k hk x hx
      rw [rsaFlat_lt _ _ _ (by omega)] at hx
      rcases rsb_mem_rsbAxisL (show x ∈ rsbAxisL _ _ _ _ _ from hx) with e | ⟨L', hL', hy, hx'⟩
      · rw [e]; simp [rsbGrid]
      · refine pre_lineA_out h hs _ L' hL' (fun y hyL => ?_) x hx'
        rw [ite_eq_right (by simp; omega)]
        rcases hy y hyL with e | e
        · rw [e]; simp [rsbGrid]
        · exact ih (k + 1) (by omega) y e

end PipeFacts

/-! ### The stage -/

section Stage

open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.NLogN
open IntegerMultBounds.Resampling.WeightTable (tableA)

/-- The record of step `k` (axis `d - 1 - k`) of the pipeline at length `n`, word size `W`. -/
def preDA (n W : ℕ) (hd0 : 0 < d n) (k : ℕ) : PreAxA where
  t := t n (rsaStepAx hd0 k)
  q := if ((rsaStepAx hd0 k : Fin (d n)) : ℕ) + 1 = d n then p n else p n + 1
  m := windowA (p n) (alpha n)
  s := s n (rsaStepAx hd0 k)
  L := Nat.log 2 (t n (rsaStepAx hd0 k))
  Ld := Nat.log 2 (t n (rsaStepAx hd0 0))
  P := rsaPre (t n) (rsaStepAx hd0 k)
  G := rsaMid (t n) (rsaStepAx hd0 k)
  α := alpha n
  p := p n
  W := W

/-- The parameter stream from step `j` on. -/
def preRecsA {A : ℕ} (n W : ℕ) (hd0 : 0 < d n) (j : ℕ) : List (Fin (A + 4)) :=
  ((List.range (d n)).drop j).flatMap fun k => preRec (preDA n W hd0 k).fields

lemma preRecsA_succ {A : ℕ} (n W : ℕ) (hd0 : 0 < d n) {j : ℕ} (hj : j < d n) :
    (preRecsA n W hd0 j : List (Fin (A + 4))) =
      preRec (preDA n W hd0 j).fields ++ preRecsA n W hd0 (j + 1) := by
  unfold preRecsA
  rw [List.drop_eq_getElem_cons (by simpa using hj), List.flatMap_cons, List.getElem_range]

/-- The canonical interchange headers of the pipeline at width `w`. -/
def preHsA (n w : ℕ) (hd0 : 0 < d n) : Fin (d n) → Fin 5 → List Bool := fun i k =>
  sxBits (BinaryInterchangeRun.values (rsaPre (t n) i) (rsaMid (t n) i) (3 * w)
    (Nat.log 2 (t n i)) (Nat.log 2 (t n (rsaStepAx hd0 0))) k)

/-- The register file configured for step `k`. -/
def preCfgA {A : ℕ} (V₀ : RsaV (RsaX t₀) A) (hd : Fin 5 → Fin t₀) (n w W : ℕ) (hd0 : 0 < d n)
    (rest : List (Fin (A + 4))) (k : ℕ) : RsaV (RsaX t₀) A :=
  preLoadA V₀ hd w (preDA n W hd0 k) (preRecsA n W hd0 (k + 1) ++ rest)

/-- The step bound of the loader at step `k`. -/
def preCpA {A : ℕ} (V₀ : RsaV (RsaX t₀) A) (hd : Fin 5 → Fin t₀) (n w W : ℕ) (hd0 : 0 < d n)
    (rest : List (Fin (A + 4))) : ℕ → ℕ
  | 0 => preCostA V₀ hd w (preDA n W hd0 0)
  | k + 1 => preCostA (preCfgA V₀ hd n w W hd0 rest k) hd w (preDA n W hd0 (k + 1))

variable {body : F → Pr F T Q (prime + K) U} {rg : RsaR (RsaX t₀) → Fin T} {ι : Fin 64 → Fin T}

set_option maxHeartbeats 4000000 in
/-- **The `Ã` stage with its loader.** At operand length `n` in the regime `Big n`, width
`w ≥ p n + 3` and table word size `W ≥ w` with `α² ((s_i + t_i)(m + 1))² 2^(13p+8) < 2^W` on
every axis: from a base register file `V₀` (`PreBaseA`) whose parameter register `c .out`
holds the records of the pipeline (`preRecsA`) followed by `rest`, with the box register
holding the padded stream of the numerators of `u` at scale `p n` (`‖u‖ ≤ 1`, zero padding),
`rsaAllP (preA rg ι hd)` ends with the box register holding the numerators of
`tensorZR (d n) (s n) (t n) (lineA n) u` at scale `p n + 1`, the register file configured for
axis `0` and `rest` on `c .out`. -/
theorem rsaStage_exec (n : ℕ) (hbig : Big n) (hd0 : 0 < d n) (hrg : Function.Injective rg)
    (hdisj : ∀ r j, rg r ≠ ι j) (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ prime + K) (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQs : swapStates hd pay hi ≤ Q) (hsw : Function.Injective fun j => rg (.x (.sw j)))
    (hTs : swapT t₀ ≤ T) (hdpay : ∀ k, hd k ≠ pay) {w W : ℕ} (hw : p n + 3 ≤ w) (hwW : w ≤ W)
    (hW : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (V₀ : RsaV (RsaX t₀) (prime + K)) (hV₀ : PreBaseA V₀ w hd) (rest : List (Fin (prime + K + 4)))
    (hout : V₀.cr .out = preRecsA n W hd0 0 ++ rest)
    (u : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) (hu : ∀ x, ‖u x‖ ≤ 1)
    (F₀ : ((i : Fin (d n)) → Fin (t n i)) → GaussianInt)
    (hF : ∀ x : (i : Fin (d n)) → Fin (t n i), (∀ i, (x i : ℕ) < s n i) →
      u (fun i => ((x i : ℕ) : ZMod (s n i))) = GaussianInt.toComplex (F₀ x) / 2 ^ p n)
    (hF0 : ∀ x : (i : Fin (d n)) → Fin (t n i), (∃ i, s n i ≤ x i) → F₀ x = 0)
    (axs : List (Fin (prime + K + 4))) (haxs : axs.length = d n - 1) :
    ∃ G : ((i : Fin (d n)) → Fin (t n i)) → GaussianInt,
      (∀ x : (i : Fin (d n)) → Fin (t n i),
        tensorZR (d n) (s n) (t n) (lineA n) u (fun i => ((x i : ℕ) : ZMod (t n i))) =
          GaussianInt.toComplex (G x) / 2 ^ (p n + 1)) ∧
      RsaRuns body rg ι (rsaAllP (preA rg ι hd) rg ι hι hT hQ hd pay hi hQs hsw hTs)
        (rsaWith V₀ (cstream (prime + K) w (rsaBox (d n) (t n) F₀)) axs []).get
        (rsaWith (preCfgA V₀ hd n w W hd0 rest (d n - 1))
          (cstream (prime + K) w (rsaBox (d n) (t n) G)) axs []).get
        (rsaAllCost (K := K) T t₀ w (windowA (p n) (alpha n)) (d n) (t n) hd0
          (rsaPipeData n (preHsA n w hd0)) hd (preCpA V₀ hd n w W hd0 rest) (∏ i, t n i)) := by
  have hp13 := hbig.thirteen_le_p
  have hα2 := two_le_alpha hbig.1
  have htpos : ∀ i, 0 < t n i := fun i => Nat.pos_of_ne_zero (NeZero.ne (t n i))
  set hs := preHsA n w hd0 with hhs
  set cfg := preCfgA V₀ hd n w W hd0 rest with hcfg
  -- the loader contracts
  have hprep₀ : ∀ l a a', RsaRuns body rg ι (preA rg ι hd) (rsaWith V₀ l a a').get
      (rsaWith (cfg 0) l a a').get (preCpA V₀ hd n w W hd0 rest 0) := fun l a a' =>
    preA_rsaWith hrg hι hdisj hi V₀ (preDA n W hd0 0) (preRecsA n W hd0 1 ++ rest) w hV₀.free
      (by simp [hout, preRecsA_succ n W hd0 hd0]) hV₀.wn hp13 hα2 (htpos _) hwW (hW _) l a a'
  have hprep : ∀ k, k + 1 < d n → ∀ l a a', RsaRuns body rg ι (preA rg ι hd)
      (rsaWith (cfg k) l a a').get (rsaWith (cfg (k + 1)) l a a').get
      (preCpA V₀ hd n w W hd0 rest (k + 1)) := by
    intro k hk l a a'
    have h := preA_rsaWith (body := body) hrg hι hdisj hi (cfg k) (preDA n W hd0 (k + 1))
      (preRecsA n W hd0 (k + 2) ++ rest) w (hV₀.free.load hd w _ _)
      (by simp [hcfg, preCfgA, preLoadA, preRecsA_succ n W hd0 hk])
      (by simp [hcfg, preCfgA, preLoadA, hV₀.wn]) hp13 hα2 (htpos _) hwW (hW _) l a a'
    rwa [hcfg, preCfgA, preLoadA_preLoadA] at h
  -- the input box and the intermediate boxes
  have hbox : ∀ y ∈ rsaBox (d n) (t n) F₀, ‖rsbGrid (p n) y‖ ≤ 1 := by
    intro y hy
    obtain ⟨a, rfl⟩ := pre_mem_rsaBox _ _ _ hy
    by_cases ha : ∀ i, (a i : ℕ) < s n i
    · rw [rsbGrid, ← hF a ha]; exact hu _
    · simp only [not_forall, not_lt] at ha
      rw [hF0 a ha]; simp [rsbGrid]
  have hfits : ∀ k ≤ d n, ∀ x ∈ rsaFlat (d n) (t n)
      (fun i => (rsaPipeData n hs i).g (windowA (p n) (alpha n)) (t n i)) k
        (rsaBox (d n) (t n) F₀), Fits w x := by
    intro k hk x hx
    rcases Nat.lt_or_ge k (d n) with hkd | hkd
    · exact rsb_fits_of_norm_le (by omega) x
        (pre_flat_ball hbig hs _ hbox (d n - 1 - k) k (by omega) x hx)
    · rw [rsaFlat_ge _ _ _ hkd] at hx
      exact rsb_fits_of_norm_le (by omega) x (hbox x hx)
  refine rsa_all_lineA n (preA rg ι hd) hrg hdisj hι hT hQ hA hd pay hi hQs hsw hTs hdpay hd0
    (by omega) hbig.good.lt (pre_windowA_le_s hbig)
    (fun i y hy => by
      simp only [rsaTabL, List.mem_flatMap, List.mem_range, List.mem_map] at hy
      obtain ⟨k, hk, j, -, rfl⟩ := hy
      exact pre_tableA_fits hbig i (by omega) _ _)
    hs (fun i hi1 => ?_) V₀ cfg (fun k hk => ?_) (preCpA V₀ hd n w W hd0 rest) hprep₀
    (fun k hk => hprep k hk) u F₀ hF hF0 hfits axs haxs
  · -- the interchange headers
    have hl := pre_log_last hbig hd0
    refine ⟨?_, ?_, fun k => ?_, fun k => canonical_sxBits _⟩
    · simp only [rsaPipeData, hl]; rcases pre_log_t (n := n) i with e | e <;> omega
    · simp only [rsaPipeData, hl]
      rcases pre_log_t (n := n) i with e | e <;> rw [e] <;> have := hbig.two_le_ℓ <;> omega
    · simp only [rsaPipeData, hhs, preHsA, value_sxBits]
  · -- the configured register files
    refine ⟨preLoadA_idle hV₀ _ _, by simp [hcfg, preCfgA, preLoadA, hV₀.ob], fun _ => ⟨fun j => ?_,
      by simp [hcfg, preCfgA, preLoadA, preBankA, hV₀.xt],
      by simp [hcfg, preCfgA, preLoadA, preBankA, hV₀.e1],
      by simp [hcfg, preCfgA, preLoadA, preBankA, hV₀.e2]⟩⟩
    rw [hcfg, preCfgA, preLoadA_bank hV₀]
    rfl

end Stage

end

end IntegerMultBounds.MathlibTM2.Fast
