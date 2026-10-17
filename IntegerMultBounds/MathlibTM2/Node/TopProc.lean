module

public import IntegerMultBounds.MathlibTM2.Node.TopWord
public import IntegerMultBounds.MathlibTM2.Node.TopRec
public import IntegerMultBounds.MathlibTM2.Node.TopEnc
public import IntegerMultBounds.MathlibTM2.Node.LayerProc
import Mathlib.Tactic.Positivity.Finset

/-!
# The host machine of the simultaneous layer

`topProg` computes `topZ` (`Layer/TopZ.lean`) on the array stored on `io`. It is one fixed program
on the register file of the layer machine (`nT SXReg` registers, procedure table
`layerTable hQ ds`): every size and configuration value is read from registers at run time, word
lengths and shift amounts are lengths of counter registers, and the pieces are a record consumed
by a loop.

**Register interface** (`topProg_exec`).
* `io`: `encZ A w Z` in, `encZ A w (topZ …)` out (`A = prime + Ka`).
* `TopRegs S.R (n + a) r w' K ρ`: every register at rest for `n + a` address bits, `r`
  coefficients and words of `w'` symbols; `lev`, `u`, `a₀`, `L`, `rows` empty; `n`, `w`, `rw`,
  `K`, `ρ` holding `n + a`, `w'`, `r w'`, `K`, `ρ` symbols.
* `park`: the configuration record `topRec (topCfg w s a R R₂ q aT K oS D)` on top of any
  contents. A record is a list of unary fields, each `x` ticks followed by the separator
  `topSep = bitSymbol false` (`Node/TopRec.lean`). Fields: `0` the input and output width `w`,
  `1` the shift `s`, `2` the number `a` of top address bits, `3` the rows `R`, `4` the padded
  rows `R₂`, `5` the number `q` of top kernels, `6` their offset `aT`, `7` the slot width `K q`,
  `8` and `9` the selected bits `ρ + oS + K i`, `i < D`.
* `ph .arr`: exactly the piece record `topRec (topPcRec K pcs)`: per piece (`TopPc`) the four
  fields `j`, `u`, `a₀`, `K · bits u j` (level, leaf bits, offset, slot width); the piece computes
  the layer at level `j` on the active bits `a₀ + ρ + K i` (`TopPc.piece`, `topPieces`) on `R₂`
  rows, `R₂ = rowsAt R₀ j` (`TopPc.Ok`).
* `lf (.k .arr)`, `st`, `cs`: empty; they hold the consumed piece fields, the top `a` symbols of
  `n` and the old `rowctr` while the pieces run.
* Every register other than `io` ends as it started.

**Stages** (`topProg`).
1. `topWidenS`: words of `w` symbols to words of `w'` symbols (sign extension,
   `Node/TopWord.lean`).
2. `topPhaseS`: `sZ sel`: the strided mask of the selected bits (`strideMask`) on `ph .msk`, the
   record count `R 2^(n+a)` on `ph .cnt` (`upow2`), `phaseProg` with `c = 1` (`topMaskOf_eq`,
   `topPhase_sZ`).
3. `topKerS`: `k2s top`: one call of the layer procedure at level `0` with `q` leaf bits at offset
   `aT` (skipped when `q = 0`).
4. `topBlockS`: the top `a` address bits become rows (no symbol changes, `topEnc_toRows`);
   `topDownS` turns the rest state into the one for `n` address bits; `topPadS` pads to `R₂` rows
   (`topEnc_padRows`); `topPcLoop` runs the pieces (`topPcBody`: four fields onto `lev`, `u`, `a₀`,
   `L`, `rows := R₂`, `topCallClr`); `topUnpadS` keeps the first `R 2^a` rows
   (`topEnc_unpadRows`), which become address bits again (`topEnc_ofRows`); `topUpS` restores
   the rest state.
5. `topPhaseS` again.
6. `topUnitS`: `D mod 8` into a scan slot (`topResid`) and the multiplication by `unitD D`
   (`topUnit`, chosen by `topDisp8`; `topUnitD_mod`).
7. `topShiftS`: the truncating shift by `s` back to words of `w` symbols (`Node/TopWord.lean`).

**Main theorems.** `topProg_exec`: under `TopRegs`, the storage registers above, empty left
stacks, `Z` fitting `w` signed bits, the array before the shift (`topPre`) fitting `w'` signed
bits, `s + w ≤ w'`, the selected bits `topSel a low top` distinct and equal to the bits
`ρ + oS + K i`, `i < D`, the machine leaves `encZ A w (topZ ds a low top hR₂ Ps s Z)` on `io`
(`top = topTop aT ρ K q (n + a) hfitT`, `Ps = topPieces hρ pcs hpcs`) within `topCost` steps.
`topProg_exec_Hl` adds `topZ_correct`: the truncation toward zero of `Hl sel` applied to `Z`.

**Cost.** `topCost` is the sum of the stage bounds `topWidenSCost`, `topPhaseSCost` (twice),
`topKerSCost` (with `layerCost … q K ρ R (n + a) r w' 0 aT`), `topBlockCost` (the rest-state
changes, padding and unpadding linear in `R₂ 2^n r w'`, and `topPcsCost`, one `topPcCost` with
`layerCost … u K ρ R₀ n r w' j a₀` per piece), `topUnitSCost` and `topShiftSCost`; each record
read costs at most `topGetCost`, linear in the length of the record.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.LayerMachine

open IntegerMultBounds IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


/-- Evaluate register updates at register names. -/
local macro "topfupd" : tactic => `(tactic| (simp only [Function.update_apply, reg_inj,
  reduceCtorEq, ↓reduceIte, eq_self_iff_true, LReg.sc.injEq, LReg.ph.injEq, LReg.lf.injEq,
  IntegerMultBounds.MathlibTM2.Node.LReg.k.injEq, Fin.reduceEq, Fin.isValue]))

/-! ### Registers -/

section Regs

variable {A : ℕ}

/-- The registers of the host machine between its stages: every register at rest for `N`
address bits, `r` coefficients and words of `w` symbols; the per-call parameters `lev`, `u`,
`a₀`, `L`, `rows` empty; `n`, `w`, `rw`, `K`, `ρ` holding `N`, `w`, `r w`, `K`, `ρ` symbols. -/
structure TopRegs (Rg : Fin (nT SXReg) → List (Fin (A + 4))) (N r w K ρ : ℕ) : Prop where
  rest : Rest bcEmpty N r w Rg
  hlev : Rg (reg .lev) = []
  hu : Rg (reg .u) = []
  ha₀ : Rg (reg .a₀) = []
  hL : Rg (reg .L) = []
  hrows : Rg (reg .rows) = []
  hn : (Rg (reg .n)).length = N
  hw : (Rg (reg .w)).length = w
  hrw : (Rg (reg .rw)).length = r * w
  hK : (Rg (reg .K)).length = K
  hρ : (Rg (reg .ρ)).length = ρ

/-- `TopRegs` does not read `io`. -/
lemma TopRegs.update_io {Rg : Fin (nT SXReg) → List (Fin (A + 4))} {N r w K ρ : ℕ}
    (h : TopRegs Rg N r w K ρ) (l : List (Fin (A + 4))) :
    TopRegs (Function.update Rg (reg .io) l) N r w K ρ where
  rest := h.rest.update_io l
  hlev := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hlev
  hu := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hu
  ha₀ := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.ha₀
  hL := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hL
  hrows := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hrows
  hn := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hn
  hw := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hw
  hrw := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hrw
  hK := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hK
  hρ := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.hρ

/-- Outside `ph .af`, `lf (.k .cf)` and `rowctr`, the rest state does not depend on the number
of address bits. -/
lemma topRestSpec_bits {bc : SXReg → List (Fin (A + 4)) → Prop} {N N' r w : ℕ}
    {x : LReg SXReg} {l : List (Fin (A + 4))} (h1 : x ≠ .ph .af) (h2 : x ≠ .lf (.k .cf))
    (h3 : x ≠ .rowctr) : restSpec bc N r w x l ↔ restSpec bc N' r w x l := by
  cases x with
  | ph y => cases y <;> simp_all [restSpec, phRest]
  | lf y =>
    cases y with
    | k z => cases z <;> simp_all [restSpec, lfRest]
    | _ => simp_all [restSpec, lfRest]
  | _ => simp_all [restSpec]

/-- The parameter registers are unconstrained at rest. -/
lemma topRestSpec_par {bc : SXReg → List (Fin (A + 4)) → Prop} {N r w : ℕ} {x : LReg SXReg}
    (hx : x ∈ parRegs (BReg := SXReg)) (l : List (Fin (A + 4))) : restSpec bc N r w x l := by
  simp only [parRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

end Regs

/-! ### Pieces -/

/-- A piece of the machine: level `j`, leaf bits `u`, base rows `R₀` and offset `a₀`; its active
bits are `a₀ + ρ + K i`, `i < bits u j`. -/
structure TopPc where
  j : ℕ
  u : ℕ
  R₀ : ℕ
  a₀ : ℕ

/-- The conditions of a piece on `R₂` rows of `n` address bits with words of `w` symbols. -/
structure TopPc.Ok (ds : ComplexFramedExecution.Directions) (K n w R₂ : ℕ) (pc : TopPc) :
    Prop where
  hu : 1 ≤ pc.u
  hR₀ : 1 ≤ pc.R₀
  hR : R₂ = rowsAt pc.R₀ pc.j
  hTw : ∀ i < pc.j, expZ pc.u ds i ≤ w
  hfit : pc.a₀ + K * bits pc.u pc.j ≤ n

lemma topFit {ρ K a₀ k n : ℕ} (hρ : ρ < K) (h : a₀ + K * k ≤ n) : ∀ i < k, a₀ + ρ + K * i < n :=
  fun i hi => by
    have : K * (i + 1) ≤ K * k := Nat.mul_le_mul_left _ hi
    rw [Nat.mul_succ] at this
    omega

/-- The piece of `TopZ` computed by a machine piece. -/
noncomputable def TopPc.piece {ds : ComplexFramedExecution.Directions} {ρ K n w R₂ : ℕ}
    (hρ : ρ < K) (pc : TopPc) (h : pc.Ok ds K n w R₂) : Piece n R₂ :=
  ⟨pc.u, pc.j, pc.R₀, h.hR, actMap pc.a₀ ρ K (bits pc.u pc.j) n (topFit hρ h.hfit)⟩

/-- The pieces of a list of machine pieces. -/
noncomputable def topPieces {ds : ComplexFramedExecution.Directions} {ρ K n w R₂ : ℕ}
    (hρ : ρ < K) : (pcs : List TopPc) → (∀ pc ∈ pcs, pc.Ok ds K n w R₂) → List (Piece n R₂)
  | [], _ => []
  | pc :: pcs, h => pc.piece hρ (h pc List.mem_cons_self) ::
      topPieces hρ pcs (fun q hq => h q (List.mem_cons_of_mem _ hq))


/-! ### Storage registers and the configuration -/

section Storage

variable {A : ℕ}

/-- The configuration record on `park`: the input width `w`, the shift `s`, the number `a` of
top address bits, the rows `R` and `R₂`, the top kernels (`q` bits at `aT + ρ + K i`, `L = K q`),
and the selected bits `oS + ρ + K i`, `i < D`. -/
def topCfg (w s a R R₂ q aT K oS D : ℕ) : List ℕ := [w, s, a, R, R₂, q, aT, K * q, oS, D]

/-- The fields of one piece: level, leaf bits, offset and slot width. -/
def topPcFields (K : ℕ) (pc : TopPc) : List ℕ := [pc.j, pc.u, pc.a₀, K * bits pc.u pc.j]

/-- The piece record on `ph .arr`. -/
def topPcRec (K : ℕ) (pcs : List TopPc) : List ℕ := pcs.flatMap (topPcFields K)

/-- The storage registers: `park` holds the configuration record on top of anything, `ph .arr`
holds the piece record, `lf (.k .arr)`, `st` and `cs` are empty. -/
structure TopIn (Rg : Fin (nT SXReg) → List (Fin (A + 4))) (cfg pfs : List ℕ) : Prop where
  cf : ∃ rest, Rg (reg .park) = topRec cfg ++ rest
  pl : Rg (reg (.ph .arr)) = topRec pfs
  pb : Rg (reg (.lf (.k .arr))) = []
  x : Rg (reg .st) = []
  y : Rg (reg .cs) = []

lemma TopIn.update_io {Rg : Fin (nT SXReg) → List (Fin (A + 4))} {cfg pfs : List ℕ}
    (h : TopIn Rg cfg pfs) (l : List (Fin (A + 4))) :
    TopIn (Function.update Rg (reg .io) l) cfg pfs where
  cf := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.cf
  pl := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.pl
  pb := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.pb
  x := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.x
  y := by rw [Function.update_of_ne (reg_ne (by simp))]; exact h.y

end Storage


/-! ### One call of the layer procedure -/

section Call

variable {Q Ka : ℕ} {U : Type}

/-- Call the layer procedure and clear `lev`, `u`, `a₀`, `L`, `rows`. -/
noncomputable def topCallClr : Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq (.call .layer)
  (.seq (uclear (reg .lev)) (.seq (uclear (reg .u)) (.seq (uclear (reg .a₀))
  (.seq (uclear (reg .L)) (uclear (reg .rows))))))

/-- **One call.** From the parameters of level `j` (`ParState`), every register at rest for `N`
address bits and `io` holding the stream of `Z`, the layer replaces `Z` on `io` and the five
per-call parameters are emptied; every other register ends as it started. -/
theorem topCallClr_exec (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime + Ka)
    (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
    {N r w K ρ R₀ j u a₀ : ℕ} (hr : 1 ≤ r) (hw : 1 ≤ w) (hρ : ρ < K) (hu : 1 ≤ u)
    (hR₀ : 1 ≤ R₀) (hTw : ∀ i < j, expZ u ds i ≤ w) (hfit : ∀ i < bits u j, a₀ + ρ + K * i < N)
    (hfitL : a₀ + K * bits u j ≤ N) (Z : ZArr (Fin (rowsAt R₀ j) × Fin r) N)
    (v : HS (nT SXReg) Q (prime + Ka) U) (S : Stacks (nT SXReg) (prime + Ka))
    (hL : ∀ y, S.L y = []) (hpar : ParState S.R j u K ρ a₀ (K * bits u j) (rowsAt R₀ j) N w (r * w))
    (hrest : Rest bcEmpty N r w S.R) (hio : S.R (reg .io) = encZ (prime + Ka) w Z) :
    ∃ (v' : HS (nT SXReg) Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      c ≤ layerCost (nT SXReg) ds u K ρ R₀ N r w j a₀ +
        (2 * j + 2 * u + 2 * a₀ + 2 * (K * bits u j) + 2 * rowsAt R₀ j + 10) ∧
      Exec (layerTable hQ ds) topCallClr (mk v S) c
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update (Function.update
            (Function.update S.R (reg .io)
              (encZ (prime + Ka) w (layerZ u ds R₀ j (actMap a₀ ρ K (bits u j) N hfit) Z)))
            (reg .lev) []) (reg .u) []) (reg .a₀) []) (reg .L) []) (reg .rows) [] }) := by
  set body := layerTable (Ka := Ka) (U := U) hQ ds
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := layer_exec hQ ds hA hA9 hNW hgate hr hw hρ hu hR₀ j hTw a₀
    hfit hfitL Z v S hL hpar hrest hio
  set X := encZ (prime + Ka) w (layerZ u ds R₀ j (actMap a₀ ρ K (bits u j) N hfit) Z)
  set R₁ := Function.update S.R (reg .io) X with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := uclear_exec body (reg .lev) v₁ { S with R := R₁ }
  obtain ⟨v₃, hu₃, e₃⟩ := uclear_exec body (reg .u) v₂
    { S with R := Function.update R₁ (reg .lev) [] }
  obtain ⟨v₄, hu₄, e₄⟩ := uclear_exec body (reg .a₀) v₃
    { S with R := Function.update (Function.update R₁ (reg .lev) []) (reg .u) [] }
  obtain ⟨v₅, hu₅, e₅⟩ := uclear_exec body (reg .L) v₄
    { S with
      R := Function.update (Function.update (Function.update R₁ (reg .lev) []) (reg .u) [])
        (reg .a₀) [] }
  obtain ⟨v₆, hu₆, e₆⟩ := uclear_exec body (reg .rows) v₅
    { S with
      R := Function.update (Function.update (Function.update (Function.update R₁
        (reg .lev) []) (reg .u) []) (reg .a₀) []) (reg .L) [] }
  refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆))))⟩
  have h1 := hpar .lev
  have h2 := hpar .u
  have h3 := hpar .a₀
  have h4 := hpar .L
  have h5 := hpar .rows
  simp only [parSpec] at h1 h2 h3 h4 h5
  dsimp only
  simp only [hR₁]
  topfupd
  rw [h1, h2, h3, h4, h5]
  omega

end Call

/-! ### Stages -/

lemma topIo {T A : ℕ} (S : Stacks T A) (i : Fin T) (X Y : List (Fin (A + 4))) :
    ({ ({ S with R := Function.update S.R i X } : Stacks T A) with
      R := Function.update (Function.update S.R i X) i Y } : Stacks T A) =
      { S with R := Function.update S.R i Y } := by
  simp [Function.update_idem]



section Stages

variable {Q A : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q A U)

/-- Read field `i` of the configuration record onto `dst`. -/
noncomputable def topRd (dst : Fin (nT SXReg)) (i : ℕ) : Pr P (nT SXReg) Q A U :=
  topGet (reg .park) (reg .lenctr) dst i

/-- `topRd`: `dst` gains `cfg[i]` ticks; every other register ends as it started. -/
theorem topRd_exec {x : LReg SXReg} (hx1 : x ≠ .park) (hx2 : x ≠ .lenctr) {cfg : List ℕ}
    (i : ℕ) (hi : i < cfg.length) (v : HS (nT SXReg) Q A U)
    (S : Stacks (nT SXReg) A) (hlc : S.R (reg .lenctr) = [])
    (hcf : ∃ rest, S.R (reg .park) = topRec cfg ++ rest) :
    ∃ (v' : HS (nT SXReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ topGetCost cfg ∧
      Exec body (topRd (reg x) i) (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg x) (List.replicate cfg[i] tick ++ S.R (reg x)) }) := by
  obtain ⟨rest, hcf⟩ := hcf
  exact topGet_exec body (nodup_map_reg (l := [.park, .lenctr, x])
    (by simp [Ne.symm hx1, Ne.symm hx2])) cfg i hi rest v S hcf hlc

/-- Widening from the input width `w` (field `0`) to the working width `w'` (register `w`). -/
noncomputable def topWidenS : Pr P (nT SXReg) Q A U :=
  .seq (topRd (reg (.sc 0)) 0)
  (.seq (ucopy (reg .w) (reg (.sc 1)) (reg .tS))
  (.seq (usub (reg (.sc 0)) (reg (.sc 1)) (reg .tS))
  (.seq (topPass (reg .io) (reg .racc)
      (topWidenWord (reg .io) (reg .racc) (reg (.sc 0)) (reg (.sc 1)) (reg (.sc 3))))
  (.seq (uclear (reg (.sc 0))) (uclear (reg (.sc 1)))))))

/-- The step bound of `topWidenS`. -/
def topWidenSCost (cfg : List ℕ) (R N r w w' : ℕ) : ℕ :=
  topGetCost cfg + (4 * w' + 4) + (4 * w + 4) + topWidenCost R N r w w' + (2 * w + 2) +
    (2 * (w' - w) + 2)

theorem topWidenS_exec {cfg pfs : List ℕ} {R N r w w' K ρ : ℕ} (hcfg : cfg[0]? = some w)
    (hw : 1 ≤ w) (hww : w ≤ w') (Z : ZArr (Fin R × Fin r) N) (hZ : ∀ p, TopFitsZ w (Z p))
    (v : HS (nT SXReg) Q A U) (S : Stacks (nT SXReg) A) (hT : TopRegs S.R N r w' K ρ)
    (hI : TopIn S.R cfg pfs) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT SXReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ topWidenSCost cfg R N r w w' ∧
      Exec body topWidenS (mk v S) c
        (mk v' { S with R := Function.update S.R (reg .io) (encZ A w' Z) }) := by
  have hi : 0 < cfg.length := by
    rcases cfg with _ | ⟨x, l⟩
    · simp at hcfg
    · simp
  have hc0 : cfg[0] = w := by
    rw [List.getElem?_eq_getElem hi] at hcfg; exact Option.some.inj hcfg
  have hs0 : S.R (reg (.sc 0)) = [] := hT.rest (.sc 0)
  have hs1 : S.R (reg (.sc 1)) = [] := hT.rest (.sc 1)
  have hs3 : S.R (reg (.sc 3)) = [] := hT.rest (.sc 3)
  have htS : S.R (reg .tS) = [] := hT.rest .tS
  have hracc : S.R (reg .racc) = [] := hT.rest .racc
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := topRd_exec body (x := .sc 0) (by simp) (by simp) 0 hi v S
    (hT.rest .lenctr) hI.cf
  rw [hc0, hs0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate w tick) with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := ucopy_exec body (a := reg .w) (b := reg (.sc 1)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₁ { S with R := R₁ }
    (by simp [hR₁, htS])
  have hw₁ : (R₁ (reg .w)).length = w' := by simp [hR₁]; exact hT.hw
  have hs1' : R₁ (reg (.sc 1)) = [] := by simp [hR₁, hs1]
  dsimp only at e₂
  rw [hw₁, hs1', List.append_nil] at e₂
  set R₂ := Function.update R₁ (reg (.sc 1)) (List.replicate w' tick) with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := usub_exec body (a := reg (.sc 0)) (b := reg (.sc 1)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ }
    (by simp [hR₂, hR₁, htS])
  dsimp only at e₃
  have h0₂ : R₂ (reg (.sc 0)) = List.replicate w tick := by simp [hR₂, hR₁]
  rw [h0₂, show R₂ (reg (.sc 1)) = List.replicate w' tick by simp [hR₂], List.length_replicate,
    List.drop_replicate] at e₃
  set R₃ := Function.update R₂ (reg (.sc 1)) (List.replicate (w' - w) tick) with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := topWidenP_exec body (src := reg .io) (dst := reg .racc)
    (c₁ := reg (.sc 0)) (c₂ := reg (.sc 1)) (sp := reg (.sc 3))
    (nodup_map_reg (l := [.io, .racc, .sc 0, .sc 1, .sc 3]) (by simp)) hw hww Z hZ v₃
    { S with R := R₃ } (by simp [hR₃, hR₂, hR₁, hio]) (by simp [hR₃, hR₂, hR₁, hracc])
    ⟨by simp [hR₃, hR₂, hR₁], by simp [hR₃], by simp [hR₃, hR₂, hR₁, hs3]⟩
  set R₄ := Function.update R₃ (reg .io) (encZ A w' Z) with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := uclear_exec body (reg (.sc 0)) v₄ { S with R := R₄ }
  obtain ⟨v₆, hu₆, e₆⟩ := uclear_exec body (reg (.sc 1)) v₅
    { S with R := Function.update R₄ (reg (.sc 0)) [] }
  refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆))))) rfl ?_⟩
  · simp only [hR₄, hR₃, hR₂, hR₁]
    topfupd
    simp only [List.length_replicate]
    unfold topWidenSCost
    omega
  · congr 2
    funext k
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hs1]
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hs0]
    simp [hR₄, hR₃, hR₂, hR₁, Function.update_apply, h0, h1]

/-- The phase stage: the strided mask of the selected bits `oS + ρ + K i`, `i < D` (fields `8`,
`9`) on `ph .msk`, the record count `R 2^N` (field `3`) on `ph .cnt`, `phaseProg` with `c = 1`
on `io`, and the scratch registers cleared. -/
noncomputable def topPhaseS : Pr P (nT SXReg) Q A U :=
  .seq (topRd (reg (.sc 0)) 8)
  (.seq (uadd (reg .ρ) (reg (.sc 0)) (reg .tS))
  (.seq (topRd (reg (.sc 1)) 9)
  (.seq (strideMask (reg .n) (reg (.sc 0)) (reg .K) (reg (.sc 1)) (reg (.ph .msk)) (reg (.sc 2))
      (reg (.sc 3)) (reg (.sc 4)) (reg (.sc 5)) 1 (fun _ => true))
  (.seq (topRd (reg (.ph .cnt)) 3)
  (.seq (upow2 (reg .n) (reg (.ph .cnt)) (reg (.sc 4)) (reg (.sc 5)))
  (.seq (phaseProg (phMap (reg .io)) (reg .st) 1)
  (.seq (uclear (reg (.ph .msk))) (.seq (uclear (reg (.ph .cnt)))
  (.seq (uclear (reg (.sc 0))) (uclear (reg (.sc 1))))))))))))

/-- The step bound of `topPhaseS`. -/
def topPhaseSCost (cfg : List ℕ) (N R r w K ρ oS D : ℕ) : ℕ :=
  3 * topGetCost cfg + (4 * ρ + 4) + (10 * N + 4 * (ρ + oS) + (D * (4 * K + 9) + 4) + 15) +
    (4 * (2 ^ N * R) + 9 * N + 4) + (R * 2 ^ N * (25 * r * w + 20 * N + 36) + 33) +
    (2 * N + 2) + (2 * (2 ^ N * R) + 2) + (2 * (ρ + oS) + 2) + (2 * D + 2)

/-- The mask of the phase stage. -/
def topMaskOf (N ρ K oS D : ℕ) : Fin N → ZMod 2 :=
  addrBits N (maskVal (ρ + oS) K D 1 (fun _ => true))

theorem topPhaseS_exec (hA : 5 ≤ A) {cfg pfs : List ℕ} {R N r w K ρ oS D : ℕ}
    (h3 : cfg[3]? = some R) (h8 : cfg[8]? = some oS) (h9 : cfg[9]? = some D)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hK : 1 ≤ K) (Z : ZArr (Fin R × Fin r) N)
    (v : HS (nT SXReg) Q A U) (S : Stacks (nT SXReg) A) (hT : TopRegs S.R N r w K ρ)
    (hI : TopIn S.R cfg pfs) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT SXReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ topPhaseSCost cfg N R r w K ρ oS D ∧
      Exec body topPhaseS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io)
            (encZ A w (phaseZ (topMaskOf N ρ K oS D) 1 Z)) }) := by
  have hl3 : 3 < cfg.length := (List.getElem?_eq_some_iff.1 h3).1
  have hl8 : 8 < cfg.length := (List.getElem?_eq_some_iff.1 h8).1
  have hl9 : 9 < cfg.length := (List.getElem?_eq_some_iff.1 h9).1
  have hc3 : cfg[3] = R := (List.getElem?_eq_some_iff.1 h3).2
  have hc8 : cfg[8] = oS := (List.getElem?_eq_some_iff.1 h8).2
  have hc9 : cfg[9] = D := (List.getElem?_eq_some_iff.1 h9).2
  have hrest := hT.rest
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hrest (.sc i)
  have htS : S.R (reg .tS) = [] := hrest .tS
  have hlc : S.R (reg .lenctr) = [] := hrest .lenctr
  have hmsk : S.R (reg (.ph .msk)) = [] := hrest (.ph .msk)
  have hcnt : S.R (reg (.ph .cnt)) = [] := hrest (.ph .cnt)
  have hph : ∀ x, x ≠ PhaseReg.arr → phMap (reg (BReg := SXReg) .io) x = reg (.ph x) :=
    fun x hx => phMap_of_ne _ hx
  -- `sc 0 := ρ + oS`
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := topRd_exec body (x := .sc 0) (by simp) (by simp) 8 hl8 v S
    hlc hI.cf
  rw [hc8, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate oS tick) with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := uadd_exec body (a := reg .ρ) (b := reg (.sc 0)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₁ { S with R := R₁ }
    (by simp [hR₁, htS])
  dsimp only at e₂
  rw [show (R₁ (reg .ρ)).length = ρ by simp [hR₁]; exact hT.hρ,
    show R₁ (reg (.sc 0)) = List.replicate oS tick by simp [hR₁],
    List.replicate_append_replicate] at e₂
  set R₂ := Function.update R₁ (reg (.sc 0)) (List.replicate (ρ + oS) tick) with hR₂
  -- `sc 1 := D`
  obtain ⟨v₃, c₃, hu₃, hc₃, e₃⟩ := topRd_exec body (x := .sc 1) (by simp) (by simp) 9 hl9 v₂
    { S with R := R₂ } (by simp [hR₂, hR₁, hlc]) (by simpa [hR₂, hR₁] using hI.cf)
  dsimp only at e₃
  rw [hc9, show R₂ (reg (.sc 1)) = [] by simp [hR₂, hR₁, hsc], List.append_nil] at e₃
  set R₃ := Function.update R₂ (reg (.sc 1)) (List.replicate D tick) with hR₃
  -- the mask
  obtain ⟨v₄, m₄, hu₄, hm₄, e₄⟩ := strideMask_exec body (nR := reg .n) (oR := reg (.sc 0))
    (KR := reg .K) (kR := reg (.sc 1)) (z := reg (.ph .msk)) (cnt := reg (.sc 2))
    (w := reg (.sc 3)) (t₁ := reg (.sc 4)) (t₂ := reg (.sc 5))
    (nodup_map_reg (l := [.n, .sc 0, .K, .sc 1, .ph .msk, .sc 2, .sc 3, .sc 4, .sc 5])
      (by simp)) 1 (fun _ => true) (n := N) (o := ρ + oS) (K := K) (k := D) v₃
    { S with R := R₃ } (by simp [hR₃, hR₂, hR₁]; exact hT.hn) (by simp [hR₃, hR₂])
    (by simp [hR₃, hR₂, hR₁]; exact hT.hK) (by simp [hR₃]) hK
    (by simp [hR₃, hR₂, hR₁, hsc]) (by simp [hR₃, hR₂, hR₁, hsc]) (by simp [hR₃, hR₂, hR₁, hsc])
    (by simp [hR₃, hR₂, hR₁, hsc])
  dsimp only at e₄
  rw [show R₃ (reg (.ph .msk)) = [] by simp [hR₃, hR₂, hR₁, hmsk], List.append_nil] at e₄
  set mnum := maskVal (ρ + oS) K D 1 (fun _ => true) with hmnum
  set R₄ := Function.update R₃ (reg (.ph .msk)) (binSyms N mnum) with hR₄
  -- the record count
  obtain ⟨v₅, c₅, hu₅, hc₅, e₅⟩ := topRd_exec body (x := .ph .cnt) (by simp) (by simp) 3 hl3 v₄
    { S with R := R₄ } (by simp [hR₄, hR₃, hR₂, hR₁, hlc])
    (by simpa [hR₄, hR₃, hR₂, hR₁] using hI.cf)
  dsimp only at e₅
  rw [hc3, show R₄ (reg (.ph .cnt)) = [] by simp [hR₄, hR₃, hR₂, hR₁, hcnt], List.append_nil] at e₅
  set R₅ := Function.update R₄ (reg (.ph .cnt)) (List.replicate R tick) with hR₅
  obtain ⟨v₆, m₆, hu₆, hm₆, e₆⟩ := upow2_exec body (a := reg .n) (b := reg (.ph .cnt))
    (t₁ := reg (.sc 4)) (t₂ := reg (.sc 5))
    (nodup_map_reg (l := [.n, .ph .cnt, .sc 4, .sc 5]) (by simp)) v₅ { S with R := R₅ }
    (by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc]) (by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc])
  dsimp only at e₆ hm₆
  have hn₅ : (R₅ (reg .n)).length = N := by simp [hR₅, hR₄, hR₃, hR₂, hR₁]; exact hT.hn
  have hc₅' : R₅ (reg (.ph .cnt)) = List.replicate R tick := by simp [hR₅]
  rw [hn₅, hc₅'] at e₆ hm₆
  set kk := (List.replicate R tick).flatMap (List.replicate (2 ^ N)) with hkk
  have hkkl : kk.length = R * 2 ^ N := by
    rw [hkk, length_flatMap_replicate, List.length_replicate, Nat.mul_comm]
  set R₆ := Function.update R₅ (reg (.ph .cnt)) kk with hR₆
  -- the phase
  have hR₆o : ∀ x : LReg SXReg, x ≠ .sc 0 → x ≠ .sc 1 → x ≠ .ph .msk → x ≠ .ph .cnt →
      R₆ (reg x) = S.R (reg x) := by
    intro x h1 h2 h3 h4
    simp [hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, h1, h2, h3, h4]
  have hP : ∀ x, x ≠ PhaseReg.arr → x ≠ .msk → x ≠ .cnt →
      R₆ (phMap (reg .io) x) = S.R (reg (.ph x)) :=
    fun x h1 h2 h3 => by
      rw [hph x h1, hR₆o _ (by simp) (by simp) (by simpa using h2) (by simpa using h3)]
  obtain ⟨v₇, m₇, hu₇, hm₇, e₇⟩ := phaseProg_exec body
    (ρ := phMap (reg (BReg := SXReg) .io)) (st := reg .st)
    (phMap_injective (fun x => reg_ne (by simp)))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        (rw [hph _ (by decide)]; exact reg_ne (by simp)))
    hA hr hw 1 (topMaskOf N ρ K oS D) mnum rfl Z
    (cs := R₆ (reg (.ph .rc))) (ws := R₆ (reg (.ph .wc))) (kk := R₆ (reg (.ph .cnt)))
    (by rw [hR₆o _ (by simp) (by simp) (by simp) (by simp)]; exact hrest (.ph .rc))
    (by rw [hR₆o _ (by simp) (by simp) (by simp) (by simp)]; exact hrest (.ph .wc))
    (by simp [hR₆, hkkl]) v₆ { S with R := R₆ }
    (by dsimp only; rw [phMap_arr, hR₆o _ (by simp) (by simp) (by simp) (by simp)]; exact hio)
    (fun q => by
      dsimp only; rw [hP _ (by simp) (by simp) (by simp)]; exact hrest (.ph (.cls q)))
    (by dsimp only; rw [hph _ (by decide)])
    (by dsimp only; rw [hph _ (by decide)])
    (by dsimp only; rw [hP _ (by decide) (by decide) (by decide)]; exact hrest (.ph .tmp))
    (by dsimp only; rw [hP _ (by decide) (by decide) (by decide)]; exact hrest (.ph .aux))
    (by dsimp only; rw [hP _ (by decide) (by decide) (by decide)]; exact hrest (.ph .aux2))
    (by dsimp only; rw [hP _ (by decide) (by decide) (by decide)]; exact hrest (.ph .af))
    (by dsimp only; rw [hph _ (by decide)]; simp [hR₆, hR₅, hR₄])
    (by dsimp only; rw [hP _ (by decide) (by decide) (by decide)]; exact hrest (.ph .t0))
    (by dsimp only; rw [hP _ (by decide) (by decide) (by decide)]; exact hrest (.ph .t1))
    (by dsimp only; rw [hph _ (by decide)])
  rw [phMap_arr] at e₇
  set X := encZ A w (phaseZ (topMaskOf N ρ K oS D) 1 Z)
  set R₇ := Function.update R₆ (reg .io) X with hR₇
  obtain ⟨v₈, hu₈, e₈⟩ := uclear_exec body (reg (.ph .msk)) v₇ { S with R := R₇ }
  obtain ⟨v₉, hu₉, e₉⟩ := uclear_exec body (reg (.ph .cnt)) v₈
    { S with R := Function.update R₇ (reg (.ph .msk)) [] }
  obtain ⟨v₁₀, hu₁₀, e₁₀⟩ := uclear_exec body (reg (.sc 0)) v₉
    { S with R := Function.update (Function.update R₇ (reg (.ph .msk)) []) (reg (.ph .cnt)) [] }
  obtain ⟨v₁₁, hu₁₁, e₁₁⟩ := uclear_exec body (reg (.sc 1)) v₁₀
    { S with
      R := Function.update (Function.update (Function.update R₇ (reg (.ph .msk)) [])
        (reg (.ph .cnt)) []) (reg (.sc 0)) [] }
  refine ⟨v₁₁, _, by rw [hu₁₁, hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ (Exec.seq e₈ (Exec.seq e₉ (Exec.seq e₁₀ e₁₁)))))))))) rfl ?_⟩
  · have hm : (R₆ (reg (.ph .msk))).length = N := by simp [hR₆, hR₅, hR₄]
    have hk : (R₆ (reg (.ph .cnt))).length = R * 2 ^ N := by simp [hR₆, hkkl]
    have h0 : (R₆ (reg (.sc 0))).length = ρ + oS := by simp [hR₆, hR₅, hR₄, hR₃, hR₂]
    have h1 : (R₆ (reg (.sc 1))).length = D := by simp [hR₆, hR₅, hR₄, hR₃]
    have hρ' : (R₁ (reg .ρ)).length = ρ := by simp [hR₁]; exact hT.hρ
    simp only [hR₇]
    topfupd
    rw [hm, hk, h0, h1]
    unfold topPhaseSCost
    simp only [List.length_replicate] at hm₆
    linarith [hc₁, hc₃, hc₅, hm₄, hm₆, hm₇]
  · congr 2
    funext k
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hsc]
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    by_cases h2 : k = reg (.ph .cnt)
    · subst h2; simp [hcnt]
    by_cases h3 : k = reg (.ph .msk)
    · subst h3; simp [hmsk]
    simp only [Function.update_apply, h0, h1, h2, h3, ↓reduceIte, hR₇]
    by_cases h4 : k = reg .io
    · simp [h4]
    · simp only [h4, ↓reduceIte, hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, Function.update_apply, h0, h1, h2,
        h3]

/-- Multiply every coefficient of `io` by the Gaussian integer `g` (through `racc`). -/
noncomputable def topUnit (g : GaussianInt) : Pr P (nT SXReg) Q A U :=
  .seq (autoWords (fun _ : Fin 1 => reg (BReg := SXReg) .io) (fun _ => reg .racc) (reg .st)
      (reg .ctr) (reg .tmp) (gaussAuto A ![![(g.re, g.im)]] (g.re.natAbs + g.im.natAbs) false))
    (moveR (reg .racc) (reg .io) id)

/-- The step bound of `topUnit` on an array of `R` rows of `2^n` records of `r` coefficients. -/
def topUnitCost (R n r w : ℕ) : ℕ :=
  (R * 2 ^ n * r * (5 * w + 6) + 2) + (2 * (R * 2 ^ n * r * w) + 2)

/-- **The unit.** `io` holding the stream of `Z` ends holding the stream of `g Z`. -/
theorem topUnit_exec (hA : 4 ≤ A) (g : GaussianInt)
    (hg : (2 * (g.re.natAbs + g.im.natAbs) + 1) ^ 2 ≤ A + 4) {R r n w : ℕ} (hw : 1 ≤ w)
    (Z : ZArr (Fin R × Fin r) n) (v : HS (nT SXReg) Q A U) (S : Stacks (nT SXReg) A)
    (hracc : S.R (reg .racc) = []) (hctr : (S.R (reg .ctr)).length = w)
    (htmp : S.R (reg .tmp) = []) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT SXReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ topUnitCost R n r w ∧
      Exec body (topUnit g) (mk v S) c
        (mk v' { S with R := Function.update S.R (reg .io) (encZ A w (fun p => g * Z p)) }) := by
  have hne : reg (BReg := SXReg) .io ≠ reg .racc := reg_ne (by simp)
  obtain ⟨v₁, m₁, S₁, hu₁, hm₁, e₁, hi₁, ho₁, hl₁, hin₁, hout₁, hoth₁⟩ := mulG_exec body
    (autoLayout_one (x := .io) (y := .racc) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp)) g.re g.im hA hg hw (ctrs := S.R (reg .ctr)) hctr (coeffList w Z) v S rfl
    htmp hio
  have hX : ((coeffList w Z).map (GR.mulG g.re g.im)).flatMap (coeffSyms A w) =
      encZ A w (fun p => g * Z p) := by
    rw [encZ, topCoeffList_mul]
  rw [hX, hracc, List.append_nil] at hout₁
  obtain ⟨v₂, hu₂, e₂⟩ := moveR_exec body (reg .racc) (reg .io) hne.symm id v₁ S₁
  have hS₁ : S₁ = { S with R := S₁.R } := by
    cases S₁; cases S; simp_all
  rw [hS₁] at e₁ e₂
  refine ⟨v₂, m₁ + (2 * (S₁.R (reg .racc)).length + 2), hu₂.trans hu₁, ?_,
    Exec.seq e₁ (Exec.cast e₂ rfl ?_)⟩
  · have hlen : (S₁.R (reg .racc)).length = R * 2 ^ n * r * w := by
      rw [hout₁, List.length_reverse, topEnc_length]
    rw [length_coeffList] at hm₁
    rw [hlen]
    unfold topUnitCost
    omega
  · congr 2
    funext k
    by_cases h1 : k = reg .io
    · subst h1
      have hin' : S₁.R (reg .io) = [] := by simpa using hin₁
      simp [movedR, hout₁, hin']
    by_cases h2 : k = reg .racc
    · subst h2; simp [movedR, hne.symm, hracc]
    simp only [movedR, Function.update_apply, h1, h2, ↓reduceIte]
    exact hoth₁ k h1 h2


end Stages

lemma topParState {A : ℕ} {Rg : Fin (nT SXReg) → List (Fin (A + 4))}
    {j u K ρ a₀ L rows n w rw : ℕ} (h1 : (Rg (reg .lev)).length = j)
    (h2 : (Rg (reg .u)).length = u) (h3 : (Rg (reg .K)).length = K)
    (h4 : (Rg (reg .ρ)).length = ρ) (h5 : (Rg (reg .a₀)).length = a₀)
    (h6 : (Rg (reg .L)).length = L) (h7 : (Rg (reg .rows)).length = rows)
    (h8 : (Rg (reg .n)).length = n) (h9 : (Rg (reg .w)).length = w)
    (h10 : (Rg (reg .rw)).length = rw) : ParState Rg j u K ρ a₀ L rows n w rw := by
  intro x
  cases x <;> first | exact trivial | assumption

/-- A register file agreeing with one at rest outside the parameter registers is at rest. -/
lemma topRest_par {A : ℕ} {Rg Rg' : Fin (nT SXReg) → List (Fin (A + 4))} {N r w : ℕ}
    (h : Rest bcEmpty N r w Rg) (hR : ∀ x, x ∉ parRegs (BReg := SXReg) → Rg' (reg x) = Rg (reg x)) :
    Rest bcEmpty N r w Rg' := by
  intro x
  by_cases hx : x ∈ parRegs (BReg := SXReg)
  · exact topRestSpec_par hx _
  · rw [hR x hx]; exact h x

section Kernels

variable {Q Ka : ℕ} {U : Type}

/-- The top kernels: `q` (field `5`) leaf bits at offset `aT` (field `6`), `L = K q` (field `7`),
`R` rows (field `3`); one call of the layer procedure at level `0`, skipped when `q = 0`. -/
noncomputable def topKerS : Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq (topRd (reg .u) 5)
  (.seq (.act (peekR (reg .u)))
  (.cond (·.flag)
    (.seq (topRd (reg .a₀) 6) (.seq (topRd (reg .L) 7) (.seq (topRd (reg .rows) 3) topCallClr)))
    (uclear (reg .u))))

/-- The step bound of `topKerS`. -/
noncomputable def topKerSCost (ds : ComplexFramedExecution.Directions) (cfg : List ℕ)
    (K ρ R N r w q aT : ℕ) : ℕ :=
  4 * topGetCost cfg + layerCost (nT SXReg) ds q K ρ R N r w 0 aT +
    (2 * q + 2 * aT + 2 * (K * q) + 2 * R + 16)

theorem topKerS_exec (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime + Ka)
    (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
    {cfg pfs : List ℕ} {N R r w K ρ q aT : ℕ} (h3 : cfg[3]? = some R) (h5 : cfg[5]? = some q)
    (h6 : cfg[6]? = some aT) (h7 : cfg[7]? = some (K * q))
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hρ : ρ < K) (hR : 1 ≤ R)
    (hfitT : ∀ i < q, aT + ρ + K * i < N) (hTL : aT + K * q ≤ N) (Z : ZArr (Fin R × Fin r) N)
    (v : HS (nT SXReg) Q (prime + Ka) U) (S : Stacks (nT SXReg) (prime + Ka))
    (hL : ∀ y, S.L y = []) (hT : TopRegs S.R N r w K ρ) (hI : TopIn S.R cfg pfs)
    (hio : S.R (reg .io) = encZ (prime + Ka) w Z) :
    ∃ (v' : HS (nT SXReg) Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      c ≤ topKerSCost ds cfg K ρ R N r w q aT ∧
      Exec (layerTable hQ ds) topKerS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io)
            (encZ (prime + Ka) w (k2s ((List.finRange q).map (actMap aT ρ K q N hfitT)) Z)) }) := by
  set body := layerTable (Ka := Ka) (U := U) hQ ds
  have hl3 : 3 < cfg.length := (List.getElem?_eq_some_iff.1 h3).1
  have hl5 : 5 < cfg.length := (List.getElem?_eq_some_iff.1 h5).1
  have hl6 : 6 < cfg.length := (List.getElem?_eq_some_iff.1 h6).1
  have hl7 : 7 < cfg.length := (List.getElem?_eq_some_iff.1 h7).1
  have hc3 : cfg[3] = R := (List.getElem?_eq_some_iff.1 h3).2
  have hc5 : cfg[5] = q := (List.getElem?_eq_some_iff.1 h5).2
  have hc6 : cfg[6] = aT := (List.getElem?_eq_some_iff.1 h6).2
  have hc7 : cfg[7] = K * q := (List.getElem?_eq_some_iff.1 h7).2
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := topRd_exec body (x := .u) (by simp) (by simp) 5 hl5 v S
    hlc hI.cf
  rw [hc5, hT.hu, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg .u) (List.replicate q tick) with hR₁
  have e₂ := Exec.act (body := body) (peekR (reg .u) : Act _ _ _ _) (mk v₁ { S with R := R₁ })
  rw [peekR_run] at e₂
  dsimp only at e₂
  have hu₁' : R₁ (reg .u) = List.replicate q tick := by simp [hR₁]
  cases q with
  | zero =>
      rw [hu₁'] at e₂
      simp only [List.replicate_zero, List.head?_nil, Option.isSome_none] at e₂
      obtain ⟨v₃, hu₃, e₃⟩ := uclear_exec body (reg .u) { v₁ with flag := false } { S with R := R₁ }
      have e₃' := Exec.cond_false (body := body) (f := (·.flag))
        (p := .seq (topRd (reg .a₀) 6) (.seq (topRd (reg .L) 7) (.seq (topRd (reg .rows) 3)
          topCallClr))) (by rfl) e₃
      refine ⟨v₃, _, by rw [hu₃, hu₁], ?_, Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₃')) rfl ?_⟩
      · unfold topKerSCost; simp [hR₁]; omega
      · congr 2
        funext k
        by_cases hk : k = reg .u
        · subst hk; simp [hR₁, hT.hu]
        · by_cases hk' : k = reg .io
          · subst hk'; simp [hR₁, hk, hio]; rfl
          · simp [hR₁, hk, hk']
  | succ q =>
      rw [hu₁'] at e₂
      simp only [List.replicate_succ, List.head?_cons, Option.isSome_some] at e₂
      obtain ⟨v₃, c₃, hu₃, hc₃', e₃⟩ := topRd_exec body (x := .a₀) (by simp) (by simp) 6 hl6
        { v₁ with flag := true } { S with R := R₁ } (by simp [hR₁, hlc])
        (by simpa [hR₁] using hI.cf)
      dsimp only at e₃
      rw [hc6, show R₁ (reg .a₀) = [] by simp [hR₁, hT.ha₀], List.append_nil] at e₃
      set R₃ := Function.update R₁ (reg .a₀) (List.replicate aT tick) with hR₃
      obtain ⟨v₄, c₄, hu₄, hc₄', e₄⟩ := topRd_exec body (x := .L) (by simp) (by simp) 7 hl7
        v₃ { S with R := R₃ } (by simp [hR₃, hR₁, hlc]) (by simpa [hR₃, hR₁] using hI.cf)
      dsimp only at e₄
      rw [hc7, show R₃ (reg .L) = [] by simp [hR₃, hR₁, hT.hL], List.append_nil] at e₄
      set R₄ := Function.update R₃ (reg .L) (List.replicate (K * (q + 1)) tick) with hR₄
      obtain ⟨v₅, c₅, hu₅, hc₅', e₅⟩ := topRd_exec body (x := .rows) (by simp) (by simp) 3 hl3
        v₄ { S with R := R₄ } (by simp [hR₄, hR₃, hR₁, hlc])
        (by simpa [hR₄, hR₃, hR₁] using hI.cf)
      dsimp only at e₅
      rw [hc3, show R₄ (reg .rows) = [] by simp [hR₄, hR₃, hR₁, hT.hrows], List.append_nil] at e₅
      set R₅ := Function.update R₄ (reg .rows) (List.replicate R tick) with hR₅
      have hR₅o : ∀ x : LReg SXReg, x ≠ .u → x ≠ .a₀ → x ≠ .L → x ≠ .rows →
          R₅ (reg x) = S.R (reg x) := by
        intro x h1 h2 h3 h4
        simp [hR₅, hR₄, hR₃, hR₁, h1, h2, h3, h4]
      have hpar : ParState R₅ 0 (q + 1) K ρ aT (K * bits (q + 1) 0) (rowsAt R 0) N w (r * w) := by
        have hh : ∀ x : LReg SXReg, x ∈ [LReg.lev, .K, .ρ, .n, .w, .rw] →
            R₅ (reg x) = S.R (reg x) := by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact hR₅o _ (by simp) (by simp) (by simp) (by simp)
        refine topParState ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · rw [hh _ (by simp), hT.hlev]; rfl
        · simp [hR₅, hR₄, hR₃, hR₁]
        · rw [hh _ (by simp)]; exact hT.hK
        · rw [hh _ (by simp)]; exact hT.hρ
        · simp [hR₅, hR₄, hR₃]
        · simp [hR₅, hR₄, bits]
        · simp [hR₅, rowsAt]
        · rw [hh _ (by simp)]; exact hT.hn
        · rw [hh _ (by simp)]; exact hT.hw
        · rw [hh _ (by simp)]; exact hT.hrw
      have hrest₅ : Rest bcEmpty N r w R₅ := topRest_par hT.rest fun x hx =>
        hR₅o x (fun h => hx (by simp [h, parRegs])) (fun h => hx (by simp [h, parRegs]))
          (fun h => hx (by simp [h, parRegs])) (fun h => hx (by simp [h, parRegs]))
      obtain ⟨v₆, c₆, hu₆, hc₆, e₆⟩ := topCallClr_exec hQ ds hA hA9 hNW hgate (j := 0) (u := q + 1)
        (R₀ := R) hr hw hρ (by omega) hR (fun i hi => absurd hi (Nat.not_lt_zero _)) hfitT hTL Z v₅
        { S with R := R₅ } hL hpar hrest₅
        ((hR₅o .io (by simp) (by simp) (by simp) (by simp)).trans hio)
      have e₇ := Exec.cond_true (body := body) (f := (·.flag)) (q := uclear (reg .u))
        (show ({ v₁ with flag := true } : HS _ _ _ _).flag = true from rfl)
        (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆)))
      refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₁], ?_,
        Exec.cast (Exec.seq e₁ (Exec.seq e₂ e₇)) rfl ?_⟩
      · unfold topKerSCost
        simp only [bits, rowsAt] at hc₆
        omega
      · congr 2
        funext k
        by_cases h1 : k = reg .u
        · subst h1; simp [hT.hu]
        by_cases h2 : k = reg .a₀
        · subst h2; simp [hT.ha₀]
        by_cases h3 : k = reg .L
        · subst h3; simp [hT.hL]
        by_cases h4 : k = reg .rows
        · subst h4; simp [hT.hrows]
        by_cases h5 : k = reg .lev
        · subst h5; simp [hT.hlev]
        simp only [Function.update_apply, h1, h2, h3, h4, h5, ↓reduceIte]
        by_cases h6 : k = reg .io
        · simp [h6]; rfl
        · simp only [h6, ↓reduceIte, hR₅, hR₄, hR₃, hR₁, Function.update_apply, h1, h2, h3, h4]

end Kernels

/-! ### The unit and the shift -/

lemma topUnitD_mod (D : ℕ) : unitD D = unitD (D % 8) := by
  have h4 : (⟨0, -1⟩ : GaussianInt) ^ 4 = 1 := by decide
  unfold unitD
  rw [pow_eq_pow_mod (D / 2) h4, pow_eq_pow_mod ((D % 8) / 2) h4,
    show D / 2 % 4 = D % 8 / 2 % 4 by omega, show D % 2 = D % 8 % 2 by omega]

/-- The unit `unitD D` has parts of absolute values summing to at most `2`. -/
lemma topUnitD_bound (D : ℕ) : (unitD D).re.natAbs + (unitD D).im.natAbs ≤ 2 := by
  have h4 : (⟨0, -1⟩ : GaussianInt) ^ 4 = 1 := by decide
  unfold unitD
  rw [pow_eq_pow_mod (D / 2) h4]
  have h1 : D / 2 % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h2 : D % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize D / 2 % 4 = x at h1 ⊢
  generalize D % 2 = y at h2 ⊢
  interval_cases x <;> interval_cases y <;> decide

section UnitShift

variable {Q A : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q A U)

/-- The unit stage: `D` (field `9`) modulo `8` into the scan slot `lev`, then the multiplication
by `unitD D` chosen by an eight-way dispatch. -/
noncomputable def topUnitS : Pr P (nT SXReg) Q A U :=
  .seq (topRd (reg (.sc 0)) 9)
  (.seq (topResid 8 (reg (.sc 0)) (reg (.sc 3)) (reg .lev))
  (.seq (topDisp8 (reg .lev) (fun q => topUnit (unitD q.val))) (uclear (reg (.sc 0)))))

/-- The step bound of `topUnitS`. -/
def topUnitSCost (cfg : List ℕ) (R N r w D : ℕ) : ℕ :=
  topGetCost cfg + (4 * D + 4) + (topUnitCost R N r w + 7) + (2 * D + 2)

theorem topUnitS_exec (hA : 21 ≤ A) {cfg pfs : List ℕ} {R N r w K ρ D : ℕ}
    (h9 : cfg[9]? = some D) (hw : 1 ≤ w) (Z : ZArr (Fin R × Fin r) N)
    (v : HS (nT SXReg) Q A U) (S : Stacks (nT SXReg) A) (hT : TopRegs S.R N r w K ρ)
    (hI : TopIn S.R cfg pfs) (hio : S.R (reg .io) = encZ A w Z) :
    ∃ (v' : HS (nT SXReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ topUnitSCost cfg R N r w D ∧
      Exec body topUnitS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w (fun p => unitD D * Z p)) }) := by
  have hl9 : 9 < cfg.length := (List.getElem?_eq_some_iff.1 h9).1
  have hc9 : cfg[9] = D := (List.getElem?_eq_some_iff.1 h9).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := topRd_exec body (x := .sc 0) (by simp) (by simp) 9 hl9 v S
    (hT.rest .lenctr) hI.cf
  rw [hc9, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate D tick) with hR₁
  obtain ⟨v₂, hu₂, hsc₂, e₂⟩ := topResid_exec body (W := 8) (by norm_num) (by omega)
    (i := reg (.sc 0)) (t := reg (.sc 3)) (reg_ne (by simp)) (reg .lev) v₁ { S with R := R₁ }
    (by simp [hR₁, hsc])
  simp only [hR₁, Function.update_self, List.length_replicate] at hsc₂ e₂
  have hg : (2 * ((unitD (D % 8)).re.natAbs + (unitD (D % 8)).im.natAbs) + 1) ^ 2 ≤ A + 4 := by
    have := topUnitD_bound (D % 8)
    have h25 : (2 * ((unitD (D % 8)).re.natAbs + (unitD (D % 8)).im.natAbs) + 1) ^ 2 ≤
        5 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  obtain ⟨v₃, c₃, hu₃, hc₃, e₃⟩ := topUnit_exec body (by omega) (unitD (D % 8)) hg hw Z v₂
    { S with R := R₁ } (by have h : S.R (reg .racc) = [] := hT.rest .racc; simp [hR₁, h])
    (by simp [hR₁]; exact hT.rest .ctr)
    (by have h : S.R (reg .tmp) = [] := hT.rest .tmp; simp [hR₁, h]) (by simp [hR₁, hio])
  obtain ⟨c₃', hc₃', e₃'⟩ := topDisp8_exec body (reg .lev) (fun q => topUnit (unitD q.val))
    ⟨D % 8, Nat.mod_lt _ (by norm_num)⟩ v₂ { S with R := R₁ } hsc₂ e₃
  rw [← topUnitD_mod] at e₃'
  set R₃ := Function.update R₁ (reg .io) (encZ A w (fun p => unitD D * Z p)) with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := uclear_exec body (reg (.sc 0)) v₃ { S with R := R₃ }
  refine ⟨v₄, _, by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃' e₄))) rfl ?_⟩
  · simp only [hR₃, hR₁]
    topfupd
    simp only [List.length_replicate]
    unfold topUnitSCost
    omega
  · congr 2
    funext k
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    simp [hR₃, hR₁, Function.update_apply, h0]

/-- The shift stage: `s` (field `1`), `w` (field `0`) and `w' - s - w` on `sc 0`, `sc 1`,
`sc 2`; the truncating shift pass (spares `racc`, `rctmp`, `sc 3`, `sc 4`, `sc 5`). -/
noncomputable def topShiftS : Pr P (nT SXReg) Q A U :=
  .seq (topRd (reg (.sc 0)) 1)
  (.seq (topRd (reg (.sc 1)) 0)
  (.seq (ucopy (reg .w) (reg (.sc 2)) (reg .tS))
  (.seq (usub (reg (.sc 0)) (reg (.sc 2)) (reg .tS))
  (.seq (usub (reg (.sc 1)) (reg (.sc 2)) (reg .tS))
  (.seq (topPass (reg .io) (reg .rctmp) (topShiftWord (reg .io) (reg .rctmp) (reg .racc) (reg .w)
      (reg (.sc 0)) (reg (.sc 1)) (reg (.sc 2)) (reg (.sc 3)) (reg (.sc 4)) (reg (.sc 5))))
  (.seq (uclear (reg (.sc 0))) (.seq (uclear (reg (.sc 1))) (uclear (reg (.sc 2))))))))))

/-- The step bound of `topShiftS`. -/
def topShiftSCost (cfg : List ℕ) (R N r w' s w : ℕ) : ℕ :=
  2 * topGetCost cfg + (4 * w' + 4) + (4 * s + 4) + (4 * w + 4) + topShiftCost R N r w' s w +
    (2 * s + 2) + (2 * w + 2) + (2 * (w' - s - w) + 2)

theorem topShiftS_exec (hA : 4 ≤ A) {cfg pfs : List ℕ} {R N r w' K ρ s w : ℕ}
    (h0 : cfg[0]? = some w) (h1 : cfg[1]? = some s) (hw' : 1 ≤ w') (hsw : s + w ≤ w')
    (Z : ZArr (Fin R × Fin r) N) (hZ : ∀ p, TopFitsZ w' (Z p))
    (v : HS (nT SXReg) Q A U) (S : Stacks (nT SXReg) A) (hT : TopRegs S.R N r w' K ρ)
    (hI : TopIn S.R cfg pfs) (hio : S.R (reg .io) = encZ A w' Z) :
    ∃ (v' : HS (nT SXReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ topShiftSCost cfg R N r w' s w ∧
      Exec body topShiftS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ A w (fun p => tdivZ s (Z p))) }) := by
  have hl0 : 0 < cfg.length := (List.getElem?_eq_some_iff.1 h0).1
  have hl1 : 1 < cfg.length := (List.getElem?_eq_some_iff.1 h1).1
  have hc0 : cfg[0] = w := (List.getElem?_eq_some_iff.1 h0).2
  have hc1 : cfg[1] = s := (List.getElem?_eq_some_iff.1 h1).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have htS : S.R (reg .tS) = [] := hT.rest .tS
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := topRd_exec body (x := .sc 0) (by simp) (by simp) 1 hl1 v S
    hlc hI.cf
  rw [hc1, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate s tick) with hR₁
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := topRd_exec body (x := .sc 1) (by simp) (by simp) 0 hl0 v₁
    { S with R := R₁ } (by simp [hR₁, hlc]) (by simpa [hR₁] using hI.cf)
  dsimp only at e₂
  rw [hc0, show R₁ (reg (.sc 1)) = [] by simp [hR₁, hsc], List.append_nil] at e₂
  set R₂ := Function.update R₁ (reg (.sc 1)) (List.replicate w tick) with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := ucopy_exec body (a := reg .w) (b := reg (.sc 2)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ }
    (by simp [hR₂, hR₁, htS])
  dsimp only at e₃
  rw [show (R₂ (reg .w)).length = w' by simp [hR₂, hR₁]; exact hT.hw,
    show R₂ (reg (.sc 2)) = [] by simp [hR₂, hR₁, hsc], List.append_nil] at e₃
  set R₃ := Function.update R₂ (reg (.sc 2)) (List.replicate w' tick) with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := usub_exec body (a := reg (.sc 0)) (b := reg (.sc 2)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₃ { S with R := R₃ }
    (by simp [hR₃, hR₂, hR₁, htS])
  dsimp only at e₄
  rw [show R₃ (reg (.sc 0)) = List.replicate s tick by simp [hR₃, hR₂, hR₁],
    show R₃ (reg (.sc 2)) = List.replicate w' tick by simp [hR₃], List.length_replicate,
    List.drop_replicate] at e₄
  set R₄ := Function.update R₃ (reg (.sc 2)) (List.replicate (w' - s) tick) with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := usub_exec body (a := reg (.sc 1)) (b := reg (.sc 2)) (t := reg .tS)
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₄ { S with R := R₄ }
    (by simp [hR₄, hR₃, hR₂, hR₁, htS])
  dsimp only at e₅
  rw [show R₄ (reg (.sc 1)) = List.replicate w tick by simp [hR₄, hR₃, hR₂],
    show R₄ (reg (.sc 2)) = List.replicate (w' - s) tick by simp [hR₄], List.length_replicate,
    List.drop_replicate] at e₅
  set R₅ := Function.update R₄ (reg (.sc 2)) (List.replicate (w' - s - w) tick) with hR₅
  obtain ⟨v₆, hu₆, e₆⟩ := topShiftP_exec body hA (src := reg .io) (dst := reg .rctmp)
    (tmp := reg .racc) (cW := reg .w) (cS := reg (.sc 0)) (cE := reg (.sc 1)) (cD := reg (.sc 2))
    (sp := reg (.sc 3)) (sg := reg (.sc 4)) (cy := reg (.sc 5))
    (nodup_map_reg (l := [.io, .rctmp, .racc, .w, .sc 0, .sc 1, .sc 2, .sc 3, .sc 4, .sc 5])
      (by simp)) hw' hsw Z hZ v₅ { S with R := R₅ }
    (by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hio])
    (by have h : S.R (reg .rctmp) = [] := hT.rest .rctmp; simp [hR₅, hR₄, hR₃, hR₂, hR₁, h])
    ⟨by simp [hR₅, hR₄, hR₃, hR₂, hR₁]; exact hT.hw, by simp [hR₅, hR₄, hR₃, hR₂, hR₁],
      by simp [hR₅, hR₄, hR₃, hR₂], by simp [hR₅], by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc],
      by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc], by simp [hR₅, hR₄, hR₃, hR₂, hR₁, hsc],
      by have h : S.R (reg .racc) = [] := hT.rest .racc; simp [hR₅, hR₄, hR₃, hR₂, hR₁, h]⟩
  set R₆ := Function.update R₅ (reg .io) (encZ A w (fun p => tdivZ s (Z p))) with hR₆
  obtain ⟨v₇, hu₇, e₇⟩ := uclear_exec body (reg (.sc 0)) v₆ { S with R := R₆ }
  obtain ⟨v₈, hu₈, e₈⟩ := uclear_exec body (reg (.sc 1)) v₇
    { S with R := Function.update R₆ (reg (.sc 0)) [] }
  obtain ⟨v₉, hu₉, e₉⟩ := uclear_exec body (reg (.sc 2)) v₈
    { S with R := Function.update (Function.update R₆ (reg (.sc 0)) []) (reg (.sc 1)) [] }
  refine ⟨v₉, _, by rw [hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ (Exec.seq e₈ e₉)))))))) rfl ?_⟩
  · simp only [hR₆, hR₅, hR₄, hR₃, hR₂, hR₁]
    topfupd
    simp only [List.length_replicate]
    unfold topShiftSCost
    omega
  · congr 2
    funext k
    by_cases h2 : k = reg (.sc 2)
    · subst h2; simp [hsc]
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hsc]
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    simp [hR₆, hR₅, hR₄, hR₃, hR₂, hR₁, Function.update_apply, h0, h1, h2]

end UnitShift

/-! ### The rest state for the pieces -/

section Down

variable {Q A : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q A U)

/-- The registers for the pieces: `a` symbols of `n` on `st`, `rowctr` on `cs`, `rowctr` rebuilt
with `2^n r w` symbols, the address fields `binSyms n 0`. -/
noncomputable def topDownR (Rg : Fin (nT SXReg) → List (Fin (A + 4))) (a n r w : ℕ) :
    Fin (nT SXReg) → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update Rg (reg .n) ((Rg (reg .n)).drop a)) (reg .st) ((Rg (reg .n)).take a).reverse)
    (reg (.ph .af)) (binSyms n 0)) (reg (.lf (.k .cf))) (binSyms n 0)) (reg .cs)
    (Rg (reg .rowctr)).reverse) (reg .rowctr)
    ((List.replicate (r * w) tick).flatMap (List.replicate (2 ^ n)))

/-- `topDownR` keeps every register outside `n`, `st`, `ph .af`, `lf (.k .cf)`, `cs`, `rowctr`. -/
lemma topDownR_of_ne {Rg : Fin (nT SXReg) → List (Fin (A + 4))} {a n r w : ℕ} {x : LReg SXReg}
    (h1 : x ≠ .n) (h2 : x ≠ .st) (h3 : x ≠ .ph .af) (h4 : x ≠ .lf (.k .cf)) (h5 : x ≠ .cs)
    (h6 : x ≠ .rowctr) : topDownR Rg a n r w (reg x) = Rg (reg x) := by
  simp [topDownR, h1, h2, h3, h4, h5, h6]

lemma topDownR_par {Rg : Fin (nT SXReg) → List (Fin (A + 4))} {a n r w : ℕ} {x : LReg SXReg}
    (hx : x ∈ [LReg.lev, .u, .a₀, .L, .rows, .w, .rw, .K, .ρ]) :
    topDownR Rg a n r w (reg x) = Rg (reg x) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact topDownR_of_ne (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)

lemma topDownR_regs {Rg : Fin (nT SXReg) → List (Fin (A + 4))} {n a r w K ρ : ℕ}
    (hT : TopRegs Rg (n + a) r w K ρ) : TopRegs (topDownR Rg a n r w) n r w K ρ where
  rest := fun x => by
    by_cases h1 : x = .n
    · subst h1; trivial
    by_cases h2 : x = .st
    · subst h2; trivial
    by_cases h3 : x = .ph .af
    · subst h3; simp [topDownR, restSpec, phRest]
    by_cases h4 : x = .lf (.k .cf)
    · subst h4; simp [topDownR, restSpec, lfRest]
    by_cases h5 : x = .cs
    · subst h5; trivial
    by_cases h6 : x = .rowctr
    · subst h6
      simp [topDownR, restSpec]
      ring
    rw [topDownR_of_ne h1 h2 h3 h4 h5 h6]
    exact (topRestSpec_bits h3 h4 h6).1 (hT.rest x)
  hlev := by rw [topDownR_par (by simp)]; exact hT.hlev
  hu := by rw [topDownR_par (by simp)]; exact hT.hu
  ha₀ := by rw [topDownR_par (by simp)]; exact hT.ha₀
  hL := by rw [topDownR_par (by simp)]; exact hT.hL
  hrows := by rw [topDownR_par (by simp)]; exact hT.hrows
  hn := by simp [topDownR, hT.hn]
  hw := by rw [topDownR_par (by simp)]; exact hT.hw
  hrw := by rw [topDownR_par (by simp)]; exact hT.hrw
  hK := by rw [topDownR_par (by simp)]; exact hT.hK
  hρ := by rw [topDownR_par (by simp)]; exact hT.hρ

/-- From the rest state for `n + a` address bits to the one for `n` (`a` from field `2`). -/
noncomputable def topDownS : Pr P (nT SXReg) Q A U :=
  .seq (topRd (reg (.sc 0)) 2)
  (.seq (Shift.counted (reg (.sc 0)) (reg (.sc 3)) (Shift.copyStep (reg (.sc 0)) (reg (.sc 3))
      (reg .n) (reg .st)))
  (.seq (usub (reg (.sc 0)) (reg (.ph .af)) (reg (.sc 3)))
  (.seq (usub (reg (.sc 0)) (reg (.lf (.k .cf))) (reg (.sc 3)))
  (.seq (moveR (reg .rowctr) (reg .cs) id)
  (.seq (ucopy (reg .rw) (reg .rowctr) (reg (.sc 3)))
  (.seq (upow2 (reg .n) (reg .rowctr) (reg (.sc 4)) (reg (.sc 5)))
    (uclear (reg (.sc 0)))))))))

/-- The step bound of `topDownS`. -/
def topDownCost (cfg : List ℕ) (n a r w : ℕ) : ℕ :=
  topGetCost cfg + (4 * a + 4) + (4 * a + 4) + (4 * a + 4) + (2 * (2 ^ (n + a) * r * w) + 2) +
    (4 * (r * w) + 4) + (4 * (2 ^ n * (r * w)) + 9 * n + 4) + (2 * a + 2)

theorem topDownS_exec {cfg pfs : List ℕ} {n a r w K ρ : ℕ} (h2 : cfg[2]? = some a)
    (v : HS (nT SXReg) Q A U) (S : Stacks (nT SXReg) A) (hT : TopRegs S.R (n + a) r w K ρ)
    (hI : TopIn S.R cfg pfs) :
    ∃ (v' : HS (nT SXReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ topDownCost cfg n a r w ∧
      Exec body topDownS (mk v S) c (mk v' { S with R := topDownR S.R a n r w }) := by
  have hl2 : 2 < cfg.length := (List.getElem?_eq_some_iff.1 h2).1
  have hc2 : cfg[2] = a := (List.getElem?_eq_some_iff.1 h2).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  set ln := S.R (reg .n) with hln
  set lr := S.R (reg .rowctr) with hlr
  have hlnl : ln.length = n + a := hT.hn
  have hlrl : lr.length = 2 ^ (n + a) * r * w := hT.rest .rowctr
  have haf : S.R (reg (.ph .af)) = List.replicate (n + a) (bitSymbol false) := by
    rw [← binSyms_zero_right]; exact hT.rest (.ph .af)
  have hcf : S.R (reg (.lf (.k .cf))) = List.replicate (n + a) (bitSymbol false) := by
    rw [← binSyms_zero_right]; exact hT.rest (.lf (.k .cf))
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := topRd_exec body (x := .sc 0) (by simp) (by simp) 2 hl2 v S
    hlc hI.cf
  rw [hc2, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate a tick) with hR₁
  obtain ⟨v₂, hv₂, e₂⟩ := topCopyC_exec body (c := reg (.sc 0)) (t := reg (.sc 3))
    (src := reg .n) (dst := reg .st) (nodup_map_reg (l := [.sc 0, .sc 3, .n, .st]) (by simp))
    (ln.take a) (ln.drop a) v₁ { S with R := R₁ } (by simp [hR₁, hlnl])
    (by simp [hR₁, hln]) (by simp [hR₁, hsc])
  rw [show (ln.take a).length = a by simp [hlnl]] at e₂
  set R₂ := Function.update (Function.update R₁ (reg .n) (ln.drop a)) (reg .st)
    ((ln.take a).reverse ++ R₁ (reg .st)) with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := usub_exec body (a := reg (.sc 0)) (b := reg (.ph .af)) (t := reg (.sc 3))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₂ { S with R := R₂ }
    (by simp [hR₂, hR₁, hsc])
  dsimp only at e₃
  rw [show (R₂ (reg (.sc 0))).length = a by simp [hR₂, hR₁],
    show R₂ (reg (.ph .af)) = List.replicate (n + a) (bitSymbol false) by simp [hR₂, hR₁, haf],
    List.drop_replicate, Nat.add_sub_cancel, ← binSyms_zero_right] at e₃
  set R₃ := Function.update R₂ (reg (.ph .af)) (binSyms n 0) with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := usub_exec body (a := reg (.sc 0)) (b := reg (.lf (.k .cf)))
    (t := reg (.sc 3)) (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₃
    { S with R := R₃ } (by simp [hR₃, hR₂, hR₁, hsc])
  dsimp only at e₄
  rw [show (R₃ (reg (.sc 0))).length = a by simp [hR₃, hR₂, hR₁],
    show R₃ (reg (.lf (.k .cf))) = List.replicate (n + a) (bitSymbol false) by
      simp [hR₃, hR₂, hR₁, hcf],
    List.drop_replicate, Nat.add_sub_cancel, ← binSyms_zero_right] at e₄
  set R₄ := Function.update R₃ (reg (.lf (.k .cf))) (binSyms n 0) with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := moveR_exec body (reg .rowctr) (reg .cs) (reg_ne (by simp)) id v₄
    { S with R := R₄ }
  dsimp only at e₅
  have hR₄r : R₄ (reg .rowctr) = lr := by simp [hR₄, hR₃, hR₂, hR₁, hlr]
  rw [hR₄r] at e₅
  set R₅ := movedR R₄ (reg .rowctr) (reg .cs) id lr with hR₅
  obtain ⟨v₆, hu₆, e₆⟩ := ucopy_exec body (a := reg .rw) (b := reg .rowctr) (t := reg (.sc 3))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₅ { S with R := R₅ }
    (by simp [hR₅, movedR, hR₄, hR₃, hR₂, hR₁, hsc])
  dsimp only at e₆
  rw [show (R₅ (reg .rw)).length = r * w by simp [hR₅, movedR, hR₄, hR₃, hR₂, hR₁]; exact hT.hrw,
    show R₅ (reg .rowctr) = [] by simp [hR₅, movedR], List.append_nil] at e₆
  set R₆ := Function.update R₅ (reg .rowctr) (List.replicate (r * w) tick) with hR₆
  obtain ⟨v₇, m₇, hu₇, hm₇, e₇⟩ := upow2_exec body (a := reg .n) (b := reg .rowctr)
    (t₁ := reg (.sc 4)) (t₂ := reg (.sc 5)) (nodup_map_reg (l := [.n, .rowctr, .sc 4, .sc 5])
      (by simp)) v₆ { S with R := R₆ } (by simp [hR₆, hR₅, movedR, hR₄, hR₃, hR₂, hR₁, hsc])
    (by simp [hR₆, hR₅, movedR, hR₄, hR₃, hR₂, hR₁, hsc])
  dsimp only at e₇ hm₇
  have hn₆ : (R₆ (reg .n)).length = n := by
    simp [hR₆, hR₅, movedR, hR₄, hR₃, hR₂, hlnl]
  have hr₆ : R₆ (reg .rowctr) = List.replicate (r * w) tick := by simp [hR₆]
  rw [hn₆, hr₆] at e₇ hm₇
  set R₇ := Function.update R₆ (reg .rowctr)
    ((List.replicate (r * w) tick).flatMap (List.replicate (2 ^ n))) with hR₇
  obtain ⟨v₈, hu₈, e₈⟩ := uclear_exec body (reg (.sc 0)) v₇ { S with R := R₇ }
  refine ⟨v₈, _, by rw [hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hv₂.user, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ e₈))))))) rfl ?_⟩
  · have h0 : (R₇ (reg (.sc 0))).length = a := by
      simp [hR₇, hR₆, hR₅, movedR, hR₄, hR₃, hR₂, hR₁]
    rw [h0]
    simp only [List.length_replicate] at hm₇
    unfold topDownCost
    rw [hlrl]
    nlinarith [hc₁, hm₇]
  · congr 2
    funext k
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [topDownR, hsc]
    rw [Function.update_of_ne h0]
    by_cases h1 : k = reg .rowctr
    · subst h1; simp [hR₇, topDownR]
    by_cases h2 : k = reg .cs
    · subst h2
      simp [hR₇, hR₆, hR₅, movedR, topDownR, hI.y, hR₄, hR₃, hR₂, hR₁, hlr]
    by_cases h3 : k = reg (.lf (.k .cf))
    · subst h3; simp [hR₇, hR₆, hR₅, movedR, hR₄, topDownR]
    by_cases h4 : k = reg (.ph .af)
    · subst h4; simp [hR₇, hR₆, hR₅, movedR, hR₄, hR₃, topDownR]
    by_cases h5 : k = reg .st
    · subst h5; simp [hR₇, hR₆, hR₅, movedR, hR₄, hR₃, hR₂, topDownR, hI.x, hR₁, hln]
    by_cases h6 : k = reg .n
    · subst h6; simp [hR₇, hR₆, hR₅, movedR, hR₄, hR₃, hR₂, topDownR, hln]
    simp [hR₇, hR₆, hR₅, movedR, hR₄, hR₃, hR₂, hR₁, topDownR, 
      h0, h1, h2, h3, h4, h5, h6]

/-- Back to the rest state for `n + a` address bits. -/
noncomputable def topUpS : Pr P (nT SXReg) Q A U :=
  .seq (topRd (reg (.sc 0)) 2)
  (.seq (uclear (reg .rowctr))
  (.seq (moveR (reg .cs) (reg .rowctr) id)
  (.seq (zeroBits (reg (.sc 0)) (reg (.ph .af)) (reg (.sc 3)))
  (.seq (zeroBits (reg (.sc 0)) (reg (.lf (.k .cf))) (reg (.sc 3)))
  (.seq (moveR (reg .st) (reg .n) id) (uclear (reg (.sc 0))))))))

/-- The step bound of `topUpS`. -/
def topUpCost (cfg : List ℕ) (n a r w : ℕ) : ℕ :=
  topGetCost cfg + (2 * (2 ^ n * (r * w)) + 2) + (2 * (2 ^ (n + a) * r * w) + 2) + (4 * a + 4) +
    (4 * a + 4) + (2 * a + 2) + (2 * a + 2)

theorem topUpS_exec {cfg pfs : List ℕ} {n a r w K ρ : ℕ} (h2 : cfg[2]? = some a)
    (v : HS (nT SXReg) Q A U) (S : Stacks (nT SXReg) A) (hT : TopRegs S.R (n + a) r w K ρ)
    (hI : TopIn S.R cfg pfs) (X : List (Fin (A + 4))) :
    ∃ (v' : HS (nT SXReg) Q A U) (c : ℕ), v'.user = v.user ∧ c ≤ topUpCost cfg n a r w ∧
      Exec body topUpS (mk v { S with R := Function.update (topDownR S.R a n r w) (reg .io) X }) c
        (mk v' { S with R := Function.update S.R (reg .io) X }) := by
  have hl2 : 2 < cfg.length := (List.getElem?_eq_some_iff.1 h2).1
  have hc2 : cfg[2] = a := (List.getElem?_eq_some_iff.1 h2).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  set ln := S.R (reg .n) with hln
  set lr := S.R (reg .rowctr) with hlr
  have hlnl : ln.length = n + a := hT.hn
  have hlrl : lr.length = 2 ^ (n + a) * r * w := hT.rest .rowctr
  have haf : S.R (reg (.ph .af)) = List.replicate (n + a) (bitSymbol false) := by
    rw [← binSyms_zero_right]; exact hT.rest (.ph .af)
  have hcf : S.R (reg (.lf (.k .cf))) = List.replicate (n + a) (bitSymbol false) := by
    rw [← binSyms_zero_right]; exact hT.rest (.lf (.k .cf))
  set Rd := Function.update (topDownR S.R a n r w) (reg .io) X with hRd
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := topRd_exec body (x := .sc 0) (by simp) (by simp) 2 hl2 v
    { S with R := Rd } (by simp [hRd, topDownR, hlc]) (by simpa [hRd, topDownR] using hI.cf)
  dsimp only at e₁
  rw [hc2, show Rd (reg (.sc 0)) = [] by simp [hRd, topDownR, hsc], List.append_nil] at e₁
  set R₁ := Function.update Rd (reg (.sc 0)) (List.replicate a tick) with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := uclear_exec body (reg .rowctr) v₁ { S with R := R₁ }
  dsimp only at e₂
  set R₂ := Function.update R₁ (reg .rowctr) [] with hR₂
  obtain ⟨v₃, hu₃, e₃⟩ := moveR_exec body (reg .cs) (reg .rowctr) (reg_ne (by simp)) id v₂
    { S with R := R₂ }
  dsimp only at e₃
  have hR₂c : R₂ (reg .cs) = lr.reverse := by simp [hR₂, hR₁, hRd, topDownR, hlr]
  rw [hR₂c] at e₃
  set R₃ := movedR R₂ (reg .cs) (reg .rowctr) id lr.reverse with hR₃
  obtain ⟨v₄, hu₄, e₄⟩ := zeroBits_exec body (len := reg (.sc 0)) (z := reg (.ph .af))
    (t := reg (.sc 3)) (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₃
    { S with R := R₃ } (by simp [hR₃, movedR, hR₂, hR₁, hRd, topDownR, hsc])
  dsimp only at e₄
  have hR₃0 : (R₃ (reg (.sc 0))).length = a := by simp [hR₃, movedR, hR₂, hR₁]
  rw [hR₃0, show R₃ (reg (.ph .af)) = binSyms n 0 by
    simp [hR₃, movedR, hR₂, hR₁, hRd, topDownR]] at e₄
  set R₄ := Function.update R₃ (reg (.ph .af)) (binSyms a 0 ++ binSyms n 0) with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := zeroBits_exec body (len := reg (.sc 0)) (z := reg (.lf (.k .cf)))
    (t := reg (.sc 3)) (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₄
    { S with R := R₄ } (by simp [hR₄, hR₃, movedR, hR₂, hR₁, hRd, topDownR, hsc])
  dsimp only at e₅
  rw [show (R₄ (reg (.sc 0))).length = a by simp [hR₄, hR₃, movedR, hR₂, hR₁],
    show R₄ (reg (.lf (.k .cf))) = binSyms n 0 by
      simp [hR₄, hR₃, movedR, hR₂, hR₁, hRd, topDownR]] at e₅
  set R₅ := Function.update R₄ (reg (.lf (.k .cf))) (binSyms a 0 ++ binSyms n 0) with hR₅
  obtain ⟨v₆, hu₆, e₆⟩ := moveR_exec body (reg .st) (reg .n) (reg_ne (by simp)) id v₅
    { S with R := R₅ }
  dsimp only at e₆
  have hR₅s : R₅ (reg .st) = (ln.take a).reverse := by
    simp [hR₅, hR₄, hR₃, movedR, hR₂, hR₁, hRd, topDownR, hln]
  rw [hR₅s] at e₆
  set R₆ := movedR R₅ (reg .st) (reg .n) id (ln.take a).reverse with hR₆
  obtain ⟨v₇, hu₇, e₇⟩ := uclear_exec body (reg (.sc 0)) v₆ { S with R := R₆ }
  refine ⟨v₇, _, by rw [hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      e₇)))))) rfl ?_⟩
  · have h1 : (R₁ (reg .rowctr)).length = 2 ^ n * (r * w) := by
      simp [hR₁, hRd, topDownR]; ring
    have h6 : (R₆ (reg (.sc 0))).length = a := by simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂, hR₁]
    rw [h1, h6]
    simp only [List.length_reverse, List.length_take, hlnl, hlrl]
    unfold topUpCost
    have : min a (n + a) = a := by omega
    rw [this]
    omega
  · congr 2
    funext k
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    rw [Function.update_of_ne h0]
    by_cases h1 : k = reg .n
    · subst h1
      simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂, hR₁, hRd, topDownR, hln]
    by_cases h2 : k = reg .st
    · subst h2; simp [hR₆, movedR, hI.x]
    by_cases h3 : k = reg (.lf (.k .cf))
    · subst h3
      simp [hR₆, movedR, hR₅, hcf, binSyms_zero_right, List.replicate_append_replicate,
        Nat.add_comm]
    by_cases h4 : k = reg (.ph .af)
    · subst h4
      simp [hR₆, movedR, hR₅, hR₄, haf, binSyms_zero_right, List.replicate_append_replicate,
        Nat.add_comm]
    by_cases h5 : k = reg .rowctr
    · subst h5; simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂, hlr]
    by_cases h6 : k = reg .cs
    · subst h6; simp [hR₆, movedR, hR₅, hR₄, hR₃, hI.y]
    by_cases h7 : k = reg .io
    · subst h7; simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂, hR₁, hRd]
    simp only [hR₆, movedR, hR₅, hR₄, hR₃, hR₂, hR₁, hRd, Function.update_apply, h0, h1, h2, h3,
      h4, h5, h6, h7, ↓reduceIte]
    obtain ⟨x, rfl⟩ := (regEquiv SXReg).surjective k
    exact topDownR_of_ne (fun h => h1 (by rw [h]; rfl)) (fun h => h2 (by rw [h]; rfl))
      (fun h => h4 (by rw [h]; rfl)) (fun h => h3 (by rw [h]; rfl)) (fun h => h6 (by rw [h]; rfl))
      (fun h => h5 (by rw [h]; rfl))

/-! ### Padding and unpadding rows -/

/-- Pad to `R₂` rows (field `4`) from `R 2^a` rows (fields `3`, `2`): `io` moved onto `racc`,
`(R₂ - R 2^a) · |rowctr|` zero pairs pushed onto `io`, `racc` moved back. -/
noncomputable def topPadS : Pr P (nT SXReg) Q A U :=
  .seq (topRd (reg (.sc 0)) 2)
  (.seq (topRd (reg (.sc 1)) 3)
  (.seq (upow2 (reg (.sc 0)) (reg (.sc 1)) (reg (.sc 4)) (reg (.sc 5)))
  (.seq (topRd (reg (.sc 2)) 4)
  (.seq (usub (reg (.sc 1)) (reg (.sc 2)) (reg (.sc 3)))
  (.seq (moveR (reg .io) (reg .racc) id)
  (.seq (scanP (reg (.sc 2)) (reg (.sc 3))
      (umulSym 1 (pairSym A false false) (reg .rowctr) (reg .io) (reg (.sc 4))))
  (.seq (moveR (reg .racc) (reg .io) id)
  (.seq (uclear (reg (.sc 0))) (.seq (uclear (reg (.sc 1))) (uclear (reg (.sc 2))))))))))))

/-- The step bound of `topPadS` with `V` symbols on `io` and rows of `L` symbols. -/
def topPadCost (cfg : List ℕ) (a R R₂ L V : ℕ) : ℕ :=
  3 * topGetCost cfg + (4 * (2 ^ a * R) + 9 * a + 4) + (4 * (2 ^ a * R) + 4) + (2 * V + 2) +
    ((R₂ - 2 ^ a * R) * (4 * L + 7) + 2 * (R₂ - 2 ^ a * R) + 4) + (2 * V + 2) + (2 * a + 2) +
    (2 * (2 ^ a * R) + 2) + (2 * (R₂ - 2 ^ a * R) + 2)

theorem topPadS_exec {cfg : List ℕ} {n a R R₂ r w K ρ : ℕ} (h2 : cfg[2]? = some a)
    (h3 : cfg[3]? = some R) (h4 : cfg[4]? = some R₂) (v : HS (nT SXReg) Q A U)
    (S : Stacks (nT SXReg) A) (hT : TopRegs S.R n r w K ρ)
    (hcf : ∃ rest, S.R (reg .park) = topRec cfg ++ rest) :
    ∃ (v' : HS (nT SXReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ topPadCost cfg a R R₂ (2 ^ n * r * w) (S.R (reg .io)).length ∧
      Exec body topPadS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (S.R (reg .io) ++
            List.replicate ((R₂ - 2 ^ a * R) * (2 ^ n * r * w)) (pairSym A false false)) }) := by
  have hl2 : 2 < cfg.length := (List.getElem?_eq_some_iff.1 h2).1
  have hl3 : 3 < cfg.length := (List.getElem?_eq_some_iff.1 h3).1
  have hl4 : 4 < cfg.length := (List.getElem?_eq_some_iff.1 h4).1
  have hc2 : cfg[2] = a := (List.getElem?_eq_some_iff.1 h2).2
  have hc3 : cfg[3] = R := (List.getElem?_eq_some_iff.1 h3).2
  have hc4 : cfg[4] = R₂ := (List.getElem?_eq_some_iff.1 h4).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  have hracc : S.R (reg .racc) = [] := hT.rest .racc
  have hrow : (S.R (reg .rowctr)).length = 2 ^ n * r * w := hT.rest .rowctr
  set Xs := S.R (reg .io) with hXs
  set L := 2 ^ n * r * w with hL
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := topRd_exec body (x := .sc 0) (by simp) (by simp) 2 hl2 v S
    hlc hcf
  rw [hc2, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate a tick) with hR₁
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := topRd_exec body (x := .sc 1) (by simp) (by simp) 3 hl3 v₁
    { S with R := R₁ } (by simp [hR₁, hlc]) (by simpa [hR₁] using hcf)
  dsimp only at e₂
  rw [hc3, show R₁ (reg (.sc 1)) = [] by simp [hR₁, hsc], List.append_nil] at e₂
  set R₂' := Function.update R₁ (reg (.sc 1)) (List.replicate R tick) with hR₂'
  obtain ⟨v₃, m₃, hu₃, hm₃, e₃⟩ := upow2_exec body (a := reg (.sc 0)) (b := reg (.sc 1))
    (t₁ := reg (.sc 4)) (t₂ := reg (.sc 5)) (nodup_map_reg (l := [.sc 0, .sc 1, .sc 4, .sc 5])
      (by simp)) v₂ { S with R := R₂' } (by simp [hR₂', hR₁, hsc]) (by simp [hR₂', hR₁, hsc])
  dsimp only at e₃ hm₃
  rw [show R₂' (reg (.sc 0)) = List.replicate a tick by simp [hR₂', hR₁],
    show R₂' (reg (.sc 1)) = List.replicate R tick by simp [hR₂'], List.length_replicate] at e₃ hm₃
  set R₃ := Function.update R₂' (reg (.sc 1))
    ((List.replicate R tick).flatMap (List.replicate (2 ^ a))) with hR₃
  have h3l : (R₃ (reg (.sc 1))).length = 2 ^ a * R := by
    simp [hR₃]; ring
  obtain ⟨v₄, c₄, hu₄, hc₄, e₄⟩ := topRd_exec body (x := .sc 2) (by simp) (by simp) 4 hl4 v₃
    { S with R := R₃ } (by simp [hR₃, hR₂', hR₁, hlc]) (by simpa [hR₃, hR₂', hR₁] using hcf)
  dsimp only at e₄
  rw [hc4, show R₃ (reg (.sc 2)) = [] by simp [hR₃, hR₂', hR₁, hsc], List.append_nil] at e₄
  set R₄ := Function.update R₃ (reg (.sc 2)) (List.replicate R₂ tick) with hR₄
  obtain ⟨v₅, hu₅, e₅⟩ := usub_exec body (a := reg (.sc 1)) (b := reg (.sc 2)) (t := reg (.sc 3))
    (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) v₄ { S with R := R₄ }
    (by simp [hR₄, hR₃, hR₂', hR₁, hsc])
  dsimp only at e₅
  rw [show (R₄ (reg (.sc 1))).length = 2 ^ a * R by simp [hR₄, h3l],
    show R₄ (reg (.sc 2)) = List.replicate R₂ tick by simp [hR₄], List.drop_replicate] at e₅
  set M := R₂ - 2 ^ a * R with hM
  set R₅ := Function.update R₄ (reg (.sc 2)) (List.replicate M tick) with hR₅
  obtain ⟨v₆, hu₆, e₆⟩ := moveR_exec body (reg .io) (reg .racc) (reg_ne (by simp)) id v₅
    { S with R := R₅ }
  dsimp only at e₆
  rw [show R₅ (reg .io) = Xs by simp [hR₅, hR₄, hR₃, hR₂', hR₁, hXs]] at e₆
  set R₆ := movedR R₅ (reg .io) (reg .racc) id Xs with hR₆
  have hR₆row : (R₆ (reg .rowctr)).length = L := by
    simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂', hR₁, hrow, hL]
  -- the zero rows
  let Ψ : ℕ → Regs (nT SXReg) A := fun j =>
    Function.update R₆ (reg .io) (List.replicate (j * L) (pairSym A false false))
  have hp : IterSpec body (umulSym 1 (pairSym A false false) (reg .rowctr) (reg .io) (reg (.sc 4)))
      (reg (.sc 2)) (reg (.sc 3)) Ψ (fun _ => 4 * L + 4) M := by
    intro j _ v' S' hS'
    have hb : S'.R (reg .io) = List.replicate (j * L) (pairSym A false false) := by
      rw [hS' _ (reg_ne (by simp)) (reg_ne (by simp))]; simp [Ψ]
    have hrw : (S'.R (reg .rowctr)).length = L := by
      rw [hS' _ (reg_ne (by simp)) (reg_ne (by simp))]; simp [Ψ, hR₆row]
    obtain ⟨v'', hu'', he''⟩ := umulSym_exec body 1 (pairSym A false false)
      (a := reg .rowctr) (b := reg .io) (t := reg (.sc 4)) (reg_ne (by simp)) (reg_ne (by simp))
      (reg_ne (by simp)) v' S'
      (by rw [hS' _ (reg_ne (by simp)) (reg_ne (by simp))]
          simp [Ψ, hR₆, movedR, hR₅, hR₄, hR₃, hR₂', hR₁, hsc])
    refine ⟨v'', _, _, hu'', le_of_eq (by rw [hrw]), he'', by simp, by simp, ?_⟩
    intro k hka hkt
    by_cases hk : k = reg .io
    · subst hk; simp [Ψ, hb, hrw, List.replicate_append_replicate]; ring_nf
    · simp [Ψ, Function.update_of_ne hk, hS' k hka hkt]
  obtain ⟨v₇, R₇, m₇, hu₇, hm₇, e₇, h7a, h7t, h7o⟩ := scanP_exec body (reg_ne (by simp)) hp 0 v₆
    { S with R := R₆ } (by simp [hR₆, movedR, hR₅]) (fun k hka hkt => by
      by_cases hk : k = reg .io
      · subst hk; simp [Ψ, hR₆, movedR]
      · simp [Ψ, Function.update_of_ne hk])
  dsimp only at h7a h7t hm₇
  have h3e : R₆ (reg (.sc 3)) = [] := by simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂', hR₁, hsc]
  have h2e : R₆ (reg (.sc 2)) = List.replicate M tick := by simp [hR₆, movedR, hR₅]
  rw [h3e, h2e] at hm₇ h7a
  simp only [List.length_replicate, Finset.sum_const, Finset.card_range,
    smul_eq_mul, List.length_nil, List.reverse_nil, List.nil_append] at hm₇ h7a
  -- `racc` back onto `io`
  obtain ⟨v₈, hu₈, e₈⟩ := moveR_exec body (reg .racc) (reg .io) (reg_ne (by simp)) id v₇
    { S with R := R₇ }
  dsimp only at e₈
  have h7r : R₇ (reg .racc) = Xs.reverse := by
    rw [h7o _ (reg_ne (by simp)) (reg_ne (by simp))]
    simp [Ψ, hR₆, movedR, hR₅, hR₄, hR₃, hR₂', hR₁, hracc]
  have h7i : R₇ (reg .io) = List.replicate (M * L) (pairSym A false false) := by
    rw [h7o _ (reg_ne (by simp)) (reg_ne (by simp))]
    simp [Ψ, h2e]
  rw [h7r] at e₈
  set R₈ := movedR R₇ (reg .racc) (reg .io) id Xs.reverse with hR₈
  obtain ⟨v₉, hu₉, e₉⟩ := uclear_exec body (reg (.sc 0)) v₈ { S with R := R₈ }
  obtain ⟨v₁₀, hu₁₀, e₁₀⟩ := uclear_exec body (reg (.sc 1)) v₉
    { S with R := Function.update R₈ (reg (.sc 0)) [] }
  obtain ⟨v₁₁, hu₁₁, e₁₁⟩ := uclear_exec body (reg (.sc 2)) v₁₀
    { S with R := Function.update (Function.update R₈ (reg (.sc 0)) []) (reg (.sc 1)) [] }
  have hR₇o : ∀ k, k ≠ reg (.sc 2) → k ≠ reg (.sc 3) → k ≠ reg .io → R₇ k = R₆ k := by
    intro k h1 h2 h3
    rw [h7o k h1 h2]; simp [Ψ, Function.update_of_ne h3]
  refine ⟨v₁₁, _, by rw [hu₁₁, hu₁₀, hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ (Exec.seq e₈ (Exec.seq e₉ (Exec.seq e₁₀ e₁₁)))))))))) rfl ?_⟩
  · have hs0 : (R₈ (reg (.sc 0))).length = a := by
      simp only [hR₈, movedR]; topfupd
      rw [hR₇o _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))]
      simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂', hR₁]
    have hs1 : (R₈ (reg (.sc 1))).length = 2 ^ a * R := by
      simp only [hR₈, movedR]; topfupd
      rw [hR₇o _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))]
      simp [hR₆, movedR, hR₅, hR₄, h3l]
    have hs2 : (R₈ (reg (.sc 2))).length = M := by
      simp only [hR₈, movedR]; topfupd; rw [h7a]; simp
    have hrl : (R₇ (reg .racc)).length = Xs.length := by rw [h7r]; simp
    dsimp only
    simp only [Function.update_apply]
    topfupd
    try rw [hs0]
    try rw [hs1]
    try rw [hs2]
    simp only [List.length_reverse]
    simp only [List.length_replicate] at hm₃
    unfold topPadCost
    rw [← hM]
    linarith [hc₁, hc₂, hc₄, hm₃, hm₇]
  · congr 2
    funext k
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hsc]
    by_cases h2 : k = reg (.sc 2)
    · subst h2; simp [hsc]
    simp only [Function.update_apply, h0, h1, h2, ↓reduceIte, hR₈, movedR]
    by_cases h3 : k = reg .io
    · subst h3
      simp [h7i, List.map_id]
    by_cases h4 : k = reg .racc
    · subst h4; simp [h3, hracc]
    simp only [h3, h4, ↓reduceIte]
    by_cases h5 : k = reg (.sc 3)
    · subst h5; rw [h7t, hsc]
    rw [hR₇o k h2 h5 h3]
    simp [hR₆, movedR, hR₅, hR₄, hR₃, hR₂', hR₁, h0, h1, h2, h3, h4]

/-- Keep the first `R 2^a` rows (fields `3`, `2`): one counted copy of a row from `io` onto
`racc` per row, then `io` cleared and `racc` moved back. -/
noncomputable def topUnpadS : Pr P (nT SXReg) Q A U :=
  .seq (topRd (reg (.sc 0)) 2)
  (.seq (topRd (reg (.sc 1)) 3)
  (.seq (upow2 (reg (.sc 0)) (reg (.sc 1)) (reg (.sc 4)) (reg (.sc 5)))
  (.seq (scanP (reg (.sc 1)) (reg (.sc 3)) (Shift.counted (reg .rowctr) (reg .rowtmp)
      (Shift.copyStep (reg .rowctr) (reg .rowtmp) (reg .io) (reg .racc))))
  (.seq (uclear (reg .io))
  (.seq (moveR (reg .racc) (reg .io) id)
  (.seq (uclear (reg (.sc 0))) (uclear (reg (.sc 1)))))))))

/-- The step bound of `topUnpadS` with `V` symbols on `io` and rows of `L` symbols. -/
def topUnpadCost (cfg : List ℕ) (a R L V : ℕ) : ℕ :=
  2 * topGetCost cfg + (4 * (2 ^ a * R) + 9 * a + 4) +
    (2 ^ a * R * (4 * L + 7) + 2 * (2 ^ a * R) + 4) + (2 * V + 2) + (2 * V + 2) + (2 * a + 2) +
    (2 * (2 ^ a * R) + 2)

theorem topUnpadS_exec {cfg : List ℕ} {n a R r w K ρ : ℕ} (h2 : cfg[2]? = some a)
    (h3 : cfg[3]? = some R) (v : HS (nT SXReg) Q A U) (S : Stacks (nT SXReg) A)
    (hT : TopRegs S.R n r w K ρ) (hcf : ∃ rest, S.R (reg .park) = topRec cfg ++ rest)
    (hlen : 2 ^ a * R * (2 ^ n * r * w) ≤ (S.R (reg .io)).length) :
    ∃ (v' : HS (nT SXReg) Q A U) (c : ℕ), v'.user = v.user ∧
      c ≤ topUnpadCost cfg a R (2 ^ n * r * w) (S.R (reg .io)).length ∧
      Exec body topUnpadS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io)
            ((S.R (reg .io)).take (2 ^ a * R * (2 ^ n * r * w))) }) := by
  have hl2 : 2 < cfg.length := (List.getElem?_eq_some_iff.1 h2).1
  have hl3 : 3 < cfg.length := (List.getElem?_eq_some_iff.1 h3).1
  have hc2 : cfg[2] = a := (List.getElem?_eq_some_iff.1 h2).2
  have hc3 : cfg[3] = R := (List.getElem?_eq_some_iff.1 h3).2
  have hsc : ∀ i, S.R (reg (.sc i)) = [] := fun i => hT.rest (.sc i)
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  have hracc : S.R (reg .racc) = [] := hT.rest .racc
  have hrt : S.R (reg .rowtmp) = [] := hT.rest .rowtmp
  have hrow : (S.R (reg .rowctr)).length = 2 ^ n * r * w := hT.rest .rowctr
  set Xs := S.R (reg .io) with hXs
  set L := 2 ^ n * r * w with hL
  set N₁ := 2 ^ a * R with hN₁
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := topRd_exec body (x := .sc 0) (by simp) (by simp) 2 hl2 v S
    hlc hcf
  rw [hc2, hsc 0, List.append_nil] at e₁
  set R₁ := Function.update S.R (reg (.sc 0)) (List.replicate a tick) with hR₁
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := topRd_exec body (x := .sc 1) (by simp) (by simp) 3 hl3 v₁
    { S with R := R₁ } (by simp [hR₁, hlc]) (by simpa [hR₁] using hcf)
  dsimp only at e₂
  rw [hc3, show R₁ (reg (.sc 1)) = [] by simp [hR₁, hsc], List.append_nil] at e₂
  set R₂' := Function.update R₁ (reg (.sc 1)) (List.replicate R tick) with hR₂'
  obtain ⟨v₃, m₃, hu₃, hm₃, e₃⟩ := upow2_exec body (a := reg (.sc 0)) (b := reg (.sc 1))
    (t₁ := reg (.sc 4)) (t₂ := reg (.sc 5)) (nodup_map_reg (l := [.sc 0, .sc 1, .sc 4, .sc 5])
      (by simp)) v₂ { S with R := R₂' } (by simp [hR₂', hR₁, hsc]) (by simp [hR₂', hR₁, hsc])
  dsimp only at e₃ hm₃
  rw [show R₂' (reg (.sc 0)) = List.replicate a tick by simp [hR₂', hR₁],
    show R₂' (reg (.sc 1)) = List.replicate R tick by simp [hR₂'], List.length_replicate] at e₃ hm₃
  set R₃ := Function.update R₂' (reg (.sc 1))
    ((List.replicate R tick).flatMap (List.replicate (2 ^ a))) with hR₃
  have h3l : (R₃ (reg (.sc 1))).length = N₁ := by
    simp [hR₃, hN₁]; ring
  -- the rows kept
  let Ψ : ℕ → Regs (nT SXReg) A := fun j =>
    Function.update (Function.update R₃ (reg .io) (Xs.drop (j * L))) (reg .racc)
      (Xs.take (j * L)).reverse
  have hp : IterSpec body (Shift.counted (reg .rowctr) (reg .rowtmp)
      (Shift.copyStep (reg .rowctr) (reg .rowtmp) (reg .io) (reg .racc)))
      (reg (.sc 1)) (reg (.sc 3)) Ψ (fun _ => 4 * L + 4) N₁ := by
    intro j hj v' S' hS'
    have hjL : (j + 1) * L ≤ Xs.length := le_trans (Nat.mul_le_mul_right _ hj) hlen
    have hjL' : j * L + L ≤ Xs.length := by rw [← Nat.succ_mul]; exact hjL
    have hio' : S'.R (reg .io) = (Xs.drop (j * L)).take L ++ Xs.drop (j * L + L) := by
      rw [hS' _ (reg_ne (by simp)) (reg_ne (by simp))]
      simp [Ψ, Nat.add_comm]
    obtain ⟨v'', hv'', he''⟩ := topCopyC_exec body (c := reg .rowctr) (t := reg .rowtmp)
      (src := reg .io) (dst := reg .racc)
      (nodup_map_reg (l := [.rowctr, .rowtmp, .io, .racc]) (by simp))
      ((Xs.drop (j * L)).take L) (Xs.drop (j * L + L)) v' S'
      (by rw [hS' _ (reg_ne (by simp)) (reg_ne (by simp))]
          simp [Ψ, hR₃, hR₂', hR₁, hrow]
          omega) hio'
      (by rw [hS' _ (reg_ne (by simp)) (reg_ne (by simp))]; simp [Ψ, hR₃, hR₂', hR₁, hrt])
    have hyl : ((Xs.drop (j * L)).take L).length = L := by simp; omega
    rw [hyl] at he''
    refine ⟨v'', _, _, hv''.user, le_refl _, he'', by simp, by simp, ?_⟩
    intro k hka hkt
    by_cases hk1 : k = reg .io
    · subst hk1; simp [Ψ, Nat.succ_mul]
    by_cases hk2 : k = reg .racc
    · subst hk2
      rw [Function.update_self, hS' _ hka hkt]
      simp [Ψ, Nat.succ_mul, List.take_add]
    simp [Ψ, Function.update_of_ne hk1, Function.update_of_ne hk2, hS' k hka hkt]
  obtain ⟨v₄, R₄, m₄, hu₄, hm₄, e₄, h4a, h4t, h4o⟩ := scanP_exec body (reg_ne (by simp)) hp 0 v₃
    { S with R := R₃ } (by simp [h3l]) (fun k hka hkt => by
      by_cases hk1 : k = reg .io
      · subst hk1; simp [Ψ, hR₃, hR₂', hR₁, hXs]
      by_cases hk2 : k = reg .racc
      · subst hk2; simp [Ψ, hR₃, hR₂', hR₁, hracc]
      simp [Ψ, Function.update_of_ne hk1, Function.update_of_ne hk2])
  dsimp only at h4a h4t hm₄
  have h3e : R₃ (reg (.sc 3)) = [] := by simp [hR₃, hR₂', hR₁, hsc]
  rw [h3e, h3l] at hm₄
  rw [h3e] at h4a
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_nil,
    List.reverse_nil, List.nil_append] at hm₄ h4a
  have h4i : R₄ (reg .io) = Xs.drop (N₁ * L) := by
    rw [h4o _ (reg_ne (by simp)) (reg_ne (by simp)), h3l]; simp [Ψ]
  have h4r : R₄ (reg .racc) = (Xs.take (N₁ * L)).reverse := by
    rw [h4o _ (reg_ne (by simp)) (reg_ne (by simp)), h3l]; simp [Ψ]
  obtain ⟨v₅, hu₅, e₅⟩ := uclear_exec body (reg .io) v₄ { S with R := R₄ }
  dsimp only at e₅
  rw [h4i] at e₅
  obtain ⟨v₆, hu₆, e₆⟩ := moveR_exec body (reg .racc) (reg .io) (reg_ne (by simp)) id v₅
    { S with R := Function.update R₄ (reg .io) [] }
  dsimp only at e₆
  rw [show Function.update R₄ (reg .io) [] (reg .racc) = (Xs.take (N₁ * L)).reverse by
    rw [Function.update_of_ne (reg_ne (by simp)), h4r]] at e₆
  set R₆ := movedR (Function.update R₄ (reg .io) []) (reg .racc) (reg .io) id
    (Xs.take (N₁ * L)).reverse with hR₆
  obtain ⟨v₇, hu₇, e₇⟩ := uclear_exec body (reg (.sc 0)) v₆ { S with R := R₆ }
  obtain ⟨v₈, hu₈, e₈⟩ := uclear_exec body (reg (.sc 1)) v₇
    { S with R := Function.update R₆ (reg (.sc 0)) [] }
  have hR₄o : ∀ k, k ≠ reg (.sc 1) → k ≠ reg (.sc 3) → k ≠ reg .io → k ≠ reg .racc →
      R₄ k = R₃ k := by
    intro k h1 h2 h3 h4
    rw [h4o k h1 h2]; simp [Ψ, Function.update_of_ne h3, Function.update_of_ne h4]
  refine ⟨v₈, _, by rw [hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ e₈))))))) rfl ?_⟩
  · have hs0 : (R₆ (reg (.sc 0))).length = a := by
      simp only [hR₆, movedR]; topfupd
      rw [hR₄o _ (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp)) (reg_ne (by simp))]
      simp [hR₃, hR₂', hR₁]
    have hs1 : (Function.update R₆ (reg (.sc 0)) [] (reg (.sc 1))).length = N₁ := by
      simp only [hR₆, movedR]; topfupd; rw [h4a, h3l]
    rw [hs0, hs1]
    simp only [List.length_reverse, List.length_take, List.length_drop]
    simp only [List.length_replicate] at hm₃
    have hmin : min (N₁ * L) Xs.length = N₁ * L := by
      apply min_eq_left; rw [hN₁]; nlinarith [hlen]
    rw [hmin]
    unfold topUnpadCost
    rw [← hN₁]
    have : Xs.length - N₁ * L ≤ Xs.length := Nat.sub_le _ _
    nlinarith [hc₁, hc₂, hm₃, hm₄]
  · congr 2
    funext k
    by_cases h0 : k = reg (.sc 0)
    · subst h0; simp [hsc]
    by_cases h1 : k = reg (.sc 1)
    · subst h1; simp [hsc]
    simp only [Function.update_apply, h0, h1, ↓reduceIte, hR₆, movedR]
    by_cases h3 : k = reg .io
    · subst h3; simp
    by_cases h4 : k = reg .racc
    · subst h4; simp [h3, hracc]
    simp only [h3, h4, ↓reduceIte]
    by_cases h5 : k = reg (.sc 3)
    · subst h5; rw [h4t, hsc]
    rw [hR₄o k h1 h5 h3 h4]
    simp [hR₃, hR₂', hR₁, h0, h1]

end Down

/-! ### The pieces -/

lemma TopRegs.update_store {A : ℕ} {Rg : Fin (nT SXReg) → List (Fin (A + 4))} {N r w K ρ : ℕ}
    (h : TopRegs Rg N r w K ρ) {x : LReg SXReg}
    (hx : x = .io ∨ x = .ph .arr ∨ x = .lf (.k .arr)) (l : List (Fin (A + 4))) :
    TopRegs (Function.update Rg (reg x) l) N r w K ρ := by
  have hne : ∀ y : LReg SXReg, y ∈ parRegs (BReg := SXReg) → reg y ≠ reg x := by
    intro y hy
    apply reg_ne
    simp only [parRegs, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hx with rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  exact {
    rest := fun y => by
      by_cases hy : y = x
      · subst hy
        rcases hx with rfl | rfl | rfl <;> trivial
      · rw [Function.update_of_ne (reg_ne hy)]; exact h.rest y
    hlev := by rw [Function.update_of_ne (hne .lev (by simp [parRegs]))]; exact h.hlev
    hu := by rw [Function.update_of_ne (hne .u (by simp [parRegs]))]; exact h.hu
    ha₀ := by rw [Function.update_of_ne (hne .a₀ (by simp [parRegs]))]; exact h.ha₀
    hL := by rw [Function.update_of_ne (hne .L (by simp [parRegs]))]; exact h.hL
    hrows := by rw [Function.update_of_ne (hne .rows (by simp [parRegs]))]; exact h.hrows
    hn := by rw [Function.update_of_ne (hne .n (by simp [parRegs]))]; exact h.hn
    hw := by rw [Function.update_of_ne (hne .w (by simp [parRegs]))]; exact h.hw
    hrw := by rw [Function.update_of_ne (hne .rw (by simp [parRegs]))]; exact h.hrw
    hK := by rw [Function.update_of_ne (hne .K (by simp [parRegs]))]; exact h.hK
    hρ := by rw [Function.update_of_ne (hne .ρ (by simp [parRegs]))]; exact h.hρ }

section PieceLoop

lemma topEnc_cast {A w R R' r n : ℕ} (h : R = R') (W : ZArr (Fin R' × Fin r) n) :
    encZ A w (fun p : (Fin R × Fin r) × (Fin n → ZMod 2) => W ((Fin.cast h p.1.1, p.1.2), p.2)) =
      encZ A w W := by
  subst h; rfl



variable {Q Ka : ℕ} {U : Type}

/-- One piece: its fields `j`, `u`, `a₀`, `L` from `ph .arr` onto `lev`, `u`, `a₀`, `L` (the
fields kept on `lf (.k .arr)`), `rows := R₂` (field `4`), the call, and `flag` for the next
piece. -/
noncomputable def topPcBody : Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq (topField (reg (.ph .arr)) (reg (.lf (.k .arr))) (reg .lev) true)
  (.seq (topField (reg (.ph .arr)) (reg (.lf (.k .arr))) (reg .u) true)
  (.seq (topField (reg (.ph .arr)) (reg (.lf (.k .arr))) (reg .a₀) true)
  (.seq (topField (reg (.ph .arr)) (reg (.lf (.k .arr))) (reg .L) true)
  (.seq (topRd (reg .rows) 4)
  (.seq topCallClr (.act (peekR (reg (.ph .arr)))))))))

/-- The step bound of one piece. -/
noncomputable def topPcCost (ds : ComplexFramedExecution.Directions) (cfg : List ℕ)
    (K ρ n r w : ℕ) (pc : TopPc) : ℕ :=
  (2 * pc.j + 3) + (2 * pc.u + 3) + (2 * pc.a₀ + 3) + (2 * (K * bits pc.u pc.j) + 3) +
    topGetCost cfg + (layerCost (nT SXReg) ds pc.u K ρ pc.R₀ n r w pc.j pc.a₀ +
      (2 * pc.j + 2 * pc.u + 2 * pc.a₀ + 2 * (K * bits pc.u pc.j) + 2 * rowsAt pc.R₀ pc.j + 10)) +
    1

/-- The step bound of the loop over the pieces. -/
noncomputable def topPcsCost (ds : ComplexFramedExecution.Directions) (cfg : List ℕ)
    (K ρ n r w : ℕ) : List TopPc → ℕ
  | [] => 1
  | pc :: pcs => topPcCost ds cfg K ρ n r w pc + 1 + topPcsCost ds cfg K ρ n r w pcs

theorem topPcBody_exec (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime + Ka)
    (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
    {cfg : List ℕ} {n r w K ρ R₂ : ℕ} (h4 : cfg[4]? = some R₂) (hr : 1 ≤ r) (hw : 1 ≤ w)
    (hρ : ρ < K) (pc : TopPc) (hok : pc.Ok ds K n w R₂) (restPL : List (Fin (prime + Ka + 4)))
    (Y : ZArr (Fin R₂ × Fin r) n) (v : HS (nT SXReg) Q (prime + Ka) U)
    (S : Stacks (nT SXReg) (prime + Ka)) (hL : ∀ y, S.L y = []) (hT : TopRegs S.R n r w K ρ)
    (hcf : ∃ rest, S.R (reg .park) = topRec cfg ++ rest)
    (hPL : S.R (reg (.ph .arr)) = topRec (topPcFields K pc) ++ restPL)
    (hio : S.R (reg .io) = encZ (prime + Ka) w Y) :
    ∃ (v' : HS (nT SXReg) Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      v'.flag = restPL.head?.isSome ∧ c ≤ topPcCost ds cfg K ρ n r w pc ∧
      Exec (layerTable hQ ds) topPcBody (mk v S) c
        (mk v' { S with
          R := Function.update (Function.update (Function.update S.R (reg .io)
            (encZ (prime + Ka) w (pieceZ (pc.piece hρ hok).u ds (pc.piece hρ hok).R₀
              (pc.piece hρ hok).j (pc.piece hρ hok).hR (pc.piece hρ hok).e Y))) (reg (.ph .arr))
              restPL) (reg (.lf (.k .arr)))
            ((topRec (topPcFields K pc)).reverse ++ S.R (reg (.lf (.k .arr)))) }) := by
  set body := layerTable (Ka := Ka) (U := U) hQ ds
  have hl4 : 4 < cfg.length := (List.getElem?_eq_some_iff.1 h4).1
  have hc4 : cfg[4] = R₂ := (List.getElem?_eq_some_iff.1 h4).2
  have hlc : S.R (reg .lenctr) = [] := hT.rest .lenctr
  set PL : Fin (nT SXReg) := reg (.ph .arr) with hPLd
  set PB : Fin (nT SXReg) := reg (.lf (.k .arr)) with hPBd
  set Lv := K * bits pc.u pc.j with hLv
  have hd : ∀ x : LReg SXReg, x ∈ [LReg.lev, .u, .a₀, .L] →
      PL ≠ reg x ∧ PB ≠ reg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact ⟨reg_ne (by simp), reg_ne (by simp)⟩
  have hPB : PL ≠ PB := reg_ne (by simp)
  -- the four fields
  have hPL₀ : S.R PL =
      List.replicate pc.j tick ++ topSep :: (topRec [pc.u, pc.a₀, Lv] ++ restPL) := by
    rw [hPL]; simp [topPcFields, topRec_cons, hLv]
  obtain ⟨v₁, hu₁, e₁⟩ := topField_exec body hPB (hd .lev (by simp)).1 (hd .lev (by simp)).2 true
    pc.j _ v S hPL₀
  simp only [ite_true, hT.hlev, List.append_nil] at e₁
  set F₁ := Function.update (Function.update (Function.update S.R PL
    (topRec [pc.u, pc.a₀, Lv] ++ restPL)) PB (topSep :: List.replicate pc.j tick ++ S.R PB))
    (reg .lev) (List.replicate pc.j tick) with hF₁
  obtain ⟨v₂, hu₂, e₂⟩ := topField_exec body hPB (hd .u (by simp)).1 (hd .u (by simp)).2 true
    pc.u (topRec [pc.a₀, Lv] ++ restPL) v₁ { S with R := F₁ }
    (by simp [hF₁, (hd .lev (by simp)).1, topRec_cons, hPB])
  simp only [ite_true] at e₂
  try dsimp only at e₂
  set F₂ := Function.update (Function.update (Function.update F₁ PL
    (topRec [pc.a₀, Lv] ++ restPL)) PB (topSep :: List.replicate pc.u tick ++ F₁ PB))
    (reg .u) (List.replicate pc.u tick ++ F₁ (reg .u)) with hF₂
  obtain ⟨v₃, hu₃, e₃⟩ := topField_exec body hPB (hd .a₀ (by simp)).1 (hd .a₀ (by simp)).2 true
    pc.a₀ (topRec [Lv] ++ restPL) v₂ { S with R := F₂ }
    (by simp [hF₂, (hd .u (by simp)).1, topRec_cons, hPB])
  simp only [ite_true] at e₃
  try dsimp only at e₃
  set F₃ := Function.update (Function.update (Function.update F₂ PL
    (topRec [Lv] ++ restPL)) PB (topSep :: List.replicate pc.a₀ tick ++ F₂ PB))
    (reg .a₀) (List.replicate pc.a₀ tick ++ F₂ (reg .a₀)) with hF₃
  obtain ⟨v₄, hu₄, e₄⟩ := topField_exec body hPB (hd .L (by simp)).1 (hd .L (by simp)).2 true
    Lv restPL v₃ { S with R := F₃ }
    (by simp [hF₃, (hd .a₀ (by simp)).1, topRec_cons, hPB])
  simp only [ite_true] at e₄
  try dsimp only at e₄
  set F₄ := Function.update (Function.update (Function.update F₃ PL restPL) PB
    (topSep :: List.replicate Lv tick ++ F₃ PB))
    (reg .L) (List.replicate Lv tick ++ F₃ (reg .L)) with hF₄
  have hF₄o : ∀ x : LReg SXReg, x ≠ .lev → x ≠ .u → x ≠ .a₀ → x ≠ .L → x ≠ .ph .arr →
      x ≠ .lf (.k .arr) → F₄ (reg x) = S.R (reg x) := by
    intro x h1 h2 h3 h4 h5 h6
    simp [hF₄, hF₃, hF₂, hF₁, hPLd, hPBd, h1, h2, h3, h4, h5, h6]
  -- `rows := F₂`
  obtain ⟨v₅, c₅, hu₅, hc₅, e₅⟩ := topRd_exec body (x := .rows) (by simp) (by simp) 4 hl4 v₄
    { S with R := F₄ }
    ((hF₄o .lenctr (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans hlc)
    (by obtain ⟨rest, h⟩ := hcf
        exact ⟨rest, (hF₄o .park (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp)).trans h⟩)
  try dsimp only at e₅
  rw [hc4, hF₄o _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), hT.hrows,
    List.append_nil] at e₅
  set F₅ := Function.update F₄ (reg .rows) (List.replicate R₂ tick) with hF₅
  -- the call
  set Z : ZArr (Fin (rowsAt pc.R₀ pc.j) × Fin r) n :=
    fun q => Y ((Fin.cast hok.hR.symm q.1.1, q.1.2), q.2) with hZ
  have hF₅o : ∀ x : LReg SXReg, x ≠ .lev → x ≠ .u → x ≠ .a₀ → x ≠ .L → x ≠ .rows →
      x ≠ .ph .arr → x ≠ .lf (.k .arr) → F₅ (reg x) = S.R (reg x) := by
    intro x h1 h2 h3 h4 h5 h6 h7
    rw [hF₅, Function.update_of_ne (reg_ne h5), hF₄o x h1 h2 h3 h4 h6 h7]
  have hpar : ParState F₅ pc.j pc.u K ρ pc.a₀ (K * bits pc.u pc.j) (rowsAt pc.R₀ pc.j) n w
      (r * w) := by
    have hh : ∀ x : LReg SXReg, x ∈ [LReg.K, .ρ, .n, .w, .rw] → F₅ (reg x) = S.R (reg x) := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        exact hF₅o _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    refine topParState ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [hF₅, hF₄, hF₃, hF₂, hF₁, hPLd, hPBd]
    · simp [hF₅, hF₄, hF₃, hF₂, hPLd, hPBd, hF₁, hT.hu]
    · rw [hh _ (by simp)]; exact hT.hK
    · rw [hh _ (by simp)]; exact hT.hρ
    · simp [hF₅, hF₄, hF₃, hPLd, hPBd, hF₂, hF₁, hT.ha₀]
    · simp [hF₅, hF₄, hPLd, hPBd, hF₃, hF₂, hF₁, hT.hL, hLv]
    · simp [hF₅, ← hok.hR]
    · rw [hh _ (by simp)]; exact hT.hn
    · rw [hh _ (by simp)]; exact hT.hw
    · rw [hh _ (by simp)]; exact hT.hrw
  have hrest₅ : Rest bcEmpty n r w F₅ := by
    intro x
    by_cases hx : x ∈ parRegs (BReg := SXReg)
    · exact topRestSpec_par hx _
    by_cases h6 : x = .ph .arr
    · subst h6; trivial
    by_cases h7 : x = .lf (.k .arr)
    · subst h7; trivial
    rw [hF₅o x (fun h => hx (by simp [h, parRegs])) (fun h => hx (by simp [h, parRegs]))
      (fun h => hx (by simp [h, parRegs])) (fun h => hx (by simp [h, parRegs]))
      (fun h => hx (by simp [h, parRegs])) h6 h7]
    exact hT.rest x
  obtain ⟨v₆, c₆, hu₆, hc₆, e₆⟩ := topCallClr_exec hQ ds hA hA9 hNW hgate hr hw hρ hok.hu
    hok.hR₀ hok.hTw (topFit hρ hok.hfit) hok.hfit Z v₅ { S with R := F₅ } hL hpar hrest₅
    ((hF₅o .io (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).trans
      (hio.trans (topEnc_cast hok.hR.symm Y).symm))
  set X := encZ (prime + Ka) w (pieceZ (pc.piece hρ hok).u ds (pc.piece hρ hok).R₀
    (pc.piece hρ hok).j (pc.piece hρ hok).hR (pc.piece hρ hok).e Y) with hX
  have hX' : encZ (prime + Ka) w (layerZ pc.u ds pc.R₀ pc.j
      (actMap pc.a₀ ρ K (bits pc.u pc.j) n (topFit hρ hok.hfit)) Z) = X := by
    rw [hX]; exact (topEnc_cast hok.hR _).symm
  rw [hX'] at e₆
  set F₆ := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update F₅ (reg .io) X) (reg .lev) []) (reg .u) []) (reg .a₀) []) (reg .L) [])
    (reg .rows) [] with hF₆
  have e₇ := Exec.act (body := body) (peekR PL : Act _ _ _ _) (mk v₆ { S with R := F₆ })
  rw [peekR_run] at e₇
  have hF₆PL : F₆ PL = restPL := by simp [hF₆, hF₅, hF₄, hPLd, hPBd]
  refine ⟨{ v₆ with flag := (F₆ PL).head?.isSome }, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁],
    by rw [hF₆PL], ?_, Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅
      (Exec.seq e₆ (Exec.cast e₇ rfl ?_))))))⟩
  · have e1 : (F₁ (reg .u)).length = 0 := by simp [hF₁, hPLd, hPBd, hT.hu]
    have e2 : (F₂ (reg .a₀)).length = 0 := by simp [hF₂, hF₁, hPLd, hPBd, hT.ha₀]
    have e3 : (F₃ (reg .L)).length = 0 := by simp [hF₃, hF₂, hF₁, hPLd, hPBd, hT.hL]
    unfold topPcCost
    rw [← hLv]
    rw [← hLv] at hc₆
    omega
  · congr 2
    funext k
    by_cases h1 : k = PB
    · subst h1
      simp [hF₆, hF₅, hF₄, hF₃, hF₂, hF₁, hPLd, hPBd, topPcFields, topRec, hLv]
    by_cases h2 : k = PL
    · subst h2; simp [hF₆, hF₅, hF₄, hPLd, hPBd]
    by_cases h3 : k = reg .io
    · subst h3; simp [hF₆, hPLd, hPBd]
    by_cases h4 : k = reg .lev
    · subst h4; simp [hF₆, hPLd, hPBd, hT.hlev]
    by_cases h5 : k = reg .u
    · subst h5; simp [hF₆, hPLd, hPBd, hT.hu]
    by_cases h6 : k = reg .a₀
    · subst h6; simp [hF₆, hPLd, hPBd, hT.ha₀]
    by_cases h7 : k = reg .L
    · subst h7; simp [hF₆, hPLd, hPBd, hT.hL]
    by_cases h8 : k = reg .rows
    · subst h8; simp [hF₆, hPLd, hPBd, hT.hrows]
    simp only [hF₆, Function.update_apply, h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte]
    obtain ⟨x, rfl⟩ := (regEquiv SXReg).surjective k
    exact hF₅o x (fun h => h4 (by rw [h]; rfl)) (fun h => h5 (by rw [h]; rfl))
      (fun h => h6 (by rw [h]; rfl)) (fun h => h7 (by rw [h]; rfl)) (fun h => h8 (by rw [h]; rfl))
      (fun h => h2 (by rw [h]; rfl)) (fun h => h1 (by rw [h]; rfl))

theorem topPcLoop_loop (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime + Ka)
    (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
    {cfg : List ℕ} {n r w K ρ R₂ : ℕ} (h4 : cfg[4]? = some R₂) (hr : 1 ≤ r) (hw : 1 ≤ w)
    (hρ : ρ < K) :
    ∀ (pcs : List TopPc) (hpcs : ∀ pc ∈ pcs, pc.Ok ds K n w R₂) (Y : ZArr (Fin R₂ × Fin r) n)
      (v : HS (nT SXReg) Q (prime + Ka) U) (S : Stacks (nT SXReg) (prime + Ka)),
      (∀ y, S.L y = []) → TopRegs S.R n r w K ρ →
      (∃ rest, S.R (reg .park) = topRec cfg ++ rest) →
      S.R (reg (.ph .arr)) = topRec (topPcRec K pcs) →
      v.flag = (S.R (reg (.ph .arr))).head?.isSome →
      S.R (reg .io) = encZ (prime + Ka) w Y →
      ∃ (v' : HS (nT SXReg) Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
        c ≤ topPcsCost ds cfg K ρ n r w pcs ∧
        Exec (layerTable hQ ds) (.loop (·.flag) topPcBody) (mk v S) c
          (mk v' { S with
            R := Function.update (Function.update (Function.update S.R (reg .io)
              (encZ (prime + Ka) w (piecesZ ds (topPieces hρ pcs hpcs) Y))) (reg (.ph .arr)) [])
              (reg (.lf (.k .arr)))
              ((topRec (topPcRec K pcs)).reverse ++ S.R (reg (.lf (.k .arr)))) })
  | [], hpcs, Y, v, S, hL, hT, hcf, hPL, hf, hio => by
      refine ⟨v, 1, rfl, le_refl _, ?_⟩
      have hS : ({ S with
          R := Function.update (Function.update (Function.update S.R (reg .io)
            (encZ (prime + Ka) w (piecesZ ds (topPieces hρ [] hpcs) Y))) (reg (.ph .arr)) [])
            (reg (.lf (.k .arr)))
            ((topRec (topPcRec K [])).reverse ++ S.R (reg (.lf (.k .arr)))) } :
            Stacks (nT SXReg) (prime + Ka)) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hio hPL ⊢
          congr 1
          funext k
          simp only [Function.update_apply]
          split_ifs with h1 h2 h3
          · subst h1; simp [topPcRec]
          · subst h2; rw [hPL]; simp [topPcRec]
          · subst h3; rw [hio]; rfl
          · rfl
      rw [hS]
      exact .loop_false (by show v.flag = false; rw [hf, hPL]; simp [topPcRec])
  | pc :: pcs, hpcs, Y, v, S, hL, hT, hcf, hPL, hf, hio => by
      have hok := hpcs pc List.mem_cons_self
      have hPL' : S.R (reg (.ph .arr)) = topRec (topPcFields K pc) ++ topRec (topPcRec K pcs) := by
        rw [hPL, topPcRec, List.flatMap_cons, topRec_append]; rfl
      obtain ⟨v₁, c₁, hu₁, hf₁, hc₁, e₁⟩ := topPcBody_exec hQ ds hA hA9 hNW hgate h4 hr hw hρ pc
        hok (topRec (topPcRec K pcs)) Y v S hL hT hcf hPL' hio
      set P := pc.piece hρ hok
      set Y' := pieceZ P.u ds P.R₀ P.j P.hR P.e Y with hY'
      set S₁ : Stacks (nT SXReg) (prime + Ka) := { S with
        R := Function.update (Function.update (Function.update S.R (reg .io)
          (encZ (prime + Ka) w Y')) (reg (.ph .arr)) (topRec (topPcRec K pcs)))
          (reg (.lf (.k .arr)))
          ((topRec (topPcFields K pc)).reverse ++ S.R (reg (.lf (.k .arr)))) } with hS₁
      have hT₁ : TopRegs S₁.R n r w K ρ :=
        ((hT.update_store (Or.inl rfl) _).update_store (Or.inr (Or.inl rfl)) _).update_store
          (Or.inr (Or.inr rfl)) _
      obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := topPcLoop_loop hQ ds hA hA9 hNW hgate h4 hr hw hρ pcs
        (fun q hq => hpcs q (List.mem_cons_of_mem _ hq)) Y' v₁ S₁ hL hT₁
        (by simpa [hS₁] using hcf) (by simp [hS₁]) (by rw [hf₁]; simp [hS₁])
        (by simp [hS₁])
      have hne : (S.R (reg (.ph .arr))).head?.isSome = true := by
        rw [hPL']; simp [topPcFields, topRec]
      refine ⟨v₂, c₁ + c₂ + 1, hu₂.trans hu₁, by simp only [topPcsCost]; omega,
        Exec.cast (Exec.loop_true (by show v.flag = true; rw [hf]; exact hne) e₁ e₂) rfl ?_⟩
      congr 2
      funext k
      simp only [hS₁, Function.update_apply]
      split_ifs <;> simp_all [topPcRec, topRec_append, List.reverse_append, piecesZ, topPieces]
      rfl

/-- The pieces: run the piece record of `ph .arr` through `topPcBody`, keeping the consumed
fields on the empty `lf (.k .arr)`, and move them back. -/
noncomputable def topPcLoop : Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq (.act (peekR (reg (.ph .arr))))
    (.seq (.loop (·.flag) topPcBody) (moveR (reg (.lf (.k .arr))) (reg (.ph .arr)) id))

theorem topPcLoop_exec (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime + Ka)
    (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
    {cfg : List ℕ} {n r w K ρ R₂ : ℕ} (h4 : cfg[4]? = some R₂) (hr : 1 ≤ r) (hw : 1 ≤ w)
    (hρ : ρ < K) (pcs : List TopPc) (hpcs : ∀ pc ∈ pcs, pc.Ok ds K n w R₂)
    (Y : ZArr (Fin R₂ × Fin r) n) (v : HS (nT SXReg) Q (prime + Ka) U)
    (S : Stacks (nT SXReg) (prime + Ka)) (hL : ∀ y, S.L y = []) (hT : TopRegs S.R n r w K ρ)
    (hcf : ∃ rest, S.R (reg .park) = topRec cfg ++ rest)
    (hPL : S.R (reg (.ph .arr)) = topRec (topPcRec K pcs)) (hPB : S.R (reg (.lf (.k .arr))) = [])
    (hio : S.R (reg .io) = encZ (prime + Ka) w Y) :
    ∃ (v' : HS (nT SXReg) Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      c ≤ topPcsCost ds cfg K ρ n r w pcs + 1 + (2 * topRecLen (topPcRec K pcs) + 2) ∧
      Exec (layerTable hQ ds) topPcLoop (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io)
            (encZ (prime + Ka) w (piecesZ ds (topPieces hρ pcs hpcs) Y)) }) := by
  set body := layerTable (Ka := Ka) (U := U) hQ ds
  have e₀ := Exec.act (body := body) (peekR (reg (.ph .arr)) : Act _ _ _ _) (mk v S)
  rw [peekR_run] at e₀
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := topPcLoop_loop hQ ds hA hA9 hNW hgate h4 hr hw hρ pcs hpcs Y
    { v with flag := (S.R (reg (.ph .arr))).head?.isSome } S hL hT hcf hPL rfl hio
  set R₁ := Function.update (Function.update (Function.update S.R (reg .io)
    (encZ (prime + Ka) w (piecesZ ds (topPieces hρ pcs hpcs) Y))) (reg (.ph .arr)) [])
    (reg (.lf (.k .arr))) ((topRec (topPcRec K pcs)).reverse ++ S.R (reg (.lf (.k .arr))))
    with hR₁
  obtain ⟨v₂, hu₂, e₂⟩ := moveR_exec body (reg (.lf (.k .arr))) (reg (.ph .arr))
    (reg_ne (by simp)) id v₁ { S with R := R₁ }
  refine ⟨v₂, _, by rw [hu₂, hu₁], ?_, Exec.cast (Exec.seq e₀ (Exec.seq e₁ e₂)) rfl ?_⟩
  · dsimp only
    simp only [hR₁, Function.update_self, hPB, List.append_nil, List.length_reverse,
      length_topRec']
    omega
  · congr 2
    funext k
    simp only [movedR, hR₁, Function.update_apply]
    split_ifs <;> simp_all

/-- The pieces on the array with the top bits as rows: the rest state for `n` address bits,
padding, the pieces, unpadding, and the rest state for `n + a` address bits again. -/
noncomputable def topBlockS : Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq topDownS (.seq topPadS (.seq topPcLoop (.seq topUnpadS topUpS)))

/-- The step bound of `topBlockS`. -/
noncomputable def topBlockCost (ds : ComplexFramedExecution.Directions) (cfg : List ℕ)
    (K ρ n a r w R R₂ : ℕ) (pcs : List TopPc) : ℕ :=
  topDownCost cfg n a r w + topPadCost cfg a R R₂ (2 ^ n * r * w) (R * 2 ^ a * 2 ^ n * r * w) +
    (topPcsCost ds cfg K ρ n r w pcs + 1 + (2 * topRecLen (topPcRec K pcs) + 2)) +
    topUnpadCost cfg a R (2 ^ n * r * w) (R₂ * 2 ^ n * r * w) + topUpCost cfg n a r w

theorem topBlockS_exec (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime + Ka)
    (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
    {cfg : List ℕ} {n a R R₂ r w K ρ : ℕ} (h2 : cfg[2]? = some a) (h3 : cfg[3]? = some R)
    (h4 : cfg[4]? = some R₂) (hr : 1 ≤ r) (hw : 1 ≤ w) (hρ : ρ < K) (hR₂ : R * 2 ^ a ≤ R₂)
    (pcs : List TopPc) (hpcs : ∀ pc ∈ pcs, pc.Ok ds K n w R₂)
    (Y : ZArr (Fin (R * 2 ^ a) × Fin r) n) (v : HS (nT SXReg) Q (prime + Ka) U)
    (S : Stacks (nT SXReg) (prime + Ka)) (hL : ∀ y, S.L y = [])
    (hT : TopRegs S.R (n + a) r w K ρ) (hI : TopIn S.R cfg (topPcRec K pcs))
    (hio : S.R (reg .io) = encZ (prime + Ka) w Y) :
    ∃ (v' : HS (nT SXReg) Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      c ≤ topBlockCost ds cfg K ρ n a r w R R₂ pcs ∧
      Exec (layerTable hQ ds) topBlockS (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ (prime + Ka) w
            (unpadRows hR₂ (piecesZ ds (topPieces hρ pcs hpcs) (padRows R₂ Y)))) }) := by
  set body := layerTable (Ka := Ka) (U := U) hQ ds
  -- down
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := topDownS_exec body h2 v S hT hI
  set Rd := topDownR S.R a n r w with hRd
  have hTd : TopRegs Rd n r w K ρ := topDownR_regs hT
  have hcfd : ∃ rest, Rd (reg .park) = topRec cfg ++ rest := by
    rw [hRd, topDownR_of_ne (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact hI.cf
  have hiod : Rd (reg .io) = encZ (prime + Ka) w Y := by
    rw [hRd, topDownR_of_ne (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact hio
  -- pad
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := topPadS_exec body h2 h3 h4 v₁ { S with R := Rd } hTd hcfd
  dsimp only at e₂ hc₂
  have hpad : Rd (reg .io) ++ List.replicate ((R₂ - 2 ^ a * R) * (2 ^ n * r * w))
      (pairSym (prime + Ka) false false) = encZ (prime + Ka) w (padRows R₂ Y) := by
    rw [hiod, topEnc_padRows hR₂]
    congr 2
    rw [Nat.mul_comm (2 ^ a) R]; ring
  rw [hpad] at e₂
  -- the pieces
  obtain ⟨v₃, c₃, hu₃, hc₃, e₃⟩ := topPcLoop_exec hQ ds hA hA9 hNW hgate h4 hr hw hρ pcs hpcs
    (padRows R₂ Y) v₂ { S with R := Function.update Rd (reg .io) (encZ (prime + Ka) w
      (padRows R₂ Y)) } hL (hTd.update_io _)
    (by simpa [Function.update_of_ne (reg_ne (show LReg.park ≠ .io by simp))] using hcfd)
    (by dsimp only; rw [Function.update_of_ne (reg_ne (by simp)), hRd,
      topDownR_of_ne (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hI.pl)
    (by dsimp only; rw [Function.update_of_ne (reg_ne (by simp)), hRd,
      topDownR_of_ne (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hI.pb)
    (by simp)
  rw [Function.update_idem] at e₃
  set G := piecesZ ds (topPieces hρ pcs hpcs) (padRows R₂ Y) with hG
  -- unpad
  have hGl : (encZ (prime + Ka) w G).length = R₂ * 2 ^ n * r * w := topEnc_length w G
  obtain ⟨v₄, c₄, hu₄, hc₄, e₄⟩ := topUnpadS_exec body h2 h3 v₃
    { S with R := Function.update Rd (reg .io) (encZ (prime + Ka) w G) } (hTd.update_io _)
    (by simpa [Function.update_of_ne (reg_ne (show LReg.park ≠ .io by simp))] using hcfd)
    (by
      simp only [Function.update_self, hGl]
      have := Nat.mul_le_mul_right (2 ^ n * r * w) hR₂
      rw [Nat.mul_comm (2 ^ a) R]; nlinarith [this])
  dsimp only at e₄ hc₄
  rw [Function.update_self, Function.update_idem] at e₄
  have hunpad : (encZ (prime + Ka) w G).take (2 ^ a * R * (2 ^ n * r * w)) =
      encZ (prime + Ka) w (unpadRows hR₂ G) := by
    rw [topEnc_unpadRows]; congr 1; ring
  rw [hunpad] at e₄
  -- up
  obtain ⟨v₅, c₅, hu₅, hc₅, e₅⟩ := topUpS_exec body h2 v₄ S hT hI
    (encZ (prime + Ka) w (unpadRows hR₂ G))
  refine ⟨v₅, c₁ + (c₂ + (c₃ + (c₄ + c₅))), by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ e₅)))⟩
  rw [hiod, Function.update_self, hGl, topEnc_length] at *
  unfold topBlockCost
  have e1 : (2 ^ a * R) = R * 2 ^ a := Nat.mul_comm _ _
  simp only [topPadCost, topUnpadCost] at hc₂ hc₄ ⊢
  nlinarith [hc₁, hc₂, hc₃, hc₄, hc₅]

end PieceLoop

/-! ### The layer -/

/-- The top bits `aT + ρ + K i`, `i < q`, of `N` address bits. -/
def topTop (aT ρ K q N : ℕ) (hfit : ∀ i < q, aT + ρ + K * i < N) : List (Fin N) :=
  (List.finRange q).map (actMap aT ρ K q N hfit)

/-- The selected bits `low ++ top` of `n + a` address bits. -/
def topSel {n : ℕ} (a : ℕ) (low : List (Fin n)) (top : List (Fin (n + a))) :
    List (Fin (n + a)) :=
  low.map (Fin.castAdd a) ++ top

/-- The array `topZ` shifts: the unit times the phased result of the kernels. -/
noncomputable def topPre {R r n : ℕ} (ds : ComplexFramedExecution.Directions) (a : ℕ)
    (low : List (Fin n)) (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂)
    (Ps : List (Piece n R₂)) (Z : ZArr (Fin R × Fin r) (n + a)) : ZArr (Fin R × Fin r) (n + a) :=
  fun p => unitD (topSel a low top).length * sZ (topSel a low top)
    (ofRows a (unpadRows hR₂ (piecesZ ds Ps (padRows R₂ (toRows a
      (k2s top (sZ (topSel a low top) Z))))))) p

lemma topZ_eq_pre {R r n : ℕ} (ds : ComplexFramedExecution.Directions) (a : ℕ)
    (low : List (Fin n)) (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂)
    (Ps : List (Piece n R₂)) (s : ℕ) (Z : ZArr (Fin R × Fin r) (n + a)) :
    topZ ds a low top hR₂ Ps s Z = fun p => tdivZ s (topPre ds a low top hR₂ Ps Z p) := rfl


/-- The selection mask of the machine is the indicator of the selected bits when these are the
bits `ρ + oS + K i`, `i < D`. -/
lemma topMaskOf_eq {N ρ K oS D : ℕ} (hK : 1 ≤ K) (sel : List (Fin N))
    (hselm : ∀ t : Fin N, t ∈ sel ↔ ∃ i < D, (t : ℕ) = ρ + oS + K * i) :
    topMaskOf N ρ K oS D = topSelMask sel := by
  funext t
  simp only [topMaskOf, addrBits, topSelMask]
  have h := testBit_maskVal (o := ρ + oS) (K := K) (k := D) (M := 1) hK (fun _ => true) t
  by_cases ht : t ∈ sel
  · have := (hselm t).1 ht
    have hb := h.2 (by simpa using this)
    simp only [ht, hb, ite_true]
  · have hb : (maskVal (ρ + oS) K D 1 fun _ => true).testBit t = false := by
      rw [← Bool.not_eq_true]
      intro hb
      obtain ⟨i, hi, -, he⟩ := h.1 hb
      exact ht ((hselm t).2 ⟨i, by simpa using hi, he⟩)
    simp only [ht, hb, ite_false]
    rfl

section Layer

variable {Q Ka : ℕ} {U : Type}

/-- **The host machine of the simultaneous layer**, one fixed program: widening (`topWidenS`),
the phase (`topPhaseS`), the top kernels (`topKerS`), the pieces with the top bits as rows
(`topBlockS`), the phase, the unit (`topUnitS`) and the truncating shift (`topShiftS`). All sizes
come from the registers. -/
noncomputable def topProg : Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq topWidenS (.seq topPhaseS (.seq topKerS (.seq topBlockS (.seq topPhaseS
    (.seq topUnitS topShiftS)))))

/-- The step bound of `topProg`: the sum of the stage bounds. -/
noncomputable def topCost (ds : ComplexFramedExecution.Directions)
    (w w' s n a R r K ρ q aT oS D R₂ : ℕ) (pcs : List TopPc) : ℕ :=
  topWidenSCost (topCfg w s a R R₂ q aT K oS D) R (n + a) r w w' +
    topPhaseSCost (topCfg w s a R R₂ q aT K oS D) (n + a) R r w' K ρ oS D +
    topKerSCost ds (topCfg w s a R R₂ q aT K oS D) K ρ R (n + a) r w' q aT +
    topBlockCost ds (topCfg w s a R R₂ q aT K oS D) K ρ n a r w' R R₂ pcs +
    topPhaseSCost (topCfg w s a R R₂ q aT K oS D) (n + a) R r w' K ρ oS D +
    topUnitSCost (topCfg w s a R R₂ q aT K oS D) R (n + a) r w' D +
    topShiftSCost (topCfg w s a R R₂ q aT K oS D) R (n + a) r w' s w

/-- **The host machine of the simultaneous layer** (`topProg`). The configuration is read from
the registers: `park` holds the record `topCfg w s a R R₂ q aT K oS D` (on top of anything),
`ph .arr` the piece record `topPcRec K pcs`, `lf (.k .arr)`, `st`, `cs` are empty, and
`TopRegs S.R (n + a) r w' K ρ` holds (the per-call parameters empty, `n`, `w`, `rw`, `K`, `ρ`
holding `n + a`, `w'`, `r w'`, `K`, `ρ`, every register at rest). With every left stack empty
and `io` holding the `w`-bit stream of `Z` (coefficients fitting `w` signed bits), the machine
ends with `io` holding the `w`-bit stream of `topZ ds a low top hR₂ Ps s Z`, `top` the bits
`aT + ρ + K i` (`i < q`) and `Ps` the pieces of `pcs`, provided the selected bits are the `D`
distinct bits `ρ + oS + K i`, the array before the shift fits `w'` signed bits and
`s + w ≤ w'`. Every other register and `user` end as they started, within `topCost` steps. -/
theorem topProg_exec (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hA : 14 ≤ prime + Ka)
    (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
    {w w' s n a R r K ρ q aT oS D R₂ : ℕ} (low : List (Fin n)) (pcs : List TopPc)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hsw : s + w ≤ w') (hρ : ρ < K) (hR : 1 ≤ R)
    (hfitT : ∀ i < q, aT + ρ + K * i < n + a) (hTL : aT + K * q ≤ n + a)
    (hR₂ : R * 2 ^ a ≤ R₂) (hpcs : ∀ pc ∈ pcs, pc.Ok ds K n w' R₂)
    (hselm : ∀ t : Fin (n + a), t ∈ topSel a low (topTop aT ρ K q (n + a) hfitT) ↔
      ∃ i < D, (t : ℕ) = ρ + oS + K * i)
    (hsel : (topSel a low (topTop aT ρ K q (n + a) hfitT)).Nodup)
    (hD : (topSel a low (topTop aT ρ K q (n + a) hfitT)).length = D)
    (Z : ZArr (Fin R × Fin r) (n + a)) (hZ : ∀ p, TopFitsZ w (Z p))
    (hX : ∀ p, TopFitsZ w' (topPre ds a low (topTop aT ρ K q (n + a) hfitT) hR₂
      (topPieces hρ pcs hpcs) Z p))
    (v : HS (nT SXReg) Q (prime + Ka) U) (S : Stacks (nT SXReg) (prime + Ka))
    (hL : ∀ y, S.L y = []) (hT : TopRegs S.R (n + a) r w' K ρ)
    (hI : TopIn S.R (topCfg w s a R R₂ q aT K oS D) (topPcRec K pcs))
    (hio : S.R (reg .io) = encZ (prime + Ka) w Z) :
    ∃ (v' : HS (nT SXReg) Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      c ≤ topCost ds w w' s n a R r K ρ q aT oS D R₂ pcs ∧
      Exec (layerTable hQ ds) topProg (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ (prime + Ka) w (topZ ds a low
            (topTop aT ρ K q (n + a) hfitT) hR₂ (topPieces hρ pcs hpcs) s Z)) }) := by
  set body := layerTable (Ka := Ka) (U := U) hQ ds
  set cfg := topCfg w s a R R₂ q aT K oS D with hcfg
  set top := topTop aT ρ K q (n + a) hfitT with htop
  set sel := topSel a low top with hseldef
  set Ps := topPieces hρ pcs hpcs with hPs
  have hw' : 1 ≤ w' := by omega
  have hK : 1 ≤ K := by omega
  have hA5 : 5 ≤ prime + Ka := by omega
  have hmask : topMaskOf (n + a) ρ K oS D = topSelMask sel := topMaskOf_eq hK sel hselm
  have hT' : ∀ X, TopRegs (Function.update S.R (reg .io) X) (n + a) r w' K ρ :=
    fun X => hT.update_io X
  have hI' : ∀ X, TopIn (Function.update S.R (reg .io) X) cfg (topPcRec K pcs) :=
    fun X => hI.update_io X
  -- the arrays
  set Z₁ := sZ sel Z with hZ₁
  set Z₂ := k2s top Z₁ with hZ₂
  set G := unpadRows hR₂ (piecesZ ds Ps (padRows R₂ (toRows a Z₂))) with hG
  set Z₃ := ofRows a G with hZ₃
  set Z₄ := sZ sel Z₃ with hZ₄
  set Z₅ := topPre ds a low top hR₂ Ps Z with hZ₅
  have hZ₅e : Z₅ = fun p => unitD D * Z₄ p := by rw [hZ₅, ← hD]; rfl
  -- 1. widen
  obtain ⟨v₁, c₁, hu₁, hc₁, e₁⟩ := topWidenS_exec body (cfg := cfg) (by simp [hcfg, topCfg]) hw
    (by omega : w ≤ w') Z hZ v S hT hI hio
  -- 2. phase
  obtain ⟨v₂, c₂, hu₂, hc₂, e₂⟩ := topPhaseS_exec body hA5 (cfg := cfg) (R := R) (oS := oS)
    (D := D)
    (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) hr hw' hK Z v₁
    { S with R := Function.update S.R (reg .io) (encZ (prime + Ka) w' Z) } (hT' _) (hI' _)
    (by simp)
  rw [hmask, topPhase_sZ sel hsel, topIo] at e₂
  -- 3. the top kernels
  obtain ⟨v₃, c₃, hu₃, hc₃, e₃⟩ := topKerS_exec hQ ds hA hA9 hNW hgate (cfg := cfg)
    (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg])
    (by simp [hcfg, topCfg]) hr hw' hρ hR hfitT hTL Z₁ v₂
    { S with R := Function.update S.R (reg .io) (encZ (prime + Ka) w' Z₁) } hL (hT' _) (hI' _)
    (by simp)
  rw [topIo] at e₃
  -- 4. the pieces with the top bits as rows
  obtain ⟨v₄, c₄, hu₄, hc₄, e₄⟩ := topBlockS_exec hQ ds hA hA9 hNW hgate (cfg := cfg)
    (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) hr hw' hρ hR₂ pcs
    hpcs (toRows a Z₂) v₃
    { S with R := Function.update S.R (reg .io) (encZ (prime + Ka) w' Z₂) } hL (hT' _) (hI' _)
    (by simp [topEnc_toRows])
  rw [topIo, ← hG, ← topEnc_ofRows a G, ← hZ₃] at e₄
  -- 5. phase
  obtain ⟨v₅, c₅, hu₅, hc₅, e₅⟩ := topPhaseS_exec body hA5 (cfg := cfg) (R := R) (oS := oS)
    (D := D)
    (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) hr hw' hK Z₃ v₄
    { S with R := Function.update S.R (reg .io) (encZ (prime + Ka) w' Z₃) } (hT' _) (hI' _)
    (by simp)
  rw [hmask, topPhase_sZ sel hsel, topIo] at e₅
  -- 6. the unit
  obtain ⟨v₆, c₆, hu₆, hc₆, e₆⟩ := topUnitS_exec body (by omega) (cfg := cfg) (D := D)
    (by simp [hcfg, topCfg]) hw' Z₄ v₅
    { S with R := Function.update S.R (reg .io) (encZ (prime + Ka) w' Z₄) } (hT' _) (hI' _)
    (by simp)
  rw [topIo, ← hZ₅e] at e₆
  -- 7. the truncating shift
  obtain ⟨v₇, c₇, hu₇, hc₇, e₇⟩ := topShiftS_exec body (by omega) (cfg := cfg)
    (by simp [hcfg, topCfg]) (by simp [hcfg, topCfg]) hw' hsw Z₅ hX v₆
    { S with R := Function.update S.R (reg .io) (encZ (prime + Ka) w' Z₅) } (hT' _) (hI' _)
    (by simp)
  rw [topIo] at e₇
  refine ⟨v₇, _, by rw [hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      e₇)))))) rfl (by rw [topZ_eq_pre])⟩
  unfold topCost
  rw [← hcfg]
  omega

/-- **The layer.** `topProg_exec` with `topZ_correct`: for injective pieces covering `low` and
the shift `s = ⌈D/2⌉ + |top| + Σ exp`, the machine leaves on `io` the stream of the
componentwise truncation toward zero of the normalized butterflies `Hl` on the selected bits. -/
theorem topProg_exec_Hl (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (hA : 14 ≤ prime + Ka) (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
    {w w' s n a R r K ρ q aT oS D R₂ : ℕ} (low : List (Fin n)) (pcs : List TopPc)
    (hr : 1 ≤ r) (hw : 1 ≤ w) (hsw : s + w ≤ w') (hρ : ρ < K) (hR : 1 ≤ R)
    (hfitT : ∀ i < q, aT + ρ + K * i < n + a) (hTL : aT + K * q ≤ n + a)
    (hR₂ : R * 2 ^ a ≤ R₂) (hpcs : ∀ pc ∈ pcs, pc.Ok ds K n w' R₂)
    (hinj : ∀ P ∈ topPieces hρ pcs hpcs, Function.Injective P.e)
    (hcover : ((topPieces hρ pcs hpcs).flatMap Piece.bitsList).Perm low)
    (hselm : ∀ t : Fin (n + a), t ∈ topSel a low (topTop aT ρ K q (n + a) hfitT) ↔
      ∃ i < D, (t : ℕ) = ρ + oS + K * i)
    (hsel : (topSel a low (topTop aT ρ K q (n + a) hfitT)).Nodup)
    (hD : (topSel a low (topTop aT ρ K q (n + a) hfitT)).length = D)
    (hs : s = (low.length + q + 1) / 2 + q + ((topPieces hρ pcs hpcs).map (Piece.exp ds)).sum)
    (Z : ZArr (Fin R × Fin r) (n + a)) (hZ : ∀ p, TopFitsZ w (Z p))
    (hX : ∀ p, TopFitsZ w' (topPre ds a low (topTop aT ρ K q (n + a) hfitT) hR₂
      (topPieces hρ pcs hpcs) Z p))
    (v : HS (nT SXReg) Q (prime + Ka) U) (S : Stacks (nT SXReg) (prime + Ka))
    (hL : ∀ y, S.L y = []) (hT : TopRegs S.R (n + a) r w' K ρ)
    (hI : TopIn S.R (topCfg w s a R R₂ q aT K oS D) (topPcRec K pcs))
    (hio : S.R (reg .io) = encZ (prime + Ka) w Z) :
    ∃ (v' : HS (nT SXReg) Q (prime + Ka) U) (c : ℕ), v'.user = v.user ∧
      c ≤ topCost ds w w' s n a R r K ρ q aT oS D R₂ pcs ∧
      Exec (layerTable hQ ds) topProg (mk v S) c
        (mk v' { S with
          R := Function.update S.R (reg .io) (encZ (prime + Ka) w (fun p =>
            (⟨truncR (Hl _ (topSel a low (topTop aT ρ K q (n + a) hfitT)) (toC Z) p).re,
              truncR (Hl _ (topSel a low (topTop aT ρ K q (n + a) hfitT)) (toC Z) p).im⟩ :
              GaussianInt))) }) := by
  obtain ⟨v', c, hu, hc, he⟩ := topProg_exec hQ ds hA hA9 hNW hgate low pcs hr hw hsw hρ hR
    hfitT hTL hR₂ hpcs hselm hsel hD Z hZ hX v S hL hT hI hio
  refine ⟨v', c, hu, hc, Exec.cast he rfl ?_⟩
  congr 4
  funext p
  have hq : (topTop aT ρ K q (n + a) hfitT).length = q := by simp [topTop]
  exact topZ_correct ds hd a low _ hR₂ _ hinj hcover hsel s (by rw [hq]; exact hs) Z p

end Layer

end IntegerMultBounds.MathlibTM2.LayerMachine
