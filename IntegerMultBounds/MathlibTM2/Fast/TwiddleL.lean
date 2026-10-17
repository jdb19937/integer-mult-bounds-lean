module

public import IntegerMultBounds.MathlibTM2.Fast.Twiddle
public import IntegerMultBounds.MathlibTM2.Mult.SynthErrRounds

/-!
# The twiddle pass in a permuted address layout

The transform machine stores the flat array in a layout `L : Equiv.Perm (Fin N)` of the address
bits (`IntegerMultBounds.MathlibTM2.Mult.SynthErr.relabel L`): logical address bit `k` (bit `h'` of axis `i` for
`k = off es i + h'`) lives at physical position `L k`. The records stream in physical address
order, so the twiddle of the record at physical address `m` is read from the logical address
`twGat pos N m`, whose bit `k` is bit `pos k` of `m` (`twGat_testBit`; `pos k = L k`,
`twGatL_ofBits`: `twGat (twPosL L) N (ofBits q) = ofBits (q ∘ L)`).

**Positions as data.** Register `pz` holds the positions as unary blocks, one per logical bit,
from `k = N - 1` down to `0`: block `k` is `pos k` ticks followed by `N - pos k` symbols
`bitSymbol false` (`twPosReg N pos`). `nn` and `nm` hold `N` symbols each.

**Gather** (`twGatherP`). For each block (`scanP` over `nn`), walk its `N` symbols (`scanP` over
`nm`), moving them onto `ps` and moving one bit of the physical address `pa` onto `pv` per tick;
then the top of `pa` is bit `pos k` of `m`, pushed onto `ad`; `pv` moves back onto `pa`. At the
end `ps` moves back onto `pz`. `twGather_runs`: the empty `ad` ends holding
`binSyms N (twGat pos N m)` and every other register as it started, within
`twGatherCost N = 12 N^2 + 12 N + 6` steps.

**Pass** (`twPassLP tg fwd`). Per record: gather the logical address onto `ad`, compute the
exponent from it (`twExpP`), clear `ad`, multiply the record (`twRecP`), increment the physical
address counter `pa` (`countIter`). `twPassL_runs`: `dst` gains the stream of the records `Z m`,
`m = m₀, …, m₀ + M - 1`, multiplied by `y^(twEx fwd es ℓ h (twGat pos N m))`; `pa` ends at
`binSyms N (m₀ + M)`.

**Flat arrays** (`twEncFlat_relabel`). If the physical stream holds the numerators of the
physical array `g` (`TwEncFlat p Z g`), the output holds those of
`twFwdFlatL es L h g = relabel L (twFwdFlat es h (relabel L.symm g))` (`fwd`) or
`twOppFlatL es L h g = relabel L (twOppFlat es h (relabel L.symm g))`: the twiddle of round `h`
in the layout `L`, the twiddle part of `SynthErr.fwdRoundFlatL` and `SynthErr.oppRoundFlatL`
(`relabel_fwdRoundFlat`, `relabel_oppRoundFlat`). `twPassL_flat` combines them for the whole
array (`M = 2^N` records from address `0`, positions `twPosL L`).

**Cost** (`twPassLCost`): `twPassLCost_le`: `M (35 r w + 50 (N + 1)(ℓ + 3) + 12 (N + 1)^2) + 4`
for `h ≤ ℓ`; `twPassLCost_le_sq`: `M (485 r w + 62 (N + 1)^2) + 4` for `h ≤ ℓ`, `1 ≤ w`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.NLogN IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.MathlibTM2.Mult.Rounds

set_option maxHeartbeats 1000000

/-! ### Logical addresses -/

/-- The logical address of the physical address `m`: bit `k < N` is bit `pos k` of `m`. -/
def twGat (pos : ℕ → ℕ) (N m : ℕ) : ℕ := twVal ((List.range N).map fun k => m.testBit (pos k))

lemma twVal_testBit : ∀ (l : List Bool) (k : ℕ), (twVal l).testBit k = l.getD k false
  | [], k => by simp [twVal]
  | b :: l, 0 => by cases b <;> simp [twVal, Nat.testBit_zero]
  | b :: l, k + 1 => by
      rw [Nat.testBit_succ, show twVal (b :: l) / 2 = twVal l by
        have := Bool.toNat_le b; simp only [twVal]; omega, twVal_testBit l k]
      simp

theorem twGat_testBit (pos : ℕ → ℕ) (N m k : ℕ) :
    (twGat pos N m).testBit k = (decide (k < N) && m.testBit (pos k)) := by
  rw [twGat, twVal_testBit]
  by_cases hk : k < N
  · simp [hk]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [hk]

/-- The positions of a layout `L`: logical bit `k` at physical position `L k`. -/
def twPosL {N : ℕ} (L : Equiv.Perm (Fin N)) (k : ℕ) : ℕ := if hk : k < N then L ⟨k, hk⟩ else 0

theorem twGatL_ofBits {N : ℕ} (L : Equiv.Perm (Fin N)) (q : Fin N → ZMod 2) :
    twGat (twPosL L) N (ofBits q) = ofBits (q ∘ L) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [twGat_testBit, testBit_ofBits, testBit_ofBits]
  by_cases hk : k < N
  · simp [hk, twPosL]
  · simp [hk]

/-- One block of positions: `p` ticks, then `N - p` symbols `bitSymbol false`. -/
def twBlock {A : ℕ} (N p : ℕ) : List (Fin (A + 4)) :=
  List.replicate p tick ++ List.replicate (N - p) (bitSymbol false)

/-- The position register: the blocks of `pos k` for `k = N - 1, …, 0`. -/
def twPosReg (A N : ℕ) (pos : ℕ → ℕ) : List (Fin (A + 4)) :=
  (List.range N).reverse.flatMap fun k => twBlock N (pos k)

lemma twBlock_length {A : ℕ} {N p : ℕ} (hp : p ≤ N) : (twBlock (A := A) N p).length = N := by
  simp [twBlock]; omega

lemma tw_tick_ne_false {A : ℕ} : (tick : Fin (A + 4)) ≠ bitSymbol false := by
  simp [tick, bitSymbol, Fin.ext_iff]

section Programs

variable {T Q A : ℕ} {U P : Type} (tg : TwReg → Fin T)

/-- One symbol of a block: onto `ps`; on a tick, one address bit from `pa` onto `pv`. -/
def twFetchStep : Pr P T Q A U :=
  .seq (.act (twMvTop (tg .pz) (tg .ps) .done))
    (.cond (fun v => decide (v.sym.getD blank = tick)) (.act (twMvTop (tg .pa) (tg .pv) .done))
      (.act .done))

/-- One logical bit: walk its block, push the address bit found onto `ad`, restore `pa`. -/
def twGatherOne : Pr P T Q A U :=
  .seq (scanP (tg .nm) (tg .t2) (twFetchStep tg)) <|
  .seq (.act (.peek (.rt (tg .pa)) (fun v o => { v with sym := o })
    (.push (.rt (tg .ad)) (fun v => v.sym.getD blank) .done))) (moveR (tg .pv) (tg .pa) id)

/-- **Gather** the logical address of the physical address `pa` onto `ad`. -/
def twGatherP : Pr P T Q A U :=
  .seq (scanP (tg .nn) (tg .t1) (twGatherOne tg)) (moveR (tg .ps) (tg .pz) id)

/-- One record in the layout: gather, exponent, product, next physical address. -/
def twStepLP (fwd : Bool) : Pr P T Q A U :=
  .seq (twGatherP tg) <| .seq (twExpP tg fwd) <| .seq (uclear (tg .ad)) <|
    .seq (twRecP tg) (countIter (tg .pa) (tg .t1) (tg .cy))

/-- **The twiddle pass in a permuted layout.** -/
def twPassLP (fwd : Bool) : Pr P T Q A U :=
  .seq (twWhile (tg .src) (twStepLP tg fwd)) (moveR (tg .acc) (tg .dst) id)

end Programs

/-- The step bound of `twGatherP`. -/
def twGatherCost (N : ℕ) : ℕ := 12 * N ^ 2 + 12 * N + 6

/-- The step bound of `twPassLP` on `M` records with `N` address bits. -/
def twPassLCost (N h ℓ w M : ℕ) : ℕ :=
  M * (twGatherCost N + twExpCost N h ℓ + (2 * N + 2) + twRecCost ℓ w + 4 * N + 5 + 2) + 2 +
    (2 * (M * (2 ^ ℓ * w)) + 2)

lemma tw_length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (n : ℕ)
    (hf : ∀ a ∈ l, (f a).length = n) : (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, hf a (by simp),
        ih (fun b hb => hf b (by simp [hb])), List.length_cons]
      ring

section Runs

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {tg : TwReg → Fin T}
  (htg : Function.Injective tg)
include htg

/-- The file of a block walk after `i` symbols: `pz`, `ps`, `pa`, `pv` moved. -/
def twWalkSt (R : TwReg → List (Fin (A + 4))) (B rest : List (Fin (A + 4))) (abits : List Bool)
    (p : ℕ) (i : ℕ) : TwReg → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update R .pz (B.drop i ++ rest)) .ps
    ((B.take i).reverse ++ R .ps)) .pa ((abits.drop (min i p)).map bitSymbol)) .pv
    ((abits.take (min i p)).reverse.map bitSymbol)

/-- **One logical bit.** -/
theorem twRuns_gatherOne {N p : ℕ} (hp : p < N) (R : TwReg → List (Fin (A + 4)))
    (rest : List (Fin (A + 4))) (abits : List Bool) (habits : abits.length = N)
    (hpz : R .pz = twBlock N p ++ rest) (hpa : R .pa = abits.map bitSymbol) (hpv : R .pv = [])
    (hnm : (R .nm).length = N) (ht2 : R .t2 = []) :
    TwRuns body tg (twGatherOne tg) R
      (Function.update (Function.update (Function.update R .pz rest) .ps
        ((twBlock N p).reverse ++ R .ps)) .ad (bitSymbol (abits.getD p false) :: R .ad))
      (10 * N + 7) := by
  set B : List (Fin (A + 4)) := twBlock N p with hB
  have hBl : B.length = N := twBlock_length hp.le
  have hBi : ∀ i (hi : i < B.length), B[i] = if i < p then tick else bitSymbol false := by
    intro i hi
    simp only [hB, twBlock]
    by_cases h : i < p
    · rw [List.getElem_append_left (by simpa using h)]; simp [h]
    · rw [List.getElem_append_right (by simp; omega)]; simp [h]
  -- the walk
  have hsc := twRuns_scanP (body := body) htg (a := .nm) (t := .t2) (by decide)
    (p := twFetchStep tg) (R .nm) (twWalkSt R B rest abits p) (fun _ => 3) ?_
  · have h0 : twAT .nm .t2 (R .nm) (twWalkSt R B rest abits p) 0 = R := by
      funext r
      cases r <;> simp [twAT, twWalkSt, hpz, hpa, hpv, ht2, hB]
    rw [h0] at hsc
    set R₁ := Function.update (Function.update (twWalkSt R B rest abits p (R .nm).length) .nm
      (R .nm)) .t2 [] with hR₁
    have hpa₁ : R₁ .pa = bitSymbol (abits[p]'(by omega)) :: (abits.drop (p + 1)).map bitSymbol := by
      simp only [hR₁, twWalkSt, Function.update_apply, reduceCtorEq, ↓reduceIte, hnm,
        min_eq_right hp.le]
      rw [List.drop_eq_getElem_cons (show p < abits.length by omega), List.map_cons]
    have h2 : TwRuns body tg (.act (.peek (.rt (tg .pa)) (fun v o => { v with sym := o })
        (.push (.rt (tg .ad)) (fun v => v.sym.getD blank) .done))) R₁
        (Function.update R₁ .ad (bitSymbol (abits.getD p false) :: R₁ .ad)) 1 := by
      refine twRuns_act _ (fun v S hS => ?_)
      refine ⟨{ v with sym := some (bitSymbol (abits.getD p false)) }, { S with
        R := Function.update S.R (tg .ad) (bitSymbol (abits.getD p false) :: S.R (tg .ad)) },
        rfl, ?_, ?_, twFr_upd S TwReg.ad _⟩
      · simp [Action.run, update_rt, hS .pa, hpa₁,
          List.getElem?_eq_getElem (show p < abits.length by omega)]
      · rw [hS .ad]; exact twHolds_upd htg hS .ad _
    have h3 := twRuns_moveR (body := body) htg (a := .pv) (b := .pa) (by decide)
      (Function.update R₁ .ad (bitSymbol (abits.getD p false) :: R₁ .ad))
    refine twRuns_mono (twRuns_congr (twRuns_seq hsc (twRuns_seq h2 h3)) ?_) ?_
    · have hBl' : (twBlock (A := A) N p).length ≤ N := (twBlock_length hp.le).le
      have hpa' : (abits.take p).reverse.reverse.map bitSymbol ++
          (abits.drop p).map (bitSymbol (a := A)) = abits.map bitSymbol := by
        rw [List.reverse_reverse, ← List.map_append, List.take_append_drop]
      funext r
      cases r <;> simp [hR₁, twWalkSt, hnm, min_eq_right hp.le, 
        ← List.map_reverse, hpa, hB, List.drop_of_length_le, hBl', ht2, hpv]
    · simp [hR₁, twWalkSt, hnm, min_eq_right hp.le, Finset.sum_const]
      omega
  · intro i hi
    rw [hnm] at hi
    have hiB : i < B.length := by omega
    have hpz' : twATin .nm .t2 (R .nm) (twWalkSt R B rest abits p) i .pz =
        B[i] :: (B.drop (i + 1) ++ rest) := by
      simp only [twATin, twWalkSt, Function.update_apply, reduceCtorEq, ↓reduceIte]
      rw [List.drop_eq_getElem_cons hiB, List.cons_append]
    have hstep := twRuns_mvTop_seqS (body := body) htg (src := .pz) (dst := .ps) (by decide)
      (q := .cond (fun v => decide (v.sym.getD blank = tick))
        (.act (twMvTop (tg .pa) (tg .pv) .done)) (.act .done))
      (ρ' := twAT .nm .t2 (R .nm) (twWalkSt R B rest abits p) (i + 1)) (b := 2) hpz' ?_
    · exact twRunsS_of (twRuns_mono hstep (by omega))
    · have htk : (B.take (i + 1)).reverse = B[i] :: (B.take i).reverse := by
        rw [List.take_add_one, List.getElem?_eq_getElem hiB]; simp
      by_cases hip : i < p
      · rw [hBi i hiB]
        simp only [hip, ↓reduceIte]
        have hpa' : Function.update (Function.update (twATin .nm .t2 (R .nm)
            (twWalkSt R B rest abits p) i) .pz (B.drop (i + 1) ++ rest)) .ps
            (tick :: twATin .nm .t2 (R .nm) (twWalkSt R B rest abits p) i .ps) .pa =
            bitSymbol (abits[i]'(by omega)) :: (abits.drop (i + 1)).map bitSymbol := by
          simp only [twATin, twWalkSt, Function.update_apply, reduceCtorEq, ↓reduceIte,
            min_eq_left hip.le]
          rw [List.drop_eq_getElem_cons (show i < abits.length by omega), List.map_cons]
        refine twRunsS_cond_true (fun v hv => by simp [hv]) (twRunsS_of ?_)
        refine twRuns_congr (twRuns_mvTop (body := body) htg (src := .pa) (dst := .pv)
          (by decide) hpa') ?_
        have hmin : min (i + 1) p = i + 1 := min_eq_left hip
        have htk2 : (abits.take (i + 1)).reverse.map (bitSymbol (a := A)) =
            bitSymbol (abits[i]'(by omega)) :: (abits.take i).reverse.map bitSymbol := by
          simp only [List.take_add_one, List.getElem?_eq_getElem (show i < abits.length by omega),
            Option.toList_some, List.reverse_append, List.reverse_cons,
            List.reverse_nil, List.nil_append, List.map_cons, List.singleton_append]
        funext r
        cases r <;> simp [twAT, twATin, twWalkSt, 
          min_eq_left hip.le, htk, htk2, hBi i hiB, hip]
      · rw [hBi i hiB]
        simp only [hip, ↓reduceIte]
        refine twRunsS_cond_false (fun v hv => by simp [hv, tw_tick_ne_false.symm])
          (twRunsS_of ?_)
        refine twRuns_congr (twRuns_act .done (fun v S hS => ⟨v, S, rfl, rfl, hS,
          twFr_refl S⟩)) ?_
        have hmin : min (i + 1) p = p := min_eq_right (by omega)
        have hmin' : min i p = p := min_eq_right (by omega)
        funext r
        cases r <;> simp [twAT, twATin, twWalkSt, hmin, hmin', htk,
          hBi i hiB, hip]

/-- The file of the gather after `t` logical bits (blocks `N - 1, …, N - t`). -/
def twGatherSt (R : TwReg → List (Fin (A + 4))) (N m : ℕ) (pos : ℕ → ℕ) (t : ℕ) :
    TwReg → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update R .pz
    ((List.range (N - t)).reverse.flatMap fun k => twBlock N (pos k))) .ps
    (((List.range' (N - t) t).reverse.flatMap fun k => twBlock N (pos k)).reverse)) .ad
    ((List.range' (N - t) t).map fun k => bitSymbol (m.testBit (pos k)))

/-- **Gather.** -/
theorem twGather_runs {N m : ℕ} (pos : ℕ → ℕ) (hpos : ∀ k < N, pos k < N)
    (R : TwReg → List (Fin (A + 4))) (hpz : R .pz = twPosReg A N pos) (hpa : R .pa = binSyms N m)
    (had : R .ad = []) (hps : R .ps = []) (hpv : R .pv = []) (hnn : (R .nn).length = N)
    (hnm : (R .nm).length = N) (ht1 : R .t1 = []) (ht2 : R .t2 = []) :
    TwRuns body tg (twGatherP tg) R (Function.update R .ad (binSyms N (twGat pos N m)))
      (twGatherCost N) := by
  have hsc := twRuns_scanP (body := body) htg (a := .nn) (t := .t1) (by decide)
    (p := twGatherOne tg) (R .nn) (twGatherSt R N m pos) (fun _ => 10 * N + 7) ?_
  · have h0 : twAT .nn .t1 (R .nn) (twGatherSt R N m pos) 0 = R := by
      funext r
      cases r <;> simp [twAT, twGatherSt, hpz, twPosReg, had, hps, ht1]
    rw [h0, hnn] at hsc
    have hmv := twRuns_moveR (body := body) htg (a := .ps) (b := .pz) (by decide)
      (Function.update (Function.update (twGatherSt R N m pos N) .nn (R .nn)) .t1 [])
    have hpsl : (Function.update (Function.update (twGatherSt R N m pos N) .nn (R .nn)) .t1 []
        .ps).length = N * N := by
      simp only [Function.update_apply, twGatherSt, reduceCtorEq, ↓reduceIte, List.length_reverse]
      rw [tw_length_flatMap_const _ _ N (fun k hk => by
        simp only [List.mem_reverse, List.mem_range'] at hk
        exact twBlock_length (hpos k (by omega)).le)]
      simp
    rw [hpsl] at hmv
    refine twRuns_mono (twRuns_congr (twRuns_seq hsc hmv) ?_) ?_
    · have had' : ((List.range' 0 N).map fun k => (bitSymbol (m.testBit (pos k)) :
          Fin (A + 4))) = binSyms N (twGat pos N m) := by
        rw [← List.range_eq_range', twGat]
        have := tw_map_bitSymbol (A := A) ((List.range N).map fun k => m.testBit (pos k))
        rw [List.map_map, List.length_map, List.length_range] at this
        exact this
      have hpz' : ((List.range' 0 N).reverse.flatMap fun k => twBlock (A := A) N (pos k)) =
          R .pz := by
        rw [hpz, ← List.range_eq_range']
        rfl
      funext r
      cases r <;> simp [twGatherSt, had', ht1, hps, hpz']
    · simp [Finset.sum_const, twGatherCost]
      nlinarith
  · intro t ht
    rw [hnn] at ht
    set k := N - (t + 1) with hk
    have hkN : k < N := by omega
    have hrange : (List.range (N - t)).reverse = k :: (List.range (N - (t + 1))).reverse := by
      rw [show N - t = k + 1 by omega, List.range_succ, List.reverse_append]
      rfl
    have hrange' : List.range' (N - (t + 1)) (t + 1) = k :: List.range' (N - t) t := by
      rw [List.range'_succ, show N - (t + 1) + 1 = N - t by omega]
    have hstep := twRuns_gatherOne (body := body) htg (N := N) (p := pos k) (hpos k hkN)
      (twATin .nn .t1 (R .nn) (twGatherSt R N m pos) t)
      ((List.range (N - (t + 1))).reverse.flatMap fun k => twBlock N (pos k)) (binBits N m)
      (length_binBits N m)
      (by simp only [twATin, twGatherSt, Function.update_apply, reduceCtorEq, ↓reduceIte]
          rw [hrange, List.flatMap_cons])
      (by simp [twATin, twGatherSt, hpa, binSyms_eq]) (by simp [twATin, twGatherSt, hpv])
      (by simp [twATin, twGatherSt, hnm]) (by simp [twATin, twGatherSt, ht2])
    refine twRunsS_of (twRuns_congr hstep ?_)
    have hbit : (binBits N m)[pos k]?.getD false = m.testBit (pos k) := by
      rw [List.getElem?_eq_getElem (by simp [hpos k hkN])]
      simp [binBits]
    have hps' : (twBlock N (pos k)).reverse ++
        ((List.range' (N - t) t).reverse.flatMap fun k => twBlock (A := A) N (pos k)).reverse =
        ((List.range' (N - (t + 1)) (t + 1)).reverse.flatMap fun k => twBlock N (pos k)).reverse := by
      rw [hrange', List.reverse_cons, List.flatMap_append, List.reverse_append]
      simp
    funext r
    cases r <;> simp [twAT, twATin, twGatherSt, hbit, hrange']

/-- The register file of the permuted pass after `j` records. -/
def twPassLSt (ρ : TwReg → List (Fin (A + 4))) (w N m₀ M : ℕ) {r : ℕ}
    (Z Z' : ℕ → Fin r → GaussianInt) (j : ℕ) : TwReg → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update ρ .src
    (twStream A w (List.range' (m₀ + j) (M - j)) Z)) .acc
    ((twStream A w (List.range' m₀ j) Z').reverse ++ ρ .acc)) .pa (binSyms N (m₀ + j))

/-- **The twiddle pass in a permuted layout.** The record at physical address `m` is multiplied
by `y^(twEx fwd es ℓ h (twGat pos N m))`, the exponent of its logical address. -/
theorem twPassL_runs (fwd : Bool) (hA : 5 ≤ A) {es : List ℕ} {ℓ h w m₀ M : ℕ} (hw : 1 ≤ w)
    (hh : h ≤ ℓ) (pos : ℕ → ℕ) (hpos : ∀ k < es.sum, pos k < es.sum)
    (Z : ℕ → Fin (2 ^ ℓ) → GaussianInt) (ρ : TwReg → List (Fin (A + 4)))
    (hsrc : ρ .src = twStream A w (List.range' m₀ M) Z) (hpa : ρ .pa = binSyms es.sum m₀)
    (hpz : ρ .pz = twPosReg A es.sum pos) (hnn : (ρ .nn).length = es.sum)
    (hnm : (ρ .nm).length = es.sum) (hrl : ρ .rl = twRoles A es h) (hwn : (ρ .wn).length = w)
    (hrwn : (ρ .rwn).length = 2 ^ ℓ * w) (hhn : (ρ .hn).length = h + 1)
    (hlh : (ρ .lh).length = ℓ - h) (had : ρ .ad = []) (hps : ρ .ps = []) (hpv : ρ .pv = [])
    (hacc : ρ .acc = []) (hx : ρ .x = []) (htl : ρ .tl = [])
    (hhd : ρ .hd = []) (hc : ρ .c = []) (hv : ρ .v = []) (hvp : ρ .vp = []) (hf : ρ .f = [])
    (hg : ρ .g = []) (hz : ρ .z = []) (hsg : ρ .sg = []) (has : ρ .as = []) (ht1 : ρ .t1 = [])
    (ht2 : ρ .t2 = []) (ht3 : ρ .t3 = []) (ht4 : ρ .t4 = []) (ht5 : ρ .t5 = []) :
    TwRuns body tg (twPassLP tg fwd) ρ
      (Function.update (Function.update (Function.update ρ .src []) .pa
        (binSyms es.sum (m₀ + M))) .dst
        (twStream A w (List.range' m₀ M)
          (fun m => twShiftZ (twEx fwd es ℓ h (twGat pos es.sum m)) (Z m)) ++ ρ .dst))
      (twPassLCost es.sum h ℓ w M) := by
  set Z' : ℕ → Fin (2 ^ ℓ) → GaussianInt :=
    fun m => twShiftZ (twEx fwd es ℓ h (twGat pos es.sum m)) (Z m) with hZ'
  set st := twPassLSt ρ w es.sum m₀ M Z Z' with hst
  have hstep : ∀ j < M, TwRuns body tg (twStepLP tg fwd) (st j) (st (j + 1))
      (twGatherCost es.sum + twExpCost es.sum h ℓ + (2 * es.sum + 2) + twRecCost ℓ w +
        (4 * es.sum + 5)) := by
    intro j hj
    set n := twGat pos es.sum (m₀ + j) with hn
    have h0 := twGather_runs (body := body) htg (N := es.sum) (m := m₀ + j) pos hpos (st j)
      (by simp [hst, twPassLSt, hpz]) (by simp [hst, twPassLSt]) (by simp [hst, twPassLSt, had])
      (by simp [hst, twPassLSt, hps]) (by simp [hst, twPassLSt, hpv])
      (by simp [hst, twPassLSt, hnn]) (by simp [hst, twPassLSt, hnm])
      (by simp [hst, twPassLSt, ht1]) (by simp [hst, twPassLSt, ht2])
    have h1 := twExp_runs (body := body) htg fwd (es := es) (ℓ := ℓ) (h := h) (n := n) hh
      (Function.update (st j) .ad (binSyms es.sum n)) (by simp [hst, twPassLSt, hrl]) (by simp)
      (by simp [hst, twPassLSt, hhn]) (by simp [hst, twPassLSt, hlh])
      (by simp [hst, twPassLSt, hf]) (by simp [hst, twPassLSt, hv])
      (by simp [hst, twPassLSt, hvp]) (by simp [hst, twPassLSt, has])
      (by simp [hst, twPassLSt, ht1]) (by simp [hst, twPassLSt, ht3])
      (by simp [hst, twPassLSt, ht4]) (by simp [hst, twPassLSt, ht5])
      (by simp [hst, twPassLSt, hz]) (by simp [hst, twPassLSt, hg])
    have h2 := twRuns_uclear (body := body) htg .ad
      (Function.update (Function.update (st j) .ad (binSyms es.sum n)) .f
        (binSyms (ℓ + 1) (twEx fwd es ℓ h n)))
    have hlen2 : (Function.update (Function.update (st j) .ad (binSyms es.sum n)) .f
        (binSyms (ℓ + 1) (twEx fwd es ℓ h n)) .ad).length = es.sum := by simp
    rw [hlen2] at h2
    set F := Function.update (Function.update (Function.update (st j) .ad (binSyms es.sum n)) .f
        (binSyms (ℓ + 1) (twEx fwd es ℓ h n))) .ad [] with hF
    have hsrcj : F .src = cstream A w (List.ofFn (Z (m₀ + j))) ++
        twStream A w (List.range' (m₀ + (j + 1)) (M - (j + 1))) Z := by
      simp only [hF, Function.update_apply, reduceCtorEq, ↓reduceIte, hst, twPassLSt]
      rw [show M - j = (M - (j + 1)) + 1 by omega, List.range'_succ]
      simp [twStream, Nat.add_assoc]
    have h3 := twRec_runs_ofFn (body := body) htg hA hw (e := twEx fwd es ℓ h n) F
      (Z (m₀ + j)) _ hsrcj (by simp [hF]) (by simp [hF, hst, twPassLSt, hwn])
      (by simp [hF, hst, twPassLSt, hrwn]) (by simp [hF, hst, twPassLSt, hx])
      (by simp [hF, hst, twPassLSt, htl]) (by simp [hF, hst, twPassLSt, hhd])
      (by simp [hF, hst, twPassLSt, hc]) (by simp [hF, hst, twPassLSt, hsg])
      (by simp [hF, hst, twPassLSt, ht1]) (by simp [hF, hst, twPassLSt, ht2])
      (by simp [hF, hst, twPassLSt, ht3])
    have h4 := twRuns_countIter (body := body) htg (c := .pa) (tmp := .t1) (by decide) (tg .cy)
      (W := es.sum) (j := m₀ + j)
      (Function.update (Function.update (Function.update F .src
        (twStream A w (List.range' (m₀ + (j + 1)) (M - (j + 1))) Z)) .acc
        ((cstream A w (List.ofFn (twShiftZ (twEx fwd es ℓ h n) (Z (m₀ + j))))).reverse ++ F .acc))
        .f []) (by simp [hF, hst, twPassLSt]) (by simp [hF, hst, twPassLSt, ht1])
    have h34 := twRuns_seq h3 h4
    refine twRuns_mono (twRuns_congr (twRuns_seq h0 (twRuns_seq h1 (twRuns_seq h2 h34))) ?_)
      (by omega)
    have hacc' : (twStream A w (List.range' m₀ (j + 1)) Z').reverse =
        (cstream A w (List.ofFn (twShiftZ (twEx fwd es ℓ h n) (Z (m₀ + j))))).reverse ++
          (twStream A w (List.range' m₀ j) Z').reverse := by
      rw [List.range'_concat]
      simp [twStream, hZ', hn]
    funext r
    cases r <;> simp [hF, hst, twPassLSt, hacc', hf, had, Nat.add_assoc]
  have hne : ∀ j < M, st j .src ≠ [] := by
    intro j hj hnil
    have hl := congrArg List.length hnil
    simp only [hst, twPassLSt, Function.update_apply, reduceCtorEq, ↓reduceIte] at hl
    rw [twStream_length, List.length_range'] at hl
    have : 0 < (M - j) * (2 ^ ℓ * w) :=
      Nat.mul_pos (by omega) (Nat.mul_pos (by positivity) hw)
    simp at hl
    omega
  have hend : st M .src = [] := by simp [hst, twPassLSt, twStream]
  have hwh := twRuns_while (body := body) (tg := tg) .src (twStepLP tg fwd) st M _ hstep hne hend
  have hmv := twRuns_moveR (body := body) htg (a := .acc) (b := .dst) (by decide) (st M)
  have hacc_len : (st M .acc).length = M * (2 ^ ℓ * w) := by
    simp [hst, twPassLSt, twStream_length, hacc]
  rw [hacc_len] at hmv
  have h0 : st 0 = ρ := by
    funext r
    cases r <;> simp [hst, twPassLSt, hsrc, hacc, hpa, twStream]
  rw [h0] at hwh
  refine twRuns_mono (twRuns_congr (twRuns_seq hwh hmv) ?_) ?_
  · funext r
    cases r <;> simp [hst, twPassLSt, hacc, hZ']
  · unfold twPassLCost
    apply le_of_eq
    ring

end Runs

/-! ### Flat arrays in a layout -/

section Flat

open IntegerMultBounds.MathlibTM2.Mult.SynthErr

variable {r : ℕ} [NeZero r]

/-- The forward twiddle of round `h` on an array stored in the layout `L`. -/
noncomputable def twFwdFlatL (es : List ℕ) (L : Equiv.Perm (Fin es.sum)) (h : ℕ)
    (g : Arr (Fin r) es.sum) : Arr (Fin r) es.sum :=
  relabel L (twFwdFlat es h (relabel L.symm g))

/-- The opposite twiddle of round `h` on an array stored in the layout `L`. -/
noncomputable def twOppFlatL (es : List ℕ) (L : Equiv.Perm (Fin es.sum)) (h : ℕ)
    (g : Arr (Fin r) es.sum) : Arr (Fin r) es.sum :=
  relabel L (twOppFlat es h (relabel L.symm g))

/-- The forward round in the layout `L` is its butterflies followed by `twFwdFlatL`. -/
theorem relabel_fwdRoundFlat (es : List ℕ) (L : Equiv.Perm (Fin es.sum)) (h : ℕ)
    (f : Arr (Fin r) es.sum) :
    fwdRoundFlatL es L h f =
      twFwdFlatL es L h (relabel L (Hl (Fin r) (selFin es h) (relabel L.symm f))) := by
  rw [twFwdFlatL, relabel_symm_relabel]; rfl

omit [NeZero r] in
/-- The opposite round in the layout `L` is `twOppFlatL` followed by its butterflies. -/
theorem relabel_oppRoundFlat (es : List ℕ) (L : Equiv.Perm (Fin es.sum)) (h : ℕ)
    (f : Arr (Fin r) es.sum) :
    oppRoundFlatL es L h f =
      relabel L (Hl (Fin r) (selFin es h) (relabel L.symm (twOppFlatL es L h f))) := by
  rw [twOppFlatL, relabel_symm_relabel]; rfl

end Flat

/-- The physical stream holds the numerators of the flat array `g` at scale `2^p`: the record at
physical address `ofBits q` holds `Z (ofBits q)`. -/
def TwEncFlat {r N : ℕ} (p : ℕ) (Z : ℕ → Fin r → GaussianInt) (g : Arr (Fin r) N) : Prop :=
  ∀ c q, g (c, q) = GaussianInt.toComplex (Z (ofBits q) c) / 2 ^ p

/-- **The output of the permuted pass on flat arrays**: the numerators of `twFwdFlatL es L h g`
(`fwd`) or `twOppFlatL es L h g`. -/
theorem twEncFlat_relabel (fwd : Bool) {ℓ p : ℕ} (es : List ℕ) (L : Equiv.Perm (Fin es.sum))
    (h : ℕ) {Z : ℕ → Fin (2 ^ ℓ) → GaussianInt} {g : Arr (Fin (2 ^ ℓ)) es.sum}
    (hZ : TwEncFlat p Z g) :
    TwEncFlat p (fun m => twShiftZ (twEx fwd es ℓ h (twGat (twPosL L) es.sum m)) (Z m))
      (if fwd then twFwdFlatL es L h g else twOppFlatL es L h g) := by
  intro c q
  have hg : (fun c' => IntegerMultBounds.MathlibTM2.Mult.SynthErr.relabel L.symm g (c', q ∘ L)) =
      fun c' => GaussianInt.toComplex (Z (ofBits q) c') / 2 ^ p := by
    funext c'
    have : (q ∘ L) ∘ L.symm = q := by funext x; simp
    simp only [IntegerMultBounds.MathlibTM2.Mult.SynthErr.relabel, this]
    exact hZ c' q
  rw [twShiftZ_toComplex, twGatL_ofBits]
  cases fwd with
  | true =>
      show shiftInv _ (fun c' => IntegerMultBounds.MathlibTM2.Mult.SynthErr.relabel L.symm g (c', q ∘ L)) c = _
      rw [hg]; rfl
  | false =>
      show shiftNegZ _ (fun c' => IntegerMultBounds.MathlibTM2.Mult.SynthErr.relabel L.symm g (c', q ∘ L)) c = _
      rw [hg, twEx_false, ← shiftNegZ_mod]

lemma twPosL_lt {N : ℕ} (L : Equiv.Perm (Fin N)) : ∀ k < N, twPosL L k < N := by
  intro k hk; simp [twPosL, hk]

section FlatRuns

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {tg : TwReg → Fin T}
  (htg : Function.Injective tg)
include htg

/-- **The twiddle pass in the layout `L`, on flat arrays.** The stream holds the physical array
`g` (records in physical address order `0, …, 2^N - 1`); afterwards `dst` holds the numerators of
the twiddle of round `h` in the layout `L`: `twFwdFlatL es L h g` (`fwd`) or
`twOppFlatL es L h g`. The positions register holds `twPosReg A N (twPosL L)`. -/
theorem twPassL_flat (fwd : Bool) (hA : 5 ≤ A) {es : List ℕ} {ℓ h w p : ℕ} (hw : 1 ≤ w)
    (hh : h ≤ ℓ) (L : Equiv.Perm (Fin es.sum)) (Z : ℕ → Fin (2 ^ ℓ) → GaussianInt)
    (g : Arr (Fin (2 ^ ℓ)) es.sum) (hZ : TwEncFlat p Z g) (ρ : TwReg → List (Fin (A + 4)))
    (hsrc : ρ .src = twStream A w (List.range (2 ^ es.sum)) Z) (hpa : ρ .pa = binSyms es.sum 0)
    (hpz : ρ .pz = twPosReg A es.sum (twPosL L)) (hnn : (ρ .nn).length = es.sum)
    (hnm : (ρ .nm).length = es.sum) (hrl : ρ .rl = twRoles A es h) (hwn : (ρ .wn).length = w)
    (hrwn : (ρ .rwn).length = 2 ^ ℓ * w) (hhn : (ρ .hn).length = h + 1)
    (hlh : (ρ .lh).length = ℓ - h) (had : ρ .ad = []) (hps : ρ .ps = []) (hpv : ρ .pv = [])
    (hacc : ρ .acc = []) (hx : ρ .x = []) (htl : ρ .tl = [])
    (hhd : ρ .hd = []) (hc : ρ .c = []) (hv : ρ .v = []) (hvp : ρ .vp = []) (hf : ρ .f = [])
    (hg : ρ .g = []) (hz : ρ .z = []) (hsg : ρ .sg = []) (has : ρ .as = []) (ht1 : ρ .t1 = [])
    (ht2 : ρ .t2 = []) (ht3 : ρ .t3 = []) (ht4 : ρ .t4 = []) (ht5 : ρ .t5 = []) :
    ∃ Z' : ℕ → Fin (2 ^ ℓ) → GaussianInt,
      TwEncFlat p Z' (if fwd then twFwdFlatL es L h g else twOppFlatL es L h g) ∧
      TwRuns body tg (twPassLP tg fwd) ρ
        (Function.update (Function.update (Function.update ρ .src []) .pa
          (binSyms es.sum (2 ^ es.sum))) .dst
          (twStream A w (List.range (2 ^ es.sum)) Z' ++ ρ .dst))
        (twPassLCost es.sum h ℓ w (2 ^ es.sum)) := by
  refine ⟨_, twEncFlat_relabel fwd es L h hZ, ?_⟩
  have := twPassL_runs (body := body) htg fwd hA (m₀ := 0) (M := 2 ^ es.sum) hw hh (twPosL L)
    (twPosL_lt L) Z ρ (by rw [hsrc, List.range_eq_range']) hpa hpz hnn hnm hrl hwn hrwn hhn hlh
    had hps hpv hacc hx htl hhd hc hv hvp hf hg hz hsg has ht1 ht2 ht3 ht4 ht5
  rw [← List.range_eq_range', Nat.zero_add] at this
  exact this

end FlatRuns

/-! ### Cost -/

/-- The permuted pass costs `O(r w + (N + 1)(ℓ + 1) + (N + 1)^2)` per record. -/
theorem twPassLCost_le {N h ℓ w M : ℕ} (hh : h ≤ ℓ) :
    twPassLCost N h ℓ w M ≤
      M * (35 * 2 ^ ℓ * w + 50 * (N + 1) * (ℓ + 3) + 12 * (N + 1) ^ 2) + 4 := by
  unfold twPassLCost twGatherCost twExpCost twRecCost
  have h1 : N * h ≤ N * ℓ := Nat.mul_le_mul_left _ hh
  have hper : 12 * N ^ 2 + 12 * N + 6 + (N * (12 * h + 33) + 24 * h + 4 * ℓ + 70) +
      (2 * N + 2) + (33 * 2 ^ ℓ * w + 20 * ℓ + 40) + 4 * N + 5 + 2 + 2 * (2 ^ ℓ * w) ≤
      35 * 2 ^ ℓ * w + 50 * (N + 1) * (ℓ + 3) + 12 * (N + 1) ^ 2 := by
    have e1 : N * (12 * h + 33) = 12 * (N * h) + 33 * N := by ring
    have e2 : 50 * (N + 1) * (ℓ + 3) = 50 * (N * ℓ) + 150 * N + 50 * ℓ + 150 := by ring
    have e3 : 33 * 2 ^ ℓ * w = 33 * (2 ^ ℓ * w) := by ring
    have e4 : 35 * 2 ^ ℓ * w = 35 * (2 ^ ℓ * w) := by ring
    have e5 : 12 * (N + 1) ^ 2 = 12 * N ^ 2 + 24 * N + 12 := by ring
    rw [e1, e2, e3, e4, e5]
    omega
  calc M * (12 * N ^ 2 + 12 * N + 6 + (N * (12 * h + 33) + 24 * h + 4 * ℓ + 70) + (2 * N + 2) +
        (33 * 2 ^ ℓ * w + 20 * ℓ + 40) + 4 * N + 5 + 2) + 2 + (2 * (M * (2 ^ ℓ * w)) + 2)
      = M * (12 * N ^ 2 + 12 * N + 6 + (N * (12 * h + 33) + 24 * h + 4 * ℓ + 70) +
        (2 * N + 2) + (33 * 2 ^ ℓ * w + 20 * ℓ + 40) + 4 * N + 5 + 2 + 2 * (2 ^ ℓ * w)) + 4 := by
        ring
    _ ≤ M * (35 * 2 ^ ℓ * w + 50 * (N + 1) * (ℓ + 3) + 12 * (N + 1) ^ 2) + 4 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left M hper) 4

/-- The permuted pass costs `M (c₁ r w + c₂ (N + 1)^2) + 4` with `c₁ = 485`, `c₂ = 62`. -/
theorem twPassLCost_le_sq {N h ℓ w M : ℕ} (hh : h ≤ ℓ) (hw : 1 ≤ w) :
    twPassLCost N h ℓ w M ≤ M * (485 * 2 ^ ℓ * w + 62 * (N + 1) ^ 2) + 4 := by
  refine le_trans (twPassLCost_le hh) ?_
  have h1 : 50 * (N + 1) * (ℓ + 3) ≤ 25 * (N + 1) ^ 2 + 25 * (ℓ + 3) ^ 2 := by
    nlinarith [sq_nonneg ((N + 1 : ℤ) - (ℓ + 3))]
  have h2 := tw_sq_le_pow ℓ
  have h3 : 2 ^ ℓ ≤ 2 ^ ℓ * w := Nat.le_mul_of_pos_right _ hw
  have h4 : 35 * 2 ^ ℓ * w + 50 * (N + 1) * (ℓ + 3) + 12 * (N + 1) ^ 2 ≤
      485 * 2 ^ ℓ * w + 62 * (N + 1) ^ 2 := by
    nlinarith
  exact Nat.add_le_add_right (Nat.mul_le_mul_left M h4) 4

end IntegerMultBounds.MathlibTM2.Fast
