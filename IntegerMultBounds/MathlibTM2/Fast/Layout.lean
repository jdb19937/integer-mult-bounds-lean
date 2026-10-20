module

public import IntegerMultBounds.MathlibTM2.Fast.LayoutMove
public import IntegerMultBounds.MathlibTM2.Fast.Runs

/-!
# The layout `L` of the synthetic transforms as a host machine

Paper §6, proof of `lem:synthetic-transform-cost`: the machine that applies the layout
`L = layPerm es ℓ K` of `IntegerMultBounds.MathlibTM2.Fast.LayoutMath` to a record stream, and the machine that
restores it. A stream of `M = 2^N` records (`N = es.sum` address bits) moves as
`l ↦ moveRecs (layRec L) l`: the record at address `x` goes to the address whose bit `L j` is
bit `j` of `x`, and the records themselves (the polynomial suffixes) are untouched.

## Runs and loops

* `LayRuns body p R₀ R₁ c`: from every store with empty left stacks and register file `R₀`, the
  program `p` reaches the same store with register file `R₁` within `c` steps (`LayRuns.seq`).
* `layScan_exec`: `scanP a t p` runs `p` once per symbol of the counter `a`, iteration `j` taking
  `Φ j` to `Φ (j + 1)`; the counter is restored.
* `layDyn rg R s dm tm dx tx`: the register file `R` with the stream `s` on `str` and the loop
  counters `cM`, `tM`, `cX`, `tX`.
* A loader `prep` is specified by `LayLoads body rg prep (W j) (W (j + 1)) c`: it takes the
  register file `W j` to `W (j + 1)` within `c` steps, whatever the stream and the counters. The
  file `W (j + 1)` carries the parameters of move `j`: the masks of a single-bit move
  (`LayMvCfg`) or the interchange headers of an exchange (`LayBank`, with canonical header
  counters `layHs`, `layHdr_layHs`). This is the parameter-loader contract of
  `IntegerMultBounds.MathlibTM2.Fast.ResampA.rsa_all`.
* `layBitLoop rg prep` (counter `cM`): per move the loader and `layMoveBit`;
  `layBitLoop_exec`: the stream ends moved by `layBitMoves bs`, within `layBitCost`.
* `layXcLoop … prep` (counter `cX`): per move the loader and `layXchg`; `layXcLoop_exec`: the
  stream ends moved by `xs.map LayXcD.move`, within `layXcLoopCost`.

## The layout machine

* `layBits es ℓ K`: the prefix moves of `layMoves` as position pairs
  (`layBitMoves_layBits`); `layXcs es ℓ K B`: its chunk exchanges, the exchange of chunks
  `p < k` realized on the three chunk slots `layXcO K p k` (a third chunk below, between or
  above, which exists since exchanges occur only with `D q ≥ 4` chunks,
  `laySwaps_layTr_three`), with canonical headers (`layXcD`, `layXcD_OK`, `layXcD_move_perm`).
* `layMovesPerm_layApply`: the moves executed by `layApply` compose to `layPerm es ℓ K`;
  `layMovesPerm_layUnapply`: the inverse moves in reverse order compose to `(layPerm es ℓ K)⁻¹`.
* `layApply hd pay hi hQ rg hsw hT prepM prepX`: the bit loop, then the exchange loop;
  `layUnapply`: the exchange loop, then the bit loop. Neither program depends on `es`, `ℓ`, `K`.
* `layApply_exec`: the stream `l.flatten` becomes `(moveRecs (layRec (layPerm es ℓ K)) l).flatten`;
  `layUnapply_exec`: it becomes `(moveRecs (layRec (layPerm es ℓ K)).symm l).flatten`;
  `lay_moveRecs_roundtrip`: the two compose to the identity. Every other register follows the
  loader files `W`; the counters are restored.

## Costs

* One single-bit move: `layMvCost N B = 2^N (18 B + 20 N + 36) + 8 N + 26`, that is
  `O(V + M N)` for `V = M B` stream symbols.
* One exchange: `layXcStep` (`layXcCost`), the vendored interchange term
  `(T + 12 swapT t₀ + 5) · swapCost` of `swapPass_exec` plus `6` per bank
  symbol, `34 V` and `2 T + 6 swapT t₀ + 23`; `layXcStep_le` bounds it by
  `3 C_swap (T + 12 swapT t₀ + 5) V max(1, K)^τ` plus those linear terms.
* `layApply_cost_le`: at most `D (b + 1)` single-bit moves and `D q - 1` exchanges, so the
  layout costs at most `D (b + 1) (cM + layMvCost N B + 5) + (D q - 1) (cX + X + 5) + 8` with
  loaders of at most `cM`, `cX` steps and exchanges of at most `X` steps:
  `O(V (D K + D q K^τ))` apart from the loaders, as `b + 1 ≤ K`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer.PackedXor
open IntegerMultBounds.Networks.Shared50ModularControl (prime)



/-! ### Streams moved by a list of moves -/

section Streams

/-- The stream `l` of `2^n` records moved by the list of moves `ms`, the head first. -/
def layStream {α : Type*} (K n : ℕ) (ms : List LayMove) (l : List (List α)) : List (List α) :=
  moveRecs (layRec (layMovesPerm K n ms)) l

theorem lay_moveRecs_one {α : Type*} {M : ℕ} (l : List (List α)) (hl : l.length = M) :
    moveRecs (1 : Equiv.Perm (Fin M)) l = l := by
  subst hl
  apply List.ext_getElem (by simp [length_moveRecs])
  intro j h1 h2
  simp [moveRecs]
  rfl

theorem layStream_nil {α : Type*} (K n : ℕ) (l : List (List α)) (hl : l.length = 2 ^ n) :
    layStream K n [] l = l := by
  rw [layStream, show layMovesPerm K n [] = 1 from rfl, layRec_one, lay_moveRecs_one l hl]

theorem layStream_append {α : Type*} (K n : ℕ) (ms ms' : List LayMove) (l : List (List α))
    (hl : l.length = 2 ^ n) : layStream K n (ms ++ ms') l = layStream K n ms' (layStream K n ms l) := by
  rw [layStream, layMovesPerm_append, layRec_trans, moveRecs_trans _ _ _ hl]
  rfl

theorem length_layStream {α : Type*} (K n : ℕ) (ms : List LayMove) (l : List (List α)) :
    (layStream K n ms l).length = 2 ^ n := length_moveRecs _ _

theorem mem_layStream {α : Type*} {K n : ℕ} {ms : List LayMove} {l : List (List α)}
    (hl : l.length = 2 ^ n) {x : List α} (hx : x ∈ layStream K n ms l) : x ∈ l :=
  mem_moveRecs _ hl hx

end Streams

/-! ### The register files of the loops -/

section Dyn

variable {T A t₀ : ℕ}

/-- The register file `R` with the stream `s` on `str` and the loop counters `cM`, `tM`, `cX`,
`tX` holding `dm`, `tm`, `dx`, `tx`. -/
def layDyn (rg : LayReg t₀ → Fin T) (R : Fin T → List (Fin (A + 4)))
    (s dm tm dx tx : List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update R
    (rg .str) s) (rg .cM) dm) (rg .tM) tm) (rg .cX) dx) (rg .tX) tx

variable {rg : LayReg t₀ → Fin T}

theorem layDyn_other (hrg : Function.Injective rg) (R : Fin T → List (Fin (A + 4)))
    (s dm tm dx tx : List (Fin (A + 4))) {y : LayReg t₀} (h1 : y ≠ .str) (h2 : y ≠ .cM)
    (h3 : y ≠ .tM) (h4 : y ≠ .cX) (h5 : y ≠ .tX) : layDyn rg R s dm tm dx tx (rg y) = R (rg y) := by
  simp [layDyn, hrg.eq_iff, h1, h2, h3, h4, h5]

theorem layDyn_str (hrg : Function.Injective rg) (R : Fin T → List (Fin (A + 4)))
    (s dm tm dx tx : List (Fin (A + 4))) : layDyn rg R s dm tm dx tx (rg .str) = s := by
  simp [layDyn, hrg.eq_iff]

theorem layDyn_upd_str (hrg : Function.Injective rg) (R : Fin T → List (Fin (A + 4)))
    (s s' dm tm dx tx : List (Fin (A + 4))) :
    Function.update (layDyn rg R s dm tm dx tx) (rg .str) s' = layDyn rg R s' dm tm dx tx := by
  funext y
  simp only [layDyn, Function.update_apply]
  split_ifs <;> simp_all [hrg.eq_iff]

theorem layDyn_upd_M (hrg : Function.Injective rg) (R : Fin T → List (Fin (A + 4)))
    (s dm tm dx tx dm' tm' : List (Fin (A + 4))) :
    Function.update (Function.update (layDyn rg R s dm tm dx tx) (rg .cM) dm') (rg .tM) tm' =
      layDyn rg R s dm' tm' dx tx := by
  funext y
  simp only [layDyn, Function.update_apply]
  split_ifs <;> simp_all [hrg.eq_iff]

theorem layDyn_upd_X (R : Fin T → List (Fin (A + 4)))
    (s dm tm dx tx dx' tx' : List (Fin (A + 4))) :
    Function.update (Function.update (layDyn rg R s dm tm dx tx) (rg .cX) dx') (rg .tX) tx' =
      layDyn rg R s dm tm dx' tx' := by
  funext y
  simp only [layDyn, Function.update_apply]
  split_ifs <;> simp_all

theorem LayMvCfg.dyn (hrg : Function.Injective rg) {R : Fin T → List (Fin (A + 4))} {n B a b : ℕ}
    (h : LayMvCfg rg R n B a b) (s dm tm dx tx : List (Fin (A + 4))) :
    LayMvCfg rg (layDyn rg R s dm tm dx tx) n B a b := by
  have e : ∀ y : LayReg t₀, y ≠ .str → y ≠ .cM → y ≠ .tM → y ≠ .cX → y ≠ .tX →
      layDyn rg R s dm tm dx tx (rg y) = R (rg y) := fun y h1 h2 h3 h4 h5 =>
    layDyn_other hrg R s dm tm dx tx h1 h2 h3 h4 h5
  exact ⟨by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r0,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r1,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r2,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r3,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.q0,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.q1,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.q2,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.q3,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.tmp,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.ctrB,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.cnt,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.fld,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.mA,
    by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.mB,
    fun r => by rw [e _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.us r⟩

end Dyn

/-! ### The two loops -/

section Loops

variable {T Q t₀ : ℕ} {U F : Type}

/-- The bit moves of a list of position pairs `(a, b)`. -/
def layBitMoves (bs : List (ℕ × ℕ)) : List LayMove := bs.map fun e => .bit e.1 e.2

/-- A parameter loader: `prep` takes the register file `R₀` to `R₁` within `c` steps, whatever
the stream and the loop counters. -/
def LayLoads {A : ℕ} (body : F → Pr F T Q A U) (rg : LayReg t₀ → Fin T) (prep : Pr F T Q A U)
    (R₀ R₁ : Fin T → List (Fin (A + 4))) (c : ℕ) : Prop :=
  ∀ s dm tm dx tx, LayRuns body prep (layDyn rg R₀ s dm tm dx tx) (layDyn rg R₁ s dm tm dx tx) c

theorem layBitPerm_eq {n a b : ℕ} (K : ℕ) (ha : a < n) (hb : b < n) :
    layBitPerm n a b = (LayMove.bit a b).perm K n := by
  ext x
  rw [layBitPerm_apply ha hb, LayMove.perm_apply (show (LayMove.bit a b).Valid K n from ⟨ha, hb⟩)]
  rfl

theorem layStream_snoc {α : Type*} (K n : ℕ) (ms : List LayMove) (m : LayMove)
    (l : List (List α)) (hl : l.length = 2 ^ n) :
    layStream K n (ms ++ [m]) l = moveRecs (layRec (m.perm K n)) (layStream K n ms l) := by
  rw [layStream_append K n _ _ l hl, layStream]
  congr 2

/-- The loop of single-bit moves: per symbol of the counter `cM`, the loader `prep` and the
pass `layMoveBit`. -/
def layBitLoop {A : ℕ} (rg : LayReg t₀ → Fin T) (prep : Pr F T Q A U) : Pr F T Q A U :=
  scanP (rg .cM) (rg .tM) (.seq prep (layMoveBit rg))

/-- **The loop of single-bit moves** over the position pairs `bs`. The loader takes the register
file `W j` to `W (j + 1)`, configured for move `j` (`LayMvCfg`). The stream ends moved by
`layBitMoves bs`, within `∑_j (cp j + layMvCost n B + 3) + 2 |bs| + 4` steps. -/
theorem layBitLoop_exec {A : ℕ} (body : F → Pr F T Q A U) {rg : LayReg t₀ → Fin T}
    (hrg : Function.Injective rg) (prep : Pr F T Q A U) (K : ℕ) {n B : ℕ} (hB : 1 ≤ B)
    (bs : List (ℕ × ℕ)) (hbs : ∀ e ∈ bs, e.1 < n ∧ e.2 < n) (W : ℕ → Fin T → List (Fin (A + 4)))
    (hcfg : ∀ j (hj : j < bs.length), LayMvCfg rg (W (j + 1)) n B bs[j].1 bs[j].2)
    (cp : ℕ → ℕ) (hprep : ∀ j < bs.length, LayLoads body rg prep (W j) (W (j + 1)) (cp j))
    (l : List (List (Fin (A + 4)))) (hl : l.length = 2 ^ n) (hlB : ∀ x ∈ l, x.length = B)
    (cs dx tx : List (Fin (A + 4))) (hcs : cs.length = bs.length) :
    LayRuns body (layBitLoop rg prep) (layDyn rg (W 0) l.flatten cs [] dx tx)
      (layDyn rg (W bs.length) (layStream K n (layBitMoves bs) l).flatten cs [] dx tx)
      (∑ j ∈ Finset.range bs.length, (cp j + layMvCost n B + 3) + 2 * bs.length + 4) := by
  have hat : rg .cM ≠ rg .tM := by simp [hrg.eq_iff]
  set Φ : ℕ → Fin T → List (Fin (A + 4)) := fun j =>
    layDyn rg (W j) (layStream K n (layBitMoves (bs.take j)) l).flatten [] [] dx tx with hΦ
  have h := layScan_exec (body := body) hat (p := .seq prep (layMoveBit rg)) Φ cs
    (fun j => cp j + layMvCost n B) (by
      intro j hj
      rw [hcs] at hj
      simp only [hΦ, layDyn_upd_M hrg]
      refine LayRuns.seq (hprep j hj _ _ _ _ _) ?_
      intro v S hL hS
      set lj := layStream K n (layBitMoves (bs.take j)) l with hlj
      have hlj_len : lj.length = 2 ^ n := length_layStream _ _ _ _
      have hljB : ∀ x ∈ lj, x.length = B := fun x hx => hlB x (mem_layStream hl hx)
      obtain ⟨ha, hb⟩ := hbs bs[j] (List.getElem_mem hj)
      obtain ⟨v', m, hu, hm, he⟩ := layMoveBit_exec body hrg ha hb hB lj hlj_len hljB v S
        (by rw [hS, layDyn_str hrg]) (by rw [hS]; exact (hcfg j hj).dyn hrg _ _ _ _ _)
      refine ⟨v', m, hu, hm, ?_⟩
      rw [hS, layDyn_upd_str hrg] at he
      have htake : bs.take (j + 1) = bs.take j ++ [bs[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
      rw [htake, layBitMoves, List.map_append, ← layBitMoves, List.map_singleton,
        layStream_snoc K n _ _ l hl, ← hlj, ← layBitPerm_eq K ha hb]
      exact he)
  simp only [hΦ, layDyn_upd_M hrg, List.take_zero, hcs, List.take_length] at h
  rw [show layBitMoves [] = [] from rfl, layStream_nil K n l hl] at h
  exact h

/-- The data of one exchange: the chunk slots `o`, the exchanged slots `a`, `b`, and the header
counters `hs` of the interchange. -/
structure LayXcD where
  o : Fin 3 → ℕ
  a : Fin 3
  b : Fin 3
  hs : Fin 5 → List Bool

instance : Inhabited LayXcD := ⟨⟨fun _ => 0, 0, 1, fun _ => []⟩⟩

/-- The move of an exchange. -/
def LayXcD.move (d : LayXcD) : LayMove := .xc (d.o d.a) (d.o d.b)

/-- An exchange of distinct chunk slots with canonical headers of its dimensions. -/
def LayXcD.OK (n K B : ℕ) (d : LayXcD) : Prop :=
  LayXcOK n K d.o ∧ d.a ≠ d.b ∧ LayHdr n K d.o d.a d.b B d.hs

theorem LayBank.dyn {Ka : ℕ} {rg : LayReg t₀ → Fin T} (hrg : Function.Injective rg)
    {R : Fin T → List (Fin (prime + Ka + 4))} {hd : Fin 5 → Fin t₀} {pay : Fin t₀}
    {hs : Fin 5 → List Bool} (h : LayBank rg R hd pay hs) (s dm tm dx tx) :
    LayBank rg (layDyn rg R s dm tm dx tx) hd pay hs := by
  have e : ∀ j, layDyn rg R s dm tm dx tx (rg (.sw j)) = R (rg (.sw j)) := fun j =>
    layDyn_other hrg R s dm tm dx tx (by simp) (by simp) (by simp) (by simp) (by simp)
  exact ⟨by rw [e]; exact h.bpay, fun j hj => by rw [e]; exact h.bpriv j hj,
    fun k => by rw [e]; exact h.bhdr k, fun i hi hk => by rw [e]; exact h.bother i hi hk⟩

/-- The loop of chunk exchanges: per symbol of the counter `cX`, the loader `prep` and the pass
`layXchg`. -/
noncomputable def layXcLoop {Ka : ℕ} (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q) (rg : LayReg t₀ → Fin T)
    (hsw : Function.Injective fun j => rg (.sw j)) (hT : swapT t₀ ≤ T)
    (prep : Pr F T Q (prime + Ka) U) : Pr F T Q (prime + Ka) U :=
  scanP (rg .cX) (rg .tX) (.seq prep (layXchg hd pay hi hQ rg hsw hT))

/-- The step bound of the exchange `d` with the bank of the register file `R`. -/
noncomputable def layXcStep {Ka : ℕ} (T t₀ n K B : ℕ) (rg : LayReg t₀ → Fin T)
    (R : Fin T → List (Fin (prime + Ka + 4))) (d : LayXcD) : ℕ :=
  layXcCost T t₀ n K d.o d.a d.b B d.hs (∑ j, (R (rg (.sw j))).length)

/-- **The loop of chunk exchanges** over the exchanges `xs`. The loader takes the register file
`W j` to `W (j + 1)`, whose bank holds the headers of exchange `j` and whose `tmp` is empty. The
stream ends moved by `xs.map LayXcD.move`, within
`∑_j (cp j + layXcStep … (W (j + 1)) xs[j] + 3) + 2 |xs| + 4` steps. -/
theorem layXcLoop_exec {Ka : ℕ} (body : F → Pr F T Q (prime + Ka) U) (hd : Fin 5 → Fin t₀)
    (pay : Fin t₀) (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q)
    {rg : LayReg t₀ → Fin T} (hrg : Function.Injective rg) (hT : swapT t₀ ≤ T)
    (prep : Pr F T Q (prime + Ka) U) {n K B : ℕ} (hB : 0 < B) (xs : List LayXcD)
    (hxs : ∀ d ∈ xs, d.OK n K B) (W : ℕ → Fin T → List (Fin (prime + Ka + 4)))
    (hcfg : ∀ j (hj : j < xs.length), LayBank rg (W (j + 1)) hd pay xs[j].hs ∧
      W (j + 1) (rg .tmp) = [])
    (cp : ℕ → ℕ) (hprep : ∀ j < xs.length, LayLoads body rg prep (W j) (W (j + 1)) (cp j))
    (l : List (List (Fin (prime + Ka + 4)))) (hl : l.length = 2 ^ n)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8)
    (cs dm tm : List (Fin (prime + Ka + 4))) (hcs : cs.length = xs.length) :
    LayRuns body (layXcLoop hd pay hi hQ rg (fun _ _ h => by simpa using hrg h) hT prep)
      (layDyn rg (W 0) l.flatten dm tm cs [])
      (layDyn rg (W xs.length) (layStream K n (xs.map LayXcD.move) l).flatten dm tm cs [])
      (∑ j ∈ Finset.range xs.length,
        (cp j + layXcStep T t₀ n K B rg (W (j + 1)) (xs.getD j default) + 3) +
        2 * xs.length + 4) := by
  have hat : rg .cX ≠ rg .tX := by simp [hrg.eq_iff]
  set Φ : ℕ → Fin T → List (Fin (prime + Ka + 4)) := fun j =>
    layDyn rg (W j) (layStream K n ((xs.take j).map LayXcD.move) l).flatten dm tm [] [] with hΦ
  have h := layScan_exec (body := body) hat
    (p := .seq prep (layXchg hd pay hi hQ rg (fun _ _ h => by simpa using hrg h) hT)) Φ cs
    (fun j => cp j + layXcStep T t₀ n K B rg (W (j + 1)) (xs.getD j default)) (by
      intro j hj
      rw [hcs] at hj
      simp only [hΦ, layDyn_upd_X]
      refine LayRuns.seq (hprep j hj _ _ _ _ _) ?_
      intro v S hL hS
      set lj := layStream K n ((xs.take j).map LayXcD.move) l with hlj
      have hlj_len : lj.length = 2 ^ n := length_layStream _ _ _ _
      have hljB : ∀ x ∈ lj, x.length = B := fun x hx => hlB x (mem_layStream hl hx)
      have hlj8 : ∀ x ∈ lj, ∀ s ∈ x, s.val < 8 := fun x hx => h8 x (mem_layStream hl hx)
      obtain ⟨hO, hab, hh⟩ := hxs xs[j] (List.getElem_mem hj)
      have htmp : S.R (rg .tmp) = [] := by
        rw [hS, layDyn_other hrg _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
        exact (hcfg j hj).2
      obtain ⟨v', m, hu, hm, he⟩ := layXchg_exec body hd pay hi hQ hrg hT hO hab hB lj hlj_len
        hljB hlj8 xs[j].hs hh v S hL (by rw [hS, layDyn_str hrg]) htmp
        (by rw [hS]; exact (hcfg j hj).1.dyn hrg _ _ _ _ _)
      refine ⟨v', m, hu, ?_, ?_⟩
      · refine hm.trans (le_of_eq ?_)
        rw [List.getD_eq_getElem _ _ hj, layXcStep]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hS, layDyn_other hrg _ _ _ _ _ _ (by simp) (by simp) (by simp) (by simp) (by simp)]
      · rw [hS, layDyn_upd_str hrg] at he
        have htake : xs.take (j + 1) = xs.take j ++ [xs[j]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
        rw [htake, List.map_append, List.map_singleton, layStream_snoc K n _ _ l hl, ← hlj]
        exact he)
  simp only [hΦ, layDyn_upd_X, List.take_zero, hcs, List.take_length, List.map_nil] at h
  rw [layStream_nil K n l hl] at h
  exact h

end Loops

/-! ### The exchanges of the layout -/

section XcData

/-- The chunk slots of the exchange of the bottom chunks `p < k` (`K` bits each, chunk `c` at bit
`c K`): with a third slot at chunk `0` (below), chunk `1` (between) or chunk `2` (above). -/
def layXcO (K p k : ℕ) : Fin 3 → ℕ :=
  if 0 < p then ![k * K, p * K, 0] else if 2 ≤ k then ![k * K, K, 0] else ![2 * K, K, 0]

/-- The slot of chunk `k` among `layXcO K p k`. -/
def layXcA (p k : ℕ) : Fin 3 := if 0 < p then 0 else if 2 ≤ k then 0 else 1

/-- The slot of chunk `p` among `layXcO K p k`. -/
def layXcB (p : ℕ) : Fin 3 := if 0 < p then 1 else 2

/-- The canonical header counters of an exchange. -/
def layHs (n K : ℕ) (o : Fin 3 → ℕ) (a b : Fin 3) (B : ℕ) : Fin 5 → List Bool := fun k =>
  GrowingCounterData.advance (swapValues (layXcDims n K o a b B).1
    (layXcDims n K o a b B).2.1 (layXcDims n K o a b B).2.2 K K k) []

theorem layHdr_layHs (n K : ℕ) (o : Fin 3 → ℕ) (a b : Fin 3) (B : ℕ) :
    LayHdr n K o a b B (layHs n K o a b B) :=
  ⟨fun _ => GrowingCounterData.empty_value _,
    fun _ => GrowingCounterData.advance_canonical _ [] (Or.inl rfl)⟩

/-- The exchange data of the chunk pair `e = (p, k)`. -/
def layXcD (n K B : ℕ) (e : ℕ × ℕ) : LayXcD :=
  ⟨layXcO K e.1 e.2, layXcA e.1 e.2, layXcB e.1,
    layHs n K (layXcO K e.1 e.2) (layXcA e.1 e.2) (layXcB e.1) B⟩

theorem layXcD_OK {n K B m : ℕ} (hm : K * m ≤ n) (h3 : 3 ≤ m) {e : ℕ × ℕ}
    (he1 : e.1 < e.2) (he2 : e.2 < m) : (layXcD n K B e).OK n K B := by
  obtain ⟨p, k⟩ := e
  simp only at he1 he2
  have a1 : (k + 1) * K ≤ m * K := Nat.mul_le_mul_right K he2
  have a3 : 3 * K ≤ m * K := Nat.mul_le_mul_right K h3
  rw [Nat.add_mul] at a1
  rw [Nat.mul_comm K m] at hm
  refine ⟨?_, ?_, layHdr_layHs _ _ _ _ _ _⟩
  · by_cases hp : 0 < p
    · have a2 : (p + 1) * K ≤ k * K := Nat.mul_le_mul_right K he1
      have a4 : 1 * K ≤ p * K := Nat.mul_le_mul_right K hp
      rw [Nat.add_mul] at a2
      refine ⟨?_, ?_, ?_⟩ <;> simp [layXcD, layXcO, hp] <;> omega
    · by_cases hk : 2 ≤ k
      · have a2 : 2 * K ≤ k * K := Nat.mul_le_mul_right K hk
        refine ⟨?_, ?_, ?_⟩ <;> simp [layXcD, layXcO, hp, hk] <;> omega
      · refine ⟨?_, ?_, ?_⟩ <;> simp [layXcD, layXcO, hp, hk] <;> omega
  · by_cases hp : 0 < p
    · simp [layXcD, layXcA, layXcB, hp]
    · by_cases hk : 2 ≤ k <;> simp [layXcD, layXcA, layXcB, hp, hk]

theorem LayMove.perm_xc_comm {K N u w : ℕ} (h : (LayMove.xc u w).Valid K N) :
    (LayMove.xc u w).perm K N = (LayMove.xc w u).perm K N := by
  have h' : (LayMove.xc w u).Valid K N := ⟨h.2.1, h.1, h.2.2.symm⟩
  ext x
  rw [LayMove.perm_apply h, LayMove.perm_apply h']
  exact layXcFun_comm K u w x h.2.2

/-- The exchange of the chunk pair `(p, k)` moves the chunks at `p K` and `k K`. -/
theorem layXcD_move_perm {n K B m : ℕ} (hm : K * m ≤ n) (h3 : 3 ≤ m)
    {e : ℕ × ℕ} (he1 : e.1 < e.2) (he2 : e.2 < m) :
    (layXcD n K B e).move.perm K n = (LayMove.xc (e.1 * K) (e.2 * K)).perm K n := by
  obtain ⟨hO, hab, _⟩ := layXcD_OK (B := B) hm h3 he1 he2
  have hv := layXc_valid hO hab
  obtain ⟨p, k⟩ := e
  simp only at he1 he2
  rw [LayXcD.move, LayMove.perm_xc_comm hv]
  by_cases hp : 0 < p
  · simp [layXcD, layXcO, layXcA, layXcB, hp]
  · have hp0 : p = 0 := by omega
    subst hp0
    by_cases hk : 2 ≤ k
    · simp [layXcD, layXcO, layXcA, layXcB, hk]
    · have hk1 : k = 1 := by omega
      subst hk1
      simp [layXcD, layXcO, layXcA, layXcB]

theorem layMovesPerm_map_congr {α : Type*} {K N : ℕ} (f g : α → LayMove) :
    ∀ (xs : List α), (∀ x ∈ xs, (f x).perm K N = (g x).perm K N) →
      layMovesPerm K N (xs.map f) = layMovesPerm K N (xs.map g)
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.map_cons, List.map_cons, layMovesPerm, layMovesPerm, h x List.mem_cons_self,
        layMovesPerm_map_congr f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem laySwaps_one {m : ℕ} : ∀ k, laySwaps k (1 : Equiv.Perm (Fin m)) = []
  | 0 => rfl
  | k + 1 => by
      unfold laySwaps
      split_ifs with h1 h2
      · exact laySwaps_one k
      · exact absurd rfl h2
      · exact laySwaps_one k

theorem layTr_eq_one {D q : ℕ} (h : D ≤ 1 ∨ q ≤ 1) : layTr D q = 1 := by
  ext c
  have hc := c.isLt
  show (c : ℕ) % q * D + c / q = c
  rcases h with hD | hq
  · rcases Nat.lt_or_ge D 1 with h0 | h1
    · have : D = 0 := by omega
      subst this; simp at hc
    · have : D = 1 := by omega
      subst this
      have hc' : (c : ℕ) < q := by simpa using hc
      rw [Nat.mod_eq_of_lt hc', Nat.div_eq_of_lt hc']; ring
  · rcases Nat.lt_or_ge q 1 with h0 | h1
    · have : q = 0 := by omega
      subst this; simp at hc
    · have : q = 1 := by omega
      subst this
      simp [Nat.mod_one]

/-- Exchanges occur only with at least three chunks (`D ≥ 2` and `q ≥ 2`). -/
theorem laySwaps_layTr_three {D q : ℕ} :
    ∀ e ∈ laySwaps (D * q) (layTr D q), 3 ≤ D * q := by
  intro e he
  by_cases h : 2 ≤ D ∧ 2 ≤ q
  · have := Nat.mul_le_mul h.1 h.2; omega
  · rw [layTr_eq_one (by omega), laySwaps_one] at he
    simp at he

end XcData

/-! ### The layout machine -/

section Machine

variable {T Q t₀ Ka : ℕ} {U F : Type}

/-- **The layout machine** `L`: the loop of single-bit moves (loader `prepM`), then the loop of
chunk exchanges (loader `prepX`). The program does not depend on the moves: their positions,
masks and interchange headers come from the loaders. -/
noncomputable def layApply (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q) (rg : LayReg t₀ → Fin T)
    (hsw : Function.Injective fun j => rg (.sw j)) (hT : swapT t₀ ≤ T)
    (prepM prepX : Pr F T Q (prime + Ka) U) : Pr F T Q (prime + Ka) U :=
  .seq (layBitLoop rg prepM) (layXcLoop hd pay hi hQ rg hsw hT prepX)

/-- **The restoring machine** `L⁻¹`: the loop of chunk exchanges, then the loop of single-bit
moves, run with the inverse moves in reverse order. -/
noncomputable def layUnapply (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q) (rg : LayReg t₀ → Fin T)
    (hsw : Function.Injective fun j => rg (.sw j)) (hT : swapT t₀ ≤ T)
    (prepM prepX : Pr F T Q (prime + Ka) U) : Pr F T Q (prime + Ka) U :=
  .seq (layXcLoop hd pay hi hQ rg hsw hT prepX) (layBitLoop rg prepM)

/-- The step bound of the bit loop. -/
def layBitCost (n B : ℕ) (cp : ℕ → ℕ) (nb : ℕ) : ℕ :=
  ∑ j ∈ Finset.range nb, (cp j + layMvCost n B + 3) + 2 * nb + 4

/-- The step bound of the exchange loop, the bank lengths read from the register files
`W (j + 1)`. -/
noncomputable def layXcLoopCost (T t₀ n K B : ℕ) (rg : LayReg t₀ → Fin T)
    (W : ℕ → Fin T → List (Fin (prime + Ka + 4))) (cp : ℕ → ℕ) (xs : List LayXcD) : ℕ :=
  ∑ j ∈ Finset.range xs.length,
    (cp j + layXcStep T t₀ n K B rg (W (j + 1)) (xs.getD j default) + 3) + 2 * xs.length + 4

/-- `layApply` on the bit moves `bs` and the exchanges `xs`, with the register files `W j`
before move `j`, the loaders taking `W j` to `W (j + 1)`. -/
theorem layApply_exec_gen (body : F → Pr F T Q (prime + Ka) U) (hd : Fin 5 → Fin t₀)
    (pay : Fin t₀) (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q)
    {rg : LayReg t₀ → Fin T} (hrg : Function.Injective rg) (hT : swapT t₀ ≤ T)
    (prepM prepX : Pr F T Q (prime + Ka) U) {n K B : ℕ} (hB : 1 ≤ B) (bs : List (ℕ × ℕ))
    (xs : List LayXcD) (hbs : ∀ e ∈ bs, e.1 < n ∧ e.2 < n) (hxs : ∀ d ∈ xs, d.OK n K B)
    (W : ℕ → Fin T → List (Fin (prime + Ka + 4)))
    (hcfgM : ∀ j (hj : j < bs.length), LayMvCfg rg (W (j + 1)) n B bs[j].1 bs[j].2)
    (hcfgX : ∀ j (hj : j < xs.length), LayBank rg (W (bs.length + (j + 1))) hd pay xs[j].hs ∧
      W (bs.length + (j + 1)) (rg .tmp) = [])
    (cpM cpX : ℕ → ℕ)
    (hprepM : ∀ j < bs.length, LayLoads body rg prepM (W j) (W (j + 1)) (cpM j))
    (hprepX : ∀ j < xs.length,
      LayLoads body rg prepX (W (bs.length + j)) (W (bs.length + (j + 1))) (cpX j))
    (l : List (List (Fin (prime + Ka + 4)))) (hl : l.length = 2 ^ n)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8)
    (csM csX : List (Fin (prime + Ka + 4))) (hcsM : csM.length = bs.length)
    (hcsX : csX.length = xs.length) :
    LayRuns body (layApply hd pay hi hQ rg (fun _ _ h => by simpa using hrg h) hT prepM prepX)
      (layDyn rg (W 0) l.flatten csM [] csX [])
      (layDyn rg (W (bs.length + xs.length))
        (layStream K n (layBitMoves bs ++ xs.map LayXcD.move) l).flatten csM [] csX [])
      (layBitCost n B cpM bs.length +
        layXcLoopCost T t₀ n K B rg (fun j => W (bs.length + j)) cpX xs) := by
  have h1 := layBitLoop_exec body hrg prepM K hB bs hbs W hcfgM cpM hprepM l hl hlB csM csX []
    hcsM
  set l' := layStream K n (layBitMoves bs) l
  have hl' : l'.length = 2 ^ n := length_layStream _ _ _ _
  have h2 := layXcLoop_exec body hd pay hi hQ hrg hT prepX (by omega : 0 < B) xs hxs
    (fun j => W (bs.length + j)) hcfgX cpX hprepX l' hl'
    (fun x hx => hlB x (mem_layStream hl hx)) (fun x hx => h8 x (mem_layStream hl hx))
    csX csM [] hcsX
  simp only [Nat.add_zero] at h2
  rw [layStream_append K n _ _ l hl]
  exact h1.seq h2

/-- `layUnapply` on the exchanges `xs` and then the bit moves `bs`. -/
theorem layUnapply_exec_gen (body : F → Pr F T Q (prime + Ka) U) (hd : Fin 5 → Fin t₀)
    (pay : Fin t₀) (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q)
    {rg : LayReg t₀ → Fin T} (hrg : Function.Injective rg) (hT : swapT t₀ ≤ T)
    (prepM prepX : Pr F T Q (prime + Ka) U) {n K B : ℕ} (hB : 1 ≤ B) (xs : List LayXcD)
    (bs : List (ℕ × ℕ)) (hxs : ∀ d ∈ xs, d.OK n K B) (hbs : ∀ e ∈ bs, e.1 < n ∧ e.2 < n)
    (W : ℕ → Fin T → List (Fin (prime + Ka + 4)))
    (hcfgX : ∀ j (hj : j < xs.length), LayBank rg (W (j + 1)) hd pay xs[j].hs ∧
      W (j + 1) (rg .tmp) = [])
    (hcfgM : ∀ j (hj : j < bs.length),
      LayMvCfg rg (W (xs.length + (j + 1))) n B bs[j].1 bs[j].2)
    (cpM cpX : ℕ → ℕ)
    (hprepX : ∀ j < xs.length, LayLoads body rg prepX (W j) (W (j + 1)) (cpX j))
    (hprepM : ∀ j < bs.length,
      LayLoads body rg prepM (W (xs.length + j)) (W (xs.length + (j + 1))) (cpM j))
    (l : List (List (Fin (prime + Ka + 4)))) (hl : l.length = 2 ^ n)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8)
    (csM csX : List (Fin (prime + Ka + 4))) (hcsM : csM.length = bs.length)
    (hcsX : csX.length = xs.length) :
    LayRuns body (layUnapply hd pay hi hQ rg (fun _ _ h => by simpa using hrg h) hT prepM prepX)
      (layDyn rg (W 0) l.flatten csM [] csX [])
      (layDyn rg (W (xs.length + bs.length))
        (layStream K n (xs.map LayXcD.move ++ layBitMoves bs) l).flatten csM [] csX [])
      (layXcLoopCost T t₀ n K B rg W cpX xs +
        layBitCost n B cpM bs.length) := by
  have h1 := layXcLoop_exec body hd pay hi hQ hrg hT prepX (by omega : 0 < B) xs hxs W hcfgX cpX
    hprepX l hl hlB h8 csX csM [] hcsX
  set l' := layStream K n (xs.map LayXcD.move) l
  have hl' : l'.length = 2 ^ n := length_layStream _ _ _ _
  have h2 := layBitLoop_exec body hrg prepM K hB bs hbs (fun j => W (xs.length + j)) hcfgM cpM
    hprepM l' hl' (fun x hx => hlB x (mem_layStream hl hx)) csM csX [] hcsM
  simp only [Nat.add_zero] at h2
  rw [layStream_append K n _ _ l hl]
  exact h1.seq h2

end Machine

/-! ### The layout `L` of the synthetic transforms as a host machine -/

section LayoutMachine

variable (es : List ℕ) (ℓ K B : ℕ)

/-- The prefix moves of the layout as position pairs `(a, b)`. -/
def layBits : List (ℕ × ℕ) :=
  (List.range (layPre es ℓ K).length).map fun k =>
    (layPos es.sum (layPre es ℓ K) k ((layPre es ℓ K).getD k 0), es.sum - 1 - k)

/-- The chunk exchanges of the layout with their slots and headers. -/
def layXcs : List LayXcD :=
  (laySwaps (es.length * layQ ℓ K) (layTr es.length (layQ ℓ K))).map (layXcD es.sum K B)

theorem layBitMoves_layBits :
    layBitMoves (layBits es ℓ K) = layPreMoves es.sum (layPre es ℓ K) := by
  simp only [layBitMoves, layBits, layPreMoves, layPreMovesK, List.map_map]
  rfl

variable {es ℓ K}

theorem length_layBits : (layBits es ℓ K).length = (layPre es ℓ K).length := by
  simp [layBits]

theorem length_layXcs :
    (layXcs es ℓ K B).length = (laySwaps (es.length * layQ ℓ K) (layTr es.length (layQ ℓ K))).length := by
  simp [layXcs]

variable (H : LayHyp es ℓ K)
include H

theorem layBits_valid : ∀ e ∈ layBits es ℓ K, e.1 < es.sum ∧ e.2 < es.sum := by
  intro e he
  have hv := layPreMoves_valid K (layPre_nodup H) (layPre_lt H) (layPre_length_le H) (.bit e.1 e.2)
    (by rw [← layBitMoves_layBits]; exact List.mem_map.2 ⟨e, he, rfl⟩)
  exact hv

theorem layXcs_OK : ∀ d ∈ layXcs es ℓ K B, d.OK es.sum K B := by
  intro d hd
  simp only [layXcs, List.mem_map] at hd
  obtain ⟨e, he, rfl⟩ := hd
  obtain ⟨_, _, h3⟩ := laySwaps_layTr_spec (es := es) (ℓ := ℓ) (K := K)
  exact layXcD_OK (by have := lay_chunk_size H; omega) (laySwaps_layTr_three e he)
    (h3 e he).1 (h3 e he).2

theorem layXcs_valid : ∀ m ∈ (layXcs es ℓ K B).map LayXcD.move, m.Valid K es.sum := by
  intro m hm
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hm
  obtain ⟨hO, hab, _⟩ := layXcs_OK B H d hd
  exact layXc_valid hO hab

/-- The moves executed by `layApply` compose to the layout `layPerm`. -/
theorem layMovesPerm_layApply :
    layMovesPerm K es.sum (layBitMoves (layBits es ℓ K) ++ (layXcs es ℓ K B).map LayXcD.move) =
      layPerm es ℓ K := by
  rw [layPerm, layMoves, layMovesPerm_append, layMovesPerm_append, layBitMoves_layBits,
    layXcs, List.map_map, layXcMoves]
  congr 1
  obtain ⟨_, _, h3⟩ := laySwaps_layTr_spec (es := es) (ℓ := ℓ) (K := K)
  refine layMovesPerm_map_congr _ _ _ fun e he => ?_
  exact layXcD_move_perm (by have := lay_chunk_size H; omega) (laySwaps_layTr_three e he)
    (h3 e he).1 (h3 e he).2

omit H in
theorem layBitMoves_inv (bs : List (ℕ × ℕ)) :
    layMovesInv (layBitMoves bs) = layBitMoves (bs.map Prod.swap).reverse := by
  simp [layMovesInv, layBitMoves, List.map_map, List.map_reverse]
  intro _ _ _
  rfl

omit H in
theorem layXcMoves_inv (xs : List LayXcD) :
    layMovesInv (xs.map LayXcD.move) = xs.reverse.map LayXcD.move := by
  simp [layMovesInv, List.map_map, List.map_reverse]
  intro _ _
  rfl

/-- The moves executed by `layUnapply` compose to `layPerm⁻¹`. -/
theorem layMovesPerm_layUnapply :
    layMovesPerm K es.sum ((layXcs es ℓ K B).reverse.map LayXcD.move ++
      layBitMoves ((layBits es ℓ K).map Prod.swap).reverse) = (layPerm es ℓ K).symm := by
  have hv : ∀ m ∈ layBitMoves (layBits es ℓ K) ++ (layXcs es ℓ K B).map LayXcD.move,
      m.Valid K es.sum := by
    intro m hm
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
      exact layBits_valid H e he
    · exact layXcs_valid B H m hm
  have e : (layXcs es ℓ K B).reverse.map LayXcD.move ++
      layBitMoves ((layBits es ℓ K).map Prod.swap).reverse =
      layMovesInv (layBitMoves (layBits es ℓ K) ++ (layXcs es ℓ K B).map LayXcD.move) := by
    rw [← layXcMoves_inv, ← layBitMoves_inv, layMovesInv, layMovesInv, layMovesInv,
      List.map_append, List.reverse_append]
  rw [e, layMovesPerm_inv hv, layMovesPerm_layApply B H]

end LayoutMachine

section LayoutExec

variable {T Q t₀ Ka : ℕ} {U F : Type} {es : List ℕ} {ℓ K B : ℕ}

/-- **The layout `L` on a record stream.** The stream register holds the `M = 2^N` records `l`
(`N = es.sum` address bits, `B ≥ 1` symbols of value below `8` per record), the counters `cM`
and `cX` hold one symbol per prefix move and per exchange, their spares are empty, and every
left stack is empty. The loaders take the register file `W j` to `W (j + 1)`: `W (j + 1)` is
configured for prefix move `j` (`LayMvCfg`, masks of `layBits`) for `j < |layBits|`, and its bank
holds the headers of exchange `j - |layBits|` (`LayBank`) afterwards. Then `layApply` leaves
`(moveRecs (layRec (layPerm es ℓ K)) l).flatten` on the stream register: the record at address
`x` moves to the address `L x` whose bit `layPerm j` is bit `j` of `x`. -/
theorem layApply_exec (H : LayHyp es ℓ K) (body : F → Pr F T Q (prime + Ka) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q) {rg : LayReg t₀ → Fin T} (hrg : Function.Injective rg)
    (hT : swapT t₀ ≤ T) (prepM prepX : Pr F T Q (prime + Ka) U) (hB : 1 ≤ B)
    (W : ℕ → Fin T → List (Fin (prime + Ka + 4)))
    (hcfgM : ∀ j (hj : j < (layBits es ℓ K).length),
      LayMvCfg rg (W (j + 1)) es.sum B (layBits es ℓ K)[j].1 (layBits es ℓ K)[j].2)
    (hcfgX : ∀ j (hj : j < (layXcs es ℓ K B).length),
      LayBank rg (W ((layBits es ℓ K).length + (j + 1))) hd pay (layXcs es ℓ K B)[j].hs ∧
        W ((layBits es ℓ K).length + (j + 1)) (rg .tmp) = [])
    (cpM cpX : ℕ → ℕ)
    (hprepM : ∀ j < (layBits es ℓ K).length, LayLoads body rg prepM (W j) (W (j + 1)) (cpM j))
    (hprepX : ∀ j < (layXcs es ℓ K B).length, LayLoads body rg prepX
      (W ((layBits es ℓ K).length + j)) (W ((layBits es ℓ K).length + (j + 1))) (cpX j))
    (l : List (List (Fin (prime + Ka + 4)))) (hl : l.length = 2 ^ es.sum)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8)
    (csM csX : List (Fin (prime + Ka + 4))) (hcsM : csM.length = (layBits es ℓ K).length)
    (hcsX : csX.length = (layXcs es ℓ K B).length) :
    LayRuns body (layApply hd pay hi hQ rg (fun _ _ h => by simpa using hrg h) hT prepM prepX)
      (layDyn rg (W 0) l.flatten csM [] csX [])
      (layDyn rg (W ((layBits es ℓ K).length + (layXcs es ℓ K B).length))
        (moveRecs (layRec (layPerm es ℓ K)) l).flatten csM [] csX [])
      (layBitCost es.sum B cpM (layBits es ℓ K).length +
        layXcLoopCost T t₀ es.sum K B rg (fun j => W ((layBits es ℓ K).length + j)) cpX
          (layXcs es ℓ K B)) := by
  have h := layApply_exec_gen body hd pay hi hQ hrg hT prepM prepX hB (layBits es ℓ K)
    (layXcs es ℓ K B) (layBits_valid H) (layXcs_OK B H) W hcfgM hcfgX cpM cpX hprepM hprepX l hl
    hlB h8 csM csX hcsM hcsX
  rw [layStream, layMovesPerm_layApply B H] at h
  exact h

/-- **The restoring machine `L⁻¹`.** `layUnapply` runs the exchanges of the layout in reverse
order (each is its own inverse), then the prefix moves in reverse order with source and target
exchanged; with loaders configured accordingly it leaves
`(moveRecs (layRec (layPerm es ℓ K)).symm l).flatten` on the stream register. -/
theorem layUnapply_exec (H : LayHyp es ℓ K) (body : F → Pr F T Q (prime + Ka) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q) {rg : LayReg t₀ → Fin T} (hrg : Function.Injective rg)
    (hT : swapT t₀ ≤ T) (prepM prepX : Pr F T Q (prime + Ka) U) (hB : 1 ≤ B)
    (W : ℕ → Fin T → List (Fin (prime + Ka + 4)))
    (hcfgX : ∀ j (hj : j < (layXcs es ℓ K B).reverse.length),
      LayBank rg (W (j + 1)) hd pay (layXcs es ℓ K B).reverse[j].hs ∧ W (j + 1) (rg .tmp) = [])
    (hcfgM : ∀ j (hj : j < ((layBits es ℓ K).map Prod.swap).reverse.length),
      LayMvCfg rg (W ((layXcs es ℓ K B).reverse.length + (j + 1))) es.sum B
        ((layBits es ℓ K).map Prod.swap).reverse[j].1 ((layBits es ℓ K).map Prod.swap).reverse[j].2)
    (cpM cpX : ℕ → ℕ)
    (hprepX : ∀ j < (layXcs es ℓ K B).reverse.length,
      LayLoads body rg prepX (W j) (W (j + 1)) (cpX j))
    (hprepM : ∀ j < ((layBits es ℓ K).map Prod.swap).reverse.length, LayLoads body rg prepM
      (W ((layXcs es ℓ K B).reverse.length + j))
      (W ((layXcs es ℓ K B).reverse.length + (j + 1))) (cpM j))
    (l : List (List (Fin (prime + Ka + 4)))) (hl : l.length = 2 ^ es.sum)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8)
    (csM csX : List (Fin (prime + Ka + 4)))
    (hcsM : csM.length = ((layBits es ℓ K).map Prod.swap).reverse.length)
    (hcsX : csX.length = (layXcs es ℓ K B).reverse.length) :
    LayRuns body (layUnapply hd pay hi hQ rg (fun _ _ h => by simpa using hrg h) hT prepM prepX)
      (layDyn rg (W 0) l.flatten csM [] csX [])
      (layDyn rg (W ((layXcs es ℓ K B).reverse.length +
          ((layBits es ℓ K).map Prod.swap).reverse.length))
        (moveRecs (layRec (layPerm es ℓ K)).symm l).flatten csM [] csX [])
      (layXcLoopCost T t₀ es.sum K B rg W cpX (layXcs es ℓ K B).reverse +
        layBitCost es.sum B cpM ((layBits es ℓ K).map Prod.swap).reverse.length) := by
  have hbs : ∀ e ∈ ((layBits es ℓ K).map Prod.swap).reverse, e.1 < es.sum ∧ e.2 < es.sum := by
    intro e he
    simp only [List.mem_reverse, List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    exact ⟨(layBits_valid H e' he').2, (layBits_valid H e' he').1⟩
  have hxs : ∀ d ∈ (layXcs es ℓ K B).reverse, d.OK es.sum K B := fun d hd =>
    layXcs_OK B H d (List.mem_reverse.1 hd)
  have h := layUnapply_exec_gen body hd pay hi hQ hrg hT prepM prepX hB _ _ hxs hbs W hcfgX hcfgM
    cpM cpX hprepX hprepM l hl hlB h8 csM csX hcsM hcsX
  rw [layStream, layMovesPerm_layUnapply B H, layRec_symm] at h
  exact h

/-- The layout followed by the restoring machine restores the stream. -/
theorem lay_moveRecs_roundtrip {α : Type*} {N : ℕ} (P : Equiv.Perm (Fin N))
    (l : List (List α)) (hl : l.length = 2 ^ N) :
    moveRecs (layRec P).symm (moveRecs (layRec P) l) = l := by
  rw [← moveRecs_trans _ _ _ hl, Equiv.self_trans_symm]
  exact lay_moveRecs_one l hl

/-! ### Costs -/

/-- One exchange costs at most the vendored interchange bound `3 C_swap (T + 12 swapT t₀ + 5) V
max(1, K)^τ` for `V = 2^n B` stream symbols, plus `6` per bank symbol, `34 V` and
`2 T + 6 swapT t₀ + 23` (`swapCost_le`, as in `swapPass_exec_le`). -/
theorem layXcStep_le (T t₀ n K B : ℕ) (rg : LayReg t₀ → Fin T)
    (R : Fin T → List (Fin (prime + Ka + 4))) {d : LayXcD} (hd : d.OK n K B) (hB : 0 < B) :
    (layXcStep T t₀ n K B rg R d : ℝ) ≤
      3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (2 ^ n * B : ℕ) *
          ((max 1 K : ℕ) : ℝ) ^ Parameters.tau +
        (6 * ∑ j, (R (rg (.sw j))).length + 34 * (2 ^ n * B) + 2 * T + 6 * swapT t₀ + 23 : ℕ) := by
  obtain ⟨hO, hab, hh⟩ := hd
  have hp : ∀ e : ℕ, 0 < 2 ^ e := fun e => by positivity
  have hpos := swapDims_pos (layN0 n K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K d.a d.b
    (hp _) (hp _) (hp _) (hp _)
  have hC := (Classical.choose_spec swapCost_le).2
    (swapDims (layN0 n K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K d.a d.b).1
    (swapDims (layN0 n K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K d.a d.b).2.1
    ((swapDims (layN0 n K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K d.a d.b).2.2 * (3 * B))
    K K d.hs hpos.1 hpos.2.1 (Nat.mul_pos hpos.2.2 (by omega)) (Nat.le_succ K) (Nat.le_succ K)
    hh.1 hh.2
  rw [max_self, BinaryAdjacentWidthInterchange.volume,
    swapDims_vol (layN0 n K d.o) (layN1 K d.o) (layN2 K d.o) (layN3 d.o) K d.a d.b hab (3 * B),
    lay_rectSize hO] at hC
  have hvol : ((2 ^ n * (3 * B) : ℕ) : ℝ) = 3 * ((2 ^ n * B : ℕ) : ℝ) := by push_cast; ring
  rw [hvol] at hC
  exact cast_time_bound (le_of_eq (by simp only [layXcStep, layXcCost, layXcDims]; ring)) hC

theorem lay_loop_sum_le (f : ℕ → ℕ) (c n : ℕ) (hf : ∀ j < n, f j ≤ c) :
    ∑ j ∈ Finset.range n, (f j + 3) + 2 * n + 4 ≤ n * (c + 5) + 4 := by
  have : ∑ j ∈ Finset.range n, (f j + 3) ≤ ∑ _j ∈ Finset.range n, (c + 3) :=
    Finset.sum_le_sum fun j hj => by have := hf j (Finset.mem_range.1 hj); omega
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
  nlinarith

/-- **The cost of `layApply`.** With loaders of at most `cM` and `cX` steps and exchanges of at
most `X` steps each, the layout costs at most
`D (b + 1) (cM + layMvCost N B + 5) + (D q - 1) (cX + X + 5) + 8` steps, where
`layMvCost N B = 2^N (18 B + 20 N + 36) + 8 N + 26` and `X` is bounded by `layXcStep_le`:
`O(V (D K + D q K^τ))` for `V = 2^N B` stream symbols when `N ≤ B`, the loaders aside. -/
theorem layApply_cost_le (T t₀ : ℕ) (rg : LayReg t₀ → Fin T)
    (W : ℕ → Fin T → List (Fin (prime + Ka + 4))) (cpM cpX : ℕ → ℕ) (cM cX X : ℕ)
    (hM : ∀ j, cpM j ≤ cM) (hX : ∀ j, cpX j ≤ cX)
    (hXs : ∀ j < (layXcs es ℓ K B).length,
      layXcStep T t₀ es.sum K B rg (W (j + 1)) ((layXcs es ℓ K B).getD j default) ≤ X) :
    layBitCost es.sum B cpM (layBits es ℓ K).length +
        layXcLoopCost T t₀ es.sum K B rg W cpX (layXcs es ℓ K B) ≤
      es.length * (layB ℓ K + 1) * (cM + layMvCost es.sum B + 5) +
        (es.length * layQ ℓ K - 1) * (cX + X + 5) + 8 := by
  obtain ⟨c1, c2⟩ := layMoves_counts (es := es) (ℓ := ℓ) (K := K)
  rw [layPreMoves, layPreMovesK, List.length_map, List.length_range] at c1
  have e1 := lay_loop_sum_le (fun j => cpM j + layMvCost es.sum B) (cM + layMvCost es.sum B)
    (layBits es ℓ K).length (fun j _ => by have := hM j; omega)
  have e2 := lay_loop_sum_le (fun j => cpX j + layXcStep T t₀ es.sum K B rg (W (j + 1))
    ((layXcs es ℓ K B).getD j default)) (cX + X) (layXcs es ℓ K B).length
    (fun j hj => by have := hX j; have := hXs j hj; omega)
  rw [length_layBits] at e1
  rw [length_layXcs] at e2
  have f1 : (layPre es ℓ K).length * (cM + layMvCost es.sum B + 5) ≤
      es.length * (layB ℓ K + 1) * (cM + layMvCost es.sum B + 5) := Nat.mul_le_mul_right _ c1
  have f2 : (laySwaps (es.length * layQ ℓ K) (layTr es.length (layQ ℓ K))).length * (cX + X + 5) ≤
      (es.length * layQ ℓ K - 1) * (cX + X + 5) := Nat.mul_le_mul_right _ c2
  unfold layBitCost layXcLoopCost
  rw [length_layBits, length_layXcs]
  omega

end LayoutExec

end IntegerMultBounds.MathlibTM2.Fast
