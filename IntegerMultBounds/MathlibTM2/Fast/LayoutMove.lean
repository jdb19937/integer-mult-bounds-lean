module

public import IntegerMultBounds.MathlibTM2.Fast.LayoutMath
public import IntegerMultBounds.MathlibTM2.Node.FixPass
public import IntegerMultBounds.MathlibTM2.Node.SwapPass

/-!
# The two moves of the layout on record streams

Paper §6, proof of `lem:synthetic-transform-cost`: the single-bit moves of
`lem:elementary-streams` and the chunk interchanges of `lem:chunk-swap` on a stream of `2^n`
records, record `x` at address `x`. A move with bit permutation `P` of the address bits moves the
record at address `x` to `layRec P x` (`IntegerMultBounds.MathlibTM2.Fast.LayoutMath`): the stream `l` becomes
`moveRecs (layRec P) l`.

**Registers.** `rg : LayReg t₀ → Fin T`, injective: the stream `str`, the route and merge
registers `r0`–`r3`, `q0`–`q3`, the record-length counter `ctrB`, the record counter `cnt`, the
spare `tmp`, the scan slot `st`, the index field `fld`, the masks `mA`, `mB`, the code-pass spares
`us r`, the interchange bank `sw j`, and the loop counters `cM`, `tM`, `cX`, `tX` of
`IntegerMultBounds.MathlibTM2.Fast.Layout`.

**The single-bit move** `layMoveBit rg` is the route-and-merge machine `fixAt` of
`IntegerMultBounds.MathlibTM2.Node.FixPass` with the code automata `layCodeAuto A 1`, `layCodeAuto A 2`: route the
records by bit `a` of their index (read in the column where the mask `mA = 2^a` is set),
restore forward order, merge by bit `b` of the output index (mask `mB = 2^b`). The records
keep their order within each value of bit `a`, and the single-bit move `layBitPerm n a b`
keeps the order of the records with a common bit `a` (`layRecVal_lt_of`), so the merge moves
the records by `layRec (layBitPerm n a b)` (`lay_merge_bit`, from `mergeIdxList_moveRecs`).
`layMoveBit_exec`: with the register file `LayMvCfg` (`ctrB` holding `B` symbols, `cnt` holding
`2^n` symbols, `fld = 0`, the masks, the route and merge registers empty), the stream ends as
`(moveRecs (layRec (layBitPerm n a b)) l).flatten` and every other register is unchanged, within
`layMvCost n B = 2^n (18 B + 20 n + 36) + 8 n + 26` steps.

**The chunk exchange** `layXchg` is the field-swap pass `swapPass` of `IntegerMultBounds.MathlibTM2.Node.SwapPass`.
Three `K`-bit chunk slots at offsets `o 0 > o 1 > o 2` (`LayXcOK`) cut the address into the
rectangle `[N₀] × [2^K] × [N₁] × [2^K] × [N₂] × [2^K] × [N₃]` (`layN0`–`layN3`, all powers of two,
`lay_rectSize`). On it the instruction `swap a b` is the exchange of the chunks at `o a` and
`o b` (`lay_rank_swap`, through the bits of a rank `lay_testBit_rank`; `lay_moveRecs_swap`).
`layXchg_exec`: with the bank holding canonical headers of the interchange dimensions
`layXcDims` (`LayBank`, `LayHdr`), the stream ends as
`(moveRecs (layRec ((LayMove.xc (o a) (o b)).perm K n)) l).flatten`, within `layXcCost`: the
vendored interchange term `(T + 12 swapT t₀ + 5) · BinaryInterchangeRun.cost` of
`swapPass_exec`, plus `6` per bank symbol, `34` per stream symbol and `2 T + 6 swapT t₀ + 23`.
`layXchg_exec_le` bounds the interchange term by `3 C_swap (T + 12 swapT t₀ + 5) 2^n B
max(1, K)^τ` (`swapPass_exec_le`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer.PackedXor
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false

/-! ### Registers -/

/-- The registers of the layout machine: the stream `str`; the route, merge and counter
registers of the single-bit move (`r0`–`r3`, `q0`–`q3`, `ctrB`, `cnt`, `tmp`, the scan slot `st`,
the index field `fld`, the masks `mA`, `mB`, the code-pass spares `us r`); the interchange bank
`sw j`; the loop counters `cM`, `cX` with their spares `tM`, `tX`. -/
inductive LayReg (t₀ : ℕ)
  | str | r0 | r1 | r2 | r3 | q0 | q1 | q2 | q3 | ctrB | cnt | tmp | st | fld | mA | mB
  | us (r : Fin 3)
  | sw (j : Fin (swapT t₀))
  | cM | tM | cX | tX

/-! ### The code automata of a single-bit move -/

/-- The code automaton reading, in the column marked by the mask register `sel`, the bit of the
index field (register `0`): code `1` if that bit is set, `0` otherwise. -/
def layCodeAuto (A : ℕ) (sel : Fin 3) : CAuto A 3 4 :=
  absAuto (fun b : Bool => (⟨b.toNat, by cases b <;> simp⟩ : Fin (A + 4)))
    (fun x => decide (x.val = 1)) false (fun s col => if col sel then col 0 else s)
    (fun s => ⟨s.toNat, by cases s <;> decide⟩)

theorem lay_foldl_code (sel : Fin 3) (vals : Fin 3 → ℕ) {p : ℕ} (hs : vals sel = 2 ^ p) :
    ∀ L : ℕ, (List.range L).foldl
        (fun s t => if (vals sel).testBit t then (vals 0).testBit t else s) false =
      (decide (p < L) && (vals 0).testBit p) := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, hs, Nat.testBit_two_pow]
      by_cases hpL : p = L
      · subst hpL; simp
      · have h1 : decide (p < L + 1) = decide (p < L) := by
          apply decide_eq_decide.2; omega
        simp only [hpL, decide_false, Bool.false_eq_true, ↓reduceIte, h1]

theorem layCode_eval {A : ℕ} (sel : Fin 3) (L : ℕ) (vals : Fin 3 → ℕ) {p : ℕ}
    (hs : vals sel = 2 ^ p) (hp : p < L) :
    (layCodeAuto A sel).eval L vals = ⟨((vals 0).testBit p).toNat, by cases (vals 0).testBit p <;> decide⟩ := by
  unfold layCodeAuto
  rw [absAuto_eval _ _ (fun b => by cases b <;> simp), lay_foldl_code sel vals hs L]
  simp [hp]

/-- The code-pass sources of the move from bit `a` to bit `b`: the index field and the masks
`2^a` and `2^b`. -/
def layRsrc (a b : ℕ) : Fin 3 → Fin 1 ⊕ ℕ := ![.inl 0, .inr (2 ^ a), .inr (2 ^ b)]

theorem lay_regVal (n a b i : ℕ) :
    regVal (fun _ : Fin 1 => n) (layRsrc a b) i = ![i % 2 ^ n, 2 ^ a, 2 ^ b] := by
  funext r
  fin_cases r
  · simp [regVal, layRsrc, digit, fieldOff_zero _ (0 : Fin 1) rfl]
  · simp [regVal, layRsrc]
  · simp [regVal, layRsrc]

theorem layIdxCode_in {A n a : ℕ} (b : ℕ) (ha : a < n) (i : ℕ) :
    idxCode (layCodeAuto A 1) n (fun _ : Fin 1 => n) (layRsrc a b) i =
      ⟨(i.testBit a).toNat, by cases i.testBit a <;> decide⟩ := by
  rw [idxCode, lay_regVal, layCode_eval 1 n _ (p := a) rfl ha]
  simp [Nat.testBit_mod_two_pow, ha]

theorem layIdxCode_out {A n b : ℕ} (a : ℕ) (hb : b < n) (i : ℕ) :
    idxCode (layCodeAuto A 2) n (fun _ : Fin 1 => n) (layRsrc a b) i =
      ⟨(i.testBit b).toNat, by cases i.testBit b <;> decide⟩ := by
  rw [idxCode, lay_regVal, layCode_eval 2 n _ (p := b) rfl hb]
  simp [Nat.testBit_mod_two_pow, hb]

/-! ### The single-bit move on record streams -/

/-- The bit permutation of the move from position `a` to position `b` of an `n`-bit address. -/
def layBitPerm (n a b : ℕ) : Equiv.Perm (Fin n) := (LayMove.bit a b).perm 0 n

theorem layBitPerm_apply {n a b : ℕ} (ha : a < n) (hb : b < n) (x : Fin n) :
    (layBitPerm n a b x : ℕ) = layMvFun a b x :=
  LayMove.perm_apply (K := 0) (m := .bit a b) ⟨ha, hb⟩ x

/-- Routing by bit `a` and merging by bit `b` moves the records as the single-bit move: the
merged stream is the stream moved by `layRec (layBitPerm n a b)`. -/
theorem lay_merge_bit {α : Type} {n a b B : ℕ} (A : ℕ) (ha : a < n) (hb : b < n)
    (l : List (List α)) (hl : l.length = 2 ^ n) (hlB : ∀ r ∈ l, r.length = B) :
    mergeIdxList B (idxCode (layCodeAuto A 2) n (fun _ : Fin 1 => n) (layRsrc a b)) (2 ^ n) 0
        (fun d => blocksIdx l.flatten B (2 ^ n)
          (idxCode (layCodeAuto A 1) n (fun _ : Fin 1 => n) (layRsrc a b)) 0 d ++ []) =
      ((moveRecs (layRec (layBitPerm n a b)) l).flatten, fun _ => []) ∧
    ∀ d, idxCount (idxCode (layCodeAuto A 2) n (fun _ : Fin 1 => n) (layRsrc a b)) 0 (2 ^ n) d =
      idxCount (idxCode (layCodeAuto A 1) n (fun _ : Fin 1 => n) (layRsrc a b)) 0 (2 ^ n) d := by
  set π := layRec (layBitPerm n a b)
  have hPa : layBitPerm n a b ⟨a, ha⟩ = ⟨b, hb⟩ :=
    Fin.ext (by rw [layBitPerm_apply ha hb]; exact layMvFun_self a b)
  have hcode : ∀ i : Fin (2 ^ n),
      idxCode (layCodeAuto A 2) n (fun _ : Fin 1 => n) (layRsrc a b) (π i) =
        idxCode (layCodeAuto A 1) n (fun _ : Fin 1 => n) (layRsrc a b) i := by
    intro i
    rw [layIdxCode_in b ha, layIdxCode_out a hb]
    apply Fin.ext
    show ((layRecVal (layBitPerm n a b) i).testBit b).toNat = ((i : ℕ).testBit a).toNat
    have := testBit_layRecVal_apply (layBitPerm n a b) i ⟨a, ha⟩
    rw [hPa] at this
    rw [this]
  refine ⟨mergeIdxList_moveRecs π l hl hlB _ _ hcode ?_, idxCount_perm π _ _ hcode⟩
  intro i i' hc hii
  rw [layIdxCode_in b ha, layIdxCode_in b ha] at hc
  have hc' : (i : ℕ).testBit a = (i' : ℕ).testBit a := by
    have := congrArg Fin.val hc
    simp only at this
    revert this
    cases (i : ℕ).testBit a <;> cases (i' : ℕ).testBit a <;> simp
  show layRecVal (layBitPerm n a b) i < layRecVal (layBitPerm n a b) i'
  refine layRecVal_lt_of (a := ⟨a, ha⟩) ?_ hii i'.isLt hc'
  intro x y hxy hx hy
  rw [Fin.lt_def, layBitPerm_apply ha hb, layBitPerm_apply ha hb]
  exact layMvFun_lt_lt hxy (fun e => hx (Fin.ext e)) (fun e => hy (Fin.ext e))

/-! ### The single-bit move pass -/

section MoveBit

variable {T Q A t₀ : ℕ} {U P : Type}

/-- **The single-bit move pass**: route the records of `str` by bit `a` of their index into
`r0`, `r1`, restore forward order into `q0`, `q1`, merge by bit `b` of the output index, move the
result back into `str` (`fixAt` with the code automata `layCodeAuto A 1`, `layCodeAuto A 2`). The
positions `a`, `b` are read from the masks `mA = 2^a`, `mB = 2^b`, so the program does not depend
on them. -/
def layMoveBit (rg : LayReg t₀ → Fin T) : Pr P T Q A U :=
  fixAt (rg .str) (rg .r0) (rg .r1) (rg .r2) (rg .r3) (rg .q0) (rg .q1) (rg .q2) (rg .q3)
    (rg .ctrB) (rg .cnt) (rg .tmp) (rg .st) (fun _ : Fin 1 => rg .fld) ![rg .fld, rg .mA, rg .mB]
    (fun r => rg (.us r)) (layCodeAuto A 1) (layCodeAuto A 2)

theorem layIdxLayout {rg : LayReg t₀ → Fin T} (hrg : Function.Injective rg) (n a b : ℕ)
    (X : Fin T → Prop)
    (hX : ∀ k, X k → k ≠ rg .fld ∧ k ≠ rg .mA ∧ k ≠ rg .mB ∧ ∀ r, k ≠ rg (.us r)) :
    IdxLayout (fun _ : Fin 1 => rg .fld) (fun _ => n) n ![rg .fld, rg .mA, rg .mB]
      (fun r => rg (.us r)) (layRsrc a b) (rg .st) X where
  rs_inj := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [hrg.eq_iff]
  tmps_inj := by
    intro r r' h
    have := hrg h
    simpa using this
  rs_tmps := by
    intro r r'
    fin_cases r <;> simp [hrg.eq_iff]
  rs_st := by
    intro r
    fin_cases r <;> simp [hrg.eq_iff]
  tmps_st := by
    intro r
    simp [hrg.eq_iff]
  cf_inj := fun f g _ => Subsingleton.elim f g
  tmps_cf := by
    intro r f
    simp [hrg.eq_iff]
  field := by
    intro r f hr
    fin_cases r
    · exact ⟨rfl, rfl⟩
    · simp [layRsrc] at hr
    · simp [layRsrc] at hr
  param := by
    intro r p f hr
    fin_cases r
    · simp [layRsrc] at hr
    · simp [hrg.eq_iff]
    · simp [hrg.eq_iff]
  cf_X := fun f hx => (hX _ hx).1 rfl
  rs_X := by
    intro r hx
    have := hX _ hx
    fin_cases r
    · exact this.1 rfl
    · exact this.2.1 rfl
    · exact this.2.2.1 rfl
  tmps_X := fun r hx => (hX _ hx).2.2.2 r rfl

theorem layFixLayout {rg : LayReg t₀ → Fin T} (hrg : Function.Injective rg) (n a b : ℕ) :
    FixLayout (rg .str) (rg .r0) (rg .r1) (rg .r2) (rg .r3) (rg .q0) (rg .q1) (rg .q2) (rg .q3)
      (rg .ctrB) (rg .cnt) (rg .tmp) (rg .st) (fun _ : Fin 1 => rg .fld) (fun _ => n) n
      ![rg .fld, rg .mA, rg .mB] (fun r => rg (.us r)) (layRsrc a b) where
  route := layIdxLayout hrg n a b _ (by
    intro k hk
    simp only [routeRegs] at hk
    rcases hk with rfl | rfl | rfl | ⟨d, rfl⟩
    · simp [hrg.eq_iff]
    · simp [hrg.eq_iff]
    · simp [hrg.eq_iff]
    · fin_cases d <;> simp [hrg.eq_iff])
  merge := layIdxLayout hrg n a b _ (by
    intro k hk
    simp only [mergeRegs] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | ⟨d, rfl⟩
    · simp [hrg.eq_iff]
    · simp [hrg.eq_iff]
    · simp [hrg.eq_iff]
    · simp [hrg.eq_iff]
    · simp [hrg.eq_iff]
    · fin_cases d <;> simp [hrg.eq_iff])
  regs := by
    have e : [rg .str, rg .r0, rg .r1, rg .r2, rg .r3, rg .q0, rg .q1, rg .q2, rg .q3, rg .ctrB,
        rg .cnt, rg .tmp] = [LayReg.str, .r0, .r1, .r2, .r3, .q0, .q1, .q2, .q3, .ctrB, .cnt,
        .tmp].map rg := rfl
    rw [e]
    exact List.Nodup.map hrg (by simp)
  cf_regs := by
    intro f
    simp [hrg.eq_iff]
  us_regs := by
    intro r
    simp [hrg.eq_iff]

/-- The register file of a single-bit move from bit `a` to bit `b` of an `n`-bit address, for
records of `B` symbols: the route and merge registers and `tmp` empty, `ctrB` holding `B`
symbols, `cnt` holding `2^n` symbols, the index field `fld` at `0` (`binSyms n 0`), the masks
`mA = binSyms n (2^a)` and `mB = binSyms n (2^b)`, and the code-pass spares empty. -/
structure LayMvCfg (rg : LayReg t₀ → Fin T) (R : Fin T → List (Fin (A + 4))) (n B a b : ℕ) :
    Prop where
  r0 : R (rg .r0) = []
  r1 : R (rg .r1) = []
  r2 : R (rg .r2) = []
  r3 : R (rg .r3) = []
  q0 : R (rg .q0) = []
  q1 : R (rg .q1) = []
  q2 : R (rg .q2) = []
  q3 : R (rg .q3) = []
  tmp : R (rg .tmp) = []
  ctrB : (R (rg .ctrB)).length = B
  cnt : (R (rg .cnt)).length = 2 ^ n
  fld : R (rg .fld) = binSyms n 0
  mA : R (rg .mA) = binSyms n (2 ^ a)
  mB : R (rg .mB) = binSyms n (2 ^ b)
  us : ∀ r, R (rg (.us r)) = []

/-- The step bound of one single-bit move on `2^n` records of `B` symbols. -/
def layMvCost (n B : ℕ) : ℕ := 2 ^ n * (18 * B + 20 * n + 36) + 8 * n + 26

/-- **The single-bit move.** The stream register holds `l.flatten`, `2^n` records of `B ≥ 1`
symbols, and the register file is configured for the move from bit `a` to bit `b`
(`LayMvCfg`). Afterwards the stream register holds the records moved by the single-bit move:
`(moveRecs (layRec (layBitPerm n a b)) l).flatten` (the record at address `x` goes to the address
whose bit `layMvFun a b j` is bit `j` of `x`), and every other register is unchanged. At most
`layMvCost n B = 2^n (18 B + 20 n + 36) + 8 n + 26` steps: `O(V + M n)` for `V = M B` stream
symbols and `M = 2^n` records. -/
theorem layMoveBit_exec (body : P → Pr P T Q A U) {rg : LayReg t₀ → Fin T}
    (hrg : Function.Injective rg) {n B a b : ℕ} (ha : a < n) (hb : b < n) (hB : 1 ≤ B)
    (l : List (List (Fin (A + 4)))) (hl : l.length = 2 ^ n) (hlB : ∀ r ∈ l, r.length = B)
    (v : HS T Q A U) (S : Stacks T A) (hS : S.R (rg .str) = l.flatten)
    (hcfg : LayMvCfg rg S.R n B a b) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ layMvCost n B ∧
      Exec body (layMoveBit rg) (mk v S) m
        (mk v' { S with
          R := Function.update S.R (rg .str) (moveRecs (layRec (layBitPerm n a b)) l).flatten }) := by
  obtain ⟨hmerge, hcount⟩ := lay_merge_bit A ha hb l hl hlB
  have hlen : (moveRecs (layRec (layBitPerm n a b)) l).flatten.length = 2 ^ n * B := by
    rw [length_flatten_of_length _ (fun r hr => hlB r (mem_moveRecs _ hl hr)), length_moveRecs]
  have hI : IdxState (fun _ : Fin 1 => rg .fld) (fun _ => n) n ![rg .fld, rg .mA, rg .mB]
      (fun r => rg (.us r)) (layRsrc a b) S.R 0 := by
    refine ⟨fun f => ?_, fun r p hr => ?_, fun r => hcfg.us r⟩
    · rw [hcfg.fld]; simp [digit]
    · fin_cases r
      · simp [layRsrc] at hr
      · simp only [layRsrc] at hr
        simp at hr
        subst hr
        exact hcfg.mA
      · simp only [layRsrc] at hr
        simp at hr
        subst hr
        exact hcfg.mB
  obtain ⟨v', m, hu, hm, he⟩ := fixAt_exec body (layFixLayout hrg n a b) (layCodeAuto A 1)
    (layCodeAuto A 2) hB l hl hlB hcount _ hlen hmerge v S hS hcfg.r0 hcfg.r1 hcfg.r2 hcfg.r3
    hcfg.q0 hcfg.q1 hcfg.q2 hcfg.q3 hcfg.ctrB hcfg.cnt hcfg.tmp hI
  refine ⟨v', m, hu, ?_, he⟩
  refine hm.trans (le_of_eq ?_)
  simp only [Finset.univ_unique, Finset.sum_singleton, layMvCost]
  ring

end MoveBit

/-! ### Chunk exchanges on the rectangle of the field-swap pass -/

section XcRank

variable {n K : ℕ} {o : Fin 3 → ℕ}

/-- Three `K`-bit chunk slots at bit offsets `o 0 > o 1 > o 2` of an `n`-bit address. -/
structure LayXcOK (n K : ℕ) (o : Fin 3 → ℕ) : Prop where
  h21 : o 2 + K ≤ o 1
  h10 : o 1 + K ≤ o 0
  h0 : o 0 + K ≤ n

/-- The rectangle `[N₀] × [2^K] × [N₁] × [2^K] × [N₂] × [2^K] × [N₃]` of the three chunk slots: the
spectator blocks are the address bits above, between and below the slots. -/
def layN0 (n K : ℕ) (o : Fin 3 → ℕ) : ℕ := 2 ^ (n - (o 0 + K))
def layN1 (K : ℕ) (o : Fin 3 → ℕ) : ℕ := 2 ^ (o 0 - (o 1 + K))
def layN2 (K : ℕ) (o : Fin 3 → ℕ) : ℕ := 2 ^ (o 1 - (o 2 + K))
def layN3 (o : Fin 3 → ℕ) : ℕ := 2 ^ (o 2)

theorem lay_rectSize (hO : LayXcOK n K o) :
    rectSize (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o) K = 2 ^ n := by
  have h21 := hO.h21
  have h10 := hO.h10
  have h0 := hO.h0
  simp only [rectSize, layN0, layN1, layN2, layN3, ← pow_add]
  congr 1
  omega

theorem lay_tb {z w : ℕ} (Y : ℕ) (hz : z < 2 ^ w) (j : ℕ) :
    (z + 2 ^ w * Y).testBit j = if j < w then z.testBit j else Y.testBit (j - w) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add Y hz]

/-- The bits of a rank: the seven fields from the bottom. -/
theorem lay_testBit_rank (hO : LayXcOK n K o)
    (p : Addr (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o) K) (j : ℕ) :
    (rank _ _ _ _ K p).testBit j =
      if j < o 2 then (p.1.2.2.2 : ℕ).testBit j
      else if j < o 2 + K then (p.2 2 : ℕ).testBit (j - o 2)
      else if j < o 1 then (p.1.2.2.1 : ℕ).testBit (j - (o 2 + K))
      else if j < o 1 + K then (p.2 1 : ℕ).testBit (j - o 1)
      else if j < o 0 then (p.1.2.1 : ℕ).testBit (j - (o 1 + K))
      else if j < o 0 + K then (p.2 0 : ℕ).testBit (j - o 0)
      else (p.1.1 : ℕ).testBit (j - (o 0 + K)) := by
  have h21 := hO.h21
  have h10 := hO.h10
  obtain ⟨⟨s₀, s₁, s₂, s₃⟩, c⟩ := p
  have e3 : (s₃ : ℕ) < 2 ^ (o 2) := s₃.isLt
  have e2 : (s₂ : ℕ) < 2 ^ (o 1 - (o 2 + K)) := s₂.isLt
  have e1 : (s₁ : ℕ) < 2 ^ (o 0 - (o 1 + K)) := s₁.isLt
  have c2 : ((c 2 : Fin (2 ^ K)) : ℕ) < 2 ^ K := (c 2).isLt
  have c1 : ((c 1 : Fin (2 ^ K)) : ℕ) < 2 ^ K := (c 1).isLt
  have c0 : ((c 0 : Fin (2 ^ K)) : ℕ) < 2 ^ K := (c 0).isLt
  show ((s₃ : ℕ) + 2 ^ (o 2) * (((c 2 : Fin (2 ^ K)) : ℕ) + 2 ^ K * ((s₂ : ℕ) +
    2 ^ (o 1 - (o 2 + K)) * (((c 1 : Fin (2 ^ K)) : ℕ) + 2 ^ K * ((s₁ : ℕ) +
    2 ^ (o 0 - (o 1 + K)) * (((c 0 : Fin (2 ^ K)) : ℕ) + 2 ^ K * (s₀ : ℕ))))))).testBit j = _
  rw [lay_tb _ e3, lay_tb _ c2, lay_tb _ e2, lay_tb _ c1, lay_tb _ e1, lay_tb _ c0]
  simp only
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

/-- Chunk slot `k` of a rank holds the chunk value `p.2 k`. -/
theorem lay_testBit_rank_chunk (hO : LayXcOK n K o)
    (p : Addr (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o) K) {k : Fin 3} {j : ℕ}
    (hj : o k ≤ j ∧ j < o k + K) : (rank _ _ _ _ K p).testBit j = (p.2 k : ℕ).testBit (j - o k) := by
  have h21 := hO.h21
  have h10 := hO.h10
  rw [lay_testBit_rank hO]
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hj ⊢ <;>
    split_ifs <;> first | rfl | (exfalso; omega)

/-- Off the chunk slots a rank does not depend on the chunk values. -/
theorem lay_testBit_rank_off (hO : LayXcOK n K o)
    (s : Spec (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o)) (c c' : Tri K) {j : ℕ}
    (hj : ∀ k : Fin 3, ¬ (o k ≤ j ∧ j < o k + K)) :
    (rank _ _ _ _ K (s, c)).testBit j = (rank _ _ _ _ K (s, c')).testBit j := by
  have h21 := hO.h21
  have h10 := hO.h10
  have j0 := hj 0
  have j1 := hj 1
  have j2 := hj 2
  rw [lay_testBit_rank hO, lay_testBit_rank hO]
  simp only at j0 j1 j2 ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The exchange of the chunk slots `a ≠ b` as a move. -/
theorem layXc_valid (hO : LayXcOK n K o) {a b : Fin 3} (hab : a ≠ b) :
    (LayMove.xc (o a) (o b)).Valid K n := by
  have h21 := hO.h21
  have h10 := hO.h10
  have h0 := hO.h0
  show o a + K ≤ n ∧ o b + K ≤ n ∧ (o a + K ≤ o b ∨ o b + K ≤ o a)
  fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega

theorem layXcFun_slot (hO : LayXcOK n K o) {a b : Fin 3} (hab : a ≠ b) {k : Fin 3} {j : ℕ}
    (hj : o k ≤ j ∧ j < o k + K) :
    layXcFun K (o a) (o b) j = j - o k + o (Equiv.swap a b k) := by
  have h21 := hO.h21
  have h10 := hO.h10
  unfold layXcFun
  fin_cases a <;> fin_cases b <;> fin_cases k <;> simp [Equiv.swap_apply_def] at hab hj ⊢ <;>
    split_ifs <;> omega

theorem layXcFun_off {a b : Fin 3} {j : ℕ} (hj : ∀ k : Fin 3, ¬ (o k ≤ j ∧ j < o k + K)) :
    layXcFun K (o a) (o b) j = j := by
  unfold layXcFun
  simp only [hj a, hj b, ↓reduceIte]

/-- **The field swap as a chunk exchange.** On the rectangle of three chunk slots at offsets
`o`, the instruction `swap a b` moves the record at address `x` to the address with the chunks at
`o a` and `o b` exchanged. -/
theorem lay_rank_swap (hO : LayXcOK n K o) {a b : Fin 3} (hab : a ≠ b)
    (p : Addr (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o) K) :
    rank _ _ _ _ K (p.1, p.2 ∘ Equiv.swap a b) =
      layRecVal ((LayMove.xc (o a) (o b)).perm K n) (rank _ _ _ _ K p) := by
  have hv := layXc_valid hO hab
  have hlt : ∀ q : Addr (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o) K,
      rank _ _ _ _ K q < 2 ^ n := by
    intro q
    rw [← rankEquiv_val, ← lay_rectSize hO]
    exact (rankEquiv _ _ _ _ K q).isLt
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_layRecVal]
  split_ifs with hjn
  · have hsymm : ((LayMove.xc (o a) (o b)).perm K n).symm ⟨j, hjn⟩ =
        (LayMove.xc (o a) (o b)).perm K n ⟨j, hjn⟩ := by
      rw [← LayMove.perm_inv hv]; rfl
    rw [hsymm]
    have hval : (((LayMove.xc (o a) (o b)).perm K n ⟨j, hjn⟩ : Fin n) : ℕ) =
        layXcFun K (o a) (o b) j := LayMove.perm_apply hv _
    rw [hval]
    by_cases hk : ∃ k : Fin 3, o k ≤ j ∧ j < o k + K
    · obtain ⟨k, hk⟩ := hk
      rw [lay_testBit_rank_chunk hO _ hk, layXcFun_slot hO hab hk]
      have hk' : o (Equiv.swap a b k) ≤ j - o k + o (Equiv.swap a b k) ∧
          j - o k + o (Equiv.swap a b k) < o (Equiv.swap a b k) + K := by omega
      rw [lay_testBit_rank_chunk hO _ hk',
        show j - o k + o (Equiv.swap a b k) - o (Equiv.swap a b k) = j - o k by omega]
      rfl
    · simp only [not_exists, not_and, not_lt] at hk
      have hk' : ∀ k : Fin 3, ¬ (o k ≤ j ∧ j < o k + K) := fun k h => by
        have := hk k h.1; omega
      rw [layXcFun_off hk']
      exact lay_testBit_rank_off hO _ _ _ hk'
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hlt _) (Nat.pow_le_pow_right (by norm_num)
      (by omega)))

/-- Two permutations of record positions with the same values move a stream the same way. -/
theorem lay_moveRecs_congr {α : Type*} {M M' : ℕ} (π : Equiv.Perm (Fin M))
    (π' : Equiv.Perm (Fin M')) (hM : M = M')
    (h : ∀ (x : ℕ) (hx : x < M) (hx' : x < M'), (π ⟨x, hx⟩ : ℕ) = π' ⟨x, hx'⟩)
    (l : List (List α)) : moveRecs π l = moveRecs π' l := by
  have hs : ∀ (x : ℕ) (hx : x < M) (hx' : x < M'), (π.symm ⟨x, hx⟩ : ℕ) = π'.symm ⟨x, hx'⟩ := by
    intro x hx hx'
    have hy' : ((π.symm ⟨x, hx⟩ : Fin M) : ℕ) < M' := hM ▸ (π.symm ⟨x, hx⟩).isLt
    have e1 := h (π.symm ⟨x, hx⟩) (π.symm ⟨x, hx⟩).isLt hy'
    have e0 : π ⟨(π.symm ⟨x, hx⟩ : ℕ), (π.symm ⟨x, hx⟩).isLt⟩ = ⟨x, hx⟩ := by
      simp
    rw [e0] at e1
    have e2 : π' ⟨(π.symm ⟨x, hx⟩ : ℕ), hy'⟩ = ⟨x, hx'⟩ := Fin.ext (by rw [← e1])
    rw [← e2, Equiv.symm_apply_apply]
  apply List.ext_getElem (by simp [length_moveRecs, hM])
  intro j h1 h2
  simp only [moveRecs, List.getElem_ofFn]
  rw [hs j (by simpa [length_moveRecs] using h1) (by simpa [length_moveRecs] using h2)]

/-- The rank permutation of `swap a b` on the rectangle of the chunk slots `o` moves a stream as
the chunk exchange of `o a` and `o b`. -/
theorem lay_moveRecs_swap {α : Type*} (hO : LayXcOK n K o) {a b : Fin 3} (hab : a ≠ b)
    (Kc ρ n' : ℕ) (l : List (List α)) :
    moveRecs (rankPerm (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o) K Kc ρ n' [.swap a b]) l =
      moveRecs (layRec ((LayMove.xc (o a) (o b)).perm K n)) l := by
  apply lay_moveRecs_congr _ _ (lay_rectSize hO)
  intro x hx hx'
  set p := (rankEquiv (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o) K).symm ⟨x, hx⟩ with hp
  have hxp : (⟨x, hx⟩ : Fin _) = rankEquiv _ _ _ _ K p := by rw [hp, Equiv.apply_symm_apply]
  have hxr : x = rank _ _ _ _ K p := by
    have := congrArg Fin.val hxp
    rw [rankEquiv_val] at this
    exact this
  rw [hxp, rankPerm_swap, rankEquiv_val, lay_rank_swap hO hab, layRec_val]
  simp only
  rw [← hxr]

end XcRank

/-! ### The chunk exchange pass -/

section Xchg

variable {T Q Ka t₀ : ℕ} {U F : Type}

/-- **The chunk exchange pass**: the field-swap pass `swapPass` on the stream register `str`
(spare `tmp`) with the interchange bank `sw`. The interchange dimensions are read from the five
header registers of the bank, so the program does not depend on the exchanged chunks. -/
noncomputable def layXchg (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q) (rg : LayReg t₀ → Fin T)
    (hsw : Function.Injective fun j => rg (.sw j)) (hT : swapT t₀ ≤ T) :
    Pr F T Q (prime + Ka) U :=
  swapPass hd pay hi hQ (fun j => rg (.sw j)) hsw hT (rg .str) (rg .tmp)

/-- The interchange dimensions `(P, G, B')` of the exchange of the chunk slots `a`, `b` at
offsets `o`, records of `B` symbols (`3 B` bits): the layout `[P] × [2^K] × [G] × [2^K] × [B']`
of the vendored interchange. -/
def layXcDims (n K : ℕ) (o : Fin 3 → ℕ) (a b : Fin 3) (B : ℕ) : ℕ × ℕ × ℕ :=
  ((swapDims (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o) K a b).1,
    (swapDims (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o) K a b).2.1,
    (swapDims (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o) K a b).2.2 * (3 * B))

/-- The bank of the interchange holding the five canonical header counters `hs`: header register
`sw (reg (hd k))` holds `separator :: (hs k).map bitSymbol`, the payload and private registers
are empty, and every other caller register of the bank holds non-blank symbols of the vendored
alphabet. -/
structure LayBank (rg : LayReg t₀ → Fin T) (R : Fin T → List (Fin (prime + Ka + 4)))
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hs : Fin 5 → List Bool) : Prop where
  bpay : R (rg (.sw (reg pay))) = []
  bpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → R (rg (.sw j)) = []
  bhdr : ∀ k, R (rg (.sw (reg (hd k)))) = separator :: (hs k).map bitSymbol
  bother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
    ∀ s ∈ R (rg (.sw (reg i))), s ≠ blank ∧ s.val < prime + 4

/-- The headers `hs` are canonical counters of the dimensions of the exchange. -/
def LayHdr (n K : ℕ) (o : Fin 3 → ℕ) (a b : Fin 3) (B : ℕ) (hs : Fin 5 → List Bool) : Prop :=
  (∀ k, Counter.value (hs k) = BinaryInterchangeRun.values (layXcDims n K o a b B).1
      (layXcDims n K o a b B).2.1 (layXcDims n K o a b B).2.2 K K k) ∧
    ∀ k, GrowingCounterData.Canonical (hs k)

/-- The step bound of one exchange: `(T + 12 swapT t₀ + 5)` host steps per step of the
interchange machine (`BinaryInterchangeRun.cost`), `6` per symbol on the bank, `34` per stream
symbol, and a term linear in the tape counts. -/
noncomputable def layXcCost (T t₀ n K : ℕ) (o : Fin 3 → ℕ) (a b : Fin 3) (B : ℕ)
    (hs : Fin 5 → List Bool) (bank : ℕ) : ℕ :=
  (T + 12 * swapT t₀ + 5) * BinaryInterchangeRun.cost (layXcDims n K o a b B).1
    (layXcDims n K o a b B).2.1 (layXcDims n K o a b B).2.2 K K hs +
    6 * bank + 34 * (2 ^ n * B) + 2 * T + 6 * swapT t₀ + 23

/-- **The chunk exchange.** The stream register holds `l.flatten`, `2^n` records of `B ≥ 1`
symbols of value below `8`; the three chunk slots `o` satisfy `LayXcOK n K o`; the bank holds
canonical headers of the exchange of the slots `a ≠ b` (`LayBank`, `LayHdr`); `tmp` and every
left stack are empty. Afterwards the stream register holds
`(moveRecs (layRec ((LayMove.xc (o a) (o b)).perm K n)) l).flatten`, the records moved by the
exchange of the chunks at bit offsets `o a` and `o b`, and every other register is unchanged,
within `layXcCost` steps. -/
theorem layXchg_exec (body : F → Pr F T Q (prime + Ka) U) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q) {rg : LayReg t₀ → Fin T}
    (hrg : Function.Injective rg) (hT : swapT t₀ ≤ T) {n K B : ℕ} {o : Fin 3 → ℕ}
    (hO : LayXcOK n K o) {a b : Fin 3} (hab : a ≠ b) (hB : 0 < B)
    (l : List (List (Fin (prime + Ka + 4)))) (hl : l.length = 2 ^ n)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8) (hs : Fin 5 → List Bool)
    (hh : LayHdr n K o a b B hs) (v : HS T Q (prime + Ka) U) (S : Stacks T (prime + Ka))
    (hL : ∀ y, S.L y = []) (hS : S.R (rg .str) = l.flatten) (htmp : S.R (rg .tmp) = [])
    (hbank : LayBank rg S.R hd pay hs) :
    ∃ (v' : HS T Q (prime + Ka) U) (m : ℕ), v'.user = v.user ∧
      m ≤ layXcCost T t₀ n K o a b B hs (∑ j, (S.R (rg (.sw j))).length) ∧
      Exec body (layXchg hd pay hi hQ rg (fun _ _ h => by simpa using hrg h) hT) (mk v S) m
        (mk v' { S with
          R := Function.update S.R (rg .str)
            (moveRecs (layRec ((LayMove.xc (o a) (o b)).perm K n)) l).flatten }) := by
  have hpos : ∀ e : ℕ, 0 < 2 ^ e := fun e => by positivity
  obtain ⟨v', m, hu, hm, he⟩ := swapPass_exec body hd pay hi hQ (fun j => rg (.sw j))
    (fun _ _ h => by simpa using hrg h) hT (rg .str) (rg .tmp) (by simp [hrg.eq_iff])
    (fun j => by simp [hrg.eq_iff]) (fun j => by simp [hrg.eq_iff])
    (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o) K 0 0 0 B a b hab (hpos _) (hpos _)
    (hpos _) (hpos _) hB l (by rw [lay_rectSize hO]; exact hl) hlB h8 hs hh.1 hh.2 v S hL hS
    htmp hbank.bpay hbank.bpriv hbank.bhdr hbank.bother
  refine ⟨v', m, hu, ?_, ?_⟩
  · refine hm.trans (le_of_eq ?_)
    rw [lay_rectSize hO]
    rfl
  · rw [← lay_moveRecs_swap hO hab 0 0 0 l]
    exact he

/-- `layXchg_exec` with the interchange cost bounded by the vendored
`BinaryInterchangeRun.uniform_bound` (`swapPass_exec_le`): at most
`3 C_swap (T + 12 swapT t₀ + 5) · 2^n B · max(1, K)^τ` plus the linear terms. -/
theorem layXchg_exec_le (body : F → Pr F T Q (prime + Ka) U) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q) {rg : LayReg t₀ → Fin T}
    (hrg : Function.Injective rg) (hT : swapT t₀ ≤ T) {n K B : ℕ} {o : Fin 3 → ℕ}
    (hO : LayXcOK n K o) {a b : Fin 3} (hab : a ≠ b) (hB : 0 < B)
    (l : List (List (Fin (prime + Ka + 4)))) (hl : l.length = 2 ^ n)
    (hlB : ∀ x ∈ l, x.length = B) (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8) (hs : Fin 5 → List Bool)
    (hh : LayHdr n K o a b B hs) (v : HS T Q (prime + Ka) U) (S : Stacks T (prime + Ka))
    (hL : ∀ y, S.L y = []) (hS : S.R (rg .str) = l.flatten) (htmp : S.R (rg .tmp) = [])
    (hbank : LayBank rg S.R hd pay hs) :
    ∃ (v' : HS T Q (prime + Ka) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ 3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (2 ^ n * B : ℕ) *
          ((max 1 K : ℕ) : ℝ) ^ Parameters.tau +
        (6 * ∑ j, (S.R (rg (.sw j))).length + 34 * (2 ^ n * B) + 2 * T + 6 * swapT t₀ + 23 : ℕ) ∧
      Exec body (layXchg hd pay hi hQ rg (fun _ _ h => by simpa using hrg h) hT) (mk v S) m
        (mk v' { S with
          R := Function.update S.R (rg .str)
            (moveRecs (layRec ((LayMove.xc (o a) (o b)).perm K n)) l).flatten }) := by
  have hpos : ∀ e : ℕ, 0 < 2 ^ e := fun e => by positivity
  obtain ⟨v', m, hu, hm, he⟩ := swapPass_exec_le body hd pay hi hQ (fun j => rg (.sw j))
    (fun _ _ h => by simpa using hrg h) hT (rg .str) (rg .tmp) (by simp [hrg.eq_iff])
    (fun j => by simp [hrg.eq_iff]) (fun j => by simp [hrg.eq_iff])
    (layN0 n K o) (layN1 K o) (layN2 K o) (layN3 o) K 0 0 0 B a b hab (hpos _) (hpos _)
    (hpos _) (hpos _) hB l (by rw [lay_rectSize hO]; exact hl) hlB h8 hs hh.1 hh.2 v S hL hS
    htmp hbank.bpay hbank.bpriv hbank.bhdr hbank.bother
  refine ⟨v', m, hu, ?_, ?_⟩
  · rw [lay_rectSize hO] at hm
    exact hm
  · rw [← lay_moveRecs_swap hO hab 0 0 0 l]
    exact he

end Xchg

end IntegerMultBounds.MathlibTM2.Fast
