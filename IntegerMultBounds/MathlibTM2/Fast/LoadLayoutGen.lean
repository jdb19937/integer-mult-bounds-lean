module

public import IntegerMultBounds.MathlibTM2.Fast.LoadLayoutHost
public import IntegerMultBounds.MathlibTM2.Fast.LoadLayoutGenX

/-!
# The layout stage from its parameters

The writer `ldgWriter` (`IntegerMultBounds.MathlibTM2.Fast.LoadLayoutHost`) followed by the layout machine
`layApply` with the loaders `ldlPrepM`, `ldlPrepX` (`IntegerMultBounds.MathlibTM2.Fast.LoadLayout`): from the unary
parameters `N = es.sum`, `ℓ`, `K`, `D = es.length`, `B` and the word `E` of the long axes, the
stage writes the description streams of `layBits es ℓ K` and `layXcs es ℓ K B` with their loop
counters, then moves the record stream by the layout `layPerm es ℓ K`.

* `LdgPre`: the register file before the stage (the registers of a single-bit move, the bank of
  the interchange, empty loader buffers and outputs, idle table registers).
* `ldgPost`: the file after the writer; `ldgPre_base`: it satisfies `LdlBase`.
* `ldg_stage_gen`: the stage for any table program `cX` that writes the exchange stream.
* `ldLayGenStage_exec`: the stage with the exchange writer `ldxCode`
  (`IntegerMultBounds.MathlibTM2.Fast.LoadLayoutGenX`), under the word-width conditions `(N + 1)^N < 2^W`,
  `N + B + 4 ≤ W`, `ℓ < 2^W`, `E < 2^W`.

**Cost.** `ldgWriterCost` (the four table-machine runs, at `tblC W w = 32 (W + 4)² + 8 w` host
steps per atom with `ldw1Atoms` and `ldxAtoms` atoms, the loads `O(W (N + ℓ + K + D + B) + W)`,
and the stream copies) plus the cost of `ldLayStage_exec` (`ldLayStage_cost_le`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.Rounds
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


section Pre

variable {T Q t₀ Ka : ℕ} {U F : Type} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}
  {gr : LdgReg → Fin T}

/-- The register file before the layout stage: the registers of a single-bit move (`LayMvCfg`
apart from the masks, which hold at most `n` symbols), the bank of the interchange (empty
payload and private registers, headers of at most `wX + 1` symbols), the record stream on `str`,
empty loop counters, empty loader registers and outputs, idle table registers (`wr` with `W`
symbols), and the parameters on the writer's input registers. -/
structure LdgPre (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) (gr : LdgReg → Fin T)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (R : Fin T → List (Fin (prime + Ka + 4)))
    (es : List ℕ) (ℓ K B E W : ℕ) (wl : List (Fin (prime + Ka + 4)))
    (l : List (List (Fin (prime + Ka + 4)))) : Prop where
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
  cnt : (R (rg .cnt)).length = 2 ^ es.sum
  fld : R (rg .fld) = binSyms es.sum 0
  us : ∀ r, R (rg (.us r)) = []
  mA : (R (rg .mA)).length ≤ es.sum
  mB : (R (rg .mB)).length ≤ es.sum
  bpay : R (rg (.sw (reg pay))) = []
  bpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → R (rg (.sw j)) = []
  bother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
    ∀ s ∈ R (rg (.sw (reg i))), s ≠ blank ∧ s.val < prime + 4
  hdr : ∀ k, (R (ldlH rg hd k)).length ≤ es.sum + B + 2 + 1
  str : R (rg .str) = l.flatten
  cM : R (rg .cM) = []
  tM : R (rg .tM) = []
  cX : R (rg .cX) = []
  tX : R (rg .tX) = []
  dM : R (lr .dM) = []
  dX : R (lr .dX) = []
  cN : R (lr .cN) = []
  cW : R (lr .cW) = []
  tA : R (lr .tA) = []
  tB : R (lr .tB) = []
  tS : R (lr .tS) = []
  tbl : ∀ r, R (ldgRv gr r) = ldgIdle wl [] r
  wl : wl.length = W
  uN : (R (gr .uN)).length = es.sum
  uL : (R (gr .uL)).length = ℓ
  uK : (R (gr .uK)).length = K
  uD : (R (gr .uD)).length = es.length
  uB : (R (gr .uB)).length = B
  eW : R (gr .eW) = binSyms W E
  tc : R (gr .tc) = []

/-- The register file after the writer. -/
noncomputable def ldgPost (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) (R : Fin T → List (Fin (prime + Ka + 4)))
    (es : List ℕ) (ℓ K B : ℕ) (xs : List LayXcD) : Fin T → List (Fin (prime + Ka + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update R (lr .dM) (ldlBitStream (prime + Ka) es.sum (layBits es ℓ K))) (rg .cM)
    (ldlBitStream (prime + Ka) 1 (layBits es ℓ K))) (lr .dX)
    (ldlXcStream (prime + Ka) (es.sum + B + 2) xs)) (rg .cX) (List.replicate xs.length tick))
    (lr .cN) (List.replicate es.sum tick)) (lr .cW) (List.replicate (es.sum + B + 2) tick)

end Pre

section Stage

variable {T Q t₀ Ka : ℕ} {U F : Type} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}
  {gr : LdgReg → Fin T}

theorem ldgPost_rg (hg : LdgRegs rg lr gr) (R : Fin T → List (Fin (prime + Ka + 4)))
    (es : List ℕ) (ℓ K B : ℕ) (xs : List LayXcD) {x : LayReg t₀} (h1 : x ≠ .cM) (h2 : x ≠ .cX) :
    ldgPost rg lr R es ℓ K B xs (rg x) = R (rg x) := by
  simp [ldgPost, hg.l.rl, hg.l.rg_inj.eq_iff, h1, h2]

theorem ldgPost_lr (hg : LdgRegs rg lr gr) (R : Fin T → List (Fin (prime + Ka + 4)))
    (es : List ℕ) (ℓ K B : ℕ) (xs : List LayXcD) {y : LdlReg} (h1 : y ≠ .dM) (h2 : y ≠ .dX)
    (h3 : y ≠ .cN) (h4 : y ≠ .cW) :
    ldgPost rg lr R es ℓ K B xs (lr y) = R (lr y) := by
  simp [ldgPost, hg.l.lr', hg.l.lr_inj.eq_iff, h1, h2, h3, h4]

/-- After the writer the file is a base file of the layout stage. -/
theorem ldgPre_base (hg : LdgRegs rg lr gr) {hd : Fin 5 → Fin t₀} {pay : Fin t₀}
    {R : Fin T → List (Fin (prime + Ka + 4))} {es : List ℕ} {ℓ K B E W : ℕ}
    {wl : List (Fin (prime + Ka + 4))} {l : List (List (Fin (prime + Ka + 4)))}
    (hp : LdgPre rg lr gr hd pay R es ℓ K B E W wl l) (xs : List LayXcD) :
    LdlBase rg lr hd pay (ldgPost rg lr R es ℓ K B xs) es.sum B (es.sum + B + 2) (layBits es ℓ K)
      xs := by
  have e := fun x h1 h2 => ldgPost_rg (Ka := Ka) hg R es ℓ K B xs (x := x) h1 h2
  have f := fun y h1 h2 h3 h4 => ldgPost_lr (Ka := Ka) hg R es ℓ K B xs (y := y) h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [e _ (by simp) (by simp)]; exact hp.r0
  · rw [e _ (by simp) (by simp)]; exact hp.r1
  · rw [e _ (by simp) (by simp)]; exact hp.r2
  · rw [e _ (by simp) (by simp)]; exact hp.r3
  · rw [e _ (by simp) (by simp)]; exact hp.q0
  · rw [e _ (by simp) (by simp)]; exact hp.q1
  · rw [e _ (by simp) (by simp)]; exact hp.q2
  · rw [e _ (by simp) (by simp)]; exact hp.q3
  · rw [e _ (by simp) (by simp)]; exact hp.tmp
  · rw [e _ (by simp) (by simp)]; exact hp.ctrB
  · rw [e _ (by simp) (by simp)]; exact hp.cnt
  · rw [e _ (by simp) (by simp)]; exact hp.fld
  · intro r; rw [e _ (by simp) (by simp)]; exact hp.us r
  · rw [e _ (by simp) (by simp)]; exact hp.mA
  · rw [e _ (by simp) (by simp)]; exact hp.mB
  · rw [e _ (by simp) (by simp)]; exact hp.bpay
  · intro j hj; rw [e _ (by simp) (by simp)]; exact hp.bpriv j hj
  · intro i hi hk; rw [e _ (by simp) (by simp)]; exact hp.bother i hi hk
  · intro k
    rw [show ldlH rg hd k = rg (.sw (reg (hd k))) from rfl, e _ (by simp) (by simp)]
    exact hp.hdr k
  · simp [ldgPost, hg.l.lr', hg.l.lr_inj.eq_iff]
  · simp [ldgPost, hg.l.lr', hg.l.lr_inj.eq_iff]
  · simp [ldgPost, hg.l.lr_inj.eq_iff]
  · simp [ldgPost]
  · rw [f _ (by simp) (by simp) (by simp) (by simp)]; exact hp.tA
  · rw [f _ (by simp) (by simp) (by simp) (by simp)]; exact hp.tB
  · rw [f _ (by simp) (by simp) (by simp) (by simp)]; exact hp.tS

theorem ldg_layDyn_self (R : Fin T → List (Fin (prime + Ka + 4))) :
    layDyn rg R (R (rg .str)) (R (rg .cM)) (R (rg .tM)) (R (rg .cX)) (R (rg .tX)) = R := by
  simp [layDyn, Function.update_eq_self]

/-- The layout stage from its parameters: the writer, then the layout machine. -/
noncomputable def ldgStage (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hQ : swapStates hd pay hi ≤ Q) (rg : LayReg t₀ → Fin T)
    (hsw : Function.Injective fun j => rg (.sw j)) (hT : swapT t₀ ≤ T) (lr : LdlReg → Fin T)
    (gr : LdgReg → Fin T) (cX : TblCode 40) : Pr F T Q (prime + Ka) U :=
  .seq (ldgWriter rg lr gr cX) (layApply hd pay hi hQ rg hsw hT (ldlPrepM rg lr) (ldlPrepX hd rg lr))

/-- **The layout stage from its parameters**, for any table program `cX` writing the exchange
stream `ldlXcStream A w (layXcs es ℓ K B)` from `N, ℓ, K, D, B` in its variables `0 … 4`. From a
file `LdgPre` (the record stream `l` on `str`), the writer leaves the description streams and
counters (`ldgPost`), and the layout machine then leaves `(moveRecs (layRec (layPerm es ℓ K))
l).flatten` on `str`; within the cost of the writer and of `ldLayStage_exec`. -/
theorem ldg_stage_gen {es : List ℕ} {ℓ K B E W : ℕ} (H : LayHyp es ℓ K)
    (body : F → Pr F T Q (prime + Ka) U) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q) (hg : LdgRegs rg lr gr)
    (hT : swapT t₀ ≤ T) (hA : 4 ≤ prime + Ka) (hpay : ∀ k, hd k ≠ pay) (hB : 1 ≤ B)
    (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2) (hEW : E < 2 ^ W)
    (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hNW : es.sum < W) (h2W : 2 ≤ W) (hℓW : ℓ < 2 ^ W)
    (hBW : es.sum + B + 2 ≤ W) {cX : TblCode 40} {KX : ℕ}
    (hX : ∀ w, ∀ st : TblSt 40 (prime + Ka), st.val 0 = es.sum → st.val 1 = ℓ → st.val 2 = K →
      st.val 3 = es.length → st.val 4 = B → st.acc = [] →
      TblDo (prime + Ka) W w cX st (fun s => s.acc.reverse = ldlXcStream (prime + Ka) w
        (layXcs es ℓ K B)) KX)
    (R : Fin T → List (Fin (prime + Ka + 4))) (wl : List (Fin (prime + Ka + 4)))
    (l : List (List (Fin (prime + Ka + 4)))) (hp : LdgPre rg lr gr hd pay R es ℓ K B E W wl l)
    (hl : l.length = 2 ^ es.sum) (hlB : ∀ x ∈ l, x.length = B)
    (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8) :
    LayRuns body (ldgStage hd pay hi hQ rg (fun _ _ e => by simpa using hg.l.rg_inj e) hT lr gr cX)
      R
      (layDyn rg (ldlW rg lr hd (prime + Ka) es.sum (es.sum + B + 2)
          (ldgPost rg lr R es ℓ K B (layXcs es ℓ K B)) (layBits es ℓ K) (layXcs es ℓ K B)
          ((layBits es ℓ K).length + (layXcs es ℓ K B).length))
        (moveRecs (layRec (layPerm es ℓ K)) l).flatten
        (ldlBitStream (prime + Ka) 1 (layBits es ℓ K)) []
        (List.replicate (layXcs es ℓ K B).length tick) [])
      (ldgWriterCost W es.sum ℓ K es.length B (layB ℓ K) (layBits es ℓ K).length
          (layXcs es ℓ K B).length KX +
        (layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es ℓ K).length +
          layXcLoopCost T t₀ es.sum K B rg
            (fun j => ldlW rg lr hd (prime + Ka) es.sum (es.sum + B + 2)
              (ldgPost rg lr R es ℓ K B (layXcs es ℓ K B)) (layBits es ℓ K) (layXcs es ℓ K B)
              ((layBits es ℓ K).length + j)) (fun _ => 60 * (es.sum + B + 2) + 75)
            (layXcs es ℓ K B))) := by
  have hw := ldg_writer_runs (body := body) hg H hE hEW hW hNW h2W hℓW hBW (layXcs es ℓ K B) hX wl
    hp.wl R hp.tbl hp.uN hp.uL hp.uK hp.uD hp.uB hp.eW hp.dM hp.dX hp.cN hp.cW hp.cM hp.cX hp.tc
  set Rw := ldgPost rg lr R es ℓ K B (layXcs es ℓ K B) with hRw
  have hs := ldLayStage_exec H body hd pay hi hQ hg.l hT hA hpay hB (wX := es.sum + B + 2) le_rfl
    Rw (ldgPre_base hg hp (layXcs es ℓ K B)) l hl hlB h8
    (ldlBitStream (prime + Ka) 1 (layBits es ℓ K)) (List.replicate (layXcs es ℓ K B).length tick)
    (length_ldlBitStream_one _) (by simp)
  have e : layDyn rg Rw l.flatten (ldlBitStream (prime + Ka) 1 (layBits es ℓ K)) []
      (List.replicate (layXcs es ℓ K B).length tick) [] = Rw := by
    have e1 : Rw (rg .str) = l.flatten := by
      rw [hRw, ldgPost_rg hg _ _ _ _ _ _ (by simp) (by simp)]; exact hp.str
    have e2 : Rw (rg .cM) = ldlBitStream (prime + Ka) 1 (layBits es ℓ K) := by
      simp [hRw, ldgPost, hg.l.rl, hg.l.rg_inj.eq_iff]
    have e3 : Rw (rg .tM) = [] := by
      rw [hRw, ldgPost_rg hg _ _ _ _ _ _ (by simp) (by simp)]; exact hp.tM
    have e4 : Rw (rg .cX) = List.replicate (layXcs es ℓ K B).length tick := by
      simp [hRw, ldgPost, hg.l.rl]
    have e5 : Rw (rg .tX) = [] := by
      rw [hRw, ldgPost_rg hg _ _ _ _ _ _ (by simp) (by simp)]; exact hp.tX
    calc layDyn rg Rw l.flatten (ldlBitStream (prime + Ka) 1 (layBits es ℓ K)) []
          (List.replicate (layXcs es ℓ K B).length tick) [] =
        layDyn rg Rw (Rw (rg .str)) (Rw (rg .cM)) (Rw (rg .tM)) (Rw (rg .cX)) (Rw (rg .tX)) := by
          rw [e1, e2, e3, e4, e5]
      _ = Rw := ldg_layDyn_self Rw
  rw [e] at hs
  exact hw.seq hs

end Stage

/-! ### The layout stage with the exchange writer `ldxCode` -/

section Closed

variable {T Q t₀ Ka : ℕ} {U F : Type} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}
  {gr : LdgReg → Fin T}

/-- **The layout stage from its parameters.** From a file `LdgPre` (the record stream `l` of
`2^N` records of `B` symbols on `str`, `N = es.sum`; unary `N, ℓ, K, D = es.length, B` and the
word `binSyms W E` of the long axes on the writer's inputs; the registers of the single-bit
move and of the interchange bank), the fixed program `ldgStage … ldxCode` writes the description
streams of the layout moves and then leaves `(moveRecs (layRec (layPerm es ℓ K)) l).flatten` on
`str`: the record at address `x` moves to the address whose bit `layPerm es ℓ K j` is bit `j` of
`x`. Word width: `(N + 1)^N < 2^W`, `N + B + 4 ≤ W`, `ℓ < 2^W`, `E < 2^W`. -/
theorem ldLayGenStage_exec {es : List ℕ} {ℓ K B E W : ℕ} (H : LayHyp es ℓ K)
    (body : F → Pr F T Q (prime + Ka) U) (hd : Fin 5 → Fin t₀) (pay : Fin t₀)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q) (hg : LdgRegs rg lr gr)
    (hT : swapT t₀ ≤ T) (hA : 4 ≤ prime + Ka) (hpay : ∀ k, hd k ≠ pay) (hB : 1 ≤ B)
    (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2) (hEW : E < 2 ^ W)
    (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hWB : es.sum + B + 4 ≤ W) (hℓW : ℓ < 2 ^ W)
    (R : Fin T → List (Fin (prime + Ka + 4))) (wl : List (Fin (prime + Ka + 4)))
    (l : List (List (Fin (prime + Ka + 4)))) (hp : LdgPre rg lr gr hd pay R es ℓ K B E W wl l)
    (hl : l.length = 2 ^ es.sum) (hlB : ∀ x ∈ l, x.length = B)
    (h8 : ∀ x ∈ l, ∀ s ∈ x, s.val < 8) :
    LayRuns body
      (ldgStage hd pay hi hQ rg (fun _ _ e => by simpa using hg.l.rg_inj e) hT lr gr ldxCode) R
      (layDyn rg (ldlW rg lr hd (prime + Ka) es.sum (es.sum + B + 2)
          (ldgPost rg lr R es ℓ K B (layXcs es ℓ K B)) (layBits es ℓ K) (layXcs es ℓ K B)
          ((layBits es ℓ K).length + (layXcs es ℓ K B).length))
        (moveRecs (layRec (layPerm es ℓ K)) l).flatten
        (ldlBitStream (prime + Ka) 1 (layBits es ℓ K)) []
        (List.replicate (layXcs es ℓ K B).length tick) [])
      (ldgWriterCost W es.sum ℓ K es.length B (layB ℓ K) (layBits es ℓ K).length
          (layXcs es ℓ K B).length (ldxAtoms es.sum es.length (layQ ℓ K)) +
        (layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es ℓ K).length +
          layXcLoopCost T t₀ es.sum K B rg
            (fun j => ldlW rg lr hd (prime + Ka) es.sum (es.sum + B + 2)
              (ldgPost rg lr R es ℓ K B (layXcs es ℓ K B)) (layBits es ℓ K) (layXcs es ℓ K B)
              ((layBits es ℓ K).length + j)) (fun _ => 60 * (es.sum + B + 2) + 75)
            (layXcs es ℓ K B))) := by
  have hNW : es.sum < W := by omega
  have h2W : 2 ≤ W := by omega
  refine ldg_stage_gen H body hd pay hi hQ hg hT hA hpay hB hE hEW hW hNW h2W hℓW (by omega)
    (fun w st h0 h1 h2 h3 h4 hacc => (ldx_do (A := prime + Ka) (W := W) (w := w) H st h0 h1 h2 h3 h4
      hW hWB hℓW).mono (fun s hs => by rw [hs, hacc, List.append_nil, List.reverse_reverse])
      le_rfl) R wl l hp hl hlB h8

end Closed

end IntegerMultBounds.MathlibTM2.Fast.TableVM
