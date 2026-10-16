module

public import IntegerMultBounds.MathlibTM2.Fast.DistSyn
public import IntegerMultBounds.MathlibTM2.Fast.BundleDist
public import IntegerMultBounds.MathlibTM2.Fast.BundleMnLay

/-!
# The wires program of the fast multiplier

The wire machine `dsySyn` (`Fast/DistSyn.lean`) on the register file of the host
(`Fast/MainRegs.lean`), in the form of the wires program `BdWires` of `Fast/BundleDist.lean`:

* the table layout `dsyRg` lives on the scratch registers `mnι` (empty before and after);
* the inputs are the parking registers `bdIo x` of the distribution (`BdPre`);
* the wires `dsyV₀ n` of the synthetic transforms are written on `mnLay (.wire (synWire x))`:
  the machine writes `p .b`, `p .Lg`, `p .lr`, `p .c`, `p .es`, `tw .pz` and the park record
  `blP₀ dsW n` on `mnLay .park`; the tail `dsyTail` moves the unary inputs `lK, lL, lD, lN, uw,
  rR` onto `p .K, p .ℓ, p .D, p .N, p .w, p .r` and clears the remaining parking registers.
* `dsyV₀_wires`: the wires meet `MnLay.wires` (`SynV` at the axes `cvAx (t n)`);
* `dsyWires_spec`: the `spec` field of `BdWires (fun n => mnσ (blP₀ dsW n) (dsyV₀ n))`;
* `dsyWiresCost_le`: `dsyWiresCost n ≤ C (b n + 1)^7 + C' · 2^ℓ · dsW n`. The second term is
  forced: the wire `p .r` has `2^ℓ` ticks and the park record has `blW dsW n ≥ 2^ℓ dsW n`
  symbols, so no program writing `mnσ (blP₀ dsW n) v₀` runs within `O((b n + 1)^k)` steps
  (`costBound` of `BdWires` cannot hold for this `σ`), see `dsyWires_lower`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ConvSt IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

/-! ### The table layout on the scratch registers -/

/-- The scratch register of a table register. -/
def dsyIdx : TblR 40 → Fin 64
  | .v i => ⟨i, by omega⟩
  | .wr => ⟨40, by omega⟩
  | .wn => ⟨41, by omega⟩
  | .acc => ⟨42, by omega⟩
  | .z j => ⟨43 + j, by omega⟩

theorem dsyIdx_inj : Function.Injective dsyIdx := by
  intro a b h
  rcases a with i | _ | _ | _ | j <;> rcases b with i' | _ | _ | _ | j' <;>
    simp only [dsyIdx, Fin.ext_iff] at h <;>
    first
    | rfl
    | (exfalso; omega)
    | (congr 1; exact Fin.ext (by omega))

/-- The table layout of the wire machine. -/
def dsyRg (r : TblR 40) : Fin mnT := mnι (dsyIdx r)

theorem dsyRg_inj : Function.Injective dsyRg := fun _ _ h => dsyIdx_inj (mnι_inj h)

theorem dsyRg_ne_lay (r : TblR 40) (x : LReg SXReg) : dsyRg r ≠ mnLay x := mnι_ne_lay _ _

@[simp] theorem dsyOv_lay (R : Regs mnT bdA) (ρ : TblR 40 → List (Fin (bdA + 4)))
    (x : LReg SXReg) : dsOv dsyRg R ρ (mnLay x) = R (mnLay x) :=
  dsOv_off _ _ fun r => dsyRg_ne_lay r x

/-- The wire register of a transform register. -/
def dsyWr (x : SynW) : Fin mnT := mnLay (.wire (synWire x))

/-! ### The wires -/

/-- The axes of the synthetic transforms at `n`. -/
abbrev dsyEs (n : ℕ) : List ℕ := List.ofFn (cvAx (t n))

/-- **The wires** of the synthetic transforms at `n`. -/
def dsyV₀ (n : ℕ) : SynW → List (Fin (bdA + 4))
  | .p .K => List.replicate (K n) tick
  | .p .ℓ => List.replicate (ℓ n) tick
  | .p .b => List.replicate (layB (ℓ n) (K n)) tick
  | .p .D => List.replicate (dsyEs n).length tick
  | .p .Lg => List.replicate (layLongs (dsyEs n) (ℓ n)).length tick
  | .p .N => List.replicate (dsyEs n).sum tick
  | .p .w => List.replicate (dsW n) tick
  | .p .r => List.replicate (r n) tick
  | .p .lr => List.replicate (ℓ n) tick
  | .p .es => topRec (dsyEs n)
  | .p .c => List.replicate (nRounds (cvAx (t n))) tick
  | .tw .pz => twPosReg bdA (dsyEs n).sum (twPosL (layPerm (dsyEs n) (ℓ n) (K n)))
  | _ => []

theorem dsy_tick_ne_blank' {A : ℕ} : (tick : Fin (A + 4)) ≠ blank := by
  simp [tick, bitSymbol, blank, Fin.ext_iff]

theorem dsy_false_ne_blank' {A : ℕ} : (bitSymbol false : Fin (A + 4)) ≠ blank := by
  simp [bitSymbol, blank, Fin.ext_iff]

theorem dsy_tick_ne_blank : (tick : Fin (bdA + 4)) ≠ blank := dsy_tick_ne_blank'

theorem dsy_false_ne_blank : (bitSymbol false : Fin (bdA + 4)) ≠ blank := dsy_false_ne_blank'

theorem dsy_blank_not_mem {l : List (Fin (bdA + 4))}
    (hl : ∀ x ∈ l, x = tick ∨ x = bitSymbol false) : blank ∉ l := by
  intro h
  rcases hl blank h with e | e
  · exact dsy_tick_ne_blank e.symm
  · exact dsy_false_ne_blank e.symm

/-- **The wires meet `MnLay.wires`.** -/
theorem dsyV₀_wires : ∀ᶠ n in atTop,
    SynV (dsyV₀ n) (dsyEs n) (ℓ n) (K n) (dsW n) (ℓ n) 0 (layPerm (dsyEs n) (ℓ n) (K n)) ∧
      dsyV₀ n (.p .h) = [] ∧ dsyV₀ n (.p .t) = [] ∧
      (dsyV₀ n (.p .c)).length = nRounds (cvAx (t n)) ∧ blank ∉ dsyV₀ n (.p .c) := by
  refine Eventually.of_forall fun n => ⟨?_, rfl, rfl, by simp [dsyV₀], ?_⟩
  · refine
      { hh := rfl
        hK := by simp [dsyV₀]
        hℓ := by simp [dsyV₀]
        hb := by simp [dsyV₀]
        hD := by simp [dsyV₀]
        hLg := by simp [dsyV₀, synLg]
        hN := by simp [dsyV₀]
        hw := by simp [dsyV₀]
        hr := by simp [dsyV₀, r]
        hlr := by simp [dsyV₀]
        hes := rfl
        hpz := rfl
        htw := fun w hw => by cases w <;> first | rfl | exact absurd rfl hw
        hs := fun _ => rfl
        hly := fun _ => rfl
        hw2 := rfl
        hcf := rfl
        hkh := rfl
        hrh := rfl
        hpr := rfl
        hblank := ?_ }
    intro x hx
    simp only [synXS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact dsy_blank_not_mem (dsy_mem_replicate_tick _)
      | exact dsy_blank_not_mem (dsy_mem_topRec _)
      | exact dsy_blank_not_mem (dsy_mem_twPosReg _ _)
      | simp [dsyV₀]
  · exact dsy_blank_not_mem (dsy_mem_replicate_tick _)

/-! ### The number of rounds -/

theorem dsy_nRounds {n : ℕ} (hbig : Big n) :
    dsyNr (List.ofFn (cvAx (t n))).sum (List.ofFn (cvAx (t n))).length (ℓ n) =
      nRounds (cvAx (t n)) := by
  have H := ds_layHyp hbig
  have hD : 1 ≤ (List.ofFn (cvAx (t n))).length := by
    rw [ds_length_cvAx]; have := hbig.2; omega
  have hℓ := H.ℓ_ge
  have hax : ∀ i : Fin (d n - 1), cvAx (t n) i = ax (List.ofFn (cvAx (t n))) i := fun i => by
    unfold ax
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hle : ∀ i : Fin (d n - 1), cvAx (t n) i ≤ ℓ n := fun i => by
    rw [hax]; rcases H.ax_of_lt (i := i) (by simp) with h | h <;> omega
  have hsum := lay_sum H
  unfold dsyNr
  split_ifs with h
  · -- some axis is long
    have hpos : 0 < (layLongs (List.ofFn (cvAx (t n))) (ℓ n)).length := by omega
    obtain ⟨i, hi⟩ := List.exists_mem_of_length_pos hpos
    rw [mem_layLongs] at hi
    have hi' : i < d n - 1 := by have := hi.1; simpa using this
    refine (le_antisymm (Finset.sup_le fun i _ => hle i) ?_).symm
    have := Finset.le_sup (f := cvAx (t n)) (Finset.mem_univ (⟨i, hi'⟩ : Fin (d n - 1)))
    rw [hax] at this
    exact hi.2 ▸ this
  · -- every axis has `ℓ - 1` bits
    have hz : (layLongs (List.ofFn (cvAx (t n))) (ℓ n)).length = 0 := by omega
    have hall : ∀ i : Fin (d n - 1), cvAx (t n) i = ℓ n - 1 := fun i => by
      rcases H.ax_of_lt (i := i) (by simp) with h' | h'
      · rw [hax]; exact h'
      · exfalso
        have : (i : ℕ) ∈ layLongs (List.ofFn (cvAx (t n))) (ℓ n) := mem_layLongs.2 ⟨by simp, h'⟩
        rw [List.length_eq_zero_iff.1 hz] at this
        simp at this
    refine (le_antisymm (Finset.sup_le fun i _ => (hall i).le) ?_).symm
    have := Finset.le_sup (f := cvAx (t n))
      (Finset.mem_univ (⟨0, by rw [ds_length_cvAx] at hD; omega⟩ : Fin (d n - 1)))
    rw [hall] at this
    exact this

/-! ### The axis word and the park record -/

theorem dsy_E_eq (n : ℕ) : dsE n = blE n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [ds_testBit_E]
  by_cases hi : i < d n - 1
  · rw [Nat.testBit_eq_decide_div_mod_eq, blE, bl_bits _ _ _ hi]
    by_cases hm : i < numHalf n
    · simp [hm]
    · simp [hm]; omega
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (blE_lt n)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp; omega

theorem dsy_park_eq {n : ℕ} (hn : 2 ≤ n) :
    dsyParkL bdA (dsWL n (dsW n) + ℓ n + (dsyEs n).length) (dsE n) = blP₀ dsW n := by
  have e : dsWL n (dsW n) + ℓ n + (dsyEs n).length = blW dsW n := by
    unfold blW slyW dsWL
    rw [ds_length_cvAx, ds_sum_cvAx hn, pow_two, show r n = 2 ^ ℓ n from rfl]
    ring
  rw [dsy_E_eq, e]
  rfl

/-! ### The program -/

/-- The tail: the unary inputs moved onto their wires, the other parking registers cleared. -/
def dsyTail : MnPr bdA :=
  .seq (moveR (bdIo .lK) (dsyWr (.p .K)) id) <| .seq (moveR (bdIo .lL) (dsyWr (.p .ℓ)) id) <|
  .seq (moveR (bdIo .lD) (dsyWr (.p .D)) id) <| .seq (moveR (bdIo .lN) (dsyWr (.p .N)) id) <|
  .seq (moveR (bdIo .uw) (dsyWr (.p .w)) id) <| .seq (moveR (bdIo .rR) (dsyWr (.p .r)) id) <|
  .seq (bclear (bdIo .lE)) <| .seq (bclear (bdIo .lW)) <| .seq (bclear (bdIo .lB))
    (bclear (bdIo .uW))

/-- **The wires program.** -/
def dsyProg : MnPr bdA :=
  .seq (dsySyn dsyRg bdIo (mnLay .park) (dsyWr (.p .b)) (dsyWr (.p .Lg)) (dsyWr (.p .lr))
    (dsyWr (.p .c)) (dsyWr (.p .es)) (dsyWr (.tw .pz))) dsyTail

/-- The step bound of the tail. -/
def dsyTailCost (n : ℕ) : ℕ :=
  (2 * K n + 2) + ((2 * ℓ n + 2) + ((2 * (dsyEs n).length + 2) + ((2 * (dsyEs n).sum + 2) +
    ((2 * dsW n + 2) + ((2 * r n + 2) + ((2 * dsWL n (dsW n) + 2) + ((2 * dsWL n (dsW n) + 2) +
    ((2 * (r n * dsW n) + 2) + (2 * dsWW n + 2)))))))))

/-- The step bound of the wires program. -/
def dsyWiresCost (n : ℕ) : ℕ :=
  dsySynCostG (dsyEs n).sum (ℓ n) (K n) (dsyEs n).length (dsWL n (dsW n)) + dsyTailCost n

theorem dsy_mnσ_wire_off (P₀ : List (Fin (bdA + 4))) (v₀ : SynW → List (Fin (bdA + 4)))
    {v : NWire} (hv : ∀ y, synWire y ≠ v) : mnσ P₀ v₀ (.wire v) = [] := by
  unfold mnσ
  rw [synG_of_ne fun y h => hv y (LReg.wire.inj (reg_injective h))]
  simp [synIdle, Function.update_apply]

@[simp] theorem dsy_wire_ne_bdLayX (v : NWire) (z : DsX) :
    (LReg.wire v : LReg SXReg) ≠ bdLayX z := fun h => bdLayX_ne_wire z v h.symm

/-- The outputs of the machine are pairwise distinct. -/
theorem dsy_outs_nodup :
    [mnLay .park, dsyWr (.p .b), dsyWr (.p .Lg), dsyWr (.p .lr), dsyWr (.p .c), dsyWr (.p .es),
      dsyWr (.tw .pz)].Nodup := by
  simp [dsyWr, List.nodup_cons, mnLay_inj.eq_iff]

/-- **The wires program**: the `spec` field of `BdWires (fun n => mnσ (blP₀ dsW n) (dsyV₀ n))`. -/
theorem dsyWires_spec : ∀ᶠ n in atTop, ∀ mainP : MnPr bdA,
    ∀ (v : HS mnT mnQ bdA Unit) (S : Stacks mnT bdA),
    (∀ y, S.L y = []) → (∀ j, S.R (mnι j) = []) → BdPre S.R n →
    ∃ (v' : HS mnT mnQ bdA Unit) (S' : Stacks mnT bdA) (m : ℕ), m ≤ dsyWiresCost n ∧
      Exec (mnBody mnLb mainP) dsyProg (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ (∀ j, S'.R (mnι j) = []) ∧
      (∀ x, S'.R (mnLay x) = mnσ (blP₀ dsW n) (dsyV₀ n) x) ∧
      ∀ r, bdWKeep r → S'.R (mnRg r) = S.R (mnRg r) := by
  filter_upwards [eventually_big] with n hbig
  intro mainP v S _ hι hP
  have hn := hbig.1
  have H := ds_layHyp hbig
  have hE := ds_lay_E hn
  have hw1 : 1 ≤ dsW n := by unfold dsW; omega
  obtain ⟨hEW, -, -, -, -⟩ := ds_lay_widths hn hw1
  have hsum := ds_sum_cvAx hn
  have hlen := ds_length_cvAx n
  have hℓr : ℓ n ≤ 2 ^ ℓ n * dsW n :=
    le_trans Nat.lt_two_pow_self.le (Nat.le_mul_of_pos_right _ hw1)
  have hio : ∀ x, S.R (bdIo x) = bdO n x := hP.io
  have hio' : ∀ x, S.R (mnLay (bdLayX x)) = bdO n x := hio
  set es := dsyEs n with hes
  -- the machine
  have hrun := dsySyn_runs (body := mnBody mnLb mainP) bl_hA dsyRg_inj
    (fun r x => dsyRg_ne_lay r _) dsy_outs_nodup
    (fun o ho r => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact dsyRg_ne_lay _ _)
    (fun o ho x => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fun h => bdLayX_ne_park x (mnLay_inj h)
      all_goals exact fun h => bdLayX_ne_wire x _ (mnLay_inj h))
    H hE (by rw [hlen]; exact dsE_lt n)
    (by
      rw [hsum]; unfold dsyW dsWL
      rw [pow_two, show r n = 2 ^ ℓ n from rfl]
      omega)
    hEW S.R (fun r => hι _) (by rw [hio', hsum]; rfl) (by rw [hio']; rfl) (by rw [hio']; rfl)
    (by rw [hio', hlen]; rfl) (by rw [hio']; rfl) (by rw [hio']; rfl)
  rw [dsy_park_eq hn, dsy_nRounds hbig] at hrun
  set R₇ := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update S.R
      (mnLay .park) (blP₀ dsW n ++ S.R (mnLay .park)))
      (dsyWr (.p .b)) (List.replicate (layB (ℓ n) (K n)) tick ++ S.R (dsyWr (.p .b))))
      (dsyWr (.p .Lg)) (List.replicate (layLongs es (ℓ n)).length tick ++ S.R (dsyWr (.p .Lg))))
      (dsyWr (.p .lr)) (List.replicate (ℓ n) tick ++ S.R (dsyWr (.p .lr))))
      (dsyWr (.p .c)) (List.replicate (nRounds (cvAx (t n))) tick ++ S.R (dsyWr (.p .c))))
      (dsyWr (.p .es)) (topRec es ++ S.R (dsyWr (.p .es))))
      (dsyWr (.tw .pz)) (twPosReg bdA es.sum (twPosL (layPerm es (ℓ n) (K n))) ++
        S.R (dsyWr (.tw .pz))) with hR₇
  set F₀ : Regs mnT bdA := dsOv dsyRg R₇ fun _ => [] with hF₀
  -- lookups
  have hlayW : ∀ y : SynW, S.R (dsyWr y) = [] := fun y =>
    hP.lay _ fun z => bdLayX_ne_wire z _
  have hpark : S.R (mnLay .park) = [] := hP.lay _ fun z => bdLayX_ne_park z
  have hwne : ∀ x : DsX, ∀ y : SynW, bdIo x ≠ dsyWr y := fun x y h =>
    bdLayX_ne_wire x _ (mnLay_inj h)
  have hpne : ∀ x : DsX, bdIo x ≠ mnLay .park := fun x h => bdLayX_ne_park x (mnLay_inj h)
  have l7io : ∀ x : DsX, F₀ (bdIo x) = bdO n x := fun x => by
    rw [hF₀, bdIo, dsyOv_lay, ← bdIo, hR₇]
    simp only [Function.update_of_ne (hwne x _), Function.update_of_ne (hpne x)]
    exact hio x
  have l7w : ∀ y : SynW, y ∉ [SynW.p .b, .p .Lg, .p .lr, .p .c, .p .es, .tw .pz] →
      F₀ (dsyWr y) = [] := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [hF₀, dsyWr, dsyOv_lay, ← dsyWr, hR₇]
    simp only [Function.update_apply, dsyWr, mnLay_inj.eq_iff, LReg.wire.injEq, synWire_eq_iff,
      hy, ite_false, reduceCtorEq]
    exact hlayW y
  -- the tail
  have hK : (bdO n .lK).length = K n := by simp [bdO, dsSrcO]
  have hL : (bdO n .lL).length = ℓ n := by simp [bdO, dsSrcO]
  have hD : (bdO n .lD).length = es.length := by simp [bdO, dsSrcO, hes, hlen]
  have hN : (bdO n .lN).length = es.sum := by simp [bdO, dsSrcO, hes, hsum]
  have hw : (bdO n .uw).length = dsW n := by simp [bdO]
  have hr : (bdO n .rR).length = r n := by simp [bdO, dsSrcO]
  have hlE : (bdO n .lE).length = dsWL n (dsW n) := by simp [bdO, dsSrcO]
  have hlW : (bdO n .lW).length = dsWL n (dsW n) := by simp [bdO, dsSrcO]
  have hlB : (bdO n .lB).length = r n * dsW n := by simp [bdO, dsSrcO]
  have huW : (bdO n .uW).length = dsWW n := by simp [bdO]
  have hKv : bdO n .lK = List.replicate (K n) tick := rfl
  have hLv : bdO n .lL = List.replicate (ℓ n) tick := rfl
  have hDv : bdO n .lD = List.replicate es.length tick := by rw [hes, hlen]; rfl
  have hNv : bdO n .lN = List.replicate es.sum tick := by rw [hes, hsum]; rfl
  have hwv : bdO n .uw = List.replicate (dsW n) tick := rfl
  have hrv : bdO n .rR = List.replicate (r n) tick := rfl
  have hine : ∀ x x' : DsX, x ≠ x' → bdIo x ≠ bdIo x' := fun x x' h => bdIo_inj.ne h
  have hwinj : ∀ y y' : SynW, y ≠ y' → dsyWr y ≠ dsyWr y' := fun y y' h e =>
    h (synWire_inj (LReg.wire.inj (mnLay_inj e)))
  -- the moves
  have m1 := dsyRuns_moveR (body := mnBody mnLb mainP) (hwne .lK (.p .K)) F₀
  rw [l7io, l7w _ (by decide), hKv, List.reverse_replicate, List.append_nil,
    List.length_replicate] at m1
  set F₁ := Function.update (Function.update F₀ (bdIo .lK) []) (dsyWr (.p .K))
    (List.replicate (K n) tick) with hF₁
  have f1 : ∀ k, k ≠ bdIo .lK → k ≠ dsyWr (.p .K) → F₁ k = F₀ k := fun k h1 h2 => by
    rw [hF₁, Function.update_of_ne h2, Function.update_of_ne h1]
  have m2 := dsyRuns_moveR (body := mnBody mnLb mainP) (hwne .lL (.p .ℓ)) F₁
  rw [f1 _ (hine _ _ (by decide)) (hwne _ _), f1 _ (hwne _ _).symm (hwinj _ _ (by decide)),
    l7io, l7w _ (by decide), hLv, List.reverse_replicate, List.append_nil,
    List.length_replicate] at m2
  set F₂ := Function.update (Function.update F₁ (bdIo .lL) []) (dsyWr (.p .ℓ))
    (List.replicate (ℓ n) tick) with hF₂
  have f2 : ∀ k, k ≠ bdIo .lK → k ≠ dsyWr (.p .K) → k ≠ bdIo .lL → k ≠ dsyWr (.p .ℓ) →
      F₂ k = F₀ k := fun k h1 h2 h3 h4 => by
    rw [hF₂, Function.update_of_ne h4, Function.update_of_ne h3, f1 k h1 h2]
  have m3 := dsyRuns_moveR (body := mnBody mnLb mainP) (hwne .lD (.p .D)) F₂
  rw [f2 _ (hine _ _ (by decide)) (hwne _ _) (hine _ _ (by decide)) (hwne _ _),
    f2 _ (hwne _ _).symm (hwinj _ _ (by decide)) (hwne _ _).symm (hwinj _ _ (by decide)),
    l7io, l7w _ (by decide), hDv, List.reverse_replicate, List.append_nil,
    List.length_replicate] at m3
  set F₃ := Function.update (Function.update F₂ (bdIo .lD) []) (dsyWr (.p .D))
    (List.replicate es.length tick) with hF₃
  have f3 : ∀ k, k ≠ bdIo .lK → k ≠ dsyWr (.p .K) → k ≠ bdIo .lL → k ≠ dsyWr (.p .ℓ) →
      k ≠ bdIo .lD → k ≠ dsyWr (.p .D) → F₃ k = F₀ k := fun k h1 h2 h3 h4 h5 h6 => by
    rw [hF₃, Function.update_of_ne h6, Function.update_of_ne h5, f2 k h1 h2 h3 h4]
  have m4 := dsyRuns_moveR (body := mnBody mnLb mainP) (hwne .lN (.p .N)) F₃
  rw [f3 _ (hine _ _ (by decide)) (hwne _ _) (hine _ _ (by decide)) (hwne _ _)
      (hine _ _ (by decide)) (hwne _ _),
    f3 _ (hwne _ _).symm (hwinj _ _ (by decide)) (hwne _ _).symm (hwinj _ _ (by decide))
      (hwne _ _).symm (hwinj _ _ (by decide)),
    l7io, l7w _ (by decide), hNv, List.reverse_replicate, List.append_nil,
    List.length_replicate] at m4
  set F₄ := Function.update (Function.update F₃ (bdIo .lN) []) (dsyWr (.p .N))
    (List.replicate es.sum tick) with hF₄
  have f4 : ∀ k, k ≠ bdIo .lK → k ≠ dsyWr (.p .K) → k ≠ bdIo .lL → k ≠ dsyWr (.p .ℓ) →
      k ≠ bdIo .lD → k ≠ dsyWr (.p .D) → k ≠ bdIo .lN → k ≠ dsyWr (.p .N) → F₄ k = F₀ k :=
    fun k h1 h2 h3 h4 h5 h6 h7 h8 => by
      rw [hF₄, Function.update_of_ne h8, Function.update_of_ne h7, f3 k h1 h2 h3 h4 h5 h6]
  have m5 := dsyRuns_moveR (body := mnBody mnLb mainP) (hwne .uw (.p .w)) F₄
  rw [f4 _ (hine _ _ (by decide)) (hwne _ _) (hine _ _ (by decide)) (hwne _ _)
      (hine _ _ (by decide)) (hwne _ _) (hine _ _ (by decide)) (hwne _ _),
    f4 _ (hwne _ _).symm (hwinj _ _ (by decide)) (hwne _ _).symm (hwinj _ _ (by decide))
      (hwne _ _).symm (hwinj _ _ (by decide)) (hwne _ _).symm (hwinj _ _ (by decide)),
    l7io, l7w _ (by decide), hwv, List.reverse_replicate, List.append_nil,
    List.length_replicate] at m5
  set F₅ := Function.update (Function.update F₄ (bdIo .uw) []) (dsyWr (.p .w))
    (List.replicate (dsW n) tick) with hF₅
  have f5 : ∀ k, k ≠ bdIo .lK → k ≠ dsyWr (.p .K) → k ≠ bdIo .lL → k ≠ dsyWr (.p .ℓ) →
      k ≠ bdIo .lD → k ≠ dsyWr (.p .D) → k ≠ bdIo .lN → k ≠ dsyWr (.p .N) →
      k ≠ bdIo .uw → k ≠ dsyWr (.p .w) → F₅ k = F₀ k :=
    fun k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
      rw [hF₅, Function.update_of_ne h10, Function.update_of_ne h9, f4 k h1 h2 h3 h4 h5 h6 h7 h8]
  have m6 := dsyRuns_moveR (body := mnBody mnLb mainP) (hwne .rR (.p .r)) F₅
  rw [f5 _ (hine _ _ (by decide)) (hwne _ _) (hine _ _ (by decide)) (hwne _ _)
      (hine _ _ (by decide)) (hwne _ _) (hine _ _ (by decide)) (hwne _ _)
      (hine _ _ (by decide)) (hwne _ _),
    f5 _ (hwne _ _).symm (hwinj _ _ (by decide)) (hwne _ _).symm (hwinj _ _ (by decide))
      (hwne _ _).symm (hwinj _ _ (by decide)) (hwne _ _).symm (hwinj _ _ (by decide))
      (hwne _ _).symm (hwinj _ _ (by decide)),
    l7io, l7w _ (by decide), hrv, List.reverse_replicate, List.append_nil,
    List.length_replicate] at m6
  set F₆ := Function.update (Function.update F₅ (bdIo .rR) []) (dsyWr (.p .r))
    (List.replicate (r n) tick) with hF₆
  have f6 : ∀ k, k ≠ bdIo .lK → k ≠ dsyWr (.p .K) → k ≠ bdIo .lL → k ≠ dsyWr (.p .ℓ) →
      k ≠ bdIo .lD → k ≠ dsyWr (.p .D) → k ≠ bdIo .lN → k ≠ dsyWr (.p .N) →
      k ≠ bdIo .uw → k ≠ dsyWr (.p .w) → k ≠ bdIo .rR → k ≠ dsyWr (.p .r) → F₆ k = F₀ k :=
    fun k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => by
      rw [hF₆, Function.update_of_ne h12, Function.update_of_ne h11,
        f5 k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]
  have f6io : ∀ x : DsX, x ∉ [DsX.lK, .lL, .lD, .lN, .uw, .rR] → F₆ (bdIo x) = bdO n x :=
    fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [f6 _ (hine _ _ hx.1) (hwne _ _) (hine _ _ hx.2.1) (hwne _ _) (hine _ _ hx.2.2.1)
        (hwne _ _) (hine _ _ hx.2.2.2.1) (hwne _ _) (hine _ _ hx.2.2.2.2.1) (hwne _ _)
        (hine _ _ hx.2.2.2.2.2) (hwne _ _), l7io]
  -- the clears
  have c1 := dsyRuns_bclear (body := mnBody mnLb mainP) (bdIo .lE) F₆
  rw [f6io _ (by decide), hlE] at c1
  set F₇ := Function.update F₆ (bdIo .lE) [] with hF₇
  have e7 : F₇ (bdIo .lW) = bdO n .lW := by
    rw [hF₇, Function.update_of_ne (hine _ _ (by decide)), f6io _ (by decide)]
  have c2 := dsyRuns_bclear (body := mnBody mnLb mainP) (bdIo .lW) F₇
  rw [e7, hlW] at c2
  set F₈ := Function.update F₇ (bdIo .lW) [] with hF₈
  have e8 : F₈ (bdIo .lB) = bdO n .lB := by
    rw [hF₈, Function.update_of_ne (hine _ _ (by decide)), hF₇,
      Function.update_of_ne (hine _ _ (by decide)), f6io _ (by decide)]
  have c3 := dsyRuns_bclear (body := mnBody mnLb mainP) (bdIo .lB) F₈
  rw [e8, hlB] at c3
  set F₉ := Function.update F₈ (bdIo .lB) [] with hF₉
  have e9 : F₉ (bdIo .uW) = bdO n .uW := by
    rw [hF₉, Function.update_of_ne (hine _ _ (by decide)), hF₈,
      Function.update_of_ne (hine _ _ (by decide)), hF₇,
      Function.update_of_ne (hine _ _ (by decide)), f6io _ (by decide)]
  have c4 := dsyRuns_bclear (body := mnBody mnLb mainP) (bdIo .uW) F₉
  rw [e9, huW] at c4
  set F₁₀ := Function.update F₉ (bdIo .uW) [] with hF₁₀
  have hall := hrun.seq (m1.seq (m2.seq (m3.seq (m4.seq (m5.seq (m6.seq (c1.seq (c2.seq
    (c3.seq c4)))))))))
  obtain ⟨v', S', m, -, hm, he, hR, hinp, hout, hL'⟩ := hall v S rfl
  -- the final file off the layer registers
  have hoff : ∀ k, (∀ x, k ≠ mnLay x) → F₁₀ k = F₀ k := fun k hk => by
    have h1 : ∀ x, k ≠ bdIo x := fun x => hk _
    have h2 : ∀ y, k ≠ dsyWr y := fun y => hk _
    rw [hF₁₀, Function.update_of_ne (h1 _), hF₉, Function.update_of_ne (h1 _), hF₈,
      Function.update_of_ne (h1 _), hF₇, Function.update_of_ne (h1 _),
      f6 k (h1 _) (h2 _) (h1 _) (h2 _) (h1 _) (h2 _) (h1 _) (h2 _) (h1 _) (h2 _) (h1 _) (h2 _)]
  have hoff7 : ∀ k, (∀ x, k ≠ mnLay x) → R₇ k = S.R k := fun k hk => by
    rw [hR₇]
    simp only [dsyWr] at hk ⊢
    rw [Function.update_of_ne (hk _), Function.update_of_ne (hk _), Function.update_of_ne (hk _),
      Function.update_of_ne (hk _), Function.update_of_ne (hk _), Function.update_of_ne (hk _),
      Function.update_of_ne (hk _)]
  refine ⟨v', S', m, ?_, he, hinp, hout, hL', fun j => ?_, fun x => ?_, fun r _ => ?_⟩
  · -- the cost
    refine hm.trans ?_
    unfold dsyWiresCost dsyTailCost
    rw [← hes]
  · -- the scratch registers
    rw [hR, hoff _ (fun x => mnι_ne_lay j x), hF₀]
    by_cases h : ∃ r, dsyRg r = mnι j
    · obtain ⟨r, hr⟩ := h
      rw [← hr, dsOv_rg dsyRg_inj]
    · push Not at h
      rw [dsOv_off _ _ h, hoff7 _ (fun x => mnι_ne_lay j x)]
      exact hι j
  · -- the layer registers
    rw [hR]
    have hlayW' : ∀ y : SynW, S.R (mnLay (.wire (synWire y))) = [] := hlayW
    have hev : ∀ x : LReg SXReg, x ≠ .park → (∀ y, x ≠ .wire (synWire y)) →
        (∀ z, x ≠ bdLayX z) → F₁₀ (mnLay x) = S.R (mnLay x) := fun x h1 h2 h3 => by
      have h1' : ∀ y, mnLay x ≠ dsyWr y := fun y e => h2 y (mnLay_inj e)
      have h3' : ∀ z, mnLay x ≠ bdIo z := fun z e => h3 z (mnLay_inj e)
      rw [hF₁₀, Function.update_of_ne (h3' _), hF₉, Function.update_of_ne (h3' _), hF₈,
        Function.update_of_ne (h3' _), hF₇, Function.update_of_ne (h3' _),
        f6 _ (h3' _) (h1' _) (h3' _) (h1' _) (h3' _) (h1' _) (h3' _) (h1' _) (h3' _) (h1' _)
          (h3' _) (h1' _), hF₀, dsyOv_lay, hR₇]
      rw [Function.update_of_ne (h1' _), Function.update_of_ne (h1' _),
        Function.update_of_ne (h1' _), Function.update_of_ne (h1' _),
        Function.update_of_ne (h1' _), Function.update_of_ne (h1' _),
        Function.update_of_ne (fun e => h1 (mnLay_inj e))]
    have hevw : ∀ y, y ∉ [SynW.p .K, .p .ℓ, .p .D, .p .N, .p .w, .p .r, .p .b, .p .Lg, .p .lr,
        .p .c, .p .es, .tw .pz] → F₁₀ (dsyWr y) = [] := fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      rw [hF₁₀, Function.update_of_ne (hwne _ _).symm, hF₉, Function.update_of_ne (hwne _ _).symm,
        hF₈, Function.update_of_ne (hwne _ _).symm, hF₇, Function.update_of_ne (hwne _ _).symm,
        f6 _ (hwne _ _).symm (hwinj _ _ hy.1) (hwne _ _).symm (hwinj _ _ hy.2.1)
          (hwne _ _).symm (hwinj _ _ hy.2.2.1) (hwne _ _).symm (hwinj _ _ hy.2.2.2.1)
          (hwne _ _).symm (hwinj _ _ hy.2.2.2.2.1) (hwne _ _).symm (hwinj _ _ hy.2.2.2.2.2.1),
        l7w _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨hy.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.1,
            hy.2.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2.2.2⟩)]
    have hpw : ∀ y, mnLay .park ≠ dsyWr y := fun y e => by
      have := mnLay_inj e; simp [dsyWr] at this
    cases x
    case park =>
      rw [mnσ_park, hF₁₀, Function.update_of_ne (hpne _).symm, hF₉,
        Function.update_of_ne (hpne _).symm, hF₈, Function.update_of_ne (hpne _).symm, hF₇,
        Function.update_of_ne (hpne _).symm,
        f6 _ (hpne _).symm (hpw _) (hpne _).symm (hpw _) (hpne _).symm (hpw _) (hpne _).symm
          (hpw _) (hpne _).symm (hpw _) (hpne _).symm (hpw _), hF₀, dsyOv_lay, hR₇]
      rw [Function.update_of_ne (hpw _), Function.update_of_ne (hpw _),
        Function.update_of_ne (hpw _), Function.update_of_ne (hpw _),
        Function.update_of_ne (hpw _), Function.update_of_ne (hpw _), Function.update_self,
        hpark, List.append_nil]
    case wire v =>
      by_cases hv : ∃ y, synWire y = v
      · obtain ⟨y, rfl⟩ := hv
        rw [mnσ_wire]
        show F₁₀ (dsyWr y) = _
        rcases y with w | i | q | i
        · by_cases hw : w = .pz
          · subst hw
            simp only [hF₁₀, hF₉, hF₈, hF₇, hF₆, hF₅, hF₄, hF₃, hF₂, hF₁, hF₀, dsyOv_lay, hR₇,
              Function.update_apply, dsyWr, bdIo, mnLay_inj.eq_iff, LReg.wire.injEq,
              synWire_eq_iff, SynW.p.injEq, SynW.tw.injEq, dsy_wire_ne_bdLayX, reduceCtorEq,
              ite_true, ite_false, hlayW', List.append_nil]
            rfl
          · rw [hevw _ (by simp [hw])]
            cases w <;> first | rfl | exact absurd rfl hw
        · rw [hevw _ (by simp)]; rfl
        · cases q
          all_goals first
            | (rw [hevw _ (by decide)]; rfl)
            | (simp only [hF₁₀, hF₉, hF₈, hF₇, hF₆, hF₅, hF₄, hF₃, hF₂, hF₁, hF₀, dsyOv_lay,
                hR₇, Function.update_apply, dsyWr, bdIo, mnLay_inj.eq_iff, LReg.wire.injEq,
                synWire_eq_iff, SynW.p.injEq, SynW.tw.injEq, dsy_wire_ne_bdLayX, reduceCtorEq,
                ite_true, ite_false, hlayW', List.append_nil]
               rfl)
        · rw [hevw _ (by simp)]; rfl
      · rw [dsy_mnσ_wire_off _ _ (fun y h => hv ⟨y, h⟩),
          hev _ (by simp) (fun y e => hv ⟨y, (LReg.wire.inj e).symm⟩)
            (fun z => dsy_wire_ne_bdLayX _ _),
          hP.lay _ (fun z => bdLayX_ne_wire z v)]
    case wtmp v =>
      rw [mnσ_eq_nil _ _ (by simp) (by simp)]
      by_cases hz : ∃ z, bdLayX z = .wtmp v
      · obtain ⟨z, hz⟩ := hz
        rw [← hz]
        show F₁₀ (bdIo z) = []
        cases z
        all_goals
          simp only [hF₁₀, hF₉, hF₈, hF₇, hF₆, hF₅, hF₄, hF₃, hF₂, hF₁, Function.update_apply,
            bdIo_inj.eq_iff, hwne, reduceCtorEq, ite_true, ite_false, l7io]
        all_goals rfl
      · rw [hev _ (by simp) (fun y => by simp) (fun z h => hz ⟨z, h.symm⟩),
          hP.lay _ (fun z h => hz ⟨z, h⟩)]
    all_goals
      rw [hev _ (by simp) (fun y => by simp) (fun z => by simp [bdLayX]),
        hP.lay _ (fun z => by simp [bdLayX]), mnσ_eq_nil _ _ (fun y => by simp) (by simp)]
  · -- the kept registers
    rw [hR, hoff _ (fun x => mnRg_ne_lay r x), hF₀,
      dsOv_off (rg := dsyRg) _ _ (fun q => (mnRg_ne_ι r (dsyIdx q)).symm),
      hoff7 _ (fun x => mnRg_ne_lay r x)]


end

end IntegerMultBounds.MathlibTM2.Fast.Main
