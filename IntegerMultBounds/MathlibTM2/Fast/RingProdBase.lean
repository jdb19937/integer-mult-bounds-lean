module

public import IntegerMultBounds.Schoenhage.RingLemma
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream
public import IntegerMultBounds.MathlibTM2.Mult.SynthErr

/-!
# The vendored ring product as a host subroutine: machine, banks and formats

The vendored signed ring product `ringLemmaProgram` (`Schoenhage/RingLemma`: header decoder
`decodeHeader3`, constants, one packed Schönhage–Strassen product per record pair) runs on any
number of record pairs.

**The contract on arrays** (`rp_vendor_hoare`). Tape 0 holds the header `Γ(p)Γ(r)Γ(w)`
(`header p r w`, `r = 2^l`), tapes 1 and 2 the arrays `array w fs`, `array w gs` of `M` records
each (`Spec.SignedRingProduct.array`: each coefficient as the real then the imaginary numerator,
both signed `w`-bit two's-complement words, most significant bit first), tape 3 is empty. For
`1 ≤ p`, `p + 2 ≤ w` and disk-grid records the program halts within `rpTime p l w M` transitions
with tapes 0–2 unchanged and `array w (zipWith (prodRec p) fs gs)` on tape 3: record `n` is
`Q_p(f_n g_n / r)` (`prodRec`). This is `runs_pwCoreWith` with the three-code header decoder,
sealed, compiled and relabelled exactly as in `ring_meets`. `rpTime` is the vendored
`pwCost p 0 l 0 w H M X` plus the sealing overhead; `pwCost` charges
`M (r (56 w + 400) + ringCost W r w (p + l) (W r) + 204)` for the records, `W = wOf p l w`, with
`ringCost` the bound of the packed product (`ringProgram`, truncation by `s = p + l` bits).

**On the host** (`rpMachine`, `rpMachine_hoare`). The program runs through the alphabet
encoding `SS.code A` (`Fin 4` into `Fin (A + 4)`, every symbol keeps its code) with its states
embedded by `liftQ`. Its banks are raw bit words: tape `j` holds `rpCells A hdr F G out j`
(the bit symbols of the header, the two operands and the output on tapes 0–3, nothing
elsewhere) from cell 0, heads at cell 0.

**Placed runs on raw words** (`rp_placedRun_exec`): `placedRun` (of `Host/SSMul`) with an exact
contract between banks of blank-free words. The placed registers go from the start words to
the final words, every other stack is unchanged.

**Formats.** `rpLsb w v` are the `w` low bits of `v`, least significant first;
`msbBits w v = (rpLsb w v).reverse`. A host coefficient `csyms A w z` carries the bits
`rpLsb w (red w z).1.val` and `rpLsb w (red w z).2.val` as pair symbols; a vendored coefficient
is `rpChunk w z = compWord w z.re ++ compWord w z.im`, the two reversed bit lists
(`rp_compWord_eq_rev`). `rp_array_eq_chunks`: an array is the chunks of its coefficients in order
(`rpCoeffs`).

**Automata.** `rpEncAuto` copies a pair symbol and splits it into its real and imaginary bit
symbols, `rpCpyAuto` copies, `rpZipAuto` pairs two bit symbols; all are stateless, so a word's
outputs are the symbolwise images of its input columns (`rp_runWord_stateless`,
`rp_cols_one`, `rp_cols_two`).
-/

@[expose] public section


set_option maxRecDepth 10000

namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Spec.SignedRingProduct

noncomputable section

/-! ### The vendored contract on arrays -/

section Vendor

open IntegerMultBounds.Schoenhage

/-- The vendored time bound of the ring product on `M` record pairs of `2^l` coefficients:
the word-level bound `pwCost` and the cost of sealing and unsealing the four data tapes. -/
def rpTime (p l w M : ℕ) : ℕ :=
  pwCost p 0 l 0 w (header p (2 ^ l) w).length M (2 * 2 ^ l * w * M) +
    4 * ((header p (2 ^ l) w).length + 3 * (2 * 2 ^ l * w * M)) + 60

set_option maxHeartbeats 4000000 in
/-- The vendored ring product on arrays of record pairs. -/
theorem rp_vendor_hoare {p l w : ℕ} {fs gs : List (Rec (2 ^ l))} (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (hlen : fs.length = gs.length) (hf : ∀ f ∈ fs, DiskGrid p f.1 f.2)
    (hg : ∀ g ∈ gs, DiskGrid p g.1 g.2) :
    HoareTime ringLemmaProgram
      (· = bank (header p (2 ^ l) w) (array w fs) (array w gs) [])
      (· = bank (header p (2 ^ l) w) (array w fs) (array w gs)
        (array w (List.zipWith (prodRec p) fs gs)))
      (rpTime p l w fs.length) := by
  obtain ⟨σ', k, hx, hq, hk⟩ := runs_pwCoreWith (fs := fs) (gs := gs)
    (hdrDecodes_decodeHeader3 (l := l) hp (by omega)) hw hlen hf hg
  subst hq
  have h4 := (compile_correct (by decide) hx).consequence (fun _ h => h) (fun _ h => h) hk
  have h := (pwProg91With_hoare (core := ringCoreProg) h4).reindex dataSwap
  refine h.consequence (fun v hv => ⟨_, rfl, by rw [hv, raw91_reindex]⟩)
    (fun v ⟨o, ho, hv⟩ => by rw [hv, ho, raw91_reindex]) ?_
  have hF : (array w fs).length = 2 * 2 ^ l * w * fs.length := by rw [length_array]
  have hG : (array w gs).length = 2 * 2 ^ l * w * fs.length := by rw [length_array, hlen]
  have hO : (array w (List.zipWith (prodRec p) fs gs)).length = 2 * 2 ^ l * w * fs.length := by
    rw [length_array, List.length_zipWith, hlen, min_self]
  unfold rpTime
  rw [hF, hG, hO]
  omega

/-- The state count of the vendored ring product. -/
abbrev rpStates : ℕ := stateCount ringLemmaProgram

end Vendor

/-! ### Raw banks over the host alphabet -/

/-- The words of the ring product's raw bank: header and operands on tapes `0`, `1`, `2`, the
output on tape `3`, every other tape empty. -/
def rpCells (A : ℕ) (hdr F G out : List Bool) (j : Fin 91) : List (Fin (A + 4)) :=
  if j.val = 0 then hdr.map bitSymbol else if j.val = 1 then F.map bitSymbol
  else if j.val = 2 then G.map bitSymbol else if j.val = 3 then out.map bitSymbol else []

/-- The raw bank with heads at cell `0`. -/
def rpRaw (A : ℕ) (hdr F G out : List Bool) : Tapes 91 A :=
  ⟨fun _ => 0, fun j => wordTape (rpCells A hdr F G out j)⟩

lemma rp_code_bitSymbol (A : ℕ) (b : Bool) : (SS.code A).encode (bitSymbol b) = bitSymbol b := by
  cases b <;> rfl

lemma rp_bitSymbol_ne_blank {A : ℕ} (b : Bool) : (bitSymbol b : Fin (A + 4)) ≠ blank := by
  cases b <;> simp [bitSymbol, blank, Fin.ext_iff]

lemma rp_blank_not_mem_cells (A : ℕ) (hdr F G out : List Bool) (j : Fin 91) :
    blank ∉ rpCells A hdr F G out j := by
  unfold rpCells
  split_ifs <;> simp [rp_bitSymbol_ne_blank]

/-- The encoded vendored bank is the raw host bank. -/
lemma rp_map_bank (A : ℕ) (hdr F G out : List Bool) :
    Alphabet.mapTapes (SS.code A) (bank (t := 91) (a := 0) hdr F G out) = rpRaw A hdr F G out := by
  simp only [Alphabet.mapTapes, bank, rpRaw, Tapes.mk.injEq, true_and]
  funext j z
  simp only [rpCells]
  split_ifs
  any_goals simp [wordAt, SS.code_wordTape, List.map_map, Function.comp_def, rp_code_bitSymbol]
  simp [wordTape_nil]
  rfl

/-- The vendored ring product over the host alphabet with its states embedded in `Fin Q`. -/
def rpMachine (A : ℕ) {Q : ℕ} (hQ : rpStates ≤ Q) : Program 91 Q A :=
  liftQ (Alphabet.program (SS.code A) IntegerMultBounds.Schoenhage.ringLemmaProgram) hQ

/-- `rp_vendor_hoare` on the raw host banks. -/
theorem rpMachine_hoare (A : ℕ) {Q : ℕ} (hQ : rpStates ≤ Q) {p l w : ℕ}
    {fs gs : List (Rec (2 ^ l))} (hp : 1 ≤ p) (hw : p + 2 ≤ w) (hlen : fs.length = gs.length)
    (hf : ∀ f ∈ fs, DiskGrid p f.1 f.2) (hg : ∀ g ∈ gs, DiskGrid p g.1 g.2) :
    HoareTime (rpMachine A hQ)
      (· = rpRaw A (header p (2 ^ l) w) (array w fs) (array w gs) [])
      (· = rpRaw A (header p (2 ^ l) w) (array w fs) (array w gs)
        (array w (List.zipWith (prodRec p) fs gs)))
      (rpTime p l w fs.length) := by
  refine HoareTime.liftQ hQ ((Alphabet.map_hoare (SS.code A)
    (rp_vendor_hoare hp hw hlen hf hg)).consequence
    (fun w hw => ⟨_, rfl, by rw [hw, rp_map_bank]⟩) (fun w ⟨o, ho, hw⟩ => ?_) le_rfl)
  rw [hw, ho, rp_map_bank]

/-! ### Placed runs on raw words -/

section PlacedRaw

variable {s T Q A : ℕ} {U F : Type}

/-- Running a placed program with an exact contract between banks of blank-free words from
cell `0`. The placed registers hold the start words with empty left stacks; afterwards they hold
the final words, and every other stack is unchanged. -/
theorem rp_placedRun_exec (body : F → Pr F T Q A U) (M : Program s Q A) (ι : Fin s → Fin T)
    (hι : Function.Injective ι) (hT : s ≤ T) {l₀ l₁ : Fin s → List (Fin (A + 4))} {k : ℕ}
    (hM : HoareTime M (· = ⟨fun _ => 0, fun j => wordTape (l₀ j)⟩)
      (· = ⟨fun _ => 0, fun j => wordTape (l₁ j)⟩) k)
    (hb : ∀ j, blank ∉ l₁ j) (v : HS T Q A U) (S : Stacks T A) (hL : ∀ j, S.L (ι j) = [])
    (hR : ∀ j, S.R (ι j) = l₀ j) :
    ∃ v' n R', v'.user = v.user ∧
      n ≤ (T + 12 * s + 5) * k + 6 * ∑ j, (S.R (ι j)).length + 2 * T + 6 * s + 9 ∧
      (∀ j, R' (ι j) = l₁ j) ∧ (∀ y, (∀ j, ι j ≠ y) → R' y = S.R y) ∧
      Exec body (placedRun M ι hι hT) (mk v S) n (mk v' { S with R := R' }) := by
  classical
  set pe := InjectivePlacement.placement ι hι (Nat.add_sub_cancel' hT) with hpe
  have hun : ∀ j, ι j ∉ unplaced ι := fun j hm => (mem_unplaced ι _).1 hm j rfl
  -- step 1: mark the unplaced registers
  have he₀ := markList_exec body (unplaced ι) (unplaced_nodup ι) v S
  set S₀ : Stacks T A :=
    { S with R := fun y => if y ∈ unplaced ι then blank :: S.R y else S.R y } with hS₀
  have hS₀ι : ∀ j, S₀.R (ι j) = S.R (ι j) := fun j => by simp [S₀, hun j]
  -- the host bank represented by `S₀`
  let w₀ : Tapes T A := ⟨fun _ => 0, fun y z => readAt blank (S₀.L y) (S₀.R y) z⟩
  let W := Placement.replace pe w₀ ⟨fun _ => 0, fun j => wordTape (l₀ j)⟩
  have hrep : RepT W S₀.L S₀.R := by
    intro y z
    by_cases hy : ∃ j, ι j = y
    · obtain ⟨j, rfl⟩ := hy
      rw [InjectivePlacement.replace_tape_slot, InjectivePlacement.replace_head_slot]
      show wordTape (l₀ j) z = readAt blank (S.L (ι j)) (S₀.R (ι j)) (z - 0)
      rw [hL j, hS₀ι, hR j, sub_zero, readAt_nil_left]
    · have hy' : ∀ j, ι j ≠ y := fun j hj => hy ⟨j, hj⟩
      rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ hy',
        InjectivePlacement.replace_head_other _ _ _ _ _ _ hy']
      show readAt blank (S₀.L y) (S₀.R y) z = readAt blank (S₀.L y) (S₀.R y) (z - 0)
      rw [sub_zero]
  have hpre := Placement.hoare_at hM pe W (Placement.active_replace pe w₀ _)
  -- step 2: run the placed program
  obtain ⟨v₂, S₂, W', ⟨w', hw', hW'⟩, hrep', hu₂, hinp₂, hout₂, hlen₂, hfr₂, m₂, hm₂, he₂⟩ :=
    foreign_exec_frame body _ (placed_idle_injective M ι hι _) hpre v S₀ W rfl hrep
  subst hw'
  have hsweep : ∀ j, sweep (S₂.L (ι j)) (S₂.R (ι j)) = l₁ j := by
    intro j
    refine filter_window (S₂.L (ι j)) (S₂.R (ι j)) (W'.head (ι j)) _ (hb j) (fun z => ?_)
    have := hrep' (ι j) z
    rw [hW', InjectivePlacement.replace_tape_slot] at this
    rw [hW', ← this]
  have hS₂un : ∀ y, (∀ j, ι j ≠ y) → S₂.L y = S.L y ∧ S₂.R y = blank :: S.R y := by
    intro y hy
    have hu : y ∈ unplaced ι := (mem_unplaced ι y).2 hy
    have h₂ := idle_stacks_eq (hfr₂ y hy) (by simp [S₀, hu])
    exact ⟨h₂.1, h₂.2.trans (by simp [S₀, hu])⟩
  -- step 3: normalize the placed registers
  obtain ⟨v₃, n₃, hu₃, hn₃, he₃⟩ :=
    normList_exec body (List.ofFn ι) (List.nodup_ofFn.2 hι) v₂ S₂
  -- step 4: unmark the unplaced registers
  have he₄ := dropList_exec body (unplaced ι) (unplaced_nodup ι) v₃ { S₂ with
    L := fun i => if i ∈ List.ofFn ι then [] else S₂.L i
    R := fun i => if i ∈ List.ofFn ι then sweep (S₂.L i) (S₂.R i) else S₂.R i }
  refine ⟨v₃, ((unplaced ι).length + 1) + (m₂ + (n₃ + ((unplaced ι).length + 1))),
    fun y => if y ∈ unplaced ι then
      (if y ∈ List.ofFn ι then sweep (S₂.L y) (S₂.R y) else S₂.R y).tail
      else if y ∈ List.ofFn ι then sweep (S₂.L y) (S₂.R y) else S₂.R y,
    hu₃.trans hu₂, ?_, fun j => ?_, fun y hy => ?_,
    Exec.cast (Exec.seq he₀ (Exec.seq he₂ (Exec.seq he₃ he₄))) rfl ?_⟩
  · rw [List.map_ofFn, List.sum_ofFn] at hn₃
    have hsum : ∑ j, ((fun i => 6 * ((S₂.L i).length + (S₂.R i).length) + 6) ∘ ι) j ≤
        ∑ j, (6 * (S.R (ι j)).length + (12 * k + 6)) := by
      apply Finset.sum_le_sum
      intro j _
      have h1 := hlen₂ (ι j)
      have h2 : S₀.L (ι j) = [] := hL j
      rw [h2, hS₀ι] at h1
      simp only [Function.comp_apply, List.length_nil] at h1 ⊢
      omega
    have hR : ∑ j : Fin s, (6 * (S.R (ι j)).length + (12 * k + 6)) =
        6 * ∑ j, (S.R (ι j)).length + s * (12 * k + 6) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    have key : k * (T + 5) + s * (12 * k + 6) = (T + 12 * s + 5) * k + 6 * s := by ring
    have hu := unplaced_length_le ι
    omega
  · have hm : ι j ∈ List.ofFn ι := List.mem_ofFn.2 ⟨j, rfl⟩
    simp only [hun j, hm, ite_true, ite_false]
    exact hsweep j
  · have hm : y ∉ List.ofFn ι := fun hm => by
      obtain ⟨j, hj⟩ := List.mem_ofFn.1 hm
      exact hy j hj
    have hu : y ∈ unplaced ι := (mem_unplaced ι y).2 hy
    simp only [hu, hm, ite_true, ite_false, (hS₂un y hy).2, List.tail_cons]
  · congr 1
    refine Stacks.ext hinp₂ hout₂ ?_ rfl
    funext y
    by_cases hy : y ∈ List.ofFn ι
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
      simp only [hy, ite_true, hL j]
    · have hy' : ∀ j, ι j ≠ y := fun j hj => hy (List.mem_ofFn.2 ⟨j, hj⟩)
      simp only [hy, ite_false, (hS₂un y hy').1]

end PlacedRaw

/-! ### Bit formats -/

/-- The `w` low bits of `v`, least significant first. -/
def rpLsb (w v : ℕ) : List Bool := List.ofFn fun t : Fin w => v.testBit t

@[simp] lemma length_rpLsb (w v : ℕ) : (rpLsb w v).length = w := by simp [rpLsb]

/-- Most significant bit first is the reverse of least significant bit first. -/
lemma rp_msbBits_eq_rev (w v : ℕ) : msbBits w v = (rpLsb w v).reverse := by
  induction w with
  | zero => rfl
  | succ n ih =>
      have e : rpLsb (n + 1) v = rpLsb n v ++ [v.testBit n] := by
        simp only [rpLsb, List.ofFn_succ', List.concat_eq_append, Fin.val_castSucc, Fin.val_last]
      rw [msbBits, ih, e, List.reverse_append]
      simp [Nat.testBit_eq_decide_div_mod_eq]

/-- A two's-complement word is the reversed low bits of the residue. -/
lemma rp_compWord_eq_rev (w : ℕ) (x : ℤ) :
    compWord w x = (rpLsb w (x : ZMod (2 ^ w)).val).reverse := by
  rw [compWord, rp_msbBits_eq_rev]
  congr 2
  have h := ZMod.val_intCast (n := 2 ^ w) x
  push_cast at h
  omega

/-- The vendored chunk of a coefficient: its real then its imaginary numerator. -/
def rpChunk (w : ℕ) (z : GaussianInt) : List Bool := compWord w z.re ++ compWord w z.im

@[simp] lemma length_rpChunk (w : ℕ) (z : GaussianInt) : (rpChunk w z).length = 2 * w := by
  simp [rpChunk, compWord]; ring

/-- The coefficients of a list of records, in order. -/
def rpCoeffs {r : ℕ} (fs : List (Rec r)) : List GaussianInt :=
  fs.flatMap fun f => List.ofFn fun c => (⟨f.1 c, f.2 c⟩ : GaussianInt)

/-- An array is the chunks of its coefficients. -/
lemma rp_array_eq_chunks {r : ℕ} (w : ℕ) (fs : List (Rec r)) :
    array w fs = (rpCoeffs fs).flatMap (rpChunk w) := by
  simp only [array, record, rpCoeffs, List.flatMap_assoc, rpChunk, List.ofFn_eq_map,
    List.flatMap_map]

/-- The real bits of a host coefficient. -/
lemma rp_csyms_map_re {A : ℕ} (hA : 4 ≤ A) (w : ℕ) (z : GaussianInt) :
    (csyms A w z).map (fun x => (bitSymbol (pairRe x) : Fin (A + 4))) =
      (rpLsb w (z.re : ZMod (2 ^ w)).val).map bitSymbol := by
  simp [csyms, coeffSyms, rpLsb, List.map_ofFn, Function.comp_def, pairRe_pairSym hA, red]

/-- The imaginary bits of a host coefficient. -/
lemma rp_csyms_map_im {A : ℕ} (hA : 4 ≤ A) (w : ℕ) (z : GaussianInt) :
    (csyms A w z).map (fun x => (bitSymbol (pairIm x) : Fin (A + 4))) =
      (rpLsb w (z.im : ZMod (2 ^ w)).val).map bitSymbol := by
  simp [csyms, coeffSyms, rpLsb, List.map_ofFn, Function.comp_def, pairIm_pairSym hA, red]

/-- Pairing the real and imaginary bits gives the host coefficient. -/
lemma rp_zip_csyms {A : ℕ} (w : ℕ) (z : GaussianInt) :
    List.zipWith (fun x y : Fin (A + 4) => pairSym A (symBit x) (symBit y))
      ((rpLsb w (z.re : ZMod (2 ^ w)).val).map bitSymbol)
      ((rpLsb w (z.im : ZMod (2 ^ w)).val).map bitSymbol) = csyms A w z := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp [csyms, coeffSyms, rpLsb, red]

/-! ### Stateless automata -/

section Autos

variable {A : ℕ}

/-- Copy a pair symbol and split it into its real and imaginary bit symbols. -/
def rpEncAuto (A : ℕ) : Auto A 1 3 where
  init := blank
  step s c := (s, ![c 0, bitSymbol (pairRe (c 0)), bitSymbol (pairIm (c 0))])

/-- Copy a symbol. -/
def rpCpyAuto (A : ℕ) : Auto A 1 1 where
  init := blank
  step s c := (s, fun _ => c 0)

/-- Pair a real and an imaginary bit symbol. -/
def rpZipAuto (A : ℕ) : Auto A 2 1 where
  init := blank
  step s c := (s, fun _ => pairSym A (symBit (c 0)) (symBit (c 1)))

/-- A stateless automaton maps each input column. -/
lemma rp_runWord_stateless {ni no : ℕ} (M : Auto A ni no) (hM : ∀ s c, (M.step s c).1 = s) :
    ∀ (s : Fin (A + 4)) (cs : List (Fin ni → Fin (A + 4))),
      M.runWord s cs = cs.map fun c => (M.step s c).2 := by
  intro s cs
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [Auto.runWord, hM, ih]

/-- The columns of a word, mapped through the symbol of one register, read off that register. -/
lemma rp_cols_one {ni : ℕ} {β : Type} (L : Fin ni → List (Fin (A + 4))) (i : Fin ni)
    (c rest : List (Fin (A + 4))) (hL : L i = c ++ rest) {len : ℕ} (hc : c.length = len)
    (f : (Fin ni → Fin (A + 4)) → β) (g : Fin (A + 4) → β) (hf : ∀ col, f col = g (col i)) :
    (Auto.cols L len 0).map f = c.map g := by
  subst hc
  apply List.ext_getElem (by simp [Auto.cols])
  intro t h₁ h₂
  simp only [List.length_map] at h₂
  simp [Auto.cols, hf, hL, List.getD_eq_getElem?_getD, List.getElem?_append_left h₂,
    List.getElem?_eq_getElem h₂]

/-- The columns of a word, mapped through the symbols of two registers, read off both. -/
lemma rp_cols_two {ni : ℕ} {β : Type} (L : Fin ni → List (Fin (A + 4))) (i i' : Fin ni)
    (c c' rest rest' : List (Fin (A + 4))) (hL : L i = c ++ rest) (hL' : L i' = c' ++ rest')
    {len : ℕ} (hc : c.length = len) (hc' : c'.length = len)
    (f : (Fin ni → Fin (A + 4)) → β) (g : Fin (A + 4) → Fin (A + 4) → β)
    (hf : ∀ col, f col = g (col i) (col i')) :
    (Auto.cols L len 0).map f = List.zipWith g c c' := by
  subst hc
  apply List.ext_getElem (by simp [Auto.cols, hc'])
  intro t h₁ h₂
  simp only [List.length_map, Auto.cols, List.length_range] at h₁
  have h₃ : t < c'.length := by omega
  simp [Auto.cols, hf, hL, hL', List.getD_eq_getElem?_getD, List.getElem?_append_left h₁,
    List.getElem?_append_left h₃, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₃]

end Autos

end

end IntegerMultBounds.MathlibTM2.Fast
