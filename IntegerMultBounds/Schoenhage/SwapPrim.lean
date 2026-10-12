module

public import IntegerMultBounds.Schoenhage.CounterWords
public import IntegerMultBounds.Schoenhage.Seal
public import IntegerMultBounds.Schoenhage.ProgPrim
public import IntegerMultBounds.Machine.BinaryInterchangeRun

/-! The address-field interchange of §4 on word tapes. Six caller tapes hold
one word each: the headers `P, G, B, h, d` and the payload. The program turns
the headers into the interchange's counter form and the payload into raw bits
(`convIn`), runs `BinaryInterchangeRun.program`, and converts back
(`convOut`); the interchange's private tapes are the remaining empty word
tapes (`enc_input`). `prim` is the result as a word-program primitive: the
payload's `2^h` and `2^d` address fields are interchanged (`swapped`). -/

@[expose] public section

namespace IntegerMultBounds.Schoenhage.SwapPrim
noncomputable section

open Machine
open Networks.Shared50ModularControl (prime)

variable {t a s : ℕ}

/-! ### The interchange's private tapes -/

/-- A bank of blank tapes with heads at zero. -/
def Blank (v : Tapes s a) : Prop := ∀ z, v.head z = 0 ∧ v.tape z = fun _ => blank

theorem append_head (v : Tapes t a) {e : Tapes s a} (he : Blank e) (x : Fin (t + s)) :
    (v.append e).head x = if h : x.val < t then v.head ⟨x.val, h⟩ else 0 := by
  induction x using Fin.addCases with
  | left i => simp [Tapes.append]
  | right i => simp [Tapes.append, (he i).1]

theorem append_tape (v : Tapes t a) {e : Tapes s a} (he : Blank e) (x : Fin (t + s)) :
    (v.append e).tape x = if h : x.val < t then v.tape ⟨x.val, h⟩ else fun _ => blank := by
  induction x using Fin.addCases with
  | left i => simp [Tapes.append]
  | right i => simp [Tapes.append, (he i).2]

theorem blank_empty (n : ℕ) : Blank (FixedHeaderBankCopy.empty n : Tapes n a) := fun _ => ⟨rfl, rfl⟩
theorem blank_zero : Blank (ArbitraryWidthZeroHeaderShared.empty : Tapes 1 a) := fun _ => ⟨rfl, rfl⟩

theorem input_head (c : Tapes t prime) (x : Fin (BinaryInterchangeRun.bankCount t + 1)) :
    (BinaryInterchangeRun.input c).head x = if h : x.val < t then c.head ⟨x.val, h⟩ else 0 := by
  simp only [BinaryInterchangeRun.input, BinaryInterchangeRun.bankInput, BinaryInterchangeRun.middle,
    BinaryAdjacentWidthMovementShared.input, BinaryAdjacentWidthHeadersShared.input,
    BinaryRadixEqualShared.input, BinaryAdjacentWidthPrefixShared.input]
  simp only [append_head _ (blank_empty _), append_head _ blank_zero]
  split_ifs <;> first | rfl | omega

theorem input_tape (c : Tapes t prime) (x : Fin (BinaryInterchangeRun.bankCount t + 1)) :
    (BinaryInterchangeRun.input c).tape x = if h : x.val < t then c.tape ⟨x.val, h⟩ else fun _ => blank := by
  simp only [BinaryInterchangeRun.input, BinaryInterchangeRun.bankInput, BinaryInterchangeRun.middle,
    BinaryAdjacentWidthMovementShared.input, BinaryAdjacentWidthHeadersShared.input,
    BinaryRadixEqualShared.input, BinaryAdjacentWidthPrefixShared.input]
  simp only [append_tape _ (blank_empty _), append_tape _ blank_zero]
  split_ifs <;> first | rfl | omega

/-- Word tapes whose tapes past the first `t` are empty are the interchange's input bank. -/
theorem enc_input (σ : Fin (BinaryInterchangeRun.bankCount t + 1) → WTape)
    (hpriv : ∀ x : Fin (BinaryInterchangeRun.bankCount t + 1), t ≤ x.val → σ x = emp) :
    enc σ = BinaryInterchangeRun.input (enc (fun i : Fin t => σ (BinaryInterchangeRun.slot i))) := by
  refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
  · rw [input_head]
    split_ifs with h
    · rfl
    · simp [enc, hpriv x (by omega), emp, WTape.pos, clen]
  · rw [input_tape]
    split_ifs with h
    · rfl
    · simp only [enc, hpriv x (by omega)]; funext j
      simp [emp, WTape.tape_eq, WTape.words, syms]

/-! ### Header and payload formats -/

theorem wordTape_val {q : ℕ} (bs : List Bool) (j : ℤ) :
    (wordTape (bs.map (bitSymbol (a := 0))) j).val = (wordTape (bs.map (bitSymbol (a := q))) j).val := by
  unfold wordTape
  split_ifs
  · rw [List.getElem?_map, List.getElem?_map]
    cases bs[j.toNat]? with
    | none => rfl
    | some b => cases b <;> rfl
  · rfl

theorem putBits_eq (f : ℤ → Fin 4) (p : ℤ) (bs : List Bool) :
    putBits f p bs = putWord f p (bs.map bitSymbol) := by
  induction bs generalizing p with
  | nil => rfl
  | cons b bs ih => simp [putBits, putWord, ih]

theorem encodedBinary_eq (bs : List Bool) : RadixZeroFill.encodedBinary (q := prime) bs = ctr bs := by
  funext j
  apply Fin.ext
  simp only [RadixZeroFill.encodedBinary, RadixToBinary.binaryEncoding, CountedCopyReuse.binary, putBits_eq,
    putWord_ite, ctr, ctr.wordAt', List.length_map]
  by_cases h0 : j = 0
  · subst h0; simp [CountedCopyReuse.empty, separator]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
    split_ifs with hin
    · exact wordTape_val bs (j - 1)
    · simp only [CountedCopyReuse.empty, ite_eq_right_of_eq_false _ _ (eq_false h0), wordTape]
      split_ifs
      · rw [List.getElem?_eq_none (by simp; omega)]; rfl
      · rfl

theorem word_eq {n : ℕ} (x : Fin n → Bool) :
    BinaryRadixRangePrepareAlphabet.word (a := a) (fun i => bitSymbol (x i)) = Spec.SignedRingProduct.wordAt (List.ofFn x) := by
  funext j
  simp only [BinaryRadixRangePrepareAlphabet.word, putWord_ite, Spec.SignedRingProduct.wordAt, List.length_ofFn,
    List.map_ofFn]
  split_ifs with h
  · rw [sub_zero]; rfl
  · simp only [wordTape]
    split_ifs
    · rw [List.getElem?_eq_none (by simp; omega)]; rfl
    · rfl

/-! ### One-tape machines on a bank -/

/-- A one-tape machine on tape `i`. -/
noncomputable def on1 (i : Fin t) {q : ℕ} (M : Program 1 q a) : Program t q a :=
  Placement.placed M (InjectivePlacement.placement (fun _ : Fin 1 => i) (slot_const_inj i) (one_size i))

theorem on1_hoare (i : Fin t) {q : ℕ} {M : Program 1 q a} {f g : ℤ → Fin (a + 4)} {h h' : ℤ} {b : ℕ}
    (hM : HoareTime M (· = one h f) (· = one h' g) b) (v : Tapes t a)
    (hh : v.head i = h) (hf : v.tape i = f) :
    HoareTime (on1 i M) (· = v) (· = ⟨Function.update v.head i h', Function.update v.tape i g⟩) b := by
  refine InjectivePlacement.hoare_exact hM _ (slot_const_inj i) (one_size i) v _ ?_ ?_
  · rw [InjectivePlacement.active_bank]
    simp only [one, hh, hf]
  · refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
    · by_cases hx : x = i
      · subst hx
        have := InjectivePlacement.replace_head_slot (fun _ : Fin 1 => x) (slot_const_inj x) (one_size x) v
          (one h' g) 0
        simpa [one] using this
      · rw [InjectivePlacement.replace_head_other _ _ _ _ _ _ (fun _ e => hx e.symm)]
        exact (Function.update_of_ne hx _ _).symm
    · by_cases hx : x = i
      · subst hx
        have := InjectivePlacement.replace_tape_slot (fun _ : Fin 1 => x) (slot_const_inj x) (one_size x) v
          (one h' g) 0
        simpa [one] using this
      · rw [InjectivePlacement.replace_tape_other _ _ _ _ _ _ (fun _ e => hx e.symm)]
        exact (Function.update_of_ne hx _ _).symm

/-! ### Converting the caller's six tapes -/

/-- The caller's six tapes with headers below `k` in counter form; the payload is a sealed word
or raw bits. -/
noncomputable def st (k : ℕ) (ws : Fin 6 → List Bool) (sealed : Bool) : Tapes 6 prime :=
  ⟨fun i => if i.val < k then 1 else 0,
   fun i => if i.val < k then ctr (ws i) else if i.val < 5 ∨ sealed then wtp (ws i)
     else Spec.SignedRingProduct.wordAt (ws i)⟩

theorem toCtr_step (ws : Fin 6 → List Bool) (k : ℕ) (hk : k < 5) :
    HoareTime (on1 (⟨k, by omega⟩ : Fin 6) (toCtrProg (a := prime))) (· = st k ws true) (· = st (k + 1) ws true)
      (2 * (ws ⟨k, by omega⟩).length + 4) := by
  refine (on1_hoare _ (toCtrProg_hoare (ws ⟨k, by omega⟩)) (st k ws true) ?_ ?_).consequence
    (fun _ h => h) (fun v hv => ?_) le_rfl
  · simp [st]
  · simp [st]
  · rw [hv]; refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
    · by_cases hx : x = ⟨k, by omega⟩
      · subst hx; simp [st]
      · dsimp only; rw [Function.update_of_ne hx]; simp only [st]
        have : x.val ≠ k := fun e => hx (Fin.ext e)
        split_ifs <;> first | rfl | omega
    · by_cases hx : x = ⟨k, by omega⟩
      · subst hx; simp [st]
      · dsimp only; rw [Function.update_of_ne hx]; simp only [st]
        have : x.val ≠ k := fun e => hx (Fin.ext e)
        split_ifs <;> first | rfl | omega

theorem fromCtr_step (ws : Fin 6 → List Bool) (k : ℕ) (hk : k < 5) :
    HoareTime (on1 (⟨k, by omega⟩ : Fin 6) (fromCtrProg (a := prime))) (· = st (k + 1) ws true) (· = st k ws true)
      (2 * (ws ⟨k, by omega⟩).length + 2) := by
  refine (on1_hoare _ (fromCtrProg_hoare (ws ⟨k, by omega⟩)) (st (k + 1) ws true) ?_ ?_).consequence
    (fun _ h => h) (fun v hv => ?_) le_rfl
  · simp [st]
  · simp [st]
  · rw [hv]; refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
    · by_cases hx : x = ⟨k, by omega⟩
      · subst hx; simp [st]
      · dsimp only; rw [Function.update_of_ne hx]; simp only [st]
        have : x.val ≠ k := fun e => hx (Fin.ext e)
        split_ifs <;> first | rfl | omega
    · by_cases hx : x = ⟨k, by omega⟩
      · subst hx; simp [st]
      · dsimp only; rw [Function.update_of_ne hx]; simp only [st]
        have : x.val ≠ k := fun e => hx (Fin.ext e)
        split_ifs <;> first | rfl | omega

theorem unseal_step (ws : Fin 6 → List Bool) :
    HoareTime (on1 (5 : Fin 6) (unsealProg (a := prime))) (· = st 5 ws true) (· = st 5 ws false)
      (2 * (ws 5).length + 6) := by
  refine (on1_hoare _ (unsealProg_hoare (ws 5)) (st 5 ws true) ?_ ?_).consequence
    (fun _ h => h) (fun v hv => ?_) le_rfl
  · simp [st]
  · simp [st]; rfl
  · rw [hv]; refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
    · by_cases hx : x = 5
      · subst hx; simp [st]
      · dsimp only; rw [Function.update_of_ne hx]; rfl
    · by_cases hx : x = 5
      · subst hx; simp [st]
      · dsimp only; rw [Function.update_of_ne hx]; simp only [st]
        have : x.val ≠ 5 := fun e => hx (Fin.ext e)
        split_ifs <;> first | rfl | omega

theorem seal_step (ws : Fin 6 → List Bool) :
    HoareTime (on1 (5 : Fin 6) (sealProg (a := prime))) (· = st 5 ws false) (· = st 5 ws true)
      (2 * (ws 5).length + 6) := by
  refine (on1_hoare _ (sealProg_hoare (ws 5)) (st 5 ws false) ?_ ?_).consequence
    (fun _ h => h) (fun v hv => ?_) le_rfl
  · simp [st]
  · simp [st]
  · rw [hv]; refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
    · by_cases hx : x = 5
      · subst hx; simp [st]
      · dsimp only; rw [Function.update_of_ne hx]; rfl
    · by_cases hx : x = 5
      · subst hx; simp [st]; rfl
      · dsimp only; rw [Function.update_of_ne hx]; simp only [st]
        have : x.val ≠ 5 := fun e => hx (Fin.ext e)
        split_ifs <;> first | rfl | omega

/-- Headers to counter form, then the payload to raw bits. -/
noncomputable def convIn :=
  seq (on1 (⟨0, by omega⟩ : Fin 6) (toCtrProg (a := prime)))
  (seq (on1 (⟨1, by omega⟩ : Fin 6) (toCtrProg (a := prime)))
  (seq (on1 (⟨2, by omega⟩ : Fin 6) (toCtrProg (a := prime)))
  (seq (on1 (⟨3, by omega⟩ : Fin 6) (toCtrProg (a := prime)))
  (seq (on1 (⟨4, by omega⟩ : Fin 6) (toCtrProg (a := prime)))
    (on1 (5 : Fin 6) (unsealProg (a := prime)))))))

/-- The payload back to a word, then the headers back to words. -/
noncomputable def convOut :=
  seq (on1 (5 : Fin 6) (sealProg (a := prime)))
  (seq (on1 (⟨4, by omega⟩ : Fin 6) (fromCtrProg (a := prime)))
  (seq (on1 (⟨3, by omega⟩ : Fin 6) (fromCtrProg (a := prime)))
  (seq (on1 (⟨2, by omega⟩ : Fin 6) (fromCtrProg (a := prime)))
  (seq (on1 (⟨1, by omega⟩ : Fin 6) (fromCtrProg (a := prime)))
    (on1 (⟨0, by omega⟩ : Fin 6) (fromCtrProg (a := prime)))))))

/-- The cost of `convIn`. -/
def inCost (ws : Fin 6 → List Bool) : ℕ :=
  (2 * (ws 0).length + 4) + 1 + ((2 * (ws 1).length + 4) + 1 + ((2 * (ws 2).length + 4) + 1 +
    ((2 * (ws 3).length + 4) + 1 + ((2 * (ws 4).length + 4) + 1 + (2 * (ws 5).length + 6)))))

/-- The cost of `convOut`. -/
def outCost (ws : Fin 6 → List Bool) : ℕ :=
  (2 * (ws 5).length + 6) + 1 + ((2 * (ws 4).length + 2) + 1 + ((2 * (ws 3).length + 2) + 1 +
    ((2 * (ws 2).length + 2) + 1 + ((2 * (ws 1).length + 2) + 1 + (2 * (ws 0).length + 2)))))

theorem convIn_hoare (ws : Fin 6 → List Bool) :
    HoareTime convIn (· = st 0 ws true) (· = st 5 ws false) (inCost ws) :=
  (toCtr_step ws 0 (by omega)).seq ((toCtr_step ws 1 (by omega)).seq ((toCtr_step ws 2 (by omega)).seq
    ((toCtr_step ws 3 (by omega)).seq ((toCtr_step ws 4 (by omega)).seq (unseal_step ws)))))

theorem convOut_hoare (ws : Fin 6 → List Bool) :
    HoareTime convOut (· = st 5 ws false) (· = st 0 ws true) (outCost ws) :=
  (seal_step ws).seq ((fromCtr_step ws 4 (by omega)).seq ((fromCtr_step ws 3 (by omega)).seq
    ((fromCtr_step ws 2 (by omega)).seq ((fromCtr_step ws 1 (by omega)).seq (fromCtr_step ws 0 (by omega))))))

/-! ### Inside the interchange's bank -/

/-- A caller program run on the interchange's bank. -/
noncomputable def liftIn {q : ℕ} (M : Program 6 q prime) : Program (BinaryInterchangeRun.bankCount 6 + 1) q prime :=
  extend (extend (extend (extend (extend (extend (extend M 1) 17) BinaryRadixEqualShared.count) 1) 17) 22) 1

theorem liftIn_hoare {q : ℕ} {M : Program 6 q prime} {X X' : Tapes 6 prime} {b : ℕ}
    (h : HoareTime M (· = X) (· = X') b) :
    HoareTime (liftIn M) (· = BinaryInterchangeRun.input X) (· = BinaryInterchangeRun.input X') b := by
  unfold liftIn BinaryInterchangeRun.input BinaryInterchangeRun.bankInput BinaryInterchangeRun.middle
    BinaryAdjacentWidthMovementShared.input BinaryAdjacentWidthHeadersShared.input
    BinaryRadixEqualShared.input BinaryAdjacentWidthPrefixShared.input
  exact hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (hoare_extend_eq h _) _) _) _) _) _) _

def focus : Fin 5 → Fin 6 := Fin.castSucc
theorem focus_inj : Function.Injective focus := Fin.castSucc_injective 5

/-- The header words as the interchange reads them. -/
def hdr (ws : Fin 6 → List Bool) : Fin 5 → List Bool := fun i => ws (focus i)

/-- The interchange's run with the payload as raw bits. -/
theorem swap_step (ws : Fin 6 → List Bool) (P G B h d : ℕ) (hhd : h ≤ d + 1) (hdh : d ≤ h + 1)
    (hv : ∀ i, Counter.value (hdr ws i) = BinaryInterchangeRun.values P G B h d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hdr ws i)) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P (2 ^ h) G (2 ^ d) B) → Bool) (hx : ws 5 = List.ofFn x) :
    HoareTime (BinaryInterchangeRun.program focus 5 focus_inj)
      (· = BinaryInterchangeRun.input (st 5 ws false))
      (· = BinaryInterchangeRun.input (st 5 (Function.update ws 5
        (List.ofFn (BinaryAdjacentWidthInterchange.transpose x))) false))
      (BinaryInterchangeRun.cost P G B h d (hdr ws)) := by
  have hr := BinaryInterchangeRun.runs (st 5 ws false) focus 5 focus_inj P G B h d (hdr ws) hhd hdh hv hc
    hP hG hB (fun i => by
      have : (focus i).val < 5 := by rw [focus, Fin.val_castSucc]; exact i.isLt
      simp [st, this, encodedBinary_eq, hdr])
    (fun i => by simp [st, focus]) x (by simp [st, hx, word_eq]) (by simp [st])
  refine hr.consequence (fun _ h => h) (fun v hv => ?_) le_rfl
  rw [hv]; congr 1
  refine Placement.Tapes.ext' (fun y => ?_) (fun y => ?_)
  · by_cases hy : y = 5
    · subst hy; simp [SharedPlacementAlphabet.setTape, st]
    · simp [SharedPlacementAlphabet.setTape, st, hy]
  · by_cases hy : y = 5
    · subst hy; simp only [SharedPlacementAlphabet.setTape, st, Function.update_self]
      rw [← word_eq]; simp
      rfl
    · simp [SharedPlacementAlphabet.setTape, st, hy]

/-- Convert, interchange, convert back. -/
noncomputable def prog :=
  seq (liftIn convIn) (seq (BinaryInterchangeRun.program focus 5 focus_inj) (liftIn convOut))

/-! ### As a word-program primitive -/

/-- The payload with the two address fields interchanged, as a list. -/
def swapList (P H G D B : ℕ) (xs : List Bool) : List Bool :=
  List.ofFn fun z : Fin (BinaryAdjacentWidthInterchange.volume P D G H B) =>
    xs.getD (BinaryAdjacentWidthInterchange.transpose
      (id : Fin (BinaryAdjacentWidthInterchange.volume P H G D B) → _) z).val false

theorem swapList_ofFn {P H G D B : ℕ} (x : Fin (BinaryAdjacentWidthInterchange.volume P H G D B) → Bool) :
    swapList P H G D B (List.ofFn x) = List.ofFn (BinaryAdjacentWidthInterchange.transpose x) := by
  simp [swapList, BinaryAdjacentWidthInterchange.transpose]; rfl

/-- The words on the six caller tapes. -/
def words (σ : Fin (BinaryInterchangeRun.bankCount 6 + 1) → WTape) : Fin 6 → List Bool :=
  fun i => (σ (BinaryInterchangeRun.slot i)).right.headD []

/-- The five header values `P, G, B, h, d`. -/
def vals (σ : Fin (BinaryInterchangeRun.bankCount 6 + 1) → WTape) : Fin 5 → ℕ :=
  fun i => Counter.value (hdr (words σ) i)

/-- The payload after the interchange. -/
def swapped (σ : Fin (BinaryInterchangeRun.bankCount 6 + 1) → WTape) : List Bool :=
  swapList (vals σ 0) (2 ^ vals σ 3) (vals σ 1) (2 ^ vals σ 4) (vals σ 2) (words σ 5)

/-- The swap primitive's precondition: six one-word tapes, empty private tapes, canonical headers
`P, G, B, h, d` with positive sizes and adjacent widths, and a payload of the full volume. -/
def Pre (σ : Fin (BinaryInterchangeRun.bankCount 6 + 1) → WTape) : Prop :=
  (∀ x : Fin (BinaryInterchangeRun.bankCount 6 + 1), 6 ≤ x.val → σ x = emp) ∧
  (∀ i, σ (BinaryInterchangeRun.slot i) = ⟨[], [words σ i]⟩) ∧
  (∀ i, GrowingCounterData.Canonical (hdr (words σ) i)) ∧
  0 < vals σ 0 ∧ 0 < vals σ 1 ∧ 0 < vals σ 2 ∧ vals σ 3 ≤ vals σ 4 + 1 ∧ vals σ 4 ≤ vals σ 3 + 1 ∧
  (words σ 5).length = BinaryAdjacentWidthInterchange.volume (vals σ 0) (2 ^ vals σ 3) (vals σ 1)
    (2 ^ vals σ 4) (vals σ 2)

/-- The swap primitive's effect: the payload's fields interchanged. -/
def sem (σ : Fin (BinaryInterchangeRun.bankCount 6 + 1) → WTape) : Fin (BinaryInterchangeRun.bankCount 6 + 1) → WTape :=
  Function.update σ (BinaryInterchangeRun.slot 5) ⟨[], [swapped σ]⟩

/-- The swap primitive's cost. -/
noncomputable def cost (σ : Fin (BinaryInterchangeRun.bankCount 6 + 1) → WTape) : ℕ :=
  inCost (words σ) + 1 + (BinaryInterchangeRun.cost (vals σ 0) (vals σ 1) (vals σ 2) (vals σ 3) (vals σ 4)
    (hdr (words σ)) + 1 + outCost (Function.update (words σ) 5 (swapped σ)))

theorem enc_st (τ : Fin 6 → WTape) (ws : Fin 6 → List Bool) (h : ∀ i, τ i = ⟨[], [ws i]⟩) :
    enc τ = st 0 ws true := by
  refine Placement.Tapes.ext' (fun x => ?_) (fun x => ?_)
  · simp [enc, st, h, WTape.pos, clen]
  · simp only [enc, st, h]; simp [wtp]

theorem slot_val (i : Fin 6) : (BinaryInterchangeRun.slot i).val = i.val := rfl

theorem prim_spec (σ : Fin (BinaryInterchangeRun.bankCount 6 + 1) → WTape) (hσ : Pre σ) :
    HoareTime prog (· = enc σ) (· = enc (sem σ)) (cost σ) := by
  obtain ⟨hpriv, hone, hc, hP, hG, hB, hhd, hdh, hlen⟩ := hσ
  set ws := words σ
  set x : Fin (BinaryAdjacentWidthInterchange.volume (vals σ 0) (2 ^ vals σ 3) (vals σ 1)
    (2 ^ vals σ 4) (vals σ 2)) → Bool := fun i => (ws 5)[i.val]'(by rw [hlen]; exact i.isLt)
  have hx : ws 5 = List.ofFn x := List.ext_getElem (by simp [hlen]) (fun n _ _ => by simp [x])
  have hv : ∀ i, Counter.value (hdr ws i) =
      BinaryInterchangeRun.values (vals σ 0) (vals σ 1) (vals σ 2) (vals σ 3) (vals σ 4) i := by
    intro i; fin_cases i <;> rfl
  have hswap : swapped σ = List.ofFn (BinaryAdjacentWidthInterchange.transpose x) := by
    rw [swapped, ← swapList_ofFn, ← hx]
  have h1 := liftIn_hoare (convIn_hoare ws)
  have h2 := swap_step ws _ _ _ _ _ hhd hdh hv hc hP hG hB x hx
  have h3 := liftIn_hoare (convOut_hoare (Function.update ws 5 (List.ofFn (BinaryAdjacentWidthInterchange.transpose x))))
  have hin : enc σ = BinaryInterchangeRun.input (st 0 ws true) := by
    rw [enc_input σ hpriv, enc_st _ ws hone]
  have hout : enc (sem σ) = BinaryInterchangeRun.input
      (st 0 (Function.update ws 5 (List.ofFn (BinaryAdjacentWidthInterchange.transpose x))) true) := by
    rw [enc_input (sem σ) (fun y hy => by
      rw [sem, Function.update_of_ne (fun e => by subst e; rw [slot_val] at hy; simp at hy)]; exact hpriv y hy)]
    rw [enc_st _ (Function.update ws 5 (List.ofFn (BinaryAdjacentWidthInterchange.transpose x))) (fun i => by
      by_cases hi : i = 5
      · subst hi; simp [sem, hswap]
      · rw [sem, Function.update_of_ne (fun e => hi (BinaryInterchangeRun.slot_injective e)),
          Function.update_of_ne hi]; exact hone i)]
  rw [hin, hout]
  refine (h1.seq (h2.seq h3)).consequence (fun _ h => h) (fun _ h => h) (le_of_eq ?_)
  simp only [cost, hswap]
  rfl

/-- The address-field interchange as a word-program primitive over the alphabet `prime`. -/
noncomputable def prim : Prim prime :=
  Prim.ofProgram prog (by omega) Pre sem cost prim_spec

end
end IntegerMultBounds.Schoenhage.SwapPrim
