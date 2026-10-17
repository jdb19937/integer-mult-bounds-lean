module

public import IntegerMultBounds.MathlibTM2.Host.Stream
public import IntegerMultBounds.MathlibTM2.Layer.Format
public import IntegerMultBounds.MathlibTM2.Statement
public import IntegerMultBounds.MathlibTM2.Binary
public import IntegerMultBounds.ExactRecovery

/-!
# The input stage of the fast multiplier

Stages F1 and F3 of `docs/fast-pipeline.md`. Registers are the right stacks `R i` of the host
(`IntegerMultBounds.MathlibTM2.Host`); a register holding the list `l` has `l.head?` on top.

## Reading (F1)

The input stack holds `pairEnc (x, y)`: the bits of `encodingNatBool.encode x` (least
significant first) as `inl` symbols, then those of `y` as `inr` symbols. `readInput tx ty rx ry`
pops it, pushing the bit symbol of each `inl` bit onto `tx` and of each `inr` bit onto `ty`
(most significant bit on top), and then moves `tx` onto `rx` and `ty` onto `ry`, which
reverses them: `rx` receives `(encodingNatBool.encode x).map bitSymbol`, least significant bit on
top, and likewise `ry` for `y` (`readInput_exec`, `4 n + 6` steps for `n = |pairEnc (x, y)|`).

## Digits (F3)

`digitRecords rx bn pn wn sn tpl tmp stmp acc dst` reads unary registers `bn`, `pn`, `wn`, `sn`
of lengths `b`, `p`, `w`, `S` (any symbols; all restored) and the LSB-first bits of `x` on `rx`,
and pushes onto `dst` the coefficient stream `digitStream A b p w S xs`: for `i < S`, the record
`coeffSyms A w (red w (digit_i · 2^(p - b - 2)))` with
`digit_i = (digitsOf b xs).getD i 0 = x / 2^(b i) % 2^b` (`getD_digitsOf`), where `xs` is any
MSB-first word of value `x` (`binaryValue xs = x`, so leading zeros of `xs` only add trailing
zero digits; `digitStream_congr`). The register `rx` is consumed (it ends empty when
`(digitsOf b xs).length ≤ S`). Requirements: `1 ≤ b`, `b + 2 ≤ p ≤ w`; the scratch registers
`tpl`, `tmp`, `stmp`, `acc` start and end empty.

The program first builds on `tpl` a template of `w` markers, `p - b - 2` zero markers (`blank`),
`b` digit markers (`separator`) and `w - p + 2` zero markers (`buildTpl`, by counted copies and
drops of the unary registers). Each record (one symbol of `sn`) walks the template
(`recStep`): a zero marker emits the zero pair symbol, a digit marker pops the next bit of `rx`
(an empty `rx` reads as `false`) and emits its pair symbol with imaginary bit `false`. The
records are pushed onto `acc` in reverse and a final move onto `dst` puts them in stream order.
`digitRecords_exec`: exactly `digitCost b p w S = S (6 w + 9) + 6 w + 8 p + 8 b + 30` steps, at
most `32 (S + 1) w` (`digitCost_le`).

## Grid values

`numerator_div_eq_scaledDigits`: the stored numerator `digit_i · 2^(p - b - 2)`, divided by
`2^p`, is `ExactRecovery.scaledDigits S b digits i`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer Computability


/-! ### Bits and digits -/

/-- Bit `j` of the LSB-first encoding is bit `j` of the number (`false` past the end). -/
lemma getD_encodeNat (x j : ℕ) : (encodeNat x).getD j false = x.testBit j := by
  induction x using Nat.binaryRec generalizing j with
  | zero => simp [encodeNat, encodeNum]
  | bit b m ih =>
      by_cases h : b = false ∧ m = 0
      · obtain ⟨rfl, rfl⟩ := h; simp [encodeNat, encodeNum]
      · have : encodeNat (Nat.bit b m) = b :: encodeNat m := by
          rw [encodeNat_bit]; cases b <;> simp_all
        rw [this]
        cases j with
        | zero => simp
        | succ j => rw [List.getD_cons_succ, ih, Nat.testBit_bit_succ]

/-- A number below `2^k` has an encoding of at most `k` bits. -/
lemma length_encodeNat_le {x k : ℕ} (h : x < 2 ^ k) : (encodeNat x).length ≤ k := by
  induction x using Nat.binaryRec generalizing k with
  | zero => simp [encodeNat, encodeNum]
  | bit b m ih =>
      by_cases hz : b = false ∧ m = 0
      · obtain ⟨rfl, rfl⟩ := hz; simp [encodeNat, encodeNum]
      · have : encodeNat (Nat.bit b m) = b :: encodeNat m := by
          rw [encodeNat_bit]; cases b <;> simp_all
        rw [this]
        cases k with
        | zero =>
            exfalso
            have : Nat.bit b m = 0 := by omega
            rw [Nat.bit_eq_zero_iff] at this
            exact hz ⟨this.2, this.1⟩
        | succ k =>
            have hm : m < 2 ^ k := by
              rw [Nat.bit_val, pow_succ] at h; cases b <;> simp at h <;> omega
            simpa using ih hm

/-- Digits below `M` with value `x` in base `M` are the base-`M` digits of `x`. -/
lemma getD_of_evalBase {M : ℕ} (hM : 0 < M) :
    ∀ cs : List ℕ, (∀ c ∈ cs, c < M) → ∀ i, cs.getD i 0 = evalBase M cs / M ^ i % M
  | [], _, i => by simp [evalBase]
  | c :: cs, h, i => by
      have hc : c < M := h c (by simp)
      have ih := getD_of_evalBase hM cs (fun d hd => h d (by simp [hd]))
      cases i with
      | zero => simp [evalBase, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
      | succ i =>
          rw [List.getD_cons_succ, ih i, pow_succ', ← Nat.div_div_eq_div_mul]
          simp only [evalBase]
          rw [show c + M * evalBase M cs = c + evalBase M cs * M by ring,
            Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hc, zero_add]

/-- The `i`-th base-`2^b` digit of an MSB-first word, least significant first: leading zeros of
the word only add zero digits. -/
theorem getD_digitsOf {b : ℕ} (hb : 0 < b) (xs : List Bool) (i : ℕ) :
    (digitsOf b xs).getD i 0 = binaryValue xs / 2 ^ (b * i) % 2 ^ b := by
  rw [getD_of_evalBase (by positivity) _ (digitsOf_lt hb xs), evalBase_digitsOf hb, pow_mul]

/-- With at most `S` digits, the value is below `2^(b S)`. -/
theorem binaryValue_lt_of_digitsOf {b S : ℕ} (hb : 0 < b) {xs : List Bool}
    (hS : (digitsOf b xs).length ≤ S) : binaryValue xs < 2 ^ (b * S) := by
  rw [← evalBase_digitsOf hb]
  calc evalBase (2 ^ b) (digitsOf b xs) < (2 ^ b) ^ (digitsOf b xs).length :=
        evalBase_lt (digitsOf_lt hb xs)
    _ ≤ (2 ^ b) ^ S := Nat.pow_le_pow_right (by positivity) hS
    _ = 2 ^ (b * S) := by rw [pow_mul]

/-- Every padded MSB-first word of `x`: the encoding reversed, with leading zeros. -/
theorem binaryValue_pad (x k : ℕ) :
    binaryValue (List.replicate k false ++ (encodingNatBool.encode x).reverse) = x := by
  rw [binaryValue_replicate_append]; exact binaryValue_reverse_encodeNat x

/-! ### Coefficient records -/

/-- One digit record: `e` zero pairs, then `b` pairs whose real bits are `l.getD j false`, then
`f` zero pairs; all imaginary bits are `false`. -/
def digitRec (A e b f : ℕ) (l : List Bool) : List (Fin (A + 4)) :=
  List.replicate e (pairSym A false false) ++
    (List.ofFn fun j : Fin b => pairSym A (l.getD j false) false) ++
    List.replicate f (pairSym A false false)

lemma length_digitRec (A e b f : ℕ) (l : List Bool) :
    (digitRec A e b f l).length = e + b + f := by
  simp [digitRec]; omega

/-- The stored numerator `d · 2^e` of a digit `d < 2^b` whose bits are `l`. -/
theorem coeffSyms_digit {A w e b : ℕ} (hw : e + b ≤ w) {d : ℕ} (hd : d < 2 ^ b)
    {l : List Bool} (hl : ∀ j < b, l.getD j false = d.testBit j) :
    coeffSyms A w (red w (⟨(d : ℤ) * 2 ^ e, 0⟩ : GaussianInt)) =
      digitRec A e b (w - e - b) l := by
  have hval : (((d : ℤ) * 2 ^ e : ℤ) : ZMod (2 ^ w)).val = d * 2 ^ e := by
    have : (((d : ℤ) * 2 ^ e : ℤ) : ZMod (2 ^ w)) = ((d * 2 ^ e : ℕ) : ZMod (2 ^ w)) := by
      push_cast; rfl
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt]
    calc d * 2 ^ e < 2 ^ b * 2 ^ e := Nat.mul_lt_mul_of_pos_right hd (by positivity)
      _ = 2 ^ (e + b) := by rw [← pow_add, add_comm]
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  apply List.ext_getElem
  · simp [digitRec]; omega
  intro t h₁ h₂
  simp only [coeffSyms, red, List.getElem_ofFn, hval, Int.cast_zero, ZMod.val_zero,
    Nat.zero_testBit, Nat.testBit_mul_two_pow]
  simp only [digitRec, List.getElem_append, List.getElem_replicate, List.getElem_ofFn,
    List.length_append, List.length_replicate, List.length_ofFn]
  split_ifs with h₃ h₄
  · simp [show ¬ e ≤ t by omega]
  · rw [hl (t - e) (by omega)]; simp [show e ≤ t by omega]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-! ### Reading the input -/

/-- Record in `flag` whether the input stack is nonempty. -/
def peekInput : Act T Q A U := .peek .inp (fun v o => { v with flag := o.isSome }) .done

/-- The bit of an input symbol. -/
def inBit (e : Bool ⊕ Bool) : Bool := Sum.elim id id e

/-- One input symbol: pop it and push its bit symbol onto `tx` (an `inl` symbol) or `ty` (an
`inr` symbol); record in `flag` whether the input is nonempty. -/
def inputStep (tx ty : Fin T) : Act T Q A U :=
  .pop .inp (fun v o => { v with
      sym := o.map fun e => bitSymbol (inBit e)
      flag := o.any Sum.isLeft })
    (.branch (·.flag)
      (.push (.rt tx) (fun v => v.sym.getD blank) peekInput)
      (.push (.rt ty) (fun v => v.sym.getD blank) peekInput))

/-- Bit symbols of the `inl` bits of an input word. -/
def leftSyms (l : List (Bool ⊕ Bool)) : List (Fin (A + 4)) :=
  (l.filterMap Sum.getLeft?).map bitSymbol

/-- Bit symbols of the `inr` bits of an input word. -/
def rightSyms (l : List (Bool ⊕ Bool)) : List (Fin (A + 4)) :=
  (l.filterMap Sum.getRight?).map bitSymbol

/-- The input loop: `tx` and `ty` receive the reversed bit symbols of the `inl` and `inr`
bits. -/
theorem inputStep_loop (tx ty : Fin T) (hxy : tx ≠ ty) :
    ∀ (l : List (Bool ⊕ Bool)) (v : HS T Q A U) (S : Stacks T A), S.inp = l →
      v.flag = l.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (inputStep tx ty))) (mk v S) (2 * l.length + 1)
          (mk v' { S with
            inp := []
            R := Function.update (Function.update S.R tx ((leftSyms l).reverse ++ S.R tx)) ty
              ((rightSyms l).reverse ++ S.R ty) }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          inp := []
          R := Function.update (Function.update S.R
            tx ((leftSyms ([] : List (Bool ⊕ Bool))).reverse ++ S.R tx))
            ty ((rightSyms ([] : List (Bool ⊕ Bool))).reverse ++ S.R ty) } : Stacks T A) = S := by
        cases S; simp_all [leftSyms, rightSyms]
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      cases e with
      | inl b =>
          obtain ⟨v', hu, he⟩ := ih
            { v with sym := some (bitSymbol b), flag := rest.head?.isSome }
            { S with inp := rest, R := Function.update S.R tx (bitSymbol b :: S.R tx) } rfl rfl
          refine ⟨v', hu, ?_⟩
          have hrun : (inputStep tx ty : Act T Q A U).run (mk v S) =
              mk { v with sym := some (bitSymbol b), flag := rest.head?.isSome }
                { S with inp := rest, R := Function.update S.R tx (bitSymbol b :: S.R tx) } := by
            simp [inputStep, peekInput, Action.run, hS, update_inp, update_rt, inBit]
          refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
            (hrun ▸ Exec.act (body := body) (inputStep tx ty) (mk v S)) he) (by simp; ring) ?_
          congr 2
          simp [leftSyms, rightSyms, List.filterMap_cons, Function.update_of_ne hxy.symm,
            Function.update_idem]
      | inr b =>
          obtain ⟨v', hu, he⟩ := ih
            { v with sym := some (bitSymbol b), flag := rest.head?.isSome }
            { S with inp := rest, R := Function.update S.R ty (bitSymbol b :: S.R ty) } rfl rfl
          refine ⟨v', hu, ?_⟩
          have hrun : (inputStep tx ty : Act T Q A U).run (mk v S) =
              mk { v with sym := some (bitSymbol b), flag := rest.head?.isSome }
                { S with inp := rest, R := Function.update S.R ty (bitSymbol b :: S.R ty) } := by
            simp [inputStep, peekInput, Action.run, hS, update_inp, update_rt, inBit]
          refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
            (hrun ▸ Exec.act (body := body) (inputStep tx ty) (mk v S)) he) (by simp; ring) ?_
          congr 2
          funext k
          by_cases h1 : k = ty
          · subst h1
            simp [leftSyms, rightSyms, List.filterMap_cons]
          · by_cases h2 : k = tx
            · subst h2
              simp [leftSyms, rightSyms, List.filterMap_cons, h1]
            · simp [leftSyms, rightSyms, List.filterMap_cons, Function.update_of_ne h1,
                Function.update_of_ne h2]

lemma leftSyms_pairEnc (x y : ℕ) :
    leftSyms (A := A) (pairEnc (x, y)) = (encodingNatBool.encode x).map bitSymbol := by
  simp [leftSyms, pairEnc, encodingProd, List.filterMap_append, List.filterMap_map,
    Function.comp_def]

lemma rightSyms_pairEnc (x y : ℕ) :
    rightSyms (A := A) (pairEnc (x, y)) = (encodingNatBool.encode y).map bitSymbol := by
  simp [rightSyms, pairEnc, encodingProd, List.filterMap_append, List.filterMap_map,
    Function.comp_def]

lemma length_pairEnc_encode (x y : ℕ) : (pairEnc (x, y)).length =
    (encodingNatBool.encode x).length + (encodingNatBool.encode y).length := by
  simp [pairEnc, encodingProd]

/-- Read the input: split `pairEnc (x, y)` onto the empty temporaries `tx`, `ty` (most
significant bit on top), then move them onto `rx`, `ry` (least significant bit on top). -/
def readInput (tx ty rx ry : Fin T) : Pr P T Q A U :=
  .seq (.act peekInput) (.seq (.loop (·.flag) (.act (inputStep tx ty)))
    (.seq (moveR tx rx id) (moveR ty ry id)))

/-- `readInput` empties the input and pushes the LSB-first bit symbols of `x` onto `rx` and of
`y` onto `ry`, in `4 n + 6` steps for the input length `n`; the temporaries end empty and every
other stack is unchanged. -/
theorem readInput_exec (tx ty rx ry : Fin T) (hreg : [tx, ty, rx, ry].Nodup) (x y : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (hin : S.inp = pairEnc (x, y)) (htx : S.R tx = [])
    (hty : S.R ty = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (readInput tx ty rx ry) (mk v S) (4 * (pairEnc (x, y)).length + 6)
        (mk v' { S with
          inp := []
          R := Function.update (Function.update S.R
            rx ((encodingNatBool.encode x).map bitSymbol ++ S.R rx))
            ry ((encodingNatBool.encode y).map bitSymbol ++ S.R ry) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2⟩, c1⟩ := hreg
  have he₀ := Exec.act (body := body) (peekInput (T := T) (Q := Q) (A := A) (U := U)) (mk v S)
  obtain ⟨v₁, hu₁, he₁⟩ := inputStep_loop body tx ty a1 (pairEnc (x, y))
    { v with flag := (S.inp).head?.isSome } S hin (by rw [hin])
  rw [leftSyms_pairEnc, rightSyms_pairEnc, htx, hty] at he₁
  set S₁ : Stacks T A := { S with
    inp := []
    R := Function.update (Function.update S.R tx
      (((encodingNatBool.encode x).map bitSymbol).reverse ++ [])) ty
      (((encodingNatBool.encode y).map bitSymbol).reverse ++ []) } with hS₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tx rx a2 id v₁ S₁
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body ty ry b2 id v₂
    { S₁ with R := movedR S₁.R tx rx id (S₁.R tx) }
  have hR : movedR (movedR S₁.R tx rx id (S₁.R tx)) ty ry id
      (movedR S₁.R tx rx id (S₁.R tx) ty) =
      Function.update (Function.update S.R
        rx ((encodingNatBool.encode x).map bitSymbol ++ S.R rx))
        ry ((encodingNatBool.encode y).map bitSymbol ++ S.R ry) := by
    funext k
    simp only [hS₁, movedR, Function.update_apply]
    split_ifs <;> simp_all
  refine ⟨v₃, by rw [hu₃, hu₂, hu₁],
    Exec.cast (Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ he₃))) ?_ ?_⟩
  · have h1 : (movedR S₁.R tx rx id (S₁.R tx) ty).length =
        (encodingNatBool.encode y).length := by
      simp [hS₁, movedR, Function.update_apply, b1, Ne.symm a1]
    have h2 : (S₁.R tx).length = (encodingNatBool.encode x).length := by
      simp [hS₁, a1]
    simp only [h1, h2, length_pairEnc_encode]
    ring
  · simp only
    rw [← hR]

/-! ### Counted copies, drops and emptying -/

/-- One step of `copyR`: pop `src`, push the symbol onto `tmp` and its image under `f` onto
`dst`; record in `flag` whether `src` is nonempty. -/
def copyStep (src dst tmp : Fin T) (f : Fin (A + 4) → Fin (A + 4)) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.push (.rt tmp) (fun v => v.sym.getD blank)
      (.push (.rt dst) (fun v => f (v.sym.getD blank)) (peekR src)))

/-- The copy loop: `src` moves onto `tmp` and its image under `f` onto `dst`, both
reversed. -/
theorem copyStep_loop (src dst tmp : Fin T) (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (f : Fin (A + 4) → Fin (A + 4)) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A), S.R src = l →
      v.flag = l.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (copyStep src dst tmp f))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := Function.update (Function.update (Function.update S.R src [])
            tmp (l.reverse ++ S.R tmp)) dst ((l.map f).reverse ++ S.R dst) }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          R := Function.update (Function.update (Function.update S.R src [])
            tmp (([] : List (Fin (A + 4))).reverse ++ S.R tmp)) dst
            ((([] : List (Fin (A + 4))).map f).reverse ++ S.R dst) } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          simp only [Function.update_apply]
          split_ifs <;> simp_all
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hu, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
        { S with R := Function.update (Function.update (Function.update S.R src rest)
          tmp (e :: S.R tmp)) dst (f e :: S.R dst) }
        (by simp [Function.update_of_ne h1, Function.update_of_ne h2]) rfl
      refine ⟨v', hu, ?_⟩
      have hrun : (copyStep src dst tmp f : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, flag := rest.head?.isSome }
            { S with R := Function.update (Function.update (Function.update S.R src rest)
              tmp (e :: S.R tmp)) dst (f e :: S.R dst) } := by
        simp [copyStep, peekR, Action.run, hS, update_rt, Function.update_of_ne h1,
          Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1.symm,
          Function.update_of_ne h2.symm]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (copyStep src dst tmp f) (mk v S)) he) (by simp; ring) ?_
      congr 2
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all

/-- Copy register `src` onto `dst`, mapping each symbol by `f`; `src` is restored through the
empty temporary `tmp`. -/
def copyR (src dst tmp : Fin T) (f : Fin (A + 4) → Fin (A + 4)) : Pr P T Q A U :=
  .seq (whileR src (copyStep src dst tmp f)) (moveR tmp src id)

/-- `copyR` pushes the reversed image of `src` onto `dst` in `4 |src| + 4` steps. -/
theorem copyR_exec (src dst tmp : Fin T) (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp)
    (f : Fin (A + 4) → Fin (A + 4)) (v : HS T Q A U) (S : Stacks T A) (ht : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyR src dst tmp f) (mk v S) (4 * (S.R src).length + 4)
        (mk v' { S with R := Function.update S.R dst (((S.R src).map f).reverse ++ S.R dst) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := copyStep_loop body src dst tmp h1 h2 h3 f (S.R src)
    { v with flag := (S.R src).head?.isSome } S rfl rfl
  have he₀ := Exec.act (body := body) (peekR src) (mk v S)
  rw [peekR_run] at he₀
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tmp src h2.symm id v₁ { S with
    R := Function.update
      (Function.update (Function.update S.R src []) tmp ((S.R src).reverse ++ S.R tmp)) dst
      (((S.R src).map f).reverse ++ S.R dst) }
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq (Exec.seq he₀ he₁) he₂) ?_ ?_⟩
  · simp [Function.update_of_ne h3.symm, ht]; ring
  · congr 2
    funext k
    simp only [movedR, Function.update_apply]
    split_ifs <;> simp_all

/-- One step of `dropR`: pop `cnt` onto `tmp` and drop the top of `dst`; record in `flag`
whether `cnt` is nonempty. -/
def dropStep (cnt dst tmp : Fin T) : Act T Q A U :=
  .pop (.rt cnt) (fun v o => { v with sym := o })
    (.push (.rt tmp) (fun v => v.sym.getD blank)
      (.pop (.rt dst) (fun v _ => v) (peekR cnt)))

/-- The drop loop: `cnt` moves onto `tmp` and `dst` loses `|cnt|` symbols. -/
theorem dropStep_loop (cnt dst tmp : Fin T) (h1 : cnt ≠ dst) (h2 : cnt ≠ tmp)
    (h3 : dst ≠ tmp) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A), S.R cnt = l →
      v.flag = l.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (dropStep cnt dst tmp))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := Function.update (Function.update (Function.update S.R cnt [])
            tmp (l.reverse ++ S.R tmp)) dst ((S.R dst).drop l.length) }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          R := Function.update (Function.update (Function.update S.R cnt [])
            tmp (([] : List (Fin (A + 4))).reverse ++ S.R tmp)) dst
            ((S.R dst).drop ([] : List (Fin (A + 4))).length) } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS
          congr 1
          funext k
          simp only [Function.update_apply]
          split_ifs <;> simp_all
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hu, he⟩ := ih { v with sym := some e, flag := rest.head?.isSome }
        { S with R := Function.update (Function.update (Function.update S.R cnt rest)
          tmp (e :: S.R tmp)) dst (S.R dst).tail }
        (by simp [Function.update_of_ne h1, Function.update_of_ne h2]) rfl
      refine ⟨v', hu, ?_⟩
      have hrun : (dropStep cnt dst tmp : Act T Q A U).run (mk v S) =
          mk { v with sym := some e, flag := rest.head?.isSome }
            { S with R := Function.update (Function.update (Function.update S.R cnt rest)
              tmp (e :: S.R tmp)) dst (S.R dst).tail } := by
        simp [dropStep, peekR, Action.run, hS, update_rt, Function.update_of_ne h1,
          Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1.symm,
          Function.update_of_ne h2.symm]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (dropStep cnt dst tmp) (mk v S)) he) (by simp; ring) ?_
      congr 2
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all [List.drop_tail, Nat.add_comm]

/-- Drop `|cnt|` symbols from the top of `dst`; `cnt` is restored through the empty temporary
`tmp`. -/
def dropR (cnt dst tmp : Fin T) : Pr P T Q A U :=
  .seq (whileR cnt (dropStep cnt dst tmp)) (moveR tmp cnt id)

/-- `dropR` drops `|cnt|` symbols from `dst` in `4 |cnt| + 4` steps. -/
theorem dropR_exec (cnt dst tmp : Fin T) (h1 : cnt ≠ dst) (h2 : cnt ≠ tmp) (h3 : dst ≠ tmp)
    (v : HS T Q A U) (S : Stacks T A) (ht : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (dropR cnt dst tmp) (mk v S) (4 * (S.R cnt).length + 4)
        (mk v' { S with R := Function.update S.R dst ((S.R dst).drop (S.R cnt).length) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := dropStep_loop body cnt dst tmp h1 h2 h3 (S.R cnt)
    { v with flag := (S.R cnt).head?.isSome } S rfl rfl
  have he₀ := Exec.act (body := body) (peekR cnt) (mk v S)
  rw [peekR_run] at he₀
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tmp cnt h2.symm id v₁ { S with
    R := Function.update
      (Function.update (Function.update S.R cnt []) tmp ((S.R cnt).reverse ++ S.R tmp)) dst
      ((S.R dst).drop (S.R cnt).length) }
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq (Exec.seq he₀ he₁) he₂) ?_ ?_⟩
  · simp [Function.update_of_ne h3.symm, ht]; ring
  · congr 2
    funext k
    simp only [movedR, Function.update_apply]
    split_ifs <;> simp_all

/-- Pop register `i` and record in `flag` whether it is nonempty. -/
def emptyStep (i : Fin T) : Act T Q A U := .pop (.rt i) (fun v _ => v) (peekR i)

theorem emptyStep_loop (i : Fin T) :
    ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A), S.R i = l →
      v.flag = l.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (emptyStep i))) (mk v S) (2 * l.length + 1)
          (mk v' { S with R := Function.update S.R i [] }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with R := Function.update S.R i [] } : Stacks T A) = S := by
        cases S; simp_all
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons e rest ih =>
      intro v S hS hf
      obtain ⟨v', hu, he⟩ := ih { v with flag := rest.head?.isSome }
        { S with R := Function.update S.R i rest } (by simp) rfl
      refine ⟨v', hu, ?_⟩
      have hrun : (emptyStep i : Act T Q A U).run (mk v S) =
          mk { v with flag := rest.head?.isSome } { S with R := Function.update S.R i rest } := by
        simp [emptyStep, peekR, Action.run, hS, update_rt]
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (emptyStep i) (mk v S)) he) (by simp; ring) ?_
      simp

/-- Empty register `i`. -/
def emptyR (i : Fin T) : Pr P T Q A U := whileR i (emptyStep i)

/-- `emptyR` empties register `i` in `2 |i| + 2` steps. -/
theorem emptyR_exec (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (emptyR i) (mk v S) (2 * (S.R i).length + 2)
        (mk v' { S with R := Function.update S.R i [] }) := by
  obtain ⟨v', hu, he⟩ := emptyStep_loop body i (S.R i) { v with flag := (S.R i).head?.isSome } S
    rfl rfl
  exact ⟨v', hu, Exec.cast
    (Exec.seq (peekR_run i v S ▸ Exec.act (body := body) (peekR i) (mk v S)) he) (by ring) rfl⟩

/-! ### The template -/

/-- The digit template: `e` zero markers (`blank`), `b` digit markers (`separator`), `f` zero
markers, top first. -/
def tplOf (A e b f : ℕ) : List (Fin (A + 4)) :=
  List.replicate e blank ++ List.replicate b separator ++ List.replicate f blank

/-- Push two zero markers onto `tpl`. -/
def push2 (tpl : Fin T) : Act T Q A U :=
  .push (.rt tpl) (fun _ => blank) (.push (.rt tpl) (fun _ => blank) .done)

/-- Pop two symbols from `tpl`. -/
def pop2 (tpl : Fin T) : Act T Q A U :=
  .pop (.rt tpl) (fun v _ => v) (.pop (.rt tpl) (fun v _ => v) .done)

/-- Build the template `tplOf A (p - b - 2) b (w - p + 2)` on the empty register `tpl` from the
unary registers `bn`, `pn`, `wn` (lengths `b`, `p`, `w`), with the empty temporary `tmp`. -/
def buildTpl (bn pn wn tpl tmp : Fin T) : Pr P T Q A U :=
  .seq (copyR wn tpl tmp (fun _ => blank))
    (.seq (dropR pn tpl tmp)
      (.seq (.act (push2 tpl))
        (.seq (copyR bn tpl tmp (fun _ => separator))
          (.seq (copyR pn tpl tmp (fun _ => blank))
            (.seq (dropR bn tpl tmp) (.act (pop2 tpl)))))))

lemma copyR_exec_upd (src tpl tmp : Fin T) (h1 : src ≠ tpl) (h2 : src ≠ tmp) (h3 : tpl ≠ tmp)
    (f : Fin (A + 4) → Fin (A + 4)) (v : HS T Q A U) (S : Stacks T A) (ht : S.R tmp = [])
    (L : List (Fin (A + 4))) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyR src tpl tmp f) (mk v { S with R := Function.update S.R tpl L })
        (4 * (S.R src).length + 4)
        (mk v' { S with R := Function.update S.R tpl (((S.R src).map f).reverse ++ L) }) := by
  obtain ⟨v', hu, he⟩ := copyR_exec body src tpl tmp h1 h2 h3 f v
    { S with R := Function.update S.R tpl L } (by simp [Function.update_of_ne h3.symm, ht])
  exact ⟨v', hu, Exec.cast he (by simp [Function.update_of_ne h1])
    (by simp [Function.update_of_ne h1])⟩

lemma dropR_exec_upd (cnt tpl tmp : Fin T) (h1 : cnt ≠ tpl) (h2 : cnt ≠ tmp) (h3 : tpl ≠ tmp)
    (v : HS T Q A U) (S : Stacks T A) (ht : S.R tmp = []) (L : List (Fin (A + 4))) :
    ∃ v', v'.user = v.user ∧
      Exec body (dropR cnt tpl tmp) (mk v { S with R := Function.update S.R tpl L })
        (4 * (S.R cnt).length + 4)
        (mk v' { S with R := Function.update S.R tpl (L.drop (S.R cnt).length) }) := by
  obtain ⟨v', hu, he⟩ := dropR_exec body cnt tpl tmp h1 h2 h3 v
    { S with R := Function.update S.R tpl L } (by simp [Function.update_of_ne h3.symm, ht])
  exact ⟨v', hu, Exec.cast he (by simp [Function.update_of_ne h1])
    (by simp [Function.update_of_ne h1])⟩

/-- `buildTpl` writes the template in `4 w + 8 p + 8 b + 22` steps and restores every other
register. -/
theorem buildTpl_exec (bn pn wn tpl tmp : Fin T) (hreg : [bn, pn, wn, tpl, tmp].Nodup)
    {b p w : ℕ} (hbp : b + 2 ≤ p) (v : HS T Q A U) (S : Stacks T A)
    (hb : (S.R bn).length = b) (hp : (S.R pn).length = p) (hw : (S.R wn).length = w)
    (htpl : S.R tpl = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (buildTpl bn pn wn tpl tmp) (mk v S) (4 * w + 8 * p + 8 * b + 22)
        (mk v' { S with R := Function.update S.R tpl (tplOf A (p - b - 2) b (w - p + 2)) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, d1⟩ := hreg
  have hS : S = { S with R := Function.update S.R tpl [] } := by
    cases S; simp only [Stacks.mk.injEq, true_and]; funext k
    simp only [Function.update_apply]; split_ifs <;> simp_all
  have hpush : ∀ (u : HS T Q A U) (L : List (Fin (A + 4))),
      (push2 tpl : Act T Q A U).run (mk u { S with R := Function.update S.R tpl L }) =
        mk u { S with R := Function.update S.R tpl (blank :: blank :: L) } := by
    intro u L; simp [push2, Action.run, update_rt]
  have hpop : ∀ (u : HS T Q A U) (L : List (Fin (A + 4))),
      (pop2 tpl : Act T Q A U).run (mk u { S with R := Function.update S.R tpl L }) =
        mk u { S with R := Function.update S.R tpl L.tail.tail } := by
    intro u L; simp [pop2, Action.run, update_rt]
  obtain ⟨v₁, hu₁, he₁⟩ :=
    copyR_exec_upd body wn tpl tmp c1 c2 d1 (fun _ => blank) v S htmp []
  rw [← hS, show ((S.R wn).map fun _ => blank).reverse ++ [] = List.replicate w blank by
    simp [hw]] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := dropR_exec_upd body pn tpl tmp b2 b3 d1 v₁ S htmp
    (List.replicate w blank)
  rw [hp, List.drop_replicate] at he₂
  have he₃ := Exec.act (body := body) (push2 tpl)
    (mk v₂ { S with R := Function.update S.R tpl (List.replicate (w - p) blank) })
  rw [hpush, show blank :: blank :: List.replicate (w - p) blank =
    List.replicate (w - p + 2) (blank : Fin (A + 4)) by simp [List.replicate_succ]] at he₃
  obtain ⟨v₄, hu₄, he₄⟩ :=
    copyR_exec_upd body bn tpl tmp a3 a4 d1 (fun _ => separator) v₂ S htmp
    (List.replicate (w - p + 2) blank)
  rw [show ((S.R bn).map fun _ => separator).reverse = List.replicate b separator by
    simp [hb]] at he₄
  obtain ⟨v₅, hu₅, he₅⟩ :=
    copyR_exec_upd body pn tpl tmp b2 b3 d1 (fun _ => blank) v₄ S htmp
    (List.replicate b separator ++ List.replicate (w - p + 2) blank)
  rw [show ((S.R pn).map fun _ => blank).reverse = List.replicate p blank by simp [hp]] at he₅
  obtain ⟨v₆, hu₆, he₆⟩ := dropR_exec_upd body bn tpl tmp a3 a4 d1 v₅ S htmp
    (List.replicate p blank ++ (List.replicate b separator ++ List.replicate (w - p + 2) blank))
  have e₆ : (List.replicate p (blank : Fin (A + 4)) ++ (List.replicate b separator ++
      List.replicate (w - p + 2) blank)).drop b =
      blank :: blank :: tplOf A (p - b - 2) b (w - p + 2) := by
    rw [List.drop_append_of_le_length (by simp; omega), List.drop_replicate,
      show p - b = p - b - 2 + 2 by omega]
    simp [tplOf, List.replicate_succ]
  rw [hb, e₆] at he₆
  have he₇ := Exec.act (body := body) (pop2 tpl) (mk v₆ { S with
    R := Function.update S.R tpl (blank :: blank :: tplOf A (p - b - 2) b (w - p + 2)) })
  rw [hpop] at he₇
  refine ⟨v₆, by rw [hu₆, hu₅, hu₄, hu₂, hu₁], Exec.cast (Exec.seq he₁ (Exec.seq he₂
    (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆ he₇)))))) (by rw [hw, hp, hb]; ring)
    rfl⟩

/-! ### Records -/

/-- One template position: pop the marker from `tpl` onto `tmp`; at a digit marker pop a bit
symbol from `rx` (an empty `rx` reads as `false`) and push its pair symbol onto `acc`, at a
zero marker push the zero pair onto `acc`; record in `flag` whether `tpl` is nonempty. -/
def recStep (tpl tmp rx acc : Fin T) : Act T Q A U :=
  .pop (.rt tpl) (fun v o => { v with sym := o })
    (.push (.rt tmp) (fun v => v.sym.getD blank)
      (.branch (fun v => decide (v.sym = some separator))
        (.pop (.rt rx) (fun v o => { v with sym := o })
          (.push (.rt acc) (fun v => pairSym A (decide (v.sym = some (bitSymbol true))) false)
            (peekR tpl)))
        (.push (.rt acc) (fun _ => pairSym A false false) (peekR tpl))))

/-- The pair symbols emitted along a template `t` reading the bits `l`. -/
def emitT (A : ℕ) : List (Fin (A + 4)) → List Bool → List (Fin (A + 4))
  | [], _ => []
  | s :: t, l => if s = separator then pairSym A (l.headD false) false :: emitT A t l.tail
      else pairSym A false false :: emitT A t l

/-- The record loop along a template `t`: `rx` loses `t.count separator` bits and `acc`
receives the reversed emitted symbols. -/
theorem recStep_loop (tpl tmp rx acc : Fin T) (hreg : [tpl, tmp, rx, acc].Nodup) :
    ∀ (t : List (Fin (A + 4))) (l : List Bool) (v : HS T Q A U) (S : Stacks T A), S.R tpl = t →
      S.R rx = l.map bitSymbol → v.flag = t.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (recStep tpl tmp rx acc))) (mk v S) (2 * t.length + 1)
          (mk v' { S with
            R := Function.update (Function.update (Function.update (Function.update S.R tpl [])
              tmp (t.reverse ++ S.R tmp)) rx ((l.drop (t.count separator)).map bitSymbol))
              acc ((emitT A t l).reverse ++ S.R acc) }) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2⟩, c1⟩ := hreg
  intro t
  induction t with
  | nil =>
      intro l v S hS hx hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          R := Function.update (Function.update (Function.update (Function.update S.R tpl [])
            tmp (([] : List (Fin (A + 4))).reverse ++ S.R tmp)) rx
            ((l.drop (([] : List (Fin (A + 4))).count separator)).map bitSymbol))
            acc ((emitT A [] l).reverse ++ S.R acc) } : Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hS hx
          congr 1
          funext k
          simp only [Function.update_apply]
          split_ifs <;> simp_all [emitT]
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons s t ih =>
      intro l v S hS hx hf
      by_cases hs : s = separator
      · subst hs
        obtain ⟨v', hu, he⟩ := ih l.tail
          { v with sym := (l.map bitSymbol).head?, flag := t.head?.isSome }
          { S with
            R := Function.update (Function.update (Function.update (Function.update S.R tpl t)
              tmp (separator :: S.R tmp)) rx (l.tail.map bitSymbol))
              acc (pairSym A (l.headD false) false :: S.R acc) }
          (by simp [a1, a2, a3]) (by simp [c1])
          rfl
        refine ⟨v', hu, ?_⟩
        have hrun : (recStep tpl tmp rx acc : Act T Q A U).run (mk v S) =
            mk { v with sym := (l.map bitSymbol).head?, flag := t.head?.isSome }
              { S with
                R := Function.update (Function.update (Function.update (Function.update S.R tpl t)
                  tmp (separator :: S.R tmp)) rx (l.tail.map bitSymbol))
                  acc (pairSym A (l.headD false) false :: S.R acc) } := by
          simp only [recStep, peekR, Action.run, mk_var, mk_stk, get_rt, hS, update_rt]
          simp [a1, a2, a3, Ne.symm a1, Ne.symm a2, Ne.symm a3,
            Ne.symm b1, Ne.symm b2, Ne.symm c1, hx]
          cases l with
          | nil => simp
          | cons β l => cases β <;> simp [bitSymbol, Fin.ext_iff]
        refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
          (hrun ▸ Exec.act (body := body) (recStep tpl tmp rx acc) (mk v S)) he)
          (by simp; ring) ?_
        congr 2
        funext k
        simp only [Function.update_apply]
        split_ifs <;> simp_all [emitT, List.drop_tail]
      · obtain ⟨v', hu, he⟩ := ih l
          { v with sym := some s, flag := t.head?.isSome }
          { S with
            R := Function.update (Function.update (Function.update S.R tpl t)
              tmp (s :: S.R tmp)) acc (pairSym A false false :: S.R acc) }
          (by simp [a1, a3])
          (by simp [c1, Ne.symm b1, Ne.symm a2, hx]) rfl
        refine ⟨v', hu, ?_⟩
        have hrun : (recStep tpl tmp rx acc : Act T Q A U).run (mk v S) =
            mk { v with sym := some s, flag := t.head?.isSome }
              { S with
                R := Function.update (Function.update (Function.update S.R tpl t)
                  tmp (s :: S.R tmp)) acc (pairSym A false false :: S.R acc) } := by
          simp only [recStep, peekR, Action.run, mk_var, mk_stk, get_rt, hS, update_rt]
          simp [a1, a3, Ne.symm a1, Ne.symm a3,
            Ne.symm b2, hs]
        refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
          (hrun ▸ Exec.act (body := body) (recStep tpl tmp rx acc) (mk v S)) he)
          (by simp; ring) ?_
        congr 2
        funext k
        simp only [Function.update_apply]
        split_ifs <;> simp_all [emitT]

/-- Pop `sn` onto `stmp`. -/
def popTo (sn stmp : Fin T) : Act T Q A U :=
  .pop (.rt sn) (fun v o => { v with sym := o })
    (.push (.rt stmp) (fun v => v.sym.getD blank) .done)

/-- One record: move a symbol of `sn` onto `stmp`, run `recStep` along the template `tpl`
(through `tmp`), move `tmp` back onto `tpl`, and record in `flag` whether `sn` is nonempty. -/
def recBody (sn stmp tpl tmp rx acc : Fin T) : Pr P T Q A U :=
  .seq (.act (popTo sn stmp))
    (.seq (whileR tpl (recStep tpl tmp rx acc)) (.seq (moveR tmp tpl id) (.act (peekR sn))))

/-- One record in `4 |t| + 6` steps: `sn` loses its top symbol to `stmp`, the template is
restored, `rx` loses `t.count separator` bits and `acc` receives the reversed record. -/
theorem recBody_exec (sn stmp tpl tmp rx acc : Fin T)
    (hreg : [sn, stmp, tpl, tmp, rx, acc].Nodup) (s : Fin (A + 4)) (rest t : List (Fin (A + 4)))
    (l : List Bool) (v : HS T Q A U) (S : Stacks T A) (hsn : S.R sn = s :: rest)
    (htpl : S.R tpl = t) (htmp : S.R tmp = []) (hx : S.R rx = l.map bitSymbol) :
    ∃ v', v'.user = v.user ∧ v'.flag = rest.head?.isSome ∧
      Exec body (recBody sn stmp tpl tmp rx acc) (mk v S) (4 * t.length + 6)
        (mk v' { S with
          R := Function.update (Function.update (Function.update (Function.update S.R sn rest)
            stmp (s :: S.R stmp)) rx ((l.drop (t.count separator)).map bitSymbol))
            acc ((emitT A t l).reverse ++ S.R acc) }) := by
  have hn := hreg
  have hr := List.nodup_reverse.2 hreg
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hr
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn hr
  set S₀ : Stacks T A := { S with
    R := Function.update (Function.update S.R sn rest) stmp (s :: S.R stmp) } with hS₀
  clear_value S₀
  have he₀ : Exec body (.act (popTo sn stmp)) (mk v S) 1 (mk { v with sym := some s } S₀) := by
    have := Exec.act (body := body) (popTo sn stmp) (mk v S)
    convert this using 1
    simp [popTo, Action.run, hsn, update_rt, hS₀, hr]
  obtain ⟨v₁, hu₁, he₁⟩ := recStep_loop body tpl tmp rx acc
    (by simp [List.nodup_cons, hn]) t l
    { v with sym := some s, flag := (S₀.R tpl).head?.isSome } S₀
    (by simp [hS₀, hr, htpl])
    (by simp [hS₀, hr, hx])
    (by simp [hS₀, hr, htpl])
  have hw₁ :=
    Exec.seq (Exec.act (body := body) (peekR tpl) (mk { v with sym := some s } S₀)) he₁
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tmp tpl (by simp [hr]) id v₁ { S₀ with
    R := Function.update (Function.update (Function.update (Function.update S₀.R tpl []) tmp
      (t.reverse ++ S₀.R tmp)) rx (List.map bitSymbol (List.drop (List.count separator t) l)))
      acc ((emitT A t l).reverse ++ S₀.R acc) }
  have he₃ := Exec.act (body := body) (peekR sn) (mk v₂ { S₀ with
    R := movedR (Function.update (Function.update (Function.update (Function.update S₀.R tpl [])
      tmp (t.reverse ++ S₀.R tmp)) rx (List.map bitSymbol (List.drop (List.count separator t) l)))
      acc ((emitT A t l).reverse ++ S₀.R acc)) tmp tpl id ((Function.update (Function.update
      (Function.update (Function.update S₀.R tpl []) tmp (t.reverse ++ S₀.R tmp)) rx
      (List.map bitSymbol (List.drop (List.count separator t) l))) acc
      ((emitT A t l).reverse ++ S₀.R acc)) tmp) })
  rw [peekR_run] at he₃
  refine ⟨{ v₂ with flag := rest.head?.isSome }, by simp [hu₂, hu₁], rfl,
    Exec.cast (Exec.seq he₀ (Exec.seq hw₁ (Exec.seq he₂ he₃))) ?_ ?_⟩
  · simp [hS₀, hn, hr, htmp]; ring
  · clear he₀ hw₁ he₁ he₂ he₃ hu₁ hu₂
    subst hS₀
    congr 2
    · simp only [movedR, Function.update_apply]
      simp [hn]
    · funext k
      simp only [movedR, Function.update_apply]
      by_cases h1 : k = sn
      · subst h1; simp [hn]
      by_cases h2 : k = stmp
      · subst h2; simp [hn]
      by_cases h3 : k = tpl
      · subst h3; simp [hn, hr, htpl, htmp]
      by_cases h4 : k = tmp
      · subst h4; simp [hn, hr, htmp]
      by_cases h5 : k = rx
      · subst h5; simp [hn, hr]
      by_cases h6 : k = acc
      · subst h6; simp [hr]
      simp [h1, h2, h3, h4, h5, h6]

/-- The pair symbols of `n` records along the template `t`, reading the bits `l`: each record
consumes `t.count separator` bits. -/
def emitN (A : ℕ) (t : List (Fin (A + 4))) : ℕ → List Bool → List (Fin (A + 4))
  | 0, _ => []
  | n + 1, l => emitT A t l ++ emitN A t n (l.drop (t.count separator))

/-- The record loop: one record per symbol of `sn`, in `|sn| (4 |t| + 7) + 1` steps. -/
theorem records_loop (sn stmp tpl tmp rx acc : Fin T)
    (hreg : [sn, stmp, tpl, tmp, rx, acc].Nodup) (t : List (Fin (A + 4))) :
    ∀ (sl : List (Fin (A + 4))) (l : List Bool) (v : HS T Q A U) (S : Stacks T A),
      S.R sn = sl → S.R tpl = t → S.R tmp = [] → S.R rx = l.map bitSymbol →
      v.flag = sl.head?.isSome →
      ∃ v', v'.user = v.user ∧
        Exec body (.loop (·.flag) (recBody sn stmp tpl tmp rx acc)) (mk v S)
          (sl.length * (4 * t.length + 7) + 1)
          (mk v' { S with
            R := Function.update (Function.update (Function.update (Function.update S.R sn [])
              stmp (sl.reverse ++ S.R stmp)) rx ((l.drop (sl.length * t.count separator)).map
              bitSymbol)) acc ((emitN A t sl.length l).reverse ++ S.R acc) }) := by
  have hn := hreg
  have hr := List.nodup_reverse.2 hreg
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hr
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn hr
  intro sl
  induction sl with
  | nil =>
      intro l v S hsn htpl htmp hx hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          R := Function.update (Function.update (Function.update (Function.update S.R sn [])
            stmp (([] : List (Fin (A + 4))).reverse ++ S.R stmp)) rx
            ((l.drop (([] : List (Fin (A + 4))).length * t.count separator)).map bitSymbol))
            acc ((emitN A t ([] : List (Fin (A + 4))).length l).reverse ++ S.R acc) } :
            Stacks T A) = S := by
        cases S with
        | mk inp out L R =>
          simp only at hsn hx
          congr 1
          funext k
          simp only [Function.update_apply]
          by_cases h1 : k = sn
          · subst h1; simp [hn, hsn]
          by_cases h2 : k = stmp
          · subst h2; simp [hn]
          by_cases h5 : k = rx
          · subst h5; simp [hn, hx]
          by_cases h6 : k = acc
          · subst h6; simp [emitN]
          simp [h1, h2, h5, h6]
      rw [this]
      refine Exec.cast (Exec.loop_false (f := fun v : HS T Q A U => v.flag) (by simpa using hf))
        (by simp) rfl
  | cons s rest ih =>
      intro l v S hsn htpl htmp hx hf
      obtain ⟨v₁, hu₁, hf₁, he₁⟩ :=
        recBody_exec body sn stmp tpl tmp rx acc hreg s rest t l v S hsn htpl htmp hx
      obtain ⟨v', hu, he⟩ := ih (l.drop (t.count separator)) v₁ { S with
        R := Function.update (Function.update (Function.update (Function.update S.R sn rest)
          stmp (s :: S.R stmp)) rx ((l.drop (t.count separator)).map bitSymbol))
          acc ((emitT A t l).reverse ++ S.R acc) }
        (by simp [hn])
        (by simp [hn, hr, htpl])
        (by simp [hn, hr, htmp])
        (by simp [hn]) hf₁
      refine ⟨v', by rw [hu, hu₁], Exec.cast (Exec.loop_true (body := body) (f := (·.flag))
        (by simpa using hf) he₁ he) (by simp; ring) ?_⟩
      clear he he₁ ih
      congr 2
      funext k
      simp only [Function.update_apply]
      have hdrop : (l.drop (t.count separator)).drop (rest.length * t.count separator) =
          l.drop ((rest.length + 1) * t.count separator) := by
        rw [List.drop_drop]; congr 1; ring
      by_cases h1 : k = sn
      · subst h1; simp [hn]
      by_cases h2 : k = stmp
      · subst h2; simp [hn]
      by_cases h5 : k = rx
      · subst h5; simp [hn, hdrop]
      by_cases h6 : k = acc
      · subst h6; simp [emitN]
      simp [h1, h2, h5, h6]

/-! ### Emitted symbols -/

lemma blank_ne_separator : (blank : Fin (A + 4)) ≠ separator := by
  simp [blank, separator, Fin.ext_iff]

lemma length_emitT : ∀ (t : List (Fin (A + 4))) (l : List Bool), (emitT A t l).length = t.length
  | [], _ => rfl
  | s :: t, l => by
      unfold emitT
      split_ifs <;> simp [length_emitT t]

lemma length_emitN (t : List (Fin (A + 4))) :
    ∀ (n : ℕ) (l : List Bool), (emitN A t n l).length = n * t.length
  | 0, _ => by simp [emitN]
  | n + 1, l => by simp [emitN, length_emitT, length_emitN t n]; ring

lemma emitT_append : ∀ (t₁ t₂ : List (Fin (A + 4))) (l : List Bool),
    emitT A (t₁ ++ t₂) l = emitT A t₁ l ++ emitT A t₂ (l.drop (t₁.count separator))
  | [], _, _ => by simp [emitT]
  | s :: t₁, t₂, l => by
      by_cases hs : s = separator
      · subst hs
        simp [emitT, emitT_append t₁ t₂ l.tail, List.drop_tail]
      · simp [emitT, hs, emitT_append t₁ t₂ l]

lemma emitT_zeros (n : ℕ) (l : List Bool) :
    emitT A (List.replicate n blank) l = List.replicate n (pairSym A false false) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, emitT, blank_ne_separator, ih]

lemma emitT_digits (b : ℕ) : ∀ l : List Bool,
    emitT A (List.replicate b separator) l =
      List.ofFn fun j : Fin b => pairSym A (l.getD j false) false := by
  induction b with
  | zero => intro l; rfl
  | succ b ih =>
      intro l
      simp only [List.replicate_succ, emitT, ↓reduceIte, ih, List.ofFn_succ]
      cases l <;> simp

lemma count_tplOf (e b f : ℕ) : (tplOf A e b f).count separator = b := by
  simp [tplOf, List.count_replicate, blank_ne_separator]

lemma emitT_tplOf (e b f : ℕ) (l : List Bool) :
    emitT A (tplOf A e b f) l = digitRec A e b f l := by
  rw [tplOf, emitT_append, emitT_append, emitT_zeros, emitT_digits, emitT_zeros, digitRec]
  simp [List.count_replicate, blank_ne_separator, List.getD_eq_getElem?_getD]

lemma length_tplOf (e b f : ℕ) : (tplOf A e b f).length = e + b + f := by simp [tplOf]; ring

lemma emitN_eq (t : List (Fin (A + 4))) : ∀ (n : ℕ) (l : List Bool),
    emitN A t n l = (List.ofFn fun i : Fin n => emitT A t (l.drop (i * t.count separator))).flatten
  | 0, _ => by simp [emitN]
  | n + 1, l => by
      rw [emitN, emitN_eq t n, List.ofFn_succ, List.flatten_cons]
      simp only [Fin.val_zero, zero_mul, List.drop_zero, Fin.val_succ, List.drop_drop]
      congr 3
      funext i
      congr 2
      ring

/-! ### The coefficient stream -/

lemma getD_drop (l : List Bool) (n j : ℕ) : (l.drop n).getD j false = l.getD (n + j) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The coefficient stream of the base-`2^b` digits of the MSB-first word `xs`: `S` records,
record `i` holding `red w (digit_i · 2^(p - b - 2))` as `w` pair symbols. -/
def digitStream (A b p w S : ℕ) (xs : List Bool) : List (Fin (A + 4)) :=
  (List.ofFn fun i : Fin S =>
    red w (⟨((digitsOf b xs).getD i 0 : ℤ) * 2 ^ (p - b - 2), 0⟩ : GaussianInt)).flatMap
    (coeffSyms A w)

/-- The records emitted along the digit template from the LSB-first bits of `binaryValue xs`
form the coefficient stream. -/
theorem emitN_tplOf {b p w : ℕ} (hb : 0 < b) (hbp : b + 2 ≤ p) (hpw : p ≤ w) (S : ℕ)
    (xs : List Bool) :
    emitN A (tplOf A (p - b - 2) b (w - p + 2)) S (encodingNatBool.encode (binaryValue xs)) =
      digitStream A b p w S xs := by
  rw [emitN_eq, count_tplOf, digitStream, List.flatMap_def, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply]
  have hd := getD_lt (digitsOf_lt hb xs) (by positivity : 0 < 2 ^ b) i
  rw [emitT_tplOf, coeffSyms_digit (show p - b - 2 + b ≤ w by omega) hd
    (l := (encodingNatBool.encode (binaryValue xs)).drop (i * b)),
    show w - (p - b - 2) - b = w - p + 2 by omega]
  intro j hj
  rw [getD_drop, show encodingNatBool.encode (binaryValue xs) = encodeNat (binaryValue xs) from rfl,
    getD_encodeNat, getD_digitsOf hb, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hj, Nat.mul_comm, Nat.add_comm]

/-- The stream depends on the word only through its value. -/
theorem digitStream_congr {b : ℕ} (hb : 0 < b) (A p w S : ℕ) {xs ys : List Bool}
    (h : binaryValue xs = binaryValue ys) :
    digitStream A b p w S xs = digitStream A b p w S ys := by
  simp only [digitStream, getD_digitsOf hb, h]

lemma length_digitStream (A b p w S : ℕ) (xs : List Bool) :
    (digitStream A b p w S xs).length = S * w := by
  simp [digitStream, List.length_flatMap, Function.comp_def, List.ofFn_const, List.sum_replicate]

/-! ### The digit stage -/

/-- The digit stage: build the template on `tpl`, run one record per symbol of `sn` (pushing
the reversed stream onto `acc` and consuming `rx`), restore `sn`, move `acc` onto `dst` (which
reverses it into stream order), and empty `tpl`. -/
def digitRecords (rx bn pn wn sn tpl tmp stmp acc dst : Fin T) : Pr P T Q A U :=
  .seq (buildTpl bn pn wn tpl tmp)
    (.seq (.act (peekR sn))
      (.seq (.loop (·.flag) (recBody sn stmp tpl tmp rx acc))
        (.seq (moveR stmp sn id)
          (.seq (moveR acc dst id) (emptyR tpl)))))

/-- The step count of `digitRecords` for `S` records of width `w`. -/
def digitCost (b p w S : ℕ) : ℕ := S * (6 * w + 9) + 6 * w + 8 * p + 8 * b + 30

/-- `digitRecords` on an arbitrary LSB-first bit list `l` in `rx`: `rx` keeps the bits beyond
the first `S b`, and `dst` receives the emitted records. -/
theorem digitRecords_exec_bits (rx bn pn wn sn tpl tmp stmp acc dst : Fin T)
    (hreg : [rx, bn, pn, wn, sn, tpl, tmp, stmp, acc, dst].Nodup)
    {b p w S : ℕ} (hbp : b + 2 ≤ p) (hpw : p ≤ w) (l : List Bool)
    (v : HS T Q A U) (St : Stacks T A) (hx : St.R rx = l.map bitSymbol)
    (hbn : (St.R bn).length = b) (hpn : (St.R pn).length = p) (hwn : (St.R wn).length = w)
    (hsn : (St.R sn).length = S) (htpl : St.R tpl = []) (htmp : St.R tmp = [])
    (hstmp : St.R stmp = []) (hacc : St.R acc = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (digitRecords rx bn pn wn sn tpl tmp stmp acc dst) (mk v St)
        (digitCost b p w S)
        (mk v' { St with
          R := Function.update (Function.update St.R rx ((l.drop (S * b)).map bitSymbol)) dst
            (emitN A (tplOf A (p - b - 2) b (w - p + 2)) S l ++ St.R dst) }) := by
  have hn := hreg
  have hr := List.nodup_reverse.2 hreg
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hr
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn hr
  obtain ⟨t, ht⟩ : ∃ t, t = tplOf A (p - b - 2) b (w - p + 2) := ⟨_, rfl⟩
  have htlen : t.length = w := by rw [ht, length_tplOf]; omega
  have htc : t.count separator = b := by rw [ht, count_tplOf]
  rw [← ht]
  -- the template
  obtain ⟨v₁, hu₁, he₁⟩ := buildTpl_exec body bn pn wn tpl tmp
    (by simp [List.nodup_cons, hn]) hbp v St hbn hpn hwn htpl htmp
  rw [← ht] at he₁
  -- the records
  have he₂ :=
    Exec.act (body := body) (peekR sn) (mk v₁ { St with R := Function.update St.R tpl t })
  rw [peekR_run] at he₂
  obtain ⟨v₃, hu₃, he₃⟩ := records_loop body sn stmp tpl tmp rx acc
    (by simp [List.nodup_cons, hn, hr]) t (St.R sn) l
    { v₁ with flag := (Function.update St.R tpl t sn).head?.isSome }
    { St with R := Function.update St.R tpl t }
    (by simp [hn]) (by simp)
    (by simp [hr, htmp]) (by simp [hn, hx])
    (by simp [hn])
  dsimp only at he₃
  generalize hR₃ : Function.update (Function.update (Function.update (Function.update
    (Function.update St.R tpl t) sn []) stmp ((St.R sn).reverse ++ Function.update St.R tpl t stmp))
    rx (List.map bitSymbol (List.drop ((St.R sn).length * List.count separator t) l))) acc
    ((emitN A t (St.R sn).length l).reverse ++ Function.update St.R tpl t acc) = R₃ at he₃
  -- restore `sn`
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body stmp sn (by simp [hr]) id v₃
    { St with R := R₃ }
  dsimp only at he₄
  generalize hR₄ : movedR R₃ stmp sn id (R₃ stmp) = R₄ at he₄
  -- the stream onto `dst`
  obtain ⟨v₅, hu₅, he₅⟩ :=
    moveR_exec body acc dst (by simp [hn]) id v₄ { St with R := R₄ }
  dsimp only at he₅
  generalize hR₅ : movedR R₄ acc dst id (R₄ acc) = R₅ at he₅
  -- empty the template
  obtain ⟨v₆, hu₆, he₆⟩ := emptyR_exec body tpl v₅ { St with R := R₅ }
  dsimp only at he₆
  have h₃stmp : R₃ stmp = (St.R sn).reverse := by
    rw [← hR₃]; simp [hn, hr, hstmp]
  have h₄acc : R₄ acc = (emitN A t (St.R sn).length l).reverse := by
    rw [← hR₄, ← hR₃]; simp [movedR, hn, hr, hacc]
  have h₅tpl : R₅ tpl = t := by
    rw [← hR₅, ← hR₄, ← hR₃]; simp [movedR, hn, hr]
  refine ⟨v₆, by rw [hu₆, hu₅, hu₄, hu₃, hu₁],
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆)))))
      ?_ ?_⟩
  · rw [h₃stmp, h₄acc, h₅tpl, List.length_reverse, List.length_reverse, length_emitN, htlen,
      hsn, digitCost]
    ring
  · clear he₁ he₂ he₃ he₄ he₅ he₆
    congr 2
    funext k
    rw [← hR₅, ← hR₄, ← hR₃]
    simp only [movedR, Function.update_apply]
    by_cases h1 : k = rx
    · subst h1; simp [hn, hsn, htc]
    by_cases h2 : k = sn
    · subst h2; simp [hn, hr, hstmp]
    by_cases h3 : k = tpl
    · subst h3; simp [hn, hr, htpl]
    by_cases h4 : k = stmp
    · subst h4; simp [hn, hr, hstmp]
    by_cases h5 : k = acc
    · subst h5; simp [hn, hr, hacc]
    by_cases h6 : k = dst
    · subst h6; simp [hr, hacc, hsn]
    simp [h1, h2, h3, h4, h5, h6]

/-- **The digit stage.** For `1 ≤ b`, `b + 2 ≤ p ≤ w` and an MSB-first word `xs` of value `x`
with at most `S` base-`2^b` digits, `digitRecords` consumes the LSB-first bits of `x` in `rx` and
pushes the coefficient stream `digitStream A b p w S xs` onto `dst`, in `digitCost b p w S`
steps. The unary registers `bn`, `pn`, `wn`, `sn` (lengths `b`, `p`, `w`, `S`, any symbols) are
restored, the scratch registers `tpl`, `tmp`, `stmp`, `acc` start and end empty, and every other
stack is unchanged. -/
theorem digitRecords_exec (rx bn pn wn sn tpl tmp stmp acc dst : Fin T)
    (hreg : [rx, bn, pn, wn, sn, tpl, tmp, stmp, acc, dst].Nodup)
    {b p w S : ℕ} (hb : 1 ≤ b) (hbp : b + 2 ≤ p) (hpw : p ≤ w)
    (x : ℕ) (xs : List Bool) (hxs : binaryValue xs = x) (hS : (digitsOf b xs).length ≤ S)
    (v : HS T Q A U) (St : Stacks T A)
    (hx : St.R rx = (encodingNatBool.encode x).map bitSymbol)
    (hbn : (St.R bn).length = b) (hpn : (St.R pn).length = p) (hwn : (St.R wn).length = w)
    (hsn : (St.R sn).length = S) (htpl : St.R tpl = []) (htmp : St.R tmp = [])
    (hstmp : St.R stmp = []) (hacc : St.R acc = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (digitRecords rx bn pn wn sn tpl tmp stmp acc dst) (mk v St)
        (digitCost b p w S)
        (mk v' { St with
          R := Function.update (Function.update St.R rx []) dst
            (digitStream A b p w S xs ++ St.R dst) }) := by
  subst hxs
  obtain ⟨v', hu, he⟩ :=
    digitRecords_exec_bits body rx bn pn wn sn tpl tmp stmp acc dst hreg hbp hpw
      (encodingNatBool.encode (binaryValue xs)) v St hx hbn hpn hwn hsn htpl htmp hstmp hacc
  have hlen : (encodingNatBool.encode (binaryValue xs)).length ≤ S * b := by
    rw [Nat.mul_comm]
    exact length_encodeNat_le (binaryValue_lt_of_digitsOf hb hS)
  rw [List.drop_eq_nil_of_le hlen, emitN_tplOf hb hbp hpw] at he
  exact ⟨v', hu, he⟩

/-- `digitCost b p w S ≤ 32 (S + 1) w`: linear in the stream length `S w` plus the record
width. -/
theorem digitCost_le {b p w S : ℕ} (hb : 1 ≤ b) (hbp : b + 2 ≤ p) (hpw : p ≤ w) :
    digitCost b p w S ≤ 32 * ((S + 1) * w) := by
  unfold digitCost
  have hw : 3 ≤ w := by omega
  nlinarith

/-! ### Grid values -/

/-- The stored numerator `digit · 2^(p - b - 2)` on the grid `2^(-p) ℤ[i]` is the quarter-scaled
digit `scaledDigits S b ds i` of the exact-recovery argument. -/
theorem numerator_div_eq_scaledDigits {b p S : ℕ} [NeZero S] (hbp : b + 2 ≤ p) (ds : List ℕ)
    (i : ZMod S) :
    GaussianInt.toComplex (⟨(ds.getD i.val 0 : ℤ) * 2 ^ (p - b - 2), 0⟩ : GaussianInt) /
        2 ^ p =
      IntegerMultBounds.ExactRecovery.scaledDigits S b ds i := by
  obtain ⟨e, rfl⟩ : ∃ e, p = e + (b + 2) := ⟨p - (b + 2), by omega⟩
  rw [show e + (b + 2) - b - 2 = e by omega]
  simp only [IntegerMultBounds.ExactRecovery.scaledDigits, vecZ, GaussianInt.toComplex_def',
    pow_add]
  push_cast
  have h1 : (2 : ℂ) ^ e ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2 : (2 : ℂ) ^ (b + 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  ring

end IntegerMultBounds.MathlibTM2.Fast
