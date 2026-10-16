module

public import IntegerMultBounds.MathlibTM2.Host.Index
public import IntegerMultBounds.MathlibTM2.Binary
public import IntegerMultBounds.NLogN.Kronecker

/-!
# The output stage of the fast multiplier (F11)

The coefficients `c_0, …, c_{S-1}` of the product arrive on register `dat` as `S` words of `W`
bits: `dat` holds `cs.flatMap (binSyms W)`, so word `0` is on top and each word has its least
significant bit on top. `carryOut` propagates carries in base `2 ^ b` and pushes the canonical
binary word of `N = evalBase (2 ^ b) cs` onto the Mathlib output stack `out`: `out` gains exactly
`encodingNatBool.encode N` (least significant bit on top, no trailing zeroes). This is the
orientation in which `Store.only … .out` presents the machine output (head = top).

**Registers.** An injective family `oreg : OReg → Fin T` of host registers (right stacks):

* `dat`: the input words; ends empty.
* `wr`, `br`: `W` and `b` in unary (any `W`, resp. `b`, symbols); both end empty.
* `ct`: spare register of the two unary counters.
* `cr`: the carry, in binary with its least significant bit on top.
* `sm`: the sum of one word and the carry, most significant bit on top.
* `acc`: the emitted bits, the latest on top.

`ct`, `cr`, `sm` and `acc` start empty, so every register of the stage ends empty. The scan
slots `oreg .cr` and `oreg .sm`, `sym` and `flag` serve as scratch. The `user` component, `inp`,
the left stacks and every register outside the family stay unchanged.

**One word** (`wordIter`). A full adder adds the word `c_i` to the carry `x`, one bit of each
per step (`W` steps counted by `wr`; the adder's carry bit lives in scan slot `oreg .sm`), and
pushes the sum bits onto `sm`; the adder's last carry is pushed on top. Moving `sm` onto `cr`
leaves `binSyms (W + 1) (c_i + x)` there, and `b` steps counted by `br` move its low `b` bits
onto `acc`. The carry register then holds `binSyms (W + 1 - b) ((c_i + x) / 2 ^ b)`.

**Carry bound.** With `c_i < 2 ^ W` and `x < 2 ^ L`, `L ≤ W`, the sum is below `2 ^ (W + 1)`
(`word_sum_lt`) and the new carry below `2 ^ (W + 1 - b)` (`word_carry_lt`). From `x = 0`, the
carry register therefore always holds exactly `W + 1 - b ≤ W` bits after a word (`b ≥ 1`), and
popping `W` bits from it during the next addition empties it (`carryAfter_lt`).

**Output.** After the last word the carry register moves onto `acc`, which then holds
`outBits W b cs` reversed: the bits of `N` (`lsbVal_outBits`), most significant on top. Its
leading zero bits are popped (`dropZStep`), the rest moves onto `out` (`outStep`), and
`encodeNat_binaryValue` identifies the result. Finally `wr` and `br` are cleared.

**Cost** (`carryOut_exec`): exactly `carryOutCost W b S` steps,
`S (6W + 6b + 15) + 4 (W + 1 - b) [S > 0] + 2W + 2b + 12`, at most `(S + 1)(10W + 6b + 15)`
(`carryOutCost_le`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host Computability
open IntegerMultBounds.NLogN (evalBase)


/-! ### Arithmetic -/

/-- Sum bit of a full adder. -/
def fullSum (x y z : Bool) : Bool := xor (xor x y) z

/-- Carry bit of a full adder. -/
def fullCarry (x y z : Bool) : Bool := (x && y) || (z && (x || y))

lemma full_adder (d x : ℕ) (c : Bool) :
    (d + x + c.toNat).testBit 0 = fullSum (d.testBit 0) (x.testBit 0) c ∧
      (d + x + c.toNat) / 2 = d / 2 + x / 2 + (fullCarry (d.testBit 0) (x.testBit 0) c).toNat := by
  rcases Nat.mod_two_eq_zero_or_one d with hd | hd <;>
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> cases c <;>
    simp [Nat.testBit_zero, hd, hx, fullSum, fullCarry] <;> omega

/-- The value of a bit list read least significant bit first. -/
def lsbVal : List Bool → ℕ
  | [] => 0
  | x :: l => x.toNat + 2 * lsbVal l

lemma lsbVal_append (l₁ l₂ : List Bool) :
    lsbVal (l₁ ++ l₂) = lsbVal l₁ + 2 ^ l₁.length * lsbVal l₂ := by
  induction l₁ with
  | nil => simp [lsbVal]
  | cons x l ih => simp only [List.cons_append, lsbVal, ih, List.length_cons, pow_succ]; ring

lemma lsbVal_binBits (L a : ℕ) : lsbVal (binBits L a) = a % 2 ^ L := by
  induction L generalizing a with
  | zero => simp [lsbVal, Nat.mod_one]
  | succ L ih =>
      rw [binBits_succ, lsbVal, ih, pow_succ', Nat.mod_mul]
      rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [Nat.testBit_zero, h]

/-- The most-significant-first reading of a reversed list is its least-significant-first
value. -/
lemma binaryValue_reverse (l : List Bool) : binaryValue l.reverse = lsbVal l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      rw [List.reverse_cons, binaryValue_append, ih, Nat.bit_val, lsbVal]; ring

/-- The bits emitted by the word loop from the carry `x`: the low `b` bits of the sum of each
word and the running carry, least significant first. -/
def wordBits (b : ℕ) : List ℕ → ℕ → List Bool
  | [], _ => []
  | c :: cs, x => binBits b (c + x) ++ wordBits b cs ((c + x) / 2 ^ b)

/-- The carry after the words `cs`, from the carry `x`. -/
def carryAfter (b : ℕ) : List ℕ → ℕ → ℕ
  | [], x => x
  | c :: cs, x => carryAfter b cs ((c + x) / 2 ^ b)

/-- The width of the carry register after the words `cs`, from width `L`. -/
def lenAfter (W b : ℕ) (cs : List ℕ) (L : ℕ) : ℕ := if cs = [] then L else W + 1 - b

lemma lenAfter_cons (W b c : ℕ) (cs : List ℕ) (L : ℕ) :
    lenAfter W b (c :: cs) L = lenAfter W b cs (W + 1 - b) := by
  simp only [lenAfter, reduceCtorEq, ite_false]; split <;> rfl

lemma length_wordBits (b : ℕ) : ∀ (cs : List ℕ) (x : ℕ), (wordBits b cs x).length = b * cs.length
  | [], _ => by simp [wordBits]
  | c :: cs, x => by simp [wordBits, length_wordBits b cs]; ring

/-- The emitted bits and the final carry together carry the value of the words and the initial
carry. -/
lemma lsbVal_wordBits (b : ℕ) : ∀ (cs : List ℕ) (x : ℕ),
    lsbVal (wordBits b cs x) + 2 ^ (b * cs.length) * carryAfter b cs x = evalBase (2 ^ b) cs + x
  | [], x => by simp [wordBits, carryAfter, lsbVal, evalBase]
  | c :: cs, x => by
      have ih := lsbVal_wordBits b cs ((c + x) / 2 ^ b)
      have hd := Nat.mod_add_div (c + x) (2 ^ b)
      have h2 : 2 ^ b * (lsbVal (wordBits b cs ((c + x) / 2 ^ b)) +
          2 ^ (b * cs.length) * carryAfter b cs ((c + x) / 2 ^ b)) =
          2 ^ b * (evalBase (2 ^ b) cs + (c + x) / 2 ^ b) := by rw [ih]
      simp only [wordBits, carryAfter, evalBase, lsbVal_append, lsbVal_binBits, length_binBits,
        List.length_cons, Nat.mul_succ, pow_add]
      nlinarith [h2, hd]

lemma word_sum_lt {W L c x : ℕ} (hc : c < 2 ^ W) (hx : x < 2 ^ L) (hL : L ≤ W) :
    c + x < 2 ^ (W + 1) := by
  have : 2 ^ L ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hL
  rw [pow_succ]; omega

lemma word_carry_lt {W L b c x : ℕ} (hc : c < 2 ^ W) (hx : x < 2 ^ L) (hL : L ≤ W) :
    (c + x) / 2 ^ b < 2 ^ (W + 1 - b) := by
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  calc c + x < 2 ^ (W + 1) := word_sum_lt hc hx hL
    _ ≤ 2 ^ (W + 1 - b + b) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The carry fits its register, and the register is at most `W` bits wide. -/
lemma carryAfter_lt {W b : ℕ} (hb : 1 ≤ b) : ∀ (cs : List ℕ) (x L : ℕ), (∀ c ∈ cs, c < 2 ^ W) →
    x < 2 ^ L → L ≤ W → carryAfter b cs x < 2 ^ lenAfter W b cs L ∧ lenAfter W b cs L ≤ W
  | [], x, L, _, hx, hL => by simp [carryAfter, lenAfter, hx, hL]
  | c :: cs, x, L, hcs, hx, hL => by
      have hc := hcs c List.mem_cons_self
      have := carryAfter_lt hb cs ((c + x) / 2 ^ b) (W + 1 - b)
        (fun c' h => hcs c' (List.mem_cons_of_mem _ h)) (word_carry_lt hc hx hL) (by omega)
      simpa [carryAfter, lenAfter_cons] using this

/-- All bits produced from the words `cs`, least significant first: the emitted bits, then the
final carry register. -/
def outBits (W b : ℕ) (cs : List ℕ) : List Bool :=
  wordBits b cs 0 ++ binBits (lenAfter W b cs 0) (carryAfter b cs 0)

lemma lsbVal_outBits {W b : ℕ} (hb : 1 ≤ b) {cs : List ℕ} (hcs : ∀ c ∈ cs, c < 2 ^ W) :
    lsbVal (outBits W b cs) = evalBase (2 ^ b) cs := by
  have h1 := lsbVal_wordBits b cs 0
  have h2 := (carryAfter_lt hb cs 0 0 hcs (by simp) (Nat.zero_le _)).1
  rw [outBits, lsbVal_append, lsbVal_binBits, Nat.mod_eq_of_lt h2, length_wordBits]; omega

lemma length_outBits (W b : ℕ) (cs : List ℕ) :
    (outBits W b cs).length = b * cs.length + lenAfter W b cs 0 := by
  simp [outBits, length_wordBits]

/-! ### Registers -/

/-- Registers of the output stage. -/
inductive OReg
  | dat | wr | br | ct | cr | sm | acc
  deriving DecidableEq

/-- Every register of the output stage. -/
def allRegs : List OReg := [.dat, .wr, .br, .ct, .cr, .sm, .acc]

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- `S'` agrees with `S` on `inp`, `out`, the left stacks and every register outside
`oreg '' rs`. -/
def Fr (oreg : OReg → Fin T) (rs : List OReg) (S S' : Stacks T A) : Prop :=
  S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ ∀ k, (∀ r ∈ rs, k ≠ oreg r) → S'.R k = S.R k

section Frame

variable {oreg : OReg → Fin T} {rs rs₁ rs₂ : List OReg} {S S' S₁ S₂ S₃ : Stacks T A}

lemma Fr.refl (oreg : OReg → Fin T) (rs : List OReg) (S : Stacks T A) : Fr oreg rs S S :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

lemma Fr.trans (h₁ : Fr oreg rs₁ S₁ S₂) (h₂ : Fr oreg rs₂ S₂ S₃) (hs₁ : ∀ r ∈ rs₁, r ∈ rs)
    (hs₂ : ∀ r ∈ rs₂, r ∈ rs) : Fr oreg rs S₁ S₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, fun k hk =>
    (h₂.2.2.2 k fun r hr => hk r (hs₂ r hr)).trans (h₁.2.2.2 k fun r hr => hk r (hs₁ r hr))⟩

lemma Fr.get (hreg : Function.Injective oreg) (h : Fr oreg rs S S') (r : OReg) (hr : r ∉ rs) :
    S'.R (oreg r) = S.R (oreg r) :=
  h.2.2.2 _ fun _ hr' he => hr (hreg he ▸ hr')

end Frame

/-! ### The program -/

section Prog

variable (oreg : OReg → Fin T)

/-- Start an addition: clear the adder's carry bit and test the word counter. -/
def addInit : Act T Q A U :=
  .load (fun v => { v with scan := Function.update v.scan (oreg .sm) (bitSymbol false) })
    (peekR (oreg .wr))

/-- One full-adder step: move a counter symbol from `wr` to `ct`, pop a bit of the word and a
bit of the carry register (`0` once it is empty), push the sum bit onto `sm` and keep the carry
bit in scan slot `oreg .sm`. -/
def addStep : Act T Q A U :=
  .pop (.rt (oreg .wr)) (fun v o => { v with sym := o })
  (.push (.rt (oreg .ct)) (fun v => v.sym.getD blank)
  (.pop (.rt (oreg .dat)) (fun v o => { v with sym := o })
  (.pop (.rt (oreg .cr))
    (fun v o => { v with scan := Function.update v.scan (oreg .cr) (o.getD blank) })
  (.push (.rt (oreg .sm)) (fun v => bitSymbol (fullSum (symBit (v.sym.getD blank))
    (symBit (v.scan (oreg .cr))) (symBit (v.scan (oreg .sm)))))
  (.load (fun v => { v with
    scan := Function.update v.scan (oreg .sm) (bitSymbol (fullCarry (symBit (v.sym.getD blank))
      (symBit (v.scan (oreg .cr))) (symBit (v.scan (oreg .sm))))) })
  (peekR (oreg .wr)))))))

/-- Push the adder's last carry bit onto `sm`. -/
def pushCarry : Act T Q A U :=
  .push (.rt (oreg .sm)) (fun v => bitSymbol (symBit (v.scan (oreg .sm)))) .done

/-- One emitted bit: move a counter symbol from `br` to `ct` and a bit from the carry register
to `acc` (`0` once it is empty). -/
def emitStep : Act T Q A U :=
  .pop (.rt (oreg .br)) (fun v o => { v with sym := o })
  (.push (.rt (oreg .ct)) (fun v => v.sym.getD blank)
  (.pop (.rt (oreg .cr)) (fun v o => { v with sym := o })
  (.push (.rt (oreg .acc)) (fun v => bitSymbol (symBit (v.sym.getD blank)))
  (peekR (oreg .br)))))

/-- One word: add it to the carry register, emit the low `b` bits, and test for another
word. -/
def wordIter : Pr P T Q A U :=
  .seq (.act (addInit oreg))
  (.seq (.loop (·.flag) (.act (addStep oreg)))
  (.seq (.act (pushCarry oreg))
  (.seq (moveR (oreg .ct) (oreg .wr) id)
  (.seq (moveR (oreg .sm) (oreg .cr) id)
  (.seq (.act (peekR (oreg .br)))
  (.seq (.loop (·.flag) (.act (emitStep oreg)))
  (.seq (moveR (oreg .ct) (oreg .br) id)
    (.act (peekR (oreg .dat))))))))))

end Prog

/-- Is a stack top the zero bit? -/
def isZero (o : Option (Fin (A + 4))) : Bool := decide (o = some (bitSymbol false))

/-- Record in `flag` whether the top of register `i` is the zero bit. -/
def peekZ (i : Fin T) : Act T Q A U :=
  .peek (.rt i) (fun v o => { v with flag := isZero o }) .done

/-- Drop a leading zero bit. -/
def dropZStep (i : Fin T) : Act T Q A U := .pop (.rt i) (fun v _ => v) (peekZ i)

/-- Move a bit from register `i` to the output stack. -/
def outStep (i : Fin T) : Act T Q A U :=
  .pop (.rt i) (fun v o => { v with sym := o })
    (.push .out (fun v => symBit (v.sym.getD blank)) (peekR i))

/-- Pop register `i` and test it again. -/
def clearStep (i : Fin T) : Act T Q A U := .pop (.rt i) (fun v _ => v) (peekR i)

/-- Empty register `i`. -/
def clearR (i : Fin T) : Pr P T Q A U := whileR i (clearStep i)

/-- The output stage: carries in base `2 ^ b` over the words on `dat`, the bits of the result
onto `out` (least significant on top, no trailing zeroes), and every register of `oreg`
emptied. -/
def carryOut (oreg : OReg → Fin T) : Pr P T Q A U :=
  .seq (.act (peekR (oreg .dat)))
  (.seq (.loop (·.flag) (wordIter oreg))
  (.seq (moveR (oreg .cr) (oreg .acc) id)
  (.seq (.act (peekZ (oreg .acc)))
  (.seq (.loop (·.flag) (.act (dropZStep (oreg .acc))))
  (.seq (.act (peekR (oreg .acc)))
  (.seq (.loop (·.flag) (.act (outStep (oreg .acc))))
  (.seq (clearR (oreg .wr)) (clearR (oreg .br)))))))))

/-! ### Binary numerals on a register -/

lemma symBit_blank : symBit (blank : Fin (A + 4)) = false := by
  simp [symBit, blank, bitSymbol]

/-- Popping a binary numeral reads its lowest bit, also when the register is empty. -/
lemma symBit_head_binSyms {L y : ℕ} (hy : y < 2 ^ L) :
    symBit ((binSyms L y : List (Fin (A + 4))).head?.getD blank) = y.testBit 0 := by
  cases L with
  | zero =>
      have : y = 0 := by simpa using hy
      subst this; simp [binSyms, symBit_blank]
  | succ L => simp [binSyms_succ]

lemma tail_binSyms (L y : ℕ) :
    (binSyms L y : List (Fin (A + 4))).tail = binSyms (L - 1) (y / 2) := by
  cases L with
  | zero => simp [binSyms]
  | succ L => simp [binSyms_succ]

lemma div_two_lt {L y : ℕ} (hy : y < 2 ^ L) : y / 2 < 2 ^ (L - 1) := by
  cases L with
  | zero =>
      have : y = 0 := by simpa using hy
      subst this; simp
  | succ L => rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ]; simpa using hy

lemma binSyms_succ_last (L y : ℕ) :
    (binSyms (L + 1) y : List (Fin (A + 4))) = binSyms L y ++ [bitSymbol (y.testBit L)] := by
  simp only [binSyms]
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

/-! ### The addition loop -/

variable {oreg : OReg → Fin T}

lemma addStep_run (hreg : Function.Injective oreg) (v : HS T Q A U) (S : Stacks T A)
    {e : Fin (A + 4)} {lw : List (Fin (A + 4))} (hw : S.R (oreg .wr) = e :: lw) :
    (addStep oreg).run (mk v S) = mk ((addStep oreg).run (mk v S)).var
      { S with
        R := Function.update (Function.update (Function.update (Function.update
          (Function.update S.R (oreg .wr) lw) (oreg .ct) (e :: S.R (oreg .ct)))
          (oreg .dat) (S.R (oreg .dat)).tail) (oreg .cr) (S.R (oreg .cr)).tail)
          (oreg .sm) (bitSymbol (fullSum (symBit ((S.R (oreg .dat)).head?.getD blank))
            (symBit ((S.R (oreg .cr)).head?.getD blank)) (symBit (v.scan (oreg .sm)))) ::
              S.R (oreg .sm)) } := by
  simp [addStep, Action.run, peekR, update_rt, hw, hreg.eq_iff]

lemma addStep_var (hreg : Function.Injective oreg) (v : HS T Q A U) (S : Stacks T A)
    {e : Fin (A + 4)} {lw : List (Fin (A + 4))} (hw : S.R (oreg .wr) = e :: lw) :
    ((addStep oreg).run (mk v S)).var.user = v.user ∧
    ((addStep oreg).run (mk v S)).var.flag = lw.head?.isSome ∧
    symBit (((addStep oreg).run (mk v S)).var.scan (oreg .sm)) =
      fullCarry (symBit ((S.R (oreg .dat)).head?.getD blank))
            (symBit ((S.R (oreg .cr)).head?.getD blank)) (symBit (v.scan (oreg .sm))) := by
  simp [addStep, Action.run, peekR, update_rt, hw, hreg.eq_iff]

/-- The addition loop, by induction on the counter `lw`: the word `d` on top of `dat` plus the
carry register `binSyms L x` plus the carry bit `cb` goes onto `sm`, most significant bit on
top, and the adder's carry bit ends as bit `lw.length` of the sum. -/
theorem addStep_loop (hreg : Function.Injective oreg) :
    ∀ (lw : List (Fin (A + 4))) (d x L : ℕ) (cb : Bool) (rest : List (Fin (A + 4)))
      (v : HS T Q A U) (S : Stacks T A),
      d < 2 ^ lw.length → x < 2 ^ L → L ≤ lw.length →
      S.R (oreg .wr) = lw → S.R (oreg .dat) = binSyms lw.length d ++ rest →
      S.R (oreg .cr) = binSyms L x → symBit (v.scan (oreg .sm)) = cb →
      v.flag = lw.head?.isSome →
      ∃ v' S', v'.user = v.user ∧
        symBit (v'.scan (oreg .sm)) = (d + x + cb.toNat).testBit lw.length ∧
        Exec body (.loop (·.flag) (.act (addStep oreg))) (mk v S) (2 * lw.length + 1)
          (mk v' S') ∧
        S'.R (oreg .wr) = [] ∧ S'.R (oreg .ct) = lw.reverse ++ S.R (oreg .ct) ∧
        S'.R (oreg .dat) = rest ∧ S'.R (oreg .cr) = [] ∧
        S'.R (oreg .sm) = (binSyms lw.length (d + x + cb.toNat)).reverse ++ S.R (oreg .sm) ∧
        Fr oreg [.wr, .ct, .dat, .cr, .sm] S S' := by
  intro lw
  induction lw with
  | nil =>
      intro d x L cb rest v S hd hx hL hw hdat hcr hcb hf
      have hd0 : d = 0 := by simpa using hd
      have hL0 : L = 0 := by simpa using hL
      subst hL0
      have hx0 : x = 0 := by simpa using hx
      subst hd0 hx0
      refine ⟨v, S, rfl, by cases cb <;> simp [hcb], .loop_false (by simpa using hf), hw,
        by simp, by simpa [binSyms] using hdat, by simpa [binSyms] using hcr, by simp [binSyms],
        Fr.refl _ _ _⟩
  | cons e lw ih =>
      intro d x L cb rest v S hd hx hL hw hdat hcr hcb hf
      obtain ⟨hs0, hs1⟩ := full_adder d x cb
      have hrun := addStep_run hreg v S hw
      obtain ⟨hu₁, hf₁, hc₁⟩ := addStep_var hreg v S hw
      set v₁ := ((addStep oreg).run (mk v S)).var
      have hdat' : S.R (oreg .dat) =
          bitSymbol (d.testBit 0) :: (binSyms lw.length (d / 2) ++ rest) := by
        rw [hdat, List.length_cons, binSyms_succ, List.cons_append]
      have hdh : symBit ((S.R (oreg .dat)).head?.getD blank) = d.testBit 0 := by
        rw [hdat']; simp
      have hch : symBit ((S.R (oreg .cr)).head?.getD blank) = x.testBit 0 := by
        rw [hcr]; exact symBit_head_binSyms hx
      rw [hdh, hch, hcb] at hrun
      rw [hdh, hch, hcb] at hc₁
      set S₁ : Stacks T A := { S with
        R := Function.update (Function.update (Function.update (Function.update
          (Function.update S.R (oreg .wr) lw) (oreg .ct) (e :: S.R (oreg .ct)))
          (oreg .dat) (S.R (oreg .dat)).tail) (oreg .cr) (S.R (oreg .cr)).tail)
          (oreg .sm) (bitSymbol (fullSum (d.testBit 0) (x.testBit 0) cb) :: S.R (oreg .sm)) }
        with hS₁
      have hfr₁ : Fr oreg [.wr, .ct, .dat, .cr, .sm] S S₁ := by
        refine ⟨rfl, rfl, rfl, fun k hk => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hk
        simp [S₁, hk]
      obtain ⟨v', S', hu, hcarry, he, hw', hct', hdat'', hcr', hsm', hfr⟩ :=
        ih (d / 2) (x / 2) (L - 1) (fullCarry (d.testBit 0) (x.testBit 0) cb) rest v₁ S₁
          (by rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ]; simpa using hd)
          (div_two_lt hx) (by simp at hL; omega)
          (by simp [S₁, hreg.eq_iff])
          (by simp [S₁, hreg.eq_iff, hdat'])
          (by simp [S₁, hreg.eq_iff, hcr, tail_binSyms])
          hc₁ hf₁
      refine ⟨v', S', hu.trans hu₁, ?_, ?_, hw', ?_, hdat'', hcr', ?_, ?_⟩
      · rw [hcarry, List.length_cons, Nat.testBit_add_one, hs1]
      · refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
          (hrun ▸ Exec.act (body := body) (addStep oreg) (mk v S)) he) (by simp; ring) rfl
      · rw [hct']; simp [S₁, hreg.eq_iff]
      · rw [hsm', List.length_cons, binSyms_succ, hs0, ← hs1]
        simp [S₁]
      · exact hfr₁.trans hfr (by decide) (by decide)

/-! ### The emission loop -/

lemma emitStep_run (hreg : Function.Injective oreg) (v : HS T Q A U) (S : Stacks T A)
    {e : Fin (A + 4)} {lb : List (Fin (A + 4))} (hb : S.R (oreg .br) = e :: lb) :
    (emitStep oreg).run (mk v S) = mk ((emitStep oreg).run (mk v S)).var
      { S with
        R := Function.update (Function.update (Function.update
          (Function.update S.R (oreg .br) lb) (oreg .ct) (e :: S.R (oreg .ct)))
          (oreg .cr) (S.R (oreg .cr)).tail)
          (oreg .acc) (bitSymbol (symBit ((S.R (oreg .cr)).head?.getD blank)) ::
            S.R (oreg .acc)) } := by
  simp [emitStep, Action.run, peekR, update_rt, hb, hreg.eq_iff]

lemma emitStep_var (hreg : Function.Injective oreg) (v : HS T Q A U) (S : Stacks T A)
    {e : Fin (A + 4)} {lb : List (Fin (A + 4))} (hb : S.R (oreg .br) = e :: lb) :
    ((emitStep oreg).run (mk v S)).var.user = v.user ∧
    ((emitStep oreg).run (mk v S)).var.flag = lb.head?.isSome := by
  simp [emitStep, Action.run, peekR, update_rt, hb, hreg.eq_iff]

/-- The emission loop, by induction on the counter `lb`: the low `lb.length` bits of the
carry register `binSyms L y` move onto `acc`. -/
theorem emitStep_loop (hreg : Function.Injective oreg) :
    ∀ (lb : List (Fin (A + 4))) (y L : ℕ) (v : HS T Q A U) (S : Stacks T A),
      y < 2 ^ L → S.R (oreg .br) = lb → S.R (oreg .cr) = binSyms L y →
      v.flag = lb.head?.isSome →
      ∃ v' S', v'.user = v.user ∧
        Exec body (.loop (·.flag) (.act (emitStep oreg))) (mk v S) (2 * lb.length + 1)
          (mk v' S') ∧
        S'.R (oreg .br) = [] ∧ S'.R (oreg .ct) = lb.reverse ++ S.R (oreg .ct) ∧
        S'.R (oreg .cr) = binSyms (L - lb.length) (y / 2 ^ lb.length) ∧
        S'.R (oreg .acc) = ((binBits lb.length y).map bitSymbol).reverse ++ S.R (oreg .acc) ∧
        Fr oreg [.br, .ct, .cr, .acc] S S' := by
  intro lb
  induction lb with
  | nil =>
      intro y L v S _ hb hcr hf
      exact ⟨v, S, rfl, .loop_false (by simpa using hf), hb, by simp, by simpa using hcr,
        by simp, Fr.refl _ _ _⟩
  | cons e lb ih =>
      intro y L v S hy hb hcr hf
      have hrun := emitStep_run hreg v S hb
      obtain ⟨hu₁, hf₁⟩ := emitStep_var hreg v S hb
      set v₁ := ((emitStep oreg).run (mk v S)).var
      have hch : symBit ((S.R (oreg .cr)).head?.getD blank) = y.testBit 0 := by
        rw [hcr]; exact symBit_head_binSyms hy
      rw [hch] at hrun
      set S₁ : Stacks T A := { S with
        R := Function.update (Function.update (Function.update
          (Function.update S.R (oreg .br) lb) (oreg .ct) (e :: S.R (oreg .ct)))
          (oreg .cr) (S.R (oreg .cr)).tail)
          (oreg .acc) (bitSymbol (y.testBit 0) :: S.R (oreg .acc)) } with hS₁
      have hfr₁ : Fr oreg [.br, .ct, .cr, .acc] S S₁ := by
        refine ⟨rfl, rfl, rfl, fun k hk => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hk
        simp [S₁, hk]
      obtain ⟨v', S', hu, he, hb', hct', hcr', hacc', hfr⟩ :=
        ih (y / 2) (L - 1) v₁ S₁ (div_two_lt hy) (by simp [S₁, hreg.eq_iff])
          (by simp [S₁, hreg.eq_iff, hcr, tail_binSyms]) hf₁
      refine ⟨v', S', hu.trans hu₁, ?_, hb', ?_, ?_, ?_, hfr₁.trans hfr (by decide) (by decide)⟩
      · refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
          (hrun ▸ Exec.act (body := body) (emitStep oreg) (mk v S)) he) (by simp; ring) rfl
      · rw [hct']; simp [S₁, hreg.eq_iff]
      · rw [hcr', List.length_cons, Nat.div_div_eq_div_mul, ← pow_succ']
        congr 1; omega
      · rw [hacc', List.length_cons, binBits_succ]
        simp [S₁]

/-! ### Moving and clearing a register -/

/-- `moveR_exec` in the frame of the output registers. -/
theorem moveR_fr (hreg : Function.Injective oreg) {ri rj : OReg} (hij : ri ≠ rj)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' S', v'.user = v.user ∧
      Exec body (moveR (oreg ri) (oreg rj) id) (mk v S) (2 * (S.R (oreg ri)).length + 2)
        (mk v' S') ∧
      S'.R (oreg ri) = [] ∧ S'.R (oreg rj) = (S.R (oreg ri)).reverse ++ S.R (oreg rj) ∧
      Fr oreg [ri, rj] S S' := by
  obtain ⟨v', hu, he⟩ := moveR_exec body (oreg ri) (oreg rj) (hreg.ne hij) id v S
  refine ⟨v', _, hu, he, ?_, ?_, ⟨rfl, rfl, rfl, fun k hk => ?_⟩⟩
  · simp [movedR, hreg.eq_iff, hij]
  · simp [movedR]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hk
    simp [movedR, hk]

theorem clearStep_loop (i : Fin T) : ∀ (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
    S.R i = l → v.flag = l.head?.isSome →
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (.act (clearStep i))) (mk v S) (2 * l.length + 1)
        (mk v' { S with R := Function.update S.R i [] }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      rw [show ({ S with R := Function.update S.R i [] } : Stacks T A) = S by
        rw [← hS, Function.update_eq_self]]
      exact .loop_false (by simpa using hf)
  | cons e l ih =>
      intro v S hS hf
      set S₁ : Stacks T A := { S with R := Function.update S.R i l }
      have hrun : (clearStep i : Act T Q A U).run (mk v S) =
          mk { v with flag := l.head?.isSome } S₁ := by
        simp [clearStep, peekR, Action.run, hS, update_rt, S₁]
      obtain ⟨v', hu, he⟩ := ih { v with flag := l.head?.isSome } S₁ (by simp [S₁]) rfl
      refine ⟨v', hu, ?_⟩
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (clearStep i) (mk v S)) he) (by simp; ring) ?_
      simp [S₁]

theorem clearR_exec (i : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    ∃ v', v'.user = v.user ∧
      Exec body (clearR i) (mk v S) (2 * (S.R i).length + 2)
        (mk v' { S with R := Function.update S.R i [] }) := by
  obtain ⟨v', hu, he⟩ := clearStep_loop body i (S.R i) { v with flag := (S.R i).head?.isSome } S
    rfl rfl
  exact ⟨v', hu, Exec.cast (Exec.seq (peekR_run i v S ▸ Exec.act (body := body) (peekR i) (mk v S))
    he) (by ring) rfl⟩

/-! ### One word -/

lemma pushCarry_run (v : HS T Q A U) (S : Stacks T A) :
    (pushCarry oreg).run (mk v S) = mk v { S with
      R := Function.update S.R (oreg .sm)
        (bitSymbol (symBit (v.scan (oreg .sm))) :: S.R (oreg .sm)) } := by
  simp [pushCarry, Action.run, update_rt]

/-- One word `c < 2 ^ W` on top of `dat`, with the carry register `binSyms L x`: the low `b`
bits of `c + x` move onto `acc`, the carry register ends as `binSyms (W + 1 - b) ((c + x) / 2 ^ b)`,
the counters are restored, and `flag` tests for another word. -/
theorem wordIter_exec (hreg : Function.Injective oreg) {W b : ℕ}
    {lw lb : List (Fin (A + 4))} (hlw : lw.length = W) (hlb : lb.length = b)
    {c x L : ℕ} (hc : c < 2 ^ W) (hx : x < 2 ^ L) (hL : L ≤ W) (rest : List (Fin (A + 4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hdat : S.R (oreg .dat) = binSyms W c ++ rest) (hwr : S.R (oreg .wr) = lw)
    (hbr : S.R (oreg .br) = lb) (hct : S.R (oreg .ct) = []) (hsm : S.R (oreg .sm) = [])
    (hcr : S.R (oreg .cr) = binSyms L x) :
    ∃ v' S', v'.user = v.user ∧ v'.flag = rest.head?.isSome ∧
      Exec body (wordIter oreg) (mk v S) (6 * W + 4 * b + 14) (mk v' S') ∧
      S'.R (oreg .dat) = rest ∧ S'.R (oreg .wr) = lw ∧ S'.R (oreg .br) = lb ∧
      S'.R (oreg .ct) = [] ∧ S'.R (oreg .sm) = [] ∧
      S'.R (oreg .cr) = binSyms (W + 1 - b) ((c + x) / 2 ^ b) ∧
      S'.R (oreg .acc) = ((binBits b (c + x)).map bitSymbol).reverse ++ S.R (oreg .acc) ∧
      Fr oreg allRegs S S' := by
  subst hlw hlb
  -- start the carry bit at `0`
  set v₁ : HS T Q A U := { v with
    scan := Function.update v.scan (oreg .sm) (bitSymbol false)
    flag := (S.R (oreg .wr)).head?.isSome }
  have hrun₁ : (addInit oreg).run (mk v S) = mk v₁ S := rfl
  -- add the word to the carry register
  obtain ⟨v₂, S₂, hu₂, hc₂, he₂, hw₂, hct₂, hdat₂, hcr₂, hsm₂, hfr₂⟩ :=
    addStep_loop body hreg lw c x L false rest v₁ S hc hx hL hwr hdat hcr (by simp [v₁])
      (by simp [v₁, hwr])
  simp only [Bool.toNat_false, Nat.add_zero] at hc₂ hsm₂
  -- the top bit of the sum
  set S₃ : Stacks T A := { S₂ with
    R := Function.update S₂.R (oreg .sm)
      (bitSymbol (symBit (v₂.scan (oreg .sm))) :: S₂.R (oreg .sm)) }
  have hrun₃ : (pushCarry oreg).run (mk v₂ S₂) = mk v₂ S₃ := pushCarry_run v₂ S₂
  have hfr₃ : Fr oreg [.sm] S₂ S₃ := by
    refine ⟨rfl, rfl, rfl, fun k hk => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hk
    simp [S₃, hk]
  have hsm₃ : S₃.R (oreg .sm) = (binSyms (lw.length + 1) (c + x)).reverse := by
    simp [S₃, hsm₂, hc₂, hsm, binSyms_succ_last]
  have hct₃ : S₃.R (oreg .ct) = lw.reverse := by
    rw [hfr₃.get hreg .ct (by decide), hct₂, hct, List.append_nil]
  -- restore the word counter
  obtain ⟨v₄, S₄, hu₄, he₄, hct₄, hw₄, hfr₄⟩ :=
    moveR_fr body hreg (ri := .ct) (rj := .wr) (by decide) v₂ S₃
  -- the sum becomes the carry register, least significant bit on top
  obtain ⟨v₅, S₅, hu₅, he₅, hsm₅, hcr₅, hfr₅⟩ :=
    moveR_fr body hreg (ri := .sm) (rj := .cr) (by decide) v₄ S₄
  have hsm₄ : S₄.R (oreg .sm) = (binSyms (lw.length + 1) (c + x)).reverse := by
    rw [hfr₄.get hreg .sm (by decide), hsm₃]
  have hcr₅' : S₅.R (oreg .cr) = binSyms (lw.length + 1) (c + x) := by
    rw [hcr₅, hsm₄, hfr₄.get hreg .cr (by decide), hfr₃.get hreg .cr (by decide), hcr₂]; simp
  have hbr₅ : S₅.R (oreg .br) = lb := by
    rw [hfr₅.get hreg .br (by decide), hfr₄.get hreg .br (by decide),
      hfr₃.get hreg .br (by decide), hfr₂.get hreg .br (by decide), hbr]
  -- emit the low `b` bits
  set v₆ : HS T Q A U := { v₅ with flag := (S₅.R (oreg .br)).head?.isSome }
  have hrun₆ : (peekR (oreg .br) : Act T Q A U).run (mk v₅ S₅) = mk v₆ S₅ := rfl
  obtain ⟨v₇, S₇, hu₇, he₇, hb₇, hct₇, hcr₇, hacc₇, hfr₇⟩ :=
    emitStep_loop body hreg lb (c + x) (lw.length + 1) v₆ S₅ (word_sum_lt hc hx hL) hbr₅ hcr₅'
      (by simp [v₆, hbr₅])
  have hct₅ : S₅.R (oreg .ct) = [] := by
    rw [hfr₅.get hreg .ct (by decide), hct₄]
  -- restore the digit counter and test for another word
  obtain ⟨v₈, S₈, hu₈, he₈, hct₈, hb₈, hfr₈⟩ :=
    moveR_fr body hreg (ri := .ct) (rj := .br) (by decide) v₇ S₇
  set v₉ : HS T Q A U := { v₈ with flag := (S₈.R (oreg .dat)).head?.isSome }
  have hrun₉ : (peekR (oreg .dat) : Act T Q A U).run (mk v₈ S₈) = mk v₉ S₈ := rfl
  have hdat₈ : S₈.R (oreg .dat) = rest := by
    rw [hfr₈.get hreg .dat (by decide), hfr₇.get hreg .dat (by decide),
      hfr₅.get hreg .dat (by decide), hfr₄.get hreg .dat (by decide),
      hfr₃.get hreg .dat (by decide), hdat₂]
  have hl₃ : (S₃.R (oreg .ct)).length = lw.length := by simp [hct₃]
  have hl₄ : (S₄.R (oreg .sm)).length = lw.length + 1 := by simp [hsm₄]
  have hl₇ : (S₇.R (oreg .ct)).length = lb.length := by simp [hct₇, hct₅]
  refine ⟨v₉, S₈, ?_, by simp [v₉, hdat₈], ?_, hdat₈, ?_, ?_, hct₈, ?_, ?_, ?_, ?_⟩
  · simp only [v₉, v₆, v₁] at hu₂ hu₄ hu₅ hu₇ hu₈ ⊢
    rw [hu₈, hu₇, hu₅, hu₄, hu₂]
  · have := Exec.seq (hrun₁ ▸ Exec.act (body := body) (addInit oreg) (mk v S))
      (Exec.seq he₂ (Exec.seq (hrun₃ ▸ Exec.act (body := body) (pushCarry oreg) (mk v₂ S₂))
      (Exec.seq he₄ (Exec.seq he₅ (Exec.seq (hrun₆ ▸ Exec.act (body := body) (peekR (oreg .br))
        (mk v₅ S₅))
      (Exec.seq he₇ (Exec.seq he₈
        (hrun₉ ▸ Exec.act (body := body) (peekR (oreg .dat)) (mk v₈ S₈)))))))))
    refine Exec.cast this ?_ rfl
    rw [hl₃, hl₄, hl₇]; ring
  · rw [hfr₈.get hreg .wr (by decide), hfr₇.get hreg .wr (by decide),
      hfr₅.get hreg .wr (by decide), hw₄, hct₃, hfr₃.get hreg .wr (by decide), hw₂]; simp
  · rw [hb₈, hb₇]; simp [hct₇, hct₅]
  · rw [hfr₈.get hreg .sm (by decide), hfr₇.get hreg .sm (by decide), hsm₅]
  · rw [hfr₈.get hreg .cr (by decide), hcr₇]
  · rw [hfr₈.get hreg .acc (by decide), hacc₇, hfr₅.get hreg .acc (by decide),
      hfr₄.get hreg .acc (by decide), hfr₃.get hreg .acc (by decide),
      hfr₂.get hreg .acc (by decide)]
  · have f₃ : Fr oreg allRegs S S₃ := hfr₂.trans hfr₃ (by decide) (by decide)
    have f₄ : Fr oreg allRegs S S₄ := f₃.trans hfr₄ (by decide) (by decide)
    have f₅ : Fr oreg allRegs S S₅ := f₄.trans hfr₅ (by decide) (by decide)
    have f₇ : Fr oreg allRegs S S₇ := f₅.trans hfr₇ (by decide) (by decide)
    exact f₇.trans hfr₈ (by decide) (by decide)

/-! ### The word loop -/

/-- The word loop over the words `cs`, by induction on `cs`, from the carry register
`binSyms L x`. -/
theorem wordIter_loop (hreg : Function.Injective oreg) {W b : ℕ} (hb : 1 ≤ b) (hW : 1 ≤ W)
    {lw lb : List (Fin (A + 4))} (hlw : lw.length = W) (hlb : lb.length = b) :
    ∀ (cs : List ℕ) (x L : ℕ) (v : HS T Q A U) (S : Stacks T A),
      (∀ c ∈ cs, c < 2 ^ W) → x < 2 ^ L → L ≤ W →
      S.R (oreg .dat) = cs.flatMap (binSyms W) → S.R (oreg .wr) = lw → S.R (oreg .br) = lb →
      S.R (oreg .ct) = [] → S.R (oreg .sm) = [] → S.R (oreg .cr) = binSyms L x →
      v.flag = (S.R (oreg .dat)).head?.isSome →
      ∃ v' S', v'.user = v.user ∧
        Exec body (.loop (·.flag) (wordIter oreg)) (mk v S)
          (cs.length * (6 * W + 4 * b + 15) + 1) (mk v' S') ∧
        S'.R (oreg .dat) = [] ∧ S'.R (oreg .wr) = lw ∧ S'.R (oreg .br) = lb ∧
        S'.R (oreg .ct) = [] ∧ S'.R (oreg .sm) = [] ∧
        S'.R (oreg .cr) = binSyms (lenAfter W b cs L) (carryAfter b cs x) ∧
        S'.R (oreg .acc) = ((wordBits b cs x).map bitSymbol).reverse ++ S.R (oreg .acc) ∧
        Fr oreg allRegs S S' := by
  intro cs
  induction cs with
  | nil =>
      intro x L v S _ _ _ hdat hwr hbr hct hsm hcr hf
      refine ⟨v, S, rfl, Exec.cast (.loop_false (by simpa [hdat] using hf)) (by simp) rfl,
        by simpa using hdat, hwr, hbr, hct, hsm, by simpa [lenAfter, carryAfter] using hcr,
        by simp [wordBits], Fr.refl _ _ _⟩
  | cons c cs ih =>
      intro x L v S hcs hx hL hdat hwr hbr hct hsm hcr hf
      have hc := hcs c List.mem_cons_self
      have hdat' : S.R (oreg .dat) = binSyms W c ++ cs.flatMap (binSyms W) := by
        rw [hdat, List.flatMap_cons]
      have hft : v.flag = true := by
        rw [hf, hdat']
        cases W with
        | zero => omega
        | succ W => simp [binSyms_succ]
      obtain ⟨v₁, S₁, hu₁, hf₁, he₁, hdat₁, hw₁, hb₁, hct₁, hsm₁, hcr₁, hacc₁, hfr₁⟩ :=
        wordIter_exec body hreg hlw hlb hc hx hL _ v S hdat' hwr hbr hct hsm hcr
      obtain ⟨v₂, S₂, hu₂, he₂, hdat₂, hw₂, hb₂, hct₂, hsm₂, hcr₂, hacc₂, hfr₂⟩ :=
        ih ((c + x) / 2 ^ b) (W + 1 - b) v₁ S₁ (fun c' h => hcs c' (List.mem_cons_of_mem _ h))
          (word_carry_lt hc hx hL) (by omega) hdat₁ hw₁ hb₁ hct₁ hsm₁ hcr₁ (by rw [hf₁, hdat₁])
      refine ⟨v₂, S₂, hu₂.trans hu₁, ?_, hdat₂, hw₂, hb₂, hct₂, hsm₂, ?_, ?_,
        hfr₁.trans hfr₂ (by decide) (by decide)⟩
      · exact Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) hft he₁ he₂)
          (by simp; ring) rfl
      · rw [hcr₂, lenAfter_cons]; rfl
      · rw [hacc₂, hacc₁]; simp [wordBits]

/-! ### Leading zeroes and the output stack -/

/-- Popping the leading zero bits of a register holding `l.map bitSymbol`. -/
theorem dropZStep_loop (i : Fin T) : ∀ (l : List Bool) (v : HS T Q A U) (S : Stacks T A),
    S.R i = l.map bitSymbol → v.flag = isZero (S.R i).head? →
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (.act (dropZStep i))) (mk v S)
        (2 * (l.takeWhile (fun b => !b)).length + 1)
        (mk v' { S with
          R := Function.update S.R i ((l.dropWhile (fun b => !b)).map bitSymbol) }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          R := Function.update S.R i ((([] : List Bool).dropWhile (fun b => !b)).map bitSymbol) } :
            Stacks T A) = S := by
        simp only [List.dropWhile_nil, ← hS, Function.update_eq_self]
      rw [this]
      exact .loop_false (by simp [hf, hS, isZero])
  | cons b l ih =>
      intro v S hS hf
      cases b with
      | false =>
          set v₁ : HS T Q A U :=
            { v with flag := isZero (l.map bitSymbol).head? }
          set S₁ : Stacks T A := { S with R := Function.update S.R i (l.map bitSymbol) }
          have hrun : (dropZStep i : Act T Q A U).run (mk v S) = mk v₁ S₁ := by
            simp [dropZStep, peekZ, Action.run, hS, update_rt, v₁, S₁]
            rfl
          obtain ⟨v', hu, he⟩ := ih v₁ S₁ (by simp [S₁]) (by simp [v₁, S₁])
          refine ⟨v', hu, ?_⟩
          refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simp [hf, hS, isZero])
            (hrun ▸ Exec.act (body := body) (dropZStep i) (mk v S)) he) (by simp; ring) ?_
          simp [S₁]
      | true =>
          refine ⟨v, rfl, ?_⟩
          have : ({ S with
              R := Function.update S.R i (((true :: l).dropWhile (fun b => !b)).map bitSymbol) } :
                Stacks T A) = S := by
            rw [show ((true :: l).dropWhile (fun b => !b)).map bitSymbol = S.R i by simp [hS],
              Function.update_eq_self]
          rw [this]
          refine Exec.cast (.loop_false ?_) (by simp) rfl
          simp [hf, hS, isZero, bitSymbol]

/-- Moving the bits `l.map bitSymbol` of a register onto the output stack reverses them. -/
theorem outStep_loop (i : Fin T) : ∀ (l : List Bool) (v : HS T Q A U) (S : Stacks T A),
    S.R i = l.map bitSymbol → v.flag = l.head?.isSome →
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (.act (outStep i))) (mk v S) (2 * l.length + 1)
        (mk v' { S with
          out := l.reverse ++ S.out
          R := Function.update S.R i [] }) := by
  intro l
  induction l with
  | nil =>
      intro v S hS hf
      refine ⟨v, rfl, ?_⟩
      have : ({ S with
          out := ([] : List Bool).reverse ++ S.out
          R := Function.update S.R i [] } : Stacks T A) = S := by
        simp only [List.reverse_nil, List.nil_append]
        rw [show ([] : List (Fin (A + 4))) = S.R i by simp [hS], Function.update_eq_self]
      rw [this]
      exact .loop_false (by simpa using hf)
  | cons b l ih =>
      intro v S hS hf
      set v₁ : HS T Q A U := { v with sym := some (bitSymbol b), flag := l.head?.isSome }
      set S₁ : Stacks T A := { S with
        out := b :: S.out
        R := Function.update S.R i (l.map bitSymbol) }
      have hrun : (outStep i : Act T Q A U).run (mk v S) = mk v₁ S₁ := by
        simp [outStep, peekR, Action.run, hS, update_rt, update_out, v₁, S₁]
      obtain ⟨v', hu, he⟩ := ih v₁ S₁ (by simp [S₁]) rfl
      refine ⟨v', hu, ?_⟩
      refine Exec.cast (Exec.loop_true (body := body) (f := (·.flag)) (by simpa using hf)
        (hrun ▸ Exec.act (body := body) (outStep i) (mk v S)) he) (by simp; ring) ?_
      simp [S₁]

/-! ### The output stage -/

/-- The exact step count of `carryOut` on `n` words of `W` bits in base `2 ^ b`. -/
def carryOutCost (W b n : ℕ) : ℕ :=
  n * (6 * W + 6 * b + 15) + 4 * (if n = 0 then 0 else W + 1 - b) + 2 * W + 2 * b + 12

lemma carryOutCost_le {W b n : ℕ} (hb : 1 ≤ b) :
    carryOutCost W b n ≤ (n + 1) * (10 * W + 6 * b + 15) := by
  unfold carryOutCost
  split_ifs with hn
  · subst hn; omega
  · have h1 : W + 1 - b ≤ W := by omega
    have h2 : W ≤ n * W := Nat.le_mul_of_pos_left W (Nat.pos_of_ne_zero hn)
    nlinarith

/-- **The output stage.** Register `dat` holds the words `binSyms W c_i` of `cs` (word `0` on
top, `c_i < 2 ^ W`), `wr` and `br` hold `W ≥ 1` and `b ≥ 1` in unary, and `ct`, `cr`, `sm`, `acc`
are empty. `carryOut` pushes `encodingNatBool.encode (evalBase (2 ^ b) cs)` onto `out`, empties
`dat`, `wr` and `br`, and leaves every other stack and the `user` component unchanged, in exactly
`carryOutCost W b cs.length` steps. -/
theorem carryOut_exec (hreg : Function.Injective oreg) {W b : ℕ} (hb : 1 ≤ b) (hW : 1 ≤ W)
    {cs : List ℕ} (hcs : ∀ c ∈ cs, c < 2 ^ W) {lw lb : List (Fin (A + 4))}
    (hlw : lw.length = W) (hlb : lb.length = b) (v : HS T Q A U) (S : Stacks T A)
    (hdat : S.R (oreg .dat) = cs.flatMap (binSyms W)) (hwr : S.R (oreg .wr) = lw)
    (hbr : S.R (oreg .br) = lb) (hct : S.R (oreg .ct) = []) (hcr : S.R (oreg .cr) = [])
    (hsm : S.R (oreg .sm) = []) (hacc : S.R (oreg .acc) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (carryOut oreg) (mk v S) (carryOutCost W b cs.length)
        (mk v' { S with
          out := encodingNatBool.encode (evalBase (2 ^ b) cs) ++ S.out
          R := Function.update (Function.update (Function.update S.R
            (oreg .dat) []) (oreg .wr) []) (oreg .br) [] }) := by
  -- test for a first word
  set v₀ : HS T Q A U := { v with flag := (S.R (oreg .dat)).head?.isSome }
  have hrun₀ : (peekR (oreg .dat) : Act T Q A U).run (mk v S) = mk v₀ S := rfl
  -- the word loop
  obtain ⟨v₁, S₁, hu₁, he₁, hdat₁, hw₁, hb₁, hct₁, hsm₁, hcr₁, hacc₁, hfr₁⟩ :=
    wordIter_loop body hreg hb hW hlw hlb cs 0 0 v₀ S hcs (by simp) (Nat.zero_le _) hdat hwr hbr
      hct hsm (by simp [hcr, binSyms]) rfl
  -- the final carry joins the emitted bits
  obtain ⟨v₂, S₂, hu₂, he₂, hcr₂, hacc₂, hfr₂⟩ :=
    moveR_fr body hreg (ri := .cr) (rj := .acc) (by decide) v₁ S₁
  set E := outBits W b cs with hE
  have hacc₂' : S₂.R (oreg .acc) = E.reverse.map bitSymbol := by
    rw [hacc₂, hcr₁, hacc₁, hacc]
    simp [E, outBits, binSyms_eq, List.map_reverse]
  -- drop the leading zeroes
  set v₃ : HS T Q A U := { v₂ with flag := isZero (S₂.R (oreg .acc)).head? }
  have hrun₃ : (peekZ (oreg .acc) : Act T Q A U).run (mk v₂ S₂) = mk v₃ S₂ := rfl
  obtain ⟨v₄, hu₄, he₄⟩ := dropZStep_loop body (oreg .acc) E.reverse v₃ S₂ hacc₂' rfl
  set D := E.reverse.dropWhile (fun b => !b) with hD
  set S₄ : Stacks T A := { S₂ with R := Function.update S₂.R (oreg .acc) (D.map bitSymbol) }
  -- write the output
  set v₅ : HS T Q A U := { v₄ with flag := (S₄.R (oreg .acc)).head?.isSome }
  have hrun₅ : (peekR (oreg .acc) : Act T Q A U).run (mk v₄ S₄) = mk v₅ S₄ := rfl
  obtain ⟨v₆, hu₆, he₆⟩ :=
    outStep_loop body (oreg .acc) D v₅ S₄ (by simp [S₄]) (by simp [v₅, S₄])
  set S₆ : Stacks T A := { S₄ with
    out := D.reverse ++ S₄.out
    R := Function.update S₄.R (oreg .acc) [] }
  -- clear the counters
  obtain ⟨v₇, hu₇, he₇⟩ := clearR_exec body (oreg .wr) v₆ S₆
  set S₇ : Stacks T A := { S₆ with R := Function.update S₆.R (oreg .wr) [] }
  obtain ⟨v₈, hu₈, he₈⟩ := clearR_exec body (oreg .br) v₇ S₇
  refine ⟨v₈, ?_, ?_⟩
  · simp only [v₅, v₃, v₀] at hu₁ hu₂ hu₄ hu₆ hu₇ hu₈ ⊢
    rw [hu₈, hu₇, hu₆, hu₄, hu₂, hu₁]
  have := Exec.seq (hrun₀ ▸ Exec.act (body := body) (peekR (oreg .dat)) (mk v S))
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq (hrun₃ ▸ Exec.act (body := body) (peekZ (oreg .acc))
      (mk v₂ S₂)) (Exec.seq he₄ (Exec.seq (hrun₅ ▸ Exec.act (body := body) (peekR (oreg .acc))
      (mk v₄ S₄)) (Exec.seq he₆ (Exec.seq he₇ he₈)))))))
  refine Exec.cast this ?_ ?_
  · have hlen : (E.reverse.takeWhile (fun b => !b)).length + D.length = E.length := by
      rw [hD, ← List.length_append, List.takeWhile_append_dropWhile, List.length_reverse]
    have hE' : E.length = b * cs.length + lenAfter W b cs 0 := length_outBits W b cs
    have hcrl : (S₁.R (oreg .cr)).length = lenAfter W b cs 0 := by simp [hcr₁]
    have hla : lenAfter W b cs 0 = if cs.length = 0 then 0 else W + 1 - b := by
      simp [lenAfter, List.length_eq_zero_iff]
    have hwl : (S₆.R (oreg .wr)).length = W := by
      simp [S₆, S₄, hreg.eq_iff, hfr₂.get hreg .wr (by decide), hw₁, hlw]
    have hbl : (S₇.R (oreg .br)).length = b := by
      simp [S₇, S₆, S₄, hreg.eq_iff, hfr₂.get hreg .br (by decide), hb₁, hlb]
    rw [hcrl, hwl, hbl]
    unfold carryOutCost
    rw [← hla]
    nlinarith [hlen, hE']
  · have hval : D.reverse = encodingNatBool.encode (evalBase (2 ^ b) cs) := by
      show D.reverse = encodeNat (evalBase (2 ^ b) cs)
      rw [← lsbVal_outBits hb hcs, ← binaryValue_reverse, encodeNat_binaryValue]
    congr 1
    refine Stacks.ext ?_ ?_ ?_ ?_
    · simp [S₇, S₆, S₄, hfr₂.1, hfr₁.1]
    · simp [S₇, S₆, S₄, hval, hfr₂.2.1, hfr₁.2.1]
    · simp [S₇, S₆, S₄, hfr₂.2.2.1, hfr₁.2.2.1]
    · funext k
      simp only [S₇, S₆, S₄, Function.update_idem]
      by_cases hk : ∃ r, k = oreg r
      · obtain ⟨r, rfl⟩ := hk
        have hdat₂ : S₂.R (oreg .dat) = [] := by rw [hfr₂.get hreg .dat (by decide), hdat₁]
        have hct₂ : S₂.R (oreg .ct) = [] := by rw [hfr₂.get hreg .ct (by decide), hct₁]
        have hsm₂ : S₂.R (oreg .sm) = [] := by rw [hfr₂.get hreg .sm (by decide), hsm₁]
        cases r <;> simp [hreg.eq_iff, hdat₂, hct₂, hsm₂, hcr₂, hct, hcr,
          hsm, hacc]
      · simp only [not_exists] at hk
        have h1 : ∀ r ∈ allRegs, k ≠ oreg r := fun r _ => hk r
        rw [Function.update_of_ne (hk .br), Function.update_of_ne (hk .wr),
          Function.update_of_ne (hk .acc), Function.update_of_ne (hk .br),
          Function.update_of_ne (hk .wr), Function.update_of_ne (hk .dat),
          hfr₂.2.2.2 k (fun r _ => hk r), hfr₁.2.2.2 k h1]

end IntegerMultBounds.MathlibTM2.Fast
