module

public import IntegerMultBounds.MathlibTM2.Host.IndexRouteP
public import IntegerMultBounds.MathlibTM2.Node.RotPass
public import IntegerMultBounds.MathlibTM2.Layer.CompactXor

/-!
# The host pass of a rotation by a prepared offset

`rotGenPass prep neg ι st` rotates one field `tf` of the record index by an offset that depends
only on the fields above `tf`: the record at index `i` moves to index
`rotF len tf neg off i` (`IntegerMultBounds.MathlibTM2.Layer.CompactXor.rotF`), the field `tf`
being replaced by `(d ± off i) mod 2^W` for `W = len tf`. The offset is written into the
computed register `comp` by the preparation program `prep` before every code pass
(`Host.PrepSpec`); this file treats `prep` as a parameter.

**Codes.** The input class of a record is whether its rotation wraps around `2^W` (`wIn`), the
output class of an index is the input class of its preimage (`wOut`). Both are the carry or
borrow of the field digit and the offset register, computed by the two-input automata `carry2`
and `borrow2` reading registers `fld tf` and `comp` (`inCode2`, `outCode2`).

**Order.** The rotation fixes everything but field `tf`, adds one shift to the field value of
every index of one class, and keeps the index order within a class (`rotF_lt_of_lt`), so routing
by the input class and merging by the output class moves the records by the rotation
(`rotG_merge`, from `Host.mergeIdxList_perm`).

**Pass.** `routeIdxP prep` by input class onto `dst 0`, `dst 1`; `revEach`; `mergeIdxP prep` by
output class onto `out`; `moveR out src`. `rotGenPass_exec`: `src` ends holding
`(moveRecs (instrPerm len h) l).flatten` for the well-formed instruction `rot tf neg off`, every
other register ends as it started, in at most
`M * (2 cP + 2 idxStepCost B L len + 4 B + 4) + 13` steps, `M = R · 2^(∑ len)`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Layer.CompactXor

/-! ### Two-input carry and borrow automata -/

section Automata

variable (A : ℕ)

/-- The carry automaton of `x + y`, reading `x` in register `0` and `y` in register `1`. -/
def carry2 : CAuto A 2 2 where
  init := bitSymbol false
  step s x := bitSymbol ((x 0 && x 1) || ((x 0 || x 1) && symBit s))
  out s := rotCls (symBit s)

/-- The borrow automaton of `x - y`, with the registers of `carry2`. -/
def borrow2 : CAuto A 2 2 where
  init := bitSymbol false
  step s x := bitSymbol ((!x 0 && x 1) || ((!x 0 || x 1) && symBit s))
  out s := rotCls (symBit s)

lemma carry2_run : ∀ (L : ℕ) (cy : Bool) (vals : Fin 2 → ℕ),
    symBit ((carry2 A).run L (bitSymbol cy) vals) =
      decide (2 ^ L ≤ vals 0 % 2 ^ L + vals 1 % 2 ^ L + cy.toNat) := by
  intro L
  induction L with
  | zero => intro cy vals; cases cy <;> simp [CAuto.run, Nat.mod_one]
  | succ L ih =>
    intro cy vals
    have hstep : ∀ s x, (carry2 A).step s x =
        bitSymbol ((x 0 && x 1) || ((x 0 || x 1) && symBit s)) := fun _ _ => rfl
    rw [CAuto.run, hstep, ih]
    have h0 : vals 0 % 2 ^ (L + 1) = vals 0 % 2 + 2 * (vals 0 / 2 % 2 ^ L) := by
      rw [pow_succ', Nat.mod_mul]
    have h1 : vals 1 % 2 ^ (L + 1) = vals 1 % 2 + 2 * (vals 1 / 2 % 2 ^ L) := by
      rw [pow_succ', Nat.mod_mul]
    simp only [symBit_bitSymbol, h0, h1, Nat.testBit_zero]
    generalize vals 0 / 2 % 2 ^ L = y₀
    generalize vals 1 / 2 % 2 ^ L = y₁
    have hP : 2 ^ (L + 1) = 2 * 2 ^ L := pow_succ' 2 L
    rw [hP]
    rcases Nat.mod_two_eq_zero_or_one (vals 0) with h | h <;> rw [h] <;>
      rcases Nat.mod_two_eq_zero_or_one (vals 1) with h' | h' <;> rw [h'] <;>
      cases cy <;> simp <;> omega

lemma borrow2_run : ∀ (L : ℕ) (br : Bool) (vals : Fin 2 → ℕ),
    symBit ((borrow2 A).run L (bitSymbol br) vals) =
      decide (vals 0 % 2 ^ L < vals 1 % 2 ^ L + br.toNat) := by
  intro L
  induction L with
  | zero => intro br vals; cases br <;> simp [CAuto.run, Nat.mod_one]
  | succ L ih =>
    intro br vals
    have hstep : ∀ s x, (borrow2 A).step s x =
        bitSymbol ((!x 0 && x 1) || ((!x 0 || x 1) && symBit s)) := fun _ _ => rfl
    rw [CAuto.run, hstep, ih]
    have h0 : vals 0 % 2 ^ (L + 1) = vals 0 % 2 + 2 * (vals 0 / 2 % 2 ^ L) := by
      rw [pow_succ', Nat.mod_mul]
    have h1 : vals 1 % 2 ^ (L + 1) = vals 1 % 2 + 2 * (vals 1 / 2 % 2 ^ L) := by
      rw [pow_succ', Nat.mod_mul]
    simp only [symBit_bitSymbol, h0, h1, Nat.testBit_zero]
    generalize vals 0 / 2 % 2 ^ L = y₀
    generalize vals 1 / 2 % 2 ^ L = y₁
    rcases Nat.mod_two_eq_zero_or_one (vals 0) with h | h <;> rw [h] <;>
      rcases Nat.mod_two_eq_zero_or_one (vals 1) with h' | h' <;> rw [h'] <;>
      cases br <;> simp <;> omega

lemma carry2_eval (L : ℕ) (vals : Fin 2 → ℕ) :
    (carry2 A).eval L vals = rotCls (decide (2 ^ L ≤ vals 0 % 2 ^ L + vals 1 % 2 ^ L)) := by
  show rotCls (symBit ((carry2 A).run L (bitSymbol false) vals)) = _
  rw [carry2_run]
  simp

lemma borrow2_eval (L : ℕ) (vals : Fin 2 → ℕ) :
    (borrow2 A).eval L vals = rotCls (decide (vals 0 % 2 ^ L < vals 1 % 2 ^ L)) := by
  show rotCls (symBit ((borrow2 A).run L (bitSymbol false) vals)) = _
  rw [borrow2_run]
  simp

/-- The input code: the carry of `c + off` or the borrow of `c - off`. -/
def inCode2 (neg : Bool) : CAuto A 2 2 := if neg then borrow2 A else carry2 A

/-- The output code: the borrow of `c' - off` or the carry of `c' + off`. -/
def outCode2 (neg : Bool) : CAuto A 2 2 := if neg then carry2 A else borrow2 A

end Automata

/-! ### Wrap classes of a field rotation -/

section Wrap

/-- Input class of the field value `c` under `c ↦ c ± off` modulo `2^W`: the rotation wraps. -/
def wIn (W : ℕ) (neg : Bool) (off c : ℕ) : Bool :=
  if neg then decide (c < off) else decide (2 ^ W ≤ c + off)

/-- Output class of the field value `c'`: its preimage wraps. -/
def wOut (W : ℕ) (neg : Bool) (off c' : ℕ) : Bool :=
  if neg then decide (2 ^ W ≤ c' + off) else decide (c' < off)

/-- The shift of a rotation by `± off` on a value of wrap class `w`. -/
def shiftZ (W : ℕ) (neg : Bool) (off : ℕ) (w : Bool) : ℤ :=
  (if neg then -(off : ℤ) else off) + (if w then (if neg then 2 ^ W else -2 ^ W) else 0)

private lemma emod_of_bounds (x d k : ℤ) (h1 : 0 ≤ x - k * d) (h2 : x - k * d < d) :
    x % d = x - k * d := by
  have : x = (x - k * d) + d * k := by ring
  rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt h1 h2]
  ring

/-- A rotation by `± off` adds the shift of the wrap class. -/
lemma rotVal_eq_shift (W : ℕ) (neg : Bool) {off c : ℕ} (ho : off < 2 ^ W) (hc : c < 2 ^ W) :
    ((rotVal W neg off c : ℕ) : ℤ) = c + shiftZ W neg off (wIn W neg off c) := by
  have hc' : ((c : ℕ) : ℤ) < 2 ^ W := by exact_mod_cast hc
  have ho' : (off : ℤ) < 2 ^ W := by exact_mod_cast ho
  cases neg
  · rw [rotVal_false_cast]
    by_cases hw : 2 ^ W ≤ c + off
    · have hw' : (2 : ℤ) ^ W ≤ c + off := by exact_mod_cast hw
      simp only [wIn, shiftZ, Bool.false_eq_true, ite_false, hw, decide_true, ite_true]
      rw [emod_of_bounds _ _ 1 (by linarith) (by linarith)]
      ring
    · have hw' : ((c : ℕ) : ℤ) + off < 2 ^ W := by exact_mod_cast not_le.mp hw
      simp only [wIn, shiftZ, Bool.false_eq_true, ite_false, hw, decide_false]
      rw [emod_of_bounds _ _ 0 (by simp; positivity) (by linarith)]
      ring
  · rw [rotVal_true_cast _ ho]
    by_cases hw : c < off
    · have hw' : ((c : ℕ) : ℤ) < off := by exact_mod_cast hw
      simp only [wIn, shiftZ, ite_true, hw, decide_true]
      rw [emod_of_bounds _ _ (-1) (by linarith) (by linarith)]
      ring
    · have hw' : (off : ℤ) ≤ (c : ℕ) := by exact_mod_cast not_lt.mp hw
      simp only [wIn, shiftZ, ite_true, hw, decide_false, Bool.false_eq_true, ite_false]
      rw [emod_of_bounds _ _ 0 (by linarith) (by linarith)]
      ring

/-- The output class of a rotated value is the input class of the value. -/
lemma wOut_rotVal (W : ℕ) (neg : Bool) {off c : ℕ} (ho : off < 2 ^ W) (hc : c < 2 ^ W) :
    wOut W neg off (rotVal W neg off c) = wIn W neg off c := by
  have h := rotVal_eq_shift W neg ho hc
  have hr := rotVal_lt W neg off c
  generalize rotVal W neg off c = r at h hr ⊢
  have hP : ((2 : ℤ) ^ W) = ((2 ^ W : ℕ) : ℤ) := by push_cast; rfl
  cases neg <;> cases hw : wIn W _ off c <;>
    simp only [wIn, Bool.false_eq_true, ite_false, ite_true, decide_eq_true_eq,
      decide_eq_false_iff_not] at hw <;>
    simp only [shiftZ, hw, Bool.false_eq_true, ite_false, ite_true, wOut, decide_eq_true_eq,
      decide_eq_false_iff_not, hP] at h ⊢ <;> omega

/-- Within one wrap class the rotation is increasing. -/
lemma rotVal_lt_of_lt (W : ℕ) (neg : Bool) {off c c' : ℕ} (ho : off < 2 ^ W) (hc : c < 2 ^ W)
    (hc' : c' < 2 ^ W) (hw : wIn W neg off c = wIn W neg off c') (hlt : c < c') :
    rotVal W neg off c < rotVal W neg off c' := by
  have h1 := rotVal_eq_shift W neg ho hc
  have h2 := rotVal_eq_shift W neg ho hc'
  rw [hw] at h1
  have : ((rotVal W neg off c : ℕ) : ℤ) < ((rotVal W neg off c' : ℕ) : ℤ) := by
    rw [h1, h2]
    have : ((c : ℕ) : ℤ) < c' := by exact_mod_cast hlt
    linarith
  exact_mod_cast this

end Wrap

/-! ### The rotation on record indices -/

section Index

variable {nf : ℕ} (len : Fin nf → ℕ) (tf : Fin nf)

/-- An offset that depends only on the fields above `tf`. -/
def HighOff (off : ℕ → ℕ) : Prop :=
  ∀ i j, i / 2 ^ (foff len tf + len tf) = j / 2 ^ (foff len tf + len tf) → off i = off j

lemma HighOff.ignores {off : ℕ → ℕ} (h : HighOff len tf off) : IgnoresF len tf off :=
  fun i v hv => h _ _ (setDig_div len tf i hv le_rfl)

lemma HighOff.rotF {off : ℕ → ℕ} (h : HighOff len tf off) (neg : Bool) (i : ℕ) :
    off (rotF len tf neg off i) = off i :=
  HighOff.ignores len tf h i _ (rotVal_lt _ _ _ _)

lemma rotF_div_top (neg : Bool) (off : ℕ → ℕ) (i : ℕ) :
    rotF len tf neg off i / 2 ^ (foff len tf + len tf) = i / 2 ^ (foff len tf + len tf) :=
  setDig_div len tf i (rotVal_lt _ _ _ _) le_rfl

lemma setDig_div_lo (i v : ℕ) :
    setDig len tf i v / 2 ^ foff len tf = v + 2 ^ len tf * (i / 2 ^ (foff len tf + len tf)) := by
  unfold setDig
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity)),
    Nat.zero_add]

lemma setDig_mod_lo (i v : ℕ) : setDig len tf i v % 2 ^ foff len tf = i % 2 ^ foff len tf := by
  unfold setDig
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt _ (by positivity))]

/-- **Order within a class.** -/
lemma rotF_lt_of_lt (neg : Bool) {off : ℕ → ℕ} (hoff : HighOff len tf off)
    (hob : ∀ i, off i < 2 ^ len tf) {i i' : ℕ} (hlt : i < i')
    (hw : wIn (len tf) neg (off i) (dig len tf i) = wIn (len tf) neg (off i') (dig len tf i')) :
    rotF len tf neg off i < rotF len tf neg off i' := by
  set o := foff len tf with ho
  set W := len tf with hW
  have hP : 0 < 2 ^ o := by positivity
  have hPQ : 0 < 2 ^ (o + W) := by positivity
  have hhi : i / 2 ^ (o + W) ≤ i' / 2 ^ (o + W) := Nat.div_le_div_right hlt.le
  rcases Nat.lt_or_eq_of_le hhi with hhi | hhi
  · apply Nat.lt_of_div_lt_div (c := 2 ^ (o + W))
    rw [rotF_div_top, rotF_div_top]
    exact hhi
  · have hoff' : off i = off i' := hoff i i' hhi
    have hmid : i / 2 ^ o ≤ i' / 2 ^ o := Nat.div_le_div_right hlt.le
    have hdi : i / 2 ^ o = dig len tf i + 2 ^ W * (i / 2 ^ (o + W)) := by
      unfold dig
      rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mod_add_div]
    have hdi' : i' / 2 ^ o = dig len tf i' + 2 ^ W * (i' / 2 ^ (o + W)) := by
      unfold dig
      rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mod_add_div]
    have hdle : dig len tf i ≤ dig len tf i' := by
      rw [hdi, hdi', hhi] at hmid
      omega
    have hlo : rotF len tf neg off i / 2 ^ o =
        rotVal W neg (off i) (dig len tf i) + 2 ^ W * (i / 2 ^ (o + W)) :=
      setDig_div_lo len tf i _
    have hlo' : rotF len tf neg off i' / 2 ^ o =
        rotVal W neg (off i') (dig len tf i') + 2 ^ W * (i' / 2 ^ (o + W)) :=
      setDig_div_lo len tf i' _
    rcases Nat.lt_or_eq_of_le hdle with hdlt | hdeq
    · apply Nat.lt_of_div_lt_div (c := 2 ^ o)
      rw [hlo, hlo', hhi, ← hoff']
      have := rotVal_lt_of_lt W neg (hob i) (dig_lt len tf i) (dig_lt len tf i')
        (by rw [hw, hoff']) hdlt
      omega
    · -- equal digits and high parts: the low parts decide
      have hdiv : rotF len tf neg off i / 2 ^ o = rotF len tf neg off i' / 2 ^ o := by
        rw [hlo, hlo', hhi, hoff', hdeq]
      have hmod : rotF len tf neg off i % 2 ^ o < rotF len tf neg off i' % 2 ^ o := by
        rw [rotF, setDig_mod_lo, rotF, setDig_mod_lo, ← ho]
        have hq : i / 2 ^ o = i' / 2 ^ o := by rw [hdi, hdi', hhi, hdeq]
        have e1 := Nat.mod_def i (2 ^ o)
        have e2 := Nat.mod_def i' (2 ^ o)
        have h3 : 2 ^ o * (i / 2 ^ o) ≤ i := Nat.mul_div_le i (2 ^ o)
        rw [hq] at e1 h3
        omega
      have e1 := Nat.div_add_mod (rotF len tf neg off i) (2 ^ o)
      have e2 := Nat.div_add_mod (rotF len tf neg off i') (2 ^ o)
      rw [hdiv] at e1
      omega

end Index

/-! ### Codes of the rotation -/

section Codes

variable {A nf : ℕ} (len : Fin nf → ℕ) (tf : Fin nf) (off : ℕ → ℕ)

/-- The code-pass sources: the field `tf` and the computed offset register. -/
def rsrcR : Fin 2 → Fin nf ⊕ (ℕ → ℕ) := ![.inl tf, .inr off]

lemma dig_eq_digit (f : Fin nf) (i : ℕ) : dig len f i = digit len f i := rfl

lemma regValP_rsrcR (i : ℕ) : regValP len (rsrcR tf off) i = ![dig len tf i, off i] := by
  funext r
  fin_cases r <;> simp [regValP, rsrcR, dig_eq_digit]

lemma inCode2_idx (neg : Bool) (hob : ∀ i, off i < 2 ^ len tf) (i : ℕ) :
    idxCodeP (inCode2 A neg) (len tf) len (rsrcR tf off) i =
      rotCls (wIn (len tf) neg (off i) (dig len tf i)) := by
  unfold idxCodeP
  rw [regValP_rsrcR]
  cases neg
  · simp [inCode2, wIn, carry2_eval, Nat.mod_eq_of_lt (dig_lt len tf i), Nat.mod_eq_of_lt (hob i)]
  · simp [inCode2, wIn, borrow2_eval, Nat.mod_eq_of_lt (dig_lt len tf i),
      Nat.mod_eq_of_lt (hob i)]

lemma outCode2_idx (neg : Bool) (hob : ∀ i, off i < 2 ^ len tf) (i : ℕ) :
    idxCodeP (outCode2 A neg) (len tf) len (rsrcR tf off) i =
      rotCls (wOut (len tf) neg (off i) (dig len tf i)) := by
  unfold idxCodeP
  rw [regValP_rsrcR]
  cases neg
  · simp [outCode2, wOut, borrow2_eval, Nat.mod_eq_of_lt (dig_lt len tf i),
      Nat.mod_eq_of_lt (hob i)]
  · simp [outCode2, wOut, carry2_eval, Nat.mod_eq_of_lt (dig_lt len tf i),
      Nat.mod_eq_of_lt (hob i)]

end Codes

/-! ### Records -/

section Lists

variable {α : Type}

/-- A permutation of `Fin M` as a map of `ℕ`, the identity from `M` on. -/
def permFun {M : ℕ} (π : Equiv.Perm (Fin M)) (i : ℕ) : ℕ := if h : i < M then π ⟨i, h⟩ else i

lemma permFun_of_lt {M : ℕ} (π : Equiv.Perm (Fin M)) {i : ℕ} (h : i < M) :
    permFun π i = π ⟨i, h⟩ := by simp [permFun, h]

lemma permFun_lt {M : ℕ} (π : Equiv.Perm (Fin M)) {i : ℕ} (h : i < M) : permFun π i < M := by
  rw [permFun_of_lt π h]; exact (π _).isLt

lemma permFun_symm {M : ℕ} (π : Equiv.Perm (Fin M)) {i : ℕ} (h : i < M) :
    permFun π.symm (permFun π i) = i := by
  rw [permFun_of_lt π h, permFun_of_lt π.symm (π _).isLt]
  simp

lemma permFun_symm' {M : ℕ} (π : Equiv.Perm (Fin M)) {i : ℕ} (h : i < M) :
    permFun π (permFun π.symm i) = i := by
  have := permFun_symm π.symm h
  rwa [Equiv.symm_symm] at this

lemma length_flatten_of {B : ℕ} : ∀ (l : List (List α)), (∀ r ∈ l, r.length = B) →
    l.flatten.length = l.length * B
  | [], _ => by simp
  | r :: l, h => by
    rw [List.flatten_cons, List.length_append, h r List.mem_cons_self,
      length_flatten_of l (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')), List.length_cons]
    ring

lemma blk_flatten {B : ℕ} : ∀ (l : List (List α)), (∀ r ∈ l, r.length = B) →
    ∀ k, blk l.flatten B k = l.getD k []
  | [], _, k => by simp [blk]
  | r :: l, h, k => by
    have hr := h r List.mem_cons_self
    cases k with
    | zero => simp [blk, List.take_left' hr]
    | succ k =>
      have := blk_flatten l (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) k
      rw [List.getD_cons_succ, ← this, List.flatten_cons]
      simp only [blk]
      rw [List.drop_append, List.drop_eq_nil_of_le (by rw [hr]; nlinarith),
        List.nil_append, hr, show (k + 1) * B - B = k * B by rw [Nat.add_one_mul]; omega]

lemma flatten_moveRecs {M B : ℕ} (π : Equiv.Perm (Fin M)) (l : List (List α))
    (hl : ∀ r ∈ l, r.length = B) :
    (moveRecs π l).flatten =
      (List.range M).flatMap (fun j => blk l.flatten B (permFun π.symm j)) := by
  rw [List.flatMap_def]
  congr 1
  apply List.ext_getElem (by simp [length_moveRecs])
  intro j h1 h2
  have hj : j < M := by simpa using h2
  simp [moveRecs, permFun_of_lt _ hj, blk_flatten l hl]

lemma length_flatten_moveRecs {M B : ℕ} (π : Equiv.Perm (Fin M)) (l : List (List α))
    (hl : l.length = M) (hlB : ∀ r ∈ l, r.length = B) :
    (moveRecs π l).flatten.length = M * B := by
  rw [length_flatten_of _ (B := B), length_moveRecs]
  intro r hr
  simp only [moveRecs, List.mem_ofFn] at hr
  obtain ⟨j, rfl⟩ := hr
  apply hlB
  have hk : (π.symm j : ℕ) < l.length := by rw [hl]; exact (π.symm j).isLt
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

/-- A code-matching bijection preserves the count of each code. -/
lemma idxCount_eq_of_perm {nd M : ℕ} (cin cout : ℕ → Fin nd) (π σ : ℕ → ℕ)
    (hπ : ∀ i < M, π i < M) (hσ : ∀ j < M, σ j < M) (hσπ : ∀ i < M, σ (π i) = i)
    (hπσ : ∀ j < M, π (σ j) = j) (hcode : ∀ i < M, cout (0 + π i) = cin (0 + i)) (d : Fin nd) :
    idxCount cout 0 M d = idxCount cin 0 M d := by
  unfold idxCount
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  have hperm : ((List.range M).map π).Perm (List.range M) := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_range.map_on ?_) List.nodup_range]
    · intro a
      simp only [List.mem_map, List.mem_range]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hπ x hx
      · intro ha; exact ⟨σ a, hσ a ha, hπσ a ha⟩
    · intro x hx y hy hxy
      rw [List.mem_range] at hx hy
      rw [← hσπ x hx, ← hσπ y hy, hxy]
  rw [← hperm.countP_eq, List.countP_map]
  apply List.countP_congr
  intro x hx
  rw [List.mem_range] at hx
  have h := hcode x hx
  simp only [Nat.zero_add] at h
  simp [h]

lemma idxCount_sum {nd : ℕ} (code : ℕ → Fin nd) :
    ∀ (m j : ℕ), ∑ d, idxCount code j m d = m := by
  intro m
  induction m with
  | zero => intro j; simp [idxCount]
  | succ m ih =>
    intro j
    simp only [idxCount_succ, Finset.sum_add_distrib, ih]
    rw [Finset.sum_ite_eq]
    simp [Nat.add_comm]

end Lists

/-! ### The rotation as a merge -/

section Merge

variable {A nf : ℕ} (len : Fin nf → ℕ) (tf : Fin nf) (neg : Bool) {off : ℕ → ℕ} {R : ℕ}

/-- The instruction `rot tf neg off` is well formed below `∑ len` for a high offset. -/
lemma rot_WF (hoff : HighOff len tf off) :
    (CInstr.rot tf neg off).WF len (∑ g, len g) :=
  ⟨HighOff.ignores len tf hoff, foff_add_len_le_sum len tf⟩

/-- The rotation as a permutation of the indices below `R · 2^(∑ len)`. -/
abbrev rotPerm (R : ℕ) (hoff : HighOff len tf off) : Equiv.Perm (Fin (R * 2 ^ ∑ g, len g)) :=
  Layer.CompactXor.instrPerm len (R := R) (rot_WF len tf neg hoff)

variable (hoff : HighOff len tf off) (hob : ∀ i, off i < 2 ^ len tf)
include hoff hob

/-- Index `i < M` moves to `rotF len tf neg off i`. -/
lemma permFun_rot {i : ℕ} (h : i < R * 2 ^ ∑ g, len g) :
    permFun (rotPerm len tf neg R hoff) i = rotF len tf neg off i := by
  rw [permFun_of_lt _ h, rotPerm, Layer.CompactXor.instrPerm_apply]
  rfl

/-- Every record moves to an output index whose output code is its input code. -/
theorem rotG_code : ∀ i < R * 2 ^ ∑ g, len g,
    idxCodeP (outCode2 A neg) (len tf) len (rsrcR tf off)
        (0 + permFun (rotPerm len tf neg R hoff) i) =
      idxCodeP (inCode2 A neg) (len tf) len (rsrcR tf off) (0 + i) := by
  intro i hi
  rw [Nat.zero_add, Nat.zero_add, permFun_rot len tf neg hoff hob hi, outCode2_idx len tf off neg hob,
    inCode2_idx len tf off neg hob, HighOff.rotF len tf hoff, dig_rotF,
    wOut_rotVal _ _ (hob i) (dig_lt len tf i)]

/-- Records of one input class keep their order. -/
theorem rotG_mono : ∀ i < R * 2 ^ ∑ g, len g, ∀ i' < R * 2 ^ ∑ g, len g,
    idxCodeP (inCode2 A neg) (len tf) len (rsrcR tf off) (0 + i) =
      idxCodeP (inCode2 A neg) (len tf) len (rsrcR tf off) (0 + i') →
    i < i' → permFun (rotPerm len tf neg R hoff) i <
      permFun (rotPerm len tf neg R hoff) i' := by
  intro i hi i' hi' hc hlt
  rw [Nat.zero_add, Nat.zero_add, inCode2_idx len tf off neg hob, inCode2_idx len tf off neg hob,
    rotCls_inj] at hc
  rw [permFun_rot len tf neg hoff hob hi, permFun_rot len tf neg hoff hob hi']
  exact rotF_lt_of_lt len tf neg hoff hob hlt hc

/-- Each output class has as many indices as the input class. -/
theorem rotG_count (d : Fin 2) :
    idxCount (idxCodeP (outCode2 A neg) (len tf) len (rsrcR tf off)) 0 (R * 2 ^ ∑ g, len g) d =
      idxCount (idxCodeP (inCode2 A neg) (len tf) len (rsrcR tf off)) 0 (R * 2 ^ ∑ g, len g) d :=
  idxCount_eq_of_perm _ _ _ _ (fun _ h => permFun_lt _ h) (fun _ h => permFun_lt _ h)
    (fun _ h => permFun_symm _ h) (fun _ h => permFun_symm' _ h)
    (rotG_code (A := A) len tf neg hoff hob) d

/-- **List semantics of the pass.** -/
theorem rotG_merge {B : ℕ} (l : List (List (Fin (A + 4)))) (hl : l.length = R * 2 ^ ∑ g, len g)
    (hlB : ∀ r ∈ l, r.length = B) :
    mergeIdxList B (idxCodeP (outCode2 A neg) (len tf) len (rsrcR tf off))
        (R * 2 ^ ∑ g, len g) 0 (fun d => blocksIdx l.flatten B (R * 2 ^ ∑ g, len g)
          (idxCodeP (inCode2 A neg) (len tf) len (rsrcR tf off)) 0 d ++ []) =
      ((moveRecs (rotPerm len tf neg R hoff) l).flatten, fun _ => []) := by
  rw [mergeIdxList_perm B _ l.flatten (by rw [length_flatten_of l hlB, hl]) _ _ 0 0 _ _
    (fun _ h => permFun_lt _ h) (fun _ h => permFun_lt _ h) (fun _ h => permFun_symm _ h)
    (fun _ h => permFun_symm' _ h) (rotG_code (A := A) len tf neg hoff hob)
    (rotG_mono (A := A) len tf neg hoff hob), flatten_moveRecs _ l hlB]

end Merge

/-! ### The machine -/

/-- The registers of the pass: the stream and its two routing banks, the counters, the fields,
the computed offset register, the code-pass spares and the scratch of the preparation. -/
inductive RotGReg (nf ns np : ℕ) where
  | src | ctr | tmp | cnt | ctmp | out
  | dst (d : Fin 2) | aux (d : Fin 2)
  | fld (g : Fin nf) | comp | spare (r : Fin 2) | scr (s : Fin ns) | prm (q : Fin np)
  deriving DecidableEq

namespace RotGReg

variable {nf ns np : ℕ}

/-- The index registers: fields, the computed register, the spares, the scratch and the
parameter registers of the preparation. -/
def isIdx : RotGReg nf ns np → Bool
  | .fld _ | .comp | .spare _ | .scr _ | .prm _ => true
  | _ => false

/-- The code-pass registers: the field `tf` and the computed register. -/
def rsRegG (tf : Fin nf) : Fin 2 → RotGReg nf ns np := ![.fld tf, .comp]

lemma rsRegG_isIdx (tf : Fin nf) (r : Fin 2) : (rsRegG (ns := ns) (np := np) tf r).isIdx = true := by
  fin_cases r <;> rfl

lemma rsRegG_injective (tf : Fin nf) : Function.Injective (rsRegG (ns := ns) (np := np) tf) := by
  intro r r' h
  fin_cases r <;> fin_cases r' <;> simp_all [rsRegG]

end RotGReg

section Machine

variable {T Q A : ℕ} {U : Type} {P : Type} {nf ns np : ℕ} (body : P → Pr P T Q A U)

open RotGReg

/-- The index layout of the pass beside any set `X` of non-index registers. -/
lemma rotG_idxLayout {ι : RotGReg nf ns np → Fin T} (hι : Function.Injective ι) {st : Fin T}
    (hst : ∀ x, x.isIdx = true → ι x ≠ st) (len : Fin nf → ℕ) (tf : Fin nf) (off : ℕ → ℕ)
    {X : Fin T → Prop} (hX : ∀ x, X (ι x) → x.isIdx = false) :
    IdxLayoutP (fun g => ι (.fld g)) len (len tf) (fun r => ι (rsRegG tf r))
      (fun r => ι (.spare r)) (rsrcR tf off) (fun s => ι (.scr s)) (fun q => ι (.prm q)) st X where
  rs_inj := hι.comp (rsRegG_injective tf)
  tmps_inj := fun r r' h => by simpa using hι h
  rs_tmps := fun r r' h => by
    have := hι h
    fin_cases r <;> simp [rsRegG] at this
  rs_st := fun r => hst _ (rsRegG_isIdx tf r)
  tmps_st := fun r => hst _ rfl
  cf_inj := fun g g' h => by simpa using hι h
  tmps_cf := fun r g h => by simpa using hι h
  field := fun r g h => by
    fin_cases r <;> simp [rsrcR] at h <;> subst h <;> exact ⟨rfl, rfl⟩
  param := fun r g f h e => by
    have := hι e
    fin_cases r <;> simp [rsrcR, rsRegG] at h this
  scr_cf := fun s f h => by simpa using hι h
  scr_rs := fun s r h => by
    have := hι h
    fin_cases r <;> simp [rsRegG] at this
  prm_cf := fun q f h => by simpa using hι h
  prm_rs := fun q r h => by
    have := hι h
    fin_cases r <;> simp [rsRegG] at this
  prm_X := fun q h => by simpa [RotGReg.isIdx] using hX _ h
  cf_X := fun g h => by simpa [RotGReg.isIdx] using hX _ h
  rs_X := fun r h => by
    have := hX _ h
    rw [rsRegG_isIdx] at this
    exact Bool.noConfusion this
  tmps_X := fun r h => by simpa [RotGReg.isIdx] using hX _ h
  scr_X := fun s h => by simpa [RotGReg.isIdx] using hX _ h

/-- The index state at index `0`. -/
lemma rotG_idxState {ι : RotGReg nf ns np → Fin T} (len : Fin nf → ℕ) (tf : Fin nf) (off : ℕ → ℕ)
    (P₀ : Fin np → List (Fin (A + 4))) (R : Fin T → List (Fin (A + 4)))
    (hf : ∀ g, R (ι (.fld g)) = binSyms (len g) 0)
    (hc : (R (ι .comp)).length = len tf) (hs : ∀ r, R (ι (.spare r)) = [])
    (hz : ∀ s, R (ι (.scr s)) = []) (hp : ∀ q, R (ι (.prm q)) = P₀ q) :
    IdxStateP (fun g => ι (.fld g)) len (len tf) (fun r => ι (rsRegG tf r))
      (fun r => ι (.spare r)) (rsrcR tf off) (fun s => ι (.scr s)) (fun q => ι (.prm q)) P₀ R 0 := by
  refine ⟨fun g => by simp [digit, hf], fun r g h => ?_, hs, hz, hp⟩
  fin_cases r <;> simp [rsrcR] at h
  exact hc

/-- The counter wraps after `M = R · 2^(∑ len)` records. -/
lemma digit_wrap (len : Fin nf → ℕ) (R : ℕ) (g : Fin nf) :
    digit len g (0 + R * 2 ^ ∑ f, len f) = 0 := by
  rw [Nat.zero_add, ← digit_mod, Nat.mul_mod_left]
  simp [digit]

/-- **The pass.** Route the records of `src` by input class onto `dst 0`, `dst 1`; reverse each
onto `aux d`; merge them by output class onto `out`; move `out` back onto `src`. -/
def rotGenPass (prep : Pr P T Q A U) (tf : Fin nf) (neg : Bool) (ι : RotGReg nf ns np → Fin T)
    (st : Fin T) : Pr P T Q A U :=
  .seq (routeIdxP prep (ι .src) (fun d => ι (.dst d)) (ι .ctr) (ι .tmp) (fun g => ι (.fld g))
      (fun r => ι (rsRegG tf r)) (fun r => ι (.spare r)) st (inCode2 A neg))
    (.seq (revEach (fun d => ι (.dst d)) (fun d => ι (.aux d)))
      (.seq (mergeIdxP prep (fun d => ι (.aux d)) (ι .out) (ι .ctr) (ι .tmp) (ι .cnt) (ι .ctmp)
          (fun g => ι (.fld g)) (fun r => ι (rsRegG tf r)) (fun r => ι (.spare r)) st
          (outCode2 A neg))
        (moveR (ι .out) (ι .src) id)))

/-- **The rotation pass.** Register `src` holds `l.flatten` for `M = R · 2^(∑ len)` records of
`B ≥ 1` symbols in index order; `ctr` holds `B` symbols and `cnt` holds `M`; the counter fields
hold zero, `comp` holds `len tf` symbols, and `tmp`, `ctmp`, `out`, `dst d`, `aux d`, the spares
and the scratch are empty. The offset `off` depends only on the fields above `tf` and is below
`2^(len tf)`, and `prep` meets `PrepSpec` with cost `cP`. Then `rotGenPass prep tf neg` leaves
`(moveRecs (instrPerm len (rot_WF len tf neg hoff)) l).flatten` on `src`; every other register
ends as it started, except that `comp` holds `len tf` symbols, and `user` is kept. At most
`M * (2 cP + 2 idxStepCost B (len tf) len + 4 B + 4) + 13` steps. -/
theorem rotGenPass_exec {prep : Pr P T Q A U} (tf : Fin nf) (neg : Bool)
    {ι : RotGReg nf ns np → Fin T} (hι : Function.Injective ι) {st : Fin T}
    (hst : ∀ x, x.isIdx = true → ι x ≠ st) (len : Fin nf → ℕ) {off : ℕ → ℕ}
    (hoff : HighOff len tf off) (hob : ∀ i, off i < 2 ^ len tf) {cP : ℕ}
    {P₀ : Fin np → List (Fin (A + 4))}
    (hprep : PrepSpec body prep (fun g => ι (.fld g)) len (len tf) (fun r => ι (rsRegG tf r))
      (fun r => ι (.spare r)) (rsrcR tf off) (fun s => ι (.scr s)) (fun q => ι (.prm q)) P₀ cP)
    {R B : ℕ} (hB : 1 ≤ B) {l : List (List (Fin (A + 4)))} (hl : l.length = R * 2 ^ ∑ g, len g)
    (hlB : ∀ r ∈ l, r.length = B) {c kk : List (Fin (A + 4))} (hcB : c.length = B)
    (hkk : kk.length = R * 2 ^ ∑ g, len g) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (ι .src) = l.flatten) (hctr : S.R (ι .ctr) = c) (hcnt : S.R (ι .cnt) = kk)
    (htmp : S.R (ι .tmp) = []) (hctmp : S.R (ι .ctmp) = []) (hout : S.R (ι .out) = [])
    (hdst : ∀ d, S.R (ι (.dst d)) = []) (haux : ∀ d, S.R (ι (.aux d)) = [])
    (hfld : ∀ g, S.R (ι (.fld g)) = binSyms (len g) 0) (hcomp : (S.R (ι .comp)).length = len tf)
    (hspare : ∀ r, S.R (ι (.spare r)) = []) (hscr : ∀ s, S.R (ι (.scr s)) = [])
    (hprm : ∀ q, S.R (ι (.prm q)) = P₀ q) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ R * 2 ^ (∑ g, len g) * (2 * cP + 2 * idxStepCost B (len tf) len + 4 * B + 4) + 13 ∧
      Exec body (rotGenPass prep tf neg ι st) (mk v S) m (mk v' { S with R := R' }) ∧
      R' (ι .src) = (moveRecs (rotPerm len tf neg R hoff) l).flatten ∧
      (R' (ι .comp)).length = len tf ∧
      ∀ k, k ≠ ι .src → k ≠ ι .comp → R' k = S.R k := by
  set M := R * 2 ^ ∑ g, len g with hM
  set π := rotPerm len tf neg R hoff with hπ
  set res := (moveRecs π l).flatten with hres
  set L := len tf with hL
  have hw : l.flatten.length = M * B := by rw [length_flatten_of l hlB, hl]
  have hne : ∀ {x y : RotGReg nf ns np}, x ≠ y → ι x ≠ ι y := fun h => hι.ne h
  have hfld0 : ∀ g, binSyms (len g) (digit len g (0 + M)) =
      (binSyms (len g) 0 : List (Fin (A + 4))) :=
    fun g => by rw [digit_wrap len R g]
  -- routing
  have hXr : ∀ x, routeRegs (ι .src) (fun d => ι (.dst d)) (ι .ctr) (ι .tmp) (ι x) →
      x.isIdx = false := by
    intro x hx
    simp only [routeRegs, hι.eq_iff] at hx
    rcases hx with rfl | rfl | rfl | ⟨d, rfl⟩ <;> rfl
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hsrc₁, hdst₁, hI₁, hoth₁⟩ :=
    routeIdxP_exec body (ι .src) (fun d => ι (.dst d)) (ι .ctr) (ι .tmp) (fun g => ι (.fld g))
      len L (fun r => ι (rsRegG tf r)) (fun r => ι (.spare r)) (rsrcR tf off) (fun s => ι (.scr s))
      (fun q => ι (.prm q)) P₀ st (inCode2 A neg) hprep (rotG_idxLayout hι hst len tf off hXr)
      (by simp [hι.eq_iff]) (fun d => by simp [hι.eq_iff]) (fun d d' h => by simpa using hι h) hB
      hw hcB v S hsrc hctr htmp (rotG_idxState len tf off P₀ S.R hfld hcomp hspare hscr hprm)
  have hcomp_ne : ∀ x : RotGReg nf ns np, x ≠ .comp →
      ∀ r g, rsrcR tf off r = .inr g → ι (rsRegG tf r) ≠ ι x := by
    intro x hx r g hr
    fin_cases r <;> simp [rsrcR] at hr
    exact hne (by simpa [rsRegG] using hx.symm)
  have hk₁ : ∀ x, x ≠ .src → (∀ d, x ≠ .dst d) → (∀ g, x ≠ .fld g) → x ≠ .comp →
      R₁ (ι x) = S.R (ι x) :=
    fun x h1 h2 h3 h4 => hoth₁ _ (hne h1) (fun d => hne (h2 d).symm) (fun g => hne (h3 g).symm)
      (hcomp_ne x h4)
  -- reversing
  obtain ⟨v₂, R₂, hu₂, he₂, hds₂, hoth₂⟩ := revList_exec body (fun d => ι (.dst d))
    (fun d => ι (.aux d)) (fun d d' h => by simpa using hι h) (fun d d' h => by simpa using hι h)
    (fun d d' h => by simpa using hι h) (List.finRange 2) (List.nodup_finRange 2) v₁
    { S with R := R₁ }
  have hk₂ : ∀ x, (∀ d, x ≠ .dst d) → (∀ d, x ≠ .aux d) → R₂ (ι x) = R₁ (ι x) :=
    fun x h1 h2 => hoth₂ _ (fun d _ => ⟨hne (h1 d), hne (h2 d)⟩)
  have hk₁₂ : ∀ x, x ≠ .src → (∀ d, x ≠ .dst d) → (∀ d, x ≠ .aux d) → (∀ g, x ≠ .fld g) →
      x ≠ .comp → R₂ (ι x) = S.R (ι x) :=
    fun x h1 h2 h3 h4 h5 => (hk₂ x h2 h3).trans (hk₁ x h1 h2 h4 h5)
  have haux₂ : ∀ d, R₂ (ι (.aux d)) =
      blocksIdx l.flatten B M (idxCodeP (inCode2 A neg) L len (rsrcR tf off)) 0 d ++ [] := by
    intro d
    rw [(hds₂ d (List.mem_finRange d)).2]
    show (R₁ (ι (.dst d))).reverse ++ R₁ (ι (.aux d)) = _
    rw [hdst₁, hdst, hk₁ _ (by simp) (by simp) (by simp) (by simp), haux]
    simp
  have hcomp₁ : (R₁ (ι .comp)).length = L := hI₁.2.1 1 off rfl
  have hI₂ : IdxStateP (fun g => ι (.fld g)) len L (fun r => ι (rsRegG tf r))
      (fun r => ι (.spare r)) (rsrcR tf off) (fun s => ι (.scr s)) (fun q => ι (.prm q)) P₀ R₂ 0 := by
    apply rotG_idxState len tf off P₀ R₂
    · intro g; rw [hk₂ _ (by simp) (by simp), hI₁.1 g, hfld0]
    · rw [hk₂ _ (by simp) (by simp)]; exact hcomp₁
    · intro r; rw [hk₂ _ (by simp) (by simp)]; exact hI₁.2.2.1 r
    · intro s; rw [hk₂ _ (by simp) (by simp)]; exact hI₁.2.2.2.1 s
    · intro q; rw [hk₂ _ (by simp) (by simp)]; exact hI₁.2.2.2.2 q
  have hsum₂ : ((List.finRange 2).map fun d => 2 * ({ S with R := R₁ }.R (ι (.dst d))).length +
      2).sum = 2 * (M * B) + 4 := by
    simp only [hdst₁, hdst, List.append_nil, List.length_reverse]
    rw [← Fin.sum_univ_def, Fin.sum_univ_two, length_blocksIdx _ _ _ _ _ _ hw,
      length_blocksIdx _ _ _ _ _ _ hw]
    have := idxCount_sum (idxCodeP (inCode2 A neg) L len (rsrcR tf off)) M 0
    rw [Fin.sum_univ_two] at this
    have h2 : M * B = (idxCount (idxCodeP (inCode2 A neg) L len (rsrcR tf off)) 0 M 0 +
        idxCount (idxCodeP (inCode2 A neg) L len (rsrcR tf off)) 0 M 1) * B := by rw [this]
    rw [h2]
    ring
  -- merging
  have hXm : ∀ x, mergeRegs (fun d => ι (.aux d)) (ι .out) (ι .ctr) (ι .tmp) (ι .cnt) (ι .ctmp)
      (ι x) → x.isIdx = false := by
    intro x hx
    simp only [mergeRegs, hι.eq_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | ⟨d, rfl⟩ <;> rfl
  obtain ⟨v₃, R₃, m₃, hu₃, hm₃, he₃, hout₃, haux₃, hI₃, hoth₃⟩ :=
    mergeIdxP_exec body (fun d => ι (.aux d)) (ι .out) (ι .ctr) (ι .tmp) (ι .cnt) (ι .ctmp)
      (fun g => ι (.fld g)) len L (fun r => ι (rsRegG tf r)) (fun r => ι (.spare r))
      (rsrcR tf off) (fun s => ι (.scr s)) (fun q => ι (.prm q)) P₀ st (outCode2 A neg) hprep
      (rotG_idxLayout hι hst len tf off hXm) (by simp [hι.eq_iff])
      (fun d => by simp [hι.eq_iff]) (fun d d' h => by simpa using hι h) hcB hkk
      (fun d => blocksIdx l.flatten B M (idxCodeP (inCode2 A neg) L len (rsrcR tf off)) 0 d ++ [])
      (fun d => by
        rw [List.length_append, length_blocksIdx _ _ _ _ _ _ hw, List.length_nil, Nat.add_zero,
          rotG_count (A := A) len tf neg hoff hob d])
      v₂ { S with R := R₂ } haux₂
      (by show R₂ (ι .ctr) = c; rw [hk₁₂ _ (by simp) (by simp) (by simp) (by simp) (by simp), hctr])
      (by show R₂ (ι .tmp) = []; rw [hk₁₂ _ (by simp) (by simp) (by simp) (by simp) (by simp), htmp])
      (by show R₂ (ι .cnt) = kk; rw [hk₁₂ _ (by simp) (by simp) (by simp) (by simp) (by simp), hcnt])
      (by show R₂ (ι .ctmp) = []; rw [hk₁₂ _ (by simp) (by simp) (by simp) (by simp) (by simp), hctmp])
      hI₂
  have hmerge := rotG_merge (A := A) len tf neg hoff hob l hl hlB
  rw [hmerge] at hout₃ haux₃
  have hout₂ : R₂ (ι .out) = [] := by
    rw [hk₁₂ _ (by simp) (by simp) (by simp) (by simp) (by simp), hout]
  have hsrc₂ : R₂ (ι .src) = [] := by rw [hk₂ _ (by simp) (by simp), hsrc₁]
  have hk₃ : ∀ x, x ≠ .out → (∀ d, x ≠ .aux d) → (∀ g, x ≠ .fld g) → x ≠ .comp →
      R₃ (ι x) = R₂ (ι x) :=
    fun x h1 h2 h3 h4 => hoth₃ _ (hne h1) (fun d => hne (h2 d).symm) (fun g => hne (h3 g).symm)
      (hcomp_ne x h4)
  have hout₃' : R₃ (ι .out) = res.reverse := by
    rw [hout₃]; show _ ++ R₂ (ι .out) = _; rw [hout₂, List.append_nil]
  have hsrc₃ : R₃ (ι .src) = [] := by rw [hk₃ _ (by simp) (by simp) (by simp) (by simp), hsrc₂]
  have hcomp₃ : (R₃ (ι .comp)).length = L := hI₃.2.1 1 off rfl
  -- moving back
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body (ι .out) (ι .src) (hne (by simp)) id v₃
    { S with R := R₃ }
  have hfin : ∀ k, k ≠ ι .src → k ≠ ι .comp →
      movedR R₃ (ι .out) (ι .src) id (R₃ (ι .out)) k = S.R k := by
    intro k hk1 hkc
    by_cases hk2 : k = ι .out
    · subst hk2
      simp [movedR, hne (show RotGReg.out ≠ (.src : RotGReg nf ns np) by simp), hout]
    simp only [movedR, Function.update_of_ne hk1, Function.update_of_ne hk2]
    by_cases hk3 : ∃ d, k = ι (.aux d)
    · obtain ⟨d, rfl⟩ := hk3
      rw [haux₃, haux]
    by_cases hk4 : ∃ g, k = ι (.fld g)
    · obtain ⟨g, rfl⟩ := hk4
      rw [hI₃.1 g, hfld0, hfld]
    simp only [not_exists] at hk3 hk4
    rw [hoth₃ k hk2 (fun d e => hk3 d e.symm) (fun g e => hk4 g e.symm)
      (fun r g hr e => by
        fin_cases r <;> simp [rsrcR] at hr
        exact hkc (by simpa [rsRegG] using e.symm))]
    show R₂ k = S.R k
    by_cases hk5 : ∃ d, k = ι (.dst d)
    · obtain ⟨d, rfl⟩ := hk5
      rw [(hds₂ d (List.mem_finRange d)).1, hdst]
    simp only [not_exists] at hk5
    rw [hoth₂ k (fun d _ => ⟨hk5 d, hk3 d⟩)]
    exact hoth₁ k hk1 (fun d e => hk5 d e.symm) (fun g e => hk4 g e.symm)
      (fun r g hr e => by
        fin_cases r <;> simp [rsrcR] at hr
        exact hkc (by simpa [rsRegG] using e.symm))
  refine ⟨v₄, movedR R₃ (ι .out) (ι .src) id (R₃ (ι .out)),
    m₁ + ((((List.finRange 2).map fun d => 2 * ({ S with R := R₁ }.R (ι (.dst d))).length + 2).sum
      + 1) + (m₃ + (2 * (R₃ (ι .out)).length + 2))),
    by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))) rfl rfl, ?_, ?_, hfin⟩
  · rw [hsum₂, hout₃', List.length_reverse, hres, length_flatten_moveRecs _ l hl hlB]
    have hC : idxStepCost B L len = 4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 12 := rfl
    nlinarith [hm₁, hm₃]
  · simp [movedR, hout₃', hsrc₃]
  · have h1 : ι .comp ≠ ι .src := hne (by simp)
    have h2 : ι .comp ≠ ι .out := hne (by simp)
    simp only [movedR, Function.update_of_ne h1, Function.update_of_ne h2]
    exact hcomp₃

end Machine

end IntegerMultBounds.MathlibTM2.Node
