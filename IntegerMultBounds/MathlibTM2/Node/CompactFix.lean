module

public import IntegerMultBounds.MathlibTM2.Node.FixPass
public import IntegerMultBounds.MathlibTM2.Node.RotGen

/-!
# The top-position fixup in the field model

`topFixC len X Y K ρ n` (`IntegerMultBounds.MathlibTM2.Layer.CompactXor`) XORs bit `p = ρ + n K` of
field `X` into bit `p` of field `Y`. It keeps every other field, so it is an involution of the
indices below `R · 2^S` whenever field `Y` lies below bit `S` (`topFixPermC`).

**Codes.** The fix machine `fixAt` reads the field registers of `X` and `Y` and the mask register
`tm` holding `2^p`; the input code of index `i` is `(x_p, y_p)` and the output code
`(x_p, y_p ⊕ x_p)` (`idxCode_topInC`, `idxCode_topOutC`). Since `topFixC` keeps `X` and flips
`y_p` exactly when `x_p = 1`, the output code of the destination is the input code of the source.

**Order.** Within one input code class `topFixC` moves every index by the same amount
`2^{foff Y} · fixShift p x_p y_p` (`topFixC_int`), so it is increasing on the class, and routing
by the input code and merging by the output code moves the records by `topFixC`
(`mergeIdxList_moveRecs`); the code classes have equal sizes (`idxCount_perm`).

**The pass** (`fixPassC`, `fixPassC_exec`): on the stream of `R · 2^S` records in `src`, `src`
ends holding `(moveRecs (topFixPermC …) l).flatten` and every other register ends as it started,
in at most `R 2^S (18 B + 12 len Y + 8 ∑ len + 8 nf + 28) + 8 ∑ len + 8 nf + 18` steps.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Layer.CompactXor

set_option linter.unusedSimpArgs false

/-! ### The top fixup as a permutation of indices -/

section TopFixPerm

variable {nf : ℕ} (len : Fin nf → ℕ)

lemma topFixC_mask_lt {X Y : Fin nf} {K ρ n : ℕ} (hLXY : len X = len Y) (i : ℕ) :
    dig len Y i ^^^ (dig len X i &&& 2 ^ (ρ + n * K)) < 2 ^ len Y :=
  Nat.xor_lt_two_pow (dig_lt len Y i)
    (lt_of_le_of_lt Nat.and_le_left (by rw [← hLXY]; exact dig_lt len X i))

lemma dig_topFixC_Y {X Y : Fin nf} {K ρ n : ℕ} (hLXY : len X = len Y) (i : ℕ) :
    dig len Y (topFixC len X Y K ρ n i) = dig len Y i ^^^ (dig len X i &&& 2 ^ (ρ + n * K)) :=
  dig_setDig_self len Y i (topFixC_mask_lt len hLXY i)

lemma dig_topFixC_ne {X Y f : Fin nf} {K ρ n : ℕ} (hLXY : len X = len Y) (hf : f ≠ Y) (i : ℕ) :
    dig len f (topFixC len X Y K ρ n i) = dig len f i :=
  dig_setDig_ne len hf i (topFixC_mask_lt len hLXY i)

lemma topFixC_topFixC {X Y : Fin nf} {K ρ n : ℕ} (hXY : X ≠ Y) (hLXY : len X = len Y) (i : ℕ) :
    topFixC len X Y K ρ n (topFixC len X Y K ρ n i) = i := by
  unfold topFixC
  rw [dig_setDig_self len Y i (topFixC_mask_lt len hLXY i),
    dig_setDig_ne len hXY i (topFixC_mask_lt len hLXY i),
    setDig_setDig_self len Y i (topFixC_mask_lt len hLXY i) (Nat.xor_lt_two_pow
      (topFixC_mask_lt len hLXY i) (lt_of_le_of_lt Nat.and_le_left
        (by rw [← hLXY]; exact dig_lt len X i))),
    Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, setDig_dig]

lemma topFixC_lt {X Y : Fin nf} {K ρ n R S : ℕ} (hLXY : len X = len Y)
    (hSY : foff len Y + len Y ≤ S) {i : ℕ} (hi : i < R * 2 ^ S) :
    topFixC len X Y K ρ n i < R * 2 ^ S :=
  setDig_lt len Y hi (topFixC_mask_lt len hLXY i) hSY

/-- The top fixup as a permutation of the indices below `R · 2^S`. -/
def topFixPermC (X Y : Fin nf) (K ρ n : ℕ) {R S : ℕ} (hXY : X ≠ Y) (hLXY : len X = len Y)
    (hSY : foff len Y + len Y ≤ S) : Equiv.Perm (Fin (R * 2 ^ S)) where
  toFun i := ⟨topFixC len X Y K ρ n i, topFixC_lt len hLXY hSY i.isLt⟩
  invFun i := ⟨topFixC len X Y K ρ n i, topFixC_lt len hLXY hSY i.isLt⟩
  left_inv i := Fin.ext (topFixC_topFixC len hXY hLXY i)
  right_inv i := Fin.ext (topFixC_topFixC len hXY hLXY i)

lemma topFixPermC_apply (X Y : Fin nf) (K ρ n : ℕ) {R S : ℕ} (hXY : X ≠ Y) (hLXY : len X = len Y)
    (hSY : foff len Y + len Y ≤ S) (i : Fin (R * 2 ^ S)) :
    (topFixPermC len X Y K ρ n hXY hLXY hSY i : ℕ) = topFixC len X Y K ρ n i := rfl

lemma topFixPermC_symm (X Y : Fin nf) (K ρ n : ℕ) {R S : ℕ} (hXY : X ≠ Y) (hLXY : len X = len Y)
    (hSY : foff len Y + len Y ≤ S) :
    (topFixPermC len X Y K ρ n hXY hLXY hSY (R := R)).symm =
      topFixPermC len X Y K ρ n hXY hLXY hSY := rfl

/-- Replacing a field shifts the index by `2^{foff f}` times the change of the field. -/
lemma setDig_int (f : Fin nf) (i v : ℕ) :
    ((setDig len f i v : ℕ) : ℤ) = i + 2 ^ foff len f * ((v : ℤ) - dig len f i) := by
  have h : (i : ℤ) = ((setDig len f i (dig len f i) : ℕ) : ℤ) := by rw [setDig_dig]
  rw [h]
  unfold setDig
  push_cast
  ring

/-- The top fixup on indices: the index moves by `2^{foff Y} · fixShift`. -/
lemma topFixC_int (X Y : Fin nf) {K ρ n : ℕ} (i : ℕ) :
    ((topFixC len X Y K ρ n i : ℕ) : ℤ) = i + 2 ^ foff len Y *
      fixShift (ρ + n * K) ((dig len X i).testBit (ρ + n * K))
        ((dig len Y i).testBit (ρ + n * K)) := by
  have hsh : ((dig len Y i ^^^ (dig len X i &&& 2 ^ (ρ + n * K)) : ℕ) : ℤ) - dig len Y i =
      fixShift (ρ + n * K) ((dig len X i).testBit (ρ + n * K))
        ((dig len Y i).testBit (ρ + n * K)) := by
    rw [Nat.and_two_pow]
    unfold fixShift
    cases hx : (dig len X i).testBit (ρ + n * K)
    · simp
    · simp only [Bool.toNat_true, one_mul, ↓reduceIte]
      rw [xor_two_pow_int]
      split_ifs <;> ring
  unfold topFixC
  rw [setDig_int, hsh]

end TopFixPerm

/-! ### The codes of the top bits in the field model -/

section TopCodes

variable {A nf : ℕ} (len : Fin nf → ℕ)

/-- The code-pass sources of the top codes: the field `X`, the field `Y`, and the mask `2^p` of
the top selected bit. -/
def topSrcC (X Y : Fin nf) (p : ℕ) : Fin 3 → Fin nf ⊕ ℕ := ![.inl X, .inl Y, .inr (2 ^ p)]

lemma regVal_topSrcC (X Y : Fin nf) (p i : ℕ) :
    regVal len (topSrcC X Y p) i = ![dig len X i, dig len Y i, 2 ^ p] := by
  funext r
  fin_cases r <;> simp [regVal, topSrcC, dig_eq_digit]

lemma idxCode_topInC (X Y : Fin nf) {p : ℕ} (hp : p < len Y) (i : ℕ) :
    idxCode (topInAuto A) (len Y) len (topSrcC X Y p) i =
      topCode ((dig len X i).testBit p) ((dig len Y i).testBit p) := by
  rw [idxCode, regVal_topSrcC, topIn_eval _ _ _ _ hp]

lemma idxCode_topOutC (X Y : Fin nf) {p : ℕ} (hp : p < len Y) (i : ℕ) :
    idxCode (topOutAuto A) (len Y) len (topSrcC X Y p) i =
      topCode ((dig len X i).testBit p) (xor ((dig len Y i).testBit p) ((dig len X i).testBit p)) := by
  rw [idxCode, regVal_topSrcC, topOut_eval _ _ _ _ hp]

end TopCodes

/-! ### The fix pass in the field model -/

section FixMainC

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {nf : ℕ}

/-- **The fix pass** of the field model: `fixAt` with the codes `(x_p, y_p)` and
`(x_p, y_p ⊕ x_p)` of the top selected bit `p`, read from the field register of `X`, the field
register of `Y` and the mask register `tm`. -/
def fixPassC (X Y : Fin nf) (src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp tm st : Fin T)
    (cf : Fin nf → Fin T) (us : Fin 3 → Fin T) : Pr P T Q A U :=
  fixAt src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp st cf ![cf X, cf Y, tm] us (topInAuto A)
    (topOutAuto A)

/-- **Fix pass.** On the stream `l` of `R · 2^S` records of `B ≥ 1` symbols in `src`, with the
field counter at index `0`, the mask `2^(ρ + n K)` in `tm`, `ctrB`, `cnt` holding `B` and
`R · 2^S` symbols, and empty `r0, …, r3`, `q0, …, q3`, `tmp`, `us`, the fix pass moves the record
at index `i` to index `topFixC i`: `src` ends holding `(moveRecs (topFixPermC …) l).flatten`, and
every other register ends as it started. -/
theorem fixPassC_exec (len : Fin nf → ℕ) {X Y : Fin nf} (hXY : X ≠ Y) (hLXY : len X = len Y)
    {R S : ℕ} (hSY : foff len Y + len Y ≤ S) {K ρ n : ℕ} (hp : ρ + n * K < len Y)
    {src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp tm st : Fin T} {cf : Fin nf → Fin T}
    {us : Fin 3 → Fin T}
    (hreg : ([src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp] ++ [tm] ++ List.ofFn us ++
      List.ofFn cf).Nodup)
    (hst : st ∉ [tm] ++ List.ofFn us ++ List.ofFn cf) {B : ℕ} (hB : 1 ≤ B)
    (l : List (List (Fin (A + 4)))) (hl : l.length = R * 2 ^ S)
    (hlB : ∀ r ∈ l, r.length = B) (v : HS T Q A U) (stk : Stacks T A)
    (hsrc : stk.R src = l.flatten)
    (hr0 : stk.R r0 = []) (hr1 : stk.R r1 = []) (hr2 : stk.R r2 = []) (hr3 : stk.R r3 = [])
    (hq0 : stk.R q0 = []) (hq1 : stk.R q1 = []) (hq2 : stk.R q2 = []) (hq3 : stk.R q3 = [])
    (hctr : (stk.R ctrB).length = B) (hcnt : (stk.R cnt).length = R * 2 ^ S)
    (htmp : stk.R tmp = []) (htm : stk.R tm = binSyms (len Y) (2 ^ (ρ + n * K)))
    (hus : ∀ r, stk.R (us r) = []) (hcf : ∀ j, stk.R (cf j) = binSyms (len j) 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ R * 2 ^ S * (18 * B + 12 * len Y + 8 * (∑ f, len f) + 8 * nf + 28) +
        8 * (∑ f, len f) + 8 * nf + 18 ∧
      Exec body (fixPassC X Y src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp tm st cf us) (mk v stk) m
        (mk v' { stk with R := (Function.update stk.R src
          (moveRecs (topFixPermC len X Y K ρ n (R := R) hXY hLXY hSY) l).flatten) }) := by
  obtain ⟨n12, n1, nus, ncf, d12, d1u, d1c, d2u, d2c, duc⟩ := nodup_append4 hreg
  have husinj : Function.Injective us := List.nodup_ofFn.1 nus
  have hcfinj : Function.Injective cf := List.nodup_ofFn.1 ncf
  have hus12 : ∀ r, us r ∉ [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp] :=
    fun r hr => d1u _ hr _ (List.mem_ofFn.2 ⟨r, rfl⟩) rfl
  have hcf12 : ∀ j, cf j ∉ [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp] :=
    fun j hj => d1c _ hj _ (List.mem_ofFn.2 ⟨j, rfl⟩) rfl
  have htm12 : tm ∉ [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp] :=
    fun h => d12 _ h _ (by simp) rfl
  have htmus : ∀ r, tm ≠ us r := fun r => d2u _ (by simp) _ (List.mem_ofFn.2 ⟨r, rfl⟩)
  have htmcf : ∀ j, tm ≠ cf j := fun j => d2c _ (by simp) _ (List.mem_ofFn.2 ⟨j, rfl⟩)
  have hucf : ∀ r j, us r ≠ cf j := fun r j =>
    duc _ (List.mem_ofFn.2 ⟨r, rfl⟩) _ (List.mem_ofFn.2 ⟨j, rfl⟩)
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.mem_ofFn] at hst
  obtain ⟨⟨hsttm, hstus⟩, hstcf⟩ := hst
  set rs : Fin 3 → Fin T := ![cf X, cf Y, tm] with hrs
  have hcode : CodeLayout rs us st :=
    { rs_inj := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          first
          | rfl
          | (exfalso; revert hij
             simp [rs, hcfinj.eq_iff, hXY, Ne.symm hXY, htmcf, Ne.symm (htmcf _)])
      tmps_inj := husinj
      rs_tmps := by
        intro r r'
        fin_cases r <;> simp [rs, hucf, Ne.symm (hucf _ _), htmus]
      rs_st := by
        intro r
        fin_cases r <;> simp [rs]
        · exact fun e => hstcf ⟨_, e⟩
        · exact fun e => hstcf ⟨_, e⟩
        · exact Ne.symm hsttm
      tmps_st := fun r e => hstus ⟨r, e⟩ }
  have hfield : ∀ r j, topSrcC X Y (ρ + n * K) r = .inl j → rs r = cf j ∧ len j = len Y := by
    intro r j hr
    fin_cases r <;> simp [topSrcC] at hr <;> subst hr <;> simp [rs, hLXY]
  have hparam : ∀ r p' j, topSrcC X Y (ρ + n * K) r = .inr p' → rs r ≠ cf j := by
    intro r p' j hr
    fin_cases r <;> simp [topSrcC] at hr
    simp [rs, htmcf]
  have hrs12 : ∀ r, rs r ∉ [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp] := by
    intro r
    fin_cases r
    · exact hcf12 _
    · exact hcf12 _
    · exact htm12
  have hX : ∀ (Xp : Fin T → Prop),
      (∀ x, Xp x → x ∈ [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp]) →
      IdxLayout cf len (len Y) rs us (topSrcC X Y (ρ + n * K)) st Xp := fun Xp hXp =>
    { hcode with
      cf_inj := hcfinj
      tmps_cf := hucf
      field := hfield
      param := hparam
      cf_X := fun j hx => hcf12 j (hXp _ hx)
      rs_X := fun r hx => hrs12 r (hXp _ hx)
      tmps_X := fun r hx => hus12 r (hXp _ hx) }
  have hlay : FixLayout src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp st cf len (len Y) rs us
      (topSrcC X Y (ρ + n * K)) :=
    { route := hX _ (by
        intro x hx
        rcases hx with rfl | rfl | rfl | ⟨d, rfl⟩
        · simp
        · simp
        · simp
        · fin_cases d <;> simp)
      merge := hX _ (by
        intro x hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | ⟨d, rfl⟩
        · simp
        · simp
        · simp
        · simp
        · simp
        · fin_cases d <;> simp)
      regs := n12
      cf_regs := hcf12
      us_regs := hus12 }
  have hIdx : IdxState cf len (len Y) rs us (topSrcC X Y (ρ + n * K)) stk.R 0 :=
    ⟨fun j => by rw [hcf j]; simp [digit],
      fun r p' hr => by
        fin_cases r <;> simp [topSrcC] at hr
        subst hr
        exact htm,
      hus⟩
  set πF := topFixPermC len X Y K ρ n (R := R) hXY hLXY hSY with hπF
  set cin := idxCode (topInAuto A) (len Y) len (topSrcC X Y (ρ + n * K)) with hcin
  set cout := idxCode (topOutAuto A) (len Y) len (topSrcC X Y (ρ + n * K)) with hcout
  have hcodes : ∀ i : Fin (R * 2 ^ S), cout (πF i) = cin i := by
    intro i
    rw [hπF, hcout, hcin, topFixPermC_apply, idxCode_topOutC len X Y hp, idxCode_topInC len X Y hp,
      dig_topFixC_Y len hLXY, dig_topFixC_ne len hLXY hXY, Nat.testBit_xor, Nat.testBit_and,
      Nat.testBit_two_pow]
    simp
  have hmono : ∀ i i' : Fin (R * 2 ^ S), cin i = cin i' → i < i' → πF i < πF i' := by
    intro i i' hc hlt
    rw [hcin, idxCode_topInC len X Y hp, idxCode_topInC len X Y hp] at hc
    obtain ⟨hx, hy⟩ := topCode_injective hc
    have e1 := topFixC_int len X Y (K := K) (ρ := ρ) (n := n) i
    have e2 := topFixC_int len X Y (K := K) (ρ := ρ) (n := n) i'
    rw [← hx, ← hy] at e2
    rw [Fin.lt_def] at hlt ⊢
    rw [hπF, topFixPermC_apply, topFixPermC_apply]
    have : ((i : ℕ) : ℤ) < ((i' : ℕ) : ℤ) := by exact_mod_cast hlt
    have h3 : ((topFixC len X Y K ρ n i : ℕ) : ℤ) < ((topFixC len X Y K ρ n i' : ℕ) : ℤ) := by
      rw [e1, e2]; linarith
    exact_mod_cast h3
  have hmerge := mergeIdxList_moveRecs πF l hl hlB cin cout hcodes hmono
  have hout : (moveRecs πF l).flatten.length = R * 2 ^ S * B := by
    rw [length_flatten_of_length _ (moveRecs_length_mem πF l hl hlB), length_moveRecs]
  obtain ⟨v', m, hu, hm, he⟩ := fixAt_exec body hlay (topInAuto A) (topOutAuto A) hB l hl hlB
    (idxCount_perm πF cin cout hcodes) _ hout hmerge v stk hsrc hr0 hr1 hr2 hr3 hq0 hq1 hq2 hq3
    hctr hcnt htmp hIdx
  exact ⟨v', m, hu, hm, he⟩

end FixMainC

end IntegerMultBounds.MathlibTM2.Node
