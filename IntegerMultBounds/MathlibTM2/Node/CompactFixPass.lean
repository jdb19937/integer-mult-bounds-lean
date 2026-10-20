module

public import IntegerMultBounds.MathlibTM2.Node.FixPass
public import IntegerMultBounds.MathlibTM2.Node.SwapPass
public import IntegerMultBounds.MathlibTM2.Node.CompactBadCode
public import IntegerMultBounds.MathlibTM2.Layer.CompactKey

/-!
# The top-column fix of the compact selected-bit XOR

The gadget toggles the used segments `c < n`; the selected bit `P = posS n` of the top column is
added by the fix pass of `IntegerMultBounds.MathlibTM2.Node.FixPass`, which moves the records by
the masked exclusive or `xorIdx (2^P)` (`y_P ← y_P ⊕ x_P`).

The code programs read `x`, `y` and the phase mask `mMk`, whose last mark is `P`
(`topStep_last`): the input code is `(x_P, y_P)` and the output code `(x_P, y_P ⊕ x_P)`
(`codeTop_spec`, `topIn_mkV`, `topOut_mkV`). Within one input code class the fix moves every
index by the same amount, so it is increasing there (`fix_mono`). `cxFix_exec`: the fix pass
leaves `moveRecs (xorPerm (2^P)) l`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks IntegerMultBounds.MathlibTM2.Layer.CompactGadget

/-! ### The top bit read at the last mark -/

lemma foldl_topStep_unmarked (x y mk : ℕ) (s : Bool × Bool) :
    ∀ l : List ℕ, (∀ t ∈ l, mk.testBit t = false) →
      l.foldl (fun s t => topStep s fun r => ((![x, y, mk] : Fin 3 → ℕ) r).testBit t) s = s
  | [], _ => rfl
  | t :: l, h => by
    rw [List.foldl_cons]
    have e : topStep s (fun r => ((![x, y, mk] : Fin 3 → ℕ) r).testBit t) = s := by
      simp [topStep, h t List.mem_cons_self]
    rw [e]
    exact foldl_topStep_unmarked x y mk s l fun t' ht' => h t' (List.mem_cons_of_mem _ ht')

/-- With its last mark below `L` at `P`, the top step reads `(x_P, y_P)`. -/
lemma topStep_last (x y mk : ℕ) {P L : ℕ} (hP : P < L) (hmk : mk.testBit P = true)
    (habove : ∀ t, P < t → t < L → mk.testBit t = false) :
    (List.range L).foldl (fun s t => topStep s fun r => ((![x, y, mk] : Fin 3 → ℕ) r).testBit t)
      (false, false) = (x.testBit P, y.testBit P) := by
  rw [show L = P + 1 + (L - (P + 1)) by omega, List.range_add, List.foldl_append,
    List.range_succ, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  have e : ∀ s, topStep s (fun r => ((![x, y, mk] : Fin 3 → ℕ) r).testBit P) =
      (x.testBit P, y.testBit P) := fun s => by simp [topStep, hmk]
  rw [e]
  have := foldl_topStep_unmarked x y mk (x.testBit P, y.testBit P)
    ((List.range (L - (P + 1))).map (P + 1 + ·)) (fun t ht => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
      rw [List.mem_range] at hj
      exact habove _ (by omega) (by omega))
  rwa [List.foldl_map] at this

lemma topIn_last {A : ℕ} (x y mk : ℕ) {P L : ℕ} (hP : P < L) (hmk : mk.testBit P = true)
    (habove : ∀ t, P < t → t < L → mk.testBit t = false) :
    (topInAuto A).eval L ![x, y, mk] = topCode (x.testBit P) (y.testBit P) := by
  unfold topInAuto
  rw [absAuto_eval _ _ topDec_topEnc, topStep_last x y mk hP hmk habove]

lemma topOut_last {A : ℕ} (x y mk : ℕ) {P L : ℕ} (hP : P < L) (hmk : mk.testBit P = true)
    (habove : ∀ t, P < t → t < L → mk.testBit t = false) :
    (topOutAuto A).eval L ![x, y, mk] = topCode (x.testBit P) (xor (y.testBit P) (x.testBit P)) := by
  unfold topOutAuto
  rw [absAuto_eval _ _ topDec_topEnc, topStep_last x y mk hP hmk habove]

variable {p : Par}

/-- The last mark of the phase mask is the top selected bit. -/
lemma mkV_last (hG : 0 < p.G) (hGK : p.G + 1 < p.K) :
    (mkV p).testBit (posS p p.n) = true ∧ ∀ t, posS p p.n < t → (mkV p).testBit t = false := by
  refine ⟨(testBit_mkV hG hGK _).2 (Or.inl ⟨p.n, le_rfl, rfl⟩), fun t ht => ?_⟩
  by_contra hne
  rcases (testBit_mkV hG hGK t).1 (by simpa using hne) with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl | rfl⟩
  · have := Nat.mul_le_mul_right p.K hc; unfold posS at ht; omega
  · have := Nat.mul_le_mul_right p.K (show c + 1 ≤ p.n by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; unfold posS at ht; omega
  · have := Nat.mul_le_mul_right p.K (show c + 1 ≤ p.n by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; unfold posS at ht; omega

lemma posS_n_lt (hm : 0 < p.m) : posS p p.n < p.wy := by unfold posS Par.wy; omega

/-! ### The code programs -/

variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U}
variable {ι : CxReg → Fin T} {len : Fin 10 → ℕ} (F : Fields 10)

/-- The code-pass registers of the top codes. -/
def rsTop : Fin 3 → CxReg := ![.fld F.x, .fld F.y, .mMk]

/-- The code program of a top code `C`. -/
def codeTop (C : CAuto A 3 4) : Pr P T Q A U :=
  codePass (fun r => ι (rsTop F r)) (fun r => ι (cxSpares (show 3 ≤ 4 by norm_num) r)) (ι .st) C

variable {F}

theorem codeTop_spec (hι : Function.Injective ι) (hF : F.Valid p len) (C : CAuto A 3 4) :
    CodeSpec body (codeTop (ι := ι) F C) (fun g => ι (.fld g)) len (ι .st) (CxIdx ι)
      (CxInv p ι len) (codeSel C)
      (fun i => C.eval p.wy ![digit len F.x i, digit len F.y i, mkV p]) (6 * p.wy + 4) where
  runs i v S hI := by
    have hxy : F.x ≠ F.y := hF.xorFields.ne
    obtain ⟨hfld, -, -, -, hmk, -, -, -, -, -, -, hsp⟩ := id hI
    have hlay : CodeLayout (fun r => ι (rsTop F r))
        (fun r => ι (cxSpares (show 3 ≤ 4 by norm_num) r)) (ι .st) := by
      refine ⟨fun r r' e => ?_, fun r r' e => ?_, fun r r' e => ?_, fun r e => ?_,
        fun r e => by simpa [cxSpares] using hι e⟩
      · have := hι e; fin_cases r <;> fin_cases r' <;> simp_all [rsTop]
      · have := hι e
        simp only [cxSpares, CxReg.spare.injEq] at this
        exact Fin.castLE_injective _ this
      · have := hι e; fin_cases r <;> simp_all [rsTop, cxSpares]
      · have := hι e; fin_cases r <;> simp_all [rsTop]
    obtain ⟨v', hu, hsc, he⟩ := codePass_exec body hlay C p.wy
      ![digit len F.x i, digit len F.y i, mkV p] v S
      (fun r => by
        fin_cases r
        · show S.R (ι (.fld F.x)) = _; rw [hfld, hF.lx]; rfl
        · show S.R (ι (.fld F.y)) = _; rw [hfld, hF.ly]; rfl
        · show S.R (ι .mMk) = _; rw [hmk]; rfl)
      (fun r => hsp _)
    exact ⟨v', _, hu, le_rfl, by rw [hsc, codeSel_val]; rfl, he⟩
  cf_inj := fun g g' e => by simpa using hι e
  cf_Y := fun g => ⟨.fld g, trivial, rfl⟩
  digits := fun R i hI => hI.1
  frame := fun R R' i hI hR => cxInv_frame hI hR
  reidx := fun R R' i j hI hcf hR => cxInv_reidx hι hI hcf hR

/-! ### The fix on indices -/

section FixIdx

variable (len F) in
/-- The input code of the fix: `(x_P, y_P)`. -/
def fixIn (P i : ℕ) : Fin 4 := topCode ((digit len F.x i).testBit P) ((digit len F.y i).testBit P)

variable (len F) in
/-- The output code of the fix: `(x_P, y_P ⊕ x_P)`. -/
def fixOut (P i : ℕ) : Fin 4 :=
  topCode ((digit len F.x i).testBit P) (xor ((digit len F.y i).testBit P) ((digit len F.x i).testBit P))

lemma fixOut_xorIdx (hX : XorFields len F) (P i : ℕ) :
    fixOut len F P (xorIdx len F (2 ^ P) i) = fixIn len F P i := by
  unfold fixOut fixIn
  rw [digit_xorIdx_ne hX.ne, digit_xorIdx_y hX, Nat.testBit_xor, Nat.testBit_and,
    Nat.testBit_two_pow_self]
  cases (digit len F.x i).testBit P <;> cases (digit len F.y i).testBit P <;> rfl

/-- **The fix is increasing on each input code class.** -/
lemma fix_mono {P : ℕ} (hP : P < len F.y) {i i' : ℕ}
    (hc : fixIn len F P i = fixIn len F P i') (hlt : i < i') :
    xorIdx len F (2 ^ P) i < xorIdx len F (2 ^ P) i' := by
  obtain ⟨hx, hy⟩ := topCode_injective hc
  rw [xorIdx_two_pow hP, xorIdx_two_pow hP, ← hx]
  split_ifs with h
  · have hbit : ∀ j, j.testBit (fieldOff len F.y + P) = (digit len F.y j).testBit P := fun j => by
      rw [digit, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
      simp [hP, Nat.add_comm]
    have e := xor_two_pow_int i (fieldOff len F.y + P)
    have e' := xor_two_pow_int i' (fieldOff len F.y + P)
    rw [hbit, hy] at e
    rw [hbit] at e'
    have : ((i ^^^ 2 ^ (fieldOff len F.y + P) : ℕ) : ℤ) <
        ((i' ^^^ 2 ^ (fieldOff len F.y + P) : ℕ) : ℤ) := by
      rw [e, e']
      split_ifs <;> omega
    exact_mod_cast this
  · exact hlt

end FixIdx

/-! ### The fix pass -/

variable (body) in
/-- **The compact fix pass.** On the stream `l` of `R 2^q` records of `B ≥ 1` symbols, with the
index registers at index `0`, the fix pass leaves the records moved by `xorIdx (2^P)`, where
`P = posS n` is the selected bit of the top column. -/
theorem cxFix_exec (hι : Function.Injective ι) (hF : F.Valid p len) (hG : 0 < p.G)
    (hGK : p.G + 1 < p.K) (hm : 0 < p.m) {q R : ℕ} (hq : fieldOff len F.y + len F.y ≤ q)
    {src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp : Fin T}
    (hY : ∀ x ∈ [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp], ¬ CxIdx ι x)
    (hregs : [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp].Nodup)
    {B : ℕ} (hB : 1 ≤ B) (l : List (List (Fin (A + 4)))) (hl : l.length = R * 2 ^ q)
    (hlB : ∀ r ∈ l, r.length = B)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = l.flatten)
    (hr0 : S.R r0 = []) (hr1 : S.R r1 = []) (hr2 : S.R r2 = []) (hr3 : S.R r3 = [])
    (hq0 : S.R q0 = []) (hq1 : S.R q1 = []) (hq2 : S.R q2 = []) (hq3 : S.R q3 = [])
    (hctr : (S.R ctrB).length = B) (hcnt : (S.R cnt).length = R * 2 ^ q)
    (htmp : S.R tmp = []) (hI : CxInv p ι len S.R 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ R * 2 ^ q * (2 * idxStepCost (6 * p.wy + 4) B len + 10 * B + 4) +
        8 * (∑ f, len f) + 8 * 10 + 18 ∧
      Exec body (fixAtC (codeTop (ι := ι) F (topInAuto A)) (codeSel (topInAuto A))
          (codeTop (ι := ι) F (topOutAuto A)) (codeSel (topOutAuto A))
          src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp (ι .st) (fun g => ι (.fld g)))
        (mk v S) m (mk v' { S with R := (Function.update S.R src
          (moveRecs (xorPerm (R := R) hF.xorFields hq (2 ^ posS p p.n)) l).flatten) }) := by
  have hX := hF.xorFields
  set P := posS p p.n with hPdef
  have hPL : P < len F.y := by rw [hF.ly]; exact posS_n_lt hm
  obtain ⟨hlast, habove⟩ := mkV_last hG hGK (p := p)
  have hin : ∀ i, (topInAuto A).eval p.wy ![digit len F.x i, digit len F.y i, mkV p] =
      fixIn len F P i := fun i =>
    topIn_last _ _ _ (posS_n_lt hm) hlast fun t h1 _ => habove t h1
  have hout : ∀ i, (topOutAuto A).eval p.wy ![digit len F.x i, digit len F.y i, mkV p] =
      fixOut len F P i := fun i =>
    topOut_last _ _ _ (posS_n_lt hm) hlast fun t h1 _ => habove t h1
  have csIn := codeTop_spec (body := body) hι hF (topInAuto A)
  have csOut := codeTop_spec (body := body) hι hF (topOutAuto A)
  simp only [hin] at csIn
  simp only [hout] at csOut
  set π := xorPerm (R := R) hX hq (2 ^ P) with hπ
  have hcodes : ∀ i : Fin (R * 2 ^ q), fixOut len F P (π i) = fixIn len F P i :=
    fun i => fixOut_xorIdx hX P i
  have hmono : ∀ i i' : Fin (R * 2 ^ q), fixIn len F P i = fixIn len F P i' → i < i' →
      π i < π i' := fun i i' hc hlt => fix_mono hPL hc hlt
  have hmem : ∀ x ∈ moveRecs π l, x.length = B := fun x hx => hlB x (mem_moveRecs π hl hx)
  obtain ⟨v', m, hu, hm', he⟩ := fixAtC_exec csIn csOut hY hregs hB l hl hlB
    (idxCount_perm π _ _ hcodes) ((moveRecs π l).flatten)
    (by rw [length_flatten_uniform _ hmem, length_moveRecs])
    (mergeIdxList_moveRecs π l hl hlB _ _ hcodes hmono) v S hsrc hr0 hr1 hr2 hr3 hq0 hq1 hq2
    hq3 hctr hcnt htmp hI
  exact ⟨v', m, hu, by rw [two_mul]; exact hm', he⟩

end IntegerMultBounds.MathlibTM2.Node
