module

public import IntegerMultBounds.MathlibTM2.Node.RepairPass

/-!
# The top-position fixup

`topFix L K ρ f` XORs bit `p = ρ + (f - 1) K` of `x` into bit `p` of `y`; with `idealT` it completes
the target, `xorSel = topFix * idealT` (`IntegerMultBounds.MathlibTM2.Layer.PackedXor.xorSel_eq`). On ranks it moves the
record at `enc σ a` to `enc σ (topFix a)` (`addrPerm σ (topFix L K ρ f)`).

**Codes.** `topInAuto` reads the field of `x`, the field of `y` and the mask register `2^p` and
outputs the code `(x_p, y_p)` (`topCode`); `topOutAuto` outputs `(x_p, y_p ⊕ x_p)`
(`topIn_eval`, `topOut_eval`, `idxCode_topIn`, `idxCode_topOut`). Since `topFix` keeps `x` and
flips `y_p` exactly when `x_p = 1`, the output code of the destination is the input code of the
source.

**Order.** Within one input code class, `topFix` moves every rank by the same amount
`slotW (σ⁻¹ 1) · fixShift p x_p y_p` (`fix_enc`, from `rank_update` and `xor_two_pow_int`), so it
is increasing on the class. Hence routing by the input code and merging by the output code moves
the records by `topFix` (`mergeIdxList_moveRecs`, from `mergeIdxList_perm`); the code classes have
equal sizes (`idxCount_perm`).

**The machine** (`fixAt`, `fixPass`). Route by the input code into `r0, …, r3`, move each into
forward order in `q0, …, q3`, reset the counter, merge by the output code into `r0`, move the
result into `src`, reset the counter. `fixPass_exec`: `src` ends holding
`(moveRecs (addrPerm σ (topFix L K ρ f)) l).flatten`, every other register ends as it started, in
at most `92 M (B + k + 1) + 8 k + 82` steps. Each record costs `O(B + k)`: the index code pass reads
`L ≤ k` bits and the counter increment walks all `k` index bits.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.PackedXor


/-! ### The code automata of the top bits -/

/-- The code of a pair of bits `(a, b)`. -/
def topCode (a b : Bool) : Fin 4 := ⟨2 * a.toNat + b.toNat, by cases a <;> cases b <;> decide⟩

lemma topCode_injective {a b a' b' : Bool} (h : topCode a b = topCode a' b') : a = a' ∧ b = b' := by
  cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all [topCode]

/-- One column `(x_t, y_t, m_t)`: at the marked bit, record `(x_t, y_t)`. -/
def topStep (s : Bool × Bool) (col : Fin 3 → Bool) : Bool × Bool :=
  if col 2 then (col 0, col 1) else s

/-- A pair of bits as a stack symbol. -/
def topEnc {A : ℕ} (s : Bool × Bool) : Fin (A + 4) :=
  ⟨(2 * s.1.toNat + s.2.toNat) % (A + 4), Nat.mod_lt _ (by omega)⟩

/-- A stack symbol as a pair of bits. -/
def topDec {A : ℕ} (x : Fin (A + 4)) : Bool × Bool := (x.val.testBit 1, x.val.testBit 0)

lemma topDec_topEnc {A : ℕ} (s : Bool × Bool) : topDec (topEnc (A := A) s) = s := by
  obtain ⟨a, b⟩ := s
  have h : 2 * a.toNat + b.toNat < A + 4 := by cases a <;> cases b <;> simp
  simp only [topDec, topEnc, Nat.mod_eq_of_lt h]
  cases a <;> cases b <;> rfl

/-- The input code of the fix pass: `(x_top, y_top)` from the registers `(x, y, mask)`. -/
def topInAuto (A : ℕ) : CAuto A 3 4 :=
  absAuto topEnc topDec (false, false) topStep fun s => topCode s.1 s.2

/-- The output code of the fix pass: `(x_top, y_top ⊕ x_top)`. -/
def topOutAuto (A : ℕ) : CAuto A 3 4 :=
  absAuto topEnc topDec (false, false) topStep fun s => topCode s.1 (xor s.2 s.1)

lemma foldl_topStep (x y p : ℕ) :
    ∀ L : ℕ, (List.range L).foldl
        (fun s t => topStep s fun r => ((![x, y, 2 ^ p] : Fin 3 → ℕ) r).testBit t) (false, false) =
      if p < L then (x.testBit p, y.testBit p) else (false, false) := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, topStep]
      simp only [Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.tail_cons,
        Matrix.head_cons, Nat.testBit_two_pow]
      by_cases hpL : p = L
      · subst hpL; simp
      · have h1 : (p < L + 1) = (p < L) := by apply propext; omega
        simp only [hpL, decide_false, Bool.false_eq_true, ↓reduceIte, h1]

lemma topIn_eval {A : ℕ} (L x y p : ℕ) (hp : p < L) :
    (topInAuto A).eval L ![x, y, 2 ^ p] = topCode (x.testBit p) (y.testBit p) := by
  unfold topInAuto
  rw [absAuto_eval _ _ topDec_topEnc, foldl_topStep]
  simp only [hp, ↓reduceIte]

lemma topOut_eval {A : ℕ} (L x y p : ℕ) (hp : p < L) :
    (topOutAuto A).eval L ![x, y,
        2 ^ p] = topCode (x.testBit p) (xor (y.testBit p) (x.testBit p)) := by
  unfold topOutAuto
  rw [absAuto_eval _ _ topDec_topEnc, foldl_topStep]
  simp only [hp, ↓reduceIte]

/-! ### Flipping one bit -/

lemma testBit_one_eq (i : ℕ) : (1 : ℕ).testBit i = decide (i = 0) := by
  rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
  simp [eq_comm]

lemma xor_two_pow_eq (v p : ℕ) : v ^^^ 2 ^ p = 2 ^ p * (v / 2 ^ p ^^^ 1) + v % 2 ^ p := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (by positivity)), Nat.testBit_xor,
    Nat.testBit_two_pow]
  split_ifs with hj
  · rw [Nat.testBit_mod_two_pow]
    simp [hj, show p ≠ j by omega]
  · rw [Nat.testBit_xor, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega), testBit_one_eq]
    congr 1
    simp only [decide_eq_decide]
    omega

/-- Flipping bit `p` adds or subtracts `2^p`. -/
lemma xor_two_pow_int (v p : ℕ) :
    ((v ^^^ 2 ^ p : ℕ) : ℤ) = v + (if v.testBit p then -(2 ^ p : ℤ) else 2 ^ p) := by
  rw [xor_two_pow_eq]
  have hv : v = 2 ^ p * (v / 2 ^ p) + v % 2 ^ p := (Nat.div_add_mod v (2 ^ p)).symm
  have hb : v.testBit p = decide (v / 2 ^ p % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ p) with h | h
  · have he : Even (v / 2 ^ p) := Nat.even_iff.2 h
    rw [Nat.xor_one_of_even he, hb, h]
    simp only [zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte]
    conv_rhs => rw [hv]
    push_cast; ring
  · have ho : Odd (v / 2 ^ p) := Nat.odd_iff.2 h
    have h1 : 1 ≤ v / 2 ^ p := by
      rcases Nat.eq_zero_or_pos (v / 2 ^ p) with h0 | h0
      · rw [h0] at h; simp at h
      · exact h0
    rw [Nat.xor_one_of_odd ho, hb, h]
    simp only [decide_true, ↓reduceIte]
    conv_rhs => rw [hv]
    push_cast [h1]; ring

/-! ### The top fixup on ranks -/

section FixRanks

variable {A N₀ N₁ N₂ N₃ L n₀ n₁ n₂ n₃ rb R : ℕ}

/-- The rank weight of chunk slot `q`. -/
def slotW (N₁ N₂ N₃ L : ℕ) : Fin 3 → ℕ := ![N₃ * 2 ^ L * N₂ * 2 ^ L * N₁, N₃ * 2 ^ L * N₂, N₃]

lemma rank_update (s : Spec N₀ N₁ N₂ N₃) (c : Tri L) (q : Fin 3) (w : Fin (2 ^ L)) :
    (rank N₀ N₁ N₂ N₃ L (s, Function.update c q w) : ℤ) =
      rank N₀ N₁ N₂ N₃ L (s, c) + slotW N₁ N₂ N₃ L q * ((w : ℤ) - (c q : ℤ)) := by
  fin_cases q <;> simp [rank, slotW] <;> ring

/-- The rank change of the top fixup: `y` gains `± 2^p` at the slot of `y` when `x_p = 1`. -/
def fixShift (p : ℕ) (x y : Bool) : ℤ := if x then (if y then -(2 ^ p : ℤ) else 2 ^ p) else 0

lemma topFix_apply_zero (K ρ f : ℕ) (v : Tri L) : topFix L K ρ f v 0 = v 0 := by
  show xorMask L (2 ^ (ρ + (f - 1) * K)) v 0 = _
  simp [xorMask]

lemma topFix_apply_ne (K ρ f : ℕ) (v : Tri L) (k : Fin 3) (hk : k ≠ 1) :
    topFix L K ρ f v k = v k := by
  show xorMask L (2 ^ (ρ + (f - 1) * K)) v k = _
  simp [xorMask, Function.update_of_ne hk]

lemma topFix_apply_one (K ρ f : ℕ) (v : Tri L) :
    ((topFix L K ρ f v 1 : Fin (2 ^ L)) : ℕ) =
      (v 1 : ℕ) ^^^ ((v 0 : ℕ) &&& 2 ^ (ρ + (f - 1) * K)) := by
  show ((xorMask L (2 ^ (ρ + (f - 1) * K)) v 1 : Fin (2 ^ L)) : ℕ) = _
  simp [xorMask]

lemma topFix_testBit (K ρ f : ℕ) (v : Tri L) :
    ((topFix L K ρ f v 1 : Fin (2 ^ L)) : ℕ).testBit (ρ + (f - 1) * K) =
      xor ((v 1 : ℕ).testBit (ρ + (f - 1) * K)) ((v 0 : ℕ).testBit (ρ + (f - 1) * K)) := by
  rw [topFix_apply_one, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow]
  simp

/-- The top fixup on ranks: the rank moves by `slotW (σ⁻¹ 1) · fixShift`. -/
lemma fix_enc (K ρ f : ℕ) (σ : Equiv.Perm (Fin 3)) (a : Addr N₀ N₁ N₂ N₃ L) :
    (enc N₀ N₁ N₂ N₃ L σ (liftA N₀ N₁ N₂ N₃ L (topFix L K ρ f) a) : ℤ) =
      enc N₀ N₁ N₂ N₃ L σ a + slotW N₁ N₂ N₃ L (σ.symm 1) *
        fixShift (ρ + (f - 1) * K) ((a.2 0 : ℕ).testBit (ρ + (f - 1) * K))
          ((a.2 1 : ℕ).testBit (ρ + (f - 1) * K)) := by
  obtain ⟨s, v⟩ := a
  rw [enc_val, enc_val]
  have hphys : phys L σ (topFix L K ρ f v) =
      Function.update (phys L σ v) (σ.symm 1) (topFix L K ρ f v 1) := by
    funext q
    by_cases hq : q = σ.symm 1
    · subst hq; simp [phys]
    · have hσq : σ q ≠ 1 := fun e => hq (by rw [← e, Equiv.symm_apply_apply])
      simp only [phys, Function.comp_apply, Function.update_of_ne hq]
      exact topFix_apply_ne K ρ f v (σ q) hσq
  show (rank N₀ N₁ N₂ N₃ L (s, phys L σ (topFix L K ρ f v)) : ℤ) = _
  rw [hphys, rank_update]
  congr 1
  have hc : (phys L σ v (σ.symm 1) : ℕ) = (v 1 : ℕ) := by simp [phys]
  rw [hc, topFix_apply_one, Nat.and_two_pow]
  unfold fixShift
  cases hx : (v 0 : ℕ).testBit (ρ + (f - 1) * K)
  · simp
  · simp only [Bool.toNat_true, one_mul, ↓reduceIte]
    rw [xor_two_pow_int]
    split_ifs <;> ring

/-- The code-pass sources of the top codes: the field of `x`, the field of `y`, and the mask
`2^p` of the top selected bit. -/
def topSrc (σ : Equiv.Perm (Fin 3)) (p : ℕ) : Fin 3 → Fin 8 ⊕ ℕ :=
  ![.inl (slotF (σ.symm 0)), .inl (slotF (σ.symm 1)), .inr (2 ^ p)]

lemma regVal_topSrc (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (σ : Equiv.Perm (Fin 3)) (p : ℕ)
    (a : Addr N₀ N₁ N₂ N₃ L) :
    regVal (idxLen n₀ n₁ n₂ n₃ L rb) (topSrc σ p) (enc N₀ N₁ N₂ N₃ L σ a) =
      ![((a.2 0 : Fin (2 ^ L)) : ℕ), ((a.2 1 : Fin (2 ^ L)) : ℕ), 2 ^ p] := by
  funext r
  fin_cases r <;> simp [regVal, topSrc, digit_enc_name hN₀ hR hN₁ hN₂ hN₃]

lemma idxCode_topIn (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (σ : Equiv.Perm (Fin 3)) {p : ℕ} (hp : p < L)
    (a : Addr N₀ N₁ N₂ N₃ L) :
    idxCode (topInAuto A) L (idxLen n₀ n₁ n₂ n₃ L rb) (topSrc σ p) (enc N₀ N₁ N₂ N₃ L σ a) =
      topCode ((a.2 0 : ℕ).testBit p) ((a.2 1 : ℕ).testBit p) := by
  rw [idxCode, regVal_topSrc hN₀ hR hN₁ hN₂ hN₃, topIn_eval _ _ _ _ hp]

lemma idxCode_topOut (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) (σ : Equiv.Perm (Fin 3)) {p : ℕ} (hp : p < L)
    (a : Addr N₀ N₁ N₂ N₃ L) :
    idxCode (topOutAuto A) L (idxLen n₀ n₁ n₂ n₃ L rb) (topSrc σ p) (enc N₀ N₁ N₂ N₃ L σ a) =
      topCode ((a.2 0 : ℕ).testBit p) (xor ((a.2 1 : ℕ).testBit p) ((a.2 0 : ℕ).testBit p)) := by
  rw [idxCode, regVal_topSrc hN₀ hR hN₁ hN₂ hN₃, topOut_eval _ _ _ _ hp]

end FixRanks

/-! ### Merging along a permutation of ranks -/

section FixLists

variable {α : Type} {nd : ℕ}

/-- Matched codes have equal counts. -/
lemma idxCount_perm {M : ℕ} (π : Equiv.Perm (Fin M)) (cin cout : ℕ → Fin nd)
    (hcode : ∀ i : Fin M, cout (π i) = cin i) (d : Fin nd) :
    idxCount cout 0 M d = idxCount cin 0 M d := by
  have hfin : ∀ code : ℕ → Fin nd, idxCount code 0 M d =
      ((List.finRange M).filter fun (i : Fin M) => code (i : ℕ) = d).length := by
    intro code
    rw [idxCount, ← List.map_coe_finRange_eq_range, List.filter_map, List.length_map]
    simp [Function.comp_def]
  rw [hfin, hfin]
  have hperm : ((List.finRange M).filter fun (i : Fin M) => cout (i : ℕ) = d).Perm
      (((List.finRange M).filter fun (i : Fin M) => cin (i : ℕ) = d).map π) := by
    rw [List.perm_ext_iff_of_nodup ((List.nodup_finRange M).filter _)
      (((List.nodup_finRange M).filter _).map π.injective)]
    intro i
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, List.mem_map]
    constructor
    · intro h
      exact ⟨π.symm i, by rw [← hcode, Equiv.apply_symm_apply, h], by simp⟩
    · rintro ⟨j, hj, rfl⟩
      rw [hcode, hj]
  rw [hperm.length_eq, List.length_map]

lemma idxCount_le (code : ℕ → Fin nd) (j m : ℕ) (d : Fin nd) : idxCount code j m d ≤ m := by
  unfold idxCount
  exact (List.length_filter_le _ _).trans (by simp)

/-- Routing by `cin` and merging by `cout`, with `cout ∘ π = cin` and `π` increasing on each
code class, moves the records by `π`. -/
lemma mergeIdxList_moveRecs {M B : ℕ} (π : Equiv.Perm (Fin M)) (l : List (List α))
    (hl : l.length = M) (hlB : ∀ r ∈ l, r.length = B) (cin cout : ℕ → Fin nd)
    (hcode : ∀ i : Fin M, cout (π i) = cin i)
    (hmono : ∀ i i' : Fin M, cin i = cin i' → i < i' → π i < π i') :
    mergeIdxList B cout M 0 (fun d => blocksIdx l.flatten B M cin 0 d ++ []) =
      ((moveRecs π l).flatten, fun _ => []) := by
  let πN : ℕ → ℕ := fun n => if h : n < M then (π ⟨n, h⟩ : ℕ) else n
  let σN : ℕ → ℕ := fun n => if h : n < M then (π.symm ⟨n, h⟩ : ℕ) else n
  have hπN : ∀ (i : Fin M), πN i = π i := fun i => by simp [πN]
  have hσN : ∀ (i : Fin M), σN i = π.symm i := fun i => by simp [σN]
  have hlen : l.flatten.length = M * B := by rw [← hl]; exact length_flatten_of_length l hlB
  have hg : ∀ j < M, (l.getD j []).length = B := fun j hj => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hlB _ (List.getElem_mem _)
  have hflat : l.flatten = (List.range M).flatMap fun n => l.getD n [] := by
    rw [List.flatMap_def, ← hl, map_getD_range]
  have h := mergeIdxList_perm B M l.flatten hlen cin cout 0 0 πN σN
    (fun n hn => by rw [show n = ((⟨n, hn⟩ : Fin M) : ℕ) from rfl, hπN]; exact (π _).isLt)
    (fun n hn => by rw [show n = ((⟨n, hn⟩ : Fin M) : ℕ) from rfl, hσN]; exact (π.symm _).isLt)
    (fun n hn => by
      rw [show n = ((⟨n, hn⟩ : Fin M) : ℕ) from rfl, hπN, hσN, Equiv.symm_apply_apply])
    (fun n hn => by
      rw [show n = ((⟨n, hn⟩ : Fin M) : ℕ) from rfl, hσN, hπN, Equiv.apply_symm_apply])
    (fun n hn => by
      rw [Nat.zero_add, Nat.zero_add, show n = ((⟨n, hn⟩ : Fin M) : ℕ) from rfl, hπN]
      exact hcode _)
    (fun n hn n' hn' hc hlt => by
      rw [show n = ((⟨n, hn⟩ : Fin M) : ℕ) from rfl, show n' = ((⟨n', hn'⟩ : Fin M) : ℕ) from rfl,
        hπN, hπN]
      exact hmono ⟨n, hn⟩ ⟨n', hn'⟩ (by simpa using hc) hlt)
    (fun _ => [])
  rw [h]
  simp only [Prod.mk.injEq, and_true]
  rw [moveRecs, ofFn_eq_range_map _ (fun j => l.getD (σN j) []) (fun j => by rw [hσN]),
    ← List.flatMap_def]
  refine List.flatMap_congr fun j hj => ?_
  have hj' := List.mem_range.1 hj
  have hσj : σN j < M := by
    rw [show j = ((⟨j, hj'⟩ : Fin M) : ℕ) from rfl, hσN]; exact (π.symm _).isLt
  rw [hflat]
  exact blk_flatMap_range M hg _ hσj

end FixLists

/-! ### The fix machine -/

section FixMachine

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {nf : ℕ}

/-- The fix pass on generic code registers: route by the input code `Cin` into `r0, …, r3`,
restore forward order into `q0, …, q3`, reset the counter, merge by the output code `Cout` into
`r0` (counted by `cnt`, temporary `r1`), move the result back into `src`, reset the counter. -/
def fixAt (src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp st : Fin T) (cf : Fin nf → Fin T)
    (rs us : Fin 3 → Fin T) (Cin Cout : CAuto A 3 4) : Pr P T Q A U :=
  .seq (routeIdx src ![r0, r1, r2, r3] ctrB tmp cf rs us st Cin)
    (.seq (moveR r0 q0 id) (.seq (moveR r1 q1 id) (.seq (moveR r2 q2 id) (.seq (moveR r3 q3 id)
      (.seq (resetFields cf tmp)
        (.seq (mergeIdx ![q0, q1, q2, q3] r0 ctrB tmp cnt r1 cf rs us st Cout)
          (.seq (moveR r0 src id) (resetFields cf tmp))))))))

/-- Register facts of the fix machine. -/
structure FixLayout (src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp st : Fin T) (cf : Fin nf → Fin T)
    (len : Fin nf → ℕ) (L : ℕ) (rs us : Fin 3 → Fin T) (rsrc : Fin 3 → Fin nf ⊕ ℕ) : Prop where
  route : IdxLayout cf len L rs us rsrc st (routeRegs src ![r0, r1, r2, r3] ctrB tmp)
  merge : IdxLayout cf len L rs us rsrc st (mergeRegs ![q0, q1, q2, q3] r0 ctrB tmp cnt r1)
  regs : [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp].Nodup
  cf_regs : ∀ f, cf f ∉ [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp]
  us_regs : ∀ r, us r ∉ [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp]

/-- **The fix machine.** The register `src` holds the `M` records `l` of `B ≥ 1` symbols and the
counter is at index `0`. If the input code `cin` and output code `cout` have equal counts and the
list merge of the routed records is `(out, [])`, then `src` ends holding `out`; every other register
ends as it started. -/
theorem fixAt_exec {src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp st : Fin T} {cf : Fin nf → Fin T}
    {len : Fin nf → ℕ} {L : ℕ} {rs us : Fin 3 → Fin T} {rsrc : Fin 3 → Fin nf ⊕ ℕ}
    (h : FixLayout src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp st cf len L rs us rsrc)
    (Cin Cout : CAuto A 3 4) {B M : ℕ} (hB : 1 ≤ B) (l : List (List (Fin (A + 4))))
    (hl : l.length = M) (hlB : ∀ r ∈ l, r.length = B)
    (hcount : ∀ d, idxCount (idxCode Cout L len rsrc) 0 M d =
      idxCount (idxCode Cin L len rsrc) 0 M d)
    (out : List (Fin (A + 4))) (hout : out.length = M * B)
    (hmerge : mergeIdxList B (idxCode Cout L len rsrc) M 0
      (fun d => blocksIdx l.flatten B M (idxCode Cin L len rsrc) 0 d ++ []) = (out, fun _ => []))
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = l.flatten)
    (hr0 : S.R r0 = []) (hr1 : S.R r1 = []) (hr2 : S.R r2 = []) (hr3 : S.R r3 = [])
    (hq0 : S.R q0 = []) (hq1 : S.R q1 = []) (hq2 : S.R q2 = []) (hq3 : S.R q3 = [])
    (hctr : (S.R ctrB).length = B) (hcnt : (S.R cnt).length = M) (htmp : S.R tmp = [])
    (hI : IdxState cf len L rs us rsrc S.R 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ M * (18 * B + 12 * L + 8 * (∑ f, len f) + 8 * nf + 28) + 8 * (∑ f, len f) + 8 * nf + 18 ∧
      Exec body (fixAt src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp st cf rs us Cin Cout) (mk v S) m
        (mk v' { S with R := (Function.update S.R src out) }) := by
  have hregs := h.regs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hregs
  obtain ⟨⟨n_src_r0, n_src_r1, n_src_r2, n_src_r3, n_src_q0, n_src_q1, n_src_q2, n_src_q3,
      n_src_ctrB, n_src_cnt, n_src_tmp⟩, ⟨n_r0_r1, n_r0_r2, n_r0_r3, n_r0_q0, n_r0_q1, n_r0_q2,
      n_r0_q3, n_r0_ctrB, n_r0_cnt, n_r0_tmp⟩, ⟨n_r1_r2, n_r1_r3, n_r1_q0, n_r1_q1, n_r1_q2,
      n_r1_q3, n_r1_ctrB, n_r1_cnt, n_r1_tmp⟩, ⟨n_r2_r3, n_r2_q0, n_r2_q1, n_r2_q2, n_r2_q3,
      n_r2_ctrB, n_r2_cnt, n_r2_tmp⟩, ⟨n_r3_q0, n_r3_q1, n_r3_q2, n_r3_q3, n_r3_ctrB, n_r3_cnt,
      n_r3_tmp⟩, ⟨n_q0_q1, n_q0_q2, n_q0_q3, n_q0_ctrB, n_q0_cnt, n_q0_tmp⟩, ⟨n_q1_q2, n_q1_q3,
      n_q1_ctrB, n_q1_cnt, n_q1_tmp⟩, ⟨n_q2_q3, n_q2_ctrB, n_q2_cnt, n_q2_tmp⟩, ⟨n_q3_ctrB,
      n_q3_cnt, n_q3_tmp⟩, ⟨n_ctrB_cnt, n_ctrB_tmp⟩, n_cnt_tmp⟩ := hregs
  have hcf : ∀ f x, x ∈ [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp] → cf f ≠ x :=
    fun f x hx e => h.cf_regs f (e ▸ hx)
  have hus : ∀ r x, x ∈ [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp] → us r ≠ x :=
    fun r x hx e => h.us_regs r (e ▸ hx)
  have hcfinj : Function.Injective cf := h.route.cf_inj
  have hcftmp : ∀ f, cf f ≠ tmp := fun f => hcf f tmp (by simp)
  set cin := idxCode Cin L len rsrc with hcin
  set cout := idxCode Cout L len rsrc with hcout
  set blks : Fin 4 → List (Fin (A + 4)) := fun d => blocksIdx l.flatten B M cin 0 d with hblks
  have hlf : l.flatten.length = M * B := by rw [← hl]; exact length_flatten_of_length l hlB
  have hblen : ∀ d, (blks d).length ≤ M * B := fun d => by
    simp only [hblks]
    rw [length_blocksIdx cin B M 0 l.flatten d hlf]
    exact Nat.mul_le_mul_right B (idxCount_le cin 0 M d)
  let Oth : Fin T → Prop := fun x => x ≠ src ∧ x ≠ r0 ∧ x ≠ r1 ∧ x ≠ r2 ∧ x ≠ r3 ∧ x ≠ q0 ∧
    x ≠ q1 ∧ x ≠ q2 ∧ x ≠ q3 ∧ ∀ f, cf f ≠ x
  -- stage 1: route
  obtain ⟨v₁, R₁, hu₁, he₁, hsrc₁, hdst₁, hcf₁, hoth₁⟩ := routeIdx_exec body src ![r0, r1, r2, r3]
    ctrB tmp cf len L rs us rsrc st Cin h.route
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]; exact ⟨⟨n_src_ctrB, n_src_tmp⟩, n_ctrB_tmp⟩)
    (by intro d; fin_cases d <;> simp [(Ne.symm n_src_r0), n_r0_ctrB, n_r0_tmp, (Ne.symm n_src_r1),
        n_r1_ctrB, n_r1_tmp, (Ne.symm n_src_r2), n_r2_ctrB, n_r2_tmp, (Ne.symm n_src_r3),
        n_r3_ctrB, n_r3_tmp])
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
        | rfl
        | (exfalso; revert hij
           simp [n_r0_r1, n_r0_r2, n_r0_r3, (Ne.symm n_r0_r1), n_r1_r2, n_r1_r3,
             (Ne.symm n_r0_r2), (Ne.symm n_r1_r2), n_r2_r3, (Ne.symm n_r0_r3),
             (Ne.symm n_r1_r3), (Ne.symm n_r2_r3)]))
    (l := l.flatten) (c := S.R ctrB) (nb := M) (B := B) (i₀ := 0) hB hlf hctr v S hsrc rfl htmp hI
  have hR₁ : ∀ x, Oth x → R₁ x = S.R x := fun x hx =>
    hoth₁ x hx.1 (fun d => by fin_cases d <;> simp [Ne.symm hx.2.1, Ne.symm hx.2.2.1,
      Ne.symm hx.2.2.2.1, Ne.symm hx.2.2.2.2.1]) hx.2.2.2.2.2.2.2.2.2
  have hR₁r : ∀ d, R₁ (![r0, r1, r2, r3] d) = (blks d).reverse := fun d => by
    rw [hdst₁ d]
    fin_cases d <;> simp [hblks, hcin, hr0, hr1, hr2, hr3]
  have hR₁q : ∀ x, x = q0 ∨ x = q1 ∨ x = q2 ∨ x = q3 → R₁ x = [] := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [hoth₁ _ (Ne.symm n_src_q0) (fun d => by fin_cases d <;> simp [n_r0_q0, 
        n_r1_q0, n_r2_q0, n_r3_q0]) (fun f => hcf f _ (by simp)), hq0]
    · rw [hoth₁ _ (Ne.symm n_src_q1) (fun d => by fin_cases d <;> simp [n_r0_q1, 
        n_r1_q1, n_r2_q1, 
        n_r3_q1]) (fun f => hcf f _ (by simp)), hq1]
    · rw [hoth₁ _ (Ne.symm n_src_q2) (fun d => by fin_cases d <;> simp [n_r0_q2,
        n_r1_q2, n_r2_q2, 
        n_r3_q2]) (fun f => hcf f _ (by simp)), hq2]
    · rw [hoth₁ _ (Ne.symm n_src_q3) (fun d => by fin_cases d <;> simp [
        n_r0_q3, n_r1_q3, n_r2_q3, 
        n_r3_q3]) (fun f => hcf f _ (by simp)), hq3]

  -- stages 2 to 5: forward order
  have hmv : ∀ (R : Fin T → List (Fin (A + 4))) (i j x : Fin T), x ≠ i → x ≠ j →
      movedR R i j id (R i) x = R x := fun R i j x h1 h2 => by simp [movedR, h1, h2]
  have hmvs : ∀ (R : Fin T → List (Fin (A + 4))) (i j : Fin T), i ≠ j →
      movedR R i j id (R i) i = [] := fun R i j h => by simp [movedR, h]
  have hmvd : ∀ (R : Fin T → List (Fin (A + 4))) (i j : Fin T),
      movedR R i j id (R i) j = (R i).reverse ++ R j := fun R i j => by simp [movedR]
  have hR₁r0 : R₁ r0 = (blks 0).reverse := hR₁r 0
  have hR₁r1 : R₁ r1 = (blks 1).reverse := hR₁r 1
  have hR₁r2 : R₁ r2 = (blks 2).reverse := hR₁r 2
  have hR₁r3 : R₁ r3 = (blks 3).reverse := hR₁r 3
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body r0 q0 n_r0_q0 id v₁ { S with R := R₁ }
  set R₂ := movedR R₁ r0 q0 id (R₁ r0) with hR₂
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body r1 q1 n_r1_q1 id v₂ { S with R := R₂ }
  set R₃ := movedR R₂ r1 q1 id (R₂ r1) with hR₃
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body r2 q2 n_r2_q2 id v₃ { S with R := R₃ }
  set R₄ := movedR R₃ r2 q2 id (R₃ r2) with hR₄
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body r3 q3 n_r3_q3 id v₄ { S with R := R₄ }
  set R₅ := movedR R₄ r3 q3 id (R₄ r3) with hR₅
  have hR₅f : ∀ x, x ≠ r0 → x ≠ r1 → x ≠ r2 → x ≠ r3 → x ≠ q0 → x ≠ q1 → x ≠ q2 → x ≠ q3 →
      R₅ x = R₁ x := fun x a0 a1 a2 a3 b0 b1 b2 b3 => by
    rw [hR₅, hmv _ _ _ _ a3 b3, hR₄, hmv _ _ _ _ a2 b2, hR₃, hmv _ _ _ _ a1 b1, hR₂,
      hmv _ _ _ _ a0 b0]
  have hR₂r1 : R₂ r1 = (blks 1).reverse := by rw [hR₂, hmv _ _ _ _ (Ne.symm n_r0_r1) n_r1_q0, hR₁r1]
  have hR₃r2 : R₃ r2 = (blks 2).reverse := by
    rw [hR₃, hmv _ _ _ _ (Ne.symm n_r1_r2) n_r2_q1, hR₂, hmv _ _ _ _ (Ne.symm n_r0_r2) n_r2_q0,
        hR₁r2]
  have hR₄r3 : R₄ r3 = (blks 3).reverse := by
    rw [hR₄, hmv _ _ _ _ (Ne.symm n_r2_r3) n_r3_q2, hR₃, hmv _ _ _ _ (Ne.symm n_r1_r3) n_r3_q1, hR₂,
      hmv _ _ _ _ (Ne.symm n_r0_r3) n_r3_q0, hR₁r3]
  have hR₅q0 : R₅ q0 = blks 0 := by
    rw [hR₅, hmv _ _ _ _ (Ne.symm n_r3_q0) n_q0_q3, hR₄, hmv _ _ _ _ (Ne.symm n_r2_q0) n_q0_q2, hR₃,
      hmv _ _ _ _ (Ne.symm n_r1_q0) n_q0_q1, hR₂, hmvd, hR₁r0, hR₁q _ (Or.inl rfl)]
    simp
  have hR₅q1 : R₅ q1 = blks 1 := by
    rw [hR₅, hmv _ _ _ _ (Ne.symm n_r3_q1) n_q1_q3, hR₄, hmv _ _ _ _ (Ne.symm n_r2_q1) n_q1_q2,
        hR₃, hmvd,
      hR₂r1, hR₂, hmv _ _ _ _ (Ne.symm n_r0_q1) (Ne.symm n_q0_q1), hR₁q _ (Or.inr (Or.inl rfl))]
    simp
  have hR₅q2 : R₅ q2 = blks 2 := by
    rw [hR₅, hmv _ _ _ _ (Ne.symm n_r3_q2) n_q2_q3, hR₄, hmvd, hR₃r2, hR₃,
        hmv _ _ _ _ (Ne.symm n_r1_q2) (Ne.symm n_q1_q2),
      hR₂, hmv _ _ _ _ (Ne.symm n_r0_q2) (Ne.symm n_q0_q2), hR₁q _ (Or.inr (Or.inr (Or.inl rfl)))]
    simp
  have hR₅q3 : R₅ q3 = blks 3 := by
    rw [hR₅, hmvd, hR₄r3, hR₄, hmv _ _ _ _ (Ne.symm n_r2_q3) (Ne.symm n_q2_q3), hR₃,
        hmv _ _ _ _ (Ne.symm n_r1_q3) (Ne.symm n_q1_q3),
      hR₂, hmv _ _ _ _ (Ne.symm n_r0_q3) (Ne.symm n_q0_q3), hR₁q _ (Or.inr (Or.inr (Or.inr rfl)))]
    simp
  have hR₅r0 : R₅ r0 = [] := by
    rw [hR₅, hmv _ _ _ _ n_r0_r3 n_r0_q3, hR₄, hmv _ _ _ _ n_r0_r2 n_r0_q2, hR₃,
      hmv _ _ _ _ n_r0_r1 n_r0_q1, hR₂, hmvs _ _ _ n_r0_q0]
  have hR₅r1 : R₅ r1 = [] := by
    rw [hR₅, hmv _ _ _ _ n_r1_r3 n_r1_q3, hR₄, hmv _ _ _ _ n_r1_r2 n_r1_q2, hR₃,
      hmvs _ _ _ n_r1_q1]
  have hR₅r2 : R₅ r2 = [] := by
    rw [hR₅, hmv _ _ _ _ n_r2_r3 n_r2_q3, hR₄, hmvs _ _ _ n_r2_q2]
  have hR₅r3 : R₅ r3 = [] := by rw [hR₅, hmvs _ _ _ n_r3_q3]
  have hO₅ : ∀ x, Oth x → R₅ x = S.R x := fun x hx => by
    rw [hR₅f x hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1
      hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1, hR₁ x hx]
  have hOtmp : Oth tmp := ⟨(Ne.symm n_src_tmp), (Ne.symm n_r0_tmp), (Ne.symm n_r1_tmp),
      (Ne.symm n_r2_tmp), (Ne.symm n_r3_tmp), (Ne.symm n_q0_tmp), (Ne.symm n_q1_tmp),
      (Ne.symm n_q2_tmp), (Ne.symm n_q3_tmp), fun f => hcf f tmp (by simp)⟩
  have hOctr : Oth ctrB := ⟨(Ne.symm n_src_ctrB), (Ne.symm n_r0_ctrB), (Ne.symm n_r1_ctrB),
      (Ne.symm n_r2_ctrB), (Ne.symm n_r3_ctrB), (Ne.symm n_q0_ctrB), (Ne.symm n_q1_ctrB),
      (Ne.symm n_q2_ctrB), (Ne.symm n_q3_ctrB), fun f => hcf f ctrB (by simp)⟩
  have hOcnt : Oth cnt := ⟨(Ne.symm n_src_cnt), (Ne.symm n_r0_cnt), (Ne.symm n_r1_cnt),
      (Ne.symm n_r2_cnt), (Ne.symm n_r3_cnt), (Ne.symm n_q0_cnt), (Ne.symm n_q1_cnt),
      (Ne.symm n_q2_cnt), (Ne.symm n_q3_cnt), fun f => hcf f cnt (by simp)⟩
  have hOus : ∀ r, Oth (us r) := fun r =>
    ⟨hus r src (by simp), hus r r0 (by simp), hus r r1 (by simp), hus r r2 (by simp),
      hus r r3 (by simp), hus r q0 (by simp), hus r q1 (by simp), hus r q2 (by simp),
      hus r q3 (by simp), fun f e => h.route.tmps_cf r f e.symm⟩
  -- stage 6: reset
  obtain ⟨v₆, R₆, hu₆, he₆, hcf₆, hoth₆⟩ := resetFields_exec body cf hcfinj tmp hcftmp len v₅
    { S with R := R₅ } (by show R₅ tmp = []; rw [hO₅ _ hOtmp, htmp])
    (fun f => by
      show (R₅ (cf f)).length = _
      rw [hR₅f _ (hcf f r0 (by simp)) (hcf f r1 (by simp)) (hcf f r2 (by simp))
        (hcf f r3 (by simp)) (hcf f q0 (by simp)) (hcf f q1 (by simp)) (hcf f q2 (by simp))
        (hcf f q3 (by simp)), hcf₁ f]
      simp)
  have hR₆f : ∀ x, (∀ f, x ≠ cf f) → R₆ x = R₅ x := hoth₆
  have hdig0 : ∀ f, digit len f 0 = 0 := fun f => by simp [digit]
  have hOrs : ∀ r p, rsrc r = .inr p → Oth (rs r) := fun r p hr =>
    ⟨fun e => h.route.rs_X r (Or.inl e),
      fun e => h.merge.rs_X r (Or.inl e),
      fun e => h.merge.rs_X r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))),
      fun e => h.route.rs_X r (Or.inr (Or.inr (Or.inr ⟨2, e.symm⟩))),
      fun e => h.route.rs_X r (Or.inr (Or.inr (Or.inr ⟨3, e.symm⟩))),
      fun e => h.merge.rs_X r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨0, e.symm⟩))))),
      fun e => h.merge.rs_X r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨1, e.symm⟩))))),
      fun e => h.merge.rs_X r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨2, e.symm⟩))))),
      fun e => h.merge.rs_X r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨3, e.symm⟩))))),
      fun f e => h.route.param r p f hr e.symm⟩
  have hI₆ : IdxState cf len L rs us rsrc R₆ 0 :=
    ⟨fun f => by rw [hcf₆ f, hdig0],
      fun r p hr => by
        rw [hR₆f _ (fun f e => (hOrs r p hr).2.2.2.2.2.2.2.2.2 f e.symm), hO₅ _ (hOrs r p hr),
          hI.2.1 r p hr],
      fun r => by
        rw [hR₆f _ (fun f e => (hOus r).2.2.2.2.2.2.2.2.2 f e.symm), hO₅ _ (hOus r), hI.2.2 r]⟩
  -- stage 7: merge
  obtain ⟨v₇, R₇, hu₇, he₇, hdst₇, hsrcs₇, hcf₇, hoth₇⟩ := mergeIdx_exec body ![q0, q1, q2, q3] r0
    ctrB tmp cnt r1 cf len L rs us rsrc st Cout h.merge
    (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨n_r0_ctrB, n_r0_tmp, n_r0_cnt, n_r0_r1⟩, ⟨n_ctrB_tmp, n_ctrB_cnt,
          (Ne.symm n_r1_ctrB)⟩, ⟨(Ne.symm n_cnt_tmp), (Ne.symm n_r1_tmp)⟩, (Ne.symm n_r1_cnt)⟩)
    (by intro d; fin_cases d <;> simp [(Ne.symm n_r0_q0), n_q0_ctrB, n_q0_tmp, n_q0_cnt,
        (Ne.symm n_r1_q0), (Ne.symm n_r0_q1), n_q1_ctrB, n_q1_tmp, n_q1_cnt, (Ne.symm n_r1_q1),
        (Ne.symm n_r0_q2), n_q2_ctrB, n_q2_tmp, n_q2_cnt, (Ne.symm n_r1_q2), (Ne.symm n_r0_q3),
        n_q3_ctrB, n_q3_tmp, n_q3_cnt, (Ne.symm n_r1_q3)])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> first | rfl |
      (exfalso; revert hij; simp [n_q0_q1, n_q0_q2, n_q0_q3, (Ne.symm n_q0_q1), n_q1_q2, n_q1_q3,
          (Ne.symm n_q0_q2), (Ne.symm n_q1_q2), n_q2_q3, (Ne.symm n_q0_q3), (Ne.symm n_q1_q3),
          (Ne.symm n_q2_q3)]))
    (c := S.R ctrB) (kk := S.R cnt) (nb := M) (B := B) (i₀ := 0) hctr hcnt
    (fun d => blks d ++ [])
    (fun d => by
      rw [List.append_nil, hcount d]
      simp only [hblks]
      rw [length_blocksIdx cin B M 0 l.flatten d hlf])
    v₆ { S with R := R₆ }
    (fun d => by
      show R₆ (![q0, q1, q2, q3] d) = blks d ++ []
      rw [List.append_nil]
      fin_cases d
      · show R₆ q0 = blks 0
        rw [hR₆f _ (fun f e => hcf f q0 (by simp) e.symm), hR₅q0]
      · show R₆ q1 = blks 1
        rw [hR₆f _ (fun f e => hcf f q1 (by simp) e.symm), hR₅q1]
      · show R₆ q2 = blks 2
        rw [hR₆f _ (fun f e => hcf f q2 (by simp) e.symm), hR₅q2]
      · show R₆ q3 = blks 3
        rw [hR₆f _ (fun f e => hcf f q3 (by simp) e.symm), hR₅q3])
    (by show R₆ ctrB = _; rw [hR₆f _ (fun f e => hcf f ctrB (by simp) e.symm), hO₅ _ hOctr])
    (by show R₆ tmp = _; rw [hR₆f _ (fun f e => hcftmp f e.symm), hO₅ _ hOtmp, htmp])
    (by show R₆ cnt = _; rw [hR₆f _ (fun f e => hcf f cnt (by simp) e.symm), hO₅ _ hOcnt])
    (by show R₆ r1 = _; rw [hR₆f _ (fun f e => hcf f r1 (by simp) e.symm), hR₅r1])
    hI₆
  rw [hmerge] at hdst₇ hsrcs₇
  have hR₇f : ∀ x, x ≠ r0 → x ≠ q0 → x ≠ q1 → x ≠ q2 → x ≠ q3 → (∀ f, cf f ≠ x) →
      R₇ x = R₆ x := fun x h0 h1 h2 h3 h4 h5 =>
    hoth₇ x h0 (fun d => by fin_cases d <;> simp [Ne.symm h1, Ne.symm h2, Ne.symm h3,
        Ne.symm h4]) h5
  have hR₇r0 : R₇ r0 = out.reverse := by
    rw [hdst₇]
    show out.reverse ++ R₆ r0 = _
    rw [hR₆f _ (fun f e => hcf f r0 (by simp) e.symm), hR₅r0, List.append_nil]
  have hR₇src : R₇ src = [] := by
    rw [hR₇f _ n_src_r0 n_src_q0 n_src_q1 n_src_q2 n_src_q3 (fun f => hcf f src (by simp)),
      hR₆f _ (fun f e => hcf f src (by simp) e.symm),
      hR₅f _ n_src_r0 n_src_r1 n_src_r2 n_src_r3 n_src_q0 n_src_q1 n_src_q2 n_src_q3,
      hsrc₁]
  -- stage 8: back into src
  obtain ⟨v₈, hu₈, he₈⟩ := moveR_exec body r0 src (Ne.symm n_src_r0) id v₇ { S with R := R₇ }
  set R₈ := movedR R₇ r0 src id (R₇ r0) with hR₈
  -- stage 9: reset
  obtain ⟨v₉, R₉, hu₉, he₉, hcf₉, hoth₉⟩ := resetFields_exec body cf hcfinj tmp hcftmp len v₈
    { S with R := R₈ }
    (by
      show R₈ tmp = []
      rw [hR₈, hmv _ _ _ _ (Ne.symm n_r0_tmp) (Ne.symm n_src_tmp),
        hR₇f _ (Ne.symm n_r0_tmp) (Ne.symm n_q0_tmp) (Ne.symm n_q1_tmp) (Ne.symm n_q2_tmp)
          (Ne.symm n_q3_tmp) (fun f => hcftmp f),
        hR₆f _ (fun f e => hcftmp f e.symm), hO₅ _ hOtmp, htmp])
    (fun f => by
      show (R₈ (cf f)).length = _
      rw [hR₈, hmv _ _ _ _ (hcf f r0 (by simp)) (hcf f src (by simp)), hcf₇ f]
      simp)
  refine ⟨v₉, _, by rw [hu₉, hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅
      (Exec.seq he₆ (Exec.seq he₇ (Exec.seq he₈ he₉)))))))) rfl ?_⟩
  · simp only [hR₁r0, hR₂r1, hR₃r2, hR₄r3, hR₇r0, List.length_reverse, hout]
    have h0 := hblen 0
    have h1 := hblen 1
    have h2 := hblen 2
    have h3 := hblen 3
    nlinarith [h0, h1, h2, h3]
  · congr 2
    funext x
    show R₉ x = _
    by_cases hxf : ∃ f, x = cf f
    · obtain ⟨f, rfl⟩ := hxf
      rw [hcf₉ f, Function.update_of_ne (hcf f src (by simp)), hI.1 f, hdig0]
    simp only [not_exists] at hxf
    rw [hoth₉ x hxf]
    show R₈ x = _
    rw [hR₈]
    by_cases hxs : x = src
    · subst hxs; rw [hmvd, hR₇r0, hR₇src]; simp
    by_cases hx0 : x = r0
    · subst hx0; rw [hmvs _ _ _ (Ne.symm n_src_r0), Function.update_of_ne (Ne.symm n_src_r0), hr0]
    rw [hmv _ _ _ _ hx0 hxs, Function.update_of_ne hxs]
    by_cases hq : x = q0 ∨ x = q1 ∨ x = q2 ∨ x = q3
    · rcases hq with rfl | rfl | rfl | rfl
      · have := hsrcs₇ 0; simp only [Matrix.cons_val_zero] at this; rw [this, hq0]
      · have := hsrcs₇ 1; simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
        rw [this, hq1]
      · have := hsrcs₇ 2
        simp only [Matrix.cons_val_two, 
          Matrix.tail_cons, Matrix.head_cons] at this
        rw [this, hq2]
      · have := hsrcs₇ 3
        simp only [Matrix.cons_val_three, 
          Matrix.tail_cons, Matrix.head_cons] at this
        rw [this, hq3]
    simp only [not_or] at hq
    obtain ⟨hq0', hq1', hq2', hq3'⟩ := hq
    rw [hR₇f x hx0 hq0' hq1' hq2' hq3' (fun f e => hxf f e.symm), hR₆f x hxf]
    by_cases hx1 : x = r1
    · subst hx1; rw [hR₅r1, hr1]
    by_cases hx2 : x = r2
    · subst hx2; rw [hR₅r2, hr2]
    by_cases hx3 : x = r3
    · subst hx3; rw [hR₅r3, hr3]
    exact hO₅ x ⟨hxs, hx0, hx1, hx2, hx3, hq0', hq1', hq2', hq3', fun f e => hxf f e.symm⟩

end FixMachine

/-! ### The fix pass on the rectangle -/

section FixMain

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
  {N₀ N₁ N₂ N₃ L n₀ n₁ n₂ n₃ rb R : ℕ}

/-- **The fix pass** for physical order `σ`: `fixAt` with the codes `(x_p, y_p)` and
`(x_p, y_p ⊕ x_p)` of the top selected bit `p = ρ + (f - 1) K`, read from the field of `x`, the
field of `y` and the mask register `tm`. -/
def fixPass (σ : Equiv.Perm (Fin 3)) (src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp tm st : Fin T)
    (cf : Fin 8 → Fin T) (us : Fin 3 → Fin T) : Pr P T Q A U :=
  fixAt src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp st cf
    ![cf (slotF (σ.symm 0)), cf (slotF (σ.symm 1)), tm] us (topInAuto A) (topOutAuto A)

/-- **Fix pass.** On the stream `l` of `M = rectSize` records of `B ≥ 1` symbols in `src`, with the
field counter at index `0`, the mask `2^(ρ + (f-1) K)` in `tm`, `ctrB`, `cnt` holding `B` and `M`
symbols, and empty `r0, …, r3`, `q0, …, q3`, `tmp`, `us`, the fix pass moves the record at
`enc σ a` to `enc σ (topFix a)`: `src` ends holding `(moveRecs π_F l).flatten` with
`π_F = addrPerm σ (topFix L K ρ f)`, and every other register ends as it started. At most
`92 M (B + k + 1) + 8 k + 82` steps. -/
theorem fixPass_exec (hN₀ : N₀ = R * 2 ^ n₀) (hR : R ≤ 2 ^ rb) (hN₁ : N₁ = 2 ^ n₁)
    (hN₂ : N₂ = 2 ^ n₂) (hN₃ : N₃ = 2 ^ n₃) {K ρ f : ℕ} (hρ : ρ < K) (hL : L = f * K)
    (hf : 1 ≤ f) (σ : Equiv.Perm (Fin 3))
    {src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp tm st : Fin T} {cf : Fin 8 → Fin T}
    {us : Fin 3 → Fin T}
    (hreg : ([src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp] ++ [tm] ++ List.ofFn us ++
      List.ofFn cf).Nodup)
    (hst : st ∉ [tm] ++ List.ofFn us ++ List.ofFn cf) {B : ℕ} (hB : 1 ≤ B)
    (l : List (List (Fin (A + 4)))) (hl : l.length = rectSize N₀ N₁ N₂ N₃ L)
    (hlB : ∀ r ∈ l, r.length = B) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = l.flatten)
    (hr0 : S.R r0 = []) (hr1 : S.R r1 = []) (hr2 : S.R r2 = []) (hr3 : S.R r3 = [])
    (hq0 : S.R q0 = []) (hq1 : S.R q1 = []) (hq2 : S.R q2 = []) (hq3 : S.R q3 = [])
    (hctr : (S.R ctrB).length = B) (hcnt : (S.R cnt).length = rectSize N₀ N₁ N₂ N₃ L)
    (htmp : S.R tmp = []) (htm : S.R tm = binSyms L (2 ^ (ρ + (f - 1) * K)))
    (hus : ∀ r, S.R (us r) = []) (hcf : ∀ j, S.R (cf j) = binSyms (idxLen n₀ n₁ n₂ n₃ L rb j) 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 92 * (rectSize N₀ N₁ N₂ N₃ L * (B + keyLen n₀ n₁ n₂ n₃ L rb + 1)) +
        8 * keyLen n₀ n₁ n₂ n₃ L rb + 82 ∧
      Exec body (fixPass σ src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp tm st cf us) (mk v S) m
        (mk v' { S with R := (Function.update S.R src
          (moveRecs (addrPerm N₀ N₁ N₂ N₃ L σ (topFix L K ρ f)) l).flatten) }) := by
  set k := keyLen n₀ n₁ n₂ n₃ L rb with hk
  set M := rectSize N₀ N₁ N₂ N₃ L with hM
  set p := ρ + (f - 1) * K with hp
  have hpL : p < L := by
    have : (f - 1) * K + K = L := by rw [hL, ← Nat.succ_mul, Nat.succ_eq_add_one,
        Nat.sub_add_cancel hf]
    omega
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
  have hxy : slotF (σ.symm 0) ≠ slotF (σ.symm 1) := fun e => by
    have := σ.symm.injective (slotF_injective e)
    exact absurd this (by decide)
  set rs : Fin 3 → Fin T := ![cf (slotF (σ.symm 0)), cf (slotF (σ.symm 1)), tm] with hrs
  have hcode : CodeLayout rs us st :=
    { rs_inj := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          first
          | rfl
          | (exfalso; revert hij
             simp [rs, hcfinj.eq_iff, hxy, Ne.symm hxy, htmcf, Ne.symm (htmcf _)])
      tmps_inj := husinj
      rs_tmps := by
        intro r r'
        fin_cases r <;> simp [rs, Ne.symm (hucf _ _), htmus]
      rs_st := by
        intro r
        fin_cases r <;> simp [rs]
        · exact fun e => hstcf ⟨_, e⟩
        · exact fun e => hstcf ⟨_, e⟩
        · exact Ne.symm hsttm
      tmps_st := fun r e => hstus ⟨r, e⟩ }
  have hfield : ∀ r j, topSrc σ p r = .inl j →
      rs r = cf j ∧ idxLen n₀ n₁ n₂ n₃ L rb j = L := by
    intro r j hr
    fin_cases r <;> simp [topSrc] at hr <;> subst hr <;> simp [rs, idxLen_slotF]
  have hparam : ∀ r p' j, topSrc σ p r = .inr p' → rs r ≠ cf j := by
    intro r p' j hr
    fin_cases r <;> simp [topSrc] at hr
    simp [rs, htmcf]
  have hrs12 : ∀ r, rs r ∉ [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp] := by
    intro r
    fin_cases r
    · exact hcf12 _
    · exact hcf12 _
    · exact htm12
  have hX : ∀ (Xp : Fin T → Prop),
      (∀ x, Xp x → x ∈ [src, r0, r1, r2, r3, q0, q1, q2, q3, ctrB, cnt, tmp]) →
      IdxLayout cf (idxLen n₀ n₁ n₂ n₃ L rb) L rs us (topSrc σ p) st Xp := fun Xp hXp =>
    { hcode with
      cf_inj := hcfinj
      tmps_cf := hucf
      field := hfield
      param := hparam
      cf_X := fun j hx => hcf12 j (hXp _ hx)
      rs_X := fun r hx => hrs12 r (hXp _ hx)
      tmps_X := fun r hx => hus12 r (hXp _ hx) }
  have hlay : FixLayout src r0 r1 r2 r3 q0 q1 q2 q3 ctrB cnt tmp st cf
      (idxLen n₀ n₁ n₂ n₃ L rb) L rs us (topSrc σ p) :=
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
  have hIdx : IdxState cf (idxLen n₀ n₁ n₂ n₃ L rb) L rs us (topSrc σ p) S.R 0 :=
    ⟨fun j => by rw [hcf j]; simp [digit],
      fun r p' hr => by
        fin_cases r <;> simp [topSrc] at hr
        subst hr
        exact htm,
      hus⟩
  set πF := addrPerm N₀ N₁ N₂ N₃ L σ (topFix L K ρ f) with hπF
  set cin := idxCode (topInAuto A) L (idxLen n₀ n₁ n₂ n₃ L rb) (topSrc σ p) with hcin
  set cout := idxCode (topOutAuto A) L (idxLen n₀ n₁ n₂ n₃ L rb) (topSrc σ p) with hcout
  have hcodes : ∀ i : Fin M, cout (πF i) = cin i := by
    intro i
    obtain ⟨a, rfl⟩ := (enc N₀ N₁ N₂ N₃ L σ).surjective i
    rw [hπF, addrPerm_enc, hcout, hcin, idxCode_topOut hN₀ hR hN₁ hN₂ hN₃ σ hpL,
      idxCode_topIn hN₀ hR hN₁ hN₂ hN₃ σ hpL]
    obtain ⟨s, w⟩ := a
    show topCode (((topFix L K ρ f w) 0 : ℕ).testBit p)
      (xor ((topFix L K ρ f w 1 : ℕ).testBit p) ((topFix L K ρ f w 0 : ℕ).testBit p)) = _
    rw [topFix_apply_zero, topFix_testBit, ← hp]
    simp
  have hmono : ∀ i i' : Fin M, cin i = cin i' → i < i' → πF i < πF i' := by
    intro i i' hc hlt
    obtain ⟨a, rfl⟩ := (enc N₀ N₁ N₂ N₃ L σ).surjective i
    obtain ⟨a', rfl⟩ := (enc N₀ N₁ N₂ N₃ L σ).surjective i'
    rw [hcin, idxCode_topIn hN₀ hR hN₁ hN₂ hN₃ σ hpL,
      idxCode_topIn hN₀ hR hN₁ hN₂ hN₃ σ hpL] at hc
    obtain ⟨hx, hy⟩ := topCode_injective hc
    have e1 := fix_enc (N₀ := N₀) (N₁ := N₁) (N₂ := N₂) (N₃ := N₃) K ρ f σ a
    have e2 := fix_enc (N₀ := N₀) (N₁ := N₁) (N₂ := N₂) (N₃ := N₃) K ρ f σ a'
    rw [← hx, ← hy] at e2
    rw [Fin.lt_def] at hlt ⊢
    rw [hπF, addrPerm_enc, addrPerm_enc]
    have : ((enc N₀ N₁ N₂ N₃ L σ a : ℕ) : ℤ) < ((enc N₀ N₁ N₂ N₃ L σ a' : ℕ) : ℤ) := by
      exact_mod_cast hlt
    have h3 : ((enc N₀ N₁ N₂ N₃ L σ (liftA N₀ N₁ N₂ N₃ L (topFix L K ρ f) a) : ℕ) : ℤ) <
        ((enc N₀ N₁ N₂ N₃ L σ (liftA N₀ N₁ N₂ N₃ L (topFix L K ρ f) a') : ℕ) : ℤ) := by
      rw [e1, e2]; linarith
    exact_mod_cast h3
  have hmerge := mergeIdxList_moveRecs πF l hl hlB cin cout hcodes hmono
  have hout : (moveRecs πF l).flatten.length = M * B := by
    rw [length_flatten_of_length _ (moveRecs_length_mem πF l hl hlB), length_moveRecs]
  obtain ⟨v', m, hu, hm, he⟩ := fixAt_exec body hlay (topInAuto A) (topOutAuto A) hB l hl hlB
    (idxCount_perm πF cin cout hcodes) _ hout hmerge v S hsrc hr0 hr1 hr2 hr3 hq0 hq1 hq2 hq3
    hctr hcnt htmp hIdx
  refine ⟨v', m, hu, ?_, he⟩
  rw [sum_idxLen] at hm
  have hLk : L ≤ k := by simp only [hk, keyLen]; omega
  have h1 : M * (18 * B + 12 * L + 8 * k + 8 * 8 + 28) ≤ 92 * (M * (B + k + 1)) := by
    have : 18 * B + 12 * L + 8 * k + 8 * 8 + 28 ≤ 92 * (B + k + 1) := by omega
    nlinarith [Nat.mul_le_mul_left M this]
  rw [← hk] at hm
  rw [← hM]
  omega

end FixMain

end IntegerMultBounds.MathlibTM2.Node
