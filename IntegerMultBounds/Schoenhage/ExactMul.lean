module

public import IntegerMultBounds.Schoenhage.RingMul
public import IntegerMultBounds.Schoenhage.RingConst

/-! Exact products of two binary words on the ring product's bank. From the
operands on `xA`, `xB` and a ruler `ones n` on `xC`, the size `N = topN n` is
built in unary on `kN` (`exSize`), the operands are fitted to `N + 1` bits,
one Schönhage–Strassen product modulo `2^N + 1` runs (`runs_mulStep`), and the
low `n` bits of the result are written to `xQ` (`runs_exactMul`). When the
operand lengths sum to at most `n`, the product is exact: `xQ` holds
`bits n (bval x * bval y)`. Every scratch tape is empty again. -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

theorem clean_update {τ : Fin 𝕌 → WTape} (hc : Clean τ) (i : Fin 𝕋) : Function.update τ (ι i) emp = τ := by
  have : τ (ι i) = emp := congrFun hc i
  rw [← this]; exact Function.update_eq_self _ _

theorem clean_update_own {τ : Fin 𝕌 → WTape} (hc : Clean τ) {s : Fin 𝕌} (hs : Own s) (v : WTape) :
    Clean (Function.update τ s v) := by
  funext i
  simp only [Function.comp_apply]
  rw [Function.update_of_ne (hs.ne' i)]
  exact congrFun hc i

/-! ### The size in unary -/

/-- `qR = ones (2 n)` with its ticks on `qT`, `qB = ones 0`, `c1 = [1]`. -/
noncomputable def exSizeA : Cmd 0 𝕌 :=
  .seq (op0 Rules.copy false xC (ι qR) (by decide)) <| .seq (rewind xC) <|
  .seq (op0 Rules.copy true xC (ι qR) (by decide)) <| .seq (rewind xC) <| .seq (rewind (ι qR)) <|
  .seq (op0 Rules.ticks false (ι qR) (ι qT) (by decide)) <| .seq (rewind (ι qR)) <| .seq (rewind (ι qT)) <|
  .seq (emit [[]] (ι qB)) <| .seq (rewind (ι qB)) <|
  .seq (emit [[true]] (ι c1)) (rewind (ι c1))

set_option maxHeartbeats 2000000 in
theorem runs_exSizeA {n : ℕ} (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hC : τ xC = reg (ones n)) :
    Runs exSizeA τ (· = Function.update (Function.update (Function.update (Function.update τ
      (ι qR) (reg (ones (2 * n)))) (ι qT) ⟨[], List.replicate (2 * n) []⟩) (ι qB) (reg (ones 0)))
      (ι c1) (reg [true])) (20 * n + 100) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  have hR := hz qR; have h1 := hz c1; have hT := hz qT; have hB := hz qB
  apply Runs.of_wp
  simp only [exSizeA, WP, wp_op0, wp_rewind, wp_emit]
  tsimp [hC, hR, h1, hT, hB, emp, reg, Rules.output_copy, Rules.output_ticks, ones_append]
  have t1 := time_le Rules.copy (ones n) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t4 := time_le Rules.ticks (ones (n + n)) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext x
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hC, hR, h1, hT, hB, emp, reg, ones_append, two_mul] at *
  · simp only [time_copy, length_ones]
    have hB0 : Rules.ticks.B = 0 := rfl
    rw [length_ones, hB0] at t4
    generalize time Rules.ticks (ones (n + n)) (fun j => j.elim0) = T at t4 ⊢
    have e : clen (List.replicate (n + n) []) = n + n := by
      simp [clen, List.map_replicate, List.sum_replicate]
    simp [clen] at *
    omega

/-- `kN = ones (topN n)`; the multiplier's tapes are clean again. -/
noncomputable def exSize : Cmd 0 𝕌 :=
  .seq exSizeA <| .seq (up (.seq sizeLoop (.seq (clear qR) (clear qT)))) <| .seq constB2 <|
  .seq doubleT <| .seq (regMove (ι qR) kN (by decide)) (clear (ι c1))

theorem topN_eq (n : ℕ) : topN n = 2 ^ Nat.size (2 * n) := rfl

set_option maxHeartbeats 2000000 in
theorem runs_exSize {n : ℕ} (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hC : τ xC = reg (ones n))
    (hN : τ kN = emp) :
    Runs exSize τ (· = Function.update τ kN (reg (ones (topN n)))) (500 * n + 100 * topN n + 1000) := by
  have hz : ∀ i : Fin 𝕋, τ (ι i) = emp := fun i => congrFun hc i
  have s1 := runs_exSizeA τ hc hC
  set τ₁ := Function.update (Function.update (Function.update (Function.update τ
      (ι qR) (reg (ones (2 * n)))) (ι qT) ⟨[], List.replicate (2 * n) []⟩) (ι qB) (reg (ones 0)))
      (ι c1) (reg [true])
  have s2 := runs_upSize (n := 2 * n) τ₁ (by tsimp [τ₁]) (by tsimp [τ₁, ones]) (by tsimp [τ₁])
    (by tsimp [τ₁]) (by tsimp [τ₁, hz]) (by tsimp [τ₁, hz])
  set b := Nat.size (2 * n)
  set τ₂ := Function.update (Function.update (Function.update τ₁ (ι qR) emp) (ι qB) (reg (ones b))) (ι qT) emp
  have s3 := runs_constB2 (b := b) τ₂ (by tsimp [τ₂]) (by tsimp [τ₂]) (by tsimp [τ₂])
  set τ₃ := Function.update (Function.update (Function.update τ₂ (ι qB) emp) (ι qT)
      ⟨[], List.replicate b []⟩) (ι qR) (reg (ones 1))
  have s4 := runs_doubleT (j := b) (r := 1) τ₃ (by tsimp [τ₃]) (by tsimp [τ₃, τ₂, τ₁, hz])
    (by tsimp [τ₃, τ₂, τ₁, hz]) (by tsimp [τ₃])
  set τ₄ := Function.update (Function.update τ₃ (ι qR) (reg (ones (1 * 2 ^ b)))) (ι qT) emp
  have s5 := runs_regMove (a := 0) (show ι qR ≠ kN by decide) τ₄ (w := ones (1 * 2 ^ b)) (by tsimp [τ₄])
    (by tsimp [τ₄, τ₃, τ₂, τ₁, hN])
  set τ₅ := Function.update (Function.update τ₄ (ι qR) emp) kN (reg (ones (1 * 2 ^ b)))
  have s6 := runs_clear (a := 0) (ι c1) τ₅
  have hc1 : τ₅ (ι c1) = reg [true] := by tsimp [τ₅, τ₄, τ₃, τ₂, τ₁]
  have hb : 2 ^ b = topN n := rfl
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 (Runs.then s4 (Runs.then s5 s6))))).mono
    (fun τ' h => ?_) ?_
  · rw [h]
    funext x
    by_cases hx : x.val < 64
    · have hx' : x = ι ⟨x.val, hx⟩ := by ext; simp
      rw [hx']
      have hk : ι ⟨x.val, hx⟩ ≠ kN := by intro e; have := congrArg Fin.val e; simp at this; omega
      rw [Function.update_of_ne hk, hz]
      simp only [τ₅, τ₄, τ₃, τ₂, τ₁, Function.update_apply]
      split_ifs <;> first | rfl | exact hz _
    · by_cases hk : x = kN
      · subst hk
        rw [Function.update_of_ne (show kN ≠ ι c1 by decide)]
        simp [τ₅, hb]
      · have h1 : ∀ i : Fin 𝕋, x ≠ ι i := fun i e => hx (by rw [e]; simp)
        simp only [τ₅, τ₄, τ₃, τ₂, τ₁, Function.update_of_ne hk, Function.update_of_ne (h1 _)]
  · have hb1 : b ≤ 2 ^ b := Nat.lt_two_pow_self.le
    have hn : 2 * n ≤ topN n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; omega
      · exact (topN_facts h).1.le
    rw [hc1]
    simp only [one_mul, length_ones, WTape.words, reg, clen_cons, clen_nil, List.reverse_nil,
      List.nil_append, List.length_singleton]
    have : 2 ^ b - 1 ≤ 2 ^ b := Nat.sub_le _ _
    omega

/-! ### Operands, product, output -/

theorem own_zH : Own zH := by unfold Own; decide

theorem true_ones (N : ℕ) : [true] ++ ones N = ones (N + 1) := by
  simp [ones, List.replicate_succ]

/-- `xE`, `xP`: the operands fitted to `N + 1` bits, driven by `ones (N + 1)` on `xQ`. -/
noncomputable def exLoad : Cmd 0 𝕌 :=
  .seq (emit [[true]] xQ) <| .seq (op0 Rules.copy true kN xQ (by decide)) <| .seq (rewind kN) <|
  .seq (rewind xQ) <|
  .seq (op1 Rules.take false xQ xA xE (by decide) (by decide) (by decide)) <| .seq (rewind xQ) <|
  .seq (rewind xA) <| .seq (rewind xE) <|
  .seq (op1 Rules.take false xQ xB xP (by decide) (by decide) (by decide)) <| .seq (rewind xQ) <|
  .seq (rewind xB) <| .seq (rewind xP) (clear xQ)

set_option maxHeartbeats 2000000 in
theorem runs_exLoad {N : ℕ} {x y : List Bool} (τ : Fin 𝕌 → WTape) (hA : τ xA = reg x) (hB : τ xB = reg y)
    (hN : τ kN = reg (ones N)) (hE : τ xE = emp) (hP : τ xP = emp) (hQ : τ xQ = emp) :
    Runs exLoad τ (· = Function.update (Function.update τ xE (reg (Rules.fit (N + 1) x)))
      xP (reg (Rules.fit (N + 1) y))) (20 * N + 3 * x.length + 3 * y.length + 200) := by
  apply Runs.of_wp
  simp only [exLoad, WP, wp_op0, wp_op1, wp_rewind, wp_emit, wp_clear]
  tsimp [hA, hB, hN, hE, hP, hQ, emp, reg, Rules.output_copy, Rules.output_take, true_ones]
  have t1 := time_le Rules.copy (ones N) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.take (true :: ones N) (fun _ => x) x.length (fun _ => le_rfl)
  have t3 := time_le Rules.take (true :: ones N) (fun _ => y) y.length (fun _ => le_rfl)
  refine ⟨?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hA, hB, hN, hE, hP, hQ, emp, reg] at *
  · simp only [length_ones, time_copy, List.length_cons] at t1 t2 t3 ⊢
    simp [WTape.words, clen] at *
    omega

/-- `xQ = fit n (zH)`, then every scratch tape cleared. -/
noncomputable def exOut : Cmd 0 𝕌 :=
  .seq (op1 Rules.take false xC zH xQ (by decide) (by decide) (by decide)) <| .seq (rewind xC) <|
  .seq (rewind xQ) <| .seq (clear zH) <| .seq (clear xE) <| .seq (clear xP) (clear kN)

set_option maxHeartbeats 2000000 in
theorem runs_exOut {n : ℕ} {z e f k : List Bool} (τ : Fin 𝕌 → WTape) (hC : τ xC = reg (ones n))
    (hH : τ zH = reg z) (hE : τ xE = reg e) (hP : τ xP = reg f) (hN : τ kN = reg k) (hQ : τ xQ = emp) :
    Runs exOut τ (· = Function.update (Function.update (Function.update (Function.update
      (Function.update τ xQ (reg (Rules.fit n z))) zH emp) xE emp) xP emp) kN emp)
      (3 * n + 3 * z.length + 2 * e.length + 2 * f.length + 2 * k.length + 100) := by
  apply Runs.of_wp
  simp only [exOut, WP, wp_op1, wp_rewind, wp_clear]
  tsimp [hC, hH, hE, hP, hN, hQ, emp, reg, Rules.output_take]
  have t1 := time_le Rules.take (ones n) (fun _ => z) z.length (fun _ => le_rfl)
  refine ⟨?_, ?_⟩
  · funext i
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [hC, hH, hE, hP, hN, hQ, emp, reg] at *
  · simp only [length_ones] at t1 ⊢
    simp [WTape.words, clen] at *
    omega

/-! ### The exact product -/

/-- Size, operands, one product modulo `2^N + 1`, low `n` bits. -/
noncomputable def exactMul : Cmd 0 𝕌 :=
  .seq exSize <| .seq exLoad <| .seq (mulStep xE xP zH own_xE own_xP own_zH) exOut

theorem fit_bits {n M v : ℕ} (h : n ≤ M) (hv : v < 2 ^ n) : Rules.fit n (bits M v) = bits n v := by
  rw [Rules.fit_eq_bits, bval_bits, Nat.mod_eq_of_lt (hv.trans_le (Nat.pow_le_pow_right (by norm_num) h))]

/-- The cost of `exactMul` at ruler length `n`. -/
noncomputable def exCost (n : ℕ) (x y : List Bool) : ℕ :=
  ssCost (topN n) [bval x, bval y] + 200 * topN n + 600 * n + 5 * x.length + 5 * y.length + 20000

set_option maxHeartbeats 4000000 in
/-- Exact products: `xQ = bits n (bval x * bval y)` when the operand lengths sum to at most `n`. -/
theorem runs_exactMul {n : ℕ} {x y : List Bool} (hn : 1 ≤ n) (hxy : x.length + y.length ≤ n)
    (τ : Fin 𝕌 → WTape) (hc : Clean τ) (hA : τ xA = reg x) (hB : τ xB = reg y)
    (hC : τ xC = reg (ones n)) (hN : τ kN = emp) (hE : τ xE = emp) (hP : τ xP = emp)
    (hQ : τ xQ = emp) (hH : τ zH = emp) :
    Runs exactMul τ (· = Function.update τ xQ (reg (bits n (bval x * bval y)))) (exCost n x y) := by
  obtain ⟨hlt, hle, hk⟩ := topN_facts hn
  set N := topN n with hNdef
  have hN0 : 0 < N := by omega
  have hpow : 2 ^ n < 2 ^ N := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hx2 : bval x < 2 ^ n :=
    (bval_lt x).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hy2 : bval y < 2 ^ n :=
    (bval_lt y).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hxy2 : bval x * bval y < 2 ^ n := by
    have := Nat.mul_lt_mul'' (bval_lt x) (bval_lt y)
    rw [← pow_add] at this
    exact this.trans_le (Nat.pow_le_pow_right (by norm_num) hxy)
  have hxF : bval x < Fm N := by unfold Fm; omega
  have hyF : bval y < Fm N := by unfold Fm; omega
  have hv : bval x * bval y % Fm N = bval x * bval y := Nat.mod_eq_of_lt (by unfold Fm; omega)
  have s1 := runs_exSize τ hc hC hN
  set τ₁ := Function.update τ kN (reg (ones N))
  have s2 := runs_exLoad (N := N) (x := x) (y := y) τ₁ (by tsimp [τ₁, hA]) (by tsimp [τ₁, hB]) (by tsimp [τ₁])
    (by tsimp [τ₁, hE]) (by tsimp [τ₁, hP]) (by tsimp [τ₁, hQ])
  have ex : Rules.fit (N + 1) x = rwd N (bval x) := by rw [Rules.fit_eq_bits]; rfl
  have ey : Rules.fit (N + 1) y = rwd N (bval y) := by rw [Rules.fit_eq_bits]; rfl
  rw [ex, ey] at s2
  set τ₂ := Function.update (Function.update τ₁ xE (reg (rwd N (bval x)))) xP (reg (rwd N (bval y)))
  have hc2 : Clean τ₂ :=
    clean_update_own (clean_update_own (clean_update_own hc (by unfold Own; decide) _) own_xE _) own_xP _
  have s3 := runs_mulStep own_xE own_xP own_zH (by decide) (by decide) (by decide) hN0 hk hxF hyF τ₂ hc2
    (by tsimp [τ₂]) (by tsimp [τ₂]) (by tsimp [τ₂, τ₁]) (by tsimp [τ₂, τ₁, hH])
  rw [hv] at s3
  set τ₃ := Function.update τ₂ zH (reg (rwd N (bval x * bval y)))
  have s4 := runs_exOut (n := n) (z := rwd N (bval x * bval y)) (e := rwd N (bval x)) (f := rwd N (bval y)) (k := ones N) τ₃ (by tsimp [τ₃, τ₂, τ₁, hC]) (by tsimp [τ₃]) (by tsimp [τ₃, τ₂])
    (by tsimp [τ₃, τ₂]) (by tsimp [τ₃, τ₂, τ₁]) (by tsimp [τ₃, τ₂, τ₁, hQ])
  refine (Runs.then s1 (Runs.then s2 (Runs.then s3 s4))).mono (fun τ' h => ?_) ?_
  · rw [h, rwd, fit_bits (by omega) hxy2]
    funext i
    simp only [τ₃, τ₂, τ₁, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> tsimp [emp, hE, hP, hH, hN] at *
  · unfold exCost
    simp only [rwd_length, length_ones]
    rw [← hNdef]
    omega

end IntegerMultBounds.Schoenhage
