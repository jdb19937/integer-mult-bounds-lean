module

public import IntegerMultBounds.Schoenhage.RingPointwiseProgram

/-! The words of the synthetic convolution's last step. Multiplying a record
by `M = 2^k` widens every component word by `k` trailing zeros
(`compWord_scale`, `array_scale`); `k = log₂ M` is half the number of zeros
in the axis codes `∏ Γ(tᵢ)` of the header (`count_false_axes`); and the
streaming rules that count those zeros, read a parity, and emit the zero
prefix of a `Γ` code. -/

@[expose] public section

set_option maxRecDepth 10000

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule Spec.SignedRingProduct

/-! ### Rules -/

namespace Rules

/-- One `true` per two zeros of the driver. -/
abbrev zhalf : Rule 0 where
  Q := Bool
  q0 := false
  step q b _ := if b then (q, none, fun _ => false) else (!q, if q then some (some true) else none, fun _ => false)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

theorem go_zhalf (q : Bool) (bs : List Bool) (ws : Fin 0 → List Bool) :
    (go zhalf q bs ws).2.1 = (ones (((if q then 1 else 0) + bs.count false) / 2)).map some := by
  induction bs generalizing q ws with
  | nil => cases q <;> simp [go, ones]
  | cons b bs ih =>
    cases b
    · simp only [go, Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      cases q
      · simp [Nat.add_comm]
      · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, Option.toList_some, List.singleton_append,
          List.count_cons_self]
        rw [show (1 + (List.count false bs + 1)) / 2 = (0 + List.count false bs) / 2 + 1 by omega]
        simp [ones, List.replicate_succ]
    · simp only [go, ↓reduceIte, Option.toList_none, List.nil_append]
      rw [ih]
      simp

theorem output_zhalf (bs : List Bool) (ws : Fin 0 → List Bool) :
    output zhalf bs ws = syms [ones (bs.count false / 2)] := by
  simp [output, syms_cons, go_zhalf]

/-- The parity of the driver's length, as a one-bit word. -/
abbrev parity : Rule 0 where
  Q := Bool
  q0 := false
  step q _ _ := (!q, none, fun _ => false)
  flush q := [some q, none]
  B := 2
  hB _ := le_rfl

theorem go_parity (q : Bool) (bs : List Bool) (ws : Fin 0 → List Bool) :
    (go parity q bs ws).2.1 = [] ∧
      (go parity q bs ws).1 = decide ((bs.length + if q then 1 else 0) % 2 = 1) := by
  induction bs generalizing q ws with
  | nil => cases q <;> simp [go]
  | cons b bs ih =>
    simp only [go, Option.toList_none, List.nil_append]
    refine ⟨(ih _ _).1, ?_⟩
    rw [(ih _ _).2]
    cases q <;> simp; omega

theorem output_parity (bs : List Bool) (ws : Fin 0 → List Bool) :
    output parity bs ws = syms [[decide (bs.length % 2 = 1)]] := by
  simp [output, syms_cons, (go_parity false bs ws).1, (go_parity false bs ws).2]

/-- A zero per driver bit after the first. -/
abbrev tailFill : Rule 0 where
  Q := Bool
  q0 := false
  step q _ _ := (true, if q then some (some false) else none, fun _ => false)
  flush _ := [none]
  B := 1
  hB _ := le_rfl

theorem go_tailFill_true (bs : List Bool) (ws : Fin 0 → List Bool) :
    (go tailFill true bs ws).2.1 = (List.replicate bs.length false).map some := by
  induction bs generalizing ws with
  | nil => simp [go]
  | cons b bs ih => simp [go, ih, List.replicate_succ]

theorem output_tailFill (bs : List Bool) (ws : Fin 0 → List Bool) :
    output tailFill bs ws = syms [List.replicate (bs.length - 1) false] := by
  cases bs with
  | nil => simp [output, go, syms_cons]
  | cons b bs => simp [output, go, go_tailFill_true, syms_cons]

end Rules

/-! ### Scaling by a power of two -/

theorem msbBits_two_pow_mul_low (k v : ℕ) : ∀ n ≤ k, msbBits n (2 ^ k * v) = List.replicate n false
  | 0, _ => rfl
  | n + 1, hn => by
    rw [msbBits, msbBits_two_pow_mul_low k v n (by omega), List.replicate_succ]
    congr 1
    have e : 2 ^ k * v / 2 ^ n = 2 * (2 ^ (k - n - 1) * v) := by
      rw [show k = n + 1 + (k - n - 1) by omega, pow_add, pow_add, pow_one]
      rw [show n + 1 + (k - n - 1) - n - 1 = k - n - 1 by omega]
      rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
    rw [e]; simp

theorem msbBits_scale (k : ℕ) : ∀ (w v : ℕ), msbBits (w + k) (2 ^ k * v) = msbBits w v ++ List.replicate k false
  | 0, v => by simp [msbBits, msbBits_two_pow_mul_low k v k le_rfl]
  | w + 1, v => by
    rw [show w + 1 + k = (w + k) + 1 by omega, msbBits, msbBits, msbBits_scale k w v, List.cons_append]
    congr 2
    rw [pow_add, Nat.mul_comm (2 ^ w), Nat.mul_div_mul_left _ _ (by positivity)]

theorem compWord_scale (w k : ℕ) (z : ℤ) :
    compWord (w + k) (2 ^ k * z) = compWord w z ++ List.replicate k false := by
  unfold compWord
  have hpos : (0 : ℤ) < 2 ^ w := by positivity
  have e : 2 ^ k * z % 2 ^ (w + k) = 2 ^ k * (z % 2 ^ w) := by
    rw [pow_add, mul_comm ((2 : ℤ) ^ w), Int.mul_emod_mul_of_pos _ _ (by positivity)]
  rw [e, Int.toNat_mul (by positivity) (Int.emod_nonneg _ hpos.ne'), show ((2 : ℤ) ^ k).toNat = 2 ^ k by
    rw [show ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast],
    msbBits_scale]

/-- A record times `2^k`. -/
def scaleRec {r : ℕ} (k : ℕ) (f : Rec r) : Rec r := (fun j => 2 ^ k * f.1 j, fun j => 2 ^ k * f.2 j)

theorem flatten_pairs_append {α : Type} (g1 g2 : α → List Bool) (z : List Bool) : ∀ l : List α,
    (l.flatMap fun j => [g1 j ++ z, g2 j ++ z]).flatten = (l.flatMap fun j => [g1 j, g2 j]).flatMap (· ++ z)
  | [] => by simp
  | j :: l => by simp [flatten_pairs_append g1 g2 z l]

theorem array_scale {r w : ℕ} (hw : 1 ≤ w) (k : ℕ) (vs : List (Rec r)) :
    array (w + k) (vs.map (scaleRec k)) = (cut w (array w vs)).flatMap (· ++ List.replicate k false) := by
  have hcut : cut w (array w vs) = vs.flatMap fun f => recordWords w f.1 f.2 := by
    rw [array_words, cut_flatten_words hw]
    · simp [List.flatMap]
    · intro c hc
      simp only [List.mem_flatten, List.mem_map] at hc
      obtain ⟨l, ⟨f, -, rfl⟩, hl⟩ := hc
      exact recordWords_lengths w f.1 f.2 c hl
  have hrec : ∀ f : Rec r, record (w + k) (scaleRec k f).1 (scaleRec k f).2 =
      (recordWords w f.1 f.2).flatMap (· ++ List.replicate k false) := by
    intro f
    rw [← recordWords_flatten]
    simp only [recordWords, scaleRec, compWord_scale]
    exact flatten_pairs_append _ _ _ _
  rw [hcut]
  clear hcut
  induction vs with
  | nil => simp [array]
  | cons f vs ih => simp [array, List.flatMap_append] at ih ⊢; rw [hrec, ih]

/-! ### `log₂ M` from the axis codes -/

theorem msbBits_two_pow (e : ℕ) : msbBits (e + 1) (2 ^ e) = true :: List.replicate e false := by
  rw [msbBits, show 2 ^ e = 2 ^ e * 1 by ring, msbBits_two_pow_mul_low e 1 e le_rfl]
  simp

theorem count_false_gamma_pow (e : ℕ) : (gamma (2 ^ e)).count false = 2 * e := by
  simp only [gamma, Nat.size_pow, Nat.add_sub_cancel, msbBits_two_pow, List.count_append,
    List.count_replicate_self, List.count_cons]
  simp; omega

theorem count_false_axes : ∀ {es : List ℕ},
    ((es.map (2 ^ ·)).flatMap gamma).count false = 2 * es.sum
  | [] => by simp
  | e :: es => by
    simp only [List.map_cons, List.flatMap_cons, List.count_append, count_false_gamma_pow,
      count_false_axes, List.sum_cons]
    ring

theorem prod_two_pow : ∀ (es : List ℕ), (es.map (2 ^ ·)).prod = 2 ^ es.sum
  | [] => by simp
  | e :: es => by simp [prod_two_pow es, pow_add]

/-- With power-of-two axes, half the zeros of the axis codes is `log₂ M`. -/
theorem axes_zeros {ts : List ℕ} (h : ∀ t ∈ ts, ∃ e, t = 2 ^ e) :
    (ts.flatMap gamma).count false / 2 = Nat.log 2 ts.prod ∧ ts.prod = 2 ^ Nat.log 2 ts.prod := by
  obtain ⟨es, rfl⟩ : ∃ es : List ℕ, es.map (2 ^ ·) = ts := by
    induction ts with
    | nil => exact ⟨[], rfl⟩
    | cons t ts ih =>
      obtain ⟨e, rfl⟩ := h t (by simp)
      obtain ⟨es, hes⟩ := ih (fun x hx => h x (by simp [hx]))
      exact ⟨e :: es, by simp [hes]⟩
  rw [count_false_axes, prod_two_pow, Nat.log_pow (by norm_num)]
  exact ⟨by omega, rfl⟩

/-! ### Binary digits of a unary word -/

/-- The binary digits of `n`, least significant first. -/
def lsb : ℕ → List Bool
  | 0 => []
  | n + 1 => decide ((n + 1) % 2 = 1) :: lsb ((n + 1) / 2)
decreasing_by omega

theorem lsb_pos {n : ℕ} (h : 0 < n) : lsb n = decide (n % 2 = 1) :: lsb (n / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [lsb]

theorem msbBits_succ_eq (s n : ℕ) : msbBits (s + 1) n = msbBits s (n / 2) ++ [decide (n % 2 = 1)] := by
  induction s generalizing n with
  | zero => simp [msbBits]
  | succ s ih =>
    rw [msbBits, ih, msbBits, List.cons_append, Nat.div_div_eq_div_mul, ← pow_succ']

theorem lsb_reverse : ∀ n : ℕ, (lsb n).reverse = msbBits (Nat.size n) n
  | 0 => by simp [lsb, msbBits]
  | n + 1 => by
    rw [lsb, List.reverse_cons, lsb_reverse ((n + 1) / 2), size_half (show 0 < n + 1 by omega),
      msbBits_succ_eq]
decreasing_by omega

theorem gamma_eq_lsb (n : ℕ) :
    gamma n = List.replicate ((lsb n).reverse.length - 1) false ++ (lsb n).reverse := by
  rw [lsb_reverse, length_msbBits]; rfl

namespace Tp

/-- Append the parity of `qR` to `qB`'s last word, then halve `qR`. -/
noncomputable def lsbIt : Cmd 0 𝕋 :=
  .seq (op0 Rules.parity true qR qB (by decide)) <| .seq (rewind qR) <|
  .seq (op0 Rules.half false qR qS (by decide)) <| .seq (clear qR) <| .seq (rewind qS)
    (regMove qS qR (by decide))

/-- One digit while `qR` is nonzero, once per tick of `qT`. -/
noncomputable def lsbStep : Cmd 0 𝕋 := .seq (.cond qR lsbIt (rewind qR)) (skp qT tJ (by decide))

/-- The digit loop. -/
noncomputable def lsbLoop : Cmd 0 𝕋 := .loop qT lsbStep

theorem runs_lsbIt {r : ℕ} {B : List Bool} {Bl : List (List Bool)} (σ : Fin 𝕋 → WTape)
    (hR : σ qR = reg (ones r)) (hB : σ qB = ⟨B :: Bl, []⟩) (hS : σ qS = emp) :
    Runs lsbIt σ (· = Function.update (Function.update σ qR (reg (ones (r / 2))))
      qB ⟨(B ++ [decide (r % 2 = 1)]) :: Bl, []⟩) (10 * r + 60) := by
  apply Runs.of_wp
  simp only [lsbIt, regMove, regIn, cpy, WP, wp_op0, wp_rewind, wp_clear]
  tsimp [hR, hB, hS, emp, reg, Rules.output_parity, Rules.output_half_ones, Rules.output_copy, WTape.put]
  have t1 := time_le Rules.parity (ones r) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t2 := time_le Rules.half (ones r) (fun j => j.elim0) 0 (fun j => j.elim0)
  have t3 := time_le Rules.copy (ones (r / 2)) (fun j => j.elim0) 0 (fun j => j.elim0)
  refine ⟨?_, ?_⟩
  · funext i; fin_cases i <;> tsimp [hR, hB, hS, emp, reg]
  · simp [clen, WTape.words] at t1 t2 t3 ⊢; omega

/-- Digits with a tick budget: `j` steps from `r` with digits `B` so far. -/
def lsbAcc : ℕ → ℕ → List Bool → ℕ × List Bool
  | 0, r, B => (r, B)
  | j + 1, r, B => if r = 0 then lsbAcc j 0 B else lsbAcc j (r / 2) (B ++ [decide (r % 2 = 1)])

theorem lsbAcc_eq : ∀ (j r : ℕ) (B : List Bool), Nat.size r ≤ j → lsbAcc j r B = (0, B ++ lsb r)
  | 0, r, B, h => by
    have : r = 0 := Nat.size_eq_zero.mp (by omega)
    subst this; simp [lsbAcc, lsb]
  | j + 1, r, B, h => by
    rw [lsbAcc]
    split_ifs with hr
    · subst hr; rw [lsbAcc_eq j 0 B (by simp)]
    · have hs := size_half (show 0 < r by omega)
      rw [lsbAcc_eq j (r / 2) _ (by omega), lsb_pos (n := r) (by omega), List.append_assoc]
      rfl

theorem runs_lsbLoop :
    ∀ (j r : ℕ) (B : List Bool) (Bl : List (List Bool)) (σ : Fin 𝕋 → WTape) (Tl : List (List Bool)),
      σ qR = reg (ones r) → σ qB = ⟨B :: Bl, []⟩ → σ qS = emp → σ tJ = emp →
      σ qT = ⟨Tl, List.replicate j []⟩ →
      Runs lsbLoop σ (· = Function.update (Function.update (Function.update σ
          qR (reg (ones (lsbAcc j r B).1))) qB ⟨(lsbAcc j r B).2 :: Bl, []⟩) qT ⟨List.replicate j [] ++ Tl, []⟩)
        (20 * r + 80 * Nat.size r + 20 * j)
  | 0, r, B, Bl, σ, Tl, hR, hB, _, _, hT => by
    refine (Runs.loop_done (by simp [hT]) rfl).mono (fun σ' h' => ?_) (by simp)
    subst h'
    funext i; fin_cases i <;> tsimp [hR, hB, hT, lsbAcc]
  | j + 1, r, B, Bl, σ, Tl, hR, hB, hS, hJ, hT => by
    by_cases hr : r = 0
    · subst hr
      have s1 : Runs (a := 0) lsbStep σ (· = Function.update σ qT ⟨[] :: Tl, List.replicate j []⟩) 12 := by
        unfold lsbStep
        refine (Runs.then (Runs.cond_false (by rw [hR]; exact not_startsOne_reg_nil) (runs_rewind qR σ))
          (runs_skp (a := 0) (s := qT) (j := tJ) (by decide) _ (by tsimp [hT, List.replicate_succ])
            (by tsimp [hJ, emp]))).mono (fun σ' h => ?_) ?_
        · rw [h]; funext i; fin_cases i <;> tsimp [hR, hT, reg, List.replicate_succ]
        · tsimp [hR, hT, reg, ones, List.replicate_succ, clen]
      set σ₁ := Function.update σ qT ⟨[] :: Tl, List.replicate j []⟩
      have ih := runs_lsbLoop j 0 B Bl σ₁ ([] :: Tl) (by tsimp [σ₁, hR]) (by tsimp [σ₁, hB])
        (by tsimp [σ₁, hS]) (by tsimp [σ₁, hJ]) (by tsimp [σ₁])
      refine (Runs.loop_step (by simp [hT]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
        (fun σ' h' => ?_) ?_
      · rw [h']; funext i; fin_cases i <;> tsimp [σ₁, lsbAcc, List.replicate_succ, replicate_append_cons]
      · simp; omega
    · have s1 : Runs (a := 0) lsbStep σ (· = Function.update (Function.update (Function.update σ
            qR (reg (ones (r / 2)))) qB ⟨(B ++ [decide (r % 2 = 1)]) :: Bl, []⟩) qT ⟨[] :: Tl, List.replicate j []⟩)
          (10 * r + 67) := by
        unfold lsbStep
        refine (Runs.then (Runs.cond_true (by rw [hR]; exact startsOne_reg_ones (by omega))
            (runs_lsbIt σ hR hB hS))
          (runs_skp (a := 0) (s := qT) (j := tJ) (by decide) _ (by tsimp [hT, List.replicate_succ])
            (by tsimp [hJ, emp]))).mono (fun σ' h => ?_) ?_
        · rw [h]; funext i; fin_cases i <;> tsimp [hT, List.replicate_succ]
        · tsimp [hT, List.replicate_succ]
      set σ₁ := Function.update (Function.update (Function.update σ
            qR (reg (ones (r / 2)))) qB ⟨(B ++ [decide (r % 2 = 1)]) :: Bl, []⟩) qT ⟨[] :: Tl, List.replicate j []⟩
      have ih := runs_lsbLoop j (r / 2) (B ++ [decide (r % 2 = 1)]) Bl σ₁ ([] :: Tl) (by tsimp [σ₁])
        (by tsimp [σ₁]) (by tsimp [σ₁, hS]) (by tsimp [σ₁, hJ]) (by tsimp [σ₁])
      refine (Runs.loop_step (by simp [hT]) (s1.mono (fun σ' h' => by rw [h']; exact ih) le_rfl)).mono
        (fun σ' h' => ?_) ?_
      · rw [h']; funext i; fin_cases i <;> tsimp [σ₁, lsbAcc, hr, List.replicate_succ, replicate_append_cons]
      · rw [size_half (show 0 < r by omega)]
        have : 2 * (r / 2) ≤ r := Nat.mul_div_le r 2
        nlinarith

end Tp

end IntegerMultBounds.Schoenhage
