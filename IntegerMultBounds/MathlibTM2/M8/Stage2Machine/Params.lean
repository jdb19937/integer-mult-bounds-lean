module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Depth
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighBody
public import IntegerMultBounds.Machine.RoundedRowDescriptor

/-!
# The rows of the stage-2 high body

At width `e` the high body joins the low `r e` digits of `h` and `d` into the rows and pads the
rows to `R' e`, the least multiple of `divisor e = W^(c clog₂ e)` above `q^(2 r e)`, where `r e`
is least with `divisor e ≤ q^(2 r e)` (stage 1's `rho`). The family's depth below the padded view
is at most `c clog₂ e` (`Depth.depth_le_clog`), so the padded view fits the core whenever two
digits are left (`fits`). The padding at most doubles the volume (`volume_le`), `r e` is at most
`c W clog₂ e` (`r_le`), and two digits are left at every large width (`eventually_fit`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Params

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRowPadding (withRows)
open ArbitraryWidthHighLayout
open ArbitraryWidthHighRows (rho)
open RoundedRowDescriptor (rounded)
open RevMachine

/-- The constant of the depth bound at base two. -/
def c : ℕ := 1058 * 2 + 1

/-- The family's role count. -/
def W : ℕ := rev97m.roleCount

theorem W_eq : W = 108516254 := rfl

/-- The divisor of the padded rows at width `e`. -/
def divisor (e : ℕ) : ℕ := W ^ (c * Nat.clog 2 e)

/-- The joined digits at width `e`. -/
def r (e : ℕ) : ℕ := rho prime (divisor e)

/-- The joined rows at width `e`. -/
def rows (e : ℕ) : ℕ := prime ^ (2 * r e)

/-- The padded rows at width `e`. -/
def padded (e : ℕ) : ℕ := rounded (rows e) (divisor e)

theorem prime_two : 2 ≤ prime := Networks.Shared50ModularControl.prime_prime.two_le

theorem divisor_pos (e : ℕ) : 0 < divisor e := pow_pos (by rw [W_eq]; norm_num) _

theorem rows_pos (e : ℕ) : 0 < rows e := pow_pos (by have := prime_two; omega) _

theorem divisor_le (e : ℕ) : divisor e ≤ rows e :=
  (ArbitraryWidthHighRows.rho_le_iff prime (divisor e) (r e) prime_two).mp le_rfl

theorem rows_le (e : ℕ) : rows e ≤ padded e :=
  RoundedRowDescriptor.rows_le _ _ (rows_pos e) (divisor_pos e)

theorem padded_lt (e : ℕ) : padded e < 2 * rows e :=
  RoundedRowDescriptor.rounded_lt_twice _ _ (rows_pos e) (divisor_le e)

theorem divisor_dvd (e : ℕ) : divisor e ∣ padded e := RoundedRowDescriptor.rounded_dvd _ _

theorem pow_le_prime_pow (V k : ℕ) : V ^ k ≤ prime ^ (2 * (V * k)) := by
  have hV : V ≤ 2 ^ V := (Nat.lt_two_pow_self).le
  calc V ^ k ≤ (2 ^ V) ^ k := Nat.pow_le_pow_left hV _
    _ = 2 ^ (V * k) := by rw [← pow_mul]
    _ ≤ 2 ^ (2 * (V * k)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ prime ^ (2 * (V * k)) := Nat.pow_le_pow_left prime_two _

/-- The joined digits are at most `c W clog₂ e`. -/
theorem r_le (e : ℕ) : r e ≤ c * W * Nat.clog 2 e := by
  unfold r
  rw [ArbitraryWidthHighRows.rho_le_iff prime _ _ prime_two]
  have h := pow_le_prime_pow W (c * Nat.clog 2 e)
  have he : W * (c * Nat.clog 2 e) = c * W * Nat.clog 2 e := by ring
  rw [he] at h
  exact h

/-- The joined view of `x` at width `e`, padded. -/
abbrev view (P e G B : ℕ) : Descriptor := withRows (joinedDescriptor prime P e (r e) G B) (padded e)

theorem view_width (P e G B : ℕ) : (view P e G B).width = e - r e := rfl

/-- **The padded view fits the core.** -/
theorem fits {K : ℕ} {P e G B : ℕ} (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hr : r e + 2 ≤ e) :
    HighBody.Fits K (view P e G B) where
  pos := ⟨hP, (rows_pos e).trans_le (rows_le e), (by change 0 < 1; decide), hG, hB⟩
  width := by rw [view_width]; omega
  rows := by
    have hn : Assembly.nOf K (view P e G B) ≤ e :=
      (Nat.div_le_self _ _).trans (by rw [view_width]; omega)
    exact (Nat.pow_dvd_pow _ (Depth.depth_le_clog le_rfl hn)).trans (divisor_dvd e)

/-- Joining keeps the volume. -/
theorem joined_eq {P e G B : ℕ} (hr : r e ≤ e) :
    volume prime (joinedDescriptor prime P e (r e) G B) = volume prime (originalDescriptor P e G B) := by
  rw [← joined_volume prime P e (r e) G B, ← original_volume prime P e (r e) G B hr]
  ring

/-- The padding at most doubles the volume. -/
theorem volume_le {P e G B : ℕ} (hr : r e ≤ e) :
    volume prime (view P e G B) ≤ 2 * volume prime (originalDescriptor P e G B) := by
  have hv : volume prime (view P e G B) * rows e =
      volume prime (joinedDescriptor prime P e (r e) G B) * padded e := by
    simp only [volume, view, withRows, joinedDescriptor, rows]
    ring
  rw [← joined_eq hr]
  have h2 := padded_lt e
  have hpos := rows_pos e
  by_contra hc
  push Not at hc
  have : 2 * volume prime (joinedDescriptor prime P e (r e) G B) * rows e <
      volume prime (view P e G B) * rows e := Nat.mul_lt_mul_of_pos_right hc hpos
  nlinarith

/-! ### Large widths -/

theorem succ_sq_le (s : ℕ) : (s + 1) ^ 2 ≤ 2 ^ (2 * s + 1) := by
  induction s with
  | zero => norm_num
  | succ s ih =>
    have : 2 ^ (2 * (s + 1) + 1) = 4 * 2 ^ (2 * s + 1) := by ring
    rw [this]
    have h : (s + 1 + 1) ^ 2 ≤ 4 * (s + 1) ^ 2 := by ring_nf; nlinarith
    omega

theorem clog_le (e : ℕ) : Nat.clog 2 e ≤ 2 * Nat.sqrt e + 1 :=
  Nat.clog_le_of_le_pow ((Nat.lt_succ_sqrt' e).le.trans (succ_sq_le _))

/-- The joined digits are at most `A (2 √e + 1)`. -/
theorem r_le_sqrt (e : ℕ) : r e ≤ c * W * (2 * Nat.sqrt e + 1) :=
  (r_le e).trans (Nat.mul_le_mul_left _ (clog_le e))

/-- The width threshold of the high body. -/
def threshold : ℕ := (2 * (c * W) + 3) ^ 2

/-- **Two digits are left at every large width.** -/
theorem fit_of_threshold {e : ℕ} (he : threshold ≤ e) : r e + 2 ≤ e := by
  have hs : 2 * (c * W) + 3 ≤ Nat.sqrt e := Nat.le_sqrt'.mpr he
  have hsq : Nat.sqrt e * Nat.sqrt e ≤ e := Nat.sqrt_le' e |>.trans' (by rw [sq])
  have := r_le_sqrt e
  nlinarith

theorem sqrt_le_rpow (e : ℕ) : (Nat.sqrt e : ℝ) ≤ (e : ℝ) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  exact Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' e)

/-- The joined digits grow at most like `√e`. -/
theorem r_succ_le {e : ℕ} (he : 1 ≤ e) :
    ((r e + 1 : ℕ) : ℝ) ≤ (3 * (c * W) + 1 : ℕ) * (e : ℝ) ^ (1 / 2 : ℝ) := by
  have h1 : (1 : ℝ) ≤ (e : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by exact_mod_cast he) (by norm_num)
  have h2 := sqrt_le_rpow e
  have h3 : ((r e : ℕ) : ℝ) ≤ ((c * W * (2 * Nat.sqrt e + 1) : ℕ) : ℝ) := by exact_mod_cast r_le_sqrt e
  push_cast at h3 ⊢
  have hA : (0 : ℝ) ≤ c * W := by positivity
  nlinarith

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Params
