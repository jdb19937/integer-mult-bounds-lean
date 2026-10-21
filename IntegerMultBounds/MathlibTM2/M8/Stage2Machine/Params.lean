module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Depth
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighBody
public import IntegerMultBounds.Machine.RoundedRowDescriptor

/-!
# The rows of the stage-2 high body

At width `e` and base `b ≥ 2` the high body joins the low `r b e` digits of `h` and `d` into the
rows and pads the rows to `padded b e`, the least multiple of `divisor b e = W^(c b · clog b e)`
above `q^(2 r b e)`, where `r b e` is least with `divisor b e ≤ q^(2 r b e)` (stage 1's `rho`).
The family's depth below the padded view is at most `c b · clog b e` (`Depth.depth_le_clog`), so
the padded view fits the core whenever two digits are left (`fits`). The padding at most doubles
the volume (`volume_le`), `r b e` is at most `c b · W · clog b e` (`r_le`), and two digits are
left at every width past `threshold b` (`fit_of_threshold`).
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

/-- The constant of the depth bound at base `b`. -/
def c (b : ℕ) : ℕ := 1058 * b + 1

/-- The family's role count. -/
def W : ℕ := rev97m.roleCount

theorem W_eq : W = 108516254 := rfl

/-- The divisor of the padded rows at width `e`. -/
def divisor (b e : ℕ) : ℕ := W ^ (c b * Nat.clog b e)

/-- The joined digits at width `e`. -/
def r (b e : ℕ) : ℕ := rho prime (divisor b e)

/-- The joined rows at width `e`. -/
def rows (b e : ℕ) : ℕ := prime ^ (2 * r b e)

/-- The padded rows at width `e`. -/
def padded (b e : ℕ) : ℕ := rounded (rows b e) (divisor b e)

theorem prime_two : 2 ≤ prime := Networks.Shared50ModularControl.prime_prime.two_le

theorem divisor_pos (b e : ℕ) : 0 < divisor b e := pow_pos (by rw [W_eq]; norm_num) _

theorem rows_pos (b e : ℕ) : 0 < rows b e := pow_pos (by have := prime_two; omega) _

theorem divisor_le (b e : ℕ) : divisor b e ≤ rows b e :=
  (ArbitraryWidthHighRows.rho_le_iff prime (divisor b e) (r b e) prime_two).mp le_rfl

theorem rows_le (b e : ℕ) : rows b e ≤ padded b e :=
  RoundedRowDescriptor.rows_le _ _ (rows_pos b e) (divisor_pos b e)

theorem padded_lt (b e : ℕ) : padded b e < 2 * rows b e :=
  RoundedRowDescriptor.rounded_lt_twice _ _ (rows_pos b e) (divisor_le b e)

theorem divisor_dvd (b e : ℕ) : divisor b e ∣ padded b e := RoundedRowDescriptor.rounded_dvd _ _

theorem pow_le_prime_pow (V k : ℕ) : V ^ k ≤ prime ^ (2 * (V * k)) := by
  have hV : V ≤ 2 ^ V := (Nat.lt_two_pow_self).le
  calc V ^ k ≤ (2 ^ V) ^ k := Nat.pow_le_pow_left hV _
    _ = 2 ^ (V * k) := by rw [← pow_mul]
    _ ≤ 2 ^ (2 * (V * k)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ prime ^ (2 * (V * k)) := Nat.pow_le_pow_left prime_two _

/-- The joined digits are at most `c W clog₂ e`. -/
theorem r_le (b e : ℕ) : r b e ≤ c b * W * Nat.clog b e := by
  unfold r
  rw [ArbitraryWidthHighRows.rho_le_iff prime _ _ prime_two]
  have h := pow_le_prime_pow W (c b * Nat.clog b e)
  have he : W * (c b * Nat.clog b e) = c b * W * Nat.clog b e := by ring
  rw [he] at h
  exact h

/-- The joined view of `x` at width `e`, padded. -/
abbrev view (b P e G B : ℕ) : Descriptor := withRows (joinedDescriptor prime P e (r b e) G B) (padded b e)

theorem view_width (b P e G B : ℕ) : (view b P e G B).width = e - r b e := rfl

/-- **The padded view fits the core.** -/
theorem fits {K b : ℕ} (hb : 2 ≤ b) {P e G B : ℕ} (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) (hr : r b e + 2 ≤ e) :
    HighBody.Fits K (view b P e G B) where
  pos := ⟨hP, (rows_pos b e).trans_le (rows_le b e), (by change 0 < 1; decide), hG, hB⟩
  width := by rw [view_width]; omega
  rows := by
    have hn : Assembly.nOf K (view b P e G B) ≤ e :=
      (Nat.div_le_self _ _).trans (by rw [view_width]; omega)
    exact (Nat.pow_dvd_pow _ (Depth.depth_le_clog hb hn)).trans (divisor_dvd b e)

/-- Joining keeps the volume. -/
theorem joined_eq {b P e G B : ℕ} (hr : r b e ≤ e) :
    volume prime (joinedDescriptor prime P e (r b e) G B) = volume prime (originalDescriptor P e G B) := by
  rw [← joined_volume prime P e (r b e) G B, ← original_volume prime P e (r b e) G B hr]
  ring

/-- The padding at most doubles the volume. -/
theorem volume_le {b P e G B : ℕ} (hr : r b e ≤ e) :
    volume prime (view b P e G B) ≤ 2 * volume prime (originalDescriptor P e G B) := by
  have hv : volume prime (view b P e G B) * rows b e =
      volume prime (joinedDescriptor prime P e (r b e) G B) * padded b e := by
    simp only [volume, view, withRows, joinedDescriptor, rows]
    ring
  rw [← joined_eq hr]
  have h2 := padded_lt b e
  have hpos := rows_pos b e
  by_contra hc
  push Not at hc
  have : 2 * volume prime (joinedDescriptor prime P e (r b e) G B) * rows b e <
      volume prime (view b P e G B) * rows b e := Nat.mul_lt_mul_of_pos_right hc hpos
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

theorem clog_le {b : ℕ} (hb : 2 ≤ b) (e : ℕ) : Nat.clog b e ≤ 2 * Nat.sqrt e + 1 :=
  (Nat.clog_anti_left (by norm_num) hb).trans
    (Nat.clog_le_of_le_pow ((Nat.lt_succ_sqrt' e).le.trans (succ_sq_le _)))

/-- The joined digits are at most `A (2 √e + 1)`. -/
theorem r_le_sqrt {b : ℕ} (hb : 2 ≤ b) (e : ℕ) : r b e ≤ c b * W * (2 * Nat.sqrt e + 1) :=
  (r_le b e).trans (Nat.mul_le_mul_left _ (clog_le hb e))

/-- The width threshold of the high body. -/
def threshold (b : ℕ) : ℕ := (2 * (c b * W) + 3) ^ 2

/-- **Two digits are left at every large width.** -/
theorem fit_of_threshold {b : ℕ} (hb : 2 ≤ b) {e : ℕ} (he : threshold b ≤ e) : r b e + 2 ≤ e := by
  have hs : 2 * (c b * W) + 3 ≤ Nat.sqrt e := Nat.le_sqrt'.mpr he
  have hsq : Nat.sqrt e * Nat.sqrt e ≤ e := Nat.sqrt_le' e |>.trans' (by rw [sq])
  have := r_le_sqrt hb e
  nlinarith

theorem sqrt_le_rpow (e : ℕ) : (Nat.sqrt e : ℝ) ≤ (e : ℝ) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  exact Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' e)

/-- The joined digits grow at most like `√e`. -/
theorem r_succ_le {b : ℕ} (hb : 2 ≤ b) {e : ℕ} (he : 1 ≤ e) :
    ((r b e + 1 : ℕ) : ℝ) ≤ (3 * (c b * W) + 1 : ℕ) * (e : ℝ) ^ (1 / 2 : ℝ) := by
  have h1 : (1 : ℝ) ≤ (e : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by exact_mod_cast he) (by norm_num)
  have h2 := sqrt_le_rpow e
  have h3 : ((r b e : ℕ) : ℝ) ≤ ((c b * W * (2 * Nat.sqrt e + 1) : ℕ) : ℝ) := by exact_mod_cast r_le_sqrt hb e
  push_cast at h3 ⊢
  have hA : (0 : ℝ) ≤ c b * W := by positivity
  nlinarith

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Params
