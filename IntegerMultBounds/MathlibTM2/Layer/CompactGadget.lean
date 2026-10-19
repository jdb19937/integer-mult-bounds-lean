module

public import IntegerMultBounds.MathlibTM2.Layer.CompactSegments

/-!
# The compact-control selected-bit XOR

The movement primitive of `compact-control-movement.tex`. A record address has a target slot `y`
and a source slot `x` of `ρ + n K + m` bits, whose selected bits are bits `ρ + c K` of the
segments `seg ρ K c` (`c < n`), and three compact fields `b`, `t`, `u` of `n` radix-`2^G` digits.
The program `prog` adds the selected bits of `x` to those of `y` modulo `2`, using only rotations
of `y` and of `b` by offsets read from other fields, and swaps of `b` with `t` and with `u`:

* `E`, the four dirty-temporary updates of `Compact.fourUpdate` with temporary `t` and control
  the parities of the digits of `u`: each segment `v` of `y` becomes `tog v z`;
* load `x` into `u` (`u_c ← u_c + x_c`), `E` again, unload.

By `Compact.later_source` the two passes of `E` toggle each segment by the bit of `x`.

`Op` is the instruction set: `rotY neg o` rotates `y` by `± o`, `rotB neg o` rotates `b`, `swapT`
and `swapU` exchange `b` with `t` and with `u`; `Off` names the five offsets. `Op.pure` is the
semantics on the five fields (`V`). `prog_good` (**main theorem**): on every good state the program
is the ideal XOR `ideal`. A state is good (`Good`) when no digit of `t` or `u` is `2^G - 1` and
the guard `seg / 2` of every segment of `y` lies in `[2 · 2^G, 2^(K-1) - 2 · 2^G)`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Layer.CompactGadget

open IntegerMultBounds.MathlibTM2.Layer.CompactDigits Finset

/-- Gadget parameters: segment length `K`, selected offset `ρ`, `n` used segments, compact
digits of `G` bits, and `m` slot bits above the used segments. -/
structure Par where
  K : ℕ
  ρ : ℕ
  n : ℕ
  G : ℕ
  m : ℕ

/-- The five fields: compact `b`, `t`, `u` and the slots `y` (target) and `x` (source). -/
structure V where
  b : ℕ
  t : ℕ
  u : ℕ
  y : ℕ
  x : ℕ

variable (p : Par)

namespace Par

/-- Slot width. -/
def wy : ℕ := p.ρ + p.n * p.K + p.m

/-- Compact width. -/
def wc : ℕ := p.n * p.G

end Par

/-- Toggle the parity of `v` when `z = 1`. -/
def tog (v z : ℕ) : ℕ := v + z - 2 * (z * (v % 2))

/-- Rotation of a `w`-bit value by `+ o` or `- o`. -/
def rotv (w : ℕ) (neg : Bool) (o y : ℕ) : ℕ :=
  if neg then (y + (2 ^ w - o % 2 ^ w)) % 2 ^ w else (y + o) % 2 ^ w

lemma rotv_lt (w : ℕ) (neg : Bool) (o y : ℕ) : rotv w neg o y < 2 ^ w := by
  unfold rotv; split_ifs <;> exact Nat.mod_lt _ (by positivity)

private lemma mod_cancel {n y o : ℕ} (h0 : 0 < n) (hy : y < n) :
    (y + o + (n - o % n)) % n = y := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < n ∧ o = r + n * q :=
    ⟨o / n, o % n, Nat.mod_lt _ h0, (Nat.mod_add_div o n).symm⟩
  have hrm : (r + n * q) % n = r := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have hs : r + (n - r) = n := Nat.add_sub_cancel' hr.le
  rw [hrm, show y + (r + n * q) + (n - r) = y + n * (q + 1) by linarith,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]

lemma rotv_rotv {w y : ℕ} (neg : Bool) (o : ℕ) (hy : y < 2 ^ w) :
    rotv w (!neg) o (rotv w neg o y) = y := by
  have h0 : 0 < 2 ^ w := by positivity
  unfold rotv
  cases neg
  · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    rw [Nat.mod_add_mod]
    exact mod_cancel h0 hy
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [Nat.mod_add_mod, Nat.add_right_comm]
    exact mod_cancel h0 hy


/-- Control bit `c`: the parity of digit `c` of `u`. -/
def zc (c : ℕ) (v : V) : ℕ := cdig p.G c v.u % 2

/-- The parity of segment `c` of a slot value. -/
def par (c Y : ℕ) : ℕ := seg p.ρ p.K c Y % 2

/-- The offsets. -/
inductive Off where
  /-- `∑ 2 z_c t_c 2^(ρ + c K)`: twice the control times the temporary digit, in `y`. -/
  | A
  /-- `∑ z_c 2^(ρ + c K)`: the controls, in `y`. -/
  | Z
  /-- `∑ y_c 2^(c G)`: the selected bits of `y`, in `b`. -/
  | Y
  /-- `∑ (y_c ⊕ z_c) 2^(c G)`, in `b`. -/
  | YZ
  /-- `∑ x_c 2^(c G)`: the selected bits of `x`, in `b`. -/
  | X
  deriving DecidableEq

def Off.eval : Off → V → ℕ
  | .A, v => ∑ c ∈ range p.n, (2 * zc p c v * cdig p.G c v.t) * 2 ^ (p.ρ + c * p.K)
  | .Z, v => ∑ c ∈ range p.n, zc p c v * 2 ^ (p.ρ + c * p.K)
  | .Y, v => casm p.G p.n fun c => par p c v.y
  | .YZ, v => casm p.G p.n fun c => (par p c v.y + zc p c v) % 2
  | .X, v => casm p.G p.n fun c => par p c v.x

/-- The instructions. -/
inductive Op where
  | rotY (neg : Bool) (o : Off)
  | rotB (neg : Bool) (o : Off)
  | swapT
  | swapU
  deriving DecidableEq

/-- The semantics of an instruction on the five fields. -/
def Op.pure : Op → V → V
  | .rotY neg o, v => { v with y := rotv p.wy neg (o.eval p v) v.y }
  | .rotB neg o, v => { v with b := rotv p.wc neg (o.eval p v) v.b }
  | .swapT, v => { v with b := v.t, t := v.b }
  | .swapU, v => { v with b := v.u, u := v.b }

/-- The four dirty-temporary updates with control `u mod 2`. -/
def E : List Op :=
  [.rotY false .A, .swapT, .rotB false .Y, .swapT, .rotY false .Z, .rotY true .A, .swapT,
    .rotB true .YZ, .swapT]

/-- The complete program: `E`, load `x` into `u`, `E`, unload. -/
def prog : List Op :=
  E ++ [.swapU, .rotB false .X, .swapU] ++ E ++ [.swapU, .rotB true .X, .swapU]

/-- Run a list of instructions. -/
def run (l : List Op) (v : V) : V := l.foldl (fun v o => o.pure p v) v

/-- `Y` with every used segment `c` toggled by `z c`. -/
def togY (z : ℕ → ℕ) (Y : ℕ) : ℕ :=
  asm p.ρ p.K p.n (Y % 2 ^ p.ρ) (fun c => tog (seg p.ρ p.K c Y) (z c)) (Y / 2 ^ (p.ρ + p.n * p.K))

/-- The ideal map: every used segment of `y` toggled by the selected bit of `x`. -/
def ideal (v : V) : V := { v with y := togY p (fun c => par p c v.x) v.y }

/-- A state in range. -/
structure Fits (v : V) : Prop where
  b : v.b < 2 ^ p.wc
  t : v.t < 2 ^ p.wc
  u : v.u < 2 ^ p.wc
  y : v.y < 2 ^ p.wy

/-- A good state: no temporary or control digit at its maximum and every guard below its
bound. -/
def Good (v : V) : Prop :=
  ∀ c < p.n, cdig p.G c v.t + 1 < 2 ^ p.G ∧ cdig p.G c v.u + 1 < 2 ^ p.G ∧
    seg p.ρ p.K c v.y / 2 + 2 ^ p.G < 2 ^ (p.K - 1)

/-! ### Rotations of assembled values -/

section Rot

variable {p}

lemma rotv_pos_asm {low top : ℕ} {s δ : ℕ → ℕ} (hlow : low < 2 ^ p.ρ)
    (hs : ∀ c < p.n, s c + δ c < 2 ^ p.K) (htop : top < 2 ^ p.m) :
    rotv p.wy false (∑ c ∈ range p.n, δ c * 2 ^ (p.ρ + c * p.K)) (asm p.ρ p.K p.n low s top) =
      asm p.ρ p.K p.n low (fun c => s c + δ c) top := by
  simp only [rotv, Bool.false_eq_true, ite_false, Par.wy]
  rw [asm_add, Nat.mod_eq_of_lt (asm_lt hlow hs htop)]

lemma rotv_neg_asm {low top : ℕ} {s δ : ℕ → ℕ} (hlow : low < 2 ^ p.ρ)
    (hs : ∀ c < p.n, s c < 2 ^ p.K) (hδ : ∀ c < p.n, δ c ≤ s c) (htop : top < 2 ^ p.m) :
    rotv p.wy true (∑ c ∈ range p.n, δ c * 2 ^ (p.ρ + c * p.K)) (asm p.ρ p.K p.n low s top) =
      asm p.ρ p.K p.n low (fun c => s c - δ c) top := by
  have he : asm p.ρ p.K p.n low (fun c => s c - δ c) top +
      (∑ c ∈ range p.n, δ c * 2 ^ (p.ρ + c * p.K)) = asm p.ρ p.K p.n low s top := by
    rw [asm_add]
    exact asm_congr fun c hc => Nat.sub_add_cancel (hδ c hc)
  have hy := asm_lt hlow hs htop
  have hy' : asm p.ρ p.K p.n low (fun c => s c - δ c) top < 2 ^ p.wy :=
    asm_lt hlow (fun c hc => lt_of_le_of_lt (Nat.sub_le _ _) (hs c hc)) htop
  generalize asm p.ρ p.K p.n low (fun c => s c - δ c) top = a at he hy'
  generalize ∑ c ∈ range p.n, δ c * 2 ^ (p.ρ + c * p.K) = o at he
  unfold Par.wy at hy hy'
  simp only [rotv, ite_true, Par.wy]
  rw [← he] at hy ⊢
  have ho : o < 2 ^ (p.ρ + p.n * p.K + p.m) := by omega
  rw [Nat.mod_eq_of_lt ho, show a + o + (2 ^ (p.ρ + p.n * p.K + p.m) - o) =
    a + 2 ^ (p.ρ + p.n * p.K + p.m) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hy']

lemma rotv_pos_casm {s δ : ℕ → ℕ} (hs : ∀ c < p.n, s c + δ c < 2 ^ p.G) :
    rotv p.wc false (casm p.G p.n δ) (casm p.G p.n s) = casm p.G p.n fun c => s c + δ c := by
  simp only [rotv, Bool.false_eq_true, ite_false, Par.wc]
  rw [casm_add, Nat.mod_eq_of_lt (casm_lt hs)]

lemma rotv_neg_casm {s δ : ℕ → ℕ} (hs : ∀ c < p.n, s c < 2 ^ p.G)
    (hδ : ∀ c < p.n, δ c ≤ s c) :
    rotv p.wc true (casm p.G p.n δ) (casm p.G p.n s) = casm p.G p.n fun c => s c - δ c := by
  have he : casm p.G p.n (fun c => s c - δ c) + casm p.G p.n δ = casm p.G p.n s := by
    rw [casm_add]
    exact casm_congr fun c hc => Nat.sub_add_cancel (hδ c hc)
  have hy : casm p.G p.n s < 2 ^ (p.n * p.G) := casm_lt hs
  have hy' : casm p.G p.n (fun c => s c - δ c) < 2 ^ (p.n * p.G) :=
    casm_lt fun c hc => lt_of_le_of_lt (Nat.sub_le _ _) (hs c hc)
  generalize casm p.G p.n (fun c => s c - δ c) = a at he hy'
  generalize casm p.G p.n δ = o at he
  simp only [rotv, ite_true, Par.wc]
  rw [← he] at hy ⊢
  have ho : o < 2 ^ (p.n * p.G) := by omega
  rw [Nat.mod_eq_of_lt ho, show a + o + (2 ^ (p.n * p.G) - o) = a + 2 ^ (p.n * p.G) by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hy']

end Rot

/-! ### One segment of the four updates -/

/-- The four updates on one segment `s` with temporary digit `w` and control `z`, in natural
numbers, under the guard. -/
lemma segment_updates {s w z B L : ℕ} (hz : z = 0 ∨ z = 1) (hw : w + 1 < B)
    (hg : s / 2 + B < L) :
    s + 2 * z * w < 2 * L ∧ (s + 2 * z * w) % 2 = s % 2 ∧
      s + 2 * z * w + z < 2 * L ∧ 2 * z * (w + s % 2) ≤ s + 2 * z * w + z ∧
      s + 2 * z * w + z - 2 * z * (w + s % 2) = tog s z := by
  unfold tog
  rcases hz with rfl | rfl <;> simp only [zero_mul, mul_zero, Nat.add_zero, mul_one,
    Nat.sub_zero, Nat.zero_le, and_true, true_and] <;> omega

lemma tog_div_two {v z : ℕ} (hz : z = 0 ∨ z = 1) : tog v z / 2 = v / 2 := by
  unfold tog; rcases hz with rfl | rfl <;> omega

lemma tog_mod_two {v z : ℕ} (hz : z = 0 ∨ z = 1) : tog v z % 2 = (v % 2 + z) % 2 := by
  unfold tog; rcases hz with rfl | rfl <;> omega

lemma tog_lt {v z L : ℕ} (hz : z = 0 ∨ z = 1) (hv : v / 2 + 1 < L) : tog v z < 2 * L := by
  unfold tog; rcases hz with rfl | rfl <;> omega

lemma tog_zero (v : ℕ) : tog v 0 = v := by simp [tog]

lemma tog_one (v : ℕ) : tog v 1 = v + 1 - 2 * (v % 2) := by simp [tog]

/-- The later-source identity on natural numbers. -/
lemma tog_tog (v u x : ℕ) (hx : x = 0 ∨ x = 1) :
    tog (tog v (u % 2)) ((u + x) % 2) = tog v x := by
  rcases hx with rfl | rfl <;> rcases Nat.mod_two_eq_zero_or_one u with hu | hu
  · simp only [Nat.add_zero, hu, tog_zero]
  · simp only [Nat.add_zero, hu, tog_zero, tog_one]
    omega
  · simp only [show (u + 1) % 2 = 1 by omega, hu, tog_zero]
  · simp only [show (u + 1) % 2 = 0 by omega, hu, tog_zero]

lemma mod_two_cases (a : ℕ) : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a

/-! ### The four updates on the fields -/

section E

variable {p}

lemma zc_cases (c : ℕ) (v : V) : zc p c v = 0 ∨ zc p c v = 1 := mod_two_cases _

lemma seg_lt (c Y : ℕ) : seg p.ρ p.K c Y < 2 ^ p.K := window_lt _ _ _

lemma cdig_lt (c w : ℕ) : cdig p.G c w < 2 ^ p.G := window_lt _ _ _

lemma low_lt (Y : ℕ) : Y % 2 ^ p.ρ < 2 ^ p.ρ := Nat.mod_lt _ (by positivity)

lemma top_lt {Y : ℕ} (hY : Y < 2 ^ p.wy) : Y / 2 ^ (p.ρ + p.n * p.K) < 2 ^ p.m := by
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, Nat.add_comm p.m]
  exact hY

/-- The parts of an assembled slot value. -/
lemma par_asm {low top c : ℕ} {s : ℕ → ℕ} (hlow : low < 2 ^ p.ρ) (hs : ∀ c < p.n, s c < 2 ^ p.K)
    (hc : c < p.n) : par p c (asm p.ρ p.K p.n low s top) = s c % 2 := by
  rw [par, seg_asm hlow hs hc]

/-- **The four updates.** On a state with good temporaries and guards, `E` toggles every
segment of `y` by the control bit and keeps `b`, `t`, `u`, `x`. -/
theorem run_E {v : V} (hv : Fits p v)
    (ht : ∀ c < p.n, cdig p.G c v.t + 1 < 2 ^ p.G)
    (hg : ∀ c < p.n, seg p.ρ p.K c v.y / 2 + 2 ^ p.G < 2 ^ (p.K - 1)) (hK : 1 ≤ p.K) :
    run p E v = { v with y := togY p (fun c => zc p c v) v.y } := by
  obtain ⟨b, t, u, y, x⟩ := v
  have hb : b < 2 ^ p.wc := hv.b
  have htf : t < 2 ^ p.wc := hv.t
  have hy : y < 2 ^ p.wy := hv.y
  simp only at ht hg ⊢
  have hL : 2 ^ p.K = 2 * 2 ^ (p.K - 1) := by
    rw [← pow_succ']; congr 1; omega
  set low := y % 2 ^ p.ρ
  set top := y / 2 ^ (p.ρ + p.n * p.K)
  set s : ℕ → ℕ := fun c => seg p.ρ p.K c y
  set w : ℕ → ℕ := fun c => cdig p.G c t
  set z : ℕ → ℕ := fun c => cdig p.G c u % 2
  have hlow : low < 2 ^ p.ρ := low_lt y
  have htop : top < 2 ^ p.m := top_lt hy
  have hs : ∀ c < p.n, s c < 2 ^ p.K := fun c _ => seg_lt c y
  have hw : ∀ c < p.n, w c < 2 ^ p.G := fun c _ => cdig_lt c t
  have hz : ∀ c, z c = 0 ∨ z c = 1 := fun c => mod_two_cases _
  have hy₀ : y = asm p.ρ p.K p.n low s top := eq_asm p.ρ p.K p.n y
  have ht₀ : t = casm p.G p.n w := eq_casm p.G p.n t htf
  -- step 1: y ← y + ∑ 2 z w 2^(ρ + c K)
  set s₁ : ℕ → ℕ := fun c => s c + 2 * z c * w c
  have hs₁ : ∀ c < p.n, s₁ c < 2 ^ p.K := fun c hc => by
    rw [hL]; exact (segment_updates (hz c) (ht c hc) (hg c hc)).1
  have hA₀ : Off.eval p .A ⟨b, t, u, y, x⟩ =
      ∑ c ∈ range p.n, (2 * z c * w c) * 2 ^ (p.ρ + c * p.K) := rfl
  have h1 : rotv p.wy false (Off.eval p .A ⟨b, t, u, y, x⟩) y = asm p.ρ p.K p.n low s₁ top := by
    rw [hA₀, hy₀]
    exact rotv_pos_asm hlow (fun c hc => hs₁ c hc) htop
  -- step 3: b position (holding t) ← t + ∑ y_c 2^(c G)
  have hpar₁ : ∀ c < p.n, par p c (asm p.ρ p.K p.n low s₁ top) = s c % 2 := fun c hc => by
    rw [par_asm hlow hs₁ hc]
    exact (segment_updates (hz c) (ht c hc) (hg c hc)).2.1
  set w₁ : ℕ → ℕ := fun c => w c + s c % 2
  have hw₁ : ∀ c < p.n, w₁ c < 2 ^ p.G := fun c hc => by
    have := ht c hc; have := Nat.mod_lt (s c) (show 0 < 2 by norm_num); simp only [w₁, w]; omega
  have h3 : rotv p.wc false (Off.eval p .Y ⟨t, b, u, asm p.ρ p.K p.n low s₁ top, x⟩) t =
      casm p.G p.n w₁ := by
    have hY : Off.eval p .Y ⟨t, b, u, asm p.ρ p.K p.n low s₁ top, x⟩ =
        casm p.G p.n fun c => s c % 2 := casm_congr fun c hc => hpar₁ c hc
    rw [hY, ht₀]
    exact rotv_pos_casm fun c hc => hw₁ c hc
  -- step 5 and 6: y ← y + ∑ z 2^(ρ + c K) - ∑ 2 z w₁ 2^(ρ + c K)
  set s₂ : ℕ → ℕ := fun c => s₁ c + z c
  have hs₂ : ∀ c < p.n, s₂ c < 2 ^ p.K := fun c hc => by
    rw [hL]; exact (segment_updates (hz c) (ht c hc) (hg c hc)).2.2.1
  have hZ : Off.eval p .Z ⟨b, casm p.G p.n w₁, u, asm p.ρ p.K p.n low s₁ top, x⟩ =
      ∑ c ∈ range p.n, z c * 2 ^ (p.ρ + c * p.K) := rfl
  have h5 : rotv p.wy false (Off.eval p .Z ⟨b, casm p.G p.n w₁, u, asm p.ρ p.K p.n low s₁ top, x⟩)
      (asm p.ρ p.K p.n low s₁ top) = asm p.ρ p.K p.n low s₂ top := by
    rw [hZ]; exact rotv_pos_asm hlow (fun c hc => hs₂ c hc) htop
  have hA₁ : Off.eval p .A ⟨b, casm p.G p.n w₁, u, asm p.ρ p.K p.n low s₂ top, x⟩ =
      ∑ c ∈ range p.n, (2 * z c * w₁ c) * 2 ^ (p.ρ + c * p.K) := by
    simp only [Off.eval, zc]
    exact sum_congr rfl fun c hc => by rw [cdig_casm hw₁ (mem_range.1 hc)]
  set s₃ : ℕ → ℕ := fun c => tog (s c) (z c)
  have h6 : rotv p.wy true (Off.eval p .A ⟨b, casm p.G p.n w₁, u, asm p.ρ p.K p.n low s₂ top, x⟩)
      (asm p.ρ p.K p.n low s₂ top) = asm p.ρ p.K p.n low s₃ top := by
    rw [hA₁, rotv_neg_asm hlow hs₂
      (fun c hc => (segment_updates (hz c) (ht c hc) (hg c hc)).2.2.2.1) htop]
    exact asm_congr fun c hc => (segment_updates (hz c) (ht c hc) (hg c hc)).2.2.2.2
  -- step 8: b position (holding w₁) ← w₁ - ∑ (y_c ⊕ z_c) 2^(c G)
  have hs₃ : ∀ c < p.n, s₃ c < 2 ^ p.K := fun c hc => by
    rw [hL]
    exact tog_lt (hz c) (lt_of_le_of_lt (Nat.add_le_add_left Nat.one_le_two_pow _) (hg c hc))
  have hYZ : Off.eval p .YZ ⟨casm p.G p.n w₁, b, u, asm p.ρ p.K p.n low s₃ top, x⟩ =
      casm p.G p.n fun c => s c % 2 := by
    refine casm_congr fun c hc => ?_
    change (par p c (asm p.ρ p.K p.n low s₃ top) + z c) % 2 = s c % 2
    rw [par_asm hlow hs₃ hc, tog_mod_two (hz c)]
    rcases hz c with h | h <;> rw [h] <;> omega
  have h8 : rotv p.wc true (Off.eval p .YZ ⟨casm p.G p.n w₁, b, u, asm p.ρ p.K p.n low s₃ top, x⟩)
      (casm p.G p.n w₁) = t := by
    rw [hYZ, rotv_neg_casm hw₁ (fun c _ => Nat.le_add_left _ _), ht₀]
    exact casm_congr fun c _ => by simp [w₁]
  simp only [run, E, List.foldl_cons, List.foldl_nil, Op.pure]
  rw [h1, h3, h5, h6, h8]
  rfl

end E

/-! ### The complete program -/

section Prog

variable {p}

lemma run_append (l l' : List Op) (v : V) : run p (l ++ l') v = run p l' (run p l v) := by
  simp [run, List.foldl_append]

/-- **Main theorem.** On every good state in range the program is the ideal XOR. -/
theorem prog_good {v : V} (hv : Fits p v) (hgood : Good p v) (hK : 1 ≤ p.K) :
    run p prog v = ideal p v := by
  obtain ⟨b, t, u, y, x⟩ := v
  have ht : ∀ c < p.n, cdig p.G c t + 1 < 2 ^ p.G := fun c hc => (hgood c hc).1
  have hu : ∀ c < p.n, cdig p.G c u + 1 < 2 ^ p.G := fun c hc => (hgood c hc).2.1
  have hg : ∀ c < p.n, seg p.ρ p.K c y / 2 + 2 ^ p.G < 2 ^ (p.K - 1) :=
    fun c hc => (hgood c hc).2.2
  have hy : y < 2 ^ p.wy := hv.y
  have hL : 2 ^ p.K = 2 * 2 ^ (p.K - 1) := by
    rw [← pow_succ']; congr 1; omega
  set low := y % 2 ^ p.ρ
  set top := y / 2 ^ (p.ρ + p.n * p.K)
  have hlow : low < 2 ^ p.ρ := low_lt y
  have htop : top < 2 ^ p.m := top_lt hy
  set s : ℕ → ℕ := fun c => seg p.ρ p.K c y
  set z : ℕ → ℕ := fun c => cdig p.G c u % 2
  set xc : ℕ → ℕ := fun c => par p c x
  have hz : ∀ c, z c = 0 ∨ z c = 1 := fun c => mod_two_cases _
  have hxc : ∀ c, xc c = 0 ∨ xc c = 1 := fun c => mod_two_cases _
  -- the first pass of E
  have hE₁ := run_E (p := p) (v := ⟨b, t, u, y, x⟩) hv ht hg hK
  simp only at hE₁
  have hy₁def : togY p (fun c => zc p c ⟨b, t, u, y, x⟩) y =
      asm p.ρ p.K p.n low (fun c => tog (s c) (z c)) top := rfl
  rw [hy₁def] at hE₁
  set y₁ := asm p.ρ p.K p.n low (fun c => tog (s c) (z c)) top
  have hs₁ : ∀ c < p.n, tog (s c) (z c) < 2 ^ p.K := fun c hc => by
    rw [hL]
    exact tog_lt (hz c) (lt_of_le_of_lt (Nat.add_le_add_left Nat.one_le_two_pow _) (hg c hc))
  have hseg₁ : ∀ c < p.n, seg p.ρ p.K c y₁ = tog (s c) (z c) := fun c hc =>
    seg_asm hlow hs₁ hc
  have hy₁ : y₁ < 2 ^ p.wy := asm_lt hlow hs₁ htop
  -- the load
  have hu₀ : u = casm p.G p.n fun c => cdig p.G c u := eq_casm p.G p.n u hv.u
  set u₁ : ℕ → ℕ := fun c => cdig p.G c u + xc c with hu₁def
  have hu₁ : ∀ c < p.n, u₁ c < 2 ^ p.G := fun c hc => by
    have h1 := hu c hc
    have h2 : xc c ≤ 1 := by rcases hxc c with h | h <;> omega
    show cdig p.G c u + xc c < 2 ^ p.G
    omega
  have hload : run p [.swapU, .rotB false .X, .swapU] ⟨b, t, u, y₁, x⟩ =
      ⟨b, t, casm p.G p.n u₁, y₁, x⟩ := by
    simp only [run, List.foldl_cons, List.foldl_nil, Op.pure]
    have hX : Off.eval p .X ⟨u, t, b, y₁, x⟩ = casm p.G p.n xc := rfl
    have : rotv p.wc false (casm p.G p.n xc) (casm p.G p.n fun c => cdig p.G c u) =
        casm p.G p.n u₁ := rotv_pos_casm fun c hc => hu₁ c hc
    rw [← hu₀] at this
    rw [hX, this]
  -- the second pass of E
  have hcu₁ : ∀ c < p.n, cdig p.G c (casm p.G p.n u₁) = u₁ c := fun c hc => cdig_casm hu₁ hc
  have hE₂ := run_E (p := p) (v := ⟨b, t, casm p.G p.n u₁, y₁, x⟩)
    ⟨hv.b, hv.t, casm_lt hu₁, hy₁⟩ ht
    (fun c hc => by rw [hseg₁ c hc, tog_div_two (hz c)]; exact hg c hc) hK
  simp only at hE₂
  have hy₂ : togY p (fun c => zc p c ⟨b, t, casm p.G p.n u₁, y₁, x⟩) y₁ =
      asm p.ρ p.K p.n low (fun c => tog (s c) (xc c)) top := by
    unfold togY
    rw [asm_mod hlow, asm_div hlow hs₁]
    refine asm_congr fun c hc => ?_
    simp only [zc, hcu₁ c hc, hseg₁ c hc, u₁]
    exact tog_tog (s c) (cdig p.G c u) (xc c) (hxc c)
  rw [hy₂] at hE₂
  -- the unload
  have hunload : run p [.swapU, .rotB true .X, .swapU]
      ⟨b, t, casm p.G p.n u₁, asm p.ρ p.K p.n low (fun c => tog (s c) (xc c)) top, x⟩ =
      ⟨b, t, u, asm p.ρ p.K p.n low (fun c => tog (s c) (xc c)) top, x⟩ := by
    simp only [run, List.foldl_cons, List.foldl_nil, Op.pure]
    have hX : Off.eval p .X ⟨casm p.G p.n u₁, t, b,
        asm p.ρ p.K p.n low (fun c => tog (s c) (xc c)) top, x⟩ = casm p.G p.n xc := rfl
    have : rotv p.wc true (casm p.G p.n xc) (casm p.G p.n u₁) = u := by
      rw [rotv_neg_casm hu₁ (fun c _ => Nat.le_add_left _ _)]
      conv_rhs => rw [hu₀]
      exact casm_congr fun c _ => by simp [u₁]
    rw [hX, this]
  rw [prog, run_append, run_append, run_append, hE₁, hload, hE₂, hunload]
  rfl

end Prog

end IntegerMultBounds.MathlibTM2.Layer.CompactGadget
