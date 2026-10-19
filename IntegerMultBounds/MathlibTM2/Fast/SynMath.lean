module
public import IntegerMultBounds.MathlibTM2.Fast.RingProd
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import IntegerMultBounds.MathlibTM2.Fast.TwiddleL
public import IntegerMultBounds.MathlibTM2.Fast.LayoutMath
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.ENatToNat
public import IntegerMultBounds.MathlibTM2.Node.TopProc


/-!
# The computed transform rounds on physical record streams

Paper §6, proof of `lem:synthetic-transform-cost`. The transform machines keep the records in the
physical order of a layout `L : Equiv.Perm (Fin N)` of the address bits (logical bit `k` at
physical bit `L k`, `IntegerMultBounds.MathlibTM2.Mult.SynthErr.relabel`).

## Physical arrays

* `synPi L m = twGat (twPosL L) N m`: the logical address of the physical address `m` (bit `k`
  is bit `L k` of `m`); `synPi_lt`, `synPi_xor`, `synPi_layRec` (`synPi L` inverts the record
  permutation `layRec L` of `Fast/LayoutMath.lean`).
* `synPhys L u m = u (synPi L m)`: a logical record array stored physically.
* `bfly_comm`, `bflyL_perm`: normalized butterflies on distinct bits commute.
* `bfly_phys`, `bflyL_phys`: the butterfly on logical bit `q` is the butterfly on physical bit
  `L q`: `bflyL (l.map L) (synPhys L u) = synPhys L (bflyL l u)`.

## Gaussian-integer arrays of the layer

* `synZ n Y : ZArr (Fin 1 × Fin r) n`: the numerator records `Y` as an array of one row with
  `n` address bits; `encZ_synZ`: its stream is `cstream A w (rpStream (2^n) Y)`; `synRd`:
  reading an array back, `synZ_synRd`, `encZ_eq_synRd`.
* `Hl_synZ`: `Hl` on the selected bits of `toC (synZ n Y)` is `bflyL` on the records.
* `synTr_toComplex`: the componentwise truncation toward zero of `2^p x` is the numerator of
  `Q_p x` (`NLogN.rhoC`).
* `topPre_toC`: the array before the final shift of the layer is `2^s Hl sel`; `topPre_fits`:
  it fits `w'` signed bits when the input has modulus at most `2^p` and `s + p + 2 ≤ w'`;
  `synFits_of_disk`: disk numerators fit `w ≥ p + 2` signed bits.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.NLogN
  IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Node hiding LReg

set_option maxHeartbeats 1000000

/-! ### The physical order of a layout -/

section Phys

variable {N : ℕ} (L : Equiv.Perm (Fin N))

/-- The logical address of the physical address `m` in the layout `L`. -/
def synPi (m : ℕ) : ℕ := twGat (twPosL L) N m

theorem testBit_synPi (m k : ℕ) :
    (synPi L m).testBit k = (decide (k < N) && m.testBit (twPosL L k)) :=
  twGat_testBit _ _ _ _

theorem synPi_lt (m : ℕ) : synPi L m < 2 ^ N := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  rw [testBit_synPi]
  simp [show ¬ k < N by omega]

theorem twPosL_inj {k k' : ℕ} (hk : k < N) (hk' : k' < N) (h : twPosL L k = twPosL L k') :
    k = k' := by
  simp only [twPosL, hk, hk', ↓reduceDIte] at h
  have := L.injective (Fin.ext h)
  simpa using this

/-- Flipping physical bit `L q` flips logical bit `q`. -/
theorem synPi_xor {q : ℕ} (hq : q < N) (m : ℕ) :
    synPi L (m ^^^ 2 ^ twPosL L q) = synPi L m ^^^ 2 ^ q := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_synPi, Nat.testBit_xor, Nat.testBit_xor, testBit_synPi, Nat.testBit_two_pow,
    Nat.testBit_two_pow]
  by_cases hk : k < N
  · by_cases hkq : k = q
    · subst hkq; simp [hk]
    · have : twPosL L q ≠ twPosL L k := fun h => hkq (twPosL_inj L hk hq h.symm)
      simp [hk, this, Ne.symm hkq]
  · have : q ≠ k := by omega
    simp [hk, this]

theorem synPi_testBit_pos {q : ℕ} (hq : q < N) (m : ℕ) :
    m.testBit (twPosL L q) = (synPi L m).testBit q := by
  rw [testBit_synPi]; simp [hq]

/-- A logical record array stored in the physical order of `L`. -/
def synPhys {r : ℕ} (u : Recs r) : Recs r := fun m => u (synPi L m)

theorem bfly_phys {r : ℕ} {q : ℕ} (hq : q < N) (u : Recs r) :
    bfly (twPosL L q) (synPhys L u) = synPhys L (bfly q u) := by
  funext m
  simp only [bfly, synPhys, synPi_xor L hq, synPi_testBit_pos L hq]

theorem bflyL_phys {r : ℕ} (u : Recs r) :
    ∀ l : List ℕ, (∀ q ∈ l, q < N) →
      bflyL (l.map (twPosL L)) (synPhys L u) = synPhys L (bflyL l u)
  | [], _ => rfl
  | q :: l, h => by
      show bfly (twPosL L q) (bflyL (l.map (twPosL L)) (synPhys L u)) =
        synPhys L (bfly q (bflyL l u))
      rw [bflyL_phys u l (fun q' hq' => h q' (by simp [hq'])), bfly_phys L (h q (by simp))]

/-- `synPi L` inverts the record permutation of the layout. -/
theorem synPi_layRec (m : Fin (2 ^ N)) : synPi L m = ((layRec L).symm m : ℕ) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_synPi]
  have h1 : ((layRec L).symm m : ℕ) = layRecVal L.symm m := by
    rw [← layRec_symm]; rfl
  rw [h1, testBit_layRecVal]
  by_cases hk : k < N
  · simp [hk, twPosL]
  · simp [hk]

end Phys

/-! ### Butterflies on distinct bits commute -/

section Comm

variable {r : ℕ}

theorem bfly_comm {q q' : ℕ} (hqq : q ≠ q') (u : Recs r) :
    bfly q (bfly q' u) = bfly q' (bfly q u) := by
  funext n c
  have h1 : (n ^^^ 2 ^ q).testBit q' = n.testBit q' := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow]; simp [hqq]
  have h2 : (n ^^^ 2 ^ q').testBit q = n.testBit q := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow]; simp [Ne.symm hqq]
  have h3 : n ^^^ 2 ^ q ^^^ 2 ^ q' = n ^^^ 2 ^ q' ^^^ 2 ^ q := by
    rw [Nat.xor_assoc, Nat.xor_comm (2 ^ q), ← Nat.xor_assoc]
  simp only [bfly, Pi.smul_apply, Pi.add_apply, smul_eq_mul, h1, h2, h3]
  split_ifs <;> ring

theorem bflyL_perm {l l' : List ℕ} (h : l.Perm l') (hl : l.Nodup) (u : Recs r) :
    bflyL l u = bflyL l' u := by
  induction h generalizing u with
  | nil => rfl
  | cons x _ ih =>
      show bfly x (bflyL _ u) = bfly x (bflyL _ u)
      rw [ih (List.nodup_cons.1 hl).2]
  | swap x y l =>
      show bfly y (bfly x (bflyL l u)) = bfly x (bfly y (bflyL l u))
      have hxy : x ≠ y := by
        intro e; subst e; simp at hl
      rw [bfly_comm (Ne.symm hxy)]
  | trans h₁ _ ih₁ ih₂ => rw [ih₁ hl, ih₂ (h₁.nodup_iff.1 hl)]

end Comm

/-! ### Gaussian-integer arrays of one row -/

section Arrays

variable {r : ℕ}

theorem ofBits_addrBits {n x : ℕ} (hx : x < 2 ^ n) : ofBits (addrBits n x) = x := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_ofBits]
  by_cases hj : j < n
  · simp only [hj, ↓reduceDIte, addrBits]
    by_cases h : x.testBit j <;> simp [h]
  · simp only [hj, ↓reduceDIte]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num)
      (by omega)))).symm

theorem addrBits_ofBits {n : ℕ} (b : Fin n → ZMod 2) : addrBits n (ofBits b) = b := by
  funext t
  simp only [addrBits, testBit_ofBits_fin]
  rcases zmod2_cases (b t) with h | h <;> simp [h]

/-- The numerator records `Y` as an array of one row with `n` address bits. -/
def synZ (n : ℕ) (Y : ℕ → Fin r → GaussianInt) : ZArr (Fin 1 × Fin r) n :=
  fun p => Y (ofBits p.2) p.1.2

/-- The records of an array of one row. -/
def synRd {n : ℕ} (Z : ZArr (Fin 1 × Fin r) n) : ℕ → Fin r → GaussianInt :=
  fun x c => Z ((0, c), addrBits n x)

theorem synZ_synRd {n : ℕ} (Z : ZArr (Fin 1 × Fin r) n) : synZ n (synRd Z) = Z := by
  funext p
  obtain ⟨⟨u, c⟩, b⟩ := p
  simp only [synZ, synRd, addrBits_ofBits]
  congr 3
  exact (Fin.fin_one_eq_zero u).symm

theorem recList_synZ (w n : ℕ) (Y : ℕ → Fin r → GaussianInt) :
    recList w (synZ n Y) =
      (List.range (2 ^ n)).map fun x => List.ofFn fun c => red w (Y x c) := by
  simp only [recList, synZ]
  rw [show (List.finRange 1) = [0] from rfl, List.flatMap_singleton]
  refine List.map_congr_left fun x hx => ?_
  rw [ofBits_addrBits (List.mem_range.1 hx)]

/-- The stream of an array of one row is the coefficient stream of its records. -/
theorem encZ_synZ (A w n : ℕ) (Y : ℕ → Fin r → GaussianInt) :
    encZ A w (synZ n Y) = cstream A w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ n) Y) := by
  simp only [encZ, coeffList, recList_synZ, cstream, IntegerMultBounds.MathlibTM2.Fast.rpStream]
  rw [List.flatten_eq_flatMap, List.flatMap_map, List.flatMap_assoc, List.flatMap_assoc]
  refine List.flatMap_congr fun x _ => ?_
  have : (List.ofFn fun c => red w (Y x c)) = (List.ofFn (Y x)).map (red w) := by
    rw [List.map_ofFn]; rfl
  simp only [id, this, List.flatMap_map]

theorem encZ_eq_synRd (A w n : ℕ) (Z : ZArr (Fin 1 × Fin r) n) :
    encZ A w Z = cstream A w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ n) (synRd Z)) := by
  conv_lhs => rw [← synZ_synRd Z]
  exact encZ_synZ A w n _

theorem rpStream_congr {M : ℕ} {Y Y' : ℕ → Fin r → GaussianInt} (h : ∀ x < M, Y x = Y' x) :
    IntegerMultBounds.MathlibTM2.Fast.rpStream M Y = IntegerMultBounds.MathlibTM2.Fast.rpStream M Y' := by
  simp only [IntegerMultBounds.MathlibTM2.Fast.rpStream]
  exact List.flatMap_congr fun x hx => by rw [h x (List.mem_range.1 hx)]

/-- `Hl` on bits of the array of one row is `bflyL` on the records. -/
theorem Hl_synZ_aux {n : ℕ} {X : Type} (g : X → Fin r) (u : ℕ → Fin r → ℂ) :
    ∀ l : List (Fin n), Hl X l (fun p => u (ofBits p.2) (g p.1)) =
      fun p => bflyL (l.map Fin.val) (fun x c => u x c) (ofBits p.2) (g p.1)
  | [] => by simp [bflyL, Hl]
  | t :: l => by
      rw [Hl_cons, Hl_synZ_aux g u l]
      funext p
      obtain ⟨x, b⟩ := p
      simp only [hBit, LinearMap.coe_mk, AddHom.coe_mk, List.map_cons]
      show _ = bfly t (bflyL (l.map Fin.val) fun x c => u x c) (ofBits b) (g x)
      simp only [bfly, Pi.smul_apply, Pi.add_apply, smul_eq_mul, testBit_ofBits_fin,
        ofBits_flip]
      rcases zmod2_cases (b t) with h | h <;> simp [h] <;> ring

theorem Hl_synZ {n : ℕ} (Y : ℕ → Fin r → GaussianInt) (l : List (Fin n)) :
    Hl (Fin 1 × Fin r) l (toC (synZ n Y)) =
      fun p => bflyL (l.map Fin.val) (fun x c => GaussianInt.toComplex (Y x c)) (ofBits p.2) p.1.2 :=
  Hl_synZ_aux (fun x : Fin 1 × Fin r => x.2) (fun x c => GaussianInt.toComplex (Y x c)) l

end Arrays

/-! ### Truncation toward zero -/

section Trunc

theorem truncR_eq_rho0 (x : ℝ) : IntegerMultBounds.MathlibTM2.Layer.truncR x = rho0 x := rfl

/-- The componentwise truncation toward zero of `2^p x` is the numerator of `Q_p x`. -/
theorem synTr_toComplex (p : ℕ) (x : ℂ) :
    GaussianInt.toComplex (⟨IntegerMultBounds.MathlibTM2.Layer.truncR ((2 ^ p : ℂ) * x).re,
      IntegerMultBounds.MathlibTM2.Layer.truncR ((2 ^ p : ℂ) * x).im⟩ : GaussianInt) / 2 ^ p = rhoC p x := by
  have hre : ((2 ^ p : ℂ) * x).re = 2 ^ p * x.re := by
    rw [show (2 ^ p : ℂ) = ((2 ^ p : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  have him : ((2 ^ p : ℂ) * x).im = 2 ^ p * x.im := by
    rw [show (2 ^ p : ℂ) = ((2 ^ p : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul]
  simp only [truncR_eq_rho0]
  apply Complex.ext
  · rw [rhoC_re, hre, GaussianInt.toComplex_def']
    simp only [Complex.div_re, Complex.add_re, Complex.intCast_re, Complex.mul_re,
      Complex.I_re, Complex.intCast_im, Complex.I_im]
    have h2 : ((2 : ℂ) ^ p).re = 2 ^ p := by
      rw [show (2 : ℂ) ^ p = ((2 ^ p : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
    have h3 : ((2 : ℂ) ^ p).im = 0 := by
      rw [show (2 : ℂ) ^ p = ((2 ^ p : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_im]
    rw [Complex.normSq_apply, h2, h3]
    have hp : (2 : ℝ) ^ p ≠ 0 := by positivity
    field_simp
    ring
  · rw [rhoC_im, him, GaussianInt.toComplex_def']
    simp only [Complex.div_im, Complex.add_im, Complex.intCast_re, Complex.mul_im,
      Complex.I_re, Complex.intCast_im, Complex.I_im, Complex.add_re, Complex.mul_re]
    have h2 : ((2 : ℂ) ^ p).re = 2 ^ p := by
      rw [show (2 : ℂ) ^ p = ((2 ^ p : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
    have h3 : ((2 : ℂ) ^ p).im = 0 := by
      rw [show (2 : ℂ) ^ p = ((2 ^ p : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_im]
    rw [Complex.normSq_apply, h2, h3]
    have hp : (2 : ℝ) ^ p ≠ 0 := by positivity
    field_simp
    ring

end Trunc

/-! ### The layer before its final shift -/

section Pre

variable {R r n : ℕ}

/-- The array before the final shift of the layer is `2^s` times the normalized butterflies. -/
theorem topPre_toC (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (a : ℕ) (low : List (Fin n)) (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂)
    (Ps : List (Piece n R₂)) (hinj : ∀ P ∈ Ps, Function.Injective P.e)
    (hcover : (Ps.flatMap Piece.bitsList).Perm low)
    (hsel : (low.map (Fin.castAdd a) ++ top).Nodup)
    (s : ℕ) (hs : s = (low.length + top.length + 1) / 2 + top.length + (Ps.map (Piece.exp ds)).sum)
    (Z : ZArr (Fin R × Fin r) (n + a)) :
    toC (topPre ds a low top hR₂ Ps Z) =
      (2 : ℂ) ^ s • Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) := by
  set sel : List (Fin (n + a)) := low.map (Fin.castAdd a) ++ top with hsel_def
  set L := Ps.flatMap Piece.bitsList
  set E := (Ps.map (Piece.exp ds)).sum
  set Z₂ := k2s top (sZ sel Z)
  set Z₃ := ofRows a (unpadRows hR₂ (piecesZ ds Ps (padRows R₂ (toRows a Z₂))))
  set D := sel.length with hD
  set F := Sl _ sel (Cl _ sel (Sl _ sel (toC Z)))
  have hZ₂ : toC Z₂ = (2 : ℂ) ^ top.length • Cl _ top (Sl _ sel (toC Z)) := by
    rw [toC_k2s, prod_reverse_kBit, toC_sZ]; rfl
  have hZ₃ : toC Z₃ = (2 : ℂ) ^ (E + top.length) • Cl _ sel (Sl _ sel (toC Z)) := by
    rw [toC_ofRows a L _ Z₂ _ (toC_unpad_pad hR₂ L _ _ _ (toC_piecesZ ds hd Ps hinj _)),
      Cl_perm (hcover.map _), hZ₂, map_smul, smul_smul, ← pow_add, hsel_def, Cl_append]
  have hZ₄ : toC (sZ sel Z₃) = (2 : ℂ) ^ (E + top.length) • F := by
    rw [toC_sZ, hZ₃, map_smul]
  have hDlen : D = low.length + top.length := by
    rw [hD, hsel_def, List.length_append, List.length_map]
  funext p
  have hH : Hl _ sel (toC Z) p = ((1 - Complex.I) / 2) ^ D * F p := by
    rw [Hl_eq sel hsel]; rfl
  change GaussianInt.toComplex (unitD D * sZ sel Z₃ p) = _
  rw [map_mul]
  change GaussianInt.toComplex (unitD D) * toC (sZ sel Z₃) p = _
  rw [hZ₄, Pi.smul_apply, smul_eq_mul, Pi.smul_apply, smul_eq_mul, hH, div_pow, one_sub_I_pow,
    hs, ← hDlen]
  have h2D : (2 : ℂ) ^ ((D + 1) / 2) * 2 ^ (D / 2) = 2 ^ D := by
    rw [← pow_add]; congr 1; omega
  have h2 : (2 : ℂ) ^ D ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [pow_add, pow_add]
  field_simp
  linear_combination (-(GaussianInt.toComplex (unitD D) * F p * 2 ^ top.length)) * h2D

/-- Normalized butterflies do not increase the coefficient bound. -/
theorem Hl_norm_le {X : Type} (l : List (Fin n)) (f : Arr X n) {B : ℝ}
    (hf : ∀ q, ‖f q‖ ≤ B) : ∀ q, ‖Hl X l f q‖ ≤ B := by
  induction l with
  | nil => simpa [Hl] using hf
  | cons t l ih =>
      intro q
      rw [Hl_cons]
      simp only [hBit, LinearMap.coe_mk, AddHom.coe_mk]
      have h1 := ih q
      have h2 := ih (q.1, Layer.flip t q.2)
      have hs : ‖(if q.2 t = 0 then (1 : ℂ) else -1)‖ = 1 := by split_ifs <;> simp
      have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [norm_div, hn2]
      calc ‖(if q.2 t = 0 then (1 : ℂ) else -1) * Hl X l f q + Hl X l f (q.1, Layer.flip t q.2)‖ / 2
          ≤ (‖(if q.2 t = 0 then (1 : ℂ) else -1)‖ * ‖Hl X l f q‖ +
              ‖Hl X l f (q.1, Layer.flip t q.2)‖) / 2 := by
            gcongr
            exact (norm_add_le _ _).trans (by rw [norm_mul])
        _ ≤ (1 * B + B) / 2 := by rw [hs]; gcongr
        _ = B := by ring

/-- An integer of modulus at most `2^k` fits a signed `w'`-bit word when `k + 2 ≤ w'`. -/
theorem topFits_of_le {x : ℤ} {k w' : ℕ} (hx : |(x : ℝ)| ≤ 2 ^ k) (hk : k + 2 ≤ w') :
    TopFits w' x := by
  have h1 : |x| ≤ 2 ^ k := by exact_mod_cast hx
  have h2 : (2 : ℤ) ^ k < 2 ^ (w' - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  rw [abs_le] at h1
  exact ⟨by linarith, by linarith⟩

theorem topFitsZ_of_norm {z : GaussianInt} {k w' : ℕ}
    (hz : ‖GaussianInt.toComplex z‖ ≤ 2 ^ k) (hk : k + 2 ≤ w') : TopFitsZ w' z := by
  refine ⟨topFits_of_le ?_ hk, topFits_of_le ?_ hk⟩
  · have := Complex.abs_re_le_norm (GaussianInt.toComplex z)
    rw [GaussianInt.toComplex_def'] at this hz
    simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.I_re, Complex.intCast_im,
      Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero] at this
    linarith
  · have := Complex.abs_im_le_norm (GaussianInt.toComplex z)
    rw [GaussianInt.toComplex_def'] at this hz
    simp only [Complex.add_im, Complex.intCast_re, Complex.mul_im, Complex.I_re, Complex.intCast_im,
      Complex.I_im, mul_zero, zero_add, mul_one, Complex.intCast_im, add_zero] at this
    linarith

/-- The array before the final shift fits `w'` signed bits when the input has modulus at most
`2^p` and `s + p + 2 ≤ w'`. -/
theorem topPre_fits (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (a : ℕ) (low : List (Fin n)) (top : List (Fin (n + a))) {R₂ : ℕ} (hR₂ : R * 2 ^ a ≤ R₂)
    (Ps : List (Piece n R₂)) (hinj : ∀ P ∈ Ps, Function.Injective P.e)
    (hcover : (Ps.flatMap Piece.bitsList).Perm low)
    (hsel : (low.map (Fin.castAdd a) ++ top).Nodup)
    (s : ℕ) (hs : s = (low.length + top.length + 1) / 2 + top.length + (Ps.map (Piece.exp ds)).sum)
    (Z : ZArr (Fin R × Fin r) (n + a)) {p w' : ℕ}
    (hZ : ∀ q, ‖GaussianInt.toComplex (Z q)‖ ≤ 2 ^ p) (hw : s + p + 2 ≤ w') :
    ∀ q, TopFitsZ w' (topPre ds a low top hR₂ Ps Z q) := by
  intro q
  refine topFitsZ_of_norm (k := s + p) ?_ (by omega)
  have e := congrFun (topPre_toC ds hd a low top hR₂ Ps hinj hcover hsel s hs Z) q
  change toC (topPre ds a low top hR₂ Ps Z) q = _ at e
  have e' : GaussianInt.toComplex (topPre ds a low top hR₂ Ps Z q) =
      (2 : ℂ) ^ s * Hl _ (low.map (Fin.castAdd a) ++ top) (toC Z) q := e
  have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e', norm_mul, norm_pow, hn2, pow_add]
  gcongr
  exact Hl_norm_le _ (toC Z) (fun q => hZ q) q

end Pre

end IntegerMultBounds.MathlibTM2.Fast
