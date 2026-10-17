module

public import IntegerMultBounds.MathlibTM2.Fast.ConvSpec
import IntegerMultBounds.MathlibTM2.Fast.PointStage
public import IntegerMultBounds.MathlibTM2.Fast.ChirpBox
public import IntegerMultBounds.MathlibTM2.Fast.ResampARegs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import IntegerMultBounds.MathlibTM2.Layer.Shift
public import IntegerMultBounds.MathlibTM2.Mult.CRT

/-!
# The synthetic convolution `M̃_r` on the host

`cvSynth` computes the numerators of `Mult/SynthErr.convC a p u v`: both forward transforms,
the pointwise ring products, the opposite transform and the exact scaling by `M = 2^{Σ aᵢ}`,
on record streams in the format of `Fast/RingProd` (`cstream A w (rpStream M Z)`).

**Semantics** (`cv_rpOut_fwd`, `cv_convNum_eq`). Both forward outputs hold their records in the
same order `π` (`ConvSpec.cvFwdOut`); the pointwise products are recordwise
(`pwC p (u ∘ π) (v ∘ π) = pwC p u v ∘ π`), so the ring products of the two permuted streams are
the stream of `pwC p Fu Fv ∘ π`, the input order of the opposite contract. The opposite
transform returns `oppRoundsC` of `pwC p Fu Fv` in natural order and the shift by `Σ aᵢ` bits
multiplies every numerator by `M` (`cst_numer_two_pow_mul`): the result is
`cvConvNum p a Zu Zv = cvNum p (convC a p (rpGrid p Zu) (rpGrid p Zv))`, exactly.

**Registers** (`CvR`, layout `rg : CvR → Fin T` injective and disjoint from the 64
Schönhage–Strassen registers `ι`). `cm x` (`x : CR`): the complex-product registers of the
twists (`Fast/ConvBox`); `cm .wn` is shared with the ring product as its word counter. `rr x`:
the ring product's stream and scratch registers; `rpi j`: the 91 placed registers of the
vendored ring product (`rpi 0` the header `Γ(p)Γ(2^l)Γ(w)`). The ring product's register map
`cvRp` sends `xs ↦ rr .xs`, `ys ↦ io`, `out ↦ rr .out`, `wn ↦ cm .wn`, `dⱼ ↦ rpi j`. `io` is
the transforms' register, `sy` the second operand, `so` the result, `t1` a transfer spare;
`shD … shU` the shift's spare, counters (`Σ aᵢ` and `w - Σ aᵢ` symbols) and temporaries;
`fi`, `gi`, `fo`, `tp`, `tm` are the box stage's inputs, output and twist tables.

**Contracts** (`CvRuns`). `RsaRuns` of `Fast/ResampARegs` with a precondition `Pre` on the
stacks (the transforms' parameter registers); `CvFramed rg Pre`: `Pre` survives every change
confined to the layout (`rsaFr`). `cv_fwd_runs`, `cv_opp_runs` lift the transform contracts
(`ConvSpec`), `cv_rp_runs` lifts `rpProg_exec`, `cv_xfer_runs` moves a stream in forward order
through `t1`.

**Program** (`cvSynth`). `fwdP` on `io`; `io → rr.xs`; `sy → io`; `fwdP` on `io`; `rpProg`
(`xs = rr.xs`, `ys = io`, onto `rr.out`); clear `rr.xs`, `io`; `rr.out → io`; `oppP` on `io`;
`shiftInto` from `io` onto `so` by `Σ aᵢ` bits.

**Result** (`cvSynth_runs`). From `io`, `sy` holding the streams of `Zu`, `Zv` (disk records),
`so` gains the stream of `cvConvNum p a Zu Zv`; `io`, `sy` end empty, every other register as
before; within
`cvSynthCost = 2 cF + cO + rpCost T p l w M + 16 M r w + 16 + M r (6 w + 4 Σaᵢ + 14) + 4`.
Hypotheses: `1 ≤ p`, `p + 2 ≤ w` (the ring product), `Σ aᵢ ≤ w` (the shift), `4 ≤ A`,
`91 ≤ T`, `rpStates ≤ Q`, `π` maps the first `M` addresses into themselves. The shift is
exact modulo `2^w`, so the output stream is the stream of the true numerators with no further
width condition; they fit `w` bits when `p + 2 ≤ w` and the result has modulus below `2`
(`Fast/ConvBox`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ConvSt

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr
open IntegerMultBounds.Spec.SignedRingProduct


noncomputable section

/-! ### Grid records and numerators -/

section Sem

theorem cv_mk_grid (p : ℕ) (N : GaussianInt) :
    (⟨(N.re : ℝ) / 2 ^ p, (N.im : ℝ) / 2 ^ p⟩ : ℂ) = cstGrid p N := by
  unfold cstGrid
  rw [two_pow_complex]
  apply Complex.ext
  · rw [toComplex_div_re]
  · rw [toComplex_div_im]

theorem cv_rpGrid_apply (p : ℕ) {r : ℕ} (X : ℕ → Fin r → GaussianInt) (n : ℕ) (c : Fin r) :
    rpGrid p X n c = cstGrid p (X n c) :=
  cv_mk_grid p (X n c)

theorem cv_gridR_rpGrid (p : ℕ) {r : ℕ} (X : ℕ → Fin r → GaussianInt) : GridR p (rpGrid p X) :=
  fun n c => by rw [cv_rpGrid_apply]; exact cst_isFixed_grid p _

theorem cv_rpGrid_cvNum {p r : ℕ} {u : Recs r} (hu : GridR p u) : rpGrid p (cvNum p u) = u := by
  funext n c
  rw [cv_rpGrid_apply]
  exact cst_grid_numer (hu n c)

variable {d : ℕ}

/-- The grid records of the forward output are the computed forward rounds in the order `π`. -/
theorem cv_rpGrid_fwdOut (p l : ℕ) (a : Fin d → ℕ) (π : ℕ → ℕ)
    (Z : ℕ → Fin (2 ^ l) → GaussianInt) :
    rpGrid p (cvFwdOut p l a π Z) =
      fun n => fwdRoundsC p (List.ofFn a) (nRounds a) (rpGrid p Z) (π n) := by
  funext n c
  rw [cv_rpGrid_apply]
  exact cst_grid_numer (fwdRoundsC_grid p _ _ (cv_gridR_rpGrid p Z) (π n) c)

/-- Pointwise products commute with a record permutation. -/
theorem cv_pwC_comp (p : ℕ) {r : ℕ} [NeZero r] (u v : Recs r) (π : ℕ → ℕ) (n : ℕ) :
    pwC p (fun n => u (π n)) (fun n => v (π n)) n = pwC p u v (π n) := rfl

/-- The computed forward rounds of a grid array, for short. -/
abbrev cvF (p l : ℕ) (a : Fin d → ℕ) (Z : ℕ → Fin (2 ^ l) → GaussianInt) : Recs (2 ^ l) :=
  fwdRoundsC p (List.ofFn a) (nRounds a) (rpGrid p Z)

/-- The ring products of the two forward outputs are the numerators of the pointwise products
`pwC p Fu Fv`, in the order `π`. -/
theorem cv_rpOut_fwd (p l : ℕ) (a : Fin d → ℕ) (π : ℕ → ℕ)
    (Zu Zv : ℕ → Fin (2 ^ l) → GaussianInt) :
    rpOut p (cvFwdOut p l a π Zu) (cvFwdOut p l a π Zv) =
      fun n => cvNum p (pwC p (cvF p l a Zu) (cvF p l a Zv)) (π n) := by
  funext n c
  have h := rp_pwC_grid p (cvFwdOut p l a π Zu) (cvFwdOut p l a π Zv) n c
  rw [cv_rpGrid_fwdOut, cv_rpGrid_fwdOut, cv_pwC_comp, cv_mk_grid] at h
  show _ = numer p _
  rw [h, cst_numer_grid]

/-- The numerators of the computed synthetic convolution `convC` of two grid arrays. -/
def cvConvNum (p : ℕ) {l : ℕ} (a : Fin d → ℕ) (Zu Zv : ℕ → Fin (2 ^ l) → GaussianInt) :
    ℕ → Fin (2 ^ l) → GaussianInt :=
  cvNum p (convC a p (rpGrid p Zu) (rpGrid p Zv))

/-- `convC` is the opposite output of the pointwise products, scaled by `M = 2^{Σ aᵢ}`. -/
theorem cv_convNum_eq (p l : ℕ) (a : Fin d → ℕ) (Zu Zv : ℕ → Fin (2 ^ l) → GaussianInt) :
    cvConvNum p a Zu Zv = fun n c => 2 ^ (List.ofFn a).sum *
      cvOppOut p l a (cvNum p (pwC p (cvF p l a Zu) (cvF p l a Zv))) n c := by
  funext n c
  have hg : GridR p (pwC p (cvF p l a Zu) (cvF p l a Zv)) := gridR_rdR p _
  simp only [cvConvNum, cvOppOut]
  rw [cv_rpGrid_cvNum hg]
  simp only [cvNum, convC, Pi.smul_apply, smul_eq_mul]
  rw [tsA_prod]
  push_cast
  exact cst_numer_two_pow_mul (oppRoundsC_grid p _ _ hg n c) _

/-- The stream of an array scaled entrywise. -/
theorem cv_rpStream_map {r : ℕ} (M : ℕ) (X : ℕ → Fin r → GaussianInt)
    (g : GaussianInt → GaussianInt) :
    (rpStream M X).map g = rpStream M fun n c => g (X n c) := by
  simp only [rpStream, List.map_flatMap, List.map_ofFn]
  rfl

end Sem

/-! ### Registers -/

/-- The registers of the convolution stage. -/
inductive CvR
  | cm (x : CR)
  | rr (x : RpReg)
  | rpi (j : Fin 91)
  | io | sy | so | t1 | fi | gi | fo | tp | tm | shD | shS | shR | shT | shU
  deriving DecidableEq

/-- The register map of the ring product. -/
def cvRp : RpReg → CvR
  | .xs => .rr .xs
  | .ys => .io
  | .out => .rr .out
  | .wn => .cm .wn
  | .sv => .rr .sv
  | .ta => .rr .ta
  | .tb => .rr .tb
  | .acc => .rr .acc
  | .tmp => .rr .tmp
  | .d0 => .rpi 0
  | .d1 => .rpi 1
  | .d2 => .rpi 2
  | .d3 => .rpi 3

theorem cvRp_inj : Function.Injective cvRp := by
  intro a b h
  cases a <;> cases b <;> first | rfl | simp [cvRp] at h

theorem cvRpi_inj : Function.Injective CvR.rpi := fun _ _ h => CvR.rpi.inj h

theorem cv_rpi_inj {T : ℕ} {rg : CvR → Fin T} (hrg : Function.Injective rg) :
    Function.Injective fun j => rg (CvR.rpi j) :=
  hrg.comp cvRpi_inj

/-- Moving a stream in forward order from `a` onto `b` through the empty spare `t1`. -/
def cvXfer {T Q A : ℕ} {U P : Type} (rg : CvR → Fin T) (a b : CvR) : Pr P T Q A U :=
  .seq (moveR (rg a) (rg .t1) id) (moveR (rg .t1) (rg b) id)

/-! ### Contracts with a precondition -/

section Contracts

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U) (rg : CvR → Fin T)
  (ι : Fin 64 → Fin T) (Pre : Stacks T A → Prop)

/-- `Pre` survives every change confined to the layout. -/
def CvFramed : Prop := ∀ S S' : Stacks T A, Pre S → rsaFr rg S S' → Pre S'

/-- `RsaRuns` from stacks meeting `Pre`. -/
def CvRuns (p : Pr P T Q A U) (ρ ρ' : CvR → List (Fin (A + 4))) (b : ℕ) : Prop :=
  ∀ v S, rsaClean ι S → Pre S → rsaHolds rg S ρ → ∃ v' S' n, v'.user = v.user ∧ n ≤ b ∧
    Exec body p (mk v S) n (mk v' S') ∧ rsaHolds rg S' ρ' ∧ rsaFr rg S S'

variable {body rg ι Pre}

theorem CvRuns.of_rsa {p : Pr P T Q A U} {ρ ρ' : CvR → List (Fin (A + 4))} {b : ℕ}
    (h : RsaRuns body rg ι p ρ ρ' b) : CvRuns body rg ι Pre p ρ ρ' b :=
  fun v S hc _ hS => h v S hc hS

theorem CvRuns.seq (hdisj : ∀ r j, rg r ≠ ι j) (hP : CvFramed rg Pre) {p q : Pr P T Q A U}
    {ρ₁ ρ₂ ρ₃ : CvR → List (Fin (A + 4))} {b₁ b₂ : ℕ} (h₁ : CvRuns body rg ι Pre p ρ₁ ρ₂ b₁)
    (h₂ : CvRuns body rg ι Pre q ρ₂ ρ₃ b₂) : CvRuns body rg ι Pre (.seq p q) ρ₁ ρ₃ (b₁ + b₂) := by
  intro v S hc hpre hS
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h₁ v S hc hpre hS
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ :=
    h₂ v₁ S₁ (hc.of_fr hdisj hf₁) (hP S S₁ hpre hf₁) hS₁
  exact ⟨v₂, S₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hS₂, hf₁.trans hf₂⟩

theorem CvRuns.mono {p : Pr P T Q A U} {ρ ρ' : CvR → List (Fin (A + 4))} {b b' : ℕ}
    (h : CvRuns body rg ι Pre p ρ ρ' b) (hb : b ≤ b') : CvRuns body rg ι Pre p ρ ρ' b' := by
  intro v S hc hpre hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := h v S hc hpre hS
  exact ⟨v', S', n, hu, hn.trans hb, he, hS', hf⟩

theorem CvRuns.congr {p : Pr P T Q A U} {ρ ρ' ρ'' : CvR → List (Fin (A + 4))} {b : ℕ}
    (h : CvRuns body rg ι Pre p ρ ρ' b) (he : ρ' = ρ'') : CvRuns body rg ι Pre p ρ ρ'' b :=
  he ▸ h

/-! ### Lifted contracts -/

variable (hrg : Function.Injective rg)
include hrg

/-- A contract whose final stacks differ from the initial ones on one layout register. -/
theorem cv_runs_of_update {p : Pr P T Q A U} {ρ : CvR → List (Fin (A + 4))} {b : ℕ}
    (x : CvR) (l : List (Fin (A + 4)))
    (h : ∀ v S, rsaClean ι S → Pre S → rsaHolds rg S ρ → ∃ v' n, v'.user = v.user ∧ n ≤ b ∧
      Exec body p (mk v S) n (mk v' { S with R := Function.update S.R (rg x) l })) :
    CvRuns body rg ι Pre p ρ (Function.update ρ x l) b := by
  intro v S hc hpre hS
  obtain ⟨v', n, hu, hn, he⟩ := h v S hc hpre hS
  exact ⟨v', _, n, hu, hn, he, rsa_holds_upd hrg hS x l, rfl, rfl, rfl,
    fun k hk => rsa_upd_off _ _ _ hk⟩

variable {d : ℕ}

/-- The forward transform on `io`. -/
theorem cv_fwd_runs {fwdP : Pr P T Q A U} {PreF : Stacks T A → Prop} {w p l cF : ℕ}
    {a : Fin d → ℕ} {π : ℕ → ℕ} (hF : SynFwdSpec body fwdP (rg .io) PreF w p l a π cF)
    (hPF : ∀ S, Pre S → PreF S) (Z : ℕ → Fin (2 ^ l) → GaussianInt)
    (hZ : SupLe (List.ofFn a).sum (rpGrid p Z) 1) (ρ : CvR → List (Fin (A + 4)))
    (hio : ρ .io = cstream A w (rpStream (cvM a) Z)) :
    CvRuns body rg ι Pre fwdP ρ
      (Function.update ρ .io (cstream A w (rpStream (cvM a) (cvFwdOut p l a π Z)))) cF :=
  cv_runs_of_update hrg _ _ fun v S _ hpre hS =>
    hF Z v S (hPF S hpre) hZ (by rw [hS, hio])

/-- The opposite transform on `io`. -/
theorem cv_opp_runs {oppP : Pr P T Q A U} {PreO : Stacks T A → Prop} {w p l cO : ℕ}
    {a : Fin d → ℕ} {π : ℕ → ℕ} (hO : SynOppSpec body oppP (rg .io) PreO w p l a π cO)
    (hPO : ∀ S, Pre S → PreO S) (V : ℕ → Fin (2 ^ l) → GaussianInt)
    (hV : SupLe (List.ofFn a).sum (rpGrid p V) 1) (ρ : CvR → List (Fin (A + 4)))
    (hio : ρ .io = cstream A w (rpStream (cvM a) fun n => V (π n))) :
    CvRuns body rg ι Pre oppP ρ
      (Function.update ρ .io (cstream A w (rpStream (cvM a) (cvOppOut p l a V)))) cO :=
  cv_runs_of_update hrg _ _ fun v S _ hpre hS =>
    hO V v S (hPO S hpre) hV (by rw [hS, hio])

omit hrg in
theorem cv_rpLayout (hrg : Function.Injective rg) :
    RpLayout (fun x => rg (cvRp x)) (fun j => rg (CvR.rpi j)) where
  rg_inj := hrg.comp cvRp_inj
  ι_inj := cv_rpi_inj hrg
  d0 := rfl
  d1 := rfl
  d2 := rfl
  d3 := rfl
  priv := by
    intro r j hj
    apply hrg.ne
    have h0 : j ≠ 0 := fun h => by subst h; simp at hj
    have h1 : j ≠ 1 := fun h => by subst h; simp at hj
    have h2 : j ≠ 2 := fun h => by subst h; simp at hj
    have h3 : j ≠ 3 := fun h => by subst h; simp at hj
    cases r <;> simp [cvRp, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3]

/-- The pointwise ring products: `rr.xs`, `io` hold the operand streams, `rr.out` gains the
stream of the products. -/
theorem cv_rp_runs (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A) {p l w M : ℕ} (hp : 1 ≤ p)
    (hw : p + 2 ≤ w) (X Y : ℕ → Fin (2 ^ l) → GaussianInt)
    (hX : ∀ n < M, DiskGrid p (rpRec X n).1 (rpRec X n).2)
    (hY : ∀ n < M, DiskGrid p (rpRec Y n).1 (rpRec Y n).2) (ρ : CvR → List (Fin (A + 4)))
    (hxs : ρ (.rr .xs) = cstream A w (rpStream M X)) (hys : ρ .io = cstream A w (rpStream M Y))
    (hwn : (ρ (.cm .wn)).length = w) (hsv : ρ (.rr .sv) = []) (hta : ρ (.rr .ta) = [])
    (htb : ρ (.rr .tb) = []) (hacc : ρ (.rr .acc) = []) (htmp : ρ (.rr .tmp) = [])
    (hd0 : ρ (.rpi 0) = (header p (2 ^ l) w).map bitSymbol)
    (hpriv : ∀ j : Fin 91, j ≠ 0 → ρ (.rpi j) = []) :
    CvRuns body rg ι Pre
      (rpProg (fun x => rg (cvRp x)) (fun j => rg (CvR.rpi j)) (cv_rpi_inj hrg) hT hQ) ρ
      (Function.update ρ (.rr .out) (cstream A w (rpStream M (rpOut p X Y)) ++ ρ (.rr .out)))
      (rpCost T p l w M) := by
  refine cv_runs_of_update hrg _ _ fun v S hc _ hS => ?_
  have hL := cv_rpLayout hrg
  have hcl : RpClean (fun j => rg (CvR.rpi j)) S :=
    ⟨fun j => hc.1 _, fun j hj => by
      rw [hS]; exact hpriv j (fun h => by subst h; simp at hj)⟩
  have e : ∀ x, S.R (rg (cvRp x)) = ρ (cvRp x) := fun x => hS _
  obtain ⟨v', n, hu, hn, he⟩ := rpProg_exec (body := body) hL hT hQ hA hp hw X Y hX hY v S hcl
    ((e .xs).trans hxs) ((e .ys).trans hys) (by rw [e .wn]; exact hwn) ((e .sv).trans hsv)
    ((e .ta).trans hta) ((e .tb).trans htb) ((e .acc).trans hacc) ((e .tmp).trans htmp)
    ((e .d0).trans hd0) ((e .d1).trans (hpriv 1 (by decide)))
    ((e .d2).trans (hpriv 2 (by decide))) ((e .d3).trans (hpriv 3 (by decide)))
  refine ⟨v', n, hu, hn, ?_⟩
  have e2 : S.R (rg (CvR.rr .out)) = ρ (.rr .out) := hS _
  rw [← e2]
  exact he

omit hrg in
theorem cv_xfer_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {a b : CvR}
    (hab : a ≠ b) (ha : a ≠ .t1) (hb : b ≠ .t1) (ρ : CvR → List (Fin (A + 4)))
    (ht : ρ .t1 = []) :
    CvRuns body rg ι Pre (cvXfer rg a b) ρ
      (Function.update (Function.update ρ a []) b (ρ a ++ ρ b)) (4 * (ρ a).length + 4) := by
  have h1 := rsa_moveR (body := body) (ι := ι) hrg ha ρ
  have h2 := rsa_moveR (body := body) (ι := ι) hrg (Ne.symm hb)
    (Function.update (Function.update ρ a []) .t1 ((ρ a).reverse ++ ρ .t1))
  refine CvRuns.of_rsa (((RsaRuns.seq hdisj h1 h2).congr ?_).mono ?_)
  · funext k
    simp only [Function.update_apply, ht, List.append_nil]
    split_ifs <;> subst_vars <;> simp_all
  · simp only [Function.update_self, ht, List.append_nil, List.length_reverse]
    omega

end Contracts

/-! ### The program -/

section Program

variable {T Q A : ℕ} {U P : Type} (rg : CvR → Fin T)

/-- **The synthetic convolution.** The forward transform of the operand on `io`, moved onto
`rr.xs`; the forward transform of the operand on `sy` (moved onto `io = ys`); the ring products
onto `rr.out`; the operands cleared; the products moved onto `io`; the opposite transform; the
shift by `Σ aᵢ` bits from `io` onto `so`. -/
def cvSynth (hrg : Function.Injective rg) (hT : 91 ≤ T) (hQ : rpStates ≤ Q)
    (fwdP oppP : Pr P T Q A U) : Pr P T Q A U :=
  .seq fwdP <| .seq (cvXfer rg .io (.rr .xs)) <| .seq (cvXfer rg .sy .io) <| .seq fwdP <|
  .seq (rpProg (fun x => rg (cvRp x)) (fun j => rg (CvR.rpi j)) (cv_rpi_inj hrg) hT hQ) <|
  .seq (uclear (rg (.rr .xs))) <| .seq (uclear (rg .io)) <| .seq (cvXfer rg (.rr .out) .io) <|
  .seq oppP
    (shiftInto (rg .io) (rg .shD) (rg .so) (rg .shS) (rg .shR) (rg .shT) (rg .shU)
      (pairSym A false false))

end Program


/-- The step bound of `cvSynth`: the two forward transforms, the opposite transform, the ring
products, three stream transfers and two clears of `M r` coefficients of `w` symbols, and the
shift. -/
def cvSynthCost (T p l w S M cF cO : ℕ) : ℕ :=
  2 * cF + cO + rpCost T p l w M + 16 * (M * 2 ^ l * w) + 16 +
    (M * 2 ^ l) * (6 * w + 4 * S + 14) + 4

/-! ### The contract of `cvSynth` -/

section Main

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : CvR → Fin T}
  {ι : Fin 64 → Fin T} {Pre : Stacks T A → Prop}

/-- **The synthetic convolution on the host.** `io` and `sy` hold the streams of the numerator
arrays `Zu`, `Zv` (disk records); the transforms meet their contracts with the record order `π`
(mapping the first `M` addresses into themselves) under preconditions implied by `Pre`, and `Pre`
is framed by the layout. The ring product's header is on `rpi 0`, its other placed registers and
scratch registers are empty, `cm .wn` holds `w` symbols; the shift's counters hold `Σ aᵢ` and
`w - Σ aᵢ` symbols, its spares are empty; `t1` is empty. Then `cvSynth` pushes the stream of
`cvConvNum p a Zu Zv` (the numerators of `convC a p (rpGrid p Zu) (rpGrid p Zv)`) onto `so`,
empties `io` and `sy`, and leaves every other register as before, within `cvSynthCost` steps. -/
theorem cvSynth_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hP : CvFramed rg Pre) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {d : ℕ} {fwdP oppP : Pr P T Q A U} {PreF PreO : Stacks T A → Prop} {w p l cF cO : ℕ}
    {a : Fin d → ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (rg .io) PreF w p l a π cF)
    (hO : SynOppSpec body oppP (rg .io) PreO w p l a π cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ n < cvM a, π n < cvM a) (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (hSw : (List.ofFn a).sum ≤ w)
    (Zu Zv : ℕ → Fin (2 ^ l) → GaussianInt)
    (hu : SupLe (List.ofFn a).sum (rpGrid p Zu) 1) (hv : SupLe (List.ofFn a).sum (rpGrid p Zv) 1)
    (ρ : CvR → List (Fin (A + 4)))
    (hio : ρ .io = cstream A w (rpStream (cvM a) Zu))
    (hsy : ρ .sy = cstream A w (rpStream (cvM a) Zv))
    (ht1 : ρ .t1 = []) (hxs : ρ (.rr .xs) = []) (hout : ρ (.rr .out) = [])
    (hwn : (ρ (.cm .wn)).length = w) (hsv : ρ (.rr .sv) = []) (hta : ρ (.rr .ta) = [])
    (htb : ρ (.rr .tb) = []) (hacc : ρ (.rr .acc) = []) (htmp : ρ (.rr .tmp) = [])
    (hd0 : ρ (.rpi 0) = (header p (2 ^ l) w).map bitSymbol)
    (hpriv : ∀ j : Fin 91, j ≠ 0 → ρ (.rpi j) = [])
    (hshD : ρ .shD = []) (hshS : (ρ .shS).length = (List.ofFn a).sum)
    (hshR : (ρ .shR).length = w - (List.ofFn a).sum) (hshT : ρ .shT = [])
    (hshU : ρ .shU = []) :
    CvRuns body rg ι Pre (cvSynth rg hrg hT hQ fwdP oppP) ρ
      (Function.update (Function.update (Function.update ρ .io []) .sy []) .so
        (cstream A w (rpStream (cvM a) (cvConvNum p a Zu Zv)) ++ ρ .so))
      (cvSynthCost T p l w (List.ofFn a).sum (cvM a) cF cO) := by
  set Fu := cvF p l a Zu with hFu_def
  set Fv := cvF p l a Zv with hFv_def
  set Xu := cvFwdOut p l a π Zu with hXu_def
  set Xv := cvFwdOut p l a π Zv with hXv_def
  set V := cvNum p (pwC p Fu Fv) with hV_def
  set O := cvOppOut p l a V with hO_def
  have hFu : SupLe (List.ofFn a).sum Fu 1 := fwdRoundsC_supLe p _ _ hu
  have hFv : SupLe (List.ofFn a).sum Fv 1 := fwdRoundsC_supLe p _ _ hv
  have hVd : SupLe (List.ofFn a).sum (rpGrid p V) 1 := by
    have hg : GridR p (pwC p Fu Fv) := gridR_rdR p _
    rw [hV_def, cv_rpGrid_cvNum hg]
    exact pwC_supLe p hFu hFv
  have hXu : ∀ n < cvM a, DiskGrid p (rpRec Xu n).1 (rpRec Xu n).2 := fun n hn =>
    rp_diskGrid_of_norm p Xu n fun c => by
      rw [hXu_def, cv_rpGrid_fwdOut]; exact hFu (π n) (hπ n hn) c
  have hXv : ∀ n < cvM a, DiskGrid p (rpRec Xv n).1 (rpRec Xv n).2 := fun n hn =>
    rp_diskGrid_of_norm p Xv n fun c => by
      rw [hXv_def, cv_rpGrid_fwdOut]; exact hFv (π n) (hπ n hn) c
  have hW : rpOut p Xu Xv = fun n => V (π n) := cv_rpOut_fwd p l a π Zu Zv
  have hscale : (rpStream (cvM a) O).map (fun N => 2 ^ (List.ofFn a).sum * N) =
      rpStream (cvM a) (cvConvNum p a Zu Zv) := by
    rw [cv_rpStream_map, cv_convNum_eq p l a Zu Zv]
  -- 1. forward transform of `Zu` on `io`
  have s1 := cv_fwd_runs (body := body) (ι := ι) (Pre := Pre) hrg hF hPF Zu hu ρ hio
  set ρ1 := Function.update ρ .io (cstream A w (rpStream (cvM a) Xu)) with hρ1
  -- 2. `io → rr.xs`
  have s2 := cv_xfer_runs (body := body) (Pre := Pre) hrg hdisj (a := .io) (b := .rr .xs)
    (by decide) (by decide) (by decide) ρ1 (by simp [ρ1, ht1])
  set ρ2 := Function.update (Function.update ρ1 .io []) (.rr .xs) (ρ1 .io ++ ρ1 (.rr .xs))
    with hρ2
  -- 3. `sy → io`
  have s3 := cv_xfer_runs (body := body) (Pre := Pre) hrg hdisj (a := .sy) (b := .io)
    (by decide) (by decide) (by decide) ρ2 (by simp [ρ2, ρ1, ht1])
  set ρ3 := Function.update (Function.update ρ2 .sy []) .io (ρ2 .sy ++ ρ2 .io) with hρ3
  -- 4. forward transform of `Zv` on `io`
  have s4 := cv_fwd_runs (body := body) (ι := ι) (Pre := Pre) hrg hF hPF Zv hv ρ3
    (by simp [ρ3, ρ2, ρ1, hsy])
  set ρ4 := Function.update ρ3 .io (cstream A w (rpStream (cvM a) Xv)) with hρ4
  -- 5. ring products onto `rr.out`
  have s5 := cv_rp_runs (body := body) (ι := ι) (Pre := Pre) hrg hT hQ hA hp hw Xu Xv hXu hXv ρ4
    (by simp [ρ4, ρ3, ρ2, ρ1, hxs]) (by simp [ρ4]) (by simp [ρ4, ρ3, ρ2, ρ1, hwn])
    (by simp [ρ4, ρ3, ρ2, ρ1, hsv]) (by simp [ρ4, ρ3, ρ2, ρ1, hta])
    (by simp [ρ4, ρ3, ρ2, ρ1, htb]) (by simp [ρ4, ρ3, ρ2, ρ1, hacc])
    (by simp [ρ4, ρ3, ρ2, ρ1, htmp]) (by simp [ρ4, ρ3, ρ2, ρ1, hd0])
    (fun j hj => by simp [ρ4, ρ3, ρ2, ρ1, hpriv j hj])
  set ρ5 := Function.update ρ4 (.rr .out)
    (cstream A w (rpStream (cvM a) (rpOut p Xu Xv)) ++ ρ4 (.rr .out)) with hρ5
  -- 6, 7. clear the operands
  have s6 := CvRuns.of_rsa (Pre := Pre) (rsa_uclear (body := body) (ι := ι) hrg (.rr .xs) ρ5)
  set ρ6 := Function.update ρ5 (.rr .xs) [] with hρ6
  have s7 := CvRuns.of_rsa (Pre := Pre) (rsa_uclear (body := body) (ι := ι) hrg .io ρ6)
  set ρ7 := Function.update ρ6 .io [] with hρ7
  -- 8. `rr.out → io`
  have s8 := cv_xfer_runs (body := body) (Pre := Pre) hrg hdisj (a := .rr .out) (b := .io)
    (by decide) (by decide) (by decide) ρ7 (by simp [ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, ht1])
  set ρ8 := Function.update (Function.update ρ7 (.rr .out) []) .io (ρ7 (.rr .out) ++ ρ7 .io)
    with hρ8
  -- 9. the opposite transform on `io`
  have s9 := cv_opp_runs (body := body) (ι := ι) (Pre := Pre) hrg hO hPO V hVd ρ8
    (by simp [ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hout, hW])
  set ρ9 := Function.update ρ8 .io (cstream A w (rpStream (cvM a) O)) with hρ9
  -- 10. the shift by `Σ aᵢ` bits onto `so`
  have s10 := CvRuns.of_rsa (Pre := Pre) (cst_scale_runs (body := body) (ι := ι) hrg
    (src := CvR.io) (dst := .shD) (out := .so) (cS := .shS) (cR := .shR) (tS := .shT)
    (tR := .shU) (by decide) (by decide) (by omega) hSw ρ9 (rpStream (cvM a) O) (by simp [ρ9])
    (by simp [ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hshS])
    (by simp [ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hshR])
    (by simp [ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hshT])
    (by simp [ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hshU])
    (by simp [ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hshD]))
  have H := s1.seq hdisj hP (s2.seq hdisj hP (s3.seq hdisj hP (s4.seq hdisj hP
    (s5.seq hdisj hP (s6.seq hdisj hP (s7.seq hdisj hP (s8.seq hdisj hP
      (s9.seq hdisj hP s10))))))))
  refine (H.congr ?_).mono ?_
  · rw [hscale]
    funext k
    simp only [ρ9, ρ8, ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · have hL : ∀ X : ℕ → Fin (2 ^ l) → GaussianInt,
        (cstream A w (rpStream (cvM a) X)).length = cvM a * 2 ^ l * w := fun X => by
      rw [length_cstream, length_rpStream]
    have e1 : (ρ1 .io).length = cvM a * 2 ^ l * w := by simp only [ρ1, Function.update_self, hL]
    have e2 : (ρ2 .sy).length = cvM a * 2 ^ l * w := by simp [ρ2, ρ1, hsy, hL]
    have e3 : (ρ5 (.rr .xs)).length = cvM a * 2 ^ l * w := by simp [ρ5, ρ4, ρ3, ρ2, ρ1, hxs, hL]
    have e4 : (ρ6 .io).length = cvM a * 2 ^ l * w := by simp [ρ6, ρ5, ρ4, hL]
    have e5 : (ρ7 (.rr .out)).length = cvM a * 2 ^ l * w := by
      simp [ρ7, ρ6, ρ5, ρ4, ρ3, ρ2, ρ1, hout, hL]
    rw [e1, e2, e3, e4, e5, length_rpStream]
    unfold cvSynthCost
    omega

end Main

end

end IntegerMultBounds.MathlibTM2.Fast.ConvSt
