module

public import IntegerMultBounds.MathlibTM2.Fast.ConvSynth
public import IntegerMultBounds.MathlibTM2.Fast.TablePhaseTwist
import IntegerMultBounds.MathlibTM2.Fast.PointStage
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The complex convolution stage `M̃_ℂ = convBox` on box streams

The stage computes `Mult/Pipeline.convBox n` (`boxConv`, `boxConvSucc`): on the box
`∏_{i ≤ D} ℤ/t_i` with last length `t_D = r = 2^l`, `M̃_ℂ(f, g) = cconvApproxVia (boxSplit t h) p
θ̃⁺ θ̃⁻ (synthMr a N p) f g` with `N i = t_i = 2^{a i}` for `i < D`.

**Formats.** A box array `F` is the stream of its numerators at scale `2^p` in address order,
axis `0` most significant (`ChirpSt.cstNumBox p t F`). With the last axis least significant the
same stream is `rpStream M (cvRecs t h p F)`, the `M = ∏_{i<D} t_i` records of `r` coefficients
along the last axis (`cv_numBox_eq`): record `n` is the line through the box point
`dec N n` (`Mult/SynthErr`, mixed radix, first axis most significant), coefficient `k` the point
`(boxSplit t h).symm (dec N n, k)`. No data moves: `ι` and `ι⁻¹` are the identity on streams.
The twist tables are the streams of the numerators of `θ̃⁺_k`, `θ̃⁻_k`, `k = 0 … r - 1`; for the
pipeline tables these are the streams `Fast/TablePhaseTwist.tblTwistStream` of the table machine
(`cv_twistPlus_stream`, `cv_twistMinus_stream`).

**Program** (`cvBox`). Three table products `cmulTable` through the complex-product layouts
`cvLay xs ys out` (operand `xs`, table `ys`, result `out`; every other register of `CR` is
`cm x`): the twist of `fi` by `tp` onto `io`, the twist of `gi` by `tp` onto `sy`; `cvSynth`
(`Fast/ConvSynth`) from `io`, `sy` onto `so`; the untwist of `so` by `tm` onto `fo`; `so`
cleared.

**Semantics.** The twist output is `cvNum p (cvTw t h p θ̃⁺ f)`, the numerators of
`ιR N (ι Q_p(θ̃⁺ · f))` (`cv_twist_eq`, from `cst_numer_rhoC_mul`); `cvSynth` gives the
numerators of `convC a p (cvTw … f) (cvTw … g)`, which on the first `M` records is
`synthMr a N p U V (dec N n)` (`cv_convC_eq_synthMr`, from `enc_dec`); the untwist gives
`Q_p(θ̃⁻_k · M̃_r(U, V)(dec N n, k))`, the value of `cconvApproxVia` at the point of record `n`,
coefficient `k` (`cv_untwist_eq`). The untwist operands fit `w` bits because `RingApprox`
(`synthMr_ringApprox`) and `eSynth < 2^p` bound `M̃_r` below modulus `2` (`cv_norm_convC_lt`).

**Results.** `cvBox_runs`: from `fi`, `gi` holding the box streams of grid functions `f`, `g` of
sup norm at most `1` and `tp`, `tm` the twist tables (grid, modulus at most `1`), `fo` gains the
box stream of `cconvApproxVia (boxSplit t h) p θ̃⁺ θ̃⁻ (synthMr a N p) f g`; every other register
ends as it started; within `cvBoxCost`. `cvBox_boxConvSucc`, `cvBox_boxConv`: the same for
`Pipeline.boxConvSucc`, `Pipeline.boxConv` with the table machine's twist streams and
`aᵢ = log₂ tᵢ` (`cvAx t`). `cvBox_convBox`: the instance `Pipeline.convBox n` for `Big n` and the
margin `hEs` of `Pipeline.convBox_spec` (`cv_eSynth_lt`); there `M r = T` (`cv_M_mul_r`).

**Cost** (`cvBoxCost`), against `Cost/Total` (one transform `F'`; `totBound` counts three):
* the three table products, `3 (M r (cmulCost T w + 6 w + 8) + 6)`: `3 T` products of
  `w`-bit numbers, `O(T M(p))`, inside the term `3 T M(p)` ("chirp products and twists") of
  `totBound`;
* the forward transforms `2 cF` and the opposite transform `cO`: the layer and twiddle part
  `T p (d K + p K^{τ-1} + ℓ d^{λ'})` of `totConv`;
* the ring products `rpCost T p l w M = M rpRecCost + rpFixCost` (`rpCost_le`: at most
  `M rpRecBound + rpFixCost`): `M = T/r` packed products of `N = O(r p)` bits, the part
  `T p log₂ (r p)` of `totConv`; the vendored bound `rpRingBound N` is
  `O(N log N log log N)`, one factor `log log (r p)` above that term;
* transfers, clears and the shift, `O(M r (w + Σ aᵢ))` steps: `O(T p)`, inside `totConv`.

**Widths.** `p + 2 ≤ w` (ring product; every stored numerator has modulus below `2^{p+1}`:
the operands, the tables, the twisted records and the synthetic convolution, of modulus below
`1 + eSynth 2^{-p} < 2`); `Σ aᵢ ≤ w` (the shift; exact modulo `2^w`, so the scaling by `M`
needs no headroom beyond the result's own).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.ConvSt

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt
open IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.MathlibTM2.Mult.SynthErr IntegerMultBounds.MathlibTM2.Mult.ComplexConv
open IntegerMultBounds.Spec.SignedRingProduct


noncomputable section

/-! ### Mixed-radix addresses -/

section Addr

theorem cv_range_flatMap {α : Type} (m P : ℕ) (G : ℕ → ℕ → α) :
    (List.range m).flatMap (fun x => (List.range P).map (G x)) =
      (List.range (m * P)).map fun n => G (n / P) (n % P) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add, List.map_append]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
    apply List.map_congr_left
    intro j hj
    have hj' := List.mem_range.1 hj
    have hP : 0 < P := by omega
    simp only [Function.comp]
    rw [Nat.mul_comm m P, Nat.mul_add_div hP, Nat.div_eq_of_lt hj', Nat.add_zero, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hj']

/-- The digits of the mixed-radix address `n`, first axis first. -/
def cvDigs (ns : List ℕ) (n : ℕ) : List ℕ := (List.range ns.length).map fun i => digit ns i n

theorem cv_length_digs (ns : List ℕ) (n : ℕ) : (cvDigs ns n).length = ns.length := by
  simp [cvDigs]

/-- The addresses of a box in increasing order are the digit lists of `0, …, ∏ nᵢ - 1`. -/
theorem cv_addrs_eq : ∀ ns : List ℕ, cstAddrs ns = (List.range ns.prod).map (cvDigs ns)
  | [] => by simp [cstAddrs, cvDigs]
  | m :: ns => by
    rw [cstAddrs, cv_addrs_eq ns]
    simp only [List.map_map, Function.comp_def]
    rw [cv_range_flatMap m ns.prod (fun x n' => x :: cvDigs ns n'), List.prod_cons]
    apply List.map_congr_left
    intro n hn
    have hn' := List.mem_range.1 hn
    have hP : 0 < ns.prod := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hn'; omega
    simp only [cvDigs, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      digit_cons_zero]
    rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hn'))]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, digit_cons_succ]
    rw [Spec.SignedRingProduct.digit_mod]

theorem cv_finEquiv_symm_val : ∀ (r : ℕ) [NeZero r] (z : ZMod r),
    ((ZMod.finEquiv r).symm z).val = z.val
  | 0, h, _ => (h.ne _ rfl).elim
  | _ + 1, _, _ => rfl

end Addr

/-! ### Box arrays as record streams -/

section BoxSem

variable {D r : ℕ} [NeZero r] (t : Fin (D + 1) → ℕ) [∀ i, NeZero (t i)]
  (h : t (Fin.last D) = r)

/-- The lengths of the first `D` axes. -/
abbrev cvN : Fin D → ℕ := fun i => t i.castSucc

omit [∀ (i : Fin (D + 1)), NeZero (t i)] in
theorem cv_boxSplit_apply (x : (i : Fin (D + 1)) → ZMod (t i)) :
    boxSplit t h x =
      (fun i : Fin D => x i.castSucc,
        (ZMod.finEquiv r).symm (ZMod.ringEquivCongr h (x (Fin.last D)))) :=
  rfl

/-- The numerators at scale `2^q` of a box function, as `M` records along the last axis. -/
def cvRecs (q : ℕ) (F : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) : ℕ → Fin r → GaussianInt :=
  fun n k => numer q (F ((boxSplit t h).symm (dec (cvN t) n, k)))

omit [∀ (i : Fin (D + 1)), NeZero (t i)] in
/-- The point of record `n`, coefficient `k`, from its address list. -/
theorem cv_point_eq (n : ℕ) (k : Fin r) :
    (fun i : Fin (D + 1) => (((cvDigs (List.ofFn (cvN t)) n ++ [(k : ℕ)]).getD i 0 : ℕ) :
      ZMod (t i))) = (boxSplit t h).symm (dec (cvN t) n, k) := by
  apply (boxSplit t h).injective
  rw [AddEquiv.apply_symm_apply, cv_boxSplit_apply]
  have hlen : (cvDigs (List.ofFn (cvN t)) n).length = D := by simp [cv_length_digs]
  refine Prod.ext ?_ ?_
  · funext i
    simp only [dec]
    rw [List.getD_append _ _ _ _ (by rw [hlen]; exact i.isLt)]
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact i.isLt)]
    simp [cvDigs]
  · simp only
    rw [List.getD_append_right _ _ _ _ (by rw [hlen]; simp)]
    simp only [hlen, Fin.val_last, Nat.sub_self, List.getD_cons_zero, map_natCast]
    apply Fin.ext
    rw [cv_finEquiv_symm_val, ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt]

omit [∀ (i : Fin (D + 1)), NeZero (t i)] in
/-- **Box streams are record streams.** The box stream of `F` (axis `0` most significant) is
the stream of its `M = ∏_{i<D} t_i` records along the last axis. -/
theorem cv_numBox_eq (q : ℕ) (F : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) :
    cstNumBox q t F = rpStream (List.ofFn (cvN t)).prod (cvRecs t h q F) := by
  set H : List ℕ → GaussianInt := fun l => numer q (F fun i => ((l.getD i 0 : ℕ) : ZMod (t i)))
    with hH
  have h1 : cstNumBox q t F = (cstAddrs (List.ofFn t)).map H := by
    unfold cstNumBox
    apply cst_rsaBox_eq_addrs
    intro x
    simp only [hH]
    congr 2
    funext i
    rw [List.getD_eq_getElem _ _ (by have := i.isLt; simp; omega), List.getElem_ofFn]
  have h2 : List.ofFn t = List.ofFn (cvN t) ++ [r] := by
    rw [List.ofFn_succ', List.concat_eq_append, h]
  rw [h1, h2, cstAddrs_append, cv_addrs_eq, List.map_flatMap, List.flatMap_map, rpStream]
  refine List.flatMap_congr fun n _ => ?_
  rw [List.map_map, ← cst_map_val_finRange r, List.map_map]
  conv_rhs => rw [List.ofFn_eq_map]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp, hH, cvRecs]
  rw [cv_point_eq t h n k]

/-- The twisted operand `ιR N (ι Q_p(θ · F))` as a record array. -/
def cvTw (p : ℕ) (θ : Fin r → ℂ) (F : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) : Recs r :=
  ιR (cvN t) (iota (phaseQ p θ (F ∘ (boxSplit t h).symm)))

omit [∀ (i : Fin (D + 1)), NeZero (t i)] in
theorem cvTw_apply (p : ℕ) (θ : Fin r → ℂ) (F : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) (n : ℕ)
    (k : Fin r) :
    cvTw t h p θ F n k = rhoC p (θ k * F ((boxSplit t h).symm (dec (cvN t) n, k))) := rfl

omit [∀ (i : Fin (D + 1)), NeZero (t i)] in
theorem cv_gridR_tw (p : ℕ) (θ : Fin r → ℂ) (F : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) :
    GridR p (cvTw t h p θ F) := fun _ _ => isFixed_rhoC _ _

end BoxSem

/-! ### Table products on record streams -/

section Tables

theorem cv_zipWith_ofFn {α β γ : Type} {r : ℕ} (g : α → β → γ) (A : Fin r → α) (B : Fin r → β) :
    List.zipWith g (List.ofFn A) (List.ofFn B) = List.ofFn fun k => g (A k) (B k) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp

theorem cv_blocks_flatten {r : ℕ} (M : ℕ) (X : ℕ → Fin r → GaussianInt) :
    ((List.range M).map fun n => List.ofFn (X n)).flatten = rpStream M X := by
  rw [rpStream, List.flatMap_def]

/-- A table product on the records of a stream, coefficient `k` of every record against table
entry `k`. -/
theorem cv_tableOut_rec {r : ℕ} (M : ℕ) (X : ℕ → Fin r → GaussianInt) (Θ : Fin r → GaussianInt)
    (g : GaussianInt → GaussianInt → GaussianInt) :
    tableOut g ((List.range M).map fun n => List.ofFn (X n)) (List.ofFn Θ) =
      rpStream M fun n k => g (X n k) (Θ k) := by
  simp only [tableOut, rpStream, List.flatMap_map, cv_zipWith_ofFn]

theorem cv_mem_rpStream {r : ℕ} {M : ℕ} {X : ℕ → Fin r → GaussianInt} {x : GaussianInt}
    (hx : x ∈ rpStream M X) : ∃ n < M, ∃ k, X n k = x := by
  simp only [rpStream, List.mem_flatMap, List.mem_range, List.mem_ofFn] at hx
  obtain ⟨n, hn, k, hk⟩ := hx
  exact ⟨n, hn, k, hk⟩

/-- The numerators of `Q_p(θ_k z)` for grid values. -/
theorem cv_numer_twist {p : ℕ} {z θ : ℂ} (hz : IsFixed p z) (hθ : IsFixed p θ) :
    tdivN p (numer p z * numer p θ) = numer p (rhoC p (θ * z)) := by
  rw [mul_comm θ z, cst_numer_rhoC_mul hz hθ]

end Tables


/-! ### The stage semantics -/

section StageSem

variable {D r : ℕ} [NeZero r] (t : Fin (D + 1) → ℕ) [∀ i, NeZero (t i)]
  (h : t (Fin.last D) = r)

theorem cv_rpStream_congr {r' : ℕ} {M : ℕ} {X Y : ℕ → Fin r' → GaussianInt}
    (hXY : ∀ n < M, X n = Y n) : rpStream M X = rpStream M Y :=
  List.flatMap_congr fun n hn => by rw [hXY n (List.mem_range.1 hn)]

omit [∀ (i : Fin (D + 1)), NeZero (t i)] in
/-- **The twist.** The table product of the box stream of `F` (grid values) with the twist
table `θ` gives the numerators of the twisted records `cvTw t h p θ F`. -/
theorem cv_twist_eq {p : ℕ} (θ : Fin r → ℂ) (hθ : ∀ k, IsFixed p (θ k))
    (F : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) (hF : ∀ x, IsFixed p (F x)) (M : ℕ) :
    tableOut (fun x y => tdivN p (x * y)) ((List.range M).map fun n => List.ofFn (cvRecs t h p F n))
        (List.ofFn fun k => numer p (θ k)) = rpStream M (cvNum p (cvTw t h p θ F)) := by
  rw [cv_tableOut_rec]
  congr 1
  funext n k
  exact cv_numer_twist (hF _) (hθ k)

/-- The twisted records are disk records. -/
theorem cv_tw_norm_le {p : ℕ} (θ : Fin r → ℂ) (hθ : ∀ k, ‖θ k‖ ≤ 1)
    (F : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) (hF : ‖F‖ ≤ 1) (n : ℕ) (k : Fin r) :
    ‖cvTw t h p θ F n k‖ ≤ 1 :=
  (norm_rhoC_mul_le (hθ k)).trans ((norm_le_pi_norm F _).trans hF)

variable (a : Fin D → ℕ)

/-- The ring operand `ι Q_p(θ · F)` on the box `∏_{i<D} ℤ/t_i`. -/
abbrev cvU (p : ℕ) (θ : Fin r → ℂ) (F : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) :
    Box (cvN t) → Fin r → ℂ :=
  iota (phaseQ p θ (F ∘ (boxSplit t h).symm))

theorem cv_diskGrid_U {p : ℕ} (θ : Fin r → ℂ) (hθ : ∀ k, ‖θ k‖ ≤ 1)
    (F : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) (hF : ‖F‖ ≤ 1) :
    DiskGridArr p (cvU t h p θ F) := fun _ k =>
  ⟨isFixed_rhoC _ _, (norm_rhoC_mul_le (hθ k)).trans ((norm_le_pi_norm F _).trans hF)⟩

/-- On the first `M` records the computed convolution of the twisted records is `M̃_r` of the
ring operands at the record's box point. -/
theorem cv_convC_eq_synthMr {p : ℕ} (θ : Fin r → ℂ) (F G : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ)
    {n : ℕ} (hn : n < (List.ofFn (cvN t)).prod) :
    convC a p (cvTw t h p θ F) (cvTw t h p θ G) n =
      synthMr a (cvN t) p (cvU t h p θ F) (cvU t h p θ G) (dec (cvN t) n) := by
  simp only [synthMr, enc_dec (cvN t) hn]
  rfl

/-- The computed convolution has modulus below `2` when `eSynth < 2^p`. -/
theorem cv_norm_convC_lt {p : ℕ} (ha : ∀ i, t i.castSucc = 2 ^ a i) (hdvd : ∀ i, 2 ^ a i ∣ 2 * r)
    (hE : eSynth a (cvN t) < 2 ^ p) (θ : Fin r → ℂ) (hθ : ∀ k, ‖θ k‖ ≤ 1)
    (F G : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) (hF : ‖F‖ ≤ 1) (hG : ‖G‖ ≤ 1)
    {n : ℕ} (hn : n < (List.ofFn (cvN t)).prod) (k : Fin r) :
    ‖convC a p (cvTw t h p θ F) (cvTw t h p θ G) n k‖ < 2 := by
  rw [cv_convC_eq_synthMr t h a θ F G hn]
  have hU := cv_diskGrid_U t h (p := p) θ hθ F hF
  have hV := cv_diskGrid_U t h (p := p) θ hθ G hG
  have hR := synthMr_ringApprox a (cvN t) ha hdvd p _ _ hU hV (dec (cvN t) n) k
  have hC := norm_synthConvNormG_le (fun j k => (hU j k).2) (fun j k => (hV j k).2) zero_le_one
    zero_le_one (dec (cvN t) n) k
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set X := synthMr a (cvN t) p (cvU t h p θ F) (cvU t h p θ G) (dec (cvN t) n) k
  set Y := synthConvNormG (cvU t h p θ F) (cvU t h p θ G) (dec (cvN t) n) k
  have h1 : ‖X‖ ≤ ‖X - Y‖ + ‖Y‖ := by
    calc ‖X‖ = ‖(X - Y) + Y‖ := by rw [sub_add_cancel]
      _ ≤ ‖X - Y‖ + ‖Y‖ := norm_add_le _ _
  have h2 : 2 ^ p * ‖X - Y‖ < 2 ^ p := hR.trans_lt hE
  have h3 : ‖X - Y‖ < 1 := lt_of_mul_lt_mul_left (by rwa [mul_one]) hp.le
  linarith

/-- The computed convolution of grid records lies on the grid. -/
theorem cv_isFixed_convC {r' : ℕ} [NeZero r'] {d' : ℕ} (a' : Fin d' → ℕ) (p : ℕ) (u v : Recs r')
    (n : ℕ) (k : Fin r') : IsFixed p (convC a' p u v n k) := by
  have hg : IsFixed p (oppRoundsC p (List.ofFn a') (nRounds a')
      (pwC p (fwdRoundsC p (List.ofFn a') (nRounds a') u)
        (fwdRoundsC p (List.ofFn a') (nRounds a') v)) n k) :=
    oppRoundsC_grid p (List.ofFn a') (nRounds a') (gridR_rdR p _) n k
  simp only [convC, Pi.smul_apply, smul_eq_mul]
  rw [tsA_prod]
  push_cast
  rw [← cst_grid_numer hg, cst_two_pow_mul_grid]
  exact cst_isFixed_grid p _

/-- **The untwist.** The table product of the records of `convC` of the twisted operands with
the table `θ⁻` is the box stream of `M̃_ℂ = cconvApproxVia (boxSplit t h) p θ⁺ θ⁻ (synthMr …)`. -/
theorem cv_untwist_eq {p : ℕ} (θp θm : Fin r → ℂ)
    (hθm : ∀ k, IsFixed p (θm k)) (f g : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) :
    tableOut (fun x y => tdivN p (x * y))
        ((List.range (List.ofFn (cvN t)).prod).map fun n =>
          List.ofFn (cvNum p (convC a p (cvTw t h p θp f) (cvTw t h p θp g)) n))
        (List.ofFn fun k => numer p (θm k)) =
      cstNumBox p t (cconvApproxVia (boxSplit t h) p θp θm (synthMr a (cvN t) p) f g) := by
  rw [cv_tableOut_rec, cv_numBox_eq t h]
  refine cv_rpStream_congr fun n hn => ?_
  funext k
  simp only [cvNum]
  rw [cv_numer_twist (cv_isFixed_convC a p _ _ n k) (hθm k), cv_convC_eq_synthMr t h a θp f g hn]
  simp only [cvRecs, cconvApproxVia, Function.comp_apply, AddEquiv.apply_symm_apply]
  rfl

end StageSem


/-- `p + k + 1 ≤ w` and modulus below `2^k`: the numerator fits `w` bits. -/
theorem cv_fits_of_norm {p w : ℕ} {z : ℂ} (hz : ‖z‖ < 2) (hw : p + 2 ≤ w) : Fits w (numer p z) :=
  cst_fits_numer (k := 1) (by simpa using hz) (by omega)

/-! ### Complex-product layouts -/

/-- The complex-product registers with operand `xs`, table `ys` and result `out`; every other
register `x` of the product is `cm x`. -/
def cvLay (xs ys out : CvR) (x : CR) : CvR :=
  if x = .xs then xs else if x = .ys then ys else if x = .out then out else .cm x

theorem cvLay_inj {xs ys out : CvR} (h1 : xs ≠ ys) (h2 : xs ≠ out) (h3 : ys ≠ out)
    (hx : ∀ y, xs ≠ .cm y) (hy : ∀ y, ys ≠ .cm y) (ho : ∀ y, out ≠ .cm y) :
    Function.Injective (cvLay xs ys out) := by
  intro a b hab
  have key : ∀ x : CR, (x = .xs ∧ cvLay xs ys out x = xs) ∨ (x = .ys ∧ cvLay xs ys out x = ys) ∨
      (x = .out ∧ cvLay xs ys out x = out) ∨ cvLay xs ys out x = .cm x := by
    intro x
    unfold cvLay
    split_ifs <;> simp_all
  rcases key a with ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha <;>
  rcases key b with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | hb <;>
  (rw [ha] at hab; try rw [hb] at hab) <;>
  (first
    | rfl
    | exact absurd hab h1 | exact absurd hab h2 | exact absurd hab h3
    | exact absurd hab.symm h1 | exact absurd hab.symm h2 | exact absurd hab.symm h3
    | exact absurd hab (hx _) | exact absurd hab (hy _) | exact absurd hab (ho _)
    | exact absurd hab.symm (hx _) | exact absurd hab.symm (hy _) | exact absurd hab.symm (ho _)
    | exact CvR.cm.inj hab)

@[simp] theorem cvLay_xs (xs ys out : CvR) : cvLay xs ys out .xs = xs := by simp [cvLay]
@[simp] theorem cvLay_ys (xs ys out : CvR) : cvLay xs ys out .ys = ys := by simp [cvLay]
@[simp] theorem cvLay_out (xs ys out : CvR) : cvLay xs ys out .out = out := by simp [cvLay]

theorem cvLay_other (xs ys out : CvR) {x : CR} (h1 : x ≠ .xs) (h2 : x ≠ .ys) (h3 : x ≠ .out) :
    cvLay xs ys out x = .cm x := by simp [cvLay, h1, h2, h3]

section Table

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : CvR → Fin T}
  {ι : Fin 64 → Fin T} {Pre : Stacks T A → Prop}

variable (rg ι) in
/-- The table product through the layout `cvLay xs ys out`. -/
def cvTable (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (xs ys out : CvR) :
    Pr P T Q A U :=
  cmulTable (fun x => rg (cvLay xs ys out x)) (cmulOne ι hι hT hQ (fun x => rg (cvLay xs ys out x)))

/-- **A table product on the layout.** `xs` holds the stream of `blocks.flatten` (every block
of the table's length), `ys` the table; `out` gains the stream of the products, everything else
as before (`cmulTable_runs`). The complex-product registers `cm x` are ready for `w` and `q`. -/
theorem cv_table_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {xs ys out : CvR} (hc : Function.Injective (cvLay xs ys out)) {w q : ℕ} (hw : 1 ≤ w)
    (hq : q ≤ w) (ρ : CvR → List (Fin (A + 4))) (hr : Ready (fun x => ρ (.cm x)) w q)
    (blocks : List (List GaussianInt)) (ts : List GaussianInt) (hL : 1 ≤ ts.length)
    (hlen : ∀ b ∈ blocks, b.length = ts.length) (hfx : ∀ x ∈ blocks.flatten, Fits w x)
    (hft : ∀ t ∈ ts, Fits w t) (hX : ρ xs = cstream A w blocks.flatten)
    (hY : ρ ys = cstream A w ts) (hxsv : ρ (.cm .xsv) = []) (hysv : ρ (.cm .ysv) = [])
    (hacc : ρ (.cm .acc) = []) :
    CvRuns body rg ι Pre (cvTable rg ι hι hT hQ xs ys out) ρ
      (Function.update ρ out
        (cstream A w (tableOut (fun x y => tdivN q (x * y)) blocks ts) ++ ρ out))
      (blocks.flatten.length * (cmulCost T w + 6 * w + 8) + 6) := by
  have hcr : Function.Injective (fun x => rg (cvLay xs ys out x)) := hrg.comp hc
  have hd : ∀ r j, (fun x => rg (cvLay xs ys out x)) r ≠ ι j := fun r j => hdisj _ j
  have hr' : Ready (fun x => ρ (cvLay xs ys out x)) w q :=
    cst_ready_of_eq hr fun x h1 h2 _ _ _ h6 => by simp only [cvLay_other xs ys out h1 h2 h6]
  have H := RsaRuns.of_c hrg hc (cmulTable_runs (body := body) hcr hd hι hT hQ hA
    (ρ := fun x => ρ (cvLay xs ys out x)) hr' hw hq blocks ts hL hlen hfx hft
    (by simpa using hX) (by simpa using hY)
    (by rw [cvLay_other xs ys out (by decide) (by decide) (by decide)]; exact hxsv)
    (by rw [cvLay_other xs ys out (by decide) (by decide) (by decide)]; exact hysv)
    (by rw [cvLay_other xs ys out (by decide) (by decide) (by decide)]; exact hacc)) ρ
    (fun _ => rfl)
  rw [cst_extend_update _ hc] at H
  simp only [cvLay_out] at H
  exact CvRuns.of_rsa H

end Table

/-! ### The program -/

section Program

variable {T Q A : ℕ} {U P : Type} (rg : CvR → Fin T) (ι : Fin 64 → Fin T)

/-- **The complex convolution stage.** Twist `fi` and `gi` by the table `tp` onto `io`, `sy`;
the synthetic convolution onto `so`; untwist `so` by the table `tm` onto `fo`; clear `so`. -/
def cvBox (hrg : Function.Injective rg) (hι : Function.Injective ι) (hT64 : 64 ≤ T)
    (hQs : SS.states ≤ Q) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (fwdP oppP : Pr P T Q A U) :
    Pr P T Q A U :=
  .seq (cvTable rg ι hι hT64 hQs .fi .tp .io) <|
  .seq (cvTable rg ι hι hT64 hQs .gi .tp .sy) <|
  .seq (cvSynth rg hrg hT hQ fwdP oppP) <|
  .seq (cvTable rg ι hι hT64 hQs .so .tm .fo) (uclear (rg .so))

end Program

/-- The step bound of `cvBox`: three table products of `M r` coefficients, the synthetic
convolution, the clear of its output. -/
def cvBoxCost (T p l w S M cF cO : ℕ) : ℕ :=
  3 * (M * 2 ^ l * (cmulCost T w + 6 * w + 8) + 6) + cvSynthCost T p l w S M cF cO +
    2 * (M * 2 ^ l * w) + 2


/-! ### The contract of `cvBox` -/

section Main

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : CvR → Fin T}
  {ι : Fin 64 → Fin T} {Pre : Stacks T A → Prop}

/-- **The complex convolution stage.** On the box `∏_{i ≤ D} ℤ/t_i` with `t_D = r = 2^l` and
`t_i = 2^{a i}` dividing `2r` for `i < D`: `fi`, `gi` hold the box streams (`cstNumBox p t`) of
grid functions `f`, `g` of sup norm at most `1`; `tp`, `tm` the streams of the numerators of the
twist tables `θ⁺`, `θ⁻` (grid, modulus at most `1`); the transforms meet their contracts with a
record order `π` of the first `M = 2^{Σ aᵢ}` addresses; `eSynth a N < 2^p`. The complex-product
registers `cm x` are ready for `w` and `p`, the ring product's header is on `rpi 0`, the shift's
counters hold `Σ aᵢ` and `w - Σ aᵢ` symbols, and the other stage registers are empty. Then
`cvBox` pushes the box stream of `cconvApproxVia (boxSplit t h) p θ⁺ θ⁻ (synthMr a N p) f g`
onto `fo` and leaves every other register as it found it, within `cvBoxCost` steps. -/
theorem cvBox_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hP : CvFramed rg Pre) (hT64 : 64 ≤ T) (hQs : SS.states ≤ Q)
    (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 96 ≤ A)
    {D r l : ℕ} [NeZero r] (t : Fin (D + 1) → ℕ) [∀ i, NeZero (t i)] (h : t (Fin.last D) = r)
    (hrl : r = 2 ^ l) (a : Fin D → ℕ) (ha : ∀ i, t i.castSucc = 2 ^ a i)
    (hdvd : ∀ i, 2 ^ a i ∣ 2 * r)
    {fwdP oppP : Pr P T Q A U} {PreF PreO : Stacks T A → Prop} {w p cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (rg .io) PreF w p l a π cF)
    (hO : SynOppSpec body oppP (rg .io) PreO w p l a π cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ n < cvM a, π n < cvM a) (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (hSw : (List.ofFn a).sum ≤ w) (hE : eSynth a (cvN t) < 2 ^ p)
    (θp θm : Fin r → ℂ) (hθp : ∀ k, IsFixed p (θp k) ∧ ‖θp k‖ ≤ 1)
    (hθm : ∀ k, IsFixed p (θm k) ∧ ‖θm k‖ ≤ 1)
    (f g : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) (hf : ∀ x, IsFixed p (f x))
    (hg : ∀ x, IsFixed p (g x)) (hf1 : ‖f‖ ≤ 1) (hg1 : ‖g‖ ≤ 1)
    (ρ : CvR → List (Fin (A + 4)))
    (hfi : ρ .fi = cstream A w (cstNumBox p t f)) (hgi : ρ .gi = cstream A w (cstNumBox p t g))
    (htp : ρ .tp = cstream A w (List.ofFn fun k => numer p (θp k)))
    (htm : ρ .tm = cstream A w (List.ofFn fun k => numer p (θm k)))
    (hio : ρ .io = []) (hsy : ρ .sy = []) (hso : ρ .so = []) (ht1 : ρ .t1 = [])
    (hrd : Ready (fun x => ρ (.cm x)) w p) (hxsv : ρ (.cm .xsv) = [])
    (hysv : ρ (.cm .ysv) = []) (hacc : ρ (.cm .acc) = [])
    (hxs : ρ (.rr .xs) = []) (hout : ρ (.rr .out) = []) (hsv : ρ (.rr .sv) = [])
    (hta : ρ (.rr .ta) = []) (htb : ρ (.rr .tb) = []) (hracc : ρ (.rr .acc) = [])
    (htmp : ρ (.rr .tmp) = []) (hd0 : ρ (.rpi 0) = (header p (2 ^ l) w).map bitSymbol)
    (hpriv : ∀ j : Fin 91, j ≠ 0 → ρ (.rpi j) = [])
    (hshD : ρ .shD = []) (hshS : (ρ .shS).length = (List.ofFn a).sum)
    (hshR : (ρ .shR).length = w - (List.ofFn a).sum) (hshT : ρ .shT = [])
    (hshU : ρ .shU = []) :
    CvRuns body rg ι Pre (cvBox rg ι hrg hι hT64 hQs hT hQ fwdP oppP) ρ
      (Function.update ρ .fo (cstream A w
        (cstNumBox p t (cconvApproxVia (boxSplit t h) p θp θm (synthMr a (cvN t) p) f g)) ++
          ρ .fo))
      (cvBoxCost T p l w (List.ofFn a).sum (cvM a) cF cO) := by
  subst hrl
  have hMN : (List.ofFn (cvN t)).prod = cvM a := by
    rw [ofFn_eq_tsA a (cvN t) ha, tsA_prod]
  set Tu := cvTw t h p θp f with hTu
  set Tv := cvTw t h p θp g with hTv
  set Zu := cvNum p Tu with hZu
  set Zv := cvNum p Tv with hZv
  have hgu : rpGrid p Zu = Tu := cv_rpGrid_cvNum (cv_gridR_tw t h p θp f)
  have hgv : rpGrid p Zv = Tv := cv_rpGrid_cvNum (cv_gridR_tw t h p θp g)
  have hconv : cvConvNum p a Zu Zv = cvNum p (convC a p Tu Tv) := by
    rw [cvConvNum, hgu, hgv]
  have hu : SupLe (List.ofFn a).sum (rpGrid p Zu) 1 := by
    rw [hgu]; intro n _ c; exact cv_tw_norm_le t h θp (fun k => (hθp k).2) f hf1 n c
  have hv : SupLe (List.ofFn a).sum (rpGrid p Zv) 1 := by
    rw [hgv]; intro n _ c; exact cv_tw_norm_le t h θp (fun k => (hθp k).2) g hg1 n c
  -- blocks and tables
  set Θp := List.ofFn fun k => numer p (θp k) with hΘp
  set Θm := List.ofFn fun k => numer p (θm k) with hΘm
  have hL : 1 ≤ Θp.length := by simp [hΘp, Nat.one_le_two_pow]
  have hLm : 1 ≤ Θm.length := by simp [hΘm, Nat.one_le_two_pow]
  have hlen : ∀ (X : ℕ → Fin (2 ^ l) → GaussianInt) (Θ : List GaussianInt),
      Θ.length = 2 ^ l → ∀ b ∈ (List.range (cvM a)).map (fun n => List.ofFn (X n)),
        b.length = Θ.length := by
    intro X Θ hΘ b hb
    obtain ⟨n, _, rfl⟩ := List.mem_map.1 hb
    simp [hΘ]
  have hfitsΘ : ∀ θ : Fin (2 ^ l) → ℂ, (∀ k, IsFixed p (θ k) ∧ ‖θ k‖ ≤ 1) →
      ∀ x ∈ List.ofFn (fun k => numer p (θ k)), Fits w x := by
    intro θ hθ x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    exact cv_fits_of_norm (lt_of_le_of_lt (hθ k).2 one_lt_two) hw
  have hfitsF : ∀ F : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ, ‖F‖ ≤ 1 →
      ∀ x ∈ ((List.range (cvM a)).map fun n => List.ofFn (cvRecs t h p F n)).flatten,
        Fits w x := by
    intro F hF1 x hx
    rw [cv_blocks_flatten] at hx
    obtain ⟨n, _, k, rfl⟩ := cv_mem_rpStream hx
    exact cv_fits_of_norm (lt_of_le_of_lt ((norm_le_pi_norm F _).trans hF1) one_lt_two) hw
  have hfitsS : ∀ x ∈ ((List.range (cvM a)).map fun n =>
      List.ofFn (cvNum p (convC a p Tu Tv) n)).flatten, Fits w x := by
    intro x hx
    rw [cv_blocks_flatten] at hx
    obtain ⟨n, hn, k, rfl⟩ := cv_mem_rpStream hx
    exact cv_fits_of_norm (cv_norm_convC_lt t h a ha hdvd hE θp (fun k => (hθp k).2) f g hf1 hg1
      (by rw [hMN]; exact hn) k) hw
  have hBf : cstream A w (cstNumBox p t f) =
      cstream A w ((List.range (cvM a)).map fun n => List.ofFn (cvRecs t h p f n)).flatten := by
    rw [cv_blocks_flatten, cv_numBox_eq t h, hMN]
  have hBg : cstream A w (cstNumBox p t g) =
      cstream A w ((List.range (cvM a)).map fun n => List.ofFn (cvRecs t h p g n)).flatten := by
    rw [cv_blocks_flatten, cv_numBox_eq t h, hMN]
  have tw1 := cv_twist_eq t h θp (fun k => (hθp k).1) f hf (cvM a)
  have tw2 := cv_twist_eq t h θp (fun k => (hθp k).1) g hg (cvM a)
  have tw4 : tableOut (fun x y => tdivN p (x * y))
      ((List.range (cvM a)).map fun n => List.ofFn (cvNum p (convC a p Tu Tv) n)) Θm =
      cstNumBox p t (cconvApproxVia (boxSplit t h) p θp θm (synthMr a (cvN t) p) f g) := by
    rw [← hMN]
    exact cv_untwist_eq t h a θp θm (fun k => (hθm k).1) f g
  -- 1. twist of `f` onto `io`
  have s1 := cv_table_runs (body := body) (Pre := Pre) hrg hdisj hι hT64 hQs hA
    (xs := .fi) (ys := .tp) (out := .io)
    (cvLay_inj (by decide) (by decide) (by decide) (fun _ => by simp) (fun _ => by simp)
      (fun _ => by simp)) (w := w) (q := p) (by omega) (by omega) ρ hrd _ Θp hL
    (hlen _ Θp (by simp [hΘp])) (hfitsF f hf1) (hfitsΘ θp hθp) (by rw [hfi, hBf]) htp hxsv hysv
    hacc
  rw [tw1, hio, List.append_nil] at s1
  set ρ1 := Function.update ρ .io (cstream A w (rpStream (cvM a) Zu)) with hρ1
  have hcm1 : (fun x => ρ1 (.cm x)) = fun x => ρ (.cm x) := by funext x; simp [ρ1]
  -- 2. twist of `g` onto `sy`
  have s2 := cv_table_runs (body := body) (Pre := Pre) hrg hdisj hι hT64 hQs hA
    (xs := .gi) (ys := .tp) (out := .sy)
    (cvLay_inj (by decide) (by decide) (by decide) (fun _ => by simp) (fun _ => by simp)
      (fun _ => by simp)) (w := w) (q := p) (by omega) (by omega) ρ1 (by rw [hcm1]; exact hrd) _
    Θp hL
    (hlen _ Θp (by simp [hΘp])) (hfitsF g hg1) (hfitsΘ θp hθp)
    (by simp [ρ1, hgi, hBg]) (by simp [ρ1, htp]) (by simp [ρ1, hxsv]) (by simp [ρ1, hysv])
    (by simp [ρ1, hacc])
  rw [tw2] at s2
  set ρ2 := Function.update ρ1 .sy (cstream A w (rpStream (cvM a) Zv) ++ ρ1 .sy) with hρ2
  -- 3. the synthetic convolution onto `so`
  have s3 := cvSynth_runs (body := body) (ι := ι) (Pre := Pre) hrg hdisj hP hT hQ (by omega)
    hF hO hPF hPO hπ hp hw hSw Zu Zv hu hv ρ2 (by simp [ρ2, ρ1]) (by simp [ρ2, ρ1, hsy])
    (by simp [ρ2, ρ1, ht1]) (by simp [ρ2, ρ1, hxs]) (by simp [ρ2, ρ1, hout])
    (by simp [ρ2, ρ1, hrd.wn]) (by simp [ρ2, ρ1, hsv]) (by simp [ρ2, ρ1, hta])
    (by simp [ρ2, ρ1, htb]) (by simp [ρ2, ρ1, hracc]) (by simp [ρ2, ρ1, htmp])
    (by simp [ρ2, ρ1, hd0]) (fun j hj => by simp [ρ2, ρ1, hpriv j hj]) (by simp [ρ2, ρ1, hshD])
    (by simp [ρ2, ρ1, hshS]) (by simp [ρ2, ρ1, hshR]) (by simp [ρ2, ρ1, hshT])
    (by simp [ρ2, ρ1, hshU])
  rw [hconv] at s3
  set ρ3 := Function.update (Function.update (Function.update ρ2 .io []) .sy []) .so
    (cstream A w (rpStream (cvM a) (cvNum p (convC a p Tu Tv))) ++ ρ2 .so) with hρ3
  have hcm3 : (fun x => ρ3 (.cm x)) = fun x => ρ (.cm x) := by funext x; simp [ρ3, ρ2, ρ1]
  -- 4. untwist of `so` onto `fo`
  have s4 := cv_table_runs (body := body) (Pre := Pre) hrg hdisj hι hT64 hQs hA
    (xs := .so) (ys := .tm) (out := .fo)
    (cvLay_inj (by decide) (by decide) (by decide) (fun _ => by simp) (fun _ => by simp)
      (fun _ => by simp)) (w := w) (q := p) (by omega) (by omega) ρ3 (by rw [hcm3]; exact hrd) _
    Θm hLm
    (hlen _ Θm (by simp [hΘm])) hfitsS (hfitsΘ θm hθm)
    (by simp [ρ3, ρ2, ρ1, hso, cv_blocks_flatten]) (by simp [ρ3, ρ2, ρ1, htm])
    (by simp [ρ3, ρ2, ρ1, hxsv]) (by simp [ρ3, ρ2, ρ1, hysv]) (by simp [ρ3, ρ2, ρ1, hacc])
  rw [tw4] at s4
  set ρ4 := Function.update ρ3 .fo (cstream A w
    (cstNumBox p t (cconvApproxVia (boxSplit t h) p θp θm (synthMr a (cvN t) p) f g)) ++
      ρ3 .fo) with hρ4
  -- 5. clear `so`
  have s5 := CvRuns.of_rsa (Pre := Pre) (rsa_uclear (body := body) (ι := ι) hrg .so ρ4)
  have H := s1.seq hdisj hP (s2.seq hdisj hP (s3.seq hdisj hP (s4.seq hdisj hP s5)))
  refine (H.congr ?_).mono ?_
  · funext k
    simp only [ρ4, ρ3, ρ2, ρ1, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · have e1 : (ρ4 .so).length = cvM a * 2 ^ l * w := by
      simp [ρ4, ρ3, ρ2, ρ1, hso, length_cstream, length_rpStream]
    rw [e1, cv_blocks_flatten, cv_blocks_flatten, cv_blocks_flatten, length_rpStream,
      length_rpStream, length_rpStream]
    unfold cvBoxCost
    omega

end Main


/-! ### The pipeline instance -/

section Pipeline

open IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Fast.TableNum IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem cv_numer_twistPlus (p r : ℕ) (k : Fin r) :
    numer p (twistPlus p r k) = ⟨tblTwRe p r k, tblTwIm p r k⟩ := by
  rw [tbl_twistPlus]
  exact (congrArg (numer p) (cv_mk_grid p ⟨tblTwRe p r k, tblTwIm p r k⟩)).trans
    (cst_numer_grid p _)

theorem cv_numer_twistMinus (p r : ℕ) (k : Fin r) :
    numer p (twistMinus p r k) = ⟨tblTwRe p r k, -tblTwIm p r k⟩ := by
  rw [tbl_twistMinus]
  exact (congrArg (numer p) (cv_mk_grid p ⟨tblTwRe p r k, -tblTwIm p r k⟩)).trans
    (cst_numer_grid p _)

/-- The twist stream of the table machine (`conj = false`) is the stream of the numerators of
`θ̃⁺ = twistPlus p r`. -/
theorem cv_twistPlus_stream (A w p r : ℕ) :
    tblTwistStream A w p r false =
      cstream A w (List.ofFn fun k : Fin r => numer p (twistPlus p r k)) := by
  rw [tblTwistStream, cstream, List.ofFn_eq_map, List.flatMap_map, ← cst_map_val_finRange,
    List.flatMap_map]
  refine List.flatMap_congr fun k _ => ?_
  simp [tblTwistEntry, cv_numer_twistPlus, csyms]

/-- The twist stream of the table machine (`conj = true`) is the stream of the numerators of
`θ̃⁻ = twistMinus p r`. -/
theorem cv_twistMinus_stream (A w p r : ℕ) :
    tblTwistStream A w p r true =
      cstream A w (List.ofFn fun k : Fin r => numer p (twistMinus p r k)) := by
  rw [tblTwistStream, cstream, List.ofFn_eq_map, List.flatMap_map, ← cst_map_val_finRange,
    List.flatMap_map]
  refine List.flatMap_congr fun k _ => ?_
  simp [tblTwistEntry, cv_numer_twistMinus, csyms]

theorem cv_twistPlus_ok (p r : ℕ) (k : Fin r) :
    IsFixed p (twistPlus p r k) ∧ ‖twistPlus p r k‖ ≤ 1 :=
  ⟨isFixed_rhoC _ _, ((twist_phaseApprox p r).1 k).2⟩

theorem cv_twistMinus_ok (p r : ℕ) (k : Fin r) :
    IsFixed p (twistMinus p r k) ∧ ‖twistMinus p r k‖ ≤ 1 :=
  ⟨cst_isFixed_conj (isFixed_rhoC _ _), ((twist_phaseApprox p r).2 k).2⟩

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : CvR → Fin T}
  {ι : Fin 64 → Fin T} {Pre : Stacks T A → Prop}

/-- **`cvBox` computes `boxConvSucc`** (`Mult/Pipeline`), with the twist tables of the table
machine on `tp`, `tm` and `a i = log₂ t_i` for the first `D` axes. -/
theorem cvBox_boxConvSucc (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hP : CvFramed rg Pre) (hT64 : 64 ≤ T) (hQs : SS.states ≤ Q)
    (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 96 ≤ A)
    {D l : ℕ} (t : Fin (D + 1) → ℕ) [∀ i, NeZero (t i)] (hrl : t (Fin.last D) = 2 ^ l)
    (hpow : ∀ i, t i = 2 ^ Nat.log 2 (t i)) (hdvd : ∀ i, t i ∣ 2 * t (Fin.last D))
    {fwdP oppP : Pr P T Q A U} {PreF PreO : Stacks T A → Prop} {w p cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (rg .io) PreF w p l (fun i : Fin D => Nat.log 2 (t i.castSucc))
      π cF)
    (hO : SynOppSpec body oppP (rg .io) PreO w p l (fun i : Fin D => Nat.log 2 (t i.castSucc))
      π cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ n < cvM (fun i : Fin D => Nat.log 2 (t i.castSucc)),
      π n < cvM (fun i : Fin D => Nat.log 2 (t i.castSucc)))
    (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (hSw : (List.ofFn fun i : Fin D => Nat.log 2 (t i.castSucc)).sum ≤ w)
    (hE : eSynth (fun i : Fin D => Nat.log 2 (t i.castSucc)) (cvN t) < 2 ^ p)
    (f g : ((i : Fin (D + 1)) → ZMod (t i)) → ℂ) (hf : ∀ x, IsFixed p (f x))
    (hg : ∀ x, IsFixed p (g x)) (hf1 : ‖f‖ ≤ 1) (hg1 : ‖g‖ ≤ 1)
    (ρ : CvR → List (Fin (A + 4)))
    (hfi : ρ .fi = cstream A w (cstNumBox p t f)) (hgi : ρ .gi = cstream A w (cstNumBox p t g))
    (htp : ρ .tp = tblTwistStream A w p (t (Fin.last D)) false)
    (htm : ρ .tm = tblTwistStream A w p (t (Fin.last D)) true)
    (hio : ρ .io = []) (hsy : ρ .sy = []) (hso : ρ .so = []) (ht1 : ρ .t1 = [])
    (hrd : Ready (fun x => ρ (.cm x)) w p) (hxsv : ρ (.cm .xsv) = [])
    (hysv : ρ (.cm .ysv) = []) (hacc : ρ (.cm .acc) = [])
    (hxs : ρ (.rr .xs) = []) (hout : ρ (.rr .out) = []) (hsv : ρ (.rr .sv) = [])
    (hta : ρ (.rr .ta) = []) (htb : ρ (.rr .tb) = []) (hracc : ρ (.rr .acc) = [])
    (htmp : ρ (.rr .tmp) = []) (hd0 : ρ (.rpi 0) = (header p (2 ^ l) w).map bitSymbol)
    (hpriv : ∀ j : Fin 91, j ≠ 0 → ρ (.rpi j) = [])
    (hshD : ρ .shD = [])
    (hshS : (ρ .shS).length = (List.ofFn fun i : Fin D => Nat.log 2 (t i.castSucc)).sum)
    (hshR : (ρ .shR).length = w - (List.ofFn fun i : Fin D => Nat.log 2 (t i.castSucc)).sum)
    (hshT : ρ .shT = []) (hshU : ρ .shU = []) :
    CvRuns body rg ι Pre (cvBox rg ι hrg hι hT64 hQs hT hQ fwdP oppP) ρ
      (Function.update ρ .fo (cstream A w (cstNumBox p t (boxConvSucc p D t f g)) ++ ρ .fo))
      (cvBoxCost T p l w (List.ofFn fun i : Fin D => Nat.log 2 (t i.castSucc)).sum
        (cvM fun i : Fin D => Nat.log 2 (t i.castSucc)) cF cO) :=
  cvBox_runs hrg hdisj hι hP hT64 hQs hT hQ hA t rfl hrl (fun i => Nat.log 2 (t i.castSucc))
    (fun i => hpow i.castSucc) (fun i => by rw [← hpow i.castSucc]; exact hdvd i.castSucc) hF hO
    hPF hPO hπ hp hw hSw hE (twistPlus p _) (twistMinus p _) (cv_twistPlus_ok p _)
    (cv_twistMinus_ok p _) f g hf hg hf1 hg1 ρ hfi hgi (htp.trans (cv_twistPlus_stream A w p _))
    (htm.trans (cv_twistMinus_stream A w p _)) hio hsy hso ht1 hrd hxsv hysv hacc hxs hout hsv
    hta htb hracc htmp hd0 hpriv hshD hshS hshR hshT hshU

/-- The exponents `log₂ tᵢ` of the first `D' - 1` axes of a box with `D'` axes. -/
def cvAx {D' : ℕ} (t : Fin D' → ℕ) : Fin (D' - 1) → ℕ := fun i => Nat.log 2 (t ⟨i, by omega⟩)

/-- The lengths of the first `D' - 1` axes. -/
abbrev cvNx {D' : ℕ} (t : Fin D' → ℕ) : Fin (D' - 1) → ℕ := fun i => t ⟨i, by omega⟩

/-- **`cvBox` computes `boxConv`** on a box with `D' ≥ 1` axes, the last of length `2^l`. -/
theorem cvBox_boxConv (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hP : CvFramed rg Pre) (hT64 : 64 ≤ T) (hQs : SS.states ≤ Q)
    (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 96 ≤ A)
    {D' l : ℕ} (t : Fin D' → ℕ) [inst : ∀ i, NeZero (t i)] (hD : 0 < D')
    (hlast : ∀ i : Fin D', (i : ℕ) + 1 = D' → t i = 2 ^ l)
    (hpow : ∀ i, t i = 2 ^ Nat.log 2 (t i)) (hdvd : ∀ i, t i ∣ 2 * 2 ^ l)
    {fwdP oppP : Pr P T Q A U} {PreF PreO : Stacks T A → Prop} {w p cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (rg .io) PreF w p l (cvAx t) π cF)
    (hO : SynOppSpec body oppP (rg .io) PreO w p l (cvAx t) π cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ n < cvM (cvAx t), π n < cvM (cvAx t)) (hp : 1 ≤ p) (hw : p + 2 ≤ w)
    (hSw : (List.ofFn (cvAx t)).sum ≤ w) (hE : eSynth (cvAx t) (cvNx t) < 2 ^ p)
    (f g : ((i : Fin D') → ZMod (t i)) → ℂ) (hf : ∀ x, IsFixed p (f x))
    (hg : ∀ x, IsFixed p (g x)) (hf1 : ‖f‖ ≤ 1) (hg1 : ‖g‖ ≤ 1)
    (ρ : CvR → List (Fin (A + 4)))
    (hfi : ρ .fi = cstream A w (cstNumBox p t f)) (hgi : ρ .gi = cstream A w (cstNumBox p t g))
    (htp : ρ .tp = tblTwistStream A w p (2 ^ l) false)
    (htm : ρ .tm = tblTwistStream A w p (2 ^ l) true)
    (hio : ρ .io = []) (hsy : ρ .sy = []) (hso : ρ .so = []) (ht1 : ρ .t1 = [])
    (hrd : Ready (fun x => ρ (.cm x)) w p) (hxsv : ρ (.cm .xsv) = [])
    (hysv : ρ (.cm .ysv) = []) (hacc : ρ (.cm .acc) = [])
    (hxs : ρ (.rr .xs) = []) (hout : ρ (.rr .out) = []) (hsv : ρ (.rr .sv) = [])
    (hta : ρ (.rr .ta) = []) (htb : ρ (.rr .tb) = []) (hracc : ρ (.rr .acc) = [])
    (htmp : ρ (.rr .tmp) = []) (hd0 : ρ (.rpi 0) = (header p (2 ^ l) w).map bitSymbol)
    (hpriv : ∀ j : Fin 91, j ≠ 0 → ρ (.rpi j) = [])
    (hshD : ρ .shD = []) (hshS : (ρ .shS).length = (List.ofFn (cvAx t)).sum)
    (hshR : (ρ .shR).length = w - (List.ofFn (cvAx t)).sum)
    (hshT : ρ .shT = []) (hshU : ρ .shU = []) :
    CvRuns body rg ι Pre (cvBox rg ι hrg hι hT64 hQs hT hQ fwdP oppP) ρ
      (Function.update ρ .fo (cstream A w (cstNumBox p t (boxConv p D' t inst f g)) ++ ρ .fo))
      (cvBoxCost T p l w (List.ofFn (cvAx t)).sum (cvM (cvAx t)) cF cO) := by
  obtain ⟨D, rfl⟩ : ∃ D, D' = D + 1 := ⟨D' - 1, by omega⟩
  have hl : t (Fin.last D) = 2 ^ l := hlast _ rfl
  exact cvBox_boxConvSucc hrg hdisj hι hP hT64 hQs hT hQ hA t hl hpow
    (fun i => by rw [hl]; exact hdvd i) hF hO hPF hPO hπ hp hw hSw hE f g hf hg hf1 hg1 ρ hfi hgi
    (by rw [hl]; exact htp) (by rw [hl]; exact htm) hio hsy hso ht1 hrd hxsv hysv hacc hxs hout
    hsv hta htb hracc htmp hd0 hpriv hshD hshS hshR hshT hshU

end Pipeline


/-! ### The instance `convBox n` -/

section ConvBoxN

open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Pipeline IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- The product of the axis lengths splits off the last axis. -/
theorem cv_prod_last {D' : ℕ} (t : Fin D' → ℕ) (hD : 0 < D') :
    ∏ i, t i = (∏ i, cvNx t i) * t ⟨D' - 1, by omega⟩ := by
  obtain ⟨D, rfl⟩ : ∃ D, D' = D + 1 := ⟨D' - 1, by omega⟩
  rw [Fin.prod_univ_castSucc]
  rfl

/-- The record count `M = ∏_{i < d-1} t_i` times `r` is `T`. -/
theorem cv_M_mul_r {n : ℕ} (h : Sizes.Big n) :
    cvM (cvAx (Sizes.t n)) * Sizes.r n = Sizes.T n := by
  have hd := h.one_le_d
  have hN : ∀ i, cvNx (Sizes.t n) i = 2 ^ cvAx (Sizes.t n) i := fun i => t_pow_log n _
  rw [cvM, ← tsA_prod, ← ofFn_eq_tsA _ _ hN, List.prod_ofFn, ← Sizes.prod_t hd,
    cv_prod_last (Sizes.t n) (by omega),
    t_of_last h ⟨Sizes.d n - 1, by omega⟩ (by show Sizes.d n - 1 + 1 = Sizes.d n; omega)]

/-- `eSynth < 2^p` at the pipeline sizes, from the margin `hEs` of `convBox_spec`. -/
theorem cv_eSynth_lt {n : ℕ} (h : Sizes.Big n)
    (hEs : 9 * (2 : ℝ) ^ Sizes.gamma n * Sizes.T n * Sizes.logT n ≤ 2 ^ Sizes.p n / 100) :
    eSynth (cvAx (Sizes.t n)) (cvNx (Sizes.t n)) < 2 ^ Sizes.p n := by
  have hA : nRounds (cvAx (Sizes.t n)) ≤ Sizes.ℓ n :=
    Finset.sup_le fun i _ => log_t_le n _
  have hlt := eSynth_lt (r := Sizes.r n) (cvAx (Sizes.t n)) (cvNx (Sizes.t n)) (two_le_r h) hA
    (by have := h.two_le_ℓ; omega) (ℓ_le_logT h)
  have hd := h.one_le_d
  have hT : Sizes.r n * ∏ i, cvNx (Sizes.t n) i = Sizes.T n := by
    rw [← Sizes.prod_t hd, cv_prod_last (Sizes.t n) (by omega),
      t_of_last h ⟨Sizes.d n - 1, by omega⟩ (by show Sizes.d n - 1 + 1 = Sizes.d n; omega),
      mul_comm]
  rw [hT] at hlt
  have hg4 : (16 : ℝ) ≤ 2 ^ Sizes.gamma n :=
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ Sizes.gamma n := pow_le_pow_right₀ (by norm_num) (four_le_gamma h)
  have hX : (0 : ℝ) ≤ (Sizes.T n : ℝ) * Sizes.logT n := by positivity
  have hp : (0 : ℝ) < 2 ^ Sizes.p n := by positivity
  nlinarith

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : CvR → Fin T}
  {ι : Fin 64 → Fin T} {Pre : Stacks T A → Prop}

/-- **`cvBox` computes `convBox n`.** For large `n` (`Big n`, the margin `hEs` of
`Pipeline.convBox_spec`): `fi`, `gi` hold the box streams of grid functions `f`, `g` on
`∏ ZMod (t n i)` of sup norm at most `1`, `tp`, `tm` the twist streams of the table machine,
the transforms meet their contracts for `a = cvAx (t n)` (`aᵢ = log₂ t_i`, `i < d - 1`) and a
record order `π`; then `fo` gains the box stream of `convBox n f g`, every other register ends
as it started, within `cvBoxCost T p ℓ w (Σ aᵢ) M cF cO` steps, `M r = T` (`cv_M_mul_r`). -/
theorem cvBox_convBox (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hP : CvFramed rg Pre) (hT64 : 64 ≤ T) (hQs : SS.states ≤ Q)
    (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 96 ≤ A) {n : ℕ} (hn : Sizes.Big n)
    (hEs : 9 * (2 : ℝ) ^ Sizes.gamma n * Sizes.T n * Sizes.logT n ≤ 2 ^ Sizes.p n / 100)
    {fwdP oppP : Pr P T Q A U} {PreF PreO : Stacks T A → Prop} {w cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (rg .io) PreF w (Sizes.p n) (Sizes.ℓ n) (cvAx (Sizes.t n)) π cF)
    (hO : SynOppSpec body oppP (rg .io) PreO w (Sizes.p n) (Sizes.ℓ n) (cvAx (Sizes.t n)) π cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ m < cvM (cvAx (Sizes.t n)), π m < cvM (cvAx (Sizes.t n)))
    (hw : Sizes.p n + 2 ≤ w) (hSw : (List.ofFn (cvAx (Sizes.t n))).sum ≤ w)
    (f g : ((i : Fin (Sizes.d n)) → ZMod (Sizes.t n i)) → ℂ) (hf : ∀ x, IsFixed (Sizes.p n) (f x))
    (hg : ∀ x, IsFixed (Sizes.p n) (g x)) (hf1 : ‖f‖ ≤ 1) (hg1 : ‖g‖ ≤ 1)
    (ρ : CvR → List (Fin (A + 4)))
    (hfi : ρ .fi = cstream A w (cstNumBox (Sizes.p n) (Sizes.t n) f))
    (hgi : ρ .gi = cstream A w (cstNumBox (Sizes.p n) (Sizes.t n) g))
    (htp : ρ .tp = tblTwistStream A w (Sizes.p n) (Sizes.r n) false)
    (htm : ρ .tm = tblTwistStream A w (Sizes.p n) (Sizes.r n) true)
    (hio : ρ .io = []) (hsy : ρ .sy = []) (hso : ρ .so = []) (ht1 : ρ .t1 = [])
    (hrd : Ready (fun x => ρ (.cm x)) w (Sizes.p n)) (hxsv : ρ (.cm .xsv) = [])
    (hysv : ρ (.cm .ysv) = []) (hacc : ρ (.cm .acc) = [])
    (hxs : ρ (.rr .xs) = []) (hout : ρ (.rr .out) = []) (hsv : ρ (.rr .sv) = [])
    (hta : ρ (.rr .ta) = []) (htb : ρ (.rr .tb) = []) (hracc : ρ (.rr .acc) = [])
    (htmp : ρ (.rr .tmp) = [])
    (hd0 : ρ (.rpi 0) = (header (Sizes.p n) (Sizes.r n) w).map bitSymbol)
    (hpriv : ∀ j : Fin 91, j ≠ 0 → ρ (.rpi j) = [])
    (hshD : ρ .shD = []) (hshS : (ρ .shS).length = (List.ofFn (cvAx (Sizes.t n))).sum)
    (hshR : (ρ .shR).length = w - (List.ofFn (cvAx (Sizes.t n))).sum)
    (hshT : ρ .shT = []) (hshU : ρ .shU = []) :
    CvRuns body rg ι Pre (cvBox rg ι hrg hι hT64 hQs hT hQ fwdP oppP) ρ
      (Function.update ρ .fo
        (cstream A w (cstNumBox (Sizes.p n) (Sizes.t n) (convBox n f g)) ++ ρ .fo))
      (cvBoxCost T (Sizes.p n) (Sizes.ℓ n) w (List.ofFn (cvAx (Sizes.t n))).sum
        (cvM (cvAx (Sizes.t n))) cF cO) :=
  cvBox_boxConv hrg hdisj hι hP hT64 hQs hT hQ hA (Sizes.t n) (by have := hn.one_le_d; omega)
    (fun i hi => t_of_last hn i hi) (t_pow_log n) (t_dvd_two_r n) hF hO hPF hPO hπ
    (by have := hn.thirteen_le_p; omega) hw hSw (cv_eSynth_lt hn hEs) f g hf hg hf1 hg1 ρ hfi hgi
    htp htm hio hsy hso ht1 hrd hxsv hysv hacc hxs hout hsv hta htb hracc htmp hd0 hpriv hshD
    hshS hshR hshT hshU

end ConvBoxN

end

end IntegerMultBounds.MathlibTM2.Fast.ConvSt
