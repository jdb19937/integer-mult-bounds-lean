module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPacking
public import IntegerMultBounds.Spec.SignedRingProductFacts

/-! # Shared short-convolution execution

Specialize the existing ring-product program to finite, zero-padded blocks. The output
coefficients are exact truncated integer divisions, not an unspecified approximation.
The complete stack equation restores operands, header, counters and all private scratch.
Packing is supplied by `packBlock_coeffs_exec`; this stage starts with packed operands.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.Spec.SignedRingProduct

/-- Numerators returned by the ring product for one short convolution. -/
def coeff (p l : ℕ) (x y : List GaussianInt) (c : Fin (2 ^ l)) : GaussianInt :=
  ⟨(convZ (block x) (block y) c).re.tdiv (2 ^ (p + l)),
    (convZ (block x) (block y) c).im.tdiv (2 ^ (p + l))⟩

/-- Padding and the no-wrap bound identify every output numerator. -/
theorem rpOut_block (p l : ℕ) (x y : List GaussianInt)
    (hxy : x.length + y.length ≤ 2 ^ l + 1) (n : ℕ) :
    rpOut p (fun _ => recOf (2 ^ l) (block x)) (fun _ => recOf (2 ^ l) (block y)) n =
      coeff p l x y := by
  funext c
  exact rpOut_recOf p l (fun _ => block x) (fun _ => block y) x.length y.length hxy
    (fun _ _ hi => block_eq_zero x hi) (fun _ _ hi => block_eq_zero y hi) n c

/-- A single record has exactly the coefficient order used by the packing stage. -/
theorem rpStream_one {r : ℕ} (X : Fin r → GaussianInt) :
    rpStream 1 (fun _ => X) = List.ofFn X := by simp [rpStream]

/-- Decode a Gaussian numerator at precision `p`. -/
noncomputable def value (p : ℕ) (z : GaussianInt) : ℂ :=
  ⟨(z.re : ℝ) / 2 ^ p, (z.im : ℝ) / 2 ^ p⟩

/-- The extracted machine coefficient has the same rounding bound as the ring arithmetic. -/
theorem coeff_err (p l : ℕ) (x y : List GaussianInt)
    (hxy : x.length + y.length ≤ 2 ^ l + 1) (c : Fin (2 ^ l)) :
    ‖((2 ^ l : ℕ) : ℂ) * value p (coeff p l x y c) -
      ∑ i ∈ Finset.range (c.val + 1), value p (block x i) * value p (block y (c.val - i))‖ ≤
        2 * (2 ^ l : ℕ) / (2 : ℝ) ^ p := by
  have hx : ∀ (n i : ℕ), x.length ≤ i → value p (block x i) = 0 := by
    intro n i hi
    simp [block_eq_zero x hi, value, Complex.ext_iff]
  have hy : ∀ (n i : ℕ), y.length ≤ i → value p (block y i) = 0 := by
    intro n i hi
    simp [block_eq_zero y hi, value, Complex.ext_iff]
  have herr := pwC_recOf_err p (fun _ i => value p (block x i))
    (fun _ i => value p (block y i)) x.length y.length hxy hx hy 0 c
  have hgrid (z : List GaussianInt) :
      (fun _ => recOf (2 ^ l) (fun i => value p (block z i))) =
        rpGrid p (fun _ => recOf (2 ^ l) (block z)) := rfl
  rw [hgrid x, hgrid y, rp_pwC_grid, rpOut_block p l x y hxy] at herr
  exact herr

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

/-- Execute a short convolution on packed finite blocks. No abstract execution hypothesis:
this is the actual ring-product program, with its full tape cost and complete bank frame. -/
theorem shortConv_exec (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w : ℕ} (hp : 1 ≤ p) (hw : p + 2 ≤ w) (x y : List GaussianInt)
    (hxy : x.length + y.length ≤ 2 ^ l + 1)
    (hX : DiskGrid p (rpRec (fun _ => recOf (2 ^ l) (block x)) 0).1
      (rpRec (fun _ => recOf (2 ^ l) (block x)) 0).2)
    (hY : DiskGrid p (rpRec (fun _ => recOf (2 ^ l) (block y)) 0).1
      (rpRec (fun _ => recOf (2 ^ l) (block y)) 0).2)
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hxs : S.R (rg .xs) = cstream A w (List.ofFn (recOf (2 ^ l) (block x))))
    (hys : S.R (rg .ys) = cstream A w (List.ofFn (recOf (2 ^ l) (block y))))
    (hwn : (S.R (rg .wn)).length = w)
    (hsv : S.R (rg .sv) = []) (hta : S.R (rg .ta) = []) (htb : S.R (rg .tb) = [])
    (hacc : S.R (rg .acc) = []) (htmp : S.R (rg .tmp) = [])
    (hd0 : S.R (rg .d0) = (header p (2 ^ l) w).map bitSymbol)
    (hd1 : S.R (rg .d1) = []) (hd2 : S.R (rg .d2) = []) (hd3 : S.R (rg .d3) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rpRecCost p l w + rpFixCost p l w ∧
      Exec body (rpProg rg ι h.ι_inj hT hQ) (mk v S) n
        (mk v' { S with R := (Function.update S.R (rg .out)
          (cstream A w (List.ofFn (coeff p l x y)) ++ S.R (rg .out))) }) := by
  obtain ⟨v', n, hu, hn, he⟩ := rpProg_exec (body := body) h hT hQ hA hp hw
    (fun _ => recOf (2 ^ l) (block x)) (fun _ => recOf (2 ^ l) (block y))
    (M := 1) (fun _ _ => hX) (fun _ _ => hY) v S hc
    (by simpa [rpStream_one] using hxs) (by simpa [rpStream_one] using hys)
    hwn hsv hta htb hacc htmp hd0 hd1 hd2 hd3
  refine ⟨v', n, hu, ?_, ?_⟩
  · simpa [rpCost_eq] using hn
  · have hout : rpOut p (fun _ => recOf (2 ^ l) (block x))
        (fun _ => recOf (2 ^ l) (block y)) = fun _ => coeff p l x y :=
      funext (rpOut_block p l x y hxy)
    simpa only [hout, rpStream_one] using he

/-- Disk-grid validity follows directly from each raw numerator, including padded zeros. -/
theorem diskGrid_block (p r : ℕ) (x : List GaussianInt)
    (hx : ∀ z ∈ x, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p)) :
    DiskGrid p (rpRec (fun _ => recOf r (block x)) 0).1
      (rpRec (fun _ => recOf r (block x)) 0).2 := by
  intro c
  change (block x c.val).re ^ 2 + (block x c.val).im ^ 2 ≤ _
  by_cases hi : c.val < x.length
  · simpa only [block, List.getElem?_eq_getElem hi, Option.getD_some] using
      hx x[c.val] (List.getElem_mem hi)
  · rw [block_eq_zero x (by omega)]
    simp

/-- Truncation preserves the disk bound, so output numerators fit the signed tape words. -/
theorem coeff_diskGrid (p l : ℕ) (x y : List GaussianInt)
    (hxy : x.length + y.length ≤ 2 ^ l + 1)
    (hx : ∀ z ∈ x, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hy : ∀ z ∈ y, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p)) :
    DiskGrid p (fun c => (coeff p l x y c).re) (fun c => (coeff p l x y c).im) := by
  let X := fun (_ : ℕ) => recOf (2 ^ l) (block x)
  let Y := fun (_ : ℕ) => recOf (2 ^ l) (block y)
  have hX : SynthErr.SupLe 0 (rpGrid p X) 1 :=
    fun _ _ c => (diskGrid_block p (2 ^ l) x hx).norm_le c
  have hY : SynthErr.SupLe 0 (rpGrid p Y) 1 :=
    fun _ _ c => (diskGrid_block p (2 ^ l) y hy).norm_le c
  have hnorm := SynthErr.pwC_supLe p hX hY
  have hdisk := rp_diskGrid_of_norm p (rpOut p X Y) 0 (fun c => by
    rw [rpGrid_rpOut]
    exact hnorm 0 (by decide) c)
  have hout : rpOut p X Y = fun _ => coeff p l x y :=
    funext (rpOut_block p l x y hxy)
  simpa only [hout, rpRec] using hdisk

/-- Signed-word decoding recovers both output numerators without modular aliasing. -/
theorem coeff_fits (p l w : ℕ) (x y : List GaussianInt)
    (hxy : x.length + y.length ≤ 2 ^ l + 1) (hw : p + 2 ≤ w)
    (hx : ∀ z ∈ x, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hy : ∀ z ∈ y, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p)) (c : Fin (2 ^ l)) :
    compValue (compWord w (coeff p l x y c).re) = (coeff p l x y c).re ∧
    compValue (compWord w (coeff p l x y c).im) = (coeff p l x y c).im :=
  (coeff_diskGrid p l x y hxy hx hy).fits hw c

/-- Actual per-block machine bound, with the packed multiplication priced by its proved bound. -/
theorem shortConv_cost_le (p l w : ℕ) :
    rpRecCost p l w + rpFixCost p l w ≤ rpRecBound p l w + rpFixCost p l w :=
  Nat.add_le_add_right (rpRecCost_le p l w) _

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
