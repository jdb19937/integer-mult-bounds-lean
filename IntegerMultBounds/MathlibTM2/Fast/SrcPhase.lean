module

public import IntegerMultBounds.MathlibTM2.Fast.SrcSem

/-!
# The phases of the source transform

The source transform runs seven phases on the register file `SrcF` of `Fast/SrcRegs`. Each phase
is a fixed program over the machine constants `SrcMach` (the layout `rg`, the multiplier
registers `ι`, the interchange constants, the state and register bounds) and a contract from a
register file `E` to `{E with …}`: only the named families change.

* `srcPA` (`srcA_runs`): `Ã` along every axis on the box register `a .ln`
  (`PrepA.rsaStage_exec`): from the padded stream of `v` at scale `2^p` to the box of
  `x₁ = tensorZR s t (lineA n) v` at scale `2^{p+1}`.
* `srcPK` (`srcK_runs`): the stored descriptions `x .tSp`, `x .sSp` copied into the chirp loader,
  then the chirp kernel stage (`LoadChirp.ldChirpStage_exec`): `k .kr` gains the kernel box
  `cstNumBox p t (chirpKernel n)`.
* `srcPC1` (`srcC1_runs`): `x₁` moved onto `m .ys`; the conjugate kernel onto `m .xs`
  (`PointStage.cstConjKeep`), the products `tdivN (p+1) (ā' x₁)` onto `m .out` (`cmulStream`,
  shift `p + 1`, `src_zip_chirp1`); `m .xs`, `m .ys` cleared: `m .out` holds the first chirp
  product `x₀ = Q_p(ā' · x₁)`.
* `srcPV` (`srcV_runs`): the kernel copied onto `v .fi`, `x₀` moved onto `v .gi`, the ring header
  `Γ(p)Γ(2^ℓ)Γ(w)` written on `v (.rpi 0)` from the unary `p`, `ℓ`, `w`
  (`LoadRing.ldrHeader_exec`), the convolution stage (`ConvBox.cvBox_convBox`), and `fi`, `gi`,
  the header cleared: `v .fo` holds `y₀ = convBox n a' x₀`.
* `srcPC2` (`srcC2_runs`): `y₀` moved onto `v (.cm .ys)`, the second chirp product through the
  convolution's complex-product registers (`PointStage.cst_chirpMulKeep_runs`, shift `p`), the
  operand and the kernel cleared: `v (.cm .out)` holds `C̃ x₁ = Q_p(ā' · y₀)`.
* `srcPB` (`srcB_runs`): `C̃ x₁` moved onto the box register `b (.inl .src)` and `B̃₀` along every
  axis (`PrepB.rsbStage_exec`): the padded stream of `z = tensorZR t s (lineB n) (C̃ x₁)`.
* `srcPG` (`srcG_runs`): the exact scale by `2^γ` (`PointStage.cst_scale_runs`) onto `x .sb`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Src

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.Spec.SignedRingProduct (header)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

/-! ### Machine constants -/

/-- The machine constants of the source transform: the layout and the multiplier registers,
the interchange headers `hd` and payload `pay` of the resampling stages, and the bounds on the
number of registers and states the stage programs need. -/
structure SrcMach (t₀ T Q : ℕ) where
  rg : SrcR t₀ → Fin T
  ι : Fin 64 → Fin T
  hrg : Function.Injective rg
  hι : Function.Injective ι
  hdisj : ∀ r j, rg r ≠ ι j
  hT : 64 ≤ T
  hT91 : 91 ≤ T
  hQ : SS.states ≤ Q
  hQrp : rpStates ≤ Q
  hd : Fin 5 → Fin t₀
  pay : Fin t₀
  hi : Function.Injective hd
  hdpay : ∀ k, hd k ≠ pay
  hQs : swapStates hd pay hi ≤ Q
  hTs : swapT t₀ ≤ T
  hQc : swapStates crtHd crtPay crtHd_inj ≤ Q
  hTc : swapT 6 ≤ T

variable {t₀ T Q : ℕ}

/-- The layout of `Ã`. -/
abbrev SrcMach.ra (M : SrcMach t₀ T Q) : RsaR (RsaX t₀) → Fin T := fun r => M.rg (.a r)
/-- The layout of `B̃₀`. -/
abbrev SrcMach.rb (M : SrcMach t₀ T Q) : RsbR → Fin T := fun r => M.rg (.b (.inl r))
/-- The extra layout of `B̃₀`. -/
abbrev SrcMach.rbx (M : SrcMach t₀ T Q) : RsbX t₀ → Fin T := fun x => M.rg (.b (.inr x))
/-- The layout of the chirp kernel stage. -/
abbrev SrcMach.rk (M : SrcMach t₀ T Q) : CsR ldcX → Fin T := fun r => M.rg (.k r)
/-- The layout of the convolution stage. -/
abbrev SrcMach.rv (M : SrcMach t₀ T Q) : CvR → Fin T := fun r => M.rg (.v r)
/-- The layout of the CRT machines. -/
abbrev SrcMach.rc (M : SrcMach t₀ T Q) : CrtReg → Fin T := fun r => M.rg (.c r)
/-- The interchange bank of the CRT machines. -/
abbrev SrcMach.rcb (M : SrcMach t₀ T Q) : Fin (swapT 6) → Fin T := fun j => M.rg (.cb j)

lemma SrcMach.hra (M : SrcMach t₀ T Q) : Function.Injective M.ra := M.hrg.comp SrcR.a_inj
lemma SrcMach.hrk (M : SrcMach t₀ T Q) : Function.Injective M.rk := M.hrg.comp SrcR.k_inj
lemma SrcMach.hrv (M : SrcMach t₀ T Q) : Function.Injective M.rv := M.hrg.comp SrcR.v_inj
lemma SrcMach.hrc (M : SrcMach t₀ T Q) : Function.Injective M.rc := M.hrg.comp SrcR.c_inj
lemma SrcMach.hrcb (M : SrcMach t₀ T Q) : Function.Injective M.rcb := M.hrg.comp SrcR.cb_inj
lemma SrcMach.hrb2 (M : SrcMach t₀ T Q) : Function.Injective (Sum.elim M.rb M.rbx) := by
  intro x y h
  have e : Sum.elim M.rb M.rbx = fun z => M.rg (.b z) := by funext z; cases z <;> rfl
  rw [e] at h
  exact SrcR.b_inj (M.hrg h)

lemma SrcMach.hswA (M : SrcMach t₀ T Q) : Function.Injective fun j => M.ra (.x (.sw j)) :=
  fun _ _ h => RsaX.sw_injective (RsaR.x.inj (SrcR.a.inj (M.hrg h)))

lemma SrcMach.hswB (M : SrcMach t₀ T Q) : Function.Injective fun j => M.rbx (.sw j) :=
  fun _ _ h => RsbX.sw.inj (Sum.inr.inj (SrcR.b.inj (M.hrg h)))

lemma SrcMach.elim_b (M : SrcMach t₀ T Q) : Sum.elim M.rb M.rbx = fun z => M.rg (.b z) := by
  funext z; cases z <;> rfl

/-! ### Programs -/

section Programs

variable {K : ℕ} {U P : Type} (M : SrcMach t₀ T Q)

/-- Phase `Ã`. -/
def srcPA : Pr P T Q (prime + K) U :=
  rsaAllP (preA M.ra M.ι M.hd) M.ra M.ι M.hι M.hT M.hQ M.hd M.pay M.hi M.hQs M.hswA M.hTs

/-- Phase: the chirp kernel. -/
def srcPK : Pr P T Q (prime + K) U :=
  .seq (bcopy (M.rg (.x .tSp)) (M.rg (.k (.x .tS))) (M.rg (.x .c1)) (M.rg (.x .c2))) <|
  .seq (bcopy (M.rg (.x .sSp)) (M.rg (.k (.x .sS))) (M.rg (.x .c1)) (M.rg (.x .c2)))
    (cstChirpBox M.ι M.hι M.hT M.hQ M.rk (ldcPrep M.rk))

/-- Phase: the first chirp product. -/
def srcPC1 : Pr P T Q (prime + K) U :=
  .seq (srcMv M.rg (.a .ln) (.m .ys) (.x .tr)) <|
  .seq (cstChirpMul M.ι M.hι M.hT M.hQ M.rg SrcR.m (.k .kr) (.x .cA) (.x .cB) (.x .c1) (.x .c2))
    (uclear (M.rg (.m .ys)))

/-- Phase: the complex convolution with its operands and ring header. -/
def srcPV (fwdP oppP : Pr P T Q (prime + K) U) : Pr P T Q (prime + K) U :=
  .seq (bcopy (M.rg (.k .kr)) (M.rg (.v .fi)) (M.rg (.x .c1)) (M.rg (.x .c2))) <|
  .seq (srcMv M.rg (.m .out) (.v .gi) (.x .tr)) <|
  .seq (ldrHeader (M.rg (.k (.x .pU))) (M.rg (.x .lU)) (M.rg (.k (.x .wU))) (M.rg (.v (.rpi 0)))
    (M.rg (.v (.rr .ta))) (M.rg (.v (.rr .tb))) (M.rg (.v (.rr .acc))) (M.rg (.v (.rr .sv)))
    (M.rg (.v (.rr .tmp)))) <|
  .seq (cvBox M.rv M.ι M.hrv M.hι M.hT M.hQ M.hT91 M.hQrp fwdP oppP) <|
  .seq (uclear (M.rg (.v .fi))) <| .seq (uclear (M.rg (.v .gi))) (uclear (M.rg (.v (.rpi 0))))

/-- Phase: the second chirp product. -/
def srcPC2 : Pr P T Q (prime + K) U :=
  .seq (srcMv M.rg (.v .fo) (.v (.cm .ys)) (.x .tr)) <|
  .seq (cstChirpMul M.ι M.hι M.hT M.hQ M.rg (fun x => .v (.cm x)) (.k .kr) (.x .cA) (.x .cB)
    (.x .c1) (.x .c2)) <|
  .seq (uclear (M.rg (.v (.cm .ys)))) (uclear (M.rg (.k .kr)))

/-- Phase `B̃₀`. -/
def srcPB : Pr P T Q (prime + K) U :=
  .seq (srcMv M.rg (.v (.cm .out)) (.b (.inl .src)) (.x .tr))
    (rsbAllP (preB M.rb M.rbx M.ι M.hd) M.rb M.rbx M.hι M.hT M.hQ M.hd M.pay M.hi M.hQs M.hswB
      M.hTs)

/-- Phase: the exact scale by `2^γ` onto `x .sb`. -/
def srcPG : Pr P T Q (prime + K) U :=
  shiftInto (M.rg (.b (.inl .src))) (M.rg (.x .gD)) (M.rg (.x .sb)) (M.rg (.x .gS))
    (M.rg (.x .gR)) (M.rg (.x .gT)) (M.rg (.x .gU)) (pairSym (prime + K) false false)

end Programs

/-! ### Phase `Ã` -/

section PhaseA

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- The cost of phase `Ã`. -/
def srcCostA (M : SrcMach t₀ T Q) (n w W : ℕ) (hd0 : 0 < d n) (V₀ : RsaV (RsaX t₀) (prime + K))
    (rest : List (Fin (prime + K + 4))) : ℕ :=
  rsaAllCost (K := K) T t₀ w (windowA (p n) (alpha n)) (d n) (t n) hd0
    (rsaPipeData n (preHsA n w hd0)) M.hd (preCpA V₀ M.hd n w W hd0 rest) (∏ i, t n i)

/-- **Phase `Ã`.** The box register `a .ln` holds the padded stream of a grid function `v` of
modulus at most `1` on the source box; the `Ã` family is the base file `V₀` with the records on
`c .out`. Afterwards `a .ln` holds the box of `Ã v = tensorZR s t (lineA n) v` at scale
`2^{p+1}` (a grid function at that scale) and the `Ã` family is configured for axis `0`. -/
theorem srcA_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hd0 : 0 < d n) {w W : ℕ} (hw : p n + 3 ≤ w) (hwW : w ≤ W)
    (hW : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (V₀ : RsaV (RsaX t₀) (prime + K)) (hV₀ : PreBaseA V₀ w M.hd)
    (rest : List (Fin (prime + K + 4))) (hout : V₀.cr .out = preRecsA n W hd0 0 ++ rest)
    (axs : List (Fin (prime + K + 4))) (haxs : axs.length = d n - 1)
    (v : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) (hv : ∀ x, ‖v x‖ ≤ 1)
    (hvf : ∀ x, IsFixed (p n) (v x)) (E : SrcF t₀ (prime + K))
    (hE : E.a = (rsaWith V₀ (cstream (prime + K) w (srcPad (p n) (s n) (t n) v)) axs []).get) :
    (∀ k, IsFixed (p n + 1) (tensorZR (d n) (s n) (t n) (lineA n) v (cstCast (t n) k))) ∧
    RsaRuns body M.rg M.ι (srcPA M) E.get
      { E with a := (rsaWith (preCfgA V₀ M.hd n w W hd0 rest (d n - 1))
          (cstream (prime + K) w (cstNumBox (p n + 1) (t n) (tensorZR (d n) (s n) (t n)
            (lineA n) v))) axs []).get }.get
      (srcCostA M n w W hd0 V₀ rest) := by
  set F₀ : ((i : Fin (d n)) → Fin (t n i)) → GaussianInt := fun x =>
    if ∀ i, (x i : ℕ) < s n i then numer (p n) (v fun i => ((x i : ℕ) : ZMod (s n i))) else 0
    with hF₀
  obtain ⟨G, hG, hrun⟩ := rsaStage_exec (body := body) (rg := M.ra) (ι := M.ι) n hbig hd0 M.hra
    (fun r j => M.hdisj _ j) M.hι M.hT M.hQ hA M.hd M.pay M.hi M.hQs M.hswA M.hTs M.hdpay hw hwW
    hW V₀ hV₀ rest hout v hv F₀
    (fun x hx => by
      simp only [hF₀, if_pos hx]
      exact (cst_grid_numer (hvf _)).symm)
    (fun x hx => by
      obtain ⟨i, hi⟩ := hx
      simp only [hF₀]
      rw [if_neg (fun h => absurd (h i) (not_lt.2 hi))])
    axs haxs
  have hbox : rsaBox (d n) (t n) G =
      cstNumBox (p n + 1) (t n) (tensorZR (d n) (s n) (t n) (lineA n) v) := by
    rw [cstNumBox_eq]
    congr 1
    funext x
    rw [hG x]
    exact (cst_numer_grid _ _).symm
  refine ⟨fun k => by rw [hG k]; exact cst_isFixed_grid _ _, ?_⟩
  have hl := src_lift M.hrg SrcR.a_inj hrun E.get (fun x => by rw [SrcF.get_a, hE]; rfl)
  rw [SrcF.ext_a, hbox] at hl
  exact hl

end PhaseA

/-! ### Phase: the chirp kernel -/

section PhaseK

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- `CstBase` only reads the stage registers, not the caller's. -/
lemma src_cstBase_of {A w p g : ℕ} {ρ ρ' : CsR ldcX → List (Fin (A + 4))}
    (h : CstBase ρ w p g) (he : ∀ r, (∀ j, r ≠ .x j) → ρ' r = ρ r) : CstBase ρ' w p g := by
  have hc : (fun x => ρ' (.c x)) = fun x => ρ (.c x) := funext fun x => he _ (by simp)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  refine ⟨hc ▸ h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rwa [he _ (by simp)]

/-- The cost of the chirp kernel phase. -/
def srcCostK (n w W : ℕ) : ℕ :=
  (6 * (ldcBlocks (A := prime + K) (List.ofFn (t n))).length + 6) +
    (6 * (ldcBlocks (A := prime + K) (List.ofFn (s n))).length + 6) +
    cstChirpCost T w (List.ofFn (t n)) fun k =>
      ldcAxisCost W w (p n) (Chirp.chirpGuard (d n)) ((List.ofFn (t n)).getD k 0)
        ((List.ofFn (s n)).getD k 0)

/-- **Phase: the chirp kernel.** The stored descriptions `x .tSp`, `x .sSp` (the axis lengths
`t` and the chirp steps `s` as delimited unary blocks) are copied into the loader and the
kernel stage runs: `k .kr` gains the kernel box `cstNumBox p t (chirpKernel n)`; every other
register ends as it started. -/
theorem srcK_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) (n : ℕ) {w W : ℕ}
    (hd : 1 ≤ d n) (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hsN : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    (E : SrcF t₀ (prime + K)) (hb : CstBase E.k w (p n) (Chirp.chirpGuard (d n)))
    (hax : (E.k .ax).length + 1 = d n) (htS : E.k (.x .tS) = []) (hsS : E.k (.x .sS) = [])
    (htU : E.k (.x .tU) = []) (hsU : E.k (.x .sU) = [])
    (hpU : (E.k (.x .pU)).length = p n) (hgU : (E.k (.x .gU)).length = Chirp.chirpGuard (d n))
    (hwU : (E.k (.x .wU)).length = w) (hwr : (E.k (.x (.tbl .wr))).length = W)
    (hwn : (E.k (.x (.tbl .wn))).length = w)
    (htb : ∀ r, r ≠ .wr → r ≠ .wn → E.k (.x (.tbl r)) = [])
    (htSp : E.x .tSp = ldcBlocks (List.ofFn (t n))) (hsSp : E.x .sSp = ldcBlocks (List.ofFn (s n)))
    (hc1 : E.x .c1 = []) (hc2 : E.x .c2 = []) :
    RsaRuns body M.rg M.ι (srcPK M) E.get
      { E with k := (Function.update E.k .kr
          (cstream (prime + K) w (cstNumBox (p n) (t n) (chirpKernel n)) ++ E.k .kr)) }.get
      (srcCostK (K := K) (T := T) n w W) := by
  have hdisj := M.hdisj
  have s1 := rsa_bcopy (body := body) (ι := M.ι) M.hrg (a := .x .tSp) (c := .k (.x .tS))
    (t₁ := .x .c1) (t₂ := .x .c2) (by simp) E.get hc1 hc2
  rw [SrcF.get_x, SrcF.get_k, htSp, htS, List.append_nil, SrcF.upd_k] at s1
  set E₁ := { E with k := Function.update E.k (.x .tS) (ldcBlocks (List.ofFn (t n))) } with hE₁
  have s2 := rsa_bcopy (body := body) (ι := M.ι) M.hrg (a := .x .sSp) (c := .k (.x .sS))
    (t₁ := .x .c1) (t₂ := .x .c2) (by simp) E₁.get hc1 hc2
  rw [SrcF.get_x, SrcF.get_k, hE₁, hsSp] at s2
  simp only [Function.update_of_ne (show (CsR.x ldcX.sS : CsR ldcX) ≠ .x .tS by decide), hsS,
    List.append_nil, SrcF.upd_k] at s2
  set E₂ := { E with k := Function.update (Function.update E.k (.x .tS)
    (ldcBlocks (List.ofFn (t n)))) (.x .sS) (ldcBlocks (List.ofFn (s n))) } with hE₂
  have hk₂ : ∀ r, (∀ j, r ≠ .x j) → E₂.k r = E.k r := fun r hr => by
    simp only [hE₂]
    rw [Function.update_of_ne (hr _), Function.update_of_ne (hr _)]
  have hx₂ : ∀ j, j ≠ .tS → j ≠ .sS → E₂.k (.x j) = E.k (.x j) := fun j h1 h2 => by
    simp only [hE₂]
    rw [Function.update_of_ne (by simpa using h2), Function.update_of_ne (by simpa using h1)]
  have h3 := ldChirpStage_exec (body := body) (rg := M.rk) (ι := M.ι) M.hrk
    (fun r j => M.hdisj _ j) M.hι M.hT M.hQ hA n hd hw hwW hsN hWk E₂.k
    (src_cstBase_of hb hk₂) (by rw [hk₂ _ (by simp)]; exact hax)
    (by simp [hE₂]) (by simp [hE₂])
    (by rw [hx₂ _ (by decide) (by decide)]; exact htU)
    (by rw [hx₂ _ (by decide) (by decide)]; exact hsU)
    (by rw [hx₂ _ (by decide) (by decide)]; exact hpU)
    (by rw [hx₂ _ (by decide) (by decide)]; exact hgU)
    (by rw [hx₂ _ (by decide) (by decide)]; exact hwU)
    (by rw [hx₂ _ (by decide) (by decide)]; exact hwr)
    (by rw [hx₂ _ (by decide) (by decide)]; exact hwn)
    (fun r h1 h2 => by rw [hx₂ _ (by simp) (by simp)]; exact htb r h1 h2)
  have s3 := src_lift M.hrg SrcR.k_inj h3 E₂.get (fun _ => rfl)
  rw [SrcF.ext_k] at s3
  refine ((s1.seq hdisj (s2.seq hdisj s3)).congr ?_).mono (le_of_eq ?_)
  · congr 1
    simp only [hE₂]
    congr 1
    funext r
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · simp only [srcCostK, SrcF.get_x, htSp, hsSp]
    ring

end PhaseK

/-! ### Generic contracts -/

section Generic

variable {T Q A : ℕ} {U P R : Type} [DecidableEq R] {body : P → Pr P T Q A U} {rg : R → Fin T}
  {ι : Fin 64 → Fin T}

variable (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
include hrg hdisj

/-- **The first chirp product, kernel kept.** As `PointStage.cst_chirpMulKeep_runs`, with the
operand `x` at scale `2^{q+1}` and the product shift `q + 1` on `pn`: `out` gains the numerator
box of `cstChirpProd t q a' x = k ↦ Q_q (conj (a' k) · x k)` at scale `2^q`. -/
theorem src_chirpMul1_runs (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (hA : 96 ≤ A) {c : CR → R} (hc : Function.Injective c) {kr tA tB t1 t2 : R}
    (hd : [kr, tA, tB, t1, t2].Nodup)
    (hcx : ∀ x, c x ≠ kr ∧ c x ≠ tA ∧ c x ≠ tB ∧ c x ≠ t1 ∧ c x ≠ t2) {w q : ℕ}
    (hw : 1 ≤ w) (hq : q + 1 ≤ w) {d : ℕ} (t : Fin d → ℕ) [∀ i, NeZero (t i)]
    (a' x : ((i : Fin d) → ZMod (t i)) → ℂ)
    (ha : ∀ k, IsFixed q (a' (cstCast t k))) (hx : ∀ k, IsFixed (q + 1) (x (cstCast t k)))
    (haw : ∀ k, Fits w (numer q (a' (cstCast t k))))
    (hxw : ∀ k, Fits w (numer (q + 1) (x (cstCast t k))))
    (ρ : R → List (Fin (A + 4))) (hr : Ready (fun x => ρ (c x)) w (q + 1))
    (hK : ρ kr = cstream A w (cstNumBox q t a'))
    (hY : ρ (c .ys) = cstream A w (cstNumBox (q + 1) t x))
    (hxs : ρ (c .xs) = []) (hxsv : ρ (c .xsv) = []) (hysv : ρ (c .ysv) = [])
    (hacc : ρ (c .acc) = []) (htA : ρ tA = []) (htB : ρ tB = []) (ht1 : ρ t1 = [])
    (ht2 : ρ t2 = []) :
    RsaRuns body rg ι (cstChirpMul ι hι hT hQ rg c kr tA tB t1 t2) ρ
      (Function.update ρ (c .out) (cstream A w (cstNumBox q t (cstChirpProd t q a' x)) ++
        ρ (c .out)))
      ((∏ i, t i) * (cmulCost T w + 21 * w + 8) + 20) := by
  have hd' := hd
  regs_ne hd'
  obtain ⟨a1, a2, a3, a4, a5⟩ := hcx .xs
  obtain ⟨b1, b2, b3, b4, b5⟩ := hcx .wn
  obtain ⟨c1, c2, c3, c4, c5⟩ := hcx .tmp
  have n1 : c .xs ≠ c .wn := hc.ne (by decide)
  have n2 : c .xs ≠ c .tmp := hc.ne (by decide)
  have n3 : c .wn ≠ c .tmp := hc.ne (by decide)
  have hn : [kr, c .xs, tA, tB, t1, t2, c .wn, c .tmp].Nodup := by regs_nodup
  have h1 := cst_conjKeep_box (body := body) (ι := ι) hrg hdisj (src := kr) (dst := c .xs)
    (tA := tA) (tB := tB) (t1 := t1) (t2 := t2) (st := c .tmp) (ctr := c .wn) (tmp := c .tmp) hn
    (Ne.symm c2) (by omega) hw t a' ρ hK htA htB ht1 ht2 hr.wn hr.tmp
  rw [hxs, List.append_nil] at h1
  set ρ₁ := Function.update ρ (c .xs)
    (cstream A w (cstNumBox q t fun k => starRingEnd ℂ (a' k))) with hρ₁
  have hr₁ : Ready (fun y => ρ₁ (c y)) w (q + 1) :=
    cst_ready_of_eq hr (fun y h1 _ _ _ _ _ => by
      simp only [hρ₁]; rw [Function.update_of_ne (hc.ne h1)])
  have hne : ∀ y, y ≠ CR.xs → ρ₁ (c y) = ρ (c y) := fun y hy => by
    simp only [hρ₁]; rw [Function.update_of_ne (hc.ne hy)]
  have hcr : Function.Injective (fun x => rg (c x)) := fun a b e => hc (hrg e)
  have hdisj' : ∀ r j, (fun x => rg (c x)) r ≠ ι j := fun r j => hdisj _ j
  have mem_box : ∀ {q' : ℕ} (g : ((i : Fin d) → ZMod (t i)) → ℂ),
      (∀ x, Fits w (numer q' (g (cstCast t x)))) → ∀ N ∈ cstNumBox q' t g, Fits w N := by
    intro q' g hg N hN
    obtain ⟨x, rfl⟩ := cst_mem_numBox hN
    exact hg x
  have h2 := RsaRuns.of_c hrg hc
    (cmulStream_runs (body := body) (cr := fun x => rg (c x)) hcr hdisj' hι hT hQ hA
      (ρ := fun x => ρ₁ (c x)) hr₁ hw hq (cstNumBox q t fun k => starRingEnd ℂ (a' k))
      (cstNumBox (q + 1) t x) (by rw [cst_length_numBox, cst_length_numBox])
      (mem_box _ fun k => by rw [cst_numer_conj]; exact cst_fits_star (haw k)) (mem_box x hxw)
      (by simp [hρ₁]) (by rw [hne _ (by decide)]; exact hY)
      (by rw [hne _ (by decide)]; exact hxsv) (by rw [hne _ (by decide)]; exact hysv)
      (by rw [hne _ (by decide)]; exact hacc)) ρ₁ (fun _ => rfl)
  rw [cst_extend_update _ hc, src_zip_chirp1 t a' x ha hx, cst_length_numBox] at h2
  have h3 := rsa_uclear (body := body) (ι := ι) hrg (c .xs)
    (Function.update ρ₁ (c .out) (cstream A w (cstNumBox q t (cstChirpProd t q a' x)) ++
      ρ₁ (c .out)))
  refine ((RsaRuns.seq hdisj h1 (RsaRuns.seq hdisj h2 h3)).congr ?_).mono ?_
  · have n4 : c .xs ≠ c .out := hc.ne (by decide)
    funext k
    simp only [hρ₁, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · have e1 : (Function.update ρ₁ (c .out)
        (cstream A w (cstNumBox q t (cstChirpProd t q a' x)) ++ ρ₁ (c .out)) (c .xs)).length =
          (∏ i, t i) * w := by
      rw [Function.update_of_ne (hc.ne (by decide)), hρ₁, Function.update_self, length_cstream,
        cst_length_numBox]
    rw [e1]
    nlinarith

/-- **The ring header** `Γ(|pR|) Γ(2^|lR|) Γ(|wR|)` onto `d0`, the work registers empty and
kept empty. -/
theorem src_header_runs {pR lR wR d0 a h par cnt t : R}
    (hreg : [pR, lR, wR, d0, a, h, par, cnt, t].Nodup) (ρ : R → List (Fin (A + 4)))
    (ha : ρ a = []) (hh : ρ h = []) (hp : ρ par = []) (hc : ρ cnt = []) (ht : ρ t = []) :
    RsaRuns body rg ι
      (ldrHeader (rg pR) (rg lR) (rg wR) (rg d0) (rg a) (rg h) (rg par) (rg cnt) (rg t)) ρ
      (Function.update ρ d0 ((header (ρ pR).length (2 ^ (ρ lR).length) (ρ wR).length).map
        bitSymbol ++ ρ d0))
      (ldrHeaderCost (ρ pR).length (ρ lR).length (ρ wR).length) := by
  refine RsaRuns.of_raw fun v S _ hS => ?_
  obtain ⟨v', m, hu, hm, he⟩ := ldrHeader_exec body (hreg.map hrg) v S (by rw [hS, ha])
    (by rw [hS, hh]) (by rw [hS, hp]) (by rw [hS, hc]) (by rw [hS, ht])
  rw [hS, hS, hS] at hm
  rw [hS, hS, hS, hS] at he
  exact ⟨v', _, m, hu, hm, he, rsa_holds_upd hrg hS d0 _, fun k hk => rsa_upd_off _ _ _ hk⟩

end Generic

/-! ### Phase: the first chirp product -/

section PhaseC1

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- The cost of a chirp product phase on a box of `V` entries. -/
def srcCostC (T w V : ℕ) : ℕ :=
  (4 * (V * w) + 4) + (V * (cmulCost T w + 21 * w + 8) + 20) + (2 * (V * w) + 2)

/-- **Phase: the first chirp product.** `a .ln` holds the box of `x` at scale `2^{q+1}`, `k .kr`
the kernel box at scale `2^q`; the `m` family is ready for `w` and the shift `q + 1`. Afterwards
`m .out` holds the box of `Q_q(ā' · x)` at scale `2^q`, `a .ln` is empty and every other
register ends as it started. -/
theorem srcC1_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {w q : ℕ} (hw : 1 ≤ w)
    (hq : q + 1 ≤ w) {d : ℕ} (t : Fin d → ℕ) [∀ i, NeZero (t i)]
    (a' x : ((i : Fin d) → ZMod (t i)) → ℂ)
    (ha : ∀ k, IsFixed q (a' (cstCast t k))) (hx : ∀ k, IsFixed (q + 1) (x (cstCast t k)))
    (haw : ∀ k, Fits w (numer q (a' (cstCast t k))))
    (hxw : ∀ k, Fits w (numer (q + 1) (x (cstCast t k)))) (E : SrcF t₀ (prime + K))
    (hln : E.a .ln = cstream (prime + K) w (cstNumBox (q + 1) t x))
    (hK : E.k .kr = cstream (prime + K) w (cstNumBox q t a')) (hr : Ready E.m w (q + 1))
    (hxs : E.m .xs = []) (hys : E.m .ys = []) (hxsv : E.m .xsv = []) (hysv : E.m .ysv = [])
    (hacc : E.m .acc = []) (hout : E.m .out = []) (htr : E.x .tr = []) (htA : E.x .cA = [])
    (htB : E.x .cB = []) (ht1 : E.x .c1 = []) (ht2 : E.x .c2 = []) :
    RsaRuns body M.rg M.ι (srcPC1 M) E.get
      { E with a := Function.update E.a .ln [],
               m := (Function.update E.m .out
                 (cstream (prime + K) w (cstNumBox q t (cstChirpProd t q a' x)))) }.get
      (srcCostC T w (∏ i, t i)) := by
  have hdisj := M.hdisj
  have s1 := src_mv_runs (body := body) M.hrg hdisj (a := .a .ln) (b := .m .ys) (sp := .x .tr)
    (by simp) (by simp) (by simp) E.get htr
  rw [SrcF.get_a, SrcF.get_m, hys, List.append_nil, SrcF.upd_a, SrcF.upd_m] at s1
  set E₁ : SrcF t₀ (prime + K) :=
    { E with a := Function.update E.a .ln [], m := Function.update E.m .ys (E.a .ln) } with hE₁
  have hm₁ : ∀ y, y ≠ CR.ys → E₁.m y = E.m y := fun y hy => by
    simp only [hE₁, Function.update_of_ne hy]
  have s2 := src_chirpMul1_runs (body := body) M.hrg hdisj M.hι M.hT M.hQ hA SrcR.m_inj
    (kr := .k .kr) (tA := .x .cA) (tB := .x .cB) (t1 := .x .c1) (t2 := .x .c2) (by simp)
    (fun _ => by simp) hw hq t a' x ha hx haw hxw E₁.get
    (cst_ready_of_eq hr fun y _ h2 _ _ _ _ => hm₁ y h2) hK
    (by simp [hE₁, hln]) (by rw [SrcF.get_m, hm₁ _ (by decide), hxs])
    (by rw [SrcF.get_m, hm₁ _ (by decide), hxsv]) (by rw [SrcF.get_m, hm₁ _ (by decide), hysv])
    (by rw [SrcF.get_m, hm₁ _ (by decide), hacc]) htA htB ht1 ht2
  rw [SrcF.get_m, hm₁ _ (by decide), hout, List.append_nil, SrcF.upd_m] at s2
  have s3 := rsa_uclear (body := body) (ι := M.ι) M.hrg (.m .ys)
    { E₁ with m := (Function.update E₁.m .out
      (cstream (prime + K) w (cstNumBox q t (cstChirpProd t q a' x)))) }.get
  rw [SrcF.upd_m] at s3
  refine ((s1.seq hdisj (s2.seq hdisj s3)).congr ?_).mono (le_of_eq ?_)
  · congr 1
    simp only [hE₁]
    congr 1
    funext r
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · simp only [srcCostC, SrcF.get_m, hE₁, hln, length_cstream, cst_length_numBox,
      Function.update_of_ne (show CR.ys ≠ CR.out by decide), Function.update_self]
    ring

end PhaseC1

/-! ### Phase: the complex convolution -/

section PhaseV

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- The convolution family between runs of the source transform: the complex-product registers
ready for `w` and `p` with empty operands, the twist tables of the table machine on `tp`, `tm`,
the shift's counters with `Σ aᵢ` and `w - Σ aᵢ` symbols (`aᵢ = log₂ t_i`, `i < d - 1`), every
other register empty. -/
structure SrcConvBase {A : ℕ} (ρ : CvR → List (Fin (A + 4))) (n w : ℕ) : Prop where
  ready : Ready (fun x => ρ (.cm x)) w (p n)
  cmxs : ρ (.cm .xs) = []
  cmys : ρ (.cm .ys) = []
  cmxsv : ρ (.cm .xsv) = []
  cmysv : ρ (.cm .ysv) = []
  cmacc : ρ (.cm .acc) = []
  cmout : ρ (.cm .out) = []
  tp : ρ .tp = TableVM.tblTwistStream A w (p n) (r n) false
  tm : ρ .tm = TableVM.tblTwistStream A w (p n) (r n) true
  fi : ρ .fi = []
  gi : ρ .gi = []
  fo : ρ .fo = []
  io : ρ .io = []
  sy : ρ .sy = []
  so : ρ .so = []
  t1 : ρ .t1 = []
  rxs : ρ (.rr .xs) = []
  rout : ρ (.rr .out) = []
  rsv : ρ (.rr .sv) = []
  rta : ρ (.rr .ta) = []
  rtb : ρ (.rr .tb) = []
  racc : ρ (.rr .acc) = []
  rtmp : ρ (.rr .tmp) = []
  rpi : ∀ j, ρ (.rpi j) = []
  shD : ρ .shD = []
  shS : (ρ .shS).length = (List.ofFn (cvAx (t n))).sum
  shR : (ρ .shR).length = w - (List.ofFn (cvAx (t n))).sum
  shT : ρ .shT = []
  shU : ρ .shU = []

/-- The cost of the convolution phase: the operand copy and transfer, the ring header, the
stage, and the three clears. -/
def srcCostV (T n w cF cO : ℕ) : ℕ :=
  (6 * ((∏ i, t n i) * w) + 6) + (4 * ((∏ i, t n i) * w) + 4) + ldrHeaderCost (p n) (ℓ n) w +
    cvBoxCost T (p n) (ℓ n) w (List.ofFn (cvAx (t n))).sum (cvM (cvAx (t n))) cF cO +
    (2 * ((∏ i, t n i) * w) + 2) + (2 * ((∏ i, t n i) * w) + 2) +
    (2 * (header (p n) (2 ^ ℓ n) w).length + 2)

set_option maxHeartbeats 1000000 in
/-- **Phase: the complex convolution.** `k .kr` holds the kernel box of `a'`, `m .out` the box
of `x₀` (grid functions at scale `2^p` of modulus at most `1`); the unary `p`, `ℓ`, `w` are on
`k (.x .pU)`, `x .lU`, `k (.x .wU)`. Afterwards `v .fo` holds the box of `convBox n a' x₀`,
`m .out` is empty and every other register ends as it started. -/
theorem srcV_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {n : ℕ} (hn : Big n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : Pr P T Q (prime + K) U} {Pre PreF PreO : Stacks T (prime + K) → Prop}
    {w cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (M.rg (.v .io)) PreF w (p n) (ℓ n) (cvAx (t n)) π cF)
    (hO : SynOppSpec body oppP (M.rg (.v .io)) PreO w (p n) (ℓ n) (cvAx (t n)) π cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ m < cvM (cvAx (t n)), π m < cvM (cvAx (t n))) (hP : SrcFramed M.rg Pre)
    (hw : p n + 2 ≤ w) (hSw : (List.ofFn (cvAx (t n))).sum ≤ w)
    (a' x₀ : ((i : Fin (d n)) → ZMod (t n i)) → ℂ) (ha : ∀ y, IsFixed (p n) (a' y))
    (hx : ∀ y, IsFixed (p n) (x₀ y)) (ha1 : ‖a'‖ ≤ 1) (hx1 : ‖x₀‖ ≤ 1)
    (E : SrcF t₀ (prime + K)) (hv : SrcConvBase E.v n w)
    (hK : E.k .kr = cstream (prime + K) w (cstNumBox (p n) (t n) a'))
    (hX : E.m .out = cstream (prime + K) w (cstNumBox (p n) (t n) x₀))
    (hpU : (E.k (.x .pU)).length = p n) (hlU : (E.x .lU).length = ℓ n)
    (hwU : (E.k (.x .wU)).length = w) (htr : E.x .tr = []) (hc1 : E.x .c1 = [])
    (hc2 : E.x .c2 = []) :
    SrcRuns body M.rg M.ι Pre (srcPV M fwdP oppP) E.get
      { E with m := Function.update E.m .out [],
               v := (Function.update E.v .fo
                 (cstream (prime + K) w (cstNumBox (p n) (t n) (convBox n a' x₀)))) }.get
      (srcCostV T n w cF cO) := by
  have hdisj := M.hdisj
  -- the kernel copy
  have s1 := rsa_bcopy (body := body) (ι := M.ι) M.hrg (a := .k .kr) (c := .v .fi)
    (t₁ := .x .c1) (t₂ := .x .c2) (by simp) E.get hc1 hc2
  rw [SrcF.get_k, SrcF.get_v, hv.fi, List.append_nil, SrcF.upd_v] at s1
  set E₁ : SrcF t₀ (prime + K) := { E with v := Function.update E.v .fi (E.k .kr) } with hE₁
  -- the operand transfer
  have s2 := src_mv_runs (body := body) M.hrg hdisj (a := .m .out) (b := .v .gi) (sp := .x .tr)
    (by simp) (by simp) (by simp) E₁.get htr
  rw [SrcF.get_m, SrcF.get_v, SrcF.upd_m, SrcF.upd_v] at s2
  set E₂ : SrcF t₀ (prime + K) :=
    { E with m := Function.update E.m .out [],
             v := (Function.update (Function.update E.v .fi (E.k .kr)) .gi (E.m .out)) }
    with hE₂
  have hv₂ : ∀ y, y ≠ .fi → y ≠ .gi → E₂.v y = E.v y := fun y h1 h2 => by
    simp only [hE₂, Function.update_of_ne h1, Function.update_of_ne h2]
  have e₂ : ({ { E₁ with m := Function.update E₁.m .out [] } with
      v := Function.update { E₁ with m := Function.update E₁.m .out [] }.v .gi
        (E₁.m .out ++ { E₁ with m := Function.update E₁.m .out [] }.v .gi) } : SrcF t₀ _) = E₂ := by
    simp only [hE₁, hE₂, Function.update_of_ne (show CvR.gi ≠ .fi by decide), hv.gi,
      List.append_nil]
  rw [e₂] at s2
  -- the ring header
  have s3 := src_header_runs (body := body) M.hrg hdisj (pR := .k (.x .pU)) (lR := .x .lU)
    (wR := .k (.x .wU)) (d0 := .v (.rpi 0)) (a := .v (.rr .ta)) (h := .v (.rr .tb))
    (par := .v (.rr .acc)) (cnt := .v (.rr .sv)) (t := .v (.rr .tmp)) (by simp) E₂.get
    (by rw [SrcF.get_v, hv₂ _ (by decide) (by decide), hv.rta])
    (by rw [SrcF.get_v, hv₂ _ (by decide) (by decide), hv.rtb])
    (by rw [SrcF.get_v, hv₂ _ (by decide) (by decide), hv.racc])
    (by rw [SrcF.get_v, hv₂ _ (by decide) (by decide), hv.rsv])
    (by rw [SrcF.get_v, hv₂ _ (by decide) (by decide), hv.rtmp])
  simp only [SrcF.get_k, SrcF.get_x, SrcF.get_v] at s3
  rw [hv₂ _ (by decide) (by decide), hv.rpi, List.append_nil, SrcF.upd_v] at s3
  have hk₂ : E₂.k = E.k := rfl
  have hx₂ : E₂.x = E.x := rfl
  rw [hk₂, hx₂, hpU, hlU, hwU] at s3
  set H : List (Fin (prime + K + 4)) := (header (p n) (2 ^ ℓ n) w).map bitSymbol with hH
  set E₃ : SrcF t₀ (prime + K) := { E₂ with v := Function.update E₂.v (.rpi 0) H } with hE₃
  have hv₃ : ∀ y, y ≠ .fi → y ≠ .gi → y ≠ .rpi 0 → E₃.v y = E.v y := fun y h1 h2 h3 => by
    simp only [hE₃, Function.update_of_ne h3]; exact hv₂ y h1 h2
  -- the convolution stage
  have hcv := cvBox_convBox (body := body) (rg := M.rv) (ι := M.ι) (Pre := Pre) M.hrv
    (fun r j => M.hdisj _ j) M.hι (hP.comp (f := SrcR.v)) M.hT M.hQ M.hT91 M.hQrp hA hn hEs
    hF hO hPF hPO hπ hw hSw a' x₀ ha hx ha1 hx1 E₃.v
    (by simp [hE₃, hE₂, hK]) (by simp [hE₃, hE₂, hX])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.tp])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.tm])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.io])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.sy])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.so])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.t1])
    (cst_ready_of_eq hv.ready fun y _ _ _ _ _ _ => hv₃ _ (by simp) (by simp) (by simp))
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.cmxsv])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.cmysv])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.cmacc])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.rxs])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.rout])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.rsv])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.rta])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.rtb])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.racc])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.rtmp])
    (by simp only [hE₃, Function.update_self]; rfl)
    (fun j hj => by
      rw [hv₃ _ (by simp) (by simp) (by simpa using hj), hv.rpi])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.shD])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.shS])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.shR])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.shT])
    (by rw [hv₃ _ (by decide) (by decide) (by decide), hv.shU])
  have s4 := SrcRuns.lift M.hrg SrcR.v_inj hcv E₃.get (fun _ => rfl)
  rw [SrcF.ext_v, hv₃ _ (by decide) (by decide) (by decide), hv.fo, List.append_nil] at s4
  set Y := cstream (prime + K) w (cstNumBox (p n) (t n) (convBox n a' x₀)) with hY
  set E₄ : SrcF t₀ (prime + K) := { E₃ with v := Function.update E₃.v .fo Y } with hE₄
  -- the clears
  have s5 := rsa_uclear (body := body) (ι := M.ι) M.hrg (.v .fi) E₄.get
  rw [SrcF.upd_v] at s5
  have s6 := rsa_uclear (body := body) (ι := M.ι) M.hrg (.v .gi)
    { E₄ with v := Function.update E₄.v .fi [] }.get
  rw [SrcF.upd_v] at s6
  have s7 := rsa_uclear (body := body) (ι := M.ι) M.hrg (.v (.rpi 0))
    { { E₄ with v := Function.update E₄.v .fi [] } with
      v := Function.update { E₄ with v := Function.update E₄.v .fi [] }.v .gi [] }.get
  rw [SrcF.upd_v] at s7
  refine (((SrcRuns.of_rsa s1).seq hdisj hP ((SrcRuns.of_rsa s2).seq hdisj hP
    ((SrcRuns.of_rsa s3).seq hdisj hP (s4.seq hdisj hP ((SrcRuns.of_rsa s5).seq hdisj hP
    ((SrcRuns.of_rsa s6).seq hdisj hP (SrcRuns.of_rsa s7))))))).congr ?_).mono (le_of_eq ?_)
  · congr 1
    simp only [hE₄, hE₃, hE₂]
    congr 1
    funext y
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [hv.fi, hv.gi, hv.fo, hv.rpi]
  · simp only [srcCostV, SrcF.get_k, SrcF.get_v, hK, hE₄, hE₃, hE₂, hE₁, hX, hY, hH,
      length_cstream, cst_length_numBox, Function.update_self, List.length_map,
      Function.update_of_ne (show CvR.fi ≠ .fo by decide),
      Function.update_of_ne (show CvR.gi ≠ .fo by decide),
      Function.update_of_ne (show CvR.gi ≠ .fi by decide),
      Function.update_of_ne (show CvR.fi ≠ .gi by decide),
      Function.update_of_ne (show CvR.rpi 0 ≠ .fo by decide),
      Function.update_of_ne (show CvR.rpi 0 ≠ .fi by decide),
      Function.update_of_ne (show CvR.rpi 0 ≠ .gi by decide),
      Function.update_of_ne (show CvR.fi ≠ .rpi 0 by decide),
      Function.update_of_ne (show CvR.gi ≠ .rpi 0 by decide)]
    ring

end PhaseV

/-! ### Phase: the second chirp product -/

section PhaseC2

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- **Phase: the second chirp product.** `v .fo` holds the box of `y`, `k .kr` the kernel box
(grid functions at scale `2^q` whose numerators fit `w` bits); the convolution's
complex-product registers are ready for `w` and `q`. Afterwards `v (.cm .out)` holds the box of
`Q_q(ā' · y)`, `v .fo` and `k .kr` are empty and every other register ends as it started. -/
theorem srcC2_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {w q : ℕ} (hw : 1 ≤ w)
    (hq : q ≤ w) {d : ℕ} (t : Fin d → ℕ) [∀ i, NeZero (t i)]
    (a' y : ((i : Fin d) → ZMod (t i)) → ℂ)
    (ha : ∀ k, IsFixed q (a' (cstCast t k))) (hy : ∀ k, IsFixed q (y (cstCast t k)))
    (haw : ∀ k, Fits w (numer q (a' (cstCast t k))))
    (hyw : ∀ k, Fits w (numer q (y (cstCast t k)))) (E : SrcF t₀ (prime + K))
    (hfo : E.v .fo = cstream (prime + K) w (cstNumBox q t y))
    (hK : E.k .kr = cstream (prime + K) w (cstNumBox q t a'))
    (hr : Ready (fun x => E.v (.cm x)) w q)
    (hxs : E.v (.cm .xs) = []) (hys : E.v (.cm .ys) = []) (hxsv : E.v (.cm .xsv) = [])
    (hysv : E.v (.cm .ysv) = []) (hacc : E.v (.cm .acc) = []) (hout : E.v (.cm .out) = [])
    (htr : E.x .tr = []) (htA : E.x .cA = []) (htB : E.x .cB = []) (ht1 : E.x .c1 = [])
    (ht2 : E.x .c2 = []) :
    RsaRuns body M.rg M.ι (srcPC2 M) E.get
      { E with k := Function.update E.k .kr [],
               v := (Function.update (Function.update E.v .fo []) (.cm .out)
                 (cstream (prime + K) w (cstNumBox q t (cstChirpProd t q a' y)))) }.get
      (srcCostC T w (∏ i, t i) + (2 * ((∏ i, t i) * w) + 2)) := by
  have hdisj := M.hdisj
  have s1 := src_mv_runs (body := body) M.hrg hdisj (a := .v .fo) (b := .v (.cm .ys))
    (sp := .x .tr) (by simp) (by simp) (by simp) E.get htr
  rw [SrcF.get_v, SrcF.get_v, hys, List.append_nil, SrcF.upd_v, SrcF.upd_v] at s1
  set E₁ : SrcF t₀ (prime + K) :=
    { E with v := Function.update (Function.update E.v .fo []) (.cm .ys) (E.v .fo) } with hE₁
  have hv₁ : ∀ y, y ≠ .fo → y ≠ .cm .ys → E₁.v y = E.v y := fun y h1 h2 => by
    simp only [hE₁, Function.update_of_ne h1, Function.update_of_ne h2]
  have s2 := cst_chirpMulKeep_runs (body := body) M.hrg hdisj M.hι M.hT M.hQ hA SrcR.vcm_inj
    (kr := .k .kr) (tA := .x .cA) (tB := .x .cB) (t1 := .x .c1) (t2 := .x .c2) (by simp)
    (fun _ => by simp) hw hq t a' y ha hy haw hyw E₁.get
    (cst_ready_of_eq hr fun x _ h2 _ _ _ _ => hv₁ _ (by simp) (by simpa using h2)) hK
    (by simp [hE₁, hfo]) (by rw [SrcF.get_v, hv₁ _ (by simp) (by simp), hxs])
    (by rw [SrcF.get_v, hv₁ _ (by simp) (by simp), hxsv])
    (by rw [SrcF.get_v, hv₁ _ (by simp) (by simp), hysv])
    (by rw [SrcF.get_v, hv₁ _ (by simp) (by simp), hacc]) htA htB ht1 ht2
  rw [SrcF.get_v, hv₁ _ (by simp) (by simp), hout, List.append_nil, SrcF.upd_v] at s2
  set Z := cstream (prime + K) w (cstNumBox q t (cstChirpProd t q a' y)) with hZ
  have s3 := rsa_uclear (body := body) (ι := M.ι) M.hrg (.v (.cm .ys))
    { E₁ with v := Function.update E₁.v (.cm .out) Z }.get
  rw [SrcF.upd_v] at s3
  have s4 := rsa_uclear (body := body) (ι := M.ι) M.hrg (.k .kr)
    { { E₁ with v := Function.update E₁.v (.cm .out) Z } with
      v := Function.update { E₁ with v := Function.update E₁.v (.cm .out) Z }.v (.cm .ys) [] }.get
  rw [SrcF.upd_k] at s4
  refine ((s1.seq hdisj (s2.seq hdisj (s3.seq hdisj s4))).congr ?_).mono (le_of_eq ?_)
  · congr 1
    simp only [hE₁]
    congr 1
    funext r
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · simp only [srcCostC, SrcF.get_v, SrcF.get_k, hE₁, hfo, hK, length_cstream, cst_length_numBox,
      Function.update_self,
      Function.update_of_ne (show CvR.cm .ys ≠ .cm .out by simp)]
    ring

end PhaseC2

/-! ### Phase `B̃₀` -/

section PhaseB

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

lemma src_rsbWith_src {A : ℕ} (σ : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)))
    (l a a' l' : List (Fin (A + 4))) :
    Function.update (rsbWith σ l a a') (.inl .src) l' = rsbWith σ l' a a' := by
  unfold rsbWith
  rw [Sum.update_elim_inl, Function.update_idem]

lemma src_rsa_of_rsb {T Q A : ℕ} {U P R : Type} {body : P → Pr P T Q A U} {rg : R → Fin T}
    {ι : Fin 64 → Fin T} {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : RsbRuns body rg ι p ρ ρ' b) : RsaRuns body rg ι p ρ ρ' b :=
  fun v S hc hS => h v S hc hS

/-- The cost of `B̃₀` along every axis. -/
def srcCostB (M : SrcMach t₀ T Q) (n w W : ℕ) (hd0 : 0 < d n)
    (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (rest : List (Fin (prime + K + 4))) : ℕ :=
  rsbAllCost T t₀ w (FastB0.fastWindow (p n) (alpha n)) (alpha n ^ 2) (d n) (t n) hd0
    (rsbLineBData n (fun i => Nat.log 2 (t n i)) (preHsB n w hd0)) (prime + K) M.hd
    (preCpB σ₀ M.hd n w W hd0 rest) (∏ i, t n i)

/-- **Phase `B̃₀`.** `v (.cm .out)` holds the box of a grid function `c` at scale `2^p` of
modulus at most `1` on the target box; the `B̃₀` family is the base file `σ₀` with the records
on `bo`. Afterwards the box register `b (.inl .src)` holds the padded stream of
`z = tensorZR t s (lineB n) c` (a grid function at scale `2^p` on the source box), the `B̃₀`
family is configured for axis `0` and `v (.cm .out)` is empty. -/
theorem srcB_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hd0 : 0 < d n) {w W : ℕ} (hw : p n + 2 ≤ w) (hwW : w ≤ W)
    (hW : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (13 * p n + 8) < 2 ^ W)
    (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))) (hσ₀ : PreBaseB σ₀ w M.hd)
    (rest : List (Fin (prime + K + 4))) (hout : σ₀ (.inl .bo) = preRecsB n W hd0 0 ++ rest)
    (axs : List (Fin (prime + K + 4))) (haxs : axs.length = d n - 1)
    (c : ((i : Fin (d n)) → ZMod (t n i)) → ℂ) (hc : ∀ y, IsFixed (p n) (c y))
    (hc1 : ∀ y, ‖c y‖ ≤ 1) (E : SrcF t₀ (prime + K)) (hE : E.b = rsbWith σ₀ [] axs [])
    (hC : E.v (.cm .out) = cstream (prime + K) w (cstNumBox (p n) (t n) c))
    (htr : E.x .tr = []) :
    (∀ x : (i : Fin (d n)) → Fin (t n i), (∀ i, (x i : ℕ) < s n i) →
      IsFixed (p n) (tensorZR (d n) (t n) (s n) (lineB n) c
        fun i => ((x i : ℕ) : ZMod (s n i)))) ∧
    RsaRuns body M.rg M.ι (srcPB M) E.get
      { E with v := Function.update E.v (.cm .out) [],
               b := rsbWith (preCfgB σ₀ M.hd n w W hd0 rest (d n - 1))
                 (cstream (prime + K) w (srcPad (p n) (s n) (t n)
                   (tensorZR (d n) (t n) (s n) (lineB n) c))) axs [] }.get
      (4 * ((∏ i, t n i) * w) + 4 + srcCostB M n w W hd0 σ₀ rest) := by
  have hdisj := M.hdisj
  set Fn : ((i : Fin (d n)) → Fin (t n i)) → GaussianInt :=
    fun x => numer (p n) (c (cstCast (t n) x)) with hFn
  obtain ⟨G, hG, hG0, hrun⟩ := rsbStage_exec (body := body) (rg := M.rb) (rgx := M.rbx)
    (ι := M.ι) n hbig hd0 M.hrb2 (fun r j => by rw [M.elim_b]; exact M.hdisj _ j) M.hι M.hT M.hQ
    hA M.hd M.pay M.hi M.hQs M.hswB M.hTs M.hdpay hw hwW hW σ₀ hσ₀ rest hout c Fn
    (fun x => (cst_grid_numer (hc _)).symm) (fun x => hc1 _) axs haxs
  set z := tensorZR (d n) (t n) (s n) (lineB n) c with hz
  have hpad : rsbBox (d n) (t n) G = srcPad (p n) (s n) (t n) z := by
    rw [src_rsbBox_eq, srcPad]
    congr 1
    funext x
    split_ifs with h
    · rw [hG x h]; exact (cst_numer_grid _ _).symm
    · obtain ⟨i, hi⟩ := not_forall.1 h
      exact hG0 x ⟨i, not_lt.1 hi⟩
  refine ⟨fun x hx => by rw [hG x hx]; exact cst_isFixed_grid _ _, ?_⟩
  have s1 := src_mv_runs (body := body) M.hrg hdisj (a := .v (.cm .out)) (b := .b (.inl .src))
    (sp := .x .tr) (by simp) (by simp) (by simp) E.get htr
  rw [SrcF.get_v, SrcF.get_b, SrcF.upd_v, SrcF.upd_b] at s1
  have hsrc0 : rsbWith σ₀ [] axs [] (.inl .src) = [] := by simp [rsbWith]
  set E₁ : SrcF t₀ (prime + K) :=
    { E with v := Function.update E.v (.cm .out) [], b := rsbWith σ₀ (E.v (.cm .out)) axs [] }
    with hE₁
  have e₁ : ({ { E with v := Function.update E.v (.cm .out) [] } with
      b := Function.update { E with v := Function.update E.v (.cm .out) [] }.b (.inl .src)
        (E.v (.cm .out) ++ E.b (.inl .src)) } : SrcF t₀ _) = E₁ := by
    simp only [hE₁, hE, hsrc0, List.append_nil, src_rsbWith_src]
  rw [e₁] at s1
  have hrb := hrun
  rw [M.elim_b] at hrb
  have s2 := src_lift M.hrg SrcR.b_inj (src_rsa_of_rsb hrb) E₁.get (fun x => by
    rw [SrcF.get_b, hE₁, hC, cstNumBox_eq, src_rsbBox_eq])
  rw [SrcF.ext_b, hpad] at s2
  refine ((s1.seq hdisj s2).congr rfl).mono (le_of_eq ?_)
  rw [hC, length_cstream, cst_length_numBox]
  rfl

end PhaseB

/-! ### Phase: the scale by `2^γ` -/

section PhaseG

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- The exact scale of a padded box of grid values. -/
theorem src_pad_scale {d q : ℕ} (s t : Fin d → ℕ) (γ : ℕ) (z : ((i : Fin d) → ZMod (s i)) → ℂ)
    (hz : ∀ x : (i : Fin d) → Fin (t i), (∀ i, (x i : ℕ) < s i) →
      IsFixed q (z fun i => ((x i : ℕ) : ZMod (s i)))) :
    (srcPad q s t z).map (fun N => 2 ^ γ * N) = srcPad q s t ((2 : ℂ) ^ γ • z) := by
  rw [srcPad, srcPad, ← rsaBox_map]
  congr 1
  funext x
  split_ifs with h
  · rw [Pi.smul_apply, smul_eq_mul, cst_numer_two_pow_mul (hz x h)]
  · simp

/-- **Phase: the exact scale by `2^γ`.** The box register `b (.inl .src)` holds the padded
stream of a function `z` on the source box, grid values at scale `2^q` at the valid addresses;
`x .gS`, `x .gR` hold `γ` and `w - γ` symbols. Afterwards `x .sb` gains the padded stream of
`2^γ z` on top, `b (.inl .src)` is empty and every other register ends as it started. -/
theorem srcG_runs (M : SrcMach t₀ T Q) {d q γ w : ℕ} (s t : Fin d → ℕ) (hw : 1 ≤ w)
    (hγ : γ ≤ w) (z : ((i : Fin d) → ZMod (s i)) → ℂ)
    (hz : ∀ x : (i : Fin d) → Fin (t i), (∀ i, (x i : ℕ) < s i) →
      IsFixed q (z fun i => ((x i : ℕ) : ZMod (s i))))
    (E : SrcF t₀ (prime + K)) (hsrc : E.b (.inl .src) = cstream (prime + K) w (srcPad q s t z))
    (hgS : (E.x .gS).length = γ) (hgR : (E.x .gR).length = w - γ) (hgT : E.x .gT = [])
    (hgU : E.x .gU = []) (hgD : E.x .gD = []) :
    RsaRuns body M.rg M.ι (srcPG M) E.get
      { E with b := Function.update E.b (.inl .src) [],
               x := (Function.update E.x .sb
                 (cstream (prime + K) w (srcPad q s t ((2 : ℂ) ^ γ • z)) ++ E.x .sb)) }.get
      ((∏ i, t i) * (6 * w + 4 * γ + 14) + 4) := by
  have h := cst_scale_runs (body := body) (ι := M.ι) M.hrg M.hdisj (src := .b (.inl .src))
    (dst := .x .gD) (out := .x .sb) (cS := .x .gS) (cR := .x .gR) (tS := .x .gT) (tR := .x .gU)
    (by simp) (by simp) hw hγ E.get (srcPad q s t z) hsrc hgS hgR hgT hgU hgD
  rw [src_pad_scale s t γ z hz, if_neg (by simp), src_length_pad, SrcF.upd_b, SrcF.upd_x] at h
  exact h

end PhaseG

end

end IntegerMultBounds.MathlibTM2.Fast.Src
