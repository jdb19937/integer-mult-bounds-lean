module

public import IntegerMultBounds.MathlibTM2.Fast.SrcStage
public import IntegerMultBounds.MathlibTM2.Fast.CRTDirectSource

/-! # Source transforms using the concrete direct CRT layouts -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Fast.Src

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open scoped Function


noncomputable section

variable {t₀ T Q : ℕ}

section Transforms

variable {K : ℕ} {U P : Type} {body : P → Pr P T Q (prime + K) U}

/-- **The computed source transform `F' = F̃ ∘ Φ`** (`Pipeline.srcMap`): the CRT layout of the
coefficient stream on `c .str`, the box moved onto `a .ln`, the source transform. -/
def srcDirectP (M : SrcMach t₀ T Q) (fwdP oppP : Pr P T Q (prime + K) U) : Pr P T Q (prime + K) U :=
  .seq (crtDirectSourceForward M.hQc M.rcb M.hrcb M.hTc M.rc) <|
  .seq (srcMv M.rg (.c .str) (.a .ln) (.x .tr)) (srcCore M fwdP oppP)

/-- **The computed opposite transform `G' = Φ⁻¹ ∘ conj ∘ F̃ ∘ conj`** (`Pipeline.oppMap`): the
padded box on `x .sb` conjugated onto `a .ln`, the source transform, its result conjugated onto
`c .str`, the inverse CRT layout. -/
def oppDirectP (M : SrcMach t₀ T Q) (fwdP oppP : Pr P T Q (prime + K) U) : Pr P T Q (prime + K) U :=
  .seq (srcConj M (.x .sb) (.a .ln)) <| .seq (srcCore M fwdP oppP) <|
  .seq (srcConj M (.x .sb) (.c .str)) (crtDirectSourceInverse M.hQc M.rcb M.hrcb M.hTc M.rc)

/-- The cost of `srcDirectP`: the concrete direct CRT layout, the transfer, the source transform. -/
def srcDirectPCost (M : SrcMach t₀ T Q) (n w W cF cO : ℕ) (hd0 : 0 < d n)
    (V₀ : RsaV (RsaX t₀) (prime + K)) (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (restA restB : List (Fin (prime + K + 4))) : ℕ :=
  srcDirectCrtCost (K := K) true T n w + (4 * ((∏ i, t n i) * w) + 4) +
    srcCoreCost M n w W cF cO hd0 V₀ σ₀ restA restB

/-- The cost of `oppDirectP`: two conjugations, the source transform, the inverse CRT layout
with its concrete direct cost. -/
def oppDirectPCost (M : SrcMach t₀ T Q) (n w W cF cO : ℕ) (hd0 : 0 < d n)
    (V₀ : RsaV (RsaX t₀) (prime + K)) (σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4)))
    (restA restB : List (Fin (prime + K + 4))) : ℕ :=
  srcConjCost (∏ i, t n i) w + srcCoreCost M n w W cF cO hd0 V₀ σ₀ restA restB +
    srcConjCost (∏ i, t n i) w + srcDirectCrtCost (K := K) false T n w

/-- **The computed source transform `F'` as a machine.** From the register file between runs
(`SrcBase`, `SrcCrtBase`) with the coefficient stream of `u` (grid values at scale `2^p`,
`‖u‖ ≤ 1/2`) on `c .str` and the box register `a .ln` empty, `srcDirectP` pushes the padded stream of
`Pipeline.srcMap n u` on the source box onto `x .sb`, empties `c .str`, configures the resampling
families for axis `0` (consuming one set of records), and leaves every other register as it
began, within `srcDirectPCost` steps. -/
theorem srcDirectP_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : Pr P T Q (prime + K) U} {Pre PreF PreO : Stacks T (prime + K) → Prop}
    {w W cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (M.rg (.v .io)) PreF w (p n) (ℓ n) (cvAx (t n)) π cF)
    (hO : SynOppSpec body oppP (M.rg (.v .io)) PreO w (p n) (ℓ n) (cvAx (t n)) π cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ m < cvM (cvAx (t n)), π m < cvM (cvAx (t n))) (hP : SrcFramed M.rg Pre)
    (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (hWB : 9 * p n + 2 ≤ w ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX t₀) (prime + K)} {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))} (E : SrcF t₀ (prime + K))
    (hE : SrcBase M E n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB)
    (hC : SrcCrtBase E.c E.cb n w) (hln : E.a .ln = [])
    (u : ZMod (∏ i, s n i) → ℂ) (hu : ‖u‖ ≤ 1 / 2) (huf : ∀ k, IsFixed (p n) (u k))
    (hstr : E.c .str = cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) u)) :
    SrcRuns body M.rg M.ι Pre (srcDirectP M fwdP oppP) E.get
      { E with a := (rsaWith (preCfgA V₀ M.hd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
               b := rsbWith (bandCfgB σ₀ M.hd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
               c := Function.update E.c .str [],
               x := (Function.update E.x .sb
                 (cstream (prime + K) w (srcPad (p n) (s n) (t n) (srcMap n u)) ++ E.x .sb)) }.get
      (srcDirectPCost M n w W cF cO (srcHd0 hbig) V₀ σ₀ restA restB) := by
  have hdisj := M.hdisj
  set v : ((i : Fin (d n)) → ZMod (s n i)) → ℂ :=
    fun x => u ((crtPhi (s n) (s_pairwise n)).symm x) with hvdef
  have s1 := srcDirectCrtF_runs (body := body) M hA hbig (by omega) E hC u hstr
  set BOX := cstream (prime + K) w (srcPad (p n) (s n) (t n) v) with hBOX
  set E₁ : SrcF t₀ (prime + K) := { E with c := Function.update E.c .str BOX } with hE₁
  have s2 := src_mv_runs (body := body) M.hrg hdisj (a := .c .str) (b := .a .ln) (sp := .x .tr)
    (by simp) (by simp) (by simp) E₁.get (by simp [hE₁, hE.x.tr])
  rw [SrcF.get_c, SrcF.get_a, SrcF.upd_c, SrcF.upd_a] at s2
  set E₂ : SrcF t₀ (prime + K) :=
    { E with c := Function.update E.c .str [], a := Function.update E.a .ln BOX } with hE₂
  have e₂ : ({ { E₁ with c := Function.update E₁.c .str [] } with
      a := Function.update { E₁ with c := Function.update E₁.c .str [] }.a .ln
        (E₁.c .str ++ { E₁ with c := Function.update E₁.c .str [] }.a .ln) } :
      SrcF t₀ _) = E₂ := by
    simp only [hE₁, hE₂, Function.update_idem, Function.update_self, hln, List.append_nil]
  rw [e₂] at s2
  have hE₂b : SrcBase M E₂ n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB :=
    hE.of_eq (fun r hr => by simp [hE₂, Function.update_of_ne hr]) rfl rfl rfl rfl
      (fun _ _ => rfl)
  have s3 := srcCore_runs (body := body) M hA hbig hsmall hEs hF hO hPF hPO hπ hP hw hwW hWA hWB
    hWs hWk E₂ hE₂b v
    ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun x => (norm_le_pi_norm u _).trans hu)
    (fun x => huf _) (by simp [hE₂, hBOX])
  refine ((SrcRuns.of_rsa s1).seq hdisj hP ((SrcRuns.of_rsa s2).seq hdisj hP s3)).congr ?_
    |>.mono (le_of_eq ?_)
  · congr 1
  · simp only [srcDirectPCost, hE₁, Function.update_self, hBOX, length_cstream, src_length_pad]
    ring

/-- **The computed opposite transform `G'` as a machine.** From the register file between runs
(`SrcBase`, `SrcCrtBase`) with the padded stream of `y` (grid values at scale `2^p`,
`‖y‖ ≤ 1/2`) on `x .sb`, the box register `a .ln` and `c .str` empty, `oppDirectP` leaves the
coefficient stream of `Pipeline.oppMap n y` on `c .str`, empties `x .sb`, configures the
resampling families for axis `0`, and leaves every other register as it began, within
`oppDirectPCost` steps. -/
theorem srcDirectOpp_runs (M : SrcMach t₀ T Q) (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : Pr P T Q (prime + K) U} {Pre PreF PreO : Stacks T (prime + K) → Prop}
    {w W cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (M.rg (.v .io)) PreF w (p n) (ℓ n) (cvAx (t n)) π cF)
    (hO : SynOppSpec body oppP (M.rg (.v .io)) PreO w (p n) (ℓ n) (cvAx (t n)) π cO)
    (hPF : ∀ S, Pre S → PreF S) (hPO : ∀ S, Pre S → PreO S)
    (hπ : ∀ m < cvM (cvAx (t n)), π m < cvM (cvAx (t n))) (hP : SrcFramed M.rg Pre)
    (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (hWB : 9 * p n + 2 ≤ w ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX t₀) (prime + K)} {σ₀ : RsbR ⊕ RsbX t₀ → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))} (E : SrcF t₀ (prime + K))
    (hE : SrcBase M E n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB)
    (hC : SrcCrtBase E.c E.cb n w) (hln : E.a .ln = []) (hstr : E.c .str = [])
    (y : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) (hy : ‖y‖ ≤ 1 / 2)
    (hyf : ∀ k, IsFixed (p n) (y k))
    (hsb : E.x .sb = cstream (prime + K) w (srcPad (p n) (s n) (t n) y)) :
    SrcRuns body M.rg M.ι Pre (oppDirectP M fwdP oppP) E.get
      { E with a := (rsaWith (preCfgA V₀ M.hd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
               b := rsbWith (bandCfgB σ₀ M.hd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
               c := (Function.update E.c .str
                 (cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) (oppMap n y)))),
               x := Function.update E.x .sb [] }.get
      (oppDirectPCost M n w W cF cO (srcHd0 hbig) V₀ σ₀ restA restB) := by
  have hdisj := M.hdisj
  set yc : ((i : Fin (d n)) → ZMod (s n i)) → ℂ := fun k => starRingEnd ℂ (y k) with hyc
  set SA := SourceErr.sourceApprox (s n) (t n) (p n) (gamma n) (lineA n) (lineB n)
    (chirpKernel n) (convBox n) yc with hSA
  -- the first conjugation
  have s1 := src_conj_runs (body := body) M hA (w := w) (by omega) (src := .x .sb)
    (dst := .a .ln) (by simp) (by simp) (by simp) E.get _ hsb (by simp [hE.x.cB]) hE.m.ready.wn hE.m.ready.tmp
  rw [src_pad_conj, SrcF.get_a, hln, List.append_nil, SrcF.upd_x, SrcF.upd_a, src_length_pad]
    at s1
  set E₁ : SrcF t₀ (prime + K) :=
    { E with x := Function.update E.x .sb [],
             a := Function.update E.a .ln (cstream (prime + K) w (srcPad (p n) (s n) (t n) yc)) }
    with hE₁
  have hE₁b : SrcBase M E₁ n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB :=
    hE.of_eq (fun r hr => by simp [hE₁, Function.update_of_ne hr]) rfl rfl rfl rfl
      (fun j hj => by simp [hE₁, Function.update_of_ne hj])
  -- the source transform
  have s2 := srcCore_runs (body := body) M hA hbig hsmall hEs hF hO hPF hPO hπ hP hw hwW hWA hWB
    hWs hWk E₁ hE₁b yc (by rw [hyc, SourceErr.norm_conj_fun]; exact hy)
    (fun x => cst_isFixed_conj (hyf x)) (by simp [hE₁])
  set E₂ : SrcF t₀ (prime + K) :=
    { E₁ with a := (rsaWith (preCfgA V₀ M.hd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
              b := rsbWith (bandCfgB σ₀ M.hd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
              x := (Function.update E₁.x .sb (cstream (prime + K) w
                (srcPad (p n) (s n) (t n) SA) ++ E₁.x .sb)) } with hE₂
  -- the second conjugation
  have s3 := src_conj_runs (body := body) M hA (w := w) (by omega) (src := .x .sb)
    (dst := .c .str) (by simp) (by simp) (by simp) E₂.get (srcPad (p n) (s n) (t n) SA)
    (by simp [hE₂, hE₁]) (by simp [hE₂, hE₁, hE.x.cB])
    (by simpa [hE₂, hE₁] using hE.m.ready.wn) (by simpa [hE₂, hE₁] using hE.m.ready.tmp)
  rw [src_pad_conj, SrcF.get_c, SrcF.upd_x, SrcF.upd_c, src_length_pad] at s3
  set E₃ : SrcF t₀ (prime + K) :=
    { E₂ with x := Function.update E₂.x .sb [],
              c := (Function.update E.c .str (cstream (prime + K) w
                (srcPad (p n) (s n) (t n) fun k => starRingEnd ℂ (SA k)))) } with hE₃
  replace s3 := s3.congr (ρ'' := E₃.get) (by
    congr 1
    simp only [hE₃, hE₂, hE₁, hstr, List.append_nil])
  -- the inverse layout
  have s4 := srcDirectCrtI_runs (body := body) M hA hbig (w := w) (by omega) E₃ (hC.upd_str _)
    (fun k => starRingEnd ℂ (SA k)) (by simp [hE₃])
  refine ((SrcRuns.of_rsa s1).seq hdisj hP (s2.seq hdisj hP ((SrcRuns.of_rsa s3).seq hdisj hP
    (SrcRuns.of_rsa s4)))).congr ?_ |>.mono (le_of_eq ?_)
  · congr 1
    refine SrcF.ext rfl rfl rfl rfl ?_ rfl rfl ?_
    · simp only [hE₃, Function.update_idem]
      rfl
    · simp only [hE₃, hE₂, hE₁, Function.update_idem]
  · simp only [oppDirectPCost, srcConjCost]
    ring

end Transforms

end

end IntegerMultBounds.MathlibTM2.Fast.Src
