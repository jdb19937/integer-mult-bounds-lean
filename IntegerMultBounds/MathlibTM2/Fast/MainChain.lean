module

public import IntegerMultBounds.MathlibTM2.Fast.MainSem
public import IntegerMultBounds.MathlibTM2.Fast.MainProg
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# The stages F3 to F10 of the fast multiplier on one register file

`mn_chain_runs`: from the register file the parameter distribution leaves (the source family a
file `E` between runs with records for three runs, the operand bits on `io .rx`, `io .ry`, the
unary parameters of the digit, rounding and output stages, every scratch register empty),
`mnChain fwdP oppP` runs to a file whose output-stage data register `out .dat` holds the words
`binSyms Wo c_i` of the rounded coefficients `c_i = rndCoeff b S p N_i.re` of the computed
opposite transform, every other output-stage register as it began, within the sum of the stage
bounds. The contract is `SrcRuns` on the layout `mnRg` of the stage registers, from stores
meeting the transforms' precondition `mnSynPre σ`.

**Register files.** `mnGlob F g` is the file with the source family `F` (a `SrcF`) and the
other stage registers `g`; `mn_upd_*` turn register updates and lifted source-transform contracts
into updates of `F` or `g`.

**Steps.** Each stage contract is lifted to the layout `mnRg`: the raw contracts of the digit and
rounding stages through `RsaRuns.of_raw` (`mn_runs_upd2`), the source transforms through
`SrcRuns.lift` along `MnR.src`, the transfers, clears and the pointwise product directly. The
file between the runs is a file between runs again (`SrcBase.next`, `SrcCrtBase.upd_str`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ResampA IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Mult.Pipeline
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.Schoenhage.Schedule (topN)
open Computability


attribute [local irreducible] mnT mnQ

noncomputable section

/-! ### Register files of the stage registers -/

section Glob

variable {A : ℕ}

/-- The file with source family `F` and the other stage registers `g`. -/
def mnGlob (F : SrcF 6 A) (g : MnR → List (Fin (A + 4))) : MnR → List (Fin (A + 4))
  | .src x => F.get x
  | .pm r => g (.pm r)
  | .io r => g (.io r)
  | .rnd r => g (.rnd r)
  | .out r => g (.out r)

@[simp] lemma mnGlob_src (F : SrcF 6 A) (g : MnR → List (Fin (A + 4))) (x : SrcR 6) :
    mnGlob F g (.src x) = F.get x := rfl
@[simp] lemma mnGlob_pm (F : SrcF 6 A) (g : MnR → List (Fin (A + 4))) (r : TblR pmNV) :
    mnGlob F g (.pm r) = g (.pm r) := rfl
@[simp] lemma mnGlob_io (F : SrcF 6 A) (g : MnR → List (Fin (A + 4))) (r : MnIO) :
    mnGlob F g (.io r) = g (.io r) := rfl
@[simp] lemma mnGlob_rnd (F : SrcF 6 A) (g : MnR → List (Fin (A + 4))) (r : RndReg) :
    mnGlob F g (.rnd r) = g (.rnd r) := rfl
@[simp] lemma mnGlob_out (F : SrcF 6 A) (g : MnR → List (Fin (A + 4))) (r : OReg) :
    mnGlob F g (.out r) = g (.out r) := rfl

/-- An update off the source family. -/
lemma mn_upd_g (F : SrcF 6 A) (g : MnR → List (Fin (A + 4))) {r : MnR} (hr : ∀ x, r ≠ .src x)
    (l : List (Fin (A + 4))) :
    Function.update (mnGlob F g) r l = mnGlob F (Function.update g r l) := by
  funext y
  cases y with
  | src x => simp [Function.update_of_ne (hr x).symm]
  | _ => simp [mnGlob, Function.update_apply]

lemma mn_upd_c (F : SrcF 6 A) (g : MnR → List (Fin (A + 4))) (r : CrtReg) (l : List (Fin (A + 4))) :
    Function.update (mnGlob F g) (.src (.c r)) l = mnGlob { F with c := Function.update F.c r l } g := by
  funext y
  cases y with
  | src z => cases z <;> simp [SrcF.get, Function.update_apply]
  | _ => simp [mnGlob]

lemma mn_upd_x (F : SrcF 6 A) (g : MnR → List (Fin (A + 4))) (r : SrcX) (l : List (Fin (A + 4))) :
    Function.update (mnGlob F g) (.src (.x r)) l = mnGlob { F with x := Function.update F.x r l } g := by
  funext y
  cases y with
  | src z => cases z <;> simp [SrcF.get, Function.update_apply]
  | _ => simp [mnGlob]

lemma mn_upd_v (F : SrcF 6 A) (g : MnR → List (Fin (A + 4))) (r : CvR) (l : List (Fin (A + 4))) :
    Function.update (mnGlob F g) (.src (.v r)) l = mnGlob { F with v := Function.update F.v r l } g := by
  funext y
  cases y with
  | src z => cases z <;> simp [SrcF.get, Function.update_apply]
  | _ => simp [mnGlob]

lemma mn_src_inj : Function.Injective (MnR.src : SrcR 6 → MnR) := fun _ _ h => MnR.src.inj h

/-- A lifted source-family contract replaces the source family. -/
lemma mn_extend_src (F F' : SrcF 6 A) (g : MnR → List (Fin (A + 4))) :
    Function.extend MnR.src F'.get (mnGlob F g) = mnGlob F' g := by
  funext y
  cases y with
  | src x => exact mn_src_inj.extend_apply _ _ x
  | _ => exact Function.extend_apply' _ _ _ (by rintro ⟨x, hx⟩; cases hx)

end Glob

/-! ### Contracts on the stage layout -/

section Runs

variable {K : ℕ} {body : MnProc → MnPr (prime + K)}
  {Pre : Stacks mnT (prime + K) → Prop}

lemma mn_hdisj : ∀ r j, mnRg r ≠ mnι j := mnRg_ne_ι

/-- `mnSynPre` survives every change confined to the stage layout. -/
lemma mn_framed (σ : LReg SXReg → List (Fin (prime + K + 4))) :
    SrcFramed mnRg (mnSynPre (A := prime + K) σ) := by
  intro S S' ⟨hL, hι, hl⟩ ⟨_, _, hL', hk⟩
  refine ⟨fun y => by rw [hL']; exact hL y, fun j => ?_, fun x => ?_⟩
  · rw [hk _ (fun r => mnRg_ne_ι r j)]; exact hι j
  · rw [hk _ (fun r => mnRg_ne_lay r x)]; exact hl x

/-- A raw contract changing two stage registers. -/
lemma mn_runs_upd2 {p : MnPr (prime + K)} {ρ : MnR → List (Fin (prime + K + 4))} {a b : MnR}
    {la lb : List (Fin (prime + K + 4))} {c : ℕ}
    (h : ∀ (v : HS mnT mnQ (prime + K) Unit) (S : Stacks mnT (prime + K)),
      rsaClean mnι S → rsaHolds mnRg S ρ → ∃ v', v'.user = v.user ∧
        Exec body p (mk v S) c (mk v' { S with
          R := Function.update (Function.update S.R (mnRg a) la) (mnRg b) lb })) :
    RsaRuns body mnRg mnι p ρ (Function.update (Function.update ρ a la) b lb) c := by
  refine RsaRuns.of_raw fun v S hc hS => ?_
  obtain ⟨v', hu, he⟩ := h v S hc hS
  refine ⟨v', _, c, hu, le_rfl, he, ?_, fun k hk => ?_⟩
  · exact rsa_holds_upd mnRg_inj (rsa_holds_upd mnRg_inj hS a la) b lb
  · rw [rsa_upd_off _ _ _ hk, rsa_upd_off _ _ _ hk]

/-- A forward transfer through the spare `io .sp`. -/
lemma mn_mv_runs {a b : MnR} (hab : a ≠ b) (ha : a ≠ .io .sp) (hb : b ≠ .io .sp)
    (ρ : MnR → List (Fin (prime + K + 4))) (ht : ρ (.io .sp) = []) :
    SrcRuns body mnRg mnι Pre (mnMv a b) ρ
      (Function.update (Function.update ρ a []) b (ρ a ++ ρ b)) (4 * (ρ a).length + 4) :=
  SrcRuns.of_rsa (src_mv_runs mnRg_inj mn_hdisj hab ha hb ρ ht)

end Runs

/-! ### The stages on the stage layout -/

section Stages

variable {K : ℕ} {body : MnProc → MnPr (prime + K)}
  {Pre : Stacks mnT (prime + K) → Prop}

lemma mn_digit_regs (src : MnIO) (hsrc : src = .rx ∨ src = .ry) :
    [mnIo src, mnIo .dbn, mnIo .dpn, mnIo .dwn, mnIo .dsn, mnIo .tpl, mnIo .tmp, mnIo .stmp,
      mnIo .acc, mnSrc (.c .str)].Nodup := by
  have h : [MnR.io src, .io .dbn, .io .dpn, .io .dwn, .io .dsn, .io .tpl, .io .tmp, .io .stmp,
      .io .acc, .src (.c .str)].Nodup := by
    rcases hsrc with rfl | rfl <;> simp
  exact h.map mnRg_inj

/-- **F3 on the stage layout.** -/
lemma mn_digits_runs (src : MnIO) (hsrc : src = .rx ∨ src = .ry) {b' p' w' S' : ℕ}
    (hb : 1 ≤ b') (hbp : b' + 2 ≤ p') (hpw : p' ≤ w') (x : ℕ) (xs : List Bool)
    (hxs : binaryValue xs = x) (hS : (digitsOf b' xs).length ≤ S') (F : SrcF 6 (prime + K))
    (g : MnR → List (Fin (prime + K + 4)))
    (hx : g (.io src) = (encodingNatBool.encode x).map bitSymbol)
    (hbn : (g (.io .dbn)).length = b') (hpn : (g (.io .dpn)).length = p')
    (hwn : (g (.io .dwn)).length = w') (hsn : (g (.io .dsn)).length = S')
    (htpl : g (.io .tpl) = []) (htmp : g (.io .tmp) = []) (hstmp : g (.io .stmp) = [])
    (hacc : g (.io .acc) = []) :
    SrcRuns body mnRg mnι Pre (mnDigits src) (mnGlob F g)
      (mnGlob
        { F with
          c := Function.update F.c .str (digitStream (prime + K) b' p' w' S' xs ++ F.c .str) }
        (Function.update g (.io src) [])) (digitCost b' p' w' S') := by
  have h := mn_runs_upd2 (body := body) (ρ := mnGlob F g) (a := .io src) (b := .src (.c .str))
    (la := []) (lb := digitStream (prime + K) b' p' w' S' xs ++ F.c .str)
    (c := digitCost b' p' w' S') fun v S _ hH => by
      have e := digitRecords_exec (body := body) _ _ _ _ _ _ _ _ _ _ (mn_digit_regs src hsrc) hb
        hbp hpw x xs hxs hS v S (by rw [hH (.io src)]; exact hx) (by rw [hH (.io .dbn)]; exact hbn)
        (by rw [hH (.io .dpn)]; exact hpn) (by rw [hH (.io .dwn)]; exact hwn)
        (by rw [hH (.io .dsn)]; exact hsn) (by rw [hH (.io .tpl)]; exact htpl)
        (by rw [hH (.io .tmp)]; exact htmp) (by rw [hH (.io .stmp)]; exact hstmp)
        (by rw [hH (.io .acc)]; exact hacc)
      rw [show S.R (mnSrc (.c .str)) = F.c .str from hH (.src (.c .str))] at e
      exact e
  refine (SrcRuns.of_rsa h).congr ?_
  rw [mn_upd_g F g (by intro x h; cases h), mn_upd_c]

/-- **A source transform run on the stage layout.** -/
lemma mn_srcP_runs (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : MnPr (prime + K)} {w W cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (mnSrc (.v .io)) Pre w (p n) (ℓ n) (cvAx (t n)) π cF)
    (hO : SynOppSpec body oppP (mnSrc (.v .io)) Pre w (p n) (ℓ n) (cvAx (t n)) π cO)
    (hπ : ∀ m < cvM (cvAx (t n)), π m < cvM (cvAx (t n))) (hP : SrcFramed mnRg Pre)
    (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (hWB : 9 * p n + 2 ≤ w ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX 6) (prime + K)} {σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))} (E : SrcF 6 (prime + K))
    (hE : SrcBase mnM E n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB)
    (hC : SrcCrtBase E.c E.cb n w) (hln : E.a .ln = [])
    (u : ZMod (∏ i, s n i) → ℂ) (hu : ‖u‖ ≤ 1 / 2) (huf : ∀ k, IsFixed (p n) (u k))
    (hstr : E.c .str = cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) u))
    (g : MnR → List (Fin (prime + K + 4))) :
    SrcRuns body mnRg mnι Pre (srcDirectP mnM fwdP oppP) (mnGlob E g)
      (mnGlob { E with
        a := (rsaWith (preCfgA V₀ crtHd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
        b := rsbWith (bandCfgB σ₀ crtHd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
        c := Function.update E.c .str [],
        x := (Function.update E.x .sb
          (cstream (prime + K) w (srcPad (p n) (s n) (t n) (srcMap n u)) ++ E.x .sb)) } g)
      (srcDirectPCost mnM n w W cF cO (srcHd0 hbig) V₀ σ₀ restA restB) := by
  have h : SrcRuns body (fun x => mnRg (MnR.src x)) mnι Pre (srcDirectP mnM fwdP oppP) E.get _ _ :=
    srcDirectP_runs (body := body) mnM hA hbig hsmall hEs hF hO (fun _ h => h) (fun _ h => h) hπ
      hP.comp hw hwW hWA hWB hWs hWk E hE hC hln u hu huf hstr
  have h' := SrcRuns.lift mnRg_inj mn_src_inj h (mnGlob E g) (fun _ => rfl)
  rwa [mn_extend_src] at h'

/-- **The opposite transform on the stage layout.** -/
lemma mn_oppP_runs (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : MnPr (prime + K)} {w W cF cO : ℕ} {π : ℕ → ℕ}
    (hF : SynFwdSpec body fwdP (mnSrc (.v .io)) Pre w (p n) (ℓ n) (cvAx (t n)) π cF)
    (hO : SynOppSpec body oppP (mnSrc (.v .io)) Pre w (p n) (ℓ n) (cvAx (t n)) π cO)
    (hπ : ∀ m < cvM (cvAx (t n)), π m < cvM (cvAx (t n))) (hP : SrcFramed mnRg Pre)
    (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (hWB : 9 * p n + 2 ≤ w ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX 6) (prime + K)} {σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))} (E : SrcF 6 (prime + K))
    (hE : SrcBase mnM E n w W (srcHd0 hbig) V₀ σ₀ restA restB axsA axsB)
    (hC : SrcCrtBase E.c E.cb n w) (hln : E.a .ln = []) (hstr : E.c .str = [])
    (y : ((i : Fin (d n)) → ZMod (s n i)) → ℂ) (hy : ‖y‖ ≤ 1 / 2)
    (hyf : ∀ k, IsFixed (p n) (y k))
    (hsb : E.x .sb = cstream (prime + K) w (srcPad (p n) (s n) (t n) y))
    (g : MnR → List (Fin (prime + K + 4))) :
    SrcRuns body mnRg mnι Pre (oppDirectP mnM fwdP oppP) (mnGlob E g)
      (mnGlob { E with
        a := (rsaWith (preCfgA V₀ crtHd n w W (srcHd0 hbig) restA (d n - 1)) [] axsA []).get,
        b := rsbWith (bandCfgB σ₀ crtHd n w W (srcHd0 hbig) restB (d n - 1)) [] axsB [],
        c := Function.update E.c .str
          (cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) (oppMap n y))),
        x := Function.update E.x .sb [] } g)
      (oppDirectPCost mnM n w W cF cO (srcHd0 hbig) V₀ σ₀ restA restB) := by
  have h : SrcRuns body (fun x => mnRg (MnR.src x)) mnι Pre (oppDirectP mnM fwdP oppP) E.get _ _ :=
    srcDirectOpp_runs (body := body) mnM hA hbig hsmall hEs hF hO (fun _ h => h) (fun _ h => h) hπ
      hP.comp hw hwW hWA hWB hWs hWk E hE hC hln hstr y hy hyf hsb
  have h' := SrcRuns.lift mnRg_inj mn_src_inj h (mnGlob E g) (fun _ => rfl)
  rwa [mn_extend_src] at h'

/-- **F7 on the stage layout.** -/
lemma mn_point_runs (hA : 96 ≤ prime + K) {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w) {d : ℕ}
    (t : Fin d → ℕ) [∀ i, NeZero (t i)] (f h : ((i : Fin d) → ZMod (t i)) → ℂ)
    (hf : ∀ x, IsFixed q (f (cstCast t x))) (hh : ∀ x, IsFixed q (h (cstCast t x)))
    (hfw : ∀ x, Fits w (numer q (f (cstCast t x))))
    (hhw : ∀ x, Fits w (numer q (h (cstCast t x))))
    (ρ : MnR → List (Fin (prime + K + 4))) (hr : Ready (fun x => ρ (.src (.v (.cm x)))) w q)
    (hX : ρ (.src (.v (.cm .xs))) = cstream (prime + K) w (cstNumBox q t f))
    (hY : ρ (.src (.v (.cm .ys))) = cstream (prime + K) w (cstNumBox q t h))
    (hxsv : ρ (.src (.v (.cm .xsv))) = []) (hysv : ρ (.src (.v (.cm .ysv))) = [])
    (hacc : ρ (.src (.v (.cm .acc))) = []) :
    SrcRuns body mnRg mnι Pre mnPoint ρ
      (Function.update ρ (.src (.v (.cm .out)))
        (cstream (prime + K) w (cstNumBox q t (rdV q (f * h))) ++ ρ (.src (.v (.cm .out)))))
      ((∏ i, t i) * (cmulCost w + 6 * w + 2) + 8) :=
  SrcRuns.of_rsa (cst_point_runs (body := body) (c := fun x => MnR.src (.v (.cm x))) mnRg_inj
    mn_hdisj mnι_inj mnT_ge_64 mnQ_ss hA (fun _ _ e => CvR.cm.inj (SrcR.v.inj (MnR.src.inj e)))
    hw hq t f h hf hh hfw hhw ρ hr hX hY hxsv hysv hacc)

/-- **A clear on the stage layout.** -/
lemma mn_clear_runs (a : MnR) (ρ : MnR → List (Fin (prime + K + 4))) :
    SrcRuns body mnRg mnι Pre (uclear (mnRg a)) ρ (Function.update ρ a [])
      (2 * (ρ a).length + 2) :=
  SrcRuns.of_rsa (rsa_uclear mnRg_inj a ρ)

/-- **F10 on the stage layout.** -/
lemma mn_round_runs (hA : 4 ≤ prime + K) {w m b' p' W S' : ℕ} (hw : 1 ≤ w) (hwm : w ≤ m) (hSm : S' * S' < 2 ^ m)
    (N : Fin S' → GaussianInt) (hN : ∀ i, |(N i).re| < 2 ^ (w - 1))
    (ρ : MnR → List (Fin (prime + K + 4)))
    (hsrc : ρ (.rnd .src) = (List.ofFn fun i => red w (N i)).flatMap (coeffSyms (prime + K) w))
    (hwn : (ρ (.rnd .wn)).length = w) (hmn : (ρ (.rnd .mn)).length = m)
    (hnn : (ρ (.rnd .nn)).length = topN m) (hsq : ρ (.rnd .sq) = binSyms m (S' * S'))
    (hbn : (ρ (.rnd .bn)).length = b') (hpn : (ρ (.rnd .pn)).length = p')
    (hwo : (ρ (.rnd .wo)).length = W) (htm : ρ (.rnd .tm) = []) (hu1 : ρ (.rnd .u1) = [])
    (hsg : ρ (.rnd .sg) = []) (hxa : ρ (.rnd .xa) = []) (hxc : ρ (.rnd .xc) = [])
    (hcy : ρ (.rnd .cy) = []) (hacc : ρ (.rnd .acc) = []) :
    SrcRuns body mnRg mnι Pre mnRound ρ
      (Function.update (Function.update ρ (.rnd .src) []) (.rnd .dst)
        ((List.ofFn fun i => rndCoeff b' S' p' (N i).re).flatMap (binSyms W) ++ ρ (.rnd .dst)))
      (roundStageCost m w b' p' W S') := by
  refine SrcRuns.of_rsa (RsaRuns.of_raw fun v S hc hS => ?_)
  obtain ⟨v', k, hu, hk, he⟩ := roundStage_exec (body := body) (rg := mnRnd) (w := w) (m := m)
    (b := b') (p := p') (W := W) (S := S')
    (fun _ _ e => MnR.rnd.inj (mnRg_inj e)) mnι_inj (fun r j => mnRg_ne_ι _ j) mnT_ge_64 mnQ_ss
    hA hw hwm hSm N hN v S (fun j => hc.1 _) hc.2
    (by rw [hS (.rnd .src)]; exact hsrc) (by rw [hS (.rnd .wn)]; exact hwn)
    (by rw [hS (.rnd .mn)]; exact hmn) (by rw [hS (.rnd .nn)]; exact hnn)
    (by rw [hS (.rnd .sq)]; exact hsq) (by rw [hS (.rnd .bn)]; exact hbn)
    (by rw [hS (.rnd .pn)]; exact hpn) (by rw [hS (.rnd .wo)]; exact hwo)
    (by rw [hS (.rnd .tm)]; exact htm) (by rw [hS (.rnd .u1)]; exact hu1)
    (by rw [hS (.rnd .sg)]; exact hsg) (by rw [hS (.rnd .xa)]; exact hxa)
    (by rw [hS (.rnd .xc)]; exact hxc) (by rw [hS (.rnd .cy)]; exact hcy)
    (by rw [hS (.rnd .acc)]; exact hacc)
  refine ⟨v', _, k, hu, hk, he, ?_, fun k hk => ?_⟩
  · have := rsa_holds_upd mnRg_inj (rsa_holds_upd mnRg_inj hS (.rnd .src) [])
      (.rnd .dst) ((List.ofFn fun i => rndCoeff b' S' p' (N i).re).flatMap (binSyms W) ++
        ρ (.rnd .dst))
    intro r
    rw [← this r, show S.R (mnRnd .dst) = ρ (.rnd .dst) from hS (.rnd .dst)]
  · rw [rsa_upd_off _ _ _ hk, rsa_upd_off _ _ _ hk]

end Stages

/-! ### The transfers, clears and stages on `mnGlob` files -/

section GlobSteps

variable {K : ℕ} {body : MnProc → MnPr (prime + K)}
  {Pre : Stacks mnT (prime + K) → Prop}

lemma mn_mv_sb_hx (F : SrcF 6 (prime + K)) (g : MnR → List (Fin (prime + K + 4)))
    (hsp : g (.io .sp) = []) :
    SrcRuns body mnRg mnι Pre (mnMv (.src (.x .sb)) (.io .hx)) (mnGlob F g)
      (mnGlob { F with x := Function.update F.x .sb [] }
        (Function.update g (.io .hx) (F.x .sb ++ g (.io .hx)))) (4 * (F.x .sb).length + 4) := by
  have h := mn_mv_runs (body := body) (Pre := Pre) (a := .src (.x .sb)) (b := .io .hx)
    (by simp) (by simp) (by simp) (mnGlob F g) hsp
  refine h.congr ?_
  simp only [mnGlob_src, mnGlob_io, SrcF.get_x]
  rw [mn_upd_x, mn_upd_g _ _ (by intro x h; cases h)]

lemma mn_mv_hx_xs (F : SrcF 6 (prime + K)) (g : MnR → List (Fin (prime + K + 4)))
    (hsp : g (.io .sp) = []) :
    SrcRuns body mnRg mnι Pre (mnMv (.io .hx) (.src (.v (.cm .xs)))) (mnGlob F g)
      (mnGlob { F with v := Function.update F.v (.cm .xs) (g (.io .hx) ++ F.v (.cm .xs)) }
        (Function.update g (.io .hx) [])) (4 * (g (.io .hx)).length + 4) := by
  have h := mn_mv_runs (body := body) (Pre := Pre) (a := .io .hx) (b := .src (.v (.cm .xs)))
    (by simp) (by simp) (by simp) (mnGlob F g) hsp
  refine h.congr ?_
  simp only [mnGlob_src, mnGlob_io, SrcF.get_v]
  rw [mn_upd_g _ _ (by intro x h; cases h), mn_upd_v]

lemma mn_mv_sb_ys (F : SrcF 6 (prime + K)) (g : MnR → List (Fin (prime + K + 4)))
    (hsp : g (.io .sp) = []) :
    SrcRuns body mnRg mnι Pre (mnMv (.src (.x .sb)) (.src (.v (.cm .ys)))) (mnGlob F g)
      (mnGlob { F with
          x := Function.update F.x .sb []
          v := Function.update F.v (.cm .ys) (F.x .sb ++ F.v (.cm .ys)) } g)
      (4 * (F.x .sb).length + 4) := by
  have h := mn_mv_runs (body := body) (Pre := Pre) (a := .src (.x .sb)) (b := .src (.v (.cm .ys)))
    (by simp) (by simp) (by simp) (mnGlob F g) hsp
  refine h.congr ?_
  simp only [mnGlob_src, SrcF.get_x, SrcF.get_v]
  rw [mn_upd_x, mn_upd_v]

lemma mn_mv_out_sb (F : SrcF 6 (prime + K)) (g : MnR → List (Fin (prime + K + 4)))
    (hsp : g (.io .sp) = []) :
    SrcRuns body mnRg mnι Pre (mnMv (.src (.v (.cm .out))) (.src (.x .sb))) (mnGlob F g)
      (mnGlob { F with
          v := Function.update F.v (.cm .out) []
          x := Function.update F.x .sb (F.v (.cm .out) ++ F.x .sb) } g)
      (4 * (F.v (.cm .out)).length + 4) := by
  have h := mn_mv_runs (body := body) (Pre := Pre) (a := .src (.v (.cm .out))) (b := .src (.x .sb))
    (by simp) (by simp) (by simp) (mnGlob F g) hsp
  refine h.congr ?_
  simp only [mnGlob_src, SrcF.get_x, SrcF.get_v]
  rw [mn_upd_v, mn_upd_x]

lemma mn_mv_str_rnd (F : SrcF 6 (prime + K)) (g : MnR → List (Fin (prime + K + 4)))
    (hsp : g (.io .sp) = []) :
    SrcRuns body mnRg mnι Pre (mnMv (.src (.c .str)) (.rnd .src)) (mnGlob F g)
      (mnGlob { F with c := Function.update F.c .str [] }
        (Function.update g (.rnd .src) (F.c .str ++ g (.rnd .src)))) (4 * (F.c .str).length + 4) := by
  have h := mn_mv_runs (body := body) (Pre := Pre) (a := .src (.c .str)) (b := .rnd .src)
    (by simp) (by simp) (by simp) (mnGlob F g) hsp
  refine h.congr ?_
  simp only [mnGlob_src, mnGlob_rnd, SrcF.get_c]
  rw [mn_upd_c, mn_upd_g _ _ (by intro x h; cases h)]

lemma mn_mv_dst_dat (F : SrcF 6 (prime + K)) (g : MnR → List (Fin (prime + K + 4)))
    (hsp : g (.io .sp) = []) :
    SrcRuns body mnRg mnι Pre (mnMv (.rnd .dst) (.out .dat)) (mnGlob F g)
      (mnGlob F (Function.update (Function.update g (.rnd .dst) []) (.out .dat)
        (g (.rnd .dst) ++ g (.out .dat)))) (4 * (g (.rnd .dst)).length + 4) := by
  have h := mn_mv_runs (body := body) (Pre := Pre) (a := .rnd .dst) (b := .out .dat)
    (by simp) (by simp) (by simp) (mnGlob F g) hsp
  refine h.congr ?_
  simp only [mnGlob_rnd, mnGlob_out]
  rw [mn_upd_g _ _ (by intro x h; cases h), mn_upd_g _ _ (by intro x h; cases h)]

lemma mn_clear_cm (r : CR) (F : SrcF 6 (prime + K)) (g : MnR → List (Fin (prime + K + 4))) :
    SrcRuns body mnRg mnι Pre (uclear (mnCm r)) (mnGlob F g)
      (mnGlob { F with v := Function.update F.v (.cm r) [] } g)
      (2 * (F.v (.cm r)).length + 2) := by
  have h := mn_clear_runs (body := body) (Pre := Pre) (.src (.v (.cm r))) (mnGlob F g)
  refine h.congr ?_
  rw [mn_upd_v]

end GlobSteps

/-! ### The chain -/

section Chain

variable {K : ℕ} {body : MnProc → MnPr (prime + K)}

lemma mn_length_words (W : ℕ) (l : List ℕ) :
    (l.flatMap (binSyms (A := prime + K) W)).length = l.length * W := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, length_binSyms, ih]; ring

/-- The words of the rounded coefficients at `n` for the operands `x`, `y`. -/
def mnWords (K n x y : ℕ) : List (Fin (prime + K + 4)) :=
  (List.ofFn fun i : Fin (∏ i, s n i) => rndCoeff (b n) (∏ i, s n i) (p n)
    (numer (p n) (oppMap n (mnY n x y) ((i : ℕ) : ZMod (∏ i, s n i)))).re).flatMap
      (binSyms (mnWo n))

/-- The step bound of the chain at `n`, coefficient width `w`, given the bounds of the three
source-transform runs. -/
def mnChainCost (n w runs : ℕ) : ℕ :=
  2 * digitCost (b n) (p n) w (S n) + runs + mnGlue n w +
    ((4 * (S n * w) + 4) + roundStageCost (mnMw n w) w (b n) (p n) (mnWo n) (S n) +
      (4 * (S n * mnWo n) + 4))

set_option maxHeartbeats 4000000 in
/-- **F3 to F10 on one register file.** -/
theorem mn_chain_runs (hA : 96 ≤ prime + K) {n : ℕ} (hbig : Big n)
    (hsmall : 2 * d n * p n ^ 2 ≤ Sizes.T n * logT n)
    (hEs : 9 * (2 : ℝ) ^ gamma n * Sizes.T n * logT n ≤ 2 ^ p n / 100)
    {fwdP oppP : MnPr (prime + K)} {w W cF cO : ℕ} {π : ℕ → ℕ}
    {σ : LReg SXReg → List (Fin (prime + K + 4))}
    (hF : SynFwdSpec body fwdP (mnSrc (.v .io)) (mnSynPre σ) w (p n) (ℓ n) (cvAx (t n)) π cF)
    (hO : SynOppSpec body oppP (mnSrc (.v .io)) (mnSynPre σ) w (p n) (ℓ n) (cvAx (t n)) π cO)
    (hπ : ∀ m < cvM (cvAx (t n)), π m < cvM (cvAx (t n)))
    (hw : p n + Chirp.chirpGuard (d n) + 3 ≤ w) (hwW : w < W)
    (hWA : ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) * (windowA (p n) (alpha n) + 1)) ^ 2 *
      2 ^ (13 * p n + 8) < 2 ^ W)
    (hWB : 9 * p n + 2 ≤ w ∧ ∀ i : Fin (d n), alpha n ^ 2 * ((s n i + t n i) *
      (8 * FastB0.fastWindow (p n) (alpha n) + 1)) ^ 2 * 2 ^ (65 * p n + 8) < 2 ^ W)
    (hWs : ∀ k, s n k * t n k * t n k < 2 ^ W)
    (hWk : ∀ k, 8 * (p n + Chirp.chirpGuard (d n)) + Nat.size (t n k) + 80 ≤ W)
    {V₀ : RsaV (RsaX 6) (prime + K)} {σ₀ : RsbR ⊕ RsbX 6 → List (Fin (prime + K + 4))}
    {restA restB axsA axsB : List (Fin (prime + K + 4))} (E : SrcF 6 (prime + K))
    (hE : SrcBase mnM E n w W (srcHd0 hbig) V₀ σ₀
      (preRecsA n W (srcHd0 hbig) 0 ++ (preRecsA n W (srcHd0 hbig) 0 ++ restA))
      (preRecsB n W (srcHd0 hbig) 0 ++ (preRecsB n W (srcHd0 hbig) 0 ++ restB)) axsA axsB)
    (hC : SrcCrtBase E.c E.cb n w) (hln : E.a .ln = []) (hstr : E.c .str = [])
    (hsb : E.x .sb = [])
    (g : MnR → List (Fin (prime + K + 4))) (x y : ℕ) (hsx : Nat.size x ≤ n)
    (hsy : Nat.size y ≤ n)
    (hrx : g (.io .rx) = (encodingNatBool.encode x).map bitSymbol)
    (hry : g (.io .ry) = (encodingNatBool.encode y).map bitSymbol)
    (hdbn : (g (.io .dbn)).length = b n) (hdpn : (g (.io .dpn)).length = p n)
    (hdwn : (g (.io .dwn)).length = w) (hdsn : (g (.io .dsn)).length = S n)
    (htpl : g (.io .tpl) = []) (htmp : g (.io .tmp) = []) (hstmp : g (.io .stmp) = [])
    (hacc : g (.io .acc) = []) (hhx : g (.io .hx) = []) (hsp : g (.io .sp) = [])
    (hrsrc : g (.rnd .src) = []) (hrdst : g (.rnd .dst) = [])
    (hrwn : (g (.rnd .wn)).length = w) (hrmn : (g (.rnd .mn)).length = mnMw n w)
    (hrnn : (g (.rnd .nn)).length = topN (mnMw n w))
    (hrsq : g (.rnd .sq) = binSyms (mnMw n w) (S n * S n))
    (hrbn : (g (.rnd .bn)).length = b n) (hrpn : (g (.rnd .pn)).length = p n)
    (hrwo : (g (.rnd .wo)).length = mnWo n) (hrtm : g (.rnd .tm) = [])
    (hru1 : g (.rnd .u1) = []) (hrsg : g (.rnd .sg) = []) (hrxa : g (.rnd .xa) = [])
    (hrxc : g (.rnd .xc) = []) (hrcy : g (.rnd .cy) = []) (hracc : g (.rnd .acc) = [])
    (hodat : g (.out .dat) = []) :
    ∃ (F' : SrcF 6 (prime + K)) (g' : MnR → List (Fin (prime + K + 4))),
      SrcRuns body mnRg mnι (mnSynPre σ) (mnChain fwdP oppP) (mnGlob E g) (mnGlob F' g')
        (mnChainCost n w
          (srcDirectPCost mnM n w W cF cO (srcHd0 hbig) V₀ σ₀
              (preRecsA n W (srcHd0 hbig) 0 ++ (preRecsA n W (srcHd0 hbig) 0 ++ restA))
              (preRecsB n W (srcHd0 hbig) 0 ++ (preRecsB n W (srcHd0 hbig) 0 ++ restB)) +
            srcDirectPCost mnM n w W cF cO (srcHd0 hbig)
              (preCfgA V₀ crtHd n w W (srcHd0 hbig)
                (preRecsA n W (srcHd0 hbig) 0 ++ (preRecsA n W (srcHd0 hbig) 0 ++ restA)) (d n - 1))
              (bandCfgB σ₀ crtHd n w W (srcHd0 hbig)
                (preRecsB n W (srcHd0 hbig) 0 ++ (preRecsB n W (srcHd0 hbig) 0 ++ restB)) (d n - 1))
              (preRecsA n W (srcHd0 hbig) 0 ++ restA) (preRecsB n W (srcHd0 hbig) 0 ++ restB) +
            oppDirectPCost mnM n w W cF cO (srcHd0 hbig)
              (preCfgA (preCfgA V₀ crtHd n w W (srcHd0 hbig)
                (preRecsA n W (srcHd0 hbig) 0 ++ (preRecsA n W (srcHd0 hbig) 0 ++ restA)) (d n - 1))
                crtHd n w W (srcHd0 hbig) (preRecsA n W (srcHd0 hbig) 0 ++ restA) (d n - 1))
              (bandCfgB (bandCfgB σ₀ crtHd n w W (srcHd0 hbig)
                (preRecsB n W (srcHd0 hbig) 0 ++ (preRecsB n W (srcHd0 hbig) 0 ++ restB)) (d n - 1))
                crtHd n w W (srcHd0 hbig) (preRecsB n W (srcHd0 hbig) 0 ++ restB) (d n - 1))
              restA restB)) ∧
      g' (.out .dat) = mnWords K n x y ∧ ∀ r, r ≠ .dat → g' (.out r) = g (.out r) := by
  set hd0 := srcHd0 hbig with hhd0
  have hP : SrcFramed mnRg (mnSynPre (A := prime + K) σ) := mn_framed σ
  have hb1 : 1 ≤ b n := one_le_b hbig.1
  have hpb : b n + 2 ≤ p n := by unfold p; omega
  have hpw : p n ≤ w := by omega
  have hw1 : 1 ≤ w := by omega
  have hA4 : 4 ≤ prime + K := by omega
  have hS0 : NeZero (∏ i, s n i) := ⟨by
    have := hbig.T_lt_two_S; have := hbig.S_lt_T; unfold Sizes.S at *; omega⟩
  -- the operands
  set ux := mnU n x with hux
  set uy := mnU n y with huy
  have hux1 : ‖ux‖ ≤ 1 / 2 := mn_scaledDigits_norm (one_le_b hbig.1) _
  have huy1 : ‖uy‖ ≤ 1 / 2 := mn_scaledDigits_norm (one_le_b hbig.1) _
  have huxf : ∀ k, IsFixed (p n) (ux k) := mn_scaledDigits_fixed hpb _
  have huyf : ∀ k, IsFixed (p n) (uy k) := mn_scaledDigits_fixed hpb _
  have hFx := mn_srcMap_norm hbig hsmall hEs hux1
  have hFy := mn_srcMap_norm hbig hsmall hEs huy1
  set Y := mnY n x y with hY
  have hY1 : ‖Y‖ ≤ 1 / 2 := mn_rdV_norm _ hFx hFy
  have hYf : ∀ k, IsFixed (p n) (Y k) := fun k => isFixed_rhoC _ _
  have hOY := mn_oppMap_norm hbig hsmall hEs hY1
  set BX := cstream (prime + K) w (srcPad (p n) (s n) (t n) (srcMap n ux)) with hBX
  set BY := cstream (prime + K) w (srcPad (p n) (s n) (t n) (srcMap n uy)) with hBY
  set PR := cstream (prime + K) w (cstNumBox (p n) (t n)
    (rdV (p n) (mnPad (s n) (t n) (srcMap n ux) * mnPad (s n) (t n) (srcMap n uy)))) with hPR
  have hPR : PR = cstream (prime + K) w (srcPad (p n) (s n) (t n) Y) := by
    rw [hPR, mn_rdV_pad, ← mn_srcPad_eq]
  set CO := cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) (oppMap n Y)) with hCO
  have hTw : BX.length = (∏ i, t n i) * w := by rw [hBX, length_cstream, src_length_pad]
  have hTwY : BY.length = (∏ i, t n i) * w := by rw [hBY, length_cstream, src_length_pad]
  have eS : S n = ∏ i, s n i := rfl
  -- 1. the digits of `x`
  have hxs : binaryValue (bitsMSB n x) = x := binaryValue_bitsMSB_of_size hsx
  have s1 := mn_digits_runs (body := body) (Pre := mnSynPre σ) .rx (Or.inl rfl) hb1 hpb hpw x
    (bitsMSB n x) hxs (mn_digits_len hbig x) E g hrx hdbn hdpn hdwn hdsn htpl htmp hstmp hacc
  rw [eS, mn_digitStream_eq hpb, hstr, List.append_nil] at s1
  obtain ⟨F₁, hF₁⟩ : ∃ F : SrcF 6 (prime + K), F =
      { E with
        c := Function.update E.c .str
          (cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) ux)) } := ⟨_, rfl⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g' : MnR → List (Fin (prime + K + 4)), g' = Function.update g (.io .rx) [] :=
    ⟨_, rfl⟩
  rw [← hF₁, ← hg₁] at s1
  -- 2. the source transform of `x`
  have hE₁ : SrcBase mnM F₁ n w W hd0 V₀ σ₀
      (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA))
      (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) axsA axsB := by
    subst hF₁; exact hE.of_eq (fun _ _ => rfl) rfl rfl rfl rfl (fun _ _ => rfl)
  have hC₁ : SrcCrtBase F₁.c F₁.cb n w := by subst hF₁; exact hC.upd_str _
  have s2 := mn_srcP_runs (body := body) hA hbig hsmall hEs hF hO hπ hP hw hwW hWA hWB hWs hWk F₁
    hE₁ hC₁ (by subst hF₁; exact hln) ux hux1 huxf (by subst hF₁; simp) g₁
  obtain ⟨F₂, hF₂⟩ : ∃ F : SrcF 6 (prime + K), F =
      { F₁ with
        a := (rsaWith (preCfgA V₀ crtHd n w W hd0
          (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1)) [] axsA []).get
        b := rsbWith (bandCfgB σ₀ crtHd n w W hd0
          (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1)) [] axsB []
        c := Function.update F₁.c .str []
        x := Function.update F₁.x .sb (BX ++ F₁.x .sb) } := ⟨_, rfl⟩
  replace s2 : SrcRuns body mnRg mnι (mnSynPre σ) (srcDirectP mnM fwdP oppP) (mnGlob F₁ g₁)
      (mnGlob F₂ g₁) (srcDirectPCost mnM n w W cF cO hd0 V₀ σ₀
        (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA))
        (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB))) := by subst hF₂; exact s2
  have hF₂sb : F₂.x .sb = BX := by subst hF₂ hF₁; simp [hsb]
  -- 3. park the first transform
  have s3 := mn_mv_sb_hx (body := body) (Pre := mnSynPre σ) F₂ g₁ (by subst hg₁; simp [hsp])
  obtain ⟨F₃, hF₃⟩ : ∃ F : SrcF 6 (prime + K), F = { F₂ with x := Function.update F₂.x .sb [] } :=
    ⟨_, rfl⟩
  obtain ⟨g₃, hg₃⟩ : ∃ g' : MnR → List (Fin (prime + K + 4)),
      g' = Function.update g₁ (.io .hx) BX := ⟨_, rfl⟩
  replace s3 : SrcRuns body mnRg mnι (mnSynPre σ) (mnMv (.src (.x .sb)) (.io .hx))
      (mnGlob F₂ g₁) (mnGlob F₃ g₃) (4 * ((∏ i, t n i) * w) + 4) := by
    rw [hF₂sb, hTw, show g₁ (.io .hx) = [] by subst hg₁; simp [hhx], List.append_nil] at s3
    rw [hF₃, hg₃]; exact s3
  -- 4. the digits of `y`
  have hys : binaryValue (bitsMSB n y) = y := binaryValue_bitsMSB_of_size hsy
  have s4 := mn_digits_runs (body := body) (Pre := mnSynPre σ) .ry (Or.inr rfl) hb1 hpb hpw y
    (bitsMSB n y) hys (mn_digits_len hbig y) F₃ g₃ (by subst hg₃ hg₁; simp [hry])
    (by subst hg₃ hg₁; simp [hdbn]) (by subst hg₃ hg₁; simp [hdpn]) (by subst hg₃ hg₁; simp [hdwn])
    (by subst hg₃ hg₁; simp [hdsn]) (by subst hg₃ hg₁; simp [htpl]) (by subst hg₃ hg₁; simp [htmp])
    (by subst hg₃ hg₁; simp [hstmp]) (by subst hg₃ hg₁; simp [hacc])
  have hF₃str : F₃.c .str = [] := by subst hF₃ hF₂; simp
  rw [eS, mn_digitStream_eq hpb, hF₃str, List.append_nil] at s4
  obtain ⟨F₄, hF₄⟩ : ∃ F : SrcF 6 (prime + K), F =
      { F₃ with
        c := Function.update F₃.c .str
          (cstream (prime + K) w (srcCoef (p n) (∏ i, s n i) uy)) } := ⟨_, rfl⟩
  obtain ⟨g₄, hg₄⟩ : ∃ g' : MnR → List (Fin (prime + K + 4)),
      g' = Function.update g₃ (.io .ry) [] := ⟨_, rfl⟩
  replace s4 : SrcRuns body mnRg mnι (mnSynPre σ) (mnDigits .ry) (mnGlob F₃ g₃) (mnGlob F₄ g₄)
      (digitCost (b n) (p n) w (∏ i, s n i)) := by rw [hF₄, hg₄]; exact s4
  -- 5. the source transform of `y`
  have hE₄ : SrcBase mnM F₄ n w W hd0
      (preCfgA V₀ crtHd n w W hd0 (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1))
      (bandCfgB σ₀ crtHd n w W hd0 (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1))
      (preRecsA n W hd0 0 ++ restA) (preRecsB n W hd0 0 ++ restB) axsA axsB := by
    refine SrcBase.next (E := E) (by omega) hE (fun r _ => by subst hF₄ hF₃ hF₂; rfl)
      (by subst hF₄ hF₃ hF₂; rfl) (by subst hF₄ hF₃ hF₂ hF₁; rfl) (by subst hF₄ hF₃ hF₂ hF₁; rfl)
      (by subst hF₄ hF₃ hF₂ hF₁; rfl) (fun j hj => ?_)
    subst hF₄ hF₃ hF₂ hF₁
    simp [Function.update_of_ne hj]
  have hC₄ : SrcCrtBase F₄.c F₄.cb n w := by
    subst hF₄ hF₃ hF₂ hF₁; exact ((hC.upd_str _).upd_str _).upd_str _
  have s5 := mn_srcP_runs (body := body) hA hbig hsmall hEs hF hO hπ hP hw hwW hWA hWB hWs hWk F₄
    hE₄ hC₄ (by subst hF₄ hF₃ hF₂; rfl) uy huy1 huyf (by subst hF₄; simp) g₄
  obtain ⟨F₅, hF₅⟩ : ∃ F : SrcF 6 (prime + K), F =
      { F₄ with
        a := (rsaWith (preCfgA (preCfgA V₀ crtHd n w W hd0
          (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1)) crtHd n w W hd0
          (preRecsA n W hd0 0 ++ restA) (d n - 1)) [] axsA []).get
        b := rsbWith (bandCfgB (bandCfgB σ₀ crtHd n w W hd0
          (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1)) crtHd n w W hd0
          (preRecsB n W hd0 0 ++ restB) (d n - 1)) [] axsB []
        c := Function.update F₄.c .str []
        x := Function.update F₄.x .sb (BY ++ F₄.x .sb) } := ⟨_, rfl⟩
  replace s5 : SrcRuns body mnRg mnι (mnSynPre σ) (srcDirectP mnM fwdP oppP) (mnGlob F₄ g₄)
      (mnGlob F₅ g₄) (srcDirectPCost mnM n w W cF cO hd0
        (preCfgA V₀ crtHd n w W hd0 (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1))
        (bandCfgB σ₀ crtHd n w W hd0 (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1))
        (preRecsA n W hd0 0 ++ restA) (preRecsB n W hd0 0 ++ restB)) := by subst hF₅; exact s5
  have hF₅sb : F₅.x .sb = BY := by subst hF₅ hF₄ hF₃; simp
  have hg₄hx : g₄ (.io .hx) = BX := by subst hg₄ hg₃; simp
  have hg₄sp : g₄ (.io .sp) = [] := by subst hg₄ hg₃ hg₁; simp [hsp]
  -- 6, 7. both transforms onto the product registers
  have s6 := mn_mv_hx_xs (body := body) (Pre := mnSynPre σ) F₅ g₄ hg₄sp
  have hF₅v : F₅.v = E.v := by subst hF₅ hF₄ hF₃ hF₂ hF₁; rfl
  rw [hg₄hx, hF₅v, hE.v.cmxs, List.append_nil, hTw] at s6
  obtain ⟨F₆, hF₆⟩ : ∃ F : SrcF 6 (prime + K), F =
      { F₅ with v := Function.update E.v (.cm .xs) BX } := ⟨_, rfl⟩
  obtain ⟨g₆, hg₆⟩ : ∃ g' : MnR → List (Fin (prime + K + 4)),
      g' = Function.update g₄ (.io .hx) [] := ⟨_, rfl⟩
  replace s6 : SrcRuns body mnRg mnι (mnSynPre σ) (mnMv (.io .hx) (.src (.v (.cm .xs))))
      (mnGlob F₅ g₄) (mnGlob F₆ g₆) (4 * ((∏ i, t n i) * w) + 4) := by
    rw [hF₆, hg₆]; exact s6
  have hg₆sp : g₆ (.io .sp) = [] := by subst hg₆; simp [hg₄sp]
  have s7 := mn_mv_sb_ys (body := body) (Pre := mnSynPre σ) F₆ g₆ hg₆sp
  have hF₆sb : F₆.x .sb = BY := by subst hF₆; exact hF₅sb
  have hF₆ys : F₆.v (.cm .ys) = [] := by subst hF₆; simp [hE.v.cmys]
  rw [hF₆sb, hF₆ys, List.append_nil, hTwY] at s7
  obtain ⟨F₇, hF₇⟩ : ∃ F : SrcF 6 (prime + K), F =
      { F₆ with
        x := Function.update F₆.x .sb []
        v := Function.update F₆.v (.cm .ys) BY } := ⟨_, rfl⟩
  replace s7 : SrcRuns body mnRg mnι (mnSynPre σ) (mnMv (.src (.x .sb)) (.src (.v (.cm .ys))))
      (mnGlob F₆ g₆) (mnGlob F₇ g₆) (4 * ((∏ i, t n i) * w) + 4) := by rw [hF₇]; exact s7
  -- 8. the pointwise product
  have hF₇v : F₇.v = Function.update (Function.update E.v (.cm .xs) BX) (.cm .ys) BY := by
    subst hF₇ hF₆; rfl
  have hF₇sb : F₇.x .sb = [] := by subst hF₇; simp
  have s8 := mn_point_runs (body := body) (Pre := mnSynPre σ) hA hw1 hpw (t n)
    (mnPad (s n) (t n) (srcMap n ux)) (mnPad (s n) (t n) (srcMap n uy))
    (fun _ => mn_pad_fixed (mn_srcMap_fixed hd0 ux) _)
    (fun _ => mn_pad_fixed (mn_srcMap_fixed hd0 uy) _)
    (fun _ => mn_pad_fits (fun k => mn_fits ((norm_le_pi_norm _ k).trans hFx) (by omega)) _)
    (fun _ => mn_pad_fits (fun k => mn_fits ((norm_le_pi_norm _ k).trans hFy) (by omega)) _)
    (mnGlob F₇ g₆)
    (cst_ready_of_eq hE.v.ready fun c h1 h2 _ _ _ _ => by
      simp only [mnGlob_src, SrcF.get_v, hF₇v]
      rw [Function.update_of_ne (by simpa using h2), Function.update_of_ne (by simpa using h1)])
    (by simp only [mnGlob_src, SrcF.get_v, hF₇v]; simp [hBX, mn_srcPad_eq])
    (by simp only [mnGlob_src, SrcF.get_v, hF₇v]; simp [hBY, mn_srcPad_eq])
    (by simp [hF₇v, hE.v.cmxsv]) (by simp [hF₇v, hE.v.cmysv]) (by simp [hF₇v, hE.v.cmacc])
  have hF₇out : F₇.v (.cm .out) = [] := by simp [hF₇v, hE.v.cmout]
  simp only [mnGlob_src, SrcF.get_v, hF₇out, List.append_nil] at s8
  rw [mn_upd_v] at s8
  obtain ⟨F₈, hF₈⟩ : ∃ F : SrcF 6 (prime + K), F =
      { F₇ with v := Function.update F₇.v (.cm .out) PR } := ⟨_, rfl⟩
  replace s8 : SrcRuns body mnRg mnι (mnSynPre σ) mnPoint (mnGlob F₇ g₆) (mnGlob F₈ g₆)
      ((∏ i, t n i) * (cmulCost w + 6 * w + 2) + 8) := by rw [hF₈]; exact s8
  -- 9, 10. clear the operands
  have s9 := mn_clear_cm (body := body) (Pre := mnSynPre σ) .xs F₈ g₆
  have hF₈xs : F₈.v (.cm .xs) = BX := by subst hF₈; simp [hF₇v]
  rw [hF₈xs, hTw] at s9
  obtain ⟨F₉, hF₉⟩ : ∃ F : SrcF 6 (prime + K), F =
      { F₈ with v := Function.update F₈.v (.cm .xs) [] } := ⟨_, rfl⟩
  replace s9 : SrcRuns body mnRg mnι (mnSynPre σ) (uclear (mnCm .xs)) (mnGlob F₈ g₆)
      (mnGlob F₉ g₆) (2 * ((∏ i, t n i) * w) + 2) := by rw [hF₉]; exact s9
  have s10 := mn_clear_cm (body := body) (Pre := mnSynPre σ) .ys F₉ g₆
  have hF₉ys : F₉.v (.cm .ys) = BY := by subst hF₉ hF₈; simp [hF₇v]
  rw [hF₉ys, hTwY] at s10
  obtain ⟨F₁₀, hF₁₀⟩ : ∃ F : SrcF 6 (prime + K), F =
      { F₉ with v := Function.update F₉.v (.cm .ys) [] } := ⟨_, rfl⟩
  replace s10 : SrcRuns body mnRg mnι (mnSynPre σ) (uclear (mnCm .ys)) (mnGlob F₉ g₆)
      (mnGlob F₁₀ g₆) (2 * ((∏ i, t n i) * w) + 2) := by rw [hF₁₀]; exact s10
  -- 11. the product onto `x .sb`
  have s11 := mn_mv_out_sb (body := body) (Pre := mnSynPre σ) F₁₀ g₆ hg₆sp
  have hF₁₀out : F₁₀.v (.cm .out) = PR := by subst hF₁₀ hF₉ hF₈; simp
  have hF₁₀sb : F₁₀.x .sb = [] := by subst hF₁₀ hF₉ hF₈; exact hF₇sb
  have hPRl : PR.length = (∏ i, t n i) * w := by rw [hPR, length_cstream, src_length_pad]
  rw [hF₁₀out, hF₁₀sb, List.append_nil, hPRl] at s11
  obtain ⟨F₁₁, hF₁₁⟩ : ∃ F : SrcF 6 (prime + K), F =
      { F₁₀ with
        v := Function.update F₁₀.v (.cm .out) []
        x := Function.update F₁₀.x .sb PR } := ⟨_, rfl⟩
  replace s11 : SrcRuns body mnRg mnι (mnSynPre σ) (mnMv (.src (.v (.cm .out))) (.src (.x .sb)))
      (mnGlob F₁₀ g₆) (mnGlob F₁₁ g₆) (4 * ((∏ i, t n i) * w) + 4) := by rw [hF₁₁]; exact s11
  -- 12. the opposite transform
  have hF₁₁v : F₁₁.v = E.v := by
    subst hF₁₁ hF₁₀ hF₉ hF₈
    rw [hF₇v]
    funext c
    by_cases h1 : c = .cm .out
    · subst h1; simp [hE.v.cmout]
    by_cases h2 : c = .cm .ys
    · subst h2; simp [hE.v.cmys]
    by_cases h3 : c = .cm .xs
    · subst h3; simp [hE.v.cmxs]
    simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  have hE₁₁ : SrcBase mnM F₁₁ n w W hd0
      (preCfgA (preCfgA V₀ crtHd n w W hd0 (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA))
        (d n - 1)) crtHd n w W hd0 (preRecsA n W hd0 0 ++ restA) (d n - 1))
      (bandCfgB (bandCfgB σ₀ crtHd n w W hd0 (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB))
        (d n - 1)) crtHd n w W hd0 (preRecsB n W hd0 0 ++ restB) (d n - 1))
      restA restB axsA axsB := by
    refine SrcBase.next (E := F₄) (by omega) hE₄ (fun r _ => by subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; rfl)
      (by subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; rfl)
      (by subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; rfl)
      (by rw [hF₁₁v]; subst hF₄ hF₃ hF₂ hF₁; rfl)
      (by subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; rfl) (fun j hj => ?_)
    subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅
    simp [Function.update_of_ne hj]
  have hC₁₁ : SrcCrtBase F₁₁.c F₁₁.cb n w := by
    subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; exact hC₄.upd_str _
  have s12 := mn_oppP_runs (body := body) hA hbig hsmall hEs hF hO hπ hP hw hwW hWA hWB hWs hWk
    F₁₁ hE₁₁ hC₁₁ (by subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; rfl)
    (by subst hF₁₁ hF₁₀ hF₉ hF₈ hF₇ hF₆ hF₅; simp) Y hY1 hYf
    (by rw [← hPR]; subst hF₁₁; simp) g₆
  obtain ⟨F₁₂, hF₁₂⟩ : ∃ F : SrcF 6 (prime + K), F =
      { F₁₁ with
        a := (rsaWith (preCfgA (preCfgA (preCfgA V₀ crtHd n w W hd0
          (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA)) (d n - 1)) crtHd n w W hd0
          (preRecsA n W hd0 0 ++ restA) (d n - 1)) crtHd n w W hd0 restA (d n - 1)) [] axsA []).get
        b := rsbWith (bandCfgB (bandCfgB (bandCfgB σ₀ crtHd n w W hd0
          (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB)) (d n - 1)) crtHd n w W hd0
          (preRecsB n W hd0 0 ++ restB) (d n - 1)) crtHd n w W hd0 restB (d n - 1)) [] axsB []
        c := Function.update F₁₁.c .str CO
        x := Function.update F₁₁.x .sb [] } := ⟨_, rfl⟩
  replace s12 : SrcRuns body mnRg mnι (mnSynPre σ) (oppDirectP mnM fwdP oppP) (mnGlob F₁₁ g₆)
      (mnGlob F₁₂ g₆) (oppDirectPCost mnM n w W cF cO hd0
        (preCfgA (preCfgA V₀ crtHd n w W hd0 (preRecsA n W hd0 0 ++ (preRecsA n W hd0 0 ++ restA))
          (d n - 1)) crtHd n w W hd0 (preRecsA n W hd0 0 ++ restA) (d n - 1))
        (bandCfgB (bandCfgB σ₀ crtHd n w W hd0 (preRecsB n W hd0 0 ++ (preRecsB n W hd0 0 ++ restB))
          (d n - 1)) crtHd n w W hd0 (preRecsB n W hd0 0 ++ restB) (d n - 1))
        restA restB) := by subst hF₁₂; exact s12
  -- 13. the coefficient stream onto the rounding stage
  have s13 := mn_mv_str_rnd (body := body) (Pre := mnSynPre σ) F₁₂ g₆ hg₆sp
  have hF₁₂str : F₁₂.c .str = CO := by subst hF₁₂; simp
  have hg₆rsrc : g₆ (.rnd .src) = [] := by subst hg₆ hg₄ hg₃ hg₁; simp [hrsrc]
  have hCOl : CO.length = S n * w := by rw [hCO, length_cstream, src_length_coef]; rfl
  rw [hF₁₂str, hg₆rsrc, List.append_nil, hCOl] at s13
  obtain ⟨F₁₃, hF₁₃⟩ : ∃ F : SrcF 6 (prime + K), F =
      { F₁₂ with c := Function.update F₁₂.c .str [] } := ⟨_, rfl⟩
  obtain ⟨g₁₃, hg₁₃⟩ : ∃ g' : MnR → List (Fin (prime + K + 4)),
      g' = Function.update g₆ (.rnd .src) CO := ⟨_, rfl⟩
  replace s13 : SrcRuns body mnRg mnι (mnSynPre σ) (mnMv (.src (.c .str)) (.rnd .src))
      (mnGlob F₁₂ g₆) (mnGlob F₁₃ g₁₃) (4 * (S n * w) + 4) := by rw [hF₁₃, hg₁₃]; exact s13
  -- 14. the rounding stage
  have hgr : ∀ r : RndReg, r ≠ .src → g₁₃ (.rnd r) = g (.rnd r) := by
    intro r hr; subst hg₁₃ hg₆ hg₄ hg₃ hg₁; simp [hr]
  have hSm : S n * S n < 2 ^ mnMw n w := by
    have h1 := Nat.lt_size_self (S n)
    calc S n * S n < 2 ^ Nat.size (S n) * 2 ^ Nat.size (S n) := Nat.mul_lt_mul'' h1 h1
      _ = 2 ^ (2 * Nat.size (S n)) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ mnMw n w := Nat.pow_le_pow_right (by norm_num) (by unfold mnMw; omega)
  have s14 := mn_round_runs (body := body) (Pre := mnSynPre σ) hA4 (m := mnMw n w) (b' := b n)
    (p' := p n) (W := mnWo n) (S' := ∏ i, s n i) hw1 (by unfold mnMw; omega) hSm
    (fun i => numer (p n) (oppMap n Y ((i : ℕ) : ZMod (∏ i, s n i))))
    (fun i => (mn_fits ((norm_le_pi_norm _ _).trans hOY) (by omega)).1)
    (mnGlob F₁₃ g₁₃) (by simp only [mnGlob_rnd]; rw [hg₁₃, Function.update_self, hCO,
      mn_coef_stream])
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrwn)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrmn)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrnn)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrsq)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrbn)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrpn)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrwo)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrtm)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hru1)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrsg)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrxa)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrxc)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hrcy)
    (by simp only [mnGlob_rnd]; rw [hgr _ (by decide)]; exact hracc)
  simp only [mnGlob_rnd] at s14
  rw [hgr _ (by decide), hrdst, List.append_nil, mn_upd_g _ _ (by intro x h; cases h),
    mn_upd_g _ _ (by intro x h; cases h)] at s14
  obtain ⟨g₁₄, hg₁₄⟩ : ∃ g' : MnR → List (Fin (prime + K + 4)),
      g' = Function.update (Function.update g₁₃ (.rnd .src) []) (.rnd .dst) (mnWords K n x y) :=
    ⟨_, rfl⟩
  replace s14 : SrcRuns body mnRg mnι (mnSynPre σ) mnRound (mnGlob F₁₃ g₁₃) (mnGlob F₁₃ g₁₄)
      (roundStageCost (mnMw n w) w (b n) (p n) (mnWo n) (S n)) := by
    rw [hg₁₄]; exact s14
  -- 15. the words onto the output stage
  have hg₁₄sp : g₁₄ (.io .sp) = [] := by subst hg₁₄ hg₁₃; simp [hg₆sp]
  have s15 := mn_mv_dst_dat (body := body) (Pre := mnSynPre σ) F₁₃ g₁₄ hg₁₄sp
  have hg₁₄dst : g₁₄ (.rnd .dst) = mnWords K n x y := by subst hg₁₄; simp
  have hg₁₄dat : g₁₄ (.out .dat) = [] := by subst hg₁₄ hg₁₃ hg₆ hg₄ hg₃ hg₁; simp [hodat]
  have hWl : (mnWords K n x y).length = S n * mnWo n := by
    rw [mnWords, mn_length_words, List.length_ofFn]; rfl
  rw [hg₁₄dst, hg₁₄dat, List.append_nil, hWl] at s15
  -- the chain
  have hd := mn_hdisj
  refine ⟨F₁₃, _, (s1.seq hd hP (s2.seq hd hP (s3.seq hd hP (s4.seq hd hP (s5.seq hd hP
    (s6.seq hd hP (s7.seq hd hP (s8.seq hd hP (s9.seq hd hP (s10.seq hd hP (s11.seq hd hP
    (s12.seq hd hP (s13.seq hd hP (s14.seq hd hP s15)))))))))))))).mono (le_of_eq ?_), ?_, ?_⟩
  · simp only [mnChainCost, mnGlue, eS]
    ring
  · simp
  · intro r hr
    subst hg₁₄ hg₁₃ hg₆ hg₄ hg₃ hg₁
    simp [hr]

end Chain

end

end IntegerMultBounds.MathlibTM2.Fast.Main
