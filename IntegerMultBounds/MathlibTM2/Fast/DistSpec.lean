module

public import IntegerMultBounds.MathlibTM2.Fast.DistSrc
import IntegerMultBounds.MathlibTM2.Fast.DistWidth
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# The final register file of the converter

The writes `dsSrcW` of the converter (`Fast/DistSrc.lean`) as one explicit register file of the
source transform, `dsSrcE n w Wt hd0 : SrcF t₀ A` (`ds_srcE_get`: the final family file of
`ds_src_runs` is `dsSrcE` on the source registers and `dsSrcO` on the converter's own outputs),
and the register file between runs it realises:

* `ds_srcE_base`: `SrcBase M (dsSrcE n w Wt hd0) n w Wt hd0 (dsV₀ …) (dsσ₀ …) (dsRestA …)
  (dsRestB …) (dsAxs n) (dsAxs n)` — the `Ã` base file `dsV₀`, the `B̃₀` base file `dsσ₀`,
  two further sets of records `dsRestA`, `dsRestB` (for the runs `srcP`, `oppP'` after the first
  `srcP`), `d - 1` ticks on the axis counters `dsAxs n`;
* `ds_srcE_crt`: `SrcCrtBase (dsSrcE …).c (dsSrcE …).cb n w`;
* `ds_srcE_ln`, `ds_srcE_str`, `ds_srcE_sb`: the box register `a .ln`, the coefficient stream
  `c .str` and the source box `x .sb` are empty.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.Sizes IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Src IntegerMultBounds.MathlibTM2.Fast.ChirpSt
  IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.ResampA
open IntegerMultBounds.Networks.Shared50ModularControl (prime)


noncomputable section

section Files

variable {A t₀ : ℕ}

/-- The `Ã` family after the converter. -/
def dsSrcEa (n w Wt : ℕ) (hd0 : 0 < d n) : RsaR (RsaX t₀) → List (Fin (A + 4))
  | .c .out => preRecsA n Wt hd0 0 ++ (preRecsA n Wt hd0 0 ++ preRecsA n Wt hd0 0)
  | .c .wn => List.replicate w tick
  | .c .nn => List.replicate (dsTopN w) tick
  | .x .ax => List.replicate (d n - 1) tick
  | _ => []

/-- The `B̃₀` family after the converter. -/
def dsSrcEb (n w Wt : ℕ) (hd0 : 0 < d n) : RsbR ⊕ RsbX t₀ → List (Fin (A + 4))
  | .inl .prm => preRecsB n Wt hd0 0 ++ (preRecsB n Wt hd0 0 ++ preRecsB n Wt hd0 0)
  | .inl (.cm .wn) => List.replicate w tick
  | .inl (.cm .nn) => List.replicate (dsTopN w) tick
  | .inr .ax => List.replicate (d n - 1) tick
  | _ => []

/-- The chirp kernel family after the converter. -/
def dsSrcEk (n w Wt : ℕ) : CsR ldcX → List (Fin (A + 4))
  | .c .pn => List.replicate (p n + Chirp.chirpGuard (d n)) tick
  | .c .wn => List.replicate w tick
  | .c .nn => List.replicate (dsTopN w) tick
  | .ax => List.replicate (d n - 1) tick
  | .pn2 => List.replicate (p n + Chirp.chirpGuard (d n) + 2) tick
  | .kc => csyms A w (cstDiskC (p n))
  | .x .pU => List.replicate (p n) tick
  | .x .gU => List.replicate (Chirp.chirpGuard (d n)) tick
  | .x .wU => List.replicate w tick
  | .x (.tbl .wr) => List.replicate Wt tick
  | .x (.tbl .wn) => List.replicate w tick
  | _ => []

/-- The convolution family after the converter. -/
def dsSrcEv (n w : ℕ) : CvR → List (Fin (A + 4))
  | .cm .pn => List.replicate (p n) tick
  | .cm .wn => List.replicate w tick
  | .cm .nn => List.replicate (dsTopN w) tick
  | .shS => List.replicate (logT n - ℓ n) tick
  | .shR => List.replicate (w - (logT n - ℓ n)) tick
  | .tp => tblTwistStream A w (p n) (r n) false
  | .tm => tblTwistStream A w (p n) (r n) true
  | _ => []

/-- The CRT family after the converter. -/
def dsSrcEc (n w : ℕ) : CrtReg → List (Fin (A + 4))
  | .wT => crtEnts ((crtRevAx (d n)).map (srcAx n))
  | .sT => crtEnts ((crtRevAx (d n)).map (s n))
  | .mT => crtEnts ((crtRevAx (d n)).map fun j =>
      (crtMu (s n) (Pipeline.s_pairwise n) j : ZMod (s n j)).val)
  | .sig => binSyms (crtPre (srcAx n) (d n)) (crtSig (srcAx n) (s n) (d n))
  | .msk => binSyms (crtPre (srcAx n) (d n)) (crtMask (srcAx n) (d n))
  | .zr => csyms A w 0
  | _ => []

/-- The first-product family after the converter. -/
def dsSrcEm (n w : ℕ) : CR → List (Fin (A + 4))
  | .pn => List.replicate (p n + 1) tick
  | .wn => List.replicate w tick
  | .nn => List.replicate (dsTopN w) tick
  | _ => []

/-- The transfer registers after the converter. -/
def dsSrcEx (n w : ℕ) : SrcX → List (Fin (A + 4))
  | .lU => List.replicate (ℓ n) tick
  | .gS => List.replicate (gamma n) tick
  | .gR => List.replicate (w - gamma n) tick
  | .tSp => ldcBlocks (List.ofFn (t n))
  | .sSp => ldcBlocks (List.ofFn (s n))
  | _ => []

/-- **The register file of the source transform after the converter.** -/
def dsSrcE (n w Wt : ℕ) (hd0 : 0 < d n) : SrcF t₀ A where
  a := dsSrcEa n w Wt hd0
  b := dsSrcEb n w Wt hd0
  k := dsSrcEk n w Wt
  v := dsSrcEv n w
  c := dsSrcEc n w
  cb := fun _ => []
  m := dsSrcEm n w
  x := dsSrcEx n w

/-- The converter's own outputs after the converter. -/
def dsSrcO (n w : ℕ) : DsX → List (Fin (A + 4))
  | .rR => List.replicate (r n) tick
  | .lK => List.replicate (K n) tick
  | .lL => List.replicate (ℓ n) tick
  | .lN => List.replicate (logT n - ℓ n) tick
  | .lD => List.replicate (d n - 1) tick
  | .lB => List.replicate (r n * w) tick
  | .lW => List.replicate (dsWL n w) tick
  | .lE => binSyms (dsWL n w) (dsE n)
  | _ => []

/-- The registers the converter writes. -/
def dsKeys : List (DsY t₀) :=
  [.s (.a (.c .out)), .s (.b (.inl .prm)), .s (.x .tSp), .s (.x .sSp), .s (.c .wT), .s (.c .sT),
   .s (.c .mT), .s (.c .sig), .s (.c .msk),
   .s (.k (.x .pU)), .s (.k (.x .gU)), .s (.x .lU), .s (.x .gS), .s (.k (.c .pn)),
   .s (.v (.cm .pn)), .o .rR, .o .lK, .o .lL,
   .s (.a (.c .wn)), .s (.b (.inl (.cm .wn))), .s (.k (.c .wn)), .s (.k (.x .wU)),
   .s (.k (.x (.tbl .wn))), .s (.v (.cm .wn)), .s (.m .wn),
   .s (.k (.x (.tbl .wr))), .s (.k .ax), .s (.a (.x .ax)), .s (.b (.inr .ax)), .o .lD,
   .s (.v .shS), .o .lN, .s (.x .gR), .s (.v .shR), .s (.m .pn), .s (.k .pn2), .s (.k (.c .nn)),
   .s (.a (.c .nn)), .s (.b (.inl (.cm .nn))), .s (.v (.cm .nn)), .s (.m .nn),
   .s (.k .kc), .s (.c .zr), .o .lB, .o .lW, .o .lE, .s (.v .tp), .s (.v .tm)]

theorem dsSrcW_keys (n w Wt : ℕ) (hd0 : 0 < d n) :
    (dsSrcW (A := A) (t₀ := t₀) n w Wt hd0).map Prod.fst = dsKeys := by
  simp [dsSrcW, dsSrcW₁, dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp, dsP2bW, dsP2cW, dsKeys]

end Files

section Get

variable {A t₀ : ℕ} {n w Wt : ℕ} {hd0 : 0 < d n} {X X' : DsY t₀ → List (Fin (A + 4))}
  (hv : ∀ e ∈ dsSrcW (A := A) (t₀ := t₀) n w Wt hd0, X' e.1 = e.2)
  (ho : ∀ y, y ∉ (dsSrcW (A := A) (t₀ := t₀) n w Wt hd0).map Prod.fst → X' y = X y)
  (hX : ∀ y, y ≠ .o .uW → y ≠ .o .uw → X y = [])
include hv ho hX

omit ho hX in
/-- The writes of the converter on a written register. -/
theorem ds_srcE_key (y : DsY t₀) (l : List (Fin (A + 4)))
    (h : (y, l) ∈ dsSrcW (A := A) (t₀ := t₀) n w Wt hd0) : X' y = l := hv (y, l) h

omit hv in
/-- The writes of the converter off the written registers. -/
theorem ds_srcE_off (y : DsY t₀) (h : y ∉ (dsKeys : List (DsY t₀))) (h1 : y ≠ .o .uW)
    (h2 : y ≠ .o .uw) : X' y = [] := by
  rw [ho y (by rwa [dsSrcW_keys]), hX y h1 h2]

omit hv hX in
/-- The converter's own inputs are untouched. -/
theorem ds_srcE_in : X' (.o .uW) = X (.o .uW) ∧ X' (.o .uw) = X (.o .uw) :=
  ⟨ho _ (by rw [dsSrcW_keys]; simp [dsKeys]), ho _ (by rw [dsSrcW_keys]; simp [dsKeys])⟩

set_option maxHeartbeats 2000000 in
theorem ds_srcE_get_a (r : RsaR (RsaX t₀)) :
    X' (.s (.a r)) = (dsSrcE (t₀ := t₀) n w Wt hd0).get (.a r) := by
  have key := ds_srcE_key hv
  have off := ds_srcE_off ho hX
  cases r <;> try (rename_i x; cases x)
  all_goals
    simp only [SrcF.get_a, dsSrcE, dsSrcEa]
    first
    | exact off _ (by simp [dsKeys]) (by simp) (by simp)
    | exact key _ _ (by simp [dsSrcW, dsSrcW₁, dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp,
        dsP2bW, dsP2cW])

set_option maxHeartbeats 2000000 in
theorem ds_srcE_get_b (r : RsbR ⊕ RsbX t₀) :
    X' (.s (.b r)) = (dsSrcE (t₀ := t₀) n w Wt hd0).get (.b r) := by
  have key := ds_srcE_key hv
  have off := ds_srcE_off ho hX
  rcases r with r | r <;> cases r <;> try (rename_i x; cases x)
  all_goals
    simp only [SrcF.get_b, dsSrcE, dsSrcEb]
    first
    | exact off _ (by simp [dsKeys]) (by simp) (by simp)
    | exact key _ _ (by simp [dsSrcW, dsSrcW₁, dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp,
        dsP2bW, dsP2cW])

set_option maxHeartbeats 2000000 in
theorem ds_srcE_get_k (r : CsR ldcX) :
    X' (.s (.k r)) = (dsSrcE (t₀ := t₀) n w Wt hd0).get (.k r) := by
  have key := ds_srcE_key hv
  have off := ds_srcE_off ho hX
  cases r <;> try (rename_i x; cases x) <;> try (rename_i y; cases y)
  all_goals
    simp only [SrcF.get_k, dsSrcE, dsSrcEk]
    first
    | exact off _ (by simp [dsKeys]) (by simp) (by simp)
    | exact key _ _ (by simp [dsSrcW, dsSrcW₁, dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp,
        dsP2bW, dsP2cW])

set_option maxHeartbeats 2000000 in
theorem ds_srcE_get_v (r : CvR) :
    X' (.s (.v r)) = (dsSrcE (t₀ := t₀) n w Wt hd0).get (.v r) := by
  have key := ds_srcE_key hv
  have off := ds_srcE_off ho hX
  cases r <;> try (rename_i x; cases x)
  all_goals
    simp only [SrcF.get_v, dsSrcE, dsSrcEv]
    first
    | exact off _ (by simp [dsKeys]) (by simp) (by simp)
    | exact key _ _ (by simp [dsSrcW, dsSrcW₁, dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp,
        dsP2bW, dsP2cW])

set_option maxHeartbeats 2000000 in
theorem ds_srcE_get_c (r : CrtReg) :
    X' (.s (.c r)) = (dsSrcE (t₀ := t₀) n w Wt hd0).get (.c r) := by
  have key := ds_srcE_key hv
  have off := ds_srcE_off ho hX
  cases r
  all_goals
    simp only [SrcF.get_c, dsSrcE, dsSrcEc]
    first
    | exact off _ (by simp [dsKeys]) (by simp) (by simp)
    | exact key _ _ (by simp [dsSrcW, dsSrcW₁, dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp,
        dsP2bW, dsP2cW])

set_option maxHeartbeats 2000000 in
theorem ds_srcE_get_m (r : CR) :
    X' (.s (.m r)) = (dsSrcE (t₀ := t₀) n w Wt hd0).get (.m r) := by
  have key := ds_srcE_key hv
  have off := ds_srcE_off ho hX
  cases r
  all_goals
    simp only [SrcF.get_m, dsSrcE, dsSrcEm]
    first
    | exact off _ (by simp [dsKeys]) (by simp) (by simp)
    | exact key _ _ (by simp [dsSrcW, dsSrcW₁, dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp,
        dsP2bW, dsP2cW])

set_option maxHeartbeats 2000000 in
theorem ds_srcE_get_x (r : SrcX) :
    X' (.s (.x r)) = (dsSrcE (t₀ := t₀) n w Wt hd0).get (.x r) := by
  have key := ds_srcE_key hv
  have off := ds_srcE_off ho hX
  cases r
  all_goals
    simp only [SrcF.get_x, dsSrcE, dsSrcEx]
    first
    | exact off _ (by simp [dsKeys]) (by simp) (by simp)
    | exact key _ _ (by simp [dsSrcW, dsSrcW₁, dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp,
        dsP2bW, dsP2cW])

/-- **The final family file on the source registers.** -/
theorem ds_srcE_get (r : SrcR t₀) : X' (.s r) = (dsSrcE n w Wt hd0).get r := by
  cases r with
  | a r => exact ds_srcE_get_a hv ho hX r
  | b r => exact ds_srcE_get_b hv ho hX r
  | k r => exact ds_srcE_get_k hv ho hX r
  | v r => exact ds_srcE_get_v hv ho hX r
  | c r => exact ds_srcE_get_c hv ho hX r
  | cb j => exact ds_srcE_off ho hX _ (by simp [dsKeys]) (by simp) (by simp)
  | m r => exact ds_srcE_get_m hv ho hX r
  | x r => exact ds_srcE_get_x hv ho hX r

/-- **The final family file on the converter's own outputs.** -/
theorem ds_srcO_get (x : DsX) (h1 : x ≠ .uW) (h2 : x ≠ .uw) : X' (.o x) = dsSrcO n w x := by
  have key := ds_srcE_key hv
  have off := ds_srcE_off ho hX
  cases x
  all_goals
    first
    | exact absurd rfl h1
    | exact absurd rfl h2
    | simp only [dsSrcO]
      first
      | exact off _ (by simp [dsKeys]) (by simp) (by simp)
      | exact key _ _ (by simp [dsSrcW, dsSrcW₁, dsP2aW, dsP2aW₁, dsP2wcp, dsP2dcp, dsP2ncp,
          dsP2bW, dsP2cW])

end Get

section Base

variable {A t₀ : ℕ} {n w Wt : ℕ} {hd0 : 0 < d n}

/-- `d - 1` ticks: the axis counters of the resampling families. -/
def dsAxs (n : ℕ) : List (Fin (A + 4)) := List.replicate (d n - 1) tick

/-- The records of the second and third runs of `Ã`. -/
def dsRestA (n Wt : ℕ) (hd0 : 0 < d n) : List (Fin (A + 4)) :=
  preRecsA n Wt hd0 0 ++ preRecsA n Wt hd0 0

/-- The records of the second and third runs of `B̃₀`. -/
def dsRestB (n Wt : ℕ) (hd0 : 0 < d n) : List (Fin (A + 4)) :=
  preRecsB n Wt hd0 0 ++ preRecsB n Wt hd0 0

/-- The base file of `Ã`: the complex-product registers and the extra family of `dsSrcEa`,
everything else empty. -/
def dsV₀ (n w Wt : ℕ) (hd0 : 0 < d n) : RsaV (RsaX t₀) A where
  cr := fun x => dsSrcEa (t₀ := t₀) n w Wt hd0 (.c x)
  ln := []
  ob := []
  sm := []
  pz := []
  sm2 := []
  ea := []
  eb := []
  er := []
  cS := []
  cM := []
  cP := []
  cW := []
  cT := []
  kW := []
  kT := []
  kx := []
  ka := []
  kb := []
  atm := []
  rr := []
  bS := []
  bxa := []
  bya := []
  bza := []
  xr := fun j => dsSrcEa (t₀ := t₀) n w Wt hd0 (.x j)

/-- The base file of `B̃₀`. -/
def dsσ₀ (n w Wt : ℕ) (hd0 : 0 < d n) : RsbR ⊕ RsbX t₀ → List (Fin (A + 4)) :=
  dsSrcEb n w Wt hd0

theorem dsAxs_length (n : ℕ) : (dsAxs (A := A) n).length = d n - 1 := by simp [dsAxs]

theorem ds_dsTopN (w : ℕ) : dsTopN w = Schoenhage.Schedule.topN w := rfl

/-- The `Ã` family is `rsaWith dsV₀ _ (dsAxs n) []` off the box register. -/
theorem ds_srcE_a (r : RsaR (RsaX t₀)) (hr : r ≠ .ln) :
    (dsSrcE (A := A) n w Wt hd0).a r = (rsaWith (dsV₀ n w Wt hd0) [] (dsAxs n) []).get r := by
  cases r <;> try (rename_i x; cases x)
  all_goals first
    | exact (hr rfl).elim
    | simp [rsaWith, dsSrcE, dsV₀, dsSrcEa, dsAxs]

/-- The `B̃₀` family is `rsbWith dsσ₀ [] (dsAxs n) []`. -/
theorem ds_srcE_b :
    (dsSrcE (A := A) (t₀ := t₀) n w Wt hd0).b =
      rsbWith (dsσ₀ n w Wt hd0) [] (dsAxs n) [] := by
  funext r
  rcases r with r | r <;> cases r
  all_goals simp [rsbWith, dsSrcE, dsσ₀, dsSrcEb, dsAxs]

theorem ds_preBaseA (hd : Fin 5 → Fin t₀) : PreBaseA (dsV₀ (A := A) n w Wt hd0) w hd := by
  constructor
  case free => constructor <;> rfl
  case wn => simp [dsV₀, dsSrcEa]
  case nn => simp [dsV₀, dsSrcEa, ← ds_dsTopN]
  case cr =>
    intro c h1 h2 h3 h4 h5
    cases c <;> first
      | rfl
      | exact (h1 rfl).elim
      | exact (h2 rfl).elim
      | exact (h3 rfl).elim
      | exact (h4 rfl).elim
      | exact (h5 rfl).elim
  case bank => intro j _; rfl
  all_goals rfl

theorem ds_bandBase {K : ℕ} (hd : Fin 5 → Fin t₀) :
    BandBase (dsσ₀ (A := prime + K) n w Wt hd0) w hd := by
  constructor
  case free =>
    constructor
    case vx => intro j; rfl
    case cm =>
      intro c h1 h2 h3 h4 h5 h6
      cases c <;> first
        | rfl
        | exact (h1 rfl).elim
        | exact (h2 rfl).elim
        | exact (h3 rfl).elim
        | exact (h4 rfl).elim
        | exact (h5 rfl).elim
        | exact (h6 rfl).elim
    all_goals rfl
  case wn => simp [dsσ₀, dsSrcEb]
  case nn => simp [dsσ₀, dsSrcEb, ← ds_dsTopN]
  case bank => intro j _; rfl
  all_goals rfl

theorem ds_ready_k : Ready (fun x => dsSrcEk (A := A) n w Wt (.c x)) w
    (p n + Chirp.chirpGuard (d n)) := by
  constructor
  case wn => simp [dsSrcEk]
  case pn => simp [dsSrcEk]
  case nn => simp [dsSrcEk, ← ds_dsTopN]
  all_goals rfl

theorem ds_ready_v : Ready (fun x => dsSrcEv (A := A) n w (.cm x)) w (p n) := by
  constructor
  case wn => simp [dsSrcEv]
  case pn => simp [dsSrcEv]
  case nn => simp [dsSrcEv, ← ds_dsTopN]
  all_goals rfl

theorem ds_ready_m : Ready (dsSrcEm (A := A) n w) w (p n + 1) := by
  constructor
  case wn => simp [dsSrcEm]
  case pn => simp [dsSrcEm]
  case nn => simp [dsSrcEm, ← ds_dsTopN]
  all_goals rfl

theorem ds_cstBase : CstBase (dsSrcEk (A := A) n w Wt) w (p n) (Chirp.chirpGuard (d n)) := by
  constructor
  case ready => exact ds_ready_k
  case pn2 => simp [dsSrcEk]
  all_goals rfl

theorem ds_kerBase (hd0 : 0 < d n) : SrcKerBase (dsSrcEk (A := A) n w Wt) n w Wt := by
  constructor
  case base => exact ds_cstBase
  case ax => simp [dsSrcEk]; omega
  case pU => simp [dsSrcEk]
  case gU => simp [dsSrcEk]
  case wU => simp [dsSrcEk]
  case wr => simp [dsSrcEk]
  case wn => simp [dsSrcEk]
  case tbl =>
    intro r h1 h2
    cases r <;> first
      | rfl
      | exact (h1 rfl).elim
      | exact (h2 rfl).elim
  all_goals rfl

theorem ds_convBase (hn : 2 ≤ n) : SrcConvBase (dsSrcEv (A := A) n w) n w := by
  constructor
  case ready => exact ds_ready_v
  case rpi => intro j; rfl
  case shS => simp [dsSrcEv, ds_sum_cvAx hn]
  case shR => simp [dsSrcEv, ds_sum_cvAx hn]
  all_goals rfl

theorem ds_mulBase : SrcMulBase (dsSrcEm (A := A) n w) n w := by
  constructor
  case ready => exact ds_ready_m
  all_goals rfl

theorem ds_xBase : SrcXBase (dsSrcEx (A := A) n w) n w := by
  constructor
  case gS => simp [dsSrcEx]
  case gR => simp [dsSrcEx]
  case lU => simp [dsSrcEx]
  all_goals rfl

theorem ds_srcE_ln : (dsSrcE (A := A) (t₀ := t₀) n w Wt hd0).a .ln = [] := rfl

theorem ds_srcE_str : (dsSrcE (A := A) (t₀ := t₀) n w Wt hd0).c .str = [] := rfl

theorem ds_srcE_sb : (dsSrcE (A := A) (t₀ := t₀) n w Wt hd0).x .sb = [] := rfl

/-- **The CRT family after the converter is a CRT file between runs.** -/
theorem ds_srcE_crt :
    SrcCrtBase (dsSrcE (A := A) (t₀ := t₀) n w Wt hd0).c
      (dsSrcE (A := A) (t₀ := t₀) n w Wt hd0).cb n w := by
  constructor
  case rest =>
    intro x hx
    cases x <;> first | rfl | simp [crtRestEmpty, crtIdle] at hx
  case bank => intro j; rfl
  all_goals rfl

variable {T Q : ℕ}

/-- **The register file after the converter is a register file between runs** of the source
transform, over the base files `dsV₀`, `dsσ₀`, with two further sets of records and `d - 1`
ticks on the axis counters. -/
theorem ds_srcE_base {K : ℕ} (M : SrcMach t₀ T Q) (hn : 2 ≤ n) (hd0 : 0 < d n) :
    SrcBase M (dsSrcE (A := prime + K) n w Wt hd0) n w Wt hd0 (dsV₀ n w Wt hd0)
      (dsσ₀ n w Wt hd0) (dsRestA n Wt hd0) (dsRestB n Wt hd0) (dsAxs n) (dsAxs n) where
  a := fun r hr => ds_srcE_a r hr
  aBase := ds_preBaseA M.hd
  aOut := rfl
  aAx := dsAxs_length n
  b := ds_srcE_b
  bBase := ds_bandBase M.hd
  bOut := rfl
  bAx := dsAxs_length n
  k := ds_kerBase hd0
  v := ds_convBase hn
  m := ds_mulBase
  x := ds_xBase

end Base

end

end IntegerMultBounds.MathlibTM2.Fast.TableVM
