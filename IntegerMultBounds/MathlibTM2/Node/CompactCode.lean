module

public import IntegerMultBounds.MathlibTM2.Host.IndexCode
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip
public import IntegerMultBounds.MathlibTM2.Layer.CompactBad
public import IntegerMultBounds.MathlibTM2.Layer.CompactGadgetIndex
public import Mathlib.Tactic.DeriveFintype

/-!
# Code programs of the compact rotations

The registers of the compact selected-bit XOR (`CxReg`) and the index state of its passes
(`CxInv`): the field counter `fld g` holds the digits of the current record index, the three mask
registers hold the selected-bit mask `mSel` (slot width), the digit-start mask `mC` (compact
width) and the temporary mask `mA` (slot width), and the scratch registers are empty.

For each offset `o` of a rotation, `codeProg o C` gathers and spreads the bits that the offset
reads into scratch registers, runs the code pass of `C` and clears the scratch. With `C` a
wrap-class automaton of `IntegerMultBounds.MathlibTM2.Layer.CompactCodes` it computes the wrap
class of the rotation by `± Off.eval p o` (`codeProg_spec`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks IntegerMultBounds.MathlibTM2.Layer.CompactGadget

/-- The registers of the compact selected-bit XOR. -/
inductive CxReg where
  /-- The scan slot of the codes and carries. -/
  | st
  /-- The record stream and the class-move registers. -/
  | src | out | ctr | tmp | cnt | ctmp
  | dst (d : Fin 2) | aux (d : Fin 2)
  /-- The record-length and key-length counters, the key temporaries, the fix buckets. -/
  | ctrB | ctrK | kt (i : Fin 3) | fr (i : Fin 4) | fq (i : Fin 4)
  /-- The setup values, the setup binary numbers, the setup temporaries. -/
  | sc (i : Fin 10) | hb (i : Fin 3) | tw (i : Fin 4)
  /-- The index counter fields. -/
  | fld (g : Fin 10)
  /-- The masks. -/
  | mSel | mC | mA | mMk
  /-- Scratch of the code programs. -/
  | g1 | s1 | s2 | gts | gtm | gdst
  /-- Spares of the code pass. -/
  | spare (r : Fin 4)
  deriving DecidableEq, Fintype

/-- The index registers: fields, masks, scratch and spares. -/
def CxReg.isIdx : CxReg → Prop
  | .fld _ | .mSel | .mC | .mA | .mMk | .g1 | .s1 | .s2 | .gts | .gtm | .gdst | .spare _ => True
  | _ => False

variable (p : Par)

/-- The selected-bit mask of a slot. -/
def selV : ℕ := Layer.CompactMasks.maskVal p.n (posS p)

/-- The digit-start mask of a compact field. -/
def mCV : ℕ := Layer.CompactMasks.maskVal p.n (posC p)

/-- The temporary mask of a slot. -/
def mAV : ℕ := Layer.CompactMasks.maskVal (p.n * p.G) (posA p)

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)
variable (ι : CxReg → Fin T) (len : Fin 10 → ℕ)

/-- The index state at index `i`. -/
def CxInv (R : Fin T → List (Fin (A + 4))) (i : ℕ) : Prop :=
  (∀ g, R (ι (.fld g)) = binSyms (len g) (digit len g i)) ∧
  R (ι .mSel) = binSyms p.wy (selV p) ∧ R (ι .mC) = binSyms p.wc (mCV p) ∧
  R (ι .mA) = binSyms p.wy (mAV p) ∧ R (ι .mMk) = binSyms p.wy (mkV p) ∧
  R (ι .g1) = [] ∧ R (ι .s1) = [] ∧ R (ι .s2) = [] ∧ R (ι .gts) = [] ∧ R (ι .gtm) = [] ∧
  R (ι .gdst) = [] ∧ ∀ r, R (ι (.spare r)) = []

/-- The index registers as registers of `Fin T`. -/
def CxIdx (k : Fin T) : Prop := ∃ x : CxReg, x.isIdx ∧ ι x = k

/-! ### Gather then spread -/

section GS

variable {body}

/-- Gather `src` at `mA` into `g`, then spread `g` at `mB` into `s`. -/
def gsProg (src mA mB g s ts tm dst cs : Fin T) : Pr P T Q A U :=
  .seq (gather src mA ts tm dst g cs) (spread g mB ts tm dst s)

theorem gsProg_exec {src mA mB g s ts tm dst cs : Fin T}
    (h₁ : GSRegs src mA ts tm dst g) (h₂ : GSRegs g mB ts tm dst s) (ss ma mb : List Bool) (hl : ma.length = ss.length)
    (hc : mb.count true = (gatherL ss ma).length) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = ss.map bitSymbol) (ha : S.R mA = ma.map bitSymbol)
    (hb : S.R mB = mb.map bitSymbol) (hg : S.R g = []) (hs0 : S.R s = [])
    (hts : S.R ts = []) (htm : S.R tm = []) (hdst : S.R dst = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 8 * ma.length + 8 * mb.length + 16 ∧
      Exec body (gsProg src mA mB g s ts tm dst cs) (mk v S) m
        (mk v' { S with R := Function.update (Function.update S.R g
          ((gatherL ss ma).map bitSymbol)) s ((spreadL (gatherL ss ma) mb).map bitSymbol) }) := by
  have hn₂ := h₂
  simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hn₂
  obtain ⟨⟨b1, b2, b3, b4, b5⟩, ⟨c1, c2, c3, c4⟩, -, -, -⟩ := hn₂
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := gather_exec body (cs := cs) h₁ ma ss hl v S ha hs hts htm hdst
  rw [hg, List.append_nil] at he₁
  set S₁ : Stacks T A := { S with R := Function.update S.R g ((gatherL ss ma).map bitSymbol) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := spread_exec body h₂ mb (gatherL ss ma) hc v₁ S₁
    (by simp [S₁, Function.update_of_ne (Ne.symm b1), hb])
    (by simp [S₁])
    (by simp [S₁, Function.update_of_ne (Ne.symm b2), hts])
    (by simp [S₁, Function.update_of_ne (Ne.symm b3), htm])
    (by simp [S₁, Function.update_of_ne (Ne.symm b4), hdst])
  refine ⟨v₂, m₁ + m₂, by rw [hu₂, hu₁], by omega, Exec.cast (Exec.seq he₁ he₂) rfl ?_⟩
  congr 2
  simp [S₁, Function.update_of_ne (Ne.symm b5), hs0]

end GS

/-! ### Code programs -/

section Code

variable {body} {ι}

/-- The code-pass spares of a `k`-register code pass, `k ≤ 4`. -/
def cxSpares {k : ℕ} (hk : k ≤ 4) (r : Fin k) : CxReg := .spare (Fin.castLE hk r)

/-- Gather `xs` at `xa` into `g1`, spread it at `xb` into `s1`, run the code pass of `C` on the
registers `rs`, clear `g1` and `s1`. -/
def codeGS {k : ℕ} [NeZero k] (hk : k ≤ 4) (xs xa xb : CxReg) (rs : Fin k → CxReg)
    {nd : ℕ} (C : CAuto A k nd) : Pr P T Q A U :=
  .seq (gsProg (ι xs) (ι xa) (ι xb) (ι .g1) (ι .s1) (ι .gts) (ι .gtm) (ι .gdst) (ι .st))
    (.seq (codePass (fun r => ι (rs r)) (fun r => ι (cxSpares hk r)) (ι .st) C)
      (.seq (bclear (ι .g1)) (bclear (ι .s1))))

/-- The registers of `codeGS` are distinct where they must be. -/
structure CodeGSRegs (ι : CxReg → Fin T) {k : ℕ} (hk : k ≤ 4) (xs xa xb : CxReg)
    (rs : Fin k → CxReg) : Prop where
  inj : Function.Injective ι
  srcA : xs ≠ xa
  scr : ∀ x ∈ [xs, xa, xb], x ∉ [CxReg.g1, .s1, .gts, .gtm, .gdst]
  mB_src : xb ≠ xs
  rs_inj : Function.Injective rs
  rs_spare : ∀ r r', rs r ≠ cxSpares hk r'
  rs_st : ∀ r, rs r ≠ .st

theorem codeGS_run {k : ℕ} [NeZero k] {hk : k ≤ 4} {xs xa xb : CxReg} {rs : Fin k → CxReg}
    (h : CodeGSRegs ι hk xs xa xb rs) {nd : ℕ} (C : CAuto A k nd) (ss ma mb : List Bool)
    (hl : ma.length = ss.length) (hc : mb.count true = (gatherL ss ma).length)
    (L : ℕ) (vals : Fin k → ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R (ι xs) = ss.map bitSymbol) (ha : S.R (ι xa) = ma.map bitSymbol)
    (hb : S.R (ι xb) = mb.map bitSymbol) (hg : S.R (ι .g1) = []) (hs1 : S.R (ι .s1) = [])
    (hts : S.R (ι .gts) = []) (htm : S.R (ι .gtm) = []) (hdst : S.R (ι .gdst) = [])
    (hsp : ∀ r, S.R (ι (cxSpares hk r)) = [])
    (hrs : ∀ r, Function.update (Function.update S.R (ι .g1) ((gatherL ss ma).map bitSymbol))
      (ι .s1) ((spreadL (gatherL ss ma) mb).map bitSymbol) (ι (rs r)) = binSyms L (vals r)) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 8 * ma.length + 8 * mb.length + 6 * L + 2 * ss.length + 2 * mb.length + 24 ∧
      v'.scan (ι .st) = C.run L C.init vals ∧
      Exec body (codeGS (ι := ι) hk xs xa xb rs C) (mk v S) m (mk v' S) := by
  obtain ⟨hι, hsa, hscr, hbs, hrsi, hrsp, hrst⟩ := h
  have hne : ∀ {x y : CxReg}, x ≠ y → ι x ≠ ι y := fun hxy => hι.ne hxy
  have hscr' := fun x hx => hscr x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hscr'
  obtain ⟨hs_scr, ha_scr, hb_scr⟩ := hscr'
  simp only [not_or] at hs_scr ha_scr hb_scr
  have h₁ : GSRegs (ι xs) (ι xa) (ι .gts) (ι .gtm) (ι .gdst) (ι .g1) := by
    simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true, hι.eq_iff]
    exact ⟨⟨hsa, hs_scr.2.2.1, hs_scr.2.2.2.1, hs_scr.2.2.2.2, hs_scr.1⟩,
      ⟨ha_scr.2.2.1, ha_scr.2.2.2.1, ha_scr.2.2.2.2, ha_scr.1⟩, by decide, by decide, by decide⟩
  have h₂ : GSRegs (ι .g1) (ι xb) (ι .gts) (ι .gtm) (ι .gdst) (ι .s1) := by
    simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true, hι.eq_iff]
    exact ⟨⟨fun e => hb_scr.1 e.symm, by decide, by decide, by decide, by decide⟩,
      ⟨hb_scr.2.2.1, hb_scr.2.2.2.1, hb_scr.2.2.2.2, hb_scr.2.1⟩, by decide, by decide, by decide⟩
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := gsProg_exec (body := body) (cs := ι .st) h₁ h₂ ss ma mb hl hc
    v S hs ha hb hg hs1 hts htm hdst
  set R₁ := Function.update (Function.update S.R (ι .g1) ((gatherL ss ma).map bitSymbol))
    (ι .s1) ((spreadL (gatherL ss ma) mb).map bitSymbol) with hR₁
  have hlay : CodeLayout (fun r => ι (rs r)) (fun r => ι (cxSpares hk r)) (ι .st) :=
    ⟨hι.comp hrsi, fun r r' e => by
        have := hι e
        simp only [cxSpares, CxReg.spare.injEq] at this
        exact Fin.castLE_injective hk this,
      fun r r' e => hrsp r r' (hι e), fun r e => hrst r (hι e),
      fun r e => by simp [cxSpares] at e; exact absurd (hι e) (by simp)⟩
  obtain ⟨v₂, hu₂, hsc₂, he₂⟩ := codePass_exec body hlay C L vals v₁ { S with R := R₁ } hrs
    (fun r => by
      simp only [hR₁]
      rw [Function.update_of_ne (hne (by simp [cxSpares])),
        Function.update_of_ne (hne (by simp [cxSpares]))]
      exact hsp r)
  obtain ⟨v₃, hu₃, hsc₃, he₃⟩ := bclear_exec body (ι .g1) v₂ { S with R := R₁ }
  obtain ⟨v₄, hu₄, hsc₄, he₄⟩ := bclear_exec body (ι .s1) v₃
    { S with R := Function.update R₁ (ι .g1) [] }
  have hfin : ({ S with R := Function.update (Function.update R₁ (ι .g1) []) (ι .s1) [] } :
      Stacks T A) = S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext x
    simp only [hR₁]
    by_cases h1 : x = ι .s1
    · subst h1; simp [hs1]
    by_cases h2 : x = ι .g1
    · subst h2; simp [hg, Function.update_of_ne (hne (show CxReg.g1 ≠ .s1 by decide))]
    simp [Function.update_of_ne h1, Function.update_of_ne h2]
  have hlen₁ : (R₁ (ι .g1)).length ≤ ss.length := by
    simp only [hR₁, Function.update_of_ne (hne (show CxReg.g1 ≠ .s1 by decide)),
      Function.update_self, List.length_map]
    exact length_gatherL_le ss ma
  have hlen₂ : (Function.update R₁ (ι .g1) [] (ι .s1)).length = mb.length := by
    simp [hR₁, Function.update_of_ne (hne (show CxReg.s1 ≠ .g1 by decide)), length_spreadL]
  refine ⟨v₄, m₁ + ((6 * L + 4) + ((2 * (R₁ (ι .g1)).length + 2) +
    (2 * (Function.update R₁ (ι .g1) [] (ι .s1)).length + 2))),
    by rw [hu₄, hu₃, hu₂, hu₁], by rw [hlen₂]; omega, by rw [hsc₄, hsc₃, hsc₂],
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.cast he₄ rfl (by rw [hfin]))))⟩

end Code

/-! ### The index state -/

section Inv

variable {p ι len}

theorem cxInv_frame {R R' : Fin T → List (Fin (A + 4))} {i : ℕ} (hI : CxInv p ι len R i)
    (hR : ∀ k, CxIdx ι k → R' k = R k) : CxInv p ι len R' i := by
  obtain ⟨h1, h2, h3, h4, hk, h5, h6, h7, h8, h9, h10, h11⟩ := hI
  have e : ∀ x : CxReg, x.isIdx → R' (ι x) = R (ι x) := fun x hx => hR _ ⟨x, hx, rfl⟩
  exact ⟨fun g => (e (.fld g) trivial).trans (h1 g), (e .mSel trivial).trans h2,
    (e .mC trivial).trans h3, (e .mA trivial).trans h4, (e .mMk trivial).trans hk,
    (e .g1 trivial).trans h5,
    (e .s1 trivial).trans h6, (e .s2 trivial).trans h7, (e .gts trivial).trans h8,
    (e .gtm trivial).trans h9, (e .gdst trivial).trans h10,
    fun r => (e (.spare r) trivial).trans (h11 r)⟩

theorem cxInv_reidx (hι : Function.Injective ι) {R R' : Fin T → List (Fin (A + 4))} {i j : ℕ}
    (hI : CxInv p ι len R i)
    (hcf : ∀ g, R' (ι (.fld g)) = binSyms (len g) (digit len g j))
    (hR : ∀ k, (∀ g, k ≠ ι (.fld g)) → R' k = R k) : CxInv p ι len R' j := by
  obtain ⟨-, h2, h3, h4, hk, h5, h6, h7, h8, h9, h10, h11⟩ := hI
  have e : ∀ x : CxReg, (∀ g, x ≠ .fld g) → R' (ι x) = R (ι x) :=
    fun x hx => hR _ (fun g e => hx g (hι e))
  exact ⟨hcf, (e .mSel (by simp)).trans h2, (e .mC (by simp)).trans h3,
    (e .mA (by simp)).trans h4, (e .mMk (by simp)).trans hk, (e .g1 (by simp)).trans h5,
    (e .s1 (by simp)).trans h6,
    (e .s2 (by simp)).trans h7, (e .gts (by simp)).trans h8, (e .gtm (by simp)).trans h9,
    (e .gdst (by simp)).trans h10, fun r => (e (.spare r) (by simp)).trans (h11 r)⟩

/-- The contract of `codeGS` over the index state: the source and the two masks hold bit lists
determined by the index, and after the gather and the spread the code-pass registers hold the
values `vals i`. -/
theorem codeGS_spec (hι : Function.Injective ι) {k : ℕ} [NeZero k] {hk : k ≤ 4}
    {xs xa xb : CxReg} {rs : Fin k → CxReg} (h : CodeGSRegs ι hk xs xa xb rs) {nd : ℕ}
    (C : CAuto A k nd) (L : ℕ) (sbits abits bbits : ℕ → List Bool)
    (hS : ∀ (R : Fin T → List (Fin (A + 4))) i, CxInv p ι len R i →
      R (ι xs) = (sbits i).map bitSymbol ∧
      R (ι xa) = (abits i).map bitSymbol ∧ R (ι xb) = (bbits i).map bitSymbol)
    (hl : ∀ i, (abits i).length = (sbits i).length)
    (hc : ∀ i, (bbits i).count true = (gatherL (sbits i) (abits i)).length)
    (vals : ℕ → Fin k → ℕ)
    (hrs : ∀ (R : Fin T → List (Fin (A + 4))) i, CxInv p ι len R i → ∀ r,
      Function.update (Function.update R (ι .g1)
      ((gatherL (sbits i) (abits i)).map bitSymbol)) (ι .s1)
      ((spreadL (gatherL (sbits i) (abits i)) (bbits i)).map bitSymbol) (ι (rs r)) =
        binSyms L (vals i r))
    (c : ℕ) (hcost : ∀ i, 8 * (abits i).length + 8 * (bbits i).length + 6 * L +
      2 * (sbits i).length + 2 * (bbits i).length + 24 ≤ c) :
    CodeSpec body (codeGS (ι := ι) hk xs xa xb rs C) (fun g => ι (.fld g)) len (ι .st) (CxIdx ι)
      (CxInv p ι len) (codeSel C) (fun i => C.eval L (vals i)) c where
  runs i v S hI := by
    obtain ⟨hs, ha, hb⟩ := hS S.R i hI
    obtain ⟨-, -, -, -, -, hg, hs1, -, hts, htm, hdst, hsp⟩ := id hI
    obtain ⟨v', m, hu, hm, hsc, he⟩ := codeGS_run h C (sbits i) (abits i) (bbits i) (hl i) (hc i) L
      (vals i) v S hs ha hb hg hs1 hts htm hdst (fun r => hsp _) (hrs S.R i hI)
    exact ⟨v', m, hu, hm.trans (hcost i), by rw [hsc, codeSel_val]; rfl, he⟩
  cf_inj := fun g g' e => by simpa using hι e
  cf_Y := fun g => ⟨.fld g, trivial, rfl⟩
  digits := fun R i hI => hI.1
  frame := fun R R' i hI hR => cxInv_frame hI hR
  reidx := fun R R' i j hI hcf hR => cxInv_reidx hι hI hcf hR

end Inv

end IntegerMultBounds.MathlibTM2.Node
