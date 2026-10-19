module

public import IntegerMultBounds.MathlibTM2.Node.CompactRotCodes

/-!
# The code program of the bad states

`codeBad` spreads the digits of `u` and `t` to the positions `posA` of slot width (into `s1` and
`s2`), runs the bad-state automaton `badC` on `y`, the two spread fields and the phase mask `mMk`,
and clears the scratch. `codeBad_spec`: from the index state at `i` the code is `0` when the
fields of `i` are good (`GoodIdx`) and `1` otherwise.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {p : Par} {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U}
variable {ι : CxReg → Fin T} {len : Fin 10 → ℕ} (F : Fields 10)

/-- The code-pass registers of the bad-state code. -/
def rsBad : Fin 4 → CxReg := ![.fld F.y, .s1, .s2, .mMk]

/-- The code program of the bad states. -/
def codeBad (hA : 4 ≤ A) : Pr P T Q A U :=
  .seq (spread (ι (.fld F.u)) (ι .mA) (ι .gts) (ι .gtm) (ι .gdst) (ι .s1))
    (.seq (spread (ι (.fld F.t)) (ι .mA) (ι .gts) (ι .gtm) (ι .gdst) (ι .s2))
      (.seq (codePass (fun r => ι (rsBad F r)) (fun r => ι (.spare r)) (ι .st) (badC A hA))
        (.seq (bclear (ι .s1)) (bclear (ι .s2)))))

/-- **The code program of the bad states.** -/
theorem codeBad_spec (hι : Function.Injective ι) (hF : F.Valid p len) (hA : 4 ≤ A)
    (hG : 0 < p.G) (hGK : p.G + 1 < p.K) :
    CodeSpec body (codeBad (ι := ι) F hA) (fun g => ι (.fld g)) len (ι .st) (CxIdx ι)
      (CxInv p ι len) (codeSel (badC A hA))
      (fun i => (badC A hA).eval p.wy (badVals p (view len F i))) (26 * p.wy + 24) where
  runs i v S hI := by
    have hne : ∀ {x y : CxReg}, x ≠ y → ι x ≠ ι y := fun hxy => hι.ne hxy
    obtain ⟨hfld, hsel, hmc, hma, hmk, hg1, hs1, hs2, hts, htm, hdst, hsp⟩ := id hI
    have h₁ : GSRegs (ι (.fld F.u)) (ι .mA) (ι .gts) (ι .gtm) (ι .gdst) (ι .s1) := by
      simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true, hι.eq_iff]; simp
    have h₂ : GSRegs (ι (.fld F.t)) (ι .mA) (ι .gts) (ι .gtm) (ι .gdst) (ι .s2) := by
      simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true, hι.eq_iff]; simp
    have hcount : (binBits p.wy (mAV p)).count true = (binBits p.wc 0).length := by
      rw [mAV, count_maskVal (posA_mono hG (by omega)) (fun j hj => posA_lt hG (by omega) hj)]
      simp [Par.wc]
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := spread_exec body h₁ (binBits p.wy (mAV p))
      (binBits p.wc (digit len F.u i)) (by rw [hcount]; simp) v S (by rw [hma, binSyms_eq])
      (by rw [cxInv_fld hI, hF.lu]) hts htm hdst
    set R₁ := Function.update S.R (ι .s1) ((spreadL (binBits p.wc (digit len F.u i))
      (binBits p.wy (mAV p))).map bitSymbol ++ S.R (ι .s1)) with hR₁
    have hk₁ : ∀ x : CxReg, x ≠ .s1 → R₁ (ι x) = S.R (ι x) := fun x h => by
      rw [hR₁, Function.update_of_ne (hne h)]
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := spread_exec body h₂ (binBits p.wy (mAV p))
      (binBits p.wc (digit len F.t i)) (by rw [hcount]; simp) v₁ { S with R := R₁ }
      (by show R₁ _ = _; rw [hk₁ _ (by simp), hma, binSyms_eq])
      (by show R₁ _ = _; rw [hk₁ _ (by simp), cxInv_fld hI, hF.lt])
      (by show R₁ _ = _; rw [hk₁ _ (by simp), hts])
      (by show R₁ _ = _; rw [hk₁ _ (by simp), htm])
      (by show R₁ _ = _; rw [hk₁ _ (by simp), hdst])
    set R₂ := Function.update R₁ (ι .s2) ((spreadL (binBits p.wc (digit len F.t i))
      (binBits p.wy (mAV p))).map bitSymbol ++ R₁ (ι .s2)) with hR₂
    have hk₂ : ∀ x : CxReg, x ≠ .s1 → x ≠ .s2 → R₂ (ι x) = S.R (ι x) :=
      fun x h1 h2 => by rw [hR₂, Function.update_of_ne (hne h2), hk₁ x h1]
    have hlay : CodeLayout (fun r => ι (rsBad F r)) (fun r => ι (.spare r)) (ι .st) := by
      refine ⟨fun r r' e => ?_, fun r r' e => by simpa using hι e, fun r r' e => ?_,
        fun r e => ?_, fun r e => by simpa using hι e⟩
      · have := hι e; fin_cases r <;> fin_cases r' <;> simp_all [rsBad]
      · have := hι e; fin_cases r <;> simp_all [rsBad]
      · have := hι e; fin_cases r <;> simp_all [rsBad]
    obtain ⟨v₃, hu₃, hsc₃, he₃⟩ := codePass_exec body hlay (badC A hA) p.wy
      (badVals p (view len F i)) v₂ { S with R := R₂ }
      (fun r => by
        fin_cases r
        · show R₂ (ι (.fld F.y)) = binSyms p.wy (digit len F.y i)
          rw [hk₂ _ (by simp) (by simp), hfld, hF.ly]
        · show R₂ (ι .s1) = binSyms p.wy
            (placeVal (p.n * p.G) (posA p) (digit len F.u i).testBit)
          rw [hR₂, Function.update_of_ne (hne (by simp)), hR₁, Function.update_self, hs1,
            List.append_nil, spread_mAV hG (by omega), ← binSyms_eq]
        · show R₂ (ι .s2) = binSyms p.wy
            (placeVal (p.n * p.G) (posA p) (digit len F.t i).testBit)
          rw [hR₂, Function.update_self, hk₁ _ (by simp), hs2, List.append_nil,
            spread_mAV hG (by omega), ← binSyms_eq]
        · show R₂ (ι .mMk) = binSyms p.wy (mkV p)
          rw [hk₂ _ (by simp) (by simp), hmk])
      (fun r => by
        show R₂ _ = _
        rw [hk₂ _ (by simp) (by simp), hsp])
    obtain ⟨v₄, hu₄, hsc₄, he₄⟩ := bclear_exec body (ι .s1) v₃ { S with R := R₂ }
    set R₃ := Function.update R₂ (ι .s1) [] with hR₃
    obtain ⟨v₅, hu₅, hsc₅, he₅⟩ := bclear_exec body (ι .s2) v₄ { S with R := R₃ }
    set R₄ := Function.update R₃ (ι .s2) [] with hR₄
    have hfin : ({ S with R := R₄ } : Stacks T A) = S := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      simp only [hR₄, hR₃]
      by_cases h2 : k = ι .s2
      · subst h2; simp [hs2]
      by_cases h1 : k = ι .s1
      · subst h1; simp [Function.update_of_ne (hne (show CxReg.s1 ≠ .s2 by decide)), hs1]
      simp only [Function.update_of_ne h2, Function.update_of_ne h1, hR₂, hR₁]
    refine ⟨v₅, m₁ + (m₂ + ((6 * p.wy + 4) + ((2 * (R₂ (ι .s1)).length + 2) +
      (2 * (R₃ (ι .s2)).length + 2)))),
      by rw [hu₅, hu₄, hu₃, hu₂, hu₁], ?_, by rw [hsc₅, hsc₄, hsc₃, codeSel_val]; rfl,
      Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄
        (Exec.cast he₅ rfl (by rw [hfin])))))⟩
    have l1 : (R₂ (ι .s1)).length = p.wy := by
      rw [hR₂, Function.update_of_ne (hne (by decide)), hR₁, Function.update_self, hs1]
      simp [length_spreadL]
    have l2 : (R₃ (ι .s2)).length = p.wy := by
      rw [hR₃, Function.update_of_ne (hne (by decide)), hR₂, Function.update_self,
        hk₁ _ (by simp), hs2]
      simp [length_spreadL]
    simp only [binBits, List.length_ofFn] at hm₁ hm₂
    rw [l1, l2]
    omega
  cf_inj := fun g g' e => by simpa using hι e
  cf_Y := fun g => ⟨.fld g, trivial, rfl⟩
  digits := fun R i hI => hI.1
  frame := fun R R' i hI hR => cxInv_frame hI hR
  reidx := fun R R' i j hI hcf hR => cxInv_reidx hι hI hcf hR

open Classical in
/-- The code of the bad states is `0` exactly on good indices. -/
lemma badCode_eq (hA : 4 ≤ A) (hG : 0 < p.G) (hGK : p.G + 1 < p.K) (hm : 0 < p.m) (i : ℕ) :
    (badC A hA).eval p.wy (badVals p (view len F i)) = if GoodIdx p len F i then 0 else 1 :=
  badC_eval hA hG hGK hm _

end IntegerMultBounds.MathlibTM2.Node
