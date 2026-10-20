module

public import IntegerMultBounds.MathlibTM2.Node.CompactCode

/-!
# The wrap-class programs of the compact rotations

For the gadget fields `F` (`IntegerMultBounds.MathlibTM2.Layer.CompactGadget.Fields`) on the index
fields of `CxReg`, the code programs of the four offsets read by gathering and spreading:

* `codeZ`: the controls `u_{c G}` spread to the selected bits of `y`, beside `y`;
* `codeY`, `codeX`: the selected bits of `y` or `x` spread to the digit starts, beside `b`;
* `codeYZ`: the selected bits of `y` spread to the digit starts, beside `b`, `u` and the
  digit-start mask.

`codeZ_spec` and its companions: from the index state at `i`, the program leaves the code
`C.eval` of the target digit and the offset `Off.eval p o (view len F i)` in the code slot.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {p : Par} {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U}
variable {ι : CxReg → Fin T} {len : Fin 10 → ℕ} (F : Fields 10)

/-- The code program of `Off.Z`, on the target `y`. -/
def codeZ {nd : ℕ} (C : CAuto A 2 nd) : Pr P T Q A U :=
  codeGS (ι := ι) (k := 2) (by decide) (.fld F.u) .mC .mSel ![.fld F.y, .s1] C

/-- The code program of `Off.Y`, on the target `b`. -/
def codeY {nd : ℕ} (C : CAuto A 2 nd) : Pr P T Q A U :=
  codeGS (ι := ι) (k := 2) (by decide) (.fld F.y) .mSel .mC ![.fld F.b, .s1] C

/-- The code program of `Off.X`, on the target `b`. -/
def codeX {nd : ℕ} (C : CAuto A 2 nd) : Pr P T Q A U :=
  codeGS (ι := ι) (k := 2) (by decide) (.fld F.x) .mSel .mC ![.fld F.b, .s1] C

/-- The code program of `Off.YZ`, on the target `b`. -/
def codeYZ {nd : ℕ} (C : CAuto A 4 nd) : Pr P T Q A U :=
  codeGS (ι := ι) (k := 4) le_rfl (.fld F.y) .mSel .mC ![.fld F.b, .s1, .fld F.u, .mC] C

variable {F}

lemma cxInv_fld {R : Fin T → List (Fin (A + 4))} {i : ℕ} (hI : CxInv p ι len R i) (g : Fin 10) :
    R (ι (.fld g)) = (binBits (len g) (digit len g i)).map bitSymbol := by
  rw [hI.1 g, binSyms_eq]

lemma cxInv_mSel {R : Fin T → List (Fin (A + 4))} {i : ℕ} (hI : CxInv p ι len R i) :
    R (ι .mSel) = (binBits p.wy (selV p)).map bitSymbol := by
  rw [hI.2.1, binSyms_eq]

lemma cxInv_mC {R : Fin T → List (Fin (A + 4))} {i : ℕ} (hI : CxInv p ι len R i) :
    R (ι .mC) = (binBits p.wc (mCV p)).map bitSymbol := by
  rw [hI.2.2.1, binSyms_eq]

/-- Gathered controls. -/
lemma gather_u (hG : 0 < p.G) (hF : F.Valid p len) (i : ℕ) :
    gatherL (binBits (len F.u) (digit len F.u i)) (binBits p.wc (mCV p)) =
      List.ofFn fun c : Fin p.n => (digit len F.u i).testBit (posC p c) := by
  rw [hF.lu]
  exact gatherL_mask (posC_mono hG) (fun c hc => by
    unfold posC Par.wc; exact Nat.mul_lt_mul_of_pos_right hc hG) _

/-- Gathered selected bits of a slot field. -/
lemma gather_slot (hK : 0 < p.K) {g : Fin 10} (hg : len g = p.wy) (i : ℕ) :
    gatherL (binBits (len g) (digit len g i)) (binBits p.wy (selV p)) =
      List.ofFn fun c : Fin p.n => (digit len g i).testBit (posS p c) := by
  rw [hg]
  exact gatherL_mask (posS_mono hK) (fun c hc => by
    unfold posS Par.wy; nlinarith) _

lemma count_selV (hK : 0 < p.K) : (binBits p.wy (selV p)).count true = p.n :=
  count_maskVal (posS_mono hK) fun c hc => by unfold posS Par.wy; nlinarith

lemma count_mCV (hG : 0 < p.G) : (binBits p.wc (mCV p)).count true = p.n :=
  count_maskVal (posC_mono hG) fun c hc => by
    unfold posC Par.wc; exact Nat.mul_lt_mul_of_pos_right hc hG

lemma spread_selV (hK : 0 < p.K) (b : ℕ → Bool) :
    spreadL (List.ofFn fun c : Fin p.n => b c) (binBits p.wy (selV p)) =
      binBits p.wy (placeVal p.n (posS p) b) :=
  spreadL_mask (posS_mono hK) (fun c hc => by unfold posS Par.wy; nlinarith) b

lemma spread_mCV (hG : 0 < p.G) (b : ℕ → Bool) :
    spreadL (List.ofFn fun c : Fin p.n => b c) (binBits p.wc (mCV p)) =
      binBits p.wc (placeVal p.n (posC p) b) :=
  spreadL_mask (posC_mono hG) (fun c hc => by
    unfold posC Par.wc; exact Nat.mul_lt_mul_of_pos_right hc hG) b

/-- **The code program of `Off.Z`.** -/
theorem codeZ_spec (hι : Function.Injective ι) (hF : F.Valid p len) (hK : 0 < p.K)
    (hG : 0 < p.G) {nd : ℕ} (C : CAuto A 2 nd) :
    CodeSpec body (codeZ (ι := ι) F C) (fun g => ι (.fld g)) len (ι .st) (CxIdx ι)
      (CxInv p ι len) (codeSel C)
      (fun i => C.eval p.wy ![digit len F.y i, Off.eval p .Z (view len F i)])
      (10 * p.wc + 16 * p.wy + 24) := by
  refine codeGS_spec (body := body) hι ⟨hι, by simp, by simp, by simp, ?_, ?_, ?_⟩ C p.wy
    (fun i => binBits (len F.u) (digit len F.u i)) (fun _ => binBits p.wc (mCV p))
    (fun _ => binBits p.wy (selV p))
    (fun R i hI => ⟨cxInv_fld hI _, cxInv_mC hI, cxInv_mSel hI⟩)
    (fun i => by simp [hF.lu]) (fun i => by rw [gather_u hG hF, count_selV hK]; simp) _
    (fun R i hI r => ?_) _ (fun i => by simp [hF.lu]; omega)
  · intro r r' e; fin_cases r <;> fin_cases r' <;> simp_all
  · intro r r'; fin_cases r <;> simp [cxSpares]
  · intro r; fin_cases r <;> simp
  · fin_cases r
    · show Function.update _ _ _ (ι (.fld F.y)) = _
      rw [Function.update_of_ne (hι.ne (by simp)), Function.update_of_ne (hι.ne (by simp)),
        hI.1, hF.ly]
      rfl
    · show Function.update _ _ _ (ι .s1) = _
      rw [Function.update_self, gather_u hG hF,
        spread_selV hK (fun c => (digit len F.u i).testBit (posC p c)), ← binSyms_eq, offZ_eq hG]
      rfl

/-- **The code program of `Off.Y`.** -/
theorem codeY_spec (hι : Function.Injective ι) (hF : F.Valid p len) (hK : 0 < p.K)
    (hG : 0 < p.G) {nd : ℕ} (C : CAuto A 2 nd) :
    CodeSpec body (codeY (ι := ι) F C) (fun g => ι (.fld g)) len (ι .st) (CxIdx ι)
      (CxInv p ι len) (codeSel C)
      (fun i => C.eval p.wc ![digit len F.b i, Off.eval p .Y (view len F i)])
      (16 * p.wc + 10 * p.wy + 24) := by
  refine codeGS_spec (body := body) hι ⟨hι, by simp, by simp, by simp, ?_, ?_, ?_⟩ C p.wc
    (fun i => binBits (len F.y) (digit len F.y i)) (fun _ => binBits p.wy (selV p))
    (fun _ => binBits p.wc (mCV p))
    (fun R i hI => ⟨cxInv_fld hI _, cxInv_mSel hI, cxInv_mC hI⟩)
    (fun i => by simp [hF.ly]) (fun i => by rw [gather_slot hK hF.ly, count_mCV hG]; simp) _
    (fun R i hI r => ?_) _ (fun i => by simp [hF.ly]; omega)
  · intro r r' e; fin_cases r <;> fin_cases r' <;> simp_all
  · intro r r'; fin_cases r <;> simp [cxSpares]
  · intro r; fin_cases r <;> simp
  · fin_cases r
    · show Function.update _ _ _ (ι (.fld F.b)) = _
      rw [Function.update_of_ne (hι.ne (by simp)), Function.update_of_ne (hι.ne (by simp)),
        hI.1, hF.lb]
      rfl
    · show Function.update _ _ _ (ι .s1) = _
      rw [Function.update_self, gather_slot hK hF.ly,
        spread_mCV hG (fun c => (digit len F.y i).testBit (posS p c)), ← binSyms_eq, offY_eq hK]
      rfl

/-- **The code program of `Off.X`.** -/
theorem codeX_spec (hι : Function.Injective ι) (hF : F.Valid p len) (hK : 0 < p.K)
    (hG : 0 < p.G) {nd : ℕ} (C : CAuto A 2 nd) :
    CodeSpec body (codeX (ι := ι) F C) (fun g => ι (.fld g)) len (ι .st) (CxIdx ι)
      (CxInv p ι len) (codeSel C)
      (fun i => C.eval p.wc ![digit len F.b i, Off.eval p .X (view len F i)])
      (16 * p.wc + 10 * p.wy + 24) := by
  refine codeGS_spec (body := body) hι ⟨hι, by simp, by simp, by simp, ?_, ?_, ?_⟩ C p.wc
    (fun i => binBits (len F.x) (digit len F.x i)) (fun _ => binBits p.wy (selV p))
    (fun _ => binBits p.wc (mCV p))
    (fun R i hI => ⟨cxInv_fld hI _, cxInv_mSel hI, cxInv_mC hI⟩)
    (fun i => by simp [hF.lx]) (fun i => by rw [gather_slot hK hF.lx, count_mCV hG]; simp) _
    (fun R i hI r => ?_) _ (fun i => by simp [hF.lx]; omega)
  · intro r r' e; fin_cases r <;> fin_cases r' <;> simp_all
  · intro r r'; fin_cases r <;> simp [cxSpares]
  · intro r; fin_cases r <;> simp
  · fin_cases r
    · show Function.update _ _ _ (ι (.fld F.b)) = _
      rw [Function.update_of_ne (hι.ne (by simp)), Function.update_of_ne (hι.ne (by simp)),
        hI.1, hF.lb]
      rfl
    · show Function.update _ _ _ (ι .s1) = _
      rw [Function.update_self, gather_slot hK hF.lx,
        spread_mCV hG (fun c => (digit len F.x i).testBit (posS p c)), ← binSyms_eq, offX_eq hK]
      rfl

/-- **The code program of `Off.YZ`.** -/
theorem codeYZ_spec (hι : Function.Injective ι) (hF : F.Valid p len) (hK : 0 < p.K)
    (hG : 0 < p.G) {nd : ℕ} (C : CAuto A 4 nd) :
    CodeSpec body (codeYZ (ι := ι) F C) (fun g => ι (.fld g)) len (ι .st) (CxIdx ι)
      (CxInv p ι len) (codeSel C)
      (fun i => C.eval p.wc ![digit len F.b i,
        placeVal p.n (posC p) (fun c => (digit len F.y i).testBit (posS p c)),
        digit len F.u i, mCV p])
      (16 * p.wc + 10 * p.wy + 24) := by
  refine codeGS_spec (body := body) hι ⟨hι, by simp, by simp, by simp, ?_, ?_, ?_⟩ C p.wc
    (fun i => binBits (len F.y) (digit len F.y i)) (fun _ => binBits p.wy (selV p))
    (fun _ => binBits p.wc (mCV p))
    (fun R i hI => ⟨cxInv_fld hI _, cxInv_mSel hI, cxInv_mC hI⟩)
    (fun i => by simp [hF.ly]) (fun i => by rw [gather_slot hK hF.ly, count_mCV hG]; simp) _
    (fun R i hI r => ?_) _ (fun i => by simp [hF.ly]; omega)
  · have hbu := hbu hF
    intro r r' e; fin_cases r <;> fin_cases r' <;> simp_all
  · intro r r'; fin_cases r <;> simp [cxSpares]
  · intro r; fin_cases r <;> simp
  · fin_cases r
    · show Function.update _ _ _ (ι (.fld F.b)) = _
      rw [Function.update_of_ne (hι.ne (by simp)), Function.update_of_ne (hι.ne (by simp)),
        hI.1, hF.lb]
      rfl
    · show Function.update _ _ _ (ι .s1) = _
      rw [Function.update_self, gather_slot hK hF.ly,
        spread_mCV hG (fun c => (digit len F.y i).testBit (posS p c)), ← binSyms_eq]
      rfl
    · show Function.update _ _ _ (ι (.fld F.u)) = _
      rw [Function.update_of_ne (hι.ne (by simp)), Function.update_of_ne (hι.ne (by simp)),
        hI.1, hF.lu]
      rfl
    · show Function.update _ _ _ (ι .mC) = _
      rw [Function.update_of_ne (hι.ne (by simp)), Function.update_of_ne (hι.ne (by simp)),
        hI.2.2.1]
      rfl

/-- The masked-XOR automaton reads `Off.YZ`. -/
theorem offv_rXor_YZ (hK : 0 < p.K) (hG : 0 < p.G) (v : V) (_hu : v.u < 2 ^ p.wc) :
    offv rXor p.wc false ![v.b, placeVal p.n (posC p) (fun c => v.y.testBit (posS p c)), v.u,
      mCV p] = Off.eval p .YZ v := by
  rw [offYZ_eq hK hG]
  apply Nat.eq_of_testBit_eq
  intro q
  rw [congrFun (offv_rXor _ _ _ _ _) q, testBit_placeVal (posC_mono hG), mCV,
    Layer.CompactMasks.testBit_maskVal (posC_mono hG), testBit_placeVal (posC_mono hG)]
  by_cases hq : ∃ c < p.n, posC p c = q
  · obtain ⟨c, hc, rfl⟩ := hq
    have hinj := (posC_mono (p := p) hG).injective
    have hlt : posC p c < p.wc := by unfold posC Par.wc; exact Nat.mul_lt_mul_of_pos_right hc hG
    have e1 : decide (∃ c' < p.n, posC p c' = posC p c ∧ v.y.testBit (posS p c') = true) =
        v.y.testBit (posS p c) := by
      cases h : v.y.testBit (posS p c)
      · simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro c' _ e; rw [hinj e, h]; simp
      · simp only [decide_eq_true_eq]; exact ⟨c, hc, rfl, h⟩
    have e2 : decide (∃ c' < p.n, posC p c' = posC p c ∧
        xor (v.y.testBit (posS p c')) (v.u.testBit (posC p c')) = true) =
        xor (v.y.testBit (posS p c)) (v.u.testBit (posC p c)) := by
      cases h : xor (v.y.testBit (posS p c)) (v.u.testBit (posC p c))
      · simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro c' _ e; rw [hinj e, h]; simp
      · simp only [decide_eq_true_eq]; exact ⟨c, hc, rfl, h⟩
    rw [e1, e2]
    simp [hlt, show ∃ c' < p.n, posC p c' = posC p c from ⟨c, hc, rfl⟩]
  · have h1 : decide (∃ c < p.n, posC p c = q) = false := by simpa using hq
    have h2 : decide (∃ c < p.n, posC p c = q ∧
        xor (v.y.testBit (posS p c)) (v.u.testBit (posC p c)) = true) = false := by
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      exact fun c hc e _ => hq ⟨c, hc, e⟩
    rw [h1, h2]
    simp

variable (F) in
/-- The code-pass registers of `Off.A`. -/
def rsA : Fin 4 → CxReg := ![.fld F.y, .s2, .s1, .mSel]

variable (F) in
/-- The code program of `Off.A`, on the target `y`: the controls spread to the selected bits
(`s1`), the temporary spread above them (`s2`). -/
def codeA {nd : ℕ} (C : CAuto A 4 nd) : Pr P T Q A U :=
  .seq (gsProg (ι (.fld F.u)) (ι .mC) (ι .mSel) (ι .g1) (ι .s1) (ι .gts) (ι .gtm) (ι .gdst) (ι .st))
    (.seq (spread (ι (.fld F.t)) (ι .mA) (ι .gts) (ι .gtm) (ι .gdst) (ι .s2))
      (.seq (codePass (fun r => ι (rsA F r)) (fun r => ι (.spare r)) (ι .st) C)
        (.seq (bclear (ι .g1)) (.seq (bclear (ι .s1)) (bclear (ι .s2))))))

lemma spread_mAV (hG : 0 < p.G) (hGK : p.G < p.K) (t : ℕ) :
    spreadL (binBits p.wc t) (binBits p.wy (mAV p)) =
      binBits p.wy (placeVal (p.n * p.G) (posA p) fun j => t.testBit j) :=
  spreadL_mask (posA_mono hG hGK) (fun _ hj => posA_lt hG hGK hj) _

/-- **The code program of `Off.A`.** -/
theorem codeA_spec (hι : Function.Injective ι) (hF : F.Valid p len) (hK : 0 < p.K)
    (hG : 0 < p.G) (hGK : p.G < p.K) {nd : ℕ} (C : CAuto A 4 nd) :
    CodeSpec body (codeA (ι := ι) F C) (fun g => ι (.fld g)) len (ι .st) (CxIdx ι)
      (CxInv p ι len) (codeSel C)
      (fun i => C.eval p.wy ![digit len F.y i,
        placeVal (p.n * p.G) (posA p) (fun j => (digit len F.t i).testBit j),
        placeVal p.n (posS p) (fun c => (digit len F.u i).testBit (posC p c)), selV p])
      (20 * p.wc + 34 * p.wy + 40) where
  runs i v S hI := by
    have hne : ∀ {x y : CxReg}, x ≠ y → ι x ≠ ι y := fun hxy => hι.ne hxy
    obtain ⟨hfld, hsel, hmc, hma, -, hg1, hs1, hs2, hts, htm, hdst, hsp⟩ := id hI
    have h₁ : GSRegs (ι (.fld F.u)) (ι .mC) (ι .gts) (ι .gtm) (ι .gdst) (ι .g1) := by
      simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true, hι.eq_iff]; simp
    have h₂ : GSRegs (ι .g1) (ι .mSel) (ι .gts) (ι .gtm) (ι .gdst) (ι .s1) := by
      simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true, hι.eq_iff]; simp
    have h₃ : GSRegs (ι (.fld F.t)) (ι .mA) (ι .gts) (ι .gtm) (ι .gdst) (ι .s2) := by
      simp only [GSRegs, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true, hι.eq_iff]; simp
    set gl := gatherL (binBits (len F.u) (digit len F.u i)) (binBits p.wc (mCV p)) with hgl
    obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := gsProg_exec (body := body) (cs := ι .st) h₁ h₂
      (binBits (len F.u) (digit len F.u i)) (binBits p.wc (mCV p)) (binBits p.wy (selV p))
      (by simp [hF.lu]) (by rw [gather_u hG hF, count_selV hK]; simp) v S
      (cxInv_fld hI _) (cxInv_mC hI) (cxInv_mSel hI) hg1 hs1 hts htm hdst
    set R₁ := Function.update (Function.update S.R (ι .g1) (gl.map bitSymbol)) (ι .s1)
      ((spreadL gl (binBits p.wy (selV p))).map bitSymbol) with hR₁
    have hk₁ : ∀ x : CxReg, x ≠ .g1 → x ≠ .s1 → R₁ (ι x) = S.R (ι x) := fun x h1 h2 => by
      rw [hR₁, Function.update_of_ne (hne h2), Function.update_of_ne (hne h1)]
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := spread_exec body h₃ (binBits p.wy (mAV p))
      (binBits p.wc (digit len F.t i))
      (by rw [mAV, count_maskVal (posA_mono hG hGK) (fun j hj => posA_lt hG hGK hj)]; simp [Par.wc])
      v₁ { S with R := R₁ }
      (by show R₁ _ = _; rw [hk₁ _ (by simp) (by simp), hma, binSyms_eq])
      (by show R₁ _ = _; rw [hk₁ _ (by simp) (by simp), cxInv_fld hI, hF.lt])
      (by show R₁ _ = _; rw [hk₁ _ (by simp) (by simp), hts])
      (by show R₁ _ = _; rw [hk₁ _ (by simp) (by simp), htm])
      (by show R₁ _ = _; rw [hk₁ _ (by simp) (by simp), hdst])
    set R₂ := Function.update R₁ (ι .s2) ((spreadL (binBits p.wc (digit len F.t i))
      (binBits p.wy (mAV p))).map bitSymbol ++ R₁ (ι .s2)) with hR₂
    have hk₂ : ∀ x : CxReg, x ≠ .g1 → x ≠ .s1 → x ≠ .s2 → R₂ (ι x) = S.R (ι x) :=
      fun x h1 h2 h3 => by rw [hR₂, Function.update_of_ne (hne h3), hk₁ x h1 h2]
    have hlay : CodeLayout (fun r => ι (rsA F r)) (fun r => ι (.spare r)) (ι .st) := by
      refine ⟨fun r r' e => ?_, fun r r' e => by simpa using hι e, fun r r' e => ?_,
        fun r e => ?_, fun r e => by simpa using hι e⟩
      · have := hι e; fin_cases r <;> fin_cases r' <;> simp_all [rsA]
      · have := hι e; fin_cases r <;> simp_all [rsA]
      · have := hι e; fin_cases r <;> simp_all [rsA]
    obtain ⟨v₃, hu₃, hsc₃, he₃⟩ := codePass_exec body hlay C p.wy ![digit len F.y i,
        placeVal (p.n * p.G) (posA p) (fun j => (digit len F.t i).testBit j),
        placeVal p.n (posS p) (fun c => (digit len F.u i).testBit (posC p c)), selV p]
      v₂ { S with R := R₂ }
      (fun r => by
        fin_cases r
        · show R₂ (ι (.fld F.y)) = binSyms p.wy (digit len F.y i)
          rw [hk₂ _ (by simp) (by simp) (by simp), hfld, hF.ly]
        · show R₂ (ι .s2) = binSyms p.wy
            (placeVal (p.n * p.G) (posA p) (fun j => (digit len F.t i).testBit j))
          rw [hR₂, Function.update_self, hk₁ _ (by simp) (by simp), hs2, List.append_nil,
            spread_mAV hG hGK, ← binSyms_eq]
        · show R₂ (ι .s1) = binSyms p.wy
            (placeVal p.n (posS p) (fun c => (digit len F.u i).testBit (posC p c)))
          rw [hR₂, Function.update_of_ne (hne (by simp)), hR₁, Function.update_self, hgl,
            gather_u hG hF, spread_selV hK (fun c => (digit len F.u i).testBit (posC p c)),
            ← binSyms_eq]
        · show R₂ (ι .mSel) = binSyms p.wy (selV p)
          rw [hk₂ _ (by simp) (by simp) (by simp), hsel])
      (fun r => by
        show R₂ _ = _
        rw [hk₂ _ (by simp) (by simp) (by simp), hsp])
    obtain ⟨v₄, hu₄, hsc₄, he₄⟩ := bclear_exec body (ι .g1) v₃ { S with R := R₂ }
    obtain ⟨v₅, hu₅, hsc₅, he₅⟩ := bclear_exec body (ι .s1) v₄
      { S with R := Function.update R₂ (ι .g1) [] }
    set R₃ := Function.update (Function.update R₂ (ι .g1) []) (ι .s1) [] with hR₃
    obtain ⟨v₆, hu₆, hsc₆, he₆⟩ := bclear_exec body (ι .s2) v₅ { S with R := R₃ }
    set R₄ := Function.update R₃ (ι .s2) [] with hR₄
    have hfin : ({ S with R := R₄ } : Stacks T A) = S := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      simp only [hR₄, hR₃]
      by_cases h3 : k = ι .s2
      · subst h3; simp [hs2]
      by_cases h2 : k = ι .s1
      · subst h2; simp [Function.update_of_ne (hne (show CxReg.s1 ≠ .s2 by decide)), hs1]
      by_cases h1 : k = ι .g1
      · subst h1
        simp [Function.update_of_ne (hne (show CxReg.g1 ≠ .s2 by decide)),
          Function.update_of_ne (hne (show CxReg.g1 ≠ .s1 by decide)), hg1]
      simp only [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1,
        hR₂, hR₁]
    refine ⟨v₆, m₁ + (m₂ + ((6 * p.wy + 4) + ((2 * (R₂ (ι .g1)).length + 2) +
      ((2 * (Function.update R₂ (ι .g1) [] (ι .s1)).length + 2) +
      (2 * (R₃ (ι .s2)).length + 2))))),
      by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_, by rw [hsc₆, hsc₅, hsc₄, hsc₃, codeSel_val]; rfl,
      Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅
        (Exec.cast he₆ rfl (by rw [hfin]))))))⟩
    have l1 : (R₂ (ι .g1)).length ≤ p.wc := by
      rw [hR₂, Function.update_of_ne (hne (by decide)), hR₁,
        Function.update_of_ne (hne (by decide)), Function.update_self, List.length_map]
      exact (length_gatherL_le _ _).trans (by simp [hF.lu])
    have l2 : (Function.update R₂ (ι .g1) [] (ι .s1)).length = p.wy := by
      rw [Function.update_of_ne (hne (by decide)), hR₂, Function.update_of_ne (hne (by decide)),
        hR₁, Function.update_self]
      simp [length_spreadL]
    have l3 : (R₃ (ι .s2)).length = p.wy := by
      rw [hR₃, Function.update_of_ne (hne (by decide)), Function.update_of_ne (hne (by decide)), hR₂,
        Function.update_self, hk₁ _ (by simp) (by simp), hs2]
      simp [length_spreadL]
    simp only [binBits, List.length_ofFn] at hm₁ hm₂
    rw [l2, l3]
    omega
  cf_inj := fun g g' e => by simpa using hι e
  cf_Y := fun g => ⟨.fld g, trivial, rfl⟩
  digits := fun R i hI => hI.1
  frame := fun R R' i hI hR => cxInv_frame hI hR
  reidx := fun R R' i j hI hcf hR => cxInv_reidx hι hI hcf hR

end IntegerMultBounds.MathlibTM2.Node
