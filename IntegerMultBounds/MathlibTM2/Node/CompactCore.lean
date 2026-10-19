module

public import IntegerMultBounds.MathlibTM2.Node.CompactProg
public import IntegerMultBounds.MathlibTM2.Node.CompactKeyPass
public import IntegerMultBounds.MathlibTM2.Node.CompactFixPass
public import IntegerMultBounds.MathlibTM2.Node.RepairPass

/-!
# The compact selected-bit XOR on a record stream

`cxCore` runs, on the stream register `ι .src` of the compact registers:

1. the key pass (`cxKey_exec`): every record gains the index of its destination under the ideal
   map `xorIdx sel` (`sel` the selected bits of the used segments), as `fieldsLen len` bits;
2. the passes of the gadget program (`progPass_exec`), which agree with the ideal map on good
   indices (`runIdx_prog_good`);
3. the repair (`repairAtC_exec` with the bad-state code `codeBad`): the records at bad
   destinations are radix sorted by their keys into place, and the keys are stripped;
4. the fix of the top column (`cxFix_exec`).

`cxCore_exec`: the records end moved by `xorIdx sel` and then `xorIdx 2^P`, `P = posS n`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactMasks IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.Compact (badRanks)

variable {p : Par} {T Q K : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q (prime + K) U}
  {ι : CxReg → Fin T} {len : Fin 10 → ℕ} (F : Fields 10)

/-! ### The key pass on the compact registers -/

lemma cx_keyRegs (hι : Function.Injective ι) :
    KeyRegs (ι .src) (ι .out) (ι .ctrB) (ι .tmp) (ι .mSel) (ι (.kt 0)) (ι (.kt 1)) (ι (.kt 2))
      (ι .st) (fun g => ι (.fld g)) := by
  have hne : ∀ {x y : CxReg}, x ≠ y → ι x ≠ ι y := fun h => hι.ne h
  exact {
    cf_inj := fun g g' e => by simpa using hι e
    cf_ne := fun g => by simp [hι.eq_iff]
    cf_st := fun g => hne (by simp)
    cm_st := hne (by simp)
    nd := by simp [hι.eq_iff]
    cf_src := fun g => hne (by simp)
    cf_ctr := fun g => hne (by simp)
    cf_tmp := fun g => hne (by simp)
    src_acc := hne (by simp)
    src_ctr := hne (by simp)
    src_tmp := hne (by simp)
    acc_ctr := hne (by simp)
    acc_tmp := hne (by simp)
    ctr_tmp := hne (by simp)
    src_cm := hne (by simp)
    src_t0 := hne (by simp)
    src_t1 := hne (by simp)
    src_t2 := hne (by simp)
    ctr_cm := hne (by simp)
    ctr_t0 := hne (by simp)
    ctr_t1 := hne (by simp)
    ctr_t2 := hne (by simp)
    tmp_cm := hne (by simp)
    tmp_t0 := hne (by simp)
    tmp_t1 := hne (by simp)
    tmp_t2 := hne (by simp) }

variable (ι) in
/-- The key pass on the compact registers. -/
noncomputable def cxKeyPass : Pr P T Q (prime + K) U :=
  keyPassAt F.y F.x (ι .src) (ι .out) (ι .ctrB) (ι .tmp) (ι .mSel) (ι (.kt 0)) (ι (.kt 1))
    (ι (.kt 2)) (ι .st) (fun g => ι (.fld g))

variable (ι) in
/-- The repair on the compact registers, with the bad-state code. -/
noncomputable def cxRepair (hA : 4 ≤ prime + K) : Pr P T Q (prime + K) U :=
  repairAtC (codeBad (ι := ι) F hA) (codeSel (badC (prime + K) hA)) (ι .src) (ι (.dst 0))
    (ι (.dst 1)) (ι (.aux 0)) (ι (.aux 1)) (ι .ctr) (ι .ctrB) (ι .ctrK) (ι .cnt) (ι .tmp) (ι .st)
    (fun g => ι (.fld g)) (fun r => ι (.spare r))

variable (ι) in
/-- The fix of the top column on the compact registers. -/
noncomputable def cxFix : Pr P T Q (prime + K) U :=
  fixAtC (codeTop (ι := ι) F (topInAuto (prime + K))) (codeSel (topInAuto (prime + K)))
    (codeTop (ι := ι) F (topOutAuto (prime + K))) (codeSel (topOutAuto (prime + K)))
    (ι .src) (ι (.fr 0)) (ι (.fr 1)) (ι (.fr 2)) (ι (.fr 3)) (ι (.fq 0)) (ι (.fq 1)) (ι (.fq 2))
    (ι (.fq 3)) (ι .ctrB) (ι .cnt) (ι .tmp) (ι .st) (fun g => ι (.fld g))

variable {bank : Fin 2 → Fin (swapT 6) → Fin T}

variable (ι) in
/-- **The compact selected-bit XOR on the record stream.** -/
noncomputable def cxCore (hA : 4 ≤ prime + K) (hb : Banks ι bank)
    (hQ : swapStates cxHd cxPay cxHd_inj ≤ Q) (hT : swapT 6 ≤ T) : Pr P T Q (prime + K) U :=
  .seq (cxKeyPass ι F) (.seq (progPass (ι := ι) F hb hQ hT) (.seq (cxRepair ι F hA) (cxFix ι F)))

/-- The non-index registers are not index registers. -/
lemma not_cxIdx (hι : Function.Injective ι) {x : CxReg} (hx : ¬ x.isIdx) : ¬ CxIdx ι (ι x) :=
  fun ⟨_, hy, e⟩ => hx (hι e ▸ hy)

lemma mem_keyRecs_sym {A M k : ℕ} {π : Equiv.Perm (Fin M)} {l : List (List (Fin (A + 4)))}
    (hl : l.length = M) (h8 : ∀ r ∈ l, ∀ s ∈ r, s.val < 8) :
    ∀ r ∈ keyRecs k π l, ∀ s ∈ r, s.val < 8 := by
  intro r hr s hs
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hr
  rcases List.mem_append.1 hs with hs | hs
  · rw [binSyms_eq] at hs
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hs
    cases b <;> simp [bitSymbol]
  · have hj : (j : ℕ) < l.length := by rw [hl]; exact j.isLt
    rw [List.getD_eq_getElem _ _ hj] at hs
    exact h8 _ (List.getElem_mem hj) s hs

variable (p) in
/-- The target of the compact selected-bit XOR on ranks: the masked exclusive or with the
selected bits of the used segments, then with the top selected bit. -/
def cxPerm {nf : ℕ} {len : Fin nf → ℕ} {F : Fields nf} (hF : F.Valid p len) {q R : ℕ}
    (hq : ∀ g, touched F g → fieldOff len g + len g ≤ q) : Equiv.Perm (Fin (R * 2 ^ q)) :=
  (xorPerm hF.xorFields (hq F.y (Or.inr (Or.inr (Or.inr rfl)))) (Layer.CompactMasks.maskVal p.n (posS p))).trans
    (xorPerm hF.xorFields (hq F.y (Or.inr (Or.inr (Or.inr rfl)))) (2 ^ posS p p.n))

open Classical in
variable (p len) in
/-- The step bound of `cxCore`. -/
noncomputable def cxCoreCost (F : Fields 10) (T Rr q B : ℕ) (bankLen : Fin 2 → ℕ) : ℝ :=
  ((1 + (Rr * 2 ^ q * (keyRecCost F.y len B + 1) + 1) +
          (2 * (Rr * 2 ^ q * ((∑ j, len j) + B)) + 2) + (4 * (∑ f, len f) + 4 * 10 + 1) : ℕ) : ℝ) +
        ((prog.map (opCost p len T Rr q (fieldsLen len + B)
          bankLen)).sum + 1) +
        ((Rr * 2 ^ q * (2 * idxStepCost (26 * p.wy + 24) (fieldsLen len + B) len +
            6 * (fieldsLen len + B) + 15) +
          fieldsLen len * ((badRanks (Equiv.refl (Fin (Rr * 2 ^ q)))
            fun i => ¬ GoodIdx p len F i).length * (12 * fieldsLen len + 6 * B + 13)) +
          10 * fieldsLen len + 8 * (∑ f, len f) + 8 * 10 + 18 : ℕ) : ℝ) +
        ((Rr * 2 ^ q * (2 * idxStepCost (6 * p.wy + 4) B len + 10 * B + 4) +
          8 * (∑ f, len f) + 8 * 10 + 18 : ℕ) : ℝ)

open Classical in
variable (body ι) in
/-- **The compact selected-bit XOR on the record stream.** On `R 2^q` records of `B ≥ 1`
symbols below `8`, beside the fixed registers of `S₀`, `cxCore` moves the records by the masked
exclusive or with the selected bits of the used segments, then with the top selected bit. -/
theorem cxCore_exec (hι : Function.Injective ι) (hF : F.Valid p len) (hO : F.Order)
    (hb : Banks ι bank) (hK : 0 < p.K) (hG : 0 < p.G) (hGK : p.G + 1 < p.K) (hm : 0 < p.m)
    (hA : 4 ≤ prime + K) (hQ : swapStates cxHd cxPay cxHd_inj ≤ Q) (hT : swapT 6 ≤ T)
    {Rr q B : ℕ} (hRr : 0 < Rr) (hq : ∀ g, touched F g → fieldOff len g + len g ≤ q)
    (hMk : Rr * 2 ^ q ≤ 2 ^ fieldsLen len) (hB : 1 ≤ B)
    (hs : Fin 2 → Fin 5 → List Bool)
    (hv : ∀ c k, Counter.value (hs c k) = BinaryInterchangeRun.values
      (swapDimsIdx (len := len) F.b (swapFld F c) p.wc Rr q (fieldsLen len + B)).1
      (swapDimsIdx (len := len) F.b (swapFld F c) p.wc Rr q (fieldsLen len + B)).2.1
      (swapDimsIdx (len := len) F.b (swapFld F c) p.wc Rr q (fieldsLen len + B)).2.2 p.wc p.wc k)
    (hc : ∀ c k, GrowingCounterData.Canonical (hs c k))
    (S₀ : Stacks T (prime + K))
    (hS : PassState ι bank p len (fieldsLen len + B) (Rr * 2 ^ q) hs S₀)
    (hctrB : (S₀.R (ι .ctrB)).length = B) (hctrK : (S₀.R (ι .ctrK)).length = fieldsLen len)
    (hkt : ∀ i, S₀.R (ι (.kt i)) = []) (hfr : ∀ i, S₀.R (ι (.fr i)) = [])
    (hfq : ∀ i, S₀.R (ι (.fq i)) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = Rr * 2 ^ q)
    (hlB : ∀ r ∈ l, r.length = B ∧ ∀ s ∈ r, s.val < 8) (v : HS T Q (prime + K) U) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ cxCoreCost p len F T Rr q B (fun c => ∑ j, (S₀.R (bank c j)).length) ∧
      Exec body (cxCore ι F hA hb hQ hT)
        (mk v { S₀ with R := Function.update S₀.R (ι .src) l.flatten }) m
        (mk v' { S₀ with
          R := Function.update S₀.R (ι .src) (moveRecs (cxPerm p (R := Rr) hF hq) l).flatten }) := by
  have hX := hF.xorFields
  have hqy : fieldOff len F.y + len F.y ≤ q := hq F.y (Or.inr (Or.inr (Or.inr rfl)))
  set k := fieldsLen len with hk
  set M := Rr * 2 ^ q with hM
  set sel := Layer.CompactMasks.maskVal p.n (posS p) with hsel
  set πT := xorPerm (R := Rr) hX hqy sel with hπT
  set Sp := listPerm (wfPerm (R := Rr) hF hq) progW with hSp
  let St : List (Fin (prime + K + 4)) → Stacks T (prime + K) := fun w =>
    { S₀ with R := Function.update S₀.R (ι .src) w }
  have hSt_src : ∀ w, (St w).R (ι .src) = w := fun w => by simp [St]
  have hSt : ∀ w (x : CxReg), x ≠ .src → (St w).R (ι x) = S₀.R (ι x) :=
    fun w x hx => Function.update_of_ne (hι.ne hx) _ _
  have hSt_upd : ∀ w w', ({ St w with R := Function.update (St w).R (ι .src) w' } :
      Stacks T (prime + K)) = St w' := fun w w' => by simp [St]
  have hInv : ∀ w, CxInv p ι len (St w).R 0 := fun w =>
    cxInv_frame hS.inv fun x ⟨y, hy, hx⟩ => by
      subst hx; exact hSt w y (by rintro rfl; exact hy)
  have hlen : ∀ r ∈ l, r.length = B := fun r hr => (hlB r hr).1
  -- the key pass
  have hkS : KeyState (fun g => ι (.fld g)) len (len F.y) (ι .mSel) (ι (.kt 0)) (ι (.kt 1))
      (ι (.kt 2)) (fun _ => 0) sel (St l.flatten).R :=
    ⟨fun g => by rw [(hInv _).1 g]; simp [digit],
      by rw [(hInv _).2.1, hF.ly]; rfl,
      by rw [hSt _ _ (by simp), hkt], by rw [hSt _ _ (by simp), hkt],
      by rw [hSt _ _ (by simp), hkt]⟩
  obtain ⟨v₁, hu₁, he₁⟩ := cxKey_exec body hX hqy (cx_keyRegs hι) hB l hl hlen v
    (St l.flatten) (hSt_src _) (by rw [hSt _ _ (by simp), hS.out])
    (by rw [hSt _ _ (by simp), hctrB]) (by rw [hSt _ _ (by simp), hS.tmp]) hkS
  rw [hSt_upd] at he₁
  set Kd := keyRecs k πT l with hKd
  have hKl : Kd.length = M := length_keyRecs _ _ _
  have hKB : ∀ r ∈ Kd, r.length = k + B ∧ ∀ s ∈ r, s.val < 8 := fun r hr =>
    ⟨keyRecs_length_mem k B πT l hl hlen r hr,
      mem_keyRecs_sym hl (fun r hr => (hlB r hr).2) r hr⟩
  -- the gadget program
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := progPass_exec body F hι hF hO hK hG (by omega) hb hQ hT hRr
    hq (by omega) hs hv hc S₀ hS Kd hKl hKB v₁
  -- the repair
  set Xr := moveRecs Sp Kd with hXr
  set Yr := moveRecs πT Kd with hYr
  let bad : Fin M → Prop := fun i => ¬ GoodIdx p len F i
  have hTbad : ∀ x, bad (πT x) ↔ bad x := fun x => not_congr (good_xorIdx hF hK x)
  have hagree : ∀ x, ¬ bad x → Sp x = πT x := fun x hx => Fin.ext (by
    rw [hSp, runPerm_val, progW_val, runIdx_prog_good hF (not_not.1 hx) hK,
      idealIdx_eq_xorIdx hK]
    rfl)
  have hcode : ∀ a : Fin M, (badC (prime + K) hA).eval p.wy (badVals p (view len F
      ((Equiv.refl (Fin M) a : Fin M) : ℕ))) = if bad a then 1 else 0 := fun a => by
    rw [badCode_eq F hA hG hGK hm]
    by_cases h : GoodIdx p len F a <;> simp [bad, h]
  have hgood := repair_good_of (Equiv.refl (Fin M)) (πS := Sp) (πT := πT)
    (code := fun i => (badC (prime + K) hA).eval p.wy (badVals p (view len F i))) hTbad hagree hcode
    (fun a => rfl) (fun a => rfl) k l
  have hbad := repair_bad_of (Equiv.refl (Fin M)) (πS := Sp) (πT := πT)
    (code := fun i => (badC (prime + K) hA).eval p.wy (badVals p (view len F i))) hTbad hagree hcode
    (fun a => rfl) (fun a => rfl) k hMk l
  have hXl : Xr.length = M := length_moveRecs _ _
  have hXB : ∀ r ∈ Xr, r.length = k + B :=
    moveRecs_length_mem _ _ hKl fun r hr => (hKB r hr).1
  have hYB : ∀ r ∈ Yr, r.length = k + B :=
    moveRecs_length_mem _ _ hKl fun r hr => (hKB r hr).1
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := repairAtC_exec (codeBad_spec (body := body) F hι hF hA hG hGK)
    (src := ι .src) (gR := ι (.dst 0)) (bR := ι (.dst 1)) (g := ι (.aux 0)) (b := ι (.aux 1))
    (ctrKB := ι .ctr) (ctrB := ι .ctrB) (ctrK := ι .ctrK) (cnt := ι .cnt) (tmp := ι .tmp)
    (us := fun r => ι (.spare r))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact not_cxIdx hι (by simp [CxReg.isIdx]))
    (fun f => hι.ne (by simp)) (fun f => hι.ne (by simp)) (by simp [hι.eq_iff])
    (fun r => by simp [hι.eq_iff]) (fun r r' e => by simpa using hι e)
    (fun r f => hι.ne (by simp)) hB Xr Yr (by rw [hXl, length_moveRecs]) hXB hYB hgood hbad v₂
    (St Xr.flatten) (hSt_src _) (by rw [hSt _ _ (by simp), hS.dst]) (by rw [hSt _ _ (by simp), hS.dst])
    (by rw [hSt _ _ (by simp), hS.aux]) (by rw [hSt _ _ (by simp), hS.aux])
    (by rw [hSt _ _ (by simp), hS.ctr]) (by rw [hSt _ _ (by simp), hctrB])
    (by rw [hSt _ _ (by simp), hctrK]) (by rw [hSt _ _ (by simp), hS.cnt, hXl])
    (by rw [hSt _ _ (by simp), hS.tmp]) (fun r => (hInv _).2.2.2.2.2.2.2.2.2.2.2 r) (hInv _)
  rw [hSt_upd, hYr, map_drop_moveRecs_keyRecs] at he₃
  -- the fix
  have hTl : (moveRecs πT l).length = M := length_moveRecs _ _
  have hTB : ∀ r ∈ moveRecs πT l, r.length = B := moveRecs_length_mem _ _ hl hlen
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := cxFix_exec body hι hF hG hGK hm hqy
    (src := ι .src) (r0 := ι (.fr 0)) (r1 := ι (.fr 1)) (r2 := ι (.fr 2)) (r3 := ι (.fr 3))
    (q0 := ι (.fq 0)) (q1 := ι (.fq 1)) (q2 := ι (.fq 2)) (q3 := ι (.fq 3)) (ctrB := ι .ctrB)
    (cnt := ι .cnt) (tmp := ι .tmp)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact not_cxIdx hι (by simp [CxReg.isIdx]))
    (by simp [hι.eq_iff]) hB (moveRecs πT l) hTl hTB v₃ (St (moveRecs πT l).flatten) (hSt_src _)
    (by rw [hSt _ _ (by simp), hfr]) (by rw [hSt _ _ (by simp), hfr])
    (by rw [hSt _ _ (by simp), hfr]) (by rw [hSt _ _ (by simp), hfr])
    (by rw [hSt _ _ (by simp), hfq]) (by rw [hSt _ _ (by simp), hfq])
    (by rw [hSt _ _ (by simp), hfq]) (by rw [hSt _ _ (by simp), hfq])
    (by rw [hSt _ _ (by simp), hctrB]) (by rw [hSt _ _ (by simp), hS.cnt])
    (by rw [hSt _ _ (by simp), hS.tmp]) (hInv _)
  rw [hSt_upd, ← moveRecs_trans _ _ l hl] at he₄
  change Exec _ _ _ _ (mk v₄ (St (moveRecs (cxPerm p hF hq) l).flatten)) at he₄
  have hnb : (codeRecs Xr (fun i => (badC (prime + K) hA).eval p.wy (badVals p (view len F i)))
      1).length = (badRanks (Equiv.refl (Fin M)) bad).length := by
    rw [codeRecs_badRanks _ _ _ hcode _ hXl, List.length_map]
  rw [hnb, hXl] at hm₃
  refine ⟨v₄, (1 + (l.length * (keyRecCost F.y len B + 1) + 1) +
      (2 * (l.length * ((∑ j, len j) + B)) + 2) + (4 * (∑ f, len f) + 4 * 10 + 1)) +
      (m₂ + (m₃ + m₄)), by rw [hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))⟩
  unfold cxCoreCost
  have h₃ := (Nat.cast_le (α := ℝ)).2 hm₃
  have h₄ := (Nat.cast_le (α := ℝ)).2 hm₄
  have e : (badRanks (Equiv.refl (Fin M)) bad).length = (badRanks (Equiv.refl
      (Fin (Rr * 2 ^ q))) fun i => ¬ GoodIdx p len F i).length := rfl
  have hMR : ((M : ℕ) : ℝ) = (Rr : ℝ) * 2 ^ q := by rw [hM]; push_cast; ring
  rw [hl]
  push_cast at h₃ h₄ ⊢
  rw [e, hMR] at h₃
  rw [hMR]
  linarith

end IntegerMultBounds.MathlibTM2.Node
