module

public import IntegerMultBounds.MathlibTM2.Node.OffPrep
public import IntegerMultBounds.MathlibTM2.Node.RepairPass

/-!
# The repair machine over prepared index codes

`repairAtP` is the repair machine of `Node/RepairPass.lean` (`repairAt`) with the index loops
replaced by their prepared versions (`Host.routeIdxP`, `Host.mergeIdxP`): a preparation program
runs before every record and writes a function of the record index into the computed code
registers, so the code automaton may read an exceptional-set indicator computed by a program
instead of a direct automaton on the index fields. The sort scratch registers are separate from
the index scratch registers.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host

section RepairMachineP

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {nf nr ns np : ℕ}

/-- The repair machine with prepared index codes: route by code into `gR` (good) and `bR`
(bad), restore the forward order on `g`, `b`, reset the counter, radix sort the bad records on
their keys, merge by code into `gR`, reset, strip the keys onto `src`. -/
def repairAtP [NeZero nr] (prep : Pr P T Q A U) (src gR bR g b ctrKB ctrB ctrK cnt tmp st : Fin T)
    (cf : Fin nf → Fin T) (rs tmps : Fin nr → Fin T) (ss : Fin 4 → Fin T) (C : CAuto A nr 2) :
    Pr P T Q A U :=
  .seq (routeIdxP prep src ![gR, bR] ctrKB tmp cf rs tmps st C)
    (.seq (moveR gR g id)
      (.seq (moveR bR b id)
        (.seq (resetFields cf tmp)
          (.seq (radixSort b ctrKB (ss 0) (ss 1) (ss 2) (ss 3) gR bR st ctrK)
            (.seq (mergeIdxP prep ![g, b] gR ctrKB tmp cnt bR cf rs tmps st C)
              (.seq (resetFields cf tmp) (stripPass gR src ctrB ctrK tmp st)))))))

/-- Register facts of the prepared repair machine. -/
structure RepairLayoutP (src gR bR g b ctrKB ctrB ctrK cnt tmp st : Fin T) (cf : Fin nf → Fin T)
    (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T) (rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ))
    (scr : Fin ns → Fin T) (prm : Fin np → Fin T) (ss : Fin 4 → Fin T) : Prop where
  route : IdxLayoutP cf len L rs tmps rsrc scr prm st (routeRegs src ![gR, bR] ctrKB tmp)
  merge : IdxLayoutP cf len L rs tmps rsrc scr prm st (mergeRegs ![g, b] gR ctrKB tmp cnt bR)
  regs : [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp].Nodup
  cf_regs : ∀ f, cf f ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp]
  tmps_regs : ∀ r, tmps r ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp]
  ss_regs : ∀ r, ss r ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp]
  ss_inj : Function.Injective ss
  ss_cf : ∀ r f, ss r ≠ cf f
  ss_tmps : ∀ r r', ss r ≠ tmps r'
  ss_rs : ∀ r r', ss r ≠ rs r'
  ss_scr : ∀ r s, ss r ≠ scr s
  ss_prm : ∀ r q, ss r ≠ prm q
  ss_st : ∀ r, ss r ≠ st
  scr_regs : ∀ s, scr s ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp]
  prm_regs : ∀ q, prm q ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp]
  rs_regs : ∀ r gg, rsrc r = .inr gg → rs r ∉ [src, gR, bR, g, b, ctrKB, ctrB, ctrK, cnt, tmp]

set_option maxHeartbeats 1000000 in
/-- **The prepared repair machine.** As `repairAt_exec`, with the codes `idxCodeP` of the
prepared registers: `src` ends holding the records of `Y` without their first `k` symbols; the
computed registers end holding `L` symbols; every other register ends as it started. -/
theorem repairAtP_exec [NeZero nr] {prep : Pr P T Q A U}
    {src gR bR g b ctrKB ctrB ctrK cnt tmp st : Fin T} {cf : Fin nf → Fin T}
    {len : Fin nf → ℕ} {L : ℕ} {rs tmps : Fin nr → Fin T} {rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ)}
    {scr : Fin ns → Fin T} {prm : Fin np → Fin T} {ss : Fin 4 → Fin T}
    {P₀ : Fin np → List (Fin (A + 4))} {cP : ℕ}
    (hprep : PrepSpec body prep cf len L rs tmps rsrc scr prm P₀ cP)
    (h : RepairLayoutP src gR bR g b ctrKB ctrB ctrK cnt tmp st cf len L rs tmps rsrc scr prm ss)
    (C : CAuto A nr 2) {k B : ℕ} (hB : 1 ≤ B) (X Y : List (List (Fin (A + 4))))
    (hXY : X.length = Y.length) (hX : ∀ r ∈ X, r.length = k + B)
    (hY : ∀ r ∈ Y, r.length = k + B)
    (hgood : codeRecs X (idxCodeP C L len rsrc) 0 = codeRecs Y (idxCodeP C L len rsrc) 0)
    (hbad : RadixSort.sort (fun rec j => symBit (rec.getD j 0)) k
        (codeRecs X (idxCodeP C L len rsrc) 1) = codeRecs Y (idxCodeP C L len rsrc) 1)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = X.flatten)
    (hgR : S.R gR = []) (hbR : S.R bR = []) (hg : S.R g = []) (hb : S.R b = [])
    (hctr : (S.R ctrKB).length = k + B) (hctrB : (S.R ctrB).length = B)
    (hctrK : (S.R ctrK).length = k) (hcnt : (S.R cnt).length = X.length) (htmp : S.R tmp = [])
    (hss : ∀ r, S.R (ss r) = []) (hI : IdxStateP cf len L rs tmps rsrc scr prm P₀ S.R 0) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ X.length * (2 * cP + 16 * (k + B) + 12 * L + 8 * (∑ f, len f) + 8 * nf + 39) +
        k * ((codeRecs X (idxCodeP C L len rsrc) 1).length * (12 * k + 6 * B + 13)) +
        10 * k + 8 * (∑ f, len f) + 8 * nf + 18 ∧
      Exec body (repairAtP prep src gR bR g b ctrKB ctrB ctrK cnt tmp st cf rs tmps ss C) (mk v S) m
        (mk v' { S with R := R' }) ∧
      R' src = (Y.map (·.drop k)).flatten ∧
      (∀ r g, rsrc r = .inr g → (R' (rs r)).length = L) ∧
      ∀ x, x ≠ src → (∀ r g, rsrc r = .inr g → rs r ≠ x) → R' x = S.R x := by
  -- register facts
  have hregs := h.regs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hregs
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩,
    ⟨c1, c2, c3, c4, c5, c6, c7⟩, ⟨d1, d2, d3, d4, d5, d6⟩, ⟨e1, e2, e3, e4, e5⟩,
    ⟨f1, f2, f3, f4⟩, ⟨g1, g2, g3⟩, ⟨h1, h2⟩, i1⟩ := hregs
  have hcf : ∀ f, cf f ≠ src ∧ cf f ≠ gR ∧ cf f ≠ bR ∧ cf f ≠ g ∧ cf f ≠ b ∧ cf f ≠ ctrKB ∧
      cf f ≠ ctrB ∧ cf f ≠ ctrK ∧ cf f ≠ cnt ∧ cf f ≠ tmp := fun f => by
    have := h.cf_regs f
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this
  have htm : ∀ r, tmps r ≠ src ∧ tmps r ≠ gR ∧ tmps r ≠ bR ∧ tmps r ≠ g ∧ tmps r ≠ b ∧
      tmps r ≠ ctrKB ∧ tmps r ≠ ctrB ∧ tmps r ≠ ctrK ∧ tmps r ≠ cnt ∧ tmps r ≠ tmp := fun r => by
    have := h.tmps_regs r
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this
  have hss' : ∀ r, ss r ≠ src ∧ ss r ≠ gR ∧ ss r ≠ bR ∧ ss r ≠ g ∧ ss r ≠ b ∧
      ss r ≠ ctrKB ∧ ss r ≠ ctrB ∧ ss r ≠ ctrK ∧ ss r ≠ cnt ∧ ss r ≠ tmp := fun r => by
    have := h.ss_regs r
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this
  have hscr' : ∀ s, scr s ≠ src ∧ scr s ≠ gR ∧ scr s ≠ bR ∧ scr s ≠ g ∧ scr s ≠ b ∧
      scr s ≠ ctrKB ∧ scr s ≠ ctrB ∧ scr s ≠ ctrK ∧ scr s ≠ cnt ∧ scr s ≠ tmp := fun s => by
    have := h.scr_regs s
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this
  have hprm' : ∀ q, prm q ≠ src ∧ prm q ≠ gR ∧ prm q ≠ bR ∧ prm q ≠ g ∧ prm q ≠ b ∧
      prm q ≠ ctrKB ∧ prm q ≠ ctrB ∧ prm q ≠ ctrK ∧ prm q ≠ cnt ∧ prm q ≠ tmp := fun q => by
    have := h.prm_regs q
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this
  have hrs' : ∀ r gg, rsrc r = .inr gg → rs r ≠ src ∧ rs r ≠ gR ∧ rs r ≠ bR ∧ rs r ≠ g ∧
      rs r ≠ b ∧ rs r ≠ ctrKB ∧ rs r ≠ ctrB ∧ rs r ≠ ctrK ∧ rs r ≠ cnt ∧ rs r ≠ tmp :=
    fun r gg hr => by
      have := h.rs_regs r gg hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
      exact this
  have hcfinj : Function.Injective cf := h.route.cf_inj
  have hcftmp : ∀ f, cf f ≠ tmp := fun f => (hcf f).2.2.2.2.2.2.2.2.2
  set code := idxCodeP C L len rsrc with hcode
  set Xg := codeRecs X code 0 with hXg
  set Xb := codeRecs X code 1 with hXb
  have hXl : X.flatten.length = X.length * (k + B) := length_flatten_of_length X hX
  have hYl : Y.flatten.length = X.length * (k + B) := by
    rw [hXY]; exact length_flatten_of_length Y hY
  have hblkX : ∀ d, blocksIdx X.flatten (k + B) X.length code 0 d =
      (codeRecs X code d).flatten := fun d => blocksIdx_flatten X (k + B) hX code d
  have hblkY : ∀ d, blocksIdx Y.flatten (k + B) X.length code 0 d =
      (codeRecs Y code d).flatten := by
    intro d; rw [hXY]; exact blocksIdx_flatten Y (k + B) hY code d
  -- the computed registers
  let Comp : Fin T → Prop := fun x => ∃ r gg, rsrc r = .inr gg ∧ rs r = x
  have hcomp_ne : ∀ x, ¬ Comp x → ∀ r gg, rsrc r = .inr gg → rs r ≠ x :=
    fun x hx r gg hr e => hx ⟨r, gg, hr, e⟩
  -- the registers that are never written
  let Oth : Fin T → Prop := fun x =>
    x ≠ src ∧ x ≠ gR ∧ x ≠ bR ∧ x ≠ g ∧ x ≠ b ∧ (∀ f, cf f ≠ x) ∧ ¬ Comp x
  -- stage 1: route
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hsrc₁, hdst₁, hI₁, hoth₁⟩ := routeIdxP_exec body src
    ![gR, bR] ctrKB tmp cf len L rs tmps rsrc scr prm P₀ st C hprep h.route
    (by simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]; exact ⟨⟨a5, a9⟩, f4⟩)
    (by intro d; fin_cases d <;> simp [Ne.symm a1, b4, b8, Ne.symm a2, c3, c7])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [b1, Ne.symm b1])
    (l := X.flatten) (c := S.R ctrKB) (nb := X.length) (B := k + B) (i₀ := 0) (by omega) hXl
    hctr v S hsrc rfl htmp hI
  have hR₁ : ∀ x, Oth x → R₁ x = S.R x := fun x hx =>
    hoth₁ x hx.1 (fun d => by fin_cases d <;> simp [Ne.symm hx.2.1, Ne.symm hx.2.2.1])
      hx.2.2.2.2.2.1 (hcomp_ne x hx.2.2.2.2.2.2)
  have hR₁gR : R₁ gR = Xg.flatten.reverse := by
    have := hdst₁ 0; simp only [Matrix.cons_val_zero] at this; rw [this, hgR, hblkX]; simp [Xg]
  have hR₁bR : R₁ bR = Xb.flatten.reverse := by
    have := hdst₁ 1; simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    rw [this, hbR, hblkX]; simp [Xb]
  have hR₁g : R₁ g = [] := by
    rw [hoth₁ g (Ne.symm a3) (fun d => by fin_cases d <;> simp [b2, c1]) (fun f => (hcf f).2.2.2.1)
      (fun r gg hr => (hrs' r gg hr).2.2.2.1), hg]
  have hR₁b : R₁ b = [] := by
    rw [hoth₁ b (Ne.symm a4) (fun d => by fin_cases d <;> simp [b3, c2])
      (fun f => (hcf f).2.2.2.2.1) (fun r gg hr => (hrs' r gg hr).2.2.2.2.1), hb]
  -- stage 2, 3: restore forward order
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body gR g b2 id v₁ { S with R := R₁ }
  set R₂ := movedR R₁ gR g id (R₁ gR) with hR₂
  have hR₂f : ∀ x, x ≠ gR → x ≠ g → R₂ x = R₁ x := fun x h1 h2 => by
    simp [hR₂, movedR, h1, h2]
  have hR₂g : R₂ g = Xg.flatten := by simp [hR₂, movedR, hR₁gR, hR₁g]
  have hR₂gR : R₂ gR = [] := by simp [hR₂, movedR, b2]
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body bR b c2 id v₂ { S with R := R₂ }
  set R₃ := movedR R₂ bR b id (R₂ bR) with hR₃
  have hR₃f : ∀ x, x ≠ bR → x ≠ b → R₃ x = R₂ x := fun x h1 h2 => by
    simp [hR₃, movedR, h1, h2]
  have hR₂bR : R₂ bR = Xb.flatten.reverse := by rw [hR₂f _ (Ne.symm b1) c1, hR₁bR]
  have hR₂b : R₂ b = [] := by rw [hR₂f _ (Ne.symm b3) (Ne.symm d1), hR₁b]
  have hR₃b : R₃ b = Xb.flatten := by simp [hR₃, movedR, hR₂bR, hR₂b]
  have hR₃bR : R₃ bR = [] := by simp [hR₃, movedR, c2]
  -- the index state survives the moves
  rw [Nat.zero_add] at hI₁
  have hI₃ : IdxStateP cf len L rs tmps rsrc scr prm P₀ R₃ X.length := by
    refine hI₁.of_frame h.merge fun x hx => ?_
    simp only [mergeRegs, not_or, not_exists] at hx
    have hx0 := hx.2.2.2.2.2 0
    have hx1 := hx.2.2.2.2.2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hx0 hx1
    rw [hR₃f _ hx.2.2.2.2.1 (Ne.symm hx1), hR₂f _ hx.1 (Ne.symm hx0)]
  -- stage 4: reset
  obtain ⟨v₄, R₄, hu₄, he₄, hcf₄, hoth₄⟩ := resetFields_exec body cf hcfinj tmp hcftmp len v₃
    { S with R := R₃ }
    (by
      show R₃ tmp = []
      rw [hR₃f _ (Ne.symm c7) (Ne.symm e5), hR₂f _ (Ne.symm b8) (Ne.symm d6),
        hR₁ _ ⟨Ne.symm a9, Ne.symm b8, Ne.symm c7, Ne.symm d6, Ne.symm e5, hcftmp,
          fun ⟨r, gg, hr, e⟩ => (hrs' r gg hr).2.2.2.2.2.2.2.2.2 e⟩, htmp])
    (fun f => by
      show (R₃ (cf f)).length = _
      rw [hI₃.1 f]
      simp)
  have hR₄f : ∀ x, (∀ f, x ≠ cf f) → R₄ x = R₃ x := hoth₄
  -- the registers outside the stream registers
  have hO₄ : ∀ x, Oth x → R₄ x = S.R x := fun x hx => by
    rw [hR₄f x (fun f e => hx.2.2.2.2.2.1 f e.symm), hR₃f x hx.2.2.1 hx.2.2.2.2.1,
      hR₂f x hx.2.1 hx.2.2.2.1, hR₁ x hx]
  have hOtm : ∀ r, Oth (tmps r) := fun r =>
    ⟨(htm r).1, (htm r).2.1, (htm r).2.2.1, (htm r).2.2.2.1, (htm r).2.2.2.2.1,
      fun f e => h.route.tmps_cf r f e.symm,
      fun ⟨r', gg, hr, e⟩ => h.route.rs_tmps r' r e⟩
  have hOss : ∀ r, Oth (ss r) := fun r =>
    ⟨(hss' r).1, (hss' r).2.1, (hss' r).2.2.1, (hss' r).2.2.2.1, (hss' r).2.2.2.2.1,
      fun f e => h.ss_cf r f e.symm, fun ⟨r', gg, hr, e⟩ => h.ss_rs r r' e.symm⟩
  have hOscr : ∀ s', Oth (scr s') := fun s' =>
    ⟨(hscr' s').1, (hscr' s').2.1, (hscr' s').2.2.1, (hscr' s').2.2.2.1, (hscr' s').2.2.2.2.1,
      fun f e => h.route.scr_cf s' f e.symm, fun ⟨r', gg, hr, e⟩ => h.route.scr_rs s' r' e.symm⟩
  have hOprm : ∀ q, Oth (prm q) := fun q =>
    ⟨(hprm' q).1, (hprm' q).2.1, (hprm' q).2.2.1, (hprm' q).2.2.2.1, (hprm' q).2.2.2.2.1,
      fun f e => h.route.prm_cf q f e.symm, fun ⟨r', gg, hr, e⟩ => h.route.prm_rs q r' e.symm⟩
  have hOctr : Oth ctrKB := ⟨Ne.symm a5, Ne.symm b4, Ne.symm c3, Ne.symm d2, Ne.symm e1,
    fun f => (hcf f).2.2.2.2.2.1, fun ⟨r, gg, hr, e⟩ => (hrs' r gg hr).2.2.2.2.2.1 e⟩
  have hOctrB : Oth ctrB := ⟨Ne.symm a6, Ne.symm b5, Ne.symm c4, Ne.symm d3, Ne.symm e2,
    fun f => (hcf f).2.2.2.2.2.2.1, fun ⟨r, gg, hr, e⟩ => (hrs' r gg hr).2.2.2.2.2.2.1 e⟩
  have hOctrK : Oth ctrK := ⟨Ne.symm a7, Ne.symm b6, Ne.symm c5, Ne.symm d4, Ne.symm e3,
    fun f => (hcf f).2.2.2.2.2.2.2.1, fun ⟨r, gg, hr, e⟩ => (hrs' r gg hr).2.2.2.2.2.2.2.1 e⟩
  have hOcnt : Oth cnt := ⟨Ne.symm a8, Ne.symm b7, Ne.symm c6, Ne.symm d5, Ne.symm e4,
    fun f => (hcf f).2.2.2.2.2.2.2.2.1, fun ⟨r, gg, hr, e⟩ => (hrs' r gg hr).2.2.2.2.2.2.2.2.1 e⟩
  have hOtmp : Oth tmp := ⟨Ne.symm a9, Ne.symm b8, Ne.symm c7, Ne.symm d6, Ne.symm e5, hcftmp,
    fun ⟨r, gg, hr, e⟩ => (hrs' r gg hr).2.2.2.2.2.2.2.2.2 e⟩
  have hR₄gR : R₄ gR = [] := by
    rw [hR₄f _ (fun f e => (hcf f).2.1 e.symm), hR₃f _ b1 b3, hR₂gR]
  have hR₄g : R₄ g = Xg.flatten := by
    rw [hR₄f _ (fun f e => (hcf f).2.2.2.1 e.symm), hR₃f _ (Ne.symm c1) d1, hR₂g]
  have hR₄b : R₄ b = Xb.flatten := by rw [hR₄f _ (fun f e => (hcf f).2.2.2.2.1 e.symm), hR₃b]
  have hR₄bR : R₄ bR = [] := by rw [hR₄f _ (fun f e => (hcf f).2.2.1 e.symm), hR₃bR]
  -- the computed registers after the route
  have hR₄rs : ∀ r gg, rsrc r = .inr gg → R₄ (rs r) = R₃ (rs r) := fun r gg hr =>
    hR₄f _ (fun f e => h.route.param r gg f hr e)
  -- stage 5: radix sort
  have hssinj := h.ss_inj
  obtain ⟨v₅, m₅, hu₅, hm₅, he₅⟩ := radixSort_exec body b ctrKB (ss 0) (ss 1) (ss 2) (ss 3) gR bR
    st ctrK
    (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      refine ⟨⟨e1, fun e => (hss' 0).2.2.2.2.1 e.symm, fun e => (hss' 1).2.2.2.2.1 e.symm,
        fun e => (hss' 2).2.2.2.2.1 e.symm, fun e => (hss' 3).2.2.2.2.1 e.symm, Ne.symm b3,
        Ne.symm c2, e3⟩, ⟨fun e => (hss' 0).2.2.2.2.2.1 e.symm, fun e => (hss' 1).2.2.2.2.2.1 e.symm,
        fun e => (hss' 2).2.2.2.2.2.1 e.symm, fun e => (hss' 3).2.2.2.2.2.1 e.symm, Ne.symm b4,
        Ne.symm c3, f2⟩, ⟨fun e => by have := hssinj e; simp at this,
        fun e => by have := hssinj e; simp at this, fun e => by have := hssinj e; simp at this,
        (hss' 0).2.1, (hss' 0).2.2.1, (hss' 0).2.2.2.2.2.2.2.1⟩,
        ⟨fun e => by have := hssinj e; simp at this, fun e => by have := hssinj e; simp at this,
        (hss' 1).2.1, (hss' 1).2.2.1, (hss' 1).2.2.2.2.2.2.2.1⟩,
        ⟨fun e => by have := hssinj e; simp at this, (hss' 2).2.1, (hss' 2).2.2.1,
        (hss' 2).2.2.2.2.2.2.2.1⟩, ⟨(hss' 3).2.1, (hss' 3).2.2.1, (hss' 3).2.2.2.2.2.2.2.1⟩,
        ⟨b1, b6⟩, c5⟩)
    (recs := Xb) (B := k + B) (K := k) (K' := k) (by omega) le_rfl
    (fun r hr => hX r (mem_codeRecs hr)) v₄ { S with R := R₄ } hR₄b
    (by show (R₄ ctrK).length = k; rw [hO₄ _ hOctrK, hctrK])
    (by show (R₄ ctrKB).length = k + B; rw [hO₄ _ hOctr, hctr])
    (by show R₄ (ss 0) = []; rw [hO₄ _ (hOss 0), hss 0])
    (by show R₄ (ss 1) = []; rw [hO₄ _ (hOss 1), hss 1])
    (by show R₄ (ss 2) = []; rw [hO₄ _ (hOss 2), hss 2])
    (by show R₄ (ss 3) = []; rw [hO₄ _ (hOss 3), hss 3])
    hR₄gR hR₄bR
  rw [hbad] at he₅
  set R₅ := Function.update R₄ b (codeRecs Y code 1).flatten with hR₅
  have hR₅f : ∀ x, x ≠ b → R₅ x = R₄ x := fun x hx => Function.update_of_ne hx _ _
  have hdig0 : ∀ f, digit len f 0 = 0 := fun f => by simp [digit]
  have hI₅ : IdxStateP cf len L rs tmps rsrc scr prm P₀ R₅ 0 :=
    ⟨fun f => by
        rw [hR₅f _ (hcf f).2.2.2.2.1, hcf₄ f, hdig0],
      fun r gg hr => by
        rw [hR₅f _ (hrs' r gg hr).2.2.2.2.1, hR₄rs r gg hr]
        exact hI₃.2.1 r gg hr,
      fun r => by
        rw [hR₅f _ (hOtm r).2.2.2.2.1, hO₄ _ (hOtm r), hI.2.2.1 r],
      fun s' => by
        rw [hR₅f _ (hOscr s').2.2.2.2.1, hO₄ _ (hOscr s'), hI.2.2.2.1 s'],
      fun q => by
        rw [hR₅f _ (hOprm q).2.2.2.2.1, hO₄ _ (hOprm q), hI.2.2.2.2 q]⟩
  -- stage 6: merge
  obtain ⟨v₆, R₆, m₆, hu₆, hm₆, he₆, hgR₆, hsrcs₆, hI₆, hoth₆⟩ := mergeIdxP_exec_blocks body
    ![g, b] gR ctrKB tmp cnt bR cf len L rs tmps rsrc scr prm P₀ st C hprep h.merge
    (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨b4, b8, b7, b1⟩, ⟨f4, f3, Ne.symm c3⟩, ⟨Ne.symm i1, Ne.symm c7⟩, Ne.symm c6⟩)
    (by
      intro d
      fin_cases d
      · simp [Ne.symm b2, d2, d6, d5, Ne.symm c1]
      · simp [Ne.symm b3, e1, e5, e4, Ne.symm c2])
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [d1, Ne.symm d1])
    (l := Y.flatten) (c := S.R ctrKB) (kk := S.R cnt) (nb := X.length) (B := k + B) (i₀ := 0)
    hYl hctr hcnt (fun _ => []) v₅ { S with R := R₅ }
    (by
      intro d
      fin_cases d
      · show R₅ g = blocksIdx Y.flatten (k + B) X.length code 0 0 ++ []
        rw [hR₅f _ d1, hR₄g, hblkY 0, List.append_nil, ← hgood]
      · show R₅ b = blocksIdx Y.flatten (k + B) X.length code 0 1 ++ []
        rw [hR₅, Function.update_self, hblkY 1, List.append_nil])
    (by show R₅ ctrKB = _; rw [hR₅f _ (Ne.symm e1), hO₄ _ hOctr])
    (by show R₅ tmp = _; rw [hR₅f _ (Ne.symm e5), hO₄ _ hOtmp, htmp])
    (by show R₅ cnt = _; rw [hR₅f _ (Ne.symm e4), hO₄ _ hOcnt])
    (by show R₅ bR = _; rw [hR₅f _ c2, hR₄bR])
    hI₅
  rw [Nat.zero_add] at hI₆
  have hR₆f : ∀ x, x ≠ gR → x ≠ g → x ≠ b → (∀ f, cf f ≠ x) → ¬ Comp x → R₆ x = R₅ x :=
    fun x h1 h2 h3 h4 h5 => hoth₆ x h1 (fun d => by fin_cases d <;> simp [Ne.symm h2, Ne.symm h3])
      h4 (hcomp_ne x h5)
  have hR₆gR : R₆ gR = Y.flatten.reverse := by
    rw [hgR₆]
    show Y.flatten.reverse ++ R₅ gR = _
    rw [hR₅f _ b3, hR₄gR, List.append_nil]
  -- stage 7: reset
  obtain ⟨v₇, R₇, hu₇, he₇, hcf₇, hoth₇⟩ := resetFields_exec body cf hcfinj tmp hcftmp len v₆
    { S with R := R₆ }
    (by
      show R₆ tmp = []
      rw [hR₆f _ (Ne.symm b8) (Ne.symm d6) (Ne.symm e5) (fun f => hcftmp f) hOtmp.2.2.2.2.2.2,
        hR₅f _ (Ne.symm e5), hO₄ _ hOtmp, htmp])
    (fun f => by show (R₆ (cf f)).length = _; rw [hI₆.1 f]; simp)
  have hR₇f : ∀ x, (∀ f, x ≠ cf f) → R₇ x = R₆ x := hoth₇
  have hO₇ : ∀ x, Oth x → R₇ x = S.R x := fun x hx => by
    rw [hR₇f x (fun f e => hx.2.2.2.2.2.1 f e.symm),
      hR₆f x hx.2.1 hx.2.2.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2, hR₅f x hx.2.2.2.2.1,
      hO₄ x hx]
  have hR₇gR : R₇ gR = Y.flatten.reverse := by
    rw [hR₇f _ (fun f e => (hcf f).2.1 e.symm), hR₆gR]
  have hCsrc : ¬ Comp src := fun ⟨r, gg, hr, e⟩ => (hrs' r gg hr).1 e
  have hR₇src : R₇ src = [] := by
    rw [hR₇f _ (fun f e => (hcf f).1 e.symm),
      hR₆f _ a1 a3 a4 (fun f => (hcf f).1) hCsrc,
      hR₅f _ a4, hR₄f _ (fun f e => (hcf f).1 e.symm), hR₃f _ a2 a4, hR₂f _ a1 a3, hsrc₁]
  -- stage 8: strip
  obtain ⟨v₈, hu₈, he₈⟩ := stripPass_exec body gR src ctrB ctrK tmp st
    (by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨Ne.symm a1, b5, b6, b8⟩, ⟨a6, a7, a9⟩, ⟨g1, g3⟩, h2⟩)
    hB Y hY v₇ { S with R := R₇ } hR₇gR
    (by show (R₇ ctrB).length = B; rw [hO₇ _ hOctrB, hctrB])
    (by show (R₇ ctrK).length = k; rw [hO₇ _ hOctrK, hctrK])
    (by show R₇ tmp = []; rw [hO₇ _ hOtmp, htmp])
  -- the computed registers at the end
  have hR₇rs : ∀ r gg, rsrc r = .inr gg → (R₇ (rs r)).length = L := fun r gg hr => by
    rw [hR₇f _ (fun f e => h.route.param r gg f hr e)]
    exact hI₆.2.1 r gg hr
  refine ⟨v₈, _, _, by rw [hu₈, hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆
      (Exec.seq he₇ he₈)))))), ?_, ?_, ?_⟩
  · -- the cost
    simp only [hR₁gR, hR₂bR, List.length_reverse]
    rw [length_codeRecs_flatten X _ hX, length_codeRecs_flatten X _ hX, ← hXY]
    have hg' := Nat.mul_le_mul_right (k + B) (length_codeRecs X code 0)
    have hb' := Nat.mul_le_mul_right (k + B) (length_codeRecs X code 1)
    unfold idxStepCost at hm₁ hm₆
    nlinarith [hg', hb', hm₅, hm₁, hm₆]
  · show Function.update (Function.update R₇ gR []) src
      ((Y.map (·.drop k)).flatten ++ R₇ src) src = _
    rw [Function.update_self, hR₇src, List.append_nil]
  · intro r gg hr
    show (Function.update (Function.update R₇ gR []) src
      ((Y.map (·.drop k)).flatten ++ R₇ src) (rs r)).length = L
    rw [Function.update_of_ne (hrs' r gg hr).1, Function.update_of_ne (hrs' r gg hr).2.1]
    exact hR₇rs r gg hr
  · intro x hx hxc
    have hxc' : ¬ Comp x := fun ⟨r, gg, hr, e⟩ => hxc r gg hr e
    show Function.update (Function.update R₇ gR []) src
      ((Y.map (·.drop k)).flatten ++ R₇ src) x = _
    rw [Function.update_of_ne hx]
    by_cases hxg : x = gR
    · subst hxg; rw [Function.update_self, hgR]
    rw [Function.update_of_ne hxg]
    by_cases hxf : ∃ f, x = cf f
    · obtain ⟨f, rfl⟩ := hxf
      rw [hcf₇ f, hI.1 f, hdig0]
    simp only [not_exists] at hxf
    rw [hR₇f x hxf]
    by_cases hxg' : x = g
    · subst hxg'
      have := hsrcs₆ 0
      simp only [Matrix.cons_val_zero] at this
      rw [this, hg]
    by_cases hxb : x = b
    · subst hxb
      have := hsrcs₆ 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
      rw [this, hb]
    rw [hR₆f x hxg hxg' hxb (fun f e => hxf f e.symm) hxc', hR₅f x hxb]
    by_cases hxbR : x = bR
    · subst hxbR; rw [hR₄bR, hbR]
    exact hO₄ x ⟨hx, hxg, hxbR, hxg', hxb, fun f e => hxf f e.symm, hxc'⟩

end RepairMachineP


/-! ### The repair on a stream in index order: list semantics -/

section RepairListsP

open IntegerMultBounds.Compact IntegerMultBounds.Machine.Partition

variable {A M : ℕ} {πS πT : Equiv.Perm (Fin M)} {bad : Fin M → Prop} [DecidablePred bad]
  {code : ℕ → Fin 2} (hcode : ∀ j : Fin M, code j = if bad j then 1 else 0)
include hcode

/-- The records of code `1` of a stream of `M` records are those at the exceptional positions. -/
lemma codeRecs_bad_refl (Z : List (List (Fin (A + 4)))) (hZ : Z.length = M) :
    codeRecs Z code 1 =
      (badRanks (Equiv.refl (Fin M)) bad).map fun (i : Fin M) => Z.getD (i : ℕ) [] := by
  unfold codeRecs badRanks
  rw [hZ, ← List.map_coe_finRange_eq_range, List.filter_map, List.map_map]
  refine congrArg (List.map _) (List.filter_congr fun i _ => ?_)
  simp only [Function.comp_apply, Equiv.refl_symm, Equiv.refl_apply]
  rw [hcode i]
  by_cases hb : bad i <;> simp [hb]

variable (hT : ∀ x, bad (πT x) ↔ bad x) (agree : ∀ x, ¬ bad x → πS x = πT x)
include hT agree

/-- **Good records.** Off the exceptional positions, the stream after the actual permutation
holds the records of the ideal permutation. -/
theorem repair_good_refl (k : ℕ) (l : List (List (Fin (A + 4)))) :
    codeRecs (moveRecs πS (keyRecs k πT l)) code 0 =
      codeRecs (moveRecs πT (keyRecs k πT l)) code 0 := by
  unfold codeRecs
  rw [length_moveRecs, length_moveRecs]
  refine List.map_congr_left fun j hj => ?_
  have hjM : j < M := List.mem_range.1 (List.mem_filter.1 hj).1
  have hc := (List.mem_filter.1 hj).2
  rw [hcode ⟨j, hjM⟩] at hc
  have hnb : ¬ bad ⟨j, hjM⟩ := by
    intro h; simp [h] at hc
  rw [getD_moveRecs πS _ ⟨j, hjM⟩, getD_moveRecs πT _ ⟨j, hjM⟩,
    inverse_agrees_off_bad πS πT bad hT agree ⟨j, hjM⟩ hnb]

/-- **Exceptional records.** At the exceptional positions, the records of the stream after the
actual permutation, radix sorted on their `k` key bits, are the records of the ideal permutation
in position order. -/
theorem repair_bad_refl (k : ℕ) (hk : M ≤ 2 ^ k) (l : List (List (Fin (A + 4)))) :
    RadixSort.sort (fun rec j => symBit (rec.getD j 0)) k
        (codeRecs (moveRecs πS (keyRecs k πT l)) code 1) =
      codeRecs (moveRecs πT (keyRecs k πT l)) code 1 := by
  set e := Equiv.refl (Fin M) with he
  let data : Fin M → List Bool := fun a => List.replicate (a : ℕ) true
  let G : Fin M × Record → List (Fin (A + 4)) :=
    fun x => binSyms k x.1 ++ l.getD x.2.payload.length []
  have hG : ∀ x j, j < k → symBit ((G x).getD j 0) = keyBit x j := by
    intro x j hj
    simp only [G, keyBit]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega)]
    simp [binSyms]
  have hsort := sortedExtracted_eq e πS πT bad hT agree k hk data
  have hXe : codeRecs (moveRecs πS (keyRecs k πT l)) code 1 =
      (extracted e πS πT bad data).map G := by
    rw [codeRecs_bad_refl hcode _ (length_moveRecs _ _), extracted, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, G, data, List.length_replicate]
    rw [getD_moveRecs, getD_keyRecs]
    simp [destRank, he]
  have hYe : codeRecs (moveRecs πT (keyRecs k πT l)) code 1 =
      (target e πT bad data).map G := by
    rw [codeRecs_bad_refl hcode _ (length_moveRecs _ _), target, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, G, data, List.length_replicate]
    rw [getD_moveRecs, getD_keyRecs]
    simp [he]
  rw [hXe, hYe, sort_map _ keyBit G k hG, ← hsort]
  rfl

end RepairListsP


/-! ### Sequencing permutations -/

section Sequencing

/-- Moving by a program is moving by its head instruction, then by the rest. -/
lemma moveRecs_progPerm_cons {α : Type*} {nf : ℕ} (len : Fin nf → ℕ) {R S : ℕ}
    (ins : Layer.CompactXor.CInstr nf) (P : List (Layer.CompactXor.CInstr nf))
    (h : ∀ i ∈ ins :: P, i.WF len S) (l : List (List α)) (hl : l.length = R * 2 ^ S) :
    moveRecs (Layer.CompactXor.progPerm len (R := R) (ins :: P) h) l =
      moveRecs (Layer.CompactXor.progPerm len (R := R) P fun i hi => h i (List.mem_cons_of_mem _ hi))
        (moveRecs (Layer.CompactXor.instrPerm len (R := R) (h ins List.mem_cons_self)) l) := by
  rw [Layer.CompactXor.progPerm, moveRecs_trans _ _ _ hl]

/-- The exceptional positions of a stream in index order are the exceptional indices. -/
lemma length_badRanks_refl {M : ℕ} (bad : Fin M → Prop) [DecidablePred bad] :
    (IntegerMultBounds.Compact.badRanks (Equiv.refl (Fin M)) bad).length =
      Fintype.card {j : Fin M // bad j} := by
  unfold IntegerMultBounds.Compact.badRanks
  rw [Fintype.card_subtype,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange M).filter _), List.toFinset_filter,
    List.toFinset_finRange]
  congr 1
  ext j
  rw [Finset.mem_filter, Finset.mem_filter]
  by_cases h : bad j <;> simp [h]

end Sequencing

end IntegerMultBounds.MathlibTM2.Node
