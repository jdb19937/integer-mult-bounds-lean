module

public import IntegerMultBounds.MathlibTM2.Host.IndexRoute

/-!
# Routing and merging by index code with a prepared register

`IntegerMultBounds.MathlibTM2.Host.IndexRoute` computes the code of a record from counter fields
and constant parameter registers. The compact-control rotations need a code register whose value
is a function of the current index that is not a single field: an offset assembled per record
from the fields above the rotated one. This file repeats the two index loops with a
*preparation* program `prep` run before the code pass of every record: `prep` reads the fields
and writes `binSyms L (g i)` into each computed register `rs r` with `rsrc r = .inr g`, restoring
everything else (`PrepSpec`). The computed registers hold `L` symbols between records.

Register interface, bundled in `IdxLayoutP cf len L rs tmps rsrc scr prm st X`: the fields `cf`,
the code-pass registers `rs` (fields or computed registers), the code-pass spares `tmps`, the
scratch registers `scr` of `prep` (empty between records), the code slot `st`, and the stream
registers `X` of the loop. `IdxStateP` is the register state at index `i`.

* `routeIdxP_exec`: `dst d` gains `(blocksIdx l B nb code i₀ d).reverse` for
  `code = idxCodeP C L len rsrc`, in at most
  `nb * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 13 + cP) + 2` steps;
* `mergeIdxP_exec`, `mergeIdxP_exec_blocks`: the merge, in at most
  `nb * (4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 15 + cP) + 4` steps.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds

variable {T Q A : ℕ} {U P : Type} {nf nr nd ns np : ℕ}

/-! ### Codes with computed registers -/

/-- Value of code-pass register `r` at index `i`: digit `f` of `i` if `rsrc r = .inl f`, the
prepared value `g i` if `rsrc r = .inr g`. -/
def regValP (len : Fin nf → ℕ) (rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ)) (i : ℕ) (r : Fin nr) : ℕ :=
  Sum.elim (fun f => digit len f i) (fun g => g i) (rsrc r)

/-- The code of record index `i`. -/
def idxCodeP (C : CAuto A nr nd) (L : ℕ) (len : Fin nf → ℕ) (rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ))
    (i : ℕ) : Fin nd :=
  C.eval L (regValP len rsrc i)

/-- Register layout of the prepared index machinery beside the stream registers `X`. -/
structure IdxLayoutP (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ)) (scr : Fin ns → Fin T) (prm : Fin np → Fin T) (st : Fin T)
    (X : Fin T → Prop) : Prop extends CodeLayout rs tmps st where
  cf_inj : Function.Injective cf
  tmps_cf : ∀ r f, tmps r ≠ cf f
  field : ∀ r f, rsrc r = .inl f → rs r = cf f ∧ len f = L
  param : ∀ r g f, rsrc r = .inr g → rs r ≠ cf f
  scr_cf : ∀ s f, scr s ≠ cf f
  scr_rs : ∀ s r, scr s ≠ rs r
  prm_cf : ∀ q f, prm q ≠ cf f
  prm_rs : ∀ q r, prm q ≠ rs r
  prm_X : ∀ q, ¬ X (prm q)
  cf_X : ∀ f, ¬ X (cf f)
  rs_X : ∀ r, ¬ X (rs r)
  tmps_X : ∀ r, ¬ X (tmps r)
  scr_X : ∀ s, ¬ X (scr s)

/-- Registers at index `i`: the fields hold the digits of `i`, the computed registers hold `L`
symbols, the spares and the scratch registers are empty, and the parameter registers of the
preparation hold their constants `P₀`. -/
def IdxStateP (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ)) (scr : Fin ns → Fin T) (prm : Fin np → Fin T)
    (P₀ : Fin np → List (Fin (A + 4))) (R : Fin T → List (Fin (A + 4))) (i : ℕ) : Prop :=
  (∀ f, R (cf f) = binSyms (len f) (digit len f i)) ∧
    (∀ r g, rsrc r = .inr g → (R (rs r)).length = L) ∧
    (∀ r, R (tmps r) = []) ∧ (∀ s, R (scr s) = []) ∧ ∀ q, R (prm q) = P₀ q

/-- The contract of a preparation program: from the state at index `i` it writes
`binSyms L (g i)` into every computed register and changes nothing else, within `cP` steps. -/
structure PrepSpec (body : P → Pr P T Q A U) (prep : Pr P T Q A U) (cf : Fin nf → Fin T)
    (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T) (rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ))
    (scr : Fin ns → Fin T) (prm : Fin np → Fin T) (P₀ : Fin np → List (Fin (A + 4))) (cP : ℕ) :
    Prop where
  run : ∀ (i : ℕ) (v : HS T Q A U) (S : Stacks T A),
    IdxStateP cf len L rs tmps rsrc scr prm P₀ S.R i →
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧ m ≤ cP ∧
      Exec body prep (mk v S) m (mk v' { S with R := R' }) ∧
      (∀ r g, rsrc r = .inr g → R' (rs r) = binSyms L (g i)) ∧
      ∀ k, (∀ r g, rsrc r = .inr g → k ≠ rs r) → R' k = S.R k

section Layout

variable {cf : Fin nf → Fin T} {len : Fin nf → ℕ} {L : ℕ} {rs tmps : Fin nr → Fin T}
  {rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ)} {scr : Fin ns → Fin T} {prm : Fin np → Fin T}
  {P₀ : Fin np → List (Fin (A + 4))} {st : Fin T} {X : Fin T → Prop}

/-- After the preparation, every code register holds its value. -/
lemma IdxStateP.rs_eq (h : IdxLayoutP cf len L rs tmps rsrc scr prm st X)
    {R R' : Fin T → List (Fin (A + 4))} {i : ℕ} (hI : IdxStateP cf len L rs tmps rsrc scr prm P₀ R i)
    (hp : ∀ r g, rsrc r = .inr g → R' (rs r) = binSyms L (g i))
    (hR : ∀ k, (∀ r g, rsrc r = .inr g → k ≠ rs r) → R' k = R k) (r : Fin nr) :
    R' (rs r) = binSyms L (regValP len rsrc i r) := by
  rcases hr : rsrc r with f | g
  · obtain ⟨h1, h2⟩ := h.field r f hr
    rw [hR _ (fun r' g' hr' e => h.param r' g' f hr' (e.symm.trans h1)), h1, hI.1 f, h2]
    simp [regValP, hr]
  · rw [hp r g hr]
    simp [regValP, hr]

/-- The state survives changes outside the index registers. -/
lemma IdxStateP.of_frame (h : IdxLayoutP cf len L rs tmps rsrc scr prm st X)
    {R R' : Fin T → List (Fin (A + 4))} {i : ℕ} (hI : IdxStateP cf len L rs tmps rsrc scr prm P₀ R i)
    (hR : ∀ k, ¬ X k → R' k = R k) : IdxStateP cf len L rs tmps rsrc scr prm P₀ R' i :=
  ⟨fun f => by rw [hR _ (h.cf_X f), hI.1 f],
    fun r g hr => by rw [hR _ (h.rs_X r)]; exact hI.2.1 r g hr,
    fun r => by rw [hR _ (h.tmps_X r), hI.2.2.1 r],
    fun s => by rw [hR _ (h.scr_X s), hI.2.2.2.1 s],
    fun q => by rw [hR _ (h.prm_X q), hI.2.2.2.2 q]⟩

/-- The state after the preparation. -/
lemma IdxStateP.of_prep (h : IdxLayoutP cf len L rs tmps rsrc scr prm st X)
    {R R' : Fin T → List (Fin (A + 4))} {i : ℕ} (hI : IdxStateP cf len L rs tmps rsrc scr prm P₀ R i)
    (hp : ∀ r g, rsrc r = .inr g → R' (rs r) = binSyms L (g i))
    (hR : ∀ k, (∀ r g, rsrc r = .inr g → k ≠ rs r) → R' k = R k) :
    IdxStateP cf len L rs tmps rsrc scr prm P₀ R' i :=
  ⟨fun f => by rw [hR _ (fun r' g' hr' e => h.param r' g' f hr' e.symm), hI.1 f],
    fun r g hr => by rw [hp r g hr]; simp [binSyms],
    fun r => by rw [hR _ (fun r' _ _ e => h.rs_tmps r' r e.symm), hI.2.2.1 r],
    fun s => by rw [hR _ (fun r' _ _ e => h.scr_rs s r' e), hI.2.2.2.1 s],
    fun q => by rw [hR _ (fun r' _ _ e => h.prm_rs q r' e), hI.2.2.2.2 q]⟩

/-- The state after an increment of the fields. -/
lemma IdxStateP.of_incr (h : IdxLayoutP cf len L rs tmps rsrc scr prm st X)
    {R R' : Fin T → List (Fin (A + 4))} {i : ℕ} (hI : IdxStateP cf len L rs tmps rsrc scr prm P₀ R i)
    (hcf : ∀ f, R' (cf f) = binSyms (len f) (digit len f (i + 1)))
    (hR : ∀ k, (∀ f, k ≠ cf f) → R' k = R k) : IdxStateP cf len L rs tmps rsrc scr prm P₀ R' (i + 1) :=
  ⟨hcf, fun r g hr => by rw [hR _ (h.param r g · hr)]; exact hI.2.1 r g hr,
    fun r => by rw [hR _ (h.tmps_cf r), hI.2.2.1 r],
    fun s => by rw [hR _ (h.scr_cf s), hI.2.2.2.1 s],
    fun q => by rw [hR _ (h.prm_cf q), hI.2.2.2.2 q]⟩

end Layout

/-! ### One record -/

/-- One record of the prepared index loops: the preparation, a code pass on the current index
into slot `st`, one block of `|ctr|` symbols from `src (code)` to `dst (code)`, an increment of
the fields, then the action `fin`. -/
def idxStepP [NeZero nr] (prep : Pr P T Q A U) (src dst : Fin nd → Fin T) (ctr tmp : Fin T)
    (cf : Fin nf → Fin T) (rs tmps : Fin nr → Fin T) (st : Fin T) (C : CAuto A nr nd)
    (fin : Act T Q A U) : Pr P T Q A U :=
  .seq prep (idxStep src dst ctr tmp cf rs tmps st C fin)

/-- The step bound of one record without the preparation. -/
def idxStepCost (B L : ℕ) (len : Fin nf → ℕ) : ℕ :=
  4 * B + 6 * L + 4 * (∑ f, len f) + 4 * nf + 12

variable (body : P → Pr P T Q A U)

/-- One record: the preparation, then the code `d` of index `i` selects the transfer of `ys`
(as many symbols as `ctr`) from the top of `src d` to `dst d`; then the fields advance to
`i + 1`. At most `cP + idxStepCost |ctr| L len` steps, the final action `fin` included. -/
theorem idxStepP_exec [NeZero nr] {prep : Pr P T Q A U} (src dst : Fin nd → Fin T) (ctr tmp : Fin T)
    (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ)) (scr : Fin ns → Fin T) (prm : Fin np → Fin T)
    (P₀ : Fin np → List (Fin (A + 4))) (st : Fin T) (C : CAuto A nr nd)
    (fin : Act T Q A U) {cP : ℕ} (hprep : PrepSpec body prep cf len L rs tmps rsrc scr prm P₀ cP) (i : ℕ)
    {X : Fin T → Prop} (h : IdxLayoutP cf len L rs tmps rsrc scr prm st X)
    (hX : ∀ k, k = ctr ∨ k = tmp ∨ k = src (idxCodeP C L len rsrc i) ∨
      k = dst (idxCodeP C L len rsrc i) → X k)
    (h1 : src (idxCodeP C L len rsrc i) ≠ ctr) (h2 : src (idxCodeP C L len rsrc i) ≠ tmp)
    (h3 : ctr ≠ tmp) (h4 : dst (idxCodeP C L len rsrc i) ≠ src (idxCodeP C L len rsrc i))
    (h5 : dst (idxCodeP C L len rsrc i) ≠ ctr) (h6 : dst (idxCodeP C L len rsrc i) ≠ tmp)
    (c ys rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hlen : c.length = ys.length) (hc : S.R ctr = c) (ht : S.R tmp = [])
    (hs : S.R (src (idxCodeP C L len rsrc i)) = ys ++ rest)
    (hI : IdxStateP cf len L rs tmps rsrc scr prm P₀ S.R i) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ cP + idxStepCost c.length L len ∧
      Exec body (idxStepP prep src dst ctr tmp cf rs tmps st C fin) (mk v S) m
        (fin.run (mk v' { S with R := R' })) ∧
      R' (src (idxCodeP C L len rsrc i)) = rest ∧
      R' (dst (idxCodeP C L len rsrc i)) = ys.reverse ++ S.R (dst (idxCodeP C L len rsrc i)) ∧
      IdxStateP cf len L rs tmps rsrc scr prm P₀ R' (i + 1) ∧
      ∀ k, k ≠ src (idxCodeP C L len rsrc i) → k ≠ dst (idxCodeP C L len rsrc i) →
        (∀ f, k ≠ cf f) → (∀ r g, rsrc r = .inr g → k ≠ rs r) → R' k = S.R k := by
  set d := idxCodeP C L len rsrc i with hd
  -- the preparation
  obtain ⟨v₀, R₀, m₀, hu₀, hm₀, he₀, hp₀, hfr₀⟩ := hprep.run i v S hI
  have hcomp : ∀ k, X k → (∀ r g, rsrc r = .inr g → k ≠ rs r) := fun k hk r g _ e =>
    h.rs_X r (e ▸ hk)
  have hI₀ : IdxStateP cf len L rs tmps rsrc scr prm P₀ R₀ i := hI.of_prep h hp₀ hfr₀
  have hctr₀ : R₀ ctr = c := by rw [hfr₀ _ (hcomp _ (hX _ (Or.inl rfl))), hc]
  have htmp₀ : R₀ tmp = [] := by rw [hfr₀ _ (hcomp _ (hX _ (Or.inr (Or.inl rfl)))), ht]
  have hs₀ : R₀ (src d) = ys ++ rest := by
    rw [hfr₀ _ (hcomp _ (hX _ (Or.inr (Or.inr (Or.inl rfl))))), hs]
  -- the code pass
  obtain ⟨v₁, hu₁, hs₁, he₁⟩ := codePass_exec body h.toCodeLayout C L (regValP len rsrc i) v₀
    { S with R := R₀ } (hI.rs_eq h hp₀ hfr₀) hI₀.2.2.1
  -- the transfer
  obtain ⟨v₂, R₁, hu₂, _, he₂, hctr₁, htmp₁, hsrc₁, hdst₁, hoth₁⟩ :=
    xferBlock_exec body src dst ctr tmp st 1 (codeSel C) .done d h1 h2 h3 h4 h5 h6 c ys rest v₁
      { S with R := R₀ } hlen hctr₀ htmp₀ hs₀ (by rw [hs₁, codeSel_val]; rfl)
  rw [run_done] at he₂
  have hfr₁ : ∀ k, ¬ X k → R₁ k = R₀ k := fun k hk =>
    hoth₁ k (fun e => hk (hX k (Or.inr (Or.inr (Or.inl e)))))
      (fun e => hk (hX k (Or.inl e))) (fun e => hk (hX k (Or.inr (Or.inl e))))
      (fun e => hk (hX k (Or.inr (Or.inr (Or.inr e)))))
  have hI₁ : IdxStateP cf len L rs tmps rsrc scr prm P₀ R₁ i := hI₀.of_frame h hfr₁
  -- the increment
  obtain ⟨v₃, R₂, hu₃, he₃, hcf₃, hoth₃⟩ := incrFields_exec body cf h.cf_inj tmp st
    (fun f e => h.cf_X f (hX _ (Or.inr (Or.inl e)))) len i _ { S with R := R₁ } htmp₁ hI₁.1
  refine ⟨v₃, R₂, m₀ + (6 * L + 4 + (4 * c.length + 5 + ((4 * (∑ f, len f) + 4 * nf + 2) + 1))),
    by rw [hu₃]; simp [hu₂, hu₁, hu₀], ?_,
    Exec.cast (Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂
      (Exec.seq he₃ (Exec.act (body := body) fin _))))) rfl rfl, ?_, ?_,
    hI₁.of_incr h hcf₃ hoth₃, ?_⟩
  · unfold idxStepCost; omega
  · rw [hoth₃ _ (fun f e => h.cf_X f (hX _ (Or.inr (Or.inr (Or.inl e.symm)))))]
    exact hsrc₁
  · rw [hoth₃ _ (fun f e => h.cf_X f (hX _ (Or.inr (Or.inr (Or.inr e.symm)))))]
    show R₁ (dst d) = ys.reverse ++ S.R (dst d)
    rw [hdst₁]
    show ys.reverse ++ R₀ (dst d) = _
    rw [hfr₀ _ (hcomp _ (hX _ (Or.inr (Or.inr (Or.inr rfl)))))]
  · intro k hk1 hk2 hk3 hk4
    rw [hoth₃ k hk3]
    show R₁ k = S.R k
    by_cases hkc : k = ctr
    · subst hkc; rw [hctr₁, hc]
    by_cases hkt : k = tmp
    · subst hkt; rw [htmp₁, ht]
    rw [hoth₁ k hk1 hkc hkt hk2]
    show R₀ k = S.R k
    exact hfr₀ k hk4

/-! ### Routing -/

/-- Route the records of `src` by index code, preparing the computed registers per record. -/
def routeIdxP [NeZero nr] (prep : Pr P T Q A U) (src : Fin T) (dst : Fin nd → Fin T)
    (ctr tmp : Fin T) (cf : Fin nf → Fin T) (rs tmps : Fin nr → Fin T) (st : Fin T)
    (C : CAuto A nr nd) : Pr P T Q A U :=
  .seq (.act (peekR src))
    (.loop (·.flag) (idxStepP prep (fun _ => src) dst ctr tmp cf rs tmps st C (peekR src)))

/-- The record loop of `routeIdxP`, from index `i` with `m` records left. -/
theorem routeIdxP_loop [NeZero nr] {prep : Pr P T Q A U} (src : Fin T) (dst : Fin nd → Fin T)
    (ctr tmp : Fin T) (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ)) (scr : Fin ns → Fin T) (prm : Fin np → Fin T)
    (P₀ : Fin np → List (Fin (A + 4))) (st : Fin T) (C : CAuto A nr nd)
    {cP : ℕ} (hprep : PrepSpec body prep cf len L rs tmps rsrc scr prm P₀ cP)
    (h : IdxLayoutP cf len L rs tmps rsrc scr prm st (routeRegs src dst ctr tmp))
    (h1 : src ≠ ctr) (h2 : src ≠ tmp) (h3 : ctr ≠ tmp) (h4 : ∀ d, dst d ≠ src)
    (h5 : ∀ d, dst d ≠ ctr) (h6 : ∀ d, dst d ≠ tmp) (hinj : Function.Injective dst) {B : ℕ}
    (hB : 1 ≤ B) (c : List (Fin (A + 4))) (hcB : c.length = B) :
    ∀ (m i : ℕ) (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      l.length = m * B → S.R src = l → S.R ctr = c → S.R tmp = [] →
      IdxStateP cf len L rs tmps rsrc scr prm P₀ S.R i → v.flag = l.head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (mm : ℕ), v'.user = v.user ∧
        mm ≤ m * (cP + idxStepCost B L len + 1) + 1 ∧
        Exec body (.loop (·.flag)
            (idxStepP prep (fun _ => src) dst ctr tmp cf rs tmps st C (peekR src)))
          (mk v S) mm (mk v' { S with R := R' }) ∧
        R' src = [] ∧ IdxStateP cf len L rs tmps rsrc scr prm P₀ R' (i + m) ∧
        (∀ d, R' (dst d) = (blocksIdx l B m (idxCodeP C L len rsrc) i d).reverse ++ S.R (dst d)) ∧
        ∀ k, k ≠ src → (∀ d, dst d ≠ k) → (∀ f, cf f ≠ k) →
          (∀ r g, rsrc r = .inr g → rs r ≠ k) → R' k = S.R k := by
  have hrs : ∀ k, routeRegs src dst ctr tmp k → ∀ r g, rsrc r = .inr g → rs r ≠ k :=
    fun k hk r _ _ e => h.rs_X r (e ▸ hk)
  intro m
  induction m with
  | zero =>
      intro i l v S hl hs _ _ hI hf
      obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      exact ⟨v, S.R, 1, rfl, by simp, Exec.cast (.loop_false (by simpa using hf)) rfl rfl, hs,
        hI, fun d => by simp, fun _ _ _ _ _ => rfl⟩
  | succ m ih =>
      intro i l v S hl hs hc ht hI hf
      have hlB : B ≤ l.length := by rw [hl]; nlinarith
      obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hsrc₁, hdst₁, hI₁, hoth₁⟩ :=
        idxStepP_exec body (fun _ => src) dst ctr tmp cf len L rs tmps rsrc scr prm P₀ st C (peekR src)
          hprep i h
          (fun k hk => by rcases hk with rfl | rfl | rfl | rfl <;> simp [routeRegs])
          h1 h2 h3 (h4 _) (h5 _) (h6 _) c (l.take B) (l.drop B) v S (by simp [hcB]; omega) hc ht
          (by simp [hs]) hI
      rw [peekR_run] at he₁
      have hfr₁ : ∀ k, k ≠ src → k ≠ dst (idxCodeP C L len rsrc i) → (∀ f, cf f ≠ k) →
          (∀ r g, rsrc r = .inr g → rs r ≠ k) → R₁ k = S.R k :=
        fun k hk1 hk2 hk3 hk4 => hoth₁ k hk1 hk2 (fun f => (hk3 f).symm)
          (fun r g hr => (hk4 r g hr).symm)
      have hcf : ∀ f k, routeRegs src dst ctr tmp k → cf f ≠ k :=
        fun f k hk e => h.cf_X f (e ▸ hk)
      have hctr₁ : R₁ ctr = c := by
        rw [← hc]
        exact hfr₁ ctr (Ne.symm h1) (Ne.symm (h5 _)) (fun f => hcf f _ (by simp [routeRegs]))
          (hrs _ (by simp [routeRegs]))
      have htmp₁ : R₁ tmp = [] := by
        rw [← ht]
        exact hfr₁ tmp (Ne.symm h2) (Ne.symm (h6 _)) (fun f => hcf f _ (by simp [routeRegs]))
          (hrs _ (by simp [routeRegs]))
      obtain ⟨v', R', mm, hu, hmm, he, hsrc, hI', hdst, hoth⟩ := ih (i + 1) (l.drop B)
        { v₁ with flag := (R₁ src).head?.isSome } { S with R := R₁ }
        (by simp [hl, Nat.add_one_mul]) hsrc₁ hctr₁ htmp₁ hI₁ (by simp [hsrc₁])
      have hne : l ≠ [] := by
        intro e; rw [e] at hlB; simp at hlB; omega
      refine ⟨v', R', m₁ + mm + 1, by rw [hu, hu₁], ?_, Exec.cast (Exec.loop_true (body := body)
        (f := (·.flag)) (by simpa [hf] using hne) he₁ he) rfl rfl, hsrc,
        by rw [show i + (m + 1) = i + 1 + m by ring]; exact hI', ?_, ?_⟩
      · rw [hcB] at hm₁
        rw [Nat.add_one_mul]
        omega
      · intro d
        rw [hdst, blocksIdx_succ]
        show (blocksIdx _ B m _ (i + 1) d).reverse ++ R₁ (dst d) = _
        by_cases hd : idxCodeP C L len rsrc i = d
        · subst hd
          simp [hdst₁]
        · rw [hfr₁ (dst d) (h4 d) (fun e => hd (hinj e).symm)
            (fun f => hcf f _ (by simp [routeRegs])) (hrs _ (by simp [routeRegs]))]
          simp [hd]
      · intro k hk1 hk2 hk3 hk4
        exact (hoth k hk1 hk2 hk3 hk4).trans (hfr₁ k hk1 (fun e => hk2 _ e.symm) hk3 hk4)

/-- Routing `nb` records of `B ≥ 1` symbols by prepared index code. At most
`nb * (cP + idxStepCost B L len + 1) + 2` steps. -/
theorem routeIdxP_exec [NeZero nr] {prep : Pr P T Q A U} (src : Fin T) (dst : Fin nd → Fin T)
    (ctr tmp : Fin T) (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ) (rs tmps : Fin nr → Fin T)
    (rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ)) (scr : Fin ns → Fin T) (prm : Fin np → Fin T)
    (P₀ : Fin np → List (Fin (A + 4))) (st : Fin T) (C : CAuto A nr nd)
    {cP : ℕ} (hprep : PrepSpec body prep cf len L rs tmps rsrc scr prm P₀ cP)
    (h : IdxLayoutP cf len L rs tmps rsrc scr prm st (routeRegs src dst ctr tmp))
    (hreg : [src, ctr, tmp].Nodup) (hdst : ∀ d, dst d ∉ [src, ctr, tmp])
    (hinj : Function.Injective dst) {l c : List (Fin (A + 4))} {nb B i₀ : ℕ} (hB : 1 ≤ B)
    (hl : l.length = nb * B) (hcB : c.length = B) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = l) (hc : S.R ctr = c) (ht : S.R tmp = [])
    (hI : IdxStateP cf len L rs tmps rsrc scr prm P₀ S.R i₀) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (mm : ℕ), v'.user = v.user ∧
      mm ≤ nb * (cP + idxStepCost B L len + 1) + 2 ∧
      Exec body (routeIdxP prep src dst ctr tmp cf rs tmps st C) (mk v S) mm
        (mk v' { S with R := R' }) ∧
      R' src = [] ∧
      (∀ d, R' (dst d) = (blocksIdx l B nb (idxCodeP C L len rsrc) i₀ d).reverse ++ S.R (dst d)) ∧
      IdxStateP cf len L rs tmps rsrc scr prm P₀ R' (i₀ + nb) ∧
      ∀ k, k ≠ src → (∀ d, dst d ≠ k) → (∀ f, cf f ≠ k) →
        (∀ r g, rsrc r = .inr g → rs r ≠ k) → R' k = S.R k := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg hdst
  obtain ⟨⟨h1, h2⟩, h3⟩ := hreg
  obtain ⟨v', R', mm, hu, hmm, he, hsrc, hI', hd, hoth⟩ :=
    routeIdxP_loop body src dst ctr tmp cf len L rs tmps rsrc scr prm P₀ st C hprep h h1 h2 h3
      (fun d => (hdst d).1) (fun d => (hdst d).2.1) (fun d => (hdst d).2.2) hinj hB c hcB nb i₀ l
      { v with flag := (S.R src).head?.isSome } S hl hs hc ht hI (by rw [hs])
  exact ⟨v', R', 1 + mm, hu, by omega, Exec.cast (Exec.seq (peekR_run src v S ▸
    Exec.act (body := body) (peekR src) (mk v S)) he) rfl rfl, hsrc, hd, hI', hoth⟩

/-! ### Merging -/

/-- Merge records by prepared index code. -/
def mergeIdxP [NeZero nr] (prep : Pr P T Q A U) (srcs : Fin nd → Fin T)
    (dst ctr tmp cnt ctmp : Fin T) (cf : Fin nf → Fin T) (rs tmps : Fin nr → Fin T) (st : Fin T)
    (C : CAuto A nr nd) : Pr P T Q A U :=
  .seq (.act (peekR cnt))
    (.seq (.loop (·.flag)
        (idxStepP prep srcs (fun _ => dst) ctr tmp cf rs tmps st C (moveStep cnt ctmp id)))
      (moveR ctmp cnt id))

/-- The record loop of `mergeIdxP`. -/
theorem mergeIdxP_loop [NeZero nr] {prep : Pr P T Q A U} (srcs : Fin nd → Fin T)
    (dst ctr tmp cnt ctmp : Fin T) (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ)
    (rs tmps : Fin nr → Fin T) (rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ)) (scr : Fin ns → Fin T) (prm : Fin np → Fin T)
    (P₀ : Fin np → List (Fin (A + 4))) (st : Fin T) (C : CAuto A nr nd) {cP : ℕ}
    (hprep : PrepSpec body prep cf len L rs tmps rsrc scr prm P₀ cP)
    (h : IdxLayoutP cf len L rs tmps rsrc scr prm st (mergeRegs srcs dst ctr tmp cnt ctmp))
    (h1 : ∀ d, srcs d ≠ ctr) (h2 : ∀ d, srcs d ≠ tmp) (h3 : ctr ≠ tmp) (h4 : ∀ d, dst ≠ srcs d)
    (h5 : dst ≠ ctr) (h6 : dst ≠ tmp) (h7 : ∀ d, srcs d ≠ cnt) (h8 : ∀ d, srcs d ≠ ctmp)
    (h9 : dst ≠ cnt) (h10 : dst ≠ ctmp) (h11 : ctr ≠ cnt) (h12 : ctr ≠ ctmp) (h13 : tmp ≠ cnt)
    (h14 : tmp ≠ ctmp) (h15 : cnt ≠ ctmp) (hinj : Function.Injective srcs) {B : ℕ}
    (c : List (Fin (A + 4))) (hcB : c.length = B) :
    ∀ (kk : List (Fin (A + 4))) (j : ℕ) (s : Fin nd → List (Fin (A + 4))) (v : HS T Q A U)
      (S : Stacks T A),
      S.R cnt = kk → (∀ d, S.R (srcs d) = s d) →
      (∀ d, idxCount (idxCodeP C L len rsrc) j kk.length d * B ≤ (s d).length) →
      S.R ctr = c → S.R tmp = [] → IdxStateP cf len L rs tmps rsrc scr prm P₀ S.R j →
      v.flag = kk.head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (mm : ℕ), v'.user = v.user ∧
        mm ≤ kk.length * (cP + idxStepCost B L len + 1) + 1 ∧
        Exec body (.loop (·.flag)
            (idxStepP prep srcs (fun _ => dst) ctr tmp cf rs tmps st C (moveStep cnt ctmp id)))
          (mk v S) mm (mk v' { S with R := R' }) ∧
        R' cnt = [] ∧ R' ctmp = kk.reverse ++ S.R ctmp ∧
        R' dst = (mergeIdxList B (idxCodeP C L len rsrc) kk.length j s).1.reverse ++ S.R dst ∧
        (∀ d, R' (srcs d) = (mergeIdxList B (idxCodeP C L len rsrc) kk.length j s).2 d) ∧
        IdxStateP cf len L rs tmps rsrc scr prm P₀ R' (j + kk.length) ∧
        ∀ k, k ≠ dst → k ≠ cnt → k ≠ ctmp → (∀ d, srcs d ≠ k) → (∀ f, cf f ≠ k) →
          (∀ r g, rsrc r = .inr g → rs r ≠ k) → R' k = S.R k := by
  have hcf : ∀ f k, mergeRegs srcs dst ctr tmp cnt ctmp k → cf f ≠ k :=
    fun f k hk e => h.cf_X f (e ▸ hk)
  have hrs : ∀ k, mergeRegs srcs dst ctr tmp cnt ctmp k → ∀ r g, rsrc r = .inr g → rs r ≠ k :=
    fun k hk r _ _ e => h.rs_X r (e ▸ hk)
  intro kk
  induction kk with
  | nil =>
      intro j s v S hk hs _ _ _ hI hf
      exact ⟨v, S.R, 1, rfl, by simp, Exec.cast (.loop_false (by simpa using hf)) rfl rfl, hk,
        rfl, by simp [mergeIdxList], fun d => by simp [mergeIdxList, hs], by simpa using hI,
        fun _ _ _ _ _ _ _ => rfl⟩
  | cons e kk ih =>
      intro j s v S hk hs hfit hc ht hI hf
      set code := idxCodeP C L len rsrc with hcode
      have hfit₀ := hfit (code j)
      rw [List.length_cons, idxCount_succ] at hfit₀
      simp only [↓reduceIte] at hfit₀
      have hB : B ≤ (s (code j)).length := by nlinarith
      obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hsrc₁, hdst₁, hI₁, hoth₁⟩ :=
        idxStepP_exec body srcs (fun _ => dst) ctr tmp cf len L rs tmps rsrc scr prm P₀ st C
          (moveStep cnt ctmp id) hprep j h
          (fun k hk => by rcases hk with rfl | rfl | rfl | rfl <;> simp [mergeRegs])
          (h1 _) (h2 _) h3 (h4 _) h5 h6 c ((s (code j)).take B) ((s (code j)).drop B) v S
          (by simp [hcB]; omega) hc ht (by rw [hs, List.take_append_drop]) hI
      have hfr₁ : ∀ k, k ≠ srcs (code j) → k ≠ dst → (∀ f, cf f ≠ k) →
          (∀ r g, rsrc r = .inr g → rs r ≠ k) → R₁ k = S.R k :=
        fun k hk1 hk2 hk3 hk4 => hoth₁ k hk1 hk2 (fun f => (hk3 f).symm)
          (fun r g hr => (hk4 r g hr).symm)
      have hcnt₁ : R₁ cnt = e :: kk := by
        rw [hfr₁ cnt (h7 _).symm h9.symm (fun f => hcf f _ (by simp [mergeRegs]))
          (hrs _ (by simp [mergeRegs])), hk]
      have hct₁ : R₁ ctmp = S.R ctmp :=
        hfr₁ ctmp (h8 _).symm h10.symm (fun f => hcf f _ (by simp [mergeRegs]))
          (hrs _ (by simp [mergeRegs]))
      have hrun : (moveStep cnt ctmp id : Act T Q A U).run (mk v₁ { S with R := R₁ }) =
          mk { v₁ with sym := some e, flag := kk.head?.isSome }
            { S with R := Function.update (Function.update R₁ cnt kk) ctmp (e :: R₁ ctmp) } := by
        simp [moveStep, peekR, Action.run, hcnt₁, update_rt, Function.update_of_ne h15,
          Function.update_of_ne h15.symm]
      rw [hrun] at he₁
      set R₂ := Function.update (Function.update R₁ cnt kk) ctmp (e :: R₁ ctmp) with hR₂
      have hfr₂ : ∀ k, k ≠ cnt → k ≠ ctmp → R₂ k = R₁ k := fun k hk1 hk2 => by
        simp [hR₂, Function.update_of_ne hk1, Function.update_of_ne hk2]
      set s' := Function.update s (code j) ((s (code j)).drop B) with hs'
      obtain ⟨v', R', mm, hu, hmm, he, hcnt, hct, hdst, hsrc, hI', hoth⟩ := ih (j + 1) s'
        { v₁ with sym := some e, flag := kk.head?.isSome } { S with R := R₂ }
        (by simp [hR₂, Function.update_of_ne h15])
        (by
          intro d
          show R₂ (srcs d) = s' d
          rw [hfr₂ _ (h7 d) (h8 d)]
          by_cases hd : d = code j
          · subst hd; rw [hsrc₁, hs', Function.update_self]
          · rw [hfr₁ _ (fun e => hd (hinj e)) (h4 d).symm
              (fun f => hcf f _ (by simp [mergeRegs])) (hrs _ (by simp [mergeRegs])), hs d, hs',
              Function.update_of_ne hd])
        (by
          intro d
          have hd' := hfit d
          rw [List.length_cons, idxCount_succ] at hd'
          by_cases hd : d = code j
          · subst hd
            rw [hs', Function.update_self, List.length_drop]
            simp only [↓reduceIte] at hd'
            have := Nat.add_mul 1 (idxCount code (j + 1) kk.length (code j)) B
            omega
          · rw [hs', Function.update_of_ne hd]
            simp only [Ne.symm hd, ↓reduceIte, Nat.zero_add] at hd'
            exact hd')
        (by
          show R₂ ctr = c
          rw [hfr₂ _ h11 h12, hfr₁ _ (h1 _).symm h5.symm
            (fun f => hcf f _ (by simp [mergeRegs])) (hrs _ (by simp [mergeRegs])), hc])
        (by
          show R₂ tmp = []
          rw [hfr₂ _ h13 h14, hfr₁ _ (h2 _).symm h6.symm
            (fun f => hcf f _ (by simp [mergeRegs])) (hrs _ (by simp [mergeRegs])), ht])
        (hI₁.of_frame h (fun k hk => hfr₂ k (fun e => hk (by simp [mergeRegs, e]))
          (fun e => hk (by simp [mergeRegs, e])))) rfl
      refine ⟨v', R', m₁ + mm + 1, by rw [hu, hu₁], ?_, Exec.cast (Exec.loop_true (body := body)
        (f := (·.flag)) (by simpa using hf) he₁ he) rfl rfl, hcnt, ?_, ?_, hsrc,
        by rw [List.length_cons, show j + (kk.length + 1) = j + 1 + kk.length by ring]; exact hI',
        ?_⟩
      · rw [hcB] at hm₁
        rw [List.length_cons, Nat.add_one_mul]
        omega
      · rw [hct]
        show kk.reverse ++ R₂ ctmp = _
        simp [hR₂, hct₁]
      · rw [hdst]
        show _ ++ R₂ dst = _
        rw [hfr₂ _ h9 h10, hdst₁]
        simp [mergeIdxList, hs']
      · intro k hk1 hk2 hk3 hk4 hk5 hk6
        rw [hoth k hk1 hk2 hk3 hk4 hk5 hk6]
        show R₂ k = S.R k
        rw [hfr₂ k hk2 hk3]
        exact hfr₁ k (fun e => hk4 _ e.symm) hk1 hk5 hk6

/-- Merging `nb` records of `B` symbols by prepared index code. At most
`nb * (cP + idxStepCost B L len + 3) + 4` steps. -/
theorem mergeIdxP_exec [NeZero nr] {prep : Pr P T Q A U} (srcs : Fin nd → Fin T)
    (dst ctr tmp cnt ctmp : Fin T) (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ)
    (rs tmps : Fin nr → Fin T) (rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ)) (scr : Fin ns → Fin T) (prm : Fin np → Fin T)
    (P₀ : Fin np → List (Fin (A + 4))) (st : Fin T) (C : CAuto A nr nd) {cP : ℕ}
    (hprep : PrepSpec body prep cf len L rs tmps rsrc scr prm P₀ cP)
    (h : IdxLayoutP cf len L rs tmps rsrc scr prm st (mergeRegs srcs dst ctr tmp cnt ctmp))
    (hreg : [dst, ctr, tmp, cnt, ctmp].Nodup) (hsrcs : ∀ d, srcs d ∉ [dst, ctr, tmp, cnt, ctmp])
    (hinj : Function.Injective srcs) {c kk : List (Fin (A + 4))} {nb B i₀ : ℕ}
    (hcB : c.length = B) (hk : kk.length = nb) (s : Fin nd → List (Fin (A + 4)))
    (hfit : ∀ d, idxCount (idxCodeP C L len rsrc) i₀ nb d * B ≤ (s d).length)
    (v : HS T Q A U) (S : Stacks T A) (hs : ∀ d, S.R (srcs d) = s d) (hc : S.R ctr = c)
    (ht : S.R tmp = []) (hcnt : S.R cnt = kk) (hct : S.R ctmp = [])
    (hI : IdxStateP cf len L rs tmps rsrc scr prm P₀ S.R i₀) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (mm : ℕ), v'.user = v.user ∧
      mm ≤ nb * (cP + idxStepCost B L len + 3) + 4 ∧
      Exec body (mergeIdxP prep srcs dst ctr tmp cnt ctmp cf rs tmps st C) (mk v S) mm
        (mk v' { S with R := R' }) ∧
      R' dst = (mergeIdxList B (idxCodeP C L len rsrc) nb i₀ s).1.reverse ++ S.R dst ∧
      (∀ d, R' (srcs d) = (mergeIdxList B (idxCodeP C L len rsrc) nb i₀ s).2 d) ∧
      IdxStateP cf len L rs tmps rsrc scr prm P₀ R' (i₀ + nb) ∧
      ∀ k, k ≠ dst → (∀ d, srcs d ≠ k) → (∀ f, cf f ≠ k) →
        (∀ r g, rsrc r = .inr g → rs r ≠ k) → R' k = S.R k := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg hsrcs
  obtain ⟨⟨h5, h6, h9, h10⟩, ⟨h3, h11, h12⟩, ⟨h13, h14⟩, h15⟩ := hreg
  subst hk
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hcnt₁, hct₁, hdst₁, hsrc₁, hI₁, hoth₁⟩ :=
    mergeIdxP_loop body srcs dst ctr tmp cnt ctmp cf len L rs tmps rsrc scr prm P₀ st C hprep h
      (fun d => (hsrcs d).2.1) (fun d => (hsrcs d).2.2.1) h3 (fun d => Ne.symm (hsrcs d).1) h5 h6
      (fun d => (hsrcs d).2.2.2.1) (fun d => (hsrcs d).2.2.2.2) h9 h10 h11 h12 h13 h14 h15 hinj
      c hcB kk i₀ s { v with flag := (S.R cnt).head?.isSome } S hcnt hs hfit hc ht hI
      (by simp [hcnt])
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body ctmp cnt (Ne.symm h15) id v₁ { S with R := R₁ }
  have hcf_cnt : ∀ f, cf f ≠ cnt := fun f e => h.cf_X f (by simp [mergeRegs, e])
  have hcf_ctmp : ∀ f, cf f ≠ ctmp := fun f e => h.cf_X f (by simp [mergeRegs, e])
  refine ⟨v₂, movedR R₁ ctmp cnt id (R₁ ctmp), 1 + (m₁ + (2 * (R₁ ctmp).length + 2)),
    by rw [hu₂, hu₁], ?_,
    Exec.cast (Exec.seq (peekR_run cnt v S ▸ Exec.act (body := body) (peekR cnt) (mk v S))
      (Exec.seq he₁ he₂)) rfl rfl, ?_, ?_, ?_, ?_⟩
  · rw [hct₁, hct]; simp; nlinarith [hm₁]
  · simp [movedR, h9, h10, hdst₁]
  · intro d; simp [movedR, (hsrcs d).2.2.2.1, (hsrcs d).2.2.2.2, hsrc₁]
  · refine hI₁.of_frame h ?_
    intro k hk
    have hk1 : k ≠ cnt := fun e => hk (by simp [mergeRegs, e])
    have hk2 : k ≠ ctmp := fun e => hk (by simp [mergeRegs, e])
    simp [movedR, hk1, hk2]
  · intro k hk1 hk2 hk3 hk6
    by_cases hk4 : k = cnt
    · subst hk4; simp [movedR, hct₁, hct, hcnt₁, hcnt]
    by_cases hk5 : k = ctmp
    · subst hk5; simp [movedR, Ne.symm h15, hct]
    simp [movedR, hk4, hk5, hoth₁ k hk1 hk4 hk5 hk2 hk3 hk6]

/-- `mergeIdxP_exec` on routed sources. -/
theorem mergeIdxP_exec_blocks [NeZero nr] {prep : Pr P T Q A U} (srcs : Fin nd → Fin T)
    (dst ctr tmp cnt ctmp : Fin T) (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (L : ℕ)
    (rs tmps : Fin nr → Fin T) (rsrc : Fin nr → Fin nf ⊕ (ℕ → ℕ)) (scr : Fin ns → Fin T) (prm : Fin np → Fin T)
    (P₀ : Fin np → List (Fin (A + 4))) (st : Fin T) (C : CAuto A nr nd) {cP : ℕ}
    (hprep : PrepSpec body prep cf len L rs tmps rsrc scr prm P₀ cP)
    (h : IdxLayoutP cf len L rs tmps rsrc scr prm st (mergeRegs srcs dst ctr tmp cnt ctmp))
    (hreg : [dst, ctr, tmp, cnt, ctmp].Nodup) (hsrcs : ∀ d, srcs d ∉ [dst, ctr, tmp, cnt, ctmp])
    (hinj : Function.Injective srcs) {l c kk : List (Fin (A + 4))} {nb B i₀ : ℕ}
    (hl : l.length = nb * B) (hcB : c.length = B) (hk : kk.length = nb)
    (rest : Fin nd → List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hs : ∀ d, S.R (srcs d) = blocksIdx l B nb (idxCodeP C L len rsrc) i₀ d ++ rest d)
    (hc : S.R ctr = c) (ht : S.R tmp = []) (hcnt : S.R cnt = kk) (hct : S.R ctmp = [])
    (hI : IdxStateP cf len L rs tmps rsrc scr prm P₀ S.R i₀) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (mm : ℕ), v'.user = v.user ∧
      mm ≤ nb * (cP + idxStepCost B L len + 3) + 4 ∧
      Exec body (mergeIdxP prep srcs dst ctr tmp cnt ctmp cf rs tmps st C) (mk v S) mm
        (mk v' { S with R := R' }) ∧
      R' dst = l.reverse ++ S.R dst ∧ (∀ d, R' (srcs d) = rest d) ∧
      IdxStateP cf len L rs tmps rsrc scr prm P₀ R' (i₀ + nb) ∧
      ∀ k, k ≠ dst → (∀ d, srcs d ≠ k) → (∀ f, cf f ≠ k) →
        (∀ r g, rsrc r = .inr g → rs r ≠ k) → R' k = S.R k := by
  have hrt := mergeIdxList_blocksIdx B (idxCodeP C L len rsrc) nb i₀ l rest hl
  obtain ⟨v', R', mm, hu, hmm, he, hdst, hsrc, hI', hoth⟩ :=
    mergeIdxP_exec body srcs dst ctr tmp cnt ctmp cf len L rs tmps rsrc scr prm P₀ st C hprep h hreg
      hsrcs hinj hcB hk (fun d => blocksIdx l B nb (idxCodeP C L len rsrc) i₀ d ++ rest d)
      (fun d => by rw [List.length_append, length_blocksIdx _ _ _ _ _ _ hl]; omega)
      v S hs hc ht hcnt hct hI
  rw [hrt] at hdst hsrc
  exact ⟨v', R', mm, hu, hmm, he, hdst, hsrc, hI', hoth⟩

end IntegerMultBounds.MathlibTM2.Host
