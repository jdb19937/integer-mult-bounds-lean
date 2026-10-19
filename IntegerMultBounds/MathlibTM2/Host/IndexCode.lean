module

public import IntegerMultBounds.MathlibTM2.Host.IndexRoute

/-!
# Routing and merging records by a code program

`IntegerMultBounds.MathlibTM2.Host.IndexRoute` with the code pass replaced by any program that
computes the code of the current index. `CodeSpec body cp cf len st Y Inv sel code c` is the
contract of such a program `cp`:

* `Inv R i` says that the register file `R` holds index `i`: the field registers `cf f` hold the
  digits of `i` (`digits`); `Inv` depends only on the index registers `Y`, which contain the
  fields (`frame`), and it follows the fields to any other index (`reidx`);
* from any register file with `Inv R i`, `cp` leaves every stack as it was and a symbol in scan
  slot `st` whose selector `sel` is `code i`, in at most `c` steps (`runs`).

`routeIdxC` and `mergeIdxC` are `routeIdx` and `mergeIdx` with the code program; their exec
theorems are those of `IndexRoute` with the code pass charged `c` and step counts as bounds.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {nf nd : ℕ}

/-- The contract of a code program. -/
structure CodeSpec (cp : Pr P T Q A U) (cf : Fin nf → Fin T) (len : Fin nf → ℕ) (st : Fin T)
    (Y : Fin T → Prop) (Inv : (Fin T → List (Fin (A + 4))) → ℕ → Prop) (sel : ℕ → Fin nd)
    (code : ℕ → Fin nd) (c : ℕ) : Prop where
  runs : ∀ (i : ℕ) (v : HS T Q A U) (S : Stacks T A), Inv S.R i →
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ c ∧ sel (v'.scan st).val = code i ∧
      Exec body cp (mk v S) m (mk v' S)
  cf_inj : Function.Injective cf
  cf_Y : ∀ f, Y (cf f)
  digits : ∀ R i, Inv R i → ∀ f, R (cf f) = binSyms (len f) (digit len f i)
  frame : ∀ R R' i, Inv R i → (∀ k, Y k → R' k = R k) → Inv R' i
  reidx : ∀ R R' i j, Inv R i → (∀ f, R' (cf f) = binSyms (len f) (digit len f j)) →
    (∀ k, (∀ f, k ≠ cf f) → R' k = R k) → Inv R' j

variable {cp : Pr P T Q A U} {cf : Fin nf → Fin T} {len : Fin nf → ℕ} {st : Fin T}
  {Y : Fin T → Prop} {Inv : (Fin T → List (Fin (A + 4))) → ℕ → Prop} {sel : ℕ → Fin nd}
  {code : ℕ → Fin nd} {c : ℕ}

/-- One record: the code program on the current index into slot `st`, one block of `|ctr|`
symbols from `src (code)` to `dst (code)`, an increment of the fields `cf`, then `fin`. -/
def idxStepC (cp : Pr P T Q A U) (sel : ℕ → Fin nd) (src dst : Fin nd → Fin T) (ctr tmp : Fin T)
    (cf : Fin nf → Fin T) (st : Fin T) (fin : Act T Q A U) : Pr P T Q A U :=
  .seq cp (.seq (xferBlock src dst ctr tmp st 1 sel .done) (.seq (incrFields cf tmp st) (.act fin)))

/-- The step bound of one record. -/
def idxStepCost (c B : ℕ) (len : Fin nf → ℕ) : ℕ := c + 4 * B + 4 * (∑ f, len f) + 4 * nf + 8

theorem idxStepC_exec (cs : CodeSpec body cp cf len st Y Inv sel code c)
    (src dst : Fin nd → Fin T) (ctr tmp : Fin T) (fin : Act T Q A U) (i : ℕ)
    (hYc : ¬ Y ctr) (hYt : ¬ Y tmp) (hYs : ¬ Y (src (code i))) (hYd : ¬ Y (dst (code i)))
    (h1 : src (code i) ≠ ctr) (h2 : src (code i) ≠ tmp)
    (h3 : ctr ≠ tmp) (h4 : dst (code i) ≠ src (code i))
    (h5 : dst (code i) ≠ ctr) (h6 : dst (code i) ≠ tmp)
    (cc ys rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hlen : cc.length = ys.length) (hc : S.R ctr = cc) (ht : S.R tmp = [])
    (hs : S.R (src (code i)) = ys ++ rest) (hI : Inv S.R i) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ idxStepCost c cc.length len ∧
      Exec body (idxStepC cp sel src dst ctr tmp cf st fin) (mk v S) m
        (fin.run (mk v' { S with R := R' })) ∧
      R' (src (code i)) = rest ∧
      R' (dst (code i)) = ys.reverse ++ S.R (dst (code i)) ∧
      Inv R' (i + 1) ∧
      ∀ k, k ≠ src (code i) → k ≠ dst (code i) → (∀ f, k ≠ cf f) → R' k = S.R k := by
  set d := code i with hd
  obtain ⟨v₁, m₁, hu₁, hm₁, hs₁, he₁⟩ := cs.runs i v S hI
  obtain ⟨v₂, R₁, hu₂, _, he₂, hctr₁, htmp₁, hsrc₁, hdst₁, hoth₁⟩ :=
    xferBlock_exec body src dst ctr tmp st 1 sel .done d h1 h2 h3 h4 h5 h6 cc ys rest v₁ S
      hlen hc ht hs hs₁
  rw [run_done] at he₂
  have hfr₁ : ∀ k, Y k → R₁ k = S.R k := fun k hk =>
    hoth₁ k (fun e => hYs (e ▸ hk)) (fun e => hYc (e ▸ hk)) (fun e => hYt (e ▸ hk))
      (fun e => hYd (e ▸ hk))
  have hI₁ : Inv R₁ i := cs.frame S.R R₁ i hI hfr₁
  obtain ⟨v₃, R₂, hu₃, he₃, hcf₃, hoth₃⟩ := incrFields_exec body cf cs.cf_inj tmp st
    (fun f e => hYt (e ▸ cs.cf_Y f)) len i _ { S with R := R₁ } htmp₁ (cs.digits R₁ i hI₁)
  refine ⟨v₃, R₂, m₁ + (4 * cc.length + 5 + (4 * (∑ f, len f) + 4 * nf + 2 + 1)),
    by rw [hu₃]; simp [hu₂, hu₁], ?_, Exec.seq he₁ (Exec.seq he₂
    (Exec.seq he₃ (Exec.act (body := body) fin _))), ?_, ?_,
    cs.reidx R₁ R₂ i (i + 1) hI₁ hcf₃ hoth₃, ?_⟩
  · unfold idxStepCost; omega
  · rw [hoth₃ _ (fun f e => hYs (by rw [e]; exact cs.cf_Y f))]
    exact hsrc₁
  · rw [hoth₃ _ (fun f e => hYd (by rw [e]; exact cs.cf_Y f))]
    exact hdst₁
  · intro k hk1 hk2 hk3
    rw [hoth₃ k hk3]
    show R₁ k = S.R k
    by_cases hkc : k = ctr
    · subst hkc; rw [hctr₁, hc]
    by_cases hkt : k = tmp
    · subst hkt; rw [htmp₁, ht]
    exact hoth₁ k hk1 hkc hkt hk2

/-! ### Routing -/

/-- Route the records of `src` by the code program. -/
def routeIdxC (cp : Pr P T Q A U) (sel : ℕ → Fin nd) (src : Fin T) (dst : Fin nd → Fin T)
    (ctr tmp : Fin T) (cf : Fin nf → Fin T) (st : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR src)) (.loop (·.flag) (idxStepC cp sel (fun _ => src) dst ctr tmp cf st (peekR src)))

theorem routeIdxC_loop (cs : CodeSpec body cp cf len st Y Inv sel code c) (src : Fin T)
    (dst : Fin nd → Fin T) (ctr tmp : Fin T)
    (hYs : ¬ Y src) (hYc : ¬ Y ctr) (hYt : ¬ Y tmp) (hYd : ∀ d, ¬ Y (dst d))
    (h1 : src ≠ ctr) (h2 : src ≠ tmp) (h3 : ctr ≠ tmp) (h4 : ∀ d, dst d ≠ src)
    (h5 : ∀ d, dst d ≠ ctr) (h6 : ∀ d, dst d ≠ tmp) (hinj : Function.Injective dst) {B : ℕ}
    (hB : 1 ≤ B) (cc : List (Fin (A + 4))) (hcB : cc.length = B) :
    ∀ (n i : ℕ) (l : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A),
      l.length = n * B → S.R src = l → S.R ctr = cc → S.R tmp = [] →
      Inv S.R i → v.flag = l.head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
        m ≤ n * (idxStepCost c B len + 1) + 1 ∧
        Exec body (.loop (·.flag) (idxStepC cp sel (fun _ => src) dst ctr tmp cf st (peekR src)))
          (mk v S) m (mk v' { S with R := R' }) ∧
        R' src = [] ∧ Inv R' (i + n) ∧
        (∀ d, R' (dst d) = (blocksIdx l B n code i d).reverse ++ S.R (dst d)) ∧
        ∀ k, k ≠ src → (∀ d, dst d ≠ k) → (∀ f, cf f ≠ k) → R' k = S.R k := by
  intro n
  induction n with
  | zero =>
      intro i l v S hl hs _ _ hI hf
      obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      exact ⟨v, S.R, 1, rfl, by simp, .loop_false (by simpa using hf), hs, hI,
        fun d => by simp, fun _ _ _ _ => rfl⟩
  | succ n ih =>
      intro i l v S hl hs hc ht hI hf
      have hlB : B ≤ l.length := by rw [hl]; nlinarith
      obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hsrc₁, hdst₁, hI₁, hoth₁⟩ :=
        idxStepC_exec body cs (fun _ => src) dst ctr tmp (peekR src) i hYc hYt hYs (hYd _)
          h1 h2 h3 (h4 _) (h5 _) (h6 _) cc (l.take B) (l.drop B) v S (by simp [hcB]; omega) hc ht
          (by simp [hs]) hI
      rw [peekR_run] at he₁
      have hfr₁ : ∀ k, k ≠ src → k ≠ dst (code i) → (∀ f, cf f ≠ k) → R₁ k = S.R k :=
        fun k hk1 hk2 hk3 => hoth₁ k hk1 hk2 (fun f => (hk3 f).symm)
      have hctr₁ : R₁ ctr = cc := by
        rw [← hc]
        exact hfr₁ ctr (Ne.symm h1) (Ne.symm (h5 _)) (fun f e => hYc (e ▸ cs.cf_Y f))
      have htmp₁ : R₁ tmp = [] := by
        rw [← ht]
        exact hfr₁ tmp (Ne.symm h2) (Ne.symm (h6 _)) (fun f e => hYt (e ▸ cs.cf_Y f))
      obtain ⟨v', R', m, hu, hm, he, hsrc, hI', hdst, hoth⟩ := ih (i + 1) (l.drop B)
        { v₁ with flag := (R₁ src).head?.isSome } { S with R := R₁ }
        (by simp [hl, Nat.add_one_mul]) hsrc₁ hctr₁ htmp₁ hI₁ (by simp [hsrc₁])
      have hne : l ≠ [] := by
        intro e; rw [e] at hlB; simp at hlB; omega
      refine ⟨v', R', m₁ + m + 1, by rw [hu, hu₁], ?_, Exec.cast (Exec.loop_true (body := body)
        (f := (·.flag)) (by simpa [hf] using hne) he₁ he) (by ring) rfl, hsrc,
        by rw [show i + (n + 1) = i + 1 + n by ring]; exact hI', ?_, ?_⟩
      · rw [hcB] at hm₁
        nlinarith
      · intro d
        rw [hdst, blocksIdx_succ]
        show (blocksIdx _ B n _ (i + 1) d).reverse ++ R₁ (dst d) = _
        by_cases hd : code i = d
        · subst hd
          simp [hdst₁]
        · rw [hfr₁ (dst d) (h4 d) (fun e => hd (hinj e).symm)
            (fun f e => hYd d (e ▸ cs.cf_Y f))]
          simp [hd]
      · intro k hk1 hk2 hk3
        exact (hoth k hk1 hk2 hk3).trans (hfr₁ k hk1 (fun e => hk2 _ e.symm) hk3)

/-- **Routing by a code program.** `dst d` gains the reversal of the records whose index has code
`d`; the index advances by the number of records. -/
theorem routeIdxC_exec (cs : CodeSpec body cp cf len st Y Inv sel code c) (src : Fin T)
    (dst : Fin nd → Fin T) (ctr tmp : Fin T)
    (hYs : ¬ Y src) (hYc : ¬ Y ctr) (hYt : ¬ Y tmp) (hYd : ∀ d, ¬ Y (dst d))
    (hreg : [src, ctr, tmp].Nodup) (hdst : ∀ d, dst d ∉ [src, ctr, tmp])
    (hinj : Function.Injective dst) {l cc : List (Fin (A + 4))} {nb B i₀ : ℕ} (hB : 1 ≤ B)
    (hl : l.length = nb * B) (hcB : cc.length = B) (v : HS T Q A U) (S : Stacks T A)
    (hs : S.R src = l) (hc : S.R ctr = cc) (ht : S.R tmp = []) (hI : Inv S.R i₀) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ nb * (idxStepCost c B len + 1) + 2 ∧
      Exec body (routeIdxC cp sel src dst ctr tmp cf st) (mk v S) m (mk v' { S with R := R' }) ∧
      R' src = [] ∧
      (∀ d, R' (dst d) = (blocksIdx l B nb code i₀ d).reverse ++ S.R (dst d)) ∧
      Inv R' (i₀ + nb) ∧
      ∀ k, k ≠ src → (∀ d, dst d ≠ k) → (∀ f, cf f ≠ k) → R' k = S.R k := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg hdst
  obtain ⟨⟨h1, h2⟩, h3⟩ := hreg
  obtain ⟨v', R', m, hu, hm, he, hsrc, hI', hd, hoth⟩ :=
    routeIdxC_loop body cs src dst ctr tmp hYs hYc hYt hYd h1 h2 h3 (fun d => (hdst d).1)
      (fun d => (hdst d).2.1) (fun d => (hdst d).2.2) hinj hB cc hcB nb i₀ l
      { v with flag := (S.R src).head?.isSome } S hl hs hc ht hI (by rw [hs])
  exact ⟨v', R', 1 + m, hu, by omega, Exec.seq (peekR_run src v S ▸
    Exec.act (body := body) (peekR src) (mk v S)) he, hsrc, hd, hI', hoth⟩

/-! ### Merging -/

/-- Merge records by the code program, one record per symbol of `cnt`. -/
def mergeIdxC (cp : Pr P T Q A U) (sel : ℕ → Fin nd) (srcs : Fin nd → Fin T)
    (dst ctr tmp cnt ctmp : Fin T) (cf : Fin nf → Fin T) (st : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR cnt))
    (.seq (.loop (·.flag) (idxStepC cp sel srcs (fun _ => dst) ctr tmp cf st (moveStep cnt ctmp id)))
      (moveR ctmp cnt id))

theorem mergeIdxC_loop (cs : CodeSpec body cp cf len st Y Inv sel code c)
    (srcs : Fin nd → Fin T) (dst ctr tmp cnt ctmp : Fin T)
    (hYs : ∀ d, ¬ Y (srcs d)) (hYd : ¬ Y dst) (hYc : ¬ Y ctr) (hYt : ¬ Y tmp)
    (hYn : ¬ Y cnt) (hYm : ¬ Y ctmp)
    (h1 : ∀ d, srcs d ≠ ctr) (h2 : ∀ d, srcs d ≠ tmp) (h3 : ctr ≠ tmp) (h4 : ∀ d, dst ≠ srcs d)
    (h5 : dst ≠ ctr) (h6 : dst ≠ tmp) (h7 : ∀ d, srcs d ≠ cnt) (h8 : ∀ d, srcs d ≠ ctmp)
    (h9 : dst ≠ cnt) (h10 : dst ≠ ctmp) (h11 : ctr ≠ cnt) (h12 : ctr ≠ ctmp) (h13 : tmp ≠ cnt)
    (h14 : tmp ≠ ctmp) (h15 : cnt ≠ ctmp) (hinj : Function.Injective srcs) {B : ℕ}
    (cc : List (Fin (A + 4))) (hcB : cc.length = B) :
    ∀ (kk : List (Fin (A + 4))) (j : ℕ) (s : Fin nd → List (Fin (A + 4))) (v : HS T Q A U)
      (S : Stacks T A),
      S.R cnt = kk → (∀ d, S.R (srcs d) = s d) →
      (∀ d, idxCount code j kk.length d * B ≤ (s d).length) →
      S.R ctr = cc → S.R tmp = [] → Inv S.R j →
      v.flag = kk.head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
        m ≤ kk.length * (idxStepCost c B len + 1) + 1 ∧
        Exec body (.loop (·.flag)
            (idxStepC cp sel srcs (fun _ => dst) ctr tmp cf st (moveStep cnt ctmp id)))
          (mk v S) m (mk v' { S with R := R' }) ∧
        R' cnt = [] ∧ R' ctmp = kk.reverse ++ S.R ctmp ∧
        R' dst = (mergeIdxList B code kk.length j s).1.reverse ++ S.R dst ∧
        (∀ d, R' (srcs d) = (mergeIdxList B code kk.length j s).2 d) ∧
        Inv R' (j + kk.length) ∧
        ∀ k, k ≠ dst → k ≠ cnt → k ≠ ctmp → (∀ d, srcs d ≠ k) → (∀ f, cf f ≠ k) →
          R' k = S.R k := by
  have hcf : ∀ f k, ¬ Y k → cf f ≠ k := fun f k hk e => hk (e ▸ cs.cf_Y f)
  intro kk
  induction kk with
  | nil =>
      intro j s v S hk hs _ _ _ hI hf
      exact ⟨v, S.R, 1, rfl, by simp, .loop_false (by simpa using hf), hk, rfl,
        by simp [mergeIdxList], fun d => by simp [mergeIdxList, hs], by simpa using hI,
        fun _ _ _ _ _ _ => rfl⟩
  | cons e kk ih =>
      intro j s v S hk hs hfit hc ht hI hf
      have hfit₀ := hfit (code j)
      rw [List.length_cons, idxCount_succ] at hfit₀
      simp only [↓reduceIte] at hfit₀
      have hB : B ≤ (s (code j)).length := by nlinarith
      obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hsrc₁, hdst₁, hI₁, hoth₁⟩ :=
        idxStepC_exec body cs srcs (fun _ => dst) ctr tmp (moveStep cnt ctmp id) j hYc hYt
          (hYs _) hYd (h1 _) (h2 _) h3 (h4 _) h5 h6 cc ((s (code j)).take B)
          ((s (code j)).drop B) v S (by simp [hcB]; omega) hc ht (by rw [hs, List.take_append_drop])
          hI
      have hfr₁ : ∀ k, k ≠ srcs (code j) → k ≠ dst → (∀ f, cf f ≠ k) → R₁ k = S.R k :=
        fun k hk1 hk2 hk3 => hoth₁ k hk1 hk2 (fun f => (hk3 f).symm)
      have hcnt₁ : R₁ cnt = e :: kk := by
        rw [hfr₁ cnt (h7 _).symm h9.symm (fun f => hcf f _ hYn), hk]
      have hct₁ : R₁ ctmp = S.R ctmp :=
        hfr₁ ctmp (h8 _).symm h10.symm (fun f => hcf f _ hYm)
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
      obtain ⟨v', R', m, hu, hm, he, hcnt, hct, hdst, hsrc, hI', hoth⟩ := ih (j + 1) s'
        { v₁ with sym := some e, flag := kk.head?.isSome } { S with R := R₂ }
        (by simp [hR₂, Function.update_of_ne h15])
        (by
          intro d
          show R₂ (srcs d) = s' d
          rw [hfr₂ _ (h7 d) (h8 d)]
          by_cases hd : d = code j
          · subst hd; rw [hsrc₁, hs', Function.update_self]
          · rw [hfr₁ _ (fun e => hd (hinj e)) (h4 d).symm
              (fun f => hcf f _ (hYs d)), hs d, hs', Function.update_of_ne hd])
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
          show R₂ ctr = cc
          rw [hfr₂ _ h11 h12, hfr₁ _ (h1 _).symm h5.symm (fun f => hcf f _ hYc), hc])
        (by
          show R₂ tmp = []
          rw [hfr₂ _ h13 h14, hfr₁ _ (h2 _).symm h6.symm (fun f => hcf f _ hYt), ht])
        (cs.frame R₁ R₂ (j + 1) hI₁ (fun k hk => hfr₂ k (fun e => hYn (e ▸ hk))
          (fun e => hYm (e ▸ hk)))) rfl
      refine ⟨v', R', m₁ + m + 1, by rw [hu, hu₁], ?_, Exec.cast (Exec.loop_true (body := body)
        (f := (·.flag)) (by simpa using hf) he₁ he) (by ring) rfl, hcnt, ?_, ?_, hsrc,
        by rw [List.length_cons, show j + (kk.length + 1) = j + 1 + kk.length by ring]; exact hI',
        ?_⟩
      · rw [hcB] at hm₁
        simp only [List.length_cons]
        nlinarith
      · rw [hct]
        show kk.reverse ++ R₂ ctmp = _
        simp [hR₂, hct₁]
      · rw [hdst]
        show _ ++ R₂ dst = _
        rw [hfr₂ _ h9 h10, hdst₁]
        simp [mergeIdxList, hs']
      · intro k hk1 hk2 hk3 hk4 hk5
        rw [hoth k hk1 hk2 hk3 hk4 hk5]
        show R₂ k = S.R k
        rw [hfr₂ k hk2 hk3]
        exact hfr₁ k (fun e => hk4 _ e.symm) hk1 hk5

/-- **Merging by a code program.** -/
theorem mergeIdxC_exec (cs : CodeSpec body cp cf len st Y Inv sel code c)
    (srcs : Fin nd → Fin T) (dst ctr tmp cnt ctmp : Fin T)
    (hYs : ∀ d, ¬ Y (srcs d)) (hYd : ¬ Y dst) (hYc : ¬ Y ctr) (hYt : ¬ Y tmp)
    (hYn : ¬ Y cnt) (hYm : ¬ Y ctmp)
    (hreg : [dst, ctr, tmp, cnt, ctmp].Nodup) (hsrcs : ∀ d, srcs d ∉ [dst, ctr, tmp, cnt, ctmp])
    (hinj : Function.Injective srcs) {cc kk : List (Fin (A + 4))} {nb B i₀ : ℕ}
    (hcB : cc.length = B) (hk : kk.length = nb) (s : Fin nd → List (Fin (A + 4)))
    (hfit : ∀ d, idxCount code i₀ nb d * B ≤ (s d).length)
    (v : HS T Q A U) (S : Stacks T A) (hs : ∀ d, S.R (srcs d) = s d) (hc : S.R ctr = cc)
    (ht : S.R tmp = []) (hcnt : S.R cnt = kk) (hct : S.R ctmp = []) (hI : Inv S.R i₀) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))) (m : ℕ), v'.user = v.user ∧
      m ≤ nb * (idxStepCost c B len + 3) + 4 ∧
      Exec body (mergeIdxC cp sel srcs dst ctr tmp cnt ctmp cf st) (mk v S) m
        (mk v' { S with R := R' }) ∧
      R' dst = (mergeIdxList B code nb i₀ s).1.reverse ++ S.R dst ∧
      (∀ d, R' (srcs d) = (mergeIdxList B code nb i₀ s).2 d) ∧
      Inv R' (i₀ + nb) ∧
      ∀ k, k ≠ dst → (∀ d, srcs d ≠ k) → (∀ f, cf f ≠ k) → R' k = S.R k := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg hsrcs
  obtain ⟨⟨h5, h6, h9, h10⟩, ⟨h3, h11, h12⟩, ⟨h13, h14⟩, h15⟩ := hreg
  subst hk
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hcnt₁, hct₁, hdst₁, hsrc₁, hI₁, hoth₁⟩ :=
    mergeIdxC_loop body cs srcs dst ctr tmp cnt ctmp hYs hYd hYc hYt hYn hYm
      (fun d => (hsrcs d).2.1) (fun d => (hsrcs d).2.2.1) h3 (fun d => Ne.symm (hsrcs d).1) h5 h6
      (fun d => (hsrcs d).2.2.2.1) (fun d => (hsrcs d).2.2.2.2) h9 h10 h11 h12 h13 h14 h15 hinj
      cc hcB kk i₀ s { v with flag := (S.R cnt).head?.isSome } S hcnt hs hfit hc ht hI
      (by simp [hcnt])
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body ctmp cnt (Ne.symm h15) id v₁ { S with R := R₁ }
  have hcf : ∀ f k, ¬ Y k → cf f ≠ k := fun f k hk e => hk (e ▸ cs.cf_Y f)
  refine ⟨v₂, movedR R₁ ctmp cnt id (R₁ ctmp), 1 + (m₁ + (2 * (R₁ ctmp).length + 2)),
    by rw [hu₂, hu₁], ?_, Exec.seq (peekR_run cnt v S ▸ Exec.act (body := body) (peekR cnt)
      (mk v S)) (Exec.seq he₁ he₂), ?_, ?_, ?_, ?_⟩
  · rw [hct₁, hct]
    simp only [List.append_nil, List.length_reverse]
    nlinarith
  · simp [movedR, h9, h10, hdst₁]
  · intro d; simp [movedR, (hsrcs d).2.2.2.1, (hsrcs d).2.2.2.2, hsrc₁]
  · refine cs.frame R₁ _ _ hI₁ (fun k hk => ?_)
    have hk1 : k ≠ cnt := fun e => hYn (e ▸ hk)
    have hk2 : k ≠ ctmp := fun e => hYm (e ▸ hk)
    simp [movedR, hk1, hk2]
  · intro k hk1 hk2 hk3
    by_cases hk4 : k = cnt
    · subst hk4; simp [movedR, hct₁, hct, hcnt₁, hcnt]
    by_cases hk5 : k = ctmp
    · subst hk5; simp [movedR, Ne.symm h15, hct]
    simp [movedR, hk4, hk5, hoth₁ k hk1 hk4 hk5 hk2 hk3]

variable {body} in
/-- A code program within `c` steps is within any larger bound. -/
lemma CodeSpec.mono (h : CodeSpec body cp cf len st Y Inv sel code c) {c' : ℕ} (hc : c ≤ c') :
    CodeSpec body cp cf len st Y Inv sel code c' where
  runs i v S hI := by
    obtain ⟨v', m, hu, hm, hs, he⟩ := h.runs i v S hI
    exact ⟨v', m, hu, hm.trans hc, hs, he⟩
  cf_inj := h.cf_inj
  cf_Y := h.cf_Y
  digits := h.digits
  frame := h.frame
  reidx := h.reidx

/-! ### Resetting the field counter -/

/-- Overwrite every symbol of register `c` by `bitSymbol false`, through the empty register
`tmp`. -/
def resetField (c tmp : Fin T) : Pr P T Q A U :=
  .seq (moveR c tmp (fun _ => bitSymbol false)) (moveR tmp c id)

/-- Reset the fields `cf` of the counter to zero. -/
def resetFields {nf : ℕ} (cf : Fin nf → Fin T) (tmp : Fin T) : Pr P T Q A U :=
  Prog.seqList ((List.finRange nf).map fun f => resetField (cf f) tmp)

/-- One field: every symbol of `c` becomes `bitSymbol false`; `tmp` ends empty. Exactly
`4 * |c| + 4` steps. -/
theorem resetField_exec (c tmp : Fin T) (h : c ≠ tmp) (v : HS T Q A U) (S : Stacks T A)
    (ht : S.R tmp = []) :
    ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body (resetField c tmp) (mk v S) (4 * (S.R c).length + 4)
        (mk v' { S with
          R := Function.update S.R c (List.replicate (S.R c).length (bitSymbol false)) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := moveR_exec body c tmp h (fun _ => bitSymbol false) v S
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body tmp c h.symm id v₁
    { S with R := movedR S.R c tmp (fun _ => bitSymbol false) (S.R c) }
  refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
  · simp [movedR, ht]; ring
  · congr 2
    funext k
    by_cases hk : k = c
    · subst hk; simp [movedR, ht, Function.update_of_ne h]
    · by_cases hk' : k = tmp
      · subst hk'; simp [movedR, hk, ht, Function.update_of_ne (Ne.symm hk)]
      · simp [movedR, hk, hk']

lemma binSyms_zero_eq (ℓ : ℕ) :
    (binSyms ℓ 0 : List (Fin (A + 4))) = List.replicate ℓ (bitSymbol false) := by
  simp [binSyms, List.ofFn_const]

/-- The fields `fs` of the counter, in order: each ends holding `binSyms (len f) 0`. -/
theorem resetList_exec {nf : ℕ} (cf : Fin nf → Fin T) (hcf : Function.Injective cf) (tmp : Fin T)
    (htmp : ∀ f, cf f ≠ tmp) (len : Fin nf → ℕ) :
    ∀ (fs : List (Fin nf)), fs.Nodup → ∀ (v : HS T Q A U) (S : Stacks T A), S.R tmp = [] →
      (∀ f ∈ fs, (S.R (cf f)).length = len f) →
      ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
        Exec body (Prog.seqList (fs.map fun f => resetField (cf f) tmp)) (mk v S)
          ((fs.map fun f => 4 * len f + 4).sum + 1) (mk v' { S with R := R' }) ∧
        (∀ f ∈ fs, R' (cf f) = binSyms (len f) 0) ∧
        ∀ k, (∀ f ∈ fs, k ≠ cf f) → R' k = S.R k := by
  intro fs
  induction fs with
  | nil =>
      intro _ v S _ _
      exact ⟨v, S.R, rfl, by simpa [Prog.seqList] using Exec.act (body := body) .done (mk v S),
        by simp, fun _ _ => rfl⟩
  | cons f fs ih =>
      intro hnd v S ht hlen
      rw [List.nodup_cons] at hnd
      obtain ⟨v₁, hu₁, he₁⟩ := resetField_exec body (cf f) tmp (htmp f) v S ht
      rw [hlen f List.mem_cons_self] at he₁
      obtain ⟨v', R', hu, he, hfs, hoth⟩ := ih hnd.2 v₁
        { S with R := Function.update S.R (cf f) (List.replicate (len f) (bitSymbol false)) }
        (by simp [Function.update_of_ne (htmp f).symm, ht])
        (by
          intro g hg
          have hgf : g ≠ f := fun h => hnd.1 (h ▸ hg)
          simp [Function.update_of_ne (fun h => hgf (hcf h)), hlen g (List.mem_cons_of_mem _ hg)])
      refine ⟨v', R', by rw [hu, hu₁], Exec.cast (Exec.seq he₁ he) ?_ rfl, ?_, ?_⟩
      · simp; ring
      · intro g hg
        rcases List.mem_cons.1 hg with rfl | hg
        · rw [hoth _ (fun g' hg' h => hnd.1 (by rw [hcf h]; exact hg')), binSyms_zero_eq]
          simp
        · exact hfs g hg
      · intro k hk
        rw [hoth k (fun g hg => hk g (List.mem_cons_of_mem _ hg))]
        simp [Function.update_of_ne (hk f List.mem_cons_self)]

/-- Resetting the fields: every field `cf f` holding `len f` symbols ends holding
`binSyms (len f) 0`; every other register is unchanged. Exactly
`4 * (∑ f, len f) + 4 * nf + 1` steps. -/
theorem resetFields_exec {nf : ℕ} (cf : Fin nf → Fin T) (hcf : Function.Injective cf)
    (tmp : Fin T) (htmp : ∀ f, cf f ≠ tmp) (len : Fin nf → ℕ) (v : HS T Q A U) (S : Stacks T A)
    (ht : S.R tmp = []) (hlen : ∀ f, (S.R (cf f)).length = len f) :
    ∃ (v' : HS T Q A U) (R' : Fin T → List (Fin (A + 4))), v'.user = v.user ∧
      Exec body (resetFields cf tmp) (mk v S) (4 * (∑ f, len f) + 4 * nf + 1)
        (mk v' { S with R := R' }) ∧
      (∀ f, R' (cf f) = binSyms (len f) 0) ∧ ∀ k, (∀ f, k ≠ cf f) → R' k = S.R k := by
  obtain ⟨v', R', hu, he, hfs, hoth⟩ := resetList_exec body cf hcf tmp htmp len
    (List.finRange nf) (List.nodup_finRange nf) v S ht (fun f _ => hlen f)
  refine ⟨v', R', hu, Exec.cast he ?_ rfl, fun f => hfs f (List.mem_finRange f),
    fun k hk => hoth k (fun f _ => hk f)⟩
  rw [← Fin.sum_univ_def, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [Nat.mul_comm]

/-! ### The code pass as a code program -/

section CodePass

variable {nr : ℕ} {L : ℕ} {rs tmps : Fin nr → Fin T} {rsrc : Fin nr → Fin nf ⊕ ℕ}
  {X : Fin T → Prop}

/-- The index registers of a code pass: the fields, the parameter registers and the spares. -/
def idxY (cf : Fin nf → Fin T) (rs tmps : Fin nr → Fin T) (rsrc : Fin nr → Fin nf ⊕ ℕ)
    (k : Fin T) : Prop :=
  (∃ f, k = cf f) ∨ (∃ r p, rsrc r = .inr p ∧ k = rs r) ∨ ∃ r, k = tmps r

/-- **The code pass of an automaton is a code program** over the index state `IdxState`. -/
theorem IdxLayout.codeSpec [NeZero nr] (h : IdxLayout cf len L rs tmps rsrc st X)
    (C : CAuto A nr nd) :
    CodeSpec body (codePass rs tmps st C) cf len st (idxY cf rs tmps rsrc)
      (IdxState cf len L rs tmps rsrc) (codeSel C) (idxCode C L len rsrc) (6 * L + 4) where
  runs i v S hI := by
    obtain ⟨v', hu, hsc, he⟩ := codePass_exec body h.toCodeLayout C L (regVal len rsrc i) v S
      (IdxState.rs_eq h hI) hI.2.2
    exact ⟨v', _, hu, le_rfl, by rw [hsc, codeSel_val]; rfl, he⟩
  cf_inj := h.cf_inj
  cf_Y f := Or.inl ⟨f, rfl⟩
  digits _ _ hI := hI.1
  frame R R' i hI hR := ⟨fun f => (hR _ (Or.inl ⟨f, rfl⟩)).trans (hI.1 f),
    fun r p hr => (hR _ (Or.inr (Or.inl ⟨r, p, hr, rfl⟩))).trans (hI.2.1 r p hr),
    fun r => (hR _ (Or.inr (Or.inr ⟨r, rfl⟩))).trans (hI.2.2 r)⟩
  reidx R R' i j hI hcf hR := ⟨hcf,
    fun r p hr => (hR _ fun f e => h.param r p f hr e).trans (hI.2.1 r p hr),
    fun r => (hR _ fun f e => h.tmps_cf r f e).trans (hI.2.2 r)⟩

end CodePass

end IntegerMultBounds.MathlibTM2.Host
