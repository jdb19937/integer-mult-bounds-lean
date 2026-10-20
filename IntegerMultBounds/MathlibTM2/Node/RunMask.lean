module

public import IntegerMultBounds.MathlibTM2.Node.Params

/-!
# Masks from runs of bits

A run `(r, b)` emits `|r|` copies of the bit `b`. `runMask nR pre kR item post` builds, on the
`n = |nR|` low bits of a mask, the runs `pre`, then `|kR|` copies of the runs `item`, then the
runs `post`, then zeros (`runMask_exec`): the bit at position `q` is `runPat … q`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Node

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U)

/-- Emit the runs `rs`, scanning each run register through the empty `t`. -/
def emitRuns (rs : List (Fin T × Bool)) (cnt w t : Fin T) : Pr P T Q A U :=
  Prog.seqList (rs.map fun x => scanR x.1 t (emit cnt w x.2))

/-- The total length of the runs. -/
def runsLen (R₀ : Regs T A) (rs : List (Fin T × Bool)) : ℕ := (rs.map fun x => (R₀ x.1).length).sum

/-- The bit at offset `j` of the runs. -/
def runBit (R₀ : Regs T A) : List (Fin T × Bool) → ℕ → Bool
  | [], _ => false
  | x :: rs, j => if j < (R₀ x.1).length then x.2 else runBit R₀ rs (j - (R₀ x.1).length)

/-- The step bound of `emitRuns`. -/
def runsCost (R₀ : Regs T A) (rs : List (Fin T × Bool)) : ℕ :=
  (rs.map fun x => 4 * (R₀ x.1).length + 4).sum + 1

/-- **Emitting runs.** -/
theorem emitRuns_exec {cnt w t : Fin T} {n X : ℕ} (R₀ : Regs T A) :
    ∀ (rs : List (Fin T × Bool)), (∀ x ∈ rs, [x.1, t, cnt, w].Nodup) →
      ∀ (p : ℕ) (v : HS T Q A U) (S : Stacks T A), S.R = maskRegs cnt w n X R₀ p →
      R₀ t = [] → (∀ j < runsLen R₀ rs, p + j < n → X.testBit (p + j) = runBit R₀ rs j) →
      ∃ v' : HS T Q A U, v'.user = v.user ∧
        Exec body (emitRuns rs cnt w t) (mk v S) (runsCost R₀ rs)
          (mk v' { S with R := maskRegs cnt w n X R₀ (p + runsLen R₀ rs) })
  | [], _, p, v, S, hS, _, _ => by
    refine ⟨v, rfl, ?_⟩
    have he := Exec.act (body := body) (.done : Act T Q A U) (mk v S)
    rw [run_done] at he
    refine Exec.cast he rfl ?_
    simp [runsLen, ← hS]
  | x :: rs, hreg, p, v, S, hS, ht, hX => by
    have hrl : runsLen R₀ (x :: rs) = (R₀ x.1).length + runsLen R₀ rs := by simp [runsLen]
    obtain ⟨v₁, hu₁, he₁⟩ := scanEmit_exec body (hreg x List.mem_cons_self) x.2 R₀ v S hS ht
      (fun q h1 h2 h3 => by
        have := hX (q - p) (by rw [hrl]; omega) (by omega)
        rw [show p + (q - p) = q by omega] at this
        rw [this, runBit]
        simp only [show q - p < (R₀ x.1).length by omega, ↓reduceIte])
    obtain ⟨v₂, hu₂, he₂⟩ := emitRuns_exec (n := n) (X := X) R₀ rs
      (fun y hy => hreg y (List.mem_cons_of_mem _ hy)) (p + (R₀ x.1).length) v₁
      { S with R := maskRegs cnt w n X R₀ (p + (R₀ x.1).length) } rfl ht (fun j hj hjn => by
        have := hX ((R₀ x.1).length + j) (by rw [hrl]; omega) (by omega)
        rw [← Nat.add_assoc] at this
        rw [this, runBit]
        simp only [show ¬ (R₀ x.1).length + j < (R₀ x.1).length by omega, ↓reduceIte,
          Nat.add_sub_cancel_left])
    refine ⟨v₂, by rw [hu₂, hu₁], Exec.cast (Exec.seq he₁ he₂) ?_ ?_⟩
    · simp [runsCost]; ring
    · rw [hrl, Nat.add_assoc]

lemma runsLen_congr {R R' : Regs T A} :
    ∀ (rs : List (Fin T × Bool)), (∀ x ∈ rs, R x.1 = R' x.1) → runsLen R rs = runsLen R' rs
  | [], _ => rfl
  | x :: rs, h => by
    have := runsLen_congr rs fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [runsLen, List.map_cons, List.sum_cons] at *
    rw [h x List.mem_cons_self, this]

lemma runBit_congr {R R' : Regs T A} :
    ∀ (rs : List (Fin T × Bool)), (∀ x ∈ rs, R x.1 = R' x.1) → ∀ j, runBit R rs j = runBit R' rs j
  | [], _, _ => rfl
  | x :: rs, h, j => by
    simp only [runBit, h x List.mem_cons_self,
      runBit_congr rs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

lemma runsCost_congr {R R' : Regs T A} :
    ∀ (rs : List (Fin T × Bool)), (∀ x ∈ rs, R x.1 = R' x.1) → runsCost R rs = runsCost R' rs
  | [], _ => rfl
  | x :: rs, h => by
    have := runsCost_congr rs fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [runsCost, List.map_cons, List.sum_cons] at *
    rw [h x List.mem_cons_self]; omega

/-- `|kR|` copies of the runs `item`, scanning `kR` through the empty `t₁`. -/
theorem runItems_exec {kR cnt w t₁ t₂ : Fin T} (hreg : [kR, cnt, w, t₁, t₂].Nodup)
    (item : List (Fin T × Bool)) (hitem : ∀ x ∈ item, x.1 ∉ [kR, cnt, w, t₁, t₂])
    {n X p₀ : ℕ} (R₀ : Regs T A) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R = maskRegs cnt w n X R₀ p₀) (ht₁ : R₀ t₁ = []) (ht₂ : R₀ t₂ = [])
    (hX : ∀ j < (R₀ kR).length, ∀ i < runsLen R₀ item, p₀ + j * runsLen R₀ item + i < n →
      X.testBit (p₀ + j * runsLen R₀ item + i) = runBit R₀ item i) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (R₀ kR).length * (runsCost R₀ item + 3) + 2 * (R₀ kR).length + 4 ∧
      Exec body (scanP kR t₁ (emitRuns item cnt w t₂)) (mk v S) m
        (mk v' { S with R := maskRegs cnt w n X R₀ (p₀ + (R₀ kR).length * runsLen R₀ item) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hkc, hkw, hk1, hk2⟩, ⟨hcw, hc1, hc2⟩, ⟨hw1, hw2⟩, h12⟩ := hreg'
  have hit : ∀ x ∈ item, x.1 ≠ kR ∧ x.1 ≠ cnt ∧ x.1 ≠ w ∧ x.1 ≠ t₁ ∧ x.1 ≠ t₂ := fun x hx => by
    have := hitem x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this
  let Ψ : ℕ → Regs T A := fun j => maskRegs cnt w n X R₀ (p₀ + j * runsLen R₀ item)
  have hp : IterSpec body (emitRuns item cnt w t₂) kR t₁ Ψ (fun _ => runsCost R₀ item)
      (R₀ kR).length := by
    intro j hj v' S' hS'
    have hc' : S'.R cnt = List.replicate (n - (p₀ + j * runsLen R₀ item)) tick :=
      (hS' cnt hkc.symm hc1).trans (maskRegs_cnt hcw _ _)
    have hw' : S'.R w = (binSyms (min (p₀ + j * runsLen R₀ item) n) X).reverse :=
      (hS' w hkw.symm hw1).trans (maskRegs_w _ _)
    have hreg₀ : ∀ x ∈ item, S'.R x.1 = R₀ x.1 := fun x hx =>
      (hS' x.1 (hit x hx).1 (hit x hx).2.2.2.1).trans
        (maskRegs_of_ne (hit x hx).2.1 (hit x hx).2.2.1 _ _)
    have ht₂' : S'.R t₂ = [] :=
      (hS' t₂ hk2.symm h12.symm).trans ((maskRegs_of_ne hc2.symm hw2.symm _ _).trans ht₂)
    have hL := runsLen_congr item hreg₀
    obtain ⟨v'', hu, he⟩ := emitRuns_exec body (n := n) (X := X) S'.R item
      (fun x hx => by
        have := hit x hx
        simp [this.2.1, this.2.2.1, this.2.2.2.2, hc2.symm, hw2.symm, hcw])
      (p₀ + j * runsLen R₀ item) v' S' (maskRegs_self hc' hw').symm ht₂'
      (fun i hi hin => by
        rw [hL] at hi
        rw [runBit_congr item hreg₀]
        exact hX j hj i hi hin)
    rw [hL, show p₀ + j * runsLen R₀ item + runsLen R₀ item = p₀ + (j + 1) * runsLen R₀ item by
      rw [Nat.add_one_mul, Nat.add_assoc]] at he
    refine ⟨v'', _, _, hu, le_of_eq (runsCost_congr item hreg₀), he, maskRegs_of_ne hkc hkw _ _,
      maskRegs_of_ne hc1.symm hw1.symm _ _, fun k hka hkt => ?_⟩
    exact maskRegs_congr _ fun h1 h2 => by
      rw [hS' k hka hkt]; exact maskRegs_of_ne h1 h2 _ _
  obtain ⟨v', R', m, hu, hm, he, ha', ht', hΨ'⟩ := scanP_exec body hk1 hp 0 v S
    (by rw [hS, maskRegs_of_ne hkc hkw]; simp)
    (fun k hka hkt => by rw [hS]; simp [Ψ])
  have hSk : S.R kR = R₀ kR := by rw [hS, maskRegs_of_ne hkc hkw]
  have hSt : S.R t₁ = [] := by rw [hS, maskRegs_of_ne hc1.symm hw1.symm, ht₁]
  refine ⟨v', m, hu, ?_, Exec.cast he rfl ?_⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, hSk, hSt,
      List.length_nil, Nat.mul_zero, Nat.add_zero] at hm
    nlinarith
  · congr 2
    funext k
    by_cases hka : k = kR
    · subst hka; rw [ha', hSt, maskRegs_of_ne hkc hkw, hSk]; rfl
    · by_cases hkt : k = t₁
      · subst hkt; rw [ht', maskRegs_of_ne hc1.symm hw1.symm, ht₁]
      · rw [hΨ' k hka hkt, hSk]; simp [Ψ]

/-- The bit at position `q` of a run mask. -/
def runPat (R₀ : Regs T A) (pre : List (Fin T × Bool)) (N : ℕ) (item post : List (Fin T × Bool))
    (q : ℕ) : Bool :=
  if q < runsLen R₀ pre then runBit R₀ pre q
  else if q < runsLen R₀ pre + N * runsLen R₀ item then
    runBit R₀ item ((q - runsLen R₀ pre) % runsLen R₀ item)
  else if q < runsLen R₀ pre + N * runsLen R₀ item + runsLen R₀ post then
    runBit R₀ post (q - runsLen R₀ pre - N * runsLen R₀ item)
  else false

/-- The run mask builder. Registers: unary input `nR` (`n`), the item count `kR`, the run
registers; output `z`; empty spares `cnt`, `w`, `t₁`, `t₂`. -/
def runMask (nR : Fin T) (pre : List (Fin T × Bool)) (kR : Fin T) (item post : List (Fin T × Bool))
    (z cnt w t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (ucopy nR cnt t₁)
    (.seq (emitRuns pre cnt w t₁)
      (.seq (scanP kR t₁ (emitRuns item cnt w t₂))
        (.seq (emitRuns post cnt w t₁)
          (.seq (scanR nR t₁ (emit cnt w false)) (moveR w z id)))))

/-- The step bound of `runMask`. -/
def runMaskCost (R₀ : Regs T A) (n N : ℕ) (pre item post : List (Fin T × Bool)) : ℕ :=
  10 * n + 10 + runsCost R₀ pre + (N * (runsCost R₀ item + 3) + 2 * N + 4) + runsCost R₀ post

/-- **The run mask.** `z` gains `binSyms n X` on top for every `X` whose low `n` bits follow
the run pattern; every other register ends as it started. -/
theorem runMask_exec {nR kR z cnt w t₁ t₂ : Fin T} (hreg : [nR, kR, z, cnt, w, t₁, t₂].Nodup)
    (pre item post : List (Fin T × Bool)) (hpre : ∀ x ∈ pre ++ post, x.1 ∉ [cnt, w, t₁])
    (hitem : ∀ x ∈ item, x.1 ∉ [kR, cnt, w, t₁, t₂]) {n X : ℕ} (v : HS T Q A U)
    (S : Stacks T A) (hn : (S.R nR).length = n) (hc : S.R cnt = []) (hw : S.R w = [])
    (ht₁ : S.R t₁ = []) (ht₂ : S.R t₂ = [])
    (hX : ∀ q < n, X.testBit q = runPat S.R pre (S.R kR).length item post q) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ runMaskCost S.R n (S.R kR).length pre item post ∧
      Exec body (runMask nR pre kR item post z cnt w t₁ t₂) (mk v S) m
        (mk v' { S with R := Function.update S.R z (binSyms n X ++ S.R z) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true, ← ne_eq] at hreg'
  obtain ⟨⟨hnk, hnz, hnc, hnw, hn1, hn2⟩, ⟨hkz, hkc, hkw, hk1, hk2⟩, ⟨hzc, hzw, hz1, hz2⟩,
    ⟨hcw, hc1, hc2⟩, ⟨hw1, hw2⟩, h12⟩ := hreg'
  have hpr : ∀ x ∈ pre ++ post, [x.1, t₁, cnt, w].Nodup := fun x hx => by
    have := hpre x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    simp [this.1, this.2.1, this.2.2, hc1.symm, hw1.symm, hcw]
  obtain ⟨Lp, hLp⟩ : ∃ L, runsLen S.R pre = L := ⟨_, rfl⟩
  obtain ⟨Li, hLi⟩ : ∃ L, runsLen S.R item = L := ⟨_, rfl⟩
  obtain ⟨Lq, hLq⟩ : ∃ L, runsLen S.R post = L := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, (S.R kR).length = N := ⟨_, rfl⟩
  have hX' : ∀ q < n, X.testBit q = if q < Lp then runBit S.R pre q
      else if q < Lp + N * Li then runBit S.R item ((q - Lp) % Li)
      else if q < Lp + N * Li + Lq then runBit S.R post (q - Lp - N * Li) else false :=
    fun q hq => by rw [hX q hq, runPat, hLp, hLi, hLq, hN]
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec body hnc hn1 hc1 v S ht₁
  rw [maskRegs_start (X := X) hcw S.R hc hw, hn] at he₁
  obtain ⟨v₂, hu₂, he₂⟩ := emitRuns_exec body (n := n) (X := X) S.R pre
    (fun x hx => hpr x (List.mem_append_left _ hx)) 0 v₁
    { S with R := maskRegs cnt w n X S.R 0 } rfl ht₁ (fun j hj hjn => by
      rw [Nat.zero_add] at hjn ⊢
      rw [hX' j hjn]; rw [hLp] at hj; simp [hj])
  rw [Nat.zero_add, hLp] at he₂
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := runItems_exec body (by simp [hkc, hkw, hk1, hk2, hcw, hc1,
      hc2, hw1, hw2, h12]) item hitem S.R v₂ { S with R := maskRegs cnt w n X S.R Lp } rfl ht₁ ht₂
    (fun j hj i hi hin => by
      rw [hLi] at hi hin ⊢
      rw [hN] at hj
      have hjN : (j + 1) * Li ≤ N * Li := Nat.mul_le_mul_right Li (by omega)
      rw [Nat.add_one_mul] at hjN
      rw [hX' _ hin]
      simp only [show ¬ (Lp + j * Li + i < Lp) by omega, show Lp + j * Li + i < Lp + N * Li by
        omega, ↓reduceIte]
      congr 1
      rw [show Lp + j * Li + i - Lp = i + Li * j by rw [Nat.mul_comm]; omega,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi])
  rw [hN, hLi] at he₃
  rw [hN] at hm₃
  obtain ⟨v₄, hu₄, he₄⟩ := emitRuns_exec body (n := n) (X := X) S.R post
    (fun x hx => hpr x (List.mem_append_right _ hx)) (Lp + N * Li) v₃
    { S with R := maskRegs cnt w n X S.R (Lp + N * Li) } rfl ht₁
    (fun j hj hjn => by
      rw [hLq] at hj
      rw [hX' _ hjn]
      simp only [show ¬ (Lp + N * Li + j < Lp) by omega, show ¬ (Lp + N * Li + j < Lp + N * Li) by
        omega, show Lp + N * Li + j < Lp + N * Li + Lq by omega, ↓reduceIte]
      congr 1; omega)
  rw [hLq] at he₄
  obtain ⟨v₅, hu₅, he₅⟩ := scanEmit_exec body (a := nR) (t := t₁) (cnt := cnt) (w := w)
    (by simp [hn1, hnc, hnw, hc1.symm, hw1.symm, hcw]) false S.R v₄
    { S with R := maskRegs cnt w n X S.R (Lp + N * Li + Lq) } rfl ht₁
    (fun q h1 _ h3 => by
      rw [hX' q h3]
      simp only [show ¬ (q < Lp) by omega, show ¬ (q < Lp + N * Li) by omega,
        show ¬ (q < Lp + N * Li + Lq) by omega, ↓reduceIte])
  rw [hn] at he₅
  obtain ⟨v₆, hu₆, he₆⟩ := maskFinish_exec body hzc hzw hcw (p := Lp + N * Li + Lq + n)
    (by omega) S.R hc hw v₅ { S with R := maskRegs cnt w n X S.R (Lp + N * Li + Lq + n) } rfl
  refine ⟨v₆, _, by rw [hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))⟩
  unfold runMaskCost
  rw [hN]
  omega

end IntegerMultBounds.MathlibTM2.Node
