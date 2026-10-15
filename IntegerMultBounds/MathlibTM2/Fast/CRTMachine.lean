module

public import IntegerMultBounds.MathlibTM2.Fast.CRTDrive

/-!
# The CRT layout machines

**Iterations.** `crtFwdIter` processes one target axis `i` of the forward map: it pops the
widths `a i`, `s i` and `μ i` of the top entries of the lists `wT`, `sT`, `mT`, moves axis `i`
below the axes `i - 1, …, 0` (`crtFwdWalk_runs`), restores the width list, runs the forward
rotation pass (`crtRotP_runs`) and pushes the three values onto the done lists `wD`, `sD`, `mD`.
`crtInvIter` processes target `i` of the inverse map: inverse rotation pass, then the inverse
walk (`crtInvWalk_runs`).

**Machines.** `crtForward` runs the padding scan (`crtPad_runs`) and then `crtFwdIter` once per
axis, `d - 1` down to `0`; `crtInverse` runs `crtInvIter` once per axis, `0` up to `d - 1`, and
then the deletion scan (`crtDel_runs`). See `crtForward_runs`, `crtInverse_runs` and the round
trip `crtRoundTrip_runs`; `crtCost` is the explicit step bound of either machine.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult
open scoped Function

set_option linter.unusedSimpArgs false

/-- The bound of the rotation pass of a target with `pre` control bits, width `ai`, `post`
spectator bits, length `S`, offset step `μ` and records of `B` symbols. -/
def crtRotCost (pre ai post S μ B : ℕ) : ℕ :=
  2 ^ pre * (2 ^ ai * (8 * (2 ^ post * B) + 9) + 14 * μ + 2 * S + 10 * pre + 61) +
    2 * (2 ^ pre * 2 ^ ai * (2 ^ post * B)) + 41 * pre + 8 * B + 6 * (2 ^ post * B) +
    9 * post + 6 * 2 ^ ai + 9 * ai + 12 * S + 80

/-- A bound of `crtRotCost` uniform over the targets: total width `L`, widths in
`[amin, am]`, records of `B` symbols. -/
def crtRotU (L am amin B : ℕ) : ℕ :=
  16 * (2 ^ L * B) + 25 * 2 ^ L + 2 ^ (L - amin) * (10 * L + 61) + 50 * L + 8 * B +
    18 * 2 ^ am + 9 * am + 80

lemma crtRotCost_le (pre ai post S μ B L am amin : ℕ) (hL : pre + ai + post = L)
    (hS : S ≤ 2 ^ ai) (hμ : μ ≤ S) (hai : ai ≤ am) (hamin : amin ≤ ai) :
    crtRotCost pre ai post S μ B ≤ crtRotU L am amin B := by
  unfold crtRotCost crtRotU
  subst hL
  have e1 : 2 ^ pre * 2 ^ ai * (2 ^ post * B) = 2 ^ (pre + ai + post) * B := by
    rw [pow_add, pow_add]; ring
  have h1 : 2 ^ pre * 2 ^ ai ≤ 2 ^ (pre + ai + post) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ pre * μ ≤ 2 ^ (pre + ai + post) :=
    (Nat.mul_le_mul_left _ (hμ.trans hS)).trans h1
  have h3 : 2 ^ pre * S ≤ 2 ^ (pre + ai + post) := (Nat.mul_le_mul_left _ hS).trans h1
  have h4 : 2 ^ pre * (10 * pre + 61) ≤ 2 ^ (pre + ai + post - amin) * (10 * (pre + ai + post) + 61) :=
    Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (by omega)
  have h5 : 2 ^ post * B ≤ 2 ^ (pre + ai + post) * B :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h6 : 2 ^ ai ≤ 2 ^ am := Nat.pow_le_pow_right (by norm_num) hai
  have hexp : 2 ^ pre * (2 ^ ai * (8 * (2 ^ post * B) + 9) + 14 * μ + 2 * S + 10 * pre + 61) =
      8 * (2 ^ pre * 2 ^ ai * (2 ^ post * B)) + 9 * (2 ^ pre * 2 ^ ai) + 14 * (2 ^ pre * μ) +
        2 * (2 ^ pre * S) + 2 ^ pre * (10 * pre + 61) := by ring
  rw [hexp, e1]
  omega

section Iter

noncomputable section

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {T Q K : ℕ} {U F : Type} {body : F → Pr F T Q (prime + K) U}

/-- One target of the forward map. -/
def crtFwdIter (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) (r : CrtReg → Fin T) :
    Pr F T Q (prime + K) U :=
  .seq (crtPopEnt (r .wT) (r .aI)) <| .seq (crtPopEnt (r .sT) (r .sI)) <|
  .seq (crtPopEnt (r .mT) (r .muI)) <| .seq (usub (r .aI) (r .preU) (r .u1)) <|
  .seq (crtWhile (r .wT) (crtFwdStep hQ ι hι hT r)) <|
  .seq (crtMv (r .wW) (r .wT)) <| .seq (uclear (r .uU)) <|
  .seq (crtRotP true (crtLr r) (r .str) (r .acc) (r .tA) (r .tB) (r .tc) (r .tr) (r .sig)
    (r .msk) (r .preU) (r .postU) (r .aI) (r .sI) (r .muI) (r .zr) (r .rbU) (r .tsU) (r .lo)
    (r .hi) (r .ov) (r .u1) (r .u2)) <|
  .seq (ucopy (r .aI) (r .postU) (r .u1)) <|
  .seq (crtPushEnt (r .aI) (r .wD)) <| .seq (crtPushEnt (r .sI) (r .sD))
    (crtPushEnt (r .muI) (r .mD))

/-- The registers that are empty between iterations. -/
def crtIdle : List CrtReg :=
  [.aI, .sI, .muI, .aK, .vU, .uU, .wW, .vacc, .stmp, .tu, .u1, .u2, .acc, .tA, .tB, .tc, .tr,
    .rbU, .tsU, .lo, .hi, .ov, .nF, .tN, .fc, .sg, .mq, .c0, .c1, .c2, .it]

lemma crtEnts_length (xs : List ℕ) :
    (crtEnts (A := prime + K) xs).length = xs.sum + 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [crtEnts_cons, List.length_append, ih]; simp [crtEnt]; ring

lemma crtW_eq_sum {d : ℕ} (a : Fin d → ℕ) (o : List (Fin d)) : (o.map a).sum = crtW a o := rfl

/-- The register file between iterations: nine registers over a base file `R₀`. -/
def crtSt (r : CrtReg → Fin T) (R₀ : Regs T (prime + K))
    (vstr vwT vsT vmT vwD vsD vmD vpre vpost : List (Fin (prime + K + 4))) : Regs T (prime + K) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update R₀
    (r .str) vstr) (r .wT) vwT) (r .sT) vsT) (r .mT) vmT) (r .wD) vwD) (r .sD) vsD) (r .mD) vmD)
    (r .preU) vpre) (r .postU) vpost

lemma crtSt_of_ne {r : CrtReg → Fin T} (R₀ : Regs T (prime + K))
    (v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ : List (Fin (prime + K + 4))) (x : Fin T)
    (hx : ∀ y ∈ [CrtReg.str, .wT, .sT, .mT, .wD, .sD, .mD, .preU, .postU], x ≠ r y) :
    crtSt r R₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ x = R₀ x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hx
  simp only [crtSt, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6,
    Function.update_of_ne h7, Function.update_of_ne h8, Function.update_of_ne h9]

set_option maxHeartbeats 2000000 in
/-- One target `i` of the forward map. -/
theorem crtFwdIter_runs {d : ℕ} (a s μ : Fin d → ℕ) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hμ : ∀ j, μ j ≤ s j) (hadj : ∀ j j', a j ≤ a j' + 1) (am : ℕ) (ham : ∀ j, a j ≤ am)
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) {r : CrtReg → Fin T}
    (hr : Function.Injective r) (hrι : ∀ x j, r x ≠ ι j) {i : ℕ} (hi : i < d)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ x ∈ C y, x.val < 8)
    (R₀ : Regs T (prime + K))
    (hsig : R₀ (r .sig) = binSyms (crtPre a d) (crtSig a s d))
    (hmsk : R₀ (r .msk) = binSyms (crtPre a d) (crtMask a d)) (hzr : (R₀ (r .zr)).length = B)
    (he3 : R₀ (r .e3B) = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (h0 : ∀ x ∈ crtIdle, R₀ (r x) = []) (hι0 : ∀ i, R₀ (ι i) = [])
    (DW DS DM : List (Fin (prime + K + 4))) :
    crtRuns body (crtFwdIter hQ ι hι hT r)
      (crtSt r R₀ (crtBox a (crtLay (i + 1)) C 0).flatten (crtEnts ((crtRevAx (i + 1)).map a))
        (crtEnts ((crtRevAx (i + 1)).map s)) (crtEnts ((crtRevAx (i + 1)).map μ)) DW DS DM
        (List.replicate (crtPre a (i + 1)) tick)
        (List.replicate (crtW a ((List.finRange d).drop (i + 1))) tick))
      (crtSt r R₀ (crtBox a (crtLay i) (crtRotC s i hi (μ ⟨i, hi⟩) true C) 0).flatten
        (crtEnts ((crtRevAx i).map a)) (crtEnts ((crtRevAx i).map s))
        (crtEnts ((crtRevAx i).map μ)) (crtEnt (a ⟨i, hi⟩) ++ DW) (crtEnt (s ⟨i, hi⟩) ++ DS)
        (crtEnt (μ ⟨i, hi⟩) ++ DM) (List.replicate (crtPre a i) tick)
        (List.replicate (crtW a ((List.finRange d).drop i)) tick))
      (i * (crtStepBound T (crtPre a d) B (2 ^ crtPre a d * B) am + 2) +
        crtRotCost (crtPre a i) (a ⟨i, hi⟩) (crtW a ((List.finRange d).drop (i + 1)))
          (s ⟨i, hi⟩) (μ ⟨i, hi⟩) B +
        12 * crtPre a (i + 1) + 4 * s ⟨i, hi⟩ + 4 * μ ⟨i, hi⟩ + 4 * i + 50) := by
  have ne : ∀ {x y : CrtReg}, x ≠ y → r x ≠ r y := fun h => hr.ne h
  have upd : ∀ {α : Type} (f : Fin T → α) (y : CrtReg) (v : α) (x : CrtReg), x ≠ y →
      Function.update f (r y) v (r x) = f (r x) := fun f y v x h => Function.update_of_ne (ne h) _ _
  set I : Fin d := ⟨i, hi⟩ with hI
  set P := (List.finRange d).drop (i + 1) with hP
  set R := crtSt r R₀ (crtBox a (crtLay (i + 1)) C 0).flatten (crtEnts ((crtRevAx (i + 1)).map a))
    (crtEnts ((crtRevAx (i + 1)).map s)) (crtEnts ((crtRevAx (i + 1)).map μ)) DW DS DM
    (List.replicate (crtPre a (i + 1)) tick) (List.replicate (crtW a P) tick) with hR
  have eR : ∀ x : CrtReg, x ≠ .str → x ≠ .wT → x ≠ .sT → x ≠ .mT → x ≠ .wD → x ≠ .sD →
      x ≠ .mD → x ≠ .preU → x ≠ .postU → R (r x) = R₀ (r x) := by
    intro x h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [hR, crtSt_of_ne]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨ne h1, ne h2, ne h3, ne h4, ne h5, ne h6, ne h7, ne h8, ne h9⟩
  have z : ∀ x ∈ crtIdle, R (r x) = [] := by
    intro x hx
    rw [eR x] <;> first | exact h0 x hx | (rintro rfl; simp [crtIdle] at hx)
  have hrevS : ∀ (g : Fin d → ℕ), (crtRevAx (i + 1)).map g = g I :: (crtRevAx i).map g := fun g => by
    rw [crtRevAx_succ hi, List.map_cons]
  -- pop the three entries
  have vRwT : R (r .wT) = crtEnts (a I :: (crtRevAx i).map a) := by
    rw [hR]; simp (disch := decide) only [crtSt, upd, Function.update_self]; rw [hrevS]
  have vRsT : R (r .sT) = crtEnts (s I :: (crtRevAx i).map s) := by
    rw [hR]; simp (disch := decide) only [crtSt, upd, Function.update_self]; rw [hrevS]
  have vRmT : R (r .mT) = crtEnts (μ I :: (crtRevAx i).map μ) := by
    rw [hR]; simp (disch := decide) only [crtSt, upd, Function.update_self]; rw [hrevS]
  have s₁ := crtPopEnt_runs (body := body) (ne (by decide : CrtReg.wT ≠ .aI)) R (a I)
    ((crtRevAx i).map a) vRwT (z .aI (by decide))
  set R₁ := Function.update (Function.update R (r .wT) (crtEnts ((crtRevAx i).map a))) (r .aI)
    (List.replicate (a I) tick) with hR₁
  clear_value R₁
  have f₁ : ∀ x, x ≠ r .wT → x ≠ r .aI → R₁ x = R x := fun x h1 h2 => by
    rw [hR₁, Function.update_of_ne h2, Function.update_of_ne h1]
  have s₂ := crtPopEnt_runs (body := body) (ne (by decide : CrtReg.sT ≠ .sI)) R₁ (s I)
    ((crtRevAx i).map s)
    (by rw [f₁ _ (ne (by decide)) (ne (by decide)), vRsT])
    (by rw [f₁ _ (ne (by decide)) (ne (by decide))]; exact z .sI (by decide))
  set R₂ := Function.update (Function.update R₁ (r .sT) (crtEnts ((crtRevAx i).map s))) (r .sI)
    (List.replicate (s I) tick) with hR₂
  clear_value R₂
  have f₂ : ∀ x, x ≠ r .sT → x ≠ r .sI → R₂ x = R₁ x := fun x h1 h2 => by
    rw [hR₂, Function.update_of_ne h2, Function.update_of_ne h1]
  have s₃ := crtPopEnt_runs (body := body) (ne (by decide : CrtReg.mT ≠ .muI)) R₂ (μ I)
    ((crtRevAx i).map μ)
    (by rw [f₂ _ (ne (by decide)) (ne (by decide)), f₁ _ (ne (by decide)) (ne (by decide)), vRmT])
    (by rw [f₂ _ (ne (by decide)) (ne (by decide)), f₁ _ (ne (by decide)) (ne (by decide))]
        exact z .muI (by decide))
  set R₃ := Function.update (Function.update R₂ (r .mT) (crtEnts ((crtRevAx i).map μ))) (r .muI)
    (List.replicate (μ I) tick) with hR₃
  clear_value R₃
  have f₃ : ∀ x, x ≠ r .mT → x ≠ r .muI → R₃ x = R₂ x := fun x h1 h2 => by
    rw [hR₃, Function.update_of_ne h2, Function.update_of_ne h1]
  -- the three popped values and the unchanged registers
  have g₃ : ∀ x : CrtReg, x ≠ .wT → x ≠ .aI → x ≠ .sT → x ≠ .sI → x ≠ .mT → x ≠ .muI →
      R₃ (r x) = R (r x) := fun x h1 h2 h3 h4 h5 h6 => by
    rw [f₃ _ (ne h5) (ne h6), f₂ _ (ne h3) (ne h4), f₁ _ (ne h1) (ne h2)]
  have v₃aI : R₃ (r .aI) = List.replicate (a I) tick := by
    rw [f₃ _ (ne (by decide)) (ne (by decide)), f₂ _ (ne (by decide)) (ne (by decide)), hR₁,
      Function.update_self]
  have v₃sI : R₃ (r .sI) = List.replicate (s I) tick := by
    rw [f₃ _ (ne (by decide)) (ne (by decide)), hR₂, Function.update_self]
  have v₃muI : R₃ (r .muI) = List.replicate (μ I) tick := by rw [hR₃, Function.update_self]
  have v₃wT : R₃ (r .wT) = crtEnts ((crtRevAx i).map a) := by
    rw [f₃ _ (ne (by decide)) (ne (by decide)), f₂ _ (ne (by decide)) (ne (by decide)), hR₁,
      Function.update_of_ne (ne (by decide)), Function.update_self]
  have z₃ : ∀ x ∈ crtIdle, x ≠ .aI → x ≠ .sI → x ≠ .muI → R₃ (r x) = [] := by
    intro x hx h2 h4 h6
    rw [g₃ x (by rintro rfl; simp [crtIdle] at hx) h2 (by rintro rfl; simp [crtIdle] at hx) h4
      (by rintro rfl; simp [crtIdle] at hx) h6]
    exact z x hx
  have vR : ∀ x : CrtReg, R (r x) = crtSt r R₀ (crtBox a (crtLay (i + 1)) C 0).flatten
      (crtEnts ((crtRevAx (i + 1)).map a)) (crtEnts ((crtRevAx (i + 1)).map s))
      (crtEnts ((crtRevAx (i + 1)).map μ)) DW DS DM (List.replicate (crtPre a (i + 1)) tick)
      (List.replicate (crtW a P) tick) (r x) := fun x => by rw [hR]
  -- preU := pre - aI
  have s₄ := crtUsub_runs (body := body) (a := r .aI) (b := r .preU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₃ (z₃ .u1 (by decide) (by decide)
      (by decide) (by decide))
  set R₄ := Function.update R₃ (r .preU) ((R₃ (r .preU)).drop (R₃ (r .aI)).length) with hR₄
  clear_value R₄
  have f₄ : ∀ x, x ≠ r .preU → R₄ x = R₃ x := fun x h => by rw [hR₄, Function.update_of_ne h]
  have v₄pre : R₄ (r .preU) = List.replicate (crtPre a i) tick := by
    rw [hR₄, Function.update_self, v₃aI, g₃ .preU (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), vR]
    simp (disch := decide) only [crtSt, upd, Function.update_self]
    rw [List.length_replicate, List.drop_replicate, crtPre_succ a hi, Nat.add_sub_cancel]
  have g₄ : ∀ x : CrtReg, x ≠ .wT → x ≠ .aI → x ≠ .sT → x ≠ .sI → x ≠ .mT → x ≠ .muI →
      x ≠ .preU → R₄ (r x) = R (r x) := fun x h1 h2 h3 h4 h5 h6 h7 => by
    rw [f₄ _ (ne h7), g₃ x h1 h2 h3 h4 h5 h6]
  have vRstr : R (r .str) = (crtBox a (crtLay (i + 1)) C 0).flatten := by
    rw [hR]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  have vRpost : R (r .postU) = List.replicate (crtW a P) tick := by
    rw [hR]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  have ιR : ∀ j, R (ι j) = R₀ (ι j) := fun j => by
    rw [hR, crtSt_of_ne]
    intro y _; exact (hrι y j).symm
  have ι₄ : ∀ j, R₄ (ι j) = R₀ (ι j) := fun j => by
    rw [f₄ _ (hrι _ _).symm, f₃ _ (hrι _ _).symm (hrι _ _).symm,
      f₂ _ (hrι _ _).symm (hrι _ _).symm, f₁ _ (hrι _ _).symm (hrι _ _).symm, ιR]
  -- the walk
  have s₅ := crtFwdWalk_runs (body := body) a hQ ι hι hT hr hrι hi hadj am ham C B hB hC h8 R₄
    (by rw [g₄ .str (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), vRstr])
    (by rw [f₄ _ (ne (by decide)), v₃wT])
    (by rw [f₄ _ (ne (by decide))]; exact z₃ .wW (by decide) (by decide) (by decide) (by decide))
    (by rw [f₄ _ (ne (by decide))]; exact z₃ .uU (by decide) (by decide) (by decide) (by decide))
    (by rw [v₄pre, g₄ .postU (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), vRpost, List.length_replicate, List.length_replicate])
    (by rw [f₄ _ (ne (by decide)), v₃aI, List.length_replicate])
    (by rw [g₄ .e3B (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), eR .e3B (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), he3])
    (by intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
          (rw [f₄ _ (ne (by decide))]; exact z₃ _ (by decide) (by decide) (by decide) (by decide)))
    (fun j => by rw [ι₄, hι0])
  set R₅ := Function.update (Function.update (Function.update (Function.update R₄ (r .str)
    (crtBox a (crtLay i) C 0).flatten) (r .wT) []) (r .uU) (List.replicate (crtPre a i) tick))
    (r .wW) (crtEnts ((crtRevAx i).reverse.map a)) with hR₅
  clear_value R₅
  have f₅ : ∀ x, x ≠ r .str → x ≠ r .wT → x ≠ r .uU → x ≠ r .wW → R₅ x = R₄ x :=
    fun x h1 h2 h3 h4 => by
      rw [hR₅, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
        Function.update_of_ne h1]
  -- restore the width list, clear uU
  have s₆ := crtMv_runs (body := body) (ne (by decide : CrtReg.wW ≠ .wT)) R₅
  set R₆ := Function.update (Function.update R₅ (r .wW) []) (r .wT)
    ((R₅ (r .wW)).reverse ++ R₅ (r .wT)) with hR₆
  clear_value R₆
  have s₇ := crtClear_runs (body := body) (r .uU) R₆
  set R₇ := Function.update R₆ (r .uU) [] with hR₇
  clear_value R₇
  have v₅wW : R₅ (r .wW) = crtEnts ((crtRevAx i).reverse.map a) := by
    rw [hR₅, Function.update_self]
  have v₅wT : R₅ (r .wT) = [] := by
    rw [hR₅]; simp (disch := decide) only [upd, Function.update_self]
  have g₇ : ∀ x : CrtReg, x ≠ .str → x ≠ .wT → x ≠ .uU → x ≠ .wW → R₇ (r x) = R₄ (r x) :=
    fun x h1 h2 h3 h4 => by
      rw [hR₇, Function.update_of_ne (ne h3), hR₆, Function.update_of_ne (ne h2),
        Function.update_of_ne (ne h4), f₅ _ (ne h1) (ne h2) (ne h3) (ne h4)]
  have v₇str : R₇ (r .str) = (crtBox a (crtLay i) C 0).flatten := by
    rw [hR₇, Function.update_of_ne (ne (by decide)), hR₆, Function.update_of_ne (ne (by decide)),
      Function.update_of_ne (ne (by decide)), hR₅]
    simp (disch := decide) only [upd, Function.update_self]
  have v₇wT : R₇ (r .wT) = crtEnts ((crtRevAx i).map a) := by
    rw [hR₇, Function.update_of_ne (ne (by decide)), hR₆, Function.update_self, v₅wW, v₅wT,
      List.append_nil, crtEnts_reverse, List.map_reverse, List.reverse_reverse]
  have v₇uU : R₇ (r .uU) = [] := by rw [hR₇, Function.update_self]
  have v₇wW : R₇ (r .wW) = [] := by
    rw [hR₇, Function.update_of_ne (ne (by decide)), hR₆, Function.update_of_ne (ne (by decide)),
      Function.update_self]
  have z₇ : ∀ x ∈ crtIdle, x ≠ .aI → x ≠ .sI → x ≠ .muI → x ≠ .uU → x ≠ .wW →
      R₇ (r x) = [] := by
    intro x hx h2 h4 h6 h8 h9
    rw [g₇ x (by rintro rfl; simp [crtIdle] at hx) (by rintro rfl; simp [crtIdle] at hx) h8 h9,
      f₄ _ (by intro h; have := hr h; subst this; simp [crtIdle] at hx)]
    exact z₃ x hx h2 h4 h6
  have v₇ : ∀ x : CrtReg, x ≠ .str → x ≠ .wT → x ≠ .uU → x ≠ .wW → x ≠ .preU → x ≠ .aI →
      x ≠ .sT → x ≠ .sI → x ≠ .mT → x ≠ .muI → R₇ (r x) = R (r x) :=
    fun x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
      rw [g₇ x h1 h2 h3 h4, g₄ x h2 h6 h7 h8 h9 h10 h5]
  -- the rotation pass
  have hlay : crtLay (d := d) i = crtRevAx i ++ I :: P := crtLay_rot hi
  have s₈ := crtRotP_runs (body := body) a s true (crtLr r) (crtLr_ok hr)
    (str := r .str) (acc := r .acc) (tA := r .tA) (tB := r .tB) (tc := r .tc) (tr := r .tr)
    (sig := r .sig) (msk := r .msk) (preU := r .preU) (postU := r .postU) (aI := r .aI)
    (sI := r .sI) (muI := r .muI) (zr := r .zr) (rbU := r .rbU) (tsU := r .tsU) (lo := r .lo)
    (hi := r .hi) (ov := r .ov) (u₁ := r .u1) (u₂ := r .u2)
    (crt_nd hr [.str, .acc, .tA, .tB, .tc, .tr, .sig, .msk, .preU, .postU, .aI, .sI, .muI, .zr,
      .rbU, .tsU, .lo, .hi, .ov, .u1, .u2] (by decide))
    (by intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact crtLr_prot hr _ rfl (by decide))
    hs hi P (by rw [← hlay]; exact crtLay_nodup i) (μ I) (hμ I) C B hC R₇
    (by rw [v₇str, hlay])
    (by rw [v₇ .sig (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), eR .sig (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hsig])
    (by rw [v₇ .msk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), eR .msk (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hmsk])
    (by rw [g₇ .preU (by decide) (by decide) (by decide) (by decide), v₄pre,
          List.length_replicate])
    (by rw [v₇ .postU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), vRpost, List.length_replicate])
    (by rw [g₇ .aI (by decide) (by decide) (by decide) (by decide), f₄ _ (ne (by decide)), v₃aI,
          List.length_replicate])
    (by rw [g₇ .sI (by decide) (by decide) (by decide) (by decide), f₄ _ (ne (by decide)), v₃sI,
          List.length_replicate])
    (by rw [g₇ .muI (by decide) (by decide) (by decide) (by decide), f₄ _ (ne (by decide)),
          v₃muI, List.length_replicate])
    (by rw [v₇ .zr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), eR .zr (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hzr])
    (by intro k hk
        simp only [crtLr, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact z₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  set R₈ := Function.update R₇ (r .str)
    (crtBox a (crtRevAx i ++ I :: P) (crtRotC s i hi (μ I) true C) 0).flatten with hR₈
  clear_value R₈
  have f₈ : ∀ x, x ≠ r .str → R₈ x = R₇ x := fun x h => by rw [hR₈, Function.update_of_ne h]
  -- postU += aI, push the three entries
  have s₉ := crtUcopy_runs (body := body) (a := r .aI) (b := r .postU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₈
    (by rw [f₈ _ (ne (by decide))]
        exact z₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  set R₉ := Function.update R₈ (r .postU) (List.replicate (R₈ (r .aI)).length tick ++
    R₈ (r .postU)) with hR₉
  clear_value R₉
  have f₉ : ∀ x, x ≠ r .postU → R₉ x = R₈ x := fun x h => by rw [hR₉, Function.update_of_ne h]
  have v₈aI : R₈ (r .aI) = List.replicate (a I) tick := by
    rw [f₈ _ (ne (by decide)), g₇ .aI (by decide) (by decide) (by decide) (by decide),
      f₄ _ (ne (by decide)), v₃aI]
  have s₁₀ := crtPushEnt_runs (body := body) (ne (by decide : CrtReg.aI ≠ .wD)) R₉ (a I)
    (by rw [f₉ _ (ne (by decide)), v₈aI])
  set R₁₀ := Function.update (Function.update R₉ (r .aI) []) (r .wD) (crtEnt (a I) ++ R₉ (r .wD))
    with hR₁₀
  clear_value R₁₀
  have f₁₀ : ∀ x, x ≠ r .aI → x ≠ r .wD → R₁₀ x = R₉ x := fun x h1 h2 => by
    rw [hR₁₀, Function.update_of_ne h2, Function.update_of_ne h1]
  have s₁₁ := crtPushEnt_runs (body := body) (ne (by decide : CrtReg.sI ≠ .sD)) R₁₀ (s I)
    (by rw [f₁₀ _ (ne (by decide)) (ne (by decide)), f₉ _ (ne (by decide)),
          f₈ _ (ne (by decide)), g₇ .sI (by decide) (by decide) (by decide) (by decide),
          f₄ _ (ne (by decide)), v₃sI])
  set R₁₁ := Function.update (Function.update R₁₀ (r .sI) []) (r .sD) (crtEnt (s I) ++ R₁₀ (r .sD))
    with hR₁₁
  clear_value R₁₁
  have f₁₁ : ∀ x, x ≠ r .sI → x ≠ r .sD → R₁₁ x = R₁₀ x := fun x h1 h2 => by
    rw [hR₁₁, Function.update_of_ne h2, Function.update_of_ne h1]
  have s₁₂ := crtPushEnt_runs (body := body) (ne (by decide : CrtReg.muI ≠ .mD)) R₁₁ (μ I)
    (by rw [f₁₁ _ (ne (by decide)) (ne (by decide)), f₁₀ _ (ne (by decide)) (ne (by decide)),
          f₉ _ (ne (by decide)), f₈ _ (ne (by decide)),
          g₇ .muI (by decide) (by decide) (by decide) (by decide), f₄ _ (ne (by decide)), v₃muI])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ (crtRuns_seq s₃
    (crtRuns_seq s₄ (crtRuns_seq s₅ (crtRuns_seq s₆ (crtRuns_seq s₇ (crtRuns_seq s₈
      (crtRuns_seq s₉ (crtRuns_seq s₁₀ (crtRuns_seq s₁₁ s₁₂))))))))))) ?_) ?_
  all_goals clear s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂
  · -- the final register file
    have v₁₁ : ∀ x, x ≠ r .muI → x ≠ r .mD → x ≠ r .sI → x ≠ r .sD → x ≠ r .aI → x ≠ r .wD →
        x ≠ r .postU → x ≠ r .str → Function.update (Function.update R₁₁ (r .muI) []) (r .mD)
          (crtEnt (μ I) ++ R₁₁ (r .mD)) x = R₇ x := fun x h1 h2 h3 h4 h5 h6 h7 h8 => by
      rw [Function.update_of_ne h2, Function.update_of_ne h1, f₁₁ _ h3 h4, f₁₀ _ h5 h6, f₉ _ h7,
        f₈ _ h8]
    funext x
    by_cases x1 : x = r .mD
    · rw [x1, Function.update_self, f₁₁ _ (ne (by decide)) (ne (by decide)),
        f₁₀ _ (ne (by decide)) (ne (by decide)), f₉ _ (ne (by decide)), f₈ _ (ne (by decide)),
        v₇ .mD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), hR]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
    by_cases x2 : x = r .muI
    · rw [x2, Function.update_of_ne (ne (by decide)), Function.update_self]
      simp (disch := decide) only [crtSt, upd]
      exact (h0 .muI (by decide)).symm
    by_cases x3 : x = r .sD
    · rw [x3, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
        hR₁₁, Function.update_self, f₁₀ _ (ne (by decide)) (ne (by decide)),
        f₉ _ (ne (by decide)), f₈ _ (ne (by decide)),
        v₇ .sD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), hR]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
    by_cases x4 : x = r .sI
    · rw [x4, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
        hR₁₁, Function.update_of_ne (ne (by decide)), Function.update_self]
      simp (disch := decide) only [crtSt, upd]
      exact (h0 .sI (by decide)).symm
    by_cases x5 : x = r .wD
    · rw [x5, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
        f₁₁ _ (ne (by decide)) (ne (by decide)), hR₁₀, Function.update_self,
        f₉ _ (ne (by decide)), f₈ _ (ne (by decide)),
        v₇ .wD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), hR]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
    by_cases x6 : x = r .aI
    · rw [x6, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
        f₁₁ _ (ne (by decide)) (ne (by decide)), hR₁₀, Function.update_of_ne (ne (by decide)),
        Function.update_self]
      simp (disch := decide) only [crtSt, upd]
      exact (h0 .aI (by decide)).symm
    by_cases x7 : x = r .postU
    · rw [x7, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
        f₁₁ _ (ne (by decide)) (ne (by decide)), f₁₀ _ (ne (by decide)) (ne (by decide)), hR₉,
        Function.update_self, v₈aI, f₈ _ (ne (by decide)),
        v₇ .postU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), vRpost, List.length_replicate,
        List.replicate_append_replicate]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
      rw [crt_drop_finRange hi, crtW_cons]
    by_cases x8 : x = r .str
    · rw [x8, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
        f₁₁ _ (ne (by decide)) (ne (by decide)), f₁₀ _ (ne (by decide)) (ne (by decide)),
        f₉ _ (ne (by decide)), hR₈, Function.update_self]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
      rw [hlay]
    rw [v₁₁ x x2 x1 x4 x3 x6 x5 x7 x8]
    by_cases x9 : x = r .wT
    · rw [x9, v₇wT]; simp (disch := decide) only [crtSt, upd, Function.update_self]
    by_cases x10 : x = r .uU
    · rw [x10, v₇uU]; simp (disch := decide) only [crtSt, upd]; exact (h0 .uU (by decide)).symm
    by_cases x11 : x = r .wW
    · rw [x11, v₇wW]; simp (disch := decide) only [crtSt, upd]; exact (h0 .wW (by decide)).symm
    by_cases x12 : x = r .preU
    · rw [x12, g₇ .preU (by decide) (by decide) (by decide) (by decide), v₄pre]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
    rw [hR₇, Function.update_of_ne x10, hR₆, Function.update_of_ne x9, Function.update_of_ne x11,
      f₅ _ x8 x9 x10 x11, f₄ _ x12]
    by_cases x13 : x = r .sT
    · rw [x13, f₃ _ (ne (by decide)) (ne (by decide)), hR₂, Function.update_of_ne (ne (by decide)),
        Function.update_self]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
    by_cases x14 : x = r .mT
    · rw [x14, hR₃, Function.update_of_ne (ne (by decide)), Function.update_self]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
    rw [f₃ _ x14 x2, f₂ _ x13 x4, f₁ _ x9 x6, hR]
    simp only [crtSt, Function.update_of_ne x1, Function.update_of_ne x3, Function.update_of_ne x5,
      Function.update_of_ne x7, Function.update_of_ne x8, Function.update_of_ne x9,
      Function.update_of_ne x12, Function.update_of_ne x13, Function.update_of_ne x14]
  · have l₄ : (R₃ (r .aI)).length = a I := by rw [v₃aI, List.length_replicate]
    have l₆ : (R₅ (r .wW)).length = crtPre a i + 2 * i := by
      rw [v₅wW, crtEnts_length, List.length_map, List.length_reverse, crtRevAx_length i hi.le,
        crtW_eq_sum, crtW_perm a (List.reverse_perm _), crtW_revAx a i hi.le]
    have l₇ : (R₆ (r .uU)).length = crtPre a i := by
      rw [hR₆, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
        hR₅]
      simp (disch := decide) only [upd, Function.update_self]
      rw [List.length_replicate]
    have l₉ : (R₈ (r .aI)).length = a I := by rw [v₈aI, List.length_replicate]
    rw [l₄, l₆, l₇, l₉, crtPre_succ a hi]
    unfold crtRotCost
    simp only [← hI]
    omega

/-- One target of the inverse map. -/
def crtInvIter (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) (r : CrtReg → Fin T) :
    Pr F T Q (prime + K) U :=
  .seq (crtPopEnt (r .wD) (r .aI)) <| .seq (crtPopEnt (r .sD) (r .sI)) <|
  .seq (crtPopEnt (r .mD) (r .muI)) <| .seq (usub (r .aI) (r .postU) (r .u1)) <|
  .seq (crtRotP false (crtLr r) (r .str) (r .acc) (r .tA) (r .tB) (r .tc) (r .tr) (r .sig)
    (r .msk) (r .preU) (r .postU) (r .aI) (r .sI) (r .muI) (r .zr) (r .rbU) (r .tsU) (r .lo)
    (r .hi) (r .ov) (r .u1) (r .u2)) <|
  .seq (crtMv (r .wT) (r .wW)) <| .seq (crtWhile (r .wW) (crtInvStep hQ ι hι hT r)) <|
  .seq (uclear (r .vacc)) <| .seq (ucopy (r .aI) (r .preU) (r .u1)) <|
  .seq (crtPushEnt (r .aI) (r .wT)) <| .seq (crtPushEnt (r .sI) (r .sT))
    (crtPushEnt (r .muI) (r .mT))

set_option maxHeartbeats 2000000 in
/-- One target `i` of the inverse map. -/
theorem crtInvIter_runs {d : ℕ} (a s μ : Fin d → ℕ) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hμ : ∀ j, μ j ≤ s j) (hadj : ∀ j j', a j ≤ a j' + 1) (am : ℕ) (ham : ∀ j, a j ≤ am)
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) {r : CrtReg → Fin T}
    (hr : Function.Injective r) (hrι : ∀ x j, r x ≠ ι j) {i : ℕ} (hi : i < d)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ x ∈ C y, x.val < 8)
    (R₀ : Regs T (prime + K))
    (hsig : R₀ (r .sig) = binSyms (crtPre a d) (crtSig a s d))
    (hmsk : R₀ (r .msk) = binSyms (crtPre a d) (crtMask a d)) (hzr : (R₀ (r .zr)).length = B)
    (he3 : R₀ (r .e3B) = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (h0 : ∀ x ∈ crtIdle, R₀ (r x) = []) (hι0 : ∀ i, R₀ (ι i) = [])
    (DS DM : List (Fin (prime + K + 4))) :
    crtRuns body (crtInvIter hQ ι hι hT r)
      (crtSt r R₀ (crtBox a (crtLay i) C 0).flatten (crtEnts ((crtRevAx i).map a)) DS DM
        (crtEnts (((List.finRange d).drop i).map a)) (crtEnts (((List.finRange d).drop i).map s))
        (crtEnts (((List.finRange d).drop i).map μ)) (List.replicate (crtPre a i) tick)
        (List.replicate (crtW a ((List.finRange d).drop i)) tick))
      (crtSt r R₀ (crtBox a (crtLay (i + 1)) (crtRotC s i hi (μ ⟨i, hi⟩) false C) 0).flatten
        (crtEnts ((crtRevAx (i + 1)).map a)) (crtEnt (s ⟨i, hi⟩) ++ DS) (crtEnt (μ ⟨i, hi⟩) ++ DM)
        (crtEnts (((List.finRange d).drop (i + 1)).map a))
        (crtEnts (((List.finRange d).drop (i + 1)).map s))
        (crtEnts (((List.finRange d).drop (i + 1)).map μ)) (List.replicate (crtPre a (i + 1)) tick)
        (List.replicate (crtW a ((List.finRange d).drop (i + 1))) tick))
      (i * (crtStepBound T (crtPre a d) B (2 ^ crtPre a d * B) am + 2) +
        crtRotCost (crtPre a i) (a ⟨i, hi⟩) (crtW a ((List.finRange d).drop (i + 1)))
          (s ⟨i, hi⟩) (μ ⟨i, hi⟩) B +
        12 * crtPre a (i + 1) + 4 * s ⟨i, hi⟩ + 4 * μ ⟨i, hi⟩ + 4 * i + 50) := by
  have ne : ∀ {x y : CrtReg}, x ≠ y → r x ≠ r y := fun h => hr.ne h
  have upd : ∀ {α : Type} (f : Fin T → α) (y : CrtReg) (v : α) (x : CrtReg), x ≠ y →
      Function.update f (r y) v (r x) = f (r x) := fun f y v x h => Function.update_of_ne (ne h) _ _
  set I : Fin d := ⟨i, hi⟩ with hI
  set P := (List.finRange d).drop (i + 1) with hP
  have hdrop : ∀ g : Fin d → ℕ, ((List.finRange d).drop i).map g = g I :: P.map g := fun g => by
    rw [crt_drop_finRange hi, List.map_cons]
  set R := crtSt r R₀ (crtBox a (crtLay i) C 0).flatten (crtEnts ((crtRevAx i).map a)) DS DM
    (crtEnts (((List.finRange d).drop i).map a)) (crtEnts (((List.finRange d).drop i).map s))
    (crtEnts (((List.finRange d).drop i).map μ)) (List.replicate (crtPre a i) tick)
    (List.replicate (crtW a ((List.finRange d).drop i)) tick) with hR
  have eR : ∀ x : CrtReg, x ≠ .str → x ≠ .wT → x ≠ .sT → x ≠ .mT → x ≠ .wD → x ≠ .sD →
      x ≠ .mD → x ≠ .preU → x ≠ .postU → R (r x) = R₀ (r x) := by
    intro x h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [hR, crtSt_of_ne]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨ne h1, ne h2, ne h3, ne h4, ne h5, ne h6, ne h7, ne h8, ne h9⟩
  have z : ∀ x ∈ crtIdle, R (r x) = [] := by
    intro x hx
    rw [eR x] <;> first | exact h0 x hx | (rintro rfl; simp [crtIdle] at hx)
  have vRwD : R (r .wD) = crtEnts (a I :: P.map a) := by
    rw [hR]; simp (disch := decide) only [crtSt, upd, Function.update_self]; rw [hdrop]
  have vRsD : R (r .sD) = crtEnts (s I :: P.map s) := by
    rw [hR]; simp (disch := decide) only [crtSt, upd, Function.update_self]; rw [hdrop]
  have vRmD : R (r .mD) = crtEnts (μ I :: P.map μ) := by
    rw [hR]; simp (disch := decide) only [crtSt, upd, Function.update_self]; rw [hdrop]
  have s₁ := crtPopEnt_runs (body := body) (ne (by decide : CrtReg.wD ≠ .aI)) R (a I)
    (P.map a) vRwD (z .aI (by decide))
  set R₁ := Function.update (Function.update R (r .wD) (crtEnts (P.map a))) (r .aI)
    (List.replicate (a I) tick) with hR₁
  clear_value R₁
  have f₁ : ∀ x, x ≠ r .wD → x ≠ r .aI → R₁ x = R x := fun x h1 h2 => by
    rw [hR₁, Function.update_of_ne h2, Function.update_of_ne h1]
  have s₂ := crtPopEnt_runs (body := body) (ne (by decide : CrtReg.sD ≠ .sI)) R₁ (s I)
    (P.map s) (by rw [f₁ _ (ne (by decide)) (ne (by decide)), vRsD])
    (by rw [f₁ _ (ne (by decide)) (ne (by decide))]; exact z .sI (by decide))
  set R₂ := Function.update (Function.update R₁ (r .sD) (crtEnts (P.map s))) (r .sI)
    (List.replicate (s I) tick) with hR₂
  clear_value R₂
  have f₂ : ∀ x, x ≠ r .sD → x ≠ r .sI → R₂ x = R₁ x := fun x h1 h2 => by
    rw [hR₂, Function.update_of_ne h2, Function.update_of_ne h1]
  have s₃ := crtPopEnt_runs (body := body) (ne (by decide : CrtReg.mD ≠ .muI)) R₂ (μ I)
    (P.map μ) (by rw [f₂ _ (ne (by decide)) (ne (by decide)), f₁ _ (ne (by decide))
      (ne (by decide)), vRmD])
    (by rw [f₂ _ (ne (by decide)) (ne (by decide)), f₁ _ (ne (by decide)) (ne (by decide))]
        exact z .muI (by decide))
  set R₃ := Function.update (Function.update R₂ (r .mD) (crtEnts (P.map μ))) (r .muI)
    (List.replicate (μ I) tick) with hR₃
  clear_value R₃
  have f₃ : ∀ x, x ≠ r .mD → x ≠ r .muI → R₃ x = R₂ x := fun x h1 h2 => by
    rw [hR₃, Function.update_of_ne h2, Function.update_of_ne h1]
  have g₃ : ∀ x : CrtReg, x ≠ .wD → x ≠ .aI → x ≠ .sD → x ≠ .sI → x ≠ .mD → x ≠ .muI →
      R₃ (r x) = R (r x) := fun x h1 h2 h3 h4 h5 h6 => by
    rw [f₃ _ (ne h5) (ne h6), f₂ _ (ne h3) (ne h4), f₁ _ (ne h1) (ne h2)]
  have v₃aI : R₃ (r .aI) = List.replicate (a I) tick := by
    rw [f₃ _ (ne (by decide)) (ne (by decide)), f₂ _ (ne (by decide)) (ne (by decide)), hR₁,
      Function.update_self]
  have v₃sI : R₃ (r .sI) = List.replicate (s I) tick := by
    rw [f₃ _ (ne (by decide)) (ne (by decide)), hR₂, Function.update_self]
  have v₃muI : R₃ (r .muI) = List.replicate (μ I) tick := by rw [hR₃, Function.update_self]
  have z₃ : ∀ x ∈ crtIdle, x ≠ .aI → x ≠ .sI → x ≠ .muI → R₃ (r x) = [] := by
    intro x hx h2 h4 h6
    rw [g₃ x (by rintro rfl; simp [crtIdle] at hx) h2 (by rintro rfl; simp [crtIdle] at hx) h4
      (by rintro rfl; simp [crtIdle] at hx) h6]
    exact z x hx
  have vR : ∀ x : CrtReg, R (r x) = crtSt r R₀ (crtBox a (crtLay i) C 0).flatten
      (crtEnts ((crtRevAx i).map a)) DS DM (crtEnts (((List.finRange d).drop i).map a))
      (crtEnts (((List.finRange d).drop i).map s)) (crtEnts (((List.finRange d).drop i).map μ))
      (List.replicate (crtPre a i) tick)
      (List.replicate (crtW a ((List.finRange d).drop i)) tick) (r x) := fun x => by rw [hR]
  -- postU := post - aI
  have s₄ := crtUsub_runs (body := body) (a := r .aI) (b := r .postU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₃ (z₃ .u1 (by decide) (by decide)
      (by decide) (by decide))
  set R₄ := Function.update R₃ (r .postU) ((R₃ (r .postU)).drop (R₃ (r .aI)).length) with hR₄
  clear_value R₄
  have f₄ : ∀ x, x ≠ r .postU → R₄ x = R₃ x := fun x h => by rw [hR₄, Function.update_of_ne h]
  have v₄post : R₄ (r .postU) = List.replicate (crtW a P) tick := by
    rw [hR₄, Function.update_self, v₃aI, g₃ .postU (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), vR]
    simp (disch := decide) only [crtSt, upd, Function.update_self]
    rw [List.length_replicate, List.drop_replicate, crt_drop_finRange hi, crtW_cons,
      Nat.add_sub_cancel_left]
  have g₄ : ∀ x : CrtReg, x ≠ .wD → x ≠ .aI → x ≠ .sD → x ≠ .sI → x ≠ .mD → x ≠ .muI →
      x ≠ .postU → R₄ (r x) = R (r x) := fun x h1 h2 h3 h4 h5 h6 h7 => by
    rw [f₄ _ (ne h7), g₃ x h1 h2 h3 h4 h5 h6]
  have vRstr : R (r .str) = (crtBox a (crtLay i) C 0).flatten := by
    rw [hR]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  have vRpre : R (r .preU) = List.replicate (crtPre a i) tick := by
    rw [hR]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  have vRwT : R (r .wT) = crtEnts ((crtRevAx i).map a) := by
    rw [hR]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  have ιR : ∀ j, R (ι j) = R₀ (ι j) := fun j => by
    rw [hR, crtSt_of_ne]
    intro y _; exact (hrι y j).symm
  have hlay : crtLay (d := d) i = crtRevAx i ++ I :: P := crtLay_rot hi
  -- the inverse rotation pass
  have s₅ := crtRotP_runs (body := body) a s false (crtLr r) (crtLr_ok hr)
    (str := r .str) (acc := r .acc) (tA := r .tA) (tB := r .tB) (tc := r .tc) (tr := r .tr)
    (sig := r .sig) (msk := r .msk) (preU := r .preU) (postU := r .postU) (aI := r .aI)
    (sI := r .sI) (muI := r .muI) (zr := r .zr) (rbU := r .rbU) (tsU := r .tsU) (lo := r .lo)
    (hi := r .hi) (ov := r .ov) (u₁ := r .u1) (u₂ := r .u2)
    (crt_nd hr [.str, .acc, .tA, .tB, .tc, .tr, .sig, .msk, .preU, .postU, .aI, .sI, .muI, .zr,
      .rbU, .tsU, .lo, .hi, .ov, .u1, .u2] (by decide))
    (by intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact crtLr_prot hr _ rfl (by decide))
    hs hi P (by rw [← hlay]; exact crtLay_nodup i) (μ I) (hμ I) C B hC R₄
    (by rw [g₄ .str (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), vRstr, hlay])
    (by rw [g₄ .sig (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), eR .sig (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), hsig])
    (by rw [g₄ .msk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), eR .msk (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), hmsk])
    (by rw [g₄ .preU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), vRpre, List.length_replicate])
    (by rw [v₄post, List.length_replicate])
    (by rw [f₄ _ (ne (by decide)), v₃aI, List.length_replicate])
    (by rw [f₄ _ (ne (by decide)), v₃sI, List.length_replicate])
    (by rw [f₄ _ (ne (by decide)), v₃muI, List.length_replicate])
    (by rw [g₄ .zr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), eR .zr (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), hzr])
    (by intro k hk
        simp only [crtLr, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (rw [f₄ _ (ne (by decide))]; exact z₃ _ (by decide) (by decide) (by decide) (by decide)))
  set C' := crtRotC s i hi (μ I) false C with hC'
  set R₅ := Function.update R₄ (r .str) (crtBox a (crtRevAx i ++ I :: P) C' 0).flatten with hR₅
  clear_value R₅
  have f₅ : ∀ x, x ≠ r .str → R₅ x = R₄ x := fun x h => by rw [hR₅, Function.update_of_ne h]
  -- reverse the done list onto wW, walk
  have s₆ := crtMv_runs (body := body) (ne (by decide : CrtReg.wT ≠ .wW)) R₅
  set R₆ := Function.update (Function.update R₅ (r .wT) []) (r .wW)
    ((R₅ (r .wT)).reverse ++ R₅ (r .wW)) with hR₆
  clear_value R₆
  have v₅wT : R₅ (r .wT) = crtEnts ((crtRevAx i).map a) := by
    rw [f₅ _ (ne (by decide)), g₄ .wT (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), vRwT]
  have v₅wW : R₅ (r .wW) = [] := by
    rw [f₅ _ (ne (by decide)), f₄ _ (ne (by decide))]
    exact z₃ .wW (by decide) (by decide) (by decide) (by decide)
  have g₆ : ∀ x : CrtReg, x ≠ .wT → x ≠ .wW → x ≠ .str → R₆ (r x) = R₄ (r x) :=
    fun x h1 h2 h3 => by
      rw [hR₆, Function.update_of_ne (ne h2), Function.update_of_ne (ne h1), f₅ _ (ne h3)]
  have ι₆ : ∀ j, R₆ (ι j) = R₀ (ι j) := fun j => by
    rw [hR₆, Function.update_of_ne (hrι _ _).symm, Function.update_of_ne (hrι _ _).symm,
      f₅ _ (hrι _ _).symm, f₄ _ (hrι _ _).symm, f₃ _ (hrι _ _).symm (hrι _ _).symm,
      f₂ _ (hrι _ _).symm (hrι _ _).symm, f₁ _ (hrι _ _).symm (hrι _ _).symm, ιR]
  have hC'len : ∀ y, (C' y).length = B := fun y => by
    rw [hC']; unfold crtRotC; split_ifs <;> exact hC _
  have h8' : ∀ y, ∀ x ∈ C' y, x.val < 8 := fun y x hx => by
    rw [hC'] at hx; unfold crtRotC at hx; split_ifs at hx <;> exact h8 _ x hx
  have s₇ := crtInvWalk_runs (body := body) a hQ ι hι hT hr hrι hi hadj am ham C' B hB hC'len h8'
    R₆
    (by rw [hR₆, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
          hR₅, Function.update_self, hlay])
    (by rw [hR₆, Function.update_self, v₅wT, v₅wW, List.append_nil, crtEnts_reverse,
          List.map_reverse])
    (by rw [hR₆, Function.update_of_ne (ne (by decide)), Function.update_self])
    (by rw [g₆ .vacc (by decide) (by decide) (by decide), f₄ _ (ne (by decide))]
        exact z₃ .vacc (by decide) (by decide) (by decide) (by decide))
    (by rw [g₆ .preU (by decide) (by decide) (by decide), g₄ .preU (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide), vRpre,
          List.length_replicate])
    (by rw [g₆ .postU (by decide) (by decide) (by decide), v₄post, List.length_replicate])
    (by rw [g₆ .aI (by decide) (by decide) (by decide), f₄ _ (ne (by decide)), v₃aI,
          List.length_replicate])
    (by rw [g₆ .e3B (by decide) (by decide) (by decide), g₄ .e3B (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide), eR .e3B (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), he3])
    (by intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (rw [g₆ _ (by decide) (by decide) (by decide), f₄ _ (ne (by decide))]
           exact z₃ _ (by decide) (by decide) (by decide) (by decide)))
    (fun j => by rw [ι₆, hι0])
  set R₇ := Function.update (Function.update (Function.update (Function.update R₆ (r .str)
    (crtBox a (crtLay (i + 1)) C' 0).flatten) (r .wW) []) (r .vacc)
    (List.replicate (crtPre a i) tick)) (r .wT) (crtEnts ((crtRevAx i).map a)) with hR₇
  clear_value R₇
  have f₇ : ∀ x, x ≠ r .str → x ≠ r .wW → x ≠ r .vacc → x ≠ r .wT → R₇ x = R₆ x :=
    fun x h1 h2 h3 h4 => by
      rw [hR₇, Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2,
        Function.update_of_ne h1]
  have s₈ := crtClear_runs (body := body) (r .vacc) R₇
  set R₈ := Function.update R₇ (r .vacc) [] with hR₈
  clear_value R₈
  have f₈ : ∀ x, x ≠ r .vacc → R₈ x = R₇ x := fun x h => by rw [hR₈, Function.update_of_ne h]
  have g₈ : ∀ x : CrtReg, x ≠ .str → x ≠ .wW → x ≠ .vacc → x ≠ .wT → R₈ (r x) = R₄ (r x) :=
    fun x h1 h2 h3 h4 => by
      rw [f₈ _ (ne h3), f₇ _ (ne h1) (ne h2) (ne h3) (ne h4), g₆ x h4 h2 h1]
  have v₈aI : R₈ (r .aI) = List.replicate (a I) tick := by
    rw [g₈ .aI (by decide) (by decide) (by decide) (by decide), f₄ _ (ne (by decide)), v₃aI]
  have s₉ := crtUcopy_runs (body := body) (a := r .aI) (b := r .preU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₈
    (by rw [g₈ .u1 (by decide) (by decide) (by decide) (by decide), f₄ _ (ne (by decide))]
        exact z₃ .u1 (by decide) (by decide) (by decide) (by decide))
  set R₉ := Function.update R₈ (r .preU) (List.replicate (R₈ (r .aI)).length tick ++
    R₈ (r .preU)) with hR₉
  clear_value R₉
  have f₉ : ∀ x, x ≠ r .preU → R₉ x = R₈ x := fun x h => by rw [hR₉, Function.update_of_ne h]
  have s₁₀ := crtPushEnt_runs (body := body) (ne (by decide : CrtReg.aI ≠ .wT)) R₉ (a I)
    (by rw [f₉ _ (ne (by decide)), v₈aI])
  set R₁₀ := Function.update (Function.update R₉ (r .aI) []) (r .wT) (crtEnt (a I) ++ R₉ (r .wT))
    with hR₁₀
  clear_value R₁₀
  have f₁₀ : ∀ x, x ≠ r .aI → x ≠ r .wT → R₁₀ x = R₉ x := fun x h1 h2 => by
    rw [hR₁₀, Function.update_of_ne h2, Function.update_of_ne h1]
  have s₁₁ := crtPushEnt_runs (body := body) (ne (by decide : CrtReg.sI ≠ .sT)) R₁₀ (s I)
    (by rw [f₁₀ _ (ne (by decide)) (ne (by decide)), f₉ _ (ne (by decide)),
          g₈ .sI (by decide) (by decide) (by decide) (by decide), f₄ _ (ne (by decide)), v₃sI])
  set R₁₁ := Function.update (Function.update R₁₀ (r .sI) []) (r .sT) (crtEnt (s I) ++ R₁₀ (r .sT))
    with hR₁₁
  clear_value R₁₁
  have f₁₁ : ∀ x, x ≠ r .sI → x ≠ r .sT → R₁₁ x = R₁₀ x := fun x h1 h2 => by
    rw [hR₁₁, Function.update_of_ne h2, Function.update_of_ne h1]
  have s₁₂ := crtPushEnt_runs (body := body) (ne (by decide : CrtReg.muI ≠ .mT)) R₁₁ (μ I)
    (by rw [f₁₁ _ (ne (by decide)) (ne (by decide)), f₁₀ _ (ne (by decide)) (ne (by decide)),
          f₉ _ (ne (by decide)), g₈ .muI (by decide) (by decide) (by decide) (by decide),
          f₄ _ (ne (by decide)), v₃muI])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ (crtRuns_seq s₃
    (crtRuns_seq s₄ (crtRuns_seq s₅ (crtRuns_seq s₆ (crtRuns_seq s₇ (crtRuns_seq s₈
      (crtRuns_seq s₉ (crtRuns_seq s₁₀ (crtRuns_seq s₁₁ s₁₂))))))))))) ?_) ?_
  all_goals clear s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂
  · have v₁₁ : ∀ x, x ≠ r .muI → x ≠ r .mT → x ≠ r .sI → x ≠ r .sT → x ≠ r .aI → x ≠ r .wT →
        x ≠ r .preU → Function.update (Function.update R₁₁ (r .muI) []) (r .mT)
          (crtEnt (μ I) ++ R₁₁ (r .mT)) x = R₈ x := fun x h1 h2 h3 h4 h5 h6 h7 => by
      rw [Function.update_of_ne h2, Function.update_of_ne h1, f₁₁ _ h3 h4, f₁₀ _ h5 h6, f₉ _ h7]
    funext x
    by_cases x1 : x = r .mT
    · rw [x1, Function.update_self, f₁₁ _ (ne (by decide)) (ne (by decide)),
        f₁₀ _ (ne (by decide)) (ne (by decide)), f₉ _ (ne (by decide)),
        g₈ .mT (by decide) (by decide) (by decide) (by decide),
        g₄ .mT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hR]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
    by_cases x2 : x = r .muI
    · rw [x2, Function.update_of_ne (ne (by decide)), Function.update_self]
      simp (disch := decide) only [crtSt, upd]
      exact (h0 .muI (by decide)).symm
    by_cases x3 : x = r .sT
    · rw [x3, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
        hR₁₁, Function.update_self, f₁₀ _ (ne (by decide)) (ne (by decide)),
        f₉ _ (ne (by decide)), g₈ .sT (by decide) (by decide) (by decide) (by decide),
        g₄ .sT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hR]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
    by_cases x4 : x = r .sI
    · rw [x4, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
        hR₁₁, Function.update_of_ne (ne (by decide)), Function.update_self]
      simp (disch := decide) only [crtSt, upd]
      exact (h0 .sI (by decide)).symm
    by_cases x5 : x = r .wT
    · rw [x5, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
        f₁₁ _ (ne (by decide)) (ne (by decide)), hR₁₀, Function.update_self,
        f₉ _ (ne (by decide)), f₈ _ (ne (by decide)), hR₇, Function.update_self]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
      rw [crtRevAx_succ hi, List.map_cons, crtEnts_cons]
    by_cases x6 : x = r .aI
    · rw [x6, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
        f₁₁ _ (ne (by decide)) (ne (by decide)), hR₁₀, Function.update_of_ne (ne (by decide)),
        Function.update_self]
      simp (disch := decide) only [crtSt, upd]
      exact (h0 .aI (by decide)).symm
    by_cases x7 : x = r .preU
    · rw [x7, Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
        f₁₁ _ (ne (by decide)) (ne (by decide)), f₁₀ _ (ne (by decide)) (ne (by decide)), hR₉,
        Function.update_self, v₈aI, g₈ .preU (by decide) (by decide) (by decide) (by decide),
        g₄ .preU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), vRpre, List.length_replicate, List.replicate_append_replicate]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
      rw [crtPre_succ a hi, Nat.add_comm (a I)]
    rw [v₁₁ x x2 x1 x4 x3 x6 x5 x7]
    by_cases x8 : x = r .str
    · rw [x8, f₈ _ (ne (by decide)), hR₇]
      simp (disch := decide) only [upd, Function.update_self, crtSt]
    by_cases x9 : x = r .wW
    · rw [x9, f₈ _ (ne (by decide)), hR₇]
      simp (disch := decide) only [upd, Function.update_self, crtSt]
      exact (h0 .wW (by decide)).symm
    by_cases x10 : x = r .vacc
    · rw [x10, hR₈, Function.update_self]
      simp (disch := decide) only [crtSt, upd]
      exact (h0 .vacc (by decide)).symm
    rw [hR₈, Function.update_of_ne x10, hR₇, Function.update_of_ne x5, Function.update_of_ne x10,
      Function.update_of_ne x9, Function.update_of_ne x8, hR₆, Function.update_of_ne x9,
      Function.update_of_ne x5, f₅ _ x8]
    by_cases x11 : x = r .postU
    · rw [x11, v₄post]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
    rw [f₄ _ x11]
    by_cases x12 : x = r .wD
    · rw [x12, f₃ _ (ne (by decide)) (ne (by decide)), f₂ _ (ne (by decide)) (ne (by decide)),
        hR₁, Function.update_of_ne (ne (by decide)), Function.update_self]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
    by_cases x13 : x = r .sD
    · rw [x13, f₃ _ (ne (by decide)) (ne (by decide)), hR₂, Function.update_of_ne (ne (by decide)),
        Function.update_self]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
    by_cases x14 : x = r .mD
    · rw [x14, hR₃, Function.update_of_ne (ne (by decide)), Function.update_self]
      simp (disch := decide) only [crtSt, upd, Function.update_self]
    rw [f₃ _ x14 x2, f₂ _ x13 x4, f₁ _ x12 x6, hR]
    simp only [crtSt, Function.update_of_ne x1, Function.update_of_ne x3, Function.update_of_ne x5,
      Function.update_of_ne x7, Function.update_of_ne x8, Function.update_of_ne x11,
      Function.update_of_ne x12, Function.update_of_ne x13, Function.update_of_ne x14]
  · have l₄ : (R₃ (r .aI)).length = a I := by rw [v₃aI, List.length_replicate]
    have l₆ : (R₅ (r .wT)).length = crtPre a i + 2 * i := by
      rw [v₅wT, crtEnts_length, List.length_map, crtRevAx_length i hi.le, crtW_eq_sum,
        crtW_revAx a i hi.le]
    have l₈ : (R₇ (r .vacc)).length = crtPre a i := by
      rw [hR₇]; simp (disch := decide) only [upd, Function.update_self]
      rw [List.length_replicate]
    have l₉ : (R₈ (r .aI)).length = a I := by rw [v₈aI, List.length_replicate]
    rw [l₄, l₆, l₈, l₉, crtPre_succ a hi]
    unfold crtRotCost
    simp only [← hI]
    omega

/-! ### Contents keep record lengths and symbols -/

lemma crtRotC_mem {d : ℕ} (s : Fin d → ℕ) {α : Type*} (p : α → Prop) {i : ℕ} (hi : i < d)
    (μ : ℕ) (fwd : Bool) (C : (Fin d → ℕ) → α) (hC : ∀ y, p (C y)) (y : Fin d → ℕ) :
    p (crtRotC s i hi μ fwd C y) := by
  unfold crtRotC; split_ifs <;> exact hC _

lemma crtFwdC_mem {d : ℕ} (s μ : Fin d → ℕ) {α : Type*} (p : α → Prop) (C : (Fin d → ℕ) → α)
    (hC : ∀ y, p (C y)) : ∀ n y, p (crtFwdC s μ C n y)
  | 0, y => hC y
  | n + 1, y => by
      rw [crtFwdC]; split_ifs
      · exact crtRotC_mem s p _ _ _ _ (crtFwdC_mem s μ p C hC n) y
      · exact crtFwdC_mem s μ p C hC n y

lemma crtInvC_mem {d : ℕ} (s μ : Fin d → ℕ) {α : Type*} (p : α → Prop) (X : (Fin d → ℕ) → α)
    (hX : ∀ y, p (X y)) : ∀ n y, p (crtInvC s μ X n y)
  | 0, y => hX y
  | n + 1, y => by
      rw [crtInvC]; split_ifs
      · exact crtRotC_mem s p _ _ _ _ (crtInvC_mem s μ p X hX n) y
      · exact crtInvC_mem s μ p X hX n y

lemma crtFwdC_succ {d : ℕ} (s μ : Fin d → ℕ) {α : Type*} (C : (Fin d → ℕ) → α) {j : ℕ}
    (hj : j < d) : crtFwdC s μ C (j + 1) =
      crtRotC s (d - 1 - j) (by omega) (μ ⟨d - 1 - j, by omega⟩) true (crtFwdC s μ C j) := by
  rw [crtFwdC, dif_pos hj]

lemma crtInvC_succ {d : ℕ} (s μ : Fin d → ℕ) {α : Type*} (X : (Fin d → ℕ) → α) {j : ℕ}
    (hj : j < d) : crtInvC s μ X (j + 1) = crtRotC s j hj (μ ⟨j, hj⟩) false (crtInvC s μ X j) := by
  rw [crtInvC, dif_pos hj]

/-- The bound of one iteration, uniform over the targets. -/
def crtIterU (T L B d am amin : ℕ) : ℕ :=
  d * (crtStepBound T L B (2 ^ L * B) am + 2) + crtRotU L am amin B + 12 * L + 8 * 2 ^ am +
    4 * d + 50

lemma crtIter_le {d : ℕ} (a s μ : Fin d → ℕ) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hμ : ∀ j, μ j ≤ s j) {am amin : ℕ} (ham : ∀ j, a j ≤ am) (hamin : ∀ j, amin ≤ a j)
    (T B : ℕ) {i : ℕ} (hi : i < d) :
    i * (crtStepBound T (crtPre a d) B (2 ^ crtPre a d * B) am + 2) +
        crtRotCost (crtPre a i) (a ⟨i, hi⟩) (crtW a ((List.finRange d).drop (i + 1)))
          (s ⟨i, hi⟩) (μ ⟨i, hi⟩) B +
        12 * crtPre a (i + 1) + 4 * s ⟨i, hi⟩ + 4 * μ ⟨i, hi⟩ + 4 * i + 50 ≤
      crtIterU T (crtPre a d) B d am amin := by
  have hW : crtPre a i + a ⟨i, hi⟩ + crtW a ((List.finRange d).drop (i + 1)) = crtPre a d := by
    have := crtW_crtLay a i
    rw [crtLay_rot hi, crtW_append, crtW_revAx a i hi.le, crtW_cons] at this
    omega
  have hrot := crtRotCost_le (crtPre a i) (a ⟨i, hi⟩) (crtW a ((List.finRange d).drop (i + 1)))
    (s ⟨i, hi⟩) (μ ⟨i, hi⟩) B (crtPre a d) am amin hW (hs _).2.le (hμ _) (ham _) (hamin _)
  have hpre : crtPre a (i + 1) ≤ crtPre a d := crtPre_mono a (by omega)
  have hs2 : s ⟨i, hi⟩ ≤ 2 ^ am :=
    (hs _).2.le.trans (Nat.pow_le_pow_right (by norm_num) (ham _))
  have hμ2 := (hμ ⟨i, hi⟩).trans hs2
  have hid : i * (crtStepBound T (crtPre a d) B (2 ^ crtPre a d * B) am + 2) ≤
      d * (crtStepBound T (crtPre a d) B (2 ^ crtPre a d * B) am + 2) :=
    Nat.mul_le_mul_right _ hi.le
  unfold crtIterU
  omega

/-- The register file between forward iterations, `n` targets left. -/
def crtFwdSt {d : ℕ} (a s μ : Fin d → ℕ) (r : CrtReg → Fin T) (R₀ : Regs T (prime + K))
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (n : ℕ) : Regs T (prime + K) :=
  crtSt r R₀ (crtBox a (crtLay n) C 0).flatten (crtEnts ((crtRevAx n).map a))
    (crtEnts ((crtRevAx n).map s)) (crtEnts ((crtRevAx n).map μ))
    (crtEnts (((List.finRange d).drop n).map a)) (crtEnts (((List.finRange d).drop n).map s))
    (crtEnts (((List.finRange d).drop n).map μ)) (List.replicate (crtPre a n) tick)
    (List.replicate (crtW a ((List.finRange d).drop n)) tick)

/-- The forward iterations, `d - 1` down to `0`. -/
theorem crtFwdLoop_runs {d : ℕ} (a s μ : Fin d → ℕ) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hμ : ∀ j, μ j ≤ s j) (hadj : ∀ j j', a j ≤ a j' + 1) (am amin : ℕ) (ham : ∀ j, a j ≤ am)
    (hamin : ∀ j, amin ≤ a j)
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) {r : CrtReg → Fin T}
    (hr : Function.Injective r) (hrι : ∀ x j, r x ≠ ι j)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ x ∈ C y, x.val < 8)
    (R₀ : Regs T (prime + K))
    (hsig : R₀ (r .sig) = binSyms (crtPre a d) (crtSig a s d))
    (hmsk : R₀ (r .msk) = binSyms (crtPre a d) (crtMask a d)) (hzr : (R₀ (r .zr)).length = B)
    (he3 : R₀ (r .e3B) = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (h0 : ∀ x ∈ crtIdle, R₀ (r x) = []) (hι0 : ∀ i, R₀ (ι i) = []) :
    crtRuns body (crtWhile (r .wT) (crtFwdIter hQ ι hι hT r))
      (crtFwdSt a s μ r R₀ C d) (crtFwdSt a s μ r R₀ (crtFwdC s μ C d) 0)
      (d * (crtIterU T (crtPre a d) B d am amin + 2) + 2) := by
  let Ψ : ℕ → Regs T (prime + K) := fun j => crtFwdSt a s μ r R₀ (crtFwdC s μ C j) (d - j)
  have hstep : ∀ j < d, (Ψ j) (r .wT) ≠ [] ∧
      crtRuns body (crtFwdIter hQ ι hι hT r) (Ψ j) (Ψ (j + 1))
        (crtIterU T (crtPre a d) B d am amin) := by
    intro j hj
    set i := d - 1 - j with hi'
    have hi : i < d := by omega
    have hn : d - j = i + 1 := by omega
    have hn' : d - (j + 1) = i := by omega
    refine ⟨?_, ?_⟩
    · simp only [Ψ, crtFwdSt, crtSt]
      rw [Function.update_of_ne (hr.ne (by decide)), Function.update_of_ne (hr.ne (by decide)),
        Function.update_of_ne (hr.ne (by decide)), Function.update_of_ne (hr.ne (by decide)),
        Function.update_of_ne (hr.ne (by decide)), Function.update_of_ne (hr.ne (by decide)),
        Function.update_of_ne (hr.ne (by decide)), Function.update_self, hn,
        crtRevAx_succ hi, List.map_cons]
      exact crtEnts_ne_nil (List.cons_ne_nil _ _)
    · have hCj := crtFwdC_mem s μ (fun c => c.length = B) C hC j
      have h8j := crtFwdC_mem s μ (fun c => ∀ x ∈ c, x.val < 8) C h8 j
      have h := crtFwdIter_runs (body := body) a s μ hs hμ hadj am ham hQ ι hι hT hr hrι hi
        (crtFwdC s μ C j) B hB hCj h8j R₀ hsig hmsk hzr he3 h0 hι0
        (crtEnts (((List.finRange d).drop (i + 1)).map a))
        (crtEnts (((List.finRange d).drop (i + 1)).map s))
        (crtEnts (((List.finRange d).drop (i + 1)).map μ))
      refine crtRuns_mono (crtRuns_congr_left (crtRuns_congr h ?_) ?_)
        (crtIter_le a s μ hs hμ ham hamin T B hi)
      · simp only [Ψ, crtFwdSt, hn', crtFwdC_succ s μ C hj, ← hi', crt_drop_finRange hi,
          List.map_cons, crtEnts_cons]
        rfl
      · simp only [Ψ, crtFwdSt, hn]
  have h := crtWhile_runs (body := body) (p := crtFwdIter hQ ι hι hT r) (Ψ := Ψ) (N := d) hstep
    (by simp only [Ψ, crtFwdSt, crtSt, Nat.sub_self]
        rw [Function.update_of_ne (hr.ne (by decide)), Function.update_of_ne (hr.ne (by decide)),
          Function.update_of_ne (hr.ne (by decide)), Function.update_of_ne (hr.ne (by decide)),
          Function.update_of_ne (hr.ne (by decide)), Function.update_of_ne (hr.ne (by decide)),
          Function.update_of_ne (hr.ne (by decide)), Function.update_self]
        rfl)
  simp only [Ψ, Nat.sub_zero, Nat.sub_self] at h
  exact h

/-- The inverse iterations, `0` up to `d - 1`. -/
theorem crtInvLoop_runs {d : ℕ} (a s μ : Fin d → ℕ) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hμ : ∀ j, μ j ≤ s j) (hadj : ∀ j j', a j ≤ a j' + 1) (am amin : ℕ) (ham : ∀ j, a j ≤ am)
    (hamin : ∀ j, amin ≤ a j)
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) {r : CrtReg → Fin T}
    (hr : Function.Injective r) (hrι : ∀ x j, r x ≠ ι j)
    (X : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hX : ∀ y, (X y).length = B) (h8 : ∀ y, ∀ x ∈ X y, x.val < 8)
    (R₀ : Regs T (prime + K))
    (hsig : R₀ (r .sig) = binSyms (crtPre a d) (crtSig a s d))
    (hmsk : R₀ (r .msk) = binSyms (crtPre a d) (crtMask a d)) (hzr : (R₀ (r .zr)).length = B)
    (he3 : R₀ (r .e3B) = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (h0 : ∀ x ∈ crtIdle, R₀ (r x) = []) (hι0 : ∀ i, R₀ (ι i) = []) :
    crtRuns body (crtWhile (r .wD) (crtInvIter hQ ι hι hT r))
      (crtFwdSt a s μ r R₀ X 0) (crtFwdSt a s μ r R₀ (crtInvC s μ X d) d)
      (d * (crtIterU T (crtPre a d) B d am amin + 2) + 2) := by
  let Ψ : ℕ → Regs T (prime + K) := fun j => crtFwdSt a s μ r R₀ (crtInvC s μ X j) j
  have hstep : ∀ j < d, (Ψ j) (r .wD) ≠ [] ∧
      crtRuns body (crtInvIter hQ ι hι hT r) (Ψ j) (Ψ (j + 1))
        (crtIterU T (crtPre a d) B d am amin) := by
    intro j hj
    refine ⟨?_, ?_⟩
    · simp only [Ψ, crtFwdSt, crtSt]
      rw [Function.update_of_ne (hr.ne (by decide)), Function.update_of_ne (hr.ne (by decide)),
        Function.update_of_ne (hr.ne (by decide)), Function.update_of_ne (hr.ne (by decide)),
        Function.update_self, crt_drop_finRange hj, List.map_cons]
      exact crtEnts_ne_nil (List.cons_ne_nil _ _)
    · have hXj := crtInvC_mem s μ (fun c => c.length = B) X hX j
      have h8j := crtInvC_mem s μ (fun c => ∀ x ∈ c, x.val < 8) X h8 j
      have h := crtInvIter_runs (body := body) a s μ hs hμ hadj am ham hQ ι hι hT hr hrι hj
        (crtInvC s μ X j) B hB hXj h8j R₀ hsig hmsk hzr he3 h0 hι0
        (crtEnts ((crtRevAx j).map s)) (crtEnts ((crtRevAx j).map μ))
      refine crtRuns_mono (crtRuns_congr_left (crtRuns_congr h ?_) ?_)
        (crtIter_le a s μ hs hμ ham hamin T B hj)
      · simp only [Ψ, crtFwdSt, crtInvC_succ s μ X hj, crtRevAx_succ hj, List.map_cons,
          crtEnts_cons]
      · simp only [Ψ, crtFwdSt]
  have h := crtWhile_runs (body := body) (p := crtInvIter hQ ι hι hT r) (Ψ := Ψ) (N := d) hstep
    (by simp only [Ψ, crtFwdSt, crtSt]
        rw [Function.update_of_ne (hr.ne (by decide)), Function.update_of_ne (hr.ne (by decide)),
          Function.update_of_ne (hr.ne (by decide)), Function.update_of_ne (hr.ne (by decide)),
          Function.update_self, List.drop_eq_nil_of_le (by simp)]
        rfl)
  exact h

/-! ### The machines -/

/-- The registers that are empty at rest. -/
def crtRestEmpty : List CrtReg :=
  crtIdle ++ ([.wD, .sD, .mD, .preU, .postU, .e3B, .t3B, .bU] ++
    (List.finRange 32).map CrtReg.extra)

/-- The forward map: the counter of `3 B`, `preU := L`, the padding scan, one iteration per
target `d - 1, …, 0`, and the restoration of the axis lists. -/
def crtForward (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) (r : CrtReg → Fin T) :
    Pr F T Q (prime + K) U :=
  .seq (umul 3 (r .zr) (r .t3B) (r .u1)) <| .seq (crtEncP (r .t3B) (r .tu) (r .e3B) (r .u1)) <|
  .seq (uclear (r .t3B)) <| .seq (ucopy (r .msk) (r .preU) (r .u1)) <|
  .seq (crtPadP (crtLp r) (r .str) (r .acc) (r .zr) (r .bU) (r .tA) (r .tB) (r .u1)) <|
  .seq (crtWhile (r .wT) (crtFwdIter hQ ι hι hT r)) <|
  .seq (crtMv (r .wD) (r .wT)) <| .seq (crtMv (r .sD) (r .sT)) <| .seq (crtMv (r .mD) (r .mT)) <|
  .seq (uclear (r .postU)) (uclear (r .e3B))

/-- The inverse map: the counter of `3 B`, `postU := L`, reversal of the axis lists, one
iteration per target `0, …, d - 1`, and the deletion scan. -/
def crtInverse (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) (r : CrtReg → Fin T) :
    Pr F T Q (prime + K) U :=
  .seq (umul 3 (r .zr) (r .t3B) (r .u1)) <| .seq (crtEncP (r .t3B) (r .tu) (r .e3B) (r .u1)) <|
  .seq (uclear (r .t3B)) <| .seq (ucopy (r .msk) (r .postU) (r .u1)) <|
  .seq (crtMv (r .wT) (r .wD)) <| .seq (crtMv (r .sT) (r .sD)) <| .seq (crtMv (r .mT) (r .mD)) <|
  .seq (crtWhile (r .wD) (crtInvIter hQ ι hι hT r)) <|
  .seq (uclear (r .preU)) <| .seq (uclear (r .e3B)) <|
  crtDelP (crtLp r) (r .str) (r .acc) (r .zr) (r .bU) (r .tA)

/-- The cost bound of either machine: the scan, `d` iterations, the counter of `3 B` and the
list moves. -/
def crtCost (T L B d am amin : ℕ) : ℕ :=
  2 ^ L * (10 * B + 10 * L + 29) + d * (crtIterU T L B d am amin + 2) + 36 * B ^ 2 + 60 * B +
    40 * L + 12 * d + 4 * (d * 2 ^ am) + 60

lemma crtEnts_map_length_le {d : ℕ} (g : Fin d → ℕ) (c : ℕ) (hg : ∀ j, g j ≤ c)
    (o : List (Fin d)) : (crtEnts (A := prime + K) (o.map g)).length ≤ o.length * c + 2 * o.length := by
  rw [crtEnts_length, List.length_map]
  have : (o.map g).sum ≤ (o.map g).length • c :=
    List.sum_le_card_nsmul _ _ fun x hx => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx; exact hg j
  rw [List.length_map, smul_eq_mul] at this
  omega

lemma crtSt_eq_self {r : CrtReg → Fin T} (hr : Function.Injective r) (R₀ : Regs T (prime + K))
    (v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ : List (Fin (prime + K + 4)))
    (h₁ : R₀ (r .str) = v₁) (h₂ : R₀ (r .wT) = v₂) (h₃ : R₀ (r .sT) = v₃) (h₄ : R₀ (r .mT) = v₄)
    (h₅ : R₀ (r .wD) = v₅) (h₆ : R₀ (r .sD) = v₆) (h₇ : R₀ (r .mD) = v₇) (h₈ : R₀ (r .preU) = v₈)
    (h₉ : R₀ (r .postU) = v₉) :
    crtSt r R₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ = R₀ := by
  have ne : ∀ {x y : CrtReg}, x ≠ y → r x ≠ r y := fun h => hr.ne h
  have upd : ∀ {α : Type} (f : Fin T → α) (y : CrtReg) (v : α) (x : CrtReg), x ≠ y →
      Function.update f (r y) v (r x) = f (r x) := fun f y v x h => Function.update_of_ne (ne h) _ _
  funext x
  by_cases x1 : x = r .str
  · rw [x1, h₁]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  by_cases x2 : x = r .wT
  · rw [x2, h₂]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  by_cases x3 : x = r .sT
  · rw [x3, h₃]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  by_cases x4 : x = r .mT
  · rw [x4, h₄]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  by_cases x5 : x = r .wD
  · rw [x5, h₅]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  by_cases x6 : x = r .sD
  · rw [x6, h₆]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  by_cases x7 : x = r .mD
  · rw [x7, h₇]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  by_cases x8 : x = r .preU
  · rw [x8, h₈]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  by_cases x9 : x = r .postU
  · rw [x9, h₉]; simp (disch := decide) only [crtSt, upd, Function.update_self]
  rw [crtSt_of_ne]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9⟩

lemma crtRevAx_full {d : ℕ} : crtRevAx (d := d) d = (List.finRange d).reverse := by
  rw [crtRevAx, List.take_of_length_le (by simp)]

set_option maxHeartbeats 4000000 in
/-- **The forward CRT layout.** From the coefficient records `l` (`∏ s` records of `B`
symbols) on `str`, the axis lists in the forward format (axis `d - 1` on top) and the packed
bounds and masks, `crtForward` leaves on `str` the box of `crtSpecC s hcop l z` along
`List.finRange d` (axis `0` most significant): the record `l[(crtPhi s hcop).symm x]` at every
valid address `x`, the zero record `z` elsewhere. Every other register ends as it started. -/
theorem crtForward_runs {d : ℕ} (a s : Fin d → ℕ) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hcop : Pairwise (Nat.Coprime on s)) (hadj : ∀ j j', a j ≤ a j' + 1) (am amin : ℕ)
    (ham : ∀ j, a j ≤ am) (hamin : ∀ j, amin ≤ a j)
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) {r : CrtReg → Fin T}
    (hr : Function.Injective r) (hrι : ∀ x j, r x ≠ ι j)
    (l : List (List (Fin (prime + K + 4)))) (z : List (Fin (prime + K + 4))) (B : ℕ)
    (hB : 0 < B) (hl : l.length = ∏ j, s j) (hlB : ∀ x ∈ l, x.length = B) (hz : z.length = B)
    (hl8 : ∀ x ∈ l, ∀ c ∈ x, c.val < 8) (hz8 : ∀ c ∈ z, c.val < 8)
    (R : Regs T (prime + K)) (hstr : R (r .str) = l.flatten)
    (hwT : R (r .wT) = crtEnts ((crtRevAx d).map a))
    (hsT : R (r .sT) = crtEnts ((crtRevAx d).map s))
    (hmT : R (r .mT) = crtEnts ((crtRevAx d).map fun j => (crtMu s hcop j : ZMod (s j)).val))
    (hsig : R (r .sig) = binSyms (crtPre a d) (crtSig a s d))
    (hmsk : R (r .msk) = binSyms (crtPre a d) (crtMask a d)) (hzr : R (r .zr) = z)
    (h0 : ∀ x ∈ crtRestEmpty, R (r x) = []) (hι0 : ∀ i, R (ι i) = []) :
    crtRuns body (crtForward hQ ι hι hT r) R
      (Function.update R (r .str) (crtBox a (List.finRange d) (crtSpecC s hcop l z) 0).flatten)
      (crtCost T (crtPre a d) B d am amin) := by
  have ne : ∀ {x y : CrtReg}, x ≠ y → r x ≠ r y := fun h => hr.ne h
  have upd : ∀ {α : Type} (f : Fin T → α) (y : CrtReg) (v : α) (x : CrtReg), x ≠ y →
      Function.update f (r y) v (r x) = f (r x) := fun f y v x h => Function.update_of_ne (ne h) _ _
  have z0 : ∀ x ∈ crtRestEmpty, R (r x) = [] := h0
  set μ : Fin d → ℕ := fun j => (crtMu s hcop j : ZMod (s j)).val with hμdef
  have hμ : ∀ j, μ j ≤ s j := fun j => by
    have : NeZero (s j) := ⟨(hs j).1.ne'⟩
    exact (ZMod.val_lt _).le
  have hzlen : (R (r .zr)).length = B := by rw [hzr, hz]
  have hmsklen : (R (r .msk)).length = crtPre a d := by rw [hmsk, length_binSyms]
  -- the counter of `3 B`
  have s₁ := crtUmul_runs (body := body) 3 (a := r .zr) (b := r .t3B) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R (z0 .u1 (by decide))
  set R₁ := Function.update R (r .t3B) (List.replicate (3 * (R (r .zr)).length) tick ++
    R (r .t3B)) with hR₁
  clear_value R₁
  have f₁ : ∀ x, x ≠ r .t3B → R₁ x = R x := fun x h => by rw [hR₁, Function.update_of_ne h]
  have v₁ : R₁ (r .t3B) = List.replicate (3 * B) tick := by
    rw [hR₁, Function.update_self, hzlen, z0 .t3B (by decide), List.append_nil]
  have s₂ := crtEncP_runs (body := body) (u := r .t3B) (tu := r .tu) (e := r .e3B) (t := r .u1)
    (crt_nd hr [.t3B, .tu, .e3B, .u1] (by decide)) R₁
    (by rw [f₁ _ (ne (by decide))]; exact z0 .tu (by decide))
    (by rw [f₁ _ (ne (by decide))]; exact z0 .e3B (by decide))
    (by rw [f₁ _ (ne (by decide))]; exact z0 .u1 (by decide))
  rw [v₁, List.length_replicate] at s₂
  set R₂ := Function.update R₁ (r .e3B)
    ((GrowingCounterData.advance (3 * B) []).map bitSymbol) with hR₂
  clear_value R₂
  have f₂ : ∀ x, x ≠ r .e3B → R₂ x = R₁ x := fun x h => by rw [hR₂, Function.update_of_ne h]
  have s₃ := crtClear_runs (body := body) (r .t3B) R₂
  set R₃ := Function.update R₂ (r .t3B) [] with hR₃
  clear_value R₃
  have f₃ : ∀ x, x ≠ r .t3B → R₃ x = R₂ x := fun x h => by rw [hR₃, Function.update_of_ne h]
  have g₃ : ∀ x : CrtReg, x ≠ .t3B → x ≠ .e3B → R₃ (r x) = R (r x) := fun x h1 h2 => by
    rw [f₃ _ (ne h1), f₂ _ (ne h2), f₁ _ (ne h1)]
  have s₄ := crtUcopy_runs (body := body) (a := r .msk) (b := r .preU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₃
    (by rw [g₃ .u1 (by decide) (by decide)]; exact z0 .u1 (by decide))
  set R₄ := Function.update R₃ (r .preU) (List.replicate (R₃ (r .msk)).length tick ++
    R₃ (r .preU)) with hR₄
  clear_value R₄
  have f₄ : ∀ x, x ≠ r .preU → R₄ x = R₃ x := fun x h => by rw [hR₄, Function.update_of_ne h]
  have g₄ : ∀ x : CrtReg, x ≠ .t3B → x ≠ .e3B → x ≠ .preU → R₄ (r x) = R (r x) :=
    fun x h1 h2 h3 => by rw [f₄ _ (ne h3), g₃ x h1 h2]
  have v₄pre : R₄ (r .preU) = List.replicate (crtPre a d) tick := by
    rw [hR₄, Function.update_self, g₃ .msk (by decide) (by decide), hmsklen,
      g₃ .preU (by decide) (by decide), z0 .preU (by decide), List.append_nil]
  -- the padding scan
  have hlS : l.length = crtProd s d := by rw [hl, crtProd, crtLow_of_le le_rfl]
  have s₅ := crtPad_runs (body := body) a s (crtLp r) (crtLp_ok hr) (str := r .str)
    (acc := r .acc) (zr := r .zr) (bU := r .bU) (tA := r .tA) (tB := r .tB) (u := r .u1)
    (crt_nd hr [.str, .acc, .zr, .bU, .tA, .tB, .u1] (by decide))
    (by intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact crtLp_prot hr _ rfl (by decide))
    hs l z B hlS hlB hz R₄
    (by rw [g₄ .str (by decide) (by decide) (by decide), hstr])
    (by rw [g₄ .zr (by decide) (by decide) (by decide), hzr])
    (by rw [g₄ .acc (by decide) (by decide) (by decide)]; exact z0 .acc (by decide))
    (by rw [g₄ .bU (by decide) (by decide) (by decide)]; exact z0 .bU (by decide))
    (by rw [g₄ .tA (by decide) (by decide) (by decide)]; exact z0 .tA (by decide))
    (by rw [g₄ .tB (by decide) (by decide) (by decide)]; exact z0 .tB (by decide))
    (by rw [g₄ .u1 (by decide) (by decide) (by decide)]; exact z0 .u1 (by decide))
    (by show R₄ (r .nF) = []; rw [g₄ .nF (by decide) (by decide) (by decide)]
        exact z0 .nF (by decide))
    (by show R₄ (r .tN) = []; rw [g₄ .tN (by decide) (by decide) (by decide)]
        exact z0 .tN (by decide))
    (by show R₄ (r .fc) = []; rw [g₄ .fc (by decide) (by decide) (by decide)]
        exact z0 .fc (by decide))
    (by show R₄ (r .sig) = _; rw [g₄ .sig (by decide) (by decide) (by decide), hsig])
    (by show R₄ (r .msk) = _; rw [g₄ .msk (by decide) (by decide) (by decide), hmsk])
    (by show R₄ (r .c0) = []; rw [g₄ .c0 (by decide) (by decide) (by decide)]
        exact z0 .c0 (by decide))
    (by show R₄ (r .c1) = []; rw [g₄ .c1 (by decide) (by decide) (by decide)]
        exact z0 .c1 (by decide))
    (by show R₄ (r .c2) = []; rw [g₄ .c2 (by decide) (by decide) (by decide)]
        exact z0 .c2 (by decide))
    (by show R₄ (r .it) = []; rw [g₄ .it (by decide) (by decide) (by decide)]
        exact z0 .it (by decide))
  set C₀ := crtPadC s l z with hC₀
  set R₅ := Function.update R₄ (r .str) (crtBox a (crtRevAx d) C₀ 0).flatten with hR₅
  clear_value R₅
  have f₅ : ∀ x, x ≠ r .str → R₅ x = R₄ x := fun x h => by rw [hR₅, Function.update_of_ne h]
  have g₅ : ∀ x : CrtReg, x ≠ .t3B → x ≠ .e3B → x ≠ .preU → x ≠ .str → R₅ (r x) = R (r x) :=
    fun x h1 h2 h3 h4 => by rw [f₅ _ (ne h4), g₄ x h1 h2 h3]
  -- the iterations
  have hCl : ∀ y, (C₀ y).length = B := fun y => by
    rw [hC₀]; unfold crtPadC; split_ifs
    · rw [List.getD_eq_getElem?_getD]
      rcases h : l[∑ j, y j * prefixProd s j]? with _ | x
      · simpa using hz
      · simp only [Option.getD_some]; exact hlB x (List.mem_of_getElem? h)
    · exact hz
  have h8₀ : ∀ y, ∀ c ∈ C₀ y, c.val < 8 := fun y c hc => by
    rw [hC₀] at hc; unfold crtPadC at hc; split_ifs at hc
    · rw [List.getD_eq_getElem?_getD] at hc
      rcases h : l[∑ j, y j * prefixProd s j]? with _ | x
      · rw [h] at hc; exact hz8 c hc
      · rw [h] at hc; exact hl8 x (List.mem_of_getElem? h) c hc
    · exact hz8 c hc
  have hidle : ∀ x ∈ crtIdle, x ≠ .t3B ∧ x ≠ .e3B ∧ x ≠ .preU ∧ x ≠ .str := by decide
  have e₅ : crtFwdSt a s μ r R₅ C₀ d = R₅ := by
    apply crtSt_eq_self hr
    · rw [hR₅, Function.update_self, crtLay_top]
    · rw [g₅ .wT (by decide) (by decide) (by decide) (by decide), hwT]
    · rw [g₅ .sT (by decide) (by decide) (by decide) (by decide), hsT]
    · rw [g₅ .mT (by decide) (by decide) (by decide) (by decide), hmT]
    · rw [g₅ .wD (by decide) (by decide) (by decide) (by decide), z0 .wD (by decide),
        List.drop_eq_nil_of_le (by simp)]; rfl
    · rw [g₅ .sD (by decide) (by decide) (by decide) (by decide), z0 .sD (by decide),
        List.drop_eq_nil_of_le (by simp)]; rfl
    · rw [g₅ .mD (by decide) (by decide) (by decide) (by decide), z0 .mD (by decide),
        List.drop_eq_nil_of_le (by simp)]; rfl
    · rw [f₅ _ (ne (by decide)), v₄pre]
    · rw [g₅ .postU (by decide) (by decide) (by decide) (by decide), z0 .postU (by decide),
        List.drop_eq_nil_of_le (by simp)]; rfl
  have s₆ := crtFwdLoop_runs (body := body) a s μ hs hμ hadj am amin ham hamin hQ ι hι hT hr hrι
    C₀ B hB hCl h8₀ R₅
    (by rw [g₅ .sig (by decide) (by decide) (by decide) (by decide), hsig])
    (by rw [g₅ .msk (by decide) (by decide) (by decide) (by decide), hmsk])
    (by rw [g₅ .zr (by decide) (by decide) (by decide) (by decide), hzlen])
    (by rw [f₅ _ (ne (by decide)), f₄ _ (ne (by decide)), f₃ _ (ne (by decide)), hR₂,
          Function.update_self])
    (fun x hx => by
      obtain ⟨h1, h2, h3, h4⟩ := hidle x hx
      rw [g₅ x h1 h2 h3 h4]; exact z0 x (List.mem_append_left _ hx))
    (fun j => by
      rw [f₅ _ (hrι _ _).symm, f₄ _ (hrι _ _).symm, f₃ _ (hrι _ _).symm, f₂ _ (hrι _ _).symm,
        f₁ _ (hrι _ _).symm]; exact hι0 j)
  rw [e₅] at s₆
  set R₆ := crtFwdSt a s μ r R₅ (crtFwdC s μ C₀ d) 0 with hR₆
  clear_value R₆
  have v₆ : ∀ x : CrtReg, x ≠ .str → x ≠ .wT → x ≠ .sT → x ≠ .mT → x ≠ .wD → x ≠ .sD →
      x ≠ .mD → x ≠ .preU → x ≠ .postU → R₆ (r x) = R₅ (r x) := by
    intro x h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [hR₆, crtFwdSt, crtSt_of_ne]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨ne h1, ne h2, ne h3, ne h4, ne h5, ne h6, ne h7, ne h8, ne h9⟩
  have w₆ : ∀ g : Fin d → ℕ, crtEnts (((List.finRange d).drop 0).map g) =
      crtEnts (A := prime + K) ((List.finRange d).map g) := fun g => by rw [List.drop_zero]
  -- restore the lists, clear
  have s₇ := crtMv_runs (body := body) (ne (by decide : CrtReg.wD ≠ .wT)) R₆
  set R₇ := Function.update (Function.update R₆ (r .wD) []) (r .wT)
    ((R₆ (r .wD)).reverse ++ R₆ (r .wT)) with hR₇
  clear_value R₇
  have s₈ := crtMv_runs (body := body) (ne (by decide : CrtReg.sD ≠ .sT)) R₇
  set R₈ := Function.update (Function.update R₇ (r .sD) []) (r .sT)
    ((R₇ (r .sD)).reverse ++ R₇ (r .sT)) with hR₈
  clear_value R₈
  have s₉ := crtMv_runs (body := body) (ne (by decide : CrtReg.mD ≠ .mT)) R₈
  set R₉ := Function.update (Function.update R₈ (r .mD) []) (r .mT)
    ((R₈ (r .mD)).reverse ++ R₈ (r .mT)) with hR₉
  clear_value R₉
  have s₁₀ := crtClear_runs (body := body) (r .postU) R₉
  have s₁₁ := crtClear_runs (body := body) (r .e3B) (Function.update R₉ (r .postU) [])
  have g₇ : ∀ x : CrtReg, x ≠ .wD → x ≠ .wT → R₇ (r x) = R₆ (r x) := fun x h1 h2 => by
    rw [hR₇, Function.update_of_ne (ne h2), Function.update_of_ne (ne h1)]
  have g₈ : ∀ x : CrtReg, x ≠ .wD → x ≠ .wT → x ≠ .sD → x ≠ .sT → R₈ (r x) = R₆ (r x) :=
    fun x h1 h2 h3 h4 => by
    rw [hR₈, Function.update_of_ne (ne h4), Function.update_of_ne (ne h3), g₇ x h1 h2]
  have g₉ : ∀ x : CrtReg, x ≠ .wD → x ≠ .wT → x ≠ .sD → x ≠ .sT → x ≠ .mD → x ≠ .mT →
      R₉ (r x) = R₆ (r x) := fun x h1 h2 h3 h4 h5 h6 => by
    rw [hR₉, Function.update_of_ne (ne h6), Function.update_of_ne (ne h5), hR₈,
      Function.update_of_ne (ne h4), Function.update_of_ne (ne h3), hR₇,
      Function.update_of_ne (ne h2), Function.update_of_ne (ne h1)]
  have v6 : ∀ (x : CrtReg) (v : List (Fin (prime + K + 4))), R₆ (r x) = v → R₆ (r x) = v :=
    fun _ _ h => h
  have r6str : R₆ (r .str) = (crtBox a (crtLay 0) (crtFwdC s μ C₀ d) 0).flatten := by
    rw [hR₆]; simp (disch := decide) only [crtFwdSt, crtSt, upd, Function.update_self]
  have r6 : ∀ (x : CrtReg) (g : Fin d → ℕ),
      (x = .wT ∧ g = a) ∨ (x = .sT ∧ g = s) ∨ (x = .mT ∧ g = μ) → R₆ (r x) = [] := by
    rintro x g (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      (rw [hR₆]; simp (disch := decide) only [crtFwdSt, crtSt, upd, Function.update_self]; rfl)
  have r6D : ∀ (x : CrtReg) (g : Fin d → ℕ),
      (x = .wD ∧ g = a) ∨ (x = .sD ∧ g = s) ∨ (x = .mD ∧ g = μ) →
      R₆ (r x) = crtEnts ((List.finRange d).map g) := by
    rintro x g (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      (rw [hR₆]; simp (disch := decide) only [crtFwdSt, crtSt, upd, Function.update_self]
       rw [w₆])
  have r6pre : R₆ (r .preU) = [] := by
    rw [hR₆]; simp (disch := decide) only [crtFwdSt, crtSt, upd, Function.update_self,
      crtPre_zero, List.replicate_zero]
  have r6post : R₆ (r .postU) = List.replicate (crtPre a d) tick := by
    rw [hR₆]; simp (disch := decide) only [crtFwdSt, crtSt, upd, Function.update_self]
    rw [List.drop_zero, crtW_finRange]
  have hrev : ∀ g : Fin d → ℕ, (crtEnts (A := prime + K) ((List.finRange d).map g)).reverse =
      crtEnts ((crtRevAx d).map g) := fun g => by
    rw [crtEnts_reverse, ← List.map_reverse, crtRevAx_full]
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ (crtRuns_seq s₃
    (crtRuns_seq s₄ (crtRuns_seq s₅ (crtRuns_seq s₆ (crtRuns_seq s₇ (crtRuns_seq s₈
      (crtRuns_seq s₉ (crtRuns_seq s₁₀ s₁₁)))))))))) ?_) ?_
  all_goals clear s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁
  · funext x
    by_cases x1 : x = r .e3B
    · subst x1; simp (disch := decide) only [upd, Function.update_self]
      rw [z0 .e3B (by decide)]
    rw [Function.update_of_ne x1]
    by_cases x2 : x = r .postU
    · subst x2; simp (disch := decide) only [upd, Function.update_self]
      rw [z0 .postU (by decide)]
    rw [Function.update_of_ne x2]
    by_cases x3 : x = r .mT
    · subst x3; rw [hR₉]; simp (disch := decide) only [upd, Function.update_self]
      rw [g₈ .mD (by decide) (by decide) (by decide) (by decide),
        g₈ .mT (by decide) (by decide) (by decide) (by decide),
        r6D .mD μ (Or.inr (Or.inr ⟨rfl, rfl⟩)), r6 .mT μ (Or.inr (Or.inr ⟨rfl, rfl⟩)), hrev,
        List.append_nil, hmT]
    by_cases x4 : x = r .mD
    · subst x4; rw [hR₉]; simp (disch := decide) only [upd, Function.update_self]
      rw [z0 .mD (by decide)]
    by_cases x5 : x = r .sT
    · subst x5; rw [hR₉]; simp (disch := decide) only [upd, Function.update_self]
      rw [hR₈]; simp (disch := decide) only [upd, Function.update_self]
      rw [g₇ .sD (by decide) (by decide), g₇ .sT (by decide) (by decide),
        r6D .sD s (Or.inr (Or.inl ⟨rfl, rfl⟩)), r6 .sT s (Or.inr (Or.inl ⟨rfl, rfl⟩)), hrev,
        List.append_nil, hsT]
    by_cases x6 : x = r .sD
    · subst x6; rw [hR₉]; simp (disch := decide) only [upd, Function.update_self]
      rw [hR₈]; simp (disch := decide) only [upd, Function.update_self]
      rw [z0 .sD (by decide)]
    by_cases x7 : x = r .wT
    · subst x7; rw [hR₉]; simp (disch := decide) only [upd, Function.update_self]
      rw [hR₈]; simp (disch := decide) only [upd, Function.update_self]
      rw [hR₇]; simp (disch := decide) only [upd, Function.update_self]
      rw [r6D .wD a (Or.inl ⟨rfl, rfl⟩), r6 .wT a (Or.inl ⟨rfl, rfl⟩), hrev,
        List.append_nil, hwT]
    by_cases x8 : x = r .wD
    · subst x8; rw [hR₉]; simp (disch := decide) only [upd, Function.update_self]
      rw [hR₈]; simp (disch := decide) only [upd, Function.update_self]
      rw [hR₇]; simp (disch := decide) only [upd, Function.update_self]
      rw [z0 .wD (by decide)]
    by_cases x9 : x = r .str
    · rw [x9, g₉ .str (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        r6str, Function.update_self, crtLay_zero, crtFwdC_spec s (fun j => (hs j).1) hcop l z]
    by_cases x10 : x = r .preU
    · subst x10
      rw [g₉ .preU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), r6pre]
      simp (disch := decide) only [upd]
      rw [z0 .preU (by decide)]
    rw [Function.update_of_ne x9, hR₉, Function.update_of_ne x3, Function.update_of_ne x4, hR₈,
      Function.update_of_ne x5, Function.update_of_ne x6, hR₇, Function.update_of_ne x7,
      Function.update_of_ne x8, hR₆, crtFwdSt, crtSt_of_ne]
    · rw [hR₅, Function.update_of_ne x9, hR₄, Function.update_of_ne x10]
      by_cases x11 : x = r .t3B
      · rw [x11, hR₃, Function.update_self, z0 .t3B (by decide)]
      rw [hR₃, Function.update_of_ne x11, hR₂, Function.update_of_ne x1, hR₁,
        Function.update_of_ne x11]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨x9, x7, x5, x3, x8, x6, x4, x10, x2⟩
  · have l₀ : (R (r .zr)).length = B := hzlen
    have l₂ : (R₂ (r .t3B)).length = 3 * B := by
      rw [f₂ _ (ne (by decide)), v₁, List.length_replicate]
    have l₃ : (R₃ (r .msk)).length = crtPre a d := by
      rw [g₃ .msk (by decide) (by decide), hmsklen]
    have l₇ : (R₆ (r .wD)).length = crtPre a d + 2 * d := by
      rw [r6D .wD a (Or.inl ⟨rfl, rfl⟩), crtEnts_length, List.length_map, List.length_finRange,
        crtW_eq_sum, crtW_finRange]
    have l₈ : (R₇ (r .sD)).length ≤ d * 2 ^ am + 2 * d := by
      rw [g₇ .sD (by decide) (by decide), r6D .sD s (Or.inr (Or.inl ⟨rfl, rfl⟩))]
      have := crtEnts_map_length_le (K := K) s (2 ^ am)
        (fun j => (hs j).2.le.trans (Nat.pow_le_pow_right (by norm_num) (ham j))) (List.finRange d)
      rwa [List.length_finRange] at this
    have l₉ : (R₈ (r .mD)).length ≤ d * 2 ^ am + 2 * d := by
      rw [g₈ .mD (by decide) (by decide) (by decide) (by decide),
        r6D .mD μ (Or.inr (Or.inr ⟨rfl, rfl⟩))]
      have := crtEnts_map_length_le (K := K) μ (2 ^ am)
        (fun j => (hμ j).trans ((hs j).2.le.trans (Nat.pow_le_pow_right (by norm_num) (ham j))))
        (List.finRange d)
      rwa [List.length_finRange] at this
    have l₁₀ : (R₉ (r .postU)).length = crtPre a d := by
      rw [g₉ .postU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        r6post, List.length_replicate]
    have l₁₁ : ((Function.update R₉ (r .postU) []) (r .e3B)).length ≤ 3 * B := by
      rw [Function.update_of_ne (ne (by decide)), g₉ .e3B (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), v₆ .e3B (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), f₅ _ (ne (by decide)),
        f₄ _ (ne (by decide)), f₃ _ (ne (by decide)), hR₂, Function.update_self,
        List.length_map]
      exact crt_advance_length _
    rw [l₀, l₂, l₃, l₇, crtCost]
    have hB2 : 3 * B * (4 * (3 * B) + 9) = 36 * B ^ 2 + 27 * B := by ring
    rw [hB2]
    omega

set_option maxHeartbeats 4000000 in
/-- **The inverse CRT layout.** From the box of `X` along `List.finRange d` (axis `0` most
significant, records of `B` symbols) on `str`, the axis lists in the forward format and the
packed bounds and masks, `crtInverse` leaves on `str` the coefficient stream whose record `k`
(`k < ∏ s`) is `X` at the address `crtPhi s hcop k`. Every other register ends as it
started. -/
theorem crtInverse_runs {d : ℕ} (a s : Fin d → ℕ) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hcop : Pairwise (Nat.Coprime on s)) (hadj : ∀ j j', a j ≤ a j' + 1) (am amin : ℕ)
    (ham : ∀ j, a j ≤ am) (hamin : ∀ j, amin ≤ a j)
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) {r : CrtReg → Fin T}
    (hr : Function.Injective r) (hrι : ∀ x j, r x ≠ ι j)
    (X : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hX : ∀ y, (X y).length = B) (h8 : ∀ y, ∀ c ∈ X y, c.val < 8)
    (R : Regs T (prime + K)) (hstr : R (r .str) = (crtBox a (List.finRange d) X 0).flatten)
    (hwT : R (r .wT) = crtEnts ((crtRevAx d).map a))
    (hsT : R (r .sT) = crtEnts ((crtRevAx d).map s))
    (hmT : R (r .mT) = crtEnts ((crtRevAx d).map fun j => (crtMu s hcop j : ZMod (s j)).val))
    (hsig : R (r .sig) = binSyms (crtPre a d) (crtSig a s d))
    (hmsk : R (r .msk) = binSyms (crtPre a d) (crtMask a d)) (hzr : (R (r .zr)).length = B)
    (h0 : ∀ x ∈ crtRestEmpty, R (r x) = []) (hι0 : ∀ i, R (ι i) = []) :
    crtRuns body (crtInverse hQ ι hι hT r) R
      (Function.update R (r .str) ((List.range (∏ j, s j)).map fun k =>
        X fun j => (crtPhi s hcop ((k : ℕ) : ZMod (∏ i, s i)) j).val).flatten)
      (crtCost T (crtPre a d) B d am amin) := by
  have ne : ∀ {x y : CrtReg}, x ≠ y → r x ≠ r y := fun h => hr.ne h
  have upd : ∀ {α : Type} (f : Fin T → α) (y : CrtReg) (v : α) (x : CrtReg), x ≠ y →
      Function.update f (r y) v (r x) = f (r x) := fun f y v x h => Function.update_of_ne (ne h) _ _
  have z0 : ∀ x ∈ crtRestEmpty, R (r x) = [] := h0
  set μ : Fin d → ℕ := fun j => (crtMu s hcop j : ZMod (s j)).val with hμdef
  have hμ : ∀ j, μ j ≤ s j := fun j => by
    have : NeZero (s j) := ⟨(hs j).1.ne'⟩
    exact (ZMod.val_lt _).le
  have hmsklen : (R (r .msk)).length = crtPre a d := by rw [hmsk, length_binSyms]
  have hrev : ∀ g : Fin d → ℕ, (crtEnts (A := prime + K) ((List.finRange d).map g)).reverse =
      crtEnts ((crtRevAx d).map g) := fun g => by
    rw [crtEnts_reverse, ← List.map_reverse, crtRevAx_full]
  -- the counter of `3 B`
  have s₁ := crtUmul_runs (body := body) 3 (a := r .zr) (b := r .t3B) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R (z0 .u1 (by decide))
  set R₁ := Function.update R (r .t3B) (List.replicate (3 * (R (r .zr)).length) tick ++
    R (r .t3B)) with hR₁
  clear_value R₁
  have f₁ : ∀ x, x ≠ r .t3B → R₁ x = R x := fun x h => by rw [hR₁, Function.update_of_ne h]
  have v₁ : R₁ (r .t3B) = List.replicate (3 * B) tick := by
    rw [hR₁, Function.update_self, hzr, z0 .t3B (by decide), List.append_nil]
  have s₂ := crtEncP_runs (body := body) (u := r .t3B) (tu := r .tu) (e := r .e3B) (t := r .u1)
    (crt_nd hr [.t3B, .tu, .e3B, .u1] (by decide)) R₁
    (by rw [f₁ _ (ne (by decide))]; exact z0 .tu (by decide))
    (by rw [f₁ _ (ne (by decide))]; exact z0 .e3B (by decide))
    (by rw [f₁ _ (ne (by decide))]; exact z0 .u1 (by decide))
  rw [v₁, List.length_replicate] at s₂
  set R₂ := Function.update R₁ (r .e3B)
    ((GrowingCounterData.advance (3 * B) []).map bitSymbol) with hR₂
  clear_value R₂
  have f₂ : ∀ x, x ≠ r .e3B → R₂ x = R₁ x := fun x h => by rw [hR₂, Function.update_of_ne h]
  have s₃ := crtClear_runs (body := body) (r .t3B) R₂
  set R₃ := Function.update R₂ (r .t3B) [] with hR₃
  clear_value R₃
  have f₃ : ∀ x, x ≠ r .t3B → R₃ x = R₂ x := fun x h => by rw [hR₃, Function.update_of_ne h]
  have g₃ : ∀ x : CrtReg, x ≠ .t3B → x ≠ .e3B → R₃ (r x) = R (r x) := fun x h1 h2 => by
    rw [f₃ _ (ne h1), f₂ _ (ne h2), f₁ _ (ne h1)]
  have s₄ := crtUcopy_runs (body := body) (a := r .msk) (b := r .postU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₃
    (by rw [g₃ .u1 (by decide) (by decide)]; exact z0 .u1 (by decide))
  set R₄ := Function.update R₃ (r .postU) (List.replicate (R₃ (r .msk)).length tick ++
    R₃ (r .postU)) with hR₄
  clear_value R₄
  have f₄ : ∀ x, x ≠ r .postU → R₄ x = R₃ x := fun x h => by rw [hR₄, Function.update_of_ne h]
  have g₄ : ∀ x : CrtReg, x ≠ .t3B → x ≠ .e3B → x ≠ .postU → R₄ (r x) = R (r x) :=
    fun x h1 h2 h3 => by rw [f₄ _ (ne h3), g₃ x h1 h2]
  have v₄post : R₄ (r .postU) = List.replicate (crtPre a d) tick := by
    rw [hR₄, Function.update_self, g₃ .msk (by decide) (by decide), hmsklen,
      g₃ .postU (by decide) (by decide), z0 .postU (by decide), List.append_nil]
  -- reverse the axis lists
  have s₅ := crtMv_runs (body := body) (ne (by decide : CrtReg.wT ≠ .wD)) R₄
  set R₅ := Function.update (Function.update R₄ (r .wT) []) (r .wD)
    ((R₄ (r .wT)).reverse ++ R₄ (r .wD)) with hR₅
  clear_value R₅
  have s₆ := crtMv_runs (body := body) (ne (by decide : CrtReg.sT ≠ .sD)) R₅
  set R₆ := Function.update (Function.update R₅ (r .sT) []) (r .sD)
    ((R₅ (r .sT)).reverse ++ R₅ (r .sD)) with hR₆
  clear_value R₆
  have s₇ := crtMv_runs (body := body) (ne (by decide : CrtReg.mT ≠ .mD)) R₆
  set R₇ := Function.update (Function.update R₆ (r .mT) []) (r .mD)
    ((R₆ (r .mT)).reverse ++ R₆ (r .mD)) with hR₇
  clear_value R₇
  have f₇ : ∀ x : Fin T, x ≠ r .wT → x ≠ r .wD → x ≠ r .sT → x ≠ r .sD → x ≠ r .mT →
      x ≠ r .mD → R₇ x = R₄ x := fun x h1 h2 h3 h4 h5 h6 => by
    rw [hR₇, Function.update_of_ne h6, Function.update_of_ne h5, hR₆, Function.update_of_ne h4,
      Function.update_of_ne h3, hR₅, Function.update_of_ne h2, Function.update_of_ne h1]
  have g₇ : ∀ x : CrtReg, x ∉ [CrtReg.t3B, .e3B, .postU, .wT, .wD, .sT, .sD, .mT, .mD] →
      R₇ (r x) = R (r x) := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hx
    rw [f₇ _ (ne h4) (ne h5) (ne h6) (ne h7) (ne h8) (ne h9), g₄ x h1 h2 h3]
  have e₇ : crtFwdSt a s μ r R₇ X 0 = R₇ := by
    apply crtSt_eq_self hr
    · rw [g₇ .str (by decide), hstr, crtLay_zero]
    · rw [hR₇, hR₆, hR₅]; simp (disch := decide) only [upd, Function.update_self]; rfl
    · rw [hR₇, hR₆, hR₅]; simp (disch := decide) only [upd, Function.update_self]; rfl
    · rw [hR₇, hR₆, hR₅]; simp (disch := decide) only [upd, Function.update_self]; rfl
    · rw [hR₇, hR₆, hR₅]; simp (disch := decide) only [upd, Function.update_self]
      rw [g₄ .wT (by decide) (by decide) (by decide), g₄ .wD (by decide) (by decide) (by decide),
        hwT, z0 .wD (by decide), List.append_nil, List.drop_zero, ← hrev, List.reverse_reverse]
    · rw [hR₇, hR₆, hR₅]; simp (disch := decide) only [upd, Function.update_self]
      rw [g₄ .sT (by decide) (by decide) (by decide), g₄ .sD (by decide) (by decide) (by decide),
        hsT, z0 .sD (by decide), List.append_nil, List.drop_zero, ← hrev, List.reverse_reverse]
    · rw [hR₇, hR₆, hR₅]; simp (disch := decide) only [upd, Function.update_self]
      rw [g₄ .mT (by decide) (by decide) (by decide), g₄ .mD (by decide) (by decide) (by decide),
        hmT, z0 .mD (by decide), List.append_nil, List.drop_zero, ← hrev, List.reverse_reverse]
    · rw [g₇ .preU (by decide), z0 .preU (by decide), crtPre_zero, List.replicate_zero]
    · rw [f₇ _ (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
        (ne (by decide)) (ne (by decide)), v₄post, List.drop_zero, crtW_finRange]
  -- the iterations
  have hidle : ∀ x ∈ crtIdle, x ∉ [CrtReg.t3B, .e3B, .postU, .wT, .wD, .sT, .sD, .mT, .mD] := by
    decide
  have s₈ := crtInvLoop_runs (body := body) a s μ hs hμ hadj am amin ham hamin hQ ι hι hT hr hrι
    X B hB hX h8 R₇
    (by rw [g₇ .sig (by decide), hsig])
    (by rw [g₇ .msk (by decide), hmsk])
    (by rw [g₇ .zr (by decide), hzr])
    (by rw [f₇ _ (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
          (ne (by decide)) (ne (by decide)), f₄ _ (ne (by decide)), f₃ _ (ne (by decide)), hR₂,
          Function.update_self])
    (fun x hx => by rw [g₇ x (hidle x hx)]; exact z0 x (List.mem_append_left _ hx))
    (fun j => by
      rw [f₇ _ (hrι _ _).symm (hrι _ _).symm (hrι _ _).symm (hrι _ _).symm (hrι _ _).symm
        (hrι _ _).symm, f₄ _ (hrι _ _).symm, f₃ _ (hrι _ _).symm, f₂ _ (hrι _ _).symm,
        f₁ _ (hrι _ _).symm]; exact hι0 j)
  rw [e₇] at s₈
  set D := crtInvC s μ X d with hD
  set R₈ := crtFwdSt a s μ r R₇ D d with hR₈
  clear_value R₈
  have v₈ : ∀ x : CrtReg, x ∉ [CrtReg.str, .wT, .sT, .mT, .wD, .sD, .mD, .preU, .postU] →
      R₈ (r x) = R₇ (r x) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hx
    rw [hR₈, crtFwdSt, crtSt_of_ne]
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨ne h1, ne h2, ne h3, ne h4, ne h5, ne h6, ne h7, ne h8, ne h9⟩
  have r8str : R₈ (r .str) = (crtBox a (crtRevAx d) D 0).flatten := by
    rw [hR₈]; simp (disch := decide) only [crtFwdSt, crtSt, upd, Function.update_self]
    rw [crtLay_top]
  have r8T : ∀ (x : CrtReg) (g : Fin d → ℕ),
      (x = .wT ∧ g = a) ∨ (x = .sT ∧ g = s) ∨ (x = .mT ∧ g = μ) →
      R₈ (r x) = crtEnts ((crtRevAx d).map g) := by
    rintro x g (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      (rw [hR₈]; simp (disch := decide) only [crtFwdSt, crtSt, upd, Function.update_self])
  have r8D : ∀ x : CrtReg, x = .wD ∨ x = .sD ∨ x = .mD ∨ x = .postU → R₈ (r x) = [] := by
    rintro x (rfl | rfl | rfl | rfl) <;>
      (rw [hR₈]; simp (disch := decide) only [crtFwdSt, crtSt, upd, Function.update_self]
       rw [List.drop_eq_nil_of_le (by simp)]; rfl)
  have r8pre : R₈ (r .preU) = List.replicate (crtPre a d) tick := by
    rw [hR₈]; simp (disch := decide) only [crtFwdSt, crtSt, upd, Function.update_self]
  -- clear, delete
  have s₉ := crtClear_runs (body := body) (r .preU) R₈
  set R₉ := Function.update R₈ (r .preU) [] with hR₉
  clear_value R₉
  have s₁₀ := crtClear_runs (body := body) (r .e3B) R₉
  set R₁₀ := Function.update R₉ (r .e3B) [] with hR₁₀
  clear_value R₁₀
  have f₁₀ : ∀ x : CrtReg, x ≠ .preU → x ≠ .e3B → R₁₀ (r x) = R₈ (r x) := fun x h1 h2 => by
    rw [hR₁₀, Function.update_of_ne (ne h2), hR₉, Function.update_of_ne (ne h1)]
  have g₁₀ : ∀ x : CrtReg, x ∉ [CrtReg.t3B, .e3B, .postU, .wT, .wD, .sT, .sD, .mT, .mD, .str,
      .preU] → R₁₀ (r x) = R (r x) := fun x hx => by
    have hx' := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hx'
    rw [f₁₀ x h11 h2, v₈ x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h10, h4, h6, h8, h5, h7, h9, h11, h3⟩),
      g₇ x (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)]
  have hDl : ∀ y, (D y).length = B := crtInvC_mem s μ (fun c => c.length = B) X hX d
  have s₁₁ := crtDel_runs (body := body) a s (crtLp r) (crtLp_ok hr) (str := r .str)
    (acc := r .acc) (zr := r .zr) (bU := r .bU) (tA := r .tA)
    (crt_nd hr [.str, .acc, .zr, .bU, .tA] (by decide))
    (by intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;>
          exact crtLp_prot hr _ rfl (by decide))
    hs D B hDl R₁₀
    (by rw [f₁₀ .str (by decide) (by decide), r8str])
    (by rw [g₁₀ .zr (by decide), hzr])
    (by rw [g₁₀ .acc (by decide)]; exact z0 .acc (by decide))
    (by rw [g₁₀ .bU (by decide)]; exact z0 .bU (by decide))
    (by rw [g₁₀ .tA (by decide)]; exact z0 .tA (by decide))
    (by show R₁₀ (r .nF) = []; rw [g₁₀ .nF (by decide)]; exact z0 .nF (by decide))
    (by show R₁₀ (r .tN) = []; rw [g₁₀ .tN (by decide)]; exact z0 .tN (by decide))
    (by show R₁₀ (r .fc) = []; rw [g₁₀ .fc (by decide)]; exact z0 .fc (by decide))
    (by show R₁₀ (r .sig) = _; rw [g₁₀ .sig (by decide), hsig])
    (by show R₁₀ (r .msk) = _; rw [g₁₀ .msk (by decide), hmsk])
    (by show R₁₀ (r .c0) = []; rw [g₁₀ .c0 (by decide)]; exact z0 .c0 (by decide))
    (by show R₁₀ (r .c1) = []; rw [g₁₀ .c1 (by decide)]; exact z0 .c1 (by decide))
    (by show R₁₀ (r .c2) = []; rw [g₁₀ .c2 (by decide)]; exact z0 .c2 (by decide))
    (by show R₁₀ (r .it) = []; rw [g₁₀ .it (by decide)]; exact z0 .it (by decide))
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ (crtRuns_seq s₃
    (crtRuns_seq s₄ (crtRuns_seq s₅ (crtRuns_seq s₆ (crtRuns_seq s₇ (crtRuns_seq s₈
      (crtRuns_seq s₉ (crtRuns_seq s₁₀ s₁₁)))))))))) ?_) ?_
  all_goals clear s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁
  · funext x
    by_cases x0 : x = r .str
    · subst x0
      rw [Function.update_self, Function.update_self, crtProd, crtLow_of_le le_rfl]
      congr 1
      refine List.map_congr_left fun k hk => ?_
      rw [List.mem_range] at hk
      exact crtInvC_spec s (fun j => (hs j).1) hcop X hk
    rw [Function.update_of_ne x0, Function.update_of_ne x0]
    by_cases x1 : x = r .e3B
    · subst x1; rw [hR₁₀, Function.update_self, z0 .e3B (by decide)]
    by_cases x2 : x = r .preU
    · subst x2; rw [hR₁₀, hR₉]; simp (disch := decide) only [upd, Function.update_self]
      rw [z0 .preU (by decide)]
    have w₁ : ∀ y : CrtReg, y ≠ .preU → y ≠ .e3B → y ≠ .str → R₁₀ (r y) = R₈ (r y) :=
      fun y h1 h2 _ => f₁₀ y h1 h2
    by_cases x3 : x = r .wT
    · subst x3; rw [w₁ .wT (by decide) (by decide) (by decide),
        r8T .wT a (Or.inl ⟨rfl, rfl⟩), hwT]
    by_cases x4 : x = r .sT
    · subst x4; rw [w₁ .sT (by decide) (by decide) (by decide),
        r8T .sT s (Or.inr (Or.inl ⟨rfl, rfl⟩)), hsT]
    by_cases x5 : x = r .mT
    · subst x5; rw [w₁ .mT (by decide) (by decide) (by decide),
        r8T .mT μ (Or.inr (Or.inr ⟨rfl, rfl⟩)), hmT]
    by_cases x6 : x = r .wD
    · subst x6; rw [w₁ .wD (by decide) (by decide) (by decide), r8D .wD (Or.inl rfl),
        z0 .wD (by decide)]
    by_cases x7 : x = r .sD
    · subst x7; rw [w₁ .sD (by decide) (by decide) (by decide), r8D .sD (Or.inr (Or.inl rfl)),
        z0 .sD (by decide)]
    by_cases x8 : x = r .mD
    · subst x8; rw [w₁ .mD (by decide) (by decide) (by decide),
        r8D .mD (Or.inr (Or.inr (Or.inl rfl))), z0 .mD (by decide)]
    by_cases x9 : x = r .postU
    · subst x9; rw [w₁ .postU (by decide) (by decide) (by decide),
        r8D .postU (Or.inr (Or.inr (Or.inr rfl))), z0 .postU (by decide)]
    have h₈ : R₈ x = R₇ x := by
      rw [hR₈, crtFwdSt, crtSt_of_ne]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨x0, x3, x4, x5, x6, x7, x8, x2, x9⟩
    rw [hR₁₀, Function.update_of_ne x1, hR₉, Function.update_of_ne x2, h₈,
      f₇ x x3 x6 x4 x7 x5 x8, f₄ x x9]
    by_cases x10 : x = r .t3B
    · subst x10; rw [hR₃, Function.update_self, z0 .t3B (by decide)]
    rw [f₃ x x10, f₂ x x1, f₁ x x10]
  · have l₂ : (R₂ (r .t3B)).length = 3 * B := by
      rw [f₂ _ (ne (by decide)), v₁, List.length_replicate]
    have l₃ : (R₃ (r .msk)).length = crtPre a d := by
      rw [g₃ .msk (by decide) (by decide), hmsklen]
    have hra : (crtRevAx (d := d) d).length = d := by
      rw [crtRevAx_full, List.length_reverse, List.length_finRange]
    have hsa : ∀ j, s j ≤ 2 ^ am :=
      fun j => (hs j).2.le.trans (Nat.pow_le_pow_right (by norm_num) (ham j))
    have l₅ : (R₄ (r .wT)).length = crtPre a d + 2 * d := by
      rw [g₄ .wT (by decide) (by decide) (by decide), hwT, ← hrev, List.length_reverse,
        crtEnts_length, List.length_map, List.length_finRange, crtW_eq_sum, crtW_finRange]
    have l₆ : (R₅ (r .sT)).length ≤ d * 2 ^ am + 2 * d := by
      rw [hR₅, upd _ _ _ _ (by decide), upd _ _ _ _ (by decide),
        g₄ .sT (by decide) (by decide) (by decide), hsT]
      have := crtEnts_map_length_le (K := K) s (2 ^ am) hsa (crtRevAx d)
      rwa [hra] at this
    have l₇ : (R₆ (r .mT)).length ≤ d * 2 ^ am + 2 * d := by
      rw [hR₆, upd _ _ _ _ (by decide), upd _ _ _ _ (by decide), hR₅,
        upd _ _ _ _ (by decide), upd _ _ _ _ (by decide),
        g₄ .mT (by decide) (by decide) (by decide), hmT]
      have := crtEnts_map_length_le (K := K) μ (2 ^ am) (fun j => (hμ j).trans (hsa j))
        (crtRevAx d)
      rwa [hra] at this
    have l₉ : (R₈ (r .preU)).length = crtPre a d := by
      rw [r8pre, List.length_replicate]
    have l₁₀ : (R₉ (r .e3B)).length ≤ 3 * B := by
      rw [hR₉, Function.update_of_ne (ne (by decide)), v₈ .e3B (by decide),
        f₇ _ (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
          (ne (by decide)) (ne (by decide)), f₄ _ (ne (by decide)), f₃ _ (ne (by decide)), hR₂,
        Function.update_self, List.length_map]
      exact crt_advance_length _
    rw [hzr, l₂, l₃, l₅, l₉, crtCost]
    have hB2 : 3 * B * (4 * (3 * B) + 9) = 36 * B ^ 2 + 27 * B := by ring
    rw [hB2]
    omega

/-- At the address `crtPhi s hcop k` of a coefficient index `k < ∏ s`, the forward content is
the record `k`. -/
lemma crtSpecC_phi {d : ℕ} (s : Fin d → ℕ) (hs : ∀ j, 0 < s j)
    (hcop : Pairwise (Nat.Coprime on s)) {α : Type*} (l : List α) (z : α) {k : ℕ}
    (hk : k < ∏ i, s i) :
    crtSpecC s hcop l z (fun j => (crtPhi s hcop ((k : ℕ) : ZMod (∏ i, s i)) j).val) =
      l.getD k z := by
  have : ∀ i, NeZero (s i) := fun i => ⟨(hs i).ne'⟩
  have : NeZero (∏ i, s i) := ⟨(Finset.prod_pos fun i _ => hs i).ne'⟩
  unfold crtSpecC
  rw [if_pos (fun j => ZMod.val_lt _)]
  simp only [ZMod.natCast_zmod_val, AddEquiv.symm_apply_apply]
  rw [ZMod.val_natCast_of_lt hk]

lemma crt_map_getD_range {α : Type*} (l : List α) (z : α) :
    (List.range l.length).map (fun k => l.getD k z) = l := by
  apply List.ext_getElem (by simp)
  intro n h₁ h₂
  simp [List.getElem?_eq_getElem h₂]

set_option maxHeartbeats 4000000 in
/-- **Round trip.** `crtForward` followed by `crtInverse` restores the whole register file. -/
theorem crtRoundTrip_runs {d : ℕ} (a s : Fin d → ℕ) (hs : ∀ j, 0 < s j ∧ s j < 2 ^ a j)
    (hcop : Pairwise (Nat.Coprime on s)) (hadj : ∀ j j', a j ≤ a j' + 1) (am amin : ℕ)
    (ham : ∀ j, a j ≤ am) (hamin : ∀ j, amin ≤ a j)
    (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) {r : CrtReg → Fin T}
    (hr : Function.Injective r) (hrι : ∀ x j, r x ≠ ι j)
    (l : List (List (Fin (prime + K + 4)))) (z : List (Fin (prime + K + 4))) (B : ℕ)
    (hB : 0 < B) (hl : l.length = ∏ j, s j) (hlB : ∀ x ∈ l, x.length = B) (hz : z.length = B)
    (hl8 : ∀ x ∈ l, ∀ c ∈ x, c.val < 8) (hz8 : ∀ c ∈ z, c.val < 8)
    (R : Regs T (prime + K)) (hstr : R (r .str) = l.flatten)
    (hwT : R (r .wT) = crtEnts ((crtRevAx d).map a))
    (hsT : R (r .sT) = crtEnts ((crtRevAx d).map s))
    (hmT : R (r .mT) = crtEnts ((crtRevAx d).map fun j => (crtMu s hcop j : ZMod (s j)).val))
    (hsig : R (r .sig) = binSyms (crtPre a d) (crtSig a s d))
    (hmsk : R (r .msk) = binSyms (crtPre a d) (crtMask a d)) (hzr : R (r .zr) = z)
    (h0 : ∀ x ∈ crtRestEmpty, R (r x) = []) (hι0 : ∀ i, R (ι i) = []) :
    crtRuns body (.seq (crtForward hQ ι hι hT r) (crtInverse hQ ι hι hT r)) R R
      (2 * crtCost T (crtPre a d) B d am amin) := by
  have hf := crtForward_runs (body := body) a s hs hcop hadj am amin ham hamin hQ ι hι hT hr hrι
    l z B hB hl hlB hz hl8 hz8 R hstr hwT hsT hmT hsig hmsk hzr h0 hι0
  set X := crtSpecC s hcop l z with hXdef
  have hXl : ∀ y, (X y).length = B ∧ ∀ c ∈ X y, c.val < 8 := fun y => by
    rw [hXdef]; unfold crtSpecC; split_ifs
    · rw [List.getD_eq_getElem?_getD]
      rcases h : l[((crtPhi s hcop).symm fun j => (y j : ZMod (s j))).val]? with _ | x
      · simpa using ⟨hz, hz8⟩
      · simp only [Option.getD_some]
        exact ⟨hlB x (List.mem_of_getElem? h), hl8 x (List.mem_of_getElem? h)⟩
    · exact ⟨hz, hz8⟩
  have hns : ∀ x ∈ crtRestEmpty, x ≠ CrtReg.str := by decide
  have ne : ∀ {x y : CrtReg}, x ≠ y → r x ≠ r y := fun h => hr.ne h
  have hi := crtInverse_runs (body := body) a s hs hcop hadj am amin ham hamin hQ ι hι hT hr hrι
    X B hB (fun y => (hXl y).1) (fun y => (hXl y).2)
    (Function.update R (r .str) (crtBox a (List.finRange d) X 0).flatten)
    (Function.update_self _ _ _)
    (by rw [Function.update_of_ne (ne (by decide)), hwT])
    (by rw [Function.update_of_ne (ne (by decide)), hsT])
    (by rw [Function.update_of_ne (ne (by decide)), hmT])
    (by rw [Function.update_of_ne (ne (by decide)), hsig])
    (by rw [Function.update_of_ne (ne (by decide)), hmsk])
    (by rw [Function.update_of_ne (ne (by decide)), hzr, hz])
    (fun x hx => by rw [Function.update_of_ne (ne (hns x hx))]; exact h0 x hx)
    (fun i => by rw [Function.update_of_ne (hrι _ i).symm]; exact hι0 i)
  refine crtRuns_congr (crtRuns_mono (crtRuns_seq hf hi) (by omega)) ?_
  rw [Function.update_idem]
  have hS : 0 < ∏ i, s i := Finset.prod_pos fun i _ => (hs i).1
  have hmap : ((List.range (∏ j, s j)).map fun k =>
      X fun j => (crtPhi s hcop ((k : ℕ) : ZMod (∏ i, s i)) j).val) = l := by
    rw [List.map_congr_left (fun k hk => crtSpecC_phi s (fun j => (hs j).1) hcop l z
      (List.mem_range.mp hk)), ← hl, crt_map_getD_range]
  rw [hmap, ← hstr, Function.update_eq_self]

end

end Iter

end IntegerMultBounds.MathlibTM2.Fast
