module

public import IntegerMultBounds.MathlibTM2.Fast.CRTSwap
public import IntegerMultBounds.MathlibTM2.Fast.CRTSpec

/-!
# Drivers of the CRT layout machines: axis lists and swap walks

**Registers.** The machines use the host registers `r x` for `x : CrtReg` (`r` injective) and
the bank `ι` of the vendored interchange (disjoint from `r`). `crtLp r` and `crtLr r` are the
address-loop register sets of the scans (bounds and mask in the master registers `sig`, `msk`)
and of the rotation passes (bounds and mask in the copies `sg`, `mq`).

**Axis lists.** A list of unary values `xs` is stored as `crtEnts xs`, every value `x` as the
entry `crtEnt x = sep :: replicate x tick ++ [sep]` (`sep = bitSymbol false`). Entries are
symmetric, so moving a whole list onto an empty register reverses the order of its values
(`crtEnts_reverse`). `crtPopEnt src dst` moves the top value onto the empty `dst` in unary,
`crtPushEnt src dst` moves the unary `src` back as an entry on top of `dst`.

**Layouts.** `crtLay a n = crtRevAx n ++ (List.finRange d).drop n`: the axes `n - 1, …, 0`
followed by `n, …, d - 1`. The forward walk of target `i` moves axis `i` from the top of
`crtLay (i + 1)` below the axes `i - 1, …, 0` (`crtWalkF`); the inverse walk moves it back
(`crtWalkI`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult


/-- The registers of the CRT layout machines. -/
inductive CrtReg
  | str | acc | tA | tB | tc | tr | u1 | u2 | zr | bU | sig | msk
  | wT | sT | mT | wD | sD | mD | wW
  | aI | sI | muI | aK | preU | postU | uU | vU | vacc
  | e3B | t3B | tu | stmp
  | rbU | tsU | lo | hi | ov
  | nF | tN | fc | sg | mq | c0 | c1 | c2 | it | st | cy
  | extra (i : Fin 32)
  deriving DecidableEq

section Regs

variable {T : ℕ} (r : CrtReg → Fin T)

/-- Distinct register names give distinct registers. -/
lemma crt_nd {r : CrtReg → Fin T} (hr : Function.Injective r) (l : List CrtReg) (h : l.Nodup) :
    (l.map r).Nodup :=
  h.map hr

/-- The address-loop registers of the scans: bounds and mask in `sig`, `msk`. -/
def crtLp : CrtAL T :=
  ⟨r .nF, r .tN, r .fc, r .sig, r .msk, r .c0, r .c1, r .c2, r .it, r .st, r .cy⟩

/-- The address-loop registers of the rotation passes: bounds and mask in `sg`, `mq`. -/
def crtLr : CrtAL T :=
  ⟨r .nF, r .tN, r .fc, r .sg, r .mq, r .c0, r .c1, r .c2, r .it, r .st, r .cy⟩

variable {r}

lemma crtLp_ok (hr : Function.Injective r) : (crtLp r).Ok :=
  crt_nd hr [.nF, .tN, .fc, .sig, .msk, .c0, .c1, .c2, .it, .st] (by decide)

lemma crtLr_ok (hr : Function.Injective r) : (crtLr r).Ok :=
  crt_nd hr [.nF, .tN, .fc, .sg, .mq, .c0, .c1, .c2, .it, .st] (by decide)

lemma crtLp_prot (hr : Function.Injective r) {x : CrtReg} (k : Fin T) (hk : k = r x)
    (hx : x ∉ [.nF, .tN, .fc, .sig, .msk, .c0, .c1, .c2, .it]) : ¬ (crtLp r).Prot k := by
  subst hk
  simp only [CrtAL.Prot, crtLp, hr.eq_iff]
  simpa using hx

lemma crtLr_prot (hr : Function.Injective r) {x : CrtReg} (k : Fin T) (hk : k = r x)
    (hx : x ∉ [.nF, .tN, .fc, .sg, .mq, .c0, .c1, .c2, .it]) : ¬ (crtLr r).Prot k := by
  subst hk
  simp only [CrtAL.Prot, crtLr, hr.eq_iff]
  simpa using hx

end Regs

/-! ### Axis lists -/

section Lists

variable {A : ℕ}

/-- The separator of entries. -/
abbrev crtSep : Fin (A + 4) := bitSymbol false

/-- One entry: a unary value between separators. -/
def crtEnt (x : ℕ) : List (Fin (A + 4)) := crtSep :: (List.replicate x tick ++ [crtSep])

/-- A list of unary values. -/
def crtEnts (xs : List ℕ) : List (Fin (A + 4)) := xs.flatMap crtEnt

@[simp] lemma crtEnts_nil : crtEnts (A := A) [] = [] := rfl

lemma crtEnts_cons (x : ℕ) (xs : List ℕ) :
    crtEnts (A := A) (x :: xs) = crtEnt x ++ crtEnts xs := by
  simp [crtEnts]

lemma crtEnt_reverse (x : ℕ) : (crtEnt (A := A) x).reverse = crtEnt x := by
  simp [crtEnt, List.reverse_replicate]

lemma crtEnts_reverse (xs : List ℕ) : (crtEnts (A := A) xs).reverse = crtEnts xs.reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [crtEnts_cons, List.reverse_append, ih, crtEnt_reverse, List.reverse_cons, crtEnts,
        crtEnts, List.flatMap_append]
      simp

lemma crtEnts_ne_nil {xs : List ℕ} (h : xs ≠ []) : crtEnts (A := A) xs ≠ [] := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  simp [crtEnts_cons, crtEnt]

lemma crtEnts_eq_nil {xs : List ℕ} : crtEnts (A := A) xs = [] ↔ xs = [] := by
  constructor
  · intro h; by_contra h'; exact crtEnts_ne_nil h' h
  · rintro rfl; rfl

variable {T Q : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Move the top value of the list `src` onto the empty `dst`, in unary. -/
def crtPopEnt (src dst : Fin T) : Pr P T Q A U :=
  .seq (crtPop src) (.seq (crtMvWhile src dst tick) (crtPop src))

theorem crtPopEnt_runs {src dst : Fin T} (h : src ≠ dst) (R : Regs T A) (x : ℕ) (xs : List ℕ)
    (hsrc : R src = crtEnts (x :: xs)) (hdst : R dst = []) :
    crtRuns body (crtPopEnt src dst) R
      (Function.update (Function.update R src (crtEnts xs)) dst (List.replicate x tick))
      (2 * x + 4) := by
  have s₁ := crtPop_runs (body := body) src R
  set R₁ := Function.update R src (R src).tail with hR₁
  have hR₁src : R₁ src = List.replicate x tick ++ (crtSep :: crtEnts xs) := by
    simp [hR₁, hsrc, crtEnts_cons, crtEnt]
  have s₂ := crtMvWhile_runs (body := body) h tick x (crtSep :: crtEnts xs)
    (by simp [tick, crtSep, bitSymbol, Fin.ext_iff]) R₁ hR₁src
  set R₂ := Function.update (Function.update R₁ src (crtSep :: crtEnts xs)) dst
    (List.replicate x tick ++ R₁ dst) with hR₂
  have s₃ := crtPop_runs (body := body) src R₂
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ s₃)) ?_) (by omega)
  funext k
  by_cases k1 : k = src
  · rw [k1]; simp [hR₂, h]
  · by_cases k2 : k = dst
    · rw [k2]; simp [hR₂, hR₁, Ne.symm h, hdst]
    · simp [hR₂, hR₁, k1, k2]

/-- Move the unary `src` (emptied) as an entry on top of `dst`. -/
def crtPushEnt (src dst : Fin T) : Pr P T Q A U :=
  .seq (crtPush dst crtSep) (.seq (crtMv src dst) (crtPush dst crtSep))

theorem crtPushEnt_runs {src dst : Fin T} (h : src ≠ dst) (R : Regs T A) (x : ℕ)
    (hsrc : R src = List.replicate x tick) :
    crtRuns body (crtPushEnt src dst) R
      (Function.update (Function.update R src []) dst (crtEnt x ++ R dst)) (2 * x + 4) := by
  have s₁ := crtPush_runs (body := body) dst crtSep R
  set R₁ := Function.update R dst (crtSep :: R dst) with hR₁
  have s₂ := crtMv_runs (body := body) h R₁
  set R₂ := Function.update (Function.update R₁ src []) dst ((R₁ src).reverse ++ R₁ dst) with hR₂
  have s₃ := crtPush_runs (body := body) dst crtSep R₂
  have hR₁src : R₁ src = List.replicate x tick := by simp [hR₁, h, hsrc]
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ s₃)) ?_)
    (by rw [hR₁src, List.length_replicate]; omega)
  funext k
  by_cases k1 : k = dst
  · rw [k1]
    simp [hR₂, hR₁, Function.update_of_ne h, hsrc, crtEnt, List.reverse_replicate]
  · by_cases k2 : k = src
    · rw [k2]; simp [hR₂, h]
    · simp [hR₂, hR₁, k1, k2]

end Lists

/-! ### Layouts -/

section Layouts

variable {d : ℕ} (a : Fin d → ℕ)

/-- The layout with the axes `n - 1, …, 0` first and `n, …, d - 1` after them. -/
def crtLay (n : ℕ) : List (Fin d) := crtRevAx n ++ (List.finRange d).drop n

lemma crt_drop_finRange {i : ℕ} (h : i < d) :
    (List.finRange d).drop i = (⟨i, h⟩ : Fin d) :: (List.finRange d).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

lemma crtLay_succ {i : ℕ} (h : i < d) :
    crtLay (d := d) (i + 1) = (⟨i, h⟩ : Fin d) :: (crtRevAx i ++ (List.finRange d).drop (i + 1)) := by
  rw [crtLay, crtRevAx_succ h, List.cons_append]

lemma crtLay_rot {i : ℕ} (h : i < d) :
    crtLay (d := d) i = crtRevAx i ++ (⟨i, h⟩ : Fin d) :: (List.finRange d).drop (i + 1) := by
  rw [crtLay, crt_drop_finRange h]

lemma crtLay_zero : crtLay (d := d) 0 = List.finRange d := by simp [crtLay]

lemma crtLay_top : crtLay (d := d) d = crtRevAx d := by simp [crtLay]

lemma crtLay_nodup (n : ℕ) : (crtLay (d := d) n).Nodup := by
  rw [crtLay, crtRevAx, List.nodup_append]
  refine ⟨List.nodup_reverse.2 ((List.nodup_finRange d).sublist (List.take_sublist _ _)),
    (List.nodup_finRange d).sublist (List.drop_sublist _ _), ?_⟩
  intro x hx y hy hxy
  subst hxy
  rw [List.mem_reverse] at hx
  have h1 := List.mem_take_iff_getElem.1 hx
  have h2 := List.mem_drop_iff_getElem.1 hy
  obtain ⟨i₁, hi₁, e₁⟩ := h1
  obtain ⟨i₂, hi₂, e₂⟩ := h2
  simp only [List.getElem_finRange] at e₁ e₂
  rw [← e₂] at e₁
  have := congrArg Fin.val e₁
  simp at this hi₁
  omega

/-- The forward walk of target `i` after `k` swaps. -/
def crtWalkF (i k : ℕ) (h : i < d) : List (Fin d) :=
  (crtRevAx i).take k ++ (⟨i, h⟩ : Fin d) :: ((crtRevAx i).drop k ++ (List.finRange d).drop (i + 1))

/-- The inverse walk of target `i` after `k` swaps. -/
def crtWalkI (i k : ℕ) (h : i < d) : List (Fin d) :=
  (crtRevAx i).take (i - k) ++
    (⟨i, h⟩ : Fin d) :: ((crtRevAx i).drop (i - k) ++ (List.finRange d).drop (i + 1))

lemma crtRevAx_length (i : ℕ) (h : i ≤ d) : (crtRevAx (d := d) i).length = i := by
  simp [crtRevAx]; omega

lemma crtRevAx_getElem {i k : ℕ} (h : i ≤ d) (hk : k < (crtRevAx (d := d) i).length) :
    (crtRevAx (d := d) i)[k] = ⟨i - 1 - k, by rw [crtRevAx_length i h] at hk; omega⟩ := by
  have hk' : k < i := by rwa [crtRevAx_length i h] at hk
  simp [crtRevAx, List.getElem_reverse, List.getElem_take, List.getElem_finRange]
  omega

end Layouts

set_option hygiene false in
/-- Evaluate a register file built by `Function.update` at a register, deciding the
inequalities of named registers through the injective `hr` and the bank disjointness `hrι`. -/
macro "crt_upd" : tactic => `(tactic| simp (disch := first
  | exact hr.ne (by decide) | exact hrι _ _ | exact (hrι _ _).symm | assumption) only
    [Function.update_self, Function.update_of_ne])

set_option hygiene false in
/-- `crt_upd` at hypotheses and the goal with extra simp lemmas. -/
macro "crt_upd'" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| simp (disch := first
  | exact hr.ne (by decide) | exact hrι _ _ | exact (hrι _ _).symm | assumption) only
    [Function.update_self, Function.update_of_ne, $ls,*])

/-! ### Widths of layouts -/

section Widths

variable {d : ℕ} (a : Fin d → ℕ)

lemma crtW_perm {l₁ l₂ : List (Fin d)} (h : l₁.Perm l₂) : crtW a l₁ = crtW a l₂ :=
  (h.map a).sum_eq

lemma crtW_finRange : crtW a (List.finRange d) = crtPre a d := by
  rw [crtW, ← Fin.sum_univ_def, crtPre, crtLow_of_le le_rfl]

lemma crtLay_perm (n : ℕ) : (crtLay (d := d) n).Perm (List.finRange d) := by
  rw [crtLay, crtRevAx]
  have h := ((List.reverse_perm ((List.finRange d).take n)).append_right
    ((List.finRange d).drop n))
  rwa [List.take_append_drop] at h

lemma crtW_crtLay (n : ℕ) : crtW a (crtLay n) = crtPre a d := by
  rw [crtW_perm a (crtLay_perm n), crtW_finRange]

lemma crtWalkF_perm {i : ℕ} (h : i < d) (k : ℕ) :
    (crtWalkF i k h).Perm (crtLay (d := d) (i + 1)) := by
  rw [crtWalkF, crtLay_succ h]
  refine List.perm_middle.trans ?_
  rw [← List.append_assoc, List.take_append_drop]

lemma crtWalkI_perm {i : ℕ} (h : i < d) (k : ℕ) :
    (crtWalkI i k h).Perm (crtLay (d := d) (i + 1)) := by
  rw [crtWalkI, crtLay_succ h]
  refine List.perm_middle.trans ?_
  rw [← List.append_assoc, List.take_append_drop]

lemma crtRevAx_drop {i k : ℕ} (hk : k ≤ i) (hi : i ≤ d) :
    (crtRevAx (d := d) i).drop (i - k) = crtRevAx k := by
  rw [crtRevAx, List.drop_reverse, List.length_take, List.length_finRange, Nat.min_eq_left hi,
    show i - (i - k) = k by omega, List.take_take, Nat.min_eq_left hk, crtRevAx]

lemma crtW_revAx_take {i k : ℕ} (hk : k ≤ i) (hi : i ≤ d) :
    crtW a ((crtRevAx (d := d) i).take (i - k)) + crtPre a k = crtPre a i := by
  rw [← crtW_revAx a k (hk.trans hi), ← crtRevAx_drop hk hi, ← crtW_append, List.take_append_drop,
    crtW_revAx a i hi]

lemma crtRevAx_reverse (i : ℕ) : (crtRevAx (d := d) i).reverse = (List.finRange d).take i := by
  rw [crtRevAx, List.reverse_reverse]

end Widths

/-! ### One step of a walk -/

section Step

noncomputable section

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {T Q K : ℕ} {U F : Type} {body : F → Pr F T Q (prime + K) U}

/-- One forward walk step: pop the next axis width `aK`, set `vU = |preU| + |postU| - |uU| - |aK|`,
exchange the axis `aI` (above) with the axis `aK` (below), add `aK` to `uU`, and push the entry
onto `wW`. -/
def crtFwdStep (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) (r : CrtReg → Fin T) :
    Pr F T Q (prime + K) U :=
  .seq (crtPopEnt (r .wT) (r .aK)) <|
  .seq (ucopy (r .preU) (r .vU) (r .u1)) <| .seq (ucopy (r .postU) (r .vU) (r .u1)) <|
  .seq (usub (r .uU) (r .vU) (r .u1)) <| .seq (usub (r .aK) (r .vU) (r .u1)) <|
  .seq (crtSwapStep hQ ι hι hT (r .str) (r .stmp) (r .uU) (r .vU) (r .aI) (r .aK) (r .e3B) (r .tu)
    (r .u1) (r .u2)) <|
  .seq (ucopy (r .aK) (r .uU) (r .u1)) <| .seq (uclear (r .vU)) (crtPushEnt (r .aK) (r .wW))

/-- The bound of one walk step: `V` record symbols, total width `Lw`, widths at most `am`. -/
def crtStepBound (T Lw B V am : ℕ) : ℕ :=
  (T + 12 * swapT 6 + 5) * crtSwapCostN (3 * V) am am + (6 * swapT 6 + 10) * (Lw + 3 * B + 2) +
    34 * V + 2 * T + 6 * swapT 6 + 18 * B + Lw * (4 * Lw + 41) + 120

lemma crtSwapCostN_mono {V h w h' w' : ℕ} (hh : max h w ≤ max h' w') :
    crtSwapCostN V h w ≤ crtSwapCostN V h' w' := by
  unfold crtSwapCostN
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (by
    have := swapConst_pos
    positivity)
  apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast max_le_max_left 1 hh)
  exact (Shared50RecursiveBudgetBound.exponent_range.1.le)

variable {d : ℕ} (a : Fin d → ℕ)

lemma crt_step_arith (ak P0 P1 u pre post aj B S6 Tn c c' V Lw : ℕ)
    (hLw : Lw = pre + aj + ak + post) (hP : P0 + P1 = pre + ak + post) (hu : u = pre)
    (hc : c ≤ c') :
    2 * ak + 4 + (4 * P0 + 4 + (4 * P1 + 4 + (4 * u + 4 + (4 * ak + 4 +
      ((Tn + 12 * S6 + 5) * c + (6 * S6 + 10) * (pre + post + 3 * B + aj + ak + 2) + 34 * V +
        2 * Tn + 6 * S6 + 4 * pre + 4 * post + 18 * B + aj * (4 * aj + 11) + ak * (4 * ak + 11) +
        80 + (4 * ak + 4 + (2 * post + 2 + (2 * ak + 4)))))))) ≤
    (Tn + 12 * S6 + 5) * c' + (6 * S6 + 10) * (Lw + 3 * B + 2) + 34 * V + 2 * Tn + 6 * S6 +
      18 * B + Lw * (4 * Lw + 41) + 120 := by
  subst hLw; rw [hu]
  have h1 := Nat.mul_le_mul_left (Tn + 12 * S6 + 5) hc
  have h2 : (6 * S6 + 10) * (pre + post + 3 * B + aj + ak + 2) =
      (6 * S6 + 10) * (pre + aj + ak + post + 3 * B + 2) := by ring
  have h3 : aj * (4 * aj + 11) + ak * (4 * ak + 11) + 4 * pre + 4 * post + 4 * P0 + 4 * P1 +
      4 * pre + 12 * ak + 2 * post ≤ (pre + aj + ak + post) * (4 * (pre + aj + ak + post) + 41) := by
    nlinarith
  omega

set_option maxHeartbeats 4000000 in
theorem crtFwdStep_runs (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) {r : CrtReg → Fin T}
    (hr : Function.Injective r) (hrι : ∀ x j, r x ≠ ι j)
    (pre post : List (Fin d)) (j k : Fin d) (hjk : j ≠ k) (hadj : a j ≤ a k + 1 ∧ a k ≤ a j + 1)
    (am : ℕ) (ham : a j ≤ am ∧ a k ≤ am)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ x ∈ C y, x.val < 8)
    (ys : List ℕ) (u : ℕ) (R : Regs T (prime + K))
    (hstr : R (r .str) = (crtBox a (pre ++ j :: k :: post) C 0).flatten)
    (hwT : R (r .wT) = crtEnts (a k :: ys)) (huU : R (r .uU) = List.replicate u tick)
    (hu : u = crtW a pre)
    (hpp : (R (r .preU)).length + (R (r .postU)).length = crtW a pre + a k + crtW a post)
    (haI : (R (r .aI)).length = a j)
    (he3 : R (r .e3B) = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (h0 : ∀ x ∈ [CrtReg.aK, .vU, .stmp, .tu, .u1, .u2], R (r x) = [])
    (hι0 : ∀ i, R (ι i) = []) :
    crtRuns body (crtFwdStep hQ ι hι hT r) R
      (Function.update (Function.update (Function.update (Function.update R (r .str)
        (crtBox a (pre ++ k :: j :: post) C 0).flatten) (r .wT) (crtEnts ys)) (r .uU)
        (List.replicate (u + a k) tick)) (r .wW) (crtEnt (a k) ++ R (r .wW)))
      (crtStepBound T (crtW a (pre ++ j :: k :: post)) B
        (2 ^ crtW a (pre ++ j :: k :: post) * B) am) := by
  have hz : ∀ x ∈ [CrtReg.aK, .vU, .stmp, .tu, .u1, .u2], R (r x) = [] := h0
  have ne : ∀ {x y : CrtReg}, x ≠ y → r x ≠ r y := fun h => hr.ne h
  obtain ⟨P0, hP0⟩ : ∃ P0, (R (r .preU)).length = P0 := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P1, (R (r .postU)).length = P1 := ⟨_, rfl⟩
  -- pop the entry
  have s₁ := crtPopEnt_runs (body := body) (ne (by decide)) R (a k) ys hwT (hz .aK (by simp))
  set R₁ := Function.update (Function.update R (r .wT) (crtEnts ys)) (r .aK)
    (List.replicate (a k) tick) with hR₁
  clear_value R₁
  have f₁ : ∀ x, x ≠ r .wT → x ≠ r .aK → R₁ x = R x := fun x h1 h2 => by
    rw [hR₁, Function.update_of_ne h2, Function.update_of_ne h1]
  have v₁aK : R₁ (r .aK) = List.replicate (a k) tick := by rw [hR₁, Function.update_self]
  have v₁wT : R₁ (r .wT) = crtEnts ys := by
    rw [hR₁, Function.update_of_ne (ne (by decide)), Function.update_self]
  have u1₁ : R₁ (r .u1) = [] := by
    rw [f₁ _ (ne (by decide)) (ne (by decide))]; exact hz .u1 (by simp)
  -- vU := preU + postU - uU - aK
  have s₂ := crtUcopy_runs (body := body) (a := r .preU) (b := r .vU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₁ u1₁
  set R₂ := Function.update R₁ (r .vU) (List.replicate (R₁ (r .preU)).length tick ++ R₁ (r .vU))
    with hR₂
  clear_value R₂
  have f₂ : ∀ x, x ≠ r .vU → R₂ x = R₁ x := fun x h => by rw [hR₂, Function.update_of_ne h]
  have v₂ : R₂ (r .vU) = List.replicate P0 tick := by
    rw [hR₂, Function.update_self, f₁ _ (ne (by decide)) (ne (by decide)),
      f₁ _ (ne (by decide)) (ne (by decide)), hP0, hz .vU (by simp), List.append_nil]
  have s₃ := crtUcopy_runs (body := body) (a := r .postU) (b := r .vU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₂
    (by rw [f₂ _ (ne (by decide)), u1₁])
  set R₃ := Function.update R₂ (r .vU) (List.replicate (R₂ (r .postU)).length tick ++ R₂ (r .vU))
    with hR₃
  clear_value R₃
  have f₃ : ∀ x, x ≠ r .vU → R₃ x = R₂ x := fun x h => by rw [hR₃, Function.update_of_ne h]
  have v₃ : R₃ (r .vU) = List.replicate (P1 + P0) tick := by
    rw [hR₃, Function.update_self, v₂, f₂ _ (ne (by decide)),
      f₁ _ (ne (by decide)) (ne (by decide)), hP1, List.replicate_append_replicate]
  have s₄ := crtUsub_runs (body := body) (a := r .uU) (b := r .vU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₃
    (by rw [f₃ _ (ne (by decide)), f₂ _ (ne (by decide)), u1₁])
  set R₄ := Function.update R₃ (r .vU) ((R₃ (r .vU)).drop (R₃ (r .uU)).length) with hR₄
  clear_value R₄
  have f₄ : ∀ x, x ≠ r .vU → R₄ x = R₃ x := fun x h => by rw [hR₄, Function.update_of_ne h]
  have v₃uU : R₃ (r .uU) = List.replicate u tick := by
    rw [f₃ _ (ne (by decide)), f₂ _ (ne (by decide)), f₁ _ (ne (by decide)) (ne (by decide)), huU]
  have v₄ : R₄ (r .vU) = List.replicate (P1 + P0 - u) tick := by
    rw [hR₄, Function.update_self, v₃, v₃uU, List.length_replicate, List.drop_replicate]
  have s₅ := crtUsub_runs (body := body) (a := r .aK) (b := r .vU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₄
    (by rw [f₄ _ (ne (by decide)), f₃ _ (ne (by decide)), f₂ _ (ne (by decide)), u1₁])
  set R₅ := Function.update R₄ (r .vU) ((R₄ (r .vU)).drop (R₄ (r .aK)).length) with hR₅
  clear_value R₅
  have f₅ : ∀ x, x ≠ r .vU → R₅ x = R₄ x := fun x h => by rw [hR₅, Function.update_of_ne h]
  have v₄aK : R₄ (r .aK) = List.replicate (a k) tick := by
    rw [f₄ _ (ne (by decide)), f₃ _ (ne (by decide)), f₂ _ (ne (by decide)), v₁aK]
  have e₅vU : R₅ (r .vU) = List.replicate (crtW a post) tick := by
    rw [hR₅, Function.update_self, v₄, v₄aK, List.length_replicate, List.drop_replicate]
    congr 1
    omega
  have e₅ : ∀ x, x ≠ CrtReg.wT → x ≠ .aK → x ≠ .vU → R₅ (r x) = R (r x) := by
    intro x h1 h2 h3
    rw [f₅ _ (ne h3), f₄ _ (ne h3), f₃ _ (ne h3), f₂ _ (ne h3), f₁ _ (ne h1) (ne h2)]
  have e₅ι : ∀ i, R₅ (ι i) = R (ι i) := by
    intro i
    rw [f₅ _ (hrι _ _).symm, f₄ _ (hrι _ _).symm, f₃ _ (hrι _ _).symm, f₂ _ (hrι _ _).symm,
      f₁ _ (hrι _ _).symm (hrι _ _).symm]
  have e₅aK : R₅ (r .aK) = List.replicate (a k) tick := by
    rw [f₅ _ (ne (by decide)), v₄aK]
  -- the exchange
  have s₆ := crtSwapStep_runs (body := body) (a := a) hQ ι hι hT
    (str := r .str) (stmp := r .stmp) (uU := r .uU) (vU := r .vU) (aJ := r .aI) (aK := r .aK)
    (e3B := r .e3B) (tu := r .tu) (t₁ := r .u1) (t₂ := r .u2)
    (crt_nd hr [.str, .stmp, .uU, .vU, .aI, .aK, .e3B, .tu, .u1, .u2] (by decide))
    (by intro x hx i; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact (hrι _ i).symm)
    pre post j k hjk hadj.1 hadj.2 C B hB hC h8 0 R₅
    (by rw [e₅ .str (by decide) (by decide) (by decide), hstr])
    (by rw [e₅ .uU (by decide) (by decide) (by decide), huU, List.length_replicate, hu])
    (by rw [e₅vU, List.length_replicate])
    (by rw [e₅ .aI (by decide) (by decide) (by decide), haI])
    (by rw [e₅aK, List.length_replicate])
    (by rw [e₅ .e3B (by decide) (by decide) (by decide), he3])
    (by rw [e₅ .stmp (by decide) (by decide) (by decide)]; exact hz .stmp (by simp))
    (by rw [e₅ .tu (by decide) (by decide) (by decide)]; exact hz .tu (by simp))
    (by rw [e₅ .u1 (by decide) (by decide) (by decide)]; exact hz .u1 (by simp))
    (by rw [e₅ .u2 (by decide) (by decide) (by decide)]; exact hz .u2 (by simp))
    (fun i => by rw [e₅ι, hι0])
  set R₆ := Function.update R₅ (r .str) (crtBox a (pre ++ k :: j :: post) C 0).flatten with hR₆
  clear_value R₆
  have f₆ : ∀ x, x ≠ r .str → R₆ x = R₅ x := fun x h => by rw [hR₆, Function.update_of_ne h]
  -- uU += aK, vU := [], push the entry
  have s₇ := crtUcopy_runs (body := body) (a := r .aK) (b := r .uU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₆
    (by rw [f₆ _ (ne (by decide)), e₅ .u1 (by decide) (by decide) (by decide)]
        exact hz .u1 (by simp))
  set R₇ := Function.update R₆ (r .uU) (List.replicate (R₆ (r .aK)).length tick ++ R₆ (r .uU))
    with hR₇
  clear_value R₇
  have f₇ : ∀ x, x ≠ r .uU → R₇ x = R₆ x := fun x h => by rw [hR₇, Function.update_of_ne h]
  have s₈ := crtClear_runs (body := body) (r .vU) R₇
  have s₉ := crtPushEnt_runs (body := body) (src := r .aK) (dst := r .wW) (ne (by decide))
    (Function.update R₇ (r .vU) []) (a k)
    (by rw [Function.update_of_ne (ne (by decide)), f₇ _ (ne (by decide)),
          f₆ _ (ne (by decide)), e₅aK])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ (crtRuns_seq s₃
    (crtRuns_seq s₄ (crtRuns_seq s₅ (crtRuns_seq s₆ (crtRuns_seq s₇ (crtRuns_seq s₈
      s₉)))))))) ?_) ?_
  all_goals clear s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉
  · have upd : ∀ {α : Type} (f : Fin T → α) (y : CrtReg) (v : α) (x : CrtReg), x ≠ y →
        Function.update f (r y) v (r x) = f (r x) := fun f y v x h => Function.update_of_ne (ne h) _ _
    funext x
    by_cases x1 : x = r .wW
    · rw [x1]
      simp (disch := decide) only [upd, Function.update_self]
      rw [f₇ _ (ne (by decide)), f₆ _ (ne (by decide)), e₅ .wW (by decide) (by decide) (by decide)]
    by_cases x2 : x = r .aK
    · rw [x2]
      simp (disch := decide) only [upd, Function.update_self]
      exact (hz .aK (by simp)).symm
    by_cases x3 : x = r .vU
    · rw [x3]
      simp (disch := decide) only [upd, Function.update_self]
      exact (hz .vU (by simp)).symm
    by_cases x4 : x = r .uU
    · rw [x4]
      simp (disch := decide) only [upd, Function.update_self]
      rw [hR₇, Function.update_self, f₆ _ (ne (by decide)), e₅aK, f₆ _ (ne (by decide)),
        e₅ .uU (by decide) (by decide) (by decide), huU, List.length_replicate,
        List.replicate_append_replicate, Nat.add_comm (a k) u]
    by_cases x5 : x = r .str
    · rw [x5]
      simp (disch := decide) only [upd, Function.update_self]
      rw [f₇ _ (ne (by decide)), hR₆, Function.update_self]
    by_cases x6 : x = r .wT
    · rw [x6]
      simp (disch := decide) only [upd, Function.update_self]
      rw [f₇ _ (ne (by decide)), f₆ _ (ne (by decide)), f₅ _ (ne (by decide)),
        f₄ _ (ne (by decide)), f₃ _ (ne (by decide)), f₂ _ (ne (by decide)), v₁wT]
    rw [Function.update_of_ne x1, Function.update_of_ne x2, Function.update_of_ne x3,
      Function.update_of_ne x1, Function.update_of_ne x4, Function.update_of_ne x6,
      Function.update_of_ne x5, f₇ _ x4, f₆ _ x5, f₅ _ x3, f₄ _ x3, f₃ _ x3, f₂ _ x3, f₁ _ x6 x2]
  · have l₁ : (R₁ (r .preU)).length = P0 := by
      rw [f₁ _ (ne (by decide)) (ne (by decide)), hP0]
    have l₂ : (R₂ (r .postU)).length = P1 := by
      rw [f₂ _ (ne (by decide)), f₁ _ (ne (by decide)) (ne (by decide)), hP1]
    have l₃ : (R₃ (r .uU)).length = u := by rw [v₃uU, List.length_replicate]
    have l₄ : (R₄ (r .aK)).length = a k := by rw [v₄aK, List.length_replicate]
    have l₆ : (R₆ (r .aK)).length = a k := by
      rw [f₆ _ (ne (by decide)), e₅aK, List.length_replicate]
    have l₇ : (R₇ (r .vU)).length = crtW a post := by
      rw [f₇ _ (ne (by decide)), f₆ _ (ne (by decide)), e₅vU, List.length_replicate]
    rw [l₁, l₂, l₃, l₄, l₆, l₇, crtStepBound]
    have hW : crtW a (pre ++ j :: k :: post) = crtW a pre + a j + a k + crtW a post := by
      rw [crtW_append, crtW_cons, crtW_cons]; ring
    have hc := crtSwapCostN_mono (V := 3 * (2 ^ crtW a (pre ++ j :: k :: post) * B))
      (show max (a j) (a k) ≤ max am am from max_le_max ham.1 ham.2)
    exact crt_step_arith (a k) P0 P1 u (crtW a pre) (crtW a post) (a j) B (swapT 6) T _ _ _ _ hW
      (by rw [← hP0, ← hP1, hpp]) hu hc

/-- One inverse walk step: pop the next axis width `aK` from `wW`, set `vU = |vacc| + |postU|`
and `uU = |preU| - |vacc| - |aK|`, exchange the axis `aK` (above) with the axis `aI` (below),
add `aK` to `vacc`, and push the entry onto `wT`. -/
def crtInvStep (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) (r : CrtReg → Fin T) :
    Pr F T Q (prime + K) U :=
  .seq (crtPopEnt (r .wW) (r .aK)) <|
  .seq (ucopy (r .vacc) (r .vU) (r .u1)) <| .seq (ucopy (r .postU) (r .vU) (r .u1)) <|
  .seq (ucopy (r .preU) (r .uU) (r .u1)) <| .seq (usub (r .vacc) (r .uU) (r .u1)) <|
  .seq (usub (r .aK) (r .uU) (r .u1)) <|
  .seq (crtSwapStep hQ ι hι hT (r .str) (r .stmp) (r .uU) (r .vU) (r .aK) (r .aI) (r .e3B) (r .tu)
    (r .u1) (r .u2)) <|
  .seq (ucopy (r .aK) (r .vacc) (r .u1)) <| .seq (uclear (r .uU)) <| .seq (uclear (r .vU))
    (crtPushEnt (r .aK) (r .wT))

lemma crt_istep_arith (aj P0 P1 v pre post ak B S6 Tn c c' V Lw : ℕ)
    (hLw : Lw = pre + aj + ak + post) (hP1 : P1 + v = post) (hP0 : P0 = pre + v + aj)
    (hc : c ≤ c') :
    2 * aj + 4 + (4 * v + 4 + (4 * P1 + 4 + (4 * P0 + 4 + (4 * v + 4 + (4 * aj + 4 +
      ((Tn + 12 * S6 + 5) * c + (6 * S6 + 10) * (pre + post + 3 * B + aj + ak + 2) + 34 * V +
        2 * Tn + 6 * S6 + 4 * pre + 4 * post + 18 * B + aj * (4 * aj + 11) + ak * (4 * ak + 11) +
        80 + (4 * aj + 4 + (2 * pre + 2 + (2 * post + 2 + (2 * aj + 4)))))))))) ≤
    (Tn + 12 * S6 + 5) * c' + (6 * S6 + 10) * (Lw + 3 * B + 2) + 34 * V + 2 * Tn + 6 * S6 +
      18 * B + Lw * (4 * Lw + 41) + 120 := by
  subst hLw hP0
  have h1 := Nat.mul_le_mul_left (Tn + 12 * S6 + 5) hc
  have h2 : (6 * S6 + 10) * (pre + post + 3 * B + aj + ak + 2) =
      (6 * S6 + 10) * (pre + aj + ak + post + 3 * B + 2) := by ring
  have h3 : aj * (4 * aj + 11) + ak * (4 * ak + 11) + 4 * pre + 4 * post + 8 * v + 4 * P1 +
      4 * (pre + v + aj) + 12 * aj + 2 * pre + 2 * post ≤
      (pre + aj + ak + post) * (4 * (pre + aj + ak + post) + 41) := by
    nlinarith
  omega

set_option maxHeartbeats 1000000 in
theorem crtInvStep_runs (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) {r : CrtReg → Fin T}
    (hr : Function.Injective r) (hrι : ∀ x j, r x ≠ ι j)
    (pre post : List (Fin d)) (j k : Fin d) (hjk : j ≠ k) (hadj : a j ≤ a k + 1 ∧ a k ≤ a j + 1)
    (am : ℕ) (ham : a j ≤ am ∧ a k ≤ am)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ x ∈ C y, x.val < 8)
    (ys : List ℕ) (v : ℕ) (R : Regs T (prime + K))
    (hstr : R (r .str) = (crtBox a (pre ++ j :: k :: post) C 0).flatten)
    (hwW : R (r .wW) = crtEnts (a j :: ys)) (hvacc : R (r .vacc) = List.replicate v tick)
    (hpost : (R (r .postU)).length + v = crtW a post)
    (hpre : (R (r .preU)).length = crtW a pre + v + a j)
    (haI : (R (r .aI)).length = a k)
    (he3 : R (r .e3B) = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (h0 : ∀ x ∈ [CrtReg.aK, .uU, .vU, .stmp, .tu, .u1, .u2], R (r x) = [])
    (hι0 : ∀ i, R (ι i) = []) :
    crtRuns body (crtInvStep hQ ι hι hT r) R
      (Function.update (Function.update (Function.update (Function.update R (r .str)
        (crtBox a (pre ++ k :: j :: post) C 0).flatten) (r .wW) (crtEnts ys)) (r .vacc)
        (List.replicate (v + a j) tick)) (r .wT) (crtEnt (a j) ++ R (r .wT)))
      (crtStepBound T (crtW a (pre ++ j :: k :: post)) B
        (2 ^ crtW a (pre ++ j :: k :: post) * B) am) := by
  have hz : ∀ x ∈ [CrtReg.aK, .uU, .vU, .stmp, .tu, .u1, .u2], R (r x) = [] := h0
  have ne : ∀ {x y : CrtReg}, x ≠ y → r x ≠ r y := fun h => hr.ne h
  obtain ⟨P0, hP0⟩ : ∃ P0, (R (r .preU)).length = P0 := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P1, (R (r .postU)).length = P1 := ⟨_, rfl⟩
  have s₁ := crtPopEnt_runs (body := body) (ne (by decide)) R (a j) ys hwW (hz .aK (by simp))
  set R₁ := Function.update (Function.update R (r .wW) (crtEnts ys)) (r .aK)
    (List.replicate (a j) tick) with hR₁
  clear_value R₁
  have f₁ : ∀ x, x ≠ r .wW → x ≠ r .aK → R₁ x = R x := fun x h1 h2 => by
    rw [hR₁, Function.update_of_ne h2, Function.update_of_ne h1]
  have v₁aK : R₁ (r .aK) = List.replicate (a j) tick := by rw [hR₁, Function.update_self]
  have v₁wW : R₁ (r .wW) = crtEnts ys := by
    rw [hR₁, Function.update_of_ne (ne (by decide)), Function.update_self]
  have u1₁ : R₁ (r .u1) = [] := by
    rw [f₁ _ (ne (by decide)) (ne (by decide))]; exact hz .u1 (by simp)
  -- vU := vacc + postU
  have s₂ := crtUcopy_runs (body := body) (a := r .vacc) (b := r .vU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₁ u1₁
  set R₂ := Function.update R₁ (r .vU) (List.replicate (R₁ (r .vacc)).length tick ++ R₁ (r .vU))
    with hR₂
  clear_value R₂
  have f₂ : ∀ x, x ≠ r .vU → R₂ x = R₁ x := fun x h => by rw [hR₂, Function.update_of_ne h]
  have s₃ := crtUcopy_runs (body := body) (a := r .postU) (b := r .vU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₂ (by rw [f₂ _ (ne (by decide)), u1₁])
  set R₃ := Function.update R₂ (r .vU) (List.replicate (R₂ (r .postU)).length tick ++ R₂ (r .vU))
    with hR₃
  clear_value R₃
  have f₃ : ∀ x, x ≠ r .vU → R₃ x = R₂ x := fun x h => by rw [hR₃, Function.update_of_ne h]
  have v₃ : R₃ (r .vU) = List.replicate (crtW a post) tick := by
    rw [hR₃, Function.update_self, hR₂, Function.update_self, Function.update_of_ne
      (ne (by decide)), f₁ _ (ne (by decide)) (ne (by decide)), f₁ _ (ne (by decide))
      (ne (by decide)), f₁ _ (ne (by decide)) (ne (by decide)), hvacc, hP1,
      hz .vU (by simp), List.length_replicate, List.append_nil, List.replicate_append_replicate]
    congr 1; omega
  -- uU := preU - vacc - aK
  have s₄ := crtUcopy_runs (body := body) (a := r .preU) (b := r .uU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₃
    (by rw [f₃ _ (ne (by decide)), f₂ _ (ne (by decide)), u1₁])
  set R₄ := Function.update R₃ (r .uU) (List.replicate (R₃ (r .preU)).length tick ++ R₃ (r .uU))
    with hR₄
  clear_value R₄
  have f₄ : ∀ x, x ≠ r .uU → R₄ x = R₃ x := fun x h => by rw [hR₄, Function.update_of_ne h]
  have g₃ : ∀ x, x ≠ CrtReg.vU → x ≠ .wW → x ≠ .aK → R₃ (r x) = R (r x) := fun x h1 h2 h3 => by
    rw [f₃ _ (ne h1), f₂ _ (ne h1), f₁ _ (ne h2) (ne h3)]
  have v₄ : R₄ (r .uU) = List.replicate P0 tick := by
    rw [hR₄, Function.update_self, g₃ .preU (by decide) (by decide) (by decide),
      g₃ .uU (by decide) (by decide) (by decide), hP0, hz .uU (by simp), List.append_nil]
  have s₅ := crtUsub_runs (body := body) (a := r .vacc) (b := r .uU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₄
    (by rw [f₄ _ (ne (by decide)), f₃ _ (ne (by decide)), f₂ _ (ne (by decide)), u1₁])
  set R₅ := Function.update R₄ (r .uU) ((R₄ (r .uU)).drop (R₄ (r .vacc)).length) with hR₅
  clear_value R₅
  have f₅ : ∀ x, x ≠ r .uU → R₅ x = R₄ x := fun x h => by rw [hR₅, Function.update_of_ne h]
  have s₆ := crtUsub_runs (body := body) (a := r .aK) (b := r .uU) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₅
    (by rw [f₅ _ (ne (by decide)), f₄ _ (ne (by decide)), f₃ _ (ne (by decide)),
          f₂ _ (ne (by decide)), u1₁])
  set R₆ := Function.update R₅ (r .uU) ((R₅ (r .uU)).drop (R₅ (r .aK)).length) with hR₆
  clear_value R₆
  have f₆ : ∀ x, x ≠ r .uU → R₆ x = R₅ x := fun x h => by rw [hR₆, Function.update_of_ne h]
  have e₆aK : R₆ (r .aK) = List.replicate (a j) tick := by
    rw [f₆ _ (ne (by decide)), f₅ _ (ne (by decide)), f₄ _ (ne (by decide)),
      f₃ _ (ne (by decide)), f₂ _ (ne (by decide)), v₁aK]
  have e₅uU : R₅ (r .uU) = List.replicate (P0 - v) tick := by
    rw [hR₅, Function.update_self, v₄, f₄ _ (ne (by decide)),
      g₃ .vacc (by decide) (by decide) (by decide), hvacc, List.length_replicate,
      List.drop_replicate]
  have e₅aK : R₅ (r .aK) = List.replicate (a j) tick := by
    rw [f₅ _ (ne (by decide)), f₄ _ (ne (by decide)), f₃ _ (ne (by decide)),
      f₂ _ (ne (by decide)), v₁aK]
  have e₆uU : R₆ (r .uU) = List.replicate (crtW a pre) tick := by
    rw [hR₆, Function.update_self, e₅uU, e₅aK, List.length_replicate, List.drop_replicate]
    congr 1; omega
  have e₆vU : R₆ (r .vU) = List.replicate (crtW a post) tick := by
    rw [f₆ _ (ne (by decide)), f₅ _ (ne (by decide)), f₄ _ (ne (by decide)), v₃]
  have e₆ : ∀ x, x ≠ CrtReg.wW → x ≠ .aK → x ≠ .vU → x ≠ .uU → R₆ (r x) = R (r x) := by
    intro x h1 h2 h3 h4
    rw [f₆ _ (ne h4), f₅ _ (ne h4), f₄ _ (ne h4), g₃ x h3 h1 h2]
  have e₆ι : ∀ i, R₆ (ι i) = R (ι i) := by
    intro i
    rw [f₆ _ (hrι _ _).symm, f₅ _ (hrι _ _).symm, f₄ _ (hrι _ _).symm, f₃ _ (hrι _ _).symm,
      f₂ _ (hrι _ _).symm, f₁ _ (hrι _ _).symm (hrι _ _).symm]
  have s₇ := crtSwapStep_runs (body := body) (a := a) hQ ι hι hT
    (str := r .str) (stmp := r .stmp) (uU := r .uU) (vU := r .vU) (aJ := r .aK) (aK := r .aI)
    (e3B := r .e3B) (tu := r .tu) (t₁ := r .u1) (t₂ := r .u2)
    (crt_nd hr [.str, .stmp, .uU, .vU, .aK, .aI, .e3B, .tu, .u1, .u2] (by decide))
    (by intro x hx i; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact (hrι _ i).symm)
    pre post j k hjk hadj.1 hadj.2 C B hB hC h8 0 R₆
    (by rw [e₆ .str (by decide) (by decide) (by decide) (by decide), hstr])
    (by rw [e₆uU, List.length_replicate])
    (by rw [e₆vU, List.length_replicate])
    (by rw [e₆aK, List.length_replicate])
    (by rw [e₆ .aI (by decide) (by decide) (by decide) (by decide), haI])
    (by rw [e₆ .e3B (by decide) (by decide) (by decide) (by decide), he3])
    (by rw [e₆ .stmp (by decide) (by decide) (by decide) (by decide)]; exact hz .stmp (by simp))
    (by rw [e₆ .tu (by decide) (by decide) (by decide) (by decide)]; exact hz .tu (by simp))
    (by rw [e₆ .u1 (by decide) (by decide) (by decide) (by decide)]; exact hz .u1 (by simp))
    (by rw [e₆ .u2 (by decide) (by decide) (by decide) (by decide)]; exact hz .u2 (by simp))
    (fun i => by rw [e₆ι, hι0])
  set R₇ := Function.update R₆ (r .str) (crtBox a (pre ++ k :: j :: post) C 0).flatten with hR₇
  clear_value R₇
  have f₇ : ∀ x, x ≠ r .str → R₇ x = R₆ x := fun x h => by rw [hR₇, Function.update_of_ne h]
  have s₈ := crtUcopy_runs (body := body) (a := r .aK) (b := r .vacc) (t := r .u1)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) R₇
    (by rw [f₇ _ (ne (by decide)), e₆ .u1 (by decide) (by decide) (by decide) (by decide)]
        exact hz .u1 (by simp))
  set R₈ := Function.update R₇ (r .vacc) (List.replicate (R₇ (r .aK)).length tick ++ R₇ (r .vacc))
    with hR₈
  clear_value R₈
  have f₈ : ∀ x, x ≠ r .vacc → R₈ x = R₇ x := fun x h => by rw [hR₈, Function.update_of_ne h]
  have s₉ := crtClear_runs (body := body) (r .uU) R₈
  have s₁₀ := crtClear_runs (body := body) (r .vU) (Function.update R₈ (r .uU) [])
  have s₁₁ := crtPushEnt_runs (body := body) (src := r .aK) (dst := r .wT) (ne (by decide))
    (Function.update (Function.update R₈ (r .uU) []) (r .vU) []) (a j)
    (by rw [Function.update_of_ne (ne (by decide)), Function.update_of_ne (ne (by decide)),
          f₈ _ (ne (by decide)), f₇ _ (ne (by decide)), e₆aK])
  refine crtRuns_mono (crtRuns_congr (crtRuns_seq s₁ (crtRuns_seq s₂ (crtRuns_seq s₃
    (crtRuns_seq s₄ (crtRuns_seq s₅ (crtRuns_seq s₆ (crtRuns_seq s₇ (crtRuns_seq s₈
      (crtRuns_seq s₉ (crtRuns_seq s₁₀ s₁₁)))))))))) ?_) ?_
  all_goals clear s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁
  · have upd : ∀ {α : Type} (f : Fin T → α) (y : CrtReg) (v : α) (x : CrtReg), x ≠ y →
        Function.update f (r y) v (r x) = f (r x) := fun f y v x h => Function.update_of_ne (ne h) _ _
    funext x
    by_cases x1 : x = r .wT
    · rw [x1]
      simp (disch := decide) only [upd, Function.update_self]
      rw [f₈ _ (ne (by decide)), f₇ _ (ne (by decide)),
        e₆ .wT (by decide) (by decide) (by decide) (by decide)]
    by_cases x2 : x = r .aK
    · rw [x2]
      simp (disch := decide) only [upd, Function.update_self]
      exact (hz .aK (by simp)).symm
    by_cases x3 : x = r .vU
    · rw [x3]
      simp (disch := decide) only [upd, Function.update_self]
      exact (hz .vU (by simp)).symm
    by_cases x4 : x = r .uU
    · rw [x4]
      simp (disch := decide) only [upd, Function.update_self]
      exact (hz .uU (by simp)).symm
    by_cases x5 : x = r .vacc
    · rw [x5]
      simp (disch := decide) only [upd, Function.update_self]
      rw [hR₈, Function.update_self, f₇ _ (ne (by decide)), e₆aK, f₇ _ (ne (by decide)),
        e₆ .vacc (by decide) (by decide) (by decide) (by decide), hvacc, List.length_replicate,
        List.replicate_append_replicate, Nat.add_comm (a j) v]
    by_cases x6 : x = r .str
    · rw [x6]
      simp (disch := decide) only [upd, Function.update_self]
      rw [f₈ _ (ne (by decide)), hR₇, Function.update_self]
    by_cases x7 : x = r .wW
    · rw [x7]
      simp (disch := decide) only [upd, Function.update_self]
      rw [f₈ _ (ne (by decide)), f₇ _ (ne (by decide)), f₆ _ (ne (by decide)),
        f₅ _ (ne (by decide)), f₄ _ (ne (by decide)), f₃ _ (ne (by decide)),
        f₂ _ (ne (by decide)), v₁wW]
    rw [Function.update_of_ne x1, Function.update_of_ne x2, Function.update_of_ne x3,
      Function.update_of_ne x4, Function.update_of_ne x1, Function.update_of_ne x5,
      Function.update_of_ne x7, Function.update_of_ne x6, f₈ _ x5, f₇ _ x6, f₆ _ x4, f₅ _ x4,
      f₄ _ x4, f₃ _ x3, f₂ _ x3, f₁ _ x7 x2]
  · have l₁ : (R₁ (r .vacc)).length = v := by
      rw [f₁ _ (ne (by decide)) (ne (by decide)), hvacc, List.length_replicate]
    have l₂ : (R₂ (r .postU)).length = P1 := by
      rw [f₂ _ (ne (by decide)), f₁ _ (ne (by decide)) (ne (by decide)), hP1]
    have l₃ : (R₃ (r .preU)).length = P0 := by
      rw [g₃ .preU (by decide) (by decide) (by decide), hP0]
    have l₄ : (R₄ (r .vacc)).length = v := by
      rw [f₄ _ (ne (by decide)), g₃ .vacc (by decide) (by decide) (by decide), hvacc,
        List.length_replicate]
    have l₅ : (R₅ (r .aK)).length = a j := by
      rw [f₅ _ (ne (by decide)), f₄ _ (ne (by decide)), f₃ _ (ne (by decide)),
        f₂ _ (ne (by decide)), v₁aK, List.length_replicate]
    have l₇ : (R₇ (r .aK)).length = a j := by
      rw [f₇ _ (ne (by decide)), e₆aK, List.length_replicate]
    have l₈ : (R₈ (r .uU)).length = crtW a pre := by
      rw [f₈ _ (ne (by decide)), f₇ _ (ne (by decide)), e₆uU, List.length_replicate]
    have l₉ : ((Function.update R₈ (r .uU) []) (r .vU)).length = crtW a post := by
      rw [Function.update_of_ne (ne (by decide)), f₈ _ (ne (by decide)), f₇ _ (ne (by decide)),
        e₆vU, List.length_replicate]
    rw [l₁, l₂, l₃, l₄, l₅, l₇, l₈, l₉, crtStepBound]
    have hW : crtW a (pre ++ j :: k :: post) = crtW a pre + a j + a k + crtW a post := by
      rw [crtW_append, crtW_cons, crtW_cons]; ring
    have hc := crtSwapCostN_mono (V := 3 * (2 ^ crtW a (pre ++ j :: k :: post) * B))
      (show max (a j) (a k) ≤ max am am from max_le_max ham.1 ham.2)
    exact crt_istep_arith (a j) P0 P1 v (crtW a pre) (crtW a post) (a k) B (swapT 6) T _ _ _ _ hW
      (by rw [← hP1, hpost]) (by rw [← hP0, hpre]) hc

/-- Four updates of four distinct registers overwrite four earlier ones. -/
lemma crt_upd4 {α : Type} (R : Fin T → α) {p q r' t : Fin T} (h1 : p ≠ q) (h2 : p ≠ r')
    (h3 : p ≠ t) (h4 : q ≠ r') (h5 : q ≠ t) (h6 : r' ≠ t) (v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄ : α) :
    Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update R p v₁) q v₂) r' v₃)
        t v₄) p w₁) q w₂) r' w₃) t w₄ =
    Function.update (Function.update (Function.update (Function.update R p w₁) q w₂) r' w₃) t w₄ := by
  funext x
  by_cases x4 : x = t
  · subst x4; simp
  by_cases x3 : x = r'
  · subst x3; simp [x4]
  by_cases x2 : x = q
  · subst x2; simp [x3, x4]
  by_cases x1 : x = p
  · subst x1; simp [x2, x3, x4]
  simp [x1, x2, x3, x4]

lemma crtRevAx_mem_lt {i : ℕ} {x : Fin d} (hx : x ∈ crtRevAx (d := d) i) : x.val < i :=
  (crt_mem_revAx x).1 hx

set_option maxHeartbeats 1000000 in
/-- The forward walk of target `i`: axis `i` moves from the top of `crtLay (i + 1)` below the
axes `i - 1, …, 0`, one exchange per entry of `wT`. -/
theorem crtFwdWalk_runs (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) {r : CrtReg → Fin T}
    (hr : Function.Injective r) (hrι : ∀ x j, r x ≠ ι j) {i : ℕ} (hi : i < d)
    (hadj : ∀ j j', a j ≤ a j' + 1) (am : ℕ) (ham : ∀ j, a j ≤ am)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ x ∈ C y, x.val < 8) (R₀ : Regs T (prime + K))
    (hstr : R₀ (r .str) = (crtBox a (crtLay (i + 1)) C 0).flatten)
    (hwT : R₀ (r .wT) = crtEnts ((crtRevAx i).map a)) (hwW : R₀ (r .wW) = [])
    (huU : R₀ (r .uU) = [])
    (hpp : (R₀ (r .preU)).length + (R₀ (r .postU)).length =
      crtPre a i + crtW a ((List.finRange d).drop (i + 1)))
    (haI : (R₀ (r .aI)).length = a ⟨i, hi⟩)
    (he3 : R₀ (r .e3B) = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (h0 : ∀ x ∈ [CrtReg.aK, .vU, .stmp, .tu, .u1, .u2], R₀ (r x) = [])
    (hι0 : ∀ i, R₀ (ι i) = []) :
    crtRuns body (crtWhile (r .wT) (crtFwdStep hQ ι hι hT r)) R₀
      (Function.update (Function.update (Function.update (Function.update R₀ (r .str)
        (crtBox a (crtLay i) C 0).flatten) (r .wT) []) (r .uU)
        (List.replicate (crtPre a i) tick)) (r .wW) (crtEnts ((crtRevAx i).reverse.map a)))
      (i * (crtStepBound T (crtPre a d) B (2 ^ crtPre a d * B) am + 2) + 2) := by
  have ne : ∀ {x y : CrtReg}, x ≠ y → r x ≠ r y := fun h => hr.ne h
  set I : Fin d := ⟨i, hi⟩ with hI
  set P := (List.finRange d).drop (i + 1) with hP
  set RA := crtRevAx (d := d) i with hRA
  have hRAlen : RA.length = i := crtRevAx_length i hi.le
  let Ψ : ℕ → Regs T (prime + K) := fun k => Function.update (Function.update (Function.update
    (Function.update R₀ (r .str) (crtBox a (crtWalkF i k hi) C 0).flatten) (r .wT)
      (crtEnts ((RA.drop k).map a))) (r .uU) (List.replicate (crtW a (RA.take k)) tick))
      (r .wW) (crtEnts ((RA.take k).reverse.map a))
  have hΨ : ∀ k, ∀ x : CrtReg, x ≠ .str → x ≠ .wT → x ≠ .uU → x ≠ .wW → Ψ k (r x) = R₀ (r x) := by
    intro k x h1 h2 h3 h4
    simp only [Ψ, Function.update_of_ne (ne h1), Function.update_of_ne (ne h2),
      Function.update_of_ne (ne h3), Function.update_of_ne (ne h4)]
  have hΨι : ∀ k j, Ψ k (ι j) = R₀ (ι j) := by
    intro k j
    simp only [Ψ, Function.update_of_ne (hrι _ j).symm]
  have hW : ∀ k, crtW a (crtWalkF i k hi) = crtPre a d := fun k => by
    rw [crtW_perm a (crtWalkF_perm hi k), crtW_crtLay]
  have hstep : ∀ k < i, (Ψ k) (r .wT) ≠ [] ∧
      crtRuns body (crtFwdStep hQ ι hι hT r) (Ψ k) (Ψ (k + 1))
        (crtStepBound T (crtPre a d) B (2 ^ crtPre a d * B) am) := by
    intro k hk
    have hkl : k < RA.length := by omega
    set x := RA[k] with hx
    have hxv : x.val < i := crtRevAx_mem_lt (List.getElem_mem hkl)
    have hxI : I ≠ x := fun h => by rw [← h] at hxv; simp [hI] at hxv
    have hdrop : RA.drop k = x :: RA.drop (k + 1) := List.drop_eq_getElem_cons hkl
    have htake : RA.take (k + 1) = RA.take k ++ [x] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hkl]; rfl
    have hwalk : crtWalkF i k hi = RA.take k ++ I :: x :: (RA.drop (k + 1) ++ P) := by
      rw [crtWalkF, ← hRA, hdrop]; rfl
    have hwalk' : crtWalkF i (k + 1) hi = RA.take k ++ x :: I :: (RA.drop (k + 1) ++ P) := by
      rw [crtWalkF, ← hRA, htake, List.append_assoc]; rfl
    have hwT' : (Ψ k) (r .wT) = crtEnts (a x :: (RA.drop (k + 1)).map a) := by
      simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.wT ≠ .wW)),
        Function.update_of_ne (ne (by decide : CrtReg.wT ≠ .uU)), Function.update_self, hdrop,
        List.map_cons]
    refine ⟨by rw [hwT']; exact crtEnts_ne_nil (List.cons_ne_nil _ _), ?_⟩
    have h := crtFwdStep_runs (body := body) a hQ ι hι hT hr hrι (RA.take k)
      (RA.drop (k + 1) ++ P) I x hxI ⟨hadj _ _, hadj _ _⟩ am ⟨ham _, ham _⟩ C B hB hC h8
      ((RA.drop (k + 1)).map a) (crtW a (RA.take k)) (Ψ k)
      (by simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.str ≠ .wW)),
            Function.update_of_ne (ne (by decide : CrtReg.str ≠ .uU)),
            Function.update_of_ne (ne (by decide : CrtReg.str ≠ .wT)), Function.update_self]
          rw [hwalk])
      hwT'
      (by simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.uU ≠ .wW)),
            Function.update_self])
      rfl
      (by rw [hΨ k .preU (by decide) (by decide) (by decide) (by decide),
            hΨ k .postU (by decide) (by decide) (by decide) (by decide), hpp, crtW_append,
            ← crtW_revAx a i hi.le, ← hRA]
          conv_lhs => rw [← List.take_append_drop k RA, hdrop]
          rw [crtW_append, crtW_cons]; ring)
      (by rw [hΨ k .aI (by decide) (by decide) (by decide) (by decide), haI])
      (by rw [hΨ k .e3B (by decide) (by decide) (by decide) (by decide), he3])
      (by intro y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
            (rw [hΨ k _ (by decide) (by decide) (by decide) (by decide)]; exact h0 _ (by simp)))
      (fun j => by rw [hΨι, hι0])
    have hW' : crtW a (RA.take k ++ I :: x :: (RA.drop (k + 1) ++ P)) = crtPre a d := by
      rw [← hwalk, hW]
    rw [hW'] at h
    refine crtRuns_congr h ?_
    have hwW' : (Ψ k) (r .wW) = crtEnts ((RA.take k).reverse.map a) := by
      simp only [Ψ, Function.update_self]
    rw [hwW']
    have e_str : (crtBox a (RA.take k ++ x :: I :: (RA.drop (k + 1) ++ P)) C 0).flatten =
        (crtBox a (crtWalkF i (k + 1) hi) C 0).flatten := by rw [hwalk']
    have e_u : crtW a (RA.take k) + a x = crtW a (RA.take (k + 1)) := by
      rw [htake, crtW_append, crtW_cons, crtW_nil, Nat.add_zero]
    have e_w : crtEnt (A := prime + K) (a x) ++ crtEnts ((RA.take k).reverse.map a) =
        crtEnts ((RA.take (k + 1)).reverse.map a) := by
      rw [htake, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, crtEnts_cons]
    simp only [Ψ]
    rw [crt_upd4 _ (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
      (ne (by decide)) (ne (by decide)), e_str, e_u, e_w]
  have h := crtWhile_runs (body := body) (p := crtFwdStep hQ ι hι hT r) (Ψ := Ψ) (N := i) hstep
    (by simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.wT ≠ .wW)),
          Function.update_of_ne (ne (by decide : CrtReg.wT ≠ .uU)), Function.update_self]
        rw [List.drop_eq_nil_of_le (by omega)]; rfl)
  have hw0 : crtWalkF i 0 hi = crtLay (i + 1) := by
    rw [crtWalkF, crtLay_succ hi, List.take_zero, List.drop_zero, List.nil_append]
  have e0 : Ψ 0 = R₀ := by
    funext y
    by_cases y1 : y = r .wW
    · rw [y1]
      simp only [Ψ, Function.update_self, List.take_zero, List.reverse_nil, List.map_nil,
        crtEnts_nil, hwW]
    by_cases y2 : y = r .uU
    · rw [y2]
      simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.uU ≠ .wW)), Function.update_self,
        List.take_zero, crtW_nil, List.replicate_zero, huU]
    by_cases y3 : y = r .wT
    · rw [y3]
      simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.wT ≠ .wW)),
        Function.update_of_ne (ne (by decide : CrtReg.wT ≠ .uU)), Function.update_self,
        List.drop_zero, hwT]
    by_cases y4 : y = r .str
    · rw [y4]
      simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.str ≠ .wW)),
        Function.update_of_ne (ne (by decide : CrtReg.str ≠ .uU)),
        Function.update_of_ne (ne (by decide : CrtReg.str ≠ .wT)), Function.update_self, hw0,
        hstr]
    simp only [Ψ, Function.update_of_ne y1, Function.update_of_ne y2, Function.update_of_ne y3,
      Function.update_of_ne y4]
  rw [e0] at h
  refine crtRuns_congr h ?_
  simp only [Ψ]
  have hwi : crtWalkF i i hi = crtLay i := by
    rw [crtWalkF, crtLay_rot hi, ← hRA, List.take_of_length_le (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  rw [hwi, List.drop_eq_nil_of_le (by omega), List.take_of_length_le (by omega), hRA,
    crtW_revAx a i hi.le]
  rfl

set_option maxHeartbeats 1000000 in
/-- The inverse walk of target `i`: axis `i` moves from below the axes `i - 1, …, 0` back to the
top, one exchange per entry of `wW` (axis `0` first); the entries return to `wT`. -/
theorem crtInvWalk_runs (hQ : swapStates crtHd crtPay crtHd_inj ≤ Q) (ι : Fin (swapT 6) → Fin T)
    (hι : Function.Injective ι) (hT : swapT 6 ≤ T) {r : CrtReg → Fin T}
    (hr : Function.Injective r) (hrι : ∀ x j, r x ≠ ι j) {i : ℕ} (hi : i < d)
    (hadj : ∀ j j', a j ≤ a j' + 1) (am : ℕ) (ham : ∀ j, a j ≤ am)
    (C : (Fin d → ℕ) → List (Fin (prime + K + 4))) (B : ℕ) (hB : 0 < B)
    (hC : ∀ y, (C y).length = B) (h8 : ∀ y, ∀ x ∈ C y, x.val < 8) (R₀ : Regs T (prime + K))
    (hstr : R₀ (r .str) = (crtBox a (crtLay i) C 0).flatten)
    (hwW : R₀ (r .wW) = crtEnts ((crtRevAx i).reverse.map a)) (hwT : R₀ (r .wT) = [])
    (hvacc : R₀ (r .vacc) = [])
    (hpre : (R₀ (r .preU)).length = crtPre a i)
    (hpost : (R₀ (r .postU)).length = crtW a ((List.finRange d).drop (i + 1)))
    (haI : (R₀ (r .aI)).length = a ⟨i, hi⟩)
    (he3 : R₀ (r .e3B) = (GrowingCounterData.advance (3 * B) []).map bitSymbol)
    (h0 : ∀ x ∈ [CrtReg.aK, .uU, .vU, .stmp, .tu, .u1, .u2], R₀ (r x) = [])
    (hι0 : ∀ i, R₀ (ι i) = []) :
    crtRuns body (crtWhile (r .wW) (crtInvStep hQ ι hι hT r)) R₀
      (Function.update (Function.update (Function.update (Function.update R₀ (r .str)
        (crtBox a (crtLay (i + 1)) C 0).flatten) (r .wW) []) (r .vacc)
        (List.replicate (crtPre a i) tick)) (r .wT) (crtEnts ((crtRevAx i).map a)))
      (i * (crtStepBound T (crtPre a d) B (2 ^ crtPre a d * B) am + 2) + 2) := by
  have ne : ∀ {x y : CrtReg}, x ≠ y → r x ≠ r y := fun h => hr.ne h
  set I : Fin d := ⟨i, hi⟩ with hI
  set P := (List.finRange d).drop (i + 1) with hP
  set RA := crtRevAx (d := d) i with hRA
  have hRAlen : RA.length = i := crtRevAx_length i hi.le
  let Ψ : ℕ → Regs T (prime + K) := fun k => Function.update (Function.update (Function.update
    (Function.update R₀ (r .str) (crtBox a (crtWalkI i k hi) C 0).flatten) (r .wW)
      (crtEnts ((RA.reverse.drop k).map a))) (r .vacc) (List.replicate (crtPre a k) tick))
      (r .wT) (crtEnts ((crtRevAx k).map a))
  have hΨ : ∀ k, ∀ x : CrtReg, x ≠ .str → x ≠ .wW → x ≠ .vacc → x ≠ .wT →
      Ψ k (r x) = R₀ (r x) := by
    intro k x h1 h2 h3 h4
    simp only [Ψ, Function.update_of_ne (ne h1), Function.update_of_ne (ne h2),
      Function.update_of_ne (ne h3), Function.update_of_ne (ne h4)]
  have hΨι : ∀ k j, Ψ k (ι j) = R₀ (ι j) := by
    intro k j
    simp only [Ψ, Function.update_of_ne (hrι _ j).symm]
  have hW : ∀ k, crtW a (crtWalkI i k hi) = crtPre a d := fun k => by
    rw [crtW_perm a (crtWalkI_perm hi k), crtW_crtLay]
  have hstep : ∀ k < i, (Ψ k) (r .wW) ≠ [] ∧
      crtRuns body (crtInvStep hQ ι hι hT r) (Ψ k) (Ψ (k + 1))
        (crtStepBound T (crtPre a d) B (2 ^ crtPre a d * B) am) := by
    intro k hk
    have hkl : i - 1 - k < RA.length := by omega
    set x := RA[i - 1 - k] with hx
    have hxk : x = ⟨k, by omega⟩ := by
      rw [hx, crtRevAx_getElem hi.le]; congr 1; omega
    have hxI : x ≠ I := fun h => by rw [hxk] at h; simp [hI, Fin.ext_iff] at h; omega
    have hrev : RA.reverse.drop k = x :: RA.reverse.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega), List.getElem_reverse]
      congr 2; omega
    have htake : RA.take (i - k) = RA.take (i - 1 - k) ++ [x] := by
      rw [show i - k = (i - 1 - k) + 1 by omega, List.take_add_one,
        List.getElem?_eq_getElem hkl]; rfl
    have hdrop : RA.drop (i - 1 - k) = x :: RA.drop (i - k) := by
      rw [List.drop_eq_getElem_cons hkl, show i - 1 - k + 1 = i - k by omega]
    have hwalk : crtWalkI i k hi = RA.take (i - 1 - k) ++ x :: I :: (RA.drop (i - k) ++ P) := by
      rw [crtWalkI, ← hRA, htake, List.append_assoc]; rfl
    have hwalk' : crtWalkI i (k + 1) hi = RA.take (i - 1 - k) ++ I :: x :: (RA.drop (i - k) ++ P) := by
      rw [crtWalkI, ← hRA, show i - (k + 1) = i - 1 - k by omega, hdrop]; rfl
    have hwW' : (Ψ k) (r .wW) = crtEnts (a x :: (RA.reverse.drop (k + 1)).map a) := by
      simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.wW ≠ .wT)),
        Function.update_of_ne (ne (by decide : CrtReg.wW ≠ .vacc)), Function.update_self, hrev,
        List.map_cons]
    refine ⟨by rw [hwW']; exact crtEnts_ne_nil (List.cons_ne_nil _ _), ?_⟩
    have hdk : RA.drop (i - k) = crtRevAx k := crtRevAx_drop (by omega) hi.le
    have h := crtInvStep_runs (body := body) a hQ ι hι hT hr hrι (RA.take (i - 1 - k))
      (RA.drop (i - k) ++ P) x I hxI ⟨hadj _ _, hadj _ _⟩ am ⟨ham _, ham _⟩ C B hB hC h8
      ((RA.reverse.drop (k + 1)).map a) (crtPre a k) (Ψ k)
      (by simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.str ≠ .wT)),
            Function.update_of_ne (ne (by decide : CrtReg.str ≠ .vacc)),
            Function.update_of_ne (ne (by decide : CrtReg.str ≠ .wW)), Function.update_self]
          rw [hwalk])
      hwW'
      (by simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.vacc ≠ .wT)),
            Function.update_self])
      (by rw [hΨ k .postU (by decide) (by decide) (by decide) (by decide), hpost, crtW_append,
            hdk, crtW_revAx a k (by omega)]; ring)
      (by rw [hΨ k .preU (by decide) (by decide) (by decide) (by decide), hpre, hxk,
            ← crtW_revAx_take a (show k + 1 ≤ i by omega) hi.le, ← hRA,
            show i - (k + 1) = i - 1 - k by omega, crtPre_succ a (show k < d by omega)]
          ring)
      (by rw [hΨ k .aI (by decide) (by decide) (by decide) (by decide), haI])
      (by rw [hΨ k .e3B (by decide) (by decide) (by decide) (by decide), he3])
      (by intro y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            (rw [hΨ k _ (by decide) (by decide) (by decide) (by decide)]; exact h0 _ (by simp)))
      (fun j => by rw [hΨι, hι0])
    have hW' : crtW a (RA.take (i - 1 - k) ++ x :: I :: (RA.drop (i - k) ++ P)) = crtPre a d := by
      rw [← hwalk, hW]
    rw [hW'] at h
    refine crtRuns_congr h ?_
    have hwT' : (Ψ k) (r .wT) = crtEnts ((crtRevAx k).map a) := by
      simp only [Ψ, Function.update_self]
    rw [hwT']
    have e_str : (crtBox a (RA.take (i - 1 - k) ++ I :: x :: (RA.drop (i - k) ++ P)) C 0).flatten =
        (crtBox a (crtWalkI i (k + 1) hi) C 0).flatten := by rw [hwalk']
    have e_v : crtPre a k + a x = crtPre a (k + 1) := by
      rw [crtPre_succ a (show k < d by omega), hxk]
    have e_w : crtEnt (A := prime + K) (a x) ++ crtEnts ((crtRevAx k).map a) =
        crtEnts ((crtRevAx (k + 1)).map a) := by
      rw [crtRevAx_succ (show k < d by omega), List.map_cons, crtEnts_cons, hxk]
    simp only [Ψ]
    rw [crt_upd4 _ (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
      (ne (by decide)) (ne (by decide)), e_str, e_v, e_w]
  have h := crtWhile_runs (body := body) (p := crtInvStep hQ ι hι hT r) (Ψ := Ψ) (N := i) hstep
    (by simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.wW ≠ .wT)),
          Function.update_of_ne (ne (by decide : CrtReg.wW ≠ .vacc)), Function.update_self]
        rw [List.drop_eq_nil_of_le (by simp; omega)]; rfl)
  have hw0 : crtWalkI i 0 hi = crtLay i := by
    rw [crtWalkI, crtLay_rot hi, ← hRA, Nat.sub_zero, List.take_of_length_le (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  have e0 : Ψ 0 = R₀ := by
    funext y
    by_cases y1 : y = r .wT
    · rw [y1]
      simp only [Ψ, Function.update_self, crtRevAx_zero, List.map_nil, crtEnts_nil, hwT]
    by_cases y2 : y = r .vacc
    · rw [y2]
      simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.vacc ≠ .wT)),
        Function.update_self, crtPre_zero, List.replicate_zero, hvacc]
    by_cases y3 : y = r .wW
    · rw [y3]
      simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.wW ≠ .wT)),
        Function.update_of_ne (ne (by decide : CrtReg.wW ≠ .vacc)), Function.update_self,
        List.drop_zero, hwW]
    by_cases y4 : y = r .str
    · rw [y4]
      simp only [Ψ, Function.update_of_ne (ne (by decide : CrtReg.str ≠ .wT)),
        Function.update_of_ne (ne (by decide : CrtReg.str ≠ .vacc)),
        Function.update_of_ne (ne (by decide : CrtReg.str ≠ .wW)), Function.update_self, hw0,
        hstr]
    simp only [Ψ, Function.update_of_ne y1, Function.update_of_ne y2, Function.update_of_ne y3,
      Function.update_of_ne y4]
  rw [e0] at h
  refine crtRuns_congr h ?_
  simp only [Ψ]
  have hwi : crtWalkI i i hi = crtLay (i + 1) := by
    rw [crtWalkI, crtLay_succ hi, ← hRA, Nat.sub_self, List.take_zero, List.drop_zero,
      List.nil_append]
  rw [hwi, List.drop_eq_nil_of_le (by simp; omega)]
  rfl

end

end Step

end IntegerMultBounds.MathlibTM2.Fast
