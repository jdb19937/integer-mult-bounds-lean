module

public import IntegerMultBounds.MathlibTM2.Host.IndexCode
public import IntegerMultBounds.MathlibTM2.Node.Rect

/-!
# Moving records by a class-monotone permutation

`classMove` routes the records of `src` by an input code onto `dst d`, reverses each onto
`aux d`, merges them by an output code onto `out` and moves `out` back onto `src`, as the
rotation pass of `IntegerMultBounds.MathlibTM2.Node.RotPass` does with its automata. The codes
are computed by programs satisfying `CodeSpec` over one index state.

`classMove_exec`: if a permutation `π` of the `M` records sends every record to an output index
whose output code is its input code (`hcode`) and keeps the order of the records of each input
code (`hmono`), then `src` ends holding the records moved by `π` (`moveRecs π`), and every other
register ends as it started. The counter is reset after the routing and after the merge.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
open IntegerMultBounds.MathlibTM2.Node (moveRecs length_moveRecs)

variable {T Q A : ℕ} {U : Type} {P : Type} (body : P → Pr P T Q A U) {nf nd : ℕ}

/-- A permutation of `Fin M` as a map of `ℕ`, the identity from `M` on. -/
def permFun {M : ℕ} (π : Equiv.Perm (Fin M)) (i : ℕ) : ℕ := if h : i < M then π ⟨i, h⟩ else i

lemma permFun_of_lt {M : ℕ} (π : Equiv.Perm (Fin M)) {i : ℕ} (h : i < M) :
    permFun π i = π ⟨i, h⟩ := by simp [permFun, h]

lemma permFun_lt {M : ℕ} (π : Equiv.Perm (Fin M)) {i : ℕ} (h : i < M) : permFun π i < M := by
  rw [permFun_of_lt π h]; exact (π _).isLt

lemma permFun_symm {M : ℕ} (π : Equiv.Perm (Fin M)) {i : ℕ} (h : i < M) :
    permFun π.symm (permFun π i) = i := by
  rw [permFun_of_lt π h, permFun_of_lt π.symm (π _).isLt]
  simp

lemma permFun_symm' {M : ℕ} (π : Equiv.Perm (Fin M)) {i : ℕ} (h : i < M) :
    permFun π (permFun π.symm i) = i := by
  have := permFun_symm π.symm h
  rwa [Equiv.symm_symm] at this

section Lists

variable {α : Type}

lemma length_flatten_of {B : ℕ} : ∀ (l : List (List α)), (∀ r ∈ l, r.length = B) →
    l.flatten.length = l.length * B
  | [], _ => by simp
  | r :: l, h => by
    rw [List.flatten_cons, List.length_append, h r List.mem_cons_self,
      length_flatten_of l (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')), List.length_cons]
    ring

lemma blk_flatten {B : ℕ} : ∀ (l : List (List α)), (∀ r ∈ l, r.length = B) →
    ∀ k, blk l.flatten B k = l.getD k []
  | [], _, k => by simp [blk]
  | r :: l, h, k => by
    have hr := h r List.mem_cons_self
    cases k with
    | zero => simp [blk, List.take_left' hr]
    | succ k =>
      have := blk_flatten l (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) k
      rw [List.getD_cons_succ, ← this, List.flatten_cons]
      simp only [blk]
      rw [List.drop_append, List.drop_eq_nil_of_le (by rw [hr]; nlinarith),
        List.nil_append, hr, show (k + 1) * B - B = k * B by rw [Nat.add_one_mul]; omega]

lemma flatten_moveRecs {M B : ℕ} (π : Equiv.Perm (Fin M)) (l : List (List α))
    (hl : ∀ r ∈ l, r.length = B) :
    (moveRecs π l).flatten =
      (List.range M).flatMap (fun j => blk l.flatten B (permFun π.symm j)) := by
  rw [List.flatMap_def]
  congr 1
  apply List.ext_getElem (by simp [length_moveRecs])
  intro j h1 h2
  have hj : j < M := by simpa using h2
  simp [moveRecs, permFun_of_lt _ hj, blk_flatten l hl]

lemma length_flatten_moveRecs {M B : ℕ} (π : Equiv.Perm (Fin M)) (l : List (List α))
    (hl : l.length = M) (hlB : ∀ r ∈ l, r.length = B) :
    (moveRecs π l).flatten.length = M * B := by
  rw [length_flatten_of _ (B := B), length_moveRecs]
  intro r hr
  simp only [moveRecs, List.mem_ofFn] at hr
  obtain ⟨j, rfl⟩ := hr
  have hj : (π.symm j : ℕ) < l.length := by rw [hl]; exact (π.symm j).isLt
  rw [List.getD_eq_getElem _ _ hj]
  exact hlB _ (List.getElem_mem hj)

end Lists

/-- A code-matching bijection preserves the count of each code. -/
lemma idxCount_eq_of_perm {M : ℕ} (cin cout : ℕ → Fin nd) (π : Equiv.Perm (Fin M))
    (hcode : ∀ i < M, cout (0 + permFun π i) = cin (0 + i)) (d : Fin nd) :
    idxCount cout 0 M d = idxCount cin 0 M d := by
  unfold idxCount
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  have hperm : ((List.range M).map (permFun π)).Perm (List.range M) := by
    rw [List.perm_ext_iff_of_nodup (List.nodup_range.map_on ?_) List.nodup_range]
    · intro a
      simp only [List.mem_map, List.mem_range]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact permFun_lt π hx
      · intro ha; exact ⟨permFun π.symm a, permFun_lt π.symm ha, permFun_symm' π ha⟩
    · intro x hx y hy hxy
      rw [List.mem_range] at hx hy
      rw [← permFun_symm π hx, ← permFun_symm π hy, hxy]
  rw [← hperm.countP_eq, List.countP_map]
  apply List.countP_congr
  intro x hx
  rw [List.mem_range] at hx
  have h := hcode x hx
  simp only [Nat.zero_add] at h
  simp [h]

lemma idxCount_sum (code : ℕ → Fin nd) : ∀ (m j : ℕ), ∑ d, idxCount code j m d = m := by
  intro m
  induction m with
  | zero => intro j; simp [idxCount]
  | succ m ih =>
    intro j
    simp only [idxCount_succ, Finset.sum_add_distrib, ih]
    rw [Finset.sum_ite_eq]
    simp [Nat.add_comm]

/-- Route by the input code, reverse each class, reset the counter, merge by the output code,
reset the counter, move back. -/
def classMove (cpIn cpOut : Pr P T Q A U) (selIn selOut : ℕ → Fin nd) (src : Fin T)
    (dst aux : Fin nd → Fin T) (out ctr tmp cnt ctmp : Fin T) (cf : Fin nf → Fin T) (st : Fin T) :
    Pr P T Q A U :=
  .seq (routeIdxC cpIn selIn src dst ctr tmp cf st)
    (.seq (revEach dst aux) (.seq (resetFields cf tmp)
      (.seq (mergeIdxC cpOut selOut aux out ctr tmp cnt ctmp cf st)
        (.seq (resetFields cf tmp) (moveR out src id)))))

/-- Registers of `classMove`: the stream registers, pairwise distinct and outside the index
registers `Y`. -/
structure MoveRegs (Y : Fin T → Prop) (src : Fin T) (dst aux : Fin nd → Fin T)
    (out ctr tmp cnt ctmp : Fin T) : Prop where
  regs : [src, out, ctr, tmp, cnt, ctmp].Nodup
  dst_regs : ∀ d, dst d ∉ [src, out, ctr, tmp, cnt, ctmp]
  aux_regs : ∀ d, aux d ∉ [src, out, ctr, tmp, cnt, ctmp]
  dst_aux : ∀ d d', dst d ≠ aux d'
  dst_inj : Function.Injective dst
  aux_inj : Function.Injective aux
  idx : ∀ k, Y k → k ∉ [src, out, ctr, tmp, cnt, ctmp]
  idx_dst : ∀ d, ¬ Y (dst d)
  idx_aux : ∀ d, ¬ Y (aux d)

/-- The step bound of `classMove`. -/
def classMoveCost (cIn cOut M B : ℕ) (len : Fin nf → ℕ) : ℕ :=
  M * (idxStepCost cIn B len + 1) + 2 + (2 * (M * B) + 2 * nd + 1) +
    (M * (idxStepCost cOut B len + 3) + 4) + (2 * (M * B) + 2) +
    2 * (4 * (∑ f, len f) + 4 * nf + 1)

/-- **Moving records by a class-monotone permutation.** -/
theorem classMove_exec {cpIn cpOut : Pr P T Q A U} {cf : Fin nf → Fin T} {len : Fin nf → ℕ}
    {st : Fin T} {Y : Fin T → Prop} {Inv : (Fin T → List (Fin (A + 4))) → ℕ → Prop}
    {selIn selOut : ℕ → Fin nd} {cin cout : ℕ → Fin nd} {cIn cOut : ℕ}
    (hin : CodeSpec body cpIn cf len st Y Inv selIn cin cIn)
    (hout : CodeSpec body cpOut cf len st Y Inv selOut cout cOut)
    {src : Fin T} {dst aux : Fin nd → Fin T} {out ctr tmp cnt ctmp : Fin T}
    (hr : MoveRegs Y src dst aux out ctr tmp cnt ctmp)
    {M B : ℕ} (hB : 1 ≤ B) (π : Equiv.Perm (Fin M))
    (hcode : ∀ i < M, cout (0 + permFun π i) = cin (0 + i))
    (hmono : ∀ i < M, ∀ i' < M, cin (0 + i) = cin (0 + i') → i < i' → permFun π i < permFun π i')
    {l : List (List (Fin (A + 4)))} (hl : l.length = M) (hlB : ∀ r ∈ l, r.length = B)
    {cc kk : List (Fin (A + 4))} (hcB : cc.length = B) (hkk : kk.length = M)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = l.flatten) (hctr : S.R ctr = cc) (hcnt : S.R cnt = kk)
    (htmp : S.R tmp = []) (hctmp : S.R ctmp = []) (houtR : S.R out = [])
    (hdst : ∀ d, S.R (dst d) = []) (haux : ∀ d, S.R (aux d) = []) (hI : Inv S.R 0) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ classMoveCost (nd := nd) cIn cOut M B len ∧
      Exec body (classMove cpIn cpOut selIn selOut src dst aux out ctr tmp cnt ctmp cf st)
        (mk v S) m
        (mk v' { S with R := Function.update S.R src (moveRecs π l).flatten }) := by
  obtain ⟨hreg, hdr, har, hda, hdinj, hainj, hidx, hYd, hYa⟩ := hr
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hreg hdr har
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, ⟨c1, c2, c3⟩, ⟨d1, d2⟩, e1⟩ := hreg
  have hY : ∀ k, Y k → k ≠ src ∧ k ≠ out ∧ k ≠ ctr ∧ k ≠ tmp ∧ k ≠ cnt ∧ k ≠ ctmp := by
    intro k hk
    have := hidx k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this
  have hYs : ¬ Y src := fun h => (hY _ h).1 rfl
  have hYo : ¬ Y out := fun h => (hY _ h).2.1 rfl
  have hYc : ¬ Y ctr := fun h => (hY _ h).2.2.1 rfl
  have hYt : ¬ Y tmp := fun h => (hY _ h).2.2.2.1 rfl
  have hYn : ¬ Y cnt := fun h => (hY _ h).2.2.2.2.1 rfl
  have hYm : ¬ Y ctmp := fun h => (hY _ h).2.2.2.2.2 rfl
  have hcf : ∀ f k, ¬ Y k → cf f ≠ k := fun f k hk e => hk (e ▸ hin.cf_Y f)
  have hw : l.flatten.length = M * B := by rw [length_flatten_of l hlB, hl]
  -- routing
  obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, hsrc₁, hdst₁, hI₁, hoth₁⟩ :=
    routeIdxC_exec body hin src dst ctr tmp hYs hYc hYt hYd (by simp [a2, a3, c1])
      (fun d => by simp [(hdr d).1, (hdr d).2.2.1, (hdr d).2.2.2.1]) hdinj hB hw hcB v S hsrc
      hctr htmp hI
  have hk₁ : ∀ k, k ≠ src → (∀ d, dst d ≠ k) → ¬ Y k → R₁ k = S.R k :=
    fun k h1 h2 h3 => hoth₁ k h1 h2 (fun f => hcf f k h3)
  -- reversing
  obtain ⟨v₂, R₂, hu₂, he₂, hds₂, hoth₂⟩ := revList_exec body dst aux hda hdinj hainj
    (List.finRange nd) (List.nodup_finRange nd) v₁ { S with R := R₁ }
  have hk₂ : ∀ k, (∀ d, k ≠ dst d) → (∀ d, k ≠ aux d) → R₂ k = R₁ k :=
    fun k h1 h2 => hoth₂ k (fun d _ => ⟨h1 d, h2 d⟩)
  have hk₁₂ : ∀ k, k ≠ src → (∀ d, k ≠ dst d) → (∀ d, k ≠ aux d) → ¬ Y k → R₂ k = S.R k :=
    fun k h1 h2 h3 h4 => (hk₂ k h2 h3).trans (hk₁ k h1 (fun d e => h2 d e.symm) h4)
  have haux₂ : ∀ d, R₂ (aux d) = blocksIdx l.flatten B M cin 0 d ++ [] := by
    intro d
    rw [(hds₂ d (List.mem_finRange d)).2]
    show (R₁ (dst d)).reverse ++ R₁ (aux d) = _
    rw [hdst₁, hdst, hk₁ _ (har d).1 (fun d' => hda d' d) (hYa d), haux]
    simp
  have hI₂M : Inv R₂ (0 + M) := hin.frame R₁ R₂ _ hI₁ (fun k hk => hk₂ k
    (fun d e => hYd d (e ▸ hk)) (fun d e => hYa d (e ▸ hk)))
  have hcftmp : ∀ f, cf f ≠ tmp := fun f => hcf f tmp hYt
  have htmp₂ : R₂ tmp = [] := by
    rw [hk₁₂ _ (Ne.symm a3) (fun d e => (hdr d).2.2.2.1 e.symm) (fun d e => (har d).2.2.2.1 e.symm)
      hYt, htmp]
  obtain ⟨v₂', R₂', hu₂', he₂', hcf₂', hoth₂'⟩ := resetFields_exec body cf hin.cf_inj tmp hcftmp
    len v₂ { S with R := R₂ } htmp₂ (fun f => by
      show (R₂ (cf f)).length = _; rw [hin.digits R₂ _ hI₂M f]; simp)
  have hdig0 : ∀ f, digit len f 0 = 0 := fun f => by simp [digit]
  have hI₂ : Inv R₂' 0 := hin.reidx R₂ R₂' _ 0 hI₂M (fun f => by rw [hcf₂' f, hdig0]) hoth₂'
  have hk₂' : ∀ k, ¬ Y k → R₂' k = R₂ k := fun k hk => hoth₂' k fun f e => hcf f k hk e.symm
  have hsum₂ : ((List.finRange nd).map fun d => 2 * ({ S with R := R₁ }.R (dst d)).length +
      2).sum = 2 * (M * B) + 2 * nd := by
    simp only [hdst₁, hdst, List.append_nil, List.length_reverse]
    rw [← Fin.sum_univ_def]
    simp only [length_blocksIdx _ _ _ _ _ _ hw]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, idxCount_sum]
    simp [Nat.mul_comm]
  -- merging
  obtain ⟨v₃, R₃, m₃, hu₃, hm₃, he₃, hout₃, haux₃, hI₃, hoth₃⟩ :=
    mergeIdxC_exec body hout aux out ctr tmp cnt ctmp hYa hYo hYc hYt hYn hYm
      (by simp [b1, b2, b3, b4, c1, c2, c3, d1, d2, e1])
      (fun d => by
        obtain ⟨_, x2, x3, x4, x5, x6⟩ := har d
        simp [x2, x3, x4, x5, x6]) hainj hcB hkk
      (fun d => blocksIdx l.flatten B M cin 0 d ++ [])
      (fun d => by
        rw [List.length_append, length_blocksIdx _ _ _ _ _ _ hw, List.length_nil, Nat.add_zero,
          idxCount_eq_of_perm cin cout π hcode d])
      v₂' { S with R := R₂' } (fun d => by
        show R₂' (aux d) = _; rw [hk₂' _ (hYa d), haux₂])
      (by show R₂' ctr = cc; rw [hk₂' _ hYc, hk₁₂ _ (Ne.symm a2) (fun d e => (hdr d).2.2.1 e.symm)
        (fun d e => (har d).2.2.1 e.symm) hYc, hctr])
      (by show R₂' tmp = []; rw [hk₂' _ hYt, htmp₂])
      (by show R₂' cnt = kk; rw [hk₂' _ hYn, hk₁₂ _ (Ne.symm a4) (fun d e => (hdr d).2.2.2.2.1 e.symm)
        (fun d e => (har d).2.2.2.2.1 e.symm) hYn, hcnt])
      (by show R₂' ctmp = []; rw [hk₂' _ hYm, hk₁₂ _ (Ne.symm a5) (fun d e => (hdr d).2.2.2.2.2 e.symm)
        (fun d e => (har d).2.2.2.2.2 e.symm) hYm, hctmp]) hI₂
  have hmerge := mergeIdxList_perm B M l.flatten hw cin cout 0 0 (permFun π) (permFun π.symm)
    (fun _ h => permFun_lt π h) (fun _ h => permFun_lt π.symm h) (fun _ h => permFun_symm π h)
    (fun _ h => permFun_symm' π h) hcode hmono (fun _ => [])
  rw [hmerge, ← flatten_moveRecs π l hlB] at hout₃ haux₃
  set res := (moveRecs π l).flatten with hres
  have hout₂ : R₂ out = [] := by
    rw [hk₁₂ _ (Ne.symm a1) (fun d e => (hdr d).2.1 e.symm) (fun d e => (har d).2.1 e.symm) hYo,
      houtR]
  have hsrc₂ : R₂ src = [] := by
    rw [hk₂ _ (fun d e => (hdr d).1 e.symm) (fun d e => (har d).1 e.symm), hsrc₁]
  have hout₃' : R₃ out = res.reverse := by
    rw [hout₃]; show _ ++ R₂' out = _; rw [hk₂' _ hYo, hout₂, List.append_nil]
  have hsrc₃ : R₃ src = [] := by
    rw [hoth₃ _ a1 (fun d e => (har d).1 e) (fun f => hcf f _ hYs)]
    exact (hk₂' _ hYs).trans hsrc₂
  -- resetting
  have htmp₃ : R₃ tmp = [] := by
    rw [hoth₃ _ (Ne.symm b2) (fun d e => (har d).2.2.2.1 e) (fun f => hcf f _ hYt)]
    exact (hk₂' _ hYt).trans htmp₂
  obtain ⟨v₃', R₃', hu₃', he₃', hcf₃', hoth₃'⟩ := resetFields_exec body cf hin.cf_inj tmp hcftmp
    len v₃ { S with R := R₃ } htmp₃ (fun f => by
      show (R₃ (cf f)).length = _; rw [hout.digits R₃ _ hI₃ f]; simp)
  have hk₃' : ∀ k, ¬ Y k → R₃' k = R₃ k := fun k hk => hoth₃' k fun f e => hcf f k hk e.symm
  -- moving back
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body out src (Ne.symm a1) id v₃' { S with R := R₃' }
  have hfin : movedR R₃' out src id (R₃' out) = Function.update S.R src res := by
    funext k
    by_cases hk1 : k = src
    · subst hk1
      simp [movedR, hk₃' _ hYo, hk₃' _ hYs, hout₃', hsrc₃]
    by_cases hk2 : k = out
    · subst hk2
      simp [movedR, Ne.symm a1, houtR]
    simp only [movedR, Function.update_of_ne hk1, Function.update_of_ne hk2]
    by_cases hk4 : ∃ f, k = cf f
    · obtain ⟨f, rfl⟩ := hk4
      rw [hcf₃' f, hin.digits S.R 0 hI f, hdig0]
    simp only [not_exists] at hk4
    rw [hoth₃' k hk4]
    show R₃ k = S.R k
    by_cases hk3 : ∃ d, k = aux d
    · obtain ⟨d, rfl⟩ := hk3
      rw [haux₃, haux]
    simp only [not_exists] at hk3
    rw [hoth₃ k hk2 (fun d e => hk3 d e.symm) (fun f e => hk4 f e.symm)]
    show R₂' k = S.R k
    rw [hoth₂' k hk4]
    show R₂ k = S.R k
    by_cases hk5 : ∃ d, k = dst d
    · obtain ⟨d, rfl⟩ := hk5
      rw [(hds₂ d (List.mem_finRange d)).1, hdst]
    simp only [not_exists] at hk5
    rw [hoth₂ k (fun d _ => ⟨hk5 d, hk3 d⟩)]
    exact hoth₁ k hk1 (fun d e => hk5 d e.symm) (fun f e => hk4 f e.symm)
  refine ⟨v₄, m₁ + (((List.finRange nd).map fun d => 2 * ({ S with R := R₁ }.R (dst d)).length +
      2).sum + 1 + ((4 * (∑ f, len f) + 4 * nf + 1) + (m₃ + ((4 * (∑ f, len f) + 4 * nf + 1) +
      (2 * (R₃' out).length + 2))))), by rw [hu₄, hu₃', hu₃, hu₂', hu₂, hu₁], ?_,
    Exec.cast (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₃' he₄)))))
      rfl (by rw [hfin])⟩
  rw [hsum₂, hk₃' _ hYo, hout₃', List.length_reverse, hres, length_flatten_moveRecs π l hl hlB]
  unfold classMoveCost
  omega

end IntegerMultBounds.MathlibTM2.Host
