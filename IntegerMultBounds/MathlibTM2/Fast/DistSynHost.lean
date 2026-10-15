module

public import IntegerMultBounds.MathlibTM2.Fast.DistSynTbl
public import IntegerMultBounds.MathlibTM2.Fast.TableLoad
public import IntegerMultBounds.MathlibTM2.Fast.DistBase

/-!
# The parameter wires of the synthetic transforms: host primitives

The host-level contract `dsyRuns body p R R' b` (from the register file `R`, the program `p`
reaches the file `R'` within `b` steps, the input, output and left stacks unchanged) and its
instances for the primitives used by the wire machine (`Fast/DistSyn.lean`):

* unary copies, clears, pushes (`dsyPush`), the unary product `dsyMulU a b dst t t'`
  (`dst` gains `|a| |b|` ticks);
* the counted transfer `dsyXfer cnt t src dst` (`|cnt|` symbols of `src` move onto `dst`);
* the table machine: `dsyRuns_of_tbl` (a `tblRuns` contract on a layout `rg`, as a file
  `dsOv rg R ρ'`), the loads `tblLoad1`, the zeroing `dsyZeroVars` of the variables, the
  clearing `dsyClearL` of a list of layout registers;
* the drain `dsyDrain a out`: the pair symbols of `a` move onto `out` as ticks and `bitSymbol
  false` (`dsyH`), and `dsyPhase rg c out`: a table program followed by the drain of `acc`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-! ### The contract -/

/-- From the file `R`, `p` reaches the file `R'` within `b` steps; `inp`, `out`, the left stacks
and `user` unchanged. -/
def dsyRuns (body : P → Pr P T Q A U) (p : Pr P T Q A U) (R R' : Regs T A) (b : ℕ) : Prop :=
  ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R → ∃ v' S' m, v'.user = v.user ∧ m ≤ b ∧
    Exec body p (mk v S) m (mk v' S') ∧ S'.R = R' ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L

theorem dsyRuns.seq {p q : Pr P T Q A U} {R₁ R₂ R₃ : Regs T A} {b₁ b₂ : ℕ}
    (h₁ : dsyRuns body p R₁ R₂ b₁) (h₂ : dsyRuns body q R₂ R₃ b₂) :
    dsyRuns body (.seq p q) R₁ R₃ (b₁ + b₂) := by
  intro v S hS
  obtain ⟨v₁, S₁, m₁, hu₁, hm₁, he₁, hR₁, hi₁, ho₁, hL₁⟩ := h₁ v S hS
  obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hR₂, hi₂, ho₂, hL₂⟩ := h₂ v₁ S₁ hR₁
  exact ⟨v₂, S₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hR₂, hi₂.trans hi₁,
    ho₂.trans ho₁, hL₂.trans hL₁⟩

theorem dsyRuns.mono {p : Pr P T Q A U} {R R' : Regs T A} {b b' : ℕ}
    (h : dsyRuns body p R R' b) (hb : b ≤ b') : dsyRuns body p R R' b' := by
  intro v S hS
  obtain ⟨v', S', m, hu, hm, he, hR, hi, ho, hL⟩ := h v S hS
  exact ⟨v', S', m, hu, hm.trans hb, he, hR, hi, ho, hL⟩

theorem dsyRuns.congr {p : Pr P T Q A U} {R R' R'' : Regs T A} {b : ℕ}
    (h : dsyRuns body p R R' b) (e : R' = R'') : dsyRuns body p R R'' b := e ▸ h

theorem dsyRuns.congr_left {p : Pr P T Q A U} {R R₀ R' : Regs T A} {b : ℕ}
    (h : dsyRuns body p R R' b) (e : R = R₀) : dsyRuns body p R₀ R' b := e ▸ h

/-- A contract from an exact execution lemma. -/
theorem dsyRuns.of_exec {p : Pr P T Q A U} (R : Regs T A) (F : Regs T A → Regs T A)
    (c : Regs T A → ℕ)
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R → ∃ v' : HS T Q A U, v'.user = v.user ∧
      Exec body p (mk v S) (c S.R) (mk v' { S with R := F S.R })) :
    dsyRuns body p R (F R) (c R) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := h v S hS
  subst hS
  exact ⟨v', _, _, hu, le_rfl, he, rfl, rfl, rfl, rfl⟩

/-- A contract from a bounded execution lemma. -/
theorem dsyRuns.of_exec_le {p : Pr P T Q A U} (R : Regs T A) (F : Regs T A → Regs T A)
    (c : Regs T A → ℕ)
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R → ∃ (v' : HS T Q A U) (m : ℕ),
      v'.user = v.user ∧ m ≤ c S.R ∧ Exec body p (mk v S) m (mk v' { S with R := F S.R })) :
    dsyRuns body p R (F R) (c R) := by
  intro v S hS
  obtain ⟨v', m, hu, hm, he⟩ := h v S hS
  subst hS
  exact ⟨v', _, m, hu, hm, he, rfl, rfl, rfl, rfl⟩

/-! ### Unary primitives -/

theorem dsyRuns_ucopy {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (R : Regs T A)
    (ht : R t = []) :
    dsyRuns body (ucopy a b t) R (Function.update R b (List.replicate (R a).length tick ++ R b))
      (4 * (R a).length + 4) :=
  dsyRuns.of_exec R (fun R => Function.update R b (List.replicate (R a).length tick ++ R b))
    (fun R => 4 * (R a).length + 4) fun v S hS =>
    ucopy_exec body hab hat hbt v S (by rw [hS]; exact ht)

theorem dsyRuns_uclear (a : Fin T) (R : Regs T A) :
    dsyRuns body (uclear a) R (Function.update R a []) (2 * (R a).length + 2) :=
  dsyRuns.of_exec R (fun R => Function.update R a []) (fun R => 2 * (R a).length + 2)
    fun v S _ => uclear_exec body a v S

theorem dsyRuns_bclear (a : Fin T) (R : Regs T A) :
    dsyRuns body (bclear a) R (Function.update R a []) (2 * (R a).length + 2) :=
  dsyRuns.of_exec R (fun R => Function.update R a []) (fun R => 2 * (R a).length + 2)
    fun v S _ => by
      obtain ⟨v', hu, -, he⟩ := bclear_exec body a v S
      exact ⟨v', hu, he⟩

/-- Push `c` copies of `y` onto `j`. -/
def dsyPush (j : Fin T) (y : Fin (A + 4)) (c : ℕ) : Pr P T Q A U :=
  .act (pushN j (fun _ => y) c .done)

theorem dsyRuns_push (j : Fin T) (y : Fin (A + 4)) (c : ℕ) (R : Regs T A) :
    dsyRuns body (dsyPush j y c) R (Function.update R j (List.replicate c y ++ R j)) 1 := by
  intro v S hS
  subst hS
  have := Exec.act (body := body) (pushN j (fun _ => y) c .done) (mk v S)
  rw [pushN_run, run_done] at this
  exact ⟨v, _, 1, rfl, le_rfl, this, rfl, rfl, rfl, rfl⟩

theorem dsyRuns_bcopy {a c t₁ t₂ : Fin T} (hd : [a, c, t₁, t₂].Nodup) (R : Regs T A)
    (h₁ : R t₁ = []) (h₂ : R t₂ = []) :
    dsyRuns body (bcopy a c t₁ t₂) R (Function.update R c (R a ++ R c)) (6 * (R a).length + 6) :=
  dsyRuns.of_exec R (fun R => Function.update R c (R a ++ R c)) (fun R => 6 * (R a).length + 6)
    fun v S hS => bcopy_exec body hd v S (by rw [hS]; exact h₁) (by rw [hS]; exact h₂)

theorem dsyRuns_moveR {i j : Fin T} (hij : i ≠ j) (R : Regs T A) :
    dsyRuns body (moveR i j id) R
      (Function.update (Function.update R i []) j ((R i).reverse ++ R j)) (2 * (R i).length + 2) :=
  dsyRuns.of_exec R (fun R => Function.update (Function.update R i []) j ((R i).reverse ++ R j))
    (fun R => 2 * (R i).length + 2) fun v S _ => by
      obtain ⟨v', hu, he⟩ := moveR_exec body i j hij id v S
      refine ⟨v', hu, ?_⟩
      simpa [movedR] using he

theorem dsyRuns_bzero {wR c t : Fin T} (hd : [wR, c, t].Nodup) (R : Regs T A) (ht : R t = []) :
    dsyRuns body (bzero wR c t) R (Function.update R c (binSyms (R wR).length 0 ++ R c))
      (4 * (R wR).length + 4) :=
  dsyRuns.of_exec R (fun R => Function.update R c (binSyms (R wR).length 0 ++ R c))
    (fun R => 4 * (R wR).length + 4) fun v S hS => bzero_exec body hd v S (by rw [hS]; exact ht)

theorem dsyRuns_bpad {a eR t₁ t₂ : Fin T} (hd : [a, eR, t₁, t₂].Nodup) {L x : ℕ} (hx : x < 2 ^ L)
    (R : Regs T A) (ha : R a = binSyms L x) (h₁ : R t₁ = []) (h₂ : R t₂ = []) :
    dsyRuns body (bpad a eR t₁ t₂) R (Function.update R a (binSyms (L + (R eR).length) x))
      (4 * L + 6 * (R eR).length + 8) :=
  dsyRuns.of_exec R (fun R => Function.update R a (binSyms (L + (R eR).length) x))
    (fun R => 4 * L + 6 * (R eR).length + 8) fun v S hS =>
    bpad_exec body hd hx v S (by rw [hS]; exact ha) (by rw [hS]; exact h₁) (by rw [hS]; exact h₂)

/-! ### The unary product -/

/-- `dst` gains `|a| |b|` ticks: one copy of `b` per symbol of `a`. -/
def dsyMulU (a b dst t t' : Fin T) : Pr P T Q A U := scanP a t (ucopy b dst t')

theorem dsyRuns_mulU {a b dst t t' : Fin T} (hd : [a, b, dst, t, t'].Nodup) (R : Regs T A)
    (ht : R t = []) (ht' : R t' = []) :
    dsyRuns body (dsyMulU a b dst t t') R
      (Function.update R dst (List.replicate ((R a).length * (R b).length) tick ++ R dst))
      ((R a).length * (4 * (R b).length + 7) + 2 * (R a).length + 4) := by
  have hd' := hd
  regs_ne hd'
  intro v S hS
  subst hS
  set L := (S.R b).length with hL
  let Ψ : ℕ → Regs T A := fun j =>
    Function.update S.R dst (List.replicate (j * L) tick ++ S.R dst)
  have hp : IterSpec body (ucopy b dst t') a t Ψ (fun _ => 4 * L + 4) (S.R a).length := by
    intro j hj w S' hS'
    have hb' : S'.R b = S.R b := by rw [hS' b ‹a ≠ b›.symm ‹b ≠ t›]; simp [Ψ, ‹b ≠ dst›]
    have hdst' : S'.R dst = List.replicate (j * L) tick ++ S.R dst := by
      rw [hS' dst ‹a ≠ dst›.symm ‹dst ≠ t›]; simp [Ψ]
    have ht'' : S'.R t' = [] := by
      rw [hS' t' ‹a ≠ t'›.symm ‹t ≠ t'›.symm]; simp [Ψ, ‹dst ≠ t'›.symm, ht']
    obtain ⟨w', hu, he⟩ := ucopy_exec body ‹b ≠ dst› ‹b ≠ t'› ‹dst ≠ t'› w S' ht''
    refine ⟨w', _, _, hu, by rw [hb'], he, ?_, ?_, fun k hka hkt => ?_⟩
    · simp [Function.update_of_ne ‹a ≠ dst›]
    · simp [Function.update_of_ne ‹dst ≠ t›.symm]
    · by_cases hk : k = dst
      · subst hk
        simp only [Function.update_self, Ψ, hdst', hb', ← List.append_assoc,
          List.replicate_append_replicate]
        congr 2
        ring
      · rw [Function.update_of_ne hk, hS' k hka hkt]
        simp [Ψ, Function.update_of_ne hk]
  obtain ⟨v', R', m, hu, hm, he, ha', ht'', hΨ⟩ := scanP_exec body ‹a ≠ t› hp 0 v S (by omega)
    (fun k hka hkt => by simp [Ψ])
  refine ⟨v', _, m, hu, ?_, he, ?_, rfl, rfl, rfl⟩
  · simp only [ht, List.length_nil, Finset.sum_const, Finset.card_range, smul_eq_mul] at hm
    omega
  · funext k
    dsimp only
    by_cases hka : k = a
    · rw [hka, ha', ht]; simp [Function.update_of_ne ‹a ≠ dst›]
    by_cases hkt : k = t
    · rw [hkt, ht'']; simp [Function.update_of_ne ‹dst ≠ t›.symm, ht]
    rw [hΨ k hka hkt]
    simp only [Ψ, Nat.zero_add]

/-! ### The counted transfer -/

/-- `|cnt|` symbols of `src` move onto `dst` (reversed), counting on `cnt` through `t`. -/
def dsyXfer (cnt t src dst : Fin T) : Pr P T Q A U := scanP cnt t (.act (popPush src dst))

theorem dsyRuns_xfer {cnt t src dst : Fin T} (hd : [cnt, t, src, dst].Nodup) (R : Regs T A)
    (ht : R t = []) (hN : (R cnt).length ≤ (R src).length) :
    dsyRuns body (dsyXfer cnt t src dst) R
      (Function.update (Function.update R src ((R src).drop (R cnt).length)) dst
        (((R src).take (R cnt).length).reverse ++ R dst)) (6 * (R cnt).length + 4) := by
  have hd' := hd
  regs_ne hd'
  intro v S hS
  subst hS
  set l := S.R src with hl
  set N := (S.R cnt).length with hNd
  let Ψ : ℕ → Regs T A := fun j => Function.update (Function.update S.R src (l.drop j))
    dst ((l.take j).reverse ++ S.R dst)
  have hp : IterSpec body (.act (popPush src dst)) cnt t Ψ (fun _ => 1) N := by
    intro j hj w S' hS'
    have hsrc : S'.R src = l[j]'(by omega) :: l.drop (j + 1) := by
      rw [hS' _ ‹cnt ≠ src›.symm ‹t ≠ src›.symm]
      simp only [Ψ, Function.update_of_ne ‹src ≠ dst›, Function.update_self]
      exact List.drop_eq_getElem_cons (show j < l.length by omega)
    have hdst : S'.R dst = (l.take j).reverse ++ S.R dst := by
      rw [hS' _ ‹cnt ≠ dst›.symm ‹t ≠ dst›.symm]
      simp [Ψ]
    refine ⟨{ w with sym := some (l[j]'(by omega)) },
      Function.update (Function.update S'.R src (l.drop (j + 1))) dst
        (l[j]'(by omega) :: S'.R dst), 1, rfl, le_rfl, ?_, ?_, ?_, ?_⟩
    · have := Exec.act (body := body) (popPush src dst) (mk w S')
      simp only [popPush, Action.run, mk_var, mk_stk, get_rt, hsrc, List.head?_cons,
        List.tail_cons, Option.getD_some, update_rt, store_mk] at this
      rw [Function.update_of_ne ‹src ≠ dst›.symm] at this
      exact this
    · simp [Function.update_of_ne ‹cnt ≠ src›, Function.update_of_ne ‹cnt ≠ dst›]
    · simp [Function.update_of_ne ‹t ≠ src›, Function.update_of_ne ‹t ≠ dst›]
    · intro k hk1 hk2
      by_cases hk3 : k = dst
      · subst hk3
        have e : (List.take (j + 1) l).reverse = l[j]'(by omega) :: (List.take j l).reverse := by
          rw [List.take_succ_eq_append_getElem (show j < l.length by omega)]; simp
        simp only [Ψ, Function.update_self, hdst, e, List.cons_append]
      by_cases hk4 : k = src
      · subst hk4
        simp [Ψ, Function.update_of_ne hk3]
      simp [Ψ, Function.update_of_ne hk3, Function.update_of_ne hk4, hS' k hk1 hk2]
  obtain ⟨v', R', m, hu, hm, he, hcnt, ht', hΨ⟩ := scanP_exec body ‹cnt ≠ t› hp 0 v S
    (by omega) (fun k h1 h2 => by
      simp only [Ψ, List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append, hl,
        Function.update_eq_self])
  refine ⟨v', _, m, hu, ?_, he, ?_, rfl, rfl, rfl⟩
  · simp only [ht, Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_nil] at hm
    omega
  · funext k
    dsimp only
    by_cases h1 : k = cnt
    · rw [h1, hcnt, ht, Function.update_of_ne ‹cnt ≠ dst›, Function.update_of_ne ‹cnt ≠ src›]
      simp
    by_cases h2 : k = t
    · rw [h2, ht', Function.update_of_ne ‹t ≠ dst›, Function.update_of_ne ‹t ≠ src›, ht]
    rw [hΨ _ h1 h2, Nat.zero_add]

/-! ### The table machine on the host -/

/-- A `tblRuns` contract on the layout `rg`, as a contract on the whole file. -/
theorem dsyRuns_of_tbl {n : ℕ} {rg : TblR n → Fin T} (hrg : Function.Injective rg)
    {p : Pr P T Q A U} {ρ ρ' : TblR n → List (Fin (A + 4))} {b : ℕ}
    (h : tblRuns body rg p ρ ρ' b) (R : Regs T A) (hR : ∀ r, R (rg r) = ρ r) :
    dsyRuns body p R (dsOv rg R ρ') b := by
  intro v S hS
  subst hS
  obtain ⟨v', S', m, hu, hm, he, hS', hf⟩ := h v S hR
  refine ⟨v', S', m, hu, hm, he, ?_, hf.1, hf.2.1, hf.2.2.1⟩
  funext k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hk
    rw [dsOv_rg hrg]; exact hS' r
  · push Not at hk
    rw [dsOv_off _ _ hk]; exact hf.2.2.2 k hk

theorem dsOv_dsOv {ι : Type} {rg : ι → Fin T} (R : Regs T A)
    (ρ ρ' : ι → List (Fin (A + 4))) : dsOv rg (dsOv rg R ρ) ρ' = dsOv rg R ρ' := by
  funext k
  by_cases hk : ∃ r, rg r = k
  · simp only [dsOv, dif_pos hk]
  · simp only [dsOv, dif_neg hk]

/-- The load of a unary register into a variable. -/
theorem dsyRuns_load1 {rg : TblR 40 → Fin T} (hrg : Function.Injective rg) {W : ℕ}
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) {u : Fin T} (hu : ∀ r, rg r ≠ u)
    (i : Fin 40) (st : TblSt 40 A) (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    dsyRuns body (tblLoad1 rg u i) R
      (dsOv rg R (tblRho W wl nl ⟨Function.update st.val i (R u).length, st.acc⟩))
      ((R u).length * (4 * W + 10) + 6 * W + 10) := by
  intro v S hS
  subst hS
  obtain ⟨v', S', m, hu', hm, he, hS', hf⟩ := tbl_load1_runs (body := body) hrg wl nl hwl hu i st
    (S.R u).length v S rfl hR
  refine ⟨v', S', m, hu', hm, he, ?_, hf.1, hf.2.1, hf.2.2.1⟩
  funext k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := hk
    rw [dsOv_rg hrg]; exact hS' r
  · push Not at hk
    rw [dsOv_off _ _ hk]; exact hf.2.2.2 k hk

/-- A terminating table program on the host, with the bound on the final values. -/
theorem dsyRuns_host {rg : TblR 40 → Fin T} (hrg : Function.Injective rg) {W : ℕ}
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = 1) (h1W : 1 ≤ W)
    {c : TblCode 40} {st : TblSt 40 A} {Post : TblSt 40 A → Prop} {K : ℕ}
    (h : TblDo A W 1 c st Post K) (hst : ∀ j, st.val j < 2 ^ W) (R : Regs T A)
    (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    ∃ st', Post st' ∧ (∀ j, st'.val j < 2 ^ W) ∧
      dsyRuns body (tblCompile rg c) R (dsOv rg R (tblRho W wl nl st')) (K * tblC W 1) := by
  obtain ⟨st', k, hb, hp, hk⟩ := h
  refine ⟨st', hp, hb.lt hst, ?_⟩
  exact (dsyRuns_of_tbl hrg (tblCompile_runs hrg wl nl hwl hnl h1W hb hst) R hR).mono
    (Nat.mul_le_mul_right _ hk)

/-! ### Sequences of programs -/

/-- The sequence of a list of programs. -/
def dsySeq (l : List (Pr P T Q A U)) : Pr P T Q A U := l.foldr .seq (.act .done)

theorem dsyRuns_done (R : Regs T A) : dsyRuns body (.act .done) R R 1 := by
  intro v S hS
  subst hS
  exact ⟨v, S, 1, rfl, le_rfl, Exec.act .done (mk v S), rfl, rfl, rfl, rfl⟩

/-- Zero the variables `l` of the layout (`W` bits each, `W = |wr|`). -/
def dsyZeroVars (rg : TblR 40 → Fin T) (l : List (Fin 40)) : Pr P T Q A U :=
  dsySeq (l.map fun i => bzero (rg .wr) (rg (.v i)) (rg (.z 7)))

theorem dsyZeroVars_runs {rg : TblR 40 → Fin T} (hrg : Function.Injective rg) :
    ∀ (l : List (Fin 40)), l.Nodup → ∀ (R : Regs T A), (∀ i ∈ l, R (rg (.v i)) = []) →
      R (rg (.z 7)) = [] →
      dsyRuns body (dsyZeroVars rg l) R
        (fun k => if ∃ i ∈ l, rg (.v i) = k then binSyms (R (rg .wr)).length 0 else R k)
        (l.length * (4 * (R (rg .wr)).length + 4) + 1)
  | [], _, R, _, _ => by
      simp only [dsyZeroVars, dsySeq, List.map_nil, List.foldr_nil, List.length_nil, Nat.zero_mul,
        Nat.zero_add]
      refine (dsyRuns_done R).congr ?_
      funext k; simp
  | i :: l, hnd, R, hv, h7 => by
      have hnd' := List.nodup_cons.1 hnd
      have hz : dsyRuns body (bzero (rg .wr) (rg (.v i)) (rg (.z 7))) R
          (Function.update R (rg (.v i)) (binSyms (R (rg .wr)).length 0))
          (4 * (R (rg .wr)).length + 4) := by
        refine (dsyRuns_bzero (tbl_nodup hrg (l := [.wr, .v i, .z 7]) (by simp)) R h7).congr ?_
        rw [hv i List.mem_cons_self, List.append_nil]
      set R₁ := Function.update R (rg (.v i)) (binSyms (R (rg .wr)).length 0) with hR₁
      have ih := dsyZeroVars_runs hrg l hnd'.2 R₁ (fun j hj => by
          rw [hR₁, Function.update_of_ne (hrg.ne (by simp; exact fun e => hnd'.1 (e ▸ hj)))]
          exact hv j (List.mem_cons_of_mem _ hj))
        (by rw [hR₁, Function.update_of_ne (hrg.ne (by simp))]; exact h7)
      have hwr : R₁ (rg .wr) = R (rg .wr) := by
        rw [hR₁, Function.update_of_ne (hrg.ne (by simp))]
      rw [hwr] at ih
      refine ((hz.seq ih).congr ?_).mono (by simp; ring_nf; omega)
      funext k
      by_cases hk : ∃ j ∈ l, rg (.v j) = k
      · obtain ⟨j, hj, rfl⟩ := hk
        simp only [List.mem_cons, exists_eq_or_imp]
        rw [if_pos (Or.inr ⟨j, hj, rfl⟩), if_pos ⟨j, hj, rfl⟩]
      · rw [if_neg hk]
        by_cases hki : rg (.v i) = k
        · subst hki
          rw [if_pos ⟨i, List.mem_cons_self, rfl⟩, hR₁, Function.update_self]
        · have hne : ¬ ∃ j ∈ i :: l, rg (.v j) = k := by
            rintro ⟨j, hj, rfl⟩
            rcases List.mem_cons.1 hj with rfl | hj
            · exact hki rfl
            · exact hk ⟨j, hj, rfl⟩
          rw [if_neg hne, hR₁, Function.update_of_ne (Ne.symm hki)]

/-- Clear the layout registers `l`. -/
def dsyClearL (rg : TblR 40 → Fin T) (l : List (TblR 40)) : Pr P T Q A U :=
  dsySeq (l.map fun r => bclear (rg r))

theorem dsyClearL_runs {rg : TblR 40 → Fin T} (hrg : Function.Injective rg) (M : ℕ) :
    ∀ (l : List (TblR 40)) (R : Regs T A), (∀ r ∈ l, (R (rg r)).length ≤ M) →
      dsyRuns body (dsyClearL rg l) R (fun k => if ∃ r ∈ l, rg r = k then [] else R k)
        (l.length * (2 * M + 2) + 1)
  | [], R, _ => by
      simp only [dsyClearL, dsySeq, List.map_nil, List.foldr_nil, List.length_nil, Nat.zero_mul,
        Nat.zero_add]
      refine (dsyRuns_done R).congr ?_
      funext k; simp
  | r :: l, R, hM => by
      have hc := dsyRuns_bclear (body := body) (rg r) R
      set R₁ := Function.update R (rg r) [] with hR₁
      have ih := dsyClearL_runs hrg M l R₁ (fun r' hr' => by
        rw [hR₁]
        by_cases h : r' = r
        · subst h; simp
        · rw [Function.update_of_ne (hrg.ne h)]; exact hM r' (List.mem_cons_of_mem _ hr'))
      refine ((hc.seq ih).congr ?_).mono ?_
      · funext k
        by_cases hk : ∃ r' ∈ l, rg r' = k
        · obtain ⟨r', hr', rfl⟩ := hk
          simp only [List.mem_cons, exists_eq_or_imp]
          rw [if_pos (Or.inr ⟨r', hr', rfl⟩), if_pos ⟨r', hr', rfl⟩]
        · rw [if_neg hk]
          by_cases hkr : rg r = k
          · subst hkr
            rw [if_pos ⟨r, List.mem_cons_self, rfl⟩, hR₁, Function.update_self]
          · have hne : ¬ ∃ r' ∈ r :: l, rg r' = k := by
              rintro ⟨r', hr', rfl⟩
              rcases List.mem_cons.1 hr' with rfl | hr'
              · exact hkr rfl
              · exact hk ⟨r', hr', rfl⟩
            rw [if_neg hne, hR₁, Function.update_of_ne (Ne.symm hkr)]
      · have := hM r List.mem_cons_self
        simp only [List.length_cons]
        nlinarith

/-! ### The drain of the emitted symbols -/

/-- The symbol of a pair symbol: a tick for `pairSym A true _`, `bitSymbol false` otherwise. -/
def dsyH (A : ℕ) (x : Fin (A + 4)) : Fin (A + 4) := if pairRe x then tick else bitSymbol false

theorem dsyH_enc (hA : 4 ≤ A) {x : Fin (A + 4)} (hx : x = tick ∨ x = bitSymbol false) :
    dsyH A (dsyEnc A x) = x := by
  rcases hx with rfl | rfl
  · simp [dsyH, dsyEnc, pairRe_pairSym hA]
  · simp [dsyH, dsyEnc, pairRe_pairSym hA, tick, bitSymbol, Fin.ext_iff]

theorem dsyH_map (hA : 4 ≤ A) (l : List (Fin (A + 4)))
    (hl : ∀ x ∈ l, x = tick ∨ x = bitSymbol false) : (l.map (dsyEnc A)).map (dsyH A) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun x hx => dsyH_enc hA (hl x hx)

theorem dsy_flatMap_one {α β : Type} (f : α → β) : ∀ l : List α,
    (l.flatMap fun x => List.replicate 1 (f x)) = l.map f
  | [] => rfl
  | x :: l => by rw [List.flatMap_cons, List.map_cons, dsy_flatMap_one f l]; rfl

/-- Move the symbols of `a` onto `out` through `dsyH`. -/
def dsyDrain (a out : Fin T) : Pr P T Q A U :=
  drainR a (pushN out (fun v => dsyH A (v.sym.getD blank)) 1)

theorem dsyRuns_drain {a out : Fin T} (hao : a ≠ out) (R : Regs T A) :
    dsyRuns body (dsyDrain a out) R
      (Function.update (Function.update R out ((R a).reverse.map (dsyH A) ++ R out)) a [])
      (2 * (R a).length + 2) := by
  refine dsyRuns.of_exec R
    (fun R => Function.update (Function.update R out ((R a).reverse.map (dsyH A) ++ R out)) a [])
    (fun R => 2 * (R a).length + 2) fun v S _ => ?_
  obtain ⟨v', hu, he⟩ := drainR_exec body a
    (regFx_pushN out 1 (fun v => dsyH A (v.sym.getD blank)) (dsyH A) fun v x hx => by simp [hx])
    (frame_pushFx hao 1 (dsyH A)) v S
  refine ⟨v', hu, ?_⟩
  rw [foldl_pushFx, dsy_flatMap_one] at he
  exact he

/-- A table program followed by the drain of `acc` onto `out`. -/
def dsyPhase (rg : TblR 40 → Fin T) (c : TblCode 40) (out : Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg c) (dsyDrain (rg .acc) out)

theorem tblRho_acc_nil {W : ℕ} (wl nl : List (Fin (A + 4))) (st : TblSt 40 A) :
    Function.update (tblRho W wl nl st) .acc [] = tblRho W wl nl ⟨st.val, []⟩ := by
  funext r
  cases r <;> simp [tblRho]

/-- **A phase**: the program `c` from `st` emits `st'.acc` (in `acc`, the latest on top); the
drain leaves the symbols on `out` in emission order through `dsyH`, the layout carrying `st'`
with `acc` empty. -/
theorem dsyPhase_runs {rg : TblR 40 → Fin T} (hrg : Function.Injective rg) {out : Fin T}
    (hout : ∀ r, rg r ≠ out) {W : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W)
    (hnl : nl.length = 1) (h1W : 1 ≤ W) {c : TblCode 40} {st : TblSt 40 A}
    {Post : TblSt 40 A → Prop} {K : ℕ} (h : TblDo A W 1 c st Post K)
    (hst : ∀ j, st.val j < 2 ^ W) (R : Regs T A) (hR : ∀ r, R (rg r) = tblRho W wl nl st r) :
    ∃ st', Post st' ∧ (∀ j, st'.val j < 2 ^ W) ∧
      dsyRuns body (dsyPhase rg c out) R
        (dsOv rg (Function.update R out ((st'.acc.reverse.map (dsyH A)) ++ R out))
          (tblRho W wl nl ⟨st'.val, []⟩)) (K * tblC W 1 + (2 * st'.acc.length + 2)) := by
  obtain ⟨st', hp, hlt, hr⟩ := dsyRuns_host (body := body) hrg wl nl hwl hnl h1W h hst R hR
  refine ⟨st', hp, hlt, ?_⟩
  have hd := dsyRuns_drain (body := body) (hout .acc) (dsOv rg R (tblRho W wl nl st'))
  rw [dsOv_rg hrg, dsOv_off _ _ hout, tblRho_acc] at hd
  refine (hr.seq hd).congr ?_
  rw [dsOv_update _ _ hout, dsOv_update_on hrg, tblRho_acc_nil]

end IntegerMultBounds.MathlibTM2.Fast.TableVM
