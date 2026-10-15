module

public import IntegerMultBounds.MathlibTM2.Fast.LoadLayoutGenM
public import IntegerMultBounds.MathlibTM2.Fast.TableLoad

/-!
# Running a table-machine writer on the host

Host programs around a table-machine program (`IntegerMultBounds.MathlibTM2.Fast.TableVM`) on `40` variables whose
registers `rv : TblR 40 → Fin T` are idle before and after (`ldgIdle`: every variable, `acc` and
`z j` empty, `wr` holding the word width `W`, `wn` holding the emission width `w`):

* `ldgVars f l`: run `f i` for the variables `i ∈ l`;
* `ldgZero rv i`: variable `i := binSyms W 0` (`zeroBits` from `wr`); `ldgClear rv i`: empty it;
* `tblLoad1 rv u i`: variable `i := |u|` from a unary register `u`; `ldgLoadBin rv e i`:
  variable `i :=` the `W`-bit word on `e`;
* `ldgHostClear rv c out`: run `c` with its emissions onto `out` (`tblHost`), then empty every
  variable.

All contracts are `LayRuns` contracts on whole register files: `ldgSetV rv R ρ` is the file `R`
with the table registers replaced by `ρ`. `ldg_hostClear_runs`: if `c` runs from the state `st`
into states whose emissions are `stream`, then `ldgHostClear` takes the file carrying `st` to the
idle file with `out` gaining `stream` on top.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section Defs

variable {T Q A : ℕ} {U P : Type}

/-- Run `f i` for the variables `i` of `l` in order. -/
def ldgVars (f : Fin 40 → Pr P T Q A U) : List (Fin 40) → Pr P T Q A U
  | [] => .act .done
  | i :: l => .seq (f i) (ldgVars f l)

/-- Variable `i := binSyms W 0`, from `wr` through `z 0`. -/
def ldgZero (rv : TblR 40 → Fin T) (i : Fin 40) : Pr P T Q A U :=
  zeroBits (rv .wr) (rv (.v i)) (rv (.z 0))

/-- Empty variable `i`. -/
def ldgClear (rv : TblR 40 → Fin T) (i : Fin 40) : Pr P T Q A U := uclear (rv (.v i))

/-- Variable `i :=` the word on the register `e`. -/
def ldgLoadBin (rv : TblR 40 → Fin T) (e : Fin T) (i : Fin 40) : Pr P T Q A U :=
  .seq (uclear (rv (.v i))) (bcopy e (rv (.v i)) (rv (.z 0)) (rv (.z 1)))

/-- Run `c` with its emissions onto `out`, then empty every variable. -/
def ldgHostClear (rv : TblR 40 → Fin T) (c : TblCode 40) (out : Fin T) : Pr P T Q A U :=
  .seq (tblHost rv c out) (ldgVars (ldgClear rv) (List.finRange 40))

end Defs

/-- The idle table registers. -/
def ldgIdle {A : ℕ} (wl nl : List (Fin (A + 4))) : TblR 40 → List (Fin (A + 4))
  | .wr => wl
  | .wn => nl
  | _ => []

open Classical in
/-- The register file `R` with the table registers replaced by `ρ`. -/
noncomputable def ldgSetV {T A : ℕ} (rv : TblR 40 → Fin T) (R : Fin T → List (Fin (A + 4)))
    (ρ : TblR 40 → List (Fin (A + 4))) : Fin T → List (Fin (A + 4)) := fun k =>
  if h : ∃ r, rv r = k then ρ h.choose else R k

/-- `R` with the variables of `l` set to `x`. -/
def ldgSetVars {T A : ℕ} (rv : TblR 40 → Fin T) (R : Fin T → List (Fin (A + 4))) :
    List (Fin 40) → List (Fin (A + 4)) → Fin T → List (Fin (A + 4))
  | [], _ => R
  | i :: l, x => ldgSetVars rv (Function.update R (rv (.v i)) x) l x

section Lemmas

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rv : TblR 40 → Fin T}

theorem ldgSetV_rv (hrv : Function.Injective rv) (R : Fin T → List (Fin (A + 4)))
    (ρ : TblR 40 → List (Fin (A + 4))) (r : TblR 40) : ldgSetV rv R ρ (rv r) = ρ r := by
  have h : ∃ r', rv r' = rv r := ⟨r, rfl⟩
  rw [ldgSetV, dif_pos h, hrv h.choose_spec]

theorem ldgSetV_of (R : Fin T → List (Fin (A + 4))) (ρ : TblR 40 → List (Fin (A + 4)))
    {k : Fin T} (hk : ∀ r, rv r ≠ k) : ldgSetV rv R ρ k = R k := by
  rw [ldgSetV, dif_neg (fun ⟨r, hr⟩ => hk r hr)]

theorem ldgSetV_self (hrv : Function.Injective rv) (R : Fin T → List (Fin (A + 4))) :
    ldgSetV rv R (fun r => R (rv r)) = R := by
  funext k
  by_cases hk : ∃ r, rv r = k
  · obtain ⟨r, rfl⟩ := hk
    rw [ldgSetV_rv hrv]
  · rw [ldgSetV_of _ _ (fun r hr => hk ⟨r, hr⟩)]

theorem ldgSetV_setV (hrv : Function.Injective rv) (R : Fin T → List (Fin (A + 4)))
    (ρ ρ' : TblR 40 → List (Fin (A + 4))) : ldgSetV rv (ldgSetV rv R ρ) ρ' = ldgSetV rv R ρ' := by
  funext k
  by_cases hk : ∃ r, rv r = k
  · obtain ⟨r, rfl⟩ := hk
    rw [ldgSetV_rv hrv, ldgSetV_rv hrv]
  · rw [ldgSetV_of _ _ (fun r hr => hk ⟨r, hr⟩), ldgSetV_of _ _ (fun r hr => hk ⟨r, hr⟩),
      ldgSetV_of _ _ (fun r hr => hk ⟨r, hr⟩)]

theorem ldgSetV_update (hrv : Function.Injective rv) (R : Fin T → List (Fin (A + 4)))
    (ρ : TblR 40 → List (Fin (A + 4))) (a : TblR 40) (x : List (Fin (A + 4))) :
    Function.update (ldgSetV rv R ρ) (rv a) x = ldgSetV rv R (Function.update ρ a x) := by
  funext k
  by_cases hk : ∃ r, rv r = k
  · obtain ⟨r, rfl⟩ := hk
    rw [ldgSetV_rv hrv]
    by_cases hr : r = a
    · subst hr; simp
    · rw [Function.update_of_ne (hrv.ne hr), Function.update_of_ne hr, ldgSetV_rv hrv]
  · rw [Function.update_of_ne (fun e => hk ⟨a, e.symm⟩), ldgSetV_of _ _ (fun r hr => hk ⟨r, hr⟩),
      ldgSetV_of _ _ (fun r hr => hk ⟨r, hr⟩)]

theorem ldgSetV_update_off (R : Fin T → List (Fin (A + 4))) (ρ : TblR 40 → List (Fin (A + 4)))
    {k : Fin T} (hk : ∀ r, rv r ≠ k) (x : List (Fin (A + 4))) :
    Function.update (ldgSetV rv R ρ) k x = ldgSetV rv (Function.update R k x) ρ := by
  funext k'
  by_cases hk' : ∃ r, rv r = k'
  · obtain ⟨r, rfl⟩ := hk'
    rw [Function.update_of_ne (hk r), ldgSetV_rv' R ρ r, ldgSetV_rv' _ ρ r]
  · rw [ldgSetV_of _ _ (fun r hr => hk' ⟨r, hr⟩)]
    by_cases e : k' = k
    · subst e; simp
    · rw [Function.update_of_ne e, Function.update_of_ne e, ldgSetV_of _ _ (fun r hr => hk' ⟨r, hr⟩)]
where
  ldgSetV_rv' (R : Fin T → List (Fin (A + 4))) (ρ : TblR 40 → List (Fin (A + 4))) (r : TblR 40) :
      ldgSetV rv R ρ (rv r) = ρ (Classical.choose (⟨r, rfl⟩ : ∃ r', rv r' = rv r)) := by
    rw [ldgSetV, dif_pos ⟨r, rfl⟩]

/-- A contract of the table layout lifts to whole register files. -/
theorem ldg_lift (hrv : Function.Injective rv) {p : Pr P T Q A U}
    {ρ ρ' : TblR 40 → List (Fin (A + 4))} {b : ℕ} (h : tblRuns body rv p ρ ρ' b)
    (R : Fin T → List (Fin (A + 4))) (hR : ∀ r, R (rv r) = ρ r) :
    LayRuns body p R (ldgSetV rv R ρ') b := by
  intro v S hL hS
  obtain ⟨v', S', m, hu, hm, he, hS', hf⟩ := h v S (fun r => by rw [hS, hR])
  refine ⟨v', m, hu, hm, ?_⟩
  have e : S' = { S with R := ldgSetV rv R ρ' } := by
    refine Stacks.ext hf.1 hf.2.1 hf.2.2.1 ?_
    funext k
    by_cases hk : ∃ r, rv r = k
    · obtain ⟨r, rfl⟩ := hk
      simp only
      rw [ldgSetV_rv hrv, hS' r]
    · simp only
      rw [ldgSetV_of _ _ (fun r hr => hk ⟨r, hr⟩), hf.2.2.2 k (fun r hr => hk ⟨r, hr⟩), hS]
  rw [← e]
  exact he

theorem ldg_done_runs (R : Fin T → List (Fin (A + 4))) :
    LayRuns body (.act .done) R R 1 := by
  intro v S _ hS
  refine ⟨v, 1, rfl, le_rfl, ?_⟩
  have h := Exec.act (body := body) (.done : Act T Q A U) (mk v S)
  rw [run_done] at h
  rw [← hS]
  exact h

/-- Zeroing the variables of `l` (distinct, empty), from `wr` with `W` symbols. -/
theorem ldg_zero_runs (hrv : Function.Injective rv) (W : ℕ) :
    ∀ (l : List (Fin 40)) (R : Fin T → List (Fin (A + 4))), l.Nodup → R (rv (.z 0)) = [] →
      (R (rv .wr)).length = W → (∀ i ∈ l, R (rv (.v i)) = []) →
      LayRuns body (ldgVars (ldgZero rv) l) R (ldgSetVars rv R l (binSyms W 0))
        (l.length * (4 * W + 4) + 1)
  | [], R, _, _, _, _ => by simpa [ldgVars, ldgSetVars] using ldg_done_runs (body := body) R
  | i :: l, R, hnd, hz, hw, hv => by
      have h1 : LayRuns body (ldgZero rv i) R (Function.update R (rv (.v i)) (binSyms W 0))
          (4 * W + 4) := by
        intro v S _ hS
        obtain ⟨v', hu, he⟩ := zeroBits_exec body (len := rv .wr) (z := rv (.v i)) (t := rv (.z 0))
          (hrv.ne (by simp)) (hrv.ne (by simp)) (hrv.ne (by simp)) v S (by rw [hS, hz])
        refine ⟨v', _, hu, le_rfl, ?_⟩
        rw [hS, hw, hv i List.mem_cons_self, List.append_nil] at he
        exact he
      have h2 := ldg_zero_runs hrv W l (Function.update R (rv (.v i)) (binSyms W 0))
        (List.nodup_cons.1 hnd).2 (by rw [Function.update_of_ne (hrv.ne (by simp))]; exact hz)
        (by rw [Function.update_of_ne (hrv.ne (by simp))]; exact hw)
        (fun j hj => by
          have hji : j ≠ i := fun e => (List.nodup_cons.1 hnd).1 (e ▸ hj)
          rw [Function.update_of_ne (hrv.ne (by simpa using hji))]
          exact hv j (List.mem_cons_of_mem _ hj))
      refine (h1.seq h2).mono (le_of_eq ?_)
      simp only [List.length_cons]; ring

/-- Emptying the variables of `l` (distinct, at most `L` symbols each). -/
theorem ldg_clear_runs (L : ℕ) :
    ∀ (l : List (Fin 40)) (R : Fin T → List (Fin (A + 4))), l.Nodup →
      (∀ i ∈ l, (R (rv (.v i))).length ≤ L) →
      LayRuns body (ldgVars (ldgClear rv) l) R (ldgSetVars rv R l []) (l.length * (2 * L + 2) + 1)
  | [], R, _, _ => by simpa [ldgVars, ldgSetVars] using ldg_done_runs (body := body) R
  | i :: l, R, hnd, hv => by
      have h1 := ldl_uclear_runs (body := body) (rv (.v i)) R
      have h2 := ldg_clear_runs L l (Function.update R (rv (.v i)) []) (List.nodup_cons.1 hnd).2
        (fun j hj => by
          by_cases e : rv (.v j) = rv (.v i)
          · rw [e, Function.update_self]; simp
          · rw [Function.update_of_ne e]; exact hv j (List.mem_cons_of_mem _ hj))
      refine (h1.seq h2).mono ?_
      have := hv i List.mem_cons_self
      simp only [List.length_cons]
      nlinarith

theorem ldgSetVars_of (R : Fin T → List (Fin (A + 4))) (x : List (Fin (A + 4))) :
    ∀ (l : List (Fin 40)) {k : Fin T}, (∀ i ∈ l, rv (.v i) ≠ k) → ldgSetVars rv R l x k = R k
  | [], _, _ => rfl
  | i :: l, k, hk => by
      rw [ldgSetVars, ldgSetVars_of _ x l (fun j hj => hk j (List.mem_cons_of_mem _ hj)),
        Function.update_of_ne (Ne.symm (hk i List.mem_cons_self))]

theorem ldgSetVars_mem (hrv : Function.Injective rv) (x : List (Fin (A + 4))) :
    ∀ (l : List (Fin 40)) (R : Fin T → List (Fin (A + 4))) {i : Fin 40}, i ∈ l →
      ldgSetVars rv R l x (rv (.v i)) = x
  | [], _, _, h => absurd h (by simp)
  | j :: l, R, i, h => by
      rw [ldgSetVars]
      by_cases hil : i ∈ l
      · exact ldgSetVars_mem hrv x l _ hil
      · have hij : i = j := by simpa [hil] using h
        subst hij
        rw [ldgSetVars_of _ _ l (fun k hk e => hil (by
          have := hrv e; simp only [TblR.v.injEq] at this; exact this ▸ hk))]
        simp

/-- All variables set to `x`: the overlay with the variables replaced. -/
theorem ldgSetVars_all (hrv : Function.Injective rv) (R : Fin T → List (Fin (A + 4)))
    (x : List (Fin (A + 4))) :
    ldgSetVars rv R (List.finRange 40) x =
      ldgSetV rv R (fun r => match r with | .v _ => x | r => R (rv r)) := by
  funext k
  by_cases hk : ∃ r, rv r = k
  · obtain ⟨r, rfl⟩ := hk
    rw [ldgSetV_rv hrv]
    cases r with
    | v i => exact ldgSetVars_mem hrv x _ R (List.mem_finRange i)
    | _ => exact ldgSetVars_of R x _ (fun i _ e => by have := hrv e; simp at this)
  · rw [ldgSetV_of _ _ (fun r hr => hk ⟨r, hr⟩),
      ldgSetVars_of R x _ (fun i _ e => hk ⟨_, e⟩)]

end Lemmas

section Runs

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rv : TblR 40 → Fin T}

theorem ldg_conv (hrv : Function.Injective rv) {S S' : Stacks T A} {R : Fin T → List (Fin (A + 4))}
    (hS : S.R = R) {ρ' : TblR 40 → List (Fin (A + 4))} (hS' : tblHolds rv S' ρ')
    (hf : tblFr rv S S') : S' = { S with R := ldgSetV rv R ρ' } := by
  refine Stacks.ext hf.1 hf.2.1 hf.2.2.1 ?_
  funext k
  by_cases hk : ∃ r, rv r = k
  · obtain ⟨r, rfl⟩ := hk
    simp only
    rw [ldgSetV_rv hrv, hS' r]
  · simp only
    rw [ldgSetV_of _ _ (fun r hr => hk ⟨r, hr⟩), hf.2.2.2 k (fun r hr => hk ⟨r, hr⟩), hS]

/-- `tblLoad1` on whole register files: variable `i := |u|`. -/
theorem ldg_load_runs (hrv : Function.Injective rv) {W : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) {u : Fin T} (hu : ∀ r, rv r ≠ u) (i : Fin 40) (st : TblSt 40 A)
    (R : Fin T → List (Fin (A + 4))) (hR : ∀ r, R (rv r) = tblRho W wl nl st r) :
    LayRuns body (tblLoad1 rv u i) R
      (ldgSetV rv R (tblRho W wl nl ⟨Function.update st.val i (R u).length, st.acc⟩))
      ((R u).length * (4 * W + 10) + 6 * W + 10) := by
  intro v S _ hS
  obtain ⟨v', S', m, hu', hm, he, hS', hf⟩ := tbl_load1_runs (body := body) hrv wl nl hwl hu i st
    (R u).length v S (by rw [hS]) (fun r => by rw [hS, hR])
  refine ⟨v', m, hu', hm, ?_⟩
  rw [← ldg_conv hrv hS hS' hf]
  exact he

/-- Variable `i :=` the word `binSyms W x` of the register `e`. -/
theorem ldg_loadBin_runs (hrv : Function.Injective rv) {W : ℕ} (wl nl : List (Fin (A + 4)))
    {e : Fin T} (he : ∀ r, rv r ≠ e) (i : Fin 40) (st : TblSt 40 A) (x : ℕ)
    (R : Fin T → List (Fin (A + 4))) (hR : ∀ r, R (rv r) = tblRho W wl nl st r)
    (hx : R e = binSyms W x) :
    LayRuns body (ldgLoadBin rv e i) R
      (ldgSetV rv R (tblRho W wl nl ⟨Function.update st.val i x, st.acc⟩)) (8 * W + 8) := by
  have h1 := ldl_uclear_runs (body := body) (rv (.v i)) R
  set R1 := Function.update R (rv (.v i)) [] with hR1
  have h2 : LayRuns body (bcopy e (rv (.v i)) (rv (.z 0)) (rv (.z 1))) R1
      (Function.update R1 (rv (.v i)) (R1 e ++ R1 (rv (.v i)))) (6 * (R1 e).length + 6) := by
    intro v S _ hS
    have hreg : [e, rv (.v i), rv (.z 0), rv (.z 1)].Nodup := by
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_,
        List.nodup_singleton _⟩⟩⟩
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
        exact ⟨fun h => he _ h.symm, fun h => he _ h.symm, fun h => he _ h.symm⟩
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
        exact ⟨hrv.ne (by simp), hrv.ne (by simp)⟩
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
        exact hrv.ne (by simp)
    obtain ⟨v', hu, hex⟩ := bcopy_exec body hreg v S
      (by rw [hS, hR1, Function.update_of_ne (hrv.ne (by simp)), hR]; rfl)
      (by rw [hS, hR1, Function.update_of_ne (hrv.ne (by simp)), hR]; rfl)
    rw [hS] at hex
    exact ⟨v', _, hu, le_rfl, hex⟩
  refine ((h1.seq h2).mono ?_).congr ?_
  · rw [hR, tblRho_v, length_binSyms, hR1, Function.update_of_ne (fun h => he _ h.symm), hx,
      length_binSyms]
    omega
  · funext k
    rw [hR1, Function.update_idem, Function.update_of_ne (fun h => he _ h.symm), hx,
      Function.update_self, List.append_nil]
    by_cases hk : ∃ r, rv r = k
    · obtain ⟨r, rfl⟩ := hk
      rw [ldgSetV_rv hrv]
      by_cases hr : r = .v i
      · subst hr; simp
      · rw [Function.update_of_ne (hrv.ne hr), hR]
        cases r <;> simp_all [tblRho]
    · rw [Function.update_of_ne (fun e => hk ⟨_, e.symm⟩), ldgSetV_of _ _ (fun r hr => hk ⟨r, hr⟩)]

/-- **A table program with emptied variables.** If `c` runs from `st` (values below `2 ^ W`)
into states whose emission lists, reversed, are `stream`, then `ldgHostClear rv c out`
takes the file carrying `st` to the idle file with `out` gaining `stream` on top. -/
theorem ldg_hostClear_runs (hrv : Function.Injective rv) {c : TblCode 40} {out : Fin T}
    (hout : ∀ r, rv r ≠ out) {W w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W)
    (hnl : nl.length = w) (hw : w ≤ W) (st : TblSt 40 A) (hst : ∀ j, st.val j < 2 ^ W)
    {Post : TblSt 40 A → Prop} {K : ℕ} (hdo : TblDo A W w c st Post K)
    (stream : List (Fin (A + 4))) (hpost : ∀ s, Post s → s.acc.reverse = stream)
    (R : Fin T → List (Fin (A + 4))) (hR : ∀ r, R (rv r) = tblRho W wl nl st r) :
    LayRuns body (ldgHostClear rv c out) R
      (Function.update (ldgSetV rv R (ldgIdle wl nl)) out (stream ++ R out))
      (K * tblC W w + 2 * stream.length + 2 + (40 * (2 * W + 2) + 1)) := by
  intro v S hL hS
  obtain ⟨v₁, S₁, m₁, st', hp, hu₁, hm₁, he₁, hout₁, hS₁, hi₁, ho₁, hL₁, hk₁⟩ :=
    tblHost_runs (body := body) hrv hout wl nl hwl hnl hw hdo hst v S (fun r => by rw [hS, hR])
  have hstream := hpost st' hp
  set R₁ := Function.update (ldgSetV rv R (tblRho W wl nl ⟨st'.val, []⟩)) out (stream ++ R out)
    with hR₁
  have eS₁ : S₁ = { S with R := R₁ } := by
    refine Stacks.ext hi₁ ho₁ hL₁ ?_
    funext k
    simp only
    by_cases hk : k = out
    · subst hk
      rw [hR₁, Function.update_self, hout₁, hstream, hS]
    · rw [hR₁, Function.update_of_ne hk]
      by_cases hk' : ∃ r, rv r = k
      · obtain ⟨r, rfl⟩ := hk'
        rw [ldgSetV_rv hrv, hS₁ r]
      · rw [ldgSetV_of _ _ (fun r hr => hk' ⟨r, hr⟩), hk₁ k hk (fun r hr => hk' ⟨r, hr⟩), hS]
  have hc := ldg_clear_runs (body := body) (rv := rv) W (List.finRange 40) R₁
    (List.nodup_finRange 40) (fun i _ => by
      rw [hR₁, Function.update_of_ne (hout _), ldgSetV_rv hrv]; simp)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hc v₁ { S with R := R₁ } (by rw [eS₁] at hL₁; simpa using hL) rfl
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, ?_⟩
  · have hlen : st'.acc.length = stream.length := by rw [← hstream, List.length_reverse]
    simp only [List.length_finRange] at hm₂
    rw [hlen] at hm₁
    omega
  · rw [eS₁] at he₁
    have e : ldgSetVars rv R₁ (List.finRange 40) [] =
        Function.update (ldgSetV rv R (ldgIdle wl nl)) out (stream ++ R out) := by
      rw [ldgSetVars_all hrv, hR₁, ← ldgSetV_update_off _ _ hout]
      congr 1
      rw [ldgSetV_update_off _ _ hout, ldgSetV_setV hrv, ← ldgSetV_update_off _ _ hout]
      congr 1
      funext r
      cases r <;> simp [ldgIdle, ldgSetV_rv hrv, Function.update_of_ne (hout _), tblRho]
    rw [← e]
    exact Exec.seq he₁ he₂

end Runs

/-! ### Zeroing and loading the inputs -/

section Inputs

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rv : TblR 40 → Fin T}

/-- Zero every variable and load the unary registers `u0 … u3` into the variables `0 … 3`. -/
def ldgLoad4 (rv : TblR 40 → Fin T) (u0 u1 u2 u3 : Fin T) : Pr P T Q A U :=
  .seq (ldgVars (ldgZero rv) (List.finRange 40)) <|
  .seq (tblLoad1 rv u0 0) <| .seq (tblLoad1 rv u1 1) <| .seq (tblLoad1 rv u2 2) (tblLoad1 rv u3 3)

/-- The table state with the values `x0 … x4` in the variables `0 … 4`, every other variable
`0`, nothing emitted. -/
def ldgSt (A x0 x1 x2 x3 x4 : ℕ) : TblSt 40 A :=
  ⟨Function.update (Function.update (Function.update (Function.update (Function.update
    (fun _ => 0) 0 x0) 1 x1) 2 x2) 3 x3) 4 x4, []⟩

/-- The step bound of `ldgLoad4`. -/
def ldgLoad4Cost (W x0 x1 x2 x3 : ℕ) : ℕ :=
  (40 * (4 * W + 4) + 1) + ((x0 * (4 * W + 10) + 6 * W + 10) + ((x1 * (4 * W + 10) + 6 * W + 10) +
    ((x2 * (4 * W + 10) + 6 * W + 10) + (x3 * (4 * W + 10) + 6 * W + 10))))

theorem ldg_load4_runs (hrv : Function.Injective rv) {W : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) {u0 u1 u2 u3 : Fin T} (hu0 : ∀ r, rv r ≠ u0) (hu1 : ∀ r, rv r ≠ u1)
    (hu2 : ∀ r, rv r ≠ u2) (hu3 : ∀ r, rv r ≠ u3) (R : Fin T → List (Fin (A + 4)))
    (hR : ∀ r, R (rv r) = ldgIdle wl nl r) :
    LayRuns body (ldgLoad4 rv u0 u1 u2 u3) R
      (ldgSetV rv R (tblRho W wl nl ⟨Function.update (Function.update (Function.update
        (Function.update (fun _ => 0) 0 (R u0).length) 1 (R u1).length) 2 (R u2).length) 3
        (R u3).length, []⟩))
      (ldgLoad4Cost W (R u0).length (R u1).length (R u2).length (R u3).length) := by
  have hz := ldg_zero_runs (body := body) hrv W (List.finRange 40) R (List.nodup_finRange 40)
    (by rw [hR]; rfl) (by rw [hR]; exact hwl) (fun i _ => by rw [hR]; rfl)
  rw [ldgSetVars_all hrv] at hz
  have e0 : (ldgSetV rv R fun r => match r with | .v _ => binSyms W 0 | r => R (rv r)) =
      ldgSetV rv R (tblRho W wl nl ⟨fun _ => 0, []⟩) := by
    congr 1
    funext r
    cases r <;> simp [hR, ldgIdle, tblRho]
  replace hz := (congrArg (fun ρ => LayRuns body (ldgVars (ldgZero rv) (List.finRange 40)) R ρ
    ((List.finRange 40).length * (4 * W + 4) + 1)) e0).mp hz
  have keep : ∀ (ρ : TblR 40 → List (Fin (A + 4))) {u : Fin T}, (∀ r, rv r ≠ u) →
      ldgSetV rv R ρ u = R u := fun ρ u hu => ldgSetV_of _ _ hu
  set s0 : TblSt 40 A := ⟨fun _ => 0, []⟩ with hs0
  set s1 : TblSt 40 A := ⟨Function.update s0.val 0 (R u0).length, s0.acc⟩ with hs1
  set s2 : TblSt 40 A := ⟨Function.update s1.val 1 (R u1).length, s1.acc⟩ with hs2
  set s3 : TblSt 40 A := ⟨Function.update s2.val 2 (R u2).length, s2.acc⟩ with hs3
  have l0 := ldg_load_runs (body := body) hrv wl nl hwl hu0 0 s0 (ldgSetV rv R (tblRho W wl nl s0))
    (ldgSetV_rv hrv R _)
  rw [keep _ hu0, ldgSetV_setV hrv] at l0
  have l1 := ldg_load_runs (body := body) hrv wl nl hwl hu1 1 s1 (ldgSetV rv R (tblRho W wl nl s1))
    (ldgSetV_rv hrv R _)
  rw [keep _ hu1, ldgSetV_setV hrv] at l1
  have l2 := ldg_load_runs (body := body) hrv wl nl hwl hu2 2 s2 (ldgSetV rv R (tblRho W wl nl s2))
    (ldgSetV_rv hrv R _)
  rw [keep _ hu2, ldgSetV_setV hrv] at l2
  have l3 := ldg_load_runs (body := body) hrv wl nl hwl hu3 3 s3 (ldgSetV rv R (tblRho W wl nl s3))
    (ldgSetV_rv hrv R _)
  rw [keep _ hu3, ldgSetV_setV hrv] at l3
  refine (hz.seq (l0.seq (l1.seq (l2.seq l3)))).mono ?_
  simp only [List.length_finRange, ldgLoad4Cost]
  omega

end Inputs

/-! ### The writer of the single-bit move stream on the host -/

section Run1

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rv : TblR 40 → Fin T}

/-- The writer of the single-bit move stream onto `out`: load `N, ℓ, K, D` from unary registers
and the word `E` from `eW`, run `ldw1Code`, empty the variables. The emission width is the
length of the register `wn`. -/
noncomputable def ldgRun1 (rv : TblR 40 → Fin T) (uN uL uK uD eW out : Fin T) : Pr P T Q A U :=
  .seq (ldgLoad4 rv uN uL uK uD) (.seq (ldgLoadBin rv eW 4) (ldgHostClear rv ldw1Code out))

/-- The step bound of `ldgRun1`. -/
def ldgRun1Cost (W w N ℓ K D b len : ℕ) : ℕ :=
  ldgLoad4Cost W N ℓ K D + (8 * W + 8) +
    (ldw1Atoms N D b * tblC W w + 2 * len + 2 + (40 * (2 * W + 2) + 1))

open IntegerMultBounds.MathlibTM2.Mult.Rounds in
/-- **The single-bit move stream on the host.** With the table registers idle (`wr` holding
`W` symbols, `wn` holding `w ≤ W` symbols), unary registers holding `N = es.sum`, `ℓ`, `K`,
`D = es.length` and the word `binSyms W E` of the long axes on `eW`, `ldgRun1` pushes
`ldlBitStream (A) w (layBits es ℓ K)` onto `out` and changes nothing else. -/
theorem ldg_run1_runs (hrv : Function.Injective rv) {es : List ℕ} {ℓ K E W w : ℕ}
    (H : LayHyp es ℓ K) (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2)
    (hEW : E < 2 ^ W) (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hNW : es.sum < W) (h2W : 2 ≤ W)
    (hℓW : ℓ < 2 ^ W) (hw : w ≤ W) {uN uL uK uD eW out : Fin T}
    (huN : ∀ r, rv r ≠ uN) (huL : ∀ r, rv r ≠ uL) (huK : ∀ r, rv r ≠ uK) (huD : ∀ r, rv r ≠ uD)
    (heW : ∀ r, rv r ≠ eW) (hout : ∀ r, rv r ≠ out) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (R : Fin T → List (Fin (A + 4)))
    (hR : ∀ r, R (rv r) = ldgIdle wl nl r) (hN : (R uN).length = es.sum) (hL : (R uL).length = ℓ)
    (hK : (R uK).length = K) (hD : (R uD).length = es.length) (hEv : R eW = binSyms W E) :
    LayRuns body (ldgRun1 rv uN uL uK uD eW out) R
      (Function.update R out (ldlBitStream A w (layBits es ℓ K) ++ R out))
      (ldgRun1Cost W w es.sum ℓ K es.length (layB ℓ K)
        (ldlBitStream A w (layBits es ℓ K)).length) := by
  have hℓ := H.ℓ_ge
  have hDN := ldw_length_le_sum H
  have hNW' : es.sum < 2 ^ W := lt_of_lt_of_le hNW (Nat.lt_two_pow_self).le
  have l4 := ldg_load4_runs (body := body) hrv wl nl hwl huN huL huK huD R hR
  rw [hN, hL, hK, hD] at l4
  set st4 : TblSt 40 A := ⟨Function.update (Function.update (Function.update
    (Function.update (fun _ => 0) 0 es.sum) 1 ℓ) 2 K) 3 es.length, []⟩ with hst4
  have lb := ldg_loadBin_runs (body := body) hrv wl nl heW 4 st4 E _ (ldgSetV_rv hrv R _)
    (by rw [ldgSetV_of _ _ heW, hEv])
  rw [ldgSetV_setV hrv] at lb
  set st5 : TblSt 40 A := ⟨Function.update st4.val 4 E, st4.acc⟩ with hst5
  have hv : ∀ j, st5.val j < 2 ^ W := by
    intro j
    simp only [hst5, hst4, Function.update_apply]
    split_ifs <;> first | exact hEW | omega | (have := H.K_le; omega)
  have hdo := ldw1_do (A := A) (W := W) (w := w) H hE st5 (by simp [hst5, hst4])
    (by simp [hst5, hst4]) (by simp [hst5, hst4]) (by simp [hst5, hst4]) (by simp [hst5, hst4])
    hW hNW h2W hℓW
  have hh := ldg_hostClear_runs (body := body) hrv hout wl nl hwl hnl hw st5 hv hdo
    (ldlBitStream A w (layBits es ℓ K)) (fun s hs => by rw [hs]; simp [hst5, hst4])
    _ (ldgSetV_rv hrv R _)
  rw [ldgSetV_setV hrv, ldgSetV_of _ _ hout] at hh
  have eR : ldgSetV rv R (ldgIdle wl nl) = R := by
    have e : ldgIdle wl nl = fun r => R (rv r) := funext fun r => (hR r).symm
    rw [e, ldgSetV_self hrv]
  rw [eR] at hh
  refine (l4.seq (lb.seq hh)).mono (le_of_eq ?_)
  unfold ldgRun1Cost
  ring

end Run1

/-! ### Unary helpers and stream lengths -/

section Unary

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem ldg_ucopy_runs {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (R : Fin T → List (Fin (A + 4))) (ht : R t = []) :
    LayRuns body (ucopy a b t) R (Function.update R b (List.replicate (R a).length tick ++ R b))
      (4 * (R a).length + 4) := by
  intro v S _ hS
  obtain ⟨v', hu, he⟩ := ucopy_exec body hab hat hbt v S (by rw [hS, ht])
  rw [hS] at he
  exact ⟨v', _, hu, le_rfl, he⟩

theorem ldg_udiv_runs {c : ℕ} (hc : 1 ≤ c) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (R : Fin T → List (Fin (A + 4))) (ht : R t = []) :
    LayRuns body (udiv c a b t) R
      (Function.update R b (List.replicate ((R a).length / c) tick ++ R b)) (4 * (R a).length + 4) := by
  intro v S _ hS
  obtain ⟨v', m, hu, hm, he⟩ := udiv_exec body hc hab hat hbt v S (by rw [hS, ht])
  rw [hS] at he hm
  exact ⟨v', m, hu, hm, he⟩

theorem length_ldlBitStream_one (bs : List (ℕ × ℕ)) :
    (ldlBitStream A 1 bs).length = bs.length := by
  simp [ldlBitStream, ldlBitRec, List.length_flatMap]

theorem length_ldlXcStream (w : ℕ) (xs : List LayXcD) :
    (ldlXcStream A w xs).length = 5 * w * xs.length := by
  simp [ldlXcStream, ldlXcRec, List.length_flatMap]
  ring

theorem length_ldlBitStream (w : ℕ) (bs : List (ℕ × ℕ)) :
    (ldlBitStream A w bs).length = w * bs.length := by
  simp [ldlBitStream, ldlBitRec, List.length_flatMap]
  ring

end Unary

/-! ### A writer with five unary inputs -/

section RunU

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rv : TblR 40 → Fin T}

/-- Load the unary registers `u0 … u4` into the variables `0 … 4`, run `c` onto `out`, empty the
variables. -/
noncomputable def ldgRunU (rv : TblR 40 → Fin T) (u0 u1 u2 u3 u4 : Fin T) (c : TblCode 40)
    (out : Fin T) : Pr P T Q A U :=
  .seq (ldgLoad4 rv u0 u1 u2 u3) (.seq (tblLoad1 rv u4 4) (ldgHostClear rv c out))

/-- The step bound of `ldgRunU`. -/
def ldgRunUCost (W w x0 x1 x2 x3 x4 Kc len : ℕ) : ℕ :=
  ldgLoad4Cost W x0 x1 x2 x3 + (x4 * (4 * W + 10) + 6 * W + 10) +
    (Kc * tblC W w + 2 * len + 2 + (40 * (2 * W + 2) + 1))

/-- **A writer with five unary inputs on the host.** If `c` emits `stream` from every state with
the values `x0 … x4` in the variables `0 … 4` and nothing emitted, within `Kc` atoms, then
`ldgRunU` pushes `stream` onto `out` and changes nothing else. -/
theorem ldg_runU_runs (hrv : Function.Injective rv) {c : TblCode 40} {W w Kc : ℕ}
    {x0 x1 x2 x3 x4 : ℕ} (stream : List (Fin (A + 4)))
    (hdo : ∀ st : TblSt 40 A, st.val 0 = x0 → st.val 1 = x1 → st.val 2 = x2 → st.val 3 = x3 →
      st.val 4 = x4 → st.acc = [] → TblDo A W w c st (fun s => s.acc.reverse = stream) Kc)
    (h0 : x0 < 2 ^ W) (h1 : x1 < 2 ^ W) (h2 : x2 < 2 ^ W) (h3 : x3 < 2 ^ W) (h4 : x4 < 2 ^ W)
    (hw : w ≤ W) {u0 u1 u2 u3 u4 out : Fin T}
    (hu0 : ∀ r, rv r ≠ u0) (hu1 : ∀ r, rv r ≠ u1) (hu2 : ∀ r, rv r ≠ u2) (hu3 : ∀ r, rv r ≠ u3)
    (hu4 : ∀ r, rv r ≠ u4) (hout : ∀ r, rv r ≠ out) (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (R : Fin T → List (Fin (A + 4)))
    (hR : ∀ r, R (rv r) = ldgIdle wl nl r) (hx0 : (R u0).length = x0) (hx1 : (R u1).length = x1)
    (hx2 : (R u2).length = x2) (hx3 : (R u3).length = x3) (hx4 : (R u4).length = x4) :
    LayRuns body (ldgRunU rv u0 u1 u2 u3 u4 c out) R (Function.update R out (stream ++ R out))
      (ldgRunUCost W w x0 x1 x2 x3 x4 Kc stream.length) := by
  have l4 := ldg_load4_runs (body := body) hrv wl nl hwl hu0 hu1 hu2 hu3 R hR
  rw [hx0, hx1, hx2, hx3] at l4
  set st4 : TblSt 40 A := ⟨Function.update (Function.update (Function.update
    (Function.update (fun _ => 0) 0 x0) 1 x1) 2 x2) 3 x3, []⟩ with hst4
  have lu := ldg_load_runs (body := body) hrv wl nl hwl hu4 4 st4
    (ldgSetV rv R (tblRho W wl nl st4)) (ldgSetV_rv hrv R _)
  rw [ldgSetV_of _ _ hu4, hx4, ldgSetV_setV hrv] at lu
  set st5 : TblSt 40 A := ⟨Function.update st4.val 4 x4, st4.acc⟩ with hst5
  have hv : ∀ j, st5.val j < 2 ^ W := by
    intro j
    simp only [hst5, hst4, Function.update_apply]
    split_ifs <;> first | assumption | exact Nat.two_pow_pos W
  have hh := ldg_hostClear_runs (body := body) hrv hout wl nl hwl hnl hw st5 hv
    (hdo st5 (by simp [hst5, hst4]) (by simp [hst5, hst4]) (by simp [hst5, hst4])
      (by simp [hst5, hst4]) (by simp [hst5, hst4]) rfl) stream (fun s hs => hs)
    _ (ldgSetV_rv hrv R _)
  rw [ldgSetV_setV hrv, ldgSetV_of _ _ hout] at hh
  have eR : ldgSetV rv R (ldgIdle wl nl) = R := by
    have e : ldgIdle wl nl = fun r => R (rv r) := funext fun r => (hR r).symm
    rw [e, ldgSetV_self hrv]
  rw [eR] at hh
  refine (l4.seq (lu.seq hh)).mono (le_of_eq ?_)
  unfold ldgRunUCost
  ring

end RunU

/-! ### The writer of the description streams -/

/-- The registers of the writer: the table machine, the unary inputs `N, ℓ, K, D, B`, the word
`E` of the long axes, and a spare counter. -/
inductive LdgReg
  | tbl (r : TblR 40)
  | uN | uL | uK | uD | uB | eW | tc
  deriving DecidableEq

section Writer

variable {T Q A t₀ : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- The table registers of the writer. -/
def ldgRv (gr : LdgReg → Fin T) (r : TblR 40) : Fin T := gr (.tbl r)

/-- Push one tick onto `d`. -/
def ldgTick (d : Fin T) : Pr P T Q A U := .act (.push (.rt d) (fun _ => tick) .done)

/-- **The writer of the description streams** of the layout loaders, from the unary inputs
`N, ℓ, K, D, B` and the word `E`: the single-bit move stream onto `dM` (emission width `N`) and
one symbol per move onto `cM`, the exchange stream of the table program `cX` onto `dX` (width
`wX = N + B + 2`) and one tick per exchange onto `cX` (width `1`, five symbols per exchange,
divided by `5`), `N` ticks onto `cN` and `wX` ticks onto `cW`. -/
noncomputable def ldgWriter (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) (gr : LdgReg → Fin T)
    (cX : TblCode 40) : Pr P T Q A U :=
  .seq (ucopy (gr .uN) (ldgRv gr .wn) (ldgRv gr (.z 0))) <|
  .seq (ldgRun1 (ldgRv gr) (gr .uN) (gr .uL) (gr .uK) (gr .uD) (gr .eW) (lr .dM)) <|
  .seq (uclear (ldgRv gr .wn)) <|
  .seq (ldgTick (ldgRv gr .wn)) <|
  .seq (ldgRun1 (ldgRv gr) (gr .uN) (gr .uL) (gr .uK) (gr .uD) (gr .eW) (rg .cM)) <|
  .seq (uclear (ldgRv gr .wn)) <|
  .seq (ucopy (gr .uN) (ldgRv gr .wn) (ldgRv gr (.z 0))) <|
  .seq (ucopy (gr .uB) (ldgRv gr .wn) (ldgRv gr (.z 0))) <|
  .seq (ldgTick (ldgRv gr .wn)) <| .seq (ldgTick (ldgRv gr .wn)) <|
  .seq (ldgRunU (ldgRv gr) (gr .uN) (gr .uL) (gr .uK) (gr .uD) (gr .uB) cX (lr .dX)) <|
  .seq (uclear (ldgRv gr .wn)) <|
  .seq (ldgTick (ldgRv gr .wn)) <|
  .seq (ldgRunU (ldgRv gr) (gr .uN) (gr .uL) (gr .uK) (gr .uD) (gr .uB) cX (gr .tc)) <|
  .seq (uclear (ldgRv gr .wn)) <|
  .seq (udiv 5 (gr .tc) (rg .cX) (ldgRv gr (.z 0))) <|
  .seq (uclear (gr .tc)) <|
  .seq (ucopy (gr .uN) (lr .cN) (ldgRv gr (.z 0))) <|
  .seq (ucopy (gr .uN) (lr .cW) (ldgRv gr (.z 0))) <|
  .seq (ucopy (gr .uB) (lr .cW) (ldgRv gr (.z 0))) <|
  .seq (ldgTick (lr .cW)) (ldgTick (lr .cW))

/-- The three register maps of the layout stage are injective with disjoint images. -/
structure LdgRegs (rg : LayReg t₀ → Fin T) (lr : LdlReg → Fin T) (gr : LdgReg → Fin T) : Prop
    where
  l : LdlRegs rg lr
  gr_inj : Function.Injective gr
  disj_rg : ∀ x y, gr x ≠ rg y
  disj_lr : ∀ x y, gr x ≠ lr y

theorem ldg_tick_runs (d : Fin T) (R : Fin T → List (Fin (A + 4))) :
    LayRuns body (ldgTick d) R (Function.update R d (tick :: R d)) 1 :=
  ldl_push_runs d tick R

end Writer

section WriterRuns

variable {T Q A t₀ : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : LayReg t₀ → Fin T}
  {lr : LdlReg → Fin T} {gr : LdgReg → Fin T}

/-- The step bound of the writer. -/
def ldgWriterCost (W N ℓ K D B b len1 lenX KX : ℕ) : ℕ :=
  ldgRun1Cost W N N ℓ K D b (N * len1) + ldgRun1Cost W 1 N ℓ K D b (1 * len1) +
    ldgRunUCost W (N + B + 2) N ℓ K D B KX (5 * (N + B + 2) * lenX) +
    ldgRunUCost W 1 N ℓ K D B KX (5 * 1 * lenX) + 30 * lenX + 20 * N + 10 * B + 52

theorem ldg_writerCost_le (W N ℓ K D B b len1 lenX KX : ℕ) :
    4 * N + 4 + (ldgRun1Cost W N N ℓ K D b (N * len1) + (2 * N + 2 + (1 + (ldgRun1Cost W 1 N ℓ K D b (1 * len1) + (2 * 1 + 2 + (4 * N + 4 + (4 * B + 4 + (1 + (1 + (ldgRunUCost W (N + B + 2) N ℓ K D B KX (5 * (N + B + 2) * lenX) + (2 * (N + B + 2) + 2 + (1 + (ldgRunUCost W 1 N ℓ K D B KX (5 * 1 * lenX) + (2 * 1 + 2 + (4 * (5 * 1 * lenX) + 4 + (2 * (5 * 1 * lenX) + 2 + (4 * N + 4 + (4 * N + 4 + (4 * B + 4 + (1 + (1))))))))))))))))))))) ≤
      ldgWriterCost W N ℓ K D B b len1 lenX KX := by
  unfold ldgWriterCost
  omega

open IntegerMultBounds.MathlibTM2.Mult.Rounds in
/-- **The writer of the description streams.** From idle table registers (`wr` with `W` symbols,
`wn` empty), unary registers holding `N = es.sum`, `ℓ`, `K`, `D = es.length`, `B`, the word
`binSyms W E` of the long axes, and empty outputs, the writer leaves the single-bit move stream
`ldlBitStream A N (layBits es ℓ K)` on `dM`, one symbol per move on `cM`, the exchange stream
`ldlXcStream A wX xs` (`wX = N + B + 2`) of the table program `cX` on `dX`, one tick per exchange
on `cX`, `N` ticks on `cN` and `wX` ticks on `cW`; every other register ends as it started. -/
theorem ldg_writer_runs (hg : LdgRegs rg lr gr) {es : List ℕ} {ℓ K B E W : ℕ}
    (H : LayHyp es ℓ K) (hE : ∀ i < es.length, ax es i = ℓ - 1 + E / 2 ^ i % 2)
    (hEW : E < 2 ^ W) (hW : (es.sum + 1) ^ es.sum < 2 ^ W) (hNW : es.sum < W) (h2W : 2 ≤ W)
    (hℓW : ℓ < 2 ^ W) (hBW : es.sum + B + 2 ≤ W) {cX : TblCode 40} {KX : ℕ} (xs : List LayXcD)
    (hX : ∀ w, ∀ st : TblSt 40 A, st.val 0 = es.sum → st.val 1 = ℓ → st.val 2 = K →
      st.val 3 = es.length → st.val 4 = B → st.acc = [] →
      TblDo A W w cX st (fun s => s.acc.reverse = ldlXcStream A w xs) KX)
    (wl : List (Fin (A + 4))) (hwl : wl.length = W) (R : Fin T → List (Fin (A + 4)))
    (hR : ∀ r, R (ldgRv gr r) = ldgIdle wl [] r) (hN : (R (gr .uN)).length = es.sum)
    (hL : (R (gr .uL)).length = ℓ) (hK : (R (gr .uK)).length = K)
    (hD : (R (gr .uD)).length = es.length) (hB : (R (gr .uB)).length = B)
    (hEv : R (gr .eW) = binSyms W E) (hdM : R (lr .dM) = []) (hdX : R (lr .dX) = [])
    (hcN : R (lr .cN) = []) (hcW : R (lr .cW) = []) (hcM : R (rg .cM) = [])
    (hcX : R (rg .cX) = []) (htc : R (gr .tc) = []) :
    LayRuns body (ldgWriter rg lr gr cX) R
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update R (lr .dM) (ldlBitStream A es.sum (layBits es ℓ K))) (rg .cM)
        (ldlBitStream A 1 (layBits es ℓ K))) (lr .dX) (ldlXcStream A (es.sum + B + 2) xs))
        (rg .cX) (List.replicate xs.length tick)) (lr .cN) (List.replicate es.sum tick))
        (lr .cW) (List.replicate (es.sum + B + 2) tick))
      (ldgWriterCost W es.sum ℓ K es.length B (layB ℓ K) (layBits es ℓ K).length xs.length KX) := by
  have rl := hg.l.rl
  have lr' := hg.l.lr'
  have ri : ∀ x y, rg x = rg y ↔ x = y := fun x y => hg.l.rg_inj.eq_iff
  have li : ∀ x y, lr x = lr y ↔ x = y := fun x y => hg.l.lr_inj.eq_iff
  have gi : ∀ x y, gr x = gr y ↔ x = y := fun x y => hg.gr_inj.eq_iff
  have g1 : ∀ x y, (gr x = rg y) ↔ False := fun x y => ⟨hg.disj_rg x y, False.elim⟩
  have g2 : ∀ x y, (rg y = gr x) ↔ False := fun x y => ⟨fun e => hg.disj_rg x y e.symm, False.elim⟩
  have g3 : ∀ x y, (gr x = lr y) ↔ False := fun x y => ⟨hg.disj_lr x y, False.elim⟩
  have g4 : ∀ x y, (lr y = gr x) ↔ False := fun x y => ⟨fun e => hg.disj_lr x y e.symm, False.elim⟩
  have hrv : Function.Injective (ldgRv gr) := fun a b e => by
    have := hg.gr_inj e; simpa using this
  have nv : ∀ (r : TblR 40) (x : LdgReg), (∀ r', x ≠ .tbl r') → ldgRv gr r ≠ gr x := by
    intro r x hx e
    exact hx r (hg.gr_inj e).symm
  have nrg : ∀ (r : TblR 40) (y : LayReg t₀), ldgRv gr r ≠ rg y := fun r y => hg.disj_rg _ y
  have nlr : ∀ (r : TblR 40) (y : LdlReg), ldgRv gr r ≠ lr y := fun r y => hg.disj_lr _ y
  have hDN := ldw_length_le_sum H
  have hℓ := H.ℓ_ge
  -- the file is idle on the table registers except `wn`
  have idle : ∀ (R' : Fin T → List (Fin (A + 4))) (nl : List (Fin (A + 4))),
      (∀ r, r ≠ .wn → R' (ldgRv gr r) = R (ldgRv gr r)) → R' (ldgRv gr .wn) = nl →
      ∀ r, R' (ldgRv gr r) = ldgIdle wl nl r := by
    intro R' nl h1 h2 r
    by_cases hr : r = .wn
    · subst hr; rw [h2]; rfl
    · rw [h1 r hr, hR]; cases r <;> first | rfl | exact absurd rfl hr
  have z0 : ∀ R' : Fin T → List (Fin (A + 4)), (∀ r, R' (ldgRv gr r) = ldgIdle wl [] r ∨
      r = .wn) → R' (ldgRv gr (.z 0)) = [] := by
    intro R' h
    rcases h (.z 0) with e | e
    · rw [e]; rfl
    · exact absurd e (by simp)
  have hwn : R (ldgRv gr .wn) = [] := by rw [hR]; rfl
  have hz0 : R (ldgRv gr (.z 0)) = [] := by rw [hR]; rfl
  have hz0' : R (gr (.tbl (.z 0))) = [] := hz0
  -- 1. wn := N ticks
  have s1 := ldg_ucopy_runs (body := body) (a := gr .uN) (b := ldgRv gr .wn) (t := ldgRv gr (.z 0))
    (fun e => nv .wn .uN (by simp) e.symm) (fun e => nv (.z 0) .uN (by simp) e.symm)
    (hrv.ne (by simp)) R hz0
  rw [hN, hwn, List.append_nil] at s1
  set R1 := Function.update R (ldgRv gr .wn) (List.replicate es.sum tick) with hR1
  -- 2. the single-bit move stream onto dM
  have s2 := ldg_run1_runs (body := body) hrv H hE hEW hW hNW h2W hℓW (w := es.sum) hNW.le
    (uN := gr .uN) (uL := gr .uL) (uK := gr .uK) (uD := gr .uD) (eW := gr .eW) (out := lr .dM)
    (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp))
    (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp)) (fun r => nlr r _) wl
    (List.replicate es.sum tick) hwl (by simp) R1
    (idle R1 _ (fun r hr => by simp [hR1, Function.update_apply, ldgRv, gi, hr, g1, g2, g3, g4, rl, lr', ri, li])
      (by simp [hR1, g1, g2, g3, g4, rl, lr', ri, li, gi]))
    (by simp [hR1, Function.update_apply, ldgRv, gi, hN, g1, g2, g3, g4, rl, lr', ri, li])
    (by simp [hR1, Function.update_apply, ldgRv, gi, hL, g1, g2, g3, g4, rl, lr', ri, li])
    (by simp [hR1, Function.update_apply, ldgRv, gi, hK, g1, g2, g3, g4, rl, lr', ri, li])
    (by simp [hR1, Function.update_apply, ldgRv, gi, hD, g1, g2, g3, g4, rl, lr', ri, li])
    (by simp [hR1, Function.update_apply, ldgRv, gi, hEv, g1, g2, g3, g4, rl, lr', ri, li])
  rw [show R1 (lr .dM) = [] by simp [hR1, Function.update_apply, ldgRv, g4, hdM, g1, g2, g3, rl, lr', ri, li, gi],
    List.append_nil] at s2
  set R2 := Function.update R1 (lr .dM) (ldlBitStream A es.sum (layBits es ℓ K)) with hR2
  -- 3. wn := []; 4. wn := one tick
  have s3 := ldl_uclear_runs (body := body) (ldgRv gr .wn) R2
  rw [show (R2 (ldgRv gr .wn)).length = es.sum by
    simp [hR2, hR1, Function.update_apply, ldgRv, g3, g1, g2, g4, rl, lr', ri, li, gi]] at s3
  set R3 := Function.update R2 (ldgRv gr .wn) [] with hR3
  have s4 := ldg_tick_runs (body := body) (ldgRv gr .wn) R3
  rw [show R3 (ldgRv gr .wn) = [] by simp [hR3, g1, g2, g3, g4, rl, lr', ri, li, gi]] at s4
  set R4 := Function.update R3 (ldgRv gr .wn) [tick] with hR4
  -- 5. one symbol per move onto cM
  have s5 := ldg_run1_runs (body := body) hrv H hE hEW hW hNW h2W hℓW (w := 1) (by omega)
    (uN := gr .uN) (uL := gr .uL) (uK := gr .uK) (uD := gr .uD) (eW := gr .eW) (out := rg .cM)
    (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp))
    (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp)) (fun r => nrg r _) wl
    [tick] hwl (by simp) R4
    (idle R4 _ (fun r hr => by simp [hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g3, hr, g1, g2, g4, rl, lr', ri, li])
      (by simp [hR4, g1, g2, g3, g4, rl, lr', ri, li, gi]))
    (by simp [hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g4, hN, g1, g2, g3, rl, lr', ri, li])
    (by simp [hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g4, hL, g1, g2, g3, rl, lr', ri, li])
    (by simp [hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g4, hK, g1, g2, g3, rl, lr', ri, li])
    (by simp [hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g4, hD, g1, g2, g3, rl, lr', ri, li])
    (by simp [hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g4, hEv, g1, g2, g3, rl, lr', ri, li])
  rw [show R4 (rg .cM) = [] by simp [hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, g2, rl, hcM, g1, g3, g4, lr', ri, li, gi],
    List.append_nil] at s5
  set R5 := Function.update R4 (rg .cM) (ldlBitStream A 1 (layBits es ℓ K)) with hR5
  -- 6. wn := []; 7–10. wn := N + B + 2 ticks
  have s6 := ldl_uclear_runs (body := body) (ldgRv gr .wn) R5
  rw [show (R5 (ldgRv gr .wn)).length = 1 by simp [hR5, hR4, Function.update_apply, ldgRv, g1, g2, g3, g4, rl, lr', ri, li, gi]]
    at s6
  set R6 := Function.update R5 (ldgRv gr .wn) [] with hR6
  have s7 := ldg_ucopy_runs (body := body) (a := gr .uN) (b := ldgRv gr .wn) (t := ldgRv gr (.z 0))
    (fun e => nv .wn .uN (by simp) e.symm) (fun e => nv (.z 0) .uN (by simp) e.symm)
    (hrv.ne (by simp)) R6
    (by simp [hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g3, hz0', hz0, g2, g4, rl, lr', ri, li])
  rw [show (R6 (gr .uN)).length = es.sum by
      simp [hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g2, g4, hN, g1, g3, rl, lr', ri, li],
    show R6 (ldgRv gr .wn) = [] by simp [hR6, g1, g2, g3, g4, rl, lr', ri, li, gi], List.append_nil] at s7
  set R7 := Function.update R6 (ldgRv gr .wn) (List.replicate es.sum tick) with hR7
  have s8 := ldg_ucopy_runs (body := body) (a := gr .uB) (b := ldgRv gr .wn) (t := ldgRv gr (.z 0))
    (fun e => nv .wn .uB (by simp) e.symm) (fun e => nv (.z 0) .uB (by simp) e.symm)
    (hrv.ne (by simp)) R7
    (by simp [hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g3, hz0', hz0, g2, g4, rl, lr', ri, li])
  rw [show (R7 (gr .uB)).length = B by
      simp [hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g2, g4, hB, g1, g3, rl, lr', ri, li],
    show R7 (ldgRv gr .wn) = List.replicate es.sum tick by simp [hR7, g1, g2, g3, g4, rl, lr', ri, li, gi]] at s8
  set R8 := Function.update R7 (ldgRv gr .wn) (List.replicate B tick ++ List.replicate es.sum tick)
    with hR8
  have s9 := ldg_tick_runs (body := body) (ldgRv gr .wn) R8
  set R9 := Function.update R8 (ldgRv gr .wn) (tick :: R8 (ldgRv gr .wn)) with hR9
  have s10 := ldg_tick_runs (body := body) (ldgRv gr .wn) R9
  set R10 := Function.update R9 (ldgRv gr .wn) (tick :: R9 (ldgRv gr .wn)) with hR10
  have hwn10 : R10 (ldgRv gr .wn) = List.replicate (es.sum + B + 2) tick := by
    simp only [hR10, hR9, hR8, Function.update_self]
    rw [List.replicate_append_replicate]
    simp [List.replicate_succ, show es.sum + B + 2 = (B + es.sum) + 1 + 1 by omega, g1, g2, g3, g4, rl, lr', ri, li, gi]
  -- 11. the exchange stream onto dX
  have hXa : ∀ w, ∀ st : TblSt 40 A, st.val 0 = es.sum → st.val 1 = ℓ → st.val 2 = K →
      st.val 3 = es.length → st.val 4 = B → st.acc = [] →
      TblDo A W w cX st (fun s => s.acc.reverse = ldlXcStream A w xs) KX := hX
  have hN2 : es.sum < 2 ^ W := lt_of_lt_of_le hNW (Nat.lt_two_pow_self).le
  have hB2 : B < 2 ^ W := lt_of_lt_of_le (by omega : B < W) (Nat.lt_two_pow_self).le
  have hK2 : K < 2 ^ W := lt_of_le_of_lt (by have := H.K_le; omega) hℓW
  have hD2 : es.length < 2 ^ W := lt_of_le_of_lt hDN hN2
  have s11 := ldg_runU_runs (body := body) hrv (c := cX) (W := W) (w := es.sum + B + 2) (Kc := KX)
    (x0 := es.sum) (x1 := ℓ) (x2 := K) (x3 := es.length) (x4 := B)
    (ldlXcStream A (es.sum + B + 2) xs) (hXa _) hN2 hℓW hK2 hD2 hB2 hBW
    (u0 := gr .uN) (u1 := gr .uL) (u2 := gr .uK) (u3 := gr .uD) (u4 := gr .uB) (out := lr .dX)
    (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp))
    (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp)) (fun r => nlr r _) wl
    (List.replicate (es.sum + B + 2) tick) hwl (by simp) R10
    (idle R10 _ (fun r hr => by
      simp [hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g3, g1, hr, g2, g4, rl, lr', ri, li]) hwn10)
    (by simp [hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g2, g4, hN, g1, g3, rl, lr', ri, li])
    (by simp [hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g2, g4, hL, g1, g3, rl, lr', ri, li])
    (by simp [hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g2, g4, hK, g1, g3, rl, lr', ri, li])
    (by simp [hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g2, g4, hD, g1, g3, rl, lr', ri, li])
    (by simp [hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g2, g4, hB, g1, g3, rl, lr', ri, li])
  rw [show R10 (lr .dX) = [] by
    simp [hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, g4, li, rl, hdX, g1, g2, g3, lr', ri, gi], List.append_nil] at s11
  set R11 := Function.update R10 (lr .dX) (ldlXcStream A (es.sum + B + 2) xs) with hR11
  -- 12. wn := []; 13. one tick
  have s12 := ldl_uclear_runs (body := body) (ldgRv gr .wn) R11
  rw [show (R11 (ldgRv gr .wn)).length = es.sum + B + 2 by
    show (Function.update R10 (lr .dX) _ (ldgRv gr .wn)).length = _
    rw [Function.update_of_ne (show ldgRv gr .wn ≠ lr .dX from hg.disj_lr _ _), hwn10]
    simp] at s12
  set R12 := Function.update R11 (ldgRv gr .wn) [] with hR12
  have s13 := ldg_tick_runs (body := body) (ldgRv gr .wn) R12
  rw [show R12 (ldgRv gr .wn) = [] by simp [hR12]] at s13
  set R13 := Function.update R12 (ldgRv gr .wn) [tick] with hR13
  -- 14. one symbol per word onto tc
  have s14 := ldg_runU_runs (body := body) hrv (c := cX) (W := W) (w := 1) (Kc := KX)
    (x0 := es.sum) (x1 := ℓ) (x2 := K) (x3 := es.length) (x4 := B)
    (ldlXcStream A 1 xs) (hXa _) hN2 hℓW hK2 hD2 hB2 (by omega)
    (u0 := gr .uN) (u1 := gr .uL) (u2 := gr .uK) (u3 := gr .uD) (u4 := gr .uB) (out := gr .tc)
    (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp))
    (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp)) (fun r => nv r _ (by simp)) wl
    [tick] hwl (by simp) R13
    (idle R13 _ (fun r hr => by
      simp [hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li, hr]) (by simp [hR13]))
    (by simp [hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li, hN])
    (by simp [hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li, hL])
    (by simp [hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li, hK])
    (by simp [hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li, hD])
    (by simp [hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li, hB])
  rw [show R13 (gr .tc) = [] by
    simp [hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li, htc],
    List.append_nil] at s14
  set R14 := Function.update R13 (gr .tc) (ldlXcStream A 1 xs) with hR14
  -- 15. wn := []
  have s15 := ldl_uclear_runs (body := body) (ldgRv gr .wn) R14
  rw [show (R14 (ldgRv gr .wn)).length = 1 by
    simp [hR14, hR13, Function.update_apply, ldgRv, gi]] at s15
  set R15 := Function.update R14 (ldgRv gr .wn) [] with hR15
  -- 16. cX := |tc| / 5 ticks; 17. tc := []
  have s16 := ldg_udiv_runs (body := body) (c := 5) (by norm_num) (a := gr .tc) (b := rg .cX)
    (t := ldgRv gr (.z 0)) (hg.disj_rg _ _) (fun e => nv (.z 0) .tc (by simp) e.symm)
    (fun e => hg.disj_rg _ _ e.symm) R15
    (by simp [hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3,
      g4, rl, lr', ri, li, hz0', hz0])
  rw [show (R15 (gr .tc)).length = 5 * 1 * xs.length by
      simp [hR15, hR14, Function.update_apply, ldgRv, gi, length_ldlXcStream],
    show 5 * 1 * xs.length / 5 = xs.length by omega,
    show R15 (rg .cX) = [] by
      simp [hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4,
        ri, rl, lr', li, hcX], List.append_nil] at s16
  set R16 := Function.update R15 (rg .cX) (List.replicate xs.length tick) with hR16
  have s17 := ldl_uclear_runs (body := body) (gr .tc) R16
  rw [show (R16 (gr .tc)).length = 5 * 1 * xs.length by
    simp [hR16, hR15, hR14, Function.update_apply, ldgRv, gi, g1, length_ldlXcStream]] at s17
  set R17 := Function.update R16 (gr .tc) [] with hR17
  -- 18. cN := N ticks; 19–22. cW := N + B + 2 ticks
  have s18 := ldg_ucopy_runs (body := body) (a := gr .uN) (b := lr .cN) (t := ldgRv gr (.z 0))
    (hg.disj_lr _ _) (fun e => nv (.z 0) .uN (by simp) e.symm) (fun e => hg.disj_lr _ _ e.symm) R17
    (by simp [hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1,
      g2, g3, g4, rl, lr', ri, li, hz0', hz0])
  rw [show (R17 (gr .uN)).length = es.sum by
      simp [hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1,
        g2, g3, g4, rl, lr', ri, li, hN],
    show R17 (lr .cN) = [] by
      simp [hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1,
        g2, g3, g4, li, rl, lr', ri, hcN], List.append_nil] at s18
  set R18 := Function.update R17 (lr .cN) (List.replicate es.sum tick) with hR18
  have s19 := ldg_ucopy_runs (body := body) (a := gr .uN) (b := lr .cW) (t := ldgRv gr (.z 0))
    (hg.disj_lr _ _) (fun e => nv (.z 0) .uN (by simp) e.symm) (fun e => hg.disj_lr _ _ e.symm) R18
    (by simp [hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv,
      gi, g1, g2, g3, g4, rl, lr', ri, li, hz0', hz0])
  rw [show (R18 (gr .uN)).length = es.sum by
      simp [hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi,
        g1, g2, g3, g4, rl, lr', ri, li, hN],
    show R18 (lr .cW) = [] by
      simp [hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi,
        g1, g2, g3, g4, li, rl, lr', ri, hcW], List.append_nil] at s19
  set R19 := Function.update R18 (lr .cW) (List.replicate es.sum tick) with hR19
  have s20 := ldg_ucopy_runs (body := body) (a := gr .uB) (b := lr .cW) (t := ldgRv gr (.z 0))
    (hg.disj_lr _ _) (fun e => nv (.z 0) .uB (by simp) e.symm) (fun e => hg.disj_lr _ _ e.symm) R19
    (by simp [hR19, hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply,
      ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li, hz0', hz0])
  rw [show (R19 (gr .uB)).length = B by
      simp [hR19, hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply,
        ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li, hB],
    show R19 (lr .cW) = List.replicate es.sum tick by simp [hR19]] at s20
  set R20 := Function.update R19 (lr .cW) (List.replicate B tick ++ List.replicate es.sum tick)
    with hR20
  have s21 := ldg_tick_runs (body := body) (lr .cW) R20
  set R21 := Function.update R20 (lr .cW) (tick :: R20 (lr .cW)) with hR21
  have s22 := ldg_tick_runs (body := body) (lr .cW) R21
  refine ((s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq (s8.seq (s9.seq (s10.seq
    (s11.seq (s12.seq (s13.seq (s14.seq (s15.seq (s16.seq (s17.seq (s18.seq (s19.seq (s20.seq
    (s21.seq s22))))))))))))))))))))).mono ?_).congr ?_
  · simp only [length_ldlBitStream, length_ldlXcStream]
    exact ldg_writerCost_le _ _ _ _ _ _ _ _ _ _
  · have hcW22 : tick :: R21 (lr .cW) = List.replicate (es.sum + B + 2) tick := by
      simp only [hR21, hR20, Function.update_self]
      rw [List.replicate_append_replicate]
      simp [List.replicate_succ, show es.sum + B + 2 = (B + es.sum) + 1 + 1 by omega]
    rw [hcW22]
    funext y
    have hwn' : R (gr (.tbl .wn)) = [] := hwn
    by_cases h1 : y = lr .cW
    · subst h1; simp only [Function.update_self]
    by_cases h2 : y = lr .cN
    · subst h2
      simp [hR21, hR20, hR19, hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li]
    by_cases h3 : y = lr .dM
    · subst h3
      simp [hR21, hR20, hR19, hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li]
    by_cases h4 : y = lr .dX
    · subst h4
      simp [hR21, hR20, hR19, hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li]
    by_cases h5 : y = rg .cM
    · subst h5
      simp [hR21, hR20, hR19, hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li]
    by_cases h6 : y = rg .cX
    · subst h6
      simp [hR21, hR20, hR19, hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li]
    by_cases h7 : y = ldgRv gr .wn
    · subst h7
      simp [hR21, hR20, hR19, hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li, hwn']
    by_cases h8 : y = gr .tc
    · subst h8
      simp [hR21, hR20, hR19, hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, ldgRv, gi, g1, g2, g3, g4, rl, lr', ri, li, htc]
    have h7' : ¬ y = gr (.tbl .wn) := h7
    simp [h7', hR21, hR20, hR19, hR18, hR17, hR16, hR15, hR14, hR13, hR12, hR11, hR10, hR9, hR8, hR7, hR6, hR5, hR4, hR3, hR2, hR1, Function.update_apply, h1, h2, h3, h4, h5, h6, h7, h8]

end WriterRuns

end IntegerMultBounds.MathlibTM2.Fast.TableVM
