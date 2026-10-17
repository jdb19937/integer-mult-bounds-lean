module
public import IntegerMultBounds.MathlibTM2.Fast.TableProg
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.ENatToNat
public import IntegerMultBounds.MathlibTM2.Fast.CMulArith


/-!
# Run contracts and pushes of the parameter distribution machine

The distribution machine (`Fast/Dist.lean`) runs after the parameter machine
(`Fast/ParamMachine.lean`) on its table layout `rg : TblR pmNV → Fin T` and on registers outside
the layout. This file gives the contract form and the primitive programs.

* `dsRuns body p R₀ R₁ c`: from every store with register file `R₀`, `p` reaches the same store
  with register file `R₁` within `c` steps, `user` kept (input, output and left stacks unchanged).
* `dsOv rg R ρ`: the register file equal to `ρ` on the layout `rg` and to `R` off it.
  `ds_tbl`: a table contract `tblRuns` between `ρ` and `ρ'` is a `dsRuns` contract between
  `dsOv rg R ρ` and `dsOv rg R ρ'` for every `R`.
* `dsUn rg x o`: `toUnary` from variable `x` onto the register `o` off the layout: `o` gains
  `val x` ticks, in at most `W (4 x + 11) + 2 x + 6` steps (`ds_un`).
* `dsSep o`: push the separator `bitSymbol false` onto `o` (one step).
* `dsPush rg ps`: for each item `(o, x, b)` of `ps`, push the field of `val x`: the separator and
  then `val x` ticks (`b = false`, the block `dsFld (val x)` on top), or the ticks and then the
  separator (`b = true`, the block reversed). `ds_push`: register `k` gains `dsOut val ps k`
  on top (`dsGain_eq`).
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer


/-! ### The contract -/

section Runs

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- `p` takes every store with register file `R₀` to the same store with register file `R₁`,
`user` kept, within `c` steps. -/
def dsRuns (p : Pr P T Q A U) (R₀ R₁ : Regs T A) (c : ℕ) : Prop :=
  ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R₀ →
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ c ∧
      Exec body p (mk v S) m (mk v' { S with R := R₁ })

variable {body}

theorem dsRuns.seq {p q : Pr P T Q A U} {R₀ R₁ R₂ : Regs T A} {c₁ c₂ : ℕ}
    (h₁ : dsRuns body p R₀ R₁ c₁) (h₂ : dsRuns body q R₁ R₂ c₂) :
    dsRuns body (.seq p q) R₀ R₂ (c₁ + c₂) := by
  intro v S hS
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := h₁ v S hS
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := h₂ v₁ { S with R := R₁ } rfl
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

theorem dsRuns.mono {p : Pr P T Q A U} {R₀ R₁ : Regs T A} {c c' : ℕ}
    (h : dsRuns body p R₀ R₁ c) (hc : c ≤ c') : dsRuns body p R₀ R₁ c' := by
  intro v S hS
  obtain ⟨v', m, hu, hm, he⟩ := h v S hS
  exact ⟨v', m, hu, hm.trans hc, he⟩

theorem dsRuns.congr {p : Pr P T Q A U} {R₀ R₁ R₁' : Regs T A} {c : ℕ}
    (h : dsRuns body p R₀ R₁ c) (e : R₁ = R₁') : dsRuns body p R₀ R₁' c := e ▸ h

theorem dsRuns.congr_left {p : Pr P T Q A U} {R₀ R₀' R₁ : Regs T A} {c : ℕ}
    (h : dsRuns body p R₀ R₁ c) (e : R₀' = R₀) : dsRuns body p R₀' R₁ c := e ▸ h

/-- Turn an execution with an explicit final register file into a contract. -/
theorem dsRuns_of_exec {p : Pr P T Q A U} {R₀ R₁ : Regs T A} {c : ℕ}
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R₀ →
      ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ c ∧
        Exec body p (mk v S) m (mk v' { S with R := R₁ })) : dsRuns body p R₀ R₁ c := h

/-- A single action. -/
theorem ds_act (a : Act T Q A U) (R₀ R₁ : Regs T A)
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), S.R = R₀ →
      ∃ v' : HS T Q A U, v'.user = v.user ∧ a.run (mk v S) = mk v' { S with R := R₁ }) :
    dsRuns body (.act a) R₀ R₁ 1 := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := h v S hS
  exact ⟨v', 1, hu, le_rfl, he ▸ Exec.act a (mk v S)⟩

/-- `moveR i j id`: `j` gains `i` reversed on top, `i` is emptied. -/
theorem ds_moveR {i j : Fin T} (hij : i ≠ j) (R : Regs T A) :
    dsRuns body (moveR i j id) R
      (Function.update (Function.update R i []) j ((R i).reverse ++ R j)) (2 * (R i).length + 2) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := moveR_exec body i j hij id v S
  refine ⟨v', 2 * (S.R i).length + 2, hu, by rw [hS], ?_⟩
  convert he using 3
  simp [movedR, hS]

/-- `uclear a`: `a` is emptied. -/
theorem ds_uclear (a : Fin T) (R : Regs T A) :
    dsRuns body (uclear a) R (Function.update R a []) (2 * (R a).length + 2) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := uclear_exec body a v S
  refine ⟨v', 2 * (S.R a).length + 2, hu, by rw [hS], ?_⟩
  convert he using 3
  rw [hS]

end Runs

/-! ### Register files over a table layout -/

section Overlay

variable {T A : ℕ} {ι : Type}

open Classical in
/-- The register file equal to `ρ` on the registers `rg` and to `R` off them. -/
noncomputable def dsOv (rg : ι → Fin T) (R : Regs T A) (ρ : ι → List (Fin (A + 4))) :
    Regs T A :=
  fun k => if h : ∃ r, rg r = k then ρ h.choose else R k

variable {rg : ι → Fin T}

theorem dsOv_rg (hrg : Function.Injective rg) (R : Regs T A) (ρ : ι → List (Fin (A + 4)))
    (r : ι) : dsOv rg R ρ (rg r) = ρ r := by
  have h : ∃ r', rg r' = rg r := ⟨r, rfl⟩
  simp only [dsOv, dite_eq_left h]
  rw [hrg h.choose_spec]

theorem dsOv_off (R : Regs T A) (ρ : ι → List (Fin (A + 4))) {k : Fin T}
    (hk : ∀ r, rg r ≠ k) : dsOv rg R ρ k = R k := by
  have h : ¬ ∃ r, rg r = k := fun ⟨r, hr⟩ => hk r hr
  simp only [dsOv, dite_eq_right h]

theorem dsOv_update (R : Regs T A) (ρ : ι → List (Fin (A + 4))) {k : Fin T}
    (hk : ∀ r, rg r ≠ k) (x : List (Fin (A + 4))) :
    Function.update (dsOv rg R ρ) k x = dsOv rg (Function.update R k x) ρ := by
  funext j
  by_cases h : ∃ r, rg r = j
  · obtain ⟨r, rfl⟩ := h
    rw [Function.update_of_ne (hk r)]
    simp only [dsOv, dite_eq_left (show ∃ r', rg r' = rg r from ⟨r, rfl⟩)]
  · by_cases hj : j = k
    · subst hj
      simp only [Function.update_self, dsOv, dite_eq_right h]
    · rw [Function.update_of_ne hj]
      simp only [dsOv, dite_eq_right h, Function.update_of_ne hj]

theorem dsOv_update_on [DecidableEq ι] (hrg : Function.Injective rg) (R : Regs T A)
    (ρ : ι → List (Fin (A + 4)))
    (x : ι) (v : List (Fin (A + 4))) :
    Function.update (dsOv rg R ρ) (rg x) v = dsOv rg R (Function.update ρ x v) := by
  funext k
  by_cases h : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := h
    rw [dsOv_rg hrg]
    by_cases hrx : r = x
    · subst hrx; simp
    · rw [Function.update_of_ne (hrg.ne hrx), Function.update_of_ne hrx, dsOv_rg hrg]
  · push Not at h
    rw [Function.update_of_ne (fun e => h x e.symm), dsOv_off _ _ h, dsOv_off _ _ h]

theorem dsOv_eq_of (hrg : Function.Injective rg) {R : Regs T A} {ρ : ι → List (Fin (A + 4))}
    {X : Regs T A} (h1 : ∀ r, X (rg r) = ρ r) (h2 : ∀ k, (∀ r, rg r ≠ k) → X k = R k) :
    X = dsOv rg R ρ := by
  funext k
  by_cases h : ∃ r, rg r = k
  · obtain ⟨r, rfl⟩ := h
    rw [h1, dsOv_rg hrg]
  · push Not at h
    rw [h2 k h, dsOv_off R ρ h]

theorem dsOv_self (hrg : Function.Injective rg) (R : Regs T A) :
    dsOv rg R (fun r => R (rg r)) = R :=
  (dsOv_eq_of hrg (fun _ => rfl) (fun _ _ => rfl)).symm

end Overlay

section Tbl

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {n : ℕ} {rg : TblR n → Fin T}

/-- A table contract is a register-file contract over every file off the layout. -/
theorem ds_tbl (hrg : Function.Injective rg) {p : Pr P T Q A U}
    {ρ ρ' : TblR n → List (Fin (A + 4))} {c : ℕ} (h : tblRuns body rg p ρ ρ' c) (R : Regs T A) :
    dsRuns body p (dsOv rg R ρ) (dsOv rg R ρ') c := by
  intro v S hS
  obtain ⟨v', S', m, hu, hm, he, hS', hf⟩ := h v S (fun r => by rw [hS, dsOv_rg hrg])
  refine ⟨v', m, hu, hm, ?_⟩
  have e : S' = { S with R := dsOv rg R ρ' } := by
    cases S' with
    | mk inp out L R' =>
      obtain ⟨h1, h2, h3, h4⟩ := hf
      simp only at h1 h2 h3 h4
      subst h1 h2 h3
      congr 1
      refine dsOv_eq_of hrg (fun r => hS' r) (fun k hk => ?_)
      rw [h4 k hk, hS, dsOv_off R ρ hk]
  rw [← e]
  exact he

/-- A compiled table program from a terminating derivation. -/
theorem ds_code (hrg : Function.Injective rg) {W w : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = w) (hw : w ≤ W) {c : TblCode n}
    {st st' : TblSt n A} {K : ℕ} (h : TblDo A W w c st (· = st') K)
    (hst : ∀ j, st.val j < 2 ^ W) (R : Regs T A) :
    dsRuns body (tblCompile rg c) (dsOv rg R (tblRho W wl nl st)) (dsOv rg R (tblRho W wl nl st'))
      (K * tblC W w) := by
  obtain ⟨s, hs, hr⟩ := TblDo.host (body := body) hrg wl nl hwl hnl hw h hst
  subst hs
  exact ds_tbl hrg hr R

end Tbl

/-! ### Unary pushes -/

section Push

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {n : ℕ} {rg : TblR n → Fin T}

/-- `toUnary` from variable `x` onto the register `o`, through `z 0`, `z 1`, `z 2`. -/
def dsUn (rg : TblR n → Fin T) (x : Fin n) (o : Fin T) : Pr P T Q A U :=
  toUnary (rg (.v x)) o (rg (.z 0)) (rg (.z 1)) (rg (.z 2))

/-- Push the separator `bitSymbol false` onto `o`. -/
def dsSep (o : Fin T) : Pr P T Q A U := .act (.push (.rt o) (fun _ => bitSymbol false) .done)

/-- The modes of a push item. -/
inductive DsMode
  | fld | rev | ent
  deriving DecidableEq

/-- A unary field: `v` ticks above the separator. -/
def dsFld (v : ℕ) : List (Fin (A + 4)) := List.replicate v tick ++ [bitSymbol false]

/-- The block of a push item: the field (`fld`), the field reversed (`rev`), or the field below
a separator (`ent`, the entry `crtEnt v` of the CRT machines). -/
def dsBlk : DsMode → ℕ → List (Fin (A + 4))
  | .fld, v => dsFld v
  | .rev, v => (dsFld v).reverse
  | .ent, v => bitSymbol false :: dsFld v

/-- One push item: the separator, then the ticks (`fld`); the ticks, then the separator
(`rev`); a separator, the ticks, a separator (`ent`). -/
def dsPush1 (rg : TblR n → Fin T) (o : Fin T) (x : Fin n) : DsMode → Pr P T Q A U
  | .fld => .seq (dsSep o) (dsUn rg x o)
  | .rev => .seq (dsUn rg x o) (dsSep o)
  | .ent => .seq (dsSep o) (.seq (dsUn rg x o) (dsSep o))

/-- A list of push items. -/
def dsPush (rg : TblR n → Fin T) : List (Fin T × Fin n × DsMode) → Pr P T Q A U
  | [] => .act .done
  | (o, x, b) :: l => .seq (dsPush1 rg o x b) (dsPush rg l)

/-- The register file after the pushes `ps` with variable values `val`. -/
def dsGain (val : Fin n → ℕ) : List (Fin T × Fin n × DsMode) → Regs T A → Regs T A
  | [], R => R
  | (o, x, b) :: l, R => dsGain val l (Function.update R o (dsBlk b (val x) ++ R o))

/-- What register `k` gains from the pushes `ps`, top first. -/
def dsOut (val : Fin n → ℕ) (ps : List (Fin T × Fin n × DsMode)) (k : Fin T) :
    List (Fin (A + 4)) :=
  ((ps.filter fun e => decide (e.1 = k)).reverse).flatMap fun e => dsBlk e.2.2 (val e.2.1)

/-- The step bound of the pushes. -/
def dsPushCost (W : ℕ) (val : Fin n → ℕ) (ps : List (Fin T × Fin n × DsMode)) : ℕ :=
  (ps.map fun e => W * (4 * val e.2.1 + 11) + 2 * val e.2.1 + 8).sum + 1

theorem dsOut_nil (val : Fin n → ℕ) (k : Fin T) : dsOut (A := A) val [] k = [] := rfl

theorem dsOut_cons (val : Fin n → ℕ) (o : Fin T) (x : Fin n) (b : DsMode)
    (l : List (Fin T × Fin n × DsMode)) (k : Fin T) :
    dsOut (A := A) val ((o, x, b) :: l) k =
      dsOut val l k ++ if o = k then dsBlk b (val x) else [] := by
  unfold dsOut
  by_cases h : o = k
  · simp [h]
  · simp [h]

theorem dsOut_append (val : Fin n → ℕ) (l₁ l₂ : List (Fin T × Fin n × DsMode)) (k : Fin T) :
    dsOut (A := A) val (l₁ ++ l₂) k = dsOut val l₂ k ++ dsOut val l₁ k := by
  unfold dsOut
  simp [List.filter_append, List.reverse_append, List.flatMap_append]

theorem dsGain_eq (val : Fin n → ℕ) :
    ∀ (ps : List (Fin T × Fin n × DsMode)) (R : Regs T A) (k : Fin T),
      dsGain val ps R k = dsOut val ps k ++ R k
  | [], R, k => rfl
  | (o, x, b) :: l, R, k => by
    rw [dsGain, dsGain_eq val l, dsOut_cons, List.append_assoc]
    congr 1
    by_cases h : o = k
    · subst h; simp
    · simp [h, Function.update_of_ne (Ne.symm h)]

variable (hrg : Function.Injective rg)
include hrg

theorem ds_un {o : Fin T} (ho : ∀ r, rg r ≠ o) {W : ℕ} (wl nl : List (Fin (A + 4)))
    (st : TblSt n A) (x : Fin n) (hx : st.val x < 2 ^ W) (R : Regs T A) :
    dsRuns body (dsUn rg x o) (dsOv rg R (tblRho W wl nl st))
      (dsOv rg (Function.update R o (List.replicate (st.val x) tick ++ R o)) (tblRho W wl nl st))
      (W * (4 * st.val x + 11) + 2 * st.val x + 6) := by
  intro v S hS
  have hreg : [rg (.v x), o, rg (.z 0), rg (.z 1), rg (.z 2)].Nodup := by
    have h3 := tbl_nodup hrg (l := [.v x, .z 0, .z 1, .z 2]) (by simp)
    simp only [List.map_cons, List.map_nil] at h3
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h3 ⊢
    exact ⟨⟨fun h => ho _ h, h3.1.1, h3.1.2.1, h3.1.2.2⟩, ⟨fun h => ho _ h.symm,
      fun h => ho _ h.symm, fun h => ho _ h.symm⟩, h3.2⟩
  obtain ⟨v', m, hu, hm, he⟩ := toUnary_exec body hreg hx v S
    (by rw [hS, dsOv_rg hrg]; rfl) (by rw [hS, dsOv_rg hrg]; rfl) (by rw [hS, dsOv_rg hrg]; rfl)
    (by rw [hS, dsOv_rg hrg]; rfl)
  refine ⟨v', m, hu, hm, ?_⟩
  have e : Function.update S.R o (List.replicate (st.val x) tick ++ S.R o) =
      dsOv rg (Function.update R o (List.replicate (st.val x) tick ++ R o)) (tblRho W wl nl st) := by
    rw [hS, dsOv_off R _ ho, dsOv_update R _ ho]
  rw [← e]
  exact he

omit hrg in
theorem ds_sep (o : Fin T) (R : Regs T A) :
    dsRuns body (dsSep o) R (Function.update R o (bitSymbol false :: R o)) 1 := by
  refine ds_act _ R _ fun v S hS => ⟨v, rfl, ?_⟩
  simp [Action.run, update_rt, hS]

theorem ds_push1 {o : Fin T} (ho : ∀ r, rg r ≠ o) {W : ℕ} (wl nl : List (Fin (A + 4)))
    (st : TblSt n A) (x : Fin n) (hx : st.val x < 2 ^ W) (b : DsMode) (R : Regs T A) :
    dsRuns body (dsPush1 rg o x b) (dsOv rg R (tblRho W wl nl st))
      (dsOv rg (Function.update R o (dsBlk b (st.val x) ++ R o)) (tblRho W wl nl st))
      (W * (4 * st.val x + 11) + 2 * st.val x + 8) := by
  cases b with
  | fld =>
    have h1 := ds_sep (body := body) o (dsOv rg R (tblRho W wl nl st))
    rw [dsOv_off R _ ho, dsOv_update R _ ho] at h1
    have h2 := ds_un (body := body) hrg ho wl nl st x hx
      (Function.update R o (bitSymbol false :: R o))
    refine ((h1.seq h2).congr ?_).mono (by omega)
    congr 1
    simp [dsBlk, dsFld]
  | rev =>
    have h1 := ds_un (body := body) hrg ho wl nl st x hx R
    have h2 := ds_sep (body := body) o
      (dsOv rg (Function.update R o (List.replicate (st.val x) tick ++ R o)) (tblRho W wl nl st))
    rw [dsOv_off _ _ ho, dsOv_update _ _ ho] at h2
    refine ((h1.seq h2).congr ?_).mono (by omega)
    congr 1
    simp [dsBlk, dsFld]
  | ent =>
    have h1 := ds_sep (body := body) o (dsOv rg R (tblRho W wl nl st))
    rw [dsOv_off R _ ho, dsOv_update R _ ho] at h1
    have h2 := ds_un (body := body) hrg ho wl nl st x hx
      (Function.update R o (bitSymbol false :: R o))
    have h3 := ds_sep (body := body) o
      (dsOv rg (Function.update (Function.update R o (bitSymbol false :: R o)) o
        (List.replicate (st.val x) tick ++ Function.update R o (bitSymbol false :: R o) o))
        (tblRho W wl nl st))
    rw [dsOv_off _ _ ho, dsOv_update _ _ ho] at h3
    refine ((h1.seq (h2.seq h3)).congr ?_).mono (by omega)
    congr 1
    simp [dsBlk, dsFld]

/-- **Pushes.** With the layout carrying `st`, the pushes `ps` onto registers off the layout
leave every register `k` with `dsOut st.val ps k` on top (`dsGain_eq`). -/
theorem ds_push {W : ℕ} (wl nl : List (Fin (A + 4))) (st : TblSt n A) :
    ∀ (ps : List (Fin T × Fin n × DsMode)), (∀ e ∈ ps, ∀ r, rg r ≠ e.1) →
      (∀ e ∈ ps, st.val e.2.1 < 2 ^ W) → ∀ R : Regs T A,
      dsRuns body (dsPush rg ps) (dsOv rg R (tblRho W wl nl st))
        (dsOv rg (dsGain st.val ps R) (tblRho W wl nl st)) (dsPushCost W st.val ps)
  | [], _, _, R => by
    refine (ds_act _ _ _ fun v S hS => ⟨v, rfl, ?_⟩).mono (by simp [dsPushCost])
    have e : ({ S with R := dsOv rg (dsGain st.val [] R) (tblRho W wl nl st) } : Stacks T A) = S := by
      rw [show dsGain st.val [] R = R from rfl, ← hS]
    rw [e]
    rfl
  | (o, x, b) :: l, hps, hv, R => by
    have h1 := ds_push1 (body := body) hrg (hps _ List.mem_cons_self) wl nl st x
      (hv _ List.mem_cons_self) b R
    have h2 := ds_push wl nl st l (fun e he => hps e (List.mem_cons_of_mem _ he))
      (fun e he => hv e (List.mem_cons_of_mem _ he))
      (Function.update R o (dsBlk b (st.val x) ++ R o))
    refine (h1.seq h2).mono ?_
    simp only [dsPushCost, List.map_cons, List.sum_cons]
    omega

end Push

end IntegerMultBounds.MathlibTM2.Fast.TableVM
