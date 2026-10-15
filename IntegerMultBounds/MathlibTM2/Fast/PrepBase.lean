module

public import IntegerMultBounds.MathlibTM2.Fast.TwiddleRuns
public import IntegerMultBounds.MathlibTM2.Fast.Tables
public import IntegerMultBounds.MathlibTM2.Node.SlotXor
public import IntegerMultBounds.MathlibTM2.Fast.ResampARegs
public import IntegerMultBounds.MathlibTM2.Fast.ResampBCore

/-!
# Parameter loaders: host primitives

Generic tools for the per-axis parameter loaders of the resampling stages (`Fast/PrepA.lean`,
`Fast/PrepB.lean`), on the register-file contracts `TwRuns` of `Fast/TwiddleRuns.lean` (an
injective layout `tg : R → Fin T`, no condition on the registers outside it).

**Unary fields.** A parameter is a unary field `preFld v`: `v` ticks followed by the delimiter
`bitSymbol false`; a record is a list of fields (`preRec`). `preTake src dst` moves the ticks of
the field on top of `src` onto `dst` and drops the delimiter (`preTake_runs`, `3 v + 3` steps), by
the loop on the top symbol `preWhileTop` (`twRuns_preWhileTop`). `preTakes src ds` takes
consecutive fields onto the registers `ds` (`preTakes_runs`, register file `preTV`).

**Unary arithmetic.** `preUMul a b c t₁ t₂`: `c` gains `|a| · |b|` ticks (`preUMul_runs`);
contracts of `umul`, `usub`, `toBinary`, `sxBinConv` on the layout; `preClears l` empties the
registers of `l` (`preClears_runs`); `preHdr src h t₁ t₂` writes the canonical interchange
header of `|src|` (`separator` over the binary digits `sxBits |src|`, `preHdr_runs`).

**The table machine.** On a layout `R ⊕ TblR n` (`preT` the table-machine part),
`preVM tg uW uw ls code o` copies the word width `W = |uW|` and the emission width `w = |uw|`,
zeroes every variable (`preZeroVars`), loads the unary registers `ls` into variables
(`preLoads`, `tbl_load1_runs`), runs `code` with its emissions onto `o` (`tblHost_runs`) and
empties every table-machine register. `preVM_runs`: from a register file with the table machine
empty, if `code` terminates from the loaded state (`preLoadVal`) within `K` atoms emitting `E`,
then `o` gains `E` on top within `preVMCost n W w lens K |E|` steps
(`K · tblC W w + O(n W + Σ lens · W)`), every table-machine register ending empty.

**Stage layouts.** `preLay rg ι` places the table machine `TblR 48` on 63 of the 64 multiplier
registers `ι` (`preIdx`). `pre_rsaRuns`, `pre_rsbRuns`: a `TwRuns` contract on `preLay rg ι`
with the table machine empty before and after is a contract `RsaRuns` (`RsbRuns`) of the stage
layout.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Node

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ### Unary fields -/

section Fields

variable {A : ℕ}

/-- A unary field: `v` ticks and the delimiter `bitSymbol false`. -/
def preFld (v : ℕ) : List (Fin (A + 4)) := List.replicate v tick ++ [bitSymbol false]

/-- A list of unary fields. -/
def preRec (l : List ℕ) : List (Fin (A + 4)) := l.flatMap preFld

@[simp] lemma preRec_nil : (preRec [] : List (Fin (A + 4))) = [] := rfl

@[simp] lemma preRec_cons (v : ℕ) (l : List ℕ) :
    (preRec (v :: l) : List (Fin (A + 4))) = preFld v ++ preRec l := rfl

lemma length_preFld (v : ℕ) : (preFld v : List (Fin (A + 4))).length = v + 1 := by
  simp [preFld]

lemma length_preRec (l : List ℕ) :
    (preRec l : List (Fin (A + 4))).length = l.sum + l.length := by
  induction l with
  | nil => rfl
  | cons v l ih => rw [preRec_cons, List.length_append, length_preFld, ih]; simp; ring

lemma tick_ne_false : (tick : Fin (A + 4)) ≠ bitSymbol false := by
  simp [tick, bitSymbol, Fin.ext_iff]

end Fields

/-! ### The loop on the top symbol -/

section WhileTop

variable {T Q A : ℕ} {U P : Type} {R : Type} [DecidableEq R] {body : P → Pr P T Q A U}
  {tg : R → Fin T}

/-- Peek the top of `g` into `sym`. -/
def prePeek (g : Fin T) : Act T Q A U := .peek (.rt g) (fun v o => { v with sym := o }) .done

lemma prePeek_run (g : Fin T) (v : HS T Q A U) (S : Stacks T A) :
    (prePeek g : Act T Q A U).run (mk v S) = mk { v with sym := (S.R g).head? } S := rfl

/-- Repeat `p` while the top of `g` is a tick. -/
def preWhileTop (g : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (prePeek g)) (.loop (fun v => symBit (v.sym.getD blank)) (.seq p (.act (prePeek g))))

/-- **Loop on the top symbol.** Iteration `j < M` takes `st j` to `st (j + 1)`; the top of `g` is
a tick before every iteration and not a tick after the last. -/
theorem twRuns_preWhileTop (g : R) (p : Pr P T Q A U) (st : ℕ → R → List (Fin (A + 4)))
    (M b : ℕ) (hstep : ∀ j < M, TwRuns body tg p (st j) (st (j + 1)) b)
    (hne : ∀ j < M, (st j g).head? = some tick)
    (hend : symBit ((st M g).head?.getD blank) = false) :
    TwRuns body tg (preWhileTop (tg g) p) (st 0) (st M) (M * (b + 2) + 2) := by
  have key : ∀ n k, k + n = M → ∀ (v : HS T Q A U) (S : Stacks T A), TwHolds tg S (st k) →
      v.sym = (S.R (tg g)).head? →
      ∃ (v' : HS T Q A U) (S' : Stacks T A) (m : ℕ), v'.user = v.user ∧ m ≤ n * (b + 2) + 1 ∧
        Exec body (.loop (fun v => symBit (v.sym.getD blank)) (.seq p (.act (prePeek (tg g)))))
          (mk v S) m (mk v' S') ∧ TwHolds tg S' (st M) ∧ TwFr tg S S' := by
    intro n
    induction n with
    | zero =>
        intro k hk v S hS hf
        refine ⟨v, S, 1, rfl, by simp, .loop_false ?_, by rw [show M = k by omega]; exact hS,
          twFr_refl S⟩
        rw [mk_var, hf, hS g, show k = M by omega]; exact hend
    | succ n ih =>
        intro k hk v S hS hf
        obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hf₁⟩ := hstep k (by omega) v S hS
        have e₂ := prePeek_run (tg g) v₁ S₁ ▸ Exec.act (body := body) (prePeek (tg g)) (mk v₁ S₁)
        obtain ⟨v₃, S₃, n₃, hu₃, hn₃, he₃, hS₃, hf₃⟩ := ih (k + 1) (by omega)
          { v₁ with sym := (S₁.R (tg g)).head? } S₁ hS₁ rfl
        have hft : symBit (v.sym.getD blank) = true := by
          rw [hf, hS g, hne k (by omega)]; simp [symBit, tick]
        refine ⟨v₃, S₃, n₁ + 1 + n₃ + 1, hu₃.trans hu₁, ?_,
          Exec.loop_true (by simpa using hft) (Exec.seq he₁ e₂) he₃, hS₃, twFr_trans hf₁ hf₃⟩
        nlinarith
  intro v S hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ :=
    key M 0 (by omega) { v with sym := (S.R (tg g)).head? } S hS rfl
  exact ⟨v', S', 1 + n, hu, by omega,
    Exec.seq (prePeek_run (tg g) v S ▸ Exec.act (body := body) (prePeek (tg g)) (mk v S)) he, hS',
    hf⟩

/-- Move the ticks of the unary field on top of `src` onto `dst`, then drop the delimiter. -/
def preTake (src dst : Fin T) : Pr P T Q A U :=
  .seq (preWhileTop src (.act (twMvTop src dst .done))) (.act (dropTop src .done))

variable (htg : Function.Injective tg)
include htg

/-- **Taking a field.** With `preFld v` on top of `src`, `dst` gains `v` ticks and `src` loses the
field. -/
theorem preTake_runs {src dst : R} (hsd : src ≠ dst) (ρ : R → List (Fin (A + 4))) {v : ℕ}
    {rest : List (Fin (A + 4))} (hsrc : ρ src = preFld v ++ rest) :
    TwRuns body tg (preTake (tg src) (tg dst)) ρ
      (Function.update (Function.update ρ src rest) dst (List.replicate v tick ++ ρ dst))
      (3 * v + 3) := by
  let st : ℕ → R → List (Fin (A + 4)) := fun j =>
    Function.update (Function.update ρ src (List.replicate (v - j) tick ++ bitSymbol false :: rest))
      dst (List.replicate j tick ++ ρ dst)
  have h0 : st 0 = ρ := by
    funext r
    simp only [st, Function.update_apply]
    split_ifs with h1 h2
    · subst h1; simp
    · subst h2; rw [hsrc]; simp [preFld]
    · rfl
  have hloop := twRuns_preWhileTop (body := body) (tg := tg) src (.act (twMvTop (tg src) (tg dst) .done))
    st v 1 (fun j hj => by
      have hs : st j src = tick :: (List.replicate (v - (j + 1)) tick ++ bitSymbol false :: rest) := by
        simp only [st, Function.update_of_ne hsd, Function.update_self]
        rw [show v - j = (v - (j + 1)) + 1 by omega, List.replicate_succ, List.cons_append]
      refine twRuns_congr (twRuns_mvTop htg hsd hs) ?_
      funext r
      simp only [st, Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all [List.replicate_succ])
    (fun j hj => by
      simp only [st, Function.update_of_ne hsd, Function.update_self]
      rw [show v - j = (v - j - 1) + 1 by omega, List.replicate_succ]; rfl)
    (by
      simp only [st, Function.update_of_ne hsd, Function.update_self, Nat.sub_self,
        List.replicate_zero, List.nil_append, List.head?_cons, Option.getD_some]
      simp [symBit, bitSymbol, Fin.ext_iff])
  rw [h0] at hloop
  have hdrop : TwRuns body tg (.act (dropTop (tg src) .done)) (st v)
      (Function.update (Function.update ρ src rest) dst (List.replicate v tick ++ ρ dst)) 1 := by
    refine twRuns_act htg _ (fun w S hS => ?_)
    refine ⟨w, { S with R := Function.update S.R (tg src) (st v src).tail }, rfl, ?_, ?_,
      twFr_upd S src _⟩
    · simp [dropTop, Action.run, update_rt, hS src]
    · have h := twHolds_upd htg hS src (st v src).tail
      convert h using 1
      funext r
      simp only [st, Function.update_apply]
      split_ifs with h1 h2 <;> subst_vars <;> simp_all
  exact twRuns_mono (twRuns_seq hloop hdrop) (by nlinarith)

/-! ### Unary arithmetic -/

theorem twRuns_umul (c : ℕ) {a b t : R} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) :
    TwRuns body tg (umul c (tg a) (tg b) (tg t)) ρ
      (Function.update ρ b (List.replicate (c * (ρ a).length) tick ++ ρ b))
      (4 * (ρ a).length + 4) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := umul_exec body c (htg.ne hab) (htg.ne hat) (htg.ne hbt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, twFr_upd S b _⟩
  rw [hS a, hS b]
  exact twHolds_upd htg hS b _

theorem twRuns_usub {a b t : R} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (ρ : R → List (Fin (A + 4))) (ht : ρ t = []) :
    TwRuns body tg (usub (tg a) (tg b) (tg t)) ρ
      (Function.update ρ b ((ρ b).drop (ρ a).length)) (4 * (ρ a).length + 4) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := usub_exec body (htg.ne hab) (htg.ne hat) (htg.ne hbt) v S
    (by rw [hS, ht])
  refine ⟨v', _, _, hu, by rw [hS], he, ?_, twFr_upd S b _⟩
  rw [hS a, hS b]
  exact twHolds_upd htg hS b _

theorem twRuns_toBinary {u wR c t tmp : R} (hreg : [u, wR, c, t, tmp].Nodup) (cy : Fin T)
    (ρ : R → List (Fin (A + 4))) (hc : ρ c = []) (ht : ρ t = []) (htmp : ρ tmp = []) :
    TwRuns body tg (toBinary (tg u) (tg wR) (tg c) (tg t) (tg tmp) cy) ρ
      (Function.update ρ c (binSyms (ρ wR).length (ρ u).length))
      ((ρ u).length * (4 * (ρ wR).length + 10) + 4 * (ρ wR).length + 8) := by
  intro v S hS
  obtain ⟨v', m, hu, hm, he⟩ := toBinary_exec body (hreg.map htg) cy v S (by rw [hS, hc])
    (by rw [hS, ht]) (by rw [hS, htmp])
  refine ⟨v', _, _, hu, by rw [hS u, hS wR] at hm; exact hm, he, ?_, twFr_upd S c _⟩
  rw [hS u, hS wR]
  exact twHolds_upd htg hS c _

theorem twRuns_sxBinConv {a d t₁ t₂ : R} (hreg : [a, d, t₁, t₂].Nodup)
    (ρ : R → List (Fin (A + 4))) (hd : ρ d = []) (ht₁ : ρ t₁ = []) (ht₂ : ρ t₂ = []) :
    TwRuns body tg (sxBinConv (tg a) (tg d) (tg t₁) (tg t₂)) ρ
      (Function.update ρ d ((sxBits (ρ a).length).map bitSymbol)) (16 * (ρ a).length + 4) := by
  intro v S hS
  obtain ⟨v', m, hu, hm, he⟩ := sxBinConv_exec body (hreg.map htg) v S (by rw [hS, hd])
    (by rw [hS, ht₁]) (by rw [hS, ht₂])
  refine ⟨v', _, _, hu, by rw [hS a] at hm; exact hm, he, ?_, twFr_upd S d _⟩
  rw [hS a]
  exact twHolds_upd htg hS d _

/-- Unary product: `c` gains `|a| · |b|` ticks, `a` kept through `t₁`, `b` copied through `t₂`. -/
def preUMul (a b c t₁ t₂ : Fin T) : Pr P T Q A U := scanP a t₁ (ucopy b c t₂)

/-- **Unary product.** `c` gains `|a| · |b|` ticks. -/
theorem preUMul_runs {a b c t₁ t₂ : R} (hreg : [a, b, c, t₁, t₂].Nodup)
    (ρ : R → List (Fin (A + 4))) (ht₁ : ρ t₁ = []) (ht₂ : ρ t₂ = []) :
    TwRuns body tg (preUMul (tg a) (tg b) (tg c) (tg t₁) (tg t₂)) ρ
      (Function.update ρ c (List.replicate ((ρ a).length * (ρ b).length) tick ++ ρ c))
      ((ρ a).length * (4 * (ρ b).length + 7) + 2 * (ρ a).length + 4) := by
  have hreg' := hreg
  regs_ne hreg'
  let Ψ : ℕ → R → List (Fin (A + 4)) := fun j =>
    Function.update ρ c (List.replicate (j * (ρ b).length) tick ++ ρ c)
  have h := twRuns_scanP (body := body) htg ‹a ≠ t₁› (p := ucopy (tg b) (tg c) (tg t₂)) (ρ a) Ψ
    (fun _ => 4 * (ρ b).length + 4)
    (fun j hj => by
      refine twRunsS_of ?_
      have hu := twRuns_ucopy (body := body) htg ‹b ≠ c› ‹b ≠ t₂› ‹c ≠ t₂› (twATin a t₁ (ρ a) Ψ j)
        (by simp [twATin, Ψ, Function.update_apply, ‹a ≠ t₂›.symm, ‹t₁ ≠ t₂›.symm, ‹c ≠ t₂›.symm,
          ht₂])
      have hb : twATin a t₁ (ρ a) Ψ j b = ρ b := by
        simp [twATin, Ψ, Function.update_apply, ‹a ≠ b›.symm, ‹b ≠ t₁›, ‹b ≠ c›]
      rw [hb] at hu
      refine twRuns_congr hu ?_
      funext r
      simp only [twAT, twATin, Ψ, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
      all_goals (rw [← List.append_assoc, ← List.replicate_add]; congr 2; ring))
  have e0 : twAT a t₁ (ρ a) Ψ 0 = ρ := by
    funext r
    simp only [twAT, Ψ, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  have e1 : Function.update (Function.update (Ψ (ρ a).length) a (ρ a)) t₁ [] =
      Function.update ρ c (List.replicate ((ρ a).length * (ρ b).length) tick ++ ρ c) := by
    funext r
    simp only [Ψ, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  rw [e0, e1] at h
  refine twRuns_mono h ?_
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  nlinarith

/-- Empty every register of a list. -/
def preClears : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | a :: l => .seq (uclear a) (preClears l)

theorem twRuns_done (ρ : R → List (Fin (A + 4))) :
    TwRuns body tg (.act .done) ρ ρ 1 :=
  twRuns_act htg _ (fun v S hS => ⟨v, S, rfl, rfl, hS, twFr_refl S⟩)

/-- **Clearing a list of registers.** -/
theorem preClears_runs (l : List R) (hl : l.Nodup) (ρ : R → List (Fin (A + 4))) :
    TwRuns body tg (preClears (l.map tg)) ρ (fun r => if r ∈ l then [] else ρ r)
      ((l.map fun r => 2 * (ρ r).length + 2).sum + 1) := by
  induction l generalizing ρ with
  | nil =>
      refine twRuns_congr (twRuns_mono (twRuns_done htg ρ) (by simp)) ?_
      funext r; simp
  | cons a l ih =>
      rw [List.nodup_cons] at hl
      have h1 := twRuns_uclear (body := body) htg a ρ
      have h2 := ih hl.2 (Function.update ρ a [])
      have hm : (l.map fun r => 2 * (Function.update ρ a [] r).length + 2) =
          l.map fun r => 2 * (ρ r).length + 2 :=
        List.map_congr_left fun r hr => by
          rw [Function.update_of_ne (by rintro rfl; exact hl.1 hr)]
      rw [hm] at h2
      refine twRuns_congr (twRuns_mono (twRuns_seq h1 h2) (by simp; omega)) ?_
      funext r
      by_cases hr : r = a
      · subst hr; simp
      · simp [hr, Function.update_of_ne hr]

/-- Take consecutive fields from `src` onto the registers `ds`. -/
def preTakes (src : Fin T) : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | d :: ds => .seq (preTake src d) (preTakes src ds)

/-- The register file after taking the fields `vs` onto `ds`, the rest `rest` left on `src`. -/
def preTV (src : R) (ds : List R) (vs : List ℕ) (rest : List (Fin (A + 4)))
    (ρ : R → List (Fin (A + 4))) : R → List (Fin (A + 4)) :=
  (ds.zip vs).foldl (fun ρ dv => Function.update ρ dv.1 (List.replicate dv.2 tick))
    (Function.update ρ src rest)

/-- **Taking fields.** With the fields `vs` on top of `src`, the empty registers `ds` receive
them. -/
theorem preTakes_runs (src : R) (ds : List R) (vs : List ℕ) (hlen : ds.length = vs.length)
    (hnd : (src :: ds).Nodup) (ρ : R → List (Fin (A + 4))) (rest : List (Fin (A + 4)))
    (hsrc : ρ src = preRec vs ++ rest) (hd : ∀ d ∈ ds, ρ d = []) :
    TwRuns body tg (preTakes (tg src) (ds.map tg)) ρ (preTV src ds vs rest ρ)
      (3 * vs.sum + 3 * vs.length + 1) := by
  induction ds generalizing vs ρ with
  | nil =>
      have hv : vs = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst hv
      refine twRuns_congr (twRuns_mono (twRuns_done htg ρ) (by simp)) ?_
      simp only [preTV, List.zip_nil_left, List.foldl_nil]
      rw [preRec_nil, List.nil_append] at hsrc
      rw [← hsrc, Function.update_eq_self]
  | cons d ds ih =>
      obtain ⟨v, vs, rfl⟩ : ∃ v vs', vs = v :: vs' := by
        cases vs with
        | nil => simp at hlen
        | cons v vs' => exact ⟨v, vs', rfl⟩
      have hnd' := hnd
      rw [List.nodup_cons, List.mem_cons, not_or] at hnd'
      have hsd : src ≠ d := hnd'.1.1
      have h1 := preTake_runs (body := body) htg hsd ρ (v := v) (rest := preRec vs ++ rest)
        (by rw [hsrc, preRec_cons, List.append_assoc])
      rw [hd d (List.mem_cons_self), List.append_nil] at h1
      have hds := (List.nodup_cons.1 hnd'.2)
      have h2 := ih vs (by simpa using hlen) (List.nodup_cons.2 ⟨hnd'.1.2, hds.2⟩)
        (Function.update (Function.update ρ src (preRec vs ++ rest)) d (List.replicate v tick))
        (by rw [Function.update_of_ne hsd, Function.update_self])
        (fun d' hd' => by
          rw [Function.update_of_ne (by rintro rfl; exact hds.1 hd'),
            Function.update_of_ne (by rintro rfl; exact hnd'.1.2 hd')]
          exact hd d' (List.mem_cons_of_mem _ hd'))
      refine twRuns_congr (twRuns_mono (twRuns_seq h1 h2) (by simp; omega)) ?_
      simp only [preTV, List.zip_cons_cons, List.foldl_cons]
      congr 1
      rw [Function.update_comm hsd.symm, Function.update_idem, Function.update_comm hsd]

theorem twRuns_seq_ex {p q : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {X : Type}
    (ρm : X → R → List (Fin (A + 4))) {b₁ b₂ : ℕ}
    (h₁ : ∀ (v : HS T Q A U) (S : Stacks T A), TwHolds tg S ρ →
      ∃ (v' : HS T Q A U) (S' : Stacks T A) (n : ℕ) (x : X), v'.user = v.user ∧ n ≤ b₁ ∧
        Exec body p (mk v S) n (mk v' S') ∧ TwHolds tg S' (ρm x) ∧ TwFr tg S S')
    (h₂ : ∀ x, TwRuns body tg q (ρm x) ρ' b₂) :
    TwRuns body tg (.seq p q) ρ ρ' (b₁ + b₂) := by
  intro v S hS
  obtain ⟨v₁, S₁, n₁, x, hu₁, hn₁, he₁, hS₁, hf₁⟩ := h₁ v S hS
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hS₂, hf₂⟩ := h₂ x v₁ S₁ hS₁
  exact ⟨v₂, S₂, n₁ + n₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, hS₂, twFr_trans hf₁ hf₂⟩

end WhileTop

/-! ### The table machine on the multiplier registers -/

section VM

open IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {U P : Type} {R : Type} [DecidableEq R] {body : P → Pr P T Q A U} {n : ℕ}
  {tg : R ⊕ TblR n → Fin T}

/-- The table-machine part of a layout. -/
def preT (tg : R ⊕ TblR n → Fin T) : TblR n → Fin T := fun x => tg (.inr x)

/-- Every register of a table machine. -/
def preVMRegs (n : ℕ) : List (TblR n) :=
  (List.finRange n).map TblR.v ++ [TblR.wr, TblR.wn, TblR.acc] ++ (List.finRange 12).map TblR.z

lemma mem_preVMRegs (x : TblR n) : x ∈ preVMRegs n := by
  cases x <;> simp [preVMRegs]

lemma nodup_preVMRegs (n : ℕ) : (preVMRegs n).Nodup := by
  unfold preVMRegs
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨List.Nodup.map (fun a b h => TblR.v.inj h) (List.nodup_finRange n), by simp, ?_⟩,
    List.Nodup.map (fun a b h => TblR.z.inj h) (List.nodup_finRange 12), ?_⟩
  all_goals simp
  rintro a (⟨b, rfl⟩ | rfl | rfl | rfl) c h <;> cases h

/-- Set the variables of a list to zero (`W` bits, the width register `wr`). -/
def preZeroVars (tg : R ⊕ TblR n → Fin T) : List (Fin n) → Pr P T Q A U
  | [] => .act .done
  | i :: l => .seq (zeroBits (tg (.inr .wr)) (tg (.inr (.v i))) (tg (.inr (.z 0))))
      (preZeroVars tg l)

/-- Load variables from unary registers, `(u, i)`: variable `i` becomes `|u|`. -/
def preLoads (tg : R ⊕ TblR n → Fin T) : List (R × Fin n) → Pr P T Q A U
  | [] => .act .done
  | ui :: l => .seq (tblLoad1 (preT tg) (tg (.inl ui.1)) ui.2) (preLoads tg l)

/-- The variables after the loads `ls` from the register file `ρ`, starting from `f`. -/
def preLoadVal (ρ : R ⊕ TblR n → List (Fin (A + 4))) (ls : List (R × Fin n)) (f : Fin n → ℕ) :
    Fin n → ℕ :=
  ls.foldl (fun g ui => Function.update g ui.2 (ρ (.inl ui.1)).length) f

/-- A run of the table program `code` on the table-machine registers: the width registers from
`uW` (`W` symbols) and `uw` (`w` symbols), every variable zero, the loads `ls`, the program
(its emitted symbols onto `o`), and every table-machine register emptied. -/
def preVM (tg : R ⊕ TblR n → Fin T) (uW uw : R) (ls : List (R × Fin n)) (code : TblCode n)
    (o : R) : Pr P T Q A U :=
  .seq (ucopy (tg (.inl uW)) (tg (.inr .wr)) (tg (.inr (.z 0))))
  (.seq (ucopy (tg (.inl uw)) (tg (.inr .wn)) (tg (.inr (.z 0))))
  (.seq (preZeroVars tg (List.finRange n))
  (.seq (preLoads tg ls)
  (.seq (tblHost (preT tg) code (tg (.inl o)))
    (preClears (((preVMRegs n).map Sum.inr).map tg))))))

/-- The register file after zeroing the variables of `l` (`W` bits). -/
def preZV (l : List (Fin n)) (W : ℕ) (ρ : R ⊕ TblR n → List (Fin (A + 4))) :
    R ⊕ TblR n → List (Fin (A + 4))
  | .inl r => ρ (.inl r)
  | .inr (.v i) => if i ∈ l then binSyms W 0 ++ ρ (.inr (.v i)) else ρ (.inr (.v i))
  | .inr .wr => ρ (.inr .wr)
  | .inr .wn => ρ (.inr .wn)
  | .inr .acc => ρ (.inr .acc)
  | .inr (.z j) => ρ (.inr (.z j))

/-- The step bound of `preVM`: `K` atoms, `E` emitted symbols. -/
def preVMCost (n W w : ℕ) (lens : List ℕ) (K E : ℕ) : ℕ :=
  (4 * W + 4) + (4 * w + 4) + (n * (4 * W + 4) + 1) +
    ((lens.map fun k => k * (4 * W + 10) + 6 * W + 10).sum + 1) +
    (K * tblC W w + 2 * E + 2) + (n * (2 * W + 2) + 2 * W + 2 * w + 31)

variable (htg : Function.Injective tg)
include htg

lemma preT_inj : Function.Injective (preT tg) := fun _ _ h => Sum.inr_injective (htg h)

lemma preT_ne (r : R) (x : TblR n) : preT tg x ≠ tg (.inl r) := fun h => by
  cases htg h

/-- Lift a contract of the table-machine layout. -/
theorem preTbl_lift {p : Pr P T Q A U} {ρ : R ⊕ TblR n → List (Fin (A + 4))}
    {τ' : TblR n → List (Fin (A + 4))} {b : ℕ}
    (h : ∀ (v : HS T Q A U) (S : Stacks T A), TwHolds tg S ρ →
      ∃ (v' : HS T Q A U) (S' : Stacks T A) (m : ℕ), v'.user = v.user ∧ m ≤ b ∧
        Exec body p (mk v S) m (mk v' S') ∧ tblHolds (preT tg) S' τ' ∧ tblFr (preT tg) S S') :
    TwRuns body tg p ρ (Sum.elim (fun r => ρ (.inl r)) τ') b := by
  intro v S hS
  obtain ⟨v', S', m, hu, hm, he, hS', hf⟩ := h v S hS
  refine ⟨v', S', m, hu, hm, he, ?_, ⟨hf.1, hf.2.1, hf.2.2.1, fun k hk => hf.2.2.2 k
    fun x => hk (.inr x)⟩⟩
  intro r
  cases r with
  | inl r =>
      rw [hf.2.2.2 _ (fun x => preT_ne htg r x)]
      exact hS (.inl r)
  | inr x => exact hS' x

/-- Zero variables. -/
theorem preZeroVars_runs (l : List (Fin n)) (hl : l.Nodup) (ρ : R ⊕ TblR n → List (Fin (A + 4)))
    (hz : ρ (.inr (.z 0)) = []) :
    TwRuns body tg (preZeroVars tg l) ρ (preZV l (ρ (.inr .wr)).length ρ)
      (l.length * (4 * (ρ (.inr .wr)).length + 4) + 1) := by
  induction l generalizing ρ with
  | nil =>
      refine twRuns_congr (twRuns_mono (twRuns_done htg ρ) (by simp)) ?_
      funext r; rcases r with r | (i | _ | _ | _ | j) <;> simp [preZV]
  | cons i l ih =>
      rw [List.nodup_cons] at hl
      have h1 := twRuns_zeroBits (body := body) htg (len := .inr .wr) (z := .inr (.v i))
        (t := .inr (.z 0)) (by simp) (by simp) (by simp) ρ hz
      have h2 := ih hl.2 (Function.update ρ (.inr (.v i)) (binSyms (ρ (.inr .wr)).length 0 ++
        ρ (.inr (.v i)))) (by rw [Function.update_of_ne (by simp)]; exact hz)
      rw [Function.update_of_ne (by simp)] at h2
      refine twRuns_congr (twRuns_mono (twRuns_seq h1 h2) (by simp; nlinarith)) ?_
      funext r
      rcases r with r | (j | _ | _ | _ | j) <;> simp only [preZV, Function.update_apply,
        reduceCtorEq, if_false, Sum.inr.injEq, TblR.v.injEq, List.mem_cons]
      by_cases hj : j = i
      · subst hj; simp [hl.1]
      · simp [hj]

/-- Load one variable. -/
theorem preLoad1_runs (u : R) (i : Fin n) {W : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (st : TblSt n A) (ρ : R ⊕ TblR n → List (Fin (A + 4)))
    (hρ : ∀ x, ρ (.inr x) = tblRho W wl nl st x) :
    TwRuns body tg (tblLoad1 (preT tg) (tg (.inl u)) i) ρ
      (Sum.elim (fun r => ρ (.inl r))
        (tblRho W wl nl ⟨Function.update st.val i (ρ (.inl u)).length, st.acc⟩))
      ((ρ (.inl u)).length * (4 * W + 10) + 6 * W + 10) := by
  refine preTbl_lift htg (fun v S hS => ?_)
  exact tbl_load1_runs (preT_inj htg) wl nl hwl (fun x => preT_ne htg u x) i st _ v S
    (by rw [hS (.inl u)]) (fun x => by rw [← hρ x]; exact hS (.inr x))

/-- Load a list of variables. -/
theorem preLoads_runs (ls : List (R × Fin n)) {W : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (st : TblSt n A) (ρ : R ⊕ TblR n → List (Fin (A + 4)))
    (hρ : ∀ x, ρ (.inr x) = tblRho W wl nl st x) :
    TwRuns body tg (preLoads tg ls) ρ
      (Sum.elim (fun r => ρ (.inl r)) (tblRho W wl nl ⟨preLoadVal ρ ls st.val, st.acc⟩))
      ((ls.map fun ui => (ρ (.inl ui.1)).length * (4 * W + 10) + 6 * W + 10).sum + 1) := by
  induction ls generalizing st ρ with
  | nil =>
      refine twRuns_congr (twRuns_mono (twRuns_done htg ρ) (by simp)) ?_
      funext r
      cases r with
      | inl r => rfl
      | inr x => simp [preLoadVal, hρ x]
  | cons ui ls ih =>
      have h1 := preLoad1_runs (body := body) htg ui.1 ui.2 wl nl hwl st ρ hρ
      have h2 := ih ⟨Function.update st.val ui.2 (ρ (.inl ui.1)).length, st.acc⟩
        (Sum.elim (fun r => ρ (.inl r))
          (tblRho W wl nl ⟨Function.update st.val ui.2 (ρ (.inl ui.1)).length, st.acc⟩))
        (fun x => rfl)
      refine twRuns_mono (twRuns_seq h1 h2) (by simp; omega)

omit htg in
lemma preLoadVal_congr {ρ ρ' : R ⊕ TblR n → List (Fin (A + 4))}
    (h : ∀ r, ρ (.inl r) = ρ' (.inl r)) (ls : List (R × Fin n)) (f : Fin n → ℕ) :
    preLoadVal ρ ls f = preLoadVal ρ' ls f := by
  induction ls generalizing f with
  | nil => rfl
  | cons ui ls ih => simp only [preLoadVal, List.foldl_cons, h] at ih ⊢

/-- **A run of the table machine.** From a register file whose table-machine registers are all
empty, with `W` symbols on `uW` and `w ≤ W` on `uw`: if the table program terminates from the
loaded state within `K` atoms in a state whose emissions are `E`, then `o` gains `E` on top and
every table-machine register ends empty. -/
theorem preVM_runs (uW uw : R) (ls : List (R × Fin n)) (code : TblCode n) (o : R)
    (ρ : R ⊕ TblR n → List (Fin (A + 4))) (hρ : ∀ x, ρ (.inr x) = []) {W w : ℕ}
    (hW : (ρ (.inl uW)).length = W) (hw : (ρ (.inl uw)).length = w) (hwW : w ≤ W)
    (hst : ∀ j, preLoadVal ρ ls (fun _ => 0) j < 2 ^ W) {Post : TblSt n A → Prop} {K : ℕ}
    (hdo : TblDo A W w code ⟨preLoadVal ρ ls (fun _ => 0), []⟩ Post K)
    (E : List (Fin (A + 4))) (hpost : ∀ s, Post s → s.acc.reverse = E) :
    TwRuns body tg (preVM tg uW uw ls code o) ρ (Function.update ρ (.inl o) (E ++ ρ (.inl o)))
      (preVMCost n W w (ls.map fun ui => (ρ (.inl ui.1)).length) K E.length) := by
  set wl : List (Fin (A + 4)) := List.replicate W tick with hwl
  set nl : List (Fin (A + 4)) := List.replicate w tick with hnl
  -- 1. the width registers
  have h1 := twRuns_ucopy (body := body) htg (a := .inl uW) (b := .inr .wr) (t := .inr (.z 0))
    (by simp) (by simp) (by simp) ρ (hρ _)
  set ρ₁ := Function.update ρ (.inr .wr) (List.replicate (ρ (.inl uW)).length tick ++ ρ (.inr .wr))
    with hρ₁
  have h2 := twRuns_ucopy (body := body) htg (a := .inl uw) (b := .inr .wn) (t := .inr (.z 0))
    (by simp) (by simp) (by simp) ρ₁ (by simp [hρ₁, hρ])
  set ρ₂ := Function.update ρ₁ (.inr .wn) (List.replicate (ρ₁ (.inl uw)).length tick ++ ρ₁ (.inr .wn))
    with hρ₂
  -- 2. zero variables
  have h3 := preZeroVars_runs (body := body) htg (List.finRange n) (List.nodup_finRange n) ρ₂
    (by simp [hρ₂, hρ₁, hρ])
  have hwr : (ρ₂ (.inr .wr)).length = W := by simp [hρ₂, hρ₁, hρ, hW]
  rw [hwr] at h3
  set ρ₃ := preZV (List.finRange n) W ρ₂ with hρ₃
  have h3x : ∀ x, ρ₃ (.inr x) = tblRho W wl nl ⟨fun _ => 0, []⟩ x := by
    intro x
    rcases x with i | _ | _ | _ | j <;> simp [hρ₃, preZV, hρ₂, hρ₁, hρ, hwl, hnl, hW, hw, tblRho]
  have h3l : ∀ r, ρ₃ (.inl r) = ρ (.inl r) := by
    intro r; simp [hρ₃, preZV, hρ₂, hρ₁]
  -- 3. loads
  have h4 := preLoads_runs (body := body) htg ls wl nl (by simp [hwl]) ⟨fun _ => 0, []⟩ ρ₃ h3x
  have hlv : preLoadVal ρ₃ ls (fun _ => 0) = preLoadVal ρ ls (fun _ => 0) :=
    preLoadVal_congr h3l ls _
  rw [hlv] at h4
  simp only [h3l] at h4
  set st₀ : TblSt n A := ⟨preLoadVal ρ ls (fun _ => 0), []⟩ with hst₀
  -- 4. the program and the cleanup
  set ρm : (Fin n → ℕ) → R ⊕ TblR n → List (Fin (A + 4)) := fun x =>
    Sum.elim (Function.update (fun r => ρ (.inl r)) o (E ++ ρ (.inl o))) (tblRho W wl nl ⟨x, []⟩)
    with hρm
  have h5 : TwRuns body tg (.seq (tblHost (preT tg) code (tg (.inl o)))
      (preClears (((preVMRegs n).map Sum.inr).map tg)))
      (Sum.elim (fun r => ρ (.inl r)) (tblRho W wl nl st₀))
      (Function.update ρ (.inl o) (E ++ ρ (.inl o)))
      ((K * tblC W w + 2 * E.length + 2) + (n * (2 * W + 2) + 2 * W + 2 * w + 31)) := by
    refine twRuns_seq_ex htg ρm (fun v S hS => ?_) (fun x => ?_)
    · obtain ⟨v', S', m, st', hP, hu, hm, he, hout, hS', hi, ho, hL, hk⟩ :=
        tblHost_runs (body := body) (preT_inj htg) (out := tg (.inl o)) (fun x => preT_ne htg o x)
          wl nl (by simp [hwl]) (by simp [hnl]) hwW hdo hst v S (fun x => hS (.inr x))
      have hE := hpost st' hP
      have hlen : st'.acc.length = E.length := by rw [← hE, List.length_reverse]
      refine ⟨v', S', m, st'.val, hu, by rw [hlen] at hm; exact hm, he, ?_,
        ⟨hi, ho, hL, fun k hk' => hk k (fun h => hk' _ h.symm) (fun x => hk' _)⟩⟩
      intro r
      rcases r with r | x
      · by_cases hr : r = o
        · subst hr
          simp only [hρm, Sum.elim_inl, Function.update_self]
          rw [hout, hE, hS (.inl r)]; rfl
        · simp only [hρm, Sum.elim_inl, Function.update_of_ne hr]
          rw [hk _ (fun h => hr (Sum.inl_injective (htg h))) (fun x => preT_ne htg r x)]
          exact hS (.inl r)
      · exact hS' x
    · have hc := preClears_runs (body := body) htg ((preVMRegs n).map Sum.inr)
        ((nodup_preVMRegs n).map Sum.inr_injective) (ρm x)
      refine twRuns_congr (twRuns_mono hc ?_) ?_
      · simp only [List.map_map, preVMRegs, List.map_append, List.sum_append, Function.comp_def,
          hρm, Sum.elim_inr, tblRho, length_binSyms, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, hwl, hnl, List.length_replicate, List.length_nil]
        simp
        omega
      · funext r
        rcases r with r | x
        · have : Sum.inl r ∉ (preVMRegs n).map (Sum.inr : TblR n → R ⊕ TblR n) := by simp
          simp only [this, if_false, hρm, Sum.elim_inl, Function.update_apply, Sum.inl.injEq]
        · have : Sum.inr x ∈ (preVMRegs n).map (Sum.inr : TblR n → R ⊕ TblR n) :=
            List.mem_map_of_mem (mem_preVMRegs x)
          simp only [this, if_true]
          rw [Function.update_of_ne (by simp), hρ]
  refine twRuns_mono (twRuns_seq h1 (twRuns_seq h2 (twRuns_seq h3 (twRuns_seq h4 h5)))) ?_
  simp only [preVMCost, hW, List.length_finRange, hρ₁, List.map_map, Function.comp_def]
  rw [Function.update_of_ne (by simp), hw]
  omega

end VM

/-! ### The table machine on the multiplier registers of a stage -/

section Lay

open IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- The table-machine registers among the 64 multiplier registers. -/
def preIdx : TblR 48 → Fin 64
  | .v i => ⟨i, by omega⟩
  | .wr => 48
  | .wn => 49
  | .acc => 50
  | .z j => ⟨51 + j, by omega⟩

lemma preIdx_inj : Function.Injective preIdx := by
  intro a b h
  cases a <;> cases b <;> simp_all [preIdx, Fin.ext_iff] <;> omega

variable {T Q A : ℕ} {U P : Type} {R : Type} [DecidableEq R] {body : P → Pr P T Q A U}

/-- A stage layout `rg` extended by the table machine on the multiplier registers `ι`. -/
def preLay (rg : R → Fin T) (ι : Fin 64 → Fin T) : R ⊕ TblR 48 → Fin T :=
  Sum.elim rg fun x => ι (preIdx x)

lemma preLay_inj {rg : R → Fin T} {ι : Fin 64 → Fin T} (hrg : Function.Injective rg)
    (hι : Function.Injective ι) (hdisj : ∀ r j, rg r ≠ ι j) : Function.Injective (preLay rg ι) := by
  rintro (a | a) (b | b) h <;> simp only [preLay, Sum.elim_inl, Sum.elim_inr] at h
  · rw [hrg h]
  · exact absurd h (hdisj _ _)
  · exact absurd h.symm (hdisj _ _)
  · rw [preIdx_inj (hι h)]

/-- A contract on the extended layout, with every table-machine register empty before and after,
is a contract of the stage layout (the multiplier registers start and end empty). -/
theorem pre_toRuns {rg : R → Fin T} {ι : Fin 64 → Fin T} {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : TwRuns body (preLay rg ι) p (Sum.elim ρ fun _ => []) (Sum.elim ρ' fun _ => []) b)
    (v : HS T Q A U) (S : Stacks T A) (hι0 : ∀ j, S.R (ι j) = []) (hS : ∀ r, S.R (rg r) = ρ r) :
    ∃ v' S' n, v'.user = v.user ∧ n ≤ b ∧ Exec body p (mk v S) n (mk v' S') ∧
      (∀ r, S'.R (rg r) = ρ' r) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := h v S (fun r => by
    rcases r with r | x
    · exact hS r
    · exact hι0 _)
  refine ⟨v', S', n, hu, hn, he, fun r => hS' (.inl r), hf.1, hf.2.1, hf.2.2.1, fun k hk => ?_⟩
  by_cases hx : ∃ x, ι (preIdx x) = k
  · obtain ⟨x, rfl⟩ := hx
    rw [hι0]
    exact hS' (.inr x)
  · simp only [not_exists] at hx
    exact hf.2.2.2 k (fun r => by rcases r with r | x; exacts [hk r, hx x])

theorem pre_rsaRuns {rg : R → Fin T} {ι : Fin 64 → Fin T} {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : TwRuns body (preLay rg ι) p (Sum.elim ρ fun _ => []) (Sum.elim ρ' fun _ => []) b) :
    ResampA.RsaRuns body rg ι p ρ ρ' b := by
  intro v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := pre_toRuns h v S hc.2 hS
  exact ⟨v', S', n, hu, hn, he, hS', hf⟩

theorem pre_rsbRuns {rg : R → Fin T} {ι : Fin 64 → Fin T} {p : Pr P T Q A U} {ρ ρ' : R → List (Fin (A + 4))} {b : ℕ}
    (h : TwRuns body (preLay rg ι) p (Sum.elim ρ fun _ => []) (Sum.elim ρ' fun _ => []) b) :
    RsbRuns body rg ι p ρ ρ' b := by
  intro v S hc hS
  obtain ⟨v', S', n, hu, hn, he, hS', hf⟩ := pre_toRuns h v S hc.2 hS
  exact ⟨v', S', n, hu, hn, he, hS', hf⟩

end Lay

/-! ### Interchange headers -/

section Hdr

variable {T Q A : ℕ} {U P : Type} {R : Type} [DecidableEq R] {body : P → Pr P T Q A U}
  {tg : R → Fin T}

/-- A canonical interchange header from the unary value on `src`: its binary digits under a
separator, on the empty `h`. -/
def preHdr (src h t₁ t₂ : Fin T) : Pr P T Q A U :=
  .seq (sxBinConv src h t₁ t₂) (.act (.push (.rt h) (fun _ => separator) .done))

variable (htg : Function.Injective tg)
include htg

theorem preHdr_runs {src h t₁ t₂ : R} (hreg : [src, h, t₁, t₂].Nodup)
    (ρ : R → List (Fin (A + 4))) (hh : ρ h = []) (ht₁ : ρ t₁ = []) (ht₂ : ρ t₂ = []) :
    TwRuns body tg (preHdr (tg src) (tg h) (tg t₁) (tg t₂)) ρ
      (Function.update ρ h (separator :: (sxBits (ρ src).length).map bitSymbol))
      (16 * (ρ src).length + 5) := by
  have h1 := twRuns_sxBinConv (body := body) htg hreg ρ hh ht₁ ht₂
  have h2 := twRuns_push (body := body) htg h separator
    (Function.update ρ h ((sxBits (ρ src).length).map bitSymbol))
  rw [Function.update_self, Function.update_idem] at h2
  exact twRuns_mono (twRuns_seq h1 h2) (by omega)

end Hdr

end IntegerMultBounds.MathlibTM2.Fast
