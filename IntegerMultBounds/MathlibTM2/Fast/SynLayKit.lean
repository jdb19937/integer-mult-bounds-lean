module

public import IntegerMultBounds.MathlibTM2.Fast.SynLayRegs

/-!
# Tools of the layout programs of the synthetic transforms

Paper §6, proof of `lem:synthetic-transform-cost`. Generic programs and lemmas used by the
layout programs `slyFwd`, `slyOpp` (`Fast/SynLayFwd.lean`, `Fast/SynLayOpp.lean`):

* `slyBlk cn sp src dst f`: move `|cn|` symbols of `src` onto `dst` through the symbol map `f`
  (`lr_slyBlk`); `slyRev`: per record (counter `cnt`, records of `|cn|` symbols) two block moves
  through a spare, which reverses the order of the records and keeps each intact
  (`lr_slyRev`); `slyRevStream`: the same, the result back on the source register
  (`lr_slyRevStream`).
* `slyPairSw`: the symbol map exchanging the real and imaginary bits of a pair symbol;
  `slyBitStream_rev`, `slyXcStream_rev`: the description streams of the inverse layout
  (`((layBits).map Prod.swap).reverse`, `(layXcs).reverse`) from the forward streams.
* `slyRecs`, `sly_moveRecs_fwd`, `sly_moveRecs_opp`: the record stream of a grid array as a
  list of records, and the streams after `moveRecs (layRec L)` and its inverse.
* `sly_ldlWM_full`, `sly_ldlWX_full`: the loader files after the last move as updates of the
  base file; `sly_ldlW_sw_congr`, `sly_layXcLoopCost_congr`: the exchange cost depends on the
  bank only; `LdlBase.slySet`: a base file with other description streams.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-! ### Block moves -/

section Block

variable {T Q A : ℕ} {U F : Type} {body : F → Pr F T Q A U}

/-- Pop a symbol of `src` and push its image under `f` onto `dst`. -/
def slyMvF (src dst : Fin T) (f : Fin (A + 4) → Fin (A + 4)) : Act T Q A U :=
  .pop (.rt src) (fun v o => { v with sym := o })
    (.push (.rt dst) (fun v => f (v.sym.getD blank)) .done)

theorem slyMvF_run {src dst : Fin T} (hsd : src ≠ dst) (f : Fin (A + 4) → Fin (A + 4))
    (x : Fin (A + 4)) (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hS : S.R src = x :: rest) :
    (slyMvF src dst f : Act T Q A U).run (mk v S) = mk { v with sym := some x }
      { S with R := Function.update (Function.update S.R src rest) dst (f x :: S.R dst) } := by
  simp [slyMvF, Action.run, hS, update_rt, Function.update_of_ne hsd.symm]

/-- Move `|cn|` symbols of `src` onto `dst` through `f`, the last on top. -/
def slyBlk (cn sp src dst : Fin T) (f : Fin (A + 4) → Fin (A + 4)) : Pr F T Q A U :=
  scanP cn sp (.act (slyMvF src dst f))

/-- The register file after moving the first `i` symbols of `ws`. -/
def slyBlkFile (src dst : Fin T) (R : Fin T → List (Fin (A + 4))) (f : Fin (A + 4) → Fin (A + 4))
    (ws rest : List (Fin (A + 4))) (i : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update R src (ws.drop i ++ rest)) dst
    (((ws.take i).map f).reverse ++ R dst)

/-- **A block move.** With `cn` holding `|ws|` symbols, `sp` empty and `src` holding `ws` on top
of `rest`, `slyBlk` leaves `rest` on `src` and pushes the images of `ws` onto `dst`, the last
on top; `cn` is restored; `6 |ws| + 4` steps. -/
theorem lr_slyBlk {cn sp src dst : Fin T} (hreg : [src, cn, sp, dst].Nodup)
    (f : Fin (A + 4) → Fin (A + 4)) (R : Fin T → List (Fin (A + 4)))
    (ws rest : List (Fin (A + 4))) (hsrc : R src = ws ++ rest) (hcn : (R cn).length = ws.length)
    (hsp : R sp = []) :
    LayRuns body (slyBlk cn sp src dst f) R
      (Function.update (Function.update R src rest) dst ((ws.map f).reverse ++ R dst))
      (6 * ws.length + 4) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hreg
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩ := hreg
  have hit : IterSpec body (.act (slyMvF src dst f)) cn sp (slyBlkFile src dst R f ws rest)
      (fun _ => 1) ws.length := by
    intro i hi v S hS
    have hsrcS : S.R src = ws[i] :: (ws.drop (i + 1) ++ rest) := by
      rw [hS src h1 h2]
      simp only [slyBlkFile, Function.update_of_ne h3, Function.update_self]
      rw [List.drop_eq_getElem_cons hi]
      rfl
    refine ⟨{ v with sym := some ws[i] }, Function.update (Function.update S.R src
      (ws.drop (i + 1) ++ rest)) dst (f ws[i] :: S.R dst), 1, rfl, le_rfl, ?_, ?_, ?_, ?_⟩
    · have h := Exec.act (body := body) (slyMvF src dst f) (mk v S)
      rw [slyMvF_run h3 f _ _ v S hsrcS] at h
      exact h
    · simp [Function.update_of_ne (Ne.symm h1), Function.update_of_ne h5]
    · simp [Function.update_of_ne (Ne.symm h2), Function.update_of_ne h6]
    · intro k hk1 hk2
      have htake : ws.take (i + 1) = ws.take i ++ [ws[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
      by_cases hkd : k = dst
      · rw [hkd, Function.update_self, hS dst (Ne.symm h5) (Ne.symm h6)]
        simp only [slyBlkFile, Function.update_self, htake, List.map_append,
          List.map_singleton, List.reverse_append, List.reverse_singleton, List.singleton_append,
          List.cons_append, List.nil_append, List.append_assoc]
      · by_cases hks : k = src
        · rw [hks, Function.update_of_ne h3, Function.update_self]
          simp only [slyBlkFile, Function.update_of_ne h3, Function.update_self]
        · rw [Function.update_of_ne hkd, Function.update_of_ne hks, hS k hk1 hk2]
          simp only [slyBlkFile, Function.update_of_ne hkd, Function.update_of_ne hks]
  intro v S hL hS
  have hΨ0 : ∀ k, k ≠ cn → k ≠ sp → S.R k = slyBlkFile src dst R f ws rest 0 k := by
    intro k _ _
    rw [hS]
    simp only [slyBlkFile, List.drop_zero, List.take_zero, List.map_nil, List.reverse_nil,
      List.nil_append]
    by_cases hkd : k = dst
    · subst hkd; simp
    · by_cases hks : k = src
      · subst hks; simp [Function.update_of_ne hkd, hsrc]
      · simp [Function.update_of_ne hkd, Function.update_of_ne hks]
  obtain ⟨v', R', m, hu, hm, he, ha, ht, hk⟩ :=
    scanP_exec body h4 hit 0 v S (by rw [hS, hcn]; omega) hΨ0
  refine ⟨v', m, hu, ?_, ?_⟩
  · rw [hS, hcn, hsp] at hm
    refine hm.trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_nil]
    ring
  · have hR' : R' = Function.update (Function.update R src rest) dst
        ((ws.map f).reverse ++ R dst) := by
      funext k
      by_cases hkc : k = cn
      · subst hkc
        rw [ha, hS, hsp]
        simp [Function.update_of_ne (Ne.symm h1), Function.update_of_ne h5]
      · by_cases hks : k = sp
        · subst hks
          rw [ht]
          simp [Function.update_of_ne (Ne.symm h2), Function.update_of_ne h6, hsp]
        · rw [hk k hkc hks, hS, hcn]
          simp [slyBlkFile]
    rw [← hR']
    exact he

end Block

/-! ### Reversing the order of the records of a stream -/

section Rev

variable {T Q A : ℕ} {U F : Type} {body : F → Pr F T Q A U}

/-- Per symbol of `cnt`: move `|cn|` symbols of `src` onto `tmp` through `f`, then back onto
`dst`. The records of `src` end on `dst` in reverse order, each intact. -/
def slyRev (cnt sp1 cn sp2 src tmp dst : Fin T) (f : Fin (A + 4) → Fin (A + 4)) :
    Pr F T Q A U :=
  scanP cnt sp1 (.seq (slyBlk cn sp2 src tmp f) (slyBlk cn sp2 tmp dst id))

/-- The register file after the first `j` records. -/
def slyRevFile (src dst : Fin T) (R : Fin T → List (Fin (A + 4))) (f : Fin (A + 4) → Fin (A + 4))
    (rs : List (List (Fin (A + 4)))) (j : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (Function.update R src (rs.drop j).flatten) dst
    (((rs.take j).map (List.map f)).reverse.flatten ++ R dst)

theorem sly_take_succ_rev {α : Type*} (rs : List (List α)) (g : List α → List α) {j : ℕ}
    (hj : j < rs.length) :
    ((rs.take (j + 1)).map g).reverse.flatten = g rs[j] ++ ((rs.take j).map g).reverse.flatten := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append,
    List.map_singleton, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.flatten_cons]

theorem sly_length_rev_flatten {α β : Type*} (f : α → β) (n : ℕ) :
    ∀ rs : List (List α), (∀ r ∈ rs, r.length = n) →
      ((rs.map (List.map f)).reverse.flatten).length = n * rs.length
  | [], _ => by simp
  | r :: rs, h => by
      have ih := sly_length_rev_flatten f n rs fun x hx => h x (by simp [hx])
      simp only [List.map_cons, List.reverse_cons, List.flatten_append, List.length_append, ih,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.length_map, h r (by simp),
        List.length_cons]
      ring

/-- **Reversing the records.** `src` holds the records `rs` of `n` symbols each, `cnt` one symbol
per record, `cn` `n` symbols, the spares and `tmp` are empty. Afterwards `src` is empty and
`dst` holds the images of the records in reverse order on top of its contents; `cnt` and `cn`
are restored. -/
theorem lr_slyRev {cnt sp1 cn sp2 src tmp dst : Fin T}
    (hreg : [cnt, sp1, cn, sp2, src, tmp, dst].Nodup) (f : Fin (A + 4) → Fin (A + 4))
    (R : Fin T → List (Fin (A + 4))) (rs : List (List (Fin (A + 4)))) (n : ℕ)
    (hrs : ∀ r ∈ rs, r.length = n) (hsrc : R src = rs.flatten) (hcnt : (R cnt).length = rs.length)
    (hcn : (R cn).length = n) (hsp1 : R sp1 = []) (hsp2 : R sp2 = []) (htmp : R tmp = []) :
    LayRuns body (slyRev cnt sp1 cn sp2 src tmp dst f) R
      (Function.update (Function.update R src []) dst
        ((rs.map (List.map f)).reverse.flatten ++ R dst))
      (rs.length * (12 * n + 11) + 2 * rs.length + 4) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hreg
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5⟩, ⟨c1, c2, c3, c4⟩, ⟨d1, d2, d3⟩,
    ⟨e1, e2⟩, g1⟩ := hreg
  have hstep : ∀ j < (R cnt).length, LayRuns body (.seq (slyBlk cn sp2 src tmp f)
      (slyBlk cn sp2 tmp dst id))
      (Function.update (Function.update (slyRevFile src dst R f rs j) cnt ((R cnt).drop (j + 1)))
        sp1 ((R cnt).take (j + 1)).reverse)
      (Function.update (Function.update (slyRevFile src dst R f rs (j + 1)) cnt
        ((R cnt).drop (j + 1))) sp1 ((R cnt).take (j + 1)).reverse)
      ((6 * n + 4) + (6 * n + 4)) := by
    intro j hj
    have hjr : j < rs.length := by rw [← hcnt]; exact hj
    have hlen : rs[j].length = n := hrs _ (List.getElem_mem hjr)
    obtain ⟨Rj, hRj⟩ : ∃ Rj, Rj = Function.update (Function.update (slyRevFile src dst R f rs j)
      cnt ((R cnt).drop (j + 1))) sp1 ((R cnt).take (j + 1)).reverse := ⟨_, rfl⟩
    rw [← hRj]
    have hRj_src : Rj src = rs[j] ++ (rs.drop (j + 1)).flatten := by
      rw [hRj, Function.update_of_ne (Ne.symm b3), Function.update_of_ne (Ne.symm a4)]
      simp only [slyRevFile, Function.update_of_ne e2, Function.update_self]
      rw [List.drop_eq_getElem_cons hjr, List.flatten_cons]
    have hRj_cn : Rj cn = R cn := by
      rw [hRj, Function.update_of_ne (Ne.symm b1), Function.update_of_ne (Ne.symm a2)]
      simp only [slyRevFile, Function.update_of_ne c4, Function.update_of_ne c2]
    have hRj_sp2 : Rj sp2 = [] := by
      rw [hRj, Function.update_of_ne (Ne.symm b2), Function.update_of_ne (Ne.symm a3)]
      simp only [slyRevFile, Function.update_of_ne d3, Function.update_of_ne d1, hsp2]
    have hRj_tmp : Rj tmp = [] := by
      rw [hRj, Function.update_of_ne (Ne.symm b4), Function.update_of_ne (Ne.symm a5)]
      simp only [slyRevFile, Function.update_of_ne g1, Function.update_of_ne (Ne.symm e1), htmp]
    have hRj_dst : Rj dst = ((rs.take j).map (List.map f)).reverse.flatten ++ R dst := by
      rw [hRj, Function.update_of_ne (Ne.symm b5), Function.update_of_ne (Ne.symm a6)]
      simp only [slyRevFile, Function.update_self]
    have h1 := lr_slyBlk (body := body) (cn := cn) (sp := sp2) (src := src) (dst := tmp)
      (by simp [Ne.symm c2, Ne.symm d1, e1, c1, c3, d2]) f Rj rs[j]
      (rs.drop (j + 1)).flatten hRj_src (by rw [hRj_cn, hcn, hlen]) hRj_sp2
    rw [hRj_tmp, List.append_nil] at h1
    obtain ⟨R1, hR1⟩ : ∃ R1, R1 = Function.update (Function.update Rj src (rs.drop (j + 1)).flatten)
      tmp (rs[j].map f).reverse := ⟨_, rfl⟩
    rw [← hR1] at h1
    have h2 := lr_slyBlk (body := body) (cn := cn) (sp := sp2) (src := tmp) (dst := dst)
      (by simp [Ne.symm c3, Ne.symm d2, g1, c1, c4, d3]) id R1 (rs[j].map f).reverse []
      (by rw [hR1, Function.update_self, List.append_nil])
      (by rw [hR1, Function.update_of_ne c3, Function.update_of_ne c2, hRj_cn, hcn]; simp [hlen])
      (by rw [hR1, Function.update_of_ne d2, Function.update_of_ne d1, hRj_sp2])
    have e5 : R1 dst = ((rs.take j).map (List.map f)).reverse.flatten ++ R dst := by
      rw [hR1, Function.update_of_ne (Ne.symm g1), Function.update_of_ne (Ne.symm e2), hRj_dst]
    rw [e5, List.map_id, List.reverse_reverse] at h2
    refine lr_weaken body (h1.seq h2) ?_ (by simp [hlen])
    funext k
    by_cases hk1 : k = sp1
    · subst hk1
      rw [Function.update_of_ne b5, Function.update_of_ne b4, hR1, Function.update_of_ne b4,
        Function.update_of_ne b3, hRj, Function.update_self, Function.update_self]
    by_cases hk2 : k = cnt
    · subst hk2
      rw [Function.update_of_ne a6, Function.update_of_ne a5, hR1, Function.update_of_ne a5,
        Function.update_of_ne a4, hRj, Function.update_of_ne a1, Function.update_self,
        Function.update_of_ne a1, Function.update_self]
    rw [Function.update_of_ne hk1, Function.update_of_ne hk2]
    by_cases hk3 : k = dst
    · subst hk3
      rw [Function.update_self]
      simp only [slyRevFile, Function.update_self, sly_take_succ_rev rs (List.map f) hjr,
        List.append_assoc]
    rw [Function.update_of_ne hk3]
    by_cases hk4 : k = tmp
    · subst hk4
      rw [Function.update_self]
      simp only [slyRevFile, Function.update_of_ne g1, Function.update_of_ne (Ne.symm e1), htmp]
    rw [Function.update_of_ne hk4, hR1, Function.update_of_ne hk4]
    by_cases hk5 : k = src
    · subst hk5
      rw [Function.update_self]
      simp only [slyRevFile, Function.update_of_ne e2, Function.update_self]
    rw [Function.update_of_ne hk5, hRj, Function.update_of_ne hk1, Function.update_of_ne hk2]
    simp only [slyRevFile, Function.update_of_ne hk3, Function.update_of_ne hk5]
  have hscan := layScan_exec (body := body) a1 (slyRevFile src dst R f rs) (R cnt)
    (fun _ => (6 * n + 4) + (6 * n + 4)) hstep
  rw [hcnt] at hscan
  have h0 : Function.update (Function.update (slyRevFile src dst R f rs 0) cnt (R cnt)) sp1 [] =
      R := by
    have e : slyRevFile src dst R f rs 0 = R := by
      simp only [slyRevFile, List.drop_zero, List.take_zero, List.map_nil, List.reverse_nil,
        List.flatten_nil, List.nil_append, ← hsrc, Function.update_eq_self]
    rw [e, Function.update_eq_self, ← hsp1, Function.update_eq_self]
  have hend : Function.update (Function.update (slyRevFile src dst R f rs rs.length) cnt (R cnt))
      sp1 [] = Function.update (Function.update R src []) dst
        ((rs.map (List.map f)).reverse.flatten ++ R dst) := by
    have e1 : slyRevFile src dst R f rs rs.length cnt = R cnt := by
      simp only [slyRevFile, Function.update_of_ne a6, Function.update_of_ne a4]
    have e2 : slyRevFile src dst R f rs rs.length sp1 = [] := by
      simp only [slyRevFile, Function.update_of_ne b5, Function.update_of_ne b3, hsp1]
    conv_lhs => rw [← e1, Function.update_eq_self, ← e2, Function.update_eq_self]
    simp [slyRevFile]
  rw [h0, hend] at hscan
  refine hscan.mono (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  ring

/-- Reverse the order of the records of `src` (through `f`), the result back on `src`. -/
def slyRevStream (cnt sp1 cn sp2 src tmp dst : Fin T) (f : Fin (A + 4) → Fin (A + 4)) :
    Pr F T Q A U :=
  .seq (slyRev cnt sp1 cn sp2 src tmp dst f) (.seq (moveR dst tmp id) (moveR tmp src id))

/-- The step bound of `slyRevStream` on `m` records of `n` symbols. -/
def slyRevStreamCost (m n : ℕ) : ℕ := m * (12 * n + 11) + 2 * m + 4 + 2 * (2 * (n * m) + 2)

/-- **Reversing the records in place.** As `lr_slyRev`, with `dst` empty: `src` ends holding
the images of its records in reverse order, every other register as before. -/
theorem lr_slyRevStream {cnt sp1 cn sp2 src tmp dst : Fin T}
    (hreg : [cnt, sp1, cn, sp2, src, tmp, dst].Nodup) (f : Fin (A + 4) → Fin (A + 4))
    (R : Fin T → List (Fin (A + 4))) (rs : List (List (Fin (A + 4)))) (n : ℕ)
    (hrs : ∀ r ∈ rs, r.length = n) (hsrc : R src = rs.flatten) (hcnt : (R cnt).length = rs.length)
    (hcn : (R cn).length = n) (hsp1 : R sp1 = []) (hsp2 : R sp2 = []) (htmp : R tmp = [])
    (hdst : R dst = []) :
    LayRuns body (slyRevStream cnt sp1 cn sp2 src tmp dst f) R
      (Function.update R src (rs.map (List.map f)).reverse.flatten)
      (slyRevStreamCost rs.length n) := by
  have hr := lr_slyRev (body := body) hreg f R rs n hrs hsrc hcnt hcn hsp1 hsp2 htmp
  have hn := hreg
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hn
  obtain ⟨-, -, -, -, ⟨e1, e2⟩, g1⟩ := hn
  rw [hdst, List.append_nil] at hr
  set X := (rs.map (List.map f)).reverse.flatten with hX
  have hXl : X.length = n * rs.length := sly_length_rev_flatten f n rs hrs
  set R1 := Function.update (Function.update R src []) dst X with hR1
  have m1 := lr_moveR_id (body := body) (R := R1) (Ne.symm g1)
  have e1' : R1 dst = X := by rw [hR1, Function.update_self]
  have e2' : R1 tmp = [] := by
    rw [hR1, Function.update_of_ne g1, Function.update_of_ne (Ne.symm e1), htmp]
  rw [e1', e2', List.append_nil] at m1
  set R2 := Function.update (Function.update R1 dst []) tmp X.reverse with hR2
  have m2 := lr_moveR_id (body := body) (R := R2) (Ne.symm e1)
  have e3 : R2 tmp = X.reverse := by rw [hR2, Function.update_self]
  have e4 : R2 src = [] := by
    rw [hR2, Function.update_of_ne e1, Function.update_of_ne e2, hR1,
      Function.update_of_ne e2, Function.update_self]
  rw [e3, e4, List.append_nil, List.reverse_reverse, List.length_reverse] at m2
  refine lr_weaken body (hr.seq (m1.seq m2)) ?_ ?_
  · rw [hR2, hR1]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  · simp only [slyRevStreamCost, hXl]
    omega

end Rev

/-! ### The description streams of the inverse layout -/

section Streams

variable {A : ℕ}

/-- Exchange the real and imaginary bits of a pair symbol. -/
def slyPairSw (A : ℕ) (x : Fin (A + 4)) : Fin (A + 4) := pairSym A (pairIm x) (pairRe x)

theorem slyPairSw_tblPairs (hA : 4 ≤ A) (w x y : ℕ) :
    (tblPairs A w x y).map (slyPairSw A) = tblPairs A w y x := by
  simp only [tblPairs, coeffSyms, List.map_ofFn]
  congr 1
  funext t
  simp [slyPairSw, pairRe_pairSym hA, pairIm_pairSym hA]

/-- The single-bit move stream of the inverse layout, from the records of the forward stream. -/
theorem slyBitStream_rev (hA : 4 ≤ A) (n : ℕ) (bs : List (ℕ × ℕ)) :
    ((bs.map (ldlBitRec A n)).map (List.map (slyPairSw A))).reverse.flatten =
      ldlBitStream A n ((bs.map Prod.swap).reverse) := by
  rw [ldlBitStream, List.flatMap_def, List.map_reverse, List.map_map, List.map_map]
  congr 3
  funext e
  simp [ldlBitRec, slyPairSw_tblPairs hA]

/-- The exchange stream of the inverse layout, from the records of the forward stream. -/
theorem slyXcStream_rev (w : ℕ) (xs : List LayXcD) :
    ((xs.map fun d => ldlXcRec A w d.hs).map (List.map id)).reverse.flatten =
      ldlXcStream A w xs.reverse := by
  rw [ldlXcStream, List.flatMap_def, List.map_reverse, List.map_map]
  congr 2
  refine List.map_congr_left fun d _ => ?_
  simp

theorem slyBitStream_eq_flatten (n : ℕ) (bs : List (ℕ × ℕ)) :
    ldlBitStream A n bs = (bs.map (ldlBitRec A n)).flatten := by
  rw [ldlBitStream, List.flatMap_def]

theorem slyXcStream_eq_flatten (w : ℕ) (xs : List LayXcD) :
    ldlXcStream A w xs = (xs.map fun d => ldlXcRec A w d.hs).flatten := by
  rw [ldlXcStream, List.flatMap_def]

theorem sly_mem_bitRec_length (n : ℕ) (bs : List (ℕ × ℕ)) :
    ∀ r ∈ bs.map (ldlBitRec A n), r.length = n := by
  intro r hr
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hr
  simp [ldlBitRec]

theorem sly_mem_xcRec_length (w : ℕ) (xs : List LayXcD) :
    ∀ r ∈ xs.map fun d => ldlXcRec A w d.hs, r.length = 5 * w := by
  intro r hr
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 hr
  simp [ldlXcRec]
  ring

end Streams

/-! ### Record streams of grid arrays -/

section Records

variable {A w r : ℕ}

theorem sly_cstream_flatMap (l : List ℕ) (g : ℕ → List GaussianInt) :
    cstream A w (l.flatMap g) = (l.map fun n => cstream A w (g n)).flatten := by
  induction l with
  | nil => simp
  | cons n l ih => rw [List.flatMap_cons, cstream_append, ih, List.map_cons, List.flatten_cons]

/-- The records of the grid array `Z`: record `n` is the coefficients of `Z n`. -/
def slyRecs (A w M : ℕ) (Z : ℕ → Fin r → GaussianInt) : List (List (Fin (A + 4))) :=
  (List.range M).map fun n => cstream A w (List.ofFn (Z n))

theorem sly_cstream_rpStream (M : ℕ) (Z : ℕ → Fin r → GaussianInt) :
    cstream A w (rpStream M Z) = (slyRecs A w M Z).flatten :=
  sly_cstream_flatMap _ _

@[simp] theorem slyRecs_length (M : ℕ) (Z : ℕ → Fin r → GaussianInt) :
    (slyRecs A w M Z).length = M := by
  simp [slyRecs]

theorem slyRecs_mem_length (M : ℕ) (Z : ℕ → Fin r → GaussianInt) :
    ∀ x ∈ slyRecs A w M Z, x.length = r * w := by
  intro x hx
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 hx
  simp

/-- The symbols of a coefficient stream are pair symbols, below `8`. -/
theorem sly_csyms_lt (hA : 4 ≤ A) (z : GaussianInt) : ∀ c ∈ csyms A w z, c.val < 8 := by
  intro c hc
  simp only [csyms, coeffSyms, List.mem_ofFn] at hc
  obtain ⟨j, rfl⟩ := hc
  rw [pairSym_val hA]
  cases (red w z).1.val.testBit j <;> cases (red w z).2.val.testBit j <;> simp

theorem slyRecs_lt8 (hA : 4 ≤ A) (M : ℕ) (Z : ℕ → Fin r → GaussianInt) :
    ∀ x ∈ slyRecs A w M Z, ∀ s ∈ x, s.val < 8 := by
  intro x hx s hs
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 hx
  simp only [cstream, List.mem_flatMap] at hs
  obtain ⟨z, -, hz⟩ := hs
  exact sly_csyms_lt hA z s hz

theorem slyRecs_getD {M : ℕ} (Z : ℕ → Fin r → GaussianInt) {i : ℕ} (hi : i < M) :
    (slyRecs A w M Z).getD i [] = cstream A w (List.ofFn (Z i)) := by
  simp [slyRecs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

theorem slyRecs_getElem {M : ℕ} (Z : ℕ → Fin r → GaussianInt) {i : ℕ}
    (hi : i < (slyRecs A w M Z).length) : (slyRecs A w M Z)[i] = cstream A w (List.ofFn (Z i)) := by
  simp [slyRecs]

/-- The records moved by the layout `L`: the stream of the array in the physical order. -/
theorem sly_moveRecs_fwd {N : ℕ} (L : Equiv.Perm (Fin N)) (Z : ℕ → Fin r → GaussianInt) :
    (moveRecs (layRec L) (slyRecs A w (2 ^ N) Z)).flatten =
      cstream A w (rpStream (2 ^ N) fun m => Z (synPi L m)) := by
  rw [sly_cstream_rpStream]
  congr 1
  apply List.ext_getElem (by simp [moveRecs])
  intro i h1 _
  have hi : i < 2 ^ N := by simpa [moveRecs] using h1
  simp only [moveRecs, List.getElem_ofFn]
  rw [slyRecs_getD _ (Fin.isLt _), slyRecs_getElem]
  have e := synPi_layRec L ⟨i, hi⟩
  simp only [Fin.val_mk] at e
  rw [e]

/-- The records moved back by the inverse layout. -/
theorem sly_moveRecs_opp {N : ℕ} (L : Equiv.Perm (Fin N)) (Y : ℕ → Fin r → GaussianInt) :
    (moveRecs (layRec L).symm (slyRecs A w (2 ^ N) Y)).flatten =
      cstream A w (rpStream (2 ^ N) fun x =>
        Y ((layRec L) ⟨x % 2 ^ N, Nat.mod_lt _ (by positivity)⟩)) := by
  rw [sly_cstream_rpStream]
  congr 1
  apply List.ext_getElem (by simp [moveRecs])
  intro i h1 _
  have hi : i < 2 ^ N := by simpa [moveRecs] using h1
  simp only [moveRecs, List.getElem_ofFn, Equiv.symm_symm]
  rw [slyRecs_getD _ (Fin.isLt _), slyRecs_getElem]
  simp [Nat.mod_eq_of_lt hi]

end Records

/-! ### The loader files after the last move -/

section Files

variable {T A t₀ : ℕ} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}

/-- After the last single-bit move: masks of at most `n` symbols, the stream consumed. -/
theorem sly_ldlWM_full (_h : LdlRegs rg lr) {n : ℕ} (R : Fin T → List (Fin (A + 4)))
    (bs : List (ℕ × ℕ)) (hdM : R (lr .dM) = ldlBitStream A n bs) (hmA : (R (rg .mA)).length ≤ n)
    (hmB : (R (rg .mB)).length ≤ n) :
    ∃ mA mB : List (Fin (A + 4)), mA.length ≤ n ∧ mB.length ≤ n ∧
      ldlWM rg lr A n R bs bs.length =
        Function.update (Function.update (Function.update R (rg .mA) mA) (rg .mB) mB)
          (lr .dM) [] := by
  cases bs with
  | nil =>
      refine ⟨R (rg .mA), R (rg .mB), hmA, hmB, ?_⟩
      rw [ldlBitStream, List.flatMap_nil] at hdM
      simp only [List.length_nil, ldlWM, Function.update_eq_self, ← hdM]
  | cons e bs =>
      refine ⟨binSyms n (2 ^ ((e :: bs).getD bs.length (0, 0)).1),
        binSyms n (2 ^ ((e :: bs).getD bs.length (0, 0)).2), by simp, by simp, ?_⟩
      simp only [List.length_cons, ldlWM, List.drop_succ_cons, List.drop_length, ldlBitStream,
        List.flatMap_nil]

/-- After the last exchange: headers of at most `w + 1` symbols, the stream consumed. -/
theorem sly_ldlWX_full (h : LdlRegs rg lr) {hd : Fin 5 → Fin t₀} (hi : Function.Injective hd)
    {w : ℕ} (R : Fin T → List (Fin (A + 4))) (xs : List LayXcD)
    (hdX : R (lr .dX) = ldlXcStream A w xs) (hH : ∀ k, (R (ldlH rg hd k)).length ≤ w + 1)
    (hw : ∀ d ∈ xs, ∀ k, (d.hs k).length ≤ w) :
    ∃ hs : Fin 5 → List (Fin (A + 4)), (∀ k, (hs k).length ≤ w + 1) ∧
      ldlWX rg lr hd A w R xs xs.length =
        Function.update (ldlSetH rg hd R hs) (lr .dX) [] := by
  cases xs with
  | nil =>
      refine ⟨fun k => R (ldlH rg hd k), hH, ?_⟩
      rw [ldlXcStream, List.flatMap_nil] at hdX
      have e : ldlSetH rg hd R (fun k => R (ldlH rg hd k)) = R := by
        funext y
        rw [ldlSetH_apply h.rg_inj hi]
        split_ifs with hy
        · rw [hy.choose_spec]
        · rfl
      simp only [List.length_nil, ldlWX, e, ← hdX, Function.update_eq_self]
  | cons d xs =>
      refine ⟨fun k => separator :: (((d :: xs).getD xs.length default).hs k).map bitSymbol,
        fun k => ?_, ?_⟩
      · have hm : (d :: xs).getD xs.length default ∈ d :: xs := by
          rw [List.getD_eq_getElem _ _ (by simp)]
          exact List.getElem_mem _
        have := hw _ hm k
        simp only [List.length_cons, List.length_map]
        omega
      · simp only [List.length_cons, ldlWX, List.drop_succ_cons, List.drop_length, ldlXcStream,
          List.flatMap_nil]

/-- The bank registers of the loader files depend on the bank of the base file only. -/
theorem sly_ldlW_sw_congr (h : LdlRegs rg lr) {hd : Fin 5 → Fin t₀} (hi : Function.Injective hd)
    (n w : ℕ) (R R' : Fin T → List (Fin (A + 4))) (bs : List (ℕ × ℕ)) (xs : List LayXcD)
    (hR : ∀ i, R (rg (.sw i)) = R' (rg (.sw i))) (j : ℕ) (i : Fin (swapT t₀)) :
    ldlW rg lr hd A n w R bs xs j (rg (.sw i)) = ldlW rg lr hd A n w R' bs xs j (rg (.sw i)) := by
  have hM : ∀ (S : Fin T → List (Fin (A + 4))) (j : ℕ),
      ldlWM rg lr A n S bs j (rg (.sw i)) = S (rg (.sw i)) := fun S j =>
    ldlWM_rg n S bs j h (by simp) (by simp)
  simp only [ldlW]
  split_ifs with hj
  · rw [hM, hM, hR]
  · cases hjx : j - bs.length with
    | zero => simp only [ldlWX]; rw [hM, hM, hR]
    | succ j' =>
        by_cases hk : ∃ k, ldlH rg hd k = rg (.sw i)
        · obtain ⟨k, hk⟩ := hk
          rw [← hk, ldlWX_H hd hi w _ xs j' h k, ldlWX_H hd hi w _ xs j' h k]
        · simp only [not_exists] at hk
          rw [ldlWX_rg hd hi w _ xs _ h hk, ldlWX_rg hd hi w _ xs _ h hk, hM, hM, hR]

end Files

section Cost

variable {T t₀ Ka : ℕ}

/-- The exchange loop cost depends on the bank registers of the loader files only. -/
theorem sly_layXcLoopCost_congr (n K B : ℕ) (rg : LayReg t₀ → Fin T)
    (W W' : ℕ → Fin T → List (Fin (prime + Ka + 4)))
    (hW : ∀ j i, W (j + 1) (rg (.sw i)) = W' (j + 1) (rg (.sw i))) (cp : ℕ → ℕ) (xs : List LayXcD) :
    layXcLoopCost T t₀ n K B rg W cp xs = layXcLoopCost T t₀ n K B rg W' cp xs := by
  have hs : ∀ j, (∑ i, (W (j + 1) (rg (.sw i))).length) =
      ∑ i, (W' (j + 1) (rg (.sw i))).length :=
    fun j => Finset.sum_congr rfl fun i _ => by rw [hW]
  unfold layXcLoopCost layXcStep
  simp only [hs]

end Cost

/-! ### Base files with other description streams -/

section Base

variable {T t₀ Ka : ℕ} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}

/-- A base file with the description streams of other moves. -/
theorem LdlBase.slySet (h : LdlRegs rg lr) {hd : Fin 5 → Fin t₀} {pay : Fin t₀}
    {R : Fin T → List (Fin (prime + Ka + 4))} {n B wX : ℕ} {bs : List (ℕ × ℕ)} {xs : List LayXcD}
    (hb : LdlBase rg lr hd pay R n B wX bs xs) (bs' : List (ℕ × ℕ)) (xs' : List LayXcD) :
    LdlBase rg lr hd pay
      (Function.update (Function.update R (lr .dM) (ldlBitStream (prime + Ka) n bs')) (lr .dX)
        (ldlXcStream (prime + Ka) wX xs')) n B wX bs' xs' := by
  have e : ∀ x : LayReg t₀,
      Function.update (Function.update R (lr .dM) (ldlBitStream (prime + Ka) n bs')) (lr .dX)
        (ldlXcStream (prime + Ka) wX xs') (rg x) = R (rg x) := fun x => by
    rw [Function.update_of_ne (h.disj _ _), Function.update_of_ne (h.disj _ _)]
  have f : ∀ y : LdlReg, y ≠ .dM → y ≠ .dX →
      Function.update (Function.update R (lr .dM) (ldlBitStream (prime + Ka) n bs')) (lr .dX)
        (ldlXcStream (prime + Ka) wX xs') (lr y) = R (lr y) := fun y h1 h2 => by
    rw [Function.update_of_ne (h.lr_inj.ne h2), Function.update_of_ne (h.lr_inj.ne h1)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [e]; exact hb.r0
  · rw [e]; exact hb.r1
  · rw [e]; exact hb.r2
  · rw [e]; exact hb.r3
  · rw [e]; exact hb.q0
  · rw [e]; exact hb.q1
  · rw [e]; exact hb.q2
  · rw [e]; exact hb.q3
  · rw [e]; exact hb.tmp
  · rw [e]; exact hb.ctrB
  · rw [e]; exact hb.cnt
  · rw [e]; exact hb.fld
  · intro r; rw [e]; exact hb.us r
  · rw [e]; exact hb.mA
  · rw [e]; exact hb.mB
  · rw [e]; exact hb.bpay
  · intro j hj; rw [e]; exact hb.bpriv j hj
  · intro i hi hk; rw [e]; exact hb.bother i hi hk
  · intro k
    simp only [ldlH]
    rw [e]
    exact hb.hdr k
  · rw [Function.update_of_ne (h.lr_inj.ne (show (LdlReg.dM : LdlReg) ≠ .dX by simp)),
      Function.update_self]
  · rw [Function.update_self]
  · rw [f _ (by simp) (by simp)]; exact hb.cN
  · rw [f _ (by simp) (by simp)]; exact hb.cW
  · rw [f _ (by simp) (by simp)]; exact hb.tA
  · rw [f _ (by simp) (by simp)]; exact hb.tB
  · rw [f _ (by simp) (by simp)]; exact hb.tS

end Base

/-! ### Clearing with a bound -/

section Clear

variable {Q A : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q A U)
  {R : Fin (nT SXReg) → List (Fin (A + 4))} {v : SynW → List (Fin (A + 4))}

theorem sgL_clear {a : SynW} {x : ℕ} (ha : (v a).length ≤ x) :
    LayRuns body (uclear (sreg a)) (synG R v) (synG R (Function.update v a [])) (2 * x + 2) :=
  lr_weaken body (sg_uclear body a) rfl (by omega)

theorem soL_clear {o : Fin (nT SXReg)} (ho : ∀ z, sreg z ≠ o) {x : ℕ} (hx : (R o).length ≤ x) :
    LayRuns body (uclear o) (synG R v) (synG (Function.update R o []) v) (2 * x + 2) :=
  lr_weaken body (lr_uclear body o) (by rw [synG_update_out ho]) (by rw [synG_of_ne ho]; omega)

end Clear

end IntegerMultBounds.MathlibTM2.Fast
