module

public import IntegerMultBounds.MathlibTM2.Fast.DistCrt

/-!
# Register primitives of the distribution machine

Contracts in the register-file form `dsRuns` for:

* `bcopy`, `bclear`, `umulSym` (`ds_bcopy`, `ds_bclear`, `ds_umulSym`);
* `dsSetVars`: the variables of a list set to one register value (`ds_zeroVars`: `zeroBits`
  from `wr`; `ds_clearVars`: `bclear`);
* `dsMoveN u tm a b = scanP u tm (popPush a b)`: the top `|u|` symbols of `a` move onto `b`,
  reversed (`ds_moveN`);
* `dsNarrow rg x uL tm tb tx o`: the low `|uL|` bits of variable `x` onto `o`, least significant
  on top (`ds_narrow`): `o` gains `binSyms |uL| (val x)`;
* `dsLoadG rg u x` on any table layout (`ds_loadG`);
* `dsTwist rg uP uR uW out conj` on an 84-variable layout with empty variables: zero the
  variables, load `p, r, w` into `54, 56, 58`, run the twist table program
  (`TableVM.tblTwistCode`) onto `out`, clear the variables (`ds_twist`): `out` gains
  `tblTwistStream A w p r conj`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ### Single operations -/

section Single

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem ds_bcopy {a c t₁ t₂ : Fin T} (hreg : [a, c, t₁, t₂].Nodup) (R : Regs T A)
    (h₁ : R t₁ = []) (h₂ : R t₂ = []) :
    dsRuns body (bcopy a c t₁ t₂) R (Function.update R c (R a ++ R c)) (6 * (R a).length + 6) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := bcopy_exec body hreg v S (by rw [hS, h₁]) (by rw [hS, h₂])
  rw [hS] at he
  exact ⟨v', _, hu, le_rfl, he⟩

theorem ds_bclear (a : Fin T) (R : Regs T A) :
    dsRuns body (bclear a) R (Function.update R a []) (2 * (R a).length + 2) := by
  intro v S hS
  obtain ⟨v', hu, -, he⟩ := bclear_exec body a v S
  rw [hS] at he
  exact ⟨v', _, hu, le_rfl, he⟩

theorem ds_umulSym (c : ℕ) (y : Fin (A + 4)) {a b t : Fin T} (hab : a ≠ b) (hat : a ≠ t)
    (hbt : b ≠ t) (R : Regs T A) (ht : R t = []) :
    dsRuns body (umulSym c y a b t) R
      (Function.update R b (List.replicate (c * (R a).length) y ++ R b)) (4 * (R a).length + 4) := by
  intro v S hS
  obtain ⟨v', hu, he⟩ := umulSym_exec body c y hab hat hbt v S (by rw [hS, ht])
  rw [hS] at he
  exact ⟨v', _, hu, le_rfl, he⟩

/-- `scanP u tm (popPush a b)`: the top `|u|` symbols of `a` move onto `b`. -/
def dsMoveN (u tm a b : Fin T) : Pr P T Q A U := scanP u tm (.act (popPush a b))

theorem ds_moveN {u tm a b : Fin T} (hreg : [u, tm, a, b].Nodup) (R : Regs T A) (ht : R tm = [])
    (hL : (R u).length ≤ (R a).length) :
    dsRuns body (dsMoveN u tm a b) R
      (Function.update (Function.update R a ((R a).drop (R u).length)) b
        (((R a).take (R u).length).reverse ++ R b)) (6 * (R u).length + 4) := by
  have hreg' := hreg
  regs_ne hreg'
  have hut : u ≠ tm := ‹_›
  have hua : u ≠ a := ‹_›
  have hub : u ≠ b := ‹_›
  have hta : tm ≠ a := ‹_›
  have htb : tm ≠ b := ‹_›
  have hab : a ≠ b := ‹_›
  set Ψ : ℕ → Regs T A := fun j => Function.update (Function.update R a ((R a).drop j)) b
    (((R a).take j).reverse ++ R b) with hΨ
  have hspec : IterSpec body (.act (popPush a b)) u tm Ψ (fun _ => 1) (R u).length := by
    intro j hj v S hS
    have hSa : S.R a = (R a).drop j := by rw [hS a hua.symm hta.symm, hΨ]; simp [Function.update_of_ne hab]
    have hSb : S.R b = ((R a).take j).reverse ++ R b := by rw [hS b hub.symm htb.symm, hΨ]; simp
    have hj' : j < (R a).length := by omega
    obtain ⟨x, hx⟩ : ∃ x, (R a).drop j = x :: (R a).drop (j + 1) :=
      ⟨(R a)[j], List.drop_eq_getElem_cons hj'⟩
    set R₂ := Function.update (Function.update S.R a ((R a).drop (j + 1))) b (x :: S.R b) with hR₂
    have hrun : (popPush a b : Act T Q A U).run (mk v S) = mk { v with sym := some x }
        { S with R := R₂ } := by
      simp [popPush, Action.run, hSa, hx, update_rt, Function.update_of_ne hab.symm, hR₂]
    refine ⟨{ v with sym := some x }, R₂, 1, rfl, le_rfl, hrun ▸ Exec.act _ (mk v S), ?_, ?_,
      fun k hku hkt => ?_⟩
    · simp [hR₂, Function.update_of_ne hua, Function.update_of_ne hub]
    · simp [hR₂, Function.update_of_ne hta, Function.update_of_ne htb]
    · have htake : (R a).take (j + 1) = (R a).take j ++ [x] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj']
        have : (R a)[j] = x := by
          have := congrArg List.head? hx
          rw [List.head?_drop] at this
          simpa [List.getElem?_eq_getElem hj'] using this
        rw [this]; rfl
      by_cases hka : k = a
      · subst hka; simp [hR₂, hΨ, Function.update_of_ne hab]
      by_cases hkb : k = b
      · subst hkb; simp [hR₂, hΨ, hSb, htake]
      rw [hR₂, Function.update_of_ne hkb, Function.update_of_ne hka, hS k hku hkt, hΨ]
      simp [Function.update_of_ne hkb, Function.update_of_ne hka]
  intro v S hS
  obtain ⟨v', R', m, hu, hm, he, hRu, hRt, hR'⟩ := scanP_exec body hut hspec 0 v S
    (by rw [hS]; omega) (fun k _ _ => by rw [hS, hΨ]; simp)
  refine ⟨v', m, hu, ?_, ?_⟩
  · rw [hS, ht] at hm
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_nil] at hm
    omega
  · have e : R' = Function.update (Function.update R a ((R a).drop (R u).length)) b
        (((R a).take (R u).length).reverse ++ R b) := by
      funext k
      by_cases hku : k = u
      · rw [hku, hRu, hS, ht, Function.update_of_ne hub, Function.update_of_ne hua]
        simp
      by_cases hkt : k = tm
      · rw [hkt, hRt, Function.update_of_ne htb, Function.update_of_ne hta, ht]
      rw [hR' k hku hkt, hS, Nat.zero_add]
    rw [e] at he
    exact he

end Single

/-! ### Lists of variables -/

section Vars

variable {T Q A m : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR m → Fin T}

/-- The variables of `l` set to `x`. -/
def dsSetVars (rg : TblR m → Fin T) (x : List (Fin (A + 4))) (l : List (Fin m)) (R : Regs T A) :
    Regs T A :=
  l.foldl (fun R i => Function.update R (rg (.v i)) x) R

theorem dsSetVars_apply (hrg : Function.Injective rg) (x : List (Fin (A + 4))) :
    ∀ (l : List (Fin m)) (R : Regs T A) (k : Fin T),
      dsSetVars rg x l R k = if ∃ i ∈ l, rg (.v i) = k then x else R k
  | [], R, k => by simp [dsSetVars]
  | i :: l, R, k => by
    rw [dsSetVars, List.foldl_cons, ← dsSetVars, dsSetVars_apply hrg x l]
    by_cases h1 : ∃ j ∈ l, rg (.v j) = k
    · rw [ite_eq_left h1, ite_eq_left (by obtain ⟨j, hj, e⟩ := h1; exact ⟨j, List.mem_cons_of_mem _ hj, e⟩)]
    · rw [ite_eq_right h1]
      by_cases h2 : rg (.v i) = k
      · subst h2; simp
      · rw [Function.update_of_ne (Ne.symm h2), ite_eq_right]
        rintro ⟨j, hj, e⟩
        rcases List.mem_cons.1 hj with rfl | hj
        · exact h2 e
        · exact h1 ⟨j, hj, e⟩

/-- Zero the variables of `l` from `wr`, through `z 0`. -/
def dsZeroVars (rg : TblR m → Fin T) : List (Fin m) → Pr P T Q A U
  | [] => .act .done
  | i :: l => .seq (zeroBits (rg .wr) (rg (.v i)) (rg (.z 0))) (dsZeroVars rg l)

/-- Clear the variables of `l`. -/
def dsClearVars (rg : TblR m → Fin T) : List (Fin m) → Pr P T Q A U
  | [] => .act .done
  | i :: l => .seq (bclear (rg (.v i))) (dsClearVars rg l)

variable (hrg : Function.Injective rg)
include hrg

theorem ds_zeroVars {W : ℕ} : ∀ (l : List (Fin m)) (R : Regs T A), l.Nodup →
    (∀ i ∈ l, R (rg (.v i)) = []) → R (rg (.z 0)) = [] → (R (rg .wr)).length = W →
      dsRuns body (dsZeroVars rg l) R (dsSetVars rg (binSyms W 0) l R)
        (l.length * (4 * W + 4) + 1)
  | [], R, _, _, _, _ => by
    refine (ds_act _ _ _ fun v S hS => ⟨v, rfl, ?_⟩).mono (by simp)
    simp [Action.run, dsSetVars, ← hS]
  | i :: l, R, hl, h0, hz, hw => by
    have hl' := List.nodup_cons.1 hl
    have h1 : dsRuns body (zeroBits (rg .wr) (rg (.v i)) (rg (.z 0))) R
        (Function.update R (rg (.v i)) (binSyms W 0)) (4 * W + 4) := by
      intro v S hS
      obtain ⟨v', hu, he⟩ := zeroBits_exec body (len := rg .wr) (z := rg (.v i)) (t := rg (.z 0))
        (hrg.ne (by simp)) (hrg.ne (by simp)) (hrg.ne (by simp)) v S (by rw [hS, hz])
      rw [hS, hw, h0 i List.mem_cons_self, List.append_nil] at he
      exact ⟨v', _, hu, le_rfl, he⟩
    have h2 := ds_zeroVars (W := W) l (Function.update R (rg (.v i)) (binSyms W 0)) hl'.2
      (fun j hj => by
        have hji : j ≠ i := fun e => hl'.1 (e ▸ hj)
        rw [Function.update_of_ne (hrg.ne (by simpa using hji))]
        exact h0 j (List.mem_cons_of_mem _ hj))
      (by rw [Function.update_of_ne (hrg.ne (by simp))]; exact hz)
      (by rw [Function.update_of_ne (hrg.ne (by simp))]; exact hw)
    refine (h1.seq h2).mono ?_
    simp only [List.length_cons]; ring_nf; omega

theorem ds_clearVars : ∀ (l : List (Fin m)) (R : Regs T A) (L : ℕ), l.Nodup →
    (∀ i ∈ l, (R (rg (.v i))).length = L) →
      dsRuns body (dsClearVars rg l) R (dsSetVars rg [] l R) (l.length * (2 * L + 2) + 1)
  | [], R, _, _, _ => by
    refine (ds_act _ _ _ fun v S hS => ⟨v, rfl, ?_⟩).mono (by simp)
    simp [Action.run, dsSetVars, ← hS]
  | i :: l, R, L, hl, h0 => by
    have hl' := List.nodup_cons.1 hl
    have h1 := ds_bclear (body := body) (rg (.v i)) R
    rw [h0 i List.mem_cons_self] at h1
    have h2 := ds_clearVars l (Function.update R (rg (.v i)) []) L hl'.2 (fun j hj => by
      have hji : j ≠ i := fun e => hl'.1 (e ▸ hj)
      rw [Function.update_of_ne (hrg.ne (by simpa using hji))]
      exact h0 j (List.mem_cons_of_mem _ hj))
    refine (h1.seq h2).mono ?_
    simp only [List.length_cons]; ring_nf; omega

/-- Load the length of the unary register `u` into variable `x`. -/
def dsLoadG (rg : TblR m → Fin T) (u : Fin T) (x : Fin m) : Pr P T Q A U :=
  .seq (bclear (rg (.v x))) (toBinary u (rg .wr) (rg (.v x)) (rg (.z 0)) (rg (.z 1)) (rg (.z 10)))

/-- **Loading**: variable `x` becomes `|u|`. -/
theorem ds_loadG {u : Fin T} (hu : ∀ r, rg r ≠ u) {W : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (σ : Fin m → ℕ) (x : Fin m) (R : Regs T A) :
    dsRuns body (dsLoadG rg u x) (dsOv rg R (tblRho W wl nl ⟨σ, []⟩))
      (dsOv rg R (tblRho W wl nl ⟨Function.update σ x (R u).length, []⟩))
      (2 * W + 2 + ((R u).length * (4 * W + 10) + 4 * W + 8)) := by
  intro v S hS
  obtain ⟨v₁, hu₁, -, he₁⟩ := bclear_exec body (rg (.v x)) v S
  have hreg : [u, rg .wr, rg (.v x), rg (.z 0), rg (.z 1)].Nodup := by
    have h4 := tbl_nodup hrg (l := [.wr, .v x, .z 0, .z 1]) (by simp)
    simp only [List.map_cons, List.map_nil] at h4
    have hu' : u ∉ [rg .wr, rg (.v x), rg (.z 0), rg (.z 1)] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hu _ h.symm, fun h => hu _ h.symm, fun h => hu _ h.symm,
        fun h => hu _ h.symm⟩
    exact List.nodup_cons.2 ⟨hu', h4⟩
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := toBinary_exec body hreg (rg (.z 10)) v₁
    { S with R := Function.update S.R (rg (.v x)) [] } (by simp)
    (by simp [Function.update_of_ne (hrg.ne (show (TblR.z 0 : TblR m) ≠ .v x by simp)), hS,
      dsOv_rg hrg])
    (by simp [Function.update_of_ne (hrg.ne (show (TblR.z 1 : TblR m) ≠ .v x by simp)), hS,
      dsOv_rg hrg])
  dsimp only at he₂ hm₂
  have e : Function.update (Function.update S.R (rg (.v x)) []) (rg (.v x))
      (binSyms ((Function.update S.R (rg (.v x)) []) (rg .wr)).length
        ((Function.update S.R (rg (.v x)) []) u).length) =
      dsOv rg R (tblRho W wl nl ⟨Function.update σ x (R u).length, []⟩) := by
    simp only [Function.update_idem]
    refine dsOv_eq_of hrg (fun r => ?_) (fun k hk => ?_)
    · by_cases hr : r = .v x
      · subst hr
        rw [Function.update_self, Function.update_of_ne (hrg.ne (by simp)),
          Function.update_of_ne (Ne.symm (hu _)), hS, dsOv_rg hrg, dsOv_off _ _ hu]
        simp [hwl]
      · rw [Function.update_of_ne (hrg.ne hr), hS, dsOv_rg hrg]
        cases r with
        | v i =>
          have hi : i ≠ x := fun h => hr (by rw [h])
          simp [Function.update_of_ne hi]
        | _ => rfl
    · rw [Function.update_of_ne (Ne.symm (hk _)), hS, dsOv_off _ _ hk]
  rw [e] at he₂
  refine ⟨v₂, _, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
  have e1 : (S.R (rg (.v x))).length = W := by rw [hS, dsOv_rg hrg]; simp
  have e2 : ((Function.update S.R (rg (.v x)) []) u).length = (R u).length := by
    rw [Function.update_of_ne (Ne.symm (hu _)), hS, dsOv_off _ _ hu]
  have e3 : ((Function.update S.R (rg (.v x)) []) (rg .wr)).length = W := by
    rw [Function.update_of_ne (hrg.ne (by simp)), hS, dsOv_rg hrg]; simp [hwl]
  rw [e1]; rw [e2, e3] at hm₂; omega

/-- The low `|uL|` bits of variable `x` onto `o`, least significant on top, through the empty
spares `tm`, `tb`, `tx`. -/
def dsNarrow (rg : TblR m → Fin T) (x : Fin m) (uL tm tb tx o : Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg (.v x)) tb (rg (.z 0)) (rg (.z 1))) (.seq (dsMoveN uL tm tb tx)
    (.seq (bclear tb) (moveR tx o id)))

theorem ds_narrow {x : Fin m} {uL tm tb tx o : Fin T} (hreg : [uL, tm, tb, tx, o].Nodup)
    (hoff : ∀ k ∈ [uL, tm, tb, tx, o], ∀ r, rg r ≠ k) {W : ℕ} (wl nl : List (Fin (A + 4)))
    (st : TblSt m A) (R : Regs T A) (htm : R tm = []) (htb : R tb = []) (htx : R tx = [])
    (hL : (R uL).length ≤ W) :
    dsRuns body (dsNarrow rg x uL tm tb tx o) (dsOv rg R (tblRho W wl nl st))
      (dsOv rg (Function.update R o (binSyms (R uL).length (st.val x) ++ R o))
        (tblRho W wl nl st)) (14 * W + 14) := by
  have hreg' := hreg
  regs_ne hreg'
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hoff
  obtain ⟨huL, htm', htb', htx', ho⟩ := hoff
  set L := (R uL).length with hLdef
  set l : List (Fin (A + 4)) := binSyms W (st.val x) with hl
  have hll : l.length = W := by simp [hl]
  -- copy
  have s1 := ds_bcopy (body := body) (a := rg (.v x)) (c := tb) (t₁ := rg (.z 0)) (t₂ := rg (.z 1))
    (by
      have h3 := tbl_nodup hrg (l := [.v x, .z 0, .z 1]) (by simp)
      simp only [List.map_cons, List.map_nil] at h3
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h3 ⊢
      exact ⟨⟨htb' _, h3.1.1, h3.1.2⟩, ⟨fun h => htb' _ h.symm, fun h => htb' _ h.symm⟩, h3.2⟩)
    (dsOv rg R (tblRho W wl nl st)) (by rw [dsOv_rg hrg]; rfl) (by rw [dsOv_rg hrg]; rfl)
  rw [dsOv_rg hrg, tblRho_v, dsOv_off _ _ htb', htb, List.append_nil, dsOv_update _ _ htb'] at s1
  -- move `L` bits
  have s2 := ds_moveN (body := body) (u := uL) (tm := tm) (a := tb) (b := tx)
    (by simp [List.nodup_cons]; exact ⟨⟨‹uL ≠ tm›, ‹uL ≠ tb›, ‹uL ≠ tx›⟩, ⟨‹tm ≠ tb›, ‹tm ≠ tx›⟩,
      ‹tb ≠ tx›⟩)
    (dsOv rg (Function.update R tb (binSyms W (st.val x))) (tblRho W wl nl st))
    (by rw [dsOv_off _ _ htm', Function.update_of_ne ‹tm ≠ tb›, htm])
    (by rw [dsOv_off _ _ huL, dsOv_off _ _ htb', Function.update_of_ne ‹uL ≠ tb›,
      Function.update_self]; simpa using hL)
  rw [dsOv_off _ _ huL, dsOv_off _ _ htb', dsOv_off _ _ htx', Function.update_of_ne ‹uL ≠ tb›,
    Function.update_self, Function.update_of_ne ‹tb ≠ tx›.symm, htx, List.append_nil,
    dsOv_update _ _ htb', dsOv_update _ _ htx'] at s2
  -- clear the rest
  set R₂ := Function.update (Function.update (Function.update R tb (binSyms W (st.val x))) tb
    (List.drop L (binSyms W (st.val x)))) tx (List.take L (binSyms W (st.val x))).reverse with hR₂
  have s3 := ds_bclear (body := body) tb (dsOv rg R₂ (tblRho W wl nl st))
  rw [dsOv_off _ _ htb', dsOv_update _ _ htb'] at s3
  have s4 := ds_moveR (body := body) ‹tx ≠ o› (dsOv rg (Function.update R₂ tb []) (tblRho W wl nl st))
  rw [dsOv_off _ _ htx', dsOv_off _ _ ho, dsOv_update _ _ htx', dsOv_update _ _ ho] at s4
  have htake : List.take L (binSyms W (st.val x)) = (binSyms L (st.val x) : List (Fin (A + 4))) := by
    have e : W = L + (W - L) := by omega
    rw [e, binSyms_append, List.take_left' (by simp)]
  have e : Function.update (Function.update (Function.update R₂ tb []) tx []) o
      (((Function.update R₂ tb []) tx).reverse ++ (Function.update R₂ tb []) o) =
      Function.update R o (binSyms L (st.val x) ++ R o) := by
    funext k
    simp only [hR₂, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [htake]
  rw [e] at s4
  refine (s1.seq (s2.seq (s3.seq s4))).mono ?_
  simp only [List.length_drop, List.length_take, List.length_reverse, length_binSyms, hR₂,
    Function.update_apply]
  simp [‹tb ≠ tx›, Ne.symm ‹tb ≠ tx›, ‹tx ≠ o›.symm, ‹tb ≠ o›]
  omega

end Vars

/-! ### The twist streams -/

section Twist

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR 84 → Fin T}

/-- The twist stream on an 84-variable layout with empty variables: zero, load `p, r, w` into
`54, 56, 58`, run `tblTwistCode conj` onto `out`, clear the variables. -/
def dsTwist (rg : TblR 84 → Fin T) (uP uR uW out : Fin T) (conj : Bool) : Pr P T Q A U :=
  .seq (dsZeroVars rg (List.finRange 84)) <| .seq (dsLoadG rg uP 54) <| .seq (dsLoadG rg uR 56) <|
  .seq (dsLoadG rg uW 58) <| .seq (tblHost rg (tblTwistCode conj) out)
    (dsClearVars rg (List.finRange 84))

/-- The step bound of `dsTwist`. -/
def dsTwistCost (W w p r : ℕ) : ℕ :=
  (84 * (4 * W + 4) + 1) + (2 * W + 2 + (p * (4 * W + 10) + 4 * W + 8)) +
    (2 * W + 2 + (r * (4 * W + 10) + 4 * W + 8)) + (2 * W + 2 + (w * (4 * W + 10) + 4 * W + 8)) +
    ((r * (39 * p + 626) + 200 * p + 4 * w + 1503) * tblC W w + 2 * (r * w) + 2) +
    (84 * (2 * W + 2) + 1)

/-- **The twist stream.** -/
theorem ds_twist (hrg : Function.Injective rg) {uP uR uW out : Fin T}
    (hoff : ∀ k ∈ [uP, uR, uW, out], ∀ r, rg r ≠ k) (conj : Bool) {W w p r : ℕ} (R : Regs T A)
    (hv : ∀ i, R (rg (.v i)) = []) (hacc : R (rg .acc) = []) (hz : ∀ j, R (rg (.z j)) = [])
    (hwr : (R (rg .wr)).length = W) (hwn : (R (rg .wn)).length = w) (hwW : w < W)
    (hP : (R uP).length = p) (hR : (R uR).length = r) (hW : (R uW).length = w)
    (hp2 : p < 2 ^ W) (hr2 : r < 2 ^ W) (hr0 : 0 < r) (hW8 : 8 * p + Nat.size r + 80 ≤ W) :
    dsRuns body (dsTwist rg uP uR uW out conj) R
      (Function.update R out (tblTwistStream A w p r conj ++ R out)) (dsTwistCost W w p r) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hoff
  obtain ⟨hoP, hoR, hoW, hoo⟩ := hoff
  set wl := R (rg .wr)
  set nl := R (rg .wn)
  have hw2 : w < 2 ^ W := hwW.trans Nat.lt_two_pow_self
  -- zero
  have s1 := ds_zeroVars (body := body) hrg (W := W) (List.finRange 84) R (List.nodup_finRange 84)
    (fun i _ => hv i) (hz 0) hwr
  have e1 : dsSetVars rg (binSyms W 0) (List.finRange 84) R =
      dsOv rg R (tblRho W wl nl ⟨fun _ => 0, []⟩) := by
    refine dsOv_eq_of hrg (fun x => ?_) (fun k hk => ?_)
    · rw [dsSetVars_apply hrg]
      cases x with
      | v i => rw [ite_eq_left ⟨i, List.mem_finRange i, rfl⟩]; rfl
      | wr => rw [ite_eq_right (fun ⟨i, _, e⟩ => by simpa using hrg e)]; rfl
      | wn => rw [ite_eq_right (fun ⟨i, _, e⟩ => by simpa using hrg e)]; rfl
      | acc => rw [ite_eq_right (fun ⟨i, _, e⟩ => by simpa using hrg e)]; exact hacc
      | z j => rw [ite_eq_right (fun ⟨i, _, e⟩ => by simpa using hrg e)]; exact hz j
    · rw [dsSetVars_apply hrg, ite_eq_right (fun ⟨i, _, e⟩ => hk _ e)]
  rw [e1] at s1
  -- loads
  have s2 := ds_loadG (body := body) hrg hoP wl nl hwr (fun _ => 0) 54 R
  have s3 := ds_loadG (body := body) hrg hoR wl nl hwr (Function.update (fun _ => 0) 54 (R uP).length)
    56 R
  have s4 := ds_loadG (body := body) hrg hoW wl nl hwr (Function.update (Function.update
    (fun _ => 0) 54 (R uP).length) 56 (R uR).length) 58 R
  set σ : Fin 84 → ℕ := Function.update (Function.update (Function.update (fun _ => 0) 54
    (R uP).length) 56 (R uR).length) 58 (R uW).length with hσ
  have hσlt : ∀ j, σ j < 2 ^ W := by
    intro j; simp only [hσ, Function.update_apply]
    split_ifs <;> omega
  have hin : tblKV (⟨σ, []⟩ : TblSt 84 A) [(54, p), (55, 0), (56, r), (57, 0), (58, w)] := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> simp [hσ, Function.update_apply, hP, hR, hW]
  -- the table program and the clearing
  have s5 : dsRuns body (.seq (tblHost rg (tblTwistCode conj) out) (dsClearVars rg (List.finRange 84)))
      (dsOv rg R (tblRho W wl nl ⟨σ, []⟩))
      (Function.update R out (tblTwistStream A w p r conj ++ R out))
      ((r * (39 * p + 626) + 200 * p + 4 * w + 1503) * tblC W w + 2 * (r * w) + 2 +
        (84 * (2 * W + 2) + 1)) := by
    intro v S hS
    obtain ⟨v₁, S₁, m₁, st', hp, hu₁, hm₁, he₁, hout, hS₁, hi, ho, hL, hk⟩ :=
      tblHost_runs (body := body) hrg hoo wl nl hwr hwn hwW.le
        (tblTwist_do conj (⟨σ, []⟩ : TblSt 84 A) hin hr0 hW8 hwW) hσlt v S
        (fun x => by rw [hS, dsOv_rg hrg])
    rw [List.append_nil] at hp
    have hlen : st'.acc.length = r * w := by
      rw [hp, List.length_reverse]
      exact tbl_stream_length A w r _ (fun j => by simp [tblTwistEntry])
    have hvars : ∀ i ∈ List.finRange 84, (S₁.R (rg (.v i))).length = W := by
      intro i _; rw [hS₁ (.v i)]; simp
    obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := ds_clearVars (body := body) hrg (List.finRange 84) S₁.R W
      (List.nodup_finRange 84) hvars v₁ S₁ rfl
    have eS : ∀ X : Regs T A, ({ S₁ with R := X } : Stacks T A) = { S with R := X } := by
      intro X; cases S₁; simp only at hi ho hL ⊢; rw [hi, ho, hL]
    have eR : dsSetVars rg [] (List.finRange 84) S₁.R =
        Function.update R out (tblTwistStream A w p r conj ++ R out) := by
      funext k
      rw [dsSetVars_apply hrg]
      by_cases hk1 : ∃ i ∈ List.finRange 84, rg (.v i) = k
      · obtain ⟨i, -, rfl⟩ := hk1
        rw [ite_eq_left ⟨i, List.mem_finRange i, rfl⟩, Function.update_of_ne (hoo _), hv i]
      rw [ite_eq_right hk1]
      by_cases hk2 : ∃ x, rg x = k
      · obtain ⟨x, rfl⟩ := hk2
        rw [hS₁ x, Function.update_of_ne (hoo x)]
        cases x with
        | v i => exact absurd ⟨i, List.mem_finRange i, rfl⟩ hk1
        | wr => rfl
        | wn => rfl
        | acc => exact hacc.symm
        | z j => exact (hz j).symm
      · push Not at hk2
        by_cases hko : k = out
        · subst hko
          rw [hout, hp, List.reverse_reverse, Function.update_self, hS, dsOv_off _ _ hoo]
        · rw [hk k hko hk2, Function.update_of_ne hko, hS, dsOv_off _ _ hk2]
    rw [eR, eS] at he₂
    refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
    rw [hlen] at hm₁
    simp only [List.length_finRange] at hm₂
    omega
  refine (s1.seq (s2.seq (s3.seq (s4.seq s5)))).mono ?_
  unfold dsTwistCost
  rw [hP, hR, hW]
  simp only [List.length_finRange]
  omega

end Twist

end IntegerMultBounds.MathlibTM2.Fast.TableVM
