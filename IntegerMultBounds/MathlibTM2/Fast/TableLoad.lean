module

public import IntegerMultBounds.MathlibTM2.Fast.TableVM

/-!
# Loading table-machine variables from unary registers

The pipeline keeps its parameters (`p`, `s_i`, `t_i`, `α`, …) in unary registers: a register
holding `k` symbols carries `k`. `tblLoad1 rg u i` sets variable `i` of a table machine to the
length of the register `u` (outside the layout), as a `W`-bit numeral: it empties the variable
register and runs `toBinary` from `u` (`Host/BinArith.lean`), which restores `u`.

`tbl_load1_runs`: the register file moves from the state `st` to `st` with variable `i` set to
`|u|` (a `W`-bit numeral, so `|u| < 2 ^ W` keeps the value exact), in at most `|u| (4 W + 10) + 6 W + 10` steps; `u` and every other
register outside the layout are unchanged.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Host


variable {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U} {n : ℕ}
  {rg : TblR n → Fin T}

/-- Set variable `i` to the length of the unary register `u`. -/
def tblLoad1 (rg : TblR n → Fin T) (u : Fin T) (i : Fin n) : Pr P T Q A U :=
  .seq (bclear (rg (.v i))) (toBinary u (rg .wr) (rg (.v i)) (rg (.z 7)) (rg (.z 8)) (rg (.z 10)))

/-- `tblLoad1`: variable `i` becomes `|u|`. -/
theorem tbl_load1_runs (hrg : Function.Injective rg) {W : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) {u : Fin T} (hu : ∀ r, rg r ≠ u) (i : Fin n) (st : TblSt n A)
    (k : ℕ) :
    ∀ v S, (S.R u).length = k → tblHolds rg S (tblRho W wl nl st) →
      ∃ v' S' m, v'.user = v.user ∧ m ≤ k * (4 * W + 10) + 6 * W + 10 ∧
        Exec body (tblLoad1 rg u i) (mk v S) m (mk v' S') ∧
        tblHolds rg S' (tblRho W wl nl ⟨Function.update st.val i k, st.acc⟩) ∧ tblFr rg S S' := by
  intro v S hlen' hS
  obtain ⟨v₁, hu₁, -, he₁⟩ := bclear_exec body (rg (.v i)) v S
  set S₁ : Stacks T A := { S with R := Function.update S.R (rg (.v i)) [] } with hS₁
  have hreg : [u, rg .wr, rg (.v i), rg (.z 7), rg (.z 8)].Nodup := by
    have h := tbl_nodup hrg (l := [.wr, .v i, .z 7, .z 8]) (by simp)
    simp only [List.map_cons, List.map_nil] at h
    exact List.nodup_cons.2 ⟨by simp [Ne.symm (hu _)], h⟩
  have h7 : S₁.R (rg (.z 7)) = [] := by
    simp [hS₁, Function.update_of_ne (hrg.ne (show (TblR.z 7 : TblR n) ≠ .v i by simp)), hS (.z 7)]
  have h8 : S₁.R (rg (.z 8)) = [] := by
    simp [hS₁, Function.update_of_ne (hrg.ne (show (TblR.z 8 : TblR n) ≠ .v i by simp)), hS (.z 8)]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := toBinary_exec body hreg (rg (.z 10)) v₁ S₁ (by simp [hS₁]) h7 h8
  have hwr : S₁.R (rg .wr) = wl := by
    simp [hS₁, Function.update_of_ne (hrg.ne (show (TblR.wr : TblR n) ≠ .v i by simp)), hS .wr]
  have huR : S₁.R u = S.R u := by simp [hS₁, Function.update_of_ne (Ne.symm (hu _))]
  rw [hwr, huR, hlen', hwl] at hm₂ he₂
  refine ⟨v₂, _, _, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, ?_, ⟨rfl, rfl, rfl, fun k' hk' => ?_⟩⟩
  · rw [hS, hwl] at *
    simp only [tblRho_v, length_binSyms]
    nlinarith
  · intro r
    dsimp only
    rw [hS₁]
    dsimp only
    rw [tbl_holds_upd hrg (tbl_holds_upd hrg hS (.v i) []) (.v i)]
    by_cases hr : r = .v i
    · subst hr; simp
    · rw [Function.update_of_ne hr, Function.update_of_ne hr]
      cases r <;> simp_all [Function.update_of_ne]
  · dsimp only
    rw [hS₁]
    dsimp only
    rw [Function.update_of_ne (Ne.symm (hk' _)), Function.update_of_ne (Ne.symm (hk' _))]

end IntegerMultBounds.MathlibTM2.Fast.TableVM
