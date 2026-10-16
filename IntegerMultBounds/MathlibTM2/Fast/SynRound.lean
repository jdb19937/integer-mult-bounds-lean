module

public import IntegerMultBounds.MathlibTM2.Fast.SynSel

/-!
# One round of the synthetic transforms

Paper §6, proof of `lem:synthetic-transform-cost`. One round of the computed forward transform at
named position `h` is the layer `Q_p(ℋ)` on the selected bits of the round (`topProg`,
`Fast/SynSel.lean`) followed by the twiddle `J_E` (`twPassLP`, `Fast/TwiddleL.lean`); one round of
the opposite transform is the inverse twiddle followed by the layer. The records stay in the
physical order of the layout `L = layPerm es ℓ K`.

## Register files

* `synIdle io P₀`: `io` holding `io`, `park` holding `P₀`, every other register empty. Between
  rounds the file is `synG (synIdle io P₀) v` with `v` the transform wires (`SynBase`).
* `synRestFile`: the registers of the layer machine at rest for `N` address bits, `r`
  coefficients, words of `w'` symbols, stride `K`, offset `ρ` and piece record `pr`
  (`synRest_topRegs`: `TopRegs`).
* `synRestUp`, `synRestDown`: build them from the wires `p .w2`, `p .N`, `p .r`, `p .kh`, `p .rh`,
  `p .pr`, and clear them.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Fast

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.MathlibTM2.Mult.Rounds IntegerMultBounds.Networks
open IntegerMultBounds.MathlibTM2.Node hiding LReg
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false

/-! ### The idle file and the rest state of the layer machine -/

section Rest

variable {A : ℕ}

/-- The idle file: `io` holding `io`, `park` holding `P₀`, every other register empty. -/
noncomputable def synIdle (io P₀ : List (Fin (A + 4))) : Fin (nT SXReg) → List (Fin (A + 4)) :=
  Function.update (Function.update (fun _ => []) (reg (BReg := SXReg) .io) io)
    (reg (BReg := SXReg) .park) P₀

/-- The rest state of the layer machine on top of `Ro`. -/
noncomputable def synRestFile (Ro : Fin (nT SXReg) → List (Fin (A + 4))) (N r w' K ρ : ℕ)
    (pr : List (Fin (A + 4))) : Fin (nT SXReg) → List (Fin (A + 4)) :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update Ro
    (reg (BReg := SXReg) .ctr) (List.replicate w' tick))
    (reg (BReg := SXReg) .cS) [tick])
    (reg (BReg := SXReg) .cR) (List.replicate (w' - 1) tick))
    (reg (BReg := SXReg) (.ph .rc)) (List.replicate (r * w') tick))
    (reg (BReg := SXReg) (.ph .wc)) (List.replicate w' tick))
    (reg (BReg := SXReg) (.ph .af)) (binSyms N 0))
    (reg (BReg := SXReg) (.lf (.k .rctr))) (List.replicate (r * w') tick))
    (reg (BReg := SXReg) (.lf (.k .wctr))) (List.replicate w' tick))
    (reg (BReg := SXReg) (.lf (.k .cf))) (binSyms N 0))
    (reg (BReg := SXReg) .rowctr) (List.replicate (2 ^ N * (r * w')) tick))
    (reg (BReg := SXReg) .n) (List.replicate N tick))
    (reg (BReg := SXReg) .w) (List.replicate w' tick))
    (reg (BReg := SXReg) .rw) (List.replicate (r * w') tick))
    (reg (BReg := SXReg) .K) (List.replicate K tick))
    (reg (BReg := SXReg) .ρ) (List.replicate ρ tick))
    (reg (BReg := SXReg) (.ph .arr)) pr

theorem synG_reg_nonwire {Ro : Fin (nT SXReg) → List (Fin (A + 4))} {v : SynW → List (Fin (A + 4))}
    {x : LReg SXReg} (hx : ∀ w, x ≠ .wire w) :
    synG Ro v (reg (BReg := SXReg) x) = Ro (reg (BReg := SXReg) x) :=
  synG_of_ne fun _ => sreg_ne_reg hx

theorem synIdle_wire (io P₀ : List (Fin (A + 4))) (w : NWire) :
    synIdle io P₀ (reg (BReg := SXReg) (.wire w)) = [] := by
  simp [synIdle, Function.update_apply]

/-- The rest state is at rest: `TopRegs` for every empty wire file. -/
theorem synRest_topRegs (io P₀ pr : List (Fin (A + 4))) (N r w' K ρ : ℕ)
    (v : SynW → List (Fin (A + 4))) (hv : ∀ x, v x = []) :
    TopRegs (synG (synRestFile (synIdle io P₀) N r w' K ρ pr) v) N r w' K ρ := by
  have hw : ∀ w : NWire,
      synG (synRestFile (synIdle io P₀) N r w' K ρ pr) v (reg (BReg := SXReg) (.wire w)) = [] := by
    intro w
    by_cases h : ∃ x, sreg x = reg (BReg := SXReg) (.wire w)
    · obtain ⟨x, hx⟩ := h
      rw [← hx, synG_sreg, hv]
    · rw [synG_of_ne (fun x hx => h ⟨x, hx⟩)]
      simp [synRestFile, synIdle, Function.update_apply]
  have hnw : ∀ x : LReg SXReg, (∀ w, x ≠ .wire w) →
      synG (synRestFile (synIdle io P₀) N r w' K ρ pr) v (reg (BReg := SXReg) x) =
        synRestFile (synIdle io P₀) N r w' K ρ pr (reg (BReg := SXReg) x) :=
    fun x hx => synG_reg_nonwire hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    cases x with
    | wire w => rw [hw]; rfl
    | ph y =>
        rw [hnw _ (by simp)]
        cases y <;> simp [restSpec, phRest, synRestFile, synIdle, Function.update_apply]
    | lf y =>
        rw [hnw _ (by simp)]
        cases y with
        | k z => cases z <;> simp [restSpec, lfRest, synRestFile, synIdle, Function.update_apply]
        | _ => simp [restSpec, lfRest, synRestFile, synIdle, Function.update_apply]
    | _ =>
        rw [hnw _ (by simp)]
        simp [restSpec, synRestFile, synIdle, Function.update_apply, bcEmpty, Nat.mul_assoc]
  all_goals
    rw [hnw _ (by simp)]
    simp [synRestFile, synIdle, Function.update_apply]

end Rest

/-- A register of the layer machine. -/
noncomputable abbrev lreg (x : LReg SXReg) : Fin (nT SXReg) := reg (BReg := SXReg) x

theorem lreg_out {x : LReg SXReg} (hx : ∀ w, x ≠ .wire w) : ∀ z, sreg z ≠ lreg x :=
  fun _ => sreg_ne_reg hx

/-! ### Building and clearing the rest state -/

section RestProg

variable {Q A : ℕ} {U P : Type}

/-- Build the rest state of the layer machine from the wires `p .w2` (`w'`), `p .N`, `p .r`, and
move `K_h`, `ρ_h` and the piece record from `p .kh`, `p .rh`, `p .pr`; `p .w2` is cleared. -/
noncomputable def synRestUp : Pr P (nT SXReg) Q A U :=
  .seq (ucopy (sreg (.p .w2)) (lreg .ctr) (sreg (.s 2))) <|
  .seq (synPush (lreg .cS) tick) <|
  .seq (ucopy (sreg (.p .w2)) (lreg .cR) (sreg (.s 2))) <| .seq (synPop (lreg .cR)) <|
  .seq (synMulR (sreg (.p .r)) (sreg (.p .w2)) (lreg (.ph .rc)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (ucopy (sreg (.p .w2)) (lreg (.ph .wc)) (sreg (.s 2))) <|
  .seq (zeroBits (sreg (.p .N)) (lreg (.ph .af)) (sreg (.s 2))) <|
  .seq (synMulR (sreg (.p .r)) (sreg (.p .w2)) (lreg (.lf (.k .rctr))) (sreg (.s 2))
    (sreg (.s 3))) <|
  .seq (ucopy (sreg (.p .w2)) (lreg (.lf (.k .wctr))) (sreg (.s 2))) <|
  .seq (zeroBits (sreg (.p .N)) (lreg (.lf (.k .cf))) (sreg (.s 2))) <|
  .seq (synMulR (sreg (.p .r)) (sreg (.p .w2)) (lreg .rowctr) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (upow2 (sreg (.p .N)) (lreg .rowctr) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (ucopy (sreg (.p .N)) (lreg .n) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.p .w2)) (lreg .w) (sreg (.s 2))) <|
  .seq (synMulR (sreg (.p .r)) (sreg (.p .w2)) (lreg .rw) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (moveR (sreg (.p .kh)) (lreg .K) id) <| .seq (moveR (sreg (.p .rh)) (lreg .ρ) id) <|
  .seq (moveR (sreg (.p .pr)) (sreg (.s 4)) id) <| .seq (moveR (sreg (.s 4)) (lreg (.ph .arr)) id)
    (uclear (sreg (.p .w2)))

/-- Clear the rest state of the layer machine. -/
noncomputable def synRestDown : Pr P (nT SXReg) Q A U :=
  .seq (uclear (lreg .ctr)) <| .seq (uclear (lreg .cS)) <| .seq (uclear (lreg .cR)) <|
  .seq (uclear (lreg (.ph .rc))) <| .seq (uclear (lreg (.ph .wc))) <|
  .seq (uclear (lreg (.ph .af))) <| .seq (uclear (lreg (.lf (.k .rctr)))) <|
  .seq (uclear (lreg (.lf (.k .wctr)))) <| .seq (uclear (lreg (.lf (.k .cf)))) <|
  .seq (uclear (lreg .rowctr)) <| .seq (uclear (lreg .n)) <| .seq (uclear (lreg .w)) <|
  .seq (uclear (lreg .rw)) <| .seq (uclear (lreg .K)) <| .seq (uclear (lreg .ρ))
    (uclear (lreg (.ph .arr)))

end RestProg

section RestRuns

variable {Q A : ℕ} {U P : Type} (body : P → Pr P (nT SXReg) Q A U)

/-- The step bound of `synRestUp`. -/
def synRestUpCost (N r w' K ρ prl : ℕ) : ℕ :=
  (4 * w' + 4) + 1 + (4 * w' + 4) + 1 + synMulRCost r w' + (4 * w' + 4) + (4 * N + 4) +
    synMulRCost r w' + (4 * w' + 4) + (4 * N + 4) + synMulRCost r w' +
    (4 * (2 ^ N * (r * w')) + 9 * N + 4) + (4 * N + 4) + (4 * w' + 4) + synMulRCost r w' +
    (2 * K + 2) + (2 * ρ + 2) + (2 * prl + 2) + (2 * prl + 2) + (2 * w' + 2)

theorem lr_synRestUp (Ro : Fin (nT SXReg) → List (Fin (A + 4))) (v : SynW → List (Fin (A + 4)))
    (N r w' K ρ : ℕ) (pr : List (Fin (A + 4)))
    (hRo : ∀ x ∈ [LReg.ctr, .cS, .cR, .ph .rc, .ph .wc, .ph .af, .lf (.k .rctr), .lf (.k .wctr),
      .lf (.k .cf), .rowctr, .n, .w, .rw, .K, .ρ, .ph .arr], Ro (lreg x) = [])
    (hw2 : v (.p .w2) = List.replicate w' tick) (hN : (v (.p .N)).length = N)
    (hr : (v (.p .r)).length = r) (hkh : v (.p .kh) = List.replicate K tick)
    (hrh : v (.p .rh) = List.replicate ρ tick) (hpr : v (.p .pr) = pr)
    (h2 : v (.s 2) = []) (h3 : v (.s 3) = []) (h4 : v (.s 4) = []) :
    LayRuns body synRestUp (synG Ro v)
      (synG (synRestFile Ro N r w' K ρ pr) (Function.update (Function.update (Function.update
        (Function.update v (.p .kh) []) (.p .rh) []) (.p .pr) []) (.p .w2) []))
      (synRestUpCost N r w' K ρ pr.length) := by
  have e := fun x hx => hRo x hx
  refine lr_weaken body
    ((so_copy body (o := lreg .ctr) (a := .p .w2) (t := .s 2) (x := w') (y := 0)
      (lreg_out (by simp)) (by decide) h2 (by simp [hw2]) (by simp [e])).seq <|
    (so_pushV body (o := lreg .cS) (lreg_out (by simp)) tick (l := [])
      (by simp [Function.update_apply, e])).seq <|
    (so_copy body (o := lreg .cR) (a := .p .w2) (t := .s 2) (x := w') (y := 0)
      (lreg_out (by simp)) (by decide) h2 (by simp [hw2])
      (by simp [Function.update_apply, e])).seq <|
    (so_popV body (o := lreg .cR) (y := w' + 0) (lreg_out (by simp)) (by simp)).seq <|
    (so_mulR body (o := lreg (.ph .rc)) (a := .p .r) (b := .p .w2) (t₁ := .s 2) (t₂ := .s 3)
      (x := r) (y := w') (z := 0) (lreg_out (by simp)) (by decide) h2 h3 hr (by simp [hw2])
      (by simp [Function.update_apply, e])).seq <|
    (so_copy body (o := lreg (.ph .wc)) (a := .p .w2) (t := .s 2) (x := w') (y := 0)
      (lreg_out (by simp)) (by decide) h2 (by simp [hw2])
      (by simp [Function.update_apply, e])).seq <|
    (so_zeroBits body (o := lreg (.ph .af)) (a := .p .N) (t := .s 2) (x := N)
      (lreg_out (by simp)) (by decide) h2 hN (by simp [Function.update_apply, e])).seq <|
    (so_mulR body (o := lreg (.lf (.k .rctr))) (a := .p .r) (b := .p .w2) (t₁ := .s 2)
      (t₂ := .s 3) (x := r) (y := w') (z := 0) (lreg_out (by simp)) (by decide) h2 h3 hr
      (by simp [hw2]) (by simp [Function.update_apply, e])).seq <|
    (so_copy body (o := lreg (.lf (.k .wctr))) (a := .p .w2) (t := .s 2) (x := w') (y := 0)
      (lreg_out (by simp)) (by decide) h2 (by simp [hw2])
      (by simp [Function.update_apply, e])).seq <|
    (so_zeroBits body (o := lreg (.lf (.k .cf))) (a := .p .N) (t := .s 2) (x := N)
      (lreg_out (by simp)) (by decide) h2 hN (by simp [Function.update_apply, e])).seq <|
    (so_mulR body (o := lreg .rowctr) (a := .p .r) (b := .p .w2) (t₁ := .s 2) (t₂ := .s 3)
      (x := r) (y := w') (z := 0) (lreg_out (by simp)) (by decide) h2 h3 hr (by simp [hw2])
      (by simp [Function.update_apply, e])).seq <|
    (so_pow2 body (o := lreg .rowctr) (a := .p .N) (t₁ := .s 2) (t₂ := .s 3) (x := N)
      (y := r * w' + 0) (lreg_out (by simp)) (by decide) h2 h3 hN (by simp)).seq <|
    (so_copy body (o := lreg .n) (a := .p .N) (t := .s 2) (x := N) (y := 0)
      (lreg_out (by simp)) (by decide) h2 hN (by simp [Function.update_apply, e])).seq <|
    (so_copy body (o := lreg .w) (a := .p .w2) (t := .s 2) (x := w') (y := 0)
      (lreg_out (by simp)) (by decide) h2 (by simp [hw2])
      (by simp [Function.update_apply, e])).seq <|
    (so_mulR body (o := lreg .rw) (a := .p .r) (b := .p .w2) (t₁ := .s 2) (t₂ := .s 3)
      (x := r) (y := w') (z := 0) (lreg_out (by simp)) (by decide) h2 h3 hr (by simp [hw2])
      (by simp [Function.update_apply, e])).seq <|
    (so_moveWOV body (o := lreg .K) (a := .p .kh) (l := List.replicate K tick) (l' := [])
      (lreg_out (by simp)) (by simp [hkh]) (by simp [Function.update_apply, e])).seq <|
    (so_moveWOV body (o := lreg .ρ) (a := .p .rh) (l := List.replicate ρ tick) (l' := [])
      (lreg_out (by simp)) (by simp [hrh]) (by simp [Function.update_apply, e])).seq <|
    (sgR_move body (a := .p .pr) (b := .s 4) (l := pr) (l' := []) (by decide) (by simp [hpr])
      (by simp [h4])).seq <|
    (so_moveWOV body (o := lreg (.ph .arr)) (a := .s 4) (l := pr.reverse ++ []) (l' := [])
      (lreg_out (by simp)) (by simp) (by simp [Function.update_apply, e])).seq <|
    sgU_clear body (a := .p .w2) (x := w') (by simp [hw2])) ?_ ?_
  · congr 1
    · simp only [synRestFile, List.reverse_replicate, List.append_nil, List.reverse_reverse,
        Nat.add_zero, Nat.mul_assoc, Function.update_idem]
    · funext y
      simp only [Function.update_apply]
      split_ifs <;> simp_all
  · simp only [synRestUpCost, List.length_replicate, List.length_append, List.length_reverse,
      List.length_nil, Nat.add_zero]
    omega

/-- The step bound of `synRestDown`. -/
def synRestDownCost (N r w' K ρ prl : ℕ) : ℕ :=
  (2 * w' + 2) + (2 * 1 + 2) + (2 * (w' - 1) + 2) + (2 * (r * w') + 2) + (2 * w' + 2) +
    (2 * N + 2) + (2 * (r * w') + 2) + (2 * w' + 2) + (2 * N + 2) +
    (2 * (2 ^ N * (r * w')) + 2) + (2 * N + 2) + (2 * w' + 2) + (2 * (r * w') + 2) +
    (2 * K + 2) + (2 * ρ + 2) + (2 * prl + 2)

theorem lr_synRestDown (Ro : Fin (nT SXReg) → List (Fin (A + 4))) (v : SynW → List (Fin (A + 4)))
    (N r w' K ρ : ℕ) (pr : List (Fin (A + 4)))
    (hRo : ∀ x ∈ [LReg.ctr, .cS, .cR, .ph .rc, .ph .wc, .ph .af, .lf (.k .rctr), .lf (.k .wctr),
      .lf (.k .cf), .rowctr, .n, .w, .rw, .K, .ρ, .ph .arr], Ro (lreg x) = []) :
    LayRuns body synRestDown (synG (synRestFile Ro N r w' K ρ pr) v) (synG Ro v)
      (synRestDownCost N r w' K ρ pr.length) := by
  refine lr_weaken body
    ((so_clear body (o := lreg .ctr) (lreg_out (by simp)) (x := w')
      (by simp [synRestFile, Function.update_apply])).seq <|
    (so_clear body (o := lreg .cS) (lreg_out (by simp)) (x := 1)
      (by simp [synRestFile, Function.update_apply])).seq <|
    (so_clear body (o := lreg .cR) (lreg_out (by simp)) (x := w' - 1)
      (by simp [synRestFile, Function.update_apply])).seq <|
    (so_clear body (o := lreg (.ph .rc)) (lreg_out (by simp)) (x := r * w')
      (by simp [synRestFile, Function.update_apply])).seq <|
    (so_clear body (o := lreg (.ph .wc)) (lreg_out (by simp)) (x := w')
      (by simp [synRestFile, Function.update_apply])).seq <|
    (so_clear body (o := lreg (.ph .af)) (lreg_out (by simp)) (x := N)
      (by simp [synRestFile, Function.update_apply, binSyms])).seq <|
    (so_clear body (o := lreg (.lf (.k .rctr))) (lreg_out (by simp)) (x := r * w')
      (by simp [synRestFile, Function.update_apply])).seq <|
    (so_clear body (o := lreg (.lf (.k .wctr))) (lreg_out (by simp)) (x := w')
      (by simp [synRestFile, Function.update_apply])).seq <|
    (so_clear body (o := lreg (.lf (.k .cf))) (lreg_out (by simp)) (x := N)
      (by simp [synRestFile, Function.update_apply, binSyms])).seq <|
    (so_clear body (o := lreg .rowctr) (lreg_out (by simp)) (x := 2 ^ N * (r * w'))
      (by simp [synRestFile, Function.update_apply])).seq <|
    (so_clear body (o := lreg .n) (lreg_out (by simp)) (x := N)
      (by simp [synRestFile, Function.update_apply])).seq <|
    (so_clear body (o := lreg .w) (lreg_out (by simp)) (x := w')
      (by simp [synRestFile, Function.update_apply])).seq <|
    (so_clear body (o := lreg .rw) (lreg_out (by simp)) (x := r * w')
      (by simp [synRestFile, Function.update_apply])).seq <|
    (so_clear body (o := lreg .K) (lreg_out (by simp)) (x := K)
      (by simp [synRestFile, Function.update_apply])).seq <|
    (so_clear body (o := lreg .ρ) (lreg_out (by simp)) (x := ρ)
      (by simp [synRestFile, Function.update_apply])).seq <|
    so_clear body (o := lreg (.ph .arr)) (lreg_out (by simp)) (x := pr.length)
      (by simp [synRestFile, Function.update_apply])) ?_ ?_
  · congr 1
    funext z
    by_cases hz : ∃ x ∈ [LReg.ctr, .cS, .cR, .ph .rc, .ph .wc, .ph .af, .lf (.k .rctr),
        .lf (.k .wctr), .lf (.k .cf), .rowctr, .n, .w, .rw, .K, .ρ, .ph .arr], lreg x = z
    · obtain ⟨x, hx, rfl⟩ := hz
      rw [hRo x hx]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp [Function.update_apply]
    · have nz : ∀ x ∈ [LReg.ctr, .cS, .cR, .ph .rc, .ph .wc, .ph .af, .lf (.k .rctr),
          .lf (.k .wctr), .lf (.k .cf), .rowctr, .n, .w, .rw, .K, .ρ, .ph .arr], lreg x ≠ z :=
        fun x hx h => hz ⟨x, hx, h⟩
      have n1 := nz _ (by simp : LReg.ctr ∈ _)
      have n2 := nz _ (by simp : LReg.cS ∈ _)
      have n3 := nz _ (by simp : LReg.cR ∈ _)
      have n4 := nz _ (by simp : LReg.ph .rc ∈ _)
      have n5 := nz _ (by simp : LReg.ph .wc ∈ _)
      have n6 := nz _ (by simp : LReg.ph .af ∈ _)
      have n7 := nz _ (by simp : LReg.lf (.k .rctr) ∈ _)
      have n8 := nz _ (by simp : LReg.lf (.k .wctr) ∈ _)
      have n9 := nz _ (by simp : LReg.lf (.k .cf) ∈ _)
      have n10 := nz _ (by simp : LReg.rowctr ∈ _)
      have n11 := nz _ (by simp : LReg.n ∈ _)
      have n12 := nz _ (by simp : LReg.w ∈ _)
      have n13 := nz _ (by simp : LReg.rw ∈ _)
      have n14 := nz _ (by simp : LReg.K ∈ _)
      have n15 := nz _ (by simp : LReg.ρ ∈ _)
      have n16 := nz _ (by simp : LReg.ph .arr ∈ _)
      simp only [synRestFile, Function.update_apply, Ne.symm n1, Ne.symm n2, Ne.symm n3,
        Ne.symm n4, Ne.symm n5, Ne.symm n6, Ne.symm n7, Ne.symm n8, Ne.symm n9, Ne.symm n10,
        Ne.symm n11, Ne.symm n12, Ne.symm n13, Ne.symm n14, Ne.symm n15, Ne.symm n16, ite_false]
  · simp only [synRestDownCost]
    omega

end RestRuns

/-! ### The roles of the twiddle -/

section Roles

variable {Q A : ℕ} {U P : Type}

theorem twRoles_snoc (A h : ℕ) : ∀ (l : List ℕ) (e : ℕ),
    twRoles A (l ++ [e]) h = twSeg A e h ++ twRoles A l h
  | [], e => by simp [twRoles]
  | x :: l, e => by
      rw [List.cons_append, twRoles, twRoles_snoc A h l e, twRoles, List.append_assoc]

/-- Push the roles `twSeg A e h` of one axis from `s 27 = e` and `p .h`. -/
noncomputable def synSegP : Pr P (nT SXReg) Q A U :=
  .seq (.seq (ucopy (sreg (.s 27)) (sreg (.s 28)) (sreg (.s 2)))
    (usub (sreg (.p .h)) (sreg (.s 28)) (sreg (.s 2)))) <|
  synIfNE (sreg (.s 28))
    (.seq (synPop (sreg (.s 28))) <|
     .seq (umulSym 1 (bitSymbol false) (sreg (.s 28)) (sreg (.tw .rl)) (sreg (.s 2))) <|
     .seq (synPush (sreg (.tw .rl)) separator) <|
     .seq (umulSym 1 (bitSymbol true) (sreg (.p .h)) (sreg (.tw .rl)) (sreg (.s 2)))
       (uclear (sreg (.s 28))))
    (umulSym 1 (bitSymbol false) (sreg (.s 27)) (sreg (.tw .rl)) (sreg (.s 2)))

/-- One axis of the roles: its field of `p .es` onto `s 26` (its ticks onto `s 27`), its roles. -/
noncomputable def synRoleStep : Pr P (nT SXReg) Q A U :=
  .seq (topField (sreg (.p .es)) (sreg (.s 26)) (sreg (.s 27)) true) <|
  .seq synSegP (uclear (sreg (.s 27)))

/-- `tw .rl := twRoles A es h` from the axis record `p .es = topRec es` and `p .h`. -/
noncomputable def synRoles : Pr P (nT SXReg) Q A U :=
  .seq (scanP (sreg (.p .D)) (sreg (.s 23)) synRoleStep) (moveR (sreg (.s 26)) (sreg (.p .es)) id)

variable (body : P → Pr P (nT SXReg) Q A U) {R : Fin (nT SXReg) → List (Fin (A + 4))}

/-- The step bound of `synSegP`. -/
def synSegCost (e h : ℕ) : ℕ :=
  (4 * e + 4) + (4 * h + 4) +
    ((if h < e then 1 + (4 * (e - h - 1) + 4) + 1 + (4 * h + 4) + (2 * (e - h - 1) + 2)
      else 4 * e + 4) + 2)

theorem sg_synSegP (v : SynW → List (Fin (A + 4))) (e h : ℕ) (rl : List (Fin (A + 4)))
    (h27 : v (.s 27) = List.replicate e tick) (hh : (v (.p .h)).length = h)
    (hrl : v (.tw .rl) = rl) (h2 : v (.s 2) = []) (h28 : v (.s 28) = []) :
    LayRuns body synSegP (synG R v)
      (synG R (Function.update v (.tw .rl) (twSeg A e h ++ rl))) (synSegCost e h) := by
  have s1 := (sgU_copy body (R := R) (v := v) (a := .s 27) (b := .s 28) (t := .s 2) (x := e)
    (y := 0) (by decide) (by decide) (by decide) h2 (by simp [h27]) (by simp [h28])).seq <|
    sgU_sub body (a := .p .h) (b := .s 28) (t := .s 2) (x := h) (y := e + 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hh]) (by simp)
  set v₁ := Function.update (Function.update v (.s 28) (List.replicate (e + 0) tick)) (.s 28)
    (List.replicate (e + 0 - h) tick) with hv₁
  by_cases he : h < e
  · have hne : v₁ (.s 28) ≠ [] := by simp [hv₁]; omega
    have s2 := sg_ifNE_pos body (R := R) (q := umulSym 1 (bitSymbol false) (sreg (.s 27))
      (sreg (.tw .rl)) (sreg (.s 2))) hne
      ((sgU_pop body (a := .s 28) (y := e + 0 - h) (by simp [hv₁])).seq <|
      (sgR_umulSym body 1 (bitSymbol false) (a := .s 28) (b := .tw .rl) (t := .s 2)
        (x := e + 0 - h - 1) (l := rl) (by decide) (by decide) (by decide) (by simp [hv₁, h2])
        (by simp) (by simp [hv₁, hrl])).seq <|
      (sgR_push body (a := .tw .rl) separator
        (l := List.replicate (1 * (e + 0 - h - 1)) (bitSymbol false) ++ rl) (by simp)).seq <|
      (sgR_umulSym body 1 (bitSymbol true) (a := .p .h) (b := .tw .rl) (t := .s 2) (x := h)
        (l := separator :: (List.replicate (1 * (e + 0 - h - 1)) (bitSymbol false) ++ rl))
        (by decide) (by decide) (by decide) (by simp [hv₁, h2]) (by simp [hv₁, hh])
        (by simp)).seq <|
      sgU_clear body (a := .s 28) (x := e + 0 - h - 1) (by simp))
    refine lr_weaken body (s1.seq s2) ?_ ?_
    · refine congrArg (synG R) ?_
      funext y
      simp only [hv₁, Function.update_apply]
      split_ifs <;> simp_all [twSeg, he]
    · simp only [synSegCost, he, ite_true]
      omega
  · have he0 : v₁ (.s 28) = [] := by simp [hv₁]; omega
    have s2 := sg_ifNE_neg body (R := R) (p := .seq (synPop (sreg (.s 28))) <|
       .seq (umulSym 1 (bitSymbol false) (sreg (.s 28)) (sreg (.tw .rl)) (sreg (.s 2))) <|
       .seq (synPush (sreg (.tw .rl)) separator) <|
       .seq (umulSym 1 (bitSymbol true) (sreg (.p .h)) (sreg (.tw .rl)) (sreg (.s 2)))
         (uclear (sreg (.s 28)))) he0
      (sgR_umulSym body 1 (bitSymbol false) (a := .s 27) (b := .tw .rl) (t := .s 2) (x := e)
        (l := rl) (by decide) (by decide) (by decide) (by simp [hv₁, h2]) (by simp [hv₁, h27])
        (by simp [hv₁, hrl]))
    refine lr_weaken body (s1.seq s2) ?_ ?_
    · refine congrArg (synG R) ?_
      funext y
      simp only [hv₁, Function.update_apply]
      split_ifs <;> simp_all [twSeg, he]
    · simp only [synSegCost, he, ite_false]
      omega

/-- The step bound of `synRoles`. -/
def synRolesCost (es : List ℕ) (h : ℕ) : ℕ :=
  (∑ t ∈ Finset.range es.length, (2 * es.getD t 0 + 3 + synSegCost (es.getD t 0) h +
    (2 * es.getD t 0 + 2) + 3)) + 2 * es.length + 4 +
    (2 * (topRec es : List (Fin (A + 4))).length + 2)

theorem sg_synRoles (v : SynW → List (Fin (A + 4))) (es : List ℕ) (h : ℕ)
    (hes : v (.p .es) = topRec es) (hD : (v (.p .D)).length = es.length)
    (hh : (v (.p .h)).length = h) (hrl : v (.tw .rl) = []) (h2 : v (.s 2) = [])
    (h23 : v (.s 23) = []) (h26 : v (.s 26) = []) (h27 : v (.s 27) = []) (h28 : v (.s 28) = []) :
    LayRuns body synRoles (synG R v)
      (synG R (Function.update v (.tw .rl) (twRoles A es h))) (synRolesCost (A := A) es h) := by
  set cs := v (.p .D) with hcs
  let Φ : ℕ → SynW → List (Fin (A + 4)) := fun t =>
    Function.update (Function.update (Function.update v (.p .es) (topRec (es.drop t))) (.s 26)
      (topRec (es.take t)).reverse) (.tw .rl) (twRoles A (es.take t) h)
  have hstep : ∀ t < cs.length, LayRuns body synRoleStep
      (synG R (Function.update (Function.update (Φ t) (.p .D) (cs.drop (t + 1))) (.s 23)
        (cs.take (t + 1)).reverse))
      (synG R (Function.update (Function.update (Φ (t + 1)) (.p .D) (cs.drop (t + 1))) (.s 23)
        (cs.take (t + 1)).reverse))
      (2 * es.getD t 0 + 3 + synSegCost (es.getD t 0) h + (2 * es.getD t 0 + 2)) := by
    intro t ht
    have htD : t < es.length := by rw [← hD]; exact ht
    have hdrop : es.drop t = es[t] :: es.drop (t + 1) := List.drop_eq_getElem_cons htD
    have hget : es.getD t 0 = es[t] := List.getD_eq_getElem _ _ htD
    rw [hget]
    have htake : es.take (t + 1) = es.take t ++ [es[t]] := List.take_succ_eq_append_getElem htD
    refine lr_weaken body
      ((sgR_topField body (src := .p .es) (bk := .s 26) (dst := .s 27) (by decide) (by decide)
        (by decide) true es[t] (rest := topRec (es.drop (t + 1)))
        (l₁ := (topRec (es.take t)).reverse) (l₂ := [])
        (by
          have e1 : Function.update (Function.update (Φ t) (.p .D) (cs.drop (t + 1))) (.s 23)
              (cs.take (t + 1)).reverse (.p .es) = topRec (es.drop t) := by simp [Φ]
          rw [e1, hdrop, topRec_cons]) (by simp [Φ]) (by simp [Φ, h27])).seq <|
      (sg_synSegP body _ es[t] h (twRoles A (es.take t) h) (by simp) (by simp [Φ, hh])
        (by simp [Φ]) (by simp [Φ, h2]) (by simp [Φ, h28])).seq <|
      sgU_clear body (a := .s 27) (x := es[t]) (by simp)) ?_ (by omega)
    refine congrArg (synG R) ?_
    funext y
    simp only [Φ, Function.update_apply, htake, twRoles_snoc, topRec_reverse_snoc]
    split_ifs <;> simp_all
  have hscan := sg_scan body (R := R) (a := .p .D) (t := .s 23) (by decide) Φ cs
    (fun t => 2 * es.getD t 0 + 3 + synSegCost (es.getD t 0) h + (2 * es.getD t 0 + 2)) hstep
  have hcsl : cs.length = es.length := hD
  rw [hcsl] at hscan
  refine lr_weaken body ((lr_congr_left body hscan ?_).seq
    (sgR_move body (a := .s 26) (b := .p .es) (l := (topRec es).reverse) (l' := [])
      (by decide) (by simp [Φ]) (by simp [Φ]))) ?_ ?_
  · refine congrArg (synG R) ?_
    funext y
    simp only [Φ, Function.update_apply, List.drop_zero, List.take_zero, twRoles, topRec_nil,
      List.reverse_nil]
    split_ifs <;> simp_all
  · refine congrArg (synG R) ?_
    funext y
    simp only [Φ, Function.update_apply, List.drop_length, List.take_length, topRec_nil,
      List.reverse_reverse, List.append_nil]
    split_ifs <;> simp_all
  · simp [synRolesCost]

end Roles

/-! ### The twiddle pass on the transform wires -/

section Twiddle

variable {Q A : ℕ} {U P : Type}

/-- The wire file `v` with the twiddle registers replaced by `ρ`. -/
def synTwSet (v : SynW → List (Fin (A + 4))) (ρ : TwReg → List (Fin (A + 4))) :
    SynW → List (Fin (A + 4))
  | .tw x => ρ x
  | y => v y

theorem twStream_eq_cstream (A w : ℕ) {r : ℕ} (M : ℕ) (Z : ℕ → Fin r → GaussianInt) :
    twStream A w (List.range M) Z = cstream A w (IntegerMultBounds.MathlibTM2.Fast.rpStream M Z) := by
  simp only [twStream, cstream, IntegerMultBounds.MathlibTM2.Fast.rpStream, List.flatMap_assoc]

theorem sg_of_twRuns (body : P → Pr P (nT SXReg) Q A U) {p : Pr P (nT SXReg) Q A U}
    {ρ ρ' : TwReg → List (Fin (A + 4))} {b : ℕ} (h : TwRuns body synTg p ρ ρ' b)
    (Ro : Fin (nT SXReg) → List (Fin (A + 4))) (v : SynW → List (Fin (A + 4)))
    (hv : ∀ x, v (.tw x) = ρ x) :
    LayRuns body p (synG Ro v) (synG Ro (synTwSet v ρ')) b := by
  intro vv S _ hS
  have hold : TwHolds synTg S ρ := fun x => by rw [hS]; simp [synTg, hv]
  obtain ⟨v', S', n, hu, hn, he, hS', hfr⟩ := h vv S hold
  refine ⟨v', n, hu, hn, ?_⟩
  have e : S' = { S with R := synG Ro (synTwSet v ρ') } := by
    obtain ⟨h1, h2, h3, h4⟩ := hfr
    cases S' with
    | mk inp out L Rr =>
      cases S with
      | mk inp₀ out₀ L₀ R₀ =>
        simp only at h1 h2 h3 h4 hS ⊢
        subst h1 h2 h3
        congr 1
        funext k
        by_cases hk : ∃ x, synTg x = k
        · obtain ⟨x, rfl⟩ := hk
          have := hS' x
          simp only at this
          rw [this]
          simp [synTg, synTwSet]
        · rw [h4 k (fun r hr => hk ⟨r, hr⟩), hS]
          by_cases hw : ∃ y, sreg y = k
          · obtain ⟨y, rfl⟩ := hw
            cases y with
            | tw x => exact absurd ⟨x, rfl⟩ hk
            | _ => simp [synTwSet]
          · rw [synG_of_ne (fun y hy => hw ⟨y, hy⟩), synG_of_ne (fun y hy => hw ⟨y, hy⟩)]
  rw [e] at he
  exact he

end Twiddle

/-! ### One twiddle pass -/

section TwStep

variable {Q A : ℕ} {U P : Type}

/-- The twiddle registers from the wires: the stream from `io` onto `tw .src`, the physical
address `binSyms N 0`, the counters `N`, `N`, the roles of round `h`, `w`, `2^l w`, `h + 1`,
`l - h`. -/
noncomputable def synTwUp : Pr P (nT SXReg) Q A U :=
  .seq (moveR (lreg .io) (sreg (.s 25)) id) <|
  .seq (moveR (sreg (.s 25)) (sreg (.tw .src)) id) <|
  .seq (zeroBits (sreg (.p .N)) (sreg (.tw .pa)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.p .N)) (sreg (.tw .nn)) (sreg (.s 2))) <|
  .seq (ucopy (sreg (.p .N)) (sreg (.tw .nm)) (sreg (.s 2))) <|
  .seq synRoles <|
  .seq (ucopy (sreg (.p .w)) (sreg (.tw .wn)) (sreg (.s 2))) <|
  .seq (synMulR (sreg (.p .r)) (sreg (.p .w)) (sreg (.tw .rwn)) (sreg (.s 2)) (sreg (.s 3))) <|
  .seq (ucopy (sreg (.p .h)) (sreg (.tw .hn)) (sreg (.s 2))) <|
  .seq (synPush (sreg (.tw .hn)) tick) <|
  .seq (ucopy (sreg (.p .lr)) (sreg (.tw .lh)) (sreg (.s 2)))
    (usub (sreg (.p .h)) (sreg (.tw .lh)) (sreg (.s 2)))

/-- The output stream back onto `io` and the twiddle registers cleared. -/
noncomputable def synTwDown : Pr P (nT SXReg) Q A U :=
  .seq (moveR (sreg (.tw .dst)) (sreg (.s 25)) id) <|
  .seq (moveR (sreg (.s 25)) (lreg .io) id) <|
  .seq (uclear (sreg (.tw .pa))) <| .seq (uclear (sreg (.tw .nn))) <|
  .seq (uclear (sreg (.tw .nm))) <| .seq (uclear (sreg (.tw .rl))) <|
  .seq (uclear (sreg (.tw .wn))) <| .seq (uclear (sreg (.tw .rwn))) <|
  .seq (uclear (sreg (.tw .hn))) (uclear (sreg (.tw .lh)))

/-- The twiddle of round `h` on the stream of `io` (`fwd`: `y^(-E)`, else `y^E`). -/
noncomputable def synTwStep (fwd : Bool) : Pr P (nT SXReg) Q A U :=
  .seq synTwUp (.seq (twPassLP synTg fwd) synTwDown)

/-- The step bound of `synTwStep`. -/
def synTwCost (es : List ℕ) (l w h : ℕ) : ℕ :=
  let N := es.sum
  let V := 2 ^ N * (2 ^ l * w)
  (2 * V + 2) + (2 * V + 2) + (4 * N + 4) + (4 * N + 4) + (4 * N + 4) +
    synRolesCost (A := 0) es h + (4 * w + 4) + synMulRCost (2 ^ l) w + (4 * h + 4) + 1 +
    (4 * l + 4) + (4 * h + 4) +
    twPassLCost N h l w (2 ^ N) +
    (2 * V + 2) + (2 * V + 2) + (2 * N + 2) + (2 * N + 2) + (2 * N + 2) + (2 * N + 2) +
    (2 * w + 2) + (2 * (2 ^ l * w) + 2) + (2 * (h + 1) + 2) + (2 * (l - h) + 2)

theorem topRec_length_A (es : List ℕ) {A A' : ℕ} :
    (topRec es : List (Fin (A + 4))).length = (topRec es : List (Fin (A' + 4))).length := by
  simp [length_topRec]

theorem twRoles_length' (A : ℕ) (es : List ℕ) (h : ℕ) : (twRoles A es h).length = es.sum :=
  twRoles_length es h

theorem cstream_rpStream_length (A w : ℕ) {r : ℕ} (M : ℕ) (Y : ℕ → Fin r → GaussianInt) :
    (cstream A w (IntegerMultBounds.MathlibTM2.Fast.rpStream M Y)).length = M * (r * w) := by
  rw [length_cstream]
  simp [IntegerMultBounds.MathlibTM2.Fast.rpStream, List.length_flatMap]
  ring

theorem sg_synTwStep (body : P → Pr P (nT SXReg) Q A U) (fwd : Bool) (hA : 5 ≤ A)
    {es : List ℕ} {l w h : ℕ} (hw1 : 1 ≤ w) (hhl : h ≤ l) (L : Equiv.Perm (Fin es.sum))
    (Ro : Fin (nT SXReg) → List (Fin (A + 4))) (v : SynW → List (Fin (A + 4)))
    (Y : ℕ → Fin (2 ^ l) → GaussianInt)
    (hio : Ro (lreg .io) = cstream A w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum) Y))
    (hpz : v (.tw .pz) = twPosReg A es.sum (twPosL L)) (htw : ∀ x, x ≠ .pz → v (.tw x) = [])
    (hN : (v (.p .N)).length = es.sum) (hw : (v (.p .w)).length = w)
    (hr : (v (.p .r)).length = 2 ^ l) (hlr : (v (.p .lr)).length = l)
    (hh : (v (.p .h)).length = h) (hes : v (.p .es) = topRec es)
    (hD : (v (.p .D)).length = es.length)
    (h2 : v (.s 2) = []) (h3 : v (.s 3) = []) (h23 : v (.s 23) = []) (h25 : v (.s 25) = [])
    (h26 : v (.s 26) = []) (h27 : v (.s 27) = []) (h28 : v (.s 28) = []) :
    LayRuns body (synTwStep fwd) (synG Ro v)
      (synG (Function.update Ro (lreg .io) (cstream A w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum)
        (fun m => twShiftZ (twEx fwd es l h (twGat (twPosL L) es.sum m)) (Y m))))) v)
      (synTwCost es l w h) := by
  have hiol : (cstream A w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum) Y)).length =
      2 ^ es.sum * (2 ^ l * w) := cstream_rpStream_length A w _ Y
  have hrng : List.range' 0 (2 ^ es.sum) = List.range (2 ^ es.sum) := (List.range_eq_range' ..).symm
  refine lr_weaken body (LayRuns.seq
    ((so_moveOWV body (o := lreg .io) (a := .s 25)
      (l := cstream A w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum) Y)) (l' := [])
      (lreg_out (by simp)) hio h25).seq <|
    (sgR_move body (a := .s 25) (b := .tw .src)
      (l := (cstream A w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum) Y)).reverse ++ []) (l' := [])
      (by decide) (by simp) (by simp [htw])).seq <|
    (sgR_zeroBits body (a := .p .N) (b := .tw .pa) (t := .s 2) (x := es.sum) (l := [])
      (by decide) (by decide) (by decide) (by simp [h2]) (by simp [hN]) (by simp [htw])).seq <|
    (sgU_copy body (a := .p .N) (b := .tw .nn) (t := .s 2) (x := es.sum) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hN]) (by simp [htw])).seq <|
    (sgU_copy body (a := .p .N) (b := .tw .nm) (t := .s 2) (x := es.sum) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hN]) (by simp [htw])).seq <|
    (sg_synRoles body _ es h (by simp [hes]) (by simp [hD]) (by simp [hh]) (by simp [htw])
      (by simp [h2]) (by simp [h23]) (by simp [h26]) (by simp [h27]) (by simp [h28])).seq <|
    (sgU_copy body (a := .p .w) (b := .tw .wn) (t := .s 2) (x := w) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hw]) (by simp [htw])).seq <|
    (sgU_mulR body (a := .p .r) (b := .p .w) (c := .tw .rwn) (t₁ := .s 2) (t₂ := .s 3)
      (x := 2 ^ l) (y := w) (z := 0) (by decide) (by simp [h2]) (by simp [h3]) (by simp [hr])
      (by simp [hw]) (by simp [htw])).seq <|
    (sgU_copy body (a := .p .h) (b := .tw .hn) (t := .s 2) (x := h) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hh]) (by simp [htw])).seq <|
    (sgU_push body (a := .tw .hn) (y := h + 0) (by simp)).seq <|
    (sgU_copy body (a := .p .lr) (b := .tw .lh) (t := .s 2) (x := l) (y := 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hlr]) (by simp [htw])).seq <|
    sgU_sub body (a := .p .h) (b := .tw .lh) (t := .s 2) (x := h) (y := l + 0) (by decide)
      (by decide) (by decide) (by simp [h2]) (by simp [hh]) (by simp))
    ((sg_of_twRuns body (twPassL_runs (body := body) synTg_injective fwd hA (es := es)
      (ℓ := l) (h := h) (w := w) (m₀ := 0) (M := 2 ^ es.sum) hw1 hhl (twPosL L) (twPosL_lt L) Y _
      (by simp [hrng, twStream_eq_cstream]) (by simp [hN, htw]) (by simp [hpz]) (by simp [hN])
      (by simp [hN]) (by simp) (by simp [hw]) (by simp) (by simp) (by simp [hh])
      (by simp [htw]) (by simp [htw]) (by simp [htw]) (by simp [htw]) (by simp [htw])
      (by simp [htw]) (by simp [htw]) (by simp [htw]) (by simp [htw]) (by simp [htw])
      (by simp [htw]) (by simp [htw]) (by simp [htw]) (by simp [htw]) (by simp [htw])
      (by simp [htw]) (by simp [htw]) (by simp [htw]) (by simp [htw]) (by simp [htw]))
      _ _ (fun x => rfl)).seq <|
    (sgR_move body (a := .tw .dst) (b := .s 25)
      (l := twStream A w (List.range' 0 (2 ^ es.sum))
        (fun m => twShiftZ (twEx fwd es l h (twGat (twPosL L) es.sum m)) (Y m)) ++ [])
      (l' := []) (by decide) (by simp [synTwSet, htw]) (by simp [synTwSet])).seq <|
    (so_moveWOV body (o := lreg .io) (a := .s 25)
      (l := (twStream A w (List.range' 0 (2 ^ es.sum))
        (fun m => twShiftZ (twEx fwd es l h (twGat (twPosL L) es.sum m)) (Y m)) ++ []).reverse ++ [])
      (l' := []) (lreg_out (by simp)) (by simp) (by simp)).seq <|
    (sgU_clear body (a := .tw .pa) (x := es.sum) (by simp [synTwSet, binSyms, htw])).seq <|
    (sgU_clear body (a := .tw .nn) (x := es.sum) (by simp [synTwSet, htw])).seq <|
    (sgU_clear body (a := .tw .nm) (x := es.sum) (by simp [synTwSet, htw])).seq <|
    (sgU_clear body (a := .tw .rl) (x := es.sum) (by simp [synTwSet, twRoles_length, htw])).seq <|
    (sgU_clear body (a := .tw .wn) (x := w) (by simp [synTwSet, htw])).seq <|
    (sgU_clear body (a := .tw .rwn) (x := 2 ^ l * w) (by simp [synTwSet, htw])).seq <|
    (sgU_clear body (a := .tw .hn) (x := h + 1) (by simp [synTwSet, htw])).seq <|
    sgU_clear body (a := .tw .lh) (x := l - h) (by simp [synTwSet, htw]))) ?_ ?_
  · congr 1
    · simp only [List.append_nil, List.reverse_reverse, hrng, twStream_eq_cstream,
        Function.update_idem]
    · funext y
      cases y with
      | tw x =>
          cases x <;> simp (config := {maxSteps := 4000000}) [synTwSet, Function.update_apply,
            htw, hpz]
      | s i =>
          by_cases hi : i = 25
          · subst hi; simp [synTwSet, Function.update_apply, h25]
          · simp [synTwSet, Function.update_apply, hi]
      | _ => simp [synTwSet, Function.update_apply]
  · simp only [synTwCost, synRolesCost, topRec_length_A (A := A) (A' := 0) es, hiol]
    simp only [twStream_length, List.length_range', List.length_append, List.length_nil,
      List.length_reverse, Nat.add_zero]
    omega

end TwStep

/-! ### The layer step of a round -/

section LayerStep

/-- The persistent wires, parked on `park` while the layer runs. -/
def synXS : List SynW :=
  [.p .h, .p .c, .p .t, .p .K, .p .ℓ, .p .b, .p .D, .p .Lg, .p .N, .p .w, .p .r, .p .lr, .p .es,
    .tw .pz]

theorem synXS_nodup : synXS.Nodup := by decide

/-- The wires of round `h` between the steps of a round: the parameters, the axis record, the
twiddle positions of the layout `L`, the round counter (`p .c`, `p .t`, any symbols but blank),
everything else empty. -/
structure SynV {A : ℕ} (v : SynW → List (Fin (A + 4))) (es : List ℕ) (ℓ K w l h : ℕ)
    (L : Equiv.Perm (Fin es.sum)) : Prop where
  hh : (v (.p .h)).length = h
  hK : (v (.p .K)).length = K
  hℓ : (v (.p .ℓ)).length = ℓ
  hb : (v (.p .b)).length = layB ℓ K
  hD : (v (.p .D)).length = es.length
  hLg : (v (.p .Lg)).length = synLg es ℓ
  hN : (v (.p .N)).length = es.sum
  hw : (v (.p .w)).length = w
  hr : (v (.p .r)).length = 2 ^ l
  hlr : (v (.p .lr)).length = l
  hes : v (.p .es) = topRec es
  hpz : v (.tw .pz) = twPosReg A es.sum (twPosL L)
  htw : ∀ x, x ≠ .pz → v (.tw x) = []
  hs : ∀ i, v (.s i) = []
  hly : ∀ i, v (.ly i) = []
  hw2 : v (.p .w2) = []
  hcf : v (.p .cf) = []
  hkh : v (.p .kh) = []
  hrh : v (.p .rh) = []
  hpr : v (.p .pr) = []
  hblank : ∀ x ∈ synXS, blank ∉ v x

variable {A : ℕ}

theorem synIdle_update_io (io P₀ X : List (Fin (A + 4))) :
    Function.update (synIdle io P₀) (lreg .io) X = synIdle X P₀ := by
  funext z
  simp only [synIdle, lreg, Function.update_apply]
  split_ifs <;> simp_all

theorem synIdle_update_park (io P₀ X : List (Fin (A + 4))) :
    Function.update (synIdle io P₀) (lreg .park) X = synIdle io X := by
  funext z
  simp only [synIdle, lreg, Function.update_apply]
  split_ifs <;> simp_all

theorem synRestFile_update {x : LReg SXReg}
    (hx : x ∉ [LReg.ctr, .cS, .cR, .ph .rc, .ph .wc, .ph .af, .lf (.k .rctr), .lf (.k .wctr),
      .lf (.k .cf), .rowctr, .n, .w, .rw, .K, .ρ, .ph .arr])
    (Ro : Fin (nT SXReg) → List (Fin (A + 4))) (N r w' K ρ : ℕ) (pr X : List (Fin (A + 4))) :
    Function.update (synRestFile Ro N r w' K ρ pr) (lreg x) X =
      synRestFile (Function.update Ro (lreg x) X) N r w' K ρ pr := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16⟩ := hx
  funext z
  by_cases hz : z = lreg x
  · subst hz
    simp [synRestFile, lreg, Function.update_apply, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11,
      n12, n13, n14, n15, n16]
  · simp only [synRestFile, Function.update_apply, hz, ite_false]

theorem synIdle_rest (io P₀ : List (Fin (A + 4))) :
    ∀ x ∈ [LReg.ctr, .cS, .cR, .ph .rc, .ph .wc, .ph .af, .lf (.k .rctr), .lf (.k .wctr),
      .lf (.k .cf), .rowctr, .n, .w, .rw, .K, .ρ, .ph .arr], synIdle io P₀ (lreg x) = [] := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> simp [synIdle, lreg, Function.update_apply]

end LayerStep

/-! ### The layer step -/

section LayerProg

variable {Q Ka : ℕ} {U : Type}

/-- Drop the configuration record (ten fields) from `park`. -/
noncomputable def synPopCfg : Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq (topSkips (lreg .park) (sreg (.s 30)) (sreg (.s 31)) 10) (uclear (sreg (.s 30)))

/-- **The layer step of round `h`**: the records (`synRec`), the rest state of the layer machine
(`synRestUp`), the persistent wires parked on `park` with the configuration record on top,
`topProg`, the record dropped, the wires restored, the rest state cleared. -/
noncomputable def synLayerStep (ds : ComplexFramedExecution.Directions) :
    Pr LProc (nT SXReg) Q (prime + Ka) U :=
  .seq (synRec (gateCount (program ds)) (factorCount (program ds))) <|
  .seq synRestUp <|
  .seq (synStash (lreg .park) blank (synXS.map sreg)) <|
  .seq (moveR (sreg (.p .cf)) (lreg .park) id) <|
  .seq topProg <|
  .seq synPopCfg <|
  .seq (synUnstash (lreg .park) blank (synXS.map sreg)) synRestDown

/-- The step bound of the layer step. -/
noncomputable def synLayerStepCost (ds : ComplexFramedExecution.Directions) (es : List ℕ)
    (ℓ K w l h : ℕ) (stk : ℕ) : ℕ :=
  let G := gateCount (program ds)
  let F := factorCount (program ds)
  let W2 := synW2 es ℓ K G F w h
  let prl := topRecLen (topPcRec (synKh ℓ K h) (synPcsR es ℓ K h))
  let cfl := topRecLen (synCfg es ℓ K G F w h)
  synRecCost G F es ℓ K w h + synRestUpCost es.sum (2 ^ l) W2 (synKh ℓ K h) (synRh ℓ K h) prl +
    (stk + 1) + (2 * cfl + 2) + synLayerCost ds es ℓ K l w h +
    (2 * cfl + 10 + 1 + (2 * cfl + 2)) + (stk + 1) +
    synRestDownCost es.sum (2 ^ l) W2 (synKh ℓ K h) (synRh ℓ K h) prl

end LayerProg

section LayerStepRuns

variable {Q Ka : ℕ} {U : Type}

theorem length_topRec_any (l : List ℕ) {A A' : ℕ} :
    (topRec l : List (Fin (A + 4))).length = (topRec l : List (Fin (A' + 4))).length := by
  simp [length_topRec]

/-- **The layer step of round `h`.** -/
theorem sg_synLayerStep (hQ : swapStates sxHd sxPay sxHd_inj ≤ Q)
    (ds : ComplexFramedExecution.Directions) (hd : ComplexPhaseBudget.Realizes ds)
    (hA : 14 ≤ prime + Ka) (hA9 : 9 ^ 4 ≤ prime + Ka + 4) (hNW : NW ≤ prime + Ka + 4)
    (hgate : ∀ g, Instr.gate g ∈ program ds →
      (2 * gateBound g + 1) ^ (2 * (gateWires g).length) ≤ prime + Ka + 4)
    {es : List ℕ} {ℓ K : ℕ} (H : LayHyp es ℓ K) {l w p h : ℕ} (hh : h + 1 ≤ ℓ)
    (hpw : p + 2 ≤ w) (v : SynW → List (Fin (prime + Ka + 4)))
    (hv : SynV v es ℓ K w l h (layPerm es ℓ K)) (P₀ : List (Fin (prime + Ka + 4)))
    (Y : ℕ → Fin (2 ^ l) → GaussianInt) (hY : ∀ x c, ‖GaussianInt.toComplex (Y x c)‖ ≤ 2 ^ p) :
    LayRuns (layerTable (Ka := Ka) (U := U) hQ ds) (synLayerStep ds)
      (synG (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum) Y)) P₀) v)
      (synG (synIdle (cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum)
        (synTrunc (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
          (fun x c => GaussianInt.toComplex (Y x c)))))) P₀) v)
      (synLayerStepCost ds es ℓ K w l h (synStashCostW v synXS)) := by
  set G := gateCount (program ds) with hG
  set F := factorCount (program ds) with hF
  set io := cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum) Y) with hio
  set io' := cstream (prime + Ka) w (IntegerMultBounds.MathlibTM2.Fast.rpStream (2 ^ es.sum)
    (synTrunc (bflyL ((selBits es h).map (twPosL (layPerm es ℓ K)))
      (fun x c => GaussianInt.toComplex (Y x c))))) with hio'
  set W2 := synW2 es ℓ K G F w h with hW2
  set Kh := synKh ℓ K h with hKh
  set ρh := synRh ℓ K h with hρh
  set cfg := synCfg es ℓ K G F w h with hcfg
  set prRec : List (Fin (prime + Ka + 4)) := topRec (topPcRec Kh (synPcsR es ℓ K h)) with hprRec
  set body := layerTable (Ka := Ka) (U := U) hQ ds with hbody
  -- 1. the records
  have s1 := sg_synRec body (R := synIdle io P₀) G F es ℓ K w h H.K_pos v hv.hs hv.hcf hv.hkh
    hv.hrh hv.hpr hv.hw2 hv.hh hv.hK hv.hℓ hv.hb hv.hD hv.hLg hv.hN hv.hw
  set v₁ := synRecOut G F es ℓ K w h v with hv₁
  -- 2. the rest state
  have s2 := lr_synRestUp body (synIdle io P₀) v₁ es.sum (2 ^ l) W2 Kh ρh prRec
    (synIdle_rest io P₀) (by simp [hv₁, synRecOut, hW2]) (by simp [hv₁, synRecOut, hv.hN])
    (by simp [hv₁, synRecOut, hv.hr]) (by simp [hv₁, synRecOut, hKh])
    (by simp [hv₁, synRecOut, hρh]) (by simp [hv₁, synRecOut, hprRec, hKh])
    (by simp [hv₁, synRecOut, hv.hs]) (by simp [hv₁, synRecOut, hv.hs])
    (by simp [hv₁, synRecOut, hv.hs])
  set RF := synRestFile (synIdle io P₀) es.sum (2 ^ l) W2 Kh ρh prRec with hRF
  set v₂ := Function.update (Function.update (Function.update (Function.update v₁ (.p .kh) [])
    (.p .rh) []) (.p .pr) []) (.p .w2) [] with hv₂
  have hv₂X : ∀ x ∈ synXS, v₂ x = v x := by
    intro x hx
    simp only [synXS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> simp [hv₂, hv₁, synRecOut]
  -- 3. park the persistent wires
  have s3 := sg_synStash body (R := RF) (v := v₂) (pk := lreg .park) (lreg_out (by simp)) blank
    synXS synXS_nodup
  have hRFp : RF (lreg .park) = P₀ := by
    simp [hRF, synRestFile, synIdle, lreg, Function.update_apply]
  rw [hRFp] at s3
  set X3 := synStkW v₂ blank synXS ++ blank :: P₀ with hX3
  -- 4. the configuration record on top
  have s4 := so_moveWOV body (R := Function.update RF (lreg .park) X3)
    (v := synClrW v₂ synXS) (o := lreg .park) (a := .p .cf) (l := (topRec cfg).reverse)
    (l' := X3) (lreg_out (by simp)) (by simp [synClrW, synXS, hv₂, hv₁, synRecOut, hcfg])
    (by simp)
  rw [Function.update_idem, List.reverse_reverse] at s4
  set v₄ := Function.update (synClrW v₂ synXS) (.p .cf) [] with hv₄
  have hv₄0 : ∀ x, v₄ x = [] := by
    intro x
    by_cases hx : x ∈ synXS
    · simp [hv₄, synClrW, hx, Function.update_apply]
    · simp only [hv₄, synClrW, hx, ite_false, Function.update_apply]
      split_ifs with hcf
      · rfl
      · rcases x with x | i | x | i
        · have : x ≠ .pz := by intro h; subst h; simp [synXS] at hx
          simp [hv₂, hv₁, synRecOut, hv.htw x this]
        · simp [hv₂, hv₁, synRecOut, hv.hly i]
        · cases x <;> simp_all [hv₂, hv₁, synRecOut, synXS, hv.hw2, hv.hkh, hv.hrh, hv.hpr]
        · simp [hv₂, hv₁, synRecOut, hv.hs i]
  -- 5. the layer
  have hpark : ∀ X, Function.update RF (lreg .park) X =
      synRestFile (synIdle io X) es.sum (2 ^ l) W2 Kh ρh prRec := fun X => by
    rw [hRF, synRestFile_update (by simp), synIdle_update_park]
  have hioU : ∀ X Y', Function.update (synRestFile (synIdle Y' X) es.sum (2 ^ l) W2 Kh ρh prRec)
      (lreg .io) io' = synRestFile (synIdle io' X) es.sum (2 ^ l) W2 Kh ρh prRec := fun X Y' => by
    rw [synRestFile_update (by simp), synIdle_update_io]
  simp only [hpark] at s4 s3
  have hcfl : cfg.length = 10 := by simp [hcfg, synCfg, topCfg]
  have s5 := synLayer_runs (U := U) hQ ds hd hA hA9 hNW hgate H hh hpw Y hY
    (synG (synRestFile (synIdle io (topRec cfg ++ X3)) es.sum (2 ^ l) W2 Kh ρh prRec) v₄)
    (synRest_topRegs _ _ _ _ _ _ _ _ _ hv₄0)
    ⟨⟨X3, by
        rw [synG_of_ne (lreg_out (by simp))]
        simp [synRestFile, synIdle, lreg, Function.update_apply, hcfg, hG, hF]⟩,
      by rw [synG_of_ne (lreg_out (by simp))]
         simp [synRestFile, synIdle, lreg, Function.update_apply, hprRec, hKh],
      by rw [synG_of_ne (lreg_out (by simp))]
         simp [synRestFile, synIdle, lreg, Function.update_apply],
      by rw [synG_of_ne (lreg_out (by simp))]
         simp [synRestFile, synIdle, lreg, Function.update_apply],
      by rw [synG_of_ne (lreg_out (by simp))]
         simp [synRestFile, synIdle, lreg, Function.update_apply]⟩
    (by rw [synG_of_ne (lreg_out (by simp))]
        simp [synRestFile, synIdle, lreg, Function.update_apply, hio])
  rw [synG_update_out (lreg_out (by simp)), hioU] at s5
  -- 6. drop the record
  have s6 := (so_topSkips (layerTable (Ka := Ka) (U := U) hQ ds)
      (R := synRestFile (synIdle io' (topRec cfg ++ X3)) es.sum (2 ^ l) W2 Kh ρh prRec) (v := v₄)
      (o := lreg .park) (b := .s 30) (c := .s 31) (lreg_out (by simp)) (by decide) 10 cfg X3
      (by omega) (by simp [synRestFile, synIdle, lreg, Function.update_apply])).seq
    (sgU_clear (layerTable (Ka := Ka) (U := U) hQ ds) (a := .s 30)
      (x := (topRec (cfg.take 10) : List (Fin (prime + Ka + 4))).length) (by simp [hv₄0]))
  rw [synRestFile_update (by simp), synIdle_update_park, show cfg.drop 10 = [] by
      rw [List.drop_eq_nil_iff]; omega, topRec_nil, List.nil_append] at s6
  have hv6 : Function.update (Function.update v₄ (.s 30)
      ((topRec (cfg.take 10)).reverse ++ v₄ (.s 30))) (.s 30) [] = v₄ := by
    rw [Function.update_idem]; funext x; simp [Function.update_apply, hv₄0]
  rw [hv6] at s6
  -- 7. restore the wires
  set v₂' := Function.update v₂ (.p .cf) [] with hv₂'
  have hv₂'X : ∀ x ∈ synXS, v₂' x = v₂ x := by
    intro x hx
    have : x ≠ .p .cf := by intro h; subst h; simp [synXS] at hx
    simp [hv₂', this]
  have s7 := sg_synUnstash (layerTable (Ka := Ka) (U := U) hQ ds)
    (R := synRestFile (synIdle io' P₀) es.sum (2 ^ l) W2 Kh ρh prRec) (v := v₂')
    (pk := lreg .park) (lreg_out (by simp)) blank synXS P₀ synXS_nodup
    (fun x hx => by rw [hv₂'X x hx, hv₂X x hx]; exact hv.hblank x hx)
  rw [synStkW_congr blank synXS hv₂'X, synRestFile_update (by simp), synIdle_update_park,
    synRestFile_update (by simp), synIdle_update_park] at s7
  have hclr : synClrW v₂' synXS = v₄ := by
    funext x
    simp only [synClrW, hv₂', hv₄, Function.update_apply]
    split_ifs <;> simp_all
  rw [hclr] at s7
  -- 8. clear the rest state
  have s8 := lr_synRestDown (layerTable (Ka := Ka) (U := U) hQ ds) (synIdle io' P₀) v₂' es.sum
    (2 ^ l) W2 Kh ρh prRec (synIdle_rest io' P₀)
  refine lr_weaken body (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (s6.seq (s7.seq s8))))))) ?_ ?_
  · refine congrArg (synG (synIdle io' P₀)) ?_
    funext x
    simp only [hv₂', hv₂, hv₁, synRecOut, Function.update_apply]
    split_ifs <;> simp_all [hv.hw2, hv.hcf, hv.hkh, hv.hrh, hv.hpr]
  · rw [synStashCostW_congr synXS hv₂X, synStashCostW_congr synXS
      (fun x hx => (hv₂'X x hx).trans (hv₂X x hx))]
    have htake : cfg.take 10 = cfg := List.take_of_length_le (by omega)
    rw [htake]
    simp only [synLayerStepCost]
    simp only [hcfg, hW2, hKh, hρh, hprRec, hG, hF]
    simp only [length_topRec', List.length_reverse]
    omega

end LayerStepRuns

end IntegerMultBounds.MathlibTM2.Fast
