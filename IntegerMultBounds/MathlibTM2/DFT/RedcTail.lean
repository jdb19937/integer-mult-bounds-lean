module

public import IntegerMultBounds.MathlibTM2.DFT.Trunc

/-!
# The end of a Montgomery reduction

After the two products of Montgomery's REDC, register `tR` holds `t` and `m2` holds `q = m p`,
both in `r + r` bits. `redcTail` finishes the reduction on the host registers:

1. `m1` (the digit `m`) is cleared;
2. `sR := t + q` (`badd`, no overflow when `t + q < 2 ^ (r + r)`), and `m2` is cleared;
3. `sR := (t + q) / 2 ^ r` (`usub` by the width register `wR`, `bhigh_exec`);
4. scan slot `oR` records `sR < p` (`blt`);
5. `oR := sR` if so (`bcopy`), else `oR := sR - p` (`bsub`); `sR` is cleared.

`redcTail_exec`: `oR` ends with `binSyms r ((t + q) / 2 ^ r)` or `binSyms r ((t + q) / 2 ^ r - p)`
(`redcOut`), `m1` and `m2` end empty, and every other register ends as it started, in at most
`2 |m1| + 50 r + 50` steps.
-/

@[expose] public section

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

namespace IntegerMultBounds.MathlibTM2.DFT

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

/-- The value after one conditional subtraction of `p`. -/
def redcOut (p r s : ℕ) : ℕ := if s / 2 ^ r < p then s / 2 ^ r else s / 2 ^ r - p

/-- The test of the last step: scan slot `c` holds `bitSymbol true`. -/
def slotTrue (c : Fin T) (v : HS T Q A U) : Bool := decide (v.scan c = bitSymbol true)

/-- The end of REDC: `oR := ((t + q) / 2 ^ r) mod p` by one conditional subtraction. -/
def redcTail (tR pR wR oR m1 m2 sR t₁ t₂ t₃ : Fin T) : Pr P T Q A U :=
  .seq (bclear m1) (.seq (badd tR m2 sR t₁ t₂ t₃ oR) (.seq (bclear m2) (.seq (usub wR sR t₁)
    (.seq (blt sR pR t₁ t₂ t₃ oR) (.seq (.cond (slotTrue oR) (bcopy sR oR t₁ t₂)
      (bsub sR pR oR t₁ t₂ t₃ oR)) (bclear sR))))))

theorem bitSymbol_true_ne_false : (bitSymbol true : Fin (A + 4)) ≠ bitSymbol false := by
  simp [bitSymbol]

/-- `redcTail`: `oR := binSyms r (redcOut p r (t + q))`. -/
theorem redcTail_exec {tR pR wR oR m1 m2 sR t₁ t₂ t₃ : Fin T}
    (hreg : [tR, pR, wR, oR, m1, m2, sR, t₁, t₂, t₃].Nodup) {r t q p : ℕ}
    (ht : t < 2 ^ (r + r)) (hq : q < 2 ^ (r + r)) (hsum : t + q < 2 ^ (r + r))
    (hraw : (t + q) / 2 ^ r < 2 ^ r) (hp : p < 2 ^ r) (v : HS T Q A U) (S : Stacks T A)
    (htR : S.R tR = binSyms (r + r) t) (hm2 : S.R m2 = binSyms (r + r) q)
    (hpR : S.R pR = binSyms r p) (hw : (S.R wR).length = r) (ho : S.R oR = [])
    (hs : S.R sR = []) (h₁ : S.R t₁ = []) (h₂ : S.R t₂ = []) (h₃ : S.R t₃ = []) :
    ∃ v' : HS T Q A U, ∃ n, v'.user = v.user ∧ n ≤ 2 * (S.R m1).length + 50 * r + 50 ∧
      Exec body (redcTail tR pR wR oR m1 m2 sR t₁ t₂ t₃) (mk v S) n
        (mk v' { S with
          R := Function.update (Function.update (Function.update S.R m1 []) m2 []) oR
            (binSyms r (redcOut p r (t + q))) }) := by
  have hreg' := hreg
  regs_ne hreg'
  -- 1. clear `m1`
  obtain ⟨v₁, hu₁, -, e₁⟩ := bclear_exec body m1 v S
  set S₁ : Stacks T A := { S with R := Function.update S.R m1 [] } with hS₁
  -- 2. `sR := t + q`
  obtain ⟨v₂, hu₂, -, -, e₂⟩ := badd_exec body (a := tR) (b := m2) (c := sR) (tx := t₁) (ty := t₂)
    (tz := t₃) (cy := oR) (by regs_nodup) ‹tR ≠ oR›.symm ‹oR ≠ m2› ht hq v₁ S₁
    (by simp [hS₁, ‹tR ≠ m1›, htR]) (by simp [hS₁, ‹m1 ≠ m2›.symm, hm2])
    (by simp [hS₁, ‹m1 ≠ t₁›.symm, h₁]) (by simp [hS₁, ‹m1 ≠ t₂›.symm, h₂])
    (by simp [hS₁, ‹m1 ≠ t₃›.symm, h₃])
  rw [Nat.mod_eq_of_lt hsum, show S₁.R sR = [] by simp [hS₁, ‹m1 ≠ sR›.symm, hs],
    List.append_nil] at e₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R sR (binSyms (r + r) (t + q)) }
    with hS₂
  -- clear `m2`
  obtain ⟨v₃, hu₃, -, e₃⟩ := bclear_exec body m2 v₂ S₂
  rw [show S₂.R m2 = binSyms (r + r) q by simp [hS₂, hS₁, ‹m2 ≠ sR›, ‹m1 ≠ m2›.symm, hm2],
    length_binSyms] at e₃
  set S₃ : Stacks T A := { S₂ with R := Function.update S₂.R m2 [] } with hS₃
  -- 3. `sR := (t + q) / 2 ^ r`
  obtain ⟨v₄, hu₄, e₄⟩ := bhigh_exec body (a := sR) (wR := wR) (t := t₁) (by regs_nodup)
    (r := r) (e := r) (X := t + q) v₃ S₃ (by simp [hS₃, hS₂, ‹m2 ≠ sR›.symm])
    (by simp [hS₃, hS₂, hS₁, ‹wR ≠ m2›, ‹wR ≠ sR›, ‹wR ≠ m1›, hw])
    (by simp [hS₃, hS₂, hS₁, ‹m2 ≠ t₁›.symm, ‹sR ≠ t₁›.symm, ‹m1 ≠ t₁›.symm, h₁])
  set S₄ : Stacks T A :=
    { S₃ with R := Function.update S₃.R sR (binSyms r ((t + q) / 2 ^ r)) } with hS₄
  have hS₄s : S₄.R sR = binSyms r ((t + q) / 2 ^ r) := by simp [hS₄]
  have hS₄p : S₄.R pR = binSyms r p := by
    simp [hS₄, hS₃, hS₂, hS₁, ‹pR ≠ sR›, ‹pR ≠ m2›, ‹pR ≠ m1›, hpR]
  have hS₄o : S₄.R oR = [] := by
    simp [hS₄, hS₃, hS₂, hS₁, ‹oR ≠ sR›, ‹oR ≠ m2›, ‹oR ≠ m1›, ho]
  have hS₄t₁ : S₄.R t₁ = [] := by
    simp [hS₄, hS₃, hS₂, hS₁, ‹sR ≠ t₁›.symm, ‹m2 ≠ t₁›.symm, ‹m1 ≠ t₁›.symm, h₁]
  have hS₄t₂ : S₄.R t₂ = [] := by
    simp [hS₄, hS₃, hS₂, hS₁, ‹sR ≠ t₂›.symm, ‹m2 ≠ t₂›.symm, ‹m1 ≠ t₂›.symm, h₂]
  have hS₄t₃ : S₄.R t₃ = [] := by
    simp [hS₄, hS₃, hS₂, hS₁, ‹sR ≠ t₃›.symm, ‹m2 ≠ t₃›.symm, ‹m1 ≠ t₃›.symm, h₃]
  -- 4. compare with `p`
  obtain ⟨v₅, hu₅, hsc₅, -, e₅⟩ := blt_exec body (a := sR) (b := pR) (tx := t₁) (ty := t₂)
    (tz := t₃) (cy := oR) (by regs_nodup) ‹oR ≠ sR› ‹pR ≠ oR›.symm hraw hp v₄ S₄ hS₄s hS₄p
    hS₄t₁ hS₄t₂ hS₄t₃
  -- 5. the conditional subtraction
  have e₆ : ∃ v₆ : HS T Q A U, ∃ n₆, v₆.user = v₅.user ∧ n₆ ≤ 8 * r + 9 ∧
      Exec body (.cond (slotTrue oR) (bcopy sR oR t₁ t₂) (bsub sR pR oR t₁ t₂ t₃ oR)) (mk v₅ S₄)
        n₆ (mk v₆ { S₄ with R := Function.update S₄.R oR (binSyms r (redcOut p r (t + q))) }) := by
    by_cases hlt : (t + q) / 2 ^ r < p
    · have hf : slotTrue oR v₅ = true := by simp [slotTrue, hsc₅, hlt]
      obtain ⟨v₆, hu₆, e⟩ := bcopy_exec body (a := sR) (c := oR) (t₁ := t₁) (t₂ := t₂)
        (by regs_nodup) v₅ S₄ hS₄t₁ hS₄t₂
      rw [hS₄s, hS₄o, List.append_nil, length_binSyms] at e
      refine ⟨v₆, _, hu₆, by omega, Exec.cond_true hf (e.cast rfl ?_)⟩
      simp [redcOut, hlt]
    · have hf : slotTrue oR v₅ = false := by
        simp [slotTrue, hsc₅, hlt, bitSymbol_true_ne_false.symm]
      obtain ⟨v₆, hu₆, -, -, e⟩ := bsub_exec body (a := sR) (b := pR) (c := oR) (tx := t₁)
        (ty := t₂) (tz := t₃) (cy := oR) (by regs_nodup) ‹oR ≠ sR› ‹pR ≠ oR›.symm hraw hp v₅ S₄
        hS₄s hS₄p hS₄t₁ hS₄t₂ hS₄t₃
      rw [hS₄o, List.append_nil] at e
      have hval : ((t + q) / 2 ^ r + 2 ^ r - p) % 2 ^ r = (t + q) / 2 ^ r - p := by
        rw [show (t + q) / 2 ^ r + 2 ^ r - p = ((t + q) / 2 ^ r - p) + 2 ^ r by omega,
          Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [hval] at e
      refine ⟨v₆, _, hu₆, by omega, Exec.cond_false hf (e.cast rfl ?_)⟩
      simp [redcOut, hlt]
  obtain ⟨v₆, n₆, hu₆, hn₆, e₆⟩ := e₆
  set S₆ : Stacks T A := { S₄ with R := Function.update S₄.R oR (binSyms r (redcOut p r (t + q))) }
    with hS₆
  -- clear `sR`
  obtain ⟨v₇, hu₇, -, e₇⟩ := bclear_exec body sR v₆ S₆
  rw [show S₆.R sR = binSyms r ((t + q) / 2 ^ r) by simp [hS₆, ‹oR ≠ sR›.symm, hS₄s],
    length_binSyms] at e₇
  refine ⟨v₇, _, by rw [hu₇, hu₆, hu₅, hu₄, hu₃, hu₂, hu₁], ?_,
    Exec.cast (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅
      (Exec.seq e₆ e₇)))))) rfl ?_⟩
  · omega
  · clear e₁ e₂ e₃ e₄ e₅ e₆ e₇
    simp only [hS₆, hS₄, hS₃, hS₂, hS₁]
    congr 2
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

end IntegerMultBounds.MathlibTM2.DFT
